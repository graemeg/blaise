#!/usr/bin/env bash
# Rolling bootstrap for the Blaise self-hosting chain.
#
# Problem this solves:
#   A release binary (e.g. v0.9.0) can only compile source up to its own
#   feature set. The moment a post-release commit adds a new language feature
#   AND a later commit uses it in the runtime/compiler, the release binary can
#   no longer cold-bootstrap HEAD. End-users following `master` between releases
#   are then stuck — they have no binary new enough to build current source.
#
#   This is fine *during* development because each commit only needs the
#   PREVIOUS commit's binary: a feature is taught to the parser in one commit
#   and used in the next (the self-hosting two-step). The chain is therefore
#   continuous even though no single old binary spans the whole range.
#
# What this script does:
#   Replays that chain. Starting from a known-good release binary, it checks
#   out each commit in order and rebuilds the compiler + RTL using the PREVIOUS
#   step's freshly-built binary, carrying the result forward, until it reaches
#   the target ref (HEAD by default). The final binary is a working `-pre`
#   bootstrap binary for the current source — the same way the committed
#   v0.10.0-pre binary was produced by hand.
#
#   All work happens in a throwaway git worktree, so your live working tree
#   (including uncommitted changes) is never touched.
#
# Usage:
#   ./scripts/rolling-bootstrap.sh [--from <tag-or-commit>] [--to <ref>]
#                                  [--keep] [--no-install]
#
#   --from REF   Commit/tag to start from. Its release binary must exist at
#                releases/<REF>/blaise. Default: latest releases/v* with a
#                binary that is an ancestor of --to.
#   --to REF     Target ref to bootstrap up to. Default: HEAD.
#   --keep       Keep the temporary worktree on success (for inspection).
#   --no-install Do not copy the final binary into releases/. Just report.
#
# Exit codes:
#   0  reached target; final binary produced (and installed unless --no-install)
#   1  usage / environment error
#   2  a step failed to build — the offending commit is reported (likely a
#      broken two-step: a feature was used before/without teaching the parser)

set -u

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------
FROM_REF=""
TO_REF="HEAD"
KEEP_WORKTREE=0
DO_INSTALL=1

while [ $# -gt 0 ]; do
  case "$1" in
    --from)       FROM_REF="$2"; shift 2 ;;
    --to)         TO_REF="$2";   shift 2 ;;
    --keep)       KEEP_WORKTREE=1; shift ;;
    --no-install) DO_INSTALL=0;    shift ;;
    -h|--help)    grep '^#' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; exit 1 ;;
  esac
done

if [ ! -f "compiler/src/main/pascal/Blaise.pas" ]; then
  echo "Run this script from the project root." >&2
  exit 1
fi

ROOT="$(pwd)"
TO_SHA="$(git rev-parse --verify "$TO_REF^{commit}" 2>/dev/null)" || {
  echo "Bad --to ref: $TO_REF" >&2; exit 1; }

# ---------------------------------------------------------------------------
# Pick the start binary: explicit --from, else the newest release tag whose
# binary exists and is an ancestor of the target.
# ---------------------------------------------------------------------------
pick_start() {
  if [ -n "$FROM_REF" ]; then
    echo "$FROM_REF"
    return
  fi
  # Newest-first over release dirs that have a binary and lie on the path to TO.
  local d ref
  for d in $(ls -d releases/v* 2>/dev/null | sort -rV); do
    ref="${d#releases/}"
    [ -x "$d/blaise" ] || continue
    git rev-parse --verify "$ref^{commit}" >/dev/null 2>&1 || continue
    if git merge-base --is-ancestor "$ref" "$TO_SHA" 2>/dev/null; then
      echo "$ref"
      return
    fi
  done
}

START_REF="$(pick_start)"
if [ -z "$START_REF" ]; then
  echo "No usable start binary found under releases/ that is an ancestor of $TO_REF." >&2
  echo "Pass --from <tag> where releases/<tag>/blaise exists." >&2
  exit 1
fi

START_BIN="$ROOT/releases/$START_REF/blaise"
if [ ! -x "$START_BIN" ]; then
  echo "Start binary not found: $START_BIN" >&2
  exit 1
fi

START_SHA="$(git rev-parse --verify "$START_REF^{commit}")"
if ! git merge-base --is-ancestor "$START_SHA" "$TO_SHA"; then
  echo "Start ref $START_REF is not an ancestor of $TO_REF — cannot replay linearly." >&2
  exit 1
fi

# Ordered list of commits to replay: every commit strictly after START up to TO.
mapfile -t COMMITS < <(git rev-list --reverse --first-parent "${START_SHA}..${TO_SHA}")

echo "Rolling bootstrap"
echo "  from : $START_REF ($START_SHA)"
echo "  to   : $TO_REF ($TO_SHA)"
echo "  steps: ${#COMMITS[@]} commit(s) to replay"
echo

if [ "${#COMMITS[@]}" -eq 0 ]; then
  echo "Target is the start commit — nothing to replay. Start binary is already current."
  exit 0
fi

# ---------------------------------------------------------------------------
# Throwaway worktree so the live tree is never disturbed.
# ---------------------------------------------------------------------------
WT="$(mktemp -d /tmp/blaise-rollboot.XXXXXX)"
cleanup() {
  if [ "$KEEP_WORKTREE" -eq 1 ]; then
    echo "Worktree kept at: $WT"
  else
    git -C "$ROOT" worktree remove --force "$WT" 2>/dev/null
    rm -rf "$WT"
  fi
}
trap cleanup EXIT

git worktree add --detach "$WT" "$START_SHA" >/dev/null 2>&1 || {
  echo "Failed to create worktree." >&2; exit 1; }

# From v0.12.0 onward the native backend is the default and the compiler links
# via its internal assembler + internal linker, so no QBE binary and no gcc are
# needed to replay the bootstrap chain.  Only the distro's CRT objects (read by
# the internal linker) are required, which the runtime depends on anyway.

# CUR_BIN holds the most recently built (or starting) compiler binary.
CUR_BIN="$START_BIN"
# If the start release shipped no RTL, we will build one at the first step.

# ---------------------------------------------------------------------------
# build_step <worktree-dir> <compiler-binary> <rtl-archive-or-empty>
#   Builds RTL (with the given compiler) then the compiler itself, in WT.
#   Writes WT/_boot/blaise on success.
# ---------------------------------------------------------------------------
build_step() {
  local wt="$1" cc="$2"
  local out="$wt/_boot"
  mkdir -p "$out"

  # 1. (No RTL pre-build step: the compiler source-builds the RTL on demand
  #    into a target-keyed object cache beside its own binary.)
  #
  # 2. Compile the compiler with the previous-step binary straight to an
  #    executable.  Native default backend + internal assembler + internal
  #    linker: source in, binary out, no --emit-ir, no QBE, no gcc.
  #
  #    $BLAISE_RTL_SRC is MANDATORY here: the carried binary lives in _carry/,
  #    not beside its own compiler/ tree, so the binary-relative RTLSourceDir
  #    default would resolve to whatever tree the binary was copied from — the
  #    MAIN repo — and compile THIS step against HEAD's RTL source instead of
  #    the step's own worktree.  That surfaces as a spurious BOOTSTRAP_BROKEN
  #    (an old binary parsing a newer RTL unit).
  if ! BLAISE_RTL_SRC="$wt/compiler/src/main/pascal" \
       "$cc" --source "$wt/compiler/src/main/pascal/Blaise.pas" \
        --unit-path "$wt/compiler/src/main/pascal" \
        --unit-path "$wt/stdlib/src/main/pascal" \
        --output "$out/blaise" 2>"$out/compile.err"; then
    echo "    compiler build failed:"; head -5 "$out/compile.err" | sed 's/^/      /'
    return 1
  fi
  if [ ! -s "$out/blaise" ]; then
    echo "    compiler binary missing after build:"; head -3 "$out/compile.err" | sed 's/^/      /'
    return 1
  fi

  return 0
}

# ---------------------------------------------------------------------------
# smoke_test <compiler-binary> <rtl-archive> <worktree>
#   Compiles + runs a trivial program to prove the freshly-built binary is
#   functional (source -> native backend -> internal assembler + linker ->
#   runs -> correct stdout). Kept deliberately feature-agnostic: it must pass
#   at EVERY commit in the replay range, so it probes only arithmetic + WriteLn,
#   not any specific later feature.
# ---------------------------------------------------------------------------
smoke_test() {
  local cc="$1" wt="$2"
  local d; d="$(mktemp -d)"
  cat > "$d/s.pas" <<'PAS'
program P;
var X: Integer;
begin
  X := 6 * 7;
  WriteLn(X)
end.
PAS
  # $BLAISE_RTL_SRC short-circuits RTLSourceDir, which is binary-relative and
  # would otherwise miss: the carried binary does not sit beside its compiler/
  # tree.  Every commit in the replay range source-builds the RTL.
  local ok=1
  if BLAISE_RTL_SRC="$wt/compiler/src/main/pascal" \
     "$cc" --source "$d/s.pas" \
           --unit-path "$wt/compiler/src/main/pascal" \
           --unit-path "$wt/stdlib/src/main/pascal" \
           --output "$d/s" 2>"$d/s.err"; then
    [ "$("$d/s" 2>/dev/null)" = "42" ] && ok=0
  fi
  rm -rf "$d"
  return $ok
}

# ---------------------------------------------------------------------------
# Replay loop.
# ---------------------------------------------------------------------------
STEP=0
for sha in "${COMMITS[@]}"; do
  STEP=$((STEP + 1))
  short="$(git rev-parse --short "$sha")"
  subj="$(git log -1 --format=%s "$sha")"
  printf '[%d/%d] %s  %s\n' "$STEP" "${#COMMITS[@]}" "$short" "$subj"

  git -C "$WT" checkout --quiet --detach "$sha" 2>/dev/null || {
    echo "    checkout failed"; exit 2; }

  if ! build_step "$WT" "$CUR_BIN"; then
    echo
    echo "BOOTSTRAP_BROKEN at $short ($subj)"
    echo "  The previous step's binary could not build this commit. This usually"
    echo "  means a language feature was USED here before (or without) a prior"
    echo "  commit teaching the parser/codegen to understand it — a broken"
    echo "  self-hosting two-step. Fix by splitting: introduce the feature in one"
    echo "  commit, use it in the next."
    exit 2
  fi

  if ! smoke_test "$WT/_boot/blaise" "$WT"; then
    echo
    echo "SMOKE_FAILED at $short ($subj)"
    echo "  The binary built but produced wrong output for the local-const-array"
    echo "  probe. Treating as a broken step."
    exit 2
  fi

  # Carry this step's binary forward as the compiler for the next commit.
  # It travels alone — the RTL is source-built per step from that step's own
  # worktree, so there is no archive to keep beside it.
  mkdir -p "$WT/_carry"
  cp "$WT/_boot/blaise" "$WT/_carry/blaise"
  CUR_BIN="$WT/_carry/blaise"
done

echo
echo "REACHED $TO_REF — rolling bootstrap succeeded through ${#COMMITS[@]} commit(s)."

# ---------------------------------------------------------------------------
# Install the final binary as the current -pre release.
# ---------------------------------------------------------------------------
VER="$(grep -m1 -oE "Version = '[^']+'" "$WT/compiler/src/main/pascal/Blaise.pas" \
        | sed "s/Version = '//; s/'//")"
# 0.11.0-SNAPSHOT -> v0.11.0-pre ; 0.11.0 -> v0.11.0-pre
PRE="v${VER%-SNAPSHOT}"
case "$PRE" in *-pre) ;; *) PRE="${PRE}-pre" ;; esac

if [ "$DO_INSTALL" -eq 1 ]; then
  DEST="$ROOT/releases/$PRE"
  mkdir -p "$DEST"
  cp "$CUR_BIN" "$DEST/blaise"
  chmod +x "$DEST/blaise"
  echo "Installed: $DEST/blaise  [version $VER]"
else
  echo "Final binary: $CUR_BIN  [version $VER, would install to releases/$PRE]"
fi
