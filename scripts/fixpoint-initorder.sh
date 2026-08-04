#!/usr/bin/env bash
# Unit-initialisation ORDER guard for the incremental (--unit-cache) path.
#
# WHAT IT GUARDS:
#   That a unit's `initialization` section runs AFTER every unit it uses —
#   from the implementation section as well as the interface — no matter which
#   units come from a cache and which are recompiled from source.
#
# WHY IT EXISTS, separately from fixpoint-warmcache.sh:
#   fixpoint-warmcache.sh proves a warm-cache rebuild produces a CORRECT
#   binary, but it builds the compiler, whose units all use each other through
#   their INTERFACE sections.  The bug this script guards is invisible there:
#   it needs a unit reached only through another unit's IMPLEMENTATION uses.
#   That is the self-registration/plugin shape — a registry unit whose
#   initialization creates the list, and plugin units that impl-use it and
#   register from their own initialization.
#
#   Two real defects lived in that blind spot (2026-08-04, both fixed):
#     1. An impl-only dependency was added to the LINK line but never
#        registered for init, so its <Unit>_init shipped in the binary and was
#        never called — its globals stayed nil.
#     2. Cached ifaces were ordered by INTERFACE uses only, and the driver
#        emitted all cached inits before all source inits, so a dependent
#        could initialise before its dependency.
#   Both produced a segfault at startup with NO diagnostic at compile or link
#   time.  BlaiseGuard hit this for real: thirteen rule units registering into
#   a nil TList<IRule>.
#
# THE THREE LEGS (each covers a different arrangement of cached vs source):
#   1. cold  — every dep compiled fresh into the test cache
#   2. warm  — deps taken from a populated cache
#   3. mixed — the registry unit EDITED so it recompiles from source while its
#              dependents stay cached.  This is the shape that survived the
#              first attempt at the fix, and the most common one in practice
#              (edit a registry, rebuild incrementally).
#
# THE AGGREGATOR UNIT IS LOAD-BEARING.  `all` interface-uses every plugin,
# which is what pulls the plugins ahead of the registry in an interface-only
# ordering.  Without it the order comes out workable by luck and none of the
# legs fail even on a broken compiler.  (That is Guard.Rules.All's shape.)
#
# Requires: a current compiler at compiler/target/blaise.

set -e

if [ ! -f "compiler/src/main/pascal/Blaise.pas" ]; then
  echo "Run this script from the project root: ./scripts/fixpoint-initorder.sh" >&2
  exit 1
fi

STAGE1="compiler/target/blaise"
if [ ! -x "$STAGE1" ]; then
  echo "Compiler not found: $STAGE1" >&2
  echo "Build it first: pasbuild compile -m blaise-compiler --compiler ..." >&2
  exit 10
fi

STAGE1_ABS="$(cd "$(dirname "$STAGE1")" && pwd)/$(basename "$STAGE1")"
STDLIB_ABS="$(pwd)/stdlib/src/main/pascal"
RTLSRC_ABS="$(pwd)/compiler/src/main/pascal"

WORK="$(mktemp -d)"
cleanup() { rm -rf "$WORK"; }
trap cleanup EXIT

SRC="$WORK/src"
mkdir -p "$SRC"

# ---- the fixture -----------------------------------------------------------
# reg: owns a list created in its OWN initialization.  Register() deliberately
# has no nil guard — dependency-ordered init is the contract under test.
cat > "$SRC/reg.pas" <<'EOF'
unit reg;
interface
uses Generics.Collections;
procedure Register(const AName: string);
function Count: Integer;
implementation
var
  GItems: TList<string>;
procedure Register(const AName: string);
begin
  GItems.Add(AName);
end;
function Count: Integer;
begin
  Result := GItems.Count;
end;
initialization
  GItems := TList<string>.Create();
end.
EOF

# plugN: EMPTY interface uses; reg is an IMPLEMENTATION dependency.
for i in 1 2 3 4 5 6; do
cat > "$SRC/plug$i.pas" <<EOF
unit plug$i;
interface
implementation
uses reg;
initialization
  Register('p$i');
end.
EOF
done

# all: the aggregator — interface-uses every plugin (see the header note).
cat > "$SRC/all.pas" <<'EOF'
unit all;
interface
uses plug1, plug2, plug3, plug4, plug5, plug6;
implementation
end.
EOF

cat > "$SRC/p.pas" <<'EOF'
program P;
uses all, reg;
begin
  WriteLn(Count())
end.
EOF

UP="--unit-path $SRC --unit-path $STDLIB_ABS --rtl-src $RTLSRC_ABS"
APPC="$WORK/appcache"
TESTC="$WORK/testcache"
mkdir -p "$APPC" "$TESTC"

# Every plugin registers exactly once, so a correct run prints 6.
EXPECT=6

run_leg() {   # $1 = leg name, $2 = output binary
  local leg="$1" bin="$2" out rc
  set +e
  out="$("$bin" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -ne 0 ]; then
    echo "INITORDER_FAIL: leg '$leg' exited $rc (expected 0)" >&2
    [ "$rc" -ge 128 ] && echo "  (signal $((rc - 128)) — the classic symptom: a" \
                              "unit global was still nil when another unit's" \
                              "initialization touched it)" >&2
    echo "  output: $out" >&2
    exit 20
  fi
  if [ "$out" != "$EXPECT" ]; then
    echo "INITORDER_FAIL: leg '$leg' printed '$out', expected '$EXPECT'" >&2
    echo "  (a wrong count means some plugin's registration was lost)" >&2
    exit 21
  fi
  echo "      leg '$leg': printed $out, exit 0"
}

echo "[1/3] cold cache — every dep compiled fresh"
"$STAGE1_ABS" --source "$SRC/p.pas" --output "$WORK/p_cold" \
  --unit-cache "$APPC" $UP >/dev/null
run_leg cold "$WORK/p_cold"

echo "[2/3] warm cache — deps taken from the populated cache"
"$STAGE1_ABS" --source "$SRC/p.pas" --output "$WORK/p_warm" \
  --unit-cache "$TESTC" --unit-path "$APPC" $UP >/dev/null
run_leg warm "$WORK/p_warm"

echo "[3/3] mixed — registry unit edited (source) while dependents stay cached"
# Change reg.pas's CONTENT (the cache keys on a source hash, not mtime).
sed -i.bak 's/^interface$/interface\n{ invalidated by fixpoint-initorder }/' \
  "$SRC/reg.pas"
rm -f "$SRC/reg.pas.bak"
"$STAGE1_ABS" --source "$SRC/p.pas" --output "$WORK/p_mixed" \
  --unit-cache "$TESTC" --unit-path "$APPC" $UP >/dev/null
run_leg mixed "$WORK/p_mixed"

echo "INITORDER_FIXPOINT_OK"
