#!/usr/bin/env bash
# Incremental warm-cache rebuild guard for the Blaise self-hosting toolchain.
#
# WHAT IT GUARDS:
#   The incremental --unit-cache path: when the compiler rebuilds a program
#   whose dependency units are loaded from a POPULATED cache (their cached
#   .bif interface + .o object) instead of from source.  This script compiles
#   the WHOLE COMPILER twice into the SAME --unit-cache: the first build fills
#   the cache from source, the second build recompiles the top program against
#   the cached interfaces.  It asserts the warm-cache rebuild produces a binary
#   that is present, plausibly sized, AND behaviourally CORRECT (compiles +
#   runs a hello-world program), not merely a non-empty file.
#
# WHY IT EXISTS, separately from the other fixpoint scripts:
#   A whole class of bugs only manifests when a unit is loaded from its cached
#   .bif/.o rather than recompiled from source — a dropped field, a wrong
#   vtable slot, a duplicate global, a missing initialiser in the cached
#   interface round-trip.  None of the existing fixpoints exercise that path:
#   fixpoint.sh uses --emit-ir (no cache at all), fixpoint-native.sh diffs the
#   emitted .s (no cache), and fixpoint-native-internal.sh compiles a tiny
#   probe program (no large warm cache).  So a regression in the cached-
#   interface import / round-trip passes every current fixpoint and only blows
#   up later when an end user does an incremental rebuild.  This script is the
#   only fixpoint-level guard that drives a real warm --unit-cache rebuild of
#   a large codebase end to end.
#
# WHY THE BEHAVIOURAL CHECK MATTERS:
#   A broken warm-cache rebuild was observed to produce a truncated binary
#   (~1.9 MB vs the ~2.8 MB clean build) that SIGABRTs or prints nothing.  So
#   beyond "exit 0 + plausible size" we compile + run a hello-world program
#   with BOTH the clean-cache and warm-cache stage-2 binaries and require each
#   to print "Hello" and exit 0.  Present-but-wrong is the failure mode this
#   guard is built to catch.
#
# Requires: a current native-built compiler at compiler/target/blaise (run
# `pasbuild compile -m blaise-compiler` first).  The RTL is source-built by
# the driver, so no blaise_rtl.a is needed.

set -e

if [ ! -f "compiler/src/main/pascal/Blaise.pas" ]; then
  echo "Run this script from the project root: ./scripts/fixpoint-warmcache.sh" >&2
  exit 1
fi

STAGE1="compiler/target/blaise"
if [ ! -x "$STAGE1" ]; then
  echo "Compiler not found: $STAGE1" >&2
  echo "Build it first: pasbuild compile -m blaise-compiler --compiler ..." >&2
  exit 10
fi

# No RTL archive needed: the driver source-builds the RTL (EnsureRTLObjects).
if [ ! -f compiler/src/main/pascal/runtime.arc.pas ]; then
  echo "RTL source not found under compiler/src/main/pascal" >&2
  exit 11
fi

UNIT_PATHS="--unit-path compiler/src/main/pascal --unit-path stdlib/src/main/pascal"

# Portable file size: GNU stat (Linux CI) takes -c %s, BSD stat (macOS) takes
# -f %z and rejects -c outright ("illegal option -- c").
file_size() {
  stat -c %s "$1" 2>/dev/null || stat -f %z "$1"
}

# All temp state in one mktemp dir so cleanup is a single rm.
WORK="$(mktemp -d)"
UC="$WORK/cache"
mkdir -p "$UC"
STAGE2A="$WORK/wc_stage2a"
STAGE2B="$WORK/wc_stage2b"
trap 'rm -rf "$WORK"' EXIT

echo "compiler (stage-1): $STAGE1"
echo "unit-cache:         $UC"

echo "[1/4] BUILD 1 — compile whole compiler into a FRESH (empty) unit-cache"
set +e
"$STAGE1" --source compiler/src/main/pascal/Blaise.pas \
  --output "$STAGE2A" --unit-cache "$UC" $UNIT_PATHS \
  > "$WORK/build1.log" 2>&1
B1_RC=$?
set -e
if [ "$B1_RC" -ne 0 ]; then
  echo "BUILD1_FAIL (clean-cache build, exit=$B1_RC)"
  tail -15 "$WORK/build1.log"
  exit 1
fi
if [ ! -s "$STAGE2A" ]; then
  echo "BUILD1_FAIL (clean-cache build produced no binary)"
  exit 1
fi
SIZE1=$(file_size "$STAGE2A")
echo "      build1 ok — stage-2a size = $SIZE1 bytes"

# EDIT a DEPENDENCY unit between the two builds.  This is what a real
# incremental rebuild looks like (edit one unit, rebuild) and is the only thing
# that exercises STALENESS PROPAGATION: a unit whose cache is now stale must be
# recompiled from source, AND every cached unit that depends on it must also be
# recompiled — otherwise the cached dependent's iface is imported before the
# recompiled dependency's types exist, and resolution fails with EImportError.
# blaise.codegen.driver is depended on by blaise.frontend.opts (TBackendKind),
# so editing it triggers exactly that propagation.  A harmless trailing comment
# changes the content hash without changing behaviour.  Restored on exit.
EDIT_UNIT="compiler/src/main/pascal/blaise.codegen.driver.pas"
cp "$EDIT_UNIT" "$WORK/edit_unit.bak"
restore_edit() { cp "$WORK/edit_unit.bak" "$EDIT_UNIT" 2>/dev/null || true; rm -rf "$WORK"; }
trap restore_edit EXIT
printf '\n{ warmcache-fixpoint content-edit probe }\n' >> "$EDIT_UNIT"

echo "[2/4] BUILD 2 — edit a dependency unit, then recompile into the SAME cache"
# Path under test: the edited unit is stale (recompiled from source); its
# cached dependents must propagate that and recompile too, and unedited
# dependency units still load from cached .bif/.o.
set +e
"$STAGE1" --source compiler/src/main/pascal/Blaise.pas \
  --output "$STAGE2B" --unit-cache "$UC" $UNIT_PATHS \
  > "$WORK/build2.log" 2>&1
B2_RC=$?
set -e
# Restore the edited unit immediately — its content is no longer needed.
cp "$WORK/edit_unit.bak" "$EDIT_UNIT"
if [ "$B2_RC" -ne 0 ]; then
  echo "BUILD2_FAIL (warm-cache rebuild after content edit, exit=$B2_RC)"
  echo "  (likely a stale-cache propagation bug — a cached dependent of the"
  echo "   edited unit was imported before the recompiled unit's types existed,"
  echo "   raising EImportError; see grep 'recompiling from source' below)"
  grep -iE "stale|EImportError|recompil" "$WORK/build2.log" | head
  tail -15 "$WORK/build2.log"
  exit 1
fi
if [ ! -s "$STAGE2B" ]; then
  echo "BUILD2_FAIL (warm-cache rebuild produced no binary)"
  exit 1
fi
SIZE2=$(file_size "$STAGE2B")
echo "      build2 ok — stage-2b size = $SIZE2 bytes"

echo "[3/4] size sanity — warm-cache binary must not be drastically smaller"
# A truncated/broken warm-cache rebuild was ~1.9 MB vs a ~2.8 MB clean build.
# Require stage-2b to be at least 90% of stage-2a's size.
MIN_SIZE=$(( SIZE1 * 90 / 100 ))
if [ "$SIZE2" -lt "$MIN_SIZE" ]; then
  echo "SIZE_REGRESSION — stage-2b ($SIZE2) < 90% of stage-2a ($SIZE1)"
  echo "  (warm-cache rebuild looks truncated — likely a dropped section/global)"
  exit 1
fi
echo "      ok — stage-2b is within 10% of stage-2a"

echo "[4/4] behavioural check — both stage-2 binaries compile + run hello-world"
HELLO="$WORK/hello.pas"
printf 'program hello;\nbegin\n  WriteLn(%s);\nend.\n' "'Hello'" > "$HELLO"

# No RTL archive needed: the driver source-builds the RTL.  The RTL source is
# resolved from compiler/src/main/pascal, passed on the unit path below.
RT_UNIT_PATHS="--unit-path compiler/src/main/pascal --unit-path stdlib/src/main/pascal"

check_binary() {
  local label="$1"
  local bin="$2"
  local out="$WORK/${label}_hello"
  set +e
  "$bin" --source "$HELLO" --output "$out" $RT_UNIT_PATHS \
    > "$WORK/${label}_compile.log" 2>&1
  local crc=$?
  set -e
  if [ "$crc" -ne 0 ] || [ ! -x "$out" ]; then
    echo "HELLO_COMPILE_FAIL ($label, exit=$crc)"
    tail -10 "$WORK/${label}_compile.log"
    exit 1
  fi
  set +e
  local stdout; stdout="$("$out" 2>"$WORK/${label}_run.err")"
  local rrc=$?
  set -e
  if [ "$rrc" -ne 0 ]; then
    echo "HELLO_RUN_FAIL ($label, exit=$rrc)"
    echo "  stdout: [$stdout]"
    cat "$WORK/${label}_run.err"
    exit 1
  fi
  if [ "$stdout" != "Hello" ]; then
    echo "HELLO_OUTPUT_MISMATCH ($label) — expected 'Hello', got '$stdout'"
    exit 1
  fi
  echo "      $label: compiled, ran, printed 'Hello' (exit 0)"
}

check_binary "stage2a" "$STAGE2A"
check_binary "stage2b" "$STAGE2B"

echo "WARMCACHE_FIXPOINT_OK"
exit 0
