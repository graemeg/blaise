#!/usr/bin/env bash
# Linked-BINARY self-hosting fixpoint for the Blaise toolchain.
#
# WHAT IT GUARDS:
#   stage-1 compiles the compiler -> stage-2 EXECUTABLE.
#   stage-2 compiles the same source -> stage-3 EXECUTABLE.
#   stage-2 and stage-3 must be BYTE-IDENTICAL.
#
#   This is the only fixpoint that compares LINKED BINARIES.  The others all
#   stop short of the container:
#
#     fixpoint.sh                 diffs .ssa IR text
#     fixpoint-native.sh          diffs .s assembly text (links with EXTERNAL gcc)
#     fixpoint-native-internal.sh compares stdout + exit code of a small probe
#     fixpoint-warmcache.sh       compares behaviour + binary size within 10%
#
#   So a nondeterminism introduced AFTER codegen — in the internal assembler,
#   the internal linker, or the ELF/Mach-O container writer — passes every one
#   of them.  Timestamps, uninitialised padding, hash-order-dependent symbol
#   or relocation emission, and unstable build-ids all live in exactly that
#   blind spot.  This script closes it.
#
# WHY THE STAGES SHARE A BASENAME (do not "simplify" this):
#   The Mach-O writer derives LC_UUID from a SHA-256 over the payloads PLUS
#   the CodeDirectory identifier, and that identifier is the OUTPUT FILENAME
#   (blaise.linker.macho.pas -> SetIdentifier(ExtractFileName(AOutPath))).
#   Apple requires the identifier inside the CodeDirectory, so a differently
#   NAMED binary legitimately has a different UUID and a different signature —
#   on a macos-arm64 build, stage-2 vs stage-3 named differently differ in
#   exactly 49 bytes (16 UUID + 33 signature) while the code/data image is
#   identical.  That is correct behaviour, not a bug: the UUID is an image
#   identity that lldb and the crash reporter rely on.
#
#   Writing both stages to the SAME basename in DIFFERENT directories makes
#   the comparison apples-to-apples on every target.  ELF has no such
#   name-dependence, so this convention costs nothing there and keeps ONE
#   script valid for all targets.
#
# TARGETS:
#   Runs for the host by default.  Pass --target <os>-<cpu> to check a
#   cross-compiled container (macos-arm64, freebsd-x86_64, ...).  A
#   cross-built stage-2 cannot RUN on the host, so for a foreign target this
#   degrades to a "stage-1 twice" determinism check (still the only guard on
#   the container writer); for the host it is a full two-stage fixpoint.
#
# Requires: a compiler at compiler/target/blaise (run `pasbuild compile` or a
# prior fixpoint first).  The RTL is source-built by the driver — no
# blaise_rtl.a is involved.

set -e

if [ ! -f "compiler/src/main/pascal/Blaise.pas" ]; then
  echo "Run this script from the project root: ./scripts/fixpoint-binary.sh" >&2
  exit 1
fi

COMPILER="compiler/target/blaise"
TARGET=""
while [ $# -gt 0 ]; do
  case "$1" in
    --target) TARGET="$2"; shift 2 ;;
    --compiler) COMPILER="$2"; shift 2 ;;
    *) echo "usage: $0 [--target <os>-<cpu>] [--compiler <path>]" >&2; exit 1 ;;
  esac
done

if [ ! -x "$COMPILER" ]; then
  echo "Compiler not found: $COMPILER" >&2
  echo "Build it first: pasbuild compile -m blaise-compiler --compiler ..." >&2
  exit 10
fi

ABS_COMPILER="$(cd "$(dirname "$COMPILER")" && pwd)/$(basename "$COMPILER")"

SRC="compiler/src/main/pascal/Blaise.pas"
UNIT_ARGS="--unit-path compiler/src/main/pascal --unit-path stdlib/src/main/pascal"
TARGET_ARGS=""
LABEL="host"
if [ -n "$TARGET" ]; then
  TARGET_ARGS="--target $TARGET"
  LABEL="$TARGET"
fi

WORK="${TMPDIR:-/tmp}/fpbin.$$"
# Same BASENAME, different directories — see the header note on LC_UUID.
S2="$WORK/stage2"
S3="$WORK/stage3"
mkdir -p "$S2" "$S3"
trap 'rm -rf "$WORK"' EXIT

echo "[1/3] stage-1 -> stage-2 binary  ($LABEL)"
if ! "$ABS_COMPILER" --source "$SRC" $UNIT_ARGS $TARGET_ARGS \
       --backend native --output "$S2/blaise" 2>"$WORK/s2.err"; then
  echo "STAGE2_BUILD_FAIL"; head -20 "$WORK/s2.err"; exit 2
fi
if [ ! -s "$S2/blaise" ]; then
  echo "STAGE2_MISSING"; exit 2
fi

# A foreign-target stage-2 cannot execute here; fall back to running stage-1
# again, which still exercises the container writer for determinism.
STAGE2_RUNS=0
if [ -z "$TARGET" ]; then
  if "$S2/blaise" --help >/dev/null 2>&1; then
    STAGE2_RUNS=1
  else
    echo "STAGE2_NOT_RUNNABLE (built, but --help failed)"; exit 3
  fi
fi

if [ "$STAGE2_RUNS" -eq 1 ]; then
  echo "[2/3] stage-2 -> stage-3 binary  (true self-host fixpoint)"
  BUILDER="$S2/blaise"
else
  echo "[2/3] stage-1 -> stage-3 binary  (cross target: determinism check only)"
  BUILDER="$ABS_COMPILER"
fi

if ! "$BUILDER" --source "$SRC" $UNIT_ARGS $TARGET_ARGS \
       --backend native --output "$S3/blaise" 2>"$WORK/s3.err"; then
  echo "STAGE3_BUILD_FAIL"; head -20 "$WORK/s3.err"; exit 4
fi

echo "[3/3] compare stage-2 vs stage-3 (byte-identical?)"
if ! cmp -s "$S2/blaise" "$S3/blaise"; then
  echo "BINARY_FIXPOINT_DIFF"
  echo "  stage2: $(wc -c < "$S2/blaise") bytes"
  echo "  stage3: $(wc -c < "$S3/blaise") bytes"
  echo "  first differing offsets (decimal):"
  cmp -l "$S2/blaise" "$S3/blaise" 2>/dev/null | awk '{print $1}' | head -12 | sed 's/^/    /'
  echo "  total differing bytes: $(cmp -l "$S2/blaise" "$S3/blaise" 2>/dev/null | wc -l)"
  echo
  echo "  A post-codegen nondeterminism: the internal assembler, the internal"
  echo "  linker, or the container writer emitted different bytes for identical"
  echo "  input.  Look for a timestamp, uninitialised padding, an unstable"
  echo "  build-id, or hash-order-dependent symbol/relocation emission."
  exit 5
fi

echo "BINARY_FIXPOINT_OK ($LABEL, $(wc -c < "$S2/blaise") bytes)"
exit 0
