#!/bin/bash
# macos-dev.sh — stand-in for PasBuild on macOS.  PasBuild is an FPC program
# and there is no macOS FPC build of it yet, so on macOS the Blaise compiler
# is driven directly.  Used locally and by the macos-check CI job; retire it
# once PasBuild runs on macOS (ported to Blaise, or built by a macOS FPC).
#
#   scripts/macos-dev.sh compile [--compiler BIN]
#       build compiler/target/blaise (stage-1 default: newest releases/v*/blaise)
#   scripts/macos-dev.sh fixpoint [--compiler BIN] [--install]
#       self-host stage-1 -> stage-2 -> stage-3 and require stage-2 and stage-3
#       to be BYTE-IDENTICAL (prints BINARY_FIXPOINT_OK, exits non-zero
#       otherwise).  --install copies the verified stage-2 binary to
#       compiler/target/blaise.
#   scripts/macos-dev.sh test-compile
#       build compiler/target/TestRunner with compiler/target/blaise
#   scripts/macos-dev.sh test [TestRunner args]
#       test-compile, then run the compiler suite
#   scripts/macos-dev.sh stdlib-test [TestRunner args]
#       build and run the stdlib suite with compiler/target/blaise
#
# Runs from anywhere inside the repo; paths are resolved from the root.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
SRC=compiler/src/main/pascal
TGT=compiler/target
COMMON=(--rtl-src "$SRC" --unit-path "$SRC" --unit-path stdlib/src/main/pascal)

latest_release() {
  local dir
  dir=$(ls -d releases/v*/ 2>/dev/null | sort -V | tail -1)
  [ -n "$dir" ] || { echo "no releases/v*/blaise found; pass --compiler BIN" >&2; exit 1; }
  echo "${dir}blaise"
}

# build <compiler> <source> <output> [extra args...]
build() {
  local bin=$1 src=$2 out=$3; shift 3
  local uc
  uc="$(dirname "$out")/units-$(basename "$out")"
  mkdir -p "$uc"            # Blaise does not create --unit-cache itself
  echo ">> $(basename "$bin") -> $out"
  # Judge by exit code, not `[ -x ]`: access(2) misreports on an smbfs mount.
  local rc=0
  "$bin" --source "$src" --output "$out" --unit-cache "$uc" "${COMMON[@]}" "$@" \
    > "$uc.log" 2>&1 || rc=$?
  grep -a -v 'linker: note: binding' "$uc.log" | head -20 || true
  [ $rc -eq 0 ] || { echo "BUILD FAILED (exit $rc): $out"; exit 1; }
}

cmd=${1:-}; shift || true
case "$cmd" in
  compile)
    BIN=""
    [ "${1:-}" = "--compiler" ] && BIN=$2
    [ -n "$BIN" ] || BIN=$(latest_release)
    mkdir -p "$TGT"
    build "$BIN" "$SRC/Blaise.pas" "$TGT/blaise.new"
    mv "$TGT/blaise.new" "$TGT/blaise"
    ;;
  fixpoint)
    BIN=""
    INSTALL=0
    while [ $# -gt 0 ]; do
      case "$1" in
        --compiler) BIN=$2; shift 2 ;;
        --install)  INSTALL=1; shift ;;
        *) echo "unknown fixpoint option: $1" >&2; exit 1 ;;
      esac
    done
    [ -n "$BIN" ] || BIN=$(latest_release)
    W=$(mktemp -d)
    build "$BIN"         "$SRC/Blaise.pas" "$W/s1/blaise"
    build "$W/s1/blaise" "$SRC/Blaise.pas" "$W/s2/blaise"
    build "$W/s2/blaise" "$SRC/Blaise.pas" "$W/s3/blaise"
    # Same basename in different dirs: the Mach-O UUID covers the filename.
    if ! cmp "$W/s2/blaise" "$W/s3/blaise"; then
      echo "FIXPOINT FAILED: stage-2 and stage-3 differ"
      exit 1
    fi
    echo BINARY_FIXPOINT_OK
    echo "stage-2 binary: $W/s2/blaise"
    if [ $INSTALL -eq 1 ]; then
      mkdir -p "$TGT"
      cp "$W/s2/blaise" "$TGT/blaise"
      echo "installed stage-2 as $TGT/blaise"
    fi
    ;;
  test-compile)
    # Test dir BEFORE stdlib: the opposite order builds a TestRunner that
    # segfaults in TUInt64Tests (BUG-20261004-arm64-testrunner-unitpath-order).
    COMMON=(--rtl-src "$SRC" --unit-path "$SRC" --unit-path compiler/src/test/pascal
            --unit-path stdlib/src/main/pascal)
    build "$TGT/blaise" compiler/src/test/pascal/TestRunner.pas "$TGT/TestRunner"
    ;;
  test)
    "$0" test-compile
    BLAISE_PROJECT_ROOT="$ROOT/" "$TGT/TestRunner" "$@"
    ;;
  stdlib-test)
    stdlib/src/test/run-tests.sh "$ROOT/$TGT/blaise" -- "$@"
    ;;
  *)
    sed -n '2,20p' "$0"; exit 1 ;;
esac
