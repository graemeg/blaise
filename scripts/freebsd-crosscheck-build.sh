#!/usr/bin/env bash
#
# Cross-compile the FreeBSD emulation-check fixtures (compiler/src/it/freebsd/*.pas)
# with --target freebsd-x86_64 on a Linux host.  The resulting static, freestanding
# FreeBSD ET_EXEC binaries are then run inside a FreeBSD VM (see the freebsd-crosscheck
# job in .github/workflows/bootstrap.yml) to validate the FreeBSD syscall leaf and
# struct-stat layout that host-side static ELF checks cannot catch.
#
# Usage:
#   BLAISE=/path/to/blaise scripts/freebsd-crosscheck-build.sh [OUTDIR]
#
# BLAISE   path to a native-backend blaise binary that supports --target
#          freebsd-x86_64 (defaults to compiler/target/blaise).
# OUTDIR   where to write the cross-compiled binaries (defaults to
#          target/freebsd-crosscheck).
#
# The binaries CANNOT run on the Linux host (FreeBSD syscall numbers/ABI); this
# script only builds and sanity-checks the emitted ELF shape.  Prints
# FREEBSD_CROSSBUILD_OK on success.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

BLAISE="${BLAISE:-compiler/target/blaise}"
OUTDIR="${1:-target/freebsd-crosscheck}"
FIXDIR="compiler/src/it/freebsd"

if [ ! -x "$BLAISE" ]; then
  echo "error: blaise binary not found or not executable: $BLAISE" >&2
  exit 1
fi

mkdir -p "$OUTDIR"

# The compiler resolves the RTL source relative to its own binary;
# the RTL source lives in the compiler tree.  Both unit paths mirror the normal
# native build.
UNIT_ARGS=(
  --unit-path runtime/src/main/pascal
  --unit-path stdlib/src/main/pascal
)

for src in "$FIXDIR"/*.pas; do
  name="$(basename "$src" .pas)"
  out="$OUTDIR/$name"
  echo "cross-compiling $src -> $out (freebsd-x86_64)"
  "$BLAISE" \
    --source "$src" \
    --backend native \
    --target freebsd-x86_64 \
    --output "$out" \
    "${UNIT_ARGS[@]}"

  # Sanity-check the emitted ELF is a FreeBSD (EI_OSABI=9) ET_EXEC.  readelf is
  # part of binutils, always present on the Linux runner.
  osabi="$(readelf -hW "$out" | awk -F: '/OS\/ABI/ {print $2}' | xargs)"
  etype="$(readelf -hW "$out" | awk -F: '/Type:/ {print $2}' | awk '{print $1}')"
  case "$osabi" in
    *FreeBSD*) : ;;
    *) echo "error: $out is not a FreeBSD binary (OS/ABI=$osabi)" >&2; exit 1 ;;
  esac
  if [ "$etype" != "EXEC" ]; then
    echo "error: $out is not a static ET_EXEC (Type=$etype)" >&2
    exit 1
  fi
done

# Drop the .o intermediates the compiler leaves beside each output, so the VM
# job can run every executable in OUTDIR without tripping over object files.
rm -f "$OUTDIR"/*.o

echo "FREEBSD_CROSSBUILD_OK"
