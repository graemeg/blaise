#!/usr/bin/env bash
# Native fixpoint test for the Blaise self-hosting check.
#
# Verifies that the native backend (--backend native) is fully
# self-hosting: a native-compiled compiler can recompile itself
# with --backend native and produce identical assembly.
#
# Steps:
#   1. Find the QBE-compiled compiler (compiler/target/blaise).
#   2. stage-1: QBE-compiled compiler emits native assembly.
#   3. Link stage-1 binary.
#   4. stage-2: stage-1 native binary emits native assembly.
#   5. Link stage-2 binary.
#   6. stage-3: stage-2 native binary emits native assembly.
#   7. diff stage-2.s stage-3.s  => empty = clean fixpoint.
#
# Requires: compiler/target/blaise must already be built (run the QBE fixpoint
# or pasbuild compile first).  The RTL is source-built via
# scripts/build-rtl-objects.sh — no blaise_rtl.a archive is involved.

set -e

if [ ! -f "compiler/src/main/pascal/Blaise.pas" ]; then
  echo "Run this script from the project root: ./scripts/fixpoint-native.sh" >&2
  exit 1
fi

COMPILER="${1:-compiler/target/blaise}"
if [ ! -x "$COMPILER" ]; then
  echo "Compiler not found: $COMPILER" >&2
  echo "Build it first: pasbuild compile -m blaise-compiler --compiler ..." >&2
  exit 10
fi

# RTL is built from source (no archive).  The --emit-asm dump inlines the RTL
# units the compiler uses, so link with --exclude-defined-by to skip supplying
# those a second time.
RTL_OBJDIR=/tmp/fpn_rtl_obj
# Absolute path WITHOUT `readlink -f`: -f is GNU-only and BSD/macOS readlink
# does not have it, which made this script fail there before it did anything.
# cd+pwd is POSIX and needs no coreutils.
ABS_COMPILER="$(cd "$(dirname "$COMPILER")" && pwd)/$(basename "$COMPILER")"

link_stage() {
  # $1 = program .s, $2 = output binary
  local prog_s="$1" out_bin="$2" prog_o rtl_objs
  prog_o="${prog_s%.s}.o"
  gcc -c -o "$prog_o" "$prog_s" 2>/tmp/fpn_cc.err || return 2
  rm -rf "$RTL_OBJDIR"
  rtl_objs=$(scripts/build-rtl-objects.sh "$ABS_COMPILER" "$RTL_OBJDIR" \
               --exclude-defined-by "$prog_o") || return 11
  gcc -o "$out_bin" "$prog_o" $rtl_objs -lm -lpthread 2>/tmp/fpn_gcc.err || return 2
  return 0
}

UNIT_ARGS="--unit-path compiler/src/main/pascal --unit-path runtime/src/main/pascal --unit-path stdlib/src/main/pascal"
SRC="--source compiler/src/main/pascal/Blaise.pas"

echo "stage-0: $COMPILER"

echo "[1/6] stage-0 -> stage-1 assembly (native)"
"$COMPILER" $SRC $UNIT_ARGS --backend native --emit-asm > /tmp/fpn_stage1.s 2>/tmp/fpn_stage1.err
if [ ! -s /tmp/fpn_stage1.s ]; then
  echo "STAGE1_ASM_FAIL"; head -3 /tmp/fpn_stage1.err; exit 1
fi
echo "      stage-1 asm: $(wc -l < /tmp/fpn_stage1.s) lines"

echo "[2/6] link stage-1 binary"
link_stage /tmp/fpn_stage1.s /tmp/fpn_blaise1 || {
  echo "GCC1_FAIL"; cat /tmp/fpn_gcc.err 2>/dev/null; cat /tmp/fpn_cc.err 2>/dev/null; exit 2;
}

echo "[3/6] stage-1 -> stage-2 assembly (native, 5min timeout)"
timeout 300 /tmp/fpn_blaise1 $SRC $UNIT_ARGS --backend native --emit-asm > /tmp/fpn_stage2.s 2>/tmp/fpn_stage2.err
RC=$?
if [ $RC -eq 124 ]; then echo "STAGE2_TIMEOUT"; exit 4
elif [ $RC -eq 139 ]; then echo "STAGE2_SEGFAULT"; exit 4
elif [ $RC -ne 0 ]; then echo "STAGE2_FAIL rc=$RC"; head -3 /tmp/fpn_stage2.err; exit 5
fi
echo "      stage-2 asm: $(wc -l < /tmp/fpn_stage2.s) lines"

echo "[4/6] link stage-2 binary"
link_stage /tmp/fpn_stage2.s /tmp/fpn_blaise2 || {
  echo "GCC2_FAIL"; cat /tmp/fpn_gcc.err 2>/dev/null; cat /tmp/fpn_cc.err 2>/dev/null; exit 2;
}

echo "[5/6] stage-2 -> stage-3 assembly (native, 5min timeout)"
timeout 300 /tmp/fpn_blaise2 $SRC $UNIT_ARGS --backend native --emit-asm > /tmp/fpn_stage3.s 2>/tmp/fpn_stage3.err
RC=$?
if [ $RC -eq 124 ]; then echo "STAGE3_TIMEOUT"; exit 4
elif [ $RC -eq 139 ]; then echo "STAGE3_SEGFAULT"; exit 4
elif [ $RC -ne 0 ]; then echo "STAGE3_FAIL rc=$RC"; head -3 /tmp/fpn_stage3.err; exit 5
fi
echo "      stage-3 asm: $(wc -l < /tmp/fpn_stage3.s) lines"

echo "[6/6] compare stage-2 vs stage-3"
DIFFLINES=$(diff /tmp/fpn_stage2.s /tmp/fpn_stage3.s | wc -l)
if [ $DIFFLINES -eq 0 ]; then
  echo "NATIVE_FIXPOINT_OK"
  exit 0
fi

echo "stage-2 != stage-3 ($DIFFLINES diff lines)"
diff /tmp/fpn_stage2.s /tmp/fpn_stage3.s | head -20
exit 6
