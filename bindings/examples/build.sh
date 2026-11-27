#!/bin/sh
# Build every example against the committed bindings.  Run from this
# directory.  Binaries land in ./target/.
set -e
ROOT=../..
BLAISE=$ROOT/compiler/target/blaise
[ -x "$BLAISE" ] || { echo "build the compiler first (pasbuild compile -m blaise-compiler)"; exit 1; }
mkdir -p target
for src in *.pas; do
    name=${src%.pas}
    echo "building $name"
    "$BLAISE" --source "$src" --output "target/$name" \
        --target linux-x86_64 \
        --unit-path "$ROOT/bindings/src/main/pascal" \
        --unit-path "$ROOT/stdlib/src/main/pascal"
done
echo "done — binaries in ./target/"
