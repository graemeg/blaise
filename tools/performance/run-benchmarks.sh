#!/usr/bin/env bash
#
# Reproducible codegen benchmark for the native backend.
#
# Two things are measured:
#   A. COMPILE TIME  — how fast the compiler self-compiles Blaise.pas
#                      (--emit-asm), plus valgrind instruction counts
#                      (deterministic).
#   B. RUNTIME       — how fast the GENERATED CODE runs (bench_fib, bench_loop,
#                      bench_calls compiled, then executed).
#
# Runtime (B) is the number that reflects codegen QUALITY / optimisation.
# Compile time (A) is dominated by the shared front end (parse+semantic+ARC).
#
# Usage (from the project root):
#   tools/performance/run-benchmarks.sh            # runtime only (fast)
#   tools/performance/run-benchmarks.sh --full     # + compile-time + callgrind
#
# Requires: a current native-built compiler at compiler/target/blaise, and for
# --full: valgrind.  Append the printed numbers to perf-optimisation-results.txt.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

BLAISE="compiler/target/blaise"
HERE="tools/performance"
UP=(--unit-path compiler/src/main/pascal
    --unit-path stdlib/src/main/pascal)
FULL=0
[ "${1:-}" = "--full" ] && FULL=1

[ -x "$BLAISE" ] || { echo "error: $BLAISE not found — build it first" >&2; exit 1; }

echo "=== host ==="
echo "CPU:    $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs)"
echo "Kernel: $(uname -sr)"
echo "Commit: $(git rev-parse --short HEAD 2>/dev/null || echo '?')"
echo "Binary: $("$BLAISE" --help 2>/dev/null | head -1)"
echo

# best_of_3 <label> <command...>  — prints the min wall time of 3 runs.
best_of_3() {
  local label="$1"; shift
  local best="" t
  for _ in 1 2 3; do
    t=$( { /usr/bin/time -f "%e" "$@" >/dev/null; } 2>&1 )
    if [ -z "$best" ] || awk "BEGIN{exit !($t < $best)}"; then best="$t"; fi
  done
  printf '  %-34s %ss\n' "$label" "$best"
}

# ---- B. RUNTIME OF GENERATED CODE ------------------------------------------
echo "=== B. RUNTIME of generated code (best of 3) ==="
for prog in bench_fib bench_loop bench_calls; do
  "$BLAISE" --source "$HERE/$prog.pas" --output "/tmp/${prog}_native" "${UP[@]}" >/dev/null
  echo "  $prog output: $(/tmp/${prog}_native)"
  best_of_3 "$prog  native" "/tmp/${prog}_native"
done
echo

[ "$FULL" -eq 1 ] || { echo "(run with --full for compile-time + instruction counts)"; exit 0; }

# ---- A. COMPILE TIME -------------------------------------------------------
echo "=== A. COMPILE TIME — self-compile of Blaise.pas (best of 3) ==="
SRC=(--source compiler/src/main/pascal/Blaise.pas)
best_of_3 "parse+semantic (--dump-ast)" "$BLAISE" "${SRC[@]}" "${UP[@]}" --dump-ast
best_of_3 "native codegen (--emit-asm)" "$BLAISE" "${SRC[@]}" "${UP[@]}" --emit-asm
echo

if command -v valgrind >/dev/null 2>&1; then
  echo "=== instruction counts (valgrind callgrind — ~3-4 min each) ==="
  for pair in "native:--emit-asm"; do
    name="${pair%%:*}"; flag="${pair##*:}"
    valgrind --tool=callgrind --callgrind-out-file="/tmp/cg_${name}.out" \
      "$BLAISE" "${SRC[@]}" "${UP[@]}" "$flag" >/dev/null 2>"/tmp/vg_${name}.log"
    ir=$(grep -oE 'I   refs:[ ,0-9]+' "/tmp/vg_${name}.log" | grep -oE '[0-9,]+' | tr -d ,)
    printf '  %-12s Ir = %s\n' "$name" "$ir"
  done
fi
