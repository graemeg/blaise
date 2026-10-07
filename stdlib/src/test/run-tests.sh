#!/usr/bin/env bash
# Build and run the Blaise stdlib test suite.
#
# Usage:  stdlib/src/test/run-tests.sh [blaise-binary] [-- runner-args...]
#   blaise-binary defaults to compiler/target/blaise, falling back to the
#   newest releases/v*/blaise.
#   Anything after '--' is passed to the runner (e.g. --suite TJsonTests).
set -euo pipefail

# Repo root = two levels up from this script's dir (stdlib/src/test -> repo).
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"

# Default to the newest releases/v*/blaise by version sort — the same
# selection rolling-bootstrap.sh uses.  Prefer compiler/target/blaise if it exists,
# since that is the binary you are usually iterating on.
default_blaise() {
  if [ -x "$ROOT/compiler/target/blaise" ]; then
    echo "$ROOT/compiler/target/blaise"
    return
  fi
  local newest
  newest="$(ls -d "$ROOT"/releases/v*/ 2>/dev/null | sort -V | tail -1)"
  [ -n "$newest" ] && echo "${newest}blaise"
}

BLAISE="${1:-$(default_blaise)}"
[ "${1:-}" != "" ] && shift || true

if [ -z "$BLAISE" ] || [ ! -x "$BLAISE" ]; then
  echo "run-tests.sh: no usable blaise binary (looked for compiler/target/blaise" >&2
  echo "  and the newest releases/v*/blaise); pass one explicitly." >&2
  exit 1
fi
# Drop a leading '--' separator if present.
[ "${1:-}" = "--" ] && shift || true

CACHE="$(mktemp -d)"
OUT="$CACHE/testrunner"

"$BLAISE" \
  --source "$ROOT/stdlib/src/test/pascal/testrunner.pas" \
  --output "$OUT" \
  --unit-path "$ROOT/stdlib/src/main/pascal" \
  --unit-path "$ROOT/compiler/src/main/pascal" \
  --unit-path "$ROOT/stdlib/src/test/pascal" \
  --unit-cache "$CACHE"

"$OUT" "$@"
RC=$?
rm -rf "$CACHE"
exit $RC
