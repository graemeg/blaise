#!/bin/bash
# linux-vm.sh — run the Linux x86-64 build and test suites from a Mac, in an
# OrbStack Linux machine (x86-64 under Rosetta).  Gives a ~5 minute local
# Linux run instead of a CI round trip.
#
#   scripts/linux-vm.sh setup         create the machine (if absent), install
#                                     packages + PasBuild, clone the repo
#   scripts/linux-vm.sh seed          cross-compile a linux-x86_64 blaise with
#                                     compiler/target/blaise and copy it in
#   scripts/linux-vm.sh sync          reset the VM clone to this repo's HEAD
#                                     (COMMITTED state only)
#   scripts/linux-vm.sh build         build the compiler with the seed, then
#                                     the test runner with that stage-2 compiler
#   scripts/linux-vm.sh test [args]   run the compiler suite (TestRunner args,
#                                     e.g. --suite TE2ENativeTests)
#   scripts/linux-vm.sh stdlib-test [args]
#                                     build and run the stdlib suite
#   scripts/linux-vm.sh all           seed + sync + build + test + stdlib-test
#   scripts/linux-vm.sh shell         interactive shell in the VM clone
#
# The VM works in its own clone (~/blaise on the VM's disk) so Linux builds
# never overwrite this tree's compiler/target/.  Requires OrbStack (`orb`).
#
# Known emulation artefact: TLinkerE2ETests.TestRun_SyscallHelloWorld fails
# under Rosetta (its hand-assembled binary has an empty second PT_LOAD, which
# Rosetta's loader rejects); it passes on real Linux.
#
# Environment: BLAISE_VM (machine name, default blaise-x86),
#              PASBUILD_VERSION (default 1.9.0).
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
VM=${BLAISE_VM:-blaise-x86}
PB_VERSION=${PASBUILD_VERSION:-1.9.0}
SRC=compiler/src/main/pascal
SEED_DIR=compiler/target/linux-seed

command -v orb >/dev/null || { echo "OrbStack (orb) not found: brew install orbstack" >&2; exit 1; }

# vm <shell command>: run in the VM, from the clone when it exists
vm() { orb -m "$VM" bash -c "set -euo pipefail; cd ~/blaise 2>/dev/null || cd ~; $1"; }

cmd=${1:-}; shift || true
case "$cmd" in
  setup)
    if ! orb list 2>/dev/null | grep -q "^$VM "; then
      echo ">> creating $VM (ubuntu:noble, amd64)"
      orb create --arch amd64 ubuntu:noble "$VM"
    fi
    echo ">> installing packages"
    vm "sudo apt-get update -qq >/dev/null && sudo DEBIAN_FRONTEND=noninteractive \
        apt-get install -y -qq build-essential unzip curl git libssl-dev >/dev/null"
    echo ">> installing PasBuild $PB_VERSION"
    vm "curl -fsSL -o /tmp/pb.zip https://github.com/graemeg/PasBuild/releases/download/v$PB_VERSION/pasbuild-$PB_VERSION-x86_64-linux.zip \
        && rm -rf /tmp/pb && unzip -o -q /tmp/pb.zip -d /tmp/pb \
        && sudo install -m 0755 \"\$(find /tmp/pb -type f -name pasbuild | head -1)\" /usr/local/bin/pasbuild \
        && pasbuild --version | head -1"
    echo ">> cloning $ROOT into the VM"
    vm "[ -d ~/blaise/.git ] || git clone -q '$ROOT' ~/blaise; mkdir -p ~/seed"
    echo "setup done; next: scripts/linux-vm.sh all"
    ;;
  seed)
    [ -x compiler/target/blaise ] || { echo "build compiler/target/blaise first (scripts/macos-dev.sh compile)" >&2; exit 1; }
    mkdir -p "$SEED_DIR/units"
    echo ">> cross-compiling a linux-x86_64 seed"
    rc=0
    compiler/target/blaise --source "$SRC/Blaise.pas" --target linux-x86_64 \
      --output "$SEED_DIR/blaise" --unit-cache "$SEED_DIR/units" \
      --rtl-src "$SRC" --unit-path "$SRC" --unit-path stdlib/src/main/pascal \
      > "$SEED_DIR/build.log" 2>&1 || rc=$?
    grep -a -v 'linker: note: binding' "$SEED_DIR/build.log" | grep -a -v 'stale vs\|compiled by' | head -20 || true
    [ $rc -eq 0 ] || { echo "SEED BUILD FAILED (exit $rc)"; exit 1; }
    vm "mkdir -p ~/seed && cp '$ROOT/$SEED_DIR/blaise' ~/seed/blaise && ~/seed/blaise --help | head -1"
    ;;
  sync)
    if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
      echo "note: uncommitted changes are NOT synced -- the VM tests HEAD" >&2
    fi
    vm "git fetch -q '$ROOT' HEAD && git reset -q --hard FETCH_HEAD && git log --oneline -1"
    ;;
  build)
    vm "pasbuild compile -m blaise-compiler --compiler ~/seed/blaise | grep -E 'BUILD|ERROR' \
        && cp compiler/target/blaise ~/seed/blaise-s2 \
        && pasbuild test-compile -m blaise-compiler --compiler ~/seed/blaise-s2 | grep -E 'BUILD|ERROR'"
    ;;
  test)
    vm "BLAISE_TEST_COMPILER=\$HOME/seed/blaise-s2 compiler/target/TestRunner $*"
    ;;
  stdlib-test)
    vm "pasbuild test-compile -m blaise-stdlib --compiler ~/seed/blaise-s2 | grep -E 'BUILD|ERROR' \
        && stdlib/target/TestRunner $*"
    ;;
  all)
    "$0" seed
    "$0" sync
    "$0" build
    rc=0
    "$0" test || rc=$?
    "$0" stdlib-test || rc=$?
    exit $rc
    ;;
  shell)
    orb -m "$VM" bash -c "cd ~/blaise && exec bash -l"
    ;;
  *)
    sed -n '2,31p' "$0"; exit 1 ;;
esac
