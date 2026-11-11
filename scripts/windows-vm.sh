#!/bin/bash
# windows-vm.sh — run windows-x86_64 binaries from a Mac, in a local
# Windows 11 ARM64 guest under UTM.  Windows on ARM runs x64 executables
# through its built-in emulation, so this is a local run instead of a CI
# round trip.
#
#   scripts/windows-vm.sh start       boot the VM and
#                                     wait until ssh answers
#   scripts/windows-vm.sh stop        shut Windows down, then power off
#   scripts/windows-vm.sh status      is it running, does ssh answer
#   scripts/windows-vm.sh ssh [cmd]   shell (or one cmd.exe command) in the VM
#   scripts/windows-vm.sh run <exe> [args]
#                                     copy a local executable in and run it;
#                                     exits with the executable's exit code
#   scripts/windows-vm.sh crosscheck  the windows fixture smoke: link
#                                     compiler/src/it/windows/exit42.s through
#                                     the PE linker (TPeLinkerTests) and check
#                                     that it exits 42 in the VM
#
# stdlib-test and selfhost arrive with the milestones that make them
# possible (design: windows-x86_64-backend-design.adoc, M3 and M7).
#
# The guest is installed once by hand (design, "Development-host setup"):
# a UTM VM running Windows 11 ARM64 with the UTM guest tools, the OpenSSH
# server, an inbound TCP 22 firewall rule, the key below in
# C:\ProgramData\ssh\administrators_authorized_keys, the Windows Error
# Reporting dialog disabled, and a Defender exclusion for $GUEST_DIR.  Its
# network is Emulated VLAN with host 127.0.0.1:$PORT forwarded to guest 22.
# The VM may live anywhere, an NFS share included; UTM finds it by name.
#
# Environment: BLAISE_WINDOWS_VM (UTM VM name, default blaise-win11),
#              BLAISE_WINDOWS_SSH_PORT (default 2222),
#              BLAISE_WINDOWS_USER (default blaise),
#              BLAISE_WINDOWS_KEY (default ~/.ssh/blaise_windows).
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
VM=${BLAISE_WINDOWS_VM:-blaise-win11}
PORT=${BLAISE_WINDOWS_SSH_PORT:-2222}
GUEST_USER=${BLAISE_WINDOWS_USER:-blaise}
KEY=${BLAISE_WINDOWS_KEY:-$HOME/.ssh/blaise_windows}
UTMCTL=${UTMCTL:-/Applications/UTM.app/Contents/MacOS/utmctl}
# Excluded from Defender real-time scanning; every run gets its own
# subdirectory so concurrent runs of same-named executables cannot collide.
GUEST_DIR='C:\blaise-test'
OUT=compiler/target/it/windows

die() { echo "$*" >&2; exit 1; }
[ -x "$UTMCTL" ] || die "utmctl not found at $UTMCTL: brew install --cask utm"
[ -f "$KEY" ] || die "no ssh key at $KEY (see the header for the guest setup)"

SSH_OPTS=(-i "$KEY" -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null
          -o LogLevel=ERROR -o ConnectTimeout=10 -o ServerAliveInterval=30
          -o BatchMode=yes)
vm_ssh() { ssh "${SSH_OPTS[@]}" -p "$PORT" "$GUEST_USER@127.0.0.1" "$@"; }
vm_scp() { scp -q "${SSH_OPTS[@]}" -P "$PORT" "$@"; }

vm_status() { "$UTMCTL" status "$VM" 2>/dev/null || echo unknown; }
running() { [ "$(vm_status)" = started ]; }
ssh_up() { vm_ssh -o ConnectTimeout=5 "exit 0" >/dev/null 2>&1; }

# wait_ssh <timeout-seconds>: poll until ssh answers; report the boot time
wait_ssh() {
  local limit=$1 t0=$SECONDS
  echo ">> waiting for ssh on 127.0.0.1:$PORT"
  until ssh_up; do
    running || die "VM $VM stopped during boot (status: $(vm_status))"
    [ $((SECONDS - t0)) -lt "$limit" ] || die "ssh not up after ${limit}s"
    sleep 5
  done
  echo ">> ssh up after $((SECONDS - t0))s"
}

start_vm() {
  if running; then echo "already running"; return; fi
  echo ">> starting $VM"
  "$UTMCTL" start "$VM"
}

stop_vm() {
  running || { echo "not running (status: $(vm_status))"; return; }
  echo ">> shutting Windows down"
  vm_ssh "shutdown /s /t 0" >/dev/null 2>&1 || "$UTMCTL" stop --request "$VM" || true
  for _ in $(seq 1 60); do running || break; sleep 2; done
  if running; then echo ">> still up after 120s, powering off"; "$UTMCTL" stop --force "$VM"; fi
}

# run_in_vm <local-exe> [args]: copy into a fresh directory under
# $GUEST_DIR, run it there, remove the directory, keep the exit code.
run_in_vm() {
  local exe=$1; shift
  [ -f "$exe" ] || die "no such file: $exe"
  ssh_up || die "VM not reachable: scripts/windows-vm.sh start"
  local name; name=$(basename "$exe")
  local dir="$GUEST_DIR\\run-$$-$RANDOM"
  vm_ssh "mkdir $dir" >/dev/null
  vm_scp "$exe" "$GUEST_USER@127.0.0.1:${dir//\\//}/$name"
  # cmd.exe is the guest's login shell: double-quote each argument.
  local q="" a
  for a in "$@"; do q+=" \"$a\""; done
  local rc=0
  vm_ssh "cd /d $dir && $name$q" || rc=$?
  vm_ssh "cd /d $GUEST_DIR && rmdir /s /q $dir" >/dev/null 2>&1 || true
  return $rc
}

cmd=${1:-}; shift || true
case "$cmd" in
  start)
    start_vm
    wait_ssh 600
    ;;
  stop)
    stop_vm
    ;;
  status)
    st=$(vm_status)
    if [ "$st" = started ]; then
      echo "running"
      if ssh_up; then vm_ssh "ver"; else echo "ssh not answering (yet) on 127.0.0.1:$PORT"; fi
    else
      echo "not running (status: $st)"; exit 1
    fi
    ;;
  ssh)
    if [ $# -eq 0 ]; then vm_ssh; else vm_ssh "$*"; fi
    ;;
  run)
    [ $# -ge 1 ] || die "usage: scripts/windows-vm.sh run <local-exe> [args]"
    run_in_vm "$@"
    ;;
  crosscheck)
    [ -x compiler/target/TestRunner ] || die "build the test runner first (scripts/macos-dev.sh test-compile)"
    echo ">> linking $OUT/exit42.exe (TPeLinkerTests.TestLink_Exit42Fixture)"
    rm -f "$OUT/exit42.exe"
    compiler/target/TestRunner --suite TPeLinkerTests.TestLink_Exit42Fixture >/dev/null \
      || die "fixture link test failed: compiler/target/TestRunner --suite TPeLinkerTests"
    [ -f "$OUT/exit42.exe" ] || die "fixture link test did not write $OUT/exit42.exe"
    echo "=== exit42 ==="
    rc=0
    run_in_vm "$OUT/exit42.exe" || rc=$?
    [ $rc -eq 42 ] || die "FAIL: exit42.exe exited $rc, want 42"
    echo "exit 42"
    echo "WINDOWS_CROSSCHECK_OK"
    ;;
  *)
    sed -n '2,34p' "$0"; exit 1 ;;
esac
