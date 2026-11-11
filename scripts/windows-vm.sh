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
#                                     (its low 8 bits; the full code is on
#                                     stderr when it is not 0)
#   scripts/windows-vm.sh crosscheck  the windows fixture smoke: link the
#                                     compiler/src/it/windows/ programs (the
#                                     TPeLinkerTests and TWin64FixtureTests
#                                     fixture tests) and check their exit
#                                     codes and output in the VM
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
#              BLAISE_WINDOWS_KEY (default ~/.ssh/blaise_windows),
#              BLAISE_WINDOWS_RUN_TIMEOUT (seconds per run, default 300).
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
RUN_TIMEOUT=${BLAISE_WINDOWS_RUN_TIMEOUT:-300}

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

# win_quote <arg>: <arg> as one Windows command-line argument.  Within the
# quotes, a run of N backslashes before a quote becomes 2N+1 followed by the
# quote; before the closing quote, 2N; elsewhere backslashes are literal.
win_quote() {
  local s=$1 out='"' n=0 c i
  for ((i = 0; i < ${#s}; i++)); do
    c=${s:i:1}
    if [ "$c" = '\' ]; then
      n=$((n + 1))
    elif [ "$c" = '"' ]; then
      out+=$(printf '%*s' $((2 * n + 1)) '' | tr ' ' '\\')'"'
      n=0
    else
      [ $n -gt 0 ] && out+=$(printf '%*s' "$n" '' | tr ' ' '\\')
      out+=$c
      n=0
    fi
  done
  [ $n -gt 0 ] && out+=$(printf '%*s' $((2 * n)) '' | tr ' ' '\\')
  printf '%s"' "$out"
}

# run_in_vm <local-exe> [args]: copy into a fresh directory under
# $GUEST_DIR, run it there through scripts/windows-run.ps1, remove the
# directory, keep the exit code.  ssh passes on only its low 8 bits; the
# full code of a failing run is on standard error ("windows-vm: exit code
# 0x..."), and a run longer than $RUN_TIMEOUT seconds is killed (exit 124).
run_in_vm() {
  local exe=$1; shift
  [ -f "$exe" ] || die "no such file: $exe"
  ssh_up || die "VM not reachable: scripts/windows-vm.sh start"
  local name; name=$(basename "$exe")
  local dir="$GUEST_DIR\\run-$$-$RANDOM"
  local tmp; tmp=$(mktemp -d)
  # The command line, each argument quoted so CommandLineToArgvW gives it
  # back unchanged.
  local q="" a
  for a in "$@"; do q+="$(win_quote "$a") "; done
  printf '%s' "$q" > "$tmp/args.txt"
  vm_ssh "mkdir $dir" >/dev/null
  vm_scp "$exe" "$tmp/args.txt" scripts/windows-run.ps1 \
    "$GUEST_USER@127.0.0.1:${dir//\\//}/"
  rm -rf "$tmp"
  local rc=0
  vm_ssh "powershell -NoProfile -ExecutionPolicy Bypass -File $dir\\windows-run.ps1 -Exe $dir\\$name -TimeoutSec $RUN_TIMEOUT" || rc=$?
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
    # link_fixture <exe> <test>: the fixture test writes $OUT/<exe>
    link_fixture() {
      echo ">> linking $OUT/$1 ($2)"
      rm -f "$OUT/$1"
      compiler/target/TestRunner --suite "$2" >/dev/null \
        || die "fixture link test failed: compiler/target/TestRunner --suite $2"
      [ -f "$OUT/$1" ] || die "$2 did not write $OUT/$1"
    }
    link_fixture exit42.exe TPeLinkerTests.TestLink_Exit42Fixture
    # the Blaise programs: <name>:<fixture test>, each checked against
    # compiler/src/it/windows/<name>.expected
    progs="m2calls:TWin64FixtureTests.TestLink_M2Calls m3tls:TWin64FixtureTests.TestLink_M3Tls m3callback:TWin64FixtureTests.TestLink_M3Callback"
    for p in $progs; do link_fixture "${p%%:*}.exe" "${p#*:}"; done
    # the programs built from the command line, with the Windows runtime
    [ -x compiler/target/blaise ] || die "build compiler/target/blaise first"
    xbuild() {
      echo ">> cross-compiling $1 -> $2.exe (windows-x86_64)"
      compiler/target/blaise --source "$1" --target windows-x86_64 \
        --output "$2" --unit-path stdlib/src/main/pascal \
        --rtl-src compiler/src/main/pascal > "$2.log" 2>&1 \
        || { grep -v 'note:' "$2.log" | head -20; die "CROSS BUILD FAILED: $1"; }
    }
    xbuild compiler/src/it/windows/m3rtl.pas "$OUT/m3rtl"
    xbuild compiler/src/it/windows/m3fault.pas "$OUT/m3fault"
    fail=0
    echo "=== exit42 ==="
    rc=0
    run_in_vm "$OUT/exit42.exe" 2>/dev/null || rc=$?
    echo "exit $rc"
    [ $rc -eq 42 ] || { echo "FAIL: exit42.exe exited $rc, want 42"; fail=1; }
    for p in $progs; do
      name=${p%%:*}
      echo "=== $name ==="
      rc=0
      got=$(run_in_vm "$OUT/$name.exe" | tr -d '\r') || rc=$?
      echo "$got"
      if [ $rc -ne 0 ] || [ "$got" != "$(cat "compiler/src/it/windows/$name.expected")" ]; then
        echo "FAIL: $name.exe exit $rc, output differs from $name.expected"; fail=1
      fi
    done
    echo "=== m3rtl ==="
    rc=0
    got=$(run_in_vm "$OUT/m3rtl.exe" | tr -d '\r') || rc=$?
    echo "$got"
    if [ $rc -ne 0 ] || [ "$got" != "$(cat compiler/src/it/windows/m3rtl.expected)" ]; then
      echo "FAIL: m3rtl.exe exit $rc, output differs from m3rtl.expected"; fail=1
    fi
    # D7: a fault is reported and its NTSTATUS code is the exit code
    for f in "nil:access violation:0xC0000005" \
             "div:integer division by zero:0xC0000094" \
             "stack:stack overflow:0xC00000FD"; do
      mode=${f%%:*}; rest=${f#*:}; what=${rest%%:*}; code=${rest#*:}
      echo "=== m3fault $mode ==="
      err=$(run_in_vm "$OUT/m3fault.exe" "$mode" 2>&1 >/dev/null | tr -d '\r') || true
      echo "$err"
      case "$err" in
        *"Runtime error: $what ($code)"*"exit code $code"*) ;;
        *) echo "FAIL: m3fault $mode, want '$what' and exit code $code"; fail=1 ;;
      esac
    done
    [ $fail -eq 0 ] || exit 1
    echo "WINDOWS_CROSSCHECK_OK"
    ;;
  *)
    sed -n '2,38p' "$0"; exit 1 ;;
esac
