#!/bin/bash
# freebsd-vm.sh — run freebsd-x86_64 cross-compiled binaries from a Mac, in a
# local FreeBSD 14.x amd64 VM under QEMU (TCG emulation on Apple Silicon:
# slow, but a local run instead of a freebsd-crosscheck CI round trip).
#
#   scripts/freebsd-vm.sh setup       download the official BASIC-CLOUDINIT
#                                     image, generate an ssh key + NoCloud
#                                     seed ISO, create an overlay disk and
#                                     boot it until ssh answers
#   scripts/freebsd-vm.sh start       boot the VM (headless, daemonised)
#   scripts/freebsd-vm.sh stop        shut the VM down (poweroff, then kill)
#   scripts/freebsd-vm.sh status      is it running, does ssh answer
#   scripts/freebsd-vm.sh ssh [cmd]   shell (or one command) in the VM
#   scripts/freebsd-vm.sh run <binary> [args]
#                                     copy a local binary in and run it;
#                                     exits with the binary's exit code
#   scripts/freebsd-vm.sh stdlib-test [args]
#                                     cross-compile the stdlib TestRunner with
#                                     compiler/target/blaise and run it in the
#                                     VM (TestRunner args, e.g. --verbose or
#                                     --suite TJsonTests)
#   scripts/freebsd-vm.sh crosscheck  the CI freebsd-crosscheck fixture smoke:
#                                     cross-build compiler/src/it/freebsd/*.pas
#                                     and check their output in the VM
#   scripts/freebsd-vm.sh destroy     stop the VM and delete its overlay disk
#                                     (the downloaded base image is kept)
#
# Everything large lives in $BLAISE_FREEBSD_VM_DIR (default
# ~/.cache/blaise-freebsd-vm), never in the repo.  The base image is never
# written to: the VM boots a qcow2 overlay on top of it, so `destroy` +
# `setup` gives a fresh guest without another download.
#
# Needs qemu-system-x86_64 + qemu-img (brew install qemu) and hdiutil (macOS)
# or xorriso/mkisofs/genisoimage (elsewhere) for the seed ISO.  Binaries need
# FreeBSD 14 or newer: dynamic ones call __libc_start1.  The guest login is
# the image's default `freebsd` user (passwordless doas/sudo is not set up;
# nothing here needs root).
#
# Environment: FREEBSD_RELEASE (default 14.3), BLAISE_FREEBSD_VM_DIR,
#              BLAISE_FREEBSD_SSH_PORT (host port forwarded to guest 22,
#              default 2223), BLAISE_FREEBSD_CPUS (default 4),
#              BLAISE_FREEBSD_MEM (MiB, default 4096).
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
REL=${FREEBSD_RELEASE:-14.3}
DIR=${BLAISE_FREEBSD_VM_DIR:-$HOME/.cache/blaise-freebsd-vm}
PORT=${BLAISE_FREEBSD_SSH_PORT:-2223}
CPUS=${BLAISE_FREEBSD_CPUS:-4}
MEM=${BLAISE_FREEBSD_MEM:-4096}
SRC=compiler/src/main/pascal
OUT=compiler/target/freebsd-vm
GUEST_USER=freebsd
GUEST_DIR=/tmp/blaise-run

IMG_NAME="FreeBSD-$REL-RELEASE-amd64-BASIC-CLOUDINIT-ufs.qcow2"
BASE="$DIR/$IMG_NAME"
DISK="$DIR/disk.qcow2"
SEED="$DIR/seed.iso"
KEY="$DIR/id_ed25519"
PIDFILE="$DIR/qemu.pid"
CONSOLE="$DIR/console.log"
MONITOR="$DIR/monitor.sock"
# Current releases live on download.freebsd.org; older ones move to the
# archive once superseded, so try both.
MIRRORS=(
  "https://download.freebsd.org/releases/VM-IMAGES/$REL-RELEASE/amd64/Latest"
  "http://ftp-archive.freebsd.org/pub/FreeBSD-Archive/old-releases/VM-IMAGES/$REL-RELEASE/amd64/Latest"
)

die() { echo "$*" >&2; exit 1; }
command -v qemu-system-x86_64 >/dev/null || die "qemu-system-x86_64 not found: brew install qemu"

SSH_OPTS=(-i "$KEY" -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null
          -o LogLevel=ERROR -o ConnectTimeout=10 -o ServerAliveInterval=30)
vm_ssh() { ssh "${SSH_OPTS[@]}" -p "$PORT" "$GUEST_USER@localhost" "$@"; }
vm_scp() { scp -q "${SSH_OPTS[@]}" -P "$PORT" "$@"; }

running() { [ -f "$PIDFILE" ] && kill -0 "$(cat "$PIDFILE")" 2>/dev/null; }
ssh_up() { vm_ssh -o ConnectTimeout=5 -o BatchMode=yes true >/dev/null 2>&1; }

# wait_ssh <timeout-seconds>: poll until ssh answers; report the boot time
wait_ssh() {
  local limit=$1 t0=$SECONDS
  echo ">> waiting for ssh on localhost:$PORT (console: $CONSOLE)"
  until ssh_up; do
    running || die "QEMU exited during boot; see $CONSOLE"
    [ $((SECONDS - t0)) -lt "$limit" ] || die "ssh not up after ${limit}s; see $CONSOLE"
    sleep 5
  done
  echo ">> ssh up after $((SECONDS - t0))s"
}

make_seed() {
  [ -f "$KEY" ] || ssh-keygen -q -t ed25519 -N '' -C blaise-freebsd-vm -f "$KEY"
  local d="$DIR/seed"
  rm -rf "$d" "$SEED"; mkdir -p "$d"
  printf 'instance-id: blaise-freebsd-vm\nlocal-hostname: blaise-freebsd\n' > "$d/meta-data"
  # FreeBSD's nuageinit: top-level ssh_authorized_keys go to the default
  # `freebsd` user.
  printf '#cloud-config\nssh_authorized_keys:\n  - %s\n' "$(cat "$KEY.pub")" > "$d/user-data"
  if command -v hdiutil >/dev/null; then
    hdiutil makehybrid -quiet -iso -joliet -default-volume-name cidata -o "$SEED" "$d"
  elif command -v xorriso >/dev/null; then
    xorriso -as mkisofs -quiet -V cidata -J -r -o "$SEED" "$d"
  else
    local mk; mk=$(command -v genisoimage || command -v mkisofs) || die "no ISO tool (hdiutil/xorriso/genisoimage)"
    "$mk" -quiet -V cidata -J -r -o "$SEED" "$d"
  fi
}

start_vm() {
  if running; then echo "already running (pid $(cat "$PIDFILE"))"; return; fi
  [ -f "$DISK" ] || die "no VM disk: run scripts/freebsd-vm.sh setup"
  rm -f "$MONITOR"
  : > "$CONSOLE"
  echo ">> booting FreeBSD $REL ($CPUS cpus, ${MEM}M, TCG) -- ssh localhost:$PORT"
  qemu-system-x86_64 \
    -machine q35 -accel tcg,thread=multi -cpu max -smp "$CPUS" -m "$MEM" \
    -drive file="$DISK",if=virtio,format=qcow2 \
    -drive file="$SEED",media=cdrom,readonly=on \
    -netdev user,id=net0,hostfwd=tcp:127.0.0.1:"$PORT"-:22 \
    -device virtio-net-pci,netdev=net0 \
    -display none -serial file:"$CONSOLE" \
    -monitor unix:"$MONITOR",server,nowait \
    -pidfile "$PIDFILE" -daemonize
}

stop_vm() {
  running || { echo "not running"; rm -f "$PIDFILE"; return; }
  local pid; pid=$(cat "$PIDFILE")
  echo ">> powering off"
  # The guest user is not root, so ask QEMU for an ACPI power button press.
  if [ -S "$MONITOR" ]; then
    printf 'system_powerdown\n' | nc -U "$MONITOR" >/dev/null 2>&1 || true
  fi
  for _ in $(seq 1 60); do kill -0 "$pid" 2>/dev/null || break; sleep 2; done
  if kill -0 "$pid" 2>/dev/null; then echo ">> still up after 120s, killing"; kill "$pid"; fi
  rm -f "$PIDFILE" "$MONITOR"
}

# run_in_vm <local-binary> [args]: copy in, run from $GUEST_DIR, keep rc
run_in_vm() {
  local bin=$1; shift
  [ -f "$bin" ] || die "no such file: $bin"
  ssh_up || die "VM not reachable: scripts/freebsd-vm.sh start"
  local name; name=$(basename "$bin")
  vm_ssh "mkdir -p $GUEST_DIR"
  vm_scp "$bin" "$GUEST_USER@localhost:$GUEST_DIR/$name"
  local q="" a
  for a in "$@"; do q+=" $(printf '%q' "$a")"; done
  local rc=0
  vm_ssh "cd $GUEST_DIR && chmod +x ./$name && ./$name$q" || rc=$?
  return $rc
}

# xbuild <source> <output> [extra args...]: cross-compile for freebsd-x86_64
xbuild() {
  local src=$1 out=$2; shift 2
  [ -x compiler/target/blaise ] || die "build compiler/target/blaise first (scripts/macos-dev.sh compile)"
  local uc; uc="$OUT/units-$(basename "$out")"
  mkdir -p "$uc"
  echo ">> cross-compiling $src -> $out (freebsd-x86_64)"
  local rc=0
  compiler/target/blaise --source "$src" --target freebsd-x86_64 --output "$out" \
    --unit-cache "$uc" --rtl-src "$SRC" "$@" > "$uc.log" 2>&1 || rc=$?
  grep -a -v 'linker: note: binding' "$uc.log" | grep -a -v 'stale vs\|compiled by' | head -20 || true
  [ $rc -eq 0 ] || die "CROSS BUILD FAILED (exit $rc): $out (log: $uc.log)"
}

cmd=${1:-}; shift || true
case "$cmd" in
  setup)
    command -v qemu-img >/dev/null || die "qemu-img not found: brew install qemu"
    mkdir -p "$DIR"
    if [ ! -f "$BASE" ]; then
      for m in "${MIRRORS[@]}"; do
        [ -f "$BASE.xz" ] && break
        echo ">> downloading $IMG_NAME.xz from $m"
        if curl -fL --progress-bar -C - -o "$BASE.xz.part" "$m/$IMG_NAME.xz"; then
          mv "$BASE.xz.part" "$BASE.xz"
        else
          # keep a partial download for `curl -C -` to resume; drop an empty one
          [ -s "$BASE.xz.part" ] || rm -f "$BASE.xz.part"
        fi
      done
      [ -f "$BASE.xz" ] || die "download failed from every mirror"
      echo ">> decompressing"
      xz -d "$BASE.xz"
      chmod a-w "$BASE"
    fi
    make_seed
    if [ ! -f "$DISK" ]; then
      echo ">> creating overlay disk (20G; growfs expands the root fs on first boot)"
      qemu-img create -q -f qcow2 -F qcow2 -b "$BASE" "$DISK" 20G
    fi
    t0=$SECONDS
    start_vm
    # First boot runs nuageinit, growfs, host-key generation AND the image's
    # firstboot freebsd-update (fetch + apply ~2000 patches, then reboot):
    # under TCG that is the bulk of setup.  Later boots skip all of it.
    wait_ssh 5400
    vm_ssh "uname -a; mkdir -p $GUEST_DIR"
    echo "setup done in $((SECONDS - t0))s; next: scripts/freebsd-vm.sh crosscheck"
    ;;
  start)
    start_vm
    wait_ssh 900
    ;;
  stop)
    stop_vm
    ;;
  status)
    if running; then
      echo "running (pid $(cat "$PIDFILE"))"
      if ssh_up; then vm_ssh "uname -sr; uptime"; else echo "ssh not answering (yet) on localhost:$PORT"; fi
    else
      echo "not running"; exit 1
    fi
    ;;
  ssh)
    if [ $# -eq 0 ]; then vm_ssh; else vm_ssh "$*"; fi
    ;;
  run)
    [ $# -ge 1 ] || die "usage: scripts/freebsd-vm.sh run <local-binary> [args]"
    run_in_vm "$@"
    ;;
  stdlib-test)
    mkdir -p "$OUT"
    # Test dir BEFORE stdlib, as in macos-dev.sh test-compile.
    xbuild stdlib/src/test/pascal/testrunner.pas "$OUT/stdlib-TestRunner" \
      --unit-path stdlib/src/test/pascal --unit-path stdlib/src/main/pascal \
      --unit-path "$SRC"
    t0=$SECONDS
    rc=0
    run_in_vm "$OUT/stdlib-TestRunner" "$@" || rc=$?
    echo ">> stdlib suite exit $rc after $((SECONDS - t0))s"
    exit $rc
    ;;
  crosscheck)
    # Mirror of scripts/freebsd-crosscheck-build.sh + the CI fixture smoke.
    mkdir -p "$OUT/crosscheck"
    for src in compiler/src/it/freebsd/*.pas; do
      xbuild "$src" "$OUT/crosscheck/$(basename "$src" .pas)" \
        --unit-path stdlib/src/main/pascal
    done
    fail=0
    check() {
      local name=$1 want=$2 got rc=0
      echo "=== $name ==="
      got=$(run_in_vm "$OUT/crosscheck/$name" | tr -d '\r' | tr '\n' '|') || rc=$?
      got=${got%|}
      echo "$got"
      if [ $rc -ne 0 ] || [ "$got" != "$want" ]; then
        echo "FAIL: $name exit $rc, output '$got' != '$want'"; fail=1
      fi
    }
    check hello 'Hello'
    check fileio 'file-io-ok|exists-ok|done'
    [ $fail -eq 0 ] || exit 1
    echo "FREEBSD_CROSSCHECK_OK"
    ;;
  destroy)
    stop_vm
    rm -f "$DISK" "$SEED" "$CONSOLE"
    echo "removed overlay disk; base image kept at $BASE"
    ;;
  *)
    sed -n '2,42p' "$0"; exit 1 ;;
esac
