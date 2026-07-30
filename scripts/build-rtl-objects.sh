#!/bin/sh
# Build the implicit RTL object files from source, mirroring the compiler's
# own TBackendDriver.EnsureRTLObjects.  Used by the fixpoint / bootstrap
# scripts to link a self-hosted compiler binary WITHOUT the legacy
# blaise_rtl.a archive (RTL-unification Stage 3).
#
# POSIX sh on purpose: the e2e suite runs this on FreeBSD, whose base system
# has no bash (and the FreeBSD CI VM deliberately installs no packages).
#
# Usage:
#   scripts/build-rtl-objects.sh <blaise-binary> <out-dir> [options]
# Options:
#   --with-startup            include runtime.start (its bare _start)
#   --exclude-defined-by FILE omit any RTL object that defines a symbol FILE
#                             already defines (FILE is the main program object)
#
# Builds each RTL unit into <out-dir>/<unit>.o and prints, one per line on
# stdout, the object paths to put on the link line.  By default runtime.start
# (the bare _start entry) is OMITTED — a gcc/cc link line gets _start from libc
# and calls main.  Pass --with-startup to include it (a -nostartfiles / native
# internal link that owns the entry point).
#
# --exclude-defined-by handles the self-host link: a whole-program --emit-ir
# dump INLINES the RTL units the compiler transitively uses (runtime.arc via
# `uses classes`, etc.), so the program object already defines their symbols.
# Linking our standalone copy too would double-define them; this option drops
# the redundant objects, mirroring the compiler driver's own dedup.
#
# The build goes through a --unit-cache so each unit references its RTL deps'
# globals externally instead of re-defining them (the archive's member
# selection used to hide those duplicate definitions; explicit .o files do not).
# RTL units carry inline asm, so the native backend + internal assembler is
# mandatory.  Build order is leaf-first so each unit's deps are already cached.

set -e

BLAISE="$1"
OUTDIR="$2"
shift 2 || true
WITH_STARTUP=0
EXCLUDE_OBJ=""
while [ $# -gt 0 ]; do
  case "$1" in
    --with-startup)       WITH_STARTUP=1; shift ;;
    --exclude-defined-by) EXCLUDE_OBJ="$2"; shift 2 ;;
    *) echo "build-rtl-objects: unknown option $1" >&2; exit 2 ;;
  esac
done

if [ -z "$BLAISE" ] || [ -z "$OUTDIR" ]; then
  echo "usage: build-rtl-objects.sh <blaise-binary> <out-dir> [--with-startup] [--exclude-defined-by FILE]" >&2
  exit 2
fi
if [ ! -x "$BLAISE" ]; then
  echo "build-rtl-objects: compiler binary not found: $BLAISE" >&2
  exit 2
fi

# Resolve the RTL source relative to THIS script (scripts/ is a sibling of
# compiler/), so the script works regardless of the caller's CWD — the fixpoint
# scripts run from the project root, the test runner from compiler/.
SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
SRC="$SCRIPT_DIR/../compiler/src/main/pascal"
if [ ! -f "$SRC/runtime.arc.pas" ]; then
  # Fall back to a CWD-relative path (e.g. an unusual invocation layout).
  SRC=compiler/src/main/pascal
fi
if [ ! -f "$SRC/runtime.arc.pas" ]; then
  echo "build-rtl-objects: RTL source not found under $SRC" >&2
  exit 2
fi

mkdir -p "$OUTDIR"

# Leaf-first link order.  rtl.platform owns the shared globals (GPlatformLayout,
# GRtlPlatform) that layout.linux + posix reference externally, so it is built
# first and linked once.
# Select the platform layout + errno units for the host OS.
case "$(uname -s)" in
  FreeBSD) LAYOUT_UNIT=rtl.platform.layout.freebsd
           ERRNO_UNIT=runtime.errno.freebsd ;;
  Darwin)  LAYOUT_UNIT=rtl.platform.layout.darwin
           ERRNO_UNIT=runtime.errno.darwin ;;
  *)       LAYOUT_UNIT=rtl.platform.layout.linux
           ERRNO_UNIT=runtime.errno.linux ;;
esac
RTL_UNITS="rtl.platform
runtime.start runtime.atomic runtime.setjmp runtime.utf8
runtime.mem runtime.str runtime.set runtime.arc
runtime.weak runtime.float runtime.math runtime.thread runtime.exc
$ERRNO_UNIT
$LAYOUT_UNIT rtl.platform.posix"

# Symbols the main program object already defines (for --exclude-defined-by).
# Written to a temp file so the per-object comm(1) below stays POSIX (no
# process substitution) and safe under parallel suite runs (unique name).
EXCL_FILE=""
if [ -n "$EXCLUDE_OBJ" ]; then
  EXCL_FILE=$(mktemp "${TMPDIR:-/tmp}/rtlexcl.XXXXXX")
  trap 'rm -f "$EXCL_FILE"' EXIT
  nm "$EXCLUDE_OBJ" 2>/dev/null | grep -E ' [TDBR] ' | awk '{print $3}' | sort -u \
    > "$EXCL_FILE"
fi

# Invalidate the whole cache when the COMPILER changes.
#
# BUG-20260726 (twin of the one fixed in blaise.codegen.driver's RTLCacheKey):
# the per-unit staleness check below compares the object against its SOURCE
# mtime, which cannot see that the compiler that produced it changed.  A
# persistent $OUTDIR therefore handed a rebuilt compiler the PREVIOUS one's
# objects, and the failure landed far from its cause — on macOS the whole e2e
# layer failed with `ARM64_RELOC_TLVP_LOAD_PAGEOFF12 relocation on non-LDR
# instruction in runtime.mem.o`, an ABI bug that had ALREADY been fixed in the
# backend; the objects simply predated the fix.  204 test failures, none of them
# real.
#
# Keyed on the compiler binary's content hash, so it survives a rebuild that
# does not change the bytes (fixpoint-stable: stage-2 and stage-3 are identical,
# so a warm $OUTDIR is still reused).  Wiping is safe here where the driver's
# equivalent could not: $OUTDIR is a per-suite scratch directory, not a shared
# cache other processes link out of.
CACHE_STAMP="$OUTDIR/.compiler-id"
COMPILER_ID=$(shasum -a 256 "$BLAISE" 2>/dev/null | awk '{print $1}')
if [ -z "$COMPILER_ID" ]; then
  COMPILER_ID=$(sha256sum "$BLAISE" 2>/dev/null | awk '{print $1}')
fi
# An unreadable compiler degrades to "always rebuild" rather than to silent
# reuse — the failure mode that caused this bug.
if [ -z "$COMPILER_ID" ]; then
  COMPILER_ID="unknown-$$"
fi
if [ ! -f "$CACHE_STAMP" ] || [ "$(cat "$CACHE_STAMP")" != "$COMPILER_ID" ]; then
  rm -f "$OUTDIR"/*.o "$OUTDIR"/*.o.syms "$OUTDIR"/*.bif "$OUTDIR"/*.build.err
  printf '%s\n' "$COMPILER_ID" > "$CACHE_STAMP"
fi

OBJS=""
for u in $RTL_UNITS; do
  obj="$OUTDIR/$u.o"
  src="$SRC/$u.pas"
  # Skip BEFORE building: the object was discarded further down anyway, and
  # runtime.start is an x86_64/glibc _start stub whose inline asm no other
  # target can even assemble (macOS arm64 rejects `endbr64`, so every e2e test
  # died with "failed to build runtime.start").  Mach-O needs no startup object
  # at all — LC_MAIN names `main` directly.
  if [ "$u" = "runtime.start" ] && [ "$WITH_STARTUP" -eq 0 ]; then
    continue
  fi
  # Rebuild only when the cached object is missing or older than its source, so
  # a persistent $OUTDIR (e.g. reused across a test suite) builds the RTL once.
  if [ ! -f "$obj" ] || [ "$src" -nt "$obj" ]; then
    "$BLAISE" --backend native --assembler internal \
      --source "$src" \
      --unit-path "$SRC" --unit-cache "$OUTDIR" \
      --output "$obj" >/dev/null 2>"$OUTDIR/$u.build.err" || {
        echo "build-rtl-objects: failed to build $u" >&2
        tail -5 "$OUTDIR/$u.build.err" >&2
        exit 1
      }
    # Cache this object's defined symbols so repeated --exclude-defined-by calls
    # (e.g. one per test in a suite) don't re-run nm on the stable RTL objects.
    nm "$obj" 2>/dev/null | grep -E ' [TDBR] ' | awk '{print $3}' | sort -u \
      > "$obj.syms"
  fi
  # Drop this object only when EVERY symbol it defines is already owned by the
  # main program.  `comm -23` lists the symbols defined HERE but not there, so
  # an empty result means the object is fully redundant.
  #
  # It used to drop on ANY overlap (comm -12 non-empty), which threw away the
  # object's UNIQUE symbols too.  In practice every object that emits class
  # metadata defines the same handful of base-class stubs — _typeinfo_TObject,
  # _vtable_TObject, __FieldCleanup_TObject and the TCustomAttribute twins — so
  # a single shared stub discarded rtl.platform.posix.o entirely and with it the
  # 119 symbols nothing else provides (__SetArgs, __SysWriteInt, ...).  That was
  # ~228 e2e failures: `Undefined symbols for architecture arm64`.
  #
  # Supplying a partially-overlapping object is safe because the backend binds
  # RTL-owned definitions WEAK (the IsUnmangledUnit rule in the native
  # backends), so ld resolves each shared symbol to the program's strong
  # definition and ignores the RTL's weak copy.  Verified on macos-arm64: the
  # program object defines _typeinfo_TObject `external`, the RTL object
  # `weak external`.  The only non-weak RTL definitions are the per-unit
  # <unit>_init routines, which are unique per unit and cannot clash.
  #
  # This matches EnsureRTLObjects in blaise.codegen.driver, which has always
  # used the every-symbol rule for the compiler-driven link.
  if [ -n "$EXCL_FILE" ] && [ -s "$EXCL_FILE" ] && \
     [ -f "$obj.syms" ] && [ -s "$obj.syms" ]; then
    if [ -z "$(comm -23 "$obj.syms" "$EXCL_FILE")" ]; then
      continue
    fi
  fi
  OBJS="$OBJS$obj
"
done

printf '%s' "$OBJS"
