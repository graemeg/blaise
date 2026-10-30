---
name: cut-blaise-release
description: |
  Cut a new Blaise compiler release from the macOS arm64 development host.
  Bumps the version in Blaise.pas + project.xml + uCompilerId.pas, builds and
  verifies every self-hosting fixpoint on macOS, runs the full suite on macOS
  and on the Linux x86-64 VM, commits, tags, archives the macOS stage-2 binary
  under releases/vX.Y.Z/ (NOT committed -- releases/ is gitignored), cross-
  compiles the Linux and FreeBSD x86-64 binaries (the Linux one proven byte-
  identical to its own Linux self-build), builds self-contained macOS, Linux
  and FreeBSD release tarballs (binary + blaise.cfg + RTL + stdlib source),
  renames + refreshes the -pre bootstrap dir, writes the community post +
  changelog into releases/, then bumps to the next -SNAPSHOT version.  Use
  when asked to "cut a release", "release v0.X.Y", "tag a release", or after
  the user confirms a fixpoint is achieved.
allowed-tools:
  - Bash
  - Read
  - Edit
  - Write
  - AskUserQuestion
---

# Cutting a Blaise release

The primary development host is a **macOS arm64** Mac mini (since v0.15.0).
The release is built and verified there; Linux x86-64 coverage comes from the
OrbStack VM (`scripts/linux-vm.sh`), and FreeBSD from CI.  Run every step in
order.  Stop and surface the failure to the user if any step fails -- never
paper over a missing fixpoint.

## Inputs

The user names the release version (e.g. "0.15.0").  If they didn't, ask via
AskUserQuestion.  The next dev version is the next minor with a `-SNAPSHOT`
suffix (0.15.0 -> 0.16.0-SNAPSHOT).  Confirm with the user if unsure.

## Shipped targets

| Target | How it is built | How it is verified |
|---|---|---|
| `macos-arm64` | native stage-2 from `scripts/macos-dev.sh fixpoint` | all fixpoints + full suite on the Mac |
| `linux-x86_64` | cross-compiled on the Mac | byte-identical to its own Linux self-build (VM) + full suite on the VM |
| `freebsd-x86_64` | cross-compiled on the Mac | ELF shape + version string here; the master CI `freebsd-crosscheck` job runs the self-host fixpoint and the full suite in a FreeBSD VM |

The compiler also accepts `linux-i386`, `linux-arm64` and `windows-x86_64`.
They are NOT release targets: no tarball, unless the user asks for one.

The Linux tarball name is a **CI contract**: `bootstrap.yml` cold-starts from
`blaise-${STAGE1_TAG}-linux-x86_64.tar.gz` on the GitHub release and takes the
first file named `blaise` inside it.  Never rename that tarball or ship a
non-Linux binary in it.

## Preconditions to check before starting

1. All commands run from the project root, currently **`~/devel/blaise`**.
   Do the release in the main checkout, not a worktree: `releases/` (the
   stage-1 binary and the archive) lives there and is gitignored.
2. `git status` must show no tracked changes.  Untracked working files
   (`BUGS.md`, `*.txt`, draft `.adoc`) are normal and must NOT be swept into
   any commit.  If tracked files are modified, ask the user before going on.
3. The `Version` constant in `compiler/src/main/pascal/Blaise.pas` reads
   `'<X.Y.Z>-SNAPSHOT'`.  If it is already a plain version, ask the user --
   they may have cut this release already.
4. The CI anchor is the previous release: `grep STAGE1_TAG
   .github/workflows/bootstrap.yml`.
5. Resolve the stage-1 binary once:

   ```bash
   cd ~/devel/blaise
   BLAISE_RELEASE="$PWD/$(ls -d releases/v*/ | sort -V | tail -1)blaise"
   "$BLAISE_RELEASE" --help | head -1
   ```

   macOS `sort -V` orders `v0.15.0-pre` BEFORE `v0.15.0`, so once a release
   directory exists the newest name wins correctly.  Before then the newest
   entry is the current `-pre` directory, which is the right stage-1.
6. The Linux VM is up: `orb list` shows `blaise-x86` (or `$BLAISE_VM`) running.

## Step 1 -- bump version to release

* `compiler/src/main/pascal/Blaise.pas`: `Version = '<X.Y.Z>-SNAPSHOT';` ->
  `Version = '<X.Y.Z>';`
* `project.xml` (root): `<version><X.Y.Z>-SNAPSHOT</version>` ->
  `<version><X.Y.Z></version>`
* `compiler/src/main/pascal/uCompilerId.pas`:
  `'blaise-<X.Y.Z>-SNAPSHOT+bif<N>'` -> `'blaise-<X.Y.Z>+bif<N>'` -- drop
  `-SNAPSHOT`, keep the `+bif<N>` suffix unchanged.

The `+bif<N>` suffix is NOT `IFACE_VERSION` (v0.15 cycle: `+bif4` against
`IFACE_VERSION = 26`).  It is bumped by hand for codegen changes the `.bif`
alone does not capture; a release does not bump it.

IMPORTANT (bif-coverage sync): `TestRun_BifCoverage_NoGaps` asserts the
project.xml base version (with `-SNAPSHOT` stripped) is a substring of
`COMPILER_ID`.  Both must carry the same base version at all times -- here,
and again at the dev-cycle bump in Step 8.

## Step 2 -- build the release compiler; verify every fixpoint

On macOS, `scripts/macos-dev.sh` drives the compiler builds (it also installs
`blaise.cfg` beside `compiler/target/blaise`).  PasBuild works on the Mac too,
but the fixpoint and test steps below use `macos-dev.sh`, as the `macos-check`
CI job does.

```bash
# stage-1 -> stage-2 -> stage-3, byte-identical; installs stage-2 as
# compiler/target/blaise.  This stage-2 is the macOS release binary.
scripts/macos-dev.sh fixpoint --compiler "$BLAISE_RELEASE" --install
compiler/target/blaise --help | head -1      # Blaise Compiler v<X.Y.Z>
```

Then the five fixpoint scripts, all of which run on macOS (each uses
`compiler/target/blaise` as stage-0):

```bash
./scripts/fixpoint-native.sh           # NATIVE_FIXPOINT_OK
./scripts/fixpoint-native-internal.sh  # NATIVE_INTERNAL_OK
./scripts/fixpoint-warmcache.sh        # WARMCACHE_FIXPOINT_OK
./scripts/fixpoint-binary.sh           # BINARY_FIXPOINT_OK
./scripts/fixpoint-initorder.sh        # INITORDER_FIXPOINT_OK
```

Note the "stage-2 asm: N lines" figure `fixpoint-native.sh` prints -- it is
the arm64 count, quoted in the commit message and the changelog.
`fixpoint-native.sh` assembles and links with external `cc` (Xcode Command
Line Tools) and leaves a cc-linked stage-2 in `/tmp/fpn_blaise2`.  That is a
cross-check only; the **shipped macOS binary is the internally linked,
signed stage-2** that `macos-dev.sh fixpoint --install` put in
`compiler/target/blaise` -- the byte-reproducible one, built exactly as a
user's compiler links programs.

Run them in the foreground with a generous timeout (600000 ms); the whole
set takes a few minutes on the Mac mini.  If any script does not print its
OK line, **stop** and show the output.  There is no acceptable "almost
fixpoint".

## Step 3 -- run the full suites (macOS, then Linux)

macOS, with the stage-2 compiler from Step 2:

```bash
scripts/macos-dev.sh test-compile
compiler/target/TestRunner             # OK (N tests, M ignored)
scripts/macos-dev.sh stdlib-test       # OK (K tests)
```

Confirm the test count ROSE against the last run you know of: test-compile
can fail quietly and leave a stale runner that still passes (check its exit
code).

Linux x86-64, from a CLEAN detached worktree of the release commit (the VM
syncs committed state only).  Do this after Step 4's commit, so the VM tests
exactly what is tagged:

```bash
git worktree add --detach ../blaise-wt-relvm v<X.Y.Z>
mkdir -p ../blaise-wt-relvm/compiler/target
cp compiler/target/blaise ../blaise-wt-relvm/compiler/target/blaise
( cd ../blaise-wt-relvm && scripts/linux-vm.sh all )
git worktree remove --force ../blaise-wt-relvm
```

Expected: OK on both suites, except the one known Rosetta artefact
`TLinkerE2ETests.TestRun_SyscallHelloWorld` (passes on real Linux).  Any
other failure: stop.  Record N, the macOS total, for the README and the post.

### Step 3b -- build and run every program in the repository (macOS)

The suites only compile what they reference.  Tools, benchmarks and test
programs that nothing references rot quietly: the v0.15 sweep found kanban
without macOS terminal support, bindgen output that would not compile, punit
printing wrong hex, five programs broken by newer language rules, and the
internal linker unable to load any C library beyond libSystem.  So before
tagging, build and RUN everything, with the stage-2 compiler from Step 2.
Work in a scratch directory, never `/tmp` (stale `.o` files there get linked
in), and give each program its own `--unit-cache`.

1. **Every default PasBuild module** (compiler, migration-analyser, kanban,
   bif-coverage, flag-coverage, blaise-guard, bindgen), from the repo root:

   ```bash
   pasbuild test --compiler "$PWD/compiler/target/blaise"   # every module OK
   ```

   Then run each tool for real:

   - `tools/bif-coverage/target/bif-coverage` and
     `tools/flag-coverage/target/flag-coverage` both print OK;
   - `tools/blaise-guard/target/blaise-guard` scans `stdlib/src/main/pascal`
     without crashing;
   - kanban: its CLI commands, plus the full-screen TUI under a pty
     (`script -q /dev/null tools/kanban/target/kanban ...`);
   - bindgen: generate bindings for a real header (zlib), compile a small
     program against them and run it;
   - `tools/migration-analyser/target/cp-migrate` runs and exits 0 (still a
     placeholder that prints a greeting).

2. **Standalone programs** -- compile and run each:

   - `tests/*.pas` (milestones, `bench_lists`);
   - `tools/performance/bench_*.pas` (or `run-benchmarks.sh`);
   - `runtime/src/test/pascal/*.pas` -- the punit tests must pass; the
     must-fail cases must fail the same way on both ISAs.
     `bench_async_http` is a load benchmark, so request failures under load
     are expected;
   - the three TLS loopback programs (`stdlib/src/test/pascal/*loopback.pas`),
     linked with the default internal linker against Homebrew OpenSSL.  The
     server certificate needs `subjectAltName=DNS:localhost,IP:127.0.0.1`;
   - `bindings/examples/x11_window.pas` only if XQuartz is installed;
     otherwise note it as not run.

Every program must build and behave as its source says.  A failure here is
a release blocker like any suite failure: fix it with a test (unit + e2e),
then re-run Steps 2-3.

## Step 4 -- commit and tag

```bash
git add compiler/src/main/pascal/Blaise.pas compiler/src/main/pascal/uCompilerId.pas project.xml
git diff --cached --stat   # exactly three files, one line each
```

If `project.xml` shows more than one changed line, it carried unrelated edits:
`git restore --staged project.xml`, then `git add -p project.xml` and stage
only the `<version>` hunk.

Commit (HEREDOC):

```
release: v<X.Y.Z>

<one or two sentences: all fixpoints green on macOS arm64 (native on N lines
of stage-2 assembly, internal-asm, warm-cache, binary, init-order), the Linux
x86-64 binary byte-identical to its own Linux self-build, the headline themes
of the cycle, and the test count.>
```

```bash
git tag v<X.Y.Z>
```

**Never reference Claude in the commit message.**  **Do not push** -- the
user decides when; the `ci-verify-then-master` skill does it (a `ci/` branch
first, then master).  The tag is pushed separately (`git push github
v<X.Y.Z>`), and only when the user asks.

Now run the Linux half of Step 3.

## Step 5 -- archive and cross-compile the release binaries

All three binaries are built while the tree is still at `<X.Y.Z>` --
**before** Step 8's dev bump.  A binary built after the bump reports
`<next>-SNAPSHOT`.

```bash
V=<X.Y.Z>
mkdir -p releases/v$V target/rel/linux target/rel/freebsd
cp compiler/target/blaise releases/v$V/blaise.new && mv releases/v$V/blaise.new releases/v$V/blaise
releases/v$V/blaise --help | head -1         # Blaise Compiler v<X.Y.Z>
codesign -v releases/v$V/blaise && echo signed
```

**Copy-then-rename for every macOS binary you replace.**  The kernel caches a
signed binary's code signature per vnode, so overwriting an existing binary
in place with different bytes gets every later exec SIGKILLed (exit 137).
`cp` to a new name and `mv` it over is a new inode.

Cross-compile the two x86-64 binaries with the macOS release binary, using
the same flags `fixpoint-binary.sh` uses (the output basename must be
`blaise`):

```bash
for T in linux freebsd; do
  UC=$(mktemp -d)
  releases/v$V/blaise --source compiler/src/main/pascal/Blaise.pas \
    --unit-path compiler/src/main/pascal --unit-path stdlib/src/main/pascal \
    --target $T-x86_64 --backend native --unit-cache "$UC" \
    --output target/rel/$T/blaise 2>&1 | grep -v 'linker: note: binding'
  rm -rf "$UC"
done
file target/rel/linux/blaise     # ELF 64-bit ... x86-64, version 1 (SYSV), statically linked
file target/rel/freebsd/blaise   # ELF 64-bit ... x86-64, version 1 (FreeBSD), statically linked
for T in linux freebsd; do
  strings target/rel/$T/blaise | grep -q "blaise-$V+" \
    || { echo "ERROR: $T binary is not v$V"; exit 1; }
done
```

(`readelf` is not installed on macOS; `file` reports the ELF OS/ABI.)

**Prove the Linux binary is a Linux fixpoint**: on the VM it must rebuild
itself byte-for-byte.  The VM sees `/Users`, so it runs the binary in place
against this checkout:

```bash
orb -m "${BLAISE_VM:-blaise-x86}" bash -c "cd '$PWD' && rm -rf /tmp/relfp && mkdir -p /tmp/relfp/s2 /tmp/relfp/uc \
  && target/rel/linux/blaise --help | head -1 \
  && target/rel/linux/blaise --source compiler/src/main/pascal/Blaise.pas \
       --unit-path compiler/src/main/pascal --unit-path stdlib/src/main/pascal \
       --backend native --unit-cache /tmp/relfp/uc --output /tmp/relfp/s2/blaise >/dev/null 2>&1 \
  && cmp target/rel/linux/blaise /tmp/relfp/s2/blaise && echo LINUX_SELFHOST_IDENTICAL"
```

It must print `LINUX_SELFHOST_IDENTICAL` (held for the v0.15 cycle,
checked 2026-10-23).  The Linux binary is freestanding and static -- no glibc
dependency.  Releases up to v0.14.0 shipped a cc-linked dynamic binary built
on Linux; say so in the changelog.

The FreeBSD binary cannot run here.  After the release commit reaches
master, the `freebsd-crosscheck` job (master tier) runs the self-host
fixpoint and the full suite in a FreeBSD VM.  Check that run is green before
the user publishes, or have the user try the tarball on a FreeBSD box.

## Step 6 -- release tarballs

**Self-contained, never binary-only.**  The compiler source-builds the RTL on
every link, so a lone binary cannot compile anything (`RTL source directory
not found`).  Each tarball bundles the RTL and stdlib source and a
`blaise.cfg` beside the binary:

```
blaise-v<X.Y.Z>-<os>-<cpu>/
  blaise            the target binary
  blaise.cfg        rtl-src=rtl-src / unit-path=stdlib-src (relative paths
                    resolve against this file's directory)
  rtl-src/          compiler/src/main/pascal/*.pas
  stdlib-src/       stdlib/src/main/pascal/*.pas
  hello.pas         a sample program
  USAGE.txt         quick start
  README.adoc  NOTICE  LICENSE
```

`blaise.cfg` recognises `rtl-src=<dir>` and `unit-path=<dir>` (KEY=VALUE, `#`
comments); relative values resolve against the file's directory, `~` expands
to `$HOME`.  The compiler reads `<bindir>/blaise.cfg` first, then
`~/.blaise.cfg`.

```bash
# make_tarball <binary-path> <os> <cpu>
make_tarball() {
  BIN="$1"; OS="$2"; CPU="$3"
  STAGING=$(mktemp -d); DIRNAME="blaise-v$V-$OS-$CPU"; D="$STAGING/$DIRNAME"
  mkdir -p "$D/rtl-src" "$D/stdlib-src"
  cp "$BIN" "$D/blaise"; chmod +x "$D/blaise"
  cp compiler/src/main/pascal/*.pas "$D/rtl-src/"
  cp stdlib/src/main/pascal/*.pas   "$D/stdlib-src/"
  cp README.adoc NOTICE LICENSE "$D/"
  cat > "$D/blaise.cfg" <<'CFG'
# Blaise compiler configuration.  Relative paths resolve against this file's
# directory, so the compiler finds its RTL + stdlib source wherever extracted.
rtl-src=rtl-src
unit-path=stdlib-src
CFG
  cat > "$D/hello.pas" <<'PAS'
program Hello;
begin
  WriteLn('Hello from Blaise!');
end.
PAS
  cat > "$D/USAGE.txt" <<'TXT'
Blaise -- self-contained toolchain.  From this directory:
    ./blaise --source hello.pas --output hello && ./hello
The bundled blaise.cfg supplies the RTL + stdlib source locations, so no extra
flags are needed.  If you move `blaise`, keep blaise.cfg / rtl-src/ / stdlib-src/
beside it, or pass --rtl-src DIR --unit-path DIR explicitly.  See README.adoc.
TXT
  if [ "$OS" = macos ]; then
    cat >> "$D/USAGE.txt" <<'TXT'

macOS: the binary is ad-hoc signed, not notarised.  If the archive was
downloaded with a browser and macOS refuses to run `blaise`, clear the
quarantine flag once:  xattr -dr com.apple.quarantine .
TXT
  fi
  COPYFILE_DISABLE=1 tar -czf "releases/$DIRNAME.tar.gz" -C "$STAGING" "$DIRNAME"
  rm -rf "$STAGING"
  tar -tzf "releases/$DIRNAME.tar.gz" | head -5
}

make_tarball releases/v$V/blaise        macos   arm64
make_tarball target/rel/linux/blaise    linux   x86_64
make_tarball target/rel/freebsd/blaise  freebsd x86_64
```

`COPYFILE_DISABLE=1` keeps macOS `tar` from adding `._*` AppleDouble files,
which would otherwise appear in every tarball.

Validate the layout by extracting and compiling `hello.pas` -- natively for
macOS, on the VM for Linux:

```bash
X=$(mktemp -d); tar -xzf releases/blaise-v$V-macos-arm64.tar.gz -C "$X"
( cd "$X/blaise-v$V-macos-arm64" && ./blaise --source hello.pas --output "$X/h" && "$X/h" )
X=$(mktemp -d); tar -xzf releases/blaise-v$V-linux-x86_64.tar.gz -C "$X"
orb -m "${BLAISE_VM:-blaise-x86}" bash -c "cd '$X/blaise-v$V-linux-x86_64' && ./blaise --source hello.pas --output /tmp/relh && /tmp/relh"
# each must print: Hello from Blaise!
```

**Never `git add` binaries or tarballs.**  `releases/` and `target/` are
gitignored; the user keeps binaries local and uploads the tarballs to the
GitHub release themselves.

## Step 7 -- refresh the -pre bootstrap dir and README

Rename the rolling `-pre` directory to the cycle being OPENED and refresh it
(plain `mv` -- `releases/` is gitignored):

```bash
NEXT=<next-minor>.0                     # e.g. 0.16.0
mv releases/v$V-pre releases/v$NEXT-pre
cp releases/v$V/blaise releases/v$NEXT-pre/blaise.new && mv -f releases/v$NEXT-pre/blaise.new releases/v$NEXT-pre/blaise
cp target/rel/linux/blaise releases/v$NEXT-pre/blaise.linux
rm -rf releases/v$NEXT-pre/rtl releases/v$NEXT-pre/*.bak
releases/v$NEXT-pre/blaise --help | head -1
```

`blaise` is the macOS stage-1 for local cold bootstraps and
`rolling-bootstrap.sh`; `blaise.linux` is the cross-built Linux compiler kept
beside it.  Removing `rtl/` makes the next compile rebuild the RTL object
cache with the new binary (a stale cache gives false failures).  CI does not
read `releases/`: it cold-starts from the published tarball (Step 8b).

Update `README.adoc`'s Project Status "Testing:" line with the Step 3 total,
and check its platform wording still matches the shipped targets, then:

```bash
git add README.adoc
git commit -m "docs: update test count to <N> for v<X.Y.Z>"
```

zsh (the macOS login shell) aborts a whole command when a glob matches
nothing, so `rm -rf releases/v$NEXT-pre/rtl releases/v$NEXT-pre/*.bak`
removes nothing at all when there is no `.bak` file.  Check that `rtl/` is
gone.

## Step 8 -- bump to the next dev version

* `Blaise.pas`: `'<X.Y.Z>'` -> `'<next-minor>.0-SNAPSHOT'`
* `project.xml`: `<version>` -> `<next-minor>.0-SNAPSHOT`
* `uCompilerId.pas`: `'blaise-<next-minor>.0-SNAPSHOT+bif<N>'` (same suffix)

```bash
git add compiler/src/main/pascal/Blaise.pas compiler/src/main/pascal/uCompilerId.pas project.xml
git diff --cached --stat   # three files, version lines only
git commit -m "chore: begin v<next-minor>.0-dev cycle"
```

### Step 8b -- advance the CI bootstrap anchor (REQUIRED)

The anchor must always be the release just cut: set `STAGE1_TAG` in
`.github/workflows/bootstrap.yml` to `v<X.Y.Z>`, in its own commit.  CI
downloads that tag's Linux tarball, so this commit lands only **after the
user has published the GitHub release** (`gh release view v<X.Y.Z>` lists
`blaise-v<X.Y.Z>-linux-x86_64.tar.gz`).  Prepare the commit and tell the user
it waits on the upload.  The anchor once drifted (v0.13.0 shipped while CI
still cold-started from v0.12.0) because this step read as optional.  Never
move the anchor backwards across v0.13.0, where the RTL archive requirement
ended.

## Step 9 -- community post and changelog

Write `releases/community-post-v<X.Y.Z>.md` and
`releases/changelog-v<X.Y.Z>.md` (gitignored working files; never `git add`
them).  Both cover only `<prev-tag>..v<X.Y.Z>`:

```bash
PREV=$(git describe --tags --abbrev=0 v<X.Y.Z>^)
git log $PREV..v<X.Y.Z> --oneline | wc -l
git log $PREV..v<X.Y.Z> --oneline | grep ' feat'   # features; also ' fix', ' perf'
```

### community-post

- A warm announcement grouped into themes, headline win up top; not a commit
  log.  Emoji in headings and milestone call-outs; British English.
- Tiny code examples (3-6 lines) for headline language features.  VERIFY each
  compiles and runs: write it to the scratchpad and build it with
  `compiler/target/blaise`; for codegen-sensitive features also cross-compile
  with `--target linux-x86_64` and run it on the VM.
- Cover: headline wins, the platforms shipped (macOS arm64 is the primary
  development host from v0.15.0), language/stdlib additions, hardening, notable
  internals, the fixpoint line count and test count, and a call to action
  pointing at the GitHub release.  End with "Onwards to v<next>! 🙌" and point
  at the changelog.

### changelog

- Grouped by area (Platforms, Native backend, Toolchain, Language,
  ARC/runtime, stdlib, Codegen, Semantic, Debugging, Performance,
  Tooling/CI); one concise line per entry.
- A "Release artefacts" section listing the three tarballs and how each
  binary was verified (the table under "Shipped targets").
- Close with the fixpoint line count and the test count.

## Step 10 -- report to the user

- Tag `v<X.Y.Z>` (local, not pushed); the last 3-4 commits.
- The OK lines: BINARY_FIXPOINT_OK (macos-dev), NATIVE_FIXPOINT_OK (N lines),
  NATIVE_INTERNAL_OK, WARMCACHE_FIXPOINT_OK, BINARY_FIXPOINT_OK (script),
  INITORDER_FIXPOINT_OK, LINUX_SELFHOST_IDENTICAL.
- Test counts: macOS suite + stdlib; Linux VM suite + stdlib (and the Rosetta
  artefact).
- `releases/v<X.Y.Z>/blaise`; the `-pre` dir renamed and refreshed.
- The three tarballs to upload:
  `releases/blaise-v<X.Y.Z>-macos-arm64.tar.gz`,
  `releases/blaise-v<X.Y.Z>-linux-x86_64.tar.gz` (the CI anchor reads this
  one), `releases/blaise-v<X.Y.Z>-freebsd-x86_64.tar.gz` (verified by the
  master `freebsd-crosscheck` job, or on a FreeBSD box).
- The post and changelog paths.
- What waits on the user: pushing (via `ci-verify-then-master`), pushing the
  tag, publishing the GitHub release, and only then the Step 8b anchor
  commit.

## Common pitfalls

- **Overwriting a signed macOS binary in place.**  Exit 137 on every later
  run of that path.  Copy beside it and `mv` over (Steps 5 and 7).
- **Shipping the cc-linked `/tmp/fpn_blaise2` on macOS.**  It is the
  `fixpoint-native.sh` cross-check.  Ship the internally linked stage-2 from
  `macos-dev.sh fixpoint --install`.
- **Building a binary after the dev bump.**  The cross-compiled binaries bake
  in the working tree's `Version`/`COMPILER_ID`.  To rebuild one later:
  `git checkout v<X.Y.Z> -- compiler/src/main/pascal/Blaise.pas
  compiler/src/main/pascal/uCompilerId.pas`, rebuild, then `git checkout HEAD
  -- ` the same two files.  Check with `strings <bin> | grep 'blaise-<X.Y.Z>+'`.
- **A binary-only tarball.**  It cannot compile anything; Step 6's layout is
  mandatory.  `._*` files in a tarball mean `COPYFILE_DISABLE=1` was missing.
- **Renaming the Linux tarball.**  CI's cold start fetches exactly
  `blaise-<tag>-linux-x86_64.tar.gz`.
- **Testing a stale runner.**  `macos-dev.sh test-compile` can fail without
  much noise and leave the previous TestRunner, which still passes.  Check the
  exit code and that the test count rose.
- **Testing the Linux VM against uncommitted state.**  `linux-vm.sh sync`
  resets the VM clone to HEAD (committed state only); run it from a clean
  detached worktree of the tag.
- **COMPILER_ID out of sync with project.xml.**  Their base versions must
  match, or `TestRun_BifCoverage_NoGaps` fails.  Leave `+bif<N>` alone.
- **Forgetting to rename the `-pre` dir.**  The newest `releases/v*-pre/` must
  name the cycle being opened.
- **Missing `timeout` on macOS.**  `fixpoint-native.sh` falls back to
  `gtimeout` or no guard (fixed 2026-10-23); any other script that calls GNU
  `timeout`, `readelf` or `stat -c` needs the same treatment before it runs on
  the Mac.
- **Forgetting `--compiler` with PasBuild.**  Without it PasBuild falls back
  to FPC, which never builds Blaise.  (`macos-dev.sh` always names the
  compiler.)
- **`blaise_rtl.a` beside a binary.**  Not needed: the compiler source-builds
  the RTL into `rtl/<target>/` beside itself.  A relocated binary needs
  resolvable RTL *source* (`blaise.cfg`, `--rtl-src` or `$BLAISE_RTL_SRC`).
