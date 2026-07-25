---
name: cut-blaise-release
description: |
  Cut a new Blaise compiler release. Bumps the version in Blaise.pas + project.xml,
  rebuilds compiler + RTL + stage-2 binary, verifies all four self-hosting
  fixpoints (QBE, native, internal-assembler, warm-cache), runs the full test
  suite, commits, tags, archives the NATIVE stage-2 binary under releases/vX.Y.Z/
  (NOT committed — releases/ is gitignored), renames + refreshes the -pre
  bootstrap dir to the next cycle, cross-compiles a FreeBSD x86_64 binary, builds
  self-contained Linux + FreeBSD release tarballs (binary + blaise.cfg + RTL +
  stdlib source), writes the community post + changelog, then
  bumps Blaise.pas + project.xml + uCompilerId.pas to the next -SNAPSHOT version.
  Use when asked to "cut a release", "release v0.X.Y", "tag a release", or after
  the user confirms a fixpoint is achieved.
allowed-tools:
  - Bash
  - Read
  - Edit
  - Write
  - AskUserQuestion
---

# Cutting a Blaise release

This skill mirrors the verified release process used for v0.11.0.
Run every step in order. Stop and surface the failure to the user if any
step fails — never paper over a missing fixpoint.

## Inputs

The user will name the release version (e.g. "0.11.0"). If they didn't,
ask them via AskUserQuestion. The next-dev version is the next minor with
a `-SNAPSHOT` suffix (0.11.0 → 0.12.0-SNAPSHOT). Confirm with the user if unsure.

## Preconditions to check before starting

1. Run `git status`. The working tree often carries **unrelated** uncommitted
   changes (e.g. `compiler/project.xml` and `tools/kanban/project.xml` build-
   option tweaks, plus many untracked `.txt`/`.adoc` working files). These are
   NORMAL on this repo and must NOT be swept into the release commit. The root
   `project.xml` may also carry unrelated edits — you will stage only its
   version line (see Step 5). If you see uncommitted changes that look like
   in-progress feature work, ask the user whether to proceed.
2. The current `Version` constant in `compiler/src/main/pascal/Blaise.pas`
   should look like `'<X.Y.Z>-SNAPSHOT'` (the dev marker). If it's already a
   plain non-dev version, ask the user — they may have already cut this release.
3. All commands run from the project root `/data/devel/new-pascal-compiler`
   (PasBuild requirement — sub-modules lack the `<version>` field).
4. `vendor/qbe/qbe` must exist (the fixpoint scripts need it). The current
   release binary lives at the newest `releases/v*-pre/blaise` or
   `releases/v*/blaise` — the fixpoint scripts auto-pick it via `sort -V`.

## Step 1 — bump version to release

Edit `compiler/src/main/pascal/Blaise.pas`. Find the line:

```pascal
  Version = '<X.Y.Z>-SNAPSHOT';
```

and change it to:

```pascal
  Version = '<X.Y.Z>';
```

Also edit `project.xml` in the project root. Find the line:

```xml
  <version><X.Y.Z>-SNAPSHOT</version>
```

and change it to:

```xml
  <version><X.Y.Z></version>
```

Edit `compiler/src/main/pascal/uCompilerId.pas`. The `COMPILER_ID` looks like
`'blaise-<X.Y.Z>-SNAPSHOT+bif<N>'`. For the release, **drop the `-SNAPSHOT`**
but **keep the `+bif<N>` tag** → `'blaise-<X.Y.Z>+bif<N>'`. Only bump the
`+bif<N>` number if the `.bif` interface format actually changed this cycle
(`IFACE_VERSION` in `uUnitInterfaceIO.pas` — the two must agree).

IMPORTANT (bif-coverage sync): the `bif-coverage` tool's `TestRun_BifCoverage_NoGaps`
asserts the project.xml base version (with `-SNAPSHOT` stripped) is a substring
of `COMPILER_ID`. So `COMPILER_ID` and project.xml `<version>` must carry the
**same base version** at all times — here at release, and again at the dev-cycle
bump in Step 7. A mismatch silently fails that test.

## Step 2 — verify the QBE fixpoint (NOT the binary we ship)

The project's `scripts/fixpoint.sh` does a whole QBE stage-2 build: it
rebuilds + installs the runtime, uses the latest release binary as stage-1 to
emit stage-2 IR, assembles + links the stage-2 binary to **`/tmp/fp_blaise2`**,
then emits stage-3 IR and diffs it.

NOTE: since v0.12.0 the **native backend is the default**, so the binary we
actually archive and ship is the NATIVE stage-2 binary from Step 3
(`/tmp/fpn_blaise2`), NOT `/tmp/fp_blaise2`. This step still runs — the QBE
fixpoint is a required reproducibility guard and prints the IR line count we
quote in the commit message and docs — but `/tmp/fp_blaise2` is only used to
rebuild `compiler/target/blaise` below so the native fixpoints run on the
released version.

```bash
./scripts/fixpoint.sh        # must print FIXPOINT_OK
```

Note the stage-2 IR line count it prints ("stage-2 IR: N lines") — you'll quote
it in the commit message and the docs.

The verified stage-2 binary is **`/tmp/fp_blaise2`**. (If the release stage-1
was too old to reach fixpoint in one round, `fixpoint.sh` extends a round and
the binary becomes `/tmp/fp_blaise3` — read the script's output to see which.)

`fixpoint.sh` only updated the IR-emitting path; `compiler/target/blaise` may
still be the old `-SNAPSHOT` build. Rebuild it from the fixpoint binary so the
native fixpoints and the test runner use the released version:

```bash
pasbuild compile -m blaise-compiler --compiler /tmp/fp_blaise2
compiler/target/blaise --help | head -1             # must print: Blaise Compiler v<X.Y.Z>
```

ALWAYS pass `--compiler` to pasbuild — without it, PasBuild falls back to FPC,
which this project does not use.

## Step 3 — verify the native, internal-assembler, and warm-cache fixpoints

`fixpoint.sh` (Step 2) only exercises the QBE backend. Three more fixpoints
guard the native backend, the in-process internal assembler, and warm-cache
(incremental) rebuilds. Run all three:

```bash
./scripts/fixpoint-native.sh           # must print NATIVE_FIXPOINT_OK
./scripts/fixpoint-native-internal.sh  # must print NATIVE_INTERNAL_OK
./scripts/fixpoint-warmcache.sh        # must print WARMCACHE_FIXPOINT_OK
```

`fixpoint-native.sh` writes the **native stage-2 binary to `/tmp/fpn_blaise2`**
— that is the binary we archive and ship (Step 6), because native is the
default backend. Confirm it prints the right version:

```bash
/tmp/fpn_blaise2 --help | head -1      # must print: Blaise Compiler v<X.Y.Z>
```

If any of the four fixpoints does not print its OK line, **stop**. Show the
user the output and do not proceed. There is no acceptable "almost fixpoint" —
any divergence means the release is not reproducible.

## Step 4 — run the full test suite with the fixpoint binary

Build the TestRunner with the verified stage-2 binary, then run the whole suite
(do NOT use `pasbuild test` — build the runner and invoke it directly so you see
the real total):

```bash
pasbuild test-compile -m blaise-compiler --compiler /tmp/fp_blaise2
compiler/target/TestRunner          # must print: OK (N tests, ...)
```

Note the test count N. If any test fails, stop — do not release.

## Step 5 — commit and tag

Stage `Blaise.pas` whole (its only change is the version), but stage **only the
version-line hunk** of `project.xml` — it frequently carries unrelated working
changes that must not enter the release commit:

```bash
git add compiler/src/main/pascal/Blaise.pas
printf '%s\n' 'y' 'n' 'n' | git add -p project.xml   # stage hunk 1 (version) only
git diff --cached --stat   # MUST show exactly: Blaise.pas | 2 +-  AND  project.xml | 2 +-
```

If `git diff --cached --stat` shows project.xml with more than 2 changed lines,
you swept in unrelated changes — `git restore --staged project.xml` and redo the
`git add -p`. (The hunk-selection answers `y n n` assume the version line is the
first hunk; if project.xml has a different shape, inspect with `git add -p` and
stage only the `<version>` hunk.)

Commit with this pattern (HEREDOC for clean formatting):

```
release: v<X.Y.Z>

<one or two sentences: fixpoint verified on N lines of QBE IR (all four
fixpoints green: QBE, native, internal-asm, warm-cache), the headline themes
of the cycle, and the test count.>
```

Then tag:

```bash
git tag v<X.Y.Z>
```

**Never reference Claude in the commit message.** **Do not push.**
The user pushes manually.

## Step 6 — archive the release binary + refresh the -pre bootstrap binary

Archive the **native** stage-2 binary (`/tmp/fpn_blaise2` from Step 3) — native
is the default backend, so the shipped/bootstrap binary must be native, NOT the
QBE `/tmp/fp_blaise2`:

```bash
mkdir -p releases/v<X.Y.Z>
cp /tmp/fpn_blaise2 releases/v<X.Y.Z>/blaise       # NATIVE binary from fixpoint-native.sh
chmod +x releases/v<X.Y.Z>/blaise
releases/v<X.Y.Z>/blaise --help | head -1          # sanity: Blaise Compiler v<X.Y.Z>
```

The binary alone is enough. The compiler source-builds the RTL into a
target-keyed cache beside itself, so no `blaise_rtl.a` accompanies a release
directory. What a stage-1 bootstrap *does* need is resolvable RTL source —
which the repo checkout provides.

Now **rename the rolling `-pre` directory to the next cycle** and refresh its
binary to this verified build, so cold-bootstrap of `master` stays current for
the dev cycle about to open. `releases/` is gitignored, so this is a plain
filesystem `mv` (no `git mv`):

```bash
# The -pre dir from the previous cycle is named v<X.Y.Z>-pre. Rename it to the
# NEXT minor so the newest releases/v*-pre/ tracks the cycle we are opening.
mv releases/v<X.Y.Z>-pre releases/v<next-minor>.0-pre   # e.g. v0.12.0-pre -> v0.13.0-pre
cp /tmp/fpn_blaise2 releases/v<next-minor>.0-pre/blaise
rm -f releases/v<next-minor>.0-pre/*.bak             # drop any stale backup cruft
releases/v<next-minor>.0-pre/blaise --help | head -1 # sanity check
```

(If no `-pre` directory exists yet, create `releases/v<next-minor>.0-pre/`
directly. The GitHub Actions CI and `rolling-bootstrap.sh` both look for the
newest `releases/v*-pre/`, so the name must be the cycle just opened — not the
one just released.)

Update the test count in `README.adoc` (the "Testing: N tests" line in the
Project Status section) to match the suite total from Step 4, then commit it:

```bash
git add README.adoc
git commit -m "docs: update test count to <N> for v<X.Y.Z>"
```

Then cross-compile the FreeBSD binary and build the **self-contained** release
tarballs for the GitHub Releases page — one for each supported target
(Linux x86_64 and FreeBSD x86_64).

**Tarball layout — self-contained, NOT binary-only.** The native backend
SOURCE-BUILDS the RTL on every link (it does *not* link `blaise_rtl.a`), so a
binary shipped alone cannot compile anything — it fails with `RTL source
directory not found`. Each tarball must therefore bundle the RTL + stdlib
**source** plus a `blaise.cfg` beside the binary so the extracted package works
with zero flags from any directory:

```
blaise-v<X.Y.Z>-<os>-x86_64/
  blaise            the target binary (native)
  blaise.cfg        rtl-src=rtl-src / unit-path=stdlib-src (relative → resolved
                    against this file's own dir, so it works wherever extracted)
  rtl-src/          compiler/src/main/pascal/*.pas  (the RTL units)
  stdlib-src/       stdlib/src/main/pascal/*.pas    (the standard library)
  hello.pas         a sample program
  USAGE.txt         quick-start (the `blaise.cfg` means `./blaise --source
                    hello.pas --output hello` just works)
  README.adoc  NOTICE  LICENSE
```

`blaise.cfg` recognises only `rtl-src=<dir>` and `unit-path=<dir>` (KEY=VALUE,
`#` comments); relative values resolve against the config file's directory, `~`
expands to `$HOME`, absolute paths are used as-is. The compiler reads
`<bindir>/blaise.cfg` first, then `~/.blaise.cfg`.

First cross-compile the FreeBSD binary with the just-archived NATIVE release
binary as stage-1 (same invocation the `freebsd-crosscheck` CI job uses —
`--target freebsd-x86_64` makes a static, freestanding FreeBSD ET_EXEC).

CRITICAL — version timing: the cross-compiled binary bakes in whatever `Version`
(Blaise.pas) and `COMPILER_ID` (uCompilerId.pas) the WORKING TREE currently
holds. This step MUST run BEFORE Step 7's dev-version bump, while the tree is
still at `<X.Y.Z>`. If you build (or rebuild) the FreeBSD tarball AFTER the bump
— e.g. adding it as an afterthought — the binary will report `<next>-SNAPSHOT`.
To rebuild correctly after the bump, first restore the two version files to the
tag, cross-compile, then restore the dev version:

```bash
# Only if the tree has already moved to the -SNAPSHOT dev version:
git checkout v<X.Y.Z> -- compiler/src/main/pascal/Blaise.pas \
                         compiler/src/main/pascal/uCompilerId.pas
# ... run the cross-compile below ...
# then restore the dev version:
git checkout HEAD -- compiler/src/main/pascal/Blaise.pas \
                     compiler/src/main/pascal/uCompilerId.pas
```

```bash
mkdir -p target/freebsd-blaise
releases/v<X.Y.Z>/blaise \
  --source compiler/src/main/pascal/Blaise.pas \
  --backend native --target freebsd-x86_64 \
  --unit-path compiler/src/main/pascal \
  --unit-path runtime/src/main/pascal \
  --unit-path stdlib/src/main/pascal \
  --output target/freebsd-blaise/blaise
# Must be a FreeBSD (EI_OSABI) executable, or stop:
readelf -hW target/freebsd-blaise/blaise | awk -F: '/OS\/ABI/{print $2}' | grep -qi FreeBSD \
  || { echo "ERROR: not a FreeBSD binary"; exit 1; }
# Must report the RELEASE version, not -SNAPSHOT (guards the version-timing trap):
strings target/freebsd-blaise/blaise | grep -q 'blaise-<X.Y.Z>+' \
  || { echo "ERROR: FreeBSD binary is not v<X.Y.Z> — rebuild at the release version"; exit 1; }
```

Then build both tarballs with a shared packaging function:

```bash
# make_tarball <binary-path> <os-label>
make_tarball() {
  BIN="$1"; OS="$2"
  STAGING=$(mktemp -d); DIRNAME="blaise-v<X.Y.Z>-${OS}-x86_64"; D="$STAGING/$DIRNAME"
  mkdir -p "$D/rtl-src" "$D/stdlib-src"
  cp "$BIN"                        "$D/blaise"; chmod +x "$D/blaise"
  cp compiler/src/main/pascal/*.pas "$D/rtl-src/"
  cp stdlib/src/main/pascal/*.pas   "$D/stdlib-src/"
  cp README.adoc "$D/README.adoc"; cp NOTICE "$D/NOTICE"; cp LICENSE "$D/LICENSE"
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
Blaise — self-contained toolchain.  From this directory:
    ./blaise --source hello.pas --output hello && ./hello
The bundled blaise.cfg supplies the RTL + stdlib source locations, so no extra
flags are needed.  If you move `blaise`, keep blaise.cfg / rtl-src/ / stdlib-src/
beside it, or pass --rtl-src DIR --unit-path DIR explicitly.  See README.adoc.
TXT
  tar -czf "releases/blaise-v<X.Y.Z>-${OS}-x86_64.tar.gz" -C "$STAGING" "$DIRNAME"
  rm -rf "$STAGING"
  tar -tzf "releases/blaise-v<X.Y.Z>-${OS}-x86_64.tar.gz" | head   # verify
}

make_tarball releases/v<X.Y.Z>/blaise         linux
make_tarball target/freebsd-blaise/blaise     freebsd
```

Sanity-check each tarball's binary is the right ELF shape (Linux = `UNIX -
System V` / `GNU`, FreeBSD = `UNIX - FreeBSD`); the FreeBSD binary cannot be
executed on the Linux host — the user copies that tarball to a FreeBSD box to
verify. The self-contained layout is validated on the LINUX binary before
shipping (same driver code, target-agnostic RTL-source resolution):

```bash
V=$(mktemp -d); tar -xzf releases/blaise-v<X.Y.Z>-linux-x86_64.tar.gz -C "$V"
( cd "$V/blaise-v<X.Y.Z>-linux-x86_64" && ./blaise --source hello.pas --output /tmp/th && /tmp/th )
rm -rf "$V"   # must print: Hello from Blaise!
```

**Do not `git add` any binary files or the tarballs.** `releases/` is gitignored
and the user keeps binaries local on purpose.

## Step 7 — bump to next -dev version

Edit `compiler/src/main/pascal/Blaise.pas` again, changing `'<X.Y.Z>'` to
`'<next-minor>.0-SNAPSHOT'` (e.g. `0.11.0` → `0.12.0-SNAPSHOT`). Use
`-SNAPSHOT` in BOTH files — the older `-dev` suffix in Blaise.pas was retired so
the two version strings stay in sync.

Also edit `project.xml`, changing `<version>` to `<next-minor>.0-SNAPSHOT`.

REQUIRED: also bump `compiler/src/main/pascal/uCompilerId.pas` back to the
`-SNAPSHOT` form for the new base version, keeping the same `+bif<N>` tag →
`'blaise-<next-minor>.0-SNAPSHOT+bif<N>'`. This keeps `COMPILER_ID` in sync
with project.xml's base version — otherwise `bif-coverage`'s
`TestRun_BifCoverage_NoGaps` fails (it checks the project base version is a
substring of `COMPILER_ID`). Do NOT bump `+bif<N>` here; the `.bif` format
hasn't changed just by opening a dev cycle.

Stage selectively again (project.xml may still carry unrelated changes):

```bash
git add compiler/src/main/pascal/Blaise.pas compiler/src/main/pascal/uCompilerId.pas
printf '%s\n' 'y' 'n' 'n' | git add -p project.xml
git diff --cached --stat   # Blaise.pas, uCompilerId.pas, project.xml — version lines only
git commit -m "chore: begin v<next-minor>.0-dev cycle"
```

### Step 7b — advance the CI bootstrap anchor (REQUIRED, do not skip)

**The anchor must always be the release just cut.** Bump `STAGE1_TAG` in
`.github/workflows/bootstrap.yml` to `v<X.Y.Z>`:

```bash
grep -n "STAGE1_TAG:" .github/workflows/bootstrap.yml   # must read v<X.Y.Z>
```

This was previously worded as a conditional ("when this release becomes the
baseline"), which is how the anchor silently drifted: v0.13.0 shipped while CI
still cold-started from v0.12.0, so every rolling bootstrap replayed a far
longer commit range than necessary. Treat it as mandatory.

Two reasons it matters beyond replay length:

* The anchor's **published tarball** is what CI downloads. It must exist on the
  GitHub Releases page (`gh release view v<X.Y.Z>`) before CI can cold-start
  from it — so this bump lands *after* the release is published, not before.
* Anchors older than v0.13.0 required a `blaise_rtl.a` beside the binary; from
  v0.13.0 the binary source-builds the RTL and the tarball ships no archive.
  Never move the anchor *backwards* across that boundary.

This is a CI-only change and lands in its own commit alongside the release.

## Step 8 — write community post and changelog

Write two documents at the project root. Both are untracked (do not `git add`
them) — they are working files the user edits and publishes manually.

Both documents cover **only the commits between the previous release tag and
the tag being cut now** — the range `<prev-tag>..v<X.Y.Z>`, where `<prev-tag>`
is the most recent existing release tag before this one. Find it with
`git describe --tags --abbrev=0 v<X.Y.Z>^` (the latest tag reachable from the
commit just before the release commit), or `git tag --sort=-v:refname | head`.
Do NOT summarise the whole history — only this cycle's delta.

Survey the commits first (the `v<X.Y.Z>` tag already exists from Step 5):
`git log <prev-tag>..v<X.Y.Z> --oneline`, and group by theme. Helpful groupings:
`git log <prev-tag>..v<X.Y.Z> --oneline | grep ' feat'` (features),
`... | grep ' fix'` (fixes), `... | grep ' perf'` (performance).

### community-post-v<X.Y.Z>.md

A warm, readable announcement for the Blaise community (forums, mailing lists,
social media). Style:

- **Not** a commit-by-commit log — group changes into themes with a clear
  headline win up top.
- Sprinkle emoji throughout section headings and milestone call-outs.
- Warm, collaborative voice; British English spelling (see the global writing
  style guide).
- Include **tiny code examples** for the headline language features — a 3–6
  line snippet per feature is far more compelling than prose. VERIFY each
  snippet actually compiles before publishing: write it to `/tmp/snip.pas` and
  run `compiler/target/blaise --source /tmp/snip.pas --output /tmp/snip` (try
  both `--backend qbe` and `--backend native` for codegen-sensitive features).
- Cover: headline win(s), language/stdlib additions, bug-fix hardening, notable
  compiler internals, the fixpoint line count and test count, and a closing
  call to action pointing at the GitHub release page.
- End with a forward-looking line ("Onwards to v<next>! 🙌").
- Reference `changelog-v<X.Y.Z>.md` for full details.

### changelog-v<X.Y.Z>.md

A technical changelog for the GitHub Releases page. Style:

- Grouped by area (Native backend, Toolchain, Language, ARC/runtime, stdlib,
  Codegen, Semantic, Debugging, Performance, Tooling/CI).
- Each entry is one concise line: what changed and why it matters. More
  technical than the community post.
- A short "Examples" block under the Language section showing the new syntax is
  welcome (same verify-it-compiles rule applies).
- Close with the fixpoint IR line count and the test count.

## Step 9 — report to the user

Summarise:

- Tag created (e.g. `v<X.Y.Z>`)
- Stage-2 IR line count and all four OK lines: "FIXPOINT_OK / NATIVE_FIXPOINT_OK
  / NATIVE_INTERNAL_OK / WARMCACHE_FIXPOINT_OK"
- Test count (N tests passing)
- Binary path: `releases/v<X.Y.Z>/blaise` (note: not in git)
- `-pre` bootstrap binary refreshed
- New dev version on master
- Last 3–4 commit oneliners
- Community post: `community-post-v<X.Y.Z>.md` (untracked)
- Changelog: `changelog-v<X.Y.Z>.md` (untracked)
- Release tarballs (upload both to GitHub Releases):
  - `releases/blaise-v<X.Y.Z>-linux-x86_64.tar.gz`
  - `releases/blaise-v<X.Y.Z>-freebsd-x86_64.tar.gz` (cross-compiled; user
    verifies on a FreeBSD box — self-contained, includes RTL + stdlib source +
    blaise.cfg)

Mention that the user must `git push --tags` themselves if they want the tag on
the remote — never push automatically.

## Common pitfalls

- **Unrelated changes swept into the release commit.** `git add project.xml`
  stages the WHOLE file, including pre-existing build-option edits. Always
  `git add -p` and confirm `git diff --cached --stat` shows exactly two
  one-line changes before committing. (This bit the v0.11.0 cut — the commit had
  to be reset and redone.)
- **Archiving the QBE binary instead of the native one.** Native is the default
  backend, so the shipped/bootstrap binary must be `/tmp/fpn_blaise2` (from
  `fixpoint-native.sh`), NOT the QBE `/tmp/fp_blaise2` (from `fixpoint.sh`). The
  QBE fixpoint is still required as a reproducibility guard — it just isn't the
  artefact.
- **Shipping a binary-only tarball.** The native backend source-builds the RTL,
  so a tarball with just `blaise` CANNOT compile
  anything once extracted — it dies with `RTL source directory not found`. Every
  release tarball must bundle `rtl-src/` (compiler/src/main/pascal) + `stdlib-src/`
  (stdlib/src/main/pascal) + a `blaise.cfg` beside the binary (Step 6). Verify by
  extracting the Linux tarball to a temp dir and compiling `hello.pas` from there
  — it must print output, not an RTL-not-found error.
- **Running the FreeBSD binary on the Linux host.** The FreeBSD tarball binary is
  a FreeBSD ET_EXEC and cannot execute on Linux — only sanity-check its ELF shape
  (`readelf -hW … | grep FreeBSD`). The self-contained layout is validated on the
  LINUX binary (same driver code); the user runs the FreeBSD tarball on a FreeBSD
  box.
- **FreeBSD binary reports `-SNAPSHOT`.** The cross-compiled binary bakes in the
  working-tree `Version`/`COMPILER_ID`. The FreeBSD cross-compile (Step 6) MUST
  run before Step 7's dev-version bump. If you build/rebuild it after the bump,
  the binary is `<next>-SNAPSHOT`, not the release version. Check the FreeBSD
  binary can't run locally, so verify with `strings … | grep 'blaise-<X.Y.Z>+'`.
  To fix: `git checkout v<X.Y.Z> -- Blaise.pas uCompilerId.pas`, re-cross-compile,
  rebuild the tarball, then `git checkout HEAD -- Blaise.pas uCompilerId.pas`.
  (The Linux release binary is immune — it's archived from the fixpoint in Step 6
  before the bump.)
- **Stale fixpoint binary in /tmp.** A `/tmp/fpn_blaise2` (or `/tmp/fp_blaise3`)
  left over from an earlier run can be days old. Always confirm the binary you
  archive prints the RIGHT version: `<binary> --help | head -1`.
- **COMPILER_ID out of sync with project.xml → bif-coverage fails.** At release
  `COMPILER_ID` drops `-SNAPSHOT`; at the dev-cycle bump it must re-gain
  `-SNAPSHOT` for the NEW base version. The base version in `COMPILER_ID` must
  always match project.xml's `<version>` base, or `TestRun_BifCoverage_NoGaps`
  fails. Keep the `+bif<N>` tag unchanged unless the `.bif` format changed.
- **Forgetting to rename the -pre dir.** The newest `releases/v*-pre/` must name
  the cycle being OPENED, not the one just released. After cutting v<X.Y.Z>,
  `mv releases/v<X.Y.Z>-pre releases/v<next-minor>.0-pre` (filesystem move —
  releases/ is gitignored). CI and rolling-bootstrap pick the newest by name.
- **`compiler/target/blaise` still on the old version.** `fixpoint.sh` does not
  rebuild it; do the `pasbuild compile --compiler /tmp/fp_blaise2` step (Step 2)
  before the native fixpoints, or they run against the previous version.
- **Forgetting `--compiler`.** Every `pasbuild` command must pass
  `--compiler <blaise-binary>`; without it PasBuild falls back to FPC, which is
  not part of this toolchain.
- **Assuming `blaise_rtl.a` must sit beside `--compiler`.** It must not and
  need not — the compiler source-builds the RTL into `rtl/<target>/` beside
  itself. There is no `FindRTL`. A relocated binary needs resolvable RTL
  *source* instead (`--rtl-src DIR` / `$BLAISE_RTL_SRC`), not an archive.
- **Wrong working directory.** All `pasbuild` commands fail outside the project
  root with a confusing version error. Stay at `/data/devel/new-pascal-compiler`.
- **Backgrounded fixpoint output drops.** Run the fixpoint scripts in the
  foreground with a generous timeout (600000 ms). Self-built compilation of the
  compiler takes ~2 min per stage.
