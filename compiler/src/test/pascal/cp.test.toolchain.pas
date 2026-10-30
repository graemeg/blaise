{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.toolchain;

{ Tests for host-aware external-tool resolution (uToolchain.ResolveSpec) and
  the target host/extension helpers it relies on.

  ResolveSpec resolves a tool, per candidate, in this order:
    1. EnvVar override (verbatim)                         — not exercised here
       (no setenv binding in the test RTL; the override branch is a simple
        GetEnvironmentVariable + FileExists guard).
    2. $BLAISE_TOOLCHAIN_PREFIX + candidate               — env-driven, skipped
    3. cross-triple prefix on $PATH (cross builds only)
    4. bare candidate on $PATH — host tools always, target tools native-only
    5. actionable fallback name

  The behaviour these tests pin is the part that is independent of the
  environment: the host-tool-vs-target-tool cross-suppression (step 4), the
  fallback naming (step 5), and the pure host/extension helpers. }

interface

uses
  blaise.testing, sysutils, process,
  blaise.codegen.target, uToolchain;

type
  TToolchainTests = class(TTestCase)
  private
    { Build a linker-like target tool spec (HostTool=False) with a mingw
      cross prefix, the shape TBackendDriver.LinkerToolSpec produces. }
    function MakeLinkerSpec: TToolSpec;
    { Build a host tool spec (HostTool=True, e.g. llc) — runs anywhere. }
    function MakeHostToolSpec: TToolSpec;
    function LinuxTarget: TTargetDesc;
    function WindowsTarget: TTargetDesc;
    { A fresh, empty scratch directory (with a trailing '/'). }
    function ScratchDir(const ATag: string): string;
    { Run a program with arguments and wait for it. }
    procedure Run(const AExe: string; const AArgs: array of string);
  published
    { ---- pure helpers ---- }
    procedure TestExecutableExtension_Windows_IsExe;
    procedure TestExecutableExtension_Linux_IsEmpty;
    procedure TestHostTarget_OnThisHost_MatchesUname;
    procedure TestHostExeExt_OnThisHost_IsEmpty;

    { ---- ResolveSpec: native (non-cross) build ---- }
    { A target tool resolves to a real $PATH binary on a native build. }
    procedure TestResolveSpec_NativeLinker_FindsCcOnPath;

    { ---- ResolveSpec: cross build, target tool ---- }
    { Cross + target tool + no cross-linker installed: the bare host fallback
      is SUPPRESSED, so we never resolve to the host cc for a Windows output;
      the actionable cross-prefixed name is returned instead. }
    procedure TestResolveSpec_CrossLinker_DoesNotFallBackToHostCc;
    procedure TestResolveSpec_CrossLinker_FallbackIsCrossPrefixed;

    { ---- ResolveSpec: cross build, host tool ---- }
    { Cross + host tool: a bare $PATH match IS allowed (host tools run on the
      host and target via flags), so a host tool still resolves. }
    procedure TestResolveSpec_CrossHostTool_AllowsBarePathMatch;

    { ---- the compiler's own location (GH #251, discussion #245) ----
      Started via $PATH, argv[0] is the bare name; started via a symlink, it
      is the link.  Both must lead back to the real install directory, which
      holds blaise.cfg, the RTL sources and the RTL object cache. }
    procedure TestResolveExePath_BareName_SearchesPath;
    procedure TestResolveExePath_BareName_NotOnPath_IsEmpty;
    procedure TestResolveExePath_RelativePath_JoinsCwd;
    procedure TestResolveExePath_Symlink_ResolvesToTarget;
    procedure TestResolveExePath_SymlinkChain_ResolvesToTarget;
    procedure TestExecutablePath_IsTheRunningBinary;

    { ---- where the compiled RTL is cached ----
      --rtl-cache, then rtl-cache= in blaise.cfg, then $BLAISE_RTL_CACHE,
      then <bindir>/rtl when the binary's directory is writable, else
      $XDG_CACHE_HOME/blaise/rtl, else $HOME/.cache/blaise/rtl. }
    procedure TestRTLCacheRoot_ExplicitChoicesInOrder;
    procedure TestRTLCacheRoot_WritableBinDir_IsBesideBinary;
    procedure TestRTLCacheRoot_UnwritableBinDir_UsesUserCache;
    procedure TestRTLCacheRoot_NowhereToGo_IsEmpty;
  end;

implementation

function TToolchainTests.MakeLinkerSpec: TToolSpec;
begin
  Result.Name := 'linker';
  Result.EnvVar := 'BLAISE_LINKER';
  SetLength(Result.Cands, 2);
  Result.Cands[0] := 'cc';
  Result.Cands[1] := 'clang';
  Result.CrossPrefix := 'x86_64-w64-mingw32-';
  Result.HostTool := False;
end;

function TToolchainTests.MakeHostToolSpec: TToolSpec;
begin
  { 'cc' is guaranteed present on $PATH in the build environment, so it makes
    a reliable stand-in for a host tool (llc) that resolves by bare name. }
  Result.Name := 'hosttool';
  Result.EnvVar := 'BLAISE_HOSTTOOL';
  SetLength(Result.Cands, 1);
  Result.Cands[0] := 'cc';
  Result.CrossPrefix := 'x86_64-w64-mingw32-';
  Result.HostTool := True;
end;

function TToolchainTests.LinuxTarget: TTargetDesc;
begin
  MakeTarget(osLinux, cpuX86_64, Result);
end;

function TToolchainTests.WindowsTarget: TTargetDesc;
begin
  MakeTarget(osWindows, cpuX86_64, Result);
end;

{ ---- pure helpers ---- }

procedure TToolchainTests.TestExecutableExtension_Windows_IsExe;
begin
  AssertEquals('Windows target → .exe', '.exe',
    ExecutableExtension(Self.WindowsTarget()));
end;

procedure TToolchainTests.TestExecutableExtension_Linux_IsEmpty;
begin
  AssertEquals('Linux target → no extension', '',
    ExecutableExtension(Self.LinuxTarget()));
end;

procedure TToolchainTests.TestHostTarget_OnThisHost_MatchesUname;
var
  Proc:  TProcess;
  Chunk: string;
  Uname: string;
  Expected: TTargetOS;
begin
  { HostTarget is a COMPILE-TIME property of the binary (target-driven
    defines).  Verify the baked-in identity matches the OS the suite is
    actually running on, as reported by uname(1) — a genuine round-trip
    check that works unchanged on every POSIX host.  The inline
    HostTarget().OS read as an AssertEquals argument also exercises the
    native sret-call-field-arg path fixed alongside this work. }
  Proc := TProcess.Create(nil);
  Proc.Executable := 'uname';
  Proc.Parameters.Add('-s');
  Proc.Execute();
  Uname := '';
  repeat
    Chunk := Proc.ReadOutput();
    Uname := Uname + Chunk
  until (Chunk = '') and not Proc.Running;
  Proc.WaitOnExit();
  Proc.Free();
  Uname := Trim(Uname);
  if Uname = 'FreeBSD' then
    Expected := osFreeBSD
  else if Uname = 'Darwin' then
    Expected := osMacOS
  else
    Expected := osLinux;
  AssertEquals('host OS matches uname (' + Uname + ')',
    Ord(Expected), Ord(HostTarget().OS));
end;

procedure TToolchainTests.TestHostExeExt_OnThisHost_IsEmpty;
begin
  AssertEquals('no host exe extension on a unix host', '', HostExeExt());
end;

{ ---- ResolveSpec: native build ---- }

procedure TToolchainTests.TestResolveSpec_NativeLinker_FindsCcOnPath;
var
  Resolved: string;
begin
  { Native build: the linker is a target tool, but the target IS the host
    (HostTarget, whatever this suite was built for), so the bare $PATH lookup
    applies and finds a real cc/clang. }
  Resolved := ResolveSpec(Self.MakeLinkerSpec(), HostTarget());
  AssertTrue('resolved to an absolute path on $PATH (found cc/clang)',
    (Length(Resolved) > 0) and (Resolved[0] = '/'));
end;

{ ---- ResolveSpec: cross build, target tool ---- }

procedure TToolchainTests.TestResolveSpec_CrossLinker_DoesNotFallBackToHostCc;
var
  Resolved: string;
begin
  { Cross-compiling to Windows from a linux host.  The mingw cross-linker is
    not installed in the build environment, so resolution must NOT silently
    fall back to the host /usr/bin/cc — that would link Windows output with
    the host linker.  The result must therefore not be an absolute host path. }
  Resolved := ResolveSpec(Self.MakeLinkerSpec(), Self.WindowsTarget());
  AssertTrue('cross target tool did not resolve to a host path',
    not ((Length(Resolved) > 0) and (Resolved[0] = '/')));
end;

procedure TToolchainTests.TestResolveSpec_CrossLinker_FallbackIsCrossPrefixed;
var
  Resolved: string;
begin
  { With no installed cross tool, the fallback (step 5) names the
    cross-prefixed first candidate so the exec-time error is actionable. }
  Resolved := ResolveSpec(Self.MakeLinkerSpec(), Self.WindowsTarget());
  AssertEquals('fallback is the cross-prefixed first candidate',
    'x86_64-w64-mingw32-cc', Resolved);
end;

{ ---- ResolveSpec: cross build, host tool ---- }

procedure TToolchainTests.TestResolveSpec_CrossHostTool_AllowsBarePathMatch;
var
  Resolved: string;
begin
  { A host tool may resolve to a bare $PATH binary even when cross-compiling,
    because it runs on the host and targets via flags.  The stand-in ('cc') is
    on $PATH, so it must resolve to an absolute path despite the Windows
    target. }
  Resolved := ResolveSpec(Self.MakeHostToolSpec(), Self.WindowsTarget());
  AssertTrue('host tool resolves to a $PATH binary even when cross',
    (Length(Resolved) > 0) and (Resolved[0] = '/'));
end;

var
  GScratchCounter: Int = 0;

function TToolchainTests.ScratchDir(const ATag: string): string;
begin
  Result := IncludeTrailingPathDelimiter(GetTempDir()) + 'blz_exepath_' +
    ATag + '_' + IntToStr(GScratchCounter) + '/';
  GScratchCounter := GScratchCounter + 1;
  Run('/bin/rm', ['-rf', Result]);
  ForceDirectories(Result);
end;

procedure TToolchainTests.Run(const AExe: string; const AArgs: array of string);
var
  Proc: TProcess;
  I: Int;
begin
  Proc := TProcess.Create(nil);
  try
    Proc.Executable := AExe;
    for I := 0 to High(AArgs) do
      Proc.Parameters.Add(AArgs[I]);
    Proc.Execute();
    repeat
    until (Proc.ReadOutput() = '') and not Proc.Running;
    Proc.WaitOnExit();
  finally
    Proc.Free();
  end;
end;

procedure TToolchainTests.TestResolveExePath_BareName_SearchesPath;
var
  D: string;
begin
  D := ScratchDir('path');
  ForceDirectories(D + 'bin');
  WriteFile(D + 'bin/blz', '');
  AssertEquals('a bare name is found on the PATH list', D + 'bin/blz',
    ResolveExecutablePath('blz', '/nonexistent:' + D + 'bin', '/'));
end;

procedure TToolchainTests.TestResolveExePath_BareName_NotOnPath_IsEmpty;
begin
  AssertEquals('a bare name on no PATH entry is unknown', '',
    ResolveExecutablePath('blz-not-anywhere', '/nonexistent', '/'));
end;

procedure TToolchainTests.TestResolveExePath_RelativePath_JoinsCwd;
var
  D: string;
begin
  D := ScratchDir('rel');
  ForceDirectories(D + 'sub');
  WriteFile(D + 'sub/blz', '');
  AssertEquals('a path with a slash is relative to the working directory',
    D + 'sub/blz', ResolveExecutablePath('sub/blz', '', D));
  AssertEquals('an absolute path is kept', D + 'sub/blz',
    ResolveExecutablePath(D + 'sub/blz', '', '/'));
end;

procedure TToolchainTests.TestResolveExePath_Symlink_ResolvesToTarget;
var
  D: string;
begin
  D := ScratchDir('link');
  ForceDirectories(D + 'install');
  ForceDirectories(D + 'bin');
  WriteFile(D + 'install/blz', '');
  Run('/bin/ln', ['-s', '../install/blz', D + 'bin/blz']);
  AssertEquals('a relative symlink found on PATH resolves to its target',
    D + 'install/blz', ResolveExecutablePath('blz', D + 'bin', '/'));
end;

procedure TToolchainTests.TestResolveExePath_SymlinkChain_ResolvesToTarget;
var
  D: string;
begin
  D := ScratchDir('chain');
  ForceDirectories(D + 'install');
  ForceDirectories(D + 'mid');
  ForceDirectories(D + 'bin');
  WriteFile(D + 'install/blz', '');
  Run('/bin/ln', ['-s', D + 'install/blz', D + 'mid/blz']);
  Run('/bin/ln', ['-s', '../mid/blz', D + 'bin/blz']);
  AssertEquals('every link in a chain is followed', D + 'install/blz',
    ResolveExecutablePath(D + 'bin/blz', '', '/'));
end;

procedure TToolchainTests.TestExecutablePath_IsTheRunningBinary;
var
  P: string;
begin
  P := ExecutablePath();
  AssertTrue('absolute: ' + P, Copy(P, 0, 1) = '/');
  AssertTrue('exists: ' + P, FileExists(P));
  AssertEquals('names the running binary', 'TestRunner', ExtractFileName(P));
end;

procedure TToolchainTests.TestRTLCacheRoot_ExplicitChoicesInOrder;
begin
  AssertEquals('--rtl-cache wins', '/cli',
    ChooseRTLCacheRoot('/cli', '/cfg', '/env', '/bin/', True, '/xdg', '/home'));
  AssertEquals('then rtl-cache= in blaise.cfg', '/cfg',
    ChooseRTLCacheRoot('', '/cfg', '/env', '/bin/', True, '/xdg', '/home'));
  AssertEquals('then $BLAISE_RTL_CACHE', '/env',
    ChooseRTLCacheRoot('', '', '/env', '/bin/', False, '', ''));
end;

procedure TToolchainTests.TestRTLCacheRoot_WritableBinDir_IsBesideBinary;
begin
  AssertEquals('beside a writable binary, as before', '/opt/blaise/rtl',
    ChooseRTLCacheRoot('', '', '', '/opt/blaise/', True, '/xdg', '/home'));
end;

procedure TToolchainTests.TestRTLCacheRoot_UnwritableBinDir_UsesUserCache;
begin
  AssertEquals('$XDG_CACHE_HOME first', '/xdg/blaise/rtl',
    ChooseRTLCacheRoot('', '', '', '/usr/local/blaise/', False, '/xdg', '/home/u'));
  AssertEquals('a relative $XDG_CACHE_HOME is ignored, as the spec says',
    '/home/u/.cache/blaise/rtl',
    ChooseRTLCacheRoot('', '', '', '/usr/local/blaise/', False, 'rel', '/home/u'));
  AssertEquals('else ~/.cache', '/home/u/.cache/blaise/rtl',
    ChooseRTLCacheRoot('', '', '', '/usr/local/blaise/', False, '', '/home/u/'));
end;

procedure TToolchainTests.TestRTLCacheRoot_NowhereToGo_IsEmpty;
begin
  AssertEquals('no writable choice at all', '',
    ChooseRTLCacheRoot('', '', '', '/usr/local/blaise/', False, '', ''));
end;

initialization
  RegisterTest(TToolchainTests);

end.
