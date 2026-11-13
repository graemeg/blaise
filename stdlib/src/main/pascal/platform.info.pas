{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Platform.Info - presentation helpers for the build target.

  The compiler folds the target into two string constants of the implicit
  System unit, TargetOS ('linux', 'freebsd', 'windows', 'macos') and
  TargetCPU ('x86_64', 'i386', 'arm64').  They are lower-case identifiers,
  meant for comparison and file names.  This unit turns an OS token into the
  spelling a person expects to read, e.g. in an About box:

    Caption := 'Running on ' + TargetOSDisplayName() + ' ' + TargetCPU;

  Both describe the target the program was BUILT for, which is not always
  the machine it runs on (a cross-compiled binary, a compatibility layer). }

unit Platform.Info;

interface

{ The display name for an OS token as spelled by TargetOS: 'macos' gives
  'macOS', 'freebsd' gives 'FreeBSD'.  Matching ignores case; an unknown
  token is returned unchanged. }
function OSDisplayName(const AOS: string): string;

{ OSDisplayName(TargetOS): the build target's OS, ready to show. }
function TargetOSDisplayName: string;

implementation

uses
  SysUtils;

function OSDisplayName(const AOS: string): string;
var
  Lower: string;
begin
  Lower := LowerCase(AOS);
  if Lower = 'macos' then
    Result := 'macOS'
  else if Lower = 'linux' then
    Result := 'Linux'
  else if Lower = 'freebsd' then
    Result := 'FreeBSD'
  else if Lower = 'windows' then
    Result := 'Windows'
  else
    Result := AOS;
end;

function TargetOSDisplayName: string;
begin
  Result := OSDisplayName(TargetOS);
end;

end.
