{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Platform.Info: OSDisplayName maps the compiler's OS tokens to
  their proper product spellings, and TargetOSDisplayName applies it to the
  target this test program was built for. }

unit PlatformInfo.Tests;

interface

uses
  blaise.testing, SysUtils, Platform.Info;

type
  TPlatformInfoTests = class(TTestCase)
  published
    procedure TestOSDisplayName_KnownTokens;
    procedure TestOSDisplayName_IsCaseInsensitive;
    procedure TestOSDisplayName_UnknownPassesThrough;
    procedure TestOSDisplayName_Empty;
    procedure TestTargetOSDisplayName_MatchesTargetOS;
  end;

implementation

procedure TPlatformInfoTests.TestOSDisplayName_KnownTokens;
begin
  AssertEquals('macOS', OSDisplayName('macos'));
  AssertEquals('Linux', OSDisplayName('linux'));
  AssertEquals('FreeBSD', OSDisplayName('freebsd'));
  AssertEquals('Windows', OSDisplayName('windows'));
end;

procedure TPlatformInfoTests.TestOSDisplayName_IsCaseInsensitive;
begin
  AssertEquals('macOS', OSDisplayName('MacOS'));
  AssertEquals('FreeBSD', OSDisplayName('FREEBSD'));
end;

procedure TPlatformInfoTests.TestOSDisplayName_UnknownPassesThrough;
begin
  AssertEquals('haiku', OSDisplayName('haiku'));
end;

procedure TPlatformInfoTests.TestOSDisplayName_Empty;
begin
  AssertEquals('', OSDisplayName(''));
end;

procedure TPlatformInfoTests.TestTargetOSDisplayName_MatchesTargetOS;
begin
  AssertEquals(OSDisplayName(TargetOS), TargetOSDisplayName());
  AssertTrue('a known target has a real display name',
    TargetOSDisplayName() <> TargetOS);
end;

initialization
  RegisterTest(TPlatformInfoTests);

end.
