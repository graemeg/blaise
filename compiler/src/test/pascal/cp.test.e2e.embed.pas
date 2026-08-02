{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.embed;

(* E2E tests for the compile-time file-embedding directives, EMBED (byte
   array) and EMBEDSTR (string).

   The IR-level suite (cp.test.embed) proves the lexer expansion produces
   the right elements.  It cannot prove the bytes survive the trip into the
   data section and back out at run time -- that needs a compiled, executed
   binary, which is what these tests do on both backends.

   Fixtures are written to an absolute path and referenced by absolute path,
   because the e2e harness lexes in memory with no source-file anchor, so a
   relative embed path would resolve against the process CWD.

   Design: docs/embedded-resources-design.adoc *)

interface

uses
  Classes, SysUtils, Streams, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EEmbedTests = class(TE2ETestCase)
  private
    FDir: string;
    function WriteFixture(const AName, AContent: string): string;
  public
    procedure SetUp; override;
  published
    { EMBEDSTR round-trips a text asset through the binary }
    procedure TestRun_EmbedStr_TextRoundTrips;
    procedure TestRun_EmbedStr_LengthIsExact;
    procedure TestRun_EmbedStr_BinaryBytesSurvive;

    { EMBED round-trips a byte asset through the binary }
    procedure TestRun_Embed_BytesReadableAtRuntime;
    procedure TestRun_Embed_HighBytesAreUnsigned;
    procedure TestRun_Embed_LengthMatchesFileSize;
    procedure TestRun_Embed_LargeAssetIsIntact;

    { A hand-written unbounded const array -- the form is general, not an
      embed-only special case }
    procedure TestRun_UnboundedArrayConst_HandWritten;

    { An embedded const exported from a UNIT interface, so the constant
      round-trips through the .bif on its way to the importing program }
    procedure TestRun_Embed_InUnitInterface_CrossesBif;
  end;

implementation

const
  LE = #10;

procedure TE2EEmbedTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-embed');
  FDir := '/tmp/blaise-embed-e2e';
  if not DirectoryExists(FDir) then
    ForceDirectories(FDir);
end;

function TE2EEmbedTests.WriteFixture(const AName, AContent: string): string;
var
  F: TFileOutputStream;
  P: string;
begin
  P := FDir + '/' + AName;
  F := TFileOutputStream.Create(P);
  try
    if Length(AContent) > 0 then
      F.Write(PChar(AContent), Length(AContent));
  finally
    F.Close();
    F.Free();
  end;
  Result := P;
end;

{ ------------------------------------------------------------------ }
{ EMBEDSTR                                                             }
{ ------------------------------------------------------------------ }

procedure TE2EEmbedTests.TestRun_EmbedStr_TextRoundTrips;
begin
  WriteFixture('greet.txt', 'Hello from the data section');
  AssertRunsOnAll(
    '''
    program P;
    const S: string = {$EMBEDSTR '/tmp/blaise-embed-e2e/greet.txt'};
    begin
      WriteLn(S)
    end.
    ''', 'Hello from the data section' + LE, 0);
end;

procedure TE2EEmbedTests.TestRun_EmbedStr_LengthIsExact;
begin
  { A trailing newline must be preserved -- a TStringList round-trip inside
    the compiler would silently drop it, and the length is how that shows. }
  WriteFixture('len.txt', 'abc' + LE);
  AssertRunsOnAll(
    '''
    program P;
    const S: string = {$EMBEDSTR '/tmp/blaise-embed-e2e/len.txt'};
    begin
      WriteLn(Length(S))
    end.
    ''', '4' + LE, 0);
end;

procedure TE2EEmbedTests.TestRun_EmbedStr_BinaryBytesSurvive;
begin
  { Blaise strings are length-counted, so an embedded NUL must not truncate
    the constant the way a C string would.  Indices are 0-based. }
  WriteFixture('nul.bin', 'a' + Chr(0) + 'b');
  AssertRunsOnAll(
    '''
    program P;
    const S: string = {$EMBEDSTR '/tmp/blaise-embed-e2e/nul.bin'};
    begin
      WriteLn(Length(S));
      WriteLn(Ord(S[0]));
      WriteLn(Ord(S[1]));
      WriteLn(Ord(S[2]))
    end.
    ''', '3' + LE + '97' + LE + '0' + LE + '98' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ EMBED                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EEmbedTests.TestRun_Embed_BytesReadableAtRuntime;
begin
  WriteFixture('abc.bin', 'ABC');
  AssertRunsOnAll(
    '''
    program P;
    const B: array of Byte = {$EMBED '/tmp/blaise-embed-e2e/abc.bin'};
    begin
      WriteLn(B[0]);
      WriteLn(B[1]);
      WriteLn(B[2])
    end.
    ''', '65' + LE + '66' + LE + '67' + LE, 0);
end;

procedure TE2EEmbedTests.TestRun_Embed_HighBytesAreUnsigned;
begin
  { The signed-byte trap: 200 and 255 must arrive as themselves, not as
    negative values, all the way through to the emitted data. }
  WriteFixture('high.bin', Chr(200) + Chr(255) + Chr(128));
  AssertRunsOnAll(
    '''
    program P;
    const B: array of Byte = {$EMBED '/tmp/blaise-embed-e2e/high.bin'};
    begin
      WriteLn(B[0]);
      WriteLn(B[1]);
      WriteLn(B[2])
    end.
    ''', '200' + LE + '255' + LE + '128' + LE, 0);
end;

procedure TE2EEmbedTests.TestRun_Embed_LengthMatchesFileSize;
begin
  WriteFixture('five.bin', 'ABCDE');
  AssertRunsOnAll(
    '''
    program P;
    const B: array of Byte = {$EMBED '/tmp/blaise-embed-e2e/five.bin'};
    begin
      WriteLn(High(B) - Low(B) + 1)
    end.
    ''', '5' + LE, 0);
end;

procedure TE2EEmbedTests.TestRun_Embed_LargeAssetIsIntact;
var
  Blob: string;
  I:    Integer;
  Sum:  Integer;
begin
  { A payload big enough to span more than a handful of data items, with a
    known checksum so a dropped or reordered byte is caught.  1024 bytes
    cycling 0..255 -- sum is 4 * (0+1+...+255) = 4 * 32640 = 130560. }
  Blob := '';
  Sum := 0;
  for I := 0 to 1023 do
  begin
    Blob := Blob + Chr(I mod 256);
    Sum := Sum + (I mod 256);
  end;
  WriteFixture('large.bin', Blob);
  AssertRunsOnAll(
    '''
    program P;
    const B: array of Byte = {$EMBED '/tmp/blaise-embed-e2e/large.bin'};
    var I, Total: Integer;
    begin
      Total := 0;
      for I := Low(B) to High(B) do
        Total := Total + B[I];
      WriteLn(High(B) - Low(B) + 1);
      WriteLn(Total)
    end.
    ''', '1024' + LE + '130560' + LE, 0);
end;

procedure TE2EEmbedTests.TestRun_UnboundedArrayConst_HandWritten;
begin
  { 'array of T' with bounds derived from the value list is a general const
    form, reachable without any directive.  Pinning it here keeps the two
    users of that parser path honest: if the unbounded form were ever made
    embed-only, this test fails rather than the behaviour silently narrowing. }
  AssertRunsOnAll(
    '''
    program P;
    const A: array of Integer = (10, 20, 30);
    begin
      WriteLn(High(A) - Low(A) + 1);
      WriteLn(A[0] + A[2])
    end.
    ''', '3' + LE + '40' + LE, 0);
end;

procedure TE2EEmbedTests.TestRun_Embed_InUnitInterface_CrossesBif;
var
  Output: string;
  RCode:  Integer;
begin
  { An embedded constant declared in a unit INTERFACE is serialised into the
    unit's .bif and read back when the program imports it.  The bounds are
    resolved at parse time, before serialisation, so they must survive the
    round trip -- if they were carried as a parse-time-only flag that codegen
    later re-derived, the importing side would see a zero-length array. }
  WriteFixture('unitasset.bin', 'XYZ');
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithUnit('eu',
    '''
    unit eu;
    interface
    const Blob: array of Byte = {$EMBED '/tmp/blaise-embed-e2e/unitasset.bin'};
    implementation
    end.
    ''',
    '''
    program M;
    uses eu;
    begin
      WriteLn(High(Blob) - Low(Blob) + 1);
      WriteLn(Blob[0]);
      WriteLn(Blob[2])
    end.
    ''', Output, RCode));
  AssertEquals('exit code', 0, RCode);
  AssertEquals('length and bytes survive the .bif',
               '3' + LE + '88' + LE + '90', Trim(Output));
end;

initialization
  RegisterTest(TE2EEmbedTests);

end.
