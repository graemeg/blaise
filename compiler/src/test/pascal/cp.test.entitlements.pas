{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.entitlements;

{ Entitlements in the internal ad-hoc signer (blaise.entitlements,
  TMachOExecWriter.SetEntitlements).

  The DER oracle strings are the CSSLOT_DER_ENTITLEMENTS payloads Apple's
  codesign wrote for the same plists (codesign -s - --entitlements, macOS 27
  arm64, 2026-10-22), so the encoder is held to codesign's exact bytes:
  key order, length forms and integer encoding.  The signature test checks
  the SuperBlob shape codesign uses (CodeDirectory, requirements,
  entitlements, DER entitlements) and that every special-slot hash covers
  its blob.  The e2e test in cp.test.e2e.sepcompile has macOS itself read
  the entitlements back. }

interface

uses
  blaise.testing, SysUtils, uStrCompat, blaise.entitlements, blaise.sha256,
  blaise.machowriter;

type
  TEntitlementsTests = class(TTestCase)
  published
    procedure TestDer_GetTaskAllow_MatchesCodesign;
    { several keys out of order, false, an escaped string, positive and
      negative integers, an array and a nested dict }
    procedure TestDer_RichPlist_MatchesCodesign;
    procedure TestDer_UnsupportedValue_Rejected;
    procedure TestDer_NotAPlist_Rejected;
    procedure TestSignature_EntitlementsInSpecialSlots;
  end;

implementation

const
  RichPlist =
    '''
    <?xml version="1.0" encoding="UTF-8"?>
    <!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
    <plist version="1.0">
    <dict>
    	<key>zeta.flag</key>
    	<false/>
    	<key>com.apple.security.get-task-allow</key>
    	<true/>
    	<key>b.str</key>
    	<string>a &amp; b</string>
    	<key>c.int</key>
    	<integer>300</integer>
    	<key>d.neg</key>
    	<integer>-2</integer>
    	<!-- a comment is skipped -->
    	<key>a.arr</key>
    	<array>
    		<string>x</string>
    		<string>yy</string>
    	</array>
    	<key>e.dict</key>
    	<dict>
    		<key>k2</key><true/>
    		<key>k1</key><string>v</string>
    	</dict>
    </dict>
    </plist>
    ''';

function HexOf(const S: string): string;
const
  Digits = '0123456789abcdef';
var
  I: Integer;
begin
  Result := '';
  for I := 0 to Length(S) - 1 do
    Result := Result + Copy(Digits, StrAt(S, I) shr 4, 1) +
      Copy(Digits, StrAt(S, I) and $F, 1);
end;

procedure TEntitlementsTests.TestDer_GetTaskAllow_MatchesCodesign;
begin
  AssertEquals('DER of get-task-allow',
    '702d020101b02830260c21636f6d2e6170706c652e73656375726974792e676574' +
    '2d7461736b2d616c6c6f770101ff',
    HexOf(EntitlementsDer(DebugEntitlementsPlist())));
end;

procedure TEntitlementsTests.TestDer_RichPlist_MatchesCodesign;
begin
  AssertEquals('DER of the rich plist',
    '708197020101b0819130100c05612e61727230070c01780c027979300e0c05622e' +
    '7374720c056120262062300b0c05632e696e740202012c30260c21636f6d2e6170' +
    '706c652e73656375726974792e6765742d7461736b2d616c6c6f770101ff300a0c' +
    '05642e6e65670201fe301c0c06652e64696374b01230070c026b310c017630070c' +
    '026b320101ff300e0c097a6574612e666c6167010100',
    HexOf(EntitlementsDer(RichPlist)));
end;

procedure TEntitlementsTests.TestDer_UnsupportedValue_Rejected;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    EntitlementsDer('<plist><dict><key>k</key><data>AA==</data></dict></plist>');
  except
    on E: EEntitlements do
      Raised := Pos('<data>', E.Message) >= 0;
  end;
  AssertTrue('<data> is reported', Raised);
end;

procedure TEntitlementsTests.TestDer_NotAPlist_Rejected;
var
  Raised: Boolean;
begin
  Raised := False;
  try
    EntitlementsDer('<dict></dict>');
  except
    on E: EEntitlements do
      Raised := True;
  end;
  AssertTrue('a document without <plist> is reported', Raised);
end;

procedure TEntitlementsTests.TestSignature_EntitlementsInSpecialSlots;
var
  W: TMachOExecWriter;
  Img, Xml: string;
  SigOff, CdOff, HashOff, NSpecial, BlobOff, BlobLen, Off, N, I: Integer;
  Slots: array[0..3] of Integer;
  Blobs: array[0..3] of string;

  function BeU32(AOff: Integer): Integer;
  begin
    Result := (StrAt(Img, AOff) shl 24) or (StrAt(Img, AOff + 1) shl 16)
      or (StrAt(Img, AOff + 2) shl 8) or StrAt(Img, AOff + 3);
  end;

  function LeU32(AOff: Integer): Integer;
  begin
    Result := StrAt(Img, AOff) or (StrAt(Img, AOff + 1) shl 8)
      or (StrAt(Img, AOff + 2) shl 16) or (StrAt(Img, AOff + 3) shl 24);
  end;

begin
  Xml := DebugEntitlementsPlist();
  W := TMachOExecWriter.Create();
  try
    W.SetText(Chr($C0) + Chr($03) + Chr($5F) + Chr($D6));   { ret }
    W.SetIdentifier('probe');
    W.SetEntryTextOffset(0);
    W.SetEntitlements(Xml);
    Img := W.Finish();
  finally
    W.Free();
  end;
  SigOff := 0;
  Off := 32;
  for N := 0 to LeU32(16) - 1 do
  begin
    if LeU32(Off) = $1D then    { LC_CODE_SIGNATURE }
    begin
      SigOff := LeU32(Off + 8);
      AssertEquals('signature size reaches the end of the file',
        Length(Img) - SigOff, LeU32(Off + 12));
    end;
    Off := Off + LeU32(Off + 4);
  end;
  AssertTrue('LC_CODE_SIGNATURE present', SigOff > 0);
  AssertEquals('SuperBlob magic', Integer($FADE0CC0), BeU32(SigOff));
  AssertEquals('SuperBlob length', Length(Img) - SigOff, BeU32(SigOff + 4));
  AssertEquals('four blobs', 4, BeU32(SigOff + 8));
  for I := 0 to 3 do
  begin
    Slots[I] := BeU32(SigOff + 12 + 8 * I);
    BlobOff := SigOff + BeU32(SigOff + 16 + 8 * I);
    BlobLen := BeU32(BlobOff + 4);
    Blobs[I] := Copy(Img, BlobOff, BlobLen);
  end;
  AssertEquals('slot 0: CodeDirectory', 0, Slots[0]);
  AssertEquals('slot 2: requirements', 2, Slots[1]);
  AssertEquals('slot 5: entitlements', 5, Slots[2]);
  AssertEquals('slot 7: DER entitlements', 7, Slots[3]);
  AssertEquals('empty requirement set',
    'fade0c010000000c00000000', HexOf(Blobs[1]));
  AssertEquals('the plist is carried verbatim', Xml, Copy(Blobs[2], 8,
    Length(Blobs[2]) - 8));
  AssertEquals('DER payload', HexOf(EntitlementsDer(Xml)),
    HexOf(Copy(Blobs[3], 8, Length(Blobs[3]) - 8)));
  CdOff := SigOff + BeU32(SigOff + 16);
  NSpecial := BeU32(CdOff + 24);
  HashOff := CdOff + BeU32(CdOff + 16);
  AssertEquals('seven special slots', 7, NSpecial);
  AssertEquals('slot -2 hashes the requirements', HexOf(Sha256(Blobs[1])),
    HexOf(Copy(Img, HashOff - 2 * 32, 32)));
  AssertEquals('slot -5 hashes the entitlements', HexOf(Sha256(Blobs[2])),
    HexOf(Copy(Img, HashOff - 5 * 32, 32)));
  AssertEquals('slot -7 hashes the DER entitlements', HexOf(Sha256(Blobs[3])),
    HexOf(Copy(Img, HashOff - 7 * 32, 32)));
  AssertEquals('unused slot -1 is zero', HexOf(Copy(Img, HashOff - 32, 0)) +
    '0000000000000000000000000000000000000000000000000000000000000000',
    HexOf(Copy(Img, HashOff - 32, 32)));
  AssertEquals('first page hash still covers the image',
    HexOf(Sha256(Copy(Img, 0, 4096))), HexOf(Copy(Img, HashOff, 32)));
end;

initialization
  RegisterTest(TEntitlementsTests);

end.
