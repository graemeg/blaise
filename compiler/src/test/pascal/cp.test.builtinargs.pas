{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.builtinargs;

{ Argument types of the compiler's built-in routines.  A built-in arm
  analysed its arguments but never compared them with the parameter type,
  so Pos('a', N) compiled and segfaulted and FileExists(5) printed False
  (BUG-20261106-builtin-arg-types-unchecked).  An ordinary routine with a
  string parameter rejects the same call; a built-in must too. }

interface

uses
  Classes, SysUtils, blaise.testing, cp.test.harness;

type
  TBuiltinArgTypeTests = class(TTestCase)
  private
    procedure AssertRejected(const ACall, AWant: string);
    procedure AssertAccepted(const ACall: string);
  published
    procedure TestPos_IntegerArgument_Rejected;
    procedure TestPosEx_IntegerArgument_Rejected;
    procedure TestFileBuiltins_IntegerArgument_Rejected;
    procedure TestStringBuiltins_NonStringArgument_Rejected;
    procedure TestPathBuiltins_NonStringArgument_Rejected;
    procedure TestPChar_ToStringBuiltin_Rejected;
    procedure TestIntegerBuiltins_StringArgument_Rejected;
    procedure TestFloatBuiltin_StringArgument_Rejected;
    procedure TestOrdinalNonNumber_ToIntegerBuiltin_Rejected;
    procedure TestOtherStringBuiltins_NonStringArgument_Rejected;
    procedure TestFileProcedures_NonStringArgument_Rejected;
    procedure TestValidArguments_Accepted;
  end;

implementation

function ProgramFor(const AExpr: string): string;
begin
  Result :=
    'program P;' + #10 +
    'type TE = (eA, eB);' + #10 +
    'var N: Int; S: string; B: Boolean; C: PChar; D: Float64; E: TE;' + #10 +
    '    W: UInt16; U: UInt64; I8: Int8;' + #10 +
    'begin' + #10 +
    '  S := ''x''; C := PChar(S); N := 0; D := 0.0; E := eA;' + #10 +
    '  WriteLn(' + AExpr + ')' + #10 +
    'end.' + #10;
end;

procedure TBuiltinArgTypeTests.AssertRejected(const ACall, AWant: string);
var
  Msg: string;
begin
  Msg := SemanticError(ProgramFor(ACall));
  AssertTrue(ACall + ' rejected naming ' + AWant + ', got: ' + Msg,
    Pos(AWant, Msg) >= 0);
end;

procedure TBuiltinArgTypeTests.AssertAccepted(const ACall: string);
begin
  AssertEquals(ACall + ' accepted', '', SemanticError(ProgramFor(ACall)));
end;

procedure TBuiltinArgTypeTests.TestPos_IntegerArgument_Rejected;
begin
  AssertRejected('Pos(''a'', N)', 'argument of ''Pos'' must be a string');
  AssertRejected('Pos(N, ''abc'')', 'argument of ''Pos'' must be a string');
  { a string subscript is a byte, not a one-character string }
  AssertRejected('Pos(S[0], ''abc'')', 'argument of ''Pos'' must be a string');
end;

procedure TBuiltinArgTypeTests.TestPosEx_IntegerArgument_Rejected;
begin
  AssertRejected('PosEx(''a'', N, 0)', 'argument of ''PosEx'' must be a string');
end;

procedure TBuiltinArgTypeTests.TestFileBuiltins_IntegerArgument_Rejected;
begin
  AssertRejected('FileExists(5)', 'argument of ''FileExists'' must be a string');
  AssertRejected('DirectoryExists(N)', 'argument of ''DirectoryExists'' must be a string');
  AssertRejected('FileAge(N)', 'argument of ''FileAge'' must be a string');
  AssertRejected('ForceDirectories(B)', 'argument of ''ForceDirectories'' must be a string');
  AssertRejected('ReadFile(N)', 'argument of ''ReadFile'' must be a string');
  AssertRejected('ListDir(N)', 'argument of ''ListDir'' must be a string');
  AssertRejected('RenameFile(S, N)', 'argument of ''RenameFile'' must be a string');
  AssertRejected('SetCurrentDir(N)', 'argument of ''SetCurrentDir'' must be a string');
end;

procedure TBuiltinArgTypeTests.TestStringBuiltins_NonStringArgument_Rejected;
begin
  AssertRejected('UpperCase(N)', 'argument of ''UpperCase'' must be a string');
  AssertRejected('LowerCase(N)', 'argument of ''LowerCase'' must be a string');
  AssertRejected('Trim(B)', 'argument of ''Trim'' must be a string');
  AssertRejected('SameText(N, ''a'')', 'argument of ''SameText'' must be a string');
  AssertRejected('CompareStr(''a'', N)', 'argument of ''CompareStr'' must be a string');
  AssertRejected('CompareText(N, ''a'')', 'argument of ''CompareText'' must be a string');
  AssertRejected('StrToInt(N)', 'argument of ''StrToInt'' must be a string');
  AssertRejected('StrToInt64(N)', 'argument of ''StrToInt64'' must be a string');
  AssertRejected('StrToDouble(N)', 'argument of ''StrToDouble'' must be a string');
  AssertRejected('GetEnvVar(N)', 'argument of ''GetEnvVar'' must be a string');
  AssertRejected('Exec(N)', 'argument of ''Exec'' must be a string');
  AssertRejected('Copy(N, 0, 1)', 'argument of ''Copy'' must be a string');
end;

procedure TBuiltinArgTypeTests.TestPathBuiltins_NonStringArgument_Rejected;
begin
  AssertRejected('ExtractFileName(N)', 'argument of ''ExtractFileName'' must be a string');
  AssertRejected('ExtractFileExt(D)', 'argument of ''ExtractFileExt'' must be a string');
  AssertRejected('ChangeFileExt(S, N)', 'argument of ''ChangeFileExt'' must be a string');
  AssertRejected('IncludeTrailingPathDelimiter(N)',
    'argument of ''IncludeTrailingPathDelimiter'' must be a string');
  AssertRejected('GetTempFileName(S, N)', 'argument of ''GetTempFileName'' must be a string');
end;

procedure TBuiltinArgTypeTests.TestPChar_ToStringBuiltin_Rejected;
begin
  { a PChar has no string header for the built-in to read its length from }
  AssertRejected('Pos(''x'', C)', 'string(');
  AssertRejected('UpperCase(C)', 'string(');
end;

procedure TBuiltinArgTypeTests.TestIntegerBuiltins_StringArgument_Rejected;
begin
  AssertRejected('IntToStr(''a'')', 'argument of ''IntToStr'' must be an integer');
  AssertRejected('Int64ToStr(S)', 'argument of ''Int64ToStr'' must be an integer');
  AssertRejected('UInt64ToStr(B)', 'argument of ''UInt64ToStr'' must be an integer');
  AssertRejected('Chr(S)', 'argument of ''Chr'' must be an integer');
end;

procedure TBuiltinArgTypeTests.TestFloatBuiltin_StringArgument_Rejected;
begin
  AssertRejected('DoubleToStr(S)', 'argument of ''DoubleToStr'' must be a number');
end;

procedure TBuiltinArgTypeTests.TestOrdinalNonNumber_ToIntegerBuiltin_Rejected;
begin
  { an enum or Boolean is an ordinal, not a number: write Ord(E) }
  AssertRejected('IntToStr(E)', 'argument of ''IntToStr'' must be an integer');
  AssertRejected('IntToStr(B)', 'argument of ''IntToStr'' must be an integer');
  AssertRejected('DoubleToStr(E)', 'argument of ''DoubleToStr'' must be a number');
end;

procedure TBuiltinArgTypeTests.TestOtherStringBuiltins_NonStringArgument_Rejected;
begin
  AssertRejected('OrdAt(N, 0)', 'argument of ''OrdAt'' must be a string');
  AssertRejected('OrdAt(S, S)', 'argument of ''OrdAt'' must be an integer');
  AssertRejected('UpCase(B)', 'argument of ''UpCase'' must be a string or a character code');
  AssertRejected('Format(N, [1])', 'argument of ''Format'' must be a string');
end;

{ The procedure built-ins, as statements rather than WriteLn arguments. }
procedure TBuiltinArgTypeTests.TestFileProcedures_NonStringArgument_Rejected;
var
  Msg: string;
  I: Int;
  Calls: array[0..5] of string;
  Wants: array[0..5] of string;
begin
  Calls[0] := 'WriteFile(5, ''x'')';
  Wants[0] := 'argument of ''WriteFile'' must be a string';
  Calls[1] := 'WriteFile(''f'', 5)';
  Wants[1] := 'argument of ''WriteFile'' must be a string';
  Calls[2] := 'AppendFile(''f'', 5)';
  Wants[2] := 'argument of ''AppendFile'' must be a string';
  Calls[3] := 'DeleteFile(5)';
  Wants[3] := 'argument of ''DeleteFile'' must be a string';
  Calls[4] := 'RemoveDir(5)';
  Wants[4] := 'argument of ''RemoveDir'' must be a string';
  Calls[5] := 'ProcessAddArg(ProcessCreate(), 5)';
  Wants[5] := 'argument of ''ProcessAddArg'' must be a string';
  for I := 0 to 5 do
  begin
    Msg := SemanticError('program P;' + #10 + 'begin' + #10 + '  ' +
      Calls[I] + #10 + 'end.' + #10);
    AssertTrue(Calls[I] + ' rejected, got: ' + Msg, Pos(Wants[I], Msg) >= 0);
  end;
  AssertEquals('string arguments accepted', '', SemanticError(
    'program P;' + #10 + 'begin' + #10 +
    '  WriteFile(''f'', ''x''); AppendFile(''f'', ''y''); DeleteFile(''f'')' +
    #10 + 'end.' + #10));
end;

procedure TBuiltinArgTypeTests.TestValidArguments_Accepted;
begin
  AssertAccepted('Pos(''x'', S)');
  AssertAccepted('Pos(Chr(120), S + ''y'')');
  AssertAccepted('PosEx(S, ''abc'', N)');
  AssertAccepted('FileExists(S)');
  AssertAccepted('UpperCase(string(C))');
  AssertAccepted('Copy(S, 0, 1)');
  AssertAccepted('IntToStr(W) + IntToStr(I8) + IntToStr(Ord(E))');
  AssertAccepted('UInt64ToStr(U)');
  AssertAccepted('Int64ToStr(N)');
  AssertAccepted('DoubleToStr(D) + DoubleToStr(N)');
  AssertAccepted('Chr(65)');
  AssertAccepted('StrToInt(''1'') + StrToInt64(S)');
  AssertAccepted('OrdAt(S, 0) + Length(UpCase(S)) + Length(Format(''%d'', [N]))');
  AssertAccepted('UpCase(97) + UpCase(N) + UpCase(Chr(98))');
end;

initialization
  RegisterTest(TBuiltinArgTypeTests);

end.
