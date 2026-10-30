{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.ordinalmatrix;

{ The ordinal TYPES x CONSTRUCTS matrix, at the boundaries.

  Every ordinal type kind -- each integer width, signed and unsigned, an
  enum and Boolean -- is driven through every construct that consumes an
  ordinal: for to/downto (full range or the last steps before a limit),
  Inc/Dec (including the wrap at a limit), Succ/Pred, comparisons, case
  labels, array index, set membership, div/mod, var and value parameters,
  and printing.  The same checks run in four storage modes: a global, a
  local, a local captured by a nested routine, and one captured by a
  closure, since each reaches the variable a different way.

  Values are the type's LIMITS -- Low(T), High(T), and the sign boundary
  -- because that is where width and signedness bugs live: GH #237 (a for
  loop ending at High(Int8) never ended on x86-64) survived every test that
  used an Integer counter over 1..3.  Each generated program is
  self-checking and prints 'BAD <mode> <construct>' for a failed check, so
  a failure names the construct, the mode and (through the test name) the
  type.  Extend the matrix when a type kind or an ordinal construct is
  added. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EOrdinalMatrixTests = class(TE2ETestCase)
  private
    procedure RunMatrix(const AType, ALow, AHigh: string; const AKind: string;
      ASmall: Boolean; const ADivHigh, AModHigh, ADivLow, AModLow: string);
  protected
    procedure SetUp; override;
  published
    procedure TestRun_Matrix_Int8;
    procedure TestRun_Matrix_Byte;
    procedure TestRun_Matrix_Int16;
    procedure TestRun_Matrix_Word;
    procedure TestRun_Matrix_Int32;
    procedure TestRun_Matrix_UInt32;
    procedure TestRun_Matrix_Int64;
    procedure TestRun_Matrix_UInt64;
    procedure TestRun_Matrix_Enum;
    procedure TestRun_Matrix_Boolean;
  end;

implementation

const
  LF = #10;
  LE = #10;

procedure TE2EOrdinalMatrixTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-ordinalmatrix');
end;

{ The checks, applied to the variable AV (V, or GV in the global mode).
  AKind: 's' signed integer, 'u' unsigned integer, 'e' enum, 'b' Boolean.
  ASmall: the whole range is iterated and an array[T] is declared (8- and
  16-bit kinds, enum, Boolean); otherwise the loops run the last steps
  before each limit. }
function CheckBody(const AV: string; const AKind: string; ASmall: Boolean;
  const ACount, ADivHigh, AModHigh, ADivLow, AModLow: string): string;
var
  IsInt: Boolean;
  S: string;

  procedure Add(const ALine: string);
  begin
    S := S + '    ' + ALine + LF;
  end;

begin
  S := '';
  IsInt := (AKind = 's') or (AKind = 'u');
  if ASmall then
  begin
    Add('C := 0; for ' + AV + ' := Low(T) to High(T) do begin C := C + 1; ' +
      'if C > 70000 then Break; end; Chk(C = ' + ACount + ', ''for-up'');');
    Add('C := 0; for ' + AV + ' := High(T) downto Low(T) do begin C := C + 1; ' +
      'if C > 70000 then Break; end; Chk(C = ' + ACount + ', ''for-down'');');
  end
  else
  begin
    Add('C := 0; for ' + AV + ' := High(T) - 2 to High(T) do begin C := C + 1; ' +
      'if C > 70000 then Break; end; Chk(C = 3, ''for-up'');');
    Add('C := 0; for ' + AV + ' := Low(T) + 2 downto Low(T) do begin C := C + 1; ' +
      'if C > 70000 then Break; end; Chk(C = 3, ''for-down'');');
  end;
  { a completed loop steps once past its end, and the counter stays a value
    of its type: High(T) + 1 wraps, as Inc does (arm64 left a Byte local
    holding 256 in its 8-byte slot) }
  if IsInt then
    Add('for ' + AV + ' := High(T) - 1 to High(T) do C := C + 1; Chk(' + AV +
      ' = Low(T), ''for-up-wraps'');');
  Add('C := 0; for ' + AV + ' := High(T) to Low(T) do C := C + 1; for ' + AV +
    ' := Low(T) downto High(T) do C := C + 1; Chk(C = 0, ''for-empty'');');
  Add(AV + ' := Pred(High(T)); Inc(' + AV + '); Chk(' + AV +
    ' = High(T), ''inc-to-high'');');
  Add('Dec(' + AV + '); Chk(' + AV + ' = Pred(High(T)), ''dec-from-high'');');
  Add(AV + ' := Low(T); Inc(' + AV + '); Dec(' + AV + '); Chk(' + AV +
    ' = Low(T), ''inc-dec-low'');');
  Add(AV + ' := Low(T); W := Succ(' + AV +
    '); Chk(Ord(W) = Ord(Low(T)) + 1, ''succ'');');
  Add(AV + ' := High(T); W := Pred(' + AV +
    '); Chk(Ord(W) = Ord(High(T)) - 1, ''pred'');');
  if IsInt then
  begin
    Add(AV + ' := High(T); Inc(' + AV + '); Chk(' + AV +
      ' = Low(T), ''inc-wraps'');');
    Add('Dec(' + AV + '); Chk(' + AV + ' = High(T), ''dec-wraps'');');
  end;
  Add(AV + ' := High(T); W := Low(T); Chk(' + AV + ' > W, ''gt''); Chk(W < ' +
    AV + ', ''lt''); Chk(not (' + AV + ' < W), ''not-lt''); Chk(' + AV +
    ' >= ' + AV + ', ''ge''); Chk(W <= ' + AV + ', ''le''); Chk(' + AV +
    ' <> W, ''ne'');');
  Add(AV + ' := High(T); case ' + AV + ' of Low(T): Chk(False, ' +
    '''case-high-as-low''); High(T): C := 1; else Chk(False, ' +
    '''case-high-else''); end;');
  Add(AV + ' := Low(T); case ' + AV + ' of High(T): Chk(False, ' +
    '''case-low-as-high''); Low(T): C := 1; else Chk(False, ' +
    '''case-low-else''); end;');
  if ASmall then
    Add('GA[High(T)] := 5; GA[Low(T)] := 7; ' + AV + ' := High(T); ' +
      'Chk(GA[' + AV + '] = 5, ''arr-high''); ' + AV + ' := Low(T); ' +
      'Chk(GA[' + AV + '] = 7, ''arr-low'');');
  if (AKind = 'e') or (AKind = 'b') or (ACount = '256') and (AKind = 'u') then
    Add('GS := [Low(T), High(T)]; ' + AV + ' := High(T); Chk(' + AV +
      ' in GS, ''set-high''); ' + AV + ' := Low(T); Chk(' + AV +
      ' in GS, ''set-low'');');
  { Succ(Low) is not a member -- except for Boolean, where it is High }
  if (AKind = 'e') or (ACount = '256') and (AKind = 'u') then
    Add(AV + ' := Succ(Low(T)); Chk(not (' + AV + ' in GS), ''set-not'');');
  if IsInt then
  begin
    Add(AV + ' := High(T); Chk(' + AV + ' div 2 = T(' + ADivHigh +
      '), ''div-high''); Chk(' + AV + ' mod 10 = T(' + AModHigh +
      '), ''mod-high'');');
    if AKind = 's' then
      Add(AV + ' := Low(T); Chk(' + AV + ' div 2 = T(' + ADivLow +
        '), ''div-low''); Chk(' + AV + ' mod 10 = T(' + AModLow +
        '), ''mod-low'');');
  end;
  Add(AV + ' := Pred(High(T)); BumpVar(' + AV + '); Chk(' + AV +
    ' = High(T), ''var-param'');');
  Add(AV + ' := High(T); Chk(Same(' + AV + ', High(T)), ''value-param'');');
  Result := S;
end;

function MatrixProgram(const AType: string; const AKind: string; ASmall: Boolean;
  const ACount, ADivHigh, AModHigh, ADivLow, AModLow: string): string;
var
  Body, GBody, Shown: string;
  HasSet: Boolean;
begin
  Body := CheckBody('V', AKind, ASmall, ACount, ADivHigh, AModHigh,
    ADivLow, AModLow);
  GBody := CheckBody('GV', AKind, ASmall, ACount, ADivHigh, AModHigh,
    ADivLow, AModLow);
  HasSet := (AKind = 'e') or (AKind = 'b') or
            ((ACount = '256') and (AKind = 'u'));
  if (AKind = 's') or (AKind = 'u') then
    Shown := 'V'
  else
    Shown := 'Ord(V)';
  Result :=
    'program P;' + LF +
    'type TE = (eA, eB, eC, eD);' + LF +
    'type T = ' + AType + ';' + LF +
    'var' + LF +
    '  GV: T;' + LF +
    '  Mode: string;' + LF +
    '  Bad: Int;' + LF;
  if HasSet then
    Result := Result + '  GS: set of T;' + LF;
  if ASmall then
    Result := Result + '  GA: array[T] of Int;' + LF;
  Result := Result + LF +
    'procedure Chk(AOk: Boolean; const AWhat: string);' + LF +
    'begin' + LF +
    '  if not AOk then' + LF +
    '  begin' + LF +
    '    WriteLn(''BAD '', Mode, '' '', AWhat);' + LF +
    '    Bad := Bad + 1;' + LF +
    '  end;' + LF +
    'end;' + LF + LF +
    'procedure BumpVar(var X: T);' + LF +
    'begin' + LF +
    '  Inc(X);' + LF +
    'end;' + LF + LF +
    'function Same(X, Y: T): Boolean;' + LF +
    'begin' + LF +
    '  Result := X = Y;' + LF +
    'end;' + LF + LF +
    'procedure ShowLimits;' + LF +
    'var' + LF +
    '  V: T;' + LF +
    'begin' + LF +
    '  V := Low(T);' + LF +
    '  Write(Mode, '' lo '', ' + Shown + ');' + LF +
    '  V := High(T);' + LF +
    '  WriteLn('' hi '', ' + Shown + ');' + LF +
    'end;' + LF + LF +
    'procedure RunGlobal;' + LF +
    'var' + LF +
    '  W: T;' + LF +
    '  C: Int;' + LF +
    'begin' + LF +
    '  Mode := ''global'';' + LF +
    '  ShowLimits();' + LF +
    GBody +
    'end;' + LF + LF +
    'procedure RunLocal;' + LF +
    'var' + LF +
    '  V, W: T;' + LF +
    '  C: Int;' + LF +
    'begin' + LF +
    '  Mode := ''local'';' + LF +
    '  ShowLimits();' + LF +
    Body +
    'end;' + LF + LF +
    'procedure RunNested;' + LF +
    'var' + LF +
    '  V, W: T;' + LF +
    '  C: Int;' + LF +
    '  procedure Inner;' + LF +
    '  begin' + LF +
    Body +
    '  end;' + LF +
    'begin' + LF +
    '  Mode := ''nested'';' + LF +
    '  ShowLimits();' + LF +
    '  Inner();' + LF +
    'end;' + LF + LF +
    'procedure RunClosure;' + LF +
    'var' + LF +
    '  V, W: T;' + LF +
    '  C: Int;' + LF +
    '  F: reference to procedure;' + LF +
    'begin' + LF +
    '  Mode := ''closure'';' + LF +
    '  ShowLimits();' + LF +
    '  F := procedure' + LF +
    '    begin' + LF +
    Body +
    '    end;' + LF +
    '  F();' + LF +
    'end;' + LF + LF +
    'begin' + LF +
    '  RunGlobal();' + LF +
    '  RunLocal();' + LF +
    '  RunNested();' + LF +
    '  RunClosure();' + LF +
    '  WriteLn(''bad '', Bad);' + LF +
    'end.' + LF;
end;

procedure TE2EOrdinalMatrixTests.RunMatrix(const AType, ALow, AHigh: string;
  const AKind: string; ASmall: Boolean; const ADivHigh, AModHigh, ADivLow,
  AModLow: string);
var
  Count, Limits: string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { the full-range trip count, for the kinds iterated end to end }
  if AKind = 'b' then
    Count := '2'
  else if AKind = 'e' then
    Count := '4'
  else if (AType = 'Int8') or (AType = 'Byte') then
    Count := '256'
  else
    Count := '65536';
  Limits := ' lo ' + ALow + ' hi ' + AHigh + LE;
  AssertRunsOnAll(
    MatrixProgram(AType, AKind, ASmall, Count, ADivHigh, AModHigh, ADivLow,
      AModLow),
    'global' + Limits + 'local' + Limits + 'nested' + Limits +
    'closure' + Limits + 'bad 0' + LE, 0);
end;

procedure TE2EOrdinalMatrixTests.TestRun_Matrix_Int8;
begin
  RunMatrix('Int8', '-128', '127', 's', True, '63', '7', '-64', '-8');
end;

procedure TE2EOrdinalMatrixTests.TestRun_Matrix_Byte;
begin
  RunMatrix('Byte', '0', '255', 'u', True, '127', '5', '0', '0');
end;

procedure TE2EOrdinalMatrixTests.TestRun_Matrix_Int16;
begin
  RunMatrix('Int16', '-32768', '32767', 's', True, '16383', '7', '-16384',
    '-8');
end;

procedure TE2EOrdinalMatrixTests.TestRun_Matrix_Word;
begin
  RunMatrix('Word', '0', '65535', 'u', True, '32767', '5', '0', '0');
end;

procedure TE2EOrdinalMatrixTests.TestRun_Matrix_Int32;
begin
  RunMatrix('Int32', '-2147483648', '2147483647', 's', False, '1073741823',
    '7', '-1073741824', '-8');
end;

procedure TE2EOrdinalMatrixTests.TestRun_Matrix_UInt32;
begin
  RunMatrix('UInt32', '0', '4294967295', 'u', False, '2147483647', '5', '0',
    '0');
end;

procedure TE2EOrdinalMatrixTests.TestRun_Matrix_Int64;
begin
  RunMatrix('Int64', '-9223372036854775808', '9223372036854775807', 's',
    False, '4611686018427387903', '7', '-4611686018427387904', '-8');
end;

procedure TE2EOrdinalMatrixTests.TestRun_Matrix_UInt64;
begin
  RunMatrix('UInt64', '0', '18446744073709551615', 'u', False,
    '9223372036854775807', '5', '0', '0');
end;

procedure TE2EOrdinalMatrixTests.TestRun_Matrix_Enum;
begin
  RunMatrix('TE', '0', '3', 'e', True, '', '', '', '');
end;

procedure TE2EOrdinalMatrixTests.TestRun_Matrix_Boolean;
begin
  RunMatrix('Boolean', '0', '1', 'b', True, '', '', '', '');
end;

initialization
  RegisterTest(TE2EOrdinalMatrixTests);

end.
