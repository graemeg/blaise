program m3callback;

{ Windows milestone M3 program under test: cdecl routines with bodies, which
  foreign code enters through a Win64 entry.  msvcrt's qsort calls a Blaise
  comparator, and Blaise calls a cdecl routine with eight mixed arguments
  -- floats, integers, an 8-byte record, a 12-byte record, two on the stack
  -- through the same entry.  Linked with the stand-in runtime m2rt.s by
  TWin64FixtureTests; checked by scripts/windows-vm.sh crosscheck against
  m3callback.expected. }

function GetStdHandle(AStdHandle: UInt32): Pointer; external 'kernel32' name 'GetStdHandle';
function Win32WriteFile(AFile: Pointer; ABuffer: Pointer; ACount: UInt32;
  AWritten: Pointer; AOverlapped: Pointer): Int32; external 'kernel32' name 'WriteFile';
function sprintf(ABuffer: Pointer; AFormat: PChar): Int32; varargs; external 'msvcrt' name 'sprintf';
procedure qsort(ABase: Pointer; ACount, AWidth: UInt64; ACompare: Pointer); external 'msvcrt' name 'qsort';

type
  TPair = record
    A, B: Int32;
  end;
  TTriple = record
    X, Y, Z: Int32;
  end;

const
  FmtSorted = 'sorted %d %d %d %d %d'#13#10;
  FmtMixed = 'mixed %.2f %d %.2f %d %d %d %d %.3f'#13#10;
  FmtCalls = 'compares %d'#13#10;

var
  Buf: array[0..255] of Byte;
  Written: UInt32;
  Data: array[0..4] of Int32;
  Compares: Int32;

procedure Put(ACount: Int32);
begin
  Win32WriteFile(GetStdHandle(UInt32(-11)), @Buf[0], UInt32(ACount), @Written, nil);
end;

{ qsort's comparator: entered by msvcrt the Win64 way. }
function CompareInt(A, B: Pointer): Int32; cdecl;
begin
  Inc(Compares);
  Result := PInt32(A)^ - PInt32(B)^;
end;

{ Eight arguments: two in XMM registers, two in integer registers, the
  8-byte record by value and the 12-byte one by reference, and the last two
  on the stack. }
function Mixed(F1: Float64; I1: Int64; F2: Float32; P: TPair; T: TTriple;
  I2: Int32; I3: Int64; F3: Float64): Int64; cdecl;
begin
  Put(sprintf(@Buf[0], PChar(FmtMixed), F1, I1, Float64(F2), P.A, P.B, T.Z,
    I2 + I3, F3));
  Result := I1 + I2 + I3;
end;

var
  P: TPair;
  T: TTriple;
  R: Int64;

begin
  Data[0] := 42; Data[1] := 7; Data[2] := 19; Data[3] := -3; Data[4] := 7;
  qsort(@Data[0], 5, 4, Pointer(@CompareInt));
  Put(sprintf(@Buf[0], PChar(FmtSorted), Data[0], Data[1], Data[2], Data[3], Data[4]));
  if Compares > 0 then
    Put(sprintf(@Buf[0], PChar(FmtCalls), 1));
  P.A := 11; P.B := 22;
  T.X := 1; T.Y := 2; T.Z := 33;
  R := Mixed(1.5, 100, 2.25, P, T, 5, 6, 0.125);
  Put(sprintf(@Buf[0], PChar(FmtCalls), R));
end.
