program m3tls;

{ Windows milestone M3 program under test: threadvars through the PE TLS
  directory -- an initialised one (.tdata), zero-filled ones (.tbss), a value
  carried across calls, and its address passed as a var parameter.  Linked
  with the stand-in runtime m2rt.s by TWin64FixtureTests; checked by
  scripts/windows-vm.sh crosscheck against m3tls.expected. }

function GetStdHandle(AStdHandle: UInt32): Pointer; external 'kernel32' name 'GetStdHandle';
function Win32WriteFile(AFile: Pointer; ABuffer: Pointer; ACount: UInt32;
  AWritten: Pointer; AOverlapped: Pointer): Int32; external 'kernel32' name 'WriteFile';
function sprintf(ABuffer: Pointer; AFormat: PChar): Int32; varargs; external 'msvcrt' name 'sprintf';

const
  FmtLine = '%s %d'#13#10;

threadvar
  Seeded: Int64 = 40;
  Counter: Int64;
  Big: array[0..999] of Int64;

var
  Buf: array[0..255] of Byte;
  Written: UInt32;

procedure Put(const ALabel: PChar; AValue: Int64);
var
  N: Int32;
begin
  N := sprintf(@Buf[0], PChar(FmtLine), ALabel, AValue);
  Win32WriteFile(GetStdHandle(UInt32(-11)), @Buf[0], UInt32(N), @Written, nil);
end;

procedure Bump(var V: Int64);
begin
  V := V + 1;
end;

procedure Fill;
var
  I: Int;
begin
  for I := 0 to 999 do
    Big[I] := I;
end;

begin
  Put(PChar('seeded'), Seeded);
  Counter := Seeded + 2;
  Bump(Counter);
  Put(PChar('counter'), Counter);
  Fill();
  Put(PChar('big'), Big[0] + Big[999]);
  Put(PChar('still'), Seeded + Counter);
end.
