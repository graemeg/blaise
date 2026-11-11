program m2calls;

{ Windows milestone M2 program under test: calls from Blaise code into
  kernel32 and msvcrt through the Win64 convention, and a frame far larger
  than a page.  TWin64FixtureTests compiles it for windows-x86_64 and links
  it with the stand-in runtime m2rt.s (the real one arrives in M3);
  scripts/windows-vm.sh crosscheck runs it in the guest and compares its
  output with m2calls.expected. }

function GetStdHandle(AStdHandle: UInt32): Pointer; external 'kernel32' name 'GetStdHandle';
function Win32WriteFile(AFile: Pointer; ABuffer: Pointer; ACount: UInt32;
  AWritten: Pointer; AOverlapped: Pointer): Int32; external 'kernel32' name 'WriteFile';
function MulDiv(ANumber, ANumerator, ADenominator: Int32): Int32; external 'kernel32' name 'MulDiv';
function sprintf(ABuffer: Pointer; AFormat: PChar): Int32; varargs; external 'msvcrt' name 'sprintf';

const
  FmtHello = 'hello from Blaise'#13#10;
  FmtInts = 'ints %d %d %d %d %d %d'#13#10;
  FmtFloat = 'float %.2f int %d float %.3f'#13#10;
  FmtMulDiv = 'muldiv %d'#13#10;
  FmtFrame = 'frame %d'#13#10;

var
  Buf: array[0..255] of Byte;
  Written: UInt32;

{ Write the first ACount bytes of Buf to standard output. }
procedure Put(ACount: Int32);
begin
  Win32WriteFile(GetStdHandle(UInt32(-11)), @Buf[0], UInt32(ACount), @Written, nil);
end;

{ 256 KiB of locals: without stack probes the first write below the guard
  page faults. }
procedure DeepFrame;
var
  Big: array[0..262143] of Byte;
begin
  Big[0] := 3;
  Big[262143] := Big[0];
  Put(sprintf(@Buf[0], PChar(FmtFrame), Int32(Big[262143])));
end;

begin
  Put(sprintf(@Buf[0], PChar(FmtHello)));
  { six variadic integers: four in registers, two on the stack }
  Put(sprintf(@Buf[0], PChar(FmtInts), 1, 2, 3, 4, 5, 6));
  { a variadic float in the third position goes in XMM2 and R8 }
  Put(sprintf(@Buf[0], PChar(FmtFloat), 2.5, 7, 0.125));
  Put(sprintf(@Buf[0], PChar(FmtMulDiv), MulDiv(300, 7, 2)));
  DeepFrame();
end.
