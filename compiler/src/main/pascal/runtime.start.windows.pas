{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit runtime.start.windows;
// The PE entry point (docs/windows-x86_64-backend-design.adoc,
// "runtime.start.windows").
//
// The loader calls _start the Win64 way with no arguments, so it is declared
// cdecl and gets a foreign entry.  It:
//
//   1. turns off the Windows Error Reporting dialog for this process, so a
//      crash ends the process instead of waiting for a click;
//   2. checks that the executable's TLS index is 0 -- the PE TLS model reaches
//      threadvars through slot 0 of the thread's TLS array;
//   3. sets the console code pages to UTF-8;
//   4. installs the fault handler (design decision D7): a fault in the
//      program's own code is reported on standard error and ends the process
//      with the exception code -- 0xC0000005 for an access violation -- the
//      Windows counterpart of exit code 139 for SIGSEGV;
//   5. splits the command line by the Windows quoting rules into UTF-8
//      argc/argv;
//   6. calls main(argc, argv) and exits through the at-exit list.

interface

procedure _start; cdecl;

implementation

function main(Argc: Int32; Argv: Pointer): Int32; external name 'main';
procedure _RunAtExitAndExit(Code: Int32); external name '_RunAtExitAndExit';
function _sys_write(Fd: Int32; Buf: Pointer; Count: Int64): Int64;
  external name 'write';
function _BlaiseGetMem(Size: Int64): Pointer; external name '_BlaiseGetMem';

function GetCommandLineW: Pointer; external 'kernel32' name 'GetCommandLineW';
function WideCharToMultiByte(ACodePage, AFlags: UInt32; AWide: Pointer;
  AWideCount: Int32; AMulti: Pointer; AMultiSize: Int32; ADefault: Pointer;
  AUsedDefault: Pointer): Int32; external 'kernel32' name 'WideCharToMultiByte';
function SetConsoleOutputCP(ACodePage: UInt32): Int32;
  external 'kernel32' name 'SetConsoleOutputCP';
function SetConsoleCP(ACodePage: UInt32): Int32;
  external 'kernel32' name 'SetConsoleCP';
function SetErrorMode(AMode: UInt32): UInt32;
  external 'kernel32' name 'SetErrorMode';
function SetThreadStackGuarantee(ASize: Pointer): Int32;
  external 'kernel32' name 'SetThreadStackGuarantee';
function AddVectoredExceptionHandler(AFirst: UInt32; AHandler: Pointer): Pointer;
  external 'kernel32' name 'AddVectoredExceptionHandler';
function GetCurrentProcess: Pointer; external 'kernel32' name 'GetCurrentProcess';
function TerminateProcess(AProcess: Pointer; ACode: UInt32): Int32;
  external 'kernel32' name 'TerminateProcess';

const
  CP_UTF8 = 65001;
  SEM_FAILCRITICALERRORS = $0001;
  SEM_NOGPFAULTERRORBOX = $0002;
  SEM_NOOPENFILEERRORBOX = $8000;
  EXCEPTION_CONTINUE_SEARCH = 0;
  { Stack kept back for the fault handler when the stack overflows. }
  HANDLER_STACK = 32768;

type
  PUInt32 = ^UInt32;
  PUInt64 = ^UInt64;
  PPointer = ^Pointer;

{ The executable's TLS index, which the loader writes into _tls_index. }
function TlsIndex: UInt32; assembler; nostackframe;
asm
    movl _tls_index(%rip), %eax
    ret
end;

{ The address the image was loaded at. }
function ImageBase: Pointer; assembler; nostackframe;
asm
    leaq __ImageBase(%rip), %rax
    ret
end;

{ The image's extent, from OptionalHeader.SizeOfImage. }
function ImageSize: UInt64;
var
  Base: Pointer;
  PeOff: UInt32;
begin
  Base := ImageBase();
  PeOff := PUInt32(Base + $3C)^;
  Result := PUInt32(Base + PeOff + 24 + 56)^;
end;

procedure PutStr(const S: string);
begin
  _sys_write(2, PChar(S), Length(S));
end;

{ AValue as eight hexadecimal digits. }
function Hex8(AValue: UInt32): string;
var
  I, D: Int;
begin
  Result := '';
  for I := 7 downto 0 do
  begin
    D := Int((AValue shr (I * 4)) and $F);
    if D < 10 then
      Result := Result + Chr(48 + D)
    else
      Result := Result + Chr(55 + D);
  end;
end;

function FaultName(ACode: UInt32): string;
begin
  case ACode of
    $C0000005: Result := 'access violation';
    $C00000FD: Result := 'stack overflow';
    $C0000094: Result := 'integer division by zero';
    $C0000095: Result := 'integer overflow';
    $C000001D: Result := 'illegal instruction';
    $C0000096: Result := 'privileged instruction';
    $C000008C: Result := 'array bounds exceeded';
  else
    Result := '';
  end;
end;

{ The fault handler.  Windows calls it with an EXCEPTION_POINTERS, whose
  first field points at the EXCEPTION_RECORD: ExceptionCode at offset 0,
  ExceptionAddress at offset 16.  It runs before any frame-based handler, so
  it answers only for faults raised in this image's own code: a DLL may
  handle its own faults with SEH. }
function FaultHandler(AInfo: Pointer): Int32; cdecl;
var
  Rec: Pointer;
  Code: UInt32;
  Addr, Base: UInt64;
  Name: string;
begin
  Result := EXCEPTION_CONTINUE_SEARCH;
  Rec := PPointer(AInfo)^;
  Code := PUInt32(Rec)^;
  Name := FaultName(Code);
  if Name = '' then Exit;
  Addr := PUInt64(Rec + 16)^;
  Base := UInt64(ImageBase());
  if (Addr < Base) or (Addr >= Base + ImageSize()) then Exit;
  PutStr('Runtime error: ' + Name + ' (0x' + Hex8(Code) + ')'#13#10);
  TerminateProcess(GetCurrentProcess(), Code);
end;

{ Split ALine, UTF-8, by the rules of CommandLineToArgvW into a nil-ended
  vector of NUL-terminated strings.  The first argument ends at the first
  space or tab, or at the closing quote when it starts with one.  In the rest,
  2n backslashes before a quote are n backslashes and the quote opens or
  closes a quoted run; 2n+1 are n and a literal quote; backslashes before
  anything else are literal; inside a quoted run "" is a literal quote. }
procedure SplitCommandLine(ALine: PChar; out AArgc: Int32; out AArgv: Pointer);
var
  Len, P, N, K, Count: Int;
  Args: array of string;
  Cur: string;
  InQuote: Boolean;
  Vec: PPointer;
  Buf: PChar;
  I, J: Int;
begin
  Len := 0;
  while ALine[Len] <> #0 do
    Len := Len + 1;
  SetLength(Args, 0);
  P := 0;
  { the program name }
  Cur := '';
  if (Len > 0) and (ALine[0] = '"') then
  begin
    P := 1;
    while (P < Len) and (ALine[P] <> '"') do
    begin
      Cur := Cur + Chr(Ord(ALine[P]));
      P := P + 1;
    end;
    if P < Len then P := P + 1;
  end
  else
    while (P < Len) and (ALine[P] <> ' ') and (ALine[P] <> #9) do
    begin
      Cur := Cur + Chr(Ord(ALine[P]));
      P := P + 1;
    end;
  SetLength(Args, 1);
  Args[0] := Cur;
  { the arguments }
  while True do
  begin
    while (P < Len) and ((ALine[P] = ' ') or (ALine[P] = #9)) do
      P := P + 1;
    if P >= Len then Break;
    Cur := '';
    InQuote := False;
    while (P < Len) and (InQuote or ((ALine[P] <> ' ') and (ALine[P] <> #9))) do
    begin
      if ALine[P] = '\' then
      begin
        N := 0;
        while (P < Len) and (ALine[P] = '\') do
        begin
          N := N + 1;
          P := P + 1;
        end;
        if (P < Len) and (ALine[P] = '"') then
        begin
          for K := 1 to N div 2 do
            Cur := Cur + '\';
          if N mod 2 = 1 then
          begin
            Cur := Cur + '"';
            P := P + 1;
          end;
        end
        else
          for K := 1 to N do
            Cur := Cur + '\';
      end
      else if ALine[P] = '"' then
      begin
        if InQuote and (P + 1 < Len) and (ALine[P + 1] = '"') then
        begin
          Cur := Cur + '"';
          P := P + 2;
        end
        else
        begin
          InQuote := not InQuote;
          P := P + 1;
        end;
      end
      else
      begin
        Cur := Cur + Chr(Ord(ALine[P]));
        P := P + 1;
      end;
    end;
    SetLength(Args, Length(Args) + 1);
    Args[Length(Args) - 1] := Cur;
  end;
  { the C vector: lives as long as the process }
  Count := Length(Args);
  Vec := PPointer(_BlaiseGetMem((Count + 1) * SizeOf(Pointer)));
  for I := 0 to Count - 1 do
  begin
    Buf := PChar(_BlaiseGetMem(Length(Args[I]) + 1));
    for J := 0 to Length(Args[I]) - 1 do
      Buf[J] := Args[I][J];
    Buf[Length(Args[I])] := #0;
    PPointer(Pointer(Vec) + I * SizeOf(Pointer))^ := Buf;
  end;
  PPointer(Pointer(Vec) + Count * SizeOf(Pointer))^ := nil;
  AArgc := Count;
  AArgv := Vec;
end;

{ The command line as UTF-8, NUL-terminated. }
function CommandLineUtf8: PChar;
var
  Wide: Pointer;
  N: Int32;
begin
  Wide := GetCommandLineW();
  N := WideCharToMultiByte(CP_UTF8, 0, Wide, -1, nil, 0, nil, nil);
  Result := PChar(_BlaiseGetMem(N + 1));
  WideCharToMultiByte(CP_UTF8, 0, Wide, -1, Result, N, nil, nil);
  Result[N] := #0;
end;

procedure _start; cdecl;
var
  Argc: Int32;
  Argv: Pointer;
  Guarantee: UInt32;
begin
  SetErrorMode(SEM_FAILCRITICALERRORS or SEM_NOGPFAULTERRORBOX or
    SEM_NOOPENFILEERRORBOX);
  if TlsIndex() <> 0 then
  begin
    PutStr('Runtime error: the executable''s TLS index is not 0'#13#10);
    TerminateProcess(GetCurrentProcess(), 3);
  end;
  SetConsoleOutputCP(CP_UTF8);
  SetConsoleCP(CP_UTF8);
  Guarantee := HANDLER_STACK;
  SetThreadStackGuarantee(@Guarantee);
  AddVectoredExceptionHandler(1, Pointer(@FaultHandler));
  SplitCommandLine(CommandLineUtf8(), Argc, Argv);
  _RunAtExitAndExit(main(Argc, Argv));
end;

end.
