{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ M7: the system walks the stack through Blaise frames.
  RtlCaptureStackBackTrace unwinds with the image's .pdata / .xdata; a
  routine with no entry there is taken for a leaf, whose return address is
  at the stack pointer, so the walk lost its way in the first Blaise frame.
  Three Blaise routines deep, it must see them all, the main program and
  the system's start-up frames beyond. }
program m7unwind;

function RtlCaptureStackBackTrace(ASkip, ACount: UInt32; ABackTrace: Pointer;
  AHash: Pointer): UInt16; external 'kernel32' name 'RtlCaptureStackBackTrace';

var
  Frames: array[0..63] of Pointer;
  Depth: Int;
  Sink: Int;

procedure Third(N: Int);
var
  I: Int;
begin
  for I := 0 to N do
    Sink := Sink + I;
  Depth := RtlCaptureStackBackTrace(0, 64, @Frames[0], nil);
end;

procedure Second(N: Int);
var
  I: Int;
begin
  for I := 0 to N do
    Sink := Sink + I;
  Third(N + 1);
  Sink := Sink + 1;
end;

procedure First(N: Int);
var
  I: Int;
begin
  for I := 0 to N do
    Sink := Sink + I;
  Second(N + 1);
  Sink := Sink + 1;
end;

begin
  First(1);
  if Depth >= 6 then
    WriteLn('stack walk ok')
  else
    WriteLn('stack walk stopped after ', Depth, ' frames');
end.
