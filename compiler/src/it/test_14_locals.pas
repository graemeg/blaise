{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

program test_14_locals;


{ Test program for 'locals' command — lists all in-scope variables }

var
  GlobalCount: Int32;
  Sentinel: Int32;

function Compute(A, B: Int32): Int32;
var
  Sum: Int32;
  Product: Int32;
begin
  Sum := A + B;
  Product := A * B;
  Result := Sum + Product;  { breakpoint here — line 17 }
end;

begin
  WriteLn(Compute(3, 7));
  WriteLn(GlobalCount);
  Sentinel := 1;
end.
