{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

program test_02_breakpoint_next;



var
  MyInt: Int32;
  Sentinel: Int32;

begin
  WriteLn('Test: Breakpoint and Next');

  MyInt := 10;
  WriteLn('Set MyInt to 10');

  MyInt := 20;
  WriteLn('Set MyInt to 20');

  MyInt := 30;
  WriteLn('Set MyInt to 30');

  WriteLn('Done');
  Sentinel := 1;
end.
