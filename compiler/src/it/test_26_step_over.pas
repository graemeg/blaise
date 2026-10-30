{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

program test_26_step_over;

{ Step-over (next) must NOT enter SetResult; must land on the WriteLn line.
  SetResult body is at higher line numbers than the call site, which tests
  that step-over uses function scope (address range) rather than line numbers. }



procedure SetResult(var N: Int32; V: Int32);
begin
  N := V;
end;

var
  Counter: Int32;

begin
  Counter := 0;
  SetResult(Counter, 99);   { line 19 - break here, then next }
  WriteLn(Counter);          { line 20 - should land here }
end.
