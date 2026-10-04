{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.targets;

{ Fixed code-generation targets for asm-shape unit tests.

  A test that asserts on x86-64 instructions (%rax, callq, movsd ...) must
  generate for x86-64 explicitly.  These suites used HostTarget(), which was
  harmless while every developer machine was x86-64 -- on an arm64 Mac host
  they generated arm64 code and ~40 tests failed on the missing x86-64
  patterns, hiding the real results. }

interface

uses
  blaise.codegen.target;

{ linux-x86_64: the target the x86-64 native-backend asm tests assert on. }
function LinuxX64Target: TTargetDesc;

implementation

function LinuxX64Target: TTargetDesc;
begin
  MakeTarget(osLinux, cpuX86_64, Result);
end;

end.
