{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Test runner for BlaiseGuard.

  Pulls in every test unit via Test.Registry (each self-registers through its
  initialization section), then runs them with the text runner.  Exits 0 when
  everything passes, 1 otherwise. }

program TestRunner;

uses
  blaise.testing,
  blaise.testing.runner.text,
  Test.Registry;

begin
  Halt(RunAll());
end.
