{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Test runner for the migration analyser.  Each test unit self-registers in
  its initialization section.  Exits 0 when everything passes, 1 otherwise. }

program TestRunner;

uses
  blaise.testing,
  blaise.testing.runner.text,
  Migration.Rules.Tests;

begin
  Halt(RunAll());
end.
