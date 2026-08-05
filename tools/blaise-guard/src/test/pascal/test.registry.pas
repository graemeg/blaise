{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Central registry of BlaiseGuard test units.  Each test unit self-registers in
  its initialization section; this unit pulls them all in.  It also pulls in
  Guard.Rules.All so every rule is registered before the suites run. }

unit Test.Registry;

interface

uses
  Guard.Rules.All,               { registers all rules }
  Guard.Domain.Tests,
  Guard.Rule.MaxLineLength.Tests,
  Guard.Rule.MaxFunctionLines.Tests,
  Guard.Rule.DeepNesting.Tests,
  Guard.Rule.UnusedIdentifiers.Tests,
  Guard.Rule.AvoidManualFree.Tests,
  Guard.Rule.ReferenceCycles.Tests,
  Guard.Rule.StringIndexing.Tests,
  Guard.Rule.DuplicateCodeBlock.Tests,
  Guard.Rule.RedundantComparison.Tests,
  Guard.Rule.UnassignedResult.Tests,
  Guard.Rule.OrdSubscript.Tests,
  Guard.Rule.EmptyHandler.Tests,
  Guard.Rule.ExhaustiveCase.Tests,
  Guard.Suppression.Tests;

implementation

end.
