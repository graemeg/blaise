{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ BlaiseGuard - the rule catalogue.

  Every rule unit self-registers in its own initialization section.  This unit
  simply pulls them all in via the uses clause, so a program only needs to
  depend on this one unit to have the full ruleset available.  Adding a rule =
  write the unit + add one line here (mirrors stdlib's Test.Registry). }

unit Guard.Rules.All;

interface

uses
  Guard.Rule.MaxLineLength,     { BL-1001 }
  Guard.Rule.MaxFunctionLines,  { BL-1002 }
  Guard.Rule.DeepNesting,       { BL-1003 }
  Guard.Rule.AvoidManualFree,   { BL-2001 }
  Guard.Rule.ReferenceCycles,   { BL-2002 }
  Guard.Rule.StringIndexing,    { BL-2003 }
  Guard.Rule.DuplicateCodeBlock; { BL-3001 }

implementation

end.
