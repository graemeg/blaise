{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.defaultargs;

{ Default parameters must be materialised into the call's argument list by
  the semantic pass for EVERY call form.  AnalyseMethodCall (method call
  STATEMENTS) didn't append them: the emitted call then carried fewer
  arguments than the callee's parameter list, and the callee read garbage
  for the missing ones — caller-frame junk once the parameter fell past
  the six SysV registers.  Found 2026-06-10 via the borrowed-local elision
  crash (native EmitInterfaceCall read its stack-passed AObjExpr=nil
  default from an argument slot the caller never wrote). }

interface

uses
  Classes, SysUtils, blaise.testing, uStrCompat,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TDefaultArgsTests = class(TTestCase)
  private
  published
  end;

implementation

initialization
  RegisterTest(TDefaultArgsTests);

end.
