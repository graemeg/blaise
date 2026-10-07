{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.pointers;

{ Tests for pointer type infrastructure: ^T types, P^ dereference,
  P^ := V store, GetMem/FreeMem/ReallocMem built-ins, and pointer arithmetic. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, blaise.codegen.qbe,
  blaise.codegen.native, blaise.codegen.native.backend, blaise.codegen.target;

type
  TPointerTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function GenIR(const ASrc: string): string;
    procedure AnalyseExpectError(const ASrc: string);
    procedure GenNativeExpectCodeGenError(const ASrc: string);
  published
    { ------------------------------------------------------------------ }
    { Parser — pointer type names and expressions                          }
    { ------------------------------------------------------------------ }
    procedure TestParse_PointerTypeName_Caret;
    procedure TestParse_DerefExpr_NodeType;
    procedure TestParse_PointerWriteStmt_NodeType;

    { ------------------------------------------------------------------ }
    { Semantic — tyPointer kind and typed pointer base type                }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_UntypedPointer_Kind;
    procedure TestSemantic_TypedPointer_Kind;
    procedure TestSemantic_TypedPointer_BaseType;
    procedure TestSemantic_GetMem_ReturnsPointer;
    procedure TestSemantic_FreeMem_IsCallable;
    procedure TestSemantic_Deref_ResolvedType;
    procedure TestSemantic_PointerWrite_AcceptsMatchingType;

    { ------------------------------------------------------------------ }
    { BUG-035 — unsupported memory-builtin forms must be rejected cleanly }
    { (the native backend used to segfault on the nil ResolvedDecl)       }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_GetMem_StatementForm_Rejected;
    procedure TestSemantic_ReallocMem_StatementForm_Rejected;
    procedure TestSemantic_FreeMem_TwoArgs_Rejected;
    procedure TestSemantic_GetMem_WrongArity_Rejected;
    procedure TestSemantic_ReallocMem_WrongArity_Rejected;
    { A builtin FUNCTION in statement position that semantic still lets
      through must raise the backend's clean 'Unknown procedure' error on
      BOTH backends — never dereference the nil decl. }
    procedure TestNative_BuiltinFuncStatement_RaisesCleanly;
    procedure TestQBE_BuiltinFuncStatement_RaisesCleanly;

    { ------------------------------------------------------------------ }
    { Codegen — emit malloc / free / load / store / pointer arithmetic     }
    { ------------------------------------------------------------------ }

    { ------------------------------------------------------------------ }
    { Pointer(intExpr) and PtrUInt(ptrExpr) cast pairs                    }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Pointer_FromInt_ReturnsPointerType;
    procedure TestSemantic_PtrUInt_FromPointer_ReturnsUInt64Type;

    { ------------------------------------------------------------------ }
    { p^.field[index] := value (issue #118)                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_DerefFieldSubscript_Parses;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                     }
{ ------------------------------------------------------------------ }

const
  { Untyped pointer variable declaration }
  SrcUntypedPtr =
    '''
        program Prg;
        var P: Pointer;
        begin
        end.
        ''';

  { Typed pointer variable declaration }
  SrcTypedPtrDecl =
    '''
        program Prg;
        var P: ^Integer;
        begin
        end.
        ''';

  { GetMem allocation }
  SrcGetMem =
    '''
        program Prg;
        var P: Pointer;
        begin
          P := GetMem(8)
        end.
        ''';

  { FreeMem call }
  SrcFreeMem =
    '''
        program Prg;
        var P: Pointer;
        begin
          P := GetMem(8);
          FreeMem(P)
        end.
        ''';

  { Typed pointer: write and read through a typed pointer variable.
    No allocation needed — we test AST/IR shapes, not runtime correctness. }
  SrcTypedPtrRW =
    '''
        program Prg;
        var
          Ptr: ^Integer;
          V: Integer;
        begin
          Ptr^ := 42;
          V := Ptr^
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TPointerTests.ParseSrc(const ASrc: string): TProgram;
var
  L: TLexer;
  P: TParser;
begin
  L := TLexer.Create(ASrc);
  P := TParser.Create(L);
  try
    Result := P.Parse();
  finally
    P.Free();
    L.Free();
  end;
end;

function TPointerTests.AnalyseSrc(const ASrc: string): TProgram;
var
  SA: TSemanticAnalyser;
begin
  Result := ParseSrc(ASrc);
  SA     := TSemanticAnalyser.Create();
  try
    SA.Analyse(Result);
  finally
    SA.Free();
  end;
end;

function TPointerTests.GenIR(const ASrc: string): string;
var
  CG:   TCodeGenQBE;
  Prog: TProgram;
begin
  Prog := AnalyseSrc(ASrc);
  CG   := TCodeGenQBE.Create();
  try
    CG.Generate(Prog);
    Result := CG.GetOutput();
  finally
    CG.Free();
    Prog.Free();
  end;
end;

procedure TPointerTests.AnalyseExpectError(const ASrc: string);
var
  Prog: TProgram;
begin
  try
    Prog := AnalyseSrc(ASrc);
    Prog.Free();
    Fail('Expected ESemanticError');
  except
    on E: ESemanticError do ; { expected }
  end;
end;

procedure TPointerTests.GenNativeExpectCodeGenError(const ASrc: string);
var
  CG:   TCodeGenNative;
  Prog: TProgram;
begin
  Prog := AnalyseSrc(ASrc);
  try
    CG := TCodeGenNative.Create();
    try
      CG.SetTarget(HostTarget());
      try
        CG.Generate(Prog);
        Fail('Expected ENativeCodeGenError');
      except
        on E: ENativeCodeGenError do ; { expected }
      end;
    finally
      CG.Free();
    end;
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TPointerTests.TestParse_PointerTypeName_Caret;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := ParseSrc(SrcTypedPtrDecl);
  try
    Decl := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('^Integer', Decl.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestParse_DerefExpr_NodeType;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  { V := Ptr^ — RHS should be TDerefExpr }
  Prog := ParseSrc(SrcTypedPtrRW);
  try
    { Second stmt: V := Ptr^ }
    Assign := TAssignment(Prog.Block.Stmts[1]);
    AssertTrue('Deref should be TDerefExpr', Assign.Expr is TDerefExpr);
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestParse_PointerWriteStmt_NodeType;
var
  Prog: TProgram;
begin
  { Ptr^ := 42 — should be TPointerWriteStmt }
  Prog := ParseSrc(SrcTypedPtrRW);
  try
    { First stmt: Ptr^ := 42 }
    AssertTrue('Ptr write should be TPointerWriteStmt',
      Prog.Block.Stmts[0] is TPointerWriteStmt);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                       }
{ ------------------------------------------------------------------ }

procedure TPointerTests.TestSemantic_UntypedPointer_Kind;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := AnalyseSrc(SrcUntypedPtr);
  try
    Decl := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('Untyped pointer kind', Ord(tyPointer),
      Ord(Decl.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestSemantic_TypedPointer_Kind;
var
  Prog: TProgram;
  Decl: TVarDecl;
begin
  Prog := AnalyseSrc(SrcTypedPtrDecl);
  try
    Decl := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('Typed pointer kind', Ord(tyPointer),
      Ord(Decl.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestSemantic_TypedPointer_BaseType;
var
  Prog:    TProgram;
  Decl:    TVarDecl;
  PtrDesc: TPointerTypeDesc;
begin
  Prog := AnalyseSrc(SrcTypedPtrDecl);
  try
    Decl    := TVarDecl(Prog.Block.Decls[0]);
    PtrDesc := TPointerTypeDesc(Decl.ResolvedType);
    AssertNotNull('Typed pointer should have BaseType', PtrDesc.BaseType);
    AssertEquals('BaseType should be Integer', 'Integer', PtrDesc.BaseType.Name);
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestSemantic_GetMem_ReturnsPointer;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := AnalyseSrc(SrcGetMem);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertEquals('GetMem result type', Ord(tyPointer),
      Ord(Assign.Expr.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestSemantic_FreeMem_IsCallable;
var
  Prog: TProgram;
begin
  { Should not raise }
  Prog := AnalyseSrc(SrcFreeMem);
  Prog.Free();
end;

procedure TPointerTests.TestSemantic_Deref_ResolvedType;
var
  Prog:        TProgram;
  Assign:      TAssignment;
  DerefExpr:   TDerefExpr;
begin
  Prog := AnalyseSrc(SrcTypedPtrRW);
  try
    Assign    := TAssignment(Prog.Block.Stmts[1]);
    DerefExpr := TDerefExpr(Assign.Expr);
    AssertEquals('Deref result type', Ord(tyInteger),
      Ord(DerefExpr.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestSemantic_PointerWrite_AcceptsMatchingType;
var
  Prog:     TProgram;
  PtrWrite: TPointerWriteStmt;
begin
  Prog := AnalyseSrc(SrcTypedPtrRW);
  try
    PtrWrite := TPointerWriteStmt(Prog.Block.Stmts[0]);
    AssertNotNull('PointerWrite BaseTy should be set', PtrWrite.BaseTy);
    AssertEquals('BaseTy should be Integer', 'Integer', PtrWrite.BaseTy.Name);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ BUG-035 — unsupported memory-builtin forms                           }
{ ------------------------------------------------------------------ }

procedure TPointerTests.TestSemantic_GetMem_StatementForm_Rejected;
begin
  { The classic Delphi/FPC two-arg procedure form is deliberately not
    supported — GetMem is a function in Blaise (P := GetMem(N)). }
  AnalyseExpectError(
    '''
        program Prg;
        var P: Pointer;
        begin
          GetMem(P, 8)
        end.
        ''');
end;

procedure TPointerTests.TestSemantic_ReallocMem_StatementForm_Rejected;
begin
  AnalyseExpectError(
    '''
        program Prg;
        var P: Pointer;
        begin
          P := GetMem(8);
          ReallocMem(P, 16)
        end.
        ''');
end;

procedure TPointerTests.TestSemantic_FreeMem_TwoArgs_Rejected;
begin
  { The Delphi FreeMem(P, Size) form is not supported either. }
  AnalyseExpectError(
    '''
        program Prg;
        var P: Pointer;
        begin
          P := GetMem(8);
          FreeMem(P, 8)
        end.
        ''');
end;

procedure TPointerTests.TestSemantic_GetMem_WrongArity_Rejected;
begin
  AnalyseExpectError(
    '''
        program Prg;
        var P: Pointer;
        begin
          P := GetMem(1, 2)
        end.
        ''');
end;

procedure TPointerTests.TestSemantic_ReallocMem_WrongArity_Rejected;
begin
  AnalyseExpectError(
    '''
        program Prg;
        var P: Pointer;
        begin
          P := ReallocMem(P)
        end.
        ''');
end;

procedure TPointerTests.TestNative_BuiltinFuncStatement_RaisesCleanly;
begin
  { Length is a builtin FUNCTION; in statement position the semantic pass
    lets it through and no codegen case matches.  The backend must raise a
    clean 'Unknown procedure' error — the nil-ResolvedDecl fall-through
    used to segfault the compiler (BUG-035). }
  GenNativeExpectCodeGenError(
    '''
        program Prg;
        var S: String;
        begin
          S := 'x';
          Length(S)
        end.
        ''');
end;

{ QBE-only (delete with the backend, Phase 2): pins QBE syntax with no
  behaviour behind it. }
procedure TPointerTests.TestQBE_BuiltinFuncStatement_RaisesCleanly;
begin
  try
    GenIR(
      '''
          program Prg;
          var S: String;
          begin
            S := 'x';
            Length(S)
          end.
          ''');
    Fail('Expected ECodeGenError');
  except
    on E: ECodeGenError do ; { expected }
  end;
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                        }
{ ------------------------------------------------------------------ }

const
  SrcPointerFromInt =
    'program Prg;' +
    'var N: Integer; P: Pointer;' +
    'begin N := 42; P := Pointer(N) end.';

  SrcPtrUIntFromPtr =
    'program Prg;' +
    'var P: Pointer; U: UInt64;' +
    'begin P := nil; U := PtrUInt(P) end.';

procedure TPointerTests.TestSemantic_Pointer_FromInt_ReturnsPointerType;
var
  Prog: TProgram;
  Assign: TAssignment;
  Cast: TFuncCallExpr;
begin
  Prog := AnalyseSrc(SrcPointerFromInt);
  try
    Assign := TAssignment(Prog.Block.Stmts.Items[1]);
    Cast   := TFuncCallExpr(Assign.Expr);
    AssertEquals('cast resolves to tyPointer',
      Ord(tyPointer), Ord(Cast.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestSemantic_PtrUInt_FromPointer_ReturnsUInt64Type;
var
  Prog: TProgram;
  Assign: TAssignment;
  Cast: TFuncCallExpr;
begin
  Prog := AnalyseSrc(SrcPtrUIntFromPtr);
  try
    Assign := TAssignment(Prog.Block.Stmts.Items[1]);
    Cast   := TFuncCallExpr(Assign.Expr);
    AssertEquals('cast resolves to tyUInt64',
      Ord(tyUInt64), Ord(Cast.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

const
  SrcDerefFieldSubscript =
    '''
    program P;
    type
      PRec = ^TRec;
      TRec = record
        DA: array of Integer;
      end;
    var
      Ptr: PRec;
      R: TRec;
    begin
      Ptr := @R;
      SetLength(R.DA, 3);
      Ptr^.DA[0] := 100
    end.
    ''';

procedure TPointerTests.TestParse_DerefFieldSubscript_Parses;
var Prog: TProgram;
begin
  Prog := ParseSrc(SrcDerefFieldSubscript);
  AssertNotNull('program parsed', Prog);
  Prog.Free();
end;

initialization
  RegisterTest(TPointerTests);

end.
