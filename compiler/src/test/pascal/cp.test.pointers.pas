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
  uLexer, uParser, uAST, uSymbolTable, uSemantic,
  blaise.codegen.native, blaise.codegen.native.backend, blaise.codegen.target,
  cp.test.harness;

type
  TPointerTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    procedure AnalyseExpectError(const ASrc: string);
  published
    { P^ := Row through a pointer to a static array copies the row; a managed
      row retains the source's elements (x86-64 stored the row's ADDRESS,
      arm64 stopped with 'pointer write of a managed static array') }
    procedure TestCodegen_PointerWriteOfStaticArray_CopiesAndRetains;
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
    { System's pointer aliases (PInteger, PByte, PInt64, ...) need no uses
      entry, and each is the very type its ^Base spelling names. }
    procedure TestSemantic_SystemPointerAliases_BaseTypes;
    procedure TestSemantic_SystemPointerAlias_IsCaretType;
    { A program or unit may still declare its own same-named alias. }
    procedure TestSemantic_SystemPointerAlias_Redeclarable;

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
    procedure TestNative_BuiltinFuncStatement_Compiles;

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

    { ------------------------------------------------------------------ }
    { P^.Method() / GetP()^ statements: the deref-then-field loops took   }
    { '.Name' eagerly, so P^.Get() was a field read followed by a call    }
    { ('Expression is not callable') and the statement forms did not      }
    { parse at all                                                         }
    { ------------------------------------------------------------------ }
    procedure TestParse_DerefMethodCallExpr_IsMethodCall;
    procedure TestParse_DerefMethodCallStmt_IsMethodCall;
    procedure TestParse_CallResultDerefWrite_IsPointerWrite;
    procedure TestParse_CallResultDerefFieldWrite_IsFieldAssignment;
    { P^.Greet() with P: ^IG dispatches through the pair at the pointer
      (x86-64 dispatched through undefined `_obj` / `_itab` symbols) }
    procedure TestNative_DerefInterfaceReceiver_PairAtPointer;

    { ------------------------------------------------------------------ }
    { Move(Source, Dest, Count) — overlap-safe byte copy intrinsic         }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_Move_Variables_Accepted;
    procedure TestSemantic_Move_DerefOperands_Accepted;
    procedure TestSemantic_Move_UnmanagedRecord_Accepted;
    procedure TestSemantic_Move_WrongArity_Rejected;
    procedure TestSemantic_Move_NonVariable_Rejected;
    procedure TestSemantic_Move_NonIntegerCount_Rejected;
    procedure TestSemantic_Move_String_Rejected;
    procedure TestSemantic_Move_ClassRef_Rejected;
    procedure TestSemantic_Move_DynArray_Rejected;
    procedure TestSemantic_Move_RecordWithString_Rejected;
    procedure TestSemantic_Move_StaticArrayOfInterface_Rejected;
    procedure TestSemantic_Move_GenericManagedInstance_Rejected;
    procedure TestNative_Move_CallsBlaiseMoveSourceFirst;

    { ------------------------------------------------------------------ }
    { FillByte(Dest, Count, Value) — byte fill intrinsic; FillChar is      }
    { recognised and pointed at FillByte (Blaise has no Char type)         }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_FillByte_Accepted;
    procedure TestSemantic_FillByte_WrongArity_Rejected;
    procedure TestSemantic_FillByte_NonVariable_Rejected;
    procedure TestSemantic_FillByte_NonIntegerCount_Rejected;
    procedure TestSemantic_FillByte_NonIntegerValue_Rejected;
    procedure TestSemantic_FillByte_ValueOutOfRange_Rejected;
    procedure TestSemantic_FillByte_Managed_Rejected;
    procedure TestSemantic_FillChar_NamesFillByte;
    procedure TestNative_FillByte_CallsBlaiseFillByte;
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

procedure TPointerTests.TestSemantic_SystemPointerAliases_BaseTypes;
const
  Src =
    '''
    program P;
    var
      A: PInteger; B: PCardinal; C: PByte; D: PWord; E: PSmallInt;
      F: PInt64; G: PUInt64; H: PQWord; I: PBoolean; J: PDouble;
      K: PSingle; L: PPointer; M: PInt8; N: PInt16; O: PInt32;
      Q: PUInt8; R: PUInt16; S: PUInt32; T: PPChar; U: PPtrUInt;
      V: PInt; W: PUInt; X: PFloat; Y: PFloat32; Z: PFloat64;
    begin
    end.
    ''';
  Bases: array[0..24] of string = ('Integer', 'UInt32', 'Byte', 'Word',
    'SmallInt', 'Int64', 'UInt64', 'UInt64', 'Boolean', 'Double', 'Single',
    'Pointer', 'Int8', 'SmallInt', 'Integer', 'Byte', 'Word', 'UInt32',
    'PChar', 'UInt64', 'Int64', 'UInt64', 'Double', 'Single', 'Double');
var
  Prog: TProgram;
  Decl: TVarDecl;
  I:    Int;
begin
  Prog := AnalyseSrc(Src);
  try
    for I := 0 to High(Bases) do
    begin
      Decl := TVarDecl(Prog.Block.Decls[I]);
      AssertTrue(Decl.TypeName + ' is a typed pointer',
        Decl.ResolvedType is TPointerTypeDesc);
      AssertEquals(Decl.TypeName + ' base type', Bases[I],
        TPointerTypeDesc(Decl.ResolvedType).BaseType.Name);
    end;
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestSemantic_SystemPointerAlias_IsCaretType;
const
  Src =
    '''
    program P;
    var
      A: PInteger;
      B: ^Integer;
      C: PCardinal;
      D: PUInt32;
    begin
      A := B;
      B := A;
      C := D
    end.
    ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertTrue('PInteger and ^Integer are one type',
      TVarDecl(Prog.Block.Decls[0]).ResolvedType =
      TVarDecl(Prog.Block.Decls[1]).ResolvedType);
    AssertTrue('PCardinal and PUInt32 are one type',
      TVarDecl(Prog.Block.Decls[2]).ResolvedType =
      TVarDecl(Prog.Block.Decls[3]).ResolvedType);
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestSemantic_SystemPointerAlias_Redeclarable;
const
  Src =
    '''
    program P;
    type
      PInteger = ^Integer;
      PByte = ^Integer;
    var
      A: PInteger;
      B: PByte;
    begin
    end.
    ''';
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(Src);
  try
    AssertEquals('own PByte wins', 'Integer',
      TPointerTypeDesc(TVarDecl(Prog.Block.Decls[1]).ResolvedType).BaseType.Name);
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

procedure TPointerTests.TestNative_BuiltinFuncStatement_Compiles;
const
  Src =
    '''
        program Prg;
        var S: String;
        begin
          S := 'x';
          Length(S)
        end.
        ''';
begin
  { Length is a builtin FUNCTION.  As a statement it reached the backend as a
    procedure call with no lowering: first a compiler segfault (BUG-035),
    then a clean 'Unknown procedure' error.  The semantic pass now lowers it
    to its expression form, so it compiles on both ISAs. }
  AssertTrue('x86-64', GenAsm(Src, TargetX86_64) <> '');
  AssertTrue('arm64', GenAsm(Src, TargetArm64) <> '');
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

const
  SrcDerefCalls =
    '''
        program Prg;
        begin
          N := P^.Get();
          P^.Bump();
          GetP()^ := 7;
          GetP()^.X := 8;
          N := (P)^.Get()
        end.
        ''';

procedure TPointerTests.TestParse_DerefMethodCallExpr_IsMethodCall;
var
  Prog: TProgram;
  E: TASTExpr;
begin
  Prog := ParseSrc(SrcDerefCalls);
  try
    E := TAssignment(Prog.Block.Stmts[0]).Expr;
    AssertTrue('P^.Get() is a method call', E is TMethodCallExpr);
    AssertTrue('its receiver is the deref',
      TMethodCallExpr(E).ObjExpr is TDerefExpr);
    E := TAssignment(Prog.Block.Stmts[4]).Expr;
    AssertTrue('(P)^.Get() is a method call', E is TMethodCallExpr);
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestParse_DerefMethodCallStmt_IsMethodCall;
var
  Prog: TProgram;
begin
  Prog := ParseSrc(SrcDerefCalls);
  try
    AssertTrue('P^.Bump() is a method-call statement',
      Prog.Block.Stmts[1] is TMethodCallStmt);
    AssertTrue('its receiver is the deref',
      TMethodCallStmt(Prog.Block.Stmts[1]).ObjExpr is TDerefExpr);
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestParse_CallResultDerefWrite_IsPointerWrite;
var
  Prog: TProgram;
begin
  Prog := ParseSrc(SrcDerefCalls);
  try
    AssertTrue('GetP()^ := 7 is a pointer write',
      Prog.Block.Stmts[2] is TPointerWriteStmt);
    AssertTrue('through the call result',
      TPointerWriteStmt(Prog.Block.Stmts[2]).PtrExpr is TFuncCallExpr);
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestParse_CallResultDerefFieldWrite_IsFieldAssignment;
var
  Prog: TProgram;
begin
  Prog := ParseSrc(SrcDerefCalls);
  try
    AssertTrue('GetP()^.X := 8 is a field assignment',
      Prog.Block.Stmts[3] is TFieldAssignment);
    AssertTrue('on the dereferenced call result',
      TFieldAssignment(Prog.Block.Stmts[3]).ObjExpr is TDerefExpr);
  finally
    Prog.Free();
  end;
end;

procedure TPointerTests.TestNative_DerefInterfaceReceiver_PairAtPointer;
const
  Src = '''
    program P;
    type
      IG = interface
        function Greet: Int64;
      end;
      PIG = ^IG;
    var
      G: IG;
      PG: PIG;
    begin
      PG := @G;
      PG^.Greet();
    end.
    ''';
begin
  AssertEquals('obj and itab load through the pointer', '',
    AsmMissing(Src,
      #9'movq PG(%rip), %rax' + #10 + #9'movq %rax, %r10' + #10 +
        #9'movq 8(%r10), %rax' + #10 + #9'movq (%r10), %r10',
      #9'ldr x0, [x9, _g_PG@PAGEOFF]' + #10 + #9'ldp x0, x1, [x0]'));
  AssertTrue('no nameless receiver slot',
    Pos(#9'movq _obj(%rip)', GenAsm(Src, TargetX86_64)) < 0);
end;

const
  SrcMoveOk = '''
    program P;
    var
      A, B: array[0..3] of Integer;
    begin
      Move(A, B, SizeOf(A));
    end.
    ''';

procedure TPointerTests.TestSemantic_Move_Variables_Accepted;
begin
  AssertEquals('Move between two static arrays', '', SemanticError(SrcMoveOk));
end;

procedure TPointerTests.TestSemantic_Move_DerefOperands_Accepted;
begin
  AssertEquals('Move through typed pointers and elements', '', SemanticError('''
    program P;
    type
      PByte = ^Byte;
    var
      Src, Dst: PByte;
      A: array[0..7] of Byte;
      N: Int64;
    begin
      N := 4;
      Move(Src^, Dst^, N);
      Move(A[0], A[2], 6);
    end.
    '''));
end;

procedure TPointerTests.TestSemantic_Move_UnmanagedRecord_Accepted;
begin
  AssertEquals('record of plain fields', '', SemanticError('''
    program P;
    type
      TPoint = record
        X, Y: Integer;
        Z: Double;
      end;
    var
      A, B: TPoint;
    begin
      Move(A, B, SizeOf(TPoint));
    end.
    '''));
end;

procedure TPointerTests.TestSemantic_Move_WrongArity_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program P;
    var A, B: Integer;
    begin
      Move(A, B);
    end.
    ''');
  AssertTrue('two arguments: ' + Msg, Pos(
    '''Move'' requires exactly 3 arguments: Move(Source, Dest, Count)', Msg) >= 0);
end;

procedure TPointerTests.TestSemantic_Move_NonVariable_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program P;
    var B: Integer;
    begin
      Move(1, B, 4);
    end.
    ''');
  AssertTrue('names the argument: ' + Msg,
    Pos('First argument of ''Move'' must be a variable', Msg) >= 0);
end;

procedure TPointerTests.TestSemantic_Move_NonIntegerCount_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program P;
    var A, B: Integer;
    begin
      Move(A, B, 1.5);
    end.
    ''');
  AssertTrue('names the count: ' + Msg,
    Pos('Count argument of ''Move'' must be an integer', Msg) >= 0);
end;

procedure MoveRejectsManaged(ATest: TPointerTests; const ADecls, AArgs, AType: string);
var
  Msg: string;
begin
  Msg := SemanticError(
    'program P;' + #10 + ADecls + #10 +
    'begin' + #10 + '  Move(' + AArgs + ');' + #10 + 'end.');
  ATest.AssertTrue(AType + ': names the type and the rule: ' + Msg,
    (Pos('''Move'' cannot copy ''' + AType + '''', Msg) >= 0) and
    (Pos('reference-counted', Msg) >= 0) and
    (Pos('assignment', Msg) >= 0));
end;

procedure TPointerTests.TestSemantic_Move_String_Rejected;
begin
  MoveRejectsManaged(Self, 'var S, T: string;', 'S, T, 8', 'string');
end;

procedure TPointerTests.TestSemantic_Move_ClassRef_Rejected;
begin
  MoveRejectsManaged(Self, 'var A, B: TObject;', 'A, B, 8', 'TObject');
end;

procedure TPointerTests.TestSemantic_Move_DynArray_Rejected;
begin
  MoveRejectsManaged(Self,
    'type TInts = array of Integer;' + #10 + 'var A, B: TInts;',
    'A, B, 8', 'array of Integer');
end;

procedure TPointerTests.TestSemantic_Move_RecordWithString_Rejected;
begin
  { the managed field is nested, and only on the DESTINATION side }
  MoveRejectsManaged(Self,
    'type' + #10 +
    '  TInner = record Name: string; end;' + #10 +
    '  TOuter = record Id: Integer; Inner: TInner; end;' + #10 +
    'var A: array[0..31] of Byte; B: TOuter;',
    'A, B, SizeOf(TOuter)', 'TOuter');
end;

procedure TPointerTests.TestSemantic_Move_StaticArrayOfInterface_Rejected;
begin
  MoveRejectsManaged(Self,
    'type' + #10 +
    '  IFoo = interface end;' + #10 +
    '  TFoos = array[0..1] of IFoo;' + #10 +
    'var A, B: TFoos;',
    'A, B, SizeOf(TFoos)', 'array[0..1] of IFoo');
end;

{ The check runs per instantiation: TBox<Integer> is fine, TBox<string>
  is refused at the Move inside the generic body. }
procedure TPointerTests.TestSemantic_Move_GenericManagedInstance_Rejected;
const
  Generic = '''
    program P;
    type
      TBox<T> = class
        A, B: T;
        procedure CopyAB;
      end;
    procedure TBox<T>.CopyAB;
    begin
      Move(A, B, SizeOf(T));
    end;

    ''';
var
  Msg: string;
begin
  AssertEquals('Integer instance is fine', '', SemanticError(Generic + '''
    var I: TBox<Integer>;
    begin
      I := TBox<Integer>.Create();
    end.
    '''));
  Msg := SemanticError(Generic + '''
    var S: TBox<string>;
    begin
      S := TBox<string>.Create();
    end.
    ''');
  AssertTrue('string instance refused: ' + Msg,
    Pos('''Move'' cannot copy ''string''', Msg) >= 0);
end;

procedure TPointerTests.TestNative_Move_CallsBlaiseMoveSourceFirst;
begin
  { Move(Source, Dest, Count) keeps the Pascal argument order in the RTL
    call, so _BlaiseMove receives Source first. }
  AssertEquals('lowers to _BlaiseMove', '',
    AsmMissing(SrcMoveOk, 'callq _BlaiseMove', 'bl __BlaiseMove'));
end;

const
  SrcFillOk = '''
    program P;
    var
      A: array[0..7] of Byte;
    begin
      FillByte(A, SizeOf(A), 255);
    end.
    ''';

procedure TPointerTests.TestSemantic_FillByte_Accepted;
begin
  AssertEquals('static array', '', SemanticError(SrcFillOk));
  AssertEquals('deref, element and variable value', '', SemanticError('''
    program P;
    type
      PByte = ^Byte;
      TRec = record
        X, Y: Integer;
      end;
    var
      Q: PByte;
      A: array[0..7] of Integer;
      R: TRec;
      V: Byte;
      N: Int64;
    begin
      V := 7;
      N := 4;
      FillByte(Q^, N, V);
      FillByte(A[2], 8, 0);
      FillByte(R, SizeOf(TRec), 0);
    end.
    '''));
end;

procedure TPointerTests.TestSemantic_FillByte_WrongArity_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program P;
    var A: Integer;
    begin
      FillByte(A, 4);
    end.
    ''');
  AssertTrue('two arguments: ' + Msg, Pos(
    '''FillByte'' requires exactly 3 arguments: FillByte(Dest, Count, Value)',
    Msg) >= 0);
end;

procedure TPointerTests.TestSemantic_FillByte_NonVariable_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program P;
    begin
      FillByte(1, 4, 0);
    end.
    ''');
  AssertTrue('names the argument: ' + Msg,
    Pos('First argument of ''FillByte'' must be a variable', Msg) >= 0);
end;

procedure TPointerTests.TestSemantic_FillByte_NonIntegerCount_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program P;
    var A: Integer;
    begin
      FillByte(A, 1.5, 0);
    end.
    ''');
  AssertTrue('names the count: ' + Msg,
    Pos('Count argument of ''FillByte'' must be an integer', Msg) >= 0);
end;

procedure TPointerTests.TestSemantic_FillByte_NonIntegerValue_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program P;
    var A: Integer;
    begin
      FillByte(A, 4, ' ');
    end.
    ''');
  AssertTrue('names the value and Ord: ' + Msg,
    (Pos('Value argument of ''FillByte'' must be an integer', Msg) >= 0) and
    (Pos('Ord(', Msg) >= 0));
end;

procedure TPointerTests.TestSemantic_FillByte_ValueOutOfRange_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program P;
    var A: Integer;
    begin
      FillByte(A, 4, 256);
    end.
    ''');
  AssertTrue('names the range: ' + Msg,
    Pos('Value argument of ''FillByte'' must be in 0..255, got 256', Msg) >= 0);
end;

procedure TPointerTests.TestSemantic_FillByte_Managed_Rejected;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program P;
    type
      TRec = record
        Id: Integer;
        Name: string;
      end;
    var R: TRec;
    begin
      FillByte(R, SizeOf(TRec), 0);
    end.
    ''');
  AssertTrue('names the type and the rule: ' + Msg,
    (Pos('''FillByte'' cannot fill ''TRec''', Msg) >= 0) and
    (Pos('reference-counted', Msg) >= 0));
end;

procedure TPointerTests.TestSemantic_FillChar_NamesFillByte;
var
  Msg: string;
begin
  Msg := SemanticError('''
    program P;
    var A: array[0..7] of Byte;
    begin
      FillChar(A, SizeOf(A), 0);
    end.
    ''');
  AssertTrue('points to FillByte: ' + Msg,
    (Pos('''FillChar'' is not available in Blaise', Msg) >= 0) and
    (Pos('no Char type', Msg) >= 0) and
    (Pos('FillByte(Dest, Count, Value)', Msg) >= 0));
end;

procedure TPointerTests.TestNative_FillByte_CallsBlaiseFillByte;
begin
  AssertEquals('lowers to _BlaiseFillByte', '',
    AsmMissing(SrcFillOk, 'callq _BlaiseFillByte', 'bl __BlaiseFillByte'));
end;

procedure TPointerTests.TestCodegen_PointerWriteOfStaticArray_CopiesAndRetains;
const
  SrcPlain = '''
      program P;
      type
        TRow = array[0..2] of Integer;
        PRow = ^TRow;
      procedure Put(P: PRow; const R: TRow);
      begin
        P^ := R
      end;
      begin
      end.
      ''';
  SrcManaged = '''
      program P;
      type
        TSRow = array[0..1] of string;
        PSRow = ^TSRow;
      procedure Put(P: PSRow; const R: TSRow);
      begin
        P^ := R
      end;
      begin
      end.
      ''';
begin
  AssertEquals('the row is copied', '',
    AsmMissing(SrcPlain, 'callq memcpy', 'bl _memcpy'));
  AssertEquals('the managed row retains its elements', '',
    AsmMissing(SrcManaged, 'callq _StringAddRef', 'bl __StringAddRef'));
end;

initialization
  RegisterTest(TPointerTests);

end.
