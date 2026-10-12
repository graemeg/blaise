{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.proctypes;

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSemantic, uSymbolTable, cp.test.harness;

type
  TProcTypesTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function FindTypeDecl(AProg: TProgram; const AName: string): TTypeDecl;
  published
    { x86-64: an interface argument through a procedural variable is its
      two-slot fat pointer (BUG-20260924-proctype-interface-arg); a float
      argument to a procedural FIELD is an xmm slot; a by-value interface
      parameter split across %r9 and the stack reads its itab half back }
    procedure TestCodegen_ProcVarCall_InterfaceArg_TwoSlots;
    procedure TestCodegen_ProcFieldCall_FloatArg_InXmm;
    procedure TestCodegen_IntfParam_SplitAcrossLastRegister;
    { a method pointer copied from another variable or a field moves BOTH
      16 bytes (x86-64 stored the source's ADDRESS as the code pointer, or
      only the code half; arm64 refused an implicit-Self field source) }
    procedure TestCodegen_MethodPtrCopy_BothHalves;
    { AM[I] := GM for a method-pointer element: a 16-byte copy on both (x86-64
      stored 8 bytes, arm64 refused it) }
    procedure TestCodegen_MethodPtrElementStore_CopiesBothHalves;
    { R.M() / X := R.F() with R a record FIELD of Self and M/F procedural
      fields of it: a call of the field ("Class 'TRec' has no method 'M'" /
      "Undeclared identifier 'R'") }
    procedure TestSemantic_ImplicitSelfRecordProcField_IsCalled;
    { a nested routine that only CALLS an outer procedural variable captures
      it (it called through a slot of that name it did not have) }
    procedure TestSemantic_IndirectCallCallee_IsCaptured;
    { Parser — bare procedural type declarations }
    procedure TestParse_NoArgFunc_KindIsProcedural;
    procedure TestParse_NoArgFunc_ReturnTypeIsInteger;
    procedure TestParse_FuncWithParams_ParamCount;
    procedure TestParse_FuncWithParams_FirstParamName;
    procedure TestParse_FuncWithParams_ConstParamFlag;
    procedure TestParse_NoArgProc_KindIsProcedural;
    procedure TestParse_NoArgProc_NoReturnType;
    procedure TestParse_ProcWithVarParam_VarParamFlag;

    { Semantic — type assignability }
    procedure TestSemantic_AssignCompatibleFunc_OK;
    procedure TestSemantic_AssignWrongReturnType_Fails;
    procedure TestSemantic_AssignWrongParamCount_Fails;

    { Semantic — indirect-call argument type checking.
      Calls through a procedural-typed variable must validate each
      argument's type against the signature, not just the arg count. }
    procedure TestSemantic_IndirectCallStmt_WrongArgType_Fails;
    procedure TestSemantic_IndirectCallExpr_WrongArgType_Fails;
    { The same checks for a QUALIFIED procedural-field call (Obj.FP(..)),
      which used to bind the field and skip argument checking entirely.
      BUG-20260722-procfield-set-literal-arg. }
    procedure TestSemantic_QualifiedProcFieldCall_WrongArgCount_Fails;
    procedure TestSemantic_QualifiedProcFieldCallExpr_WrongArgType_Fails;

    { Codegen — emission }
    { BUG-20260923-qbe-implicit-self-ref-field-call: an unqualified call to a
      'reference to' field must pass the closure env (Data half) first. }
    { A procedural-typed class field called through a receiver as an
      expression (Result := Self.FFn(S)) must type to the field's return
      type and dispatch through the loaded pointer, not a direct call. }
    { BUG-20260722-closure-record-field-direct-call: a proc-field call on a
      RECORD variable must use the record's ADDRESS as the base.  Both
      backends loaded the slot's CONTENTS (the class-receiver convention),
      so the record's first 8 bytes were dispatched through as if they were
      an instance pointer.  ResolvedMethod is nil for a proc-field call, so
      every record arm gated on MDecl.IsRecordMethod was skipped. }
    { An unqualified procedural-field call via implicit Self (Result := FFn(S),
      no 'Self.' prefix) must resolve and dispatch through Self's field. }
    { BUG-20260923-closure-call-via-byval-record-param: a BY-VALUE record
      parameter is passed BY REFERENCE, so its slot holds the caller's record
      ADDRESS — exactly like a var param.  The five method-call STATEMENT
      sites in uSemantic used the narrow `Kind = skVarParameter` test, while
      every expression / field-access site already used the full predicate
      that also covers a by-value record or static-array parameter.  The
      call path therefore treated the parameter SLOT as the record base. }
    { BUG-20260923-addr-of-openarray-proc: an open-array (or array of const)
      param of a procedural type must stay an open array -- it resolved as
      its element type -- so @Proc is assignable, a scalar arg is rejected,
      and an indirect call passes the array as its (data, high) pair. }
    procedure TestSemantic_AddrOfOpenArrayProc_Assignable;
    procedure TestSemantic_AddrOfOpenArrayProc_ElementMismatch_Fails;
    procedure TestSemantic_ProcTypeOpenArrayParam_ScalarArg_Fails;
  end;

implementation

function TProcTypesTests.ParseSrc(const ASrc: string): TProgram;
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

function TProcTypesTests.FindTypeDecl(AProg: TProgram; const AName: string): TTypeDecl;
var
  I: Integer;
  TD: TTypeDecl;
begin
  Result := nil;
  for I := 0 to AProg.Block.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(AProg.Block.TypeDecls.Items[I]);
    if SameText(TD.Name, AName) then
    begin
      Result := TD;
      Exit;
    end;
  end;
end;

{ ── Parser tests ─────────────────────────────────────────────────────────── }

procedure TProcTypesTests.TestParse_NoArgFunc_KindIsProcedural;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TIntFn = function: Integer;
        begin
        end.
        '''
  );
  try
    TD := FindTypeDecl(Prog, 'TIntFn');
    AssertNotNull('Should find type decl TIntFn', TD);
    AssertTrue('Def should be a TProceduralTypeDef',
      TD.Def is TProceduralTypeDef);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_NoArgFunc_ReturnTypeIsInteger;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TIntFn = function: Integer;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TIntFn');
    Def := TProceduralTypeDef(TD.Def);
    AssertEquals('IsFunction should be True', True, Def.IsFunction);
    AssertEquals('ReturnTypeName should be Integer', 'Integer', Def.ReturnTypeName);
    AssertEquals('Should have 0 params', 0, Def.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_FuncWithParams_ParamCount;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TBinFn = function(A: Integer; B: Integer): Integer;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TBinFn');
    Def := TProceduralTypeDef(TD.Def);
    AssertEquals('Should have 2 params', 2, Def.Params.Count);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_FuncWithParams_FirstParamName;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
  P1:   TMethodParam;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TBinFn = function(A: Integer; B: Integer): Integer;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TBinFn');
    Def := TProceduralTypeDef(TD.Def);
    P1  := TMethodParam(Def.Params.Items[0]);
    AssertEquals('First param name', 'A', P1.ParamName);
    AssertEquals('First param type', 'Integer', P1.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_FuncWithParams_ConstParamFlag;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
  P1:   TMethodParam;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TStrFn = function(const S: string): Integer;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TStrFn');
    Def := TProceduralTypeDef(TD.Def);
    P1  := TMethodParam(Def.Params.Items[0]);
    AssertEquals('Param name', 'S', P1.ParamName);
    AssertTrue('IsConstParam should be True', P1.IsConstParam);
    AssertFalse('IsVarParam should be False', P1.IsVarParam);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_NoArgProc_KindIsProcedural;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TVoidProc = procedure;
        begin
        end.
        '''
  );
  try
    TD := FindTypeDecl(Prog, 'TVoidProc');
    AssertNotNull('Should find type decl TVoidProc', TD);
    AssertTrue('Def should be a TProceduralTypeDef',
      TD.Def is TProceduralTypeDef);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_NoArgProc_NoReturnType;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TVoidProc = procedure;
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TVoidProc');
    Def := TProceduralTypeDef(TD.Def);
    AssertEquals('IsFunction should be False', False, Def.IsFunction);
    AssertEquals('ReturnTypeName should be empty', '', Def.ReturnTypeName);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestParse_ProcWithVarParam_VarParamFlag;
var
  Prog: TProgram;
  TD:   TTypeDecl;
  Def:  TProceduralTypeDef;
  P1:   TMethodParam;
begin
  Prog := ParseSrc(
    '''
        program Test;
        type
          TIncProc = procedure(var X: Integer);
        begin
        end.
        '''
  );
  try
    TD  := FindTypeDecl(Prog, 'TIncProc');
    Def := TProceduralTypeDef(TD.Def);
    P1  := TMethodParam(Def.Params.Items[0]);
    AssertTrue('IsVarParam should be True', P1.IsVarParam);
    AssertFalse('IsConstParam should be False', P1.IsConstParam);
  finally
    Prog.Free();
  end;
end;

{ ── Semantic tests ───────────────────────────────────────────────────────── }

procedure TProcTypesTests.TestSemantic_AssignCompatibleFunc_OK;
begin
  { Should not raise. Assigning @MyFn to a TIntFn variable type-checks. }
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
        program Test;
        type
          TIntFn = function: Integer;
        function MyFn: Integer;
        begin
          Result := 42;
        end;
        var F: TIntFn;
        begin
          F := @MyFn;
        end.
        '''));
end;

procedure TProcTypesTests.TestSemantic_AssignWrongReturnType_Fails;
begin
  AssertTrue('Should raise on incompatible return type',
    SemanticError(
      '''
          program Test;
          type
            TIntFn = function: Integer;
          function MyFn: string;
          begin
            Result := 'nope';
          end;
          var F: TIntFn;
          begin
            F := @MyFn;
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_AssignWrongParamCount_Fails;
begin
  AssertTrue('Should raise on incompatible param count',
    SemanticError(
      '''
          program Test;
          type
            TIntFn = function: Integer;
          function MyFn(X: Integer): Integer;
          begin
            Result := X;
          end;
          var F: TIntFn;
          begin
            F := @MyFn;
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_QualifiedProcFieldCall_WrongArgCount_Fails;
begin
  AssertTrue('Qualified proc-field call must reject a wrong arg count',
    SemanticError(
      '''
          program Test;
          type
            TP = procedure(A, B: Integer);
            TBox = class
              FP: TP;
            end;
          var X: TBox;
          begin
            X.FP(1)
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_QualifiedProcFieldCallExpr_WrongArgType_Fails;
begin
  AssertTrue('Qualified proc-field call expr must reject string where Integer expected',
    SemanticError(
      '''
          program Test;
          type
            TF = function(N: Integer): Integer;
            TBox = class
              FF: TF;
            end;
          var X: TBox; R: Integer;
          begin
            R := X.FF('oops')
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_IndirectCallStmt_WrongArgType_Fails;
begin
  { Statement-form indirect call: H('s') where H expects Integer must
    be rejected at semantic time, not silently miscompiled. }
  AssertTrue('Indirect call statement should reject string where Integer expected',
    SemanticError(
      '''
          program Test;
          type
            THandler = procedure(N: Integer);
          procedure DoIt(N: Integer);
          begin
          end;
          var H: THandler;
          begin
            H := @DoIt;
            H('oops')
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_IndirectCallExpr_WrongArgType_Fails;
begin
  { Expression-form indirect call: R := F('s') where F expects Integer
    must also be rejected at semantic time. }
  AssertTrue('Indirect call expression should reject string where Integer expected',
    SemanticError(
      '''
          program Test;
          type
            TIntFn = function(N: Integer): Integer;
          function Square(N: Integer): Integer;
          begin
            Result := N * N
          end;
          var F: TIntFn; R: Integer;
          begin
            F := @Square;
            R := F('oops')
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_AddrOfOpenArrayProc_Assignable;
begin
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
        program Test;
        type
          TCnt = function(const A: array of Integer): Integer;
          TFmt = procedure(const S: string; const Args: array of const);
        function Cnt(const A: array of Integer): Integer;
        begin
          Result := Length(A)
        end;
        procedure Fmt(const S: string; const Args: array of const);
        begin
        end;
        var
          C: TCnt;
          F: TFmt;
        begin
          C := @Cnt;
          F := @Fmt
        end.
        '''));
end;

procedure TProcTypesTests.TestSemantic_AddrOfOpenArrayProc_ElementMismatch_Fails;
begin
  AssertTrue('array of Byte routine must not match an array of Integer signature',
    SemanticError(
      '''
          program Test;
          type
            TCnt = function(const A: array of Integer): Integer;
          function Cnt(const A: array of Byte): Integer;
          begin
            Result := Length(A)
          end;
          var C: TCnt;
          begin
            C := @Cnt
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_ProcTypeOpenArrayParam_ScalarArg_Fails;
begin
  AssertTrue('an Integer is not an array of Integer',
    SemanticError(
      '''
          program Test;
          type
            TCnt = function(const A: array of Integer): Integer;
          var
            C: TCnt;
            N: Integer;
          begin
            N := C(5)
          end.
          ''') <> '');
end;

const
  SrcProcIntfFloat = '''
    program pf;
    type
      IGreet = interface function Name(): string; end;
      TGreet = class(TObject, IGreet) public function Name(): string; end;
      TShow = procedure(const G: IGreet);
      TF = function(X: Double; N: Integer): Integer;
      TBox = class Show: TShow; F: TF; end;
      TR = record Show: TShow; F: TF; end;
    function TGreet.Name(): string; begin Result := 'bob' end;
    procedure Show(const G: IGreet); begin WriteLn(G.Name()) end;
    function FF(X: Double; N: Integer): Integer; begin Result := Trunc(X * 10) + N end;
    var P: TShow; G: IGreet; B: TBox; R: TR;
    begin
      G := TGreet.Create(); Show(G);
      P := @Show; P(G);
      B := TBox.Create(); B.Show := @Show; B.Show(G);
      B.F := @FF; WriteLn(B.F(2.5, 3));
      R.Show := @Show; R.Show(G);
      R.F := @FF; WriteLn(R.F(1.5, 4));
    end.
    ''';

procedure TProcTypesTests.TestCodegen_ProcVarCall_InterfaceArg_TwoSlots;
begin
  AssertEquals('P(G) passes obj and itab', '',
    AsmMissing(SrcProcIntfFloat,
      #9'movq %rax, 0(%rsp)'#10#9'movq %rcx, 8(%rsp)'#10 +
        #9'movq 0(%rsp), %rdi'#10#9'movq 8(%rsp), %rsi'#10 +
        #9'movq P(%rip), %r10',
      #9'blr '));
end;

procedure TProcTypesTests.TestCodegen_ProcFieldCall_FloatArg_InXmm;
begin
  AssertEquals('B.F(2.5, 3) loads the float into %xmm0', '',
    AsmMissing(SrcProcIntfFloat,
      #9'movsd 0(%rsp), %xmm0',
      #9'blr '));
end;

procedure TProcTypesTests.TestCodegen_IntfParam_SplitAcrossLastRegister;
const
  Src = '''
    program m4;
    type
      IS1 = interface function V: Integer; end;
      TS = class(TObject, IS1) N: Integer; function V: Integer; end;
      TBig = record A, B, C: Int64; end;
      TP = function(A, B, C, D, E: Integer; const I: IS1; F: Integer): Integer;
      TK = class
        function M(A, B, C, D, E: Integer; const I: IS1; F: Integer): Integer;
      end;
    function TS.V: Integer; begin Result := N end;
    function MkS(K: Integer): IS1; var T: TS; begin T := TS.Create(); T.N := K; Result := T end;
    function Seven(A, B, C, D, E: Integer; const I: IS1; F: Integer): Integer;
    begin Result := A + E + I.V() * 10 + F * 1000 end;
    function SevenF(X: Double; const I: IS1; F: Integer): Integer;
    begin Result := Trunc(X) + I.V() * 10 + F * 1000 end;
    function SR(const I: IS1; K: Integer): TBig; begin Result.A := I.V(); Result.B := K end;
    function TK.M(A, B, C, D, E: Integer; const I: IS1; F: Integer): Integer;
    begin Result := A + I.V() * 10 + F * 1000 end;
    var P: TP; K: TK; R: TBig;
    begin
      WriteLn(Seven(1, 2, 3, 4, 5, MkS(6), 7));
    end.
    ''';
begin
  AssertEquals('Seven copies the itab half in from the stack', '',
    AsmMissing(Src,
      #9'movq %r9, -56(%rbp)'#10#9'movq 16(%rbp), %rax'#10 +
        #9'movq %rax, -48(%rbp)',
      #9'bl _Seven'#10));
end;

procedure TProcTypesTests.TestCodegen_MethodPtrCopy_BothHalves;
const
  Src = '''
    program P;
    type
      TMeth = procedure of object;
      TObj = class M: TMeth; procedure Run; end;
    procedure TObj.Run; var K: TMeth; begin K := M end;
    var A, B: TMeth;
    begin
      B := A;
    end.
    ''';
begin
  AssertEquals('both halves copied', '',
    AsmMissing(Src,
      #9'popq %rsi' + #10 + #9'movq (%rsi), %rax' + #10 +
        #9'movq %rax, (%rcx)' + #10 + #9'movq 8(%rsi), %rax' + #10 +
        #9'movq %rax, 8(%rcx)',
      #9'ldr x1, [sp], #16' + #10 + #9'ldp x9, x10, [x1]' + #10 +
        #9'sub x1, x29, #'));
end;

procedure TProcTypesTests.TestCodegen_MethodPtrElementStore_CopiesBothHalves;
const
  Src = '''
    program P;
    type TMeth = procedure of object;
    var GM: TMeth; AM: array[0..1] of TMeth;
    begin
      AM[1] := GM;
    end.
    ''';
begin
  AssertEquals('a 16-byte element copy', '',
    AsmMissing(Src,
      #9'movq $16, %rdx' + #10 + #9'callq memcpy',
      #9'ldp x10, x11, [x1]' + #10 + #9'stp x10, x11, [x9]'));
end;

procedure TProcTypesTests.TestSemantic_ImplicitSelfRecordProcField_IsCalled;
var
  Prog: TProgram;
begin
  Prog := Analyse('''
    program P;
    type
      TFn = function: Integer of object;
      TMeth = procedure of object;
      TRec = record M: TMeth; F: TFn; end;
      TObj = class R: TRec; procedure Run; end;
    procedure TObj.Run;
    var X: Integer;
    begin
      R.M();
      X := R.F() + 1;
    end;
    begin
    end.
    ''');
  AssertNotNull('analysed', Prog);
  Prog.Free();
end;

procedure TProcTypesTests.TestSemantic_IndirectCallCallee_IsCaptured;
var
  Prog: TProgram;
  Outer, Inner: TMethodDecl;
begin
  Prog := Analyse('''
    program P;
    type TClos = reference to procedure;
    procedure Outer(VC: TClos);
      procedure Inner;
      begin
        VC();
      end;
    begin
      Inner();
    end;
    begin
    end.
    ''');
  try
    Outer := TMethodDecl(Prog.Block.ProcDecls.Items[0]);
    Inner := TMethodDecl(Outer.Body.ProcDecls.Items[0]);
    AssertTrue('VC captured',
      (Inner.CapturedVars <> nil) and (Inner.CapturedVars.IndexOf('VC') >= 0));
  finally
    Prog.Free();
  end;
end;

initialization
  RegisterTest(TProcTypesTests);

end.
