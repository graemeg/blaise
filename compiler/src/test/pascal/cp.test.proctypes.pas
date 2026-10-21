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
    { FGet() / FProc(1) -- a call through a procedural FIELD of Self, bare,
      inside a nested routine of a method reads Self, so Self is captured }
    procedure TestCodegen_NestedProcFieldCall_CapturesSelf;
    { MkHold().FP(5): a call through a procedural field of a receiver a call
      returned -- the receiver is parked for release at the statement end
      (arm64 refused it, x86-64 had no arm for a call receiver) }
    procedure TestCodegen_ProcFieldCall_OnCallResultReceiver;
    { Obj.OnChange(Sender) / OnChange(Self): a call through a field-backed
      property of procedural type is a call through its backing field; a
      getter-backed one calls the value the getter returns
      (BUG-20261020-getter-proc-property-call) }
    procedure TestSemantic_CallThroughProcProperty_UsesBackingField;
    procedure TestSemantic_CallThroughGetterProcProperty_CallsGetterValue;
    { O.C[I] := K into an array FIELD of closures: a 16-byte copy with the
      Env retained (x86-64 stored 8 bytes; arm64 refused it) }
    procedure TestCodegen_ClosureArrayFieldElemStore_CopiesPair;
    { K = nil / Assigned(K) on a closure tests its CODE half (x86-64 tested
      the block's address: always non-nil) }
    procedure TestCodegen_ClosureNilCompare_TestsCodeHalf;
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
    { BUG-20261013-proctype-inline-param-types: a parameter or return type
      written as an inline type form (^T, set of T, array of T) resolves --
      it was looked up by name only ("Unknown parameter type '^Integer'") --
      and still takes part in the signature check }
    procedure TestSemantic_ProcTypeInlineParamTypes_Resolve;
    procedure TestSemantic_ProcTypeInlineParamType_Mismatch_Fails;
    { GH #222: an inline procedural type in a var declaration or a field
      ("Expected type name").  Same structural rules as a named one: the
      signature is checked on assignment and on a call, an inline and a named
      type with the same signature are compatible, and the of object /
      reference to flags keep the forms apart. }
    procedure TestSemantic_InlineProcVar_Accepted;
    procedure TestSemantic_InlineProcVar_WrongSignature_Fails;
    procedure TestSemantic_InlineProcVar_CompatibleWithNamed;
    procedure TestSemantic_InlineProcVar_WrongArgType_Fails;
    procedure TestSemantic_InlineProcVar_OfObjectAndReference_Accepted;
    procedure TestSemantic_InlineProcVar_OfObjectToBare_Fails;
    { parameter modes are part of the encoded signature: var differs from
      value, and a var-param inline type accepts a matching routine }
    procedure TestSemantic_InlineProcVar_ParamMode_Distinguished;
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
      #9'ldr x9, [sp], #16' + #10 + #9'ldp x10, x11, [x9]' + #10 +
        #9'stp x10, x11, [x1]'));
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
      #9'ldp x0, x1, [sp], #16' + #10 + #9'ldr x9, [sp], #16' + #10 +
        #9'stp x0, x1, [x9]'));
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

procedure TProcTypesTests.TestCodegen_NestedProcFieldCall_CapturesSelf;
const
  Src = '''
    program P;
    type
      TFn = function: Integer of object;
      TProc = procedure(A: Integer) of object;
      THold = class
        FGet: TFn;
        FProc: TProc;
        procedure Run;
      end;
    procedure THold.Run;
    var X: Integer;
      procedure Inner;
      begin
        X := FGet();
        FProc(1);
      end;
    begin
      Inner();
    end;
    begin
    end.
    ''';
begin
  { the nested routine's prologue loads Self through its _cap_Self slot
    (the first hidden argument) into its own Self slot }
  AssertEquals('Self captured by the nested routine', '',
    AsmMissing(Src,
      #9'movq -8(%rbp), %rax'#10#9'movq (%rax), %rax'#10#9'movq %rax, -24(%rbp)',
      #9'ldur x9, [x29, #-8]'#10#9'ldr x0, [x9]'#10#9'stur x0, [x29, #-24]'));
end;

procedure TProcTypesTests.TestCodegen_ProcFieldCall_OnCallResultReceiver;
const
  Src = '''
    program Prg;
    type
      TP = procedure(N: Integer);
      THold = class FP: TP; end;
    function MkHold(): THold; begin Result := THold.Create() end;
    begin
      MkHold().FP(5)
    end.
    ''';
begin
  AssertEquals('the receiver is parked for the statement-end release', '',
    AsmMissing(Src,
      #9'callq MkHold'#10#9'movq %rax, _pendrel_0(%rip)',
      #9'bl _MkHold'#10#9'stur x0, [x29, #-'));
end;

procedure TProcTypesTests.TestSemantic_CallThroughProcProperty_UsesBackingField;
var
  Prog: TProgram;
  Call: TMethodCallStmt;
begin
  Prog := Analyse('''
    program P;
    type
      TNotify = procedure(Sender: TObject) of object;
      TBox = class
      private
        FOnChange: TNotify;
      public
        property OnChange: TNotify read FOnChange write FOnChange;
        procedure Fire;
      end;
    procedure TBox.Fire; begin OnChange(Self) end;
    var B: TBox;
    begin
      B.OnChange(B)
    end.
    ''');
  try
    Call := TMethodCallStmt(Prog.Block.Stmts.Items[0]);
    AssertTrue('a procedural-field call', Call.IsProcFieldCall);
    AssertEquals('through the backing field', 'FOnChange',
      Call.ProcFieldInfo.Name);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestSemantic_CallThroughGetterProcProperty_CallsGetterValue;
var
  Prog: TProgram;
  WL: TProcCall;
  Call: TIndirectFuncCallExpr;
  Stmt: TMethodCallStmt;
begin
  Prog := Analyse('''
    program P;
    type
      TFn = function(N: Integer): Integer;
      TBox = class
        FFn: TFn;
        function GetFn: TFn;
        property Fn: TFn read GetFn;
      end;
    function TBox.GetFn: TFn; begin Result := FFn end;
    var B: TBox;
    begin
      WriteLn(B.Fn(1));
      B.Fn(2);
    end.
    ''');
  try
    WL := TProcCall(Prog.Block.Stmts.Items[0]);
    AssertTrue('the expression is an indirect call',
      TASTExpr(WL.Args.Items[0]) is TIndirectFuncCallExpr);
    Call := TIndirectFuncCallExpr(WL.Args.Items[0]);
    AssertTrue('of the property read through its getter',
      (Call.CalleeExpr is TFieldAccessExpr) and
      (TFieldAccessExpr(Call.CalleeExpr).PropReadDecl <> nil));
    AssertEquals('the argument passed', 1, Call.Args.Count);
    Stmt := TMethodCallStmt(Prog.Block.Stmts.Items[1]);
    AssertTrue('the statement is lowered to the same call',
      Stmt.LoweredCall is TExprCallStmt);
  finally
    Prog.Free();
  end;
end;

procedure TProcTypesTests.TestCodegen_ClosureArrayFieldElemStore_CopiesPair;
const
  Src = '''
    program P;
    type
      TClos = reference to function: Integer;
      TObj = class C: array[0..1] of TClos; end;
    var O: TObj; K: TClos;
    begin
      O.C[1] := K;
    end.
    ''';
begin
  AssertEquals('Env retained, 16 bytes stored', '',
    AsmMissing(Src,
      #9'movq 8(%rbx), %rdi' + #10 + #9'callq _ClassAddRef' + #10 +
        #9'movq 8(%r15), %rdi' + #10 + #9'callq _ClassRelease',
      #9'ldr x9, [sp], #16' + #10 + #9'ldp x0, x1, [sp], #16' + #10 +
        #9'stp x0, x1, [x9]'));
end;

procedure TProcTypesTests.TestCodegen_ClosureNilCompare_TestsCodeHalf;
const
  Src = '''
    program P;
    type TClos = reference to function: Integer;
    var K: TClos; B: Boolean;
    begin
      B := K = nil;
      B := Assigned(K);
    end.
    ''';
begin
  AssertEquals('the code half is tested', '',
    AsmMissing(Src,
      #9'leaq K(%rip), %rax' + #10 + #9'movq (%rax), %rax' + #10 +
        #9'testq %rax, %rax' + #10 + #9'sete %al',
      #9'ldr x0, [x9, _g_K@PAGEOFF]'));
end;

procedure TProcTypesTests.TestSemantic_ProcTypeInlineParamTypes_Resolve;
begin
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
        program Test;
        type
          TPtr = procedure(P: ^Integer);
          TSet = procedure(S: set of Byte);
          TArr = function(): array of Integer;
          TMeta = function(): class of TObject;
        procedure UsePtr(P: ^Integer);
        begin
        end;
        procedure UseSet(S: set of Byte);
        begin
        end;
        function MkArr(): array of Integer;
        begin
        end;
        function MkMeta(): class of TObject;
        begin
          Result := TObject
        end;
        var
          A: TPtr;
          B: TSet;
          C: TArr;
          D: TMeta;
        begin
          A := @UsePtr;
          B := @UseSet;
          C := @MkArr;
          D := @MkMeta
        end.
        '''));
end;

procedure TProcTypesTests.TestSemantic_ProcTypeInlineParamType_Mismatch_Fails;
begin
  AssertTrue('a ^Byte routine must not match a ^Integer signature',
    SemanticError(
      '''
          program Test;
          type
            TPtr = procedure(P: ^Integer);
          procedure UsePtr(P: ^Byte);
          begin
          end;
          var A: TPtr;
          begin
            A := @UsePtr
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_InlineProcVar_Accepted;
begin
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
        program Test;
        type
          TRec = record
            F: function(A, B: Integer): Integer;
          end;
        procedure Report(nr, line, col: Integer; pos: Int64);
        begin
        end;
        function Mul(A, B: Integer): Integer;
        begin
          Result := A * B
        end;
        var
          Error: procedure(nr, line, col: Integer; pos: Int64);
          R: TRec;
          X: Integer;
        procedure Local();
        var H: function(A, B: Integer): Integer;
        begin
          H := @Mul;
          X := H(2, 3)
        end;
        begin
          Error := @Report;
          Error(1, 2, 3, 4);
          R.F := @Mul;
          X := R.F(4, 5)
        end.
        '''));
end;

procedure TProcTypesTests.TestSemantic_InlineProcVar_WrongSignature_Fails;
begin
  AssertTrue('a routine with a different parameter list must not be assignable',
    SemanticError(
      '''
          program Test;
          procedure Report(nr, line: Integer);
          begin
          end;
          var Error: procedure(nr, line, col: Integer);
          begin
            Error := @Report
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_InlineProcVar_CompatibleWithNamed;
begin
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
        program Test;
        type
          TCmp = function(const A, B: string): Integer;
        var
          Named: TCmp;
          Inline1: function(const X, Y: string): Integer;
          Inline2: function(const P, Q: string): Integer;
        begin
          Inline1 := Named;
          Named := Inline1;
          Inline2 := Inline1
        end.
        '''));
end;

procedure TProcTypesTests.TestSemantic_InlineProcVar_WrongArgType_Fails;
begin
  AssertTrue('a call through an inline type checks argument types',
    SemanticError(
      '''
          program Test;
          var Error: procedure(nr: Integer; const S: string);
          begin
            Error('one', 'two')
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_InlineProcVar_OfObjectAndReference_Accepted;
begin
  AssertEquals('program is accepted', '',
    SemanticError(
      '''
        program Test;
        type
          TC = class
            procedure Hi(K: Integer);
          end;
        procedure TC.Hi(K: Integer);
        begin
        end;
        var
          C: TC;
          M: procedure(K: Integer) of object;
          R: reference to function(X: Integer): Integer;
          N: Integer;
        begin
          C := TC.Create();
          M := @C.Hi;
          M(1);
          R := function(X: Integer): Integer
               begin
                 Result := X + 1
               end;
          N := R(2)
        end.
        '''));
end;

procedure TProcTypesTests.TestSemantic_InlineProcVar_OfObjectToBare_Fails;
begin
  AssertTrue('a method pointer must not bind to a bare procedural variable',
    SemanticError(
      '''
          program Test;
          var
            M: procedure(K: Integer) of object;
            P: procedure(K: Integer);
          begin
            P := M
          end.
          ''') <> '');
end;

procedure TProcTypesTests.TestSemantic_InlineProcVar_ParamMode_Distinguished;
begin
  AssertEquals('a var-param routine matches a var-param inline type', '',
    SemanticError(
      '''
        program Test;
        procedure Get(var sym: Integer);
        begin
          sym := 1
        end;
        var G: procedure(var sym: Integer);
        begin
          G := @Get
        end.
        '''));
  AssertTrue('a value-param routine must not match a var-param inline type',
    SemanticError(
      '''
          program Test;
          procedure Get(sym: Integer);
          begin
          end;
          var G: procedure(var sym: Integer);
          begin
            G := @Get
          end.
          ''') <> '');
end;

initialization
  RegisterTest(TProcTypesTests);

end.
