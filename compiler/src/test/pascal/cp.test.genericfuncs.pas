{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.genericfuncs;

{ Tests for standalone generic function monomorphization.
  Syntax: function Name<T>(Param: T): T — demand-driven instantiation on first call. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic, cp.test.harness;

type
  TGenericFuncTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
    function ProbeBody(const AAsm: string): string;
    procedure AssertProbeARC(const ASrc, ATarget: string; ABorrowed: Boolean);
  published
    { ------------------------------------------------------------------ }
    { Parser — generic function declarations                               }
    { ------------------------------------------------------------------ }
    procedure TestParse_GenericFunc_HasTypeParams;
    procedure TestParse_GenericFunc_TypeParamName;
    procedure TestParse_GenericFunc_TwoTypeParams;
    procedure TestParse_GenericFunc_ParamUsesTypeParam;
    procedure TestParse_GenericFunc_ReturnUsesTypeParam;

    { ------------------------------------------------------------------ }
    { Parser — generic function call sites                                 }
    { ------------------------------------------------------------------ }
    procedure TestParse_GenericFunc_CallSite_IsFuncCallExpr;
    procedure TestParse_GenericFunc_CallSite_Name;
    procedure TestParse_GenericFunc_CallSite_ArgCount;

    { ------------------------------------------------------------------ }
    { Semantic — instantiation on use                                      }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_GenericFunc_TemplateNotInstantiatedWithoutUse;
    procedure TestSemantic_GenericFunc_Usage_CreatesInstance;
    procedure TestSemantic_GenericFunc_ReturnType_IsInteger;
    procedure TestSemantic_GenericFunc_ParamType_IsInteger;

    { ------------------------------------------------------------------ }
    { Codegen — mangled names and emission                                 }
    { ------------------------------------------------------------------ }
    { Generic METHOD (method-level <T>) — monomorphised body + call site. }

    { ------------------------------------------------------------------ }
    { 'const' on a type-parameter param survives monomorphisation         }
    { ------------------------------------------------------------------ }
    procedure TestSemantic_GenericMethod_ConstParamFlagPreserved;
    procedure TestCodegen_GenericClass_ConstStringParam_NoKeyARC;
    procedure TestCodegen_GenericClass_ByValStringParam_HasARC;
  end;

implementation

{ ------------------------------------------------------------------ }
{ Source constants                                                     }
{ ------------------------------------------------------------------ }

const
  { Generic function declaration only — no usage }
  SrcGenericFuncDecl =
    '''
        program P;
        function Identity<T>(Val: T): T;
        begin
          Result := Val
        end;
        begin
        end.
        ''';

  { Two type params }
  SrcGenericFuncTwoParams =
    '''
        program P;
        function Swap<A, B>(X: A; Y: B): A;
        begin
          Result := X
        end;
        begin
        end.
        ''';

  { Usage — instantiates Identity<Integer> }
  SrcGenericFuncUsage =
    '''
        program P;
        function Identity<T>(Val: T): T;
        begin
          Result := Val
        end;
        var X: Integer;
        begin
          X := Identity<Integer>(42)
        end.
        ''';

  { Call-site source for parser test only (semantics not needed) }
  SrcGenericFuncCallSite =
    '''
        program P;
        function Identity<T>(Val: T): T;
        begin
          Result := Val
        end;
        var X: Integer;
        begin
          X := Identity<Integer>(42)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                             }
{ ------------------------------------------------------------------ }

function TGenericFuncTests.ParseSrc(const ASrc: string): TProgram;
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

function TGenericFuncTests.AnalyseSrc(const ASrc: string): TProgram;
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

{ The instantiated TBox<string>.Probe body, label to first return; '' when
  the body is missing. }
function TGenericFuncTests.ProbeBody(const AAsm: string): string;
var
  P, Q: Integer;
begin
  Result := '';
  P := Pos('TBox_string_Probe:', AAsm);
  if P < 0 then Exit;
  Result := Copy(AAsm, P, Length(AAsm) - P);
  Q := Pos(#9'ret', Result);
  if Q >= 0 then
    Result := Copy(Result, 0, Q);
end;

{ A borrowed (const) key takes no ARC in the Probe body; a by-value key is
  retained on entry. }
procedure TGenericFuncTests.AssertProbeARC(const ASrc, ATarget: string;
  ABorrowed: Boolean);
var
  Body: string;
begin
  Body := ProbeBody(GenAsm(ASrc, ATarget));
  AssertTrue(ATarget + ': instantiated Probe body emitted', Body <> '');
  if ABorrowed then
  begin
    AssertTrue(ATarget + ': const type-param string key is borrowed -- no _StringAddRef',
      Pos('_StringAddRef', Body) < 0);
    AssertTrue(ATarget + ': const type-param string key is borrowed -- no _StringRelease',
      Pos('_StringRelease', Body) < 0);
  end
  else
    AssertTrue(ATarget + ': by-value type-param string key still retains',
      Pos('_StringAddRef', Body) >= 0);
end;

{ ------------------------------------------------------------------ }
{ Parser — generic function declarations                               }
{ ------------------------------------------------------------------ }

procedure TGenericFuncTests.TestParse_GenericFunc_HasTypeParams;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcGenericFuncDecl);
  try
    AssertEquals('one proc decl', 1, Prog.Block.ProcDecls.Count);
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertNotNull('TypeParams not nil', MD.TypeParams);
  finally
    Prog.Free();
  end;
end;

procedure TGenericFuncTests.TestParse_GenericFunc_TypeParamName;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcGenericFuncDecl);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('one type param', 1, MD.TypeParams.Count);
    AssertEquals('param name T', 'T', MD.TypeParams[0]);
  finally
    Prog.Free();
  end;
end;

procedure TGenericFuncTests.TestParse_GenericFunc_TwoTypeParams;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcGenericFuncTwoParams);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertNotNull('TypeParams not nil', MD.TypeParams);
    AssertEquals('two type params', 2, MD.TypeParams.Count);
    AssertEquals('first param A', 'A', MD.TypeParams[0]);
    AssertEquals('second param B', 'B', MD.TypeParams[1]);
  finally
    Prog.Free();
  end;
end;

procedure TGenericFuncTests.TestParse_GenericFunc_ParamUsesTypeParam;
var
  Prog: TProgram;
  MD:   TMethodDecl;
  Par:  TMethodParam;
begin
  Prog := ParseSrc(SrcGenericFuncDecl);
  try
    MD  := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('one param', 1, MD.Params.Count);
    Par := TMethodParam(MD.Params[0]);
    AssertEquals('param name Val', 'Val', Par.ParamName);
    AssertEquals('param type T', 'T', Par.TypeName);
  finally
    Prog.Free();
  end;
end;

procedure TGenericFuncTests.TestParse_GenericFunc_ReturnUsesTypeParam;
var
  Prog: TProgram;
  MD:   TMethodDecl;
begin
  Prog := ParseSrc(SrcGenericFuncDecl);
  try
    MD := TMethodDecl(Prog.Block.ProcDecls[0]);
    AssertEquals('return type T', 'T', MD.ReturnTypeName);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Parser — generic function call sites                                 }
{ ------------------------------------------------------------------ }

procedure TGenericFuncTests.TestParse_GenericFunc_CallSite_IsFuncCallExpr;
var
  Prog:   TProgram;
  Assign: TAssignment;
begin
  Prog := ParseSrc(SrcGenericFuncCallSite);
  try
    AssertEquals('one stmt', 1, Prog.Block.Stmts.Count);
    AssertTrue('assign stmt', Prog.Block.Stmts[0] is TAssignment);
    Assign := TAssignment(Prog.Block.Stmts[0]);
    AssertTrue('rhs is TFuncCallExpr', Assign.Expr is TFuncCallExpr);
  finally
    Prog.Free();
  end;
end;

procedure TGenericFuncTests.TestParse_GenericFunc_CallSite_Name;
var
  Prog:   TProgram;
  Assign: TAssignment;
  FCall:  TFuncCallExpr;
begin
  Prog := ParseSrc(SrcGenericFuncCallSite);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    FCall  := TFuncCallExpr(Assign.Expr);
    AssertEquals('call name', 'Identity<Integer>', FCall.Name);
  finally
    Prog.Free();
  end;
end;

procedure TGenericFuncTests.TestParse_GenericFunc_CallSite_ArgCount;
var
  Prog:   TProgram;
  Assign: TAssignment;
  FCall:  TFuncCallExpr;
begin
  Prog := ParseSrc(SrcGenericFuncCallSite);
  try
    Assign := TAssignment(Prog.Block.Stmts[0]);
    FCall  := TFuncCallExpr(Assign.Expr);
    AssertEquals('one arg', 1, FCall.Args.Count);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic — instantiation on use                                      }
{ ------------------------------------------------------------------ }

procedure TGenericFuncTests.TestSemantic_GenericFunc_TemplateNotInstantiatedWithoutUse;
var
  Prog: TProgram;
begin
  { Declaration without use: no instance created }
  Prog := AnalyseSrc(SrcGenericFuncDecl);
  try
    AssertEquals('no instances', 0, Prog.GenericFuncInstances.Count);
  finally
    Prog.Free();
  end;
end;

procedure TGenericFuncTests.TestSemantic_GenericFunc_Usage_CreatesInstance;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcGenericFuncUsage);
  try
    AssertEquals('one instance', 1, Prog.GenericFuncInstances.Count);
  finally
    Prog.Free();
  end;
end;

procedure TGenericFuncTests.TestSemantic_GenericFunc_ReturnType_IsInteger;
var
  Prog: TProgram;
  GFI:  TGenericFuncInstance;
begin
  Prog := AnalyseSrc(SrcGenericFuncUsage);
  try
    GFI := TGenericFuncInstance(Prog.GenericFuncInstances[0]);
    AssertNotNull('return type not nil', GFI.MethodDecl.ResolvedReturnType);
    AssertEquals('return type is Integer', Ord(tyInteger),
      Ord(GFI.MethodDecl.ResolvedReturnType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TGenericFuncTests.TestSemantic_GenericFunc_ParamType_IsInteger;
var
  Prog: TProgram;
  GFI:  TGenericFuncInstance;
  Par:  TMethodParam;
begin
  Prog := AnalyseSrc(SrcGenericFuncUsage);
  try
    GFI := TGenericFuncInstance(Prog.GenericFuncInstances[0]);
    AssertEquals('one param', 1, GFI.MethodDecl.Params.Count);
    Par := TMethodParam(GFI.MethodDecl.Params[0]);
    AssertNotNull('param type not nil', Par.ResolvedType);
    AssertEquals('param type is Integer', Ord(tyInteger), Ord(Par.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Codegen — mangled names and emission                                 }
{ ------------------------------------------------------------------ }

const
{ ------------------------------------------------------------------------ }
{ 'const' on a type-parameter param must survive monomorphisation.          }
{                                                                            }
{ The generic-instantiation paths hand-build each TMethodParam and copied    }
{ only ParamName/IsVarParam/TypeName, silently dropping IsConstParam.  So    }
{ `const AKey: K` monomorphised to string was treated as a BY-VALUE string   }
{ param and got the callee AddRef(entry)/Release(exit) pair, while a         }
{ concrete `const AKey: string` correctly borrowed.                          }
{                                                                            }
{ For a refcount-0 transient argument (a fresh concat/Format result) that    }
{ pair is AddRef(0->1) then Release(1->0) = FREE, freeing the string out     }
{ from under a caller that still owns it — the macOS/arm64 round-34          }
{ TDictionary key over-release, though the defect is backend-agnostic.       }
{ ------------------------------------------------------------------------ }

const
  SrcGenericConstParam =
    'program P;'#10 +
    'type'#10 +
    '  TBox<K> = record'#10 +
    '    function Probe(const AKey: K): Boolean;'#10 +
    '  end;'#10 +
    'function TBox<K>.Probe(const AKey: K): Boolean;'#10 +
    'begin'#10 +
    '  Result := True;'#10 +
    'end;'#10 +
    'var b: TBox<string>; r: Boolean; s: string;'#10 +
    'begin'#10 +
    '  s := ''x'';'#10 +
    '  r := b.Probe(s);'#10 +
    'end.';

  { Class form of the same shape — generic CLASS instances are recorded in
    TProgram.GenericInstances, which is what the semantic assertion walks. }
  SrcGenericConstParamClass =
    'program P;'#10 +
    'type'#10 +
    '  TBox<K> = class'#10 +
    '    function Probe(const AKey: K): Boolean;'#10 +
    '  end;'#10 +
    'function TBox<K>.Probe(const AKey: K): Boolean;'#10 +
    'begin'#10 +
    '  Result := True;'#10 +
    'end;'#10 +
    'var b: TBox<string>; r: Boolean; s: string;'#10 +
    'begin'#10 +
    '  s := ''x'';'#10 +
    '  b := TBox<string>.Create();'#10 +
    '  r := b.Probe(s);'#10 +
    'end.';

  SrcGenericByValParam =
    'program P;'#10 +
    'type'#10 +
    '  TBox<K> = record'#10 +
    '    function Probe(AKey: K): Boolean;'#10 +
    '  end;'#10 +
    'function TBox<K>.Probe(AKey: K): Boolean;'#10 +
    'begin'#10 +
    '  Result := True;'#10 +
    'end;'#10 +
    'var b: TBox<string>; r: Boolean; s: string;'#10 +
    'begin'#10 +
    '  s := ''x'';'#10 +
    '  r := b.Probe(s);'#10 +
    'end.';

{ The flag itself must reach the instantiated decl — asserted at the AST
  level so a failure points at the semantic pass, not at any one backend. }
procedure TGenericFuncTests.TestSemantic_GenericMethod_ConstParamFlagPreserved;
var
  Prog: TProgram;
  I, J: Integer;
  GI: TGenericInstance;
  MD: TMethodDecl;
  Found: Boolean;
begin
  Prog := AnalyseSrc(SrcGenericConstParamClass);
  try
    Found := False;
    for I := 0 to Prog.GenericInstances.Count - 1 do
    begin
      GI := TGenericInstance(Prog.GenericInstances.Items[I]);
      if GI.ClassDef = nil then
        Continue;
      for J := 0 to GI.ClassDef.Methods.Count - 1 do
      begin
        MD := TMethodDecl(GI.ClassDef.Methods.Items[J]);
        if not SameText(MD.Name, 'Probe') then
          Continue;
        if MD.Params.Count < 1 then
          Continue;
        Found := True;
        AssertTrue('const survives monomorphisation of ''const AKey: K''',
          TMethodParam(MD.Params.Items[0]).IsConstParam);
      end;
    end;
    AssertTrue('instantiated TBox<string>.Probe was found', Found);
  finally
    Prog.Free();
  end;
end;

{ A `const` type-param string borrows: no callee-side ARC on the key. }
procedure TGenericFuncTests.TestCodegen_GenericClass_ConstStringParam_NoKeyARC;
begin
  AssertProbeARC(SrcGenericConstParam, TargetX86_64, True);
  AssertProbeARC(SrcGenericConstParam, TargetArm64, True);
end;

{ Control: WITHOUT const the by-value copy still retains/releases, so the
  test above is pinning `const`, not the absence of string-param ARC. }
procedure TGenericFuncTests.TestCodegen_GenericClass_ByValStringParam_HasARC;
begin
  AssertProbeARC(SrcGenericByValParam, TargetX86_64, False);
  AssertProbeARC(SrcGenericByValParam, TargetArm64, False);
end;

initialization
  RegisterTest(TGenericFuncTests);
end.
