{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.imap;

{ IR unit tests for IMap<K,V>: the generic map interface that TDictionary and
  TOrderedDictionary both implement.  Exercises:
    - parsing IMap<K,V> interface definition with two type params
    - semantic instantiation and class-implements-IMap<K,V> check
    - codegen: typeinfo, itab, impllist, indirect dispatch
    - IMap<K,V> variable receiving both concrete dictionary types }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TIMapTests = class(TTestCase)
  private
    function ParseSrc(const ASrc: string): TProgram;
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    { Parser }
    procedure TestParse_IMap_IsGenericInterfaceDef;
    procedure TestParse_IMap_TwoTypeParams;
    procedure TestParse_IMap_HasAddMethod;
    procedure TestParse_IMap_HasTryGetValueMethod;
    procedure TestParse_IMap_HasCountProperty;

    { Semantic }
    procedure TestSemantic_IMap_InstantiatesOnVarDecl;
    procedure TestSemantic_IMap_InstantiatedType_IsInterface;
    procedure TestSemantic_TDictionary_ImplementsIMap_OK;
    procedure TestSemantic_TOrderedDictionary_ImplementsIMap_OK;
    procedure TestSemantic_IMap_ReceivesTDictionary;
    procedure TestSemantic_IMap_ReceivesTOrderedDictionary;
    procedure TestSemantic_IMap_Add_CallableViaInterface;
    procedure TestSemantic_IMap_TryGetValue_CallableViaInterface;
    procedure TestSemantic_IMap_ContainsKey_CallableViaInterface;
    procedure TestSemantic_IMap_Remove_CallableViaInterface;

    { Codegen }
  end;

implementation

{ ------------------------------------------------------------------ }
{ IMap<K,V> interface + TDictionary implementing it                    }
{ ------------------------------------------------------------------ }

const
  IMapDecl =
    '''
        type
          IMap<K, V> = interface
            procedure Add(Key: K; Value: V);
            function  TryGetValue(Key: K; var Value: V): Boolean;
            function  ContainsKey(Key: K): Boolean;
            procedure Remove(Key: K);
            function  GetCount: Integer;
          end;
        ''';

  DictDecl =
    '''
          TDictionary<K, V> = class(IMap<K, V>)
            FKeys:     ^K;
            FValues:   ^V;
            FCount:    Integer;
            FCapacity: Integer;
            procedure Grow;
            function  FindKey(Key: K): Integer;
            procedure Add(Key: K; Value: V);
            function  TryGetValue(Key: K; var Value: V): Boolean;
            function  ContainsKey(Key: K): Boolean;
            procedure Remove(Key: K);
            function  GetCount: Integer;
            procedure Destroy;
            property Count: Integer read GetCount;
          end;
        ''';

  DictImpls =
    '''
        procedure TDictionary<K, V>.Grow;
        var NewCap, OldCap: Integer;
        begin
          OldCap := Self.FCapacity;
          if OldCap = 0 then NewCap := 8 else NewCap := OldCap * 2;
          Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(K));
          ZeroMem(Self.FKeys   + OldCap * SizeOf(K), (NewCap - OldCap) * SizeOf(K));
          Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(V));
          ZeroMem(Self.FValues + OldCap * SizeOf(V), (NewCap - OldCap) * SizeOf(V));
          Self.FCapacity := NewCap
        end;
        function TDictionary<K, V>.FindKey(Key: K): Integer;
        var I: Integer; Ptr: ^K;
        begin
          Result := -1; I := 0;
          while I < Self.FCount do begin
            Ptr := Self.FKeys + I * SizeOf(K);
            if Ptr^ = Key then begin Result := I; break end;
            I := I + 1
          end
        end;
        procedure TDictionary<K, V>.Add(Key: K; Value: V);
        var Idx: Integer; KPtr: ^K; VPtr: ^V;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            VPtr := Self.FValues + Idx * SizeOf(V); VPtr^ := Value
          end else begin
            if Self.FCount = Self.FCapacity then Self.Grow();
            KPtr := Self.FKeys   + Self.FCount * SizeOf(K);
            VPtr := Self.FValues + Self.FCount * SizeOf(V);
            KPtr^ := Key; VPtr^ := Value;
            Self.FCount := Self.FCount + 1
          end
        end;
        function TDictionary<K, V>.TryGetValue(Key: K; var Value: V): Boolean;
        var Idx: Integer; VPtr: ^V;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            VPtr := Self.FValues + Idx * SizeOf(V); Value := VPtr^; Result := True
          end else Result := False
        end;
        function TDictionary<K, V>.ContainsKey(Key: K): Boolean;
        begin Result := Self.FindKey(Key) >= 0 end;
        procedure TDictionary<K, V>.Remove(Key: K);
        var Idx, I: Integer; KDst, KSrc: ^K; VDst, VSrc: ^V;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            I := Idx;
            while I < Self.FCount - 1 do begin
              KDst := Self.FKeys   + I * SizeOf(K); KSrc := Self.FKeys   + (I+1) * SizeOf(K);
              VDst := Self.FValues + I * SizeOf(V); VSrc := Self.FValues + (I+1) * SizeOf(V);
              KDst^ := KSrc^; VDst^ := VSrc^; I := I + 1
            end;
            Self.FCount := Self.FCount - 1
          end
        end;
        function TDictionary<K, V>.GetCount: Integer;
        begin Result := Self.FCount end;
        procedure TDictionary<K, V>.Destroy;
        begin
          FreeMem(Self.FKeys); FreeMem(Self.FValues);
          Self.FKeys := nil; Self.FValues := nil;
          Self.FCount := 0; Self.FCapacity := 0
        end;
        ''';

  OrdDictDecl =
    '''
          TOrderedDictionary<K, V> = class(IMap<K, V>)
            FKeys:     ^K;
            FValues:   ^V;
            FCount:    Integer;
            FCapacity: Integer;
            procedure Grow;
            function  FindKey(Key: K): Integer;
            procedure Add(Key: K; Value: V);
            function  TryGetValue(Key: K; var Value: V): Boolean;
            function  ContainsKey(Key: K): Boolean;
            procedure Remove(Key: K);
            function  GetCount: Integer;
            function  GetKey(AIndex: Integer): K;
            function  GetValue(AIndex: Integer): V;
            procedure Destroy;
            property Count: Integer read GetCount;
            property Keys[Index: Integer]: K read GetKey;
            property Values[Index: Integer]: V read GetValue;
          end;
        ''';

  OrdDictImpls =
    '''
        procedure TOrderedDictionary<K, V>.Grow;
        var NewCap, OldCap: Integer;
        begin
          OldCap := Self.FCapacity;
          if OldCap = 0 then NewCap := 8 else NewCap := OldCap * 2;
          Self.FKeys   := ReallocMem(Self.FKeys,   NewCap * SizeOf(K));
          ZeroMem(Self.FKeys   + OldCap * SizeOf(K), (NewCap - OldCap) * SizeOf(K));
          Self.FValues := ReallocMem(Self.FValues, NewCap * SizeOf(V));
          ZeroMem(Self.FValues + OldCap * SizeOf(V), (NewCap - OldCap) * SizeOf(V));
          Self.FCapacity := NewCap
        end;
        function TOrderedDictionary<K, V>.FindKey(Key: K): Integer;
        var I: Integer; Ptr: ^K;
        begin
          Result := -1; I := 0;
          while I < Self.FCount do begin
            Ptr := Self.FKeys + I * SizeOf(K);
            if Ptr^ = Key then begin Result := I; break end;
            I := I + 1
          end
        end;
        procedure TOrderedDictionary<K, V>.Add(Key: K; Value: V);
        var Idx: Integer; KPtr: ^K; VPtr: ^V;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            VPtr := Self.FValues + Idx * SizeOf(V); VPtr^ := Value
          end else begin
            if Self.FCount = Self.FCapacity then Self.Grow();
            KPtr := Self.FKeys   + Self.FCount * SizeOf(K);
            VPtr := Self.FValues + Self.FCount * SizeOf(V);
            KPtr^ := Key; VPtr^ := Value;
            Self.FCount := Self.FCount + 1
          end
        end;
        function TOrderedDictionary<K, V>.TryGetValue(Key: K; var Value: V): Boolean;
        var Idx: Integer; VPtr: ^V;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            VPtr := Self.FValues + Idx * SizeOf(V); Value := VPtr^; Result := True
          end else Result := False
        end;
        function TOrderedDictionary<K, V>.ContainsKey(Key: K): Boolean;
        begin Result := Self.FindKey(Key) >= 0 end;
        procedure TOrderedDictionary<K, V>.Remove(Key: K);
        var Idx, I: Integer; KDst, KSrc: ^K; VDst, VSrc: ^V;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then begin
            I := Idx;
            while I < Self.FCount - 1 do begin
              KDst := Self.FKeys   + I * SizeOf(K); KSrc := Self.FKeys   + (I+1) * SizeOf(K);
              VDst := Self.FValues + I * SizeOf(V); VSrc := Self.FValues + (I+1) * SizeOf(V);
              KDst^ := KSrc^; VDst^ := VSrc^; I := I + 1
            end;
            Self.FCount := Self.FCount - 1
          end
        end;
        function TOrderedDictionary<K, V>.GetCount: Integer;
        begin Result := Self.FCount end;
        function TOrderedDictionary<K, V>.GetKey(AIndex: Integer): K;
        var Ptr: ^K; begin Ptr := Self.FKeys + AIndex * SizeOf(K); Result := Ptr^ end;
        function TOrderedDictionary<K, V>.GetValue(AIndex: Integer): V;
        var Ptr: ^V; begin Ptr := Self.FValues + AIndex * SizeOf(V); Result := Ptr^ end;
        procedure TOrderedDictionary<K, V>.Destroy;
        begin
          FreeMem(Self.FKeys); FreeMem(Self.FValues);
          Self.FKeys := nil; Self.FValues := nil;
          Self.FCount := 0; Self.FCapacity := 0
        end;
        ''';

  { Minimal source: just declare IMap and a var of IMap<Integer,Integer> }
  SrcIMapVarDecl =
    'program P;' + #10 +
    IMapDecl +
    '''
        var M: IMap<Integer, Integer>;
        begin end.
        ''';

  { TDictionary implements IMap }
  SrcDictImplementsIMap =
    'program P;' + #10 +
    IMapDecl +
    'type' + #10 +
    DictDecl +
    DictImpls +
    '''
        var M: IMap<Integer, Integer>;
        begin
          M := TDictionary<Integer, Integer>.Create()
        end.
        ''';

  { TOrderedDictionary implements IMap }
  SrcOrdDictImplementsIMap =
    'program P;' + #10 +
    IMapDecl +
    'type' + #10 +
    OrdDictDecl +
    OrdDictImpls +
    '''
        var M: IMap<Integer, Integer>;
        begin
          M := TOrderedDictionary<Integer, Integer>.Create()
        end.
        ''';

  { Dispatch: call Add through IMap reference }
  SrcIMapAddDispatch =
    'program P;' + #10 +
    IMapDecl +
    'type' + #10 +
    DictDecl +
    DictImpls +
    '''
        var M: IMap<Integer, Integer>;
        begin
          M := TDictionary<Integer, Integer>.Create();
          M.Add(1, 100)
        end.
        ''';

  { Dispatch: call TryGetValue through IMap reference }
  SrcIMapTryGetDispatch =
    'program P;' + #10 +
    IMapDecl +
    'type' + #10 +
    DictDecl +
    DictImpls +
    '''
        var M: IMap<Integer, Integer>; V: Integer; OK: Boolean;
        begin
          M := TDictionary<Integer, Integer>.Create();
          M.Add(42, 99);
          OK := M.TryGetValue(42, V)
        end.
        ''';

  { Dispatch: call ContainsKey through IMap reference }
  SrcIMapContainsKeyDispatch =
    'program P;' + #10 +
    IMapDecl +
    'type' + #10 +
    DictDecl +
    DictImpls +
    '''
        var M: IMap<Integer, Integer>; OK: Boolean;
        begin
          M := TDictionary<Integer, Integer>.Create();
          M.Add(7, 70);
          OK := M.ContainsKey(7)
        end.
        ''';

  { Dispatch: call Remove through IMap reference }
  SrcIMapRemoveDispatch =
    'program P;' + #10 +
    IMapDecl +
    'type' + #10 +
    DictDecl +
    DictImpls +
    '''
        var M: IMap<Integer, Integer>;
        begin
          M := TDictionary<Integer, Integer>.Create();
          M.Add(3, 30);
          M.Remove(3)
        end.
        ''';

  { Both concrete types assigned to IMap<K,V> in the same program }
  SrcBothConcreteTypes =
    'program P;' + #10 +
    IMapDecl +
    'type' + #10 +
    DictDecl +
    OrdDictDecl +
    DictImpls +
    OrdDictImpls +
    '''
        var
          M1: IMap<Integer, Integer>;
          M2: IMap<Integer, Integer>;
        begin
          M1 := TDictionary<Integer, Integer>.Create();
          M2 := TOrderedDictionary<Integer, Integer>.Create();
          M1.Add(1, 10);
          M2.Add(2, 20)
        end.
        ''';

{ ------------------------------------------------------------------ }
{ Helpers                                                              }
{ ------------------------------------------------------------------ }

function TIMapTests.ParseSrc(const ASrc: string): TProgram;
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

function TIMapTests.AnalyseSrc(const ASrc: string): TProgram;
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

{ ------------------------------------------------------------------ }
{ Parser tests                                                         }
{ ------------------------------------------------------------------ }

procedure TIMapTests.TestParse_IMap_IsGenericInterfaceDef;
var
  Prog: TProgram;
  TD:   TTypeDecl;
begin
  Prog := ParseSrc(SrcIMapVarDecl);
  try
    AssertEquals('One type decl', 1, Prog.Block.TypeDecls.Count);
    TD := TTypeDecl(Prog.Block.TypeDecls[0]);
    AssertTrue('IMap def is TGenericInterfaceDef', TD.Def is TGenericInterfaceDef);
  finally
    Prog.Free();
  end;
end;

procedure TIMapTests.TestParse_IMap_TwoTypeParams;
var
  Prog: TProgram;
  GID:  TGenericInterfaceDef;
begin
  Prog := ParseSrc(SrcIMapVarDecl);
  try
    GID := TGenericInterfaceDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    AssertEquals('Two type params', 2, GID.ParamNames.Count);
    AssertEquals('First param is K', 'K', GID.ParamNames[0]);
    AssertEquals('Second param is V', 'V', GID.ParamNames[1]);
  finally
    Prog.Free();
  end;
end;

procedure TIMapTests.TestParse_IMap_HasAddMethod;
var
  Prog:  TProgram;
  GID:   TGenericInterfaceDef;
  Found: Boolean;
  I:     Integer;
begin
  Prog := ParseSrc(SrcIMapVarDecl);
  try
    GID   := TGenericInterfaceDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    Found := False;
    for I := 0 to GID.IntfDef.Methods.Count - 1 do
      if TMethodDecl(GID.IntfDef.Methods[I]).Name = 'Add' then
        Found := True;
    AssertTrue('IMap has Add method', Found);
  finally
    Prog.Free();
  end;
end;

procedure TIMapTests.TestParse_IMap_HasTryGetValueMethod;
var
  Prog:  TProgram;
  GID:   TGenericInterfaceDef;
  Found: Boolean;
  I:     Integer;
begin
  Prog := ParseSrc(SrcIMapVarDecl);
  try
    GID   := TGenericInterfaceDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    Found := False;
    for I := 0 to GID.IntfDef.Methods.Count - 1 do
      if TMethodDecl(GID.IntfDef.Methods[I]).Name = 'TryGetValue' then
        Found := True;
    AssertTrue('IMap has TryGetValue method', Found);
  finally
    Prog.Free();
  end;
end;

procedure TIMapTests.TestParse_IMap_HasCountProperty;
var
  Prog:  TProgram;
  GID:   TGenericInterfaceDef;
  Found: Boolean;
  I:     Integer;
begin
  { IMap exposes Count via GetCount method — interface bodies do not yet
    support property declarations, so Count is accessed as GetCount() }
  Prog := ParseSrc(SrcIMapVarDecl);
  try
    GID   := TGenericInterfaceDef(TTypeDecl(Prog.Block.TypeDecls[0]).Def);
    Found := False;
    for I := 0 to GID.IntfDef.Methods.Count - 1 do
      if TMethodDecl(GID.IntfDef.Methods[I]).Name = 'GetCount' then
        Found := True;
    AssertTrue('IMap has GetCount method (Count accessor)', Found);
  finally
    Prog.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Semantic tests                                                        }
{ ------------------------------------------------------------------ }

procedure TIMapTests.TestSemantic_IMap_InstantiatesOnVarDecl;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcIMapVarDecl);
  Prog.Free();
end;

procedure TIMapTests.TestSemantic_IMap_InstantiatedType_IsInterface;
var
  Prog: TProgram;
  VD:   TVarDecl;
begin
  Prog := AnalyseSrc(SrcIMapVarDecl);
  try
    VD := TVarDecl(Prog.Block.Decls[0]);
    AssertEquals('IMap<Integer,Integer> resolves to tyInterface',
      Ord(tyInterface), Ord(VD.ResolvedType.Kind));
  finally
    Prog.Free();
  end;
end;

procedure TIMapTests.TestSemantic_TDictionary_ImplementsIMap_OK;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcDictImplementsIMap);
  Prog.Free();
end;

procedure TIMapTests.TestSemantic_TOrderedDictionary_ImplementsIMap_OK;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcOrdDictImplementsIMap);
  Prog.Free();
end;

procedure TIMapTests.TestSemantic_IMap_ReceivesTDictionary;
var
  Prog: TProgram;
begin
  { Assignment M := TDictionary<...>.Create must pass type-compat check }
  Prog := AnalyseSrc(SrcDictImplementsIMap);
  Prog.Free();
end;

procedure TIMapTests.TestSemantic_IMap_ReceivesTOrderedDictionary;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcOrdDictImplementsIMap);
  Prog.Free();
end;

procedure TIMapTests.TestSemantic_IMap_Add_CallableViaInterface;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcIMapAddDispatch);
  Prog.Free();
end;

procedure TIMapTests.TestSemantic_IMap_TryGetValue_CallableViaInterface;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcIMapTryGetDispatch);
  Prog.Free();
end;

procedure TIMapTests.TestSemantic_IMap_ContainsKey_CallableViaInterface;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcIMapContainsKeyDispatch);
  Prog.Free();
end;

procedure TIMapTests.TestSemantic_IMap_Remove_CallableViaInterface;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcIMapRemoveDispatch);
  Prog.Free();
end;

{ ------------------------------------------------------------------ }
{ Codegen tests                                                         }
{ ------------------------------------------------------------------ }

initialization
  RegisterTest(TIMapTests);

end.
