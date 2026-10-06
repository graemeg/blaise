{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.tordereddictionary;

{ IR unit tests for TOrderedDictionary<K,V>: insertion-ordered map.
  Verifies Add/TryGetValue/ContainsKey/Remove/GetKey/GetValue codegen.
  Uses Integer keys and Integer values throughout. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TTOrderedDictionaryTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    procedure TestSemantic_OrdDict_Instantiates;
    procedure TestSemantic_OrdDict_Add_ContainsKey_Compiles;
    procedure TestSemantic_OrdDict_TryGetValue_Compiles;
    procedure TestSemantic_OrdDict_Remove_Compiles;
    procedure TestSemantic_OrdDict_IndexedAccess_Compiles;
  end;

implementation

const
  OrdDictDecl =
    '''
        type
          TOrderedDictionary<K, V> = class
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
            function  GetKey(AIndex: Integer): K;
            function  GetValue(AIndex: Integer): V;
            procedure Destroy;
            property Count: Integer read FCount;
            property Keys[Index: Integer]: K read GetKey;
            property Values[Index: Integer]: V read GetValue;
          end;
        ''';

  OrdDictImpls =
    '''
        procedure TOrderedDictionary<K, V>.Grow;
        var
          NewCap: Integer;
          OldCap: Integer;
        begin
          OldCap := Self.FCapacity;
          if OldCap = 0 then
            NewCap := 8
          else
            NewCap := OldCap * 2;
          Self.FKeys     := ReallocMem(Self.FKeys,   NewCap * SizeOf(K));
          ZeroMem(Self.FKeys + OldCap * SizeOf(K), (NewCap - OldCap) * SizeOf(K));
          Self.FValues   := ReallocMem(Self.FValues, NewCap * SizeOf(V));
          ZeroMem(Self.FValues + OldCap * SizeOf(V), (NewCap - OldCap) * SizeOf(V));
          Self.FCapacity := NewCap
        end;
        function TOrderedDictionary<K, V>.FindKey(Key: K): Integer;
        var
          I:   Integer;
          Ptr: ^K;
        begin
          Result := -1;
          I      := 0;
          while I < Self.FCount do
          begin
            Ptr := Self.FKeys + I * SizeOf(K);
            if Ptr^ = Key then
            begin
              Result := I;
              break
            end;
            I := I + 1
          end
        end;
        procedure TOrderedDictionary<K, V>.Add(Key: K; Value: V);
        var
          Idx:  Integer;
          KPtr: ^K;
          VPtr: ^V;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then
          begin
            VPtr  := Self.FValues + Idx * SizeOf(V);
            VPtr^ := Value
          end
          else
          begin
            if Self.FCount = Self.FCapacity then
              Self.Grow();
            KPtr  := Self.FKeys   + Self.FCount * SizeOf(K);
            VPtr  := Self.FValues + Self.FCount * SizeOf(V);
            KPtr^ := Key;
            VPtr^ := Value;
            Self.FCount := Self.FCount + 1
          end
        end;
        function TOrderedDictionary<K, V>.TryGetValue(Key: K; var Value: V): Boolean;
        var
          Idx:  Integer;
          VPtr: ^V;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then
          begin
            VPtr   := Self.FValues + Idx * SizeOf(V);
            Value  := VPtr^;
            Result := True
          end
          else
            Result := False
        end;
        function TOrderedDictionary<K, V>.ContainsKey(Key: K): Boolean;
        begin
          Result := Self.FindKey(Key) >= 0
        end;
        procedure TOrderedDictionary<K, V>.Remove(Key: K);
        var
          Idx:  Integer;
          I:    Integer;
          KDst: ^K;
          KSrc: ^K;
          VDst: ^V;
          VSrc: ^V;
        begin
          Idx := Self.FindKey(Key);
          if Idx >= 0 then
          begin
            I := Idx;
            while I < Self.FCount - 1 do
            begin
              KDst  := Self.FKeys   + I * SizeOf(K);
              KSrc  := Self.FKeys   + (I + 1) * SizeOf(K);
              VDst  := Self.FValues + I * SizeOf(V);
              VSrc  := Self.FValues + (I + 1) * SizeOf(V);
              KDst^ := KSrc^;
              VDst^ := VSrc^;
              I     := I + 1
            end;
            Self.FCount := Self.FCount - 1
          end
        end;
        function TOrderedDictionary<K, V>.GetKey(AIndex: Integer): K;
        var
          Ptr: ^K;
        begin
          Ptr    := Self.FKeys + AIndex * SizeOf(K);
          Result := Ptr^
        end;
        function TOrderedDictionary<K, V>.GetValue(AIndex: Integer): V;
        var
          Ptr: ^V;
        begin
          Ptr    := Self.FValues + AIndex * SizeOf(V);
          Result := Ptr^
        end;
        procedure TOrderedDictionary<K, V>.Destroy;
        begin
          FreeMem(Self.FKeys);
          FreeMem(Self.FValues);
          Self.FKeys     := nil;
          Self.FValues   := nil;
          Self.FCount    := 0;
          Self.FCapacity := 0
        end;
        ''';

  SrcCreate =
    'program P;' + #10 +
    OrdDictDecl +
    OrdDictImpls +
    '''
        var D: TOrderedDictionary<Integer, Integer>;
        begin
          D := TOrderedDictionary<Integer, Integer>.Create()
        end.
        ''';

  SrcAddGet =
    'program P;' + #10 +
    OrdDictDecl +
    OrdDictImpls +
    '''
        var
          D:  TOrderedDictionary<Integer, Integer>;
          OK: Boolean;
        begin
          D := TOrderedDictionary<Integer, Integer>.Create();
          D.Add(1, 100);
          D.Add(2, 200);
          OK := D.ContainsKey(1)
        end.
        ''';

  SrcTryGet =
    'program P;' + #10 +
    OrdDictDecl +
    OrdDictImpls +
    '''
        var
          D:  TOrderedDictionary<Integer, Integer>;
          V:  Integer;
          OK: Boolean;
        begin
          D := TOrderedDictionary<Integer, Integer>.Create();
          D.Add(42, 99);
          OK := D.TryGetValue(42, V)
        end.
        ''';

  SrcRemove =
    'program P;' + #10 +
    OrdDictDecl +
    OrdDictImpls +
    '''
        var
          D:  TOrderedDictionary<Integer, Integer>;
          OK: Boolean;
        begin
          D := TOrderedDictionary<Integer, Integer>.Create();
          D.Add(7, 70);
          D.Remove(7);
          OK := D.ContainsKey(7)
        end.
        ''';

  SrcIndexed =
    'program P;' + #10 +
    OrdDictDecl +
    OrdDictImpls +
    '''
        var
          D: TOrderedDictionary<Integer, Integer>;
          K: Integer;
          V: Integer;
        begin
          D := TOrderedDictionary<Integer, Integer>.Create();
          D.Add(5, 50);
          K := D.Keys[0];
          V := D.Values[0]
        end.
        ''';

function TTOrderedDictionaryTests.AnalyseSrc(const ASrc: string): TProgram;
var
  Lex: TLexer;
  Par: TParser;
  SA:  TSemanticAnalyser;
begin
  Lex    := TLexer.Create(ASrc);
  Par    := TParser.Create(Lex);
  Result := Par.Parse();
  Par.Free();
  Lex.Free();
  SA := TSemanticAnalyser.Create();
  try
    SA.Analyse(Result);
  finally
    SA.Free();
  end;
end;

procedure TTOrderedDictionaryTests.TestSemantic_OrdDict_Instantiates;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcCreate);
  Prog.Free();
end;

procedure TTOrderedDictionaryTests.TestSemantic_OrdDict_Add_ContainsKey_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcAddGet);
  Prog.Free();
end;

procedure TTOrderedDictionaryTests.TestSemantic_OrdDict_TryGetValue_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcTryGet);
  Prog.Free();
end;

procedure TTOrderedDictionaryTests.TestSemantic_OrdDict_Remove_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcRemove);
  Prog.Free();
end;

procedure TTOrderedDictionaryTests.TestSemantic_OrdDict_IndexedAccess_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcIndexed);
  Prog.Free();
end;

initialization
  RegisterTest(TTOrderedDictionaryTests);

end.
