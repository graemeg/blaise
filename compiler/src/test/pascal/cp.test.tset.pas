{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.tset;

{ IR unit tests for TSet<T>: Include/Exclude/Contains/Clear/Destroy and Grow.
  Uses Integer as the type parameter throughout. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TTSetTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    procedure TestSemantic_TSet_Instantiates;
    procedure TestSemantic_TSet_Include_Compiles;
    procedure TestSemantic_TSet_Exclude_Compiles;
    procedure TestSemantic_TSet_Contains_Compiles;
  end;

implementation

const
  SetDecl =
    '''
        type
          TSet<T> = class
            FData:     ^T;
            FCount:    Integer;
            FCapacity: Integer;
            procedure Grow;
            function  IndexOf(Value: T): Integer;
            procedure Include(Value: T);
            procedure Exclude(Value: T);
            function  Contains(Value: T): Boolean;
            procedure Clear;
            procedure Destroy;
            property Count: Integer read FCount;
          end;
        ''';

  SetImpls =
    '''
        procedure TSet<T>.Grow;
        var
          NewCap: Integer;
          OldCap: Integer;
        begin
          OldCap := Self.FCapacity;
          if OldCap = 0 then
            NewCap := 4
          else
            NewCap := OldCap * 2;
          Self.FData     := ReallocMem(Self.FData, NewCap * SizeOf(T));
          ZeroMem(Self.FData + OldCap * SizeOf(T), (NewCap - OldCap) * SizeOf(T));
          Self.FCapacity := NewCap
        end;
        function TSet<T>.IndexOf(Value: T): Integer;
        var
          I:   Integer;
          Ptr: ^T;
        begin
          Result := -1;
          I      := 0;
          while I < Self.FCount do
          begin
            Ptr := Self.FData + I * SizeOf(T);
            if Ptr^ = Value then
            begin
              Result := I;
              break
            end;
            I := I + 1
          end
        end;
        procedure TSet<T>.Include(Value: T);
        var
          Dest: ^T;
        begin
          if Self.IndexOf(Value) >= 0 then
            Exit;
          if Self.FCount = Self.FCapacity then
            Self.Grow();
          Dest        := Self.FData + Self.FCount * SizeOf(T);
          Dest^       := Value;
          Self.FCount := Self.FCount + 1
        end;
        procedure TSet<T>.Exclude(Value: T);
        var
          Idx: Integer;
          I:   Integer;
          Dst: ^T;
          Src: ^T;
        begin
          Idx := Self.IndexOf(Value);
          if Idx < 0 then
            Exit;
          I := Idx;
          while I < Self.FCount - 1 do
          begin
            Dst  := Self.FData + I * SizeOf(T);
            Src  := Self.FData + (I + 1) * SizeOf(T);
            Dst^ := Src^;
            I    := I + 1
          end;
          Self.FCount := Self.FCount - 1
        end;
        function TSet<T>.Contains(Value: T): Boolean;
        begin
          Result := Self.IndexOf(Value) >= 0
        end;
        procedure TSet<T>.Clear;
        begin
          Self.FCount := 0
        end;
        procedure TSet<T>.Destroy;
        begin
          FreeMem(Self.FData);
          Self.FData     := nil;
          Self.FCount    := 0;
          Self.FCapacity := 0
        end;
        ''';

  SrcCreate =
    'program P;' + #10 +
    SetDecl +
    SetImpls +
    '''
        var S: TSet<Integer>;
        begin
          S := TSet<Integer>.Create()
        end.
        ''';

  SrcInclude =
    'program P;' + #10 +
    SetDecl +
    SetImpls +
    '''
        var S: TSet<Integer>;
        begin
          S := TSet<Integer>.Create();
          S.Include(1);
          S.Include(2);
          S.Include(1)
        end.
        ''';

  SrcExclude =
    'program P;' + #10 +
    SetDecl +
    SetImpls +
    '''
        var S: TSet<Integer>;
        begin
          S := TSet<Integer>.Create();
          S.Include(5);
          S.Exclude(5)
        end.
        ''';

  SrcContains =
    'program P;' + #10 +
    SetDecl +
    SetImpls +
    '''
        var
          S: TSet<Integer>;
          B: Boolean;
        begin
          S := TSet<Integer>.Create();
          S.Include(42);
          B := S.Contains(42)
        end.
        ''';

function TTSetTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TTSetTests.TestSemantic_TSet_Instantiates;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcCreate);
  Prog.Free();
end;

procedure TTSetTests.TestSemantic_TSet_Include_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcInclude);
  Prog.Free();
end;

procedure TTSetTests.TestSemantic_TSet_Exclude_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcExclude);
  Prog.Free();
end;

procedure TTSetTests.TestSemantic_TSet_Contains_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcContains);
  Prog.Free();
end;

initialization
  RegisterTest(TTSetTests);

end.
