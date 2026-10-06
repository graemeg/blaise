{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.tstack;

{ IR unit tests for TStack<T>: Push/Pop/Peek/Clear/Destroy and Grow.
  Uses Integer as the type parameter throughout. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TTStackTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    procedure TestSemantic_TStack_Instantiates;
    procedure TestSemantic_TStack_Push_Compiles;
    procedure TestSemantic_TStack_Pop_Compiles;
    procedure TestSemantic_TStack_Peek_Compiles;
  end;

implementation

const
  StackDecl =
    '''
        type
          TStack<T> = class
            FData:     ^T;
            FCount:    Integer;
            FCapacity: Integer;
            procedure Grow;
            procedure Push(Value: T);
            function  Pop: T;
            function  Peek: T;
            procedure Clear;
            procedure Destroy;
            property Count: Integer read FCount;
          end;
        ''';

  StackImpls =
    '''
        procedure TStack<T>.Grow;
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
        procedure TStack<T>.Push(Value: T);
        var
          Dest: ^T;
        begin
          if Self.FCount = Self.FCapacity then
            Self.Grow();
          Dest        := Self.FData + Self.FCount * SizeOf(T);
          Dest^       := Value;
          Self.FCount := Self.FCount + 1
        end;
        function TStack<T>.Pop: T;
        var
          Src: ^T;
        begin
          Self.FCount := Self.FCount - 1;
          Src         := Self.FData + Self.FCount * SizeOf(T);
          Result      := Src^
        end;
        function TStack<T>.Peek: T;
        var
          Src: ^T;
        begin
          Src    := Self.FData + (Self.FCount - 1) * SizeOf(T);
          Result := Src^
        end;
        procedure TStack<T>.Clear;
        begin
          Self.FCount := 0
        end;
        procedure TStack<T>.Destroy;
        begin
          FreeMem(Self.FData);
          Self.FData     := nil;
          Self.FCount    := 0;
          Self.FCapacity := 0
        end;
        ''';

  SrcCreate =
    'program P;' + #10 +
    StackDecl +
    StackImpls +
    '''
        var S: TStack<Integer>;
        begin
          S := TStack<Integer>.Create()
        end.
        ''';

  SrcPush =
    'program P;' + #10 +
    StackDecl +
    StackImpls +
    '''
        var S: TStack<Integer>;
        begin
          S := TStack<Integer>.Create();
          S.Push(10);
          S.Push(20)
        end.
        ''';

  SrcPop =
    'program P;' + #10 +
    StackDecl +
    StackImpls +
    '''
        var
          S: TStack<Integer>;
          V: Integer;
        begin
          S := TStack<Integer>.Create();
          S.Push(42);
          V := S.Pop()
        end.
        ''';

  SrcPeek =
    'program P;' + #10 +
    StackDecl +
    StackImpls +
    '''
        var
          S: TStack<Integer>;
          V: Integer;
        begin
          S := TStack<Integer>.Create();
          S.Push(7);
          V := S.Peek()
        end.
        ''';

function TTStackTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TTStackTests.TestSemantic_TStack_Instantiates;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcCreate);
  Prog.Free();
end;

procedure TTStackTests.TestSemantic_TStack_Push_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcPush);
  Prog.Free();
end;

procedure TTStackTests.TestSemantic_TStack_Pop_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcPop);
  Prog.Free();
end;

procedure TTStackTests.TestSemantic_TStack_Peek_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcPeek);
  Prog.Free();
end;

initialization
  RegisterTest(TTStackTests);

end.
