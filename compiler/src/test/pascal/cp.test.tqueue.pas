{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.tqueue;

{ IR unit tests for TQueue<T>: Enqueue/Dequeue/Peek/Clear/Destroy and Grow.
  Uses Integer as the type parameter throughout. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TTQueueTests = class(TTestCase)
  private
    function AnalyseSrc(const ASrc: string): TProgram;
  published
    procedure TestSemantic_TQueue_Instantiates;
    procedure TestSemantic_TQueue_Enqueue_Compiles;
    procedure TestSemantic_TQueue_Dequeue_Compiles;
    procedure TestSemantic_TQueue_Peek_Compiles;
  end;

implementation

const
  QueueDecl =
    '''
        type
          TQueue<T> = class
            FData:     ^T;
            FCount:    Integer;
            FCapacity: Integer;
            FHead:     Integer;
            FTail:     Integer;
            procedure Grow;
            procedure Enqueue(Value: T);
            function  Dequeue: T;
            function  Peek: T;
            procedure Clear;
            procedure Destroy;
            property Count: Integer read FCount;
          end;
        ''';

  QueueImpls =
    '''
        procedure TQueue<T>.Grow;
        var
          NewCap:  Integer;
          OldCap:  Integer;
          NewData: ^T;
          I:       Integer;
          Src:     ^T;
          Dst:     ^T;
        begin
          OldCap  := Self.FCapacity;
          if OldCap = 0 then
            NewCap := 4
          else
            NewCap := OldCap * 2;
          NewData := GetMem(NewCap * SizeOf(T));
          ZeroMem(NewData, NewCap * SizeOf(T));
          I := 0;
          while I < Self.FCount do
          begin
            Src  := Self.FData + ((Self.FHead + I) mod OldCap) * SizeOf(T);
            Dst  := NewData + I * SizeOf(T);
            Dst^ := Src^;
            I    := I + 1
          end;
          FreeMem(Self.FData);
          Self.FData     := NewData;
          Self.FHead     := 0;
          Self.FTail     := Self.FCount;
          Self.FCapacity := NewCap
        end;
        procedure TQueue<T>.Enqueue(Value: T);
        var
          Dest: ^T;
        begin
          if Self.FCount = Self.FCapacity then
            Self.Grow();
          Dest        := Self.FData + Self.FTail * SizeOf(T);
          Dest^       := Value;
          Self.FTail  := (Self.FTail + 1) mod Self.FCapacity;
          Self.FCount := Self.FCount + 1
        end;
        function TQueue<T>.Dequeue: T;
        var
          Src: ^T;
        begin
          Src         := Self.FData + Self.FHead * SizeOf(T);
          Result      := Src^;
          Self.FHead  := (Self.FHead + 1) mod Self.FCapacity;
          Self.FCount := Self.FCount - 1
        end;
        function TQueue<T>.Peek: T;
        var
          Src: ^T;
        begin
          Src    := Self.FData + Self.FHead * SizeOf(T);
          Result := Src^
        end;
        procedure TQueue<T>.Clear;
        begin
          Self.FCount := 0;
          Self.FHead  := 0;
          Self.FTail  := 0
        end;
        procedure TQueue<T>.Destroy;
        begin
          FreeMem(Self.FData);
          Self.FData     := nil;
          Self.FCount    := 0;
          Self.FCapacity := 0;
          Self.FHead     := 0;
          Self.FTail     := 0
        end;
        ''';

  SrcCreate =
    'program P;' + #10 +
    QueueDecl +
    QueueImpls +
    '''
        var Q: TQueue<Integer>;
        begin
          Q := TQueue<Integer>.Create()
        end.
        ''';

  SrcEnqueue =
    'program P;' + #10 +
    QueueDecl +
    QueueImpls +
    '''
        var Q: TQueue<Integer>;
        begin
          Q := TQueue<Integer>.Create();
          Q.Enqueue(1);
          Q.Enqueue(2);
          Q.Enqueue(3)
        end.
        ''';

  SrcDequeue =
    'program P;' + #10 +
    QueueDecl +
    QueueImpls +
    '''
        var
          Q: TQueue<Integer>;
          V: Integer;
        begin
          Q := TQueue<Integer>.Create();
          Q.Enqueue(10);
          V := Q.Dequeue()
        end.
        ''';

  SrcPeek =
    'program P;' + #10 +
    QueueDecl +
    QueueImpls +
    '''
        var
          Q: TQueue<Integer>;
          V: Integer;
        begin
          Q := TQueue<Integer>.Create();
          Q.Enqueue(99);
          V := Q.Peek()
        end.
        ''';

function TTQueueTests.AnalyseSrc(const ASrc: string): TProgram;
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

procedure TTQueueTests.TestSemantic_TQueue_Instantiates;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcCreate);
  Prog.Free();
end;

procedure TTQueueTests.TestSemantic_TQueue_Enqueue_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcEnqueue);
  Prog.Free();
end;

procedure TTQueueTests.TestSemantic_TQueue_Dequeue_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcDequeue);
  Prog.Free();
end;

procedure TTQueueTests.TestSemantic_TQueue_Peek_Compiles;
var
  Prog: TProgram;
begin
  Prog := AnalyseSrc(SrcPeek);
  Prog.Free();
end;

initialization
  RegisterTest(TTQueueTests);

end.
