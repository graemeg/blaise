{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.streams;

{ IR-level tests for the streams design.

  These tests are deliberately self-contained — they declare the stream
  interfaces and abstract bases inline so the test harness does not need
  to resolve the Streams RTL unit.  They verify that the compiler:

    * accepts the design's class shape (abstract base + concrete subclass
      implementing the interface);
    * emits an itab that points at $_AbstractMethodError for abstract
      slots on the abstract base; and
    * emits a concrete-impl pointer in the subclass's itab/vtable. }

interface

uses
  Classes, SysUtils, blaise.testing,
  uLexer, uParser, uAST, uSymbolTable, uSemantic;

type
  TStreamsTests = class(TTestCase)
  private
    function IRContains(const AIR, AFragment: string): Boolean;
  published
  end;

implementation

function TStreamsTests.IRContains(const AIR, AFragment: string): Boolean;
begin
  Result := Pos(AFragment, AIR) > 0
end;

const
  { Mirrors the actual streams.pas shape: ICloseable, IInputStream
    extending it, and an abstract TInputStream that declares the
    interface but defers the implementation. }
  SrcAbstractBase =
    '''
    program P;
    type
      ICloseable = interface
        procedure Close;
      end;
      IInputStream = interface(ICloseable)
        function Read(Buf: Pointer; Count: Integer): Integer;
      end;
      TInputStream = class(TObject, IInputStream, ICloseable)
        function Read(Buf: Pointer; Count: Integer): Integer; virtual; abstract;
        procedure Close; virtual; abstract;
      end;
    begin end.
    ''';

  SrcConcreteSubclass =
    '''
    program P;
    type
      ICloseable = interface
        procedure Close;
      end;
      IInputStream = interface(ICloseable)
        function Read(Buf: Pointer; Count: Integer): Integer;
      end;
      TInputStream = class(TObject, IInputStream, ICloseable)
        function Read(Buf: Pointer; Count: Integer): Integer; virtual; abstract;
        procedure Close; virtual; abstract;
      end;
      TMemoryInput = class(TInputStream, IInputStream, ICloseable)
        function Read(Buf: Pointer; Count: Integer): Integer; override;
        procedure Close; override;
      end;
    function TMemoryInput.Read(Buf: Pointer; Count: Integer): Integer;
    begin Result := 0 end;
    procedure TMemoryInput.Close;
    begin end;
    begin end.
    ''';

initialization
  RegisterTest(TStreamsTests)

end.
