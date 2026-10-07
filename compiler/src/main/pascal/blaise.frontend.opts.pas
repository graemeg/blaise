{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit blaise.frontend.opts;

{ Front-end-only command-line state.

  This is the front-end counterpart to TBackendOpts (blaise.codegen.driver).
  TBackendOpts carries the cross-cutting knobs a backend driver actually
  reads (target, debug mode, OPDF, internal-assembler).  TFrontEndOpts
  carries everything the front-end consumes BEFORE or INDEPENDENTLY of any
  resolved driver: input/output paths, search paths, separate-compilation
  flags, and the output-mode policy flags that drive driver SELECTION
  (EmitAsm) and the Backend kind that is the INPUT to selection.

  The split keeps TBackendOpts from becoming a god-object: no driver method
  should ever see SourceFile / SearchPaths / EmitIfaceDir.  It lives in its
  own unit (not blaise.codegen.driver) precisely because that unit is the
  backend-facing abstraction and front-end state is not a backend concern.

  Backend kind is referenced via the driver registry's TBackendKind so the
  front-end and the drivers share one enum. }

interface

uses
  Classes,
  blaise.codegen.driver,   { TBackendKind }
  blaise.codegen.target;   { TTargetDesc }

type
  { Built once by the Blaise.pas flag parser; read by the front-end driver
    body.  Owns its SearchPaths list (freed by the destructor). }
  TFrontEndOpts = class
  public
    SourceFile: string;
    OutputFile: string;
    SearchPaths: TStringList;   { owned }
    Defines: TStringList;       { owned — conditional-compilation symbols from -d }
    EmitIfaceDir: string;
    Incremental: Boolean;
    UnitCacheDir: string;
    DumpAST: Boolean;
    SkipDepCodegen: Boolean;

    { Output-mode policy + selection input. EmitAsm picks the top driver (see
      PickTopDriver) and governs stdout dispatch; Backend is the requested
      backend kind, consumed by PickTopDriver before any driver exists. }
    EmitAsm: Boolean;
    Backend: TBackendKind;
    { True only when --backend was given explicitly; an explicit flag
      outranks the BLAISE_BACKEND environment variable. }
    BackendExplicit: Boolean;

    constructor Create;
    destructor Destroy; override;
  end;

implementation

constructor TFrontEndOpts.Create;
begin
  Self.SearchPaths := TStringList.Create();
  Self.Defines := TStringList.Create();
end;

destructor TFrontEndOpts.Destroy;
begin
  Self.Defines.Free();
  Self.SearchPaths.Free();
  inherited Destroy();
end;

end.
