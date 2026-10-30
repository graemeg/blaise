{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ bindgen — C declaration model.

  The in-memory representation of the C declarations harvested from a
  clang AST dump.  Types are carried as raw clang qualType strings
  (e.g. 'const char *', 'unsigned long'); mapping them to Blaise type
  names is Bindgen.TypeMap's job, and emitting Blaise source from this
  model is Bindgen.Emit's job. }

unit Bindgen.Model;

interface

uses
  generics.collections;

type
  { Base class for all harvested declarations; TCModel.Decls preserves
    the original C declaration order, which the emitter relies on for
    declare-before-use (C guarantees it; Pascal requires it). }
  TCDecl = class
  end;

  TCParam = class
  public
    Name: string;          { may be '' for unnamed C parameters }
    CType: string;         { clang qualType string }
    constructor Create(const AName, ACType: string);
  end;

  TCFunction = class(TCDecl)
  public
    Name: string;
    ReturnCType: string;   { 'void' for procedures }
    Params: TList<TCParam>;
    IsVariadic: Boolean;
    constructor Create(const AName: string);
  end;

  TCTypedef = class(TCDecl)
  public
    Name: string;
    CType: string;         { underlying qualType, e.g. 'unsigned long' }
    constructor Create(const AName, ACType: string);
  end;

  TCEnumMember = class
  public
    Name: string;
    Value: Int64;
    constructor Create(const AName: string; AValue: Int64);
  end;

  TCEnum = class(TCDecl)
  public
    Name: string;          { '' for anonymous enums }
    Members: TList<TCEnumMember>;
    constructor Create(const AName: string);
  end;

  TCField = class
  public
    Name: string;
    CType: string;
    IsBitfield: Boolean;
    BitWidth: Int;
    Note: string;      { emitter appends this as a comment, e.g. the
                         member:width list of a collapsed bitfield run }
    constructor Create(const AName, ACType: string);
  end;

  TCRecord = class(TCDecl)
  public
    Name: string;          { C tag name, or the typedef name when the
                             struct is anonymous and typedef-named }
    IsUnion: Boolean;
    IsComplete: Boolean;   { False = opaque forward declaration }
    Fields: TList<TCField>;
    constructor Create(const AName: string);
  end;

  { The whole harvested translation unit.  Decls preserves the original
    C declaration order; the typed lists are convenience views onto the
    same objects. }
  TCModel = class
  public
    Decls: TList<TCDecl>;
    Typedefs: TList<TCTypedef>;
    Enums: TList<TCEnum>;
    Records: TList<TCRecord>;
    Functions: TList<TCFunction>;
    constructor Create;
    function FindRecord(const AName: string): TCRecord;
    procedure AddTypedef(ATypedef: TCTypedef);
    procedure AddEnum(AEnum: TCEnum);
    procedure AddRecord(ARecord: TCRecord);
    procedure AddFunction(AFunction: TCFunction);
  end;

implementation

constructor TCParam.Create(const AName, ACType: string);
begin
  inherited Create();
  Name := AName;
  CType := ACType;
end;

constructor TCFunction.Create(const AName: string);
begin
  inherited Create();
  Name := AName;
  Params := TList<TCParam>.Create();
  IsVariadic := False;
end;

constructor TCTypedef.Create(const AName, ACType: string);
begin
  inherited Create();
  Name := AName;
  CType := ACType;
end;

constructor TCEnumMember.Create(const AName: string; AValue: Int64);
begin
  inherited Create();
  Name := AName;
  Value := AValue;
end;

constructor TCEnum.Create(const AName: string);
begin
  inherited Create();
  Name := AName;
  Members := TList<TCEnumMember>.Create();
end;

constructor TCField.Create(const AName, ACType: string);
begin
  inherited Create();
  Name := AName;
  CType := ACType;
  IsBitfield := False;
  BitWidth := 0;
  Note := '';
end;

constructor TCRecord.Create(const AName: string);
begin
  inherited Create();
  Name := AName;
  IsUnion := False;
  IsComplete := False;
  Fields := TList<TCField>.Create();
end;

constructor TCModel.Create();
begin
  inherited Create();
  Decls := TList<TCDecl>.Create();
  Typedefs := TList<TCTypedef>.Create();
  Enums := TList<TCEnum>.Create();
  Records := TList<TCRecord>.Create();
  Functions := TList<TCFunction>.Create();
end;

procedure TCModel.AddTypedef(ATypedef: TCTypedef);
begin
  Decls.Add(ATypedef);
  Typedefs.Add(ATypedef);
end;

procedure TCModel.AddEnum(AEnum: TCEnum);
begin
  Decls.Add(AEnum);
  Enums.Add(AEnum);
end;

procedure TCModel.AddRecord(ARecord: TCRecord);
begin
  Decls.Add(ARecord);
  Records.Add(ARecord);
end;

procedure TCModel.AddFunction(AFunction: TCFunction);
begin
  Decls.Add(AFunction);
  Functions.Add(AFunction);
end;

function TCModel.FindRecord(const AName: string): TCRecord;
var
  I: Int;
begin
  Result := nil;
  for I := 0 to Records.Count - 1 do
    if Records[I].Name = AName then
    begin
      Result := Records[I];
      Exit;
    end;
end;

end.
