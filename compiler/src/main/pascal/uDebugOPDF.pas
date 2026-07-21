{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uDebugOPDF;

{ OPDF debug information emitter.
  Produces a companion .opdf.s GNU assembly file that the linker folds into
  the ELF .opdf section.  The existing pdr debugger reads that section without
  modification.

  Platform note: section and relocation syntax targets Linux x86_64 (ELF).
  For macOS arm64 (Mach-O) change the .section directive to
  ".section __DATA,__opdf" and review .quad relocation constraints. }

interface

uses
  SysUtils, Classes, contnrs, uAST, uSymbolTable, uDebugFacts, blaise.codegen;

type
  TOPDFEmitter = class
  private
    FProgram:    TProgram;
    FUnit:       TUnit;        { non-nil in unit mode; FProgram is nil then }
    [Unretained] FUnitSymTable: TSymbolTable;  { unit-mode symbol table (not owned) }
    FSourceFile: string;
    [Unretained] FFacts: TDbgFacts;  { non-owned — provided by the driver }
    FOutput:     TStringList;
    FTypeNames:  TStringList;   { sorted; Objects[i] = Pointer(PtrUInt(TypeID)) }
    FEmitted:    TStringList;   { sorted canonical names already written }
    FRecordCount:       Integer;
    FTotRecIdx:         Integer;  { FOutput line index of the TotalRecords placeholder }
    FUnitDirRecCountIdx: Integer;  { FOutput line index of the UnitDirectory RecordCount placeholder }
    FDone:        Boolean;

    function  FNV1a32(const S: string): Cardinal;
    function  GetOrAllocTypeID(const AName: string): Cardinal;
    function  HasBeenEmitted(const AName: string): Boolean;
    procedure MarkEmitted(const AName: string);
    procedure L(const AText: string);
    procedure EmitRecHdr(ARecType: Byte; ARecSize: Integer);
    procedure EmitNameLen(const AStr: string);
    procedure EmitNameData(const AStr: string);
    procedure EmitStrField(const AStr: string);
    procedure EmitSection;
    procedure EmitHeader;
    procedure EmitTypeDesc(AType: TTypeDesc);
    procedure EmitPrimitive(AType: TTypeDesc);
    procedure EmitEnum(AType: TEnumTypeDesc);
    procedure EmitRecord(AType: TRecordTypeDesc);
    procedure EmitClass(AType: TRecordTypeDesc);
    procedure EmitUtf8Str;
    procedure EmitGlobalVar(const AVarName: string; AType: TTypeDesc);
    procedure EmitFunctionScope(AMethod: TMethodDecl; AScopeID: Integer;
                                ADeclIdx: Integer; const ANextLabel: string;
                                const ALabel: string);
    procedure EmitParameters(AMethod: TMethodDecl);
    procedure EmitLocalVars(ABlock: TBlock; AScopeID: Integer);
    procedure EmitFunctionScope_Main(AScopeID, ADeclIdx: Integer);
    procedure EmitUnitDirectory;
    procedure EmitRuntimeHelper(AKind: Integer; const ASymbol: string);
    procedure EmitRuntimeHelpers;
    procedure EmitPointer(AType: TPointerTypeDesc);
    procedure EmitOpaquePointer(AType: TTypeDesc);
    procedure EmitArray(AType: TTypeDesc);
    procedure EmitSet(AType: TSetTypeDesc);
    procedure EmitInterface(AType: TInterfaceTypeDesc);
    procedure EmitProperties(AClass: TRecordTypeDesc);
    procedure EmitConstants;
    procedure EmitConstantsFromList(AList: TObjectList);
    procedure EmitTypesFromBlock(ABlock: TBlock);
    procedure EmitGlobalVarsFromList(AList: TObjectList);
    procedure EmitStaticVarsFromBlock(ABlock: TBlock);
    procedure EmitAllTypes;
    procedure EmitGlobalVars;
    procedure EmitFunctionScopes;
    function MangledClassSym(const AClassName: string): string;
    procedure EmitFactsTypes;
    procedure EmitFunctionScopesFromFacts;
    procedure EmitFactParameter(AVar: TDbgVar; var ADeclIdx: Integer);
    procedure EmitFactLocalVar(AVar: TDbgVar; AScopeID: Integer;
      var ADeclIdx: Integer);
    procedure CollectStmtLines(AStmt: TASTStmt; ALines: TStringList);
    procedure EmitLineInfoForBlock(ABlock: TBlock; const AFuncLabel, AFuncName: string);
    procedure EmitLineInfoForScope(AMethod: TMethodDecl);
    procedure PatchTotalRecords;
    procedure PatchUnitDirRecordCount;
    procedure DoEmit;
    function  FuncLabel(AMethod: TMethodDecl): string;
    function  CanonicalName(AType: TTypeDesc): string;
    function  FieldsPayloadSize(ARec: TRecordTypeDesc): Integer;
    procedure EmitFields(ARec: TRecordTypeDesc);
    function  ActiveSymTable: TSymbolTable;
  public
    constructor Create(AProgram: TProgram; const ASourceFile: string);
    { Unit-mode emitter: produces a complete, self-contained .opdf section for
      a single unit's object file (no program directory, no 'main' scope).
      The same section is concatenated by the linker with every other unit's
      and the program's .opdf section. }
    constructor CreateForUnit(AUnit: TUnit; ASymTable: TSymbolTable;
                              const ASourceFile: string);
    { Optional codegen facts: when set, scopes/locals/lines are emitted
      from exact backend data instead of the approximate AST walk. }
    procedure SetFacts(AFacts: TDbgFacts);
    destructor Destroy; override;
    procedure EmitToFile(const AFileName: string);
    function  GetOutput: string;
  end;

implementation

const
  REC_PRIMITIVE = 1;
  REC_GLOBALVAR = 2;
  REC_ANSISTR   = 4;   { kept for reference; Blaise now emits recUtf8Str instead }
  REC_UTF8STR   = 23;
  REC_POINTER   = 6;
  REC_ARRAY     = 7;
  REC_RECORD    = 8;
  REC_CLASS     = 9;
  REC_PROPERTY  = 10;
  REC_LOCALVAR  = 12;
  REC_PARAMETER = 13;
  REC_LINEINFO  = 14;
  REC_FUNCSCOPE = 15;
  REC_INTERFACE = 16;
  REC_ENUM      = 17;
  REC_SET       = 18;
  REC_UNITDIR   = 19;
  REC_CONSTANT  = 20;
  REC_RUNTIMEHELPER = 25;

  { TRuntimeHelperKind ordinals (mirror opdf_types.TRuntimeHelperKind) }
  RHK_STRING_RELEASE   = 0;
  RHK_DYNARRAY_RELEASE = 1;

  SK_INTEGER = 0;
  SK_BOOLEAN = 1;
  { SK_CHAR = 2; SK_WIDECHAR = 3; — reserved by the OPDF spec, not emitted yet }
  SK_FLOAT   = 4;  { Single, Double — pdr renders via TFloatEvaluator }

  LOC_RBP = 1;
  LOC_RBP_INDIRECT = 3;  { frame slot holds the value's address }
  LOC_OPENARRAY = 5;     { open-array: data ptr at LocationData, element count
                           from companion _high slot (trailing SmallInt) }

  PAT_FIELD  = 0;  { property accessor: direct field offset }
  PAT_METHOD = 1;  { property accessor: method call }
  PAT_NONE   = 2;  { property accessor: no accessor }

  CK_ORD    = 0;  { constant kind: ordinal (Int64) }
  CK_STRING = 1;  { constant kind: string bytes }
  CK_REAL   = 2;  { constant kind: floating-point (Double, 8 bytes) }

constructor TOPDFEmitter.Create(AProgram: TProgram; const ASourceFile: string);
begin
  inherited Create();
  FProgram    := AProgram;
  FUnit       := nil;
  FUnitSymTable := nil;
  FSourceFile := ASourceFile;
  FOutput     := TStringList.Create();
  FTypeNames  := TStringList.Create();
  FTypeNames.Sorted        := True;
  FTypeNames.CaseSensitive := True;
  FEmitted    := TStringList.Create();
  FEmitted.Sorted        := True;
  FEmitted.CaseSensitive := True;
  FRecordCount        := 0;
  FTotRecIdx          := -1;
  FUnitDirRecCountIdx := -1;
  FDone               := False;
end;

constructor TOPDFEmitter.CreateForUnit(AUnit: TUnit; ASymTable: TSymbolTable;
  const ASourceFile: string);
begin
  inherited Create();
  FProgram      := nil;
  FUnit         := AUnit;
  FUnitSymTable := ASymTable;
  FSourceFile   := ASourceFile;
  FOutput       := TStringList.Create();
  FTypeNames    := TStringList.Create();
  FTypeNames.Sorted        := True;
  FTypeNames.CaseSensitive := True;
  FEmitted      := TStringList.Create();
  FEmitted.Sorted        := True;
  FEmitted.CaseSensitive := True;
  FRecordCount        := 0;
  FTotRecIdx          := -1;
  FUnitDirRecCountIdx := -1;
  FDone               := False;
end;

{ Escape a raw string value for a GNU-as / internal-assembler `.ascii "..."`
  literal.  A string CONSTANT's value is arbitrary user text — it may contain a
  double-quote, backslash, `#`, or control characters, any of which would break
  the surrounding `.ascii "<val>"  # Value` line (an unescaped `"` closes the
  literal early, leaving `..."  # Value` as a garbage mnemonic).  We emit the
  C-style escapes both assemblers understand.  The OPDF ValueLen field is the
  RAW byte count (Length before escaping), which `.ascii` with these escapes
  reproduces exactly, so escaping does not change the emitted byte length. }
function EscapeAsciiStr(const S: string): string;
var
  I, B: Integer;
begin
  Result := '';
  for I := 0 to Length(S) - 1 do
  begin
    B := OrdAt(S, I) and $FF;
    case B of
      Ord('\'): Result := Result + '\\';
      Ord('"'): Result := Result + '\"';
      10:       Result := Result + '\n';
      13:       Result := Result + '\r';
      9:        Result := Result + '\t';
    else
      { Printable ASCII passes through; anything else (including '#', which is a
        comment start OUTSIDE a quoted literal but harmless inside one, and any
        non-printable byte) is emitted as a 3-digit octal escape so the line
        stays a single well-formed token. }
      if (B >= 32) and (B < 127) then
        Result := Result + Chr(B)
      else
        Result := Result + '\' +
          Chr(Ord('0') + ((B shr 6) and 7)) +
          Chr(Ord('0') + ((B shr 3) and 7)) +
          Chr(Ord('0') + (B and 7));
    end;
  end;
end;

function TOPDFEmitter.ActiveSymTable: TSymbolTable;
begin
  if FUnit <> nil then
    Result := FUnitSymTable
  else if FProgram <> nil then
    Result := FProgram.SymbolTable
  else
    Result := nil;
end;

destructor TOPDFEmitter.Destroy;
begin
  FEmitted.Free();
  FTypeNames.Free();
  FOutput.Free();
  inherited Destroy();
end;

procedure TOPDFEmitter.L(const AText: string);
begin
  FOutput.Add(AText);
end;

function TOPDFEmitter.FNV1a32(const S: string): Cardinal;
const
  FNV_PRIME  = $01000193;
  FNV_OFFSET = $811C9DC5;
var
  B: Byte;
begin
  Result := FNV_OFFSET;
  for B in S do
  begin
    Result := Result xor Cardinal(B);
    Result := Result * FNV_PRIME;
  end;
  if Result = 0 then
    Result := 1;
end;

function TOPDFEmitter.GetOrAllocTypeID(const AName: string): Cardinal;
var
  Idx: Integer;
begin
  if FTypeNames.Find(AName, Idx) then
    Result := Cardinal(PtrUInt(FTypeNames.Objects[Idx]))
  else
  begin
    Result := FNV1a32(AName);
    FTypeNames.AddObject(AName, TObject(PtrUInt(Result)));
  end;
end;

function TOPDFEmitter.HasBeenEmitted(const AName: string): Boolean;
var
  Idx: Integer;
begin
  Result := FEmitted.Find(AName, Idx);
end;

procedure TOPDFEmitter.MarkEmitted(const AName: string);
begin
  if not HasBeenEmitted(AName) then
    FEmitted.Add(AName);
end;

procedure TOPDFEmitter.EmitRecHdr(ARecType: Byte; ARecSize: Integer);
begin
  L('    .byte ' + IntToStr(ARecType) + '  # RecType');
  L('    .int  ' + IntToStr(ARecSize) + '  # RecSize');
  FRecordCount := FRecordCount + 1;
end;

procedure TOPDFEmitter.EmitNameLen(const AStr: string);
begin
  L('    .word ' + IntToStr(Length(AStr)) + '  # NameLen');
end;

procedure TOPDFEmitter.EmitNameData(const AStr: string);
begin
  if Length(AStr) > 0 then
    L('    .ascii "' + AStr + '"');
end;

procedure TOPDFEmitter.EmitStrField(const AStr: string);
begin
  EmitNameLen(AStr);
  EmitNameData(AStr);
end;

function TOPDFEmitter.CanonicalName(AType: TTypeDesc): string;
var
  SA: TStaticArrayTypeDesc;
begin
  if AType = nil then
  begin
    Exit('Pointer');
  end;
  case AType.Kind of
    tyString:
      Result := 'Utf8String';
    tyPointer:
      if TPointerTypeDesc(AType).BaseType = nil then
        Result := 'Pointer'
      else
        Result := '^' + CanonicalName(TPointerTypeDesc(AType).BaseType);
    tyStaticArray:
    begin
      SA := TStaticArrayTypeDesc(AType);
      if SA.Name <> '' then
        Result := SA.Name
      else
        Result := 'array[' + IntToStr(SA.LowBound) + '..' +
                  IntToStr(SA.HighBound) + '] of ' +
                  CanonicalName(SA.ElementType);
    end;
    tyOpenArray:
      { An open array is a distinct kind from a dynamic array (no heap header;
        length in a companion slot).  Give it a distinct canonical name so it
        gets its own TypeID and recArray(ArrayKind=2) — otherwise it would
        alias a same-element 'array of T' dynamic-array record and inherit
        ArrayKind=1. }
      Result := 'open array of ' +
                CanonicalName(TOpenArrayTypeDesc(AType).ElementType);
  else
    if AType.Name = '' then
      Result := 'Pointer'
    else
      Result := AType.Name;
  end;
end;

function TOPDFEmitter.FieldsPayloadSize(ARec: TRecordTypeDesc): Integer;
var
  I: Integer;
  F: TFieldInfo;
begin
  Result := 0;
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    Result := Result + 4 + 4 + 2 + Length(F.Name);
  end;
end;

procedure TOPDFEmitter.EmitFields(ARec: TRecordTypeDesc);
var
  I: Integer;
  F: TFieldInfo;
  FTypeName: string;
begin
  for I := 0 to ARec.Fields.Count - 1 do
  begin
    F := TFieldInfo(ARec.Fields.Items[I]);
    if F.TypeDesc <> nil then
      FTypeName := CanonicalName(F.TypeDesc)
    else
      FTypeName := 'Pointer';
    L('    # field: ' + F.Name);
    L('    .int  ' + IntToStr(GetOrAllocTypeID(FTypeName)) + '  # FieldTypeID');
    L('    .int  ' + IntToStr(F.Offset) + '  # Offset');
    EmitStrField(F.Name);
  end;
end;

procedure TOPDFEmitter.EmitTypeDesc(AType: TTypeDesc);
var
  CName: string;
begin
  if AType = nil then Exit;
  CName := CanonicalName(AType);
  if HasBeenEmitted(CName) then Exit;
  case AType.Kind of
    tyInteger, tyInt64, tyUInt32, tyUInt64,
    tySmallInt, tyWord, tyByte, tyBoolean,
    tyDouble, tySingle:
      EmitPrimitive(AType);
    tyString:
      EmitUtf8Str();
    tyEnum:
      EmitEnum(TEnumTypeDesc(AType));
    tyRecord:
      EmitRecord(TRecordTypeDesc(AType));
    tyClass:
      EmitClass(TRecordTypeDesc(AType));
    tyPointer:
      EmitPointer(TPointerTypeDesc(AType));
    tyStaticArray, tyOpenArray, tyDynArray:
      EmitArray(AType);
    tySet:
      EmitSet(TSetTypeDesc(AType));
    tyInterface:
      EmitInterface(TInterfaceTypeDesc(AType));
    tyPChar:
      EmitOpaquePointer(AType);
  else
    { tyVoid, tyNil: no OPDF record }
  end;
end;

procedure TOPDFEmitter.EmitPrimitive(AType: TTypeDesc);
var
  CName: string;
  SubKind, IsSigned, SzB: Byte;
  RecSize: Integer;
begin
  CName := CanonicalName(AType);
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  SzB      := AType.RawSize();
  case AType.Kind of
    tyBoolean:         begin SubKind := SK_BOOLEAN; IsSigned := 0; end;
    tyInt64, tyInteger, tySmallInt:
                       begin SubKind := SK_INTEGER;  IsSigned := 1; end;
    tyDouble, tySingle:
                       { Single (4B) / Double (8B) — pdr keys off SubKind=skFloat
                         and reads the IEEE 754 value by SizeInBytes. }
                       begin SubKind := SK_FLOAT;    IsSigned := 1; end;
  else
    SubKind := SK_INTEGER; IsSigned := 0;
  end;
  RecSize := 9 + Length(CName);

  L('');
  L('    # recPrimitive: ' + CName);
  EmitRecHdr(REC_PRIMITIVE, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .byte ' + IntToStr(SzB) + '  # SizeInBytes');
  L('    .byte ' + IntToStr(IsSigned) + '  # IsSigned');
  L('    .byte ' + IntToStr(SubKind) + '  # SubKind');
  EmitStrField(CName);
end;

procedure TOPDFEmitter.EmitUtf8Str;
const
  CNAME    = 'Utf8String';
  { Data-pointer convention: variable holds pointer to char data.
    The 12-byte header lives before it at negative offsets:
      data_ptr − 12 = RefCount
      data_ptr −  8 = Length    (byte count = character count for ASCII range)
      data_ptr −  4 = Capacity
    Encoding is always UTF-8; no code-page or element-size fields. }
  RC_OFFSET  = -12;
  LEN_OFFSET = -8;
  CAP_OFFSET = -4;
var
  RecSize: Integer;
begin
  if HasBeenEmitted(CNAME) then Exit;
  MarkEmitted(CNAME);
  RecSize := 12 + Length(CNAME);   { TDefUtf8String fixed part = 12 bytes }
  L('');
  L('    # recUtf8Str: Utf8String (data_ptr-12=RC, data_ptr-8=Len, data_ptr-4=Cap, data_ptr+0=chars)');
  EmitRecHdr(REC_UTF8STR, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CNAME)) + '  # TypeID');
  L('    .word ' + IntToStr(RC_OFFSET)  + '  # RefCountOffset');
  L('    .word ' + IntToStr(LEN_OFFSET) + '  # LengthOffset');
  L('    .word ' + IntToStr(CAP_OFFSET) + '  # CapacityOffset');
  EmitStrField(CNAME);
end;

procedure TOPDFEmitter.EmitEnum(AType: TEnumTypeDesc);
var
  CName: string;
  RecSize, MembSize, I: Integer;
begin
  CName := AType.Name;
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  MembSize := 0;
  for I := 0 to AType.Members.Count - 1 do
    MembSize := MembSize + 8 + 2 + Length(AType.Members.Strings[I]);

  RecSize := 11 + Length(CName) + MembSize;

  L('');
  L('    # recEnum: ' + CName);
  EmitRecHdr(REC_ENUM, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .byte 4                          # SizeInBytes');
  L('    .int  ' + IntToStr(AType.Members.Count) + '  # MemberCount');
  EmitStrField(CName);
  for I := 0 to AType.Members.Count - 1 do
  begin
    L('    # member: ' + AType.Members.Strings[I]);
    { The real stored ordinal, not the positional index — an explicit-ordinal
      enum's members carry their own values, and the debugger must show them
      (BUG-20260720-enum-explicit-ordinal-highlow). }
    L('    .quad ' + IntToStr(AType.OrdinalAt(I)) + '  # Value');
    EmitStrField(AType.Members.Strings[I]);
  end;
end;

procedure TOPDFEmitter.EmitRecord(AType: TRecordTypeDesc);
var
  CName: string;
  RecSize, I: Integer;
  F: TFieldInfo;
begin
  CName := AType.Name;
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  for I := 0 to AType.Fields.Count - 1 do
  begin
    F := TFieldInfo(AType.Fields.Items[I]);
    if F.TypeDesc <> nil then
      EmitTypeDesc(F.TypeDesc);
  end;

  RecSize := 14 + Length(CName) + FieldsPayloadSize(AType);

  L('');
  L('    # recRecord: ' + CName);
  EmitRecHdr(REC_RECORD, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .int  ' + IntToStr(AType.Fields.Count) + '  # FieldCount');
  L('    .int  ' + IntToStr(AType.TotalSize()) + '  # TotalSize');
  EmitStrField(CName);
  EmitFields(AType);
end;

function TOPDFEmitter.MangledClassSym(const AClassName: string): string;
var
  Sym:   TSymbol;
  Owner: string;
  I:     Integer;
  Ch:    string;
  Pfx:   string;
begin
  { Mirror the native backend's ClassSymName exactly so the .quad vtable_<sym>
    label here matches the symbol the backend actually defined.  In WHOLE-
    PROGRAM mode the backend has a program name and drops the prefix for
    program-owned classes; in UNIT mode there is no program name, so even the
    unit's own classes carry their unit prefix (vtable_<Unit>_<Class>). }
  Pfx := '';
  if Self.ActiveSymTable() <> nil then
  begin
    Sym := Self.ActiveSymTable().Lookup(AClassName);
    if Sym <> nil then
    begin
      Owner := Sym.OwningUnit;
      if (Owner <> '') and
         not ((FProgram <> nil) and SameText(Owner, FProgram.Name)) and
         not SameText(Owner, 'System') and
         not ((Length(Owner) >= 4) and SameText(Copy(Owner, 0, 4), 'rtl.')) and
         not ((Length(Owner) >= 7) and SameText(Copy(Owner, 0, 7), 'blaise_')) then
      begin
        for I := 0 to Length(Owner) - 1 do
        begin
          Ch := Copy(Owner, I, 1);
          if Ch = '.' then Pfx := Pfx + '_'
          else             Pfx := Pfx + Ch;
        end;
        Pfx := Pfx + '_';
      end;
    end;
  end;
  { Apply the shared CodegenMangle so the symbol matches the native backend
    exactly — handles '<', '>', ',', ' ' (e.g. 'class of T'), '$', '@', '^'. }
  Result := Pfx + CodegenMangle(AClassName);
end;

procedure TOPDFEmitter.EmitClass(AType: TRecordTypeDesc);
var
  CName, ParentName: string;
  ParentID: Cardinal;
  RecSize, I: Integer;
  F: TFieldInfo;
begin
  CName := AType.Name;
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  if AType.Parent <> nil then
  begin
    EmitClass(AType.Parent);
    ParentName := AType.Parent.Name;
    ParentID   := GetOrAllocTypeID(ParentName);
  end
  else
  begin
    ParentName := '';
    ParentID   := 0;
  end;

  for I := 0 to AType.Fields.Count - 1 do
  begin
    F := TFieldInfo(AType.Fields.Items[I]);
    if F.TypeDesc <> nil then
      EmitTypeDesc(F.TypeDesc);
  end;

  RecSize := 26 + Length(CName) + FieldsPayloadSize(AType);

  L('');
  L('    # recClass: ' + CName);
  EmitRecHdr(REC_CLASS, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .int  ' + IntToStr(ParentID) + '  # ParentTypeID');
  if AType.HasVTable() then
    L('    .quad vtable_' + MangledClassSym(CName) + '  # VMTAddress')
  else
    L('    .quad 0  # VMTAddress (no vtable)');
  L('    .int  ' + IntToStr(AType.TotalSize()) + '  # InstanceSize');
  L('    .int  ' + IntToStr(AType.Fields.Count) + '  # FieldCount');
  EmitStrField(CName);
  EmitFields(AType);
  EmitProperties(AType);
end;

procedure TOPDFEmitter.EmitGlobalVar(const AVarName: string; AType: TTypeDesc);
var
  CName: string;
  RecSize: Integer;
begin
  if AType <> nil then
  begin
    CName := CanonicalName(AType);
    EmitTypeDesc(AType);
  end
  else
    CName := 'Pointer';

  RecSize := 14 + Length(AVarName);

  L('');
  L('    # recGlobalVar: ' + AVarName);
  EmitRecHdr(REC_GLOBALVAR, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  if (AType <> nil) and (AType.Kind = tyInterface) then
    { Interface globals are two labels, Name_obj + Name_itab — there is no
      bare Name symbol.  Point the record at the object-pointer half. }
    L('    .quad ' + AVarName + '_obj  # Address (linker-resolved)')
  else
    L('    .quad ' + AVarName + '  # Address (linker-resolved)');
  EmitStrField(AVarName);
end;

procedure TOPDFEmitter.EmitFunctionScope(AMethod: TMethodDecl; AScopeID: Integer;
  ADeclIdx: Integer; const ANextLabel: string; const ALabel: string);
var
  FuncName, Label_: string;
  RecSize: Integer;
begin
  { The record name doubles as the symbol a debugger resolves for
    break-by-function-name — use the qualified label (TThing_Bump), which
    equals the bare name for plain functions. }
  FuncName := ALabel;
  Label_   := ALabel;
  RecSize  := 24 + Length(FuncName);

  L('');
  L('    # recFunctionScope: ' + FuncName);
  EmitRecHdr(REC_FUNCSCOPE, RecSize);
  L('    .int  ' + IntToStr(AScopeID) + '  # ScopeID');
  L('    .quad ' + Label_ + '  # LowPC');
  if ANextLabel <> '' then
    L('    .quad ' + ANextLabel + '  # HighPC (approx: next function start)')
  else
    L('    .quad 0  # HighPC (last function)');
  L('    .word ' + IntToStr(ADeclIdx) + '  # DeclIndex');
  EmitStrField(FuncName);
end;

procedure TOPDFEmitter.EmitRuntimeHelper(AKind: Integer; const ASymbol: string);
begin
  { recRuntimeHelper: 1-byte kind + 8-byte linker-resolved RTL entry-point
    address.  Lets the debugger inject a call to the RTL release routine for a
    +1 transient an injected property getter returns — see uDebugOPDF rationale
    and opdf-specification.adoc (recRuntimeHelper = 25). }
  L('');
  L('    # recRuntimeHelper: ' + ASymbol);
  EmitRecHdr(REC_RUNTIMEHELPER, 9);
  L('    .byte ' + IntToStr(AKind) + '  # Kind');
  L('    .quad ' + ASymbol + '  # Address (linker-resolved)');
end;

procedure TOPDFEmitter.EmitRuntimeHelpers;
begin
  { Emitted once per binary (program object only).  The RTL release routines
    are global symbols the linker resolves; the addresses land in the same
    image as the OPDF section, so the ASLR slide applies uniformly. }
  EmitRuntimeHelper(RHK_STRING_RELEASE,   '_StringRelease');
  EmitRuntimeHelper(RHK_DYNARRAY_RELEASE, '_DynArrayRelease');
end;

procedure TOPDFEmitter.EmitParameters(AMethod: TMethodDecl);
var
  I: Integer;
  P: TMethodParam;
  CName: string;
  RecSize: Integer;
begin
  for I := 0 to AMethod.Params.Count - 1 do
  begin
    P := TMethodParam(AMethod.Params.Items[I]);
    if P.ResolvedType <> nil then
    begin
      CName := CanonicalName(P.ResolvedType);
      { Ensure the parameter's type record is emitted (e.g. an open-array
        param's recArray with ArrayKind=2) — otherwise the TypeID below
        references a record that was never written. }
      EmitTypeDesc(P.ResolvedType);
    end
    else
      CName := 'Pointer';
    RecSize := 9 + Length(P.ParamName);
    L('');
    L('    # recParameter: ' + P.ParamName);
    EmitRecHdr(REC_PARAMETER, RecSize);
    L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
    L('    .byte ' + IntToStr(Ord(P.IsVarParam)) + '  # IsVar');
    L('    .byte ' + IntToStr(Ord(P.IsConstParam)) + '  # IsConst');
    L('    .byte 0  # IsOut');
    EmitStrField(P.ParamName);
  end;
end;

procedure TOPDFEmitter.EmitLocalVars(ABlock: TBlock; AScopeID: Integer);
var
  DeclIdx, RBPOffset: Integer;
  I, J: Integer;
  V: TVarDecl;
  CName, VarName: string;
  RawSz, RecSize: Integer;
begin
  DeclIdx   := 0;
  RBPOffset := 0;
  for I := 0 to ABlock.Decls.Count - 1 do
  begin
    V := TVarDecl(ABlock.Decls.Items[I]);
    if V.IsGlobal then Continue;
    if V.ResolvedType <> nil then
    begin
      CName  := CanonicalName(V.ResolvedType);
      RawSz  := V.ResolvedType.RawSize();
    end
    else
    begin
      CName := 'Pointer';
      RawSz := 8;
    end;
    RBPOffset := RBPOffset - ((RawSz + 7) and (-8));  { round up to 8-byte alignment; -8 = not 7 }
    for J := 0 to V.Names.Count - 1 do
    begin
      VarName := V.Names.Strings[J];
      RecSize := 15 + Length(VarName);
      L('');
      L('    # recLocalVar: ' + VarName);
      EmitRecHdr(REC_LOCALVAR, RecSize);
      L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
      L('    .int  ' + IntToStr(AScopeID) + '  # ScopeID');
      L('    .byte ' + IntToStr(LOC_RBP) + '  # LocationExpr (RBP-relative)');
      L('    .word ' + IntToStr(DeclIdx) + '  # DeclIndex');
      EmitNameLen(VarName);
      L('    .word ' + IntToStr(RBPOffset) + '  # LocationData (RBP offset)');
      EmitNameData(VarName);
      DeclIdx := DeclIdx + 1;
    end;
  end;
end;

function TOPDFEmitter.FuncLabel(AMethod: TMethodDecl): string;
begin
  if AMethod.OwnerTypeName = '' then
    Result := AMethod.Name
  else
    Result := AMethod.OwnerTypeName + '_' + AMethod.Name;
end;

procedure TOPDFEmitter.EmitSection;
begin
  L('    # OPDF debug companion file — generated by Blaise compiler');
  L('    # Platform: linux-x86_64 (ELF)');
  L('    # macOS arm64 adaptation: change .section to .section __DATA,__opdf');
  L('    .section .opdf, "aw", @progbits');
  L('');
  L('.Lopdf_start:');
end;

procedure TOPDFEmitter.EmitHeader;
begin
  L('    # OPDF header (32 bytes)');
  L('    .byte 79, 80, 68, 70           # Magic: OPDF');
  L('    .word 1                        # Version');
  L('    .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0  # BuildID (zeroed)');
  L('    .byte 2                        # TargetArch: archX86_64');
  L('    .byte 8                        # PointerSize: 8');
  FTotRecIdx := FOutput.Count;
  { TotalRecords = 0 selects stream-terminated mode: the reader does not trust
    a count, it reads records until section EOF and skips any further 32-byte
    'OPDF' magic headers (the next unit's block).  This is what makes per-unit
    .opdf sections concatenate cleanly at link time.  pdr ignores this field. }
  L('    .int  0                        # TotalRecords (0 = stream-terminated)');
  L('    .int  3                        # Flags: HAS_DIRECTORY or DYNARRAY_LEN32');
end;

procedure TOPDFEmitter.EmitFunctionScope_Main(AScopeID, ADeclIdx: Integer);
var
  ProgName: string;
  RecSize: Integer;
begin
  ProgName := FProgram.Name;
  RecSize  := 24 + Length(ProgName);
  L('');
  L('    # recFunctionScope: ' + ProgName);
  EmitRecHdr(REC_FUNCSCOPE, RecSize);
  L('    .int  ' + IntToStr(AScopeID) + '  # ScopeID');
  L('    .quad main  # LowPC (program entry point)');
  L('    .quad 0  # HighPC (last scope)');
  L('    .word ' + IntToStr(ADeclIdx) + '  # DeclIndex');
  EmitStrField(ProgName);
  EmitLineInfoForBlock(FProgram.Block, 'main', ProgName);
end;

procedure TOPDFEmitter.EmitUnitDirectory;
var
  DirName: string;
  RecSize: Integer;
begin
  DirName := FProgram.Name;
  RecSize := 14 + Length(DirName);  { 4(UnitCount)+4(Offset)+4(Count)+2(NameLen) }
  L('');
  L('    # recUnitDirectory');
  EmitRecHdr(REC_UNITDIR, RecSize);
  L('    .int  1  # UnitCount');
  L('    .int  .Lopdf_unit0_start - .Lopdf_start  # RecordOffset');
  FUnitDirRecCountIdx := FOutput.Count;
  L('    .int  0  # RecordCount (patched)');
  EmitStrField(DirName);
  L('');
  L('.Lopdf_unit0_start:');
end;

procedure TOPDFEmitter.EmitPointer(AType: TPointerTypeDesc);
var
  CName: string;
  TargetID: Cardinal;
  RecSize: Integer;
begin
  CName := CanonicalName(AType);
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  if AType.BaseType <> nil then
  begin
    EmitTypeDesc(AType.BaseType);
    TargetID := GetOrAllocTypeID(CanonicalName(AType.BaseType));
  end
  else
    TargetID := 0;

  RecSize := 10 + Length(CName);
  L('');
  L('    # recPointer: ' + CName);
  EmitRecHdr(REC_POINTER, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .int  ' + IntToStr(TargetID) + '  # TargetTypeID (0 = untyped)');
  EmitStrField(CName);
end;

procedure TOPDFEmitter.EmitOpaquePointer(AType: TTypeDesc);
var
  CName: string;
  RecSize: Integer;
begin
  { tyPChar is an opaque C pointer with no tracked element type (see
    uSymbolTable.pas) — emit it as a recPointer with TargetTypeID = 0,
    the same "untyped pointer" encoding EmitPointer uses for Pointer. }
  CName := CanonicalName(AType);
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  RecSize := 10 + Length(CName);
  L('');
  L('    # recPointer: ' + CName);
  EmitRecHdr(REC_POINTER, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .int  0  # TargetTypeID (0 = untyped)');
  EmitStrField(CName);
end;

procedure TOPDFEmitter.EmitArray(AType: TTypeDesc);
var
  CName, ElemName: string;
  ElemID: Cardinal;
  SA: TStaticArrayTypeDesc;
  IsDyn, RecSize: Integer;
begin
  CName := CanonicalName(AType);
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  if AType.Kind = tyStaticArray then
  begin
    SA := TStaticArrayTypeDesc(AType);
    EmitTypeDesc(SA.ElementType);
    ElemName := CanonicalName(SA.ElementType);
    ElemID   := GetOrAllocTypeID(ElemName);
    IsDyn    := 0;
    RecSize  := 12 + Length(CName) + 16;  { 12 fixed + name + 1×TArrayBound (16 bytes) }
    L('');
    L('    # recArray (static): ' + CName);
    EmitRecHdr(REC_ARRAY, RecSize);
    L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
    L('    .int  ' + IntToStr(ElemID) + '  # ElementTypeID');
    L('    .byte 1  # Dimensions');
    L('    .byte ' + IntToStr(IsDyn) + '  # IsDynamic');
    EmitStrField(CName);
    L('    .quad ' + IntToStr(SA.LowBound) + '  # LowerBound');
    L('    .quad ' + IntToStr(SA.HighBound) + '  # UpperBound');
  end
  else if AType.Kind = tyDynArray then
  begin
    EmitTypeDesc(TDynArrayTypeDesc(AType).ElementType);
    ElemName := CanonicalName(TDynArrayTypeDesc(AType).ElementType);
    ElemID   := GetOrAllocTypeID(ElemName);
    IsDyn    := 1;
    RecSize  := 12 + Length(CName);
    L('');
    L('    # recArray (dynamic): ' + CName);
    EmitRecHdr(REC_ARRAY, RecSize);
    L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
    L('    .int  ' + IntToStr(ElemID) + '  # ElementTypeID');
    L('    .byte 1  # Dimensions');
    L('    .byte ' + IntToStr(IsDyn) + '  # IsDynamic');
    EmitStrField(CName);
  end
  else
  begin
    { Open array: a (data ptr, high) pair with no heap header.  ArrayKind=2
      tells the debugger to read the length from the variable's companion
      slot, not from data-4.  (FPC's dbgopdf.pas has no open-array concept;
      this is a Blaise extension to the OPDF format.) }
    EmitTypeDesc(TOpenArrayTypeDesc(AType).ElementType);
    ElemName := CanonicalName(TOpenArrayTypeDesc(AType).ElementType);
    ElemID   := GetOrAllocTypeID(ElemName);
    RecSize  := 12 + Length(CName);
    L('');
    L('    # recArray (open): ' + CName);
    EmitRecHdr(REC_ARRAY, RecSize);
    L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
    L('    .int  ' + IntToStr(ElemID) + '  # ElementTypeID');
    L('    .byte 1  # Dimensions');
    L('    .byte 2  # ArrayKind');
    EmitStrField(CName);
  end;
end;

procedure TOPDFEmitter.EmitSet(AType: TSetTypeDesc);
var
  CName: string;
  BaseID: Cardinal;
  SzB, RecSize: Integer;
begin
  CName := AType.Name;
  if CName = '' then CName := 'set of ' + AType.BaseType.Name;
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  EmitTypeDesc(AType.BaseType);
  BaseID := GetOrAllocTypeID(AType.BaseType.Name);

  SzB := AType.RawSize();
  RecSize := 15 + Length(CName);  { 4(TypeID)+4(BaseTypeID)+1(SzB)+4(LBound)+2(NameLen) }

  L('');
  L('    # recSet: ' + CName);
  EmitRecHdr(REC_SET, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .int  ' + IntToStr(BaseID) + '  # BaseTypeID');
  L('    .byte ' + IntToStr(SzB) + '  # SizeInBytes');
  L('    .int  0  # LowerBound');
  EmitStrField(CName);
end;

procedure TOPDFEmitter.EmitInterface(AType: TInterfaceTypeDesc);
var
  CName: string;
  ParentID: Cardinal;
  I, MethodRecSize, RecSize: Integer;
  MName: string;
begin
  CName := AType.Name;
  if HasBeenEmitted(CName) then Exit;
  MarkEmitted(CName);

  if AType.Parent <> nil then
  begin
    EmitInterface(AType.Parent);
    ParentID := GetOrAllocTypeID(AType.Parent.Name);
  end
  else
    ParentID := 0;

  MethodRecSize := 0;
  for I := 0 to AType.MethodCount() - 1 do
    MethodRecSize := MethodRecSize + 7 + Length(AType.MethodName(I));

  RecSize := 31 + Length(CName) + MethodRecSize;
  { 4(TypeID)+4(ParentID)+1(IntfType)+16(GUID)+4(MethodCount)+2(NameLen) = 31 }

  L('');
  L('    # recInterface: ' + CName);
  EmitRecHdr(REC_INTERFACE, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .int  ' + IntToStr(ParentID) + '  # ParentTypeID');
  L('    .byte 0  # IntfType: itfCOM');
  L('    .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0  # GUID (zeroed)');
  L('    .int  ' + IntToStr(AType.MethodCount()) + '  # MethodCount');
  EmitStrField(CName);
  for I := 0 to AType.MethodCount() - 1 do
  begin
    MName := AType.MethodName(I);
    L('    # method: ' + MName);
    L('    .int  0  # ReturnTypeID (0 = procedure)');
    L('    .byte 0  # ParamCount');
    EmitStrField(MName);
  end;
end;

procedure TOPDFEmitter.EmitProperties(AClass: TRecordTypeDesc);
var
  I: Integer;
  PI: TPropertyInfo;
  PropTypeID, ClassTypeID: Cardinal;
  ReadType, WriteType: Integer;
  RecSize: Integer;
  RF: TFieldInfo;
  ReadMethSym, WriteMethSym: string;
begin
  if AClass.Properties.Count = 0 then Exit;
  ClassTypeID := GetOrAllocTypeID(AClass.Name);
  for I := 0 to AClass.Properties.Count - 1 do
  begin
    PI := TPropertyInfo(AClass.Properties.Items[I]);
    if PI.TypeDesc <> nil then
      PropTypeID := GetOrAllocTypeID(CanonicalName(PI.TypeDesc))
    else
      PropTypeID := 0;

    { Determine read accessor type }
    if PI.ReadField <> '' then
      ReadType := PAT_FIELD
    else if PI.ReadMethod <> '' then
      ReadType := PAT_METHOD
    else
      ReadType := PAT_NONE;

    { Determine write accessor type }
    if PI.WriteField <> '' then
      WriteType := PAT_FIELD
    else if PI.WriteMethod <> '' then
      WriteType := PAT_METHOD
    else
      WriteType := PAT_NONE;

    { Method-backed accessors carry the getter/setter SYMBOL name so the
      debugger can resolve it via FindFunctionByName (which matches against the
      recFunctionScope name = the mangled symbol) and inject the call.  The
      symbol is the same one written as ReadAddr/WriteAddr below. }
    if ReadType = PAT_METHOD then
      ReadMethSym := MangledClassSym(AClass.Name) + '_' + PI.ReadMethod
    else
      ReadMethSym := '';
    if WriteType = PAT_METHOD then
      WriteMethSym := MangledClassSym(AClass.Name) + '_' + PI.WriteMethod
    else
      WriteMethSym := '';

    { Fixed-size payload (30 bytes) + the three variable-length strings.
      4(ClassTypeID)+4(PropTypeID)+1(ReadType)+1(WriteType)+8(ReadAddr)+
      8(WriteAddr)+2(ReadMethodNameLen)+2(WriteMethodNameLen)+2(NameLen). }
    RecSize := 32 + Length(ReadMethSym) + Length(WriteMethSym) + Length(PI.Name);

    L('');
    L('    # recProperty: ' + PI.Name);
    EmitRecHdr(REC_PROPERTY, RecSize);
    L('    .int  ' + IntToStr(ClassTypeID) + '  # ClassTypeID');
    L('    .int  ' + IntToStr(PropTypeID) + '  # PropertyTypeID');
    L('    .byte ' + IntToStr(ReadType) + '  # ReadType');
    L('    .byte ' + IntToStr(WriteType) + '  # WriteType');

    { ReadAddr }
    if ReadType = PAT_FIELD then
    begin
      RF := AClass.FindField(PI.ReadField);
      if RF <> nil then
        L('    .quad ' + IntToStr(RF.Offset) + '  # ReadAddr (field offset)')
      else
        L('    .quad 0  # ReadAddr (field not found)');
    end
    else if ReadType = PAT_METHOD then
      L('    .quad ' + MangledClassSym(AClass.Name) + '_' + PI.ReadMethod + '  # ReadAddr (getter)')
    else
      L('    .quad 0  # ReadAddr (none)');

    { WriteAddr }
    if WriteType = PAT_FIELD then
    begin
      RF := AClass.FindField(PI.WriteField);
      if RF <> nil then
        L('    .quad ' + IntToStr(RF.Offset) + '  # WriteAddr (field offset)')
      else
        L('    .quad 0  # WriteAddr (field not found)');
    end
    else if WriteType = PAT_METHOD then
      L('    .quad ' + MangledClassSym(AClass.Name) + '_' + PI.WriteMethod + '  # WriteAddr (setter)')
    else
      L('    .quad 0  # WriteAddr (none)');

    { The reader (TDefProperty) expects all three length words FIRST, then the
      three strings in order: ReadMethodName, WriteMethodName, Name. }
    L('    .word ' + IntToStr(Length(ReadMethSym)) + '  # ReadMethodNameLen');
    L('    .word ' + IntToStr(Length(WriteMethSym)) + '  # WriteMethodNameLen');
    L('    .word ' + IntToStr(Length(PI.Name)) + '  # NameLen');
    EmitNameData(ReadMethSym);
    EmitNameData(WriteMethSym);
    EmitNameData(PI.Name);
  end;
end;

procedure TOPDFEmitter.EmitConstantsFromList(AList: TObjectList);
var
  I: Integer;
  C: TConstDecl;
  TypeID: Cardinal;
  RecSize: Integer;
begin
  for I := 0 to AList.Count - 1 do
  begin
    C := TConstDecl(AList.Items[I]);
    if C.IsFloat then
    begin
      { Floating-point constant: emit the 8-byte IEEE-754 Double via GAS
        .double (StrVal holds the raw literal text).  The debugger decodes
        ckReal as a Double. }
      TypeID  := GetOrAllocTypeID('Double');
      RecSize := 17 + Length(C.Name);  { 9 fixed + 8 (Double value) + name }
      L('');
      L('    # recConstant: ' + C.Name);
      EmitRecHdr(REC_CONSTANT, RecSize);
      L('    .int  ' + IntToStr(TypeID) + '  # TypeID');
      L('    .byte ' + IntToStr(CK_REAL) + '  # ConstKind: ckReal');
      L('    .word 8  # ValueLen');
      EmitNameLen(C.Name);
      L('    .double ' + C.StrVal + '  # Value');
      EmitNameData(C.Name);
    end
    else if C.IsString then
    begin
      TypeID  := GetOrAllocTypeID('AnsiString');
      RecSize := 9 + Length(C.StrVal) + Length(C.Name);
      L('');
      L('    # recConstant: ' + C.Name);
      EmitRecHdr(REC_CONSTANT, RecSize);
      L('    .int  ' + IntToStr(TypeID) + '  # TypeID');
      L('    .byte ' + IntToStr(CK_STRING) + '  # ConstKind: ckString');
      L('    .word ' + IntToStr(Length(C.StrVal)) + '  # ValueLen');
      EmitNameLen(C.Name);
      if Length(C.StrVal) > 0 then
        L('    .ascii "' + EscapeAsciiStr(C.StrVal) + '"  # Value');
      EmitNameData(C.Name);
    end
    else
    begin
      { Ordinal constant.  A typed ordinal (e.g. Boolean) carries its type so
        the debugger renders it symbolically (True/False); untyped integers
        use TypeID 0. }
      if (C.TypeName <> '') and HasBeenEmitted(C.TypeName) then
        TypeID := GetOrAllocTypeID(C.TypeName)
      else
        TypeID := 0;
      RecSize := 17 + Length(C.Name);  { 9 fixed + 8 (Int64 value) + name }
      L('');
      L('    # recConstant: ' + C.Name);
      EmitRecHdr(REC_CONSTANT, RecSize);
      L('    .int  ' + IntToStr(TypeID) + '  # TypeID');
      L('    .byte ' + IntToStr(CK_ORD) + '  # ConstKind: ckOrd');
      L('    .word 8  # ValueLen');
      EmitNameLen(C.Name);
      L('    .quad ' + IntToStr(C.IntVal) + '  # Value');
      EmitNameData(C.Name);
    end;
  end;
end;

procedure TOPDFEmitter.EmitConstants;
begin
  if FUnit <> nil then
  begin
    EmitConstantsFromList(FUnit.IntfBlock.ConstDecls);
    EmitConstantsFromList(FUnit.ImplBlock.ConstDecls);
  end
  else if FProgram <> nil then
    EmitConstantsFromList(FProgram.Block.ConstDecls);
end;

procedure TOPDFEmitter.EmitTypesFromBlock(ABlock: TBlock);
var
  I: Integer;
  TD: TTypeDecl;
  TDesc: TTypeDesc;
  ST: TSymbolTable;
begin
  ST := Self.ActiveSymTable();
  if ST = nil then Exit;
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    TDesc := ST.FindType(TD.Name);
    if TDesc <> nil then
      EmitTypeDesc(TDesc);
  end;
end;

procedure TOPDFEmitter.EmitAllTypes;
var
  I: Integer;
  GI: TGenericInstance;
  ST: TSymbolTable;
  GIList: TObjectList;
begin
  EmitUtf8Str();
  ST := Self.ActiveSymTable();
  if ST <> nil then
  begin
    EmitPrimitive(ST.TypeInteger);
    EmitPrimitive(ST.TypeInt64);
    EmitPrimitive(ST.TypeByte);
    EmitPrimitive(ST.TypeBoolean);
  end;
  if FUnit <> nil then
  begin
    EmitTypesFromBlock(FUnit.IntfBlock);
    EmitTypesFromBlock(FUnit.ImplBlock);
    GIList := FUnit.GenericInstances;
  end
  else
  begin
    EmitTypesFromBlock(FProgram.Block);
    GIList := FProgram.GenericInstances;
  end;
  for I := 0 to GIList.Count - 1 do
  begin
    GI := TGenericInstance(GIList.Items[I]);
    if (GI.TypeDesc <> nil) and (GI.TypeDesc.Kind = tyClass) then
      EmitTypeDesc(GI.TypeDesc);
  end;
  { Facts path: parameter/local types are often anonymous (e.g. an
    open-array param 'array of Integer') and never appear in TypeDecls,
    so emit every frame slot's type here.  EmitTypeDesc dedupes against
    types already written above. }
  EmitFactsTypes();
end;

procedure TOPDFEmitter.EmitFactsTypes;
var
  I, J: Integer;
  F: TDbgFunc;
  V: TDbgVar;
begin
  if FFacts = nil then Exit;
  for I := 0 to FFacts.Funcs.Count - 1 do
  begin
    F := TDbgFunc(FFacts.Funcs.Items[I]);
    for J := 0 to F.Vars.Count - 1 do
    begin
      V := TDbgVar(F.Vars.Items[J]);
      if V.TypeDesc <> nil then
        EmitTypeDesc(V.TypeDesc);
    end;
  end;
end;

procedure TOPDFEmitter.EmitGlobalVarsFromList(AList: TObjectList);
var
  I, J: Integer;
  V: TVarDecl;
begin
  for I := 0 to AList.Count - 1 do
  begin
    V := TVarDecl(AList.Items[I]);
    if not V.IsGlobal then Continue;
    for J := 0 to V.Names.Count - 1 do
      EmitGlobalVar(V.Names.Strings[J], V.ResolvedType);
  end;
end;

{ Static (class-level) variables are shared global pointer/value slots, not
  instance fields, so they are not in any block's var-decl list and EmitFields
  (instance fields only) skips them.  Emit one recGlobalVar per IsClassVar field
  under its mangled ClassVarEmitName so a debugger can print TFoo.FInstance. }
procedure TOPDFEmitter.EmitStaticVarsFromBlock(ABlock: TBlock);
var
  I, K, N: Integer;
  TD:      TTypeDecl;
  Flds:    TObjectList;
  FDecl:   TFieldDecl;
  Nm:      string;
begin
  if ABlock = nil then Exit;
  for I := 0 to ABlock.TypeDecls.Count - 1 do
  begin
    TD := TTypeDecl(ABlock.TypeDecls.Items[I]);
    Flds := nil;
    if TD.Def is TClassTypeDef then
      Flds := TClassTypeDef(TD.Def).Fields
    else if TD.Def is TRecordTypeDef then
      Flds := TRecordTypeDef(TD.Def).Fields;
    if Flds = nil then Continue;
    for K := 0 to Flds.Count - 1 do
    begin
      FDecl := TFieldDecl(Flds.Items[K]);
      if not FDecl.IsClassVar then Continue;
      for N := 0 to FDecl.Names.Count - 1 do
      begin
        if (FDecl.ClassVarEmitName <> '') and (FDecl.Names.Count = 1) then
          Nm := FDecl.ClassVarEmitName
        else
          Continue;  { multi-name static vars carry no per-name emit label yet }
        EmitGlobalVar(Nm, FDecl.ResolvedType);
      end;
    end;
  end;
end;

procedure TOPDFEmitter.EmitGlobalVars;
begin
  if FUnit <> nil then
  begin
    EmitGlobalVarsFromList(FUnit.IntfBlock.Decls);
    EmitGlobalVarsFromList(FUnit.ImplBlock.Decls);
    EmitStaticVarsFromBlock(FUnit.IntfBlock);
    EmitStaticVarsFromBlock(FUnit.ImplBlock);
  end
  else if FProgram <> nil then
  begin
    EmitGlobalVarsFromList(FProgram.Block.Decls);
    EmitStaticVarsFromBlock(FProgram.Block);
  end;
end;

procedure TOPDFEmitter.SetFacts(AFacts: TDbgFacts);
begin
  FFacts := AFacts;
end;

procedure TOPDFEmitter.EmitFactParameter(AVar: TDbgVar; var ADeclIdx: Integer);
var
  CName: string;
  RecSize: Integer;
begin
  if AVar.TypeDesc <> nil then
    CName := CanonicalName(AVar.TypeDesc)
  else
    CName := 'Pointer';
  RecSize := 9 + Length(AVar.Name);
  L('');
  L('    # recParameter: ' + AVar.Name);
  EmitRecHdr(REC_PARAMETER, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  if AVar.IsVarParam then
    L('    .byte 1  # IsVar')
  else
    L('    .byte 0  # IsVar');
  if AVar.IsConstParam then
    L('    .byte 1  # IsConst')
  else
    L('    .byte 0  # IsConst');
  L('    .byte 0  # IsOut');
  EmitNameLen(AVar.Name);
  EmitNameData(AVar.Name);
  ADeclIdx := ADeclIdx + 1;
end;

procedure TOPDFEmitter.EmitFactLocalVar(AVar: TDbgVar; AScopeID: Integer;
  var ADeclIdx: Integer);
var
  CName: string;
  RecSize: Integer;
begin
  if AVar.TypeDesc <> nil then
    CName := CanonicalName(AVar.TypeDesc)
  else
    CName := 'Pointer';
  RecSize := 15 + Length(AVar.Name);
  { Open-array locals carry an extra trailing SmallInt: the companion
    '_high' slot offset.  Account for it in the record size. }
  if AVar.IsOpenArray then
    RecSize := RecSize + 2;
  L('');
  L('    # recLocalVar: ' + AVar.Name + ' (rbp' +
    IntToStr(AVar.RbpOffset) + ')');
  EmitRecHdr(REC_LOCALVAR, RecSize);
  L('    .int  ' + IntToStr(GetOrAllocTypeID(CName)) + '  # TypeID');
  L('    .int  ' + IntToStr(AScopeID) + '  # ScopeID');
  if AVar.IsOpenArray then
    L('    .byte ' + IntToStr(LOC_OPENARRAY) + '  # LocationExpr (open-array)')
  else if AVar.Indirect then
    L('    .byte ' + IntToStr(LOC_RBP_INDIRECT) +
      '  # LocationExpr (RBP-relative indirect)')
  else
    L('    .byte ' + IntToStr(LOC_RBP) + '  # LocationExpr (RBP-relative)');
  L('    .word ' + IntToStr(ADeclIdx) + '  # DeclIndex');
  EmitNameLen(AVar.Name);
  L('    .word ' + IntToStr(AVar.RbpOffset) + '  # LocationData (RBP offset)');
  if AVar.IsOpenArray then
    L('    .word ' + IntToStr(AVar.HighRbpOffset) +
      '  # CompanionData (_high RBP offset)');
  EmitNameData(AVar.Name);
  ADeclIdx := ADeclIdx + 1;
end;

{ Facts-driven scopes: exact LowPC/HighPC from codegen labels, every frame
  slot with its real %rbp offset (parameters get BOTH a recParameter for
  signature info and a recLocalVar so the debugger can locate the value),
  and one recLineInfo per STATEMENT label — line breakpoints and stepping
  work at statement granularity. }
procedure TOPDFEmitter.EmitFunctionScopesFromFacts;
var
  I, J, ScopeID, DeclIdx, ParamIdx, RecSize: Integer;
  F: TDbgFunc;
  V: TDbgVar;
  LineF: TDbgLine;
  LineFile: string;
begin
  ScopeID := 0;
  DeclIdx := 0;
  for I := 0 to FFacts.Funcs.Count - 1 do
  begin
    F := TDbgFunc(FFacts.Funcs.Items[I]);
    ScopeID := ScopeID + 1;

    RecSize := 24 + Length(F.SymbolName);
    L('');
    L('    # recFunctionScope: ' + F.SymbolName);
    EmitRecHdr(REC_FUNCSCOPE, RecSize);
    L('    .int  ' + IntToStr(ScopeID) + '  # ScopeID');
    L('    .quad ' + F.SymbolName + '  # LowPC');
    if F.EndLabel <> '' then
      L('    .quad ' + F.EndLabel + '  # HighPC (exact end label)')
    else
      L('    .quad 0  # HighPC (no end label recorded)');
    L('    .word ' + IntToStr(DeclIdx) + '  # DeclIndex');
    EmitStrField(F.SymbolName);
    DeclIdx := DeclIdx + 1;

    ParamIdx := 0;
    for J := 0 to F.Vars.Count - 1 do
    begin
      V := TDbgVar(F.Vars.Items[J]);
      if V.IsParam then
        EmitFactParameter(V, ParamIdx);
    end;
    ParamIdx := 0;
    for J := 0 to F.Vars.Count - 1 do
    begin
      V := TDbgVar(F.Vars.Items[J]);
      EmitFactLocalVar(V, ScopeID, ParamIdx);
    end;

    { Per-function source file: unit functions carry their own .pas path
      (recorded by the backend at emission time) so break file:line works
      inside units; empty means the program's main source file. }
    if F.SourceFile <> '' then
      LineFile := F.SourceFile
    else
      LineFile := FSourceFile;
    RecSize := 16 + Length(LineFile);
    for J := 0 to F.Lines.Count - 1 do
    begin
      LineF := TDbgLine(F.Lines.Items[J]);
      L('');
      L('    # recLineInfo: line ' + IntToStr(LineF.Line) + ' in ' + F.SymbolName);
      EmitRecHdr(REC_LINEINFO, RecSize);
      L('    .quad ' + LineF.LabelName + '  # Address (statement label)');
      L('    .int  ' + IntToStr(LineF.Line) + '  # LineNumber');
      L('    .word ' + IntToStr(LineF.Col) + '  # ColumnNumber');
      EmitStrField(LineFile);
    end;
  end;
end;

procedure TOPDFEmitter.EmitFunctionScopes;
var
  I, J, ScopeID, DeclIdx: Integer;
  M: TMethodDecl;
  Decls: TObjectList;
  Labels: TStringList;
  NextLabel: string;
  TD: TTypeDecl;
  CD: TClassTypeDef;
  RD: TRecordTypeDef;
begin
  { Gather every function with a body: standalone procedures/functions from
    ProcDecls, plus class and record METHODS — after semantic analysis the
    implementation bodies live on the type declarations' method lists (the
    ProcDecls impl entries are body-less matching stubs).  Without this walk
    no method — destructors included — ever got a scope record. }
  if FFacts <> nil then
  begin
    EmitFunctionScopesFromFacts();
    Exit;
  end;
  { Non-facts (approximate AST-walk) path is whole-program only.  Per-unit
    incremental compilation only embeds OPDF when the backend produced exact
    debug facts (native); the QBE backend produces none, so a unit-mode
    emitter without facts emits no function scopes (acceptable: native is the
    debug backend, see CLAUDE.md). }
  if FProgram = nil then Exit;
  Decls  := TObjectList.Create(False);
  Labels := TStringList.Create();
  try
    for I := 0 to FProgram.Block.ProcDecls.Count - 1 do
    begin
      M := TMethodDecl(FProgram.Block.ProcDecls.Items[I]);
      if M.IsExternal or (M.Body = nil) then Continue;
      Decls.Add(M);
      Labels.Add(FuncLabel(M));
    end;
    for I := 0 to FProgram.Block.TypeDecls.Count - 1 do
    begin
      TD := TTypeDecl(FProgram.Block.TypeDecls.Items[I]);
      if TD.Def is TClassTypeDef then
      begin
        CD := TClassTypeDef(TD.Def);
        for J := 0 to CD.Methods.Count - 1 do
        begin
          M := TMethodDecl(CD.Methods.Items[J]);
          if M.IsExternal or (M.Body = nil) then Continue;
          Decls.Add(M);
          if M.OwnerTypeName <> '' then
            Labels.Add(FuncLabel(M))
          else
            Labels.Add(TD.Name + '_' + M.Name);
        end;
      end
      else if TD.Def is TRecordTypeDef then
      begin
        RD := TRecordTypeDef(TD.Def);
        if RD.Methods <> nil then
          for J := 0 to RD.Methods.Count - 1 do
          begin
            M := TMethodDecl(RD.Methods.Items[J]);
            if M.IsExternal or (M.Body = nil) then Continue;
            Decls.Add(M);
            if M.OwnerTypeName <> '' then
              Labels.Add(FuncLabel(M))
            else
              Labels.Add(TD.Name + '_' + M.Name);
          end;
      end;
    end;

    ScopeID := 0;
    DeclIdx := 0;
    for I := 0 to Decls.Count - 1 do
    begin
      M := TMethodDecl(Decls.Items[I]);
      ScopeID := ScopeID + 1;
      NextLabel := '';
      if I + 1 < Labels.Count then
        NextLabel := Labels.Strings[I + 1];
      EmitFunctionScope(M, ScopeID, DeclIdx, NextLabel, Labels.Strings[I]);
      EmitParameters(M);
      if M.Body <> nil then
        EmitLocalVars(M.Body, ScopeID);
      EmitLineInfoForBlock(M.Body, Labels.Strings[I], Labels.Strings[I]);
      DeclIdx := DeclIdx + 1;
    end;

    { Main program body — emit as a function scope keyed on 'main' }
    if FProgram.Block.Stmts.Count > 0 then
    begin
      ScopeID := ScopeID + 1;
      EmitFunctionScope_Main(ScopeID, DeclIdx);
    end;
  finally
    Labels.Free();
    Decls.Free();
  end;
end;

procedure TOPDFEmitter.CollectStmtLines(AStmt: TASTStmt; ALines: TStringList);
var
  I: Integer;
  Key: string;
begin
  if AStmt = nil then Exit;
  if AStmt.Line > 0 then
  begin
    Key := IntToStr(AStmt.Line);
    if ALines.IndexOf(Key) < 0 then
      ALines.AddObject(Key, TObject(PtrUInt(AStmt.Col)));
  end;
  if AStmt is TCompoundStmt then
  begin
    for I := 0 to TCompoundStmt(AStmt).Stmts.Count - 1 do
      CollectStmtLines(TASTStmt(TCompoundStmt(AStmt).Stmts.Items[I]), ALines);
  end
  else if AStmt is TIfStmt then
  begin
    CollectStmtLines(TIfStmt(AStmt).ThenStmt, ALines);
    CollectStmtLines(TIfStmt(AStmt).ElseStmt, ALines);
  end
  else if AStmt is TWhileStmt then
    CollectStmtLines(TWhileStmt(AStmt).Body, ALines)
  else if AStmt is TRepeatStmt then
    CollectStmtLines(TRepeatStmt(AStmt).Body, ALines)
  else if AStmt is TForStmt then
    CollectStmtLines(TForStmt(AStmt).Body, ALines)
  else if AStmt is TForInStmt then
    CollectStmtLines(TForInStmt(AStmt).Body, ALines)
  else if AStmt is TTryFinallyStmt then
  begin
    CollectStmtLines(TTryFinallyStmt(AStmt).TryBody, ALines);
    CollectStmtLines(TTryFinallyStmt(AStmt).FinallyBody, ALines);
  end
  else if AStmt is TTryExceptStmt then
  begin
    CollectStmtLines(TTryExceptStmt(AStmt).TryBody, ALines);
    CollectStmtLines(TTryExceptStmt(AStmt).ExceptBody, ALines);
  end
  else if AStmt is TCaseStmt then
  begin
    for I := 0 to TCaseStmt(AStmt).Branches.Count - 1 do
      CollectStmtLines(TCaseBranch(TCaseStmt(AStmt).Branches.Items[I]).Stmt, ALines);
    CollectStmtLines(TCaseStmt(AStmt).ElseStmt, ALines);
  end;
end;

procedure TOPDFEmitter.EmitLineInfoForBlock(ABlock: TBlock;
  const AFuncLabel, AFuncName: string);
var
  Lines: TStringList;
  I, LineNum, ColNum, RecSize: Integer;
begin
  Lines := TStringList.Create();
  try
    for I := 0 to ABlock.Stmts.Count - 1 do
      CollectStmtLines(TASTStmt(ABlock.Stmts.Items[I]), Lines);
    if Lines.Count = 0 then Exit;
    RecSize := 16 + Length(FSourceFile);
    for I := 0 to Lines.Count - 1 do
    begin
      LineNum := StrToInt(Lines.Strings[I]);
      ColNum := Integer(PtrUInt(Lines.Objects[I]));
      L('');
      L('    # recLineInfo: line ' + Lines.Strings[I] + ' in ' + AFuncName);
      EmitRecHdr(REC_LINEINFO, RecSize);
      L('    .quad ' + AFuncLabel + '  # Address (function start; per-stmt addr needs QBE label support)');
      L('    .int  ' + IntToStr(LineNum) + '  # LineNumber');
      L('    .word ' + IntToStr(ColNum) + '  # ColumnNumber');
      EmitStrField(FSourceFile);
    end;
  finally
    Lines.Free();
  end;
end;

procedure TOPDFEmitter.EmitLineInfoForScope(AMethod: TMethodDecl);
begin
  if AMethod.Body = nil then Exit;
  EmitLineInfoForBlock(AMethod.Body, FuncLabel(AMethod), AMethod.Name);
end;

procedure TOPDFEmitter.PatchTotalRecords;
begin
  { Stream-terminated mode: TotalRecords stays 0.  Readers (pdr) ignore the
    field and read records until section EOF, skipping any subsequent 32-byte
    'OPDF' headers from concatenated per-unit blocks.  Patching a real count
    here would be wrong once the linker concatenates sections, so this is a
    deliberate no-op. }
end;

procedure TOPDFEmitter.PatchUnitDirRecordCount;
begin
  { RecordCount for the unit = all records except the directory record itself }
  if FUnitDirRecCountIdx >= 0 then
    FOutput.Strings[FUnitDirRecCountIdx] := '    .int  ' + IntToStr(FRecordCount - 1) +
                                           '  # RecordCount';
end;

procedure TOPDFEmitter.DoEmit;
begin
  if FDone then Exit;
  FDone := True;
  EmitSection();
  EmitHeader();
  { recUnitDirectory is emitted ONLY by the program object (pdr ignores it).
    Units omit it; their records are read in stream-terminated mode. }
  if FProgram <> nil then
    EmitUnitDirectory();
  EmitAllTypes();
  EmitGlobalVars();
  EmitConstants();
  { recRuntimeHelper records are emitted ONLY by the program object (one set
    per binary) — the RTL release routines are global symbols, not per-unit. }
  if FProgram <> nil then
    EmitRuntimeHelpers();
  EmitFunctionScopes();
  PatchTotalRecords();
  PatchUnitDirRecordCount();
end;

procedure TOPDFEmitter.EmitToFile(const AFileName: string);
begin
  DoEmit();
  FOutput.SaveToFile(AFileName);
end;

function TOPDFEmitter.GetOutput: string;
begin
  DoEmit();
  Result := FOutput.Text;
end;

end.
