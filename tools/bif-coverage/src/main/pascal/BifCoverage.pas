{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
}

(*
  BifCoverage - verifies every TAST{Stmt,Expr} subclass declared in
  uAST.pas is wired into the encoder/decoder dispatch in
  uUnitInterfaceIO.pas, AND that every public field on each such class
  is referenced from both sides.

  It ALSO covers the .bif interface-container types in
  uUnitInterface.pas (TUnitInterface, TRoutineSig, TConstEntry,
  TVarEntry) plus TMethodParam (uAST.pas).  Their fields are
  hand-serialised across WriteMeta / EncodeMethodSig / WriteRoutines /
  … rather than via the per-node AST dispatch, so they are checked
  against the encoder-side and decoder-side text of uUnitInterfaceIO.pas
  as two haystacks: a field counts as covered when its `.Field`
  identifier appears in both.  Catches the class of bug where a field on
  one of those types is dropped from one side of the META / routine
  serialiser (e.g. ResolvedEmitName, VTableSlot, ImplUsedUnits,
  HasInitialization, a TMethodParam default-value flag).

  Catches the two failure modes from docs/extending-ast.adoc:
    1. New node class added but never wired into Encode/Read dispatch.
    2. New public field added but forgotten from one side of the
       encoder/decoder pair - surfaces later as a stage-2 != stage-3
       fixpoint failure with a length-prefix corruption message.

  Field exemption: trailing "no-bif" marker on the field's source line
  suppresses the warning. Use for fields populated by semantic only, or
  container fields rebuilt via Add* mutators on decode.

  Exit codes: 0 = clean, 1 = coverage gap(s), 2 = I/O error.
*)

program BifCoverage;

uses
  SysUtils, Classes, Contnrs, Generics.Collections, strutils, uStrCompat;

const
  AST_REL          = 'compiler/src/main/pascal/uAST.pas';
  IO_REL           = 'compiler/src/main/pascal/uUnitInterfaceIO.pas';
  IFACE_REL        = 'compiler/src/main/pascal/uUnitInterface.pas';
  COMPILER_ID_REL  = 'compiler/src/main/pascal/uCompilerId.pas';
  ROOT_REL         = 'project.xml';
  STATUS_REL       = 'tools/bif-coverage/bif-coverage.status';
  COMPILER_ID_PREFIX = 'blaise-';

  { The .bif interface-container types in uUnitInterface.pas whose
    serialised fields are cross-checked against the hand-written
    encoder/decoder in uUnitInterfaceIO.pas.  These carry the META,
    routine and type-entry data that the AST-dispatch mechanism does
    NOT see.  TInlineBody / TGenericBody / TUnitInterface's private
    index fields are intentionally excluded: index lists are rebuilt
    from the serialised data on read, and the inline/generic bodies
    round-trip as AST blocks already covered by the AST mechanism.

    TMethodParam lives in uAST.pas (it is a TASTNode) but is NOT a
    TASTStmt/TASTExpr, so the AST mechanism skips it; its fields are
    hand-serialised via EncodeMethodSig / EncodeParamFlags /
    WriteRoutines, so it is checked here against the IO haystacks. }
  IFACE_TYPE_COUNT = 4;

var
  GRoot:            string;
  GAstFile:         string;
  GIoFile:          string;
  GIfaceFile:       string;
  GCompilerIdFile:  string;
  GRootProject:     string;
  GStatusFile:      string;
  GIfaceTypes:      array[0 .. IFACE_TYPE_COUNT - 1] of string;

(* Walk up from CWD looking for a directory that contains both
   `compiler/src/main/pascal/uAST.pas` and `project.xml`. Lets the
   binary be invoked from any subdir of the repo - tests run from
   compiler/, dev runs from tools/bif-coverage/, etc. *)
function FindProjectRoot(): string;
var
  Dir, Parent: string;
  I: Integer;
begin
  Dir := GetCurrentDir();
  for I := 0 to 6 do
  begin
    if FileExists(IncludeTrailingPathDelimiter(Dir) + AST_REL) and
       FileExists(IncludeTrailingPathDelimiter(Dir) + ROOT_REL) then
      Exit(IncludeTrailingPathDelimiter(Dir));
    Parent := ExtractFileDir(Dir);
    if (Parent = '') or (Parent = Dir) then Break;
    Dir := Parent;
  end;
  Result := '';
end;

type
  TASTClass = class
  public
    Name:   string;
    Parent: string;
    Fields:     TList<String>;    { field names }
    FieldLines: TList<Integer>;   { parallel: source line per field, 0 if unknown }
    LineNo: Integer;
    SrcName: string;   { basename of the source file the class came from,
                         for [new]/header location reporting }
    constructor Create;
  end;

  TIOBlock = class
  public
    ClsName: string;
    Body:    string;
    constructor Create;
  end;

var
  GASTNames:    TStringList;   { class names, parallel index with GASTObjs }
  GASTObjs:     TObjectList;   { TASTClass instances }
  GEncodeNames: TStringList;
  GEncodeObjs:  TObjectList;
  GDecodeNames: TStringList;
  GDecodeObjs:  TObjectList;
  GErrors:      Integer;

  { Interface-container types from uUnitInterface.pas (parallel lists),
    plus the encoder-side and decoder-side text of uUnitInterfaceIO.pas
    used as two haystacks for the loose `.Field` substring check. }
  GIfaceNames:    TStringList;
  GIfaceObjs:     TObjectList;   { TASTClass instances (reused for fields) }
  GIoEncodeText:  string;
  GIoDecodeText:  string;

constructor TASTClass.Create;
begin
  inherited Create();
  Fields     := TList<String>.Create;
  FieldLines := TList<Integer>.Create;
end;

constructor TIOBlock.Create;
begin
  inherited Create();
end;

function IsIdentStart(C: Integer): Boolean;
begin
  Result := ((C >= Ord('A')) and (C <= Ord('Z'))) or
            ((C >= Ord('a')) and (C <= Ord('z'))) or
            (C = Ord('_'));
end;

function IsIdentCont(C: Integer): Boolean;
begin
  Result := IsIdentStart(C) or ((C >= Ord('0')) and (C <= Ord('9')));
end;

function IsSpace(C: Integer): Boolean;
begin
  Result := (C = 32) or (C = 9) or (C = 13) or (C = 10);
end;

(* Strip a single source line of trailing comments (`// ...`), inline
   block comments (`{ ... }` if closed on same line), and string
   literals (replace contents with spaces). For multi-line block
   comments the caller tracks state via InBlockComment. *)
function StripLine(const ALine: string; var InBlockComment: Boolean): string;
var
  I, Len, C: Integer;
  Tail: string;
begin
  Result := '';
  Len := Length(ALine);
  I := 0;
  while I < Len do
  begin
    C := StrAt(ALine, I);
    if InBlockComment then
    begin
      if C = Ord('}') then InBlockComment := False;
      Result := Result + ' ';
      Inc(I);
      Continue;
    end;
    if (C = Ord('/')) and (I + 1 < Len) and (StrAt(ALine, I + 1) = Ord('/')) then
      Break;
    if C = Ord('{') then
    begin
      (* preserve `{ no-bif }` marker verbatim so field-exemption works *)
      Tail := Copy(ALine, I, 10);
      if Tail = '{ no-bif }' then
      begin
        Result := Result + Tail;
        Inc(I, 10);
        Continue;
      end;
      InBlockComment := True;
      Result := Result + ' ';
      Inc(I);
      Continue;
    end;
    if C = Ord('''') then
    begin
      Result := Result + ' ';
      Inc(I);
      while (I < Len) and (StrAt(ALine, I) <> Ord('''')) do
      begin
        Result := Result + ' ';
        Inc(I);
      end;
      if I < Len then
      begin
        Result := Result + ' ';
        Inc(I);
      end;
      Continue;
    end;
    Result := Result + Chr(C);
    Inc(I);
  end;
end;

function LoadLines(const APath: string): TStringList;
begin
  Result := TStringList.Create;
  Result.LoadFromFile(APath);
end;

(* Read a Pascal identifier starting at APos in S, advancing APos past
   it. Returns empty string if APos is not on an identifier start. *)
function ReadIdent(const S: string; var APos: Integer): string;
var
  Start, Len, C: Integer;
begin
  Result := '';
  Len := Length(S);
  while (APos < Len) and IsSpace(StrAt(S, APos)) do Inc(APos);
  if APos >= Len then Exit;
  C := StrAt(S, APos);
  if not IsIdentStart(C) then Exit;
  Start := APos;
  while (APos < Len) and IsIdentCont(StrAt(S, APos)) do Inc(APos);
  Result := Copy(S, Start, APos - Start);
end;

function ASTAt(I: Integer): TASTClass;
begin
  Result := TASTClass(GASTObjs.Get(I));
end;

(* Line number for a field by index in Cls.Fields, recovered from the
   parallel Objects[] slot stamped by ScanAST(). Falls back to the class
   header line when zero. *)
function FieldLineNo(ACls: TASTClass; AFieldIndex: Integer): Integer;
begin
  Result := ACls.FieldLines.Get(AFieldIndex);
  if Result = 0 then Result := ACls.LineNo;
end;

function FindASTClass(const AName: string): TASTClass;
var
  Idx: Integer;
begin
  Idx := GASTNames.IndexOf(AName);
  if Idx < 0 then Result := nil
  else Result := ASTAt(Idx);
end;

function FindBlock(ANames: TStringList; AObjs: TObjectList;
  const AName: string): TIOBlock;
var
  Idx: Integer;
begin
  Idx := ANames.IndexOf(AName);
  if Idx < 0 then Result := nil
  else Result := TIOBlock(AObjs.Get(Idx));
end;

(* Extract a class-header line's components: name, parent, and whether
   the declaration has a body. Returns False if the line is not a class
   declaration. Handles both `T = class(P)` (with body) and
   `T = class(P);` (no body, forward decl or empty alias). *)
function ParseClassHeader(const ALine: string;
  var AName, AParent: string; var AHasBody: Boolean): Boolean;
var
  P, Len: Integer;
  Tok: string;
begin
  Result := False;
  AHasBody := False;
  AName := '';
  AParent := '';
  P := 0;
  Len := Length(ALine);
  while (P < Len) and IsSpace(StrAt(ALine, P)) do Inc(P);
  Tok := ReadIdent(ALine, P);
  if (Length(Tok) < 2) or (StrAt(Tok, 0) <> Ord('T')) then Exit;
  AName := Tok;
  while (P < Len) and IsSpace(StrAt(ALine, P)) do Inc(P);
  if (P >= Len) or (StrAt(ALine, P) <> Ord('=')) then Exit;
  Inc(P);
  while (P < Len) and IsSpace(StrAt(ALine, P)) do Inc(P);
  Tok := ReadIdent(ALine, P);
  if not SameText(Tok, 'class') then Exit;
  while (P < Len) and IsSpace(StrAt(ALine, P)) do Inc(P);
  if (P < Len) and (StrAt(ALine, P) = Ord('(')) then
  begin
    Inc(P);
    AParent := ReadIdent(ALine, P);
    while (P < Len) and (StrAt(ALine, P) <> Ord(')')) do Inc(P);
    if P < Len then Inc(P);
  end;
  while (P < Len) and IsSpace(StrAt(ALine, P)) do Inc(P);
  (* body if line does NOT end with `;` on this line *)
  AHasBody := (P >= Len) or (StrAt(ALine, P) <> Ord(';'));
  Result := True;
end;

(* Strip leading [Attr] (one or more bracketed FPC-style attributes) and
   return the remainder. Pure helper - the attribute survives StripLine()
   (it's not a comment) but precedes the field name. *)
function StripAttrs(const ALine: string): string;
var
  I, Len, C: Integer;
begin
  Result := ALine;
  Len := Length(Result);
  I := 0;
  while (I < Len) and IsSpace(StrAt(Result, I)) do Inc(I);
  while (I < Len) and (StrAt(Result, I) = Ord('[')) do
  begin
    while (I < Len) and (StrAt(Result, I) <> Ord(']')) do Inc(I);
    if I < Len then Inc(I);
    while (I < Len) and IsSpace(StrAt(Result, I)) do Inc(I);
  end;
  Result := Copy(Result, I, Length(Result) - I);
end;

(* Recognise a public-field declaration line. Pattern:
   `Name: Type;`  or `Name1, Name2: Type;` (the latter is rare but
   supported). The caller is responsible for only invoking this inside
   the public section. Returns the comma-separated list of field names,
   or empty if the line is not a field declaration. *)
function ParseFieldNames(const ALine: string): TList<String>;
var
  Stripped, Tok: string;
  P, Len: Integer;
begin
  Result := TList<String>.Create;
  Stripped := StripAttrs(ALine);
  P := 0;
  Len := Length(Stripped);
  while True do
  begin
    Tok := ReadIdent(Stripped, P);
    if Tok = '' then
    begin
      Result.Clear();
      Exit;
    end;
    Result.Add(Tok);
    while (P < Len) and IsSpace(StrAt(Stripped, P)) do Inc(P);
    if (P < Len) and (StrAt(Stripped, P) = Ord(',')) then
    begin
      Inc(P);
      Continue;
    end;
    Break;
  end;
  (* Must be followed by `:` then a type, then a `;` somewhere. *)
  if (P >= Len) or (StrAt(Stripped, P) <> Ord(':')) then
  begin
    Result.Clear();
    Exit;
  end;
end;

(* Skip non-field declarations inside a class body. Returns True if the
   line is structural (visibility modifier, method, property, end of
   class) and the caller should advance without recording fields. *)
function IsStructuralLine(const ALine: string; var AInPublic: Boolean;
  var AIsEnd: Boolean): Boolean;
var
  P: Integer;
  Tok: string;
begin
  AIsEnd := False;
  Result := False;
  P := 0;
  Tok := ReadIdent(ALine, P);
  if Tok = '' then Exit(True);
  if SameText(Tok, 'end') then begin AIsEnd := True; Exit(True); end;
  if SameText(Tok, 'public')    then begin AInPublic := True;  Exit(True); end;
  if SameText(Tok, 'published') then begin AInPublic := True;  Exit(True); end;
  if SameText(Tok, 'private')   then begin AInPublic := False; Exit(True); end;
  if SameText(Tok, 'protected') then begin AInPublic := False; Exit(True); end;
  if SameText(Tok, 'strict')    then Exit(True);
  if SameText(Tok, 'constructor') or SameText(Tok, 'destructor') or
     SameText(Tok, 'procedure')   or SameText(Tok, 'function')   or
     SameText(Tok, 'property')    or SameText(Tok, 'class')      then
    Exit(True);
end;

(* True when AAllow is nil (accept every class) or AName appears in
   the allow-list. Lets the same scan run over uAST.pas (all classes)
   and uUnitInterface.pas (only the target .bif container types). *)
function ClassAccepted(AAllow: TList<String>; const AName: string): Boolean;
begin
  Result := (AAllow = nil) or (AAllow.IndexOf(AName) >= 0);
end;

(* Generic `T = class ... public ... end;` scanner. Records every
   accepted class header and its public field names (with source line
   numbers) into ANames / AObjs. The `no-bif` trailing-marker
   exemption and the StripLine/ParseClassHeader/ParseFieldNames helpers
   are shared with the AST scan. When AAllow is non-nil only classes
   named in it are recorded. *)
procedure ScanClassFile(const APath: string;
  ANames: TStringList; AObjs: TObjectList; AAllow: TList<String>);
var
  Lines: TStringList;
  InBlockComment, InPublic, InClassBody, HasBody, IsEnd, Recording: Boolean;
  I, J: Integer;
  Raw, Stripped, Trimmed, Name, Parent, SrcName: string;
  Cls: TASTClass;
  FieldNames: TList<String>;
begin
  SrcName := ExtractFileName(APath);
  Lines := LoadLines(APath);
  begin
    InBlockComment := False;
    InClassBody := False;
    InPublic := True;
    Recording := False;
    Cls := nil;
    for I := 0 to Lines.Count - 1 do
    begin
      Raw := Lines.Strings[I];
      Stripped := StripLine(Raw, InBlockComment);
      Trimmed := Trim(Stripped);
      if Trimmed = '' then Continue;

      if not InClassBody then
      begin
        if ParseClassHeader(Trimmed, Name, Parent, HasBody) then
        begin
          Recording := ClassAccepted(AAllow, Name);
          if Recording then
          begin
            Cls := TASTClass.Create;
            Cls.Name := Name;
            Cls.Parent := Parent;
            Cls.LineNo := I + 1;
            Cls.SrcName := SrcName;
            ANames.Add(Name);
            AObjs.Add(Cls);
          end
          else
            Cls := nil;
          if HasBody then
          begin
            InClassBody := True;
            InPublic := True;
          end;
        end;
        Continue;
      end;

      if IsStructuralLine(Trimmed, InPublic, IsEnd) then
      begin
        if IsEnd then
        begin
          InClassBody := False;
          Cls := nil;
        end;
        Continue;
      end;
      if not Recording then Continue;
      if not InPublic then Continue;
      if Pos('no-bif', Raw) >= 0 then Continue;
      { A `Name: Type` candidate that carries a parenthesis is a
        continuation line of a multi-line method/constructor signature
        (e.g. a wrapped 'ACaseSensitive: Boolean = False);' param), not
        a real field — skip it. Plain public fields never contain (). }
      if (Pos('(', Trimmed) >= 0) or (Pos(')', Trimmed) >= 0) then Continue;
      FieldNames := ParseFieldNames(Trimmed);
      for J := 0 to FieldNames.Count - 1 do
      begin
        Cls.Fields.Add(FieldNames[J]);
        Cls.FieldLines.Add(I + 1);
      end;
    end;
  end;
end;

procedure ScanAST();
begin
  ScanClassFile(GAstFile, GASTNames, GASTObjs, nil);
end;

(* Scan the .bif container types whose fields are hand-serialised in
   uUnitInterfaceIO.pas: the GIfaceTypes from uUnitInterface.pas, plus
   TMethodParam from uAST.pas (an AST node the TASTStmt/TASTExpr
   dispatch deliberately skips).  All land in GIfaceNames / GIfaceObjs
   and are checked against the file-level IO haystacks. *)
procedure ScanInterfaceTypes();
var
  Allow: TList<String>;
  I: Integer;
begin
  Allow := TList<String>.Create;
  for I := 0 to IFACE_TYPE_COUNT - 1 do
    Allow.Add(GIfaceTypes[I]);
  ScanClassFile(GIfaceFile, GIfaceNames, GIfaceObjs, Allow);

  Allow.Clear();
  Allow.Add('TMethodParam');
  ScanClassFile(GAstFile, GIfaceNames, GIfaceObjs, Allow);
end;

function IfaceAt(I: Integer): TASTClass;
begin
  Result := TASTClass(GIfaceObjs.Get(I));
end;

function FindIfaceClass(const AName: string): TASTClass;
var
  Idx: Integer;
begin
  Idx := GIfaceNames.IndexOf(AName);
  if Idx < 0 then Result := nil
  else Result := IfaceAt(Idx);
end;

(* Find the body of `function FName(...)` in a list of stripped source
   lines and return it as one concatenated string. The body spans from
   the first `begin` after the signature to the matching `end;` (depth
   counting on begin/case/record/try). *)
function ExtractFunctionBody(ALines: TList<String>; const AFName: string): string;
var
  I, J, P, Depth: Integer;
  Line, Tok: string;
  InFn, InBody: Boolean;
  Header: string;
begin
  Result := '';
  Header := 'function ' + AFName + '(';
  InFn := False;
  InBody := False;
  Depth := 0;
  for I := 0 to ALines.Count - 1 do
  begin
    Line := ALines[I];
    if not InFn then
    begin
      if (Pos(Header, Line) >= 0) and (Pos('forward', Line) < 0) then
        InFn := True
      else
        Continue;
    end;
    if not InBody then
    begin
      if Pos('begin', Line) >= 0 then
      begin
        InBody := True;
        Depth := 1;
        Result := Result + Line + Chr(10);
        Continue;
      end;
      Continue;
    end;
    (* depth tracking via identifier scan *)
    P := 0;
    while P < Length(Line) do
    begin
      Tok := ReadIdent(Line, P);
      if Tok = '' then
      begin
        if P < Length(Line) then Inc(P);
        Continue;
      end;
      if SameText(Tok, 'begin')  then Inc(Depth)
      else if SameText(Tok, 'case')   then Inc(Depth)
      else if SameText(Tok, 'try')    then Inc(Depth)
      else if SameText(Tok, 'record') then Inc(Depth)
      else if SameText(Tok, 'end')    then
      begin
        Dec(Depth);
        if Depth <= 0 then
        begin
          Result := Result + Copy(Line, 0, P) + Chr(10);
          Exit;
        end;
      end;
    end;
    Result := Result + Line + Chr(10);
  end;
end;

(* Carve EncodeStmt / EncodeExpr body into per-class blocks. Each block
   runs from one `is TFoo` marker to the next (or to end of body). *)
procedure CarveEncodeBlocks(const ABody: string;
  ANames: TStringList; AObjs: TObjectList);
var
  MarkPositions: TList<String>;
  MarkNames: TList<String>;
  P, Len, Save: Integer;
  Tok: string;
  Blk: TIOBlock;
  I, EndPos, StartPos: Integer;
begin
  MarkPositions := TList<String>.Create;
  MarkNames := TList<String>.Create;
  begin
    Len := Length(ABody);
    P := 0;
    while P < Len do
    begin
      if (P + 3 <= Len) and (Copy(ABody, P, 3) = 'is ') then
      begin
        if (P = 0) or not IsIdentCont(StrAt(ABody, P - 1)) then
        begin
          Save := P + 3;
          Tok := ReadIdent(ABody, Save);
          if (Length(Tok) > 1) and (StrAt(Tok, 0) = Ord('T')) then
          begin
            MarkPositions.Add(IntToStr(P));
            MarkNames.Add(Tok);
          end;
          P := Save;
          Continue;
        end;
      end;
      Inc(P);
    end;
    for I := 0 to MarkNames.Count - 1 do
    begin
      StartPos := StrToInt(MarkPositions[I]);
      if I < MarkNames.Count - 1 then
        EndPos := StrToInt(MarkPositions[I + 1])
      else
        EndPos := Len;
      Blk := TIOBlock.Create;
      Blk.ClsName := MarkNames[I];
      Blk.Body := Copy(ABody, StartPos, EndPos - StartPos);
      ANames.Add(MarkNames[I]);
      AObjs.Add(Blk);
    end;
  end;
end;

(* Carve ReadStmt / ReadExpr body into per-class blocks. Each block
   starts at a `Tag = ` discriminator and is keyed by the first known
   AST class name appearing inside it. *)
procedure CarveDecodeBlocks(const ABody: string;
  ANames: TStringList; AObjs: TObjectList);
var
  Starts: TList<String>;
  P, Len, I, EndPos, J, Q, StartPos: Integer;
  Block, Tok: string;
  Blk: TIOBlock;
begin
  Starts := TList<String>.Create;
  begin
  Len := Length(ABody);
  P := 0;
  while P + 7 < Len do
  begin
    if Copy(ABody, P, 7) = 'Kind = ' then
    begin
      Starts.Add(IntToStr(P));
      Inc(P, 7);
    end
    else
      Inc(P);
  end;
  for I := 0 to Starts.Count - 1 do
  begin
    StartPos := StrToInt(Starts[I]);
    if I < Starts.Count - 1 then EndPos := StrToInt(Starts[I + 1])
    else EndPos := Len;
    Block := Copy(ABody, StartPos, EndPos - StartPos);
    J := 0;
    while J < Length(Block) do
    begin
      if (StrAt(Block, J) = Ord('T')) and
         ((J = 0) or not IsIdentCont(StrAt(Block, J - 1))) then
      begin
        Q := J;
        Tok := ReadIdent(Block, Q);
        if FindASTClass(Tok) <> nil then
        begin
          Blk := TIOBlock.Create;
          Blk.ClsName := Tok;
          Blk.Body := Block;
          ANames.Add(Tok);
          AObjs.Add(Blk);
          Break;
        end;
        J := Q;
      end
      else
        Inc(J);
    end;
  end;
  end;
end;

(* True when ALine begins (after leading whitespace) a decoder-side
   function/procedure - i.e. the boundary between the encoder half and
   the decoder half of uUnitInterfaceIO.pas's implementation. The
   decoder helpers all sort after every Encode*/Write* routine in
   source order, so the first such line splits the file cleanly. *)
function IsDecoderBoundary(const ALine: string): Boolean;
var
  P: Integer;
  Kw, Nm: string;
begin
  Result := False;
  P := 0;
  Kw := ReadIdent(ALine, P);
  if (not SameText(Kw, 'function')) and (not SameText(Kw, 'procedure')) then
    Exit;
  Nm := ReadIdent(ALine, P);
  if (Pos('Read', Nm) = 0) or (Pos('Decode', Nm) = 0) or
     (Pos('Split', Nm) = 0) or SameText(Nm, 'LoadEnumMembers') or
     SameText(Nm, 'SkipWhitespace') or SameText(Nm, 'IsWhitespaceOrd') or
     SameText(Nm, 'IsUpperOrd') or SameText(Nm, 'IsDigitOrd') then
    Result := True;
end;

procedure ScanIO();
var
  Raw: TStringList;
  Cleaned: TList<String>;
  I: Integer;
  InBlockComment, InImpl, InDecoder: Boolean;
  Body, Line, Trimmed: string;
  EncSB, DecSB: TStringBuilder;
begin
  Raw := LoadLines(GIoFile);
  Cleaned := TList<String>.Create;
  EncSB := TStringBuilder.Create;
  DecSB := TStringBuilder.Create;
  begin
    InBlockComment := False;
    InImpl := False;
    InDecoder := False;
    for I := 0 to Raw.Count - 1 do
    begin
      Line := StripLine(Raw.Strings[I], InBlockComment);
      Cleaned.Add(Line);
      Trimmed := Trim(Line);
      if not InImpl then
      begin
        if SameText(Trimmed, 'implementation') then InImpl := True;
        Continue;
      end;
      if (not InDecoder) and IsDecoderBoundary(Trimmed) then
        InDecoder := True;
      if InDecoder then DecSB.AppendLine(Line)
                   else EncSB.AppendLine(Line);
    end;
    Body := ExtractFunctionBody(Cleaned, 'EncodeExpr');
    CarveEncodeBlocks(Body, GEncodeNames, GEncodeObjs);
    Body := ExtractFunctionBody(Cleaned, 'EncodeStmt');
    CarveEncodeBlocks(Body, GEncodeNames, GEncodeObjs);
    Body := ExtractFunctionBody(Cleaned, 'ReadExpr');
    CarveDecodeBlocks(Body, GDecodeNames, GDecodeObjs);
    Body := ExtractFunctionBody(Cleaned, 'ReadStmt');
    CarveDecodeBlocks(Body, GDecodeNames, GDecodeObjs);
    GIoEncodeText := EncSB.ToString();
    GIoDecodeText := DecSB.ToString();
  end;
end;

function InheritsFrom(ACls: TASTClass; const ABase: string): Boolean;
var
  Cur: TASTClass;
begin
  Cur := ACls;
  while Cur <> nil do
  begin
    if SameText(Cur.Name, ABase) then Exit(True);
    Cur := FindASTClass(Cur.Parent);
  end;
  Result := False;
end;

(* Read the root project.xml's <version>...</version> body. Returns ''
   if the file or tag isn't readable. *)
function ReadProjectVersion(): string;
var
  Raw: string;
  Lines: TStringList;
  I, OpenP, CloseP: Integer;
  Line: string;
begin
  Result := '';
  if not FileExists(GRootProject) then Exit;
  Lines := TStringList.Create;
  begin
    Lines.LoadFromFile(GRootProject);
    for I := 0 to Lines.Count - 1 do
    begin
      Line := Lines.Strings[I];
      OpenP := Pos('<version>', Line);
      if OpenP < 0 then Continue;
      OpenP := OpenP + 9;
      CloseP := Pos('</version>', Line);
      if CloseP < 0 then Continue;
      Result := Copy(Line, OpenP, CloseP - OpenP);
      Result := Trim(Result);
      Exit;
    end;
  end;
end;

(* Read uCompilerId.pas and pull the string literal assigned to
   COMPILER_ID. Returns '' on failure. *)
function ReadCompilerId(): string;
var
  Lines: TStringList;
  I, Q1, Q2: Integer;
  Line: string;
begin
  Result := '';
  if not FileExists(GCompilerIdFile) then Exit;
  Lines := TStringList.Create;
  begin
    Lines.LoadFromFile(GCompilerIdFile);
    for I := 0 to Lines.Count - 1 do
    begin
      Line := Lines.Strings[I];
      if Pos('COMPILER_ID', Line) < 0 then Continue;
      if Pos('=', Line) < 0 then Continue;
      Q1 := Pos('''', Line);
      if Q1 < 0 then Continue;
      Q2 := Pos('''', Copy(Line, Q1 + 1, Length(Line) - Q1 - 1));
      if Q2 < 0 then Continue;
      Result := Copy(Line, Q1 + 1, Q2);
      Exit;
    end;
  end;
end;

procedure Report(const AMsg: string);
begin
  WriteLn(AMsg);
  Inc(GErrors);
end;

(* Return the 1-based line number in GIoFile of the first reference of
   the form `<ClsName>(...).<FieldName>` (or any line carrying both
   `ClsName` and `.FieldName`). Returns 0 if not found. Used to point
   `[drift]` reports at the stale encoder/decoder line that needs
   removing. *)
(* Encoders use `TFoo(AE).Field`; decoders typically use a local var
   like `IL.Field := ...`. So we look for two distinct patterns and
   only require ClsName context on the encoder side - the decoder
   block is already scoped by AStartLine to the ReadExpr/ReadStmt
   region, where field names are unique enough to grep blindly. *)
function FindIORefLine(const AClsName, AFieldName: string;
  AStartLine: Integer; ARequireClassName: Boolean): Integer;
var
  Lines: TStringList;
  I: Integer;
  Line, Needle: string;
begin
  Result := 0;
  if not FileExists(GIoFile) then Exit;
  Needle := '.' + AFieldName;
  Lines := TStringList.Create;
  begin
    Lines.LoadFromFile(GIoFile);
    for I := AStartLine to Lines.Count - 1 do
    begin
      Line := Lines.Strings[I];
      if Pos(Needle, Line) < 0 then Continue;
      if ARequireClassName and (Pos(AClsName, Line) < 0) then Continue;
      Result := I + 1;
      Exit;
    end;
  end;
end;

(* Find the 0-based line index where the decoder section begins -
   first non-forward `function ReadExpr(` declaration. Cached on first
   call. *)
var
  GDecoderStart: Integer;

function DecoderStartLine(): Integer;
var
  Lines: TStringList;
  I: Integer;
  Line: string;
begin
  if GDecoderStart >= 0 then
  begin
    Result := GDecoderStart;
    Exit;
  end;
  Result := 0;
  if not FileExists(GIoFile) then Exit;
  Lines := TStringList.Create;
  begin
    Lines.LoadFromFile(GIoFile);
    for I := 0 to Lines.Count - 1 do
    begin
      Line := Lines.Strings[I];
      if (Pos('function ReadExpr(', Line) >= 0) and
         (Pos('forward', Line) < 0) then
      begin
        Result := I;
        GDecoderStart := I;
        Exit;
      end;
    end;
  end;
end;

procedure CheckVersion();
var
  ProjVer, CompId, Tail, BaseVer: string;
  DashPos: Integer;
begin
  ProjVer := ReadProjectVersion();
  CompId := ReadCompilerId();
  if ProjVer = '' then
  begin
    Report('  [version] could not read <version> from ' + GRootProject);
    Exit;
  end;
  if CompId = '' then
  begin
    Report('  [version] could not read COMPILER_ID from ' + GCompilerIdFile);
    Exit;
  end;
  if Pos(COMPILER_ID_PREFIX, CompId) <> 0 then
  begin
    Report('  [version] COMPILER_ID ' + CompId +
           ' does not start with expected prefix ' + COMPILER_ID_PREFIX);
    Exit;
  end;
  Tail := Copy(CompId, Length(COMPILER_ID_PREFIX),
               Length(CompId) - Length(COMPILER_ID_PREFIX));
  { Strip -SNAPSHOT suffix from project version for comparison.
    Convention: both project.xml and COMPILER_ID use X.Y.Z-SNAPSHOT. }
  BaseVer := ProjVer;
  DashPos := Pos('-', BaseVer);
  if DashPos >= 0 then
    BaseVer := Copy(BaseVer, 0, DashPos);
  if Pos(BaseVer, Tail) <> 0 then
    Report('  [version] COMPILER_ID ' + CompId +
           ' does not contain base version ' + BaseVer +
           ' (after ' + COMPILER_ID_PREFIX + ' prefix)');
end;

function IsSerialisedClass(ACls: TASTClass): Boolean;
begin
  Result := False;
  if ACls = nil then Exit;
  if SameText(ACls.Name, 'TASTStmt') or SameText(ACls.Name, 'TASTExpr') or
     SameText(ACls.Name, 'TASTNode') then Exit;
  Result := InheritsFrom(ACls, 'TASTStmt') or InheritsFrom(ACls, 'TASTExpr');
end;

(* Bootstrap mode: walk every AST class that descends from TASTStmt or
   TASTExpr, dump each public field as either `serialise` (if found in
   the corresponding encoder block) or `safe` (if not). Outpput goes to
   GStatusFile for hand-curation thereafter. *)
procedure WriteStatus();
var
  Outp: TStringList;
  I, J: Integer;
  Cls: TASTClass;
  Blk: TIOBlock;
  FieldName, State, Header: string;
begin
  Outp := TStringList.Create;
  begin
    Outp.Add('# bif-coverage status - one line per public AST field.');
    Outp.Add('# Format: <TClass>.<Field>  <serialise|safe>');
    Outp.Add('#   serialise  must appear in EncodeStmt/EncodeExpr AND ReadStmt/ReadExpr');
    Outp.Add('#   safe       intentionally not serialised (set by semantic etc.)');
    Outp.Add('# Regenerate from scratch with: bif-coverage --reset');
    Outp.Add('');
    for I := 0 to GASTNames.Count - 1 do
    begin
      Cls := ASTAt(I);
      if not IsSerialisedClass(Cls) then Continue;
      Header := '# ' + Cls.Name + ' (uAST.pas:' + IntToStr(Cls.LineNo) + ')';
      Outp.Add(Header);
      Blk := FindBlock(GEncodeNames, GEncodeObjs, Cls.Name);
      for J := 0 to Cls.Fields.Count - 1 do
      begin
        FieldName := Cls.Fields.Get(J);
        if (Blk <> nil) and (Pos('.' + FieldName, Blk.Body) >= 0) then
          State := 'serialise'
        else
          State := 'safe';
        Outp.Add(Cls.Name + '.' + FieldName + '  ' + State);
      end;
      Outp.Add('');
    end;

    { ----- .bif interface-container types -------------------------
      These fields are hand-serialised across WriteMeta/EncodeMethodSig/
      WriteRoutines/... rather than via the AST dispatch, so they are
      checked against the file-level encoder/decoder haystacks. }
    Outp.Add('# === Interface-container types (uUnitInterface.pas + TMethodParam) ===');
    Outp.Add('#   serialise  must appear in the encoder AND decoder of uUnitInterfaceIO.pas');
    Outp.Add('');
    for I := 0 to GIfaceNames.Count - 1 do
    begin
      Cls := IfaceAt(I);
      Header := '# ' + Cls.Name + ' (' + Cls.SrcName + ':' +
                IntToStr(Cls.LineNo) + ')';
      Outp.Add(Header);
      for J := 0 to Cls.Fields.Count - 1 do
      begin
        FieldName := Cls.Fields.Get(J);
        if Pos('.' + FieldName, GIoEncodeText) >= 0 then
          State := 'serialise'
        else
          State := 'safe';
        Outp.Add(Cls.Name + '.' + FieldName + '  ' + State);
      end;
      Outp.Add('');
    end;

    Outp.SaveToFile(GStatusFile);
    WriteLn('bif-coverage: wrote ' + GStatusFile);
  end;
end;

(* Check mode: read GStatusFile as source of truth and verify against
   live AST + encoder/decoder.
   - AST has a field not in status                       → "new, needs marking"
   - status names a field/class not in AST               → "stale entry"
   - status says `serialise` but encoder/decoder missing → "broken: not encoded/decoded"
   - status says `safe` but encoder references the field → "should be serialise" *)
procedure CheckAgainstStatus();
var
  Status: TStringList;
  I, J, SpacePos: Integer;
  Line, Key, State, ClsName, FieldName, Loc: string;
  Cls: TASTClass;
  Blk: TIOBlock;
  KnownFields: TList<String>;
  EncoderHasField, DecoderHasField, IsIface: Boolean;
begin
  if not FileExists(GStatusFile) then
  begin
    Report('  bif-coverage.status not found — run --reset first');
    Exit;
  end;
  Status := TStringList.Create;
  KnownFields := TList<String>.Create;
  begin
    Status.LoadFromFile(GStatusFile);
    for I := 0 to Status.Count - 1 do
    begin
      Line := Trim(Status.Strings[I]);
      if (Line = '') or (StrAt(Line, 0) = Ord('#')) then Continue;
      SpacePos := Pos(' ', Line);
      if SpacePos < 0 then
      begin
        Report('  status:' + IntToStr(I + 1) + ' malformed: ' + Line);
        Continue;
      end;
      Key := Trim(Copy(Line, 0, SpacePos));
      State := Trim(Copy(Line, SpacePos, Length(Line) - SpacePos));
      KnownFields.Add(Key);
      { Split Key into ClsName.FieldName }
      SpacePos := Pos('.', Key);
      if SpacePos < 0 then
      begin
        Report('  status:' + IntToStr(I + 1) + ' bad key (no dot): ' + Key);
        Continue;
      end;
      ClsName := Copy(Key, 0, SpacePos);
      FieldName := Copy(Key, SpacePos + 1, Length(Key) - SpacePos - 1);
      { Probe the iface-container store first: TMethodParam is also an AST
        node (so it appears in the AST scan) but has no AST encode/decode
        dispatch block — it must be checked against the file-level
        haystacks, not the per-class block. }
      Cls := FindIfaceClass(ClsName);
      IsIface := Cls <> nil;
      if Cls = nil then
        Cls := FindASTClass(ClsName);
      if Cls = nil then
      begin
        Report('  [stale] status names unknown class ' + Key);
        Continue;
      end;
      if Cls.Fields.IndexOf(FieldName) < 0 then
      begin
        Report('  [stale] ' + Key + ' is not a public field on ' + ClsName);
        Continue;
      end;
      if IsIface then
      begin
        { Interface-container fields are hand-serialised across many
          functions; check the file-level encoder/decoder haystacks. }
        EncoderHasField := Pos('.' + FieldName, GIoEncodeText) >= 0;
        DecoderHasField := Pos('.' + FieldName, GIoDecodeText) >= 0;
      end
      else
      begin
        Blk := FindBlock(GEncodeNames, GEncodeObjs, ClsName);
        EncoderHasField := (Blk <> nil) and (Pos('.' + FieldName, Blk.Body) >= 0);
        Blk := FindBlock(GDecodeNames, GDecodeObjs, ClsName);
        DecoderHasField := (Blk <> nil) and (Pos('.' + FieldName, Blk.Body) >= 0);
      end;
      if State = 'serialise' then
      begin
        if not EncoderHasField then
          Report('  [broken] ' + Key + ' marked serialise but encoder is missing it');
        if not DecoderHasField then
          Report('  [broken] ' + Key + ' marked serialise but decoder is missing it');
      end
      else if State = 'safe' then
      begin
        if EncoderHasField then
          Report('  [drift] ' + Key +
                 ' marked safe but encoder writes it' +
                 ' (uUnitInterfaceIO.pas:' +
                 IntToStr(FindIORefLine(ClsName, FieldName, 0, True))
                 + ')');
        if DecoderHasField then
          Report('  [drift] ' + Key +
                 ' marked safe but decoder reads it' +
                 ' (uUnitInterfaceIO.pas:' +
                 IntToStr(FindIORefLine(ClsName, FieldName,
                                        DecoderStartLine(), False)) +
                 ')');
      end
      else
        Report('  status:' + IntToStr(I + 1) + ' unknown state ' + State +
               ' for ' + Key);
    end;
    { Forward check: every AST field on a serialised class must be in status }
    for I := 0 to GASTNames.Count - 1 do
    begin
      Cls := ASTAt(I);
      if not IsSerialisedClass(Cls) then Continue;
      EncoderHasField := FindBlock(GEncodeNames, GEncodeObjs, Cls.Name) <> nil;
      DecoderHasField := FindBlock(GDecodeNames, GDecodeObjs, Cls.Name) <> nil;
      if Cls.Fields.Count = 0 then
      begin
        { fieldless node still needs a class-level dispatch case }
        Loc := ' (uAST.pas:' + IntToStr(Cls.LineNo) + ')';
        if not EncoderHasField then
          Report('  [encoder] >>> missing ' +
                 Cls.Name + ' (no fields)' + Loc);
        if not DecoderHasField then
          Report('  [decoder] <<< missing ' +
                 Cls.Name + ' (no fields)' + Loc);
      end
      else
        for J := 0 to Cls.Fields.Count - 1 do
        begin
          Key := Cls.Name + '.' + Cls.Fields.Get(J);
          Loc := ' (uAST.pas:' + IntToStr(FieldLineNo(Cls, J)) + ')';
          if not EncoderHasField then
            Report('  [encoder] >>> missing ' +
                   Key + Loc);
          if not DecoderHasField then
            Report('  [decoder] <<< missing ' +
                   Key + Loc);
          if KnownFields.IndexOf(Key) < 0 then
            Report('  [new] not in status (mark as serialise or safe) ' +
                   Key + Loc);
        end;
    end;
    { Forward check: every public field of each .bif interface-container
      type must be classified in the status file. }
    for I := 0 to GIfaceNames.Count - 1 do
    begin
      Cls := IfaceAt(I);
      for J := 0 to Cls.Fields.Count - 1 do
      begin
        Key := Cls.Name + '.' + Cls.Fields.Get(J);
        Loc := ' (' + Cls.SrcName + ':' + IntToStr(FieldLineNo(Cls, J)) + ')';
        if KnownFields.IndexOf(Key) < 0 then
          Report('  [new] not in status (mark as serialise or safe) ' +
                 Key + Loc);
      end;
    end;
  end;
end;

begin
  GErrors := 0;
  GDecoderStart := -1;
  GRoot := FindProjectRoot();
  if GRoot = '' then
  begin
    WriteLn('bif-coverage: could not locate project root from CWD ' +
            GetCurrentDir());
    Halt(2);
  end;
  GAstFile        := GRoot + AST_REL;
  GIoFile         := GRoot + IO_REL;
  GIfaceFile      := GRoot + IFACE_REL;
  GCompilerIdFile := GRoot + COMPILER_ID_REL;
  GRootProject    := GRoot + ROOT_REL;
  GStatusFile     := GRoot + STATUS_REL;
  GIfaceTypes[0]  := 'TUnitInterface';
  GIfaceTypes[1]  := 'TRoutineSig';
  GIfaceTypes[2]  := 'TConstEntry';
  GIfaceTypes[3]  := 'TVarEntry';
  GASTNames := TStringList.Create;
  GASTObjs := TObjectList.Create(True);
  GEncodeNames := TStringList.Create;
  GEncodeObjs := TObjectList.Create(True);
  GDecodeNames := TStringList.Create;
  GDecodeObjs := TObjectList.Create(True);
  GIfaceNames := TStringList.Create;
  GIfaceObjs := TObjectList.Create(True);
  GEncodeNames.Duplicates := dupAccept;
  GDecodeNames.Duplicates := dupAccept;
  GIfaceNames.Duplicates := dupAccept;
  if not FileExists(GAstFile) then
  begin
    WriteLn('bif-coverage: cannot open ' + GAstFile);
    Halt(2);
  end;
  if not FileExists(GIoFile) then
  begin
    WriteLn('bif-coverage: cannot open ' + GIoFile);
    Halt(2);
  end;
  if not FileExists(GIfaceFile) then
  begin
    WriteLn('bif-coverage: cannot open ' + GIfaceFile);
    Halt(2);
  end;
  ScanAST();
  ScanInterfaceTypes();
  ScanIO();
  WriteLn('bif-coverage: scanned ' + IntToStr(GASTNames.Count) +
          ' AST classes, ' + IntToStr(GEncodeNames.Count) +
          ' encoder cases, ' + IntToStr(GDecodeNames.Count) +
          ' decoder cases');
  if (ParamCount() > 0) and (ParamStr(1) = '--reset') then
    WriteStatus()
  else
  begin
    CheckVersion();
    CheckAgainstStatus();
  end;
  if GErrors = 0 then
    WriteLn('bif-coverage: OK')
  else
    WriteLn('bif-coverage: ' + IntToStr(GErrors) + ' gap(s) found');
  if GErrors > 0 then Halt(1);
end.
