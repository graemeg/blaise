{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit uParser;

// Recursive-descent parser for the Blaise grammar:
//   Program        ::= 'program' Ident ';' [Uses] Block '.'
//   Uses           ::= 'uses' Ident {',' Ident} ';'
//   Block          ::= [TypeSection] [VarSection] 'begin' StmtList 'end'
//   TypeSection    ::= 'type' TypeDecl {TypeDecl}
//   TypeDecl       ::= Ident '=' (RecordDef | ClassDef) ';'
//   RecordDef      ::= 'record' FieldList 'end'
//   ClassDef       ::= 'class' ['(' Ident ')'] FieldList MethodList 'end'
//   FieldList      ::= {FieldDecl}
//   FieldDecl      ::= IdentList ':' TypeName ';'
//   MethodList     ::= {MethodDecl}
//   MethodDecl     ::= 'procedure' Ident ['(' ParamList ')'] ';' Block ';'
//   ParamList      ::= ParamGroup {';' ParamGroup}
//   ParamGroup     ::= IdentList ':' TypeName
//   VarSection     ::= 'var' VarDecl {VarDecl}
//   VarDecl        ::= IdentList ':' TypeName ';'
//   StmtList       ::= Stmt {';' Stmt} [';']
//   Stmt           ::= FieldAssignment | MethodCall | Assignment | ProcCall | empty
//   FieldAssign    ::= Ident '.' Ident ':=' Expr
//   MethodCall     ::= Ident '.' Ident ['(' [ExprList] ')']
//   Assignment     ::= Ident ':=' Expr
//   ProcCall       ::= Ident ['(' [ExprList] ')']
//   ExprList       ::= Expr {',' Expr}
//   Expr           ::= Term (('+' | '-') Term)*
//   Term           ::= Factor (('*' | '/' | 'div') Factor)*
//   Factor         ::= IntLit | StringLit | Ident '.' Ident | Ident | '(' Expr ')'
//   TypeName       ::= Ident

interface

uses
  SysUtils, Classes, contnrs, uLexer, uAST, uStrCompat;

type
  EParseError = class(Exception);

  TParser = class
  private
    FLexer:      TLexer;
    FCurrent:    TToken;
    FLookahead:  TToken;  { one-token lookahead }
    FLookahead2: TToken;  { two-token lookahead for generic disambiguation }
    FAhead:      array of TToken;  { tokens beyond FLookahead2 (FIFO), filled on
                                     demand by PeekTok for unbounded lookahead }
    FUsedUnits:  TStringList; { unit names from every 'uses' clause, plus implicit
                                'System'.  Consulted purely as a syntactic name list
                                to recognise 'UnitName.Symbol' — no symbol lookup. }
    FLinkLibs:   TObjectList; { non-owning ref to the current TUnit/TProgram.LinkLibs;
                                external 'lib' decls append a TLinkLibDecl here as they
                                are parsed (any section). nil outside a unit/program. }
    FGenericTypeDepth: Integer; { > 0 while parsing the body of a generic record /
                                  class template.  `class operator` declarations
                                  are rejected there: operator resolution would
                                  need per-instantiation FMethodGroups keying and
                                  a generic-template .bif round-trip, neither of
                                  which is designed yet. }

    { Record a 'link library X' dependency on the unit/program being parsed. }
    procedure AddLinkLib(const ALibName: string; ALine, ACol: Integer);
    function  IsUsedUnit(const AName: string): Boolean;
    function  IsUnitPrefix(const AName: string): Boolean;
    { Unbounded lookahead, exposed as scalar accessors (0 = FCurrent).  A
      TToken-returning peek is deliberately avoided — TToken carries a managed
      string, and returning it by value would create transient managed records
      in the hot matcher path. }
    procedure EnsureAhead(N: Integer);
    function  PeekKindAt(N: Integer): TTokenKind;
    function  PeekValueAt(N: Integer): string;
    function  PeekLineAt(N: Integer): Integer;
    function  PeekColAt(N: Integer): Integer;
    function  TryCollapseUnitQualifier(var AName: string;
                                       var ALine, ACol: Integer;
                                       out AUnit: string): Boolean;
    procedure Advance;
    function  PeekKind(): TTokenKind;
    function  PeekKind2(): TTokenKind;  { two tokens ahead }
    procedure Expect(AKind: TTokenKind);
    function  Check(AKind: TTokenKind): Boolean;
    function  CheckUnitNamePart: Boolean;
    function  ParseTypeName: string;  { reads Ident optionally followed by '<' ArgList '>' }
    function  SubrangeAhead: Boolean; { current token starts an integer-literal subrange: IntLit.. or -IntLit.. }
    function  ParseIntegerSubrangeBaseType(out ALo, AHi: Int64): string; { parse lo..hi, return narrowest fitting standard integer type and the bounds }
    function  ReadConstBoundText: string;  { read an array bound: literal, ident, or expr }
    function  ParseAnonEnumName: string;  { parse '(a,b,c)' → encoded member-list string }

    function  ParseProgram: TProgram;
    procedure ParseUsesList(AList: TStringList);
    procedure ParseUses(AProg: TProgram);
    function  ParseBlock: TBlock;
    function  ParseAsmBody: TBlock;
    procedure ParseTypeSection(ABlock: TBlock);
    procedure ParseTypeDecl(ABlock: TBlock);
    procedure ParseConstBlock(AList: TObjectList);
    procedure ParseConstArrayType(CD: TConstDecl);
    procedure ReadConstArrayDim(CD: TConstDecl);
    procedure ParseConstArrayScalar(CD: TConstDecl);
    procedure ParseConstArrayGroup(CD: TConstDecl);
    procedure ParseConstValue(CD: TConstDecl);
    function  TryParseConstIntTypecast(out AValue: Int64): Boolean;
    function  IsConstExprOp(AKind: TTokenKind): Boolean;
    function  ConstRhsStartsIntExpr: Boolean;
    function  CurrentIsConstBitOp: Boolean;
    function  ConsumeConstBitOpName: string;
    function  CollectConstBitOpExpr(const AFirstStr: string;
                                    AFirstIsIdent: Boolean): TStringList;
    function  ParseEnumDef: TEnumTypeDef;
    function  ParseSetDef: TSetTypeDef;
    function  ParseRecordDef: TRecordTypeDef;
    function  ParseProceduralTypeDef: TProceduralTypeDef;
    function  ParseGenericName: string;  { reads IDENT optionally followed by '<' TypeArgs '>' }
    function  ParseClassDef: TClassTypeDef;
    function  ParseInterfaceDef: TInterfaceTypeDef;
    procedure ParseFieldDecl(AFields: TObjectList);
    procedure ParseAttributeList(AAttrs: TStringList; AUses: TObjectList = nil);
    function  ParsePropertyDecl: TPropertyDecl;
    function  ParseMethodDecl(IsFunction: Boolean; ACanHaveNestedProcs: Boolean = False;
                              AIsOperator: Boolean = False): TMethodDecl;
    { True when the token stream is at `class operator` — the only position in
      which the operator NAME identifiers (Add, Equal, ...) are special. }
    function  AtClassOperator: Boolean;
    { Consume `class operator`, parse the decl through ParseMethodDecl, then
      validate the operator name and arity.  ACanHaveNestedProcs is passed
      through for out-of-line bodies. }
    function  ParseClassOperatorDecl(ACanHaveNestedProcs: Boolean = False): TMethodDecl;
    procedure ParseParamList(AParams: TObjectList);
    procedure ParseStandaloneDecl(ABlock: TBlock);
    procedure ParseVarBlock(ABlock: TBlock);
    procedure ParseVarDecl(ABlock: TBlock; AIsThreadVar: Boolean = False);
    procedure ParseStmtList(ABlock: TBlock);
    function  ParseStmt: TASTStmt;
    function  ParseIfStmt: TIfStmt;
    function  ParseWhileStmt: TWhileStmt;
    function  ParseRepeatStmt: TRepeatStmt;
    function  ParseForStmt: TASTStmt;
    function  ParseTryStmt: TASTStmt;
    function  ParseExceptHandlerClause: TExceptHandlerClause;
    procedure ParseBodyInto(ATarget: TCompoundStmt; AStop1, AStop2: TTokenKind);
    function  ParseRaiseStmt: TRaiseStmt;
    function  ParseInheritedStmt: TInheritedCallStmt;
    function  ParseCaseLabel: TASTExpr;
    function  ParseCaseStmt: TCaseStmt;
    function  ParseForwardDecl(IsFunction: Boolean): TMethodDecl;
    function  ParseCompoundStmt: TCompoundStmt;
    function  ParseBlockVarDeclStmt: TASTStmt;
    function  ParseExpr: TASTExpr;
    function  ParseAnonMethodLiteral: TAnonMethodExpr;
    { Terse lambda: 'x -> expr', '(a, b) -> expr', '(a: T) -> begin ... end'.
      Desugars to a TAnonMethodExpr with IsArrow set; untyped params and the
      return type are filled by target-typed inference (Phase 9a). }
    function  ParseArrowLambda: TAnonMethodExpr;
    { True when the token stream at the current position starts an arrow
      lambda: 'ident ->' or a parenthesised (possibly empty) parameter list
      whose matching ')' is immediately followed by '->'. }
    function  ArrowLambdaAhead: Boolean;
    function  ParseSetOrArrayElement: TASTExpr;
    function  ParseAddSub: TASTExpr;
    function  ParseTerm: TASTExpr;
    function  ParseFactor: TASTExpr;
    procedure ParseArgList(ACall: TProcCall);
    procedure ParseMethodCallArgList(ACall: TMethodCallStmt);
  public
    constructor Create(ALexer: TLexer);
    destructor Destroy; override;
    function Parse: TProgram;
    function ParseUnit: TUnit;
    { True iff the primed first token is `unit` — caller forks to
      ParseUnit instead of Parse.  Safe to call straight after Create. }
    function IsUnitTopLevel: Boolean;
  end;

implementation

constructor TParser.Create(ALexer: TLexer);
begin
  inherited Create();
  FLexer      := ALexer;
  FUsedUnits  := TStringList.Create();
  { 'System' is implicitly used by every compilation unit. }
  FUsedUnits.Add('System');
  FCurrent    := FLexer.Next();
  FLookahead  := FLexer.Next();
  FLookahead2 := FLexer.Next();
end;

destructor TParser.Destroy;
begin
  FUsedUnits.Free();
  inherited Destroy();
end;

procedure TParser.Advance;
var
  I: Integer;
begin
  FCurrent    := FLookahead;
  FLookahead  := FLookahead2;
  { Drain the on-demand lookahead buffer first (tokens PeekTok pre-read), so
    consumption order is preserved; fall back to the lexer when it is empty. }
  if Length(FAhead) > 0 then
  begin
    FLookahead2 := FAhead[0];
    for I := 1 to High(FAhead) do
      FAhead[I - 1] := FAhead[I];
    SetLength(FAhead, Length(FAhead) - 1);
  end
  else
    FLookahead2 := FLexer.Next();
end;

function TParser.PeekKind(): TTokenKind;
begin
  Result := FLookahead.Kind;
end;

function TParser.PeekKind2(): TTokenKind;
begin
  Result := FLookahead2.Kind;
end;

{ Ensure the on-demand lookahead buffer holds enough tokens that conceptual
  index N (>= 3) maps to FAhead[N - 3].  Tokens are pulled from the lexer and
  held (FIFO) until consumed by Advance.  Lets the unit-qualifier matcher
  inspect a whole dotted chain of any depth before consuming any of it. }
procedure TParser.EnsureAhead(N: Integer);
var
  T: TToken;
begin
  while Length(FAhead) < (N - 2) do
  begin
    T := FLexer.Next();
    SetLength(FAhead, Length(FAhead) + 1);
    FAhead[High(FAhead)] := T;
  end;
end;

{ Kind of the token N positions ahead of FCurrent (0=FCurrent, 1=FLookahead,
  2=FLookahead2, 3+ from FAhead). }
function TParser.PeekKindAt(N: Integer): TTokenKind;
begin
  case N of
    0: Exit(FCurrent.Kind);
    1: Exit(FLookahead.Kind);
    2: Exit(FLookahead2.Kind);
  end;
  EnsureAhead(N);
  Result := FAhead[N - 3].Kind;
end;

{ Value text of the token N positions ahead. }
function TParser.PeekValueAt(N: Integer): string;
begin
  case N of
    0: Exit(FCurrent.Value);
    1: Exit(FLookahead.Value);
    2: Exit(FLookahead2.Value);
  end;
  EnsureAhead(N);
  Result := FAhead[N - 3].Value;
end;

function TParser.PeekLineAt(N: Integer): Integer;
begin
  case N of
    0: Exit(FCurrent.Line);
    1: Exit(FLookahead.Line);
    2: Exit(FLookahead2.Line);
  end;
  EnsureAhead(N);
  Result := FAhead[N - 3].Line;
end;

function TParser.PeekColAt(N: Integer): Integer;
begin
  case N of
    0: Exit(FCurrent.Col);
    1: Exit(FLookahead.Col);
    2: Exit(FLookahead2.Col);
  end;
  EnsureAhead(N);
  Result := FAhead[N - 3].Col;
end;

{ Case-insensitive membership test against the parsed 'uses' names. }
{ Append a 'link library ALibName' dependency to the unit/program being parsed.
  Duplicates are tolerated — the exporter dedupes when building the .bif set. }
procedure TParser.AddLinkLib(const ALibName: string; ALine, ACol: Integer);
var
  LL: TLinkLibDecl;
begin
  if (FLinkLibs = nil) or (ALibName = '') then Exit;
  LL := TLinkLibDecl.Create();
  LL.LibName := ALibName;
  LL.Line := ALine;
  LL.Col  := ACol;
  FLinkLibs.Add(LL);
end;

function TParser.IsUsedUnit(const AName: string): Boolean;
var
  I: Integer;
begin
  for I := 0 to FUsedUnits.Count - 1 do
    if SameText(FUsedUnits.Strings[I], AName) then
      Exit(True);
  Result := False;
end;

{ True iff AName is a used unit OR a dotted prefix of one (some used unit equals
  AName or begins with 'AName.').  Lets the matcher stop extending a candidate
  the moment it can no longer complete any unit name. }
function TParser.IsUnitPrefix(const AName: string): Boolean;
var
  I: Integer;
  U: string;
begin
  for I := 0 to FUsedUnits.Count - 1 do
  begin
    U := FUsedUnits.Strings[I];
    if SameText(U, AName) then Exit(True);
    { U begins with 'AName.' — StrHead is 0-based (Blaise strings are 0-indexed). }
    if (Length(U) > Length(AName) + 1) and
       SameText(StrHead(U, Length(AName) + 1), AName + '.') then Exit(True);
  end;
  Result := False;
end;

{ Recognise a unit-qualified reference 'Unit.Symbol' where Unit is the LONGEST
  dotted prefix (starting at AName) that exactly names a used unit and is
  followed by a trailing '.Symbol'.  The 'uses' name list bounds how far to
  scan, so any unit-name depth works (System.SysUtils.Foo, A.B.C.D.Sym, ...).

  Cursor on entry: AName has just been consumed, so FCurrent is the '.' before
  the first extra component.  Component idents after AName therefore sit at peek
  indices 1, 3, 5, ... with the separating dots at 0, 2, 4, ...

  On a match the unit name and its trailing dot are consumed, AName/ALine/ACol
  become the bare Symbol (cursor left just past it), and the caller proceeds as
  if it had read an unqualified reference.  On no match NOTHING is consumed, so
  a same-prefixed record/field chain (My.Pkg := x) is left intact — the required
  trailing '.Symbol' is what distinguishes the two. }
function TParser.TryCollapseUnitQualifier(var AName: string;
  var ALine, ACol: Integer; out AUnit: string): Boolean;
var
  Cand, BestUnit: string;
  Comps, BestComps, J, DotIdx, IdentIdx: Integer;
begin
  Result := False;
  AUnit  := '';
  BestUnit := '';
  Cand := AName;
  Comps := 0;
  if IsUsedUnit(Cand) then
  begin
    BestComps := 0;
    BestUnit  := Cand;
  end
  else
    BestComps := -1;
  { Greedily absorb '.ident' components while the candidate stays a viable unit
    prefix; remember the longest position that is an exact used-unit match. }
  J := 1;
  while True do
  begin
    DotIdx   := 2 * (J - 1);
    IdentIdx := 2 * J - 1;
    if (PeekKindAt(DotIdx) <> tkDot) or (PeekKindAt(IdentIdx) <> tkIdent) then
      Break;
    if not IsUnitPrefix(Cand + '.' + PeekValueAt(IdentIdx)) then
      Break;
    Cand := Cand + '.' + PeekValueAt(IdentIdx);
    Comps := J;
    if IsUsedUnit(Cand) then
    begin
      BestComps := Comps;
      BestUnit  := Cand;
    end;
    Inc(J);
  end;
  if BestComps < 0 then Exit;  { AName does not lead to a used unit }
  { A trailing '.Symbol' must follow the matched unit, else this is a bare unit
    reference or a same-prefixed value chain — leave it for the normal parser. }
  DotIdx   := 2 * BestComps;
  IdentIdx := 2 * BestComps + 1;
  if (PeekKindAt(DotIdx) <> tkDot) or (PeekKindAt(IdentIdx) <> tkIdent) then
    Exit;
  AName := PeekValueAt(IdentIdx);
  ALine := PeekLineAt(IdentIdx);
  ACol  := PeekColAt(IdentIdx);
  AUnit := BestUnit;
  for J := 1 to IdentIdx + 1 do Advance();  { consume unit name, dot, symbol }
  Result := True;
end;

function TParser.ReadConstBoundText: string;
var
  Depth: Integer;
begin
  Result := '';
  Depth := 0;
  while True do
  begin
    if (Depth = 0) and ((Check(tkDotDot)) or (Check(tkRBracket))
       or (Check(tkComma))) then
      Break;
    if Check(tkLParen) then
    begin
      Depth := Depth + 1;
      Result := Result + '(';
      Advance();
    end
    else if Check(tkRParen) then
    begin
      Depth := Depth - 1;
      Result := Result + ')';
      Advance();
    end
    else if Check(tkIntLit) then
    begin
      Result := Result + FCurrent.Value;
      Advance();
    end
    else if Check(tkIdent) then
    begin
      Result := Result + FCurrent.Value;
      Advance();
    end
    else if Check(tkMinus) then
    begin
      Result := Result + '-';
      Advance();
    end
    else if Check(tkPlus) then
    begin
      Result := Result + '+';
      Advance();
    end
    else if Check(tkStar) then
    begin
      Result := Result + '*';
      Advance();
    end
    else if Check(tkDiv) then
    begin
      Result := Result + ' div ';
      Advance();
    end
    else if Check(tkMod) then
    begin
      Result := Result + ' mod ';
      Advance();
    end
    else if Check(tkShl) then
    begin
      Result := Result + ' shl ';
      Advance();
    end
    else if Check(tkShr) then
    begin
      Result := Result + ' shr ';
      Advance();
    end
    else
      raise EParseError.Create(Format(
        'Expected constant bound expression at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  end;
  if Result = '' then
    raise EParseError.Create(Format(
      'Expected constant bound expression at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
end;

{ Parse a type name, including generic instantiations.
  Returns 'Integer', 'TBox<Integer>', 'TPair<string,Integer>', etc.
  Spaces around commas are stripped for a canonical representation. }
function TParser.ParseTypeName: string;
var
  LStr, HStr, ElemTypeName: string;
  Lows, Highs: TStringList;
  I: Integer;
begin
  { Array type: static 'array[L..H] of T' or dynamic 'array of T' }
  if Check(tkArray) then
  begin
    Advance();  { consume 'array' }
    if Check(tkLBracket) then
    begin
      { Static array: array[L..H] of T (range-indexed) or
        array[TEnum] of T (ordinal-indexed).  Multi-dimensional with
        comma-separated dimensions: array[L1..H1, L2..H2] of T.  The
        multi-dim form is desugared into nested single-dimension arrays
        (array[L1..H1] of array[L2..H2] of T) so the rest of the pipeline
        sees only the already-supported nested form. }
      Advance();  { consume '[' }
      if Check(tkIdent) and (PeekKind() = tkRBracket) then
      begin
        Result := '@' + FCurrent.Value;
        Advance();  { consume ident }
        Expect(tkRBracket);
        Expect(tkOf);
        ElemTypeName := Self.ParseTypeName();
        Result := 'array[' + Result + '] of ' + ElemTypeName;
        Exit;
      end;
      Lows := TStringList.Create();
      Highs := TStringList.Create();
      try
        repeat
          { An enum-type dimension is a bare identifier NOT followed by '..'
            (e.g. the TEnum dimensions in 'array[TEnum, 0..1]').  Encode BOTH
            bounds as self-describing markers '@L:TEnum' / '@H:TEnum' so the
            resolver derives low and high from the type — a full enum spans
            0..N-1, an enum-subrange type spans its own ordinal bounds
            (GH #182; hardcoding low=0 mis-sized a subrange dimension). }
          if Check(tkIdent) and (PeekKind() <> tkDotDot) then
          begin
            Lows.Add('@L:' + FCurrent.Value);
            Highs.Add('@H:' + FCurrent.Value);
            Advance();
          end
          else
          begin
            Lows.Add(Self.ReadConstBoundText());
            Expect(tkDotDot);
            Highs.Add(Self.ReadConstBoundText());
          end;
          if not Check(tkComma) then
            Break;
          Advance();  { consume ',' — next dimension }
        until False;
        Expect(tkRBracket);
        Expect(tkOf);
        ElemTypeName := Self.ParseTypeName();
        { Build nested type from the innermost dimension outwards. }
        Result := ElemTypeName;
        for I := Highs.Count - 1 downto 0 do
        begin
          LStr := Lows.Strings[I];
          HStr := Highs.Strings[I];
          Result := Format('array[%s..%s] of %s', [LStr, HStr, Result]);
        end;
      finally
        Lows.Free();
        Highs.Free();
      end;
    end
    else
    begin
      { Dynamic array: array of T }
      Expect(tkOf);
      ElemTypeName := Self.ParseTypeName();
      Result := 'array of ' + ElemTypeName;
    end;
    Exit;
  end;
  { Pointer-to type: '^TypeName' }
  if Check(tkCaret) then
  begin
    Advance();  { consume '^' }
    Result := '^' + Self.ParseTypeName();  { Self. forces recursive call, not result-var read }
    Exit;
  end;
  { Metaclass reference: 'class of TFoo' — encoded as 'class of <Name>'.
    The base class name is parsed via ParseTypeName so that 'class of
    TList<Integer>' (a metaclass of a generic instance) is also valid. }
  if Check(tkClass) then
  begin
    Advance();  { consume 'class' }
    Expect(tkOf);
    Exit('class of ' + Self.ParseTypeName());
  end;
  { Inline set type: 'set of <NamedEnum>' or 'set of (a, b, c)'.  The element
    is either a named enum (encoded as 'set of <Name>') or an anonymous enum
    written in place.  An anonymous enum is parsed and wrapped in a synthetic
    type declaration with a minted unique name; the declaration is staged in
    FPendingTypeDecls and flushed into the enclosing block so the normal type
    pass registers it.  The set then references that synthetic name. }
  if Check(tkSet) then
  begin
    Advance();  { consume 'set' }
    Expect(tkOf);
    if Check(tkLParen) then
      { Anonymous enum element: encode the member list directly in the type
        name as 'set of (a,b,c)'.  The semantic pass synthesises the enum and
        the set from this string on demand — no parser-side symbol table is
        needed, and the encoding is self-contained. }
      Exit('set of ' + Self.ParseAnonEnumName())
    else if Check(tkIdent) and (PeekKind() <> tkDotDot) then
    begin
      { Named base type: 'set of Byte', 'set of Boolean', 'set of TEnum'. }
      Result := 'set of ' + FCurrent.Value;
      Advance();
      Exit;
    end
    else if Check(tkIntLit) or Check(tkIdent) then
    begin
      { Integer subrange base type: 'set of 0..255', 'set of 1..10', or a named
        constant bound ('set of Lo..Hi').  Each bound is a single integer literal
        or identifier; encode as 'set of lo..hi' for the semantic pass to
        validate (0..255) and size.  (A bracket-context bound reader is wrong
        here — the subrange is not delimited by ']'/','.) }
      LStr := FCurrent.Value;
      Advance();
      Expect(tkDotDot);
      if not (Check(tkIntLit) or Check(tkIdent)) then
        raise EParseError.Create(Format(
          'Expected set subrange upper bound at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      HStr := FCurrent.Value;
      Advance();
      Exit('set of ' + LStr + '..' + HStr);
    end
    else
      raise EParseError.Create(Format(
        'Expected enum type, integer subrange, or ''('' after ''set of'' ' +
        'at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  end;
  if not Check(tkIdent) then
    raise EParseError.Create(Format('Expected type name at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  Result := FCurrent.Value;
  Advance();
  { Qualified type name: 'UnitName.TypeName'.  The unit qualifier may itself
    be dotted (e.g. System.SysUtils.TFormatSettings).  A type is always the
    final identifier; the leading components name the (possibly dotted) unit.
    Carry the full dotted form through — the semantic type resolver strips the
    unit qualifier and resolves the tail via the uses chain. }
  while Check(tkDot) and (PeekKind() = tkIdent) do
  begin
    Advance();  { consume '.' }
    Result := Result + '.' + FCurrent.Value;
    Advance();
  end;
  if Check(tkLessThan) then
  begin
    Advance();  { consume '<' }
    Result := Result + '<';
    if not Check(tkIdent) then
      raise EParseError.Create(Format(
        'Expected type argument after ''<'' at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    { Each type argument is itself a (possibly-generic) type name, so recurse
      — this is what makes nested generics like TList<TList<Integer>> and
      TBox<TPair<Integer, string>> parse. }
    Result := Result + Self.ParseTypeName();
    while Check(tkComma) do
    begin
      Advance();
      if not Check(tkIdent) then
        raise EParseError.Create(Format(
          'Expected type argument after '','' at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result := Result + ',' + Self.ParseTypeName();
    end;
    Expect(tkGreaterThan);
    Result := Result + '>';
  end;
end;

function TParser.SubrangeAhead: Boolean;
begin
  { An integer-literal subrange in a type RHS: `0..255` or `-10..10`.
    Recognised by a leading integer literal (optionally a minus sign) followed
    by the '..' token.  Pure lookahead — consumes nothing. }
  if Check(tkIntLit) then
    Result := (PeekKind() = tkDotDot)
  else if Check(tkMinus) then
    Result := (PeekKind() = tkIntLit) and (PeekKind2() = tkDotDot)
  else
    Result := False;
end;

function TParser.ParseIntegerSubrangeBaseType(out ALo, AHi: Int64): string;
var
  Lo, Hi: Int64;
  Neg: Boolean;
begin
  { Parse `lo..hi` (each an integer literal, lo optionally negative) and return
    the name of the narrowest STANDARD integer type that holds both bounds.
    Blaise performs no range checking, so a named subrange is just an alias to
    this base type; the choice keeps record/array element layout correct
    (e.g. 0..255 is byte-sized). }
  Neg := False;
  if Check(tkMinus) then begin Neg := True; Advance(); end;
  if not Check(tkIntLit) then
    raise EParseError.Create(Format(
      'Expected integer literal as subrange lower bound at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  Lo := ParseIntLiteral(FCurrent.Value);
  if Neg then Lo := -Lo;
  Advance();
  Expect(tkDotDot);
  Neg := False;
  if Check(tkMinus) then begin Neg := True; Advance(); end;
  if not Check(tkIntLit) then
    raise EParseError.Create(Format(
      'Expected integer literal as subrange upper bound at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  Hi := ParseIntLiteral(FCurrent.Value);
  if Neg then Hi := -Hi;
  Advance();
  if Hi < Lo then
    raise EParseError.Create(Format(
      'Subrange %d..%d is descending at line %d col %d in %s',
      [Lo, Hi, FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  ALo := Lo;
  AHi := Hi;
  { Pick the narrowest standard type covering [Lo, Hi]. }
  if Lo >= 0 then
  begin
    if Hi <= 255 then               Result := 'Byte'
    else if Hi <= 65535 then        Result := 'Word'
    else if Hi <= 4294967295 then   Result := 'Cardinal'
    else                            Result := 'UInt64';
  end
  else
  begin
    { Blaise has no 8-bit signed alias name (no ShortInt), so the narrowest
      signed alias target is SmallInt (16-bit). }
    if (Lo >= -32768) and (Hi <= 32767) then        Result := 'SmallInt'
    else if (Lo >= -2147483648) and (Hi <= 2147483647) then Result := 'Integer'
    else                                            Result := 'Int64';
  end;
end;

function TParser.ParseAnonEnumName: string;
begin
  { Encode an inline '(a, b, c)' enumeration as the literal text '(a,b,c)'
    (no whitespace).  The semantic pass parses the member list out of this
    string, synthesises the enum type and its member constants, and builds the
    enclosing set — so no symbol-table access is needed here in the parser. }
  Expect(tkLParen);
  Result := '(';
  if not Check(tkIdent) then
    raise EParseError.Create(Format('Expected enum member at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  Result := Result + FCurrent.Value;
  Advance();
  while Check(tkComma) do
  begin
    Advance();
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected enum member at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result := Result + ',' + FCurrent.Value;
    Advance();
  end;
  Expect(tkRParen);
  Result := Result + ')';
end;

procedure TParser.Expect(AKind: TTokenKind);
var
  gotName, gotDetail: string;
begin
  if FCurrent.Kind <> AKind then
  begin
    gotName := TokenKindName(FCurrent.Kind);
    if FCurrent.Value <> gotName then
      gotDetail := ' (''' + FCurrent.Value + ''')'
    else
      gotDetail := '';
    raise EParseError.Create(Format(
      'Expected ''%s'' but got ''%s''%s at line %d col %d in %s',
      [TokenKindName(AKind), gotName, gotDetail,
       FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  end;
  Advance();
end;

function TParser.Check(AKind: TTokenKind): Boolean;
begin
  Result := FCurrent.Kind = AKind;
end;

function TParser.CheckUnitNamePart: Boolean;
begin
  Result := (FCurrent.Kind = tkIdent) or
            (FCurrent.Kind in [tkInitialization, tkFinalization, tkProgram,
              tkUses, tkType, tkRecord, tkClass, tkProcedure, tkFunction,
              tkVar, tkBegin, tkEnd, tkIf, tkThen, tkElse, tkWhile, tkDo,
              tkFor, tkTo, tkDownto, tkRepeat, tkUntil, tkTry, tkFinally,
              tkExcept, tkRaise, tkNil, tkUnit, tkIntf, tkImplementation,
              tkVirtual, tkOverride, tkExternal, tkIs, tkAs, tkAnd, tkOr,
              tkNot, tkExit, tkBreak, tkContinue, tkInherited, tkCase,
              tkOf, tkArray, tkSet, tkIn, tkShl, tkShr, tkSar, tkXor, tkConst,
              tkOut, tkConstructor, tkDestructor, tkDiv, tkMod,
              tkThreadvar]);
end;

{ ------------------------------------------------------------------ }

function TParser.Parse: TProgram;
begin
  Result := ParseProgram();
end;

function TParser.IsUnitTopLevel: Boolean;
begin
  Result := FCurrent.Kind = tkUnit;
end;

function TParser.ParseProgram: TProgram;
begin
  Result := TProgram.Create();
  FLinkLibs := Result.LinkLibs;   { collect external 'lib' deps into the program }
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;

    Expect(tkProgram);

    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected program name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result.Name := FCurrent.Value;
    Advance();

    Expect(tkSemicolon);

    if Check(tkUses) then
      ParseUses(Result);

    Result.Block := ParseBlock();

    Expect(tkDot);

    if not Check(tkEOF) then
      raise EParseError.Create(Format(
        'Unexpected tokens after program end at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  except
    Result.Free();
    raise;
  end;
end;

procedure TParser.ParseUsesList(AList: TStringList);
var
  UName: string;
begin
  Expect(tkUses);
  if not CheckUnitNamePart() then
    raise EParseError.Create(Format('Expected unit name after ''uses'' at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  UName := FCurrent.Value;
  Advance();
  while Check(tkDot) do
  begin
    Advance();
    if not CheckUnitNamePart() then
      raise EParseError.Create(Format('Expected identifier after ''.'' in unit name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    UName := UName + '.' + FCurrent.Value;
    Advance();
  end;
  AList.Add(UName);
  FUsedUnits.Add(UName);
  while Check(tkComma) do
  begin
    Advance();
    if not CheckUnitNamePart() then
      raise EParseError.Create(Format('Expected unit name after '','' at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    UName := FCurrent.Value;
    Advance();
    while Check(tkDot) do
    begin
      Advance();
      if not CheckUnitNamePart() then
        raise EParseError.Create(Format('Expected identifier after ''.'' in unit name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      UName := UName + '.' + FCurrent.Value;
      Advance();
    end;
    AList.Add(UName);
    FUsedUnits.Add(UName);
  end;
  Expect(tkSemicolon);
end;

procedure TParser.ParseUses(AProg: TProgram);
begin
  ParseUsesList(AProg.UsedUnits);
end;

function TParser.ParseBlock: TBlock;
begin
  Result := TBlock.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;

    { Accept any number of type/var/procedure/function sections in any order,
      as required when concatenating multiple Pascal units into one file. }
    while Check(tkType) or Check(tkVar) or Check(tkThreadVar) or
          Check(tkProcedure) or Check(tkFunction) or Check(tkConst) or
          Check(tkConstructor) or Check(tkDestructor) or
          AtClassOperator() or
          (Check(tkIdent) and SameText(FCurrent.Value, 'static') and
           (PeekKind() in [tkFunction, tkProcedure])) do
    begin
      if Check(tkType) then
        ParseTypeSection(Result)
      else if Check(tkVar) or Check(tkThreadVar) then
        ParseVarBlock(Result)
      else if Check(tkConst) then
        ParseConstBlock(Result.ConstDecls)
      else
        ParseStandaloneDecl(Result);
    end;

    Expect(tkBegin);
    ParseStmtList(Result);
    Expect(tkEnd);
  except
    Result.Free();
    raise;
  end;
end;

{ ------------------------------------------------------------------ }
{ Type section                                                        }
{ ------------------------------------------------------------------ }

procedure TParser.ParseTypeSection(ABlock: TBlock);
begin
  Expect(tkType);
  while (Check(tkIdent) or Check(tkLBracket)) and
        { Stop the type section at a leading `static function/procedure` — that
          is an out-of-line static-method implementation, not a type decl. }
        not (Check(tkIdent) and SameText(FCurrent.Value, 'static') and
             (PeekKind() in [tkFunction, tkProcedure])) do
    ParseTypeDecl(ABlock);
end;

procedure TParser.ParseTypeDecl(ABlock: TBlock);
var
  TD:               TTypeDecl;
  GD:               TGenericTypeDef;
  GRD:              TGenericRecordDef;
  GID:              TGenericInterfaceDef;
  GPD:              TGenericProcDef;
  AD:               TTypeAliasDef;
  ParamNames:       TStringList;
  ParamConstraints: TStringList;
  IsGeneric:        Boolean;
  Constraint:       string;
  ClassAttrs:       TStringList;
  ClassAttrUses:    TObjectList;  { non-owning transfer list; the class def's
                                    owning AttrUses list adopts the items }
  AUIdx:            Integer;
  SubLo:            Int64;
  SubHi:            Int64;
begin
  ClassAttrs    := TStringList.Create();
  ClassAttrUses := TObjectList.Create(False);
  try
  ParseAttributeList(ClassAttrs, ClassAttrUses);
  TD := TTypeDecl.Create();
  TD.Line := FCurrent.Line;
  TD.Col  := FCurrent.Col;
  try
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected type name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    TD.Name := FCurrent.Value;
    Advance();
    { Check for generic type parameters: TBox<T>, TPair<K,V>, IFoo<T> }
    IsGeneric := Check(tkLessThan);
    if IsGeneric then
    begin
      Advance();  { consume '<' }
      ParamNames       := TStringList.Create();
      ParamConstraints := TStringList.Create();
      try
        if not Check(tkIdent) then
          raise EParseError.Create(Format(
            'Expected type parameter name at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        ParamNames.Add(FCurrent.Value);
        Advance();
        { Optional constraint: T : (class | record | TypeName) }
        Constraint := '';
        if Check(tkColon) then
        begin
          Advance();
          if      Check(tkClass)  then begin Constraint := 'class';  Advance(); end
          else if Check(tkRecord) then begin Constraint := 'record'; Advance(); end
          else if Check(tkIdent)  then begin Constraint := FCurrent.Value; Advance(); end
          else
            raise EParseError.Create(Format(
              'Expected ''class'', ''record'', or a type name after '':'' at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        end;
        ParamConstraints.Add(Constraint);
        while Check(tkComma) do
        begin
          Advance();
          if not Check(tkIdent) then
            raise EParseError.Create(Format(
              'Expected type parameter name at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          ParamNames.Add(FCurrent.Value);
          Advance();
          Constraint := '';
          if Check(tkColon) then
          begin
            Advance();
            if      Check(tkClass)  then begin Constraint := 'class';  Advance(); end
            else if Check(tkRecord) then begin Constraint := 'record'; Advance(); end
            else if Check(tkIdent)  then begin Constraint := FCurrent.Value; Advance(); end
            else
              raise EParseError.Create(Format(
                'Expected ''class'', ''record'', or a type name after '':'' at line %d col %d in %s',
                [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          end;
          ParamConstraints.Add(Constraint);
        end;
        Expect(tkGreaterThan);
        Expect(tkEquals);
        if Check(tkIntf) then
        begin
          GID            := TGenericInterfaceDef.Create();
          GID.Line       := TD.Line;
          GID.Col        := TD.Col;
          GID.ParamNames.AddStrings(ParamNames);
          GID.ParamConstraints.AddStrings(ParamConstraints);
          GID.IntfDef := ParseInterfaceDef();
          TD.Def := GID;
        end
        else if Check(tkRecord) then
        begin
          GRD            := TGenericRecordDef.Create();
          GRD.Line       := TD.Line;
          GRD.Col        := TD.Col;
          GRD.ParamNames.AddStrings(ParamNames);
          GRD.ParamConstraints.AddStrings(ParamConstraints);
          Inc(FGenericTypeDepth);
          try
            GRD.RecordDef := ParseRecordDef();
          finally
            Dec(FGenericTypeDepth);
          end;
          TD.Def := GRD;
        end
        else if Check(tkClass) then
        begin
          GD            := TGenericTypeDef.Create();
          GD.Line       := TD.Line;
          GD.Col        := TD.Col;
          GD.ParamNames.AddStrings(ParamNames);
          GD.ParamConstraints.AddStrings(ParamConstraints);
          Inc(FGenericTypeDepth);
          try
            GD.ClassDef := ParseClassDef();
          finally
            Dec(FGenericTypeDepth);
          end;
          GD.ClassDef.Attributes.AddStrings(ClassAttrs);
          for AUIdx := 0 to ClassAttrUses.Count - 1 do
            GD.ClassDef.AttrUses.Add(ClassAttrUses.Get(AUIdx));
          TD.Def := GD;
        end
        else if Check(tkFunction) or Check(tkProcedure) or
                (Check(tkIdent) and SameText(FCurrent.Value, 'reference') and
                 (PeekKind() = tkTo)) then
        begin
          { Generic procedural-type alias:
              TGetter<T> = reference to function(): T;
            'reference' is the same soft keyword as in the non-generic
            procedural-type branch of ParseTypeSection. }
          GPD := TGenericProcDef.Create();
          GPD.Line := TD.Line;
          GPD.Col  := TD.Col;
          GPD.ParamNames.AddStrings(ParamNames);
          GPD.ParamConstraints.AddStrings(ParamConstraints);
          if Check(tkIdent) then
          begin
            Advance();  { consume 'reference' }
            Advance();  { consume 'to' }
            if not (Check(tkFunction) or Check(tkProcedure)) then
              raise EParseError.Create(Format(
                'Expected ''procedure'' or ''function'' after ''reference to'' ' +
                'at line %d col %d in %s',
                [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
            GPD.ProcDef := ParseProceduralTypeDef();
            if GPD.ProcDef.IsMethodPtr then
              raise EParseError.Create(Format(
                '''reference to'' and ''of object'' are mutually exclusive ' +
                'at line %d col %d in %s',
                [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
            GPD.ProcDef.IsReference := True;
          end
          else
            GPD.ProcDef := ParseProceduralTypeDef();
          TD.Def := GPD;
        end
        else
          raise EParseError.Create(Format(
            'Generic type must be a class, record, or interface, or a ' +
            'procedural type at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      finally
        ParamConstraints.Free();
        ParamNames.Free();
      end;
    end
    else
    begin
      Expect(tkEquals);
      { `bitpacked` is an FPC-only keyword (bit-level packing); Delphi has no
        equivalent and Blaise does not support it.  It lexes as a plain
        identifier, so catch it here and point users at the supported idiom
        (`set of` for boolean flags) rather than letting it fall through to a
        confusing "expected ..." error. }
      if (FCurrent.Kind = tkIdent) and SameText(FCurrent.Value, 'bitpacked') then
        raise EParseError.Create(Format(
          '''bitpacked'' is not supported in Blaise (FPC-only, bit-level ' +
          'packing). Use ''set of'' for packed boolean flags, or an integer ' +
          'with explicit bit operations, at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      if Check(tkPacked) then
      begin
        { Only `packed record` is supported.  `packed class` and `packed
          array` are legal Delphi/FPC syntax but Blaise rejects them
          explicitly so users get a clear error rather than silent no-op. }
        Advance();
        if Check(tkArray) then
          raise EParseError.Create(Format(
            '''packed array'' is not supported in Blaise. Use ''set of'' for ' +
            'packed boolean flags, or a plain array, at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        if not Check(tkRecord) then
          raise EParseError.Create(Format(
            '''packed'' may only precede ''record'' at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        TD.Def := ParseRecordDef();
        TRecordTypeDef(TD.Def).IsPacked := True;
      end
      else if Check(tkRecord) then
        TD.Def := ParseRecordDef()
      else if Check(tkClass) and (PeekKind() = tkOf) then
      begin
        { Metaclass alias: type TFooClass = class of TFoo;  Use the
          generic type-name parser, which already encodes the metaclass
          form as 'class of <Name>'. }
        AD := TTypeAliasDef.Create();
        AD.TypeName := Self.ParseTypeName();
        TD.Def := AD;
      end
      else if Check(tkClass) then
      begin
        TD.Def := ParseClassDef();
        TClassTypeDef(TD.Def).Attributes.AddStrings(ClassAttrs);
        for AUIdx := 0 to ClassAttrUses.Count - 1 do
          TClassTypeDef(TD.Def).AttrUses.Add(ClassAttrUses.Get(AUIdx));
      end
      else if Check(tkIntf) then
        TD.Def := ParseInterfaceDef()
      else if Check(tkLParen) then
        TD.Def := ParseEnumDef()
      else if Check(tkSet) then
        TD.Def := ParseSetDef()
      else if Check(tkFunction) or Check(tkProcedure) then
        TD.Def := ParseProceduralTypeDef()
      { 'reference to procedure/function' — anonymous-method (closure) type.
        'reference' is a soft keyword: it introduces a reference type only
        when immediately followed by 'to'; a type alias to a type literally
        named Reference still parses via the ident branch below. }
      else if Check(tkIdent) and SameText(FCurrent.Value, 'reference') and
              (PeekKind() = tkTo) then
      begin
        Advance();  { consume 'reference' }
        Advance();  { consume 'to' }
        if not (Check(tkFunction) or Check(tkProcedure)) then
          raise EParseError.Create(Format(
            'Expected ''procedure'' or ''function'' after ''reference to'' ' +
            'at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        TD.Def := ParseProceduralTypeDef();
        if TProceduralTypeDef(TD.Def).IsMethodPtr then
          raise EParseError.Create(Format(
            '''reference to'' and ''of object'' are mutually exclusive ' +
            'at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        TProceduralTypeDef(TD.Def).IsReference := True;
      end
      else if (Check(tkIntLit) or Check(tkMinus)) and SubrangeAhead() then
      begin
        { Named integer subrange:  type TByte = 0..255;  type TIdx = -10..10;
          Blaise does not range-check, so a subrange is an alias to the
          narrowest standard integer type that holds both bounds.  This keeps
          record/array layout correct (TByte is byte-sized) while the value
          behaves as an ordinary integer. }
        AD := TTypeAliasDef.Create();
        AD.TypeName := Self.ParseIntegerSubrangeBaseType(SubLo, SubHi);
        AD.IsSubrange := True;
        AD.SubrangeLow := SubLo;
        AD.SubrangeHigh := SubHi;
        TD.Def := AD;
      end
      else if Check(tkIdent) and (PeekKind() = tkDotDot) then
      begin
        { Enum-member (or named-const) subrange:  type TSub = zwei..drei;
          The bounds are identifiers whose ordinals are semantic-time knowledge,
          so store the NAMES; the semantic pass resolves them to the enum base +
          ordinal bounds (GH #182).  The TypeName is left empty — the semantic
          pass supplies the base from the resolved enum. }
        AD := TTypeAliasDef.Create();
        AD.IsSubrange := True;
        AD.SubrangeLowName := FCurrent.Value;
        Advance();
        Expect(tkDotDot);
        AD.SubrangeHighName := FCurrent.Value;
        Expect(tkIdent);
        TD.Def := AD;
      end
      else if Check(tkArray) or Check(tkCaret) or Check(tkIdent) then
      begin
        { Array alias:   type TArr = array[L..H] of T;
          Pointer alias: type PFoo = ^TFoo;
          Simple alias:  type TMyInt = Integer;  (ident rhs) }
        AD := TTypeAliasDef.Create();
        AD.TypeName := Self.ParseTypeName();
        TD.Def := AD;
      end
      else
        raise EParseError.Create(Format(
          'Expected ''record'', ''class'', ''interface'', ''('', ''set'', ''function'', ''procedure'', subrange, or type name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    end;
    Expect(tkSemicolon);
    ABlock.TypeDecls.Add(TD);
  except
    TD.Free();
    raise;
  end;
  finally
    ClassAttrs.Free();
    ClassAttrUses.Free();
  end;
end;

{ Recognise a TypeName(IntLit) or TypeName(-IntLit) cast in a const-init
  position and yield the truncated integer value.  Returns False (without
  consuming any tokens) when the current token is not a known integer
  type name followed by '('.

  The cast applies the type's bit-width as an unsigned truncation mask;
  signed types then sign-extend back to Int64 so e.g. Integer(-11) round-
  trips to -11 while LongWord(-11) yields $FFFFFFF5 (4294967285).  Const
  init only — full-expression casts are handled by ParseFactor. }
function TParser.TryParseConstIntTypecast(out AValue: Int64): Boolean;
var
  TypeName: string;
  Width:    Integer;  { bit-width of the target type; 64 = no truncation }
  IsSigned: Boolean;
  Negate:   Boolean;
  Raw:      Int64;
  Mask:     Int64;
  SignBit:  Int64;
begin
  Result := False;
  if not Check(tkIdent) then Exit;
  if PeekKind() <> tkLParen then Exit;
  TypeName := FCurrent.Value;
  Width := 0; IsSigned := False;
  if SameText(TypeName, 'Byte') then
    begin Width := 8;  IsSigned := False; end
  else if SameText(TypeName, 'ShortInt') then
    begin Width := 8;  IsSigned := True; end
  else if SameText(TypeName, 'SmallInt') or SameText(TypeName, 'Int16') then
    begin Width := 16; IsSigned := True; end
  else if SameText(TypeName, 'Word') or SameText(TypeName, 'UInt16') then
    begin Width := 16; IsSigned := False; end
  else if SameText(TypeName, 'Integer') or SameText(TypeName, 'LongInt') then
    begin Width := 32; IsSigned := True; end
  else if SameText(TypeName, 'Cardinal') or SameText(TypeName, 'LongWord')
       or SameText(TypeName, 'UInt32') then
    begin Width := 32; IsSigned := False; end
  else if SameText(TypeName, 'Int64') then
    begin Width := 64; IsSigned := True; end
  else if SameText(TypeName, 'UInt64') or SameText(TypeName, 'QWord')
       or SameText(TypeName, 'PtrUInt') then
    begin Width := 64; IsSigned := False; end
  else
    Exit;  { unknown / non-integer type name — not our cast }
  Advance();          { consume type name }
  Expect(tkLParen);
  Negate := False;
  if Check(tkMinus) then begin Negate := True; Advance(); end;
  if not Check(tkIntLit) then
    raise EParseError.Create(Format(
      'Expected integer literal inside ''%s(...)'' const cast at line %d col %d in %s',
      [TypeName, FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  Raw := ParseIntLiteral(FCurrent.Value);
  if Negate then Raw := -Raw;
  Advance();
  Expect(tkRParen);
  { No truncation needed for 64-bit targets — the literal already fits. }
  if Width < 64 then
  begin
    Mask    := (Int64(1) shl Width) - 1;
    SignBit := Int64(1) shl (Width - 1);
    Raw     := Raw and Mask;
    { Sign-extend by toggling the sign bit and subtracting it back. }
    if IsSigned and ((Raw and SignBit) <> 0) then
      Raw := Raw - (SignBit shl 1);
  end;
  AValue := Raw;
  Result := True;
end;

{ True when FCurrent is one of the bitwise operators legal inside a
  const initialiser: 'or', 'and', 'xor', 'shl', 'shr'.  Used to detect
  the start of a deferred bit-op expression chain after the first
  operand has been parsed. }
{ True when the const RHS is a multi-token integer expression that must be
  parsed with full operator precedence (via ParseExpr) rather than the
  single-literal / single-precedence bit-op fast paths.  Recognises:
    - a leading '(' (always an arithmetic grouping in const position),
    - an integer literal followed by any binary operator,
    - a leading minus + integer literal followed by any binary operator.
  A lone integer literal (no trailing operator) is deliberately NOT matched,
  so the simple 'const X = 5;' fast path is preserved. }
function TParser.IsConstExprOp(AKind: TTokenKind): Boolean;
begin
  Result := (AKind = tkPlus) or (AKind = tkMinus) or (AKind = tkStar)
         or (AKind = tkSlash) or (AKind = tkDiv)  or (AKind = tkMod)
         or (AKind = tkOr)   or (AKind = tkAnd)   or (AKind = tkXor)
         or (AKind = tkShl)  or (AKind = tkShr);
end;

function TParser.ConstRhsStartsIntExpr: Boolean;
begin
  Result := False;
  if Check(tkLParen) then
    Result := True
  else if Check(tkIntLit) and Self.IsConstExprOp(PeekKind()) then
    Result := True
  else if Check(tkFloatLit) and Self.IsConstExprOp(PeekKind()) then
    Result := True
  else if Check(tkMinus) and (PeekKind() = tkIntLit)
       and Self.IsConstExprOp(PeekKind2()) then
    Result := True
  else if Check(tkMinus) and (PeekKind() = tkFloatLit)
       and Self.IsConstExprOp(PeekKind2()) then
    Result := True
  { Ident-led integer expression (e.g. BASE * 2).  Only the unambiguously
    numeric operators trigger this — '+' is left to the string path so that
    string-concat consts ('a' + b) keep their existing behaviour, and the
    legacy ident-bitop chain handles or/and/xor/shl/shr starting on an ident. }
  else if Check(tkIdent) and
          ((PeekKind() = tkStar) or (PeekKind() = tkSlash) or
           (PeekKind() = tkDiv)  or (PeekKind() = tkMod) or
           (PeekKind() = tkMinus)) then
    Result := True;
end;

function TParser.CurrentIsConstBitOp: Boolean;
begin
  Result := Check(tkOr)  or Check(tkAnd) or Check(tkXor)
         or Check(tkShl) or Check(tkShr);
end;

{ Map current bit-op token to its lowercase name, then advance past it.
  Caller has already verified CurrentIsConstBitOp. }
function TParser.ConsumeConstBitOpName: string;
begin
  case FCurrent.Kind of
    tkOr:  Result := 'or';
    tkAnd: Result := 'and';
    tkXor: Result := 'xor';
    tkShl: Result := 'shl';
    tkShr: Result := 'shr';
  else
    Result := '';  { unreachable — caller gated }
  end;
  Advance();
end;

{ Build a deferred bit-op expression token list, seeded with the first
  operand which has already been parsed by the caller.  Operands and
  operators alternate; operand entries are tagged on Objects[]:

    Objects[i] = nil          → integer literal (the string is the int)
    Objects[i] = TObject(1)   → ident reference
    Objects[i] = TObject(2)   → operator name

  Each new operand may be an optionally-signed int literal, a
  TypeName(IntLit) cast, or a bare ident; trailing typecasts apply the
  same truncation rules as TryParseConstIntTypecast. }
function TParser.CollectConstBitOpExpr(const AFirstStr: string;
                                       AFirstIsIdent: Boolean): TStringList;
var
  OpName:    string;
  Sign:      Integer;
  Raw:       Int64;
  CastVal:   Int64;
begin
  Result := TStringList.Create();
  try
    if AFirstIsIdent then
      Result.AddObject(AFirstStr, TObject(1))
    else
      Result.AddObject(AFirstStr, nil);
    while CurrentIsConstBitOp() do
    begin
      OpName := ConsumeConstBitOpName();
      Result.AddObject(OpName, TObject(2));
      Sign := 1;
      if Check(tkMinus) then begin Advance(); Sign := -1; end;
      if Check(tkIdent) and (PeekKind() = tkLParen)
         and TryParseConstIntTypecast(CastVal) then
      begin
        if Sign < 0 then CastVal := -CastVal;
        Result.AddObject(IntToStr(CastVal), nil);
      end
      else if Check(tkIntLit) then
      begin
        Raw := ParseIntLiteral(FCurrent.Value);
        if Sign < 0 then Raw := -Raw;
        Result.AddObject(IntToStr(Raw), nil);
        Advance();
      end
      else if Check(tkIdent) then
      begin
        if Sign < 0 then
          raise EParseError.Create(Format(
            'Unary minus on named constant operand is not supported '+
            'in const bit-op expression at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        Result.AddObject(FCurrent.Value, TObject(1));
        Advance();
      end
      else
        raise EParseError.Create(Format(
          'Expected operand after ''%s'' in const bit-op expression '+
          'at line %d col %d in %s',
          [OpName, FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    end;
  except
    Result.Free();
    raise;
  end;
end;

procedure TParser.ParseConstBlock(AList: TObjectList);
var
  CD:          TConstDecl;
begin
  Expect(tkConst);
  while Check(tkIdent) do
  begin
    { Stop at a class/record section keyword: a const section inside a class or
      record body is terminated by the next visibility/`static` section or by a
      `property` member.  A genuine const decl is always `IDENT (':' | '=')`, so
      if the current identifier is a section keyword and is NOT immediately
      followed by `:` or `=`, it begins the next section, not another const.
      (Top-level const blocks never hit this: they are followed by `var`/`type`/
      `begin`, which are not tkIdent.) }
    if (SameText(FCurrent.Value, 'private')   or
        SameText(FCurrent.Value, 'protected') or
        SameText(FCurrent.Value, 'public')    or
        SameText(FCurrent.Value, 'published') or
        SameText(FCurrent.Value, 'static')    or
        SameText(FCurrent.Value, 'property')) and
       not (PeekKind() in [tkColon, tkEquals]) then
      Break;
    CD      := TConstDecl.Create();
    CD.Line := FCurrent.Line;
    CD.Col  := FCurrent.Col;
    CD.Name := FCurrent.Value;
    Advance();
    { Typed constant: const Name: TypeName = Value
      or:             const Name: array[IndexType] of ElemType = (v, ...) }
    if Check(tkColon) then
    begin
      Advance();
      if Check(tkArray) then
        Self.ParseConstArrayType(CD)
      else if Check(tkIdent) then
      begin
        CD.TypeName := FCurrent.Value;
        Advance();
      end
      else
        raise EParseError.Create(Format(
          'Expected type name after '':'' in const at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    end;
    Expect(tkEquals);
    Self.ParseConstValue(CD);
    Expect(tkSemicolon);
    AList.Add(CD);
  end;
end;

{ Parse the TYPE of an array-typed constant, starting at 'array'.  Supports:

    array[L..H] of T                       single, range-indexed
    array[E] of T                          single, enum-indexed (E an enum type)
    array[L0..H0, L1..H1, ...] of T        multi-dim, comma form
    array[L0..H0] of array[L1..H1] of T    multi-dim, nested form

  Each range dimension's bounds are pushed onto CD.ArrayDimLows /
  ArrayDimHighs.  For the single range-indexed case ArrayLowBound /
  ArrayHighBound are also set so the existing single-dim path is unchanged.
  Enum indexing is only supported for a single dimension (CD.ArrayIndexType);
  it cannot be mixed with multi-dimensional ranges. }
procedure TParser.ReadConstArrayDim(CD: TConstDecl);
var
  LoText, HiText: string;
begin
  { An enum-type dimension is a bare identifier NOT followed by '..' (e.g. the
    TEnum in 'array[TEnum, 0..1]').  Encode BOTH bounds as self-describing
    markers '@L:TEnum' / '@H:TEnum' so the semantic pass derives the low and
    high from the type: a full enum spans 0..N-1, but an ENUM-SUBRANGE type
    (TSub = a..b) spans its own ordinal bounds SubrangeLow..SubrangeHigh —
    hardcoding the low to 0 mis-sized a subrange dimension (GH #182). }
  if Check(tkIdent) and (PeekKind() <> tkDotDot) then
  begin
    CD.ArrayDimLows.Add('@L:' + FCurrent.Value);
    CD.ArrayDimHighs.Add('@H:' + FCurrent.Value);
    Advance();
    CD.ArrayIsRangeIndexed := True;
    Exit;
  end;
  LoText := Self.ReadConstBoundText();
  Expect(tkDotDot);
  HiText := Self.ReadConstBoundText();
  CD.ArrayDimLows.Add(LoText);
  CD.ArrayDimHighs.Add(HiText);
  CD.ArrayIsRangeIndexed := True;
end;

procedure TParser.ParseConstArrayType(CD: TConstDecl);
begin
  CD.IsArrayConst := True;
  CD.ArrayDimLows  := TStringList.Create();
  CD.ArrayDimHighs := TStringList.Create();
  { Outer loop walks one or more 'array[...] of' headers — the nested form
    contributes one iteration per 'array' keyword; the comma form contributes
    several dimensions within a single header. }
  while True do
  begin
    Expect(tkArray);
    Expect(tkLBracket);
    if Check(tkIdent) and (PeekKind() = tkRBracket) then
    begin
      { Enum-indexed: 'array[TEnum]' — ident alone followed by ']'. }
      if (CD.ArrayDimLows.Count > 0) or (CD.ArrayIndexType <> '') then
        raise EParseError.Create(Format(
          'Enum-indexed dimension cannot be combined with other dimensions ' +
          'in array const at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      CD.ArrayIndexType := FCurrent.Value;
      Advance();
    end
    else if Check(tkIntLit) or Check(tkIdent) or Check(tkMinus)
         or Check(tkLParen) then
    begin
      Self.ReadConstArrayDim(CD);
      while Check(tkComma) do
      begin
        Advance();
        Self.ReadConstArrayDim(CD);
      end;
    end
    else
      raise EParseError.Create(Format(
        'Expected index type or range in array const at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Expect(tkRBracket);
    Expect(tkOf);
    { A nested 'array' continues the dimension chain; anything else is the
      scalar element type that terminates it. }
    if Check(tkArray) then
      Continue;
    if not Check(tkIdent) then
      raise EParseError.Create(Format(
        'Expected element type name in array const at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    CD.ArrayElemType := FCurrent.Value;
    Advance();
    Break;
  end;
  { Legacy single-dim fields (ArrayLowBound / ArrayHighBound) are resolved
    from ArrayDimLows/ArrayDimHighs by the semantic pass, which can evaluate
    named constants and constant expressions. }
end;

{ Parse a constant value (everything after '=', up to but excluding the
  terminating ';') into CD.  CD.IsArrayConst / CD.TypeName must already be set
  by the caller when they were declared.  Shared by const declarations and
  initialised variable declarations (var G: T = value). }
{ Parse a single scalar element (string/int/float/typecast/named const, with
  an optional leading minus and an optional integer bit-op chain) and append it
  to CD.ArrayElements in row-major order.  Shared by the flat and nested
  (multi-dimensional) array-const value forms. }
procedure TParser.ParseConstArrayScalar(CD: TConstDecl);
var
  CastVal:      Int64;
  FirstOperand: string;
  FirstIsIdent: Boolean;
begin
  FirstOperand := '';
  FirstIsIdent := False;
  if Check(tkMinus) then
  begin
    Advance();
    if Check(tkFloatLit) then
    begin
      CD.ArrayElements.Add('-' + FCurrent.Value);
      Advance();
    end
    else if Check(tkIntLit) then
    begin
      FirstOperand := '-' + FCurrent.Value;
      Advance();
      CD.ArrayElements.Add(FirstOperand);
    end
    else
      raise EParseError.Create(Format(
        'Expected numeric literal after minus in array const at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  end
  else if Check(tkStringLit) then
  begin
    CD.ArrayElements.Add(FCurrent.Value);
    Advance();
  end
  else if Check(tkIntLit) then
  begin
    FirstOperand := FCurrent.Value;
    CD.ArrayElements.Add(FirstOperand);
    Advance();
  end
  else if Check(tkFloatLit) then
  begin
    CD.ArrayElements.Add(FCurrent.Value);
    Advance();
  end
  else if Check(tkIdent) and (PeekKind() = tkLParen)
       and TryParseConstIntTypecast(CastVal) then
  begin
    { TypeName(IntLit) typecast — store the truncated value }
    FirstOperand := IntToStr(CastVal);
    CD.ArrayElements.Add(FirstOperand);
  end
  else if Check(tkIdent) then
  begin
    { named constant or boolean literal }
    FirstOperand := FCurrent.Value;
    FirstIsIdent := True;
    CD.ArrayElements.Add(FirstOperand);
    Advance();
  end
  else
    raise EParseError.Create(Format(
      'Expected constant value in array const at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  { Bit-op continuation — only applies when the element started as an
    integer operand (FirstOperand was set), not strings/floats. }
  if (FirstOperand <> '') and CurrentIsConstBitOp() then
  begin
    if CD.ArrayElementParts = nil then
    begin
      CD.ArrayElementParts := TObjectList.Create(True);
      { Pad with nils for prior elements that were not expressions. }
      while CD.ArrayElementParts.Count < CD.ArrayElements.Count - 1 do
        CD.ArrayElementParts.Add(nil);
    end;
    CD.ArrayElementParts.Add(
      CollectConstBitOpExpr(FirstOperand, FirstIsIdent));
  end
  else if CD.ArrayElementParts <> nil then
    CD.ArrayElementParts.Add(nil);
end;

{ Parse a parenthesised group of comma-separated items.  Each item is either a
  nested group (multi-dimensional initialiser) or a scalar element.  Leaves
  accumulate into CD.ArrayElements in row-major order, which matches the
  contiguous in-memory layout the codegen emitters expect. }
procedure TParser.ParseConstArrayGroup(CD: TConstDecl);
begin
  Expect(tkLParen);
  while True do
  begin
    if Check(tkLParen) then
      Self.ParseConstArrayGroup(CD)
    else
      Self.ParseConstArrayScalar(CD);
    if Check(tkComma) then
      Advance()
    else
      Break;
  end;
  Expect(tkRParen);
end;

procedure TParser.ParseConstValue(CD: TConstDecl);
var
  CastVal:      Int64;
  FirstOperand: string;
  ElemStr:      string;
begin
    { Array const value list: flat (e, e, ...) or nested ((..),(..)). }
    if CD.IsArrayConst then
    begin
      CD.ArrayElements := TStringList.Create();
      Self.ParseConstArrayGroup(CD);
      Exit;
    end;
    { Named-type array const: const A: TArr = (10, 20, 30).  The type is
      a named alias for a static array.  Detect the value-list shape by
      lookahead: '(' value ',' must be a comma-separated list (Pascal has
      no comma operator).  Also catch nested groups: '(' '(' .. }
    if (CD.TypeName <> '') and Check(tkLParen) and
       ((PeekKind2() = tkComma) or (PeekKind() = tkLParen)) then
    begin
      CD.IsArrayConst := True;
      CD.ArrayElements := TStringList.Create();
      Self.ParseConstArrayGroup(CD);
      Exit;
    end;
    { Compile-time integer expression with precedence / parentheses
      (e.g. 2 * 3, 2 + 3 * 4, (1 shl 8) or 7).  Parsed into a normal
      expression AST and folded by the semantic pass (EvalConstIntExpr),
      which also resolves any named-constant references.  A bare literal
      without a trailing operator skips this and uses the fast path below. }
    if Self.ConstRhsStartsIntExpr() then
    begin
      CD.IsString    := False;
      CD.IntValueExpr := Self.ParseExpr();
      Exit;
    end;
    if Check(tkMinus) then
    begin
      Advance();
      if Check(tkFloatLit) then
      begin
        CD.StrVal  := '-' + StripUnderscores(FCurrent.Value);
        CD.IsFloat := True;
        Advance();
      end
      else
      begin
        if not Check(tkIntLit) then
          raise EParseError.Create(Format('Expected numeric literal after minus in const at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        CD.IntVal   := -ParseIntLiteral(FCurrent.Value);
        CD.IsString := False;
        Advance();
        if CurrentIsConstBitOp() then
        begin
          CD.IntExprTokens := CollectConstBitOpExpr(IntToStr(CD.IntVal), False);
          CD.IntVal := 0;
        end;
      end;
    end
    else if Check(tkFloatLit) then
    begin
      CD.StrVal  := StripUnderscores(FCurrent.Value);
      CD.IsFloat := True;
      Advance();
    end
    else if Check(tkIntLit) then
    begin
      { Accept the full 64-bit unsigned range as a bit pattern (e.g.
        $8080808080808080): ParseIntOrUInt64Literal yields the bit pattern and
        flags when the value exceeded High(Int64).  This is the Int64/UInt64
        hex-constant case from issue #133. }
      ParseIntOrUInt64Literal(FCurrent.Value, CD.IntVal, CD.IsUInt64);
      CD.IsString := False;
      Advance();
      if CurrentIsConstBitOp() then
      begin
        CD.IntExprTokens := CollectConstBitOpExpr(IntToStr(CD.IntVal), False);
        CD.IntVal := 0;
        CD.IsUInt64 := False;
      end;
    end
    else if Check(tkIdent) and (PeekKind() = tkLParen)
         and TryParseConstIntTypecast(CastVal) then
    begin
      { TypeName(IntLit) typecast in scalar const init }
      CD.IsString := False;
      if CurrentIsConstBitOp() then
      begin
        CD.IntExprTokens := CollectConstBitOpExpr(IntToStr(CastVal), False);
        CD.IntVal := 0;
      end
      else
        CD.IntVal := CastVal;
    end
    else if Check(tkIdent)
         and (PeekKind() in [tkOr, tkAnd, tkXor, tkShl, tkShr]) then
    begin
      { Bit-op chain whose first operand is a named constant. }
      FirstOperand := FCurrent.Value;
      Advance();
      CD.IntExprTokens := CollectConstBitOpExpr(FirstOperand, True);
      CD.IsString := False;
    end
    else if Check(tkIdent)
         and (SameText(FCurrent.Value, 'True') or SameText(FCurrent.Value, 'False'))
         and not (PeekKind() in [tkPlus, tkOr, tkAnd, tkXor, tkShl, tkShr]) then
    begin
      { Boolean literal constant: const Enabled = True;  True/False are plain
        identifiers (no dedicated token), so catch them here before the generic
        ident-as-string path treats them as a string constant.  TypeName is set
        to Boolean so the debug emitter can type it (renders True/False, not 1/0). }
      CD.IsString := False;
      CD.TypeName := 'Boolean';
      if SameText(FCurrent.Value, 'True') then
        CD.IntVal := 1
      else
        CD.IntVal := 0;
      Advance();
    end
    else if Check(tkLBracket) then
    begin
      { Set-valued constant: const Name [: SetType] = [member, member, ...]
        or the empty set [].  A member is an enum-constant identifier, an integer
        literal, or an inclusive range `lo..hi` (either endpoint an identifier or
        an integer literal).  Each member is stored as a string in SetElements; a
        range is stored as the two endpoints joined by '..' so the semantic pass
        (AnalyseSetConstDecl) can resolve and expand it.  Semantic folds the
        bitmask. }
      CD.IsSet       := True;
      CD.SetElements := TStringList.Create();
      Advance();   { consume '[' }
      if not Check(tkRBracket) then
        while True do
        begin
          if Check(tkIdent) then
            ElemStr := FCurrent.Value
          else if Check(tkIntLit) then
            ElemStr := FCurrent.Value
          else
            raise EParseError.Create(Format(
              'Expected set member (identifier or integer) at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          Advance();
          { Optional range continuation: lo..hi. }
          if Check(tkDotDot) then
          begin
            Advance();
            if Check(tkIdent) or Check(tkIntLit) then
              ElemStr := ElemStr + '..' + FCurrent.Value
            else
              raise EParseError.Create(Format(
                'Expected set range upper bound at line %d col %d in %s',
                [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
            Advance();
          end;
          CD.SetElements.Add(ElemStr);
          if Check(tkComma) then
            Advance()
          else
            Break;
        end;
      Expect(tkRBracket);
    end
    else if Check(tkStringLit) or Check(tkIdent) then
    begin
      CD.IsString := True;
      if Check(tkIdent) then
      begin
        CD.ConstParts := TStringList.Create();
        CD.ConstParts.AddObject(FCurrent.Value, TObject(1));
      end
      else
        CD.StrVal := FCurrent.Value;
      Advance();
      while Check(tkPlus) do
      begin
        Advance();
        if Check(tkStringLit) or Check(tkIdent) then
        begin
          if CD.ConstParts <> nil then
          begin
            if Check(tkIdent) then
              CD.ConstParts.AddObject(FCurrent.Value, TObject(1))
            else
              CD.ConstParts.AddObject(FCurrent.Value, nil);
          end
          else if Check(tkIdent) then
          begin
            CD.ConstParts := TStringList.Create();
            CD.ConstParts.AddObject(CD.StrVal, nil);
            CD.ConstParts.AddObject(FCurrent.Value, TObject(1));
            CD.StrVal := '';
          end
          else
            CD.StrVal := CD.StrVal + FCurrent.Value;
          Advance();
        end
        else
          raise EParseError.Create(Format(
            'Expected string literal after ''+'' in const at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      end;
    end
    else
      raise EParseError.Create(Format(
        'Expected numeric or string constant at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
end;

function TParser.ParseEnumDef: TEnumTypeDef;
var
  MName: string;
  NextVal: Integer;
  Negative: Boolean;
  ExplicitVal: Integer;
begin
  Result := TEnumTypeDef.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    NextVal := 0;
    Expect(tkLParen);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected enum member at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    MName := FCurrent.Value;
    Advance();
    if Check(tkEquals) then
    begin
      Advance();
      Negative := False;
      if Check(tkMinus) then
      begin
        Negative := True;
        Advance();
      end;
      if not Check(tkIntLit) then
        raise EParseError.Create(Format('Expected integer after ''='' in enum at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      ExplicitVal := ParseIntLiteral(FCurrent.Value);
      if Negative then ExplicitVal := -ExplicitVal;
      Advance();
      NextVal := ExplicitVal;
    end;
    Result.AddMember(MName, NextVal);
    Inc(NextVal);
    while Check(tkComma) do
    begin
      Advance();
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected enum member at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      MName := FCurrent.Value;
      Advance();
      if Check(tkEquals) then
      begin
        Advance();
        Negative := False;
        if Check(tkMinus) then
        begin
          Negative := True;
          Advance();
        end;
        if not Check(tkIntLit) then
          raise EParseError.Create(Format('Expected integer after ''='' in enum at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        ExplicitVal := ParseIntLiteral(FCurrent.Value);
        if Negative then ExplicitVal := -ExplicitVal;
        Advance();
        NextVal := ExplicitVal;
      end;
      Result.AddMember(MName, NextVal);
      Inc(NextVal);
    end;
    Expect(tkRParen);
  except
    Result.Free();
    raise;
  end;
end;

function TParser.ParseSetDef: TSetTypeDef;
var
  Lo, Hi: string;
begin
  Result := TSetTypeDef.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkSet);
    Expect(tkOf);
    if Check(tkIdent) and (PeekKind() <> tkDotDot) then
    begin
      { Named base type: set of Byte / Boolean / TEnum. }
      Result.BaseTypeName := FCurrent.Value;
      Advance();
    end
    else if Check(tkIntLit) or Check(tkIdent) then
    begin
      { Integer subrange base type: set of 0..255 / 1..10 / Lo..Hi.  Stored as
        'lo..hi' in BaseTypeName; the semantic pass resolves and validates it. }
      Lo := FCurrent.Value;
      Advance();
      Expect(tkDotDot);
      if not (Check(tkIntLit) or Check(tkIdent)) then
        raise EParseError.Create(Format(
          'Expected set subrange upper bound at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Hi := FCurrent.Value;
      Advance();
      Result.BaseTypeName := Lo + '..' + Hi;
    end
    else
      raise EParseError.Create(Format(
        'Expected base type or integer subrange after ''set of'' ' +
        'at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  except
    Result.Free();
    raise;
  end;
end;

function TParser.ParseProceduralTypeDef: TProceduralTypeDef;
begin
  Result := TProceduralTypeDef.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    if Check(tkFunction) then
    begin
      Result.IsFunction := True;
      Advance();
    end
    else if Check(tkProcedure) then
    begin
      Result.IsFunction := False;
      Advance();
    end
    else
      raise EParseError.Create(Format(
        'Expected ''function'' or ''procedure'' at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    if Check(tkLParen) then
    begin
      Advance();  { '(' }
      if not Check(tkRParen) then
        ParseParamList(Result.Params);
      Expect(tkRParen);
    end;
    if Result.IsFunction then
    begin
      Expect(tkColon);
      Result.ReturnTypeName := ParseTypeName();
    end;
    { Optional 'of object' modifier — turns the bare procedural type into
      a method-pointer type, with a 16-byte (Code, Data) representation. }
    if Check(tkOf) then
    begin
      Advance();  { consume 'of' }
      if not (Check(tkIdent) and SameText(FCurrent.Value, 'object')) then
        raise EParseError.Create(Format(
          'Expected ''object'' after ''of'' in procedural-type declaration at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Advance();  { consume 'object' }
      Result.IsMethodPtr := True;
    end;
  except
    Result.Free();
    raise;
  end;
end;

function TParser.ParseRecordDef: TRecordTypeDef;
var
  MethDecl:         TMethodDecl;
  CurrStatic:       Boolean;   { current section's static (class-level) association }
  CurrStaticBlock:  Boolean;   { bare `static var`/`static const` block (see
                                 ParseClassDef; BUG-036) }
  CurrVisibility:   TMemberVisibility; { current section's visibility }
  LocalStatic:      Boolean;
  FieldCountBefore: Integer;
  FieldIdx:         Integer;
begin
  Result := TRecordTypeDef.Create();
  CurrStatic     := False;
  CurrStaticBlock := False;
  CurrVisibility := mvPublic;
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkRecord);
    repeat
      { Bare `static var` / `static const` SECTION keyword.  `static` is a soft
        keyword: a section qualifier only when followed by `var`/`const`; a
        field literally named `Static` (`Static: Integer;`) falls through. }
      if Check(tkIdent) and SameText(FCurrent.Value, 'static') and
         (PeekKind() in [tkVar, tkConst]) then
      begin
        CurrStatic := True;
        CurrStaticBlock := True;
        Advance();  { the following var/const section belongs to this static section }
      end
      { Optional `strict` soft keyword before private/protected (record fields). }
      else if Check(tkIdent) and SameText(FCurrent.Value, 'strict') and
              (PeekKind() = tkIdent) and
              (SameText(PeekValueAt(1), 'private') or
               SameText(PeekValueAt(1), 'protected')) then
      begin
        Advance();  { consume `strict` }
        if SameText(FCurrent.Value, 'private') then
          CurrVisibility := mvStrictPrivate
        else
          CurrVisibility := mvStrictProtected;
        CurrStatic := False;
        CurrStaticBlock := False;
        Advance();  { consume private/protected }
        if Check(tkIdent) and SameText(FCurrent.Value, 'static') and
           (PeekKind() in [tkVar, tkConst, tkFunction, tkProcedure]) then
        begin
          CurrStatic := True;
          CurrStaticBlock := PeekKind() in [tkVar, tkConst];
          Advance();
        end;
      end
      else if Check(tkIdent) and SameText(FCurrent.Value, 'strict') and
              (PeekKind() = tkIdent) and
              (SameText(PeekValueAt(1), 'public') or
               SameText(PeekValueAt(1), 'published')) then
        raise EParseError.Create(Format(
          'Only ''private'' or ''protected'' may be ''strict'' at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]))
      { Visibility section keywords, with an optional trailing `static`.
        A new visibility section resets static. }
      else if Check(tkIdent) and (SameText(FCurrent.Value, 'private') or
                                  SameText(FCurrent.Value, 'public') or
                                  SameText(FCurrent.Value, 'protected')) then
      begin
        if SameText(FCurrent.Value, 'private') then
          CurrVisibility := mvPrivate
        else if SameText(FCurrent.Value, 'protected') then
          CurrVisibility := mvProtected
        else
          CurrVisibility := mvPublic;
        CurrStatic := False;
        CurrStaticBlock := False;
        Advance();
        if Check(tkIdent) and SameText(FCurrent.Value, 'static') and
           (PeekKind() in [tkVar, tkConst, tkFunction, tkProcedure]) then
        begin
          CurrStatic := True;
          CurrStaticBlock := PeekKind() in [tkVar, tkConst];
          Advance();
        end;
      end
      else if Check(tkConst) then
        ParseConstBlock(Result.ConstDecls)
      else if Check(tkVar) then
        Advance()  { optional `var` keyword before field declarations }
      { `class operator Add(const A, B: TFoo): TFoo;` — a static method whose
        name is a reserved operator name. }
      else if AtClassOperator() then
      begin
        MethDecl := ParseClassOperatorDecl();
        MethDecl.Visibility := CurrVisibility;
        Result.Methods.Add(MethDecl);
      end
      { Method declarations — before the field branch so a leading `static`
        prefix is not mistaken for a field name. }
      else if Check(tkFunction) or Check(tkProcedure) or
              (Check(tkIdent) and SameText(FCurrent.Value, 'static') and
               (PeekKind() in [tkFunction, tkProcedure])) then
      begin
        if CurrStatic and CurrStaticBlock then
        begin
          { a bare `static var`/`static const` block ends at the first
            method/property member (BUG-036) }
          CurrStatic := False;
          CurrStaticBlock := False;
        end;
        LocalStatic := CurrStatic;
        if Check(tkIdent) and SameText(FCurrent.Value, 'static') then
        begin
          LocalStatic := True;
          Advance();
        end;
        if Check(tkFunction) then
          MethDecl := ParseMethodDecl(True)
        else
          MethDecl := ParseMethodDecl(False);
        MethDecl.IsStatic := LocalStatic;
        MethDecl.Visibility := CurrVisibility;
        Result.Methods.Add(MethDecl);
      end
      else if Check(tkIdent) or Check(tkLBracket) then
      begin
        FieldCountBefore := Result.Fields.Count;
        ParseFieldDecl(Result.Fields);
        for FieldIdx := FieldCountBefore to Result.Fields.Count - 1 do
        begin
          if CurrStatic then
            TFieldDecl(Result.Fields.Items[FieldIdx]).IsClassVar := True;
          TFieldDecl(Result.Fields.Items[FieldIdx]).Visibility := CurrVisibility;
        end;
      end
      else
        Break;
    until False;
    Expect(tkEnd);
  except
    Result.Free();
    raise;
  end;
end;

function TParser.ParseGenericName: string;
var
  TypeArgs: string;
begin
  if not Check(tkIdent) then
    raise EParseError.Create(Format('Expected identifier at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  Result := FCurrent.Value;
  Advance();
  if Check(tkNotEquals) then
  begin
    { Diamond in type-name context: TFoo<> — lexer folds '<>' into tkNotEquals }
    Advance();
    Exit(Result + '<>');
  end;
  if Check(tkLessThan) then
  begin
    Advance();  { consume '<' }
    TypeArgs := FCurrent.Value;
    Advance();
    while Check(tkComma) do
    begin
      Advance();
      TypeArgs := TypeArgs + ',' + FCurrent.Value;
      Advance();
    end;
    Expect(tkGreaterThan);
    Result := Result + '<' + TypeArgs + '>';
  end;
end;

function TParser.ParseClassDef: TClassTypeDef;
var
  CurrPublished:    Boolean;
  CurrVisibility:   TMemberVisibility; { current section's visibility }
  CurrStatic:       Boolean;   { current section's static (class-level) association }
  CurrStaticBlock:  Boolean;   { CurrStatic came from a bare `static var`/
                                 `static const` BLOCK (not a `public static`
                                 section) — such a block ends at the first
                                 method/property, so a member declared after
                                 it must not silently become static (BUG-036) }
  LocalStatic:      Boolean;   { effective static for the member being parsed }
  MethDecl:         TMethodDecl;
  PropDecl:         TPropertyDecl;
  FieldCountBefore: Integer;
  FieldIdx:         Integer;
  PendAttrNames:    TStringList; { attribute list captured at the top of the
                                   member loop, attached to the next field or
                                   method declaration }
  PendAttrUses:     TObjectList; { non-owning; parallel TAttributeUse items }
  AUIdx:            Integer;
begin
  PendAttrNames := TStringList.Create();
  PendAttrUses  := TObjectList.Create(False);
  Result := TClassTypeDef.Create();
  try
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkClass);
    { Forward class declaration: the keyword `class` immediately followed by
      `;` (no ancestor clause, no body).  `class(TBase);` and `class end;` are
      complete empty classes, not forwards.  The full declaration later in the
      same type scope completes it (see uSemantic.AnalyseTypeDecls). }
    if Check(tkSemicolon) then
    begin
      Result.IsForward := True;
      Exit;
    end;
    if Check(tkLParen) then
    begin
      Advance();
      { First name may be a plain class name, a unit-qualified ancestor
        (Unit.TParent), or a generic interface name like IFoo<T>.  ParseTypeName
        already absorbs the unit qualifier and (nested) generic arguments, so a
        qualified ancestor disambiguates a same-named type via the resolver. }
      Result.ParentName := ParseTypeName();
      { Additional names after a comma are implemented interface names }
      while Check(tkComma) do
      begin
        Advance();
        Result.ImplementsNames.Add(ParseTypeName());
      end;
      Expect(tkRParen);
    end;
    { Class body: fields, properties, and methods in any order.  A field
      declaration may be preceded by an attribute list, so accept
      `[` as a legal field-start token too.  Visibility keywords
      (private/public/protected/published) update CurrPublished, which
      is then attached to each method decl so codegen can emit a
      published-method table entry. }
    CurrPublished  := False;
    CurrVisibility := mvPublic;
    CurrStatic     := False;
    CurrStaticBlock := False;
    repeat
      { An attribute list may precede a field or a method declaration.
        Capture it here and attach it to whichever member follows. }
      if Check(tkLBracket) then
        ParseAttributeList(PendAttrNames, PendAttrUses);
      { Optional `strict` soft keyword preceding `private`/`protected`.  `strict`
        is not a real token — recognise it only at section start, immediately
        before `private` or `protected`, so an ordinary identifier named `strict`
        elsewhere is unaffected.  `strict public`, `strict published` and bare
        `strict` are errors. }
      if Check(tkIdent) and SameText(FCurrent.Value, 'strict') and
         (PeekKind() = tkIdent) and
         (SameText(PeekValueAt(1), 'private') or
          SameText(PeekValueAt(1), 'protected')) then
      begin
        Advance();  { consume `strict`; the following private/protected sets visibility }
        if SameText(FCurrent.Value, 'private') then
          CurrVisibility := mvStrictPrivate
        else
          CurrVisibility := mvStrictProtected;
        CurrPublished := False;
        CurrStatic    := False;
        Advance();  { consume the private/protected keyword }
        { Optional trailing `static` section qualifier — `strict private static var`. }
        if Check(tkIdent) and SameText(FCurrent.Value, 'static') and
           ((PeekKind() in [tkVar, tkConst, tkFunction, tkProcedure,
                            tkConstructor, tkDestructor]) or
            ((PeekKind() = tkIdent) and SameText(PeekValueAt(1), 'property'))) then
        begin
          CurrStatic := True;
          { `<visibility> static var/const` is the BLOCK form (ends at the
            first method/property — BUG-036); followed by a routine or
            property it is the section form applying until the next
            visibility keyword. }
          CurrStaticBlock := PeekKind() in [tkVar, tkConst];
          Advance();
        end;
      end
      { `strict` not followed by private/protected is an error inside a class body. }
      else if Check(tkIdent) and SameText(FCurrent.Value, 'strict') and
              (PeekKind() = tkIdent) and
              (SameText(PeekValueAt(1), 'public') or
               SameText(PeekValueAt(1), 'published')) then
        raise EParseError.Create(Format(
          'Only ''private'' or ''protected'' may be ''strict'' at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]))
      { Visibility section keyword (private/public/protected/published),
        optionally followed by a `static` qualifier.  A visibility keyword
        resets the static section (you must re-state `static` after it). }
      else if Check(tkIdent) and (SameText(FCurrent.Value, 'private') or
                              SameText(FCurrent.Value, 'public') or
                              SameText(FCurrent.Value, 'protected') or
                              SameText(FCurrent.Value, 'published')) then
      begin
        CurrPublished := SameText(FCurrent.Value, 'published');
        if SameText(FCurrent.Value, 'private') then
          CurrVisibility := mvPrivate
        else if SameText(FCurrent.Value, 'protected') then
          CurrVisibility := mvProtected
        else if SameText(FCurrent.Value, 'published') then
          CurrVisibility := mvPublished
        else
          CurrVisibility := mvPublic;
        CurrStatic    := False;  { a new visibility section is non-static unless
                                   `static` follows }
        CurrStaticBlock := False;
        Advance();  { consume the visibility modifier }
        { Optional trailing `static` section qualifier.  `static` is a soft
          keyword: treat it as a qualifier only when it introduces a static
          member (followed by var/const/method/property), NOT when it is a
          field literally named `Static` (`private Static: Boolean;`). }
        if Check(tkIdent) and SameText(FCurrent.Value, 'static') and
           ((PeekKind() in [tkVar, tkConst, tkFunction, tkProcedure,
                            tkConstructor, tkDestructor]) or
            ((PeekKind() = tkIdent) and SameText(PeekValueAt(1), 'property'))) then
        begin
          CurrStatic := True;
          { `<visibility> static var/const` is the BLOCK form (ends at the
            first method/property — BUG-036); followed by a routine or
            property it is the section form applying until the next
            visibility keyword. }
          CurrStaticBlock := PeekKind() in [tkVar, tkConst];
          Advance();
        end;
      end
      { Bare `static` SECTION keyword — `static var` / `static const` only.
        `static` is a soft keyword: it acts as a section qualifier only when
        immediately followed by `var` or `const`.  Followed by anything else
        (e.g. `Static: Boolean;` — a field literally named Static, or `Static,`)
        it is an ordinary field identifier and falls through to the field
        branch.  The `static function/procedure/property` PREFIX forms are
        handled in the method/property branches below. }
      else if Check(tkIdent) and SameText(FCurrent.Value, 'static') and
              (PeekKind() in [tkVar, tkConst]) then
      begin
        CurrStatic := True;
        CurrStaticBlock := True;
        Advance();  { consume `static`; the following `var`/`const` section is
                     part of this static section }
      end
      else if Check(tkConst) then
        ParseConstBlock(Result.ConstDecls)
      else if Check(tkVar) then
        Advance()  { optional 'var' keyword before field declarations — consume and continue }
      else if (Check(tkIdent) and SameText(FCurrent.Value, 'property')) or
              (Check(tkIdent) and SameText(FCurrent.Value, 'static') and
               (PeekKind() = tkIdent) and SameText(PeekValueAt(1), 'property')) then
      begin
        if CurrStatic and CurrStaticBlock then
        begin
          { a bare `static var`/`static const` block ends at the first
            method/property member (BUG-036) }
          CurrStatic := False;
          CurrStaticBlock := False;
        end;
        LocalStatic := CurrStatic;
        if Check(tkIdent) and SameText(FCurrent.Value, 'static') then
        begin
          LocalStatic := True;
          Advance();  { consume per-member `static` prefix }
        end;
        PropDecl := ParsePropertyDecl();
        PropDecl.IsStatic := LocalStatic;
        PropDecl.Visibility := CurrVisibility;
        Result.Properties.Add(PropDecl);
      end
      { `class operator Add(const A, B: TFoo): TFoo;` — a static method whose
        name is a reserved operator name. }
      else if AtClassOperator() then
      begin
        MethDecl := ParseClassOperatorDecl();
        MethDecl.Visibility := CurrVisibility;
        Result.Methods.Add(MethDecl);
      end
      { Method declarations — checked BEFORE the generic field branch so that a
        leading `static` prefix on a method is not mistaken for a field name. }
      else if Check(tkFunction) or Check(tkProcedure) or
              Check(tkConstructor) or Check(tkDestructor) or
              (Check(tkIdent) and SameText(FCurrent.Value, 'static') and
               (PeekKind() in [tkFunction, tkProcedure, tkConstructor, tkDestructor])) then
      begin
        if CurrStatic and CurrStaticBlock then
        begin
          { a bare `static var`/`static const` block ends at the first
            method/property member (BUG-036) }
          CurrStatic := False;
          CurrStaticBlock := False;
        end;
        LocalStatic := CurrStatic;
        if Check(tkIdent) and SameText(FCurrent.Value, 'static') then
        begin
          LocalStatic := True;
          Advance();  { consume per-member `static` prefix }
        end;
        if Check(tkConstructor) or Check(tkDestructor) then
        begin
          if LocalStatic then
            raise EParseError.Create(Format(
              'A constructor or destructor cannot be declared static at line %d col %d in %s'
              + ' — Blaise has no type-initialiser (class constructor); use the unit'
              + ' initialization/finalization sections',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          MethDecl := ParseMethodDecl(False);
        end
        else if Check(tkFunction) then
          MethDecl := ParseMethodDecl(True)
        else
          MethDecl := ParseMethodDecl(False);
        MethDecl.IsPublished := CurrPublished;
        MethDecl.IsStatic    := LocalStatic;
        MethDecl.Visibility  := CurrVisibility;
        { Attach the pending attribute list, if any, to this method. }
        for AUIdx := 0 to PendAttrUses.Count - 1 do
          MethDecl.AttrUses.Add(PendAttrUses.Get(AUIdx));
        PendAttrUses.Clear();
        PendAttrNames.Clear();
        Result.Methods.Add(MethDecl);
      end
      else if Check(tkIdent) or Check(tkLBracket) then
      begin
        FieldCountBefore := Result.Fields.Count;
        ParseFieldDecl(Result.Fields);
        { Stamp class-var flag and visibility on every field this decl produced. }
        for FieldIdx := FieldCountBefore to Result.Fields.Count - 1 do
        begin
          if CurrStatic then
            TFieldDecl(Result.Fields.Items[FieldIdx]).IsClassVar := True;
          TFieldDecl(Result.Fields.Items[FieldIdx]).Visibility := CurrVisibility;
        end;
        { A pending attribute list captured at the loop top belongs to this
          field decl ([Weak] etc.).  Field attributes stay name-driven — the
          TAttributeUse items are discarded. }
        if PendAttrNames.Count > 0 then
        begin
          for FieldIdx := FieldCountBefore to Result.Fields.Count - 1 do
            TFieldDecl(Result.Fields.Items[FieldIdx]).Attributes.AddStrings(PendAttrNames);
          PendAttrNames.Clear();
          PendAttrUses.Clear();
        end;
      end
      else
        Break;
    until False;
    { Empty class declaration: TFoo = class(TBase); has no body, no 'end' }
    if Check(tkEnd) then
      Advance()
    else if not (Check(tkSemicolon) or Check(tkEOF)) then
      raise EParseError.Create(Format(
        'Expected ''end'' in class definition at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  except
    Result.Free();
    raise;
  end;
  finally
    PendAttrNames.Free();
    PendAttrUses.Free();
  end;
end;

function TParser.ParseInterfaceDef: TInterfaceTypeDef;
begin
  Result := TInterfaceTypeDef.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkIntf);
    { Forward interface declaration `IFoo = interface;` — no parent, no body,
      completed later in the same type scope. }
    if Check(tkSemicolon) then
    begin
      Result.IsForward := True;
      Exit;
    end;
    if Check(tkLParen) then
    begin
      Advance();
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected parent interface name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.ParentName := FCurrent.Value;
      Advance();
      Expect(tkRParen);
    end;
    while Check(tkProcedure) or Check(tkFunction) or
          Check(tkConstructor) or Check(tkDestructor) or
          (Check(tkIdent) and SameText(FCurrent.Value, 'property')) do
    begin
      if Check(tkIdent) then
        Result.Properties.Add(ParsePropertyDecl())
      else if Check(tkFunction) then
        Result.Methods.Add(ParseMethodDecl(True))
      else
        Result.Methods.Add(ParseMethodDecl(False));
    end;
    Expect(tkEnd);
  except
    Result.Free();
    raise;
  end;
end;

function TParser.AtClassOperator: Boolean;
begin
  { `operator` is a CONTEXTUAL identifier — special only directly after
    `class` and followed by the operator name.  A field or method named
    `Operator` still parses normally. }
  Result := Check(tkClass) and (PeekKind() = tkIdent) and
            SameText(PeekValueAt(1), 'operator') and
            (PeekKind2() = tkIdent);
end;

function TParser.ParseClassOperatorDecl(ACanHaveNestedProcs: Boolean): TMethodDecl;
var
  OpLine, OpCol: Integer;
  OpName:        string;
  Kind:          TOperatorKind;
  WantArity:     Integer;
  GotArity:      Integer;
begin
  OpLine := FCurrent.Line;
  OpCol  := FCurrent.Col;
  if FGenericTypeDepth > 0 then
    raise EParseError.Create(Format(
      'A ''class operator'' cannot be declared inside a generic type at line %d col %d in %s'
      + ' — operators on generic types are deferred',
      [OpLine, OpCol, FLexer.Filename]));
  Expect(tkClass);
  Advance();   { consume the contextual `operator` identifier }
  { The operator NAME is validated AFTER parsing, off Result.Name: for an
    out-of-line body (`class operator TFoo.Add(...)`) the identifier here is
    the OWNER type, and ParseMethodDecl moves the post-dot name into Name. }
  Result := ParseMethodDecl(True, ACanHaveNestedProcs, True);
  OpName := Result.Name;
  Kind   := OperatorKindFromName(OpName);
  if Kind = okNone then
  begin
    Result.Free();
    Result := nil;
    raise EParseError.Create(Format(
      'Unknown operator name ''%s'' at line %d col %d in %s — expected one of'
      + ' Add, Subtract, Multiply, Divide, Equal, NotEqual, LessThan, GreaterThan,'
      + ' LessThanOrEqual, GreaterThanOrEqual, Negative',
      [OpName, OpLine, OpCol, FLexer.Filename]));
  end;
  Result.OperatorKind := Kind;
  WantArity := OperatorKindArity(Kind);
  GotArity  := Result.Params.Count;
  if GotArity <> WantArity then
  begin
    Result.Free();
    Result := nil;
    raise EParseError.Create(Format(
      'Operator ''%s'' must take exactly %d parameter(s), got %d, at line %d col %d in %s',
      [OpName, WantArity, GotArity, OpLine, OpCol, FLexer.Filename]));
  end;
end;

function TParser.ParseMethodDecl(IsFunction: Boolean; ACanHaveNestedProcs: Boolean;
  AIsOperator: Boolean): TMethodDecl;
var
  TempParams:       TStringList;
  TempConstraints:  TStringList;
  Constraint:       string;
  IsForward:        Boolean;   { 'forward;' directive seen — no body follows }
begin
  TempParams      := nil;
  TempConstraints := nil;
  IsForward       := False;
  Result := TMethodDecl.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    { An operator declaration has no `function` keyword — the caller has
      already consumed `class operator` and the operator NAME is current.
      Everything after the name (type params, qualified name, params, `:`
      return type, directives, body) is identical to a function. }
    if AIsOperator then
    begin
      Result.IsOperator := True;
      Result.IsStatic   := True;   { operators receive no Self }
      IsFunction        := True;   { a return type is mandatory }
    end
    else if IsFunction then
      Expect(tkFunction)
    else if Check(tkProcedure) then
      Advance()
    else if Check(tkConstructor) or Check(tkDestructor) then
      Advance()
    else
      Expect(tkProcedure);  { will produce a clear error message }
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected method name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result.Name := FCurrent.Value;
    Advance();
    { Type parameter list: applies to the method itself ('function Identity<T>')
      or the generic owner class ('procedure TList<T>.Add').  Parse tentatively;
      DOT after '>' decides which case it is. }
    if Check(tkLessThan) and (PeekKind() = tkIdent) and
       (PeekKind2() in [tkGreaterThan, tkComma, tkColon]) then
    begin
      TempParams      := TStringList.Create();
      TempConstraints := TStringList.Create();
      try
        Advance();  { consume '<' }
        if not Check(tkIdent) then
          raise EParseError.Create(Format('Expected type parameter name at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        TempParams.Add(FCurrent.Value);
        Advance();
        Constraint := '';
        if Check(tkColon) then
        begin
          Advance();
          if      Check(tkClass)  then begin Constraint := 'class';  Advance(); end
          else if Check(tkRecord) then begin Constraint := 'record'; Advance(); end
          else if Check(tkIdent)  then begin Constraint := FCurrent.Value; Advance(); end
          else
            raise EParseError.Create(Format(
              'Expected ''class'', ''record'', or a type name after '':'' at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        end;
        TempConstraints.Add(Constraint);
        while Check(tkComma) do
        begin
          Advance();
          if not Check(tkIdent) then
            raise EParseError.Create(Format('Expected type parameter name at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          TempParams.Add(FCurrent.Value);
          Advance();
          Constraint := '';
          if Check(tkColon) then
          begin
            Advance();
            if      Check(tkClass)  then begin Constraint := 'class';  Advance(); end
            else if Check(tkRecord) then begin Constraint := 'record'; Advance(); end
            else if Check(tkIdent)  then begin Constraint := FCurrent.Value; Advance(); end
            else
              raise EParseError.Create(Format(
                'Expected ''class'', ''record'', or a type name after '':'' at line %d col %d in %s',
                [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          end;
          TempConstraints.Add(Constraint);
        end;
        Expect(tkGreaterThan);
        if Check(tkDot) then
        begin
          { Generic owner: procedure TList<T>.Add(...) — constraints are
            carried on the type decl, not repeated on method impls. }
          Result.OwnerTypeParams := TempParams;
          TempParams := nil;
          TempConstraints.Free();
          TempConstraints := nil;
        end
        else
        begin
          { Method's own type params: function Identity<T>(...) }
          Result.TypeParams           := TempParams;
          Result.TypeParamConstraints := TempConstraints;
          TempParams      := nil;
          TempConstraints := nil;
        end;
      finally
        TempParams.Free();
        TempConstraints.Free();
      end;
    end;
    { Qualified name: TypeName.MethodName or TypeName<T>.MethodName }
    if Check(tkDot) then
    begin
      Advance();
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected method name after ''.'' at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.OwnerTypeName := Result.Name;
      Result.Name          := FCurrent.Value;
      Advance();
      { Out-of-line generic METHOD impl: function TUtil.Pick<T>(...).  The
        method's own type params follow the qualified name (the <T> BEFORE the
        dot is the owner's, handled above).  Parse them into TypeParams so the
        impl matches its in-class generic-method template. }
      if (Result.TypeParams = nil) and Check(tkLessThan) and
         (PeekKind() = tkIdent) and
         (PeekKind2() in [tkGreaterThan, tkComma, tkColon]) then
      begin
        Result.TypeParams           := TStringList.Create();
        Result.TypeParamConstraints := TStringList.Create();
        Advance();  { consume '<' }
        repeat
          if not Check(tkIdent) then
            raise EParseError.Create(Format(
              'Expected type parameter name at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          Result.TypeParams.Add(FCurrent.Value);
          Advance();
          Constraint := '';
          if Check(tkColon) then
          begin
            Advance();
            if      Check(tkClass)  then begin Constraint := 'class';  Advance(); end
            else if Check(tkRecord) then begin Constraint := 'record'; Advance(); end
            else if Check(tkIdent)  then begin Constraint := FCurrent.Value; Advance(); end
            else
              raise EParseError.Create(Format(
                'Expected ''class'', ''record'', or a type name after '':'' at line %d col %d in %s',
                [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          end;
          Result.TypeParamConstraints.Add(Constraint);
          if not Check(tkComma) then Break;
          Advance();
        until False;
        Expect(tkGreaterThan);
      end;
    end;
    if Check(tkLParen) then
    begin
      Advance();
      if not Check(tkRParen) then
        ParseParamList(Result.Params);
      Expect(tkRParen);
    end;
    if IsFunction then
    begin
      Expect(tkColon);
      Result.ReturnTypeName := ParseTypeName();
    end;
    Expect(tkSemicolon);
    { Consume method directives: virtual, override, and identifier-form directives
      such as inline, stdcall, cdecl, abstract, reintroduce, static, assembler, etc. }
    while True do
    begin
      if Check(tkVirtual) then
      begin
        Result.IsVirtual := True;
        Advance();
        if Check(tkSemicolon) then Advance();
      end
      else if Check(tkOverride) then
      begin
        Result.IsOverride := True;
        Advance();
        if Check(tkSemicolon) then Advance();
      end
      else if Check(tkExternal) then
      begin
        Result.IsExternal := True;
        Advance();
        { optional: a library name string — external 'c' name 'malloc'.
          Records a unit-level link dependency (works for implementation
          imports too, so the private routine's library still propagates). }
        if Check(tkStringLit) then
        begin
          Result.ExternalLib := FCurrent.Value;
          AddLinkLib(FCurrent.Value, FCurrent.Line, FCurrent.Col);
          Advance();
        end;
        { optional: name 'c_symbol' }
        if Check(tkIdent) and SameText(FCurrent.Value, 'name') then
        begin
          Advance();
          Result.ExternalName := FCurrent.Value;
          Expect(tkStringLit);
        end;
        if Check(tkSemicolon) then Advance();
      end
      else if Check(tkIdent) and SameText(FCurrent.Value, 'overload') then
      begin
        Result.IsOverload := True;
        Advance();
        if Check(tkSemicolon) then Advance();
      end
      else if Check(tkIdent) and SameText(FCurrent.Value, 'abstract') then
      begin
        Result.IsAbstract := True;
        Result.IsVirtual  := True;  { abstract implies virtual }
        Advance();
        if Check(tkSemicolon) then Advance();
      end
      else if Check(tkIdent) and
              (SameText(FCurrent.Value, 'inline')      or
               SameText(FCurrent.Value, 'stdcall')     or
               SameText(FCurrent.Value, 'cdecl')       or
               SameText(FCurrent.Value, 'register')    or
               SameText(FCurrent.Value, 'pascal')      or
               SameText(FCurrent.Value, 'safecall')    or
               SameText(FCurrent.Value, 'reintroduce') or
               SameText(FCurrent.Value, 'final')       or
               SameText(FCurrent.Value, 'assembler')   or
               SameText(FCurrent.Value, 'nostackframe') or
               SameText(FCurrent.Value, 'varargs')     or
               SameText(FCurrent.Value, 'forward')     or
               SameText(FCurrent.Value, 'deprecated')  or
               SameText(FCurrent.Value, 'platform')    or
               SameText(FCurrent.Value, 'experimental')) then
      begin
        if SameText(FCurrent.Value, 'inline') then
          Result.IsInline := True
        else if SameText(FCurrent.Value, 'nostackframe') then
          Result.NoStackFrame := True
        else if SameText(FCurrent.Value, 'varargs') then
          Result.IsVarArgs := True
        else if SameText(FCurrent.Value, 'forward') then
          IsForward := True
        else if SameText(FCurrent.Value, 'cdecl')    or
                SameText(FCurrent.Value, 'stdcall')  or
                SameText(FCurrent.Value, 'register') or
                SameText(FCurrent.Value, 'pascal')   or
                SameText(FCurrent.Value, 'safecall') then
          Result.CallingConv := LowerCase(FCurrent.Value);
        Advance();
        if Check(tkSemicolon) then Advance();
      end
      else
        Break;
    end;
    { Body is optional — present for standalone impls and inline class methods,
      absent for class forward declarations, external declarations, etc.
      When ACanHaveNestedProcs is True (standalone proc context), a bare
      'procedure'/'function' keyword triggers body parsing so that a nested
      sub-procedure declaration is parsed as part of the enclosing routine.
      A 'forward;'-declared routine has NO body here — the following
      'procedure'/'function' is the SEPARATE implementation, not a nested
      proc.  Without this guard the forward decl swallowed the real
      implementation (and everything up to the program's 'end.') as its body
      (issue #130 bug2). }
    if (not Result.IsExternal) and (not IsForward) and Check(tkAsmBlock) then
    begin
      { Inline-assembler body: the lexer already captured the whole asm ... end
        block as one tkAsmBlock token whose Value is the verbatim text.  Wrap it
        in a TBlock holding a single TAsmStmt; semantic treats it as opaque and
        codegen emits the text verbatim. }
      Result.Body := Self.ParseAsmBody();
      Expect(tkSemicolon);
    end
    else if (not Result.IsExternal) and (not IsForward) and
       (Check(tkBegin) or Check(tkVar) or Check(tkType) or Check(tkConst) or
        (ACanHaveNestedProcs and (Check(tkProcedure) or Check(tkFunction)))) then
    begin
      Result.Body := ParseBlock();
      Expect(tkSemicolon);
    end;
  except
    Result.Free();
    raise;
  end;
end;

{ Build a TBlock whose sole statement is the TAsmStmt for the current
  tkAsmBlock token, then consume that token. }
function TParser.ParseAsmBody: TBlock;
var
  Stmt: TAsmStmt;
begin
  Result := TBlock.Create();
  Stmt := TAsmStmt.Create();
  Stmt.Line := FCurrent.Line;
  Stmt.Col  := FCurrent.Col;
  Stmt.Code := FCurrent.Value;
  Result.Stmts.Add(Stmt);
  Advance();   { consume the tkAsmBlock token }
end;

procedure TParser.ParseParamList(AParams: TObjectList);
var
  Par:         TMethodParam;
  I:           Integer;
  Names:       TStringList;
  TypeN:       string;
  IsVarGrp:    Boolean;
  IsOutGrp:    Boolean;
  IsConstGrp:  Boolean;
  IsOpenArr:   Boolean;
  Default:     TASTExpr;
  DefLine:     Integer;
  DefCol:      Integer;
begin
  repeat
    IsOutGrp   := Check(tkOut);
    IsVarGrp   := Check(tkVar) or IsOutGrp;
    IsConstGrp := Check(tkConst);
    if IsVarGrp then Advance()
    else if IsConstGrp then Advance();
    Names := TStringList.Create();
    try
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected parameter name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Names.Add(FCurrent.Value);
      Advance();
      while Check(tkComma) do
      begin
        Advance();
        if not Check(tkIdent) then
          raise EParseError.Create(Format('Expected parameter name at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        Names.Add(FCurrent.Value);
        Advance();
      end;
      Expect(tkColon);
      IsOpenArr := Check(tkArray);
      if IsOpenArr then
      begin
        Advance();        { consume 'array' }
        Expect(tkOf);
        { 'array of const' — a heterogeneous variadic list.  The element type
          is the intrinsic TVarRec; each call-site bracket element is boxed
          into a (VType, VValue) record.  Reuses the open-array ABI. }
        if Check(tkConst) then
        begin
          Advance();      { consume 'const' }
          TypeN := 'TVarRec';
        end
        else
          TypeN := ParseTypeName();   { element type }
      end
      else
        TypeN := ParseTypeName();
      Default := nil;
      if Check(tkEquals) then
      begin
        if Names.Count > 1 then
          raise EParseError.Create(Format(
            'Default value not allowed in a multi-name parameter group at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        if IsVarGrp then
          raise EParseError.Create(Format(
            'Default value not allowed on var/out parameter at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        if IsOpenArr then
          raise EParseError.Create(Format(
            'Default value not allowed on open-array parameter at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        DefLine := FCurrent.Line;
        DefCol  := FCurrent.Col;
        Advance();  { consume '=' }
        Default := ParseExpr();
        if Default = nil then
          raise EParseError.Create(Format(
            'Expected default value expression at line %d col %d in %s',
            [DefLine, DefCol, FLexer.Filename]));
      end;
      for I := 0 to Names.Count - 1 do
      begin
        Par              := TMethodParam.Create();
        Par.ParamName    := Names.Strings[I];
        Par.TypeName     := TypeN;
        Par.IsVarParam   := IsVarGrp;
        Par.IsConstParam := IsConstGrp;
        Par.IsOutParam   := IsOutGrp;
        Par.IsOpenArray  := IsOpenArr;
        if (I = Names.Count - 1) and (Default <> nil) then
        begin
          Par.DefaultValue := Default;
          Default := nil;  { ownership transferred to Par }
        end;
        AParams.Add(Par);
      end;
    finally
      Names.Free();
    end;
    if Check(tkSemicolon) then
      Advance()
    else
      Break;
  until False;
end;

procedure TParser.ParseStandaloneDecl(ABlock: TBlock);
var
  IsFunc:   Boolean;
  IsStat:   Boolean;
  MD:       TMethodDecl;
begin
  { Leading `static` on an out-of-line implementation: `static function T.M ...`.
    Consume it and record the static-ness on the parsed decl, where it is later
    reconciled against the in-class declaration. }
  { Out-of-line operator body: `class operator TFoo.Add(...): TFoo; begin ... end;`
    Parsed by the same path as an in-type declaration, so the impl carries
    IsOperator/OperatorKind/IsStatic and reconciles against the declaration
    exactly as an overloaded static method does. }
  if AtClassOperator() then
  begin
    ABlock.ProcDecls.Add(ParseClassOperatorDecl(True));
    Exit;
  end;
  IsStat := False;
  if Check(tkIdent) and SameText(FCurrent.Value, 'static') and
     (PeekKind() in [tkFunction, tkProcedure]) then
  begin
    IsStat := True;
    Advance();
  end;
  IsFunc := Check(tkFunction);
  MD     := ParseMethodDecl(IsFunc, True);  { True = may have nested proc/func decls }
  if IsStat then
    MD.IsStatic := True;
  ABlock.ProcDecls.Add(MD);
end;



function TParser.ParsePropertyDecl: TPropertyDecl;
begin
  Result := TPropertyDecl.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Advance();  { consume 'property' identifier }
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected property name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result.Name := FCurrent.Value;
    Advance();
    { Optional index parameter: 'property Name[ParamName: TypeName]: ...' }
    if Check(tkLBracket) then
    begin
      Advance();  { consume '[' }
      if not Check(tkIdent) then
        raise EParseError.Create(Format(
          'Expected index parameter name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.IndexParamName := FCurrent.Value;
      Advance();
      Expect(tkColon);
      Result.IndexTypeName := ParseTypeName();
      Expect(tkRBracket);
    end;
    Expect(tkColon);
    Result.TypeName := ParseTypeName();
    { Optional: read Accessor }
    if Check(tkIdent) and SameText(FCurrent.Value, 'read') then
    begin
      Advance();
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected read accessor name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.ReadName := FCurrent.Value;
      Advance();
    end;
    { Optional: write Accessor }
    if Check(tkIdent) and SameText(FCurrent.Value, 'write') then
    begin
      Advance();
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected write accessor name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.WriteName := FCurrent.Value;
      Advance();
    end;
    Expect(tkSemicolon);
    { Optional `default` directive on an indexed property — marks it as the
      class's default array property, enabling Obj[I] sugar.  It appears as a
      separate directive after the property's own semicolon:
        property Items[I: Integer]: T read Get write Put; default; }
    if Check(tkIdent) and SameText(FCurrent.Value, 'default') then
    begin
      Result.IsDefault := True;
      Advance();
      Expect(tkSemicolon);
    end;
  except
    Result.Free();
    raise;
  end;
end;

procedure TParser.ParseAttributeList(AAttrs: TStringList; AUses: TObjectList);
{ Parse zero or more `[Ident]` or `[Ident(args)]` attributes.  Bare identifier
  names are appended to AAttrs — the name list drives compiler-recognised
  behaviour ([Weak], [Unretained]) and BIF export.  When AUses is non-nil a
  TAttributeUse carrying the parsed argument expressions is additionally
  appended for each attribute, so custom-attribute constructor calls can be
  reified into typeinfo (class-level and method-level attribute sites pass a
  list; var/field sites pass nil).  Arguments are constant expressions —
  uSemantic type-checks them against the attribute class's constructor when
  it synthesises the factory thunk.  Unknown attributes are accepted silently
  here for forward compatibility with user-defined attributes. }
var
  Use:  TAttributeUse;
  Arg:  TASTExpr;
begin
  while Check(tkLBracket) do
  begin
    Advance();  { consume [ }
    if not Check(tkIdent) then
      raise EParseError.Create(Format(
        'Expected attribute name after ''['' at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    AAttrs.Add(FCurrent.Value);
    Use := nil;
    if AUses <> nil then
    begin
      Use := TAttributeUse.Create();
      Use.Name := FCurrent.Value;
      Use.Line := FCurrent.Line;
      Use.Col  := FCurrent.Col;
      AUses.Add(Use);
    end;
    Advance();  { consume attribute name }
    { Optional argument list: (expr, ...). }
    if Check(tkLParen) then
    begin
      Advance();
      if not Check(tkRParen) then
      begin
        Arg := ParseExpr();
        if Use <> nil then Use.Args.Add(Arg) else Arg.Free();
        while Check(tkComma) do
        begin
          Advance();
          Arg := ParseExpr();
          if Use <> nil then Use.Args.Add(Arg) else Arg.Free();
        end;
      end;
      Expect(tkRParen);
    end;
    Expect(tkRBracket);
  end;
end;

procedure TParser.ParseFieldDecl(AFields: TObjectList);
var
  Fld: TFieldDecl;
begin
  Fld := TFieldDecl.Create();
  Fld.Line := FCurrent.Line;
  Fld.Col  := FCurrent.Col;
  try
    ParseAttributeList(Fld.Attributes);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected field name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Fld.Names.Add(FCurrent.Value);
    Advance();
    while Check(tkComma) do
    begin
      Advance();
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected field name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Fld.Names.Add(FCurrent.Value);
      Advance();
    end;
    Expect(tkColon);
    Fld.TypeName := ParseTypeName();
    Expect(tkSemicolon);
    AFields.Add(Fld);
  except
    Fld.Free();
    raise;
  end;
end;

{ ------------------------------------------------------------------ }
{ Var section                                                         }
{ ------------------------------------------------------------------ }

procedure TParser.ParseVarBlock(ABlock: TBlock);
var
  IsTV: Boolean;
begin
  IsTV := Check(tkThreadVar);
  if IsTV then
    Advance()
  else
    Expect(tkVar);
  while Check(tkIdent) or Check(tkLBracket) do
    Self.ParseVarDecl(ABlock, IsTV);
end;

procedure TParser.ParseVarDecl(ABlock: TBlock; AIsThreadVar: Boolean);
var
  Decl: TVarDecl;
begin
  Decl := TVarDecl.Create();
  Decl.Line := FCurrent.Line;
  Decl.Col  := FCurrent.Col;
  Decl.IsThreadVar := AIsThreadVar;
  try
    ParseAttributeList(Decl.Attributes);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected variable name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Decl.Names.Add(FCurrent.Value);
    Advance();
    while Check(tkComma) do
    begin
      Advance();
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected variable name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Decl.Names.Add(FCurrent.Value);
      Advance();
    end;
    Expect(tkColon);
    Decl.TypeName := ParseTypeName();
    { Optional initialiser: var G: T = value.  Parsed via the shared const
      value scanner; semantic folds it and codegen emits it into the data
      section.  An aggregate (array/record) type takes a parenthesised value
      list, so mark the carrier IsArrayConst for the array branch. }
    if Check(tkEquals) then
    begin
      if Decl.Names.Count <> 1 then
        raise EParseError.Create(Format(
          'An initialised variable declaration may declare only one name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Advance();  { consume '=' }
      Decl.InitConst := TConstDecl.Create();
      Decl.InitConst.Line := Decl.Line;
      Decl.InitConst.Col  := Decl.Col;
      Decl.InitConst.Name := Decl.Names.Strings[0];
      Decl.InitConst.TypeName := Decl.TypeName;
      if Copy(Decl.TypeName, 0, 6) = 'array[' then
        Decl.InitConst.IsArrayConst := True;
      Self.ParseConstValue(Decl.InitConst);
    end;
    Expect(tkSemicolon);
    ABlock.Decls.Add(Decl);
  except
    Decl.Free();
    raise;
  end;
end;

{ ------------------------------------------------------------------ }
{ Statements                                                          }
{ ------------------------------------------------------------------ }

procedure TParser.ParseStmtList(ABlock: TBlock);
var
  Stmt: TASTStmt;
begin
  while not (Check(tkEnd) or Check(tkEOF) or Check(tkElse)) do
  begin
    Stmt := ParseStmt();
    if Stmt <> nil then
      ABlock.Stmts.Add(Stmt);
    if Check(tkSemicolon) then
      Advance()
    else
      Break;
  end;
end;

function TParser.ParseBlockVarDeclStmt: TASTStmt;
{ 'var Name: TypeName [:= Expr]' in statement position.  v1 deliberately
  minimal: one name, a named type (no inline type constructions, no
  inference).  The optional ':=' initialiser is re-evaluated every time the
  statement executes. }
var
  VS:   TVarDeclStmt;
  Line: Integer;
  Col:  Integer;
begin
  Line := FCurrent.Line;
  Col  := FCurrent.Col;
  Expect(tkVar);
  VS := TVarDeclStmt.Create();
  VS.Line := Line;
  VS.Col  := Col;
  VS.Decl := TVarDecl.Create();
  VS.Decl.Line := Line;
  VS.Decl.Col  := Col;
  VS.Decl.IsBlockScoped := True;
  if not Check(tkIdent) then
  begin
    VS.Free();
    raise EParseError.Create(Format(
      'Expected variable name after ''var'' at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  end;
  VS.Decl.Names.Add(FCurrent.Value);
  Advance();
  if not Check(tkColon) then
  begin
    VS.Free();
    raise EParseError.Create(Format(
      'Block-scoped ''var'' requires an explicit type: expected '':'' ' +
      'at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  end;
  Advance();
  if not Check(tkIdent) then
  begin
    VS.Free();
    raise EParseError.Create(Format(
      'Expected type name at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  end;
  VS.Decl.TypeName := FCurrent.Value;
  Advance();
  if Check(tkAssign) then
  begin
    Advance();
    VS.InitExpr := Self.ParseExpr();
  end;
  Result := VS;
end;

function TParser.ParseStmt: TASTStmt;
var
  Name:        string;
  QualUnit:    string;  { matched unit from a 'Unit.Symbol' target; unused here }
  Line, Col:   Integer;
  Call:        TProcCall;
  Assign:      TAssignment;
  FldAssign:   TFieldAssignment;
  MCall:       TMethodCallStmt;
  MCallExpr:   TMethodCallExpr;
  PtrWrite:    TPointerWriteStmt;
  PtrIdNode:   TIdentExpr;
  DerefNode:   TDerefExpr;
  SecondIdent: string;
  FldNode:     TFieldAccessExpr;
  ParenExpr:   TASTExpr;
  InnerFld:    TFieldAccessExpr;
  CastRcv:     TASTExpr;
  FCallNode:   TFuncCallExpr;
  SubAssign:   TStaticSubscriptAssign;
  SubNode:     TStringSubscriptExpr;
  ChainBase:   TASTExpr;
  ExitS:       TExitStmt;
begin
  Result := nil;

  if Check(tkEnd) or Check(tkEOF) or Check(tkSemicolon) or Check(tkElse) then
    Exit;

  if Check(tkIf) then
  begin
    Exit(ParseIfStmt());
  end;

  if Check(tkWhile) then
  begin
    Exit(ParseWhileStmt());
  end;

  if Check(tkRepeat) then
  begin
    Exit(ParseRepeatStmt());
  end;

  if Check(tkFor) then
  begin
    Exit(ParseForStmt());
  end;

  if Check(tkTry) then
  begin
    Exit(ParseTryStmt());
  end;

  if Check(tkRaise) then
  begin
    Exit(ParseRaiseStmt());
  end;

  if Check(tkExit) then
  begin
    ExitS      := TExitStmt.Create();
    ExitS.Line := FCurrent.Line;
    ExitS.Col  := FCurrent.Col;
    Advance();
    { Exit(X) shorthand: assign X to Result before returning.  Semantic checks
      X is assignment-compatible with the return type and that the enclosing
      routine is a function (not a procedure). }
    if Check(tkLParen) then
    begin
      Advance();
      ExitS.Value := Self.ParseExpr();
      Expect(tkRParen);
    end;
    Exit(ExitS);
  end;

  if Check(tkBreak) then
  begin
    Result      := TBreakStmt.Create();
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Advance();
    Exit;
  end;

  if Check(tkContinue) then
  begin
    Result      := TContinueStmt.Create();
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Advance();
    Exit;
  end;

  if Check(tkInherited) then
  begin
    Exit(ParseInheritedStmt());
  end;

  if Check(tkCase) then
  begin
    Exit(ParseCaseStmt());
  end;

  if Check(tkBegin) then
  begin
    Exit(ParseCompoundStmt());
  end;

  { Block-scoped variable declaration statement (Phase 4):
      var Name: TypeName [:= Expr]
    Single name, explicit type (no inference), optional initialiser.  The
    name is scoped to the enclosing block; the declaration re-runs per
    execution.  docs/anonymous-methods-design.adoc + language-rationale. }
  if Check(tkVar) then
  begin
    Exit(ParseBlockVarDeclStmt());
  end;

  { A statement that begins with '(' is an assignment whose lvalue is a
    parenthesised expression, e.g. a typecast target:  (a as TB).FX := V.
    Parse the parenthesised expression, then require a '.Field := Expr'
    suffix and build a TFieldAssignment whose receiver is that expression
    (the same ObjExpr path used for element-field writes). }
  if Check(tkLParen) then
  begin
    Line := FCurrent.Line;
    Col  := FCurrent.Col;
    Advance();  { consume '(' }
    ParenExpr := Self.ParseExpr();
    try
      Expect(tkRParen);
      if not Check(tkDot) then
        raise EParseError.Create(Format(
          'Expected ''.'' after parenthesised assignment target at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Advance();  { consume '.' }
      if not Check(tkIdent) then
        raise EParseError.Create(Format(
          'Expected field name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      SecondIdent := FCurrent.Value;
      Advance();
      Expect(tkAssign);
    except
      ParenExpr.Free();
      raise;
    end;
    FldAssign := TFieldAssignment.Create();
    FldAssign.Line := Line;
    FldAssign.Col := Col;
    FldAssign.FieldName := SecondIdent;
    FldAssign.ObjExpr := ParenExpr;
    FldAssign.Expr := Self.ParseExpr();
    Exit(FldAssign);
  end;

  if not Check(tkIdent) then
    raise EParseError.Create(Format(
      'Expected statement at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));

  Name := FCurrent.Value;
  Line := FCurrent.Line;
  Col  := FCurrent.Col;
  Advance();

  { Unit-qualified statement target 'Unit.Symbol' (Unit may be dotted to any
    depth).  Collapse to the bare symbol so the rest of the statement parser
    treats it as an unqualified procedure call or assignment target resolved
    through the uses chain.  No-op (consumes nothing) for a same-prefixed
    record/field chain — see TryCollapseUnitQualifier. }
  TryCollapseUnitQualifier(Name, Line, Col, QualUnit);

  if Check(tkLBracket) then
  begin
    { Subscript on the statement LHS.  Three shapes:
        Name[I] := V                — element write (TStaticSubscriptAssign)
        Name[I]....F := V           — field assignment through the element
                                      (TFieldAssignment via ObjExpr)
        Name[I]....M / ....M(args)  — method call on the element
                                      (TMethodCallStmt via ObjExpr) }
    Advance();  { consume '[' }
    SubAssign := TStaticSubscriptAssign.Create();
    SubAssign.Line := Line;
    SubAssign.Col := Col;
    SubAssign.ArrayName := Name;
    try
      SubAssign.IndexExpr := ParseExpr();
      { Single-dimension simple write: Name[I] := V (no comma, no chain). }
      if Check(tkRBracket) then
      begin
        Advance();  { consume ']' }
        if Check(tkAssign) then
        begin
          Advance();  { consume ':=' }
          SubAssign.ValueExpr := ParseExpr();
          Exit(SubAssign);
        end;
      end;
    except
      SubAssign.Free();
      raise;
    end;
    { Either a comma-separated multi-dimensional write Name[I, J] := V, a
      chained write Name[I][J] := V, or a postfix chain on the element
      (field/method access).  Rebuild Name[Index] as an expression base, then
      consume the remaining comma indices / '[' / '.' suffixes until the
      terminating assignment or method call.  Multi-dim and chained element
      writes are lowered to a TStaticSubscriptAssign carrying BaseExpr. }
    PtrIdNode := TIdentExpr.Create();
    PtrIdNode.Line := Line;
    PtrIdNode.Col := Col;
    PtrIdNode.Name := Name;
    SubNode := TStringSubscriptExpr.Create();
    SubNode.Line := Line;
    SubNode.Col := Col;
    SubNode.StrExpr := PtrIdNode;
    SubNode.IndexExpr := SubAssign.IndexExpr;
    SubAssign.IndexExpr := nil;  { ownership transferred to SubNode }
    SubAssign.Free();
    SubAssign := nil;
    ChainBase := SubNode;
    { Remaining comma indices inside the first bracket: Name[I, J, ...].
      Each opens a further subscript whose base is the previous one; the
      closing ']' is consumed here so the chain loop below sees the suffixes
      that follow. }
    if Check(tkComma) then
    begin
      try
        while Check(tkComma) do
        begin
          Advance();  { consume ',' }
          SubNode := TStringSubscriptExpr.Create();
          SubNode.Line := FCurrent.Line;
          SubNode.Col := FCurrent.Col;
          SubNode.StrExpr := ChainBase;
          ChainBase := SubNode;
          SubNode.IndexExpr := ParseExpr();
        end;
        Expect(tkRBracket);
      except
        ChainBase.Free();
        raise;
      end;
      { After Name[I, J] the next token is ':=' for a plain element write, or
        a further suffix for a chained access.  An immediate ':=' lowers to a
        BaseExpr element write. }
      if Check(tkAssign) then
      begin
        Advance();  { consume ':=' }
        SubNode := TStringSubscriptExpr(ChainBase);
        SubAssign := TStaticSubscriptAssign.Create();
        SubAssign.Line := Line;
        SubAssign.Col := Col;
        SubAssign.ArrayName := Name;
        try
          SubAssign.BaseExpr := SubNode.StrExpr;
          SubAssign.IndexExpr := SubNode.IndexExpr;
          SubNode.StrExpr := nil;
          SubNode.IndexExpr := nil;
          ChainBase := nil;
          SubNode.Free();
          SubAssign.ValueExpr := ParseExpr();
          Exit(SubAssign);
        except
          SubAssign.Free();
          raise;
        end;
      end;
    end;
    try
      repeat
        if Check(tkLBracket) then
        begin
          { Further subscript: ChainBase[Index] }
          Advance();  { consume '[' }
          SubNode := TStringSubscriptExpr.Create();
          SubNode.Line := FCurrent.Line;
          SubNode.Col := FCurrent.Col;
          SubNode.StrExpr := ChainBase;
          ChainBase := SubNode;
          SubNode.IndexExpr := ParseExpr();
          Expect(tkRBracket);
          if Check(tkAssign) then
          begin
            if SubNode.StrExpr is TFieldAccessExpr then
            begin
              { …Field[idx] := value — element write into an array-typed
                field (or indexed property write).  Rebuild as a
                TFieldAssignment: receiver = the field's base, index =
                the subscript. }
              Advance();  { consume ':=' }
              FldNode := TFieldAccessExpr(SubNode.StrExpr);
              FldAssign := TFieldAssignment.Create();
              FldAssign.Line := Line;
              FldAssign.Col := Col;
              FldAssign.FieldName := FldNode.FieldName;
              FldAssign.ObjExpr := FldNode.Base;
              FldNode.Base := nil;
              FldAssign.PropIndexExpr := SubNode.IndexExpr;
              SubNode.IndexExpr := nil;
              ChainBase := nil;
              SubNode.Free();  { frees the now-detached field node too }
              FldAssign.Expr := ParseExpr();
              Exit(FldAssign);
            end;
            { Chained element write into a nested array: Base[J] := value where
              Base is itself a subscript chain (e.g. A[I][J] := V).  Lower to a
              TStaticSubscriptAssign carrying BaseExpr = the inner-array address
              expression and IndexExpr = the final index. }
            Advance();  { consume ':=' }
            SubAssign := TStaticSubscriptAssign.Create();
            SubAssign.Line := Line;
            SubAssign.Col := Col;
            SubAssign.ArrayName := Name;
            try
              SubAssign.BaseExpr := SubNode.StrExpr;
              SubAssign.IndexExpr := SubNode.IndexExpr;
              SubNode.StrExpr := nil;
              SubNode.IndexExpr := nil;
              ChainBase := nil;
              SubNode.Free();
              SubAssign.ValueExpr := ParseExpr();
              Exit(SubAssign);
            except
              SubAssign.Free();
              raise;
            end;
          end;
          Continue;
        end;
        if not Check(tkDot) then
          raise EParseError.Create(Format(
            'Expected ''.'' or '':='' after subscript at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        Advance();  { consume '.' }
        if not Check(tkIdent) then
          raise EParseError.Create(Format(
            'Expected field or method name at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        SecondIdent := FCurrent.Value;
        Advance();  { consume ident }
        if Check(tkAssign) then
        begin
          { Name[I]....F := Expr — field assignment through the element }
          Advance();  { consume ':=' }
          FldAssign := TFieldAssignment.Create();
          FldAssign.Line := Line;
          FldAssign.Col := Col;
          FldAssign.FieldName := SecondIdent;
          FldAssign.ObjExpr := ChainBase;
          ChainBase := nil;
          FldAssign.Expr := ParseExpr();
          Exit(FldAssign);
        end;
        if Check(tkLParen) then
        begin
          { Name[I]....M(args) — method call on the element }
          MCall := TMethodCallStmt.Create();
          MCall.Line := Line;
          MCall.Col := Col;
          MCall.ObjectName := '';
          MCall.Name := SecondIdent;
          MCall.ObjExpr := ChainBase;
          ChainBase := nil;
          Advance();  { consume '(' }
          if not Check(tkRParen) then
            ParseMethodCallArgList(MCall);
          Expect(tkRParen);
          Exit(MCall);
        end;
        if Check(tkDot) or Check(tkLBracket) then
        begin
          { Extend the chain: Name[I].F.…  or  Name[I].F[J]… }
          FldNode := TFieldAccessExpr.Create();
          FldNode.Line := Line;
          FldNode.Col := Col;
          FldNode.Base := ChainBase;
          FldNode.FieldName := SecondIdent;
          ChainBase := FldNode;
          Continue;
        end;
        { Statement boundary: parenless method call Name[I]....M }
        MCall := TMethodCallStmt.Create();
        MCall.Line := Line;
        MCall.Col := Col;
        MCall.ObjectName := '';
        MCall.Name := SecondIdent;
        MCall.ObjExpr := ChainBase;
        ChainBase := nil;
        Exit(MCall);
      until False;
    except
      ChainBase.Free();
      raise;
    end;
  end;

  if Check(tkCaret) then
  begin
    Advance();  { consume '^' }
    if Check(tkDot) then
    begin
      { Deref-then-field assignment: Ident^.Field := Expr
        Re-use the field-assignment path with a TDerefExpr as ObjExpr. }
      Advance();  { consume '.' }
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected field name after ''^.'' at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      SecondIdent := FCurrent.Value;
      Advance();  { consume field name }
      { Build chain: handle further A^.B.C.D chaining }
      PtrIdNode        := TIdentExpr.Create();
      PtrIdNode.Line   := Line;
      PtrIdNode.Col    := Col;
      PtrIdNode.Name   := Name;
      DerefNode        := TDerefExpr.Create();
      DerefNode.Line   := Line;
      DerefNode.Col    := Col;
      DerefNode.Expr   := PtrIdNode;
      FldNode          := TFieldAccessExpr.Create();
      FldNode.Line     := Line;
      FldNode.Col      := Col;
      FldNode.Base     := DerefNode;
      FldNode.FieldName := SecondIdent;
      while Check(tkDot) and (PeekKind() = tkIdent) do
      begin
        Advance();
        InnerFld           := TFieldAccessExpr.Create();
        InnerFld.Line      := FCurrent.Line;
        InnerFld.Col       := FCurrent.Col;
        InnerFld.FieldName := FCurrent.Value;
        InnerFld.Base      := FldNode;
        FldNode            := InnerFld;
        Advance();
      end;
      FldAssign         := TFieldAssignment.Create();
      FldAssign.Line    := Line;
      FldAssign.Col     := Col;
      FldAssign.ObjExpr := FldNode.Base;
      FldAssign.FieldName := FldNode.FieldName;
      FldNode.Base      := nil;
      FldNode.Free();
      if Check(tkLBracket) then
      begin
        Advance();
        FldAssign.PropIndexExpr := ParseExpr();
        Expect(tkRBracket);
      end;
      Expect(tkAssign);
      FldAssign.Expr := ParseExpr();
      Result := FldAssign;
    end
    else
    begin
      { Plain pointer dereference assignment: Ident^ := Expr }
      Expect(tkAssign);
      PtrWrite         := TPointerWriteStmt.Create();
      PtrWrite.Line    := Line;
      PtrWrite.Col     := Col;
      PtrIdNode        := TIdentExpr.Create();
      PtrIdNode.Line   := Line;
      PtrIdNode.Col    := Col;
      PtrIdNode.Name   := Name;
      PtrWrite.PtrExpr := PtrIdNode;
      PtrWrite.ValExpr := ParseExpr();
      Result := PtrWrite;
    end;
  end
  else if Check(tkDot) then
  begin
    Advance();
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected field or method name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    SecondIdent := FCurrent.Value;
    Advance();

    if Check(tkLBracket) then
    begin
      { Ident '.' Ident '[' ... — either an indexed property write
        (Ident.Field[Index] := Expr) or a subscripted chain with field
        access (Self.FStack[I].Count := Expr). }
      Advance();  { consume '[' }
      PtrIdNode      := TIdentExpr.Create();
      PtrIdNode.Line := Line;
      PtrIdNode.Col  := Col;
      PtrIdNode.Name := Name;
      FldNode          := TFieldAccessExpr.Create();
      FldNode.Line     := Line;
      FldNode.Col      := Col;
      FldNode.Base     := PtrIdNode;
      FldNode.FieldName := SecondIdent;
      SubNode            := TStringSubscriptExpr.Create();
      SubNode.Line       := Line;
      SubNode.Col        := Col;
      SubNode.StrExpr    := FldNode;
      SubNode.IndexExpr  := ParseExpr();
      Expect(tkRBracket);
      if Check(tkAssign) then
      begin
        { Indexed property / array-element write: Ident.Field[Index] := Expr.
          Semantic sets IsElemWrite when the field is an array type. }
        FldAssign := TFieldAssignment.Create();
        FldAssign.Line := Line;
        FldAssign.Col := Col;
        FldAssign.RecordName := Name;
        FldAssign.FieldName := SecondIdent;
        FldAssign.PropIndexExpr := SubNode.IndexExpr;
        SubNode.IndexExpr := nil;
        SubNode.Free();
        SubNode := nil;
        FldNode.Base := nil;
        PtrIdNode.Free();
        PtrIdNode := nil;
        FldNode.Free();
        FldNode := nil;
        Advance();  { consume ':=' }
        FldAssign.Expr := ParseExpr();
        Result := FldAssign;
      end
      else
      begin
        { Chain after subscript: Self.FStack[I].Count := ... or
          Self.FStack[I].Method(args) }
        ChainBase := SubNode;
        SubNode := nil;
        try
          repeat
            if Check(tkDot) then
            begin
              Advance();  { consume '.' }
              if not Check(tkIdent) then
                raise EParseError.Create(Format(
                  'Expected field or method name at line %d col %d in %s',
                  [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
              SecondIdent := FCurrent.Value;
              Advance();
              if Check(tkAssign) then
              begin
                Advance();  { consume ':=' }
                FldAssign := TFieldAssignment.Create();
                FldAssign.Line := Line;
                FldAssign.Col := Col;
                FldAssign.FieldName := SecondIdent;
                FldAssign.ObjExpr := ChainBase;
                ChainBase := nil;
                FldAssign.Expr := ParseExpr();
                Exit(FldAssign);
              end;
              if Check(tkLParen) then
              begin
                MCall := TMethodCallStmt.Create();
                MCall.Line := Line;
                MCall.Col := Col;
                MCall.ObjectName := '';
                MCall.Name := SecondIdent;
                MCall.ObjExpr := ChainBase;
                ChainBase := nil;
                Advance();  { consume '(' }
                if not Check(tkRParen) then
                  ParseMethodCallArgList(MCall);
                Expect(tkRParen);
                Exit(MCall);
              end;
              InnerFld := TFieldAccessExpr.Create();
              InnerFld.Line := FCurrent.Line;
              InnerFld.Col := FCurrent.Col;
              InnerFld.Base := ChainBase;
              InnerFld.FieldName := SecondIdent;
              ChainBase := InnerFld;
            end
            else if Check(tkLBracket) then
            begin
              Advance();  { consume '[' }
              SubNode := TStringSubscriptExpr.Create();
              SubNode.Line := FCurrent.Line;
              SubNode.Col := FCurrent.Col;
              SubNode.StrExpr := ChainBase;
              ChainBase := SubNode;
              SubNode.IndexExpr := ParseExpr();
              Expect(tkRBracket);
              { A subscript-terminated chain can itself be an assignment target
                (GH #187): Aouter.ora[x].innerOneArr[c] := V.  Mirror the
                bare-Name[...] loop above — without this the loop Breaks and the
                unconditional raise below rejects the '.:=' as "after chain". }
              if Check(tkAssign) then
              begin
                if SubNode.StrExpr is TFieldAccessExpr then
                begin
                  { …Field[idx] := value — element write into an array-typed
                    field; rebuild as a TFieldAssignment with the subscript as
                    PropIndexExpr. }
                  Advance();  { consume ':=' }
                  FldNode := TFieldAccessExpr(SubNode.StrExpr);
                  FldAssign := TFieldAssignment.Create();
                  FldAssign.Line := Line;
                  FldAssign.Col := Col;
                  FldAssign.FieldName := FldNode.FieldName;
                  FldAssign.ObjExpr := FldNode.Base;
                  FldNode.Base := nil;
                  FldAssign.PropIndexExpr := SubNode.IndexExpr;
                  SubNode.IndexExpr := nil;
                  ChainBase := nil;
                  SubNode.Free();  { frees the now-detached field node too }
                  FldAssign.Expr := ParseExpr();
                  Exit(FldAssign);
                end;
                { Nested array element write: Base[J] := value where Base is
                  itself a subscript chain (e.g. A[I][J] := V). }
                Advance();  { consume ':=' }
                SubAssign := TStaticSubscriptAssign.Create();
                SubAssign.Line := Line;
                SubAssign.Col := Col;
                SubAssign.ArrayName := Name;
                try
                  SubAssign.BaseExpr := SubNode.StrExpr;
                  SubAssign.IndexExpr := SubNode.IndexExpr;
                  SubNode.StrExpr := nil;
                  SubNode.IndexExpr := nil;
                  ChainBase := nil;
                  SubNode.Free();
                  SubAssign.ValueExpr := ParseExpr();
                  Exit(SubAssign);
                except
                  SubAssign.Free();
                  raise;
                end;
              end;
            end
            else
              Break;
          until False;
        except
          ChainBase.Free();
          raise;
        end;
        raise EParseError.Create(Format(
          'Expected '':='' or ''('' after chain at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      end;
    end
    else if Check(tkAssign) then
    begin
      { Field assignment: Ident '.' Ident ':=' Expr }
      FldAssign := TFieldAssignment.Create();
      FldAssign.Line := Line;
      FldAssign.Col := Col;
      FldAssign.RecordName := Name;
      FldAssign.FieldName := SecondIdent;
      Expect(tkAssign);
      FldAssign.Expr := ParseExpr();
      Result := FldAssign;
    end
    else
    begin
      { Method call: Ident '.' Ident ['(' [args] ')'] — may chain to
        Ident.Ident.Ident... with further '.' before the final method call. }
      if Check(tkDot) then
      begin
        { Chained: AProg.UsedUnits.Add(...) — build a field-access chain as
          the receiver expression. }
        MCall            := TMethodCallStmt.Create();
        MCall.Line       := Line;
        MCall.Col        := Col;
        MCall.ObjectName := '';
        { Build chain: AProg -> AProg.UsedUnits }
        PtrIdNode        := TIdentExpr.Create();
        PtrIdNode.Line   := Line;
        PtrIdNode.Col    := Col;
        PtrIdNode.Name   := Name;
        FldNode          := TFieldAccessExpr.Create();
        FldNode.Line     := Line;
        FldNode.Col      := Col;
        FldNode.Base     := PtrIdNode;
        FldNode.FieldName:= SecondIdent;
        MCall.ObjExpr    := FldNode;
        while Check(tkDot) do
        begin
          Advance();
          if not Check(tkIdent) then
            raise EParseError.Create(Format('Expected field or method name at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          SecondIdent := FCurrent.Value;
          Advance();
          if Check(tkDot) then
          begin
            { Still more chain — extend field access path }
            FldNode          := TFieldAccessExpr.Create();
            FldNode.Line     := Line;
            FldNode.Col      := Col;
            FldNode.Base     := MCall.ObjExpr;
            FldNode.FieldName:= SecondIdent;
            MCall.ObjExpr    := FldNode;
          end
          else if Check(tkLBracket) then
          begin
            { Chained indexed L-value: A.B.C[idx] := value — element write
              into an array-typed field (or indexed property write) reached
              via a chain.  Semantic disambiguates field vs property. }
            Advance();  { consume '[' }
            FldAssign           := TFieldAssignment.Create();
            FldAssign.Line      := Line;
            FldAssign.Col       := Col;
            FldAssign.FieldName := SecondIdent;
            FldAssign.ObjExpr   := MCall.ObjExpr;
            MCall.ObjExpr       := nil;  { transfer ownership }
            MCall.Free();
            MCall := nil;
            FldAssign.PropIndexExpr := ParseExpr();
            Expect(tkRBracket);
            Expect(tkAssign);
            FldAssign.Expr := ParseExpr();
            Exit(FldAssign);
          end
          else
          begin
            MCall.Name := SecondIdent;
            if Check(tkLParen) then
            begin
              Advance();
              if not Check(tkRParen) then
                ParseMethodCallArgList(MCall);
              Expect(tkRParen);
            end;
            Break;
          end;
        end;
        { Chained field assignment: A.B.C := value }
        if Check(tkAssign) then
        begin
          Advance();
          FldAssign           := TFieldAssignment.Create();
          FldAssign.Line      := Line;
          FldAssign.Col       := Col;
          FldAssign.FieldName := MCall.Name;
          FldAssign.ObjExpr   := MCall.ObjExpr;
          MCall.ObjExpr       := nil;  { transfer ownership — prevent double-free }
          MCall.Free();
          MCall := nil;
          FldAssign.Expr := ParseExpr();
          Exit(FldAssign);
        end;
        Result := MCall;
      end
      else
      begin
        MCall            := TMethodCallStmt.Create();
        MCall.Line       := Line;
        MCall.Col        := Col;
        MCall.ObjectName := Name;
        MCall.Name       := SecondIdent;
        if Check(tkLParen) then
        begin
          Advance();
          if not Check(tkRParen) then
            ParseMethodCallArgList(MCall);
          Expect(tkRParen);
        end
        else if not Check(tkDot) then
        begin
          { Bare 'Obj.Method' with no '(' and no further '.' chain — a
            parameterless method call written without its mandatory parentheses.
            (A following '.' is a post-call/field chain handled just below; a
            terminating bare reference is the error case.)  Every call carries ()
            even with no arguments — see language-rationale.adoc, "Mandatory
            parentheses on zero-argument calls". }
          MCall.Free();
          MCall := nil;
          raise EParseError.Create(Format(
            'Bare reference to ''%s.%s'' requires () for a call at line %d col %d in %s',
            [Name, SecondIdent, Line, Col, FLexer.Filename]));
        end;
        { Post-method chain: Name.Method(args).Field := value or .Method2(args) }
        if Check(tkDot) then
        begin
          MCallExpr            := TMethodCallExpr.Create();
          MCallExpr.Line       := Line;
          MCallExpr.Col        := Col;
          MCallExpr.ObjectName := MCall.ObjectName;
          MCallExpr.Name       := MCall.Name;
          while MCall.Args.Count > 0 do
            MCallExpr.Args.Add(MCall.Args.Extract(MCall.Args.Items[0]));
          MCall.Free();
          MCall   := nil;
          CastRcv := MCallExpr;
          while Check(tkDot) do
          begin
            Advance();
            if not Check(tkIdent) then
              raise EParseError.Create(Format(
                'Expected identifier after ''.'' at line %d col %d in %s',
                [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
            SecondIdent := FCurrent.Value;
            Advance();
            if Check(tkLParen) then
            begin
              MCall            := TMethodCallStmt.Create();
              MCall.Line       := Line;
              MCall.Col        := Col;
              MCall.ObjectName := '';
              MCall.Name       := SecondIdent;
              MCall.ObjExpr    := CastRcv;
              Advance();
              if not Check(tkRParen) then
                ParseMethodCallArgList(MCall);
              Expect(tkRParen);
              Exit(MCall);
            end;
            FldNode           := TFieldAccessExpr.Create();
            FldNode.Line      := Line;
            FldNode.Col       := Col;
            FldNode.Base      := CastRcv;
            FldNode.FieldName := SecondIdent;
            CastRcv := FldNode;
          end;
          if Check(tkAssign) and (CastRcv is TFieldAccessExpr) then
          begin
            Advance();
            FldAssign           := TFieldAssignment.Create();
            FldAssign.Line      := Line;
            FldAssign.Col       := Col;
            FldAssign.FieldName := TFieldAccessExpr(CastRcv).FieldName;
            FldAssign.ObjExpr   := TFieldAccessExpr(CastRcv).Base;
            TFieldAccessExpr(CastRcv).Base := nil;
            CastRcv.Free();
            FldAssign.Expr := ParseExpr();
            Exit(FldAssign);
          end;
          raise EParseError.Create(Format(
            'Expected method call or assignment after chain at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        end;
        Result := MCall;
      end;
    end;
  end
  else if Check(tkAssign) then
  begin
    Advance();
    Assign      := TAssignment.Create();
    Assign.Line := Line;
    Assign.Col  := Col;
    Assign.Name := Name;
    Assign.Expr := ParseExpr();
    Result := Assign;
  end
  else
  begin
    { Typecast-then-method-call statement: TCast(expr).Method(args)
      or chained Ident(arg).Field.Method(args). Detect by peeking for
      '(' followed by a '.' after the paren closure — parse directly
      into a TFuncCallExpr receiver so the inner arg lives on. }
    if Check(tkLParen) then
    begin
      FCallNode      := TFuncCallExpr.Create();
      FCallNode.Line := Line;
      FCallNode.Col  := Col;
      FCallNode.Name := Name;
      Advance();  { '(' }
      if not Check(tkRParen) then
      begin
        FCallNode.Args.Add(ParseExpr());
        while Check(tkComma) do
        begin
          Advance();
          FCallNode.Args.Add(ParseExpr());
        end;
      end;
      Expect(tkRParen);
      if Check(tkDot) then
      begin
        CastRcv := FCallNode;
        { Chain parse: each step reads '.Ident', then either '(' (call) or
          more '.'. The final method call terminates as TMethodCallStmt. }
        while Check(tkDot) do
        begin
          Advance();
          if not Check(tkIdent) then
            raise EParseError.Create(Format('Expected field or method name at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          SecondIdent := FCurrent.Value;
          Advance();
          if Check(tkLParen) then
          begin
            MCall            := TMethodCallStmt.Create();
            MCall.Line       := Line;
            MCall.Col        := Col;
            MCall.ObjectName := '';
            MCall.Name       := SecondIdent;
            MCall.ObjExpr    := CastRcv;
            Advance();  { consume '(' }
            if not Check(tkRParen) then
              ParseMethodCallArgList(MCall);
            Expect(tkRParen);
            Exit(MCall);
          end;
          FldNode            := TFieldAccessExpr.Create();
          FldNode.Line       := Line;
          FldNode.Col        := Col;
          FldNode.Base       := CastRcv;
          FldNode.FieldName  := SecondIdent;
          CastRcv            := FldNode;
        end;
        { Field assignment through typecast/chain: TCast(expr).Field := value }
        if Check(tkAssign) and (CastRcv is TFieldAccessExpr) then
        begin
          Advance(); { consume ':=' }
          FldAssign          := TFieldAssignment.Create();
          FldAssign.Line     := Line;
          FldAssign.Col      := Col;
          FldAssign.FieldName := TFieldAccessExpr(CastRcv).FieldName;
          FldAssign.ObjExpr  := TFieldAccessExpr(CastRcv).Base;
          TFieldAccessExpr(CastRcv).Base := nil; { transfer ownership }
          CastRcv.Free();
          FldAssign.Expr := ParseExpr();
          Exit(FldAssign);
        end;
        { No-arg method call: Func(...).Field treated as Func(...).Method }
        if CastRcv is TFieldAccessExpr then
        begin
          MCall            := TMethodCallStmt.Create();
          MCall.Line       := Line;
          MCall.Col        := Col;
          MCall.ObjectName := '';
          MCall.Name       := TFieldAccessExpr(CastRcv).FieldName;
          MCall.ObjExpr    := TFieldAccessExpr(CastRcv).Base;
          TFieldAccessExpr(CastRcv).Base := nil;
          CastRcv.Free();
          Exit(MCall);
        end;
        raise EParseError.Create(Format(
          'Expected method call after typecast at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      end;
      { No '.': it was a plain procedure/function call. Move args to a
        fresh TProcCall using FPC-style Extract (removes without freeing). }
      Call      := TProcCall.Create();
      Call.Line := Line;
      Call.Col  := Col;
      Call.Name := Name;
      while FCallNode.Args.Count > 0 do
        Call.Args.Add(FCallNode.Args.Extract(FCallNode.Args.Items[0]));
      FCallNode.Free();
      Exit(Call);
    end;
    { Bare identifier in statement position with no '(' — a parameterless
      procedure/function call written without its mandatory parentheses.
      Every call carries () even with no arguments (see language-rationale.adoc,
      "Mandatory parentheses on zero-argument calls"). }
    raise EParseError.Create(Format(
      'Bare reference to ''%s'' requires () for a call at line %d col %d in %s',
      [Name, Line, Col, FLexer.Filename]));
  end;
end;

function TParser.ParseWhileStmt: TWhileStmt;
begin
  Result := TWhileStmt.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkWhile);
    Result.Condition := ParseExpr();
    Expect(tkDo);
    Result.Body := ParseStmt();
  except
    Result.Free();
    raise;
  end;
end;

function TParser.ParseRepeatStmt: TRepeatStmt;
var
  Stmt: TASTStmt;
begin
  Result := TRepeatStmt.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkRepeat);
    Result.Body := TCompoundStmt.Create();
    Result.Body.Line := FCurrent.Line;
    Result.Body.Col  := FCurrent.Col;
    while not (Check(tkUntil) or Check(tkEOF)) do
    begin
      Stmt := ParseStmt();
      if Stmt <> nil then
        Result.Body.Stmts.Add(Stmt);
      if Check(tkSemicolon) then
        Advance()
      else
        Break;
    end;
    Expect(tkUntil);
    Result.Condition := ParseExpr();
  except
    Result.Free();
    raise;
  end;
end;

function TParser.ParseIfStmt: TIfStmt;
begin
  Result := TIfStmt.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkIf);
    Result.Condition := ParseExpr();
    Expect(tkThen);
    Result.ThenStmt := ParseStmt();
    // 'if cond then { comment } else' leaves ThenStmt nil when the comment is the only body.
    // Substitute an empty compound so EmitIfStmt can always call EmitStmt.
    if Result.ThenStmt = nil then
      Result.ThenStmt := TCompoundStmt.Create();
    if Check(tkElse) then
    begin
      Advance();
      Result.ElseStmt := ParseStmt();
    end;
  except
    Result.Free();
    raise;
  end;
end;

function TParser.ParseForStmt: TASTStmt;
var
  SLine:    Integer;
  SCol:     Integer;
  VarName:  string;
  ForS:     TForStmt;
  ForInS:   TForInStmt;
begin
  SLine := FCurrent.Line;
  SCol  := FCurrent.Col;
  Expect(tkFor);
  if not Check(tkIdent) then
    raise EParseError.Create(Format('Expected loop variable at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  VarName := FCurrent.Value;
  Advance();

  if Check(tkIn) then
  begin
    { for X in Collection do Body }
    ForInS := TForInStmt.Create();
    Result := ForInS;
    try
      ForInS.Line    := SLine;
      ForInS.Col     := SCol;
      ForInS.VarName := VarName;
      Advance();  { consume 'in' }
      ForInS.CollExpr := ParseExpr();
      Expect(tkDo);
      ForInS.Body := ParseStmt();
    except
      ForInS.Free();
      Result := nil;
      raise;
    end;
  end
  else
  begin
    { for X := Start to/downto End do Body }
    ForS := TForStmt.Create();
    Result := ForS;
    try
      ForS.Line    := SLine;
      ForS.Col     := SCol;
      ForS.VarName := VarName;
      Expect(tkAssign);
      ForS.StartExpr := ParseExpr();
      if Check(tkTo) then
      begin
        ForS.IsDownTo := False;
        Advance();
      end
      else if Check(tkDownto) then
      begin
        ForS.IsDownTo := True;
        Advance();
      end
      else
        raise EParseError.Create(Format(
          'Expected ''to'' or ''downto'' at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      ForS.EndExpr := ParseExpr();
      Expect(tkDo);
      ForS.Body := ParseStmt();
    except
      ForS.Free();
      Result := nil;
      raise;
    end;
  end;
end;

procedure TParser.ParseBodyInto(ATarget: TCompoundStmt;
  AStop1, AStop2: TTokenKind);
var
  S: TASTStmt;
begin
  while not (Check(AStop1) or Check(AStop2) or Check(tkEnd) or Check(tkEOF)) do
  begin
    S := ParseStmt();
    if S <> nil then
      ATarget.Stmts.Add(S);
    if Check(tkSemicolon) then
      Advance()
    else
      Break;
  end;
end;

function TParser.ParseTryStmt: TASTStmt;
var
  TryBody:     TCompoundStmt;
  FinallyBody: TCompoundStmt;
  ExceptBody:  TCompoundStmt;
  TFS:         TTryFinallyStmt;
  TES:         TTryExceptStmt;
  Line, Col:   Integer;
begin
  Line := FCurrent.Line;
  Col  := FCurrent.Col;
  Expect(tkTry);

  TryBody := TCompoundStmt.Create();
  TryBody.Line := Line;
  TryBody.Col  := Col;
  try
    ParseBodyInto(TryBody, tkFinally, tkExcept);

    if Check(tkFinally) then
    begin
      Advance();
      FinallyBody := TCompoundStmt.Create();
      try
        ParseBodyInto(FinallyBody, tkEnd, tkEnd);
        Expect(tkEnd);
        TFS             := TTryFinallyStmt.Create();
        TFS.Line        := Line;
        TFS.Col         := Col;
        TFS.TryBody     := TryBody;
        TFS.FinallyBody := FinallyBody;
        TryBody     := nil;
        FinallyBody := nil;
        Result := TFS;
      except
        FinallyBody.Free();
        raise;
      end;
    end
    else if Check(tkExcept) then
    begin
      Advance();
      TES      := TTryExceptStmt.Create();
      TES.Line := Line;
      TES.Col  := Col;
      TES.TryBody := TryBody;
      TryBody  := nil;
      try
        { Typed handler form: 'on [Var :] TypeName do Stmt' }
        if Check(tkIdent) and SameText(FCurrent.Value, 'on') then
        begin
          while Check(tkIdent) and SameText(FCurrent.Value, 'on') do
          begin
            TES.Handlers.Add(ParseExceptHandlerClause());
            if Check(tkSemicolon) then
              Advance();
          end;
          { Optional catch-all else clause }
          if Check(tkElse) then
          begin
            Advance();
            TES.ElseBody := TCompoundStmt.Create();
            ParseBodyInto(TES.ElseBody, tkEnd, tkEnd);
          end;
        end
        else
        begin
          { Plain catch-all body }
          ExceptBody := TCompoundStmt.Create();
          try
            ParseBodyInto(ExceptBody, tkEnd, tkEnd);
            TES.ExceptBody := ExceptBody;
            ExceptBody := nil;
          except
            ExceptBody.Free();
            raise;
          end;
        end;
        Expect(tkEnd);
        Result := TES;
        TES := nil;
      except
        TES.Free();
        raise;
      end;
    end
    else
    begin
      raise EParseError.Create(Format(
        'Expected ''finally'' or ''except'' after try body at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    end;
  except
    TryBody.Free();
    raise;
  end;
end;

{ Parse one 'on [VarName :] TypeName do Stmt' clause.
  The leading 'on' keyword (as identifier) must be the current token. }
function TParser.ParseExceptHandlerClause: TExceptHandlerClause;
var
  Name1: string;
  H:     TExceptHandlerClause;
  Stmt:  TASTStmt;
begin
  { consume 'on' }
  Expect(tkIdent);  { value is 'on' — caller already checked }
  H := TExceptHandlerClause.Create();
  try
    if not Check(tkIdent) then
      raise EParseError.Create(Format(
        'Expected identifier after ''on'' at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Name1 := FCurrent.Value;
    Advance();
    if Check(tkColon) then
    begin
      { 'on VarName : TypeName do' form }
      Advance();
      if not Check(tkIdent) then
        raise EParseError.Create(Format(
          'Expected type name after '':'' at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      H.VarName  := Name1;
      H.TypeName := FCurrent.Value;
      Advance();
    end
    else
    begin
      { 'on TypeName do' form — no variable binding }
      H.VarName  := '';
      H.TypeName := Name1;
    end;
    Expect(tkDo);
    H.Body := TCompoundStmt.Create();
    { Handler body is a single statement (Delphi/FPC standard) }
    if Check(tkBegin) then
    begin
      Advance();
      ParseBodyInto(H.Body, tkEnd, tkEnd);
      Expect(tkEnd);
    end
    else
    begin
      { Single statement — nil means empty (bare semicolon); skip it }
      Stmt := ParseStmt();
      if Stmt <> nil then
        H.Body.Stmts.Add(Stmt);
    end;
    Result := H;
  except
    H.Free();
    raise;
  end;
end;

function TParser.ParseRaiseStmt: TRaiseStmt;
begin
  Result := TRaiseStmt.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkRaise);
    { Bare raise has no expression; detect by checking statement terminators }
    if not (Check(tkSemicolon) or Check(tkEnd) or Check(tkEOF) or
            Check(tkFinally) or Check(tkExcept) or Check(tkElse)) then
      Result.Expr := ParseExpr();
  except
    Result.Free();
    raise;
  end;
end;

function TParser.ParseInheritedStmt: TInheritedCallStmt;
begin
  Result := TInheritedCallStmt.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkInherited);
    if not Check(tkIdent) then
      raise EParseError.Create(Format(
        'Expected method name after ''inherited'' at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result.Name := FCurrent.Value;
    Advance();
    { Mandatory parentheses: 'inherited Method' is a call and must carry ()
      even with no arguments (see language-rationale.adoc, "Mandatory
      parentheses on zero-argument calls"). }
    if not Check(tkLParen) then
      raise EParseError.Create(Format(
        'Bare reference to ''%s'' requires () for a call at line %d col %d in %s',
        [Result.Name, FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Advance();
    if not Check(tkRParen) then
    begin
      Result.Args.Add(ParseExpr());
      while Check(tkComma) do
      begin
        Advance();
        Result.Args.Add(ParseExpr());
      end;
    end;
    Expect(tkRParen);
  except
    Result.Free();
    raise;
  end;
end;

function TParser.ParseCompoundStmt: TCompoundStmt;
var
  Stmt: TASTStmt;
begin
  Result := TCompoundStmt.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkBegin);
    while not (Check(tkEnd) or Check(tkEOF)) do
    begin
      Stmt := ParseStmt();
      if Stmt <> nil then
        Result.Stmts.Add(Stmt);
      if Check(tkSemicolon) then
        Advance()
      else
        Break;
    end;
    Expect(tkEnd);
  except
    Result.Free();
    raise;
  end;
end;

function TParser.ParseCaseLabel: TASTExpr;
{ A case label is a single constant value or a range `lo..hi`.  A range is
  represented with a TSetRangeExpr (reused from set literals); the semantic and
  codegen passes treat a TSetRangeExpr label as an inclusive range test. }
var
  Lo, Hi: TASTExpr;
  Range:  TSetRangeExpr;
begin
  Lo := ParseExpr();
  if Check(tkDotDot) then
  begin
    Advance();  { consume '..' }
    Hi := ParseExpr();
    Range := TSetRangeExpr.Create();
    Range.Line     := Lo.Line;
    Range.Col      := Lo.Col;
    Range.LowExpr  := Lo;
    Range.HighExpr := Hi;
    Result := Range;
  end
  else
    Result := Lo;
end;

function TParser.ParseCaseStmt: TCaseStmt;
var
  Branch:   TCaseBranch;
  Stmt:     TASTStmt;
  CmpElse:  TCompoundStmt;
begin
  Result := TCaseStmt.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Expect(tkCase);
    Result.Selector := ParseExpr();
    Expect(tkOf);
    { Parse branches: value [, value]* : stmt }
    while not (Check(tkEnd) or Check(tkElse) or Check(tkEOF)) do
    begin
      Branch := TCaseBranch.Create();
      Branch.Values.Add(ParseCaseLabel());
      while Check(tkComma) do
      begin
        Advance();
        Branch.Values.Add(ParseCaseLabel());
      end;
      Expect(tkColon);
      Stmt := ParseStmt();
      { consume optional trailing semicolon between branches }
      if Check(tkSemicolon) then Advance();
      if Stmt <> nil then
        Branch.Stmt := Stmt
      else
        Branch.Stmt := TCompoundStmt.Create();  { empty branch }
      Result.Branches.Add(Branch);
    end;
    if Check(tkElse) then
    begin
      Advance();  { consume 'else' }
      if Check(tkBegin) then
        Result.ElseStmt := ParseCompoundStmt()
      else
      begin
        { Collect all statements until 'end' — FPC allows multi-stmt else without begin..end }
        CmpElse := TCompoundStmt.Create();
        CmpElse.Stmts.Add(ParseStmt());
        if Check(tkSemicolon) then Advance();
        while not (Check(tkEnd) or Check(tkEOF)) do
        begin
          CmpElse.Stmts.Add(ParseStmt());
          if Check(tkSemicolon) then Advance();
        end;
        if CmpElse.Stmts.Count = 1 then
        begin
          { Unwrap single-item compound for simplicity }
          Result.ElseStmt := TASTStmt(CmpElse.Stmts.Extract(CmpElse.Stmts.Items[0]));
          CmpElse.Free();
        end
        else
          Result.ElseStmt := CmpElse;
      end;
      if Check(tkSemicolon) then Advance();
    end;
    Expect(tkEnd);
  except
    Result.Free();
    raise;
  end;
end;

procedure TParser.ParseArgList(ACall: TProcCall);
begin
  ACall.Args.Add(ParseExpr());
  while Check(tkComma) do
  begin
    Advance();
    ACall.Args.Add(ParseExpr());
  end;
end;

procedure TParser.ParseMethodCallArgList(ACall: TMethodCallStmt);
begin
  ACall.Args.Add(ParseExpr());
  while Check(tkComma) do
  begin
    Advance();
    ACall.Args.Add(ParseExpr());
  end;
end;

{ ------------------------------------------------------------------ }
{ Unit parsing                                                        }
{ ------------------------------------------------------------------ }

function TParser.ParseForwardDecl(IsFunction: Boolean): TMethodDecl;
var
  Constraint: string;
begin
  Result := TMethodDecl.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    if IsFunction then
      Expect(tkFunction)
    else if Check(tkProcedure) then
      Advance()
    else if Check(tkConstructor) or Check(tkDestructor) then
      Advance()
    else
      Expect(tkProcedure);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result.Name := FCurrent.Value;
    Advance();
    { Optional generic type-parameter list: function Identity<T>(...).
      Mirrors the subset of ParseMethodDecl's logic that applies to
      forward declarations (no '.MethodName' continuation here — those
      live in the implementation section). }
    if Check(tkLessThan) and (PeekKind() = tkIdent) and
       (PeekKind2() in [tkGreaterThan, tkComma, tkColon]) then
    begin
      Result.TypeParams           := TStringList.Create();
      Result.TypeParamConstraints := TStringList.Create();
      Advance();  { consume '<' }
      if not Check(tkIdent) then
        raise EParseError.Create(Format('Expected type parameter name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.TypeParams.Add(FCurrent.Value);
      Advance();
      Constraint := '';
      if Check(tkColon) then
      begin
        Advance();
        if      Check(tkClass)  then begin Constraint := 'class';  Advance(); end
        else if Check(tkRecord) then begin Constraint := 'record'; Advance(); end
        else if Check(tkIdent)  then begin Constraint := FCurrent.Value; Advance(); end
        else
          raise EParseError.Create(Format(
            'Expected ''class'', ''record'', or a type name after '':'' at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      end;
      Result.TypeParamConstraints.Add(Constraint);
      while Check(tkComma) do
      begin
        Advance();
        if not Check(tkIdent) then
          raise EParseError.Create(Format('Expected type parameter name at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        Result.TypeParams.Add(FCurrent.Value);
        Advance();
        Constraint := '';
        if Check(tkColon) then
        begin
          Advance();
          if      Check(tkClass)  then begin Constraint := 'class';  Advance(); end
          else if Check(tkRecord) then begin Constraint := 'record'; Advance(); end
          else if Check(tkIdent)  then begin Constraint := FCurrent.Value; Advance(); end
          else
            raise EParseError.Create(Format(
              'Expected ''class'', ''record'', or a type name after '':'' at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        end;
        Result.TypeParamConstraints.Add(Constraint);
      end;
      Expect(tkGreaterThan);
    end;
    if Check(tkLParen) then
    begin
      Advance();
      if not Check(tkRParen) then
        ParseParamList(Result.Params);
      Expect(tkRParen);
    end;
    if IsFunction then
    begin
      Expect(tkColon);
      Result.ReturnTypeName := ParseTypeName();
    end;
    Expect(tkSemicolon);
    { Directive loop — forward declarations may carry overload, external,
      and the same identifier-form directives accepted by ParseMethodDecl. }
    while True do
    begin
      if Check(tkExternal) then
      begin
        Result.IsExternal := True;
        Advance();
        { optional library name — external 'c' name 'malloc' (records a
          unit-level link dependency). }
        if Check(tkStringLit) then
        begin
          Result.ExternalLib := FCurrent.Value;
          AddLinkLib(FCurrent.Value, FCurrent.Line, FCurrent.Col);
          Advance();
        end;
        if Check(tkIdent) and SameText(FCurrent.Value, 'name') then
        begin
          Advance();
          Result.ExternalName := FCurrent.Value;
          Expect(tkStringLit);
        end;
        if Check(tkSemicolon) then Advance();
      end
      else if Check(tkIdent) and SameText(FCurrent.Value, 'overload') then
      begin
        Result.IsOverload := True;
        Advance();
        if Check(tkSemicolon) then Advance();
      end
      else if Check(tkIdent) and
              (SameText(FCurrent.Value, 'inline')      or
               SameText(FCurrent.Value, 'stdcall')     or
               SameText(FCurrent.Value, 'cdecl')       or
               SameText(FCurrent.Value, 'register')    or
               SameText(FCurrent.Value, 'pascal')      or
               SameText(FCurrent.Value, 'safecall')    or
               SameText(FCurrent.Value, 'varargs')     or
               SameText(FCurrent.Value, 'forward')     or
               SameText(FCurrent.Value, 'deprecated')  or
               SameText(FCurrent.Value, 'platform')    or
               SameText(FCurrent.Value, 'experimental')) then
      begin
        if SameText(FCurrent.Value, 'inline') then
          Result.IsInline := True
        else if SameText(FCurrent.Value, 'varargs') then
          Result.IsVarArgs := True
        else if SameText(FCurrent.Value, 'cdecl')    or
                SameText(FCurrent.Value, 'stdcall')  or
                SameText(FCurrent.Value, 'register') or
                SameText(FCurrent.Value, 'pascal')   or
                SameText(FCurrent.Value, 'safecall') then
          Result.CallingConv := LowerCase(FCurrent.Value);
        Advance();
        if Check(tkSemicolon) then Advance();
      end
      else
        Break;
    end;
    { Body remains nil — forward or external declaration }
  except
    Result.Free();
    raise;
  end;
end;

function TParser.ParseUnit: TUnit;
var
  InitStmt: TASTStmt;
begin
  Result := TUnit.Create();
  FLinkLibs := Result.LinkLibs;   { collect external 'lib' deps into the unit }
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;

    Expect(tkUnit);
    if not Check(tkIdent) then
      raise EParseError.Create(Format('Expected unit name at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    Result.Name := FCurrent.Value;
    Advance();
    while Check(tkDot) do
    begin
      Advance();
      if not CheckUnitNamePart() then
        raise EParseError.Create(Format('Expected identifier after ''.'' in unit name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.Name := Result.Name + '.' + FCurrent.Value;
      Advance();
    end;
    Expect(tkSemicolon);

    { Interface section }
    Expect(tkIntf);
    if Check(tkUses) then
      ParseUsesList(Result.UsedUnits);
    while Check(tkType) or Check(tkVar) or Check(tkThreadVar) or Check(tkConst) or
          Check(tkProcedure) or Check(tkFunction) or
          Check(tkConstructor) or Check(tkDestructor) do
    begin
      if Check(tkType) then
        ParseTypeSection(Result.IntfBlock)
      else if Check(tkVar) or Check(tkThreadVar) then
        ParseVarBlock(Result.IntfBlock)
      else if Check(tkConst) then
        ParseConstBlock(Result.IntfBlock.ConstDecls)
      else if Check(tkFunction) then
        Result.IntfBlock.ProcDecls.Add(ParseForwardDecl(True))
      else
        Result.IntfBlock.ProcDecls.Add(ParseForwardDecl(False));
    end;

    { Implementation section }
    Expect(tkImplementation);
    if Check(tkUses) then
      ParseUsesList(Result.ImplUsedUnits);  { implementation-only deps — loaded but not re-exported }
    while Check(tkProcedure) or Check(tkFunction) or
          Check(tkConstructor) or Check(tkDestructor) or
          Check(tkVar) or Check(tkThreadVar) or Check(tkConst) or Check(tkType) or
          AtClassOperator() or
          (Check(tkIdent) and SameText(FCurrent.Value, 'static') and
           (PeekKind() in [tkFunction, tkProcedure])) do
    begin
      if AtClassOperator() then
        { Out-of-line operator body in the implementation section. }
        ParseStandaloneDecl(Result.ImplBlock)
      else if Check(tkIdent) and SameText(FCurrent.Value, 'static') and
         (PeekKind() in [tkFunction, tkProcedure]) then
        { Out-of-line static-method body in the implementation section:
          `static function T.M ...`.  Mirror the program-level standalone path
          (ParseStandaloneDecl) — consume `static`, parse the routine, mark it
          IsStatic so it reconciles against the in-class static declaration. }
        ParseStandaloneDecl(Result.ImplBlock)
      else if Check(tkFunction) then
        Result.ImplBlock.ProcDecls.Add(ParseMethodDecl(True, True))
      else if Check(tkVar) or Check(tkThreadVar) then
        ParseVarBlock(Result.ImplBlock)
      else if Check(tkConst) then
        ParseConstBlock(Result.ImplBlock.ConstDecls)
      else if Check(tkType) then
        ParseTypeSection(Result.ImplBlock)
      else
        { ACanHaveNestedProcs=True: an impl routine whose body opens with a
          nested procedure/function (before any var/const/type) must parse as
          one routine WITH a body, not split into two bodyless decls.  The
          IsForward guard inside ParseMethodDecl stops a forward decl from
          swallowing the following sibling.  (Andrew's fix 82e770ac.) }
        Result.ImplBlock.ProcDecls.Add(ParseMethodDecl(False, True));
    end;

    { Optional initialization / finalization sections }
    if Check(tkInitialization) then
    begin
      Advance();
      Result.InitStmts := TObjectList.Create(True);
      while not (Check(tkEnd) or Check(tkFinalization) or Check(tkEOF)) do
      begin
        InitStmt := ParseStmt();
        if InitStmt <> nil then Result.InitStmts.Add(InitStmt);
        if Check(tkSemicolon) then Advance() else Break;
      end;
    end;
    if Check(tkFinalization) then
    begin
      Advance();
      Result.FinalStmts := TObjectList.Create(True);
      while not (Check(tkEnd) or Check(tkEOF)) do
      begin
        InitStmt := ParseStmt();
        if InitStmt <> nil then Result.FinalStmts.Add(InitStmt);
        if Check(tkSemicolon) then Advance() else Break;
      end;
    end;

    { Issue #172: reject the legacy Turbo Pascal unit-initialization form
      (`implementation ... begin ... end.`).  Blaise deliberately drops this
      redundant, asymmetric spelling in favour of an explicit
      'initialization' section (see docs/language-rationale.adoc).  Give a
      clear, actionable error instead of the raw 'Expected end but got begin'. }
    if Check(tkBegin) then
      raise EParseError.Create(Format(
        'A unit body cannot use a bare ''begin'' block; use an ' +
        '''initialization'' section instead ' +
        '(the legacy Turbo Pascal unit-initialization form is not supported) ' +
        'at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));

    Expect(tkEnd);
    Expect(tkDot);

    if not Check(tkEOF) then
      raise EParseError.Create(Format(
        'Unexpected tokens after unit end at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  except
    Result.Free();
    raise;
  end;
end;

{ ------------------------------------------------------------------ }
{ Expression parsing — standard precedence climbing                   }
{ ------------------------------------------------------------------ }

{ Parse one element of a bracket literal [ ... ].  An ordinary element is a
  plain expression; a `lo..hi` form (set range, issue #105) becomes a
  TSetRangeExpr that uSemantic expands into individual set members.  The
  range form is only meaningful for set literals — uSemantic rejects it in
  array-literal context. }
function TParser.ParseSetOrArrayElement: TASTExpr;
var
  LowE:  TASTExpr;
  Range: TSetRangeExpr;
begin
  LowE := Self.ParseExpr();
  if not Check(tkDotDot) then
    Exit(LowE);
  Range          := TSetRangeExpr.Create();
  Range.Line     := LowE.Line;
  Range.Col      := LowE.Col;
  Range.LowExpr  := LowE;
  Advance();  { consume '..' }
  Range.HighExpr := Self.ParseExpr();
  Result := Range;
end;

function TParser.ParseExpr: TASTExpr;
var
  Right:    TASTExpr;
  CmpOp:    TBinaryOp;
  Node:     TBinaryExpr;
  IsNode:   TIsExpr;
  AsNode:   TAsExpr;
  OpLine:   Integer;
  OpCol:    Integer;
begin
  Result := ParseAddSub();

  { Comparison — non-associative, one level only }
  if Check(tkEquals) or Check(tkNotEquals) or
     Check(tkLessThan) or Check(tkGreaterThan) or
     Check(tkLessEqual) or Check(tkGreaterEqual) then
  begin
    if      Check(tkEquals)      then CmpOp := boEQ
    else if Check(tkNotEquals)   then CmpOp := boNE
    else if Check(tkLessThan)    then CmpOp := boLT
    else if Check(tkGreaterThan) then CmpOp := boGT
    else if Check(tkLessEqual)   then CmpOp := boLE
    else                              CmpOp := boGE;
    OpLine  := FCurrent.Line;
    OpCol   := FCurrent.Col;
    Advance();
    Right       := ParseAddSub();
    Node        := TBinaryExpr.Create();
    Node.Line   := OpLine;
    Node.Col    := OpCol;
    Node.Op     := CmpOp;
    Node.Left   := Result;
    Node.Right  := Right;
    Result      := Node;
  end
  else if Check(tkIn) then
  begin
    OpLine  := FCurrent.Line;
    OpCol   := FCurrent.Col;
    Advance();
    Right       := ParseAddSub();
    Node        := TBinaryExpr.Create();
    Node.Line   := OpLine;
    Node.Col    := OpCol;
    Node.Op     := boIn;
    Node.Left   := Result;
    Node.Right  := Right;
    Result      := Node;
  end
  else if Check(tkIs) then
  begin
    IsNode          := TIsExpr.Create();
    IsNode.Line     := FCurrent.Line;
    IsNode.Col      := FCurrent.Col;
    Advance();
    IsNode.Obj      := Result;
    IsNode.TypeName := FCurrent.Value;
    Expect(tkIdent);
    Result := IsNode;
  end
  else if Check(tkAs) then
  begin
    Advance();
    AsNode          := TAsExpr.Create();
    AsNode.Obj      := Result;
    AsNode.TypeName := FCurrent.Value;
    Expect(tkIdent);
    Result := AsNode;
  end;
end;

function TParser.ParseAddSub: TASTExpr;
var
  Right:  TASTExpr;
  Op:     TBinaryOp;
  Node:   TBinaryExpr;
  OpLine: Integer;
  OpCol:  Integer;
begin
  Result := ParseTerm();
  while Check(tkPlus) or Check(tkMinus) or Check(tkOr) do
  begin
    if      Check(tkPlus)  then Op := boAdd
    else if Check(tkMinus) then Op := boSub
    else                        Op := boOr;
    OpLine := FCurrent.Line;
    OpCol  := FCurrent.Col;
    Advance();
    Right      := ParseTerm();
    Node       := TBinaryExpr.Create();
    Node.Line  := OpLine;
    Node.Col   := OpCol;
    Node.Op    := Op;
    Node.Left  := Result;
    Node.Right := Right;
    Result     := Node;
  end;
end;

function TParser.ParseTerm: TASTExpr;
var
  Right:  TASTExpr;
  Op:     TBinaryOp;
  Node:   TBinaryExpr;
  OpLine: Integer;
  OpCol:  Integer;
begin
  Result := ParseFactor();
  while Check(tkStar) or Check(tkSlash) or Check(tkDiv) or Check(tkMod)
        or Check(tkAnd) or Check(tkXor) or Check(tkShl) or Check(tkShr)
        or Check(tkSar) do
  begin
    if      Check(tkStar)  then Op := boMul
    else if Check(tkSlash) then Op := boSlash
    else if Check(tkMod)   then Op := boMod
    else if Check(tkAnd)   then Op := boAnd
    else if Check(tkXor)   then Op := boXor
    else if Check(tkShl)   then Op := boShl
    else if Check(tkShr)   then Op := boShr
    else if Check(tkSar)   then Op := boSar
    else                        Op := boDiv;
    OpLine     := FCurrent.Line;
    OpCol      := FCurrent.Col;
    Advance();
    Right      := ParseFactor();
    Node       := TBinaryExpr.Create();
    Node.Line  := OpLine;
    Node.Col   := OpCol;
    Node.Op    := Op;
    Node.Left  := Result;
    Node.Right := Right;
    Result     := Node;
  end;
end;

function TParser.ParseAnonMethodLiteral: TAnonMethodExpr;
{ Anonymous procedure/function literal in expression position
  (docs/anonymous-methods-design.adoc):

    procedure [Weak a, b] (params) begin ... end
    function (params): T begin ... end

  The body is a full routine block — its own var/const/type sections and
  nested decls are allowed (ParseBlock).  There is no name and no trailing
  semicolon: the literal ends at the body's 'end', and the surrounding
  expression context continues from there. }
var
  IsFunc: Boolean;
  MD:     TMethodDecl;
begin
  Result := TAnonMethodExpr.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    IsFunc := Check(tkFunction);
    Advance();  { consume 'procedure' / 'function' }
    { Optional [Weak name, name, ...] capture-modifier list (used from the
      [Weak]-capture phase; parsed and stored now).  NOTE: keep this comment
      free of inner brace characters — a nested open-brace closes the comment
      early and the lexer then mis-parses the rest of the line. }
    if Check(tkLBracket) then
    begin
      Advance();
      if not (Check(tkIdent) and SameText(FCurrent.Value, 'Weak')) then
        raise EParseError.Create(Format(
          'Expected ''Weak'' in anonymous-method capture-modifier list ' +
          'at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Advance();
      Result.WeakCaptures := TStringList.Create();
      if not Check(tkIdent) then
        raise EParseError.Create(Format(
          'Expected captured name after ''Weak'' at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      Result.WeakCaptures.Add(FCurrent.Value);
      Advance();
      while Check(tkComma) do
      begin
        Advance();
        if not Check(tkIdent) then
          raise EParseError.Create(Format(
            'Expected captured name after '','' at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        Result.WeakCaptures.Add(FCurrent.Value);
        Advance();
      end;
      Expect(tkRBracket);
    end;
    MD := TMethodDecl.Create();
    MD.Line := Result.Line;
    MD.Col  := Result.Col;
    Result.Decl := MD;
    if Check(tkLParen) then
    begin
      Advance();
      if not Check(tkRParen) then
        ParseParamList(MD.Params);
      Expect(tkRParen);
    end;
    if IsFunc then
    begin
      Expect(tkColon);
      MD.ReturnTypeName := ParseTypeName();
    end;
    if not (Check(tkBegin) or Check(tkVar) or Check(tkConst) or Check(tkType)) then
      raise EParseError.Create(Format(
        'Expected anonymous-method body (''begin'' or a local declaration ' +
        'section) at line %d col %d in %s',
        [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
    MD.Body := ParseBlock();
  except
    Result.Free();
    raise;
  end;
end;

function TParser.ArrowLambdaAhead: Boolean;
var
  N, Depth: Integer;
  K: TTokenKind;
begin
  Result := False;
  if Check(tkIdent) and (PeekKind() = tkArrow) then
    Exit(True);
  if not Check(tkLParen) then Exit;
  { Scan to the matching ')' (param lists may nest parens in default-value
    expressions) and test for a following '->'. }
  N := 1;
  Depth := 1;
  while Depth > 0 do
  begin
    K := PeekKindAt(N);
    if K = tkEOF then Exit;
    if K = tkLParen then Depth := Depth + 1
    else if K = tkRParen then Depth := Depth - 1;
    N := N + 1;
    { Defensive bound: a genuine lambda parameter list is short. }
    if N > 64 then Exit;
  end;
  Result := PeekKindAt(N) = tkArrow;
end;

function TParser.ParseArrowLambda: TAnonMethodExpr;
var
  MD:       TMethodDecl;
  Par:      TMethodParam;
  TypedAhead: Boolean;
  N: Integer;
  K: TTokenKind;
begin
  Result := TAnonMethodExpr.Create();
  try
    Result.Line := FCurrent.Line;
    Result.Col  := FCurrent.Col;
    Result.IsArrow := True;
    MD := TMethodDecl.Create();
    MD.Line := Result.Line;
    MD.Col  := Result.Col;
    Result.Decl := MD;

    if Check(tkIdent) then
    begin
      { Single inferred parameter: x -> ... }
      Par := TMethodParam.Create();
      Par.ParamName := FCurrent.Value;
      Par.TypeName  := '';
      MD.Params.Add(Par);
      Advance();
    end
    else
    begin
      Expect(tkLParen);
      if not Check(tkRParen) then
      begin
        { Distinguish the untyped ident list '(a, b)' from a fully typed
          '(a: T; const b: U)': scan for a ':' before the closing ')'. }
        TypedAhead := False;
        N := 0;
        while True do
        begin
          K := PeekKindAt(N);
          if (K = tkRParen) or (K = tkEOF) then Break;
          if K = tkColon then begin TypedAhead := True; Break; end;
          N := N + 1;
          if N > 64 then Break;
        end;
        if TypedAhead then
          ParseParamList(MD.Params)
        else
        begin
          if not Check(tkIdent) then
            raise EParseError.Create(Format(
              'Expected lambda parameter name at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          Par := TMethodParam.Create();
          Par.ParamName := FCurrent.Value;
          Par.TypeName  := '';
          MD.Params.Add(Par);
          Advance();
          while Check(tkComma) do
          begin
            Advance();
            if not Check(tkIdent) then
              raise EParseError.Create(Format(
                'Expected lambda parameter name after '','' at line %d col %d in %s',
                [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
            Par := TMethodParam.Create();
            Par.ParamName := FCurrent.Value;
            Par.TypeName  := '';
            MD.Params.Add(Par);
            Advance();
          end;
        end;
      end;
      Expect(tkRParen);
    end;

    Expect(tkArrow);

    if Check(tkBegin) or Check(tkVar) or Check(tkConst) or Check(tkType) then
      MD.Body := ParseBlock()
    else
      { Single-expression body — desugared by uSemantic once the target
        type is known ('Result := expr' for function targets, a call
        statement for procedure targets). }
      Result.ArrowExpr := ParseExpr();
  except
    Result.Free();
    raise;
  end;
end;

function TParser.ParseFactor: TASTExpr;
var
  IntNode:    TIntLiteral;
  FloatNode:  TFloatLiteral;
  StrNode:    TStringLiteral;
  NilNode:    TNilLiteral;
  IdNode:     TIdentExpr;
  FldNode:    TFieldAccessExpr;
  MCallNode:  TMethodCallExpr;
  FCallNode:  TFuncCallExpr;
  SuppNode:   TSupportsExpr;
  DerefNode:  TDerefExpr;
  AddrNode:   TAddrOfExpr;
  NotNode:    TNotExpr;
  Inner:      TASTExpr;
  Name:       string;
  SecondName: string;
  QualUnit:   string;
  Line, Col:  Integer;
  ZeroNode:   TIntLiteral;
  NegNode:    TBinaryExpr;
  SubNode:       TStringSubscriptExpr;
  ArrNode:       TArrayLiteralExpr;
  IndCallNode:   TIndirectFuncCallExpr;
  ParseIntV:    Int64;
  ParseIntFlag: Boolean;
  InhNode:      TInheritedCallExpr;
begin
  { Terse lambda (Phase 9a): 'x -> ...' or '(params) -> ...' — must be
    detected before the plain ident / parenthesised-expression arms. }
  if ArrowLambdaAhead() then
    Exit(ParseArrowLambda());
  case FCurrent.Kind of
    tkProcedure, tkFunction:
      begin
        { Anonymous procedure/function literal — in expression position a
          'procedure'/'function' keyword can only start a closure literal
          (a type declaration is never an expression). }
        Result := ParseAnonMethodLiteral();
      end;
    tkInherited:
      begin
        { `inherited Method(args)` in expression position — the parent
          method's result value is needed.  Mirrors ParseInheritedStmt. }
        InhNode      := TInheritedCallExpr.Create();
        InhNode.Line := FCurrent.Line;
        InhNode.Col  := FCurrent.Col;
        Advance();  { consume 'inherited' }
        if not Check(tkIdent) then
          raise EParseError.Create(Format(
            'Expected method name after ''inherited'' at line %d col %d in %s',
            [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        InhNode.Name := FCurrent.Value;
        Advance();
        { Mandatory parentheses: 'inherited Method' is a call and must carry
          () even with no arguments (see language-rationale.adoc, "Mandatory
          parentheses on zero-argument calls"). }
        if not Check(tkLParen) then
          raise EParseError.Create(Format(
            'Bare reference to ''%s'' requires () for a call at line %d col %d in %s',
            [InhNode.Name, FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        Advance();
        if not Check(tkRParen) then
        begin
          InhNode.Args.Add(Self.ParseExpr());
          while Check(tkComma) do
          begin
            Advance();
            InhNode.Args.Add(Self.ParseExpr());
          end;
        end;
        Expect(tkRParen);
        Result := InhNode;
      end;
    tkAt:
      begin
        AddrNode      := TAddrOfExpr.Create();
        AddrNode.Line := FCurrent.Line;
        AddrNode.Col  := FCurrent.Col;
        Advance();  { consume '@' }
        AddrNode.Expr := Self.ParseFactor();  { Self. forces recursive call }
        Result := AddrNode;
      end;
    tkNot:
      begin
        NotNode      := TNotExpr.Create();
        NotNode.Line := FCurrent.Line;
        NotNode.Col  := FCurrent.Col;
        Advance();  { consume 'not' }
        NotNode.Expr := Self.ParseFactor();  { Self. forces recursive call }
        Result := NotNode;
      end;
    tkMinus:
      begin
        { Unary minus: synthesise as 0 - Factor }
        ZeroNode       := TIntLiteral.Create();
        ZeroNode.Line  := FCurrent.Line;
        ZeroNode.Col   := FCurrent.Col;
        ZeroNode.Value := 0;
        NegNode        := TBinaryExpr.Create();
        NegNode.Line   := FCurrent.Line;
        NegNode.Col    := FCurrent.Col;
        NegNode.Op     := boSub;
        NegNode.Left   := ZeroNode;
        Advance();  { consume '-' }
        NegNode.Right  := Self.ParseFactor();  { Self. forces recursive call, not result-var read }
        Result         := NegNode;
      end;
    tkNil:
      begin
        NilNode      := TNilLiteral.Create();
        NilNode.Line := FCurrent.Line;
        NilNode.Col  := FCurrent.Col;
        Advance();
        Result := NilNode;
      end;
    tkIntLit:
      begin
        IntNode       := TIntLiteral.Create();
        IntNode.Line  := FCurrent.Line;
        IntNode.Col   := FCurrent.Col;
        ParseIntOrUInt64Literal(FCurrent.Value, ParseIntV, ParseIntFlag);
        IntNode.Value    := ParseIntV;
        IntNode.IsUInt64 := ParseIntFlag;
        Advance();
        Result := IntNode;
      end;
    tkFloatLit:
      begin
        FloatNode       := TFloatLiteral.Create();
        FloatNode.Line  := FCurrent.Line;
        FloatNode.Col   := FCurrent.Col;
        FloatNode.Value := StripUnderscores(FCurrent.Value);
        Advance();
        Result := FloatNode;
      end;
    tkStringLit:
      begin
        StrNode       := TStringLiteral.Create();
        StrNode.Line  := FCurrent.Line;
        StrNode.Col   := FCurrent.Col;
        StrNode.Value := FCurrent.Value;
        Advance();
        Result := StrNode;
      end;
    tkIdent:
      begin
        Name := FCurrent.Value;
        Line := FCurrent.Line;
        Col  := FCurrent.Col;
        Advance();
        { Unit-qualified reference 'Unit.Symbol' (Unit may be dotted to any
          depth).  Collapse to the bare Symbol and reposition the origin to it,
          so everything below resolves Symbol through the uses chain as an
          unqualified reference — a free call when '(' follows, otherwise a
          plain identifier / indexed / chained / generic access.  No-op for a
          same-prefixed record/field chain.  QualUnit captures the matched
          unit so a plain identifier can be resolved against that unit's own
          exports (see IdNode.QualifierUnit below). }
        TryCollapseUnitQualifier(Name, Line, Col, QualUnit);
        { Generic constructor: TypeName<Args>.Method  or diamond TypeName<>.Method
          Heuristic: '<' followed by IDENT followed by '>' or ',' is treated as
          generic type args.  '<>' (empty) is the diamond operator — type args
          inferred by the semantic pass from the LHS type.
          If the token two ahead is neither '>' nor ',', the '<' is a comparison
          operator (e.g. "if A < B then"). }
        if Check(tkNotEquals) and (PeekKind() = tkDot) then
        begin
          { Diamond: TFoo<> — the lexer folds '<>' into a single tkNotEquals token }
          Advance();  { consume '<>' }
          Name := Name + '<>';
          { Must be followed by '.' (type access) }
          if not Check(tkDot) then
            raise EParseError.Create(Format(
              'Expected ''.'' after ''<>'' at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        end
        else if Check(tkLessThan) and (PeekKind() = tkIdent) and
           (PeekKind2() in [tkGreaterThan, tkComma, tkLessThan]) then
        begin
          { Generic type args.  PeekKind2 = '<' means the first arg is itself
            generic (TList<TList<Integer>>) — recurse via ParseTypeName so
            nested generics parse.  Plain idents also go through ParseTypeName
            (which simply returns the ident when no '<' follows). }
          Advance();  { consume '<' }
          Name := Name + '<' + Self.ParseTypeName();
          while Check(tkComma) do
          begin
            Advance();
            Name := Name + ',' + Self.ParseTypeName();
          end;
          Expect(tkGreaterThan);
          Name := Name + '>';
          { Generic type args must be followed by '.' (type access) or '(' (generic func call) }
          if not (Check(tkDot) or Check(tkLParen)) then
            raise EParseError.Create(Format(
              'Expected ''.'' or ''('' after generic type arguments at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
        end;
        { Supports(Obj, IFoo) or Supports(Obj, IFoo, OutVar) — compiler intrinsic }
        if SameText(Name, 'Supports') and Check(tkLParen) then
        begin
          SuppNode          := TSupportsExpr.Create();
          SuppNode.Line     := Line;
          SuppNode.Col      := Col;
          Advance();  { consume '(' }
          SuppNode.Obj      := ParseExpr();
          Expect(tkComma);
          SuppNode.IntfTypeName := FCurrent.Value;
          Expect(tkIdent);
          if Check(tkComma) then
          begin
            Advance();  { consume ',' }
            SuppNode.OutVarName := FCurrent.Value;
            Expect(tkIdent);
          end;
          Expect(tkRParen);
          Result := SuppNode;
        end
        else if Check(tkDot) then
        begin
          Advance();
          if not Check(tkIdent) then
            raise EParseError.Create(Format('Expected field or method name at line %d col %d in %s',
              [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
          SecondName := FCurrent.Value;
          Advance();
          { Generic-method call: IDENT '.' IDENT '<' TypeArgs '>' '(' ... ')'.
            Fold the explicit type arguments into the method name
            (Pick<Integer>), mirroring the generic free-function call site; the
            semantic pass instantiates on the '<' in the name. }
          if Check(tkLessThan) and (PeekKind() = tkIdent) and
             (PeekKind2() in [tkGreaterThan, tkComma, tkLessThan]) then
          begin
            Advance();  { consume '<' }
            SecondName := SecondName + '<' + ParseTypeName();
            while Check(tkComma) do
            begin
              Advance();
              SecondName := SecondName + ',' + ParseTypeName();
            end;
            Expect(tkGreaterThan);
            SecondName := SecondName + '>';
          end;
          if Check(tkLParen) then
          begin
            { IDENT '.' IDENT '(' ... ')' — method call expression }
            MCallNode            := TMethodCallExpr.Create();
            MCallNode.Line       := Line;
            MCallNode.Col        := Col;
            MCallNode.ObjectName := Name;
            MCallNode.Name       := SecondName;
            MCallNode.QualifierUnit := QualUnit;
            Advance();
            if not Check(tkRParen) then
            begin
              MCallNode.Args.Add(ParseExpr());
              while Check(tkComma) do
              begin
                Advance();
                MCallNode.Args.Add(ParseExpr());
              end;
            end;
            Expect(tkRParen);
            Result := MCallNode;
          end
          else
          begin
            { IDENT '.' IDENT — field access or constructor call }
            FldNode            := TFieldAccessExpr.Create();
            FldNode.Line       := Line;
            FldNode.Col        := Col;
            FldNode.RecordName := Name;
            FldNode.FieldName  := SecondName;
            FldNode.QualifierUnit := QualUnit;
            Result := FldNode;
            { Indexed property read: Ident.Prop[idx] }
            if Check(tkLBracket) then
            begin
              Advance();
              FldNode.PropIndexExpr := ParseExpr();
              Expect(tkRBracket);
            end;
            { Chained access: A.B.C.D ... — wrap each subsequent '.IDENT' }
            while Check(tkDot) and (PeekKind() = tkIdent) do
            begin
              Advance();  { consume '.' }
              SecondName := FCurrent.Value;
              Advance();  { consume field/method name }
              if Check(tkLParen) then
              begin
                { Chained method call on expression }
                MCallNode             := TMethodCallExpr.Create();
                MCallNode.Line        := FCurrent.Line;
                MCallNode.Col         := FCurrent.Col;
                MCallNode.ObjectName  := '';
                MCallNode.Name        := SecondName;
                MCallNode.ObjExpr     := Result;
                Advance();  { consume '(' }
                if not Check(tkRParen) then
                begin
                  MCallNode.Args.Add(ParseExpr());
                  while Check(tkComma) do
                  begin
                    Advance();
                    MCallNode.Args.Add(ParseExpr());
                  end;
                end;
                Expect(tkRParen);
                Result := MCallNode;
              end
              else
              begin
                FldNode            := TFieldAccessExpr.Create();
                FldNode.Line       := FCurrent.Line;
                FldNode.Col        := FCurrent.Col;
                FldNode.Base       := Result;
                FldNode.FieldName  := SecondName;
                Result := FldNode;
                { Indexed property on chained access: A.B.Prop[idx] }
                if Check(tkLBracket) then
                begin
                  Advance();
                  FldNode.PropIndexExpr := ParseExpr();
                  Expect(tkRBracket);
                end;
              end;
            end;
          end;
        end
        else if Check(tkLParen) then
        begin
          { Standalone function call expression: Ident '(' [args] ')' }
          FCallNode      := TFuncCallExpr.Create();
          FCallNode.Line := Line;
          FCallNode.Col  := Col;
          FCallNode.Name := Name;
          Advance();  { consume '(' }
          if not Check(tkRParen) then
          begin
            FCallNode.Args.Add(ParseExpr());
            while Check(tkComma) do
            begin
              Advance();
              FCallNode.Args.Add(ParseExpr());
            end;
          end;
          Expect(tkRParen);
          Result := FCallNode;
          { Postfix chained field/method access: FuncOrCast(...).Member ... }
          while Check(tkDot) and (PeekKind() = tkIdent) do
          begin
            Advance();  { consume '.' }
            SecondName := FCurrent.Value;
            Advance();  { consume field/method name }
            FldNode            := TFieldAccessExpr.Create();
            FldNode.Line       := FCurrent.Line;
            FldNode.Col        := FCurrent.Col;
            FldNode.Base       := Result;
            FldNode.FieldName  := SecondName;
            Result := FldNode;
            if Check(tkLParen) then
            begin
              { Method call with args on the chained expression — represent
                by marking the access as a method call and parsing an arg list
                into a synthesised TMethodCallExpr with Obj=Base. }
              { We convert the TFieldAccessExpr into an arg-bearing method call. }
              Advance();  { consume '(' }
              if not Check(tkRParen) then
              begin
                FldNode.ResolvedType := nil; { placeholder to note args }
              end;
              { Lift the FldNode to a method call by storing args via a
                temporary TMethodCallExpr and using Base for the receiver. }
              MCallNode             := TMethodCallExpr.Create();
              MCallNode.Line        := FldNode.Line;
              MCallNode.Col         := FldNode.Col;
              MCallNode.ObjectName  := '';  { empty — receiver is Base expr }
              MCallNode.Name        := SecondName;
              MCallNode.ObjExpr     := FldNode.Base;
              FldNode.Base          := nil;  { transfer ownership }
              FldNode.Free();
              if not Check(tkRParen) then
              begin
                MCallNode.Args.Add(ParseExpr());
                while Check(tkComma) do
                begin
                  Advance();
                  MCallNode.Args.Add(ParseExpr());
                end;
              end;
              Expect(tkRParen);
              Result := MCallNode;
            end
            else if Check(tkLBracket) then
            begin
              { Indexed property on chained access from a typecast/call:
                FuncOrCast(...).A.B.Items[idx].  Same shape as the
                A.B.Items[idx] branch above — store the index on the
                outer FieldAccess so the analyser can resolve the property
                with its index in one place. }
              Advance();
              FldNode.PropIndexExpr := ParseExpr();
              Expect(tkRBracket);
            end;
          end;
        end
        else
        begin
          IdNode      := TIdentExpr.Create();
          IdNode.Line := Line;
          IdNode.Col  := Col;
          IdNode.Name := Name;
          IdNode.QualifierUnit := QualUnit;
          Result := IdNode;
        end;
        { Postfix dereference: Expr^ and optional Expr^.Field chaining }
        if Check(tkCaret) then
        begin
          Advance();
          DerefNode      := TDerefExpr.Create();
          DerefNode.Line := Line;
          DerefNode.Col  := Col;
          DerefNode.Expr := Result;
          Result         := DerefNode;
          { Deref-then-field: P^.Field or P^.Field.Sub ... }
          while Check(tkDot) and (PeekKind() = tkIdent) do
          begin
            Advance();  { consume '.' }
            FldNode           := TFieldAccessExpr.Create();
            FldNode.Line      := FCurrent.Line;
            FldNode.Col       := FCurrent.Col;
            FldNode.FieldName := FCurrent.Value;
            FldNode.Base      := Result;
            Advance();  { consume field name }
            Result := FldNode;
          end;
        end;
      end;
    tkLBracket:
      begin
        ArrNode      := TArrayLiteralExpr.Create();
        ArrNode.Line := FCurrent.Line;
        ArrNode.Col  := FCurrent.Col;
        try
          Advance();  { consume '[' }
          if not Check(tkRBracket) then
          begin
            ArrNode.Elements.Add(Self.ParseSetOrArrayElement());
            while Check(tkComma) do
            begin
              Advance();  { consume ',' }
              ArrNode.Elements.Add(Self.ParseSetOrArrayElement());
            end;
          end;
          Expect(tkRBracket);
        except
          ArrNode.Free();
          raise;
        end;
        Result := ArrNode;
        Exit;  { array literals are not subscriptable — skip postfix check }
      end;
    tkLParen:
      begin
        Advance();
        Inner := ParseExpr();
        Expect(tkRParen);
        { Postfix dereference: (Expr)^ and optional (Expr)^.Field chaining }
        if Check(tkCaret) then
        begin
          Advance();
          DerefNode      := TDerefExpr.Create();
          DerefNode.Line := FCurrent.Line;
          DerefNode.Col  := FCurrent.Col;
          DerefNode.Expr := Inner;
          Result         := DerefNode;
          while Check(tkDot) and (PeekKind() = tkIdent) do
          begin
            Advance();
            FldNode           := TFieldAccessExpr.Create();
            FldNode.Line      := FCurrent.Line;
            FldNode.Col       := FCurrent.Col;
            FldNode.FieldName := FCurrent.Value;
            FldNode.Base      := Result;
            Advance();
            Result := FldNode;
          end;
        end
        else
          Result := Inner;
      end;
  else
    raise EParseError.Create(Format(
      'Expected expression at line %d col %d in %s',
      [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
  end;
  { Postfix chaining loop: Expr.Field, Expr.Method(...), Expr[i], Expr^, Expr(...) }
  while Check(tkDot) or Check(tkLBracket) or Check(tkCaret) or Check(tkLParen) do
  begin
    if Check(tkLParen) then
    begin
      { Indirect call through a non-identifier expression: Expr(args).
        Build TIndirectFuncCallExpr with Result as the callee. }
      IndCallNode            := TIndirectFuncCallExpr.Create();
      IndCallNode.Line       := FCurrent.Line;
      IndCallNode.Col        := FCurrent.Col;
      IndCallNode.CalleeExpr := Result;
      Result                 := nil;
      try
        Advance();  { consume '(' }
        if not Check(tkRParen) then
        begin
          IndCallNode.Args.Add(ParseExpr());
          while Check(tkComma) do
          begin
            Advance();
            IndCallNode.Args.Add(ParseExpr());
          end;
        end;
        Expect(tkRParen);
      except
        IndCallNode.Free();
        raise;
      end;
      Result := IndCallNode;
    end
    else if Check(tkDot) then
    begin
      Advance();  { consume '.' }
      if not Check(tkIdent) then
        raise EParseError.Create(Format(
          'Expected field or method name at line %d col %d in %s',
          [FCurrent.Line, FCurrent.Col, FLexer.Filename]));
      SecondName := FCurrent.Value;
      Advance();  { consume ident }
      if Check(tkLParen) then
      begin
        MCallNode            := TMethodCallExpr.Create();
        MCallNode.Line       := FCurrent.Line;
        MCallNode.Col        := FCurrent.Col;
        MCallNode.ObjectName := '';
        MCallNode.Name       := SecondName;
        MCallNode.ObjExpr    := Result;
        Advance();  { consume '(' }
        if not Check(tkRParen) then
        begin
          MCallNode.Args.Add(ParseExpr());
          while Check(tkComma) do
          begin
            Advance();
            MCallNode.Args.Add(ParseExpr());
          end;
        end;
        Expect(tkRParen);
        Result := MCallNode;
      end
      else
      begin
        FldNode           := TFieldAccessExpr.Create();
        FldNode.Line      := FCurrent.Line;
        FldNode.Col       := FCurrent.Col;
        FldNode.Base      := Result;
        FldNode.FieldName := SecondName;
        Result := FldNode;
        if Check(tkLBracket) then
        begin
          Advance();
          FldNode.PropIndexExpr := ParseExpr();
          Expect(tkRBracket);
        end;
      end;
    end
    else if Check(tkLBracket) then
    begin
      { Subscript read.  A comma-separated index list A[i, j] is desugared
        into chained single-index subscripts A[i][j] — each comma opens a
        further TStringSubscriptExpr whose base is the previous one. }
      Advance();  { consume '[' }
      try
        repeat
          SubNode := TStringSubscriptExpr.Create();
          SubNode.Line := FCurrent.Line;
          SubNode.Col  := FCurrent.Col;
          SubNode.StrExpr := Result;
          Result := SubNode;
          SubNode.IndexExpr := ParseExpr();
          if not Check(tkComma) then
            Break;
          Advance();  { consume ',' — next dimension }
        until False;
        Expect(tkRBracket);
      except
        Result.Free();
        Result := nil;
        raise;
      end;
    end
    else
    begin
      Advance();  { consume '^' }
      DerefNode      := TDerefExpr.Create();
      DerefNode.Line := FCurrent.Line;
      DerefNode.Col  := FCurrent.Col;
      DerefNode.Expr := Result;
      Result         := DerefNode;
    end;
  end;
end;

end.
