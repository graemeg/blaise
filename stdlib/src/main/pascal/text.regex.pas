{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - regular expressions.

  A .NET-shaped regular-expression API: an immutable TRegex object compiled
  once from a pattern, a TMatch value record carrying the result, and static
  convenience methods for one-off use.

  ENGINE — BACKTRACKING, AND WHY

  The matcher is a recursive backtracking engine over a compiled node tree,
  not a Thompson NFA simulation.  That is a deliberate trade.  A Thompson NFA
  gives guaranteed linear time in the subject length, but it cannot express
  backreferences, lookaround, atomic groups or possessive quantifiers, because
  those features need the match history that a set-of-states simulation throws
  away.  Backtracking keeps the history and therefore supports the full
  syntax below, at the cost of worst-case exponential time on adversarial
  pattern/subject pairs -- the classic '(a+)+b' blowup.

  One cheap pruning rule takes most of the sting out of that in practice: a
  quantifier only recurses into a further iteration when the previous
  iteration actually CONSUMED input.  A zero-width iteration cannot lead
  anywhere new, so continuing past it only re-explores the same partitions by
  another route.  Dropping those branches collapses the redundant
  re-partitioning that makes '(a+)+b', '(a*)*b' and '(a|a)+b' exponential in
  a naive backtracker -- they terminate here in linear-ish time -- while
  changing no match RESULT, because a zero-width iteration by definition adds
  nothing to what was matched.  The pruning is not a general guarantee, which
  is exactly why the step budget below is not optional.

  The matcher is written in continuation-passing style: MatchNode takes "what
  to do after this node succeeds" as a linked chain of TContinuation frames.
  A linked chain rather than a single (node-list, index) pair is essential --
  groups nest, so on entering a group body the matcher must remember both the
  rest of that body AND the rest of every enclosing sequence.  Passing the
  continuation down into each alternative and each quantifier iteration is
  what makes give-back work: when the tail of the pattern fails, control
  returns into the quantifier, which offers a shorter extent and re-runs the
  tail.

  STEP BUDGET

  Because exponential blowup is a real denial-of-service vector whenever a
  pattern or a subject comes from outside the program (an HTTP request handler
  is the motivating case), the matcher is not permitted to run unbounded.
  Every backtracking step increments a counter; when the counter passes
  StepLimit the match aborts with ERegexComplexity instead of hanging.

  The default limit is DEFAULT_STEP_LIMIT = 10,000,000 steps.  The number is
  chosen to be far above anything a well-behaved pattern needs -- ordinary
  matching costs on the order of (subject length x pattern size) steps, so a
  10 MB budget covers e.g. a 100 KB subject against a 100-node pattern with
  room to spare -- while still terminating a catastrophic pattern in well
  under a second.  Callers that knowingly run expensive patterns over large
  inputs can raise StepLimit; callers handling hostile input should lower it.
  The budget is a property of the TRegex, but the counter itself is a local
  in the match call, so raising the limit never makes matching stateful.

  A blown budget raises rather than returning "no match" on purpose: it is not
  a statement about the data (the subject may well match) but a statement that
  the answer could not be computed within the allowance, and silently
  reporting "no match" would turn a resource failure into a wrong answer.

  THREAD / FIBER SAFETY

  TRegex is IMMUTABLE once constructed: the compiled program is built in the
  constructor and never mutated afterwards, and NO match state whatsoever is
  stored on the object.  Capture registers, the step counter and the input
  cursor all live in locals of the matching call or in the caller's TMatch.
  A single TRegex can therefore be shared by any number of concurrent fibers
  or threads without locking.  This is an invariant worth preserving: adding
  a "last match" or scratch field to TRegex would silently break every
  concurrent user.  (StepLimit is settable and so is technically mutable, but
  it is read once at the start of a match; set it before sharing.)

  ERROR CONVENTION

  A malformed pattern is a programmer error -- the developer wrote it -- so it
  raises ERegexSyntaxError carrying a 0-based Position into the pattern.  A
  subject that simply does not match is data, not an error, so it is reported
  as Success = False with Index = -1.

  UNICODE POSITION (v1)

  Matching is BYTE-oriented and every Index/Length in a TMatch or TGroup is a
  BYTE offset into the subject, consistent with Length, Pos and Copy.  Mixing
  codepoint offsets into this API would be a trap: the offsets would not be
  usable with any other string routine in the stdlib.

  Consequences, stated plainly:

    * Multi-byte UTF-8 literals in a pattern work for free -- they match as
      byte runs, and a captured Value is byte-identical to the source text.
    * '.' is UTF-8 AWARE: it consumes one whole codepoint (1-4 bytes), so a
      match can never split a UTF-8 sequence and Value is always well-formed.
    * \d \w \s (and their negations) are ASCII-ONLY.  \w does not match an
      accented letter.
    * roIgnoreCase is ASCII-ONLY.  'E' folds to 'e'; U+00C9 does not fold to
      U+00E9.  Folding is applied when the pattern is compiled, so it costs
      nothing at match time.
    * A character-class RANGE whose endpoints are not both ASCII is rejected
      with ERegexSyntaxError, rather than silently matching an arbitrary
      byte range that almost certainly is not what the author meant.  A
      non-ASCII byte as a plain class member is still allowed.

  Full Unicode property classes and Unicode case folding are deliberately out
  of scope for v1.

  COMPILER WORKAROUNDS IN THIS UNIT

  This unit was originally written against a compiler that could not store a
  jumbo (>64-member) set in a record or class field, pass one as an out/var
  parameter, or use one across several other shapes.  Character classes were
  therefore held as an explicit 32-byte bitmap with hand-written
  membership/copy helpers.  Those bugs were fixed on 2026-07-20 and the
  workarounds have been removed: TRegexNode.Cls and TEscape.Cls are now the
  'set of Byte' (TCharClass) they always wanted to be, and membership is the
  'in' operator.

  Three workarounds remain, each still load-bearing:

    * BUG-20260719-native-indexed-prop-record -- an indexed property returning
      a record miscompiles on the native backend, so 'TList<TMatch>' must be
      read with L.Get(I) rather than L[I].  This affects CALLERS of Matches,
      not just this unit.
    * BUG-20260720-native-jumbo-set-self-assign -- 'X := F(X)' on a set
      miscompiles on the native backend (the destination aliases the argument
      the callee is still reading).  ParseEscape and ParseClass write every
      complement/fold into a distinct Tmp local.  Note this one is SILENT and
      native-only: it yields a plausible but wrong set, so it is invisible
      unless QBE and native output are compared.
    * BUG-20260720-set-literal-overload-cached-bif -- a bare set literal fails
      OVERLOAD resolution against a set parameter imported from a cached
      .bif, so callers in other units must bind options to a variable.  See
      the note on the constructor.

  ParseEscape still returns a TEscape record by value and FoldClass is still
  a function over a const set.  Both were adopted to dodge an out/var
  parameter bug that is now fixed, but both read better than the
  out-parameter forms they replaced, so they stay on their own merits.

  SUPPORTED SYNTAX

    literals, and any byte after a backslash
    .                  any codepoint (not newline unless roDotMatchesNewLine)
    [abc] [a-z] [^a-z] character class, ranges, negation, shorthands inside
    \d \D \w \W \s \S  ASCII digit / word / whitespace classes
    \t \n \r \f \v \0  control-character escapes
    ^ $                start / end anchors (per line under roMultiLine)
    \b \B              ASCII word-boundary assertions
    * + ?              greedy quantifiers
    *? +? ??           lazy quantifiers
    *+ ++ ?+           possessive quantifiers
    braces n / n,m     bounded repetition, e.g. a<3> a<2,> a<2,4> written with
                       curly braces; a trailing ? makes it lazy and a
                       trailing + makes it possessive.  (Curly braces cannot
                       be written literally inside this comment: a closing
                       brace would terminate it.)
    |                  alternation, leftmost-FIRST (Perl/.NET, not POSIX)
    ( )                capturing group
    (?: )              non-capturing group
    (?> )              atomic group (no give-back once matched)
    (?= ) (?! )        positive / negative lookahead
    (?<= ) (?<! )      positive / negative lookbehind
    \1 .. \9           backreference to a capturing group

  Group numbering is by the order of opening parentheses, starting at 1;
  group 0 is the whole match. }

unit Text.Regex;

interface

uses
  SysUtils, StrUtils, Generics.Collections;

const
  { See the STEP BUDGET discussion in the unit header for why this value. }
  DEFAULT_STEP_LIMIT = 10000000;
  { Upper bound on a braced repetition count.  Bounded repetition is compiled
    by expansion, so an unbounded m would let a short pattern produce an
    enormous program; a pattern needing more than this wants '+' or '*'. }
  MAX_REPEAT_BOUND = 1000;
  { Highest backreference number the syntax accepts (\1 .. \9). }
  MAX_BACKREF = 9;

type
  TRegexOption = (roIgnoreCase, roMultiLine, roDotMatchesNewLine);
  TRegexOptions = set of TRegexOption;

  { Raised for a malformed pattern.  Position is a 0-based byte offset into
    the pattern text, pointing at (or just past) the offending construct. }
  ERegexSyntaxError = class(Exception)
  private
    FPosition: Int;
  public
    constructor Create(const AMessage: string; APosition: Int);
    property Position: Int read FPosition;
  end;

  { Raised when a match exceeds the TRegex's StepLimit.  See the unit header:
    this reports "could not be computed within the allowance", NOT "does not
    match". }
  ERegexComplexity = class(Exception)
  end;

  { One capture group's result.  Index is a 0-based BYTE offset, or -1 when
    the group did not participate in the match. }
  TGroup = record
    Index: Int;
    Length: Int;
    Value: string;
  end;

  { The result of a match attempt.  A plain value record: copying it copies
    the result, and it holds no reference back to the TRegex that produced
    it.  Group 0 is the whole match. }
  TMatch = record
  private
    FGroups: array of TGroup;
  public
    Success: Boolean;
    Index: Int;
    Length: Int;
    Value: string;
    { Number of groups including group 0, so a pattern with two capturing
      groups reports 3. }
    function GroupCount: Int;
    { Group AIndex, or a group with Index = -1 when out of range or when the
      group did not participate.  Never raises. }
    function Group(AIndex: Int): TGroup;
    { Shorthand for Group(AIndex).Value; '' when absent. }
    function GroupValue(AIndex: Int): string;
  end;

  { Compiled-node opcodes.  The compiled form is a tree of TRegexNode rather
    than a flat instruction array: the backtracking matcher recurses over the
    tree with a continuation index, which keeps quantifier give-back and the
    zero-width assertions straightforward to express. }
  { A character class: one bit per byte value, giving O(1) membership via the
    'in' operator.  There is no Char type in Blaise, so bytes are the
    character currency throughout this unit. }
  TCharClass = set of Byte;

  { Result of decoding one backslash escape.  Returned BY VALUE rather than
    through out-parameters — the escape is a small value with no identity,
    so a return reads more directly than an out-parameter pair. }
  TEscape = record
    IsClass: Boolean;      { True when Cls carries a shorthand class }
    Cls: TCharClass;
    Value: Int;        { literal byte, or -(group number) for a backref }
  end;

  TRegexOp = (
    opChar,          { single literal byte }
    opAny,           { '.' — one codepoint }
    opClass,         { character class }
    opConcat,        { sequence of children }
    opAlt,           { alternation over children }
    opRepeat,        { quantified child }
    opGroup,         { capturing / non-capturing / atomic group }
    opBackref,       { \1..\9 }
    opBOL,           { ^ }
    opEOL,           { $ }
    opWordB,         { \b }
    opNotWordB,      { \B }
    opLookahead,     { (?=) (?!) }
    opLookbehind,    { (?<=) (?<!) }
    opCapStart,      { records a capturing group's start (zero-width) }
    opCapEnd,        { records a capturing group's end (zero-width) }
    opEmpty          { matches the empty string }
  );

  TRegexNode = class
  public
    Op: TRegexOp;
    Ch: Byte;                { opChar }
    Cls: TCharClass;         { opClass }
    Negate: Boolean;         { opClass negation; lookaround negation }
    Kids: TList<TRegexNode>; { opConcat / opAlt children; [0] for wrappers }
    RepMin: Int;         { opRepeat lower bound }
    RepMax: Int;         { opRepeat upper bound; -1 = unbounded }
    Lazy: Boolean;           { opRepeat }
    Possessive: Boolean;     { opRepeat; also set for atomic groups }
    GroupNum: Int;       { opGroup capture number, 0 = non-capturing }
    Atomic: Boolean;         { opGroup }
    RefNum: Int;         { opBackref }
    constructor Create(AOp: TRegexOp);
    destructor Destroy; override;
    procedure AddKid(ANode: TRegexNode);
  end;

  TRegex = class
  private
    FPattern: string;
    FOptions: TRegexOptions;
    FRoot: TRegexNode;
    FGroupCount: Int;
    FStepLimit: Int;
    { --- pattern parsing (constructor only; never touched afterwards) --- }
    FPat: string;
    FPos: Int;
    FLen: Int;
    procedure Fail(const AMsg: string);
    procedure FailAt(const AMsg: string; APos: Int);
    function PeekByte: Int;
    function ParseAlternation: TRegexNode;
    function ParseConcat: TRegexNode;
    function ParseQuantified: TRegexNode;
    function ParseAtom: TRegexNode;
    function ParseGroup: TRegexNode;
    function ParseClass: TRegexNode;
    function ParseEscape(AInClass: Boolean): TEscape;
    procedure ApplyQuantifier(var ANode: TRegexNode);
    function ParseBound(out AMin, AMax: Int): Boolean;
    function FoldClass(const ACls: TCharClass): TCharClass;
    function GetStepLimit: Int;
    procedure SetStepLimit(AValue: Int);
  public
    { Compile APattern.  Raises ERegexSyntaxError if it is malformed.

      NOTE for callers in OTHER units: pass the options as a variable or via
      the NoOptions helper, not as a bare set literal.  A set literal fails
      OVERLOAD resolution against a set parameter imported from a cached unit
      interface (BUG-20260720-set-literal-overload-cached-bif), so
      'TRegex.Create(P, [roIgnoreCase])' compiles from source but fails on an
      incremental rebuild.  'Opts := [roIgnoreCase]; TRegex.Create(P, Opts)'
      is safe. }
    constructor Create(const APattern: string); overload;
    constructor Create(const APattern: string; AOptions: TRegexOptions); overload;
    destructor Destroy; override;

    { True when the pattern matches anywhere in AInput. }
    function IsMatch(const AInput: string): Boolean; overload;
    { True when the pattern matches at or after byte offset AStartAt. }
    function IsMatch(const AInput: string; AStartAt: Int): Boolean; overload;
    { Leftmost match, or Success = False / Index = -1 when there is none. }
    function Match(const AInput: string): TMatch; overload;
    function Match(const AInput: string; AStartAt: Int): TMatch; overload;
    { All non-overlapping matches, left to right.  Never nil; the caller owns
      the returned list.  An empty match still advances one codepoint, so
      this always terminates. }
    function Matches(const AInput: string): TList<TMatch>;
    { Replace every match with AReplacement, in which '$1'..'$9' expand to the
      corresponding group, '$&' to the whole match, and '$$' to a literal
      '$'.  Any other '$x' is left verbatim. }
    function Replace(const AInput, AReplacement: string): string; overload;
    { Split AInput around every match.  The caller owns the returned list. }
    function Split(const AInput: string): TList<String>; overload;

    { --- static convenience: compile, use once, discard --- }
    static function IsMatch(const AInput, APattern: string): Boolean; overload;
    static function IsMatch(const AInput, APattern: string;
                            AOptions: TRegexOptions): Boolean; overload;
    static function Match(const AInput, APattern: string): TMatch; overload;
    static function Match(const AInput, APattern: string;
                          AOptions: TRegexOptions): TMatch; overload;
    static function Replace(const AInput, APattern,
                            AReplacement: string): string; overload;
    static function Split(const AInput, APattern: string): TList<String>; overload;

    property Pattern: string read FPattern;
    property Options: TRegexOptions read FOptions;
    { Number of CAPTURING groups, not counting group 0. }
    property GroupCount: Int read FGroupCount;
    { Backtracking-step allowance for a single match call.  See the unit
      header.  Read once per match, so changing it mid-flight is safe. }
    property StepLimit: Int read GetStepLimit write SetStepLimit;
  end;

{ The empty option set, spelled out so call sites can read
  TRegex.Create(P, NoOptions) rather than the bare TRegex.Create(P, []).
  A bare '[]' is also fine wherever the parameter type is known. }
function NoOptions: TRegexOptions;

implementation

function NoOptions: TRegexOptions;
begin
  Result := [];
end;

const
  { ASCII byte constants.  Byte('x') on a char LITERAL does not yield the
    character code in this dialect (a literal is a UTF-8 string and the cast
    takes the pointer), so byte comparisons must use numeric constants.  A
    byte read FROM a string via S[i] does give the correct code. }
  CH_NUL      = 0;
  CH_TAB      = 9;
  CH_LF       = 10;
  CH_VT       = 11;
  CH_FF       = 12;
  CH_CR       = 13;
  CH_SPACE    = 32;
  CH_BANG     = 33;   { ! }
  CH_DOLLAR   = 36;   { $ }
  CH_AMP      = 38;   { & }
  CH_LPAREN   = 40;   { ( }
  CH_RPAREN   = 41;   { ) }
  CH_STAR     = 42;   { * }
  CH_PLUS     = 43;   { + }
  CH_COMMA    = 44;   { , }
  CH_MINUS    = 45;   { - }
  CH_DOT      = 46;   { . }
  CH_0        = 48;
  CH_9        = 57;
  CH_LT       = 60;   { < }
  CH_EQUALS   = 61;   { = }
  CH_GT       = 62;   { > }
  CH_QUESTION = 63;   { ? }
  CH_UC_A     = 65;
  CH_UC_B     = 66;
  CH_UC_D     = 68;
  CH_UC_S     = 83;
  CH_UC_W     = 87;
  CH_UC_Z     = 90;
  CH_LBRACKET = 91;   { [ }
  CH_BACKSL   = 92;   { \ }
  CH_RBRACKET = 93;   { ] }
  CH_CARET    = 94;   { ^ }
  CH_UNDER    = 95;   { _ }
  CH_LC_A     = 97;
  CH_LC_B     = 98;
  CH_LC_D     = 100;
  CH_LC_F     = 102;
  CH_LC_N     = 110;
  CH_LC_R     = 114;
  CH_LC_S     = 115;
  CH_LC_T     = 116;
  CH_LC_V     = 118;
  CH_LC_W     = 119;
  CH_LC_Z     = 122;
  CH_LBRACE   = 123;  { openbrace }
  CH_PIPE     = 124;  { | }
  CH_RBRACE   = 125;  { closebrace }
  ASCII_MAX   = 127;

  { Repeat bound sentinel for '*' and '+'. }
  UNBOUNDED = -1;

{ The empty byte class.  A function rather than a constant: it reads at the
  call sites as the counterpart of FullClass, and a bare '[]' literal needs
  an inferable element type from context, which not every position supplies. }
function EmptyClass: TCharClass;
begin
  Result := [];
end;

{ Complement of ASet over the full byte range.  Built by iteration rather
  than as 'FullClass() - ASet' so no full 256-member intermediate is
  materialised. }
function ComplementClass(const ASet: TCharClass): TCharClass;
var
  I: Int;
begin
  Result := [];
  for I := 0 to 255 do
    if not (I in ASet) then
      Result := Result + [I];
end;

{ ------------------------------------------------------------------ }
{ Byte predicates — all ASCII-only by design (see unit header).       }
{ ------------------------------------------------------------------ }

function IsDigitByte(B: Int): Boolean;
begin
  Result := (B >= CH_0) and (B <= CH_9);
end;

function IsWordByte(B: Int): Boolean;
begin
  Result := ((B >= CH_LC_A) and (B <= CH_LC_Z))
         or ((B >= CH_UC_A) and (B <= CH_UC_Z))
         or ((B >= CH_0) and (B <= CH_9))
         or (B = CH_UNDER);
end;

function IsSpaceByte(B: Int): Boolean;
begin
  Result := (B = CH_SPACE) or (B = CH_TAB) or (B = CH_LF)
         or (B = CH_CR) or (B = CH_FF) or (B = CH_VT);
end;

{ ASCII-only lower/upper folding helpers. }
function LowerByte(B: Int): Int;
begin
  if (B >= CH_UC_A) and (B <= CH_UC_Z) then
    Result := B + 32
  else
    Result := B;
end;

function UpperByte(B: Int): Int;
begin
  if (B >= CH_LC_A) and (B <= CH_LC_Z) then
    Result := B - 32
  else
    Result := B;
end;

{ Number of bytes in the UTF-8 sequence whose leading byte is B.  A stray
  continuation byte or an invalid lead is treated as a single byte, so the
  matcher always makes progress on malformed input rather than looping. }
function Utf8SeqLen(B: Int): Int;
begin
  if B < $80 then
    Result := 1
  else if (B and $E0) = $C0 then
    Result := 2
  else if (B and $F0) = $E0 then
    Result := 3
  else if (B and $F8) = $F0 then
    Result := 4
  else
    Result := 1;
end;

{ ------------------------------------------------------------------ }
{ ERegexSyntaxError                                                   }
{ ------------------------------------------------------------------ }

constructor ERegexSyntaxError.Create(const AMessage: string; APosition: Int);
begin
  inherited Create(AMessage + ' at pattern offset ' + IntToStr(APosition));
  FPosition := APosition;
end;

{ ------------------------------------------------------------------ }
{ TMatch                                                              }
{ ------------------------------------------------------------------ }

function TMatch.GroupCount: Int;
begin
  Result := System.Length(FGroups);
end;

function TMatch.Group(AIndex: Int): TGroup;
begin
  if (AIndex < 0) or (AIndex >= System.Length(FGroups)) then
  begin
    Result.Index := -1;
    Result.Length := 0;
    Result.Value := '';
  end
  else
    Result := FGroups[AIndex];
end;

function TMatch.GroupValue(AIndex: Int): string;
begin
  Result := Self.Group(AIndex).Value;
end;

{ ------------------------------------------------------------------ }
{ TRegexNode                                                          }
{ ------------------------------------------------------------------ }

constructor TRegexNode.Create(AOp: TRegexOp);
begin
  Op := AOp;
  Ch := 0;
  Cls := [];
  Negate := False;
  Kids := TList<TRegexNode>.Create();
  RepMin := 0;
  RepMax := 0;
  Lazy := False;
  Possessive := False;
  GroupNum := 0;
  Atomic := False;
  RefNum := 0;
end;

destructor TRegexNode.Destroy;
var
  I: Int;
begin
  for I := 0 to Kids.Count - 1 do
    Kids.Get(I).Free();
  Kids.Free();
  inherited Destroy();
end;

procedure TRegexNode.AddKid(ANode: TRegexNode);
begin
  Kids.Add(ANode);
end;

{ ------------------------------------------------------------------ }
{ TRegex — construction and pattern parsing                           }
{ ------------------------------------------------------------------ }

constructor TRegex.Create(const APattern: string);
var
  Opts: TRegexOptions;
begin
  Opts := [];
  Self.Create(APattern, Opts);
end;

constructor TRegex.Create(const APattern: string; AOptions: TRegexOptions);
begin
  FPattern := APattern;
  FOptions := AOptions;
  FStepLimit := DEFAULT_STEP_LIMIT;
  FGroupCount := 0;
  FRoot := nil;

  FPat := APattern;
  FPos := 0;
  FLen := Length(APattern);

  FRoot := Self.ParseAlternation();
  { Anything left over means an unbalanced ')' — ParseAlternation stops at
    one but only ParseGroup is entitled to consume it. }
  if FPos < FLen then
    Self.Fail('Unbalanced '')''');
end;

destructor TRegex.Destroy;
begin
  if FRoot <> nil then
    FRoot.Free();
  inherited Destroy();
end;

procedure TRegex.Fail(const AMsg: string);
begin
  Self.FailAt(AMsg, FPos);
end;

procedure TRegex.FailAt(const AMsg: string; APos: Int);
begin
  raise ERegexSyntaxError.Create(AMsg, APos);
end;

function TRegex.PeekByte: Int;
begin
  if FPos < FLen then
    Result := Byte(FPat[FPos])
  else
    Result := -1;
end;

function TRegex.GetStepLimit: Int;
begin
  Result := FStepLimit;
end;

procedure TRegex.SetStepLimit(AValue: Int);
begin
  if AValue < 1 then
    FStepLimit := 1
  else
    FStepLimit := AValue;
end;

{ alternation := concat, then zero or more of: '|' concat }
function TRegex.ParseAlternation: TRegexNode;
var
  First: TRegexNode;
  Alt: TRegexNode;
begin
  First := Self.ParseConcat();
  if Self.PeekByte() <> CH_PIPE then
  begin
    Result := First;
    Exit;
  end;

  Alt := TRegexNode.Create(opAlt);
  Alt.AddKid(First);
  while Self.PeekByte() = CH_PIPE do
  begin
    FPos := FPos + 1;
    Alt.AddKid(Self.ParseConcat());
  end;
  Result := Alt;
end;

{ concat := zero or more quantified atoms; stops at '|', ')' or end }
function TRegex.ParseConcat: TRegexNode;
var
  Seq: TRegexNode;
  B: Int;
begin
  Seq := TRegexNode.Create(opConcat);
  while True do
  begin
    B := Self.PeekByte();
    if (B < 0) or (B = CH_PIPE) or (B = CH_RPAREN) then
      Break;
    Seq.AddKid(Self.ParseQuantified());
  end;
  { An empty branch (as in 'a(b|)c') matches the empty string. }
  if Seq.Kids.Count = 0 then
    Seq.AddKid(TRegexNode.Create(opEmpty));
  Result := Seq;
end;

{ quantified := atom, optionally followed by a quantifier }
function TRegex.ParseQuantified: TRegexNode;
var
  Node: TRegexNode;
begin
  Node := Self.ParseAtom();
  Self.ApplyQuantifier(Node);
  Result := Node;
end;

{ Read a braced repetition bound starting at the opening brace.  Returns False (leaving FPos
  untouched) when what follows is not a well-formed bound, so a stray '{' can
  fall through and be treated as a literal — Perl and .NET both do this. }
function TRegex.ParseBound(out AMin, AMax: Int): Boolean;
var
  Save: Int;
  B: Int;
  HasMin: Boolean;
  HasMax: Boolean;
begin
  Save := FPos;
  AMin := 0;
  AMax := UNBOUNDED;
  Result := False;

  if Self.PeekByte() <> CH_LBRACE then
    Exit;
  FPos := FPos + 1;

  HasMin := False;
  while IsDigitByte(Self.PeekByte()) do
  begin
    AMin := AMin * 10 + (Self.PeekByte() - CH_0);
    HasMin := True;
    FPos := FPos + 1;
    { Stop runaway digit runs from overflowing before the bound check. }
    if AMin > MAX_REPEAT_BOUND * 100 then
      Break;
  end;

  if not HasMin then
  begin
    FPos := Save;
    Exit;
  end;

  B := Self.PeekByte();
  if B = CH_RBRACE then
  begin
    { exactly n }
    FPos := FPos + 1;
    AMax := AMin;
    Result := True;
  end
  else if B = CH_COMMA then
  begin
    FPos := FPos + 1;
    HasMax := False;
    AMax := 0;
    while IsDigitByte(Self.PeekByte()) do
    begin
      AMax := AMax * 10 + (Self.PeekByte() - CH_0);
      HasMax := True;
      FPos := FPos + 1;
      if AMax > MAX_REPEAT_BOUND * 100 then
        Break;
    end;
    if Self.PeekByte() <> CH_RBRACE then
    begin
      FPos := Save;
      Exit;
    end;
    FPos := FPos + 1;
    if not HasMax then
      AMax := UNBOUNDED;
    Result := True;
  end
  else
  begin
    FPos := Save;
    Exit;
  end;

  { Bounds are validated only once the braces really were a bound, so an
    ordinary literal '{' never trips these errors. }
  if AMin > MAX_REPEAT_BOUND then
    Self.FailAt('Repetition count exceeds ' + IntToStr(MAX_REPEAT_BOUND), Save);
  if (AMax <> UNBOUNDED) and (AMax > MAX_REPEAT_BOUND) then
    Self.FailAt('Repetition count exceeds ' + IntToStr(MAX_REPEAT_BOUND), Save);
  if (AMax <> UNBOUNDED) and (AMax < AMin) then
    Self.FailAt('Repetition minimum exceeds maximum', Save);
end;

{ Wrap ANode in an opRepeat when a quantifier follows it. }
procedure TRegex.ApplyQuantifier(var ANode: TRegexNode);
var
  B: Int;
  Rep: TRegexNode;
  Lo, Hi: Int;
  QPos: Int;
begin
  B := Self.PeekByte();
  QPos := FPos;

  if B = CH_STAR then
  begin
    FPos := FPos + 1;
    Lo := 0;
    Hi := UNBOUNDED;
  end
  else if B = CH_PLUS then
  begin
    FPos := FPos + 1;
    Lo := 1;
    Hi := UNBOUNDED;
  end
  else if B = CH_QUESTION then
  begin
    FPos := FPos + 1;
    Lo := 0;
    Hi := 1;
  end
  else if B = CH_LBRACE then
  begin
    if not Self.ParseBound(Lo, Hi) then
      Exit;      { not a bound after all — '{' was a literal }
  end
  else
    Exit;        { no quantifier }

  { A quantifier must follow something quantifiable.  A zero-width assertion
    or an empty branch is not, and '**' is not either. }
  if (ANode.Op = opEmpty) or (ANode.Op = opBOL) or (ANode.Op = opEOL)
     or (ANode.Op = opWordB) or (ANode.Op = opNotWordB) then
    Self.FailAt('Nothing to repeat', QPos);

  Rep := TRegexNode.Create(opRepeat);
  Rep.RepMin := Lo;
  Rep.RepMax := Hi;
  Rep.AddKid(ANode);

  { A trailing '?' makes it lazy, a trailing '+' makes it possessive. }
  B := Self.PeekByte();
  if B = CH_QUESTION then
  begin
    Rep.Lazy := True;
    FPos := FPos + 1;
  end
  else if B = CH_PLUS then
  begin
    Rep.Possessive := True;
    FPos := FPos + 1;
  end;

  { A second quantifier on the same atom ('a**') is meaningless. }
  B := Self.PeekByte();
  if (B = CH_STAR) or (B = CH_PLUS) or (B = CH_QUESTION) then
    Self.Fail('Nested quantifier');

  ANode := Rep;
end;

{ Decode one escape sequence.  FPos is on the backslash on entry.  Returns
  either a literal byte (IsClass = False, byte in Value) or a shorthand
  character class (IsClass = True, class in Cls).  A backreference is
  signalled by a NEGATIVE Value of -(group number), and is only valid outside
  a character class. }
function TRegex.ParseEscape(AInClass: Boolean): TEscape;
var
  B: Int;
  I: Int;
  EscPos: Int;
  Acc: TCharClass;
  { Distinct destination for every complement/fold: 'X := F(X)' on a jumbo set
    miscompiles on the native backend (BUG-20260720-native-jumbo-set-self-assign). }
  Tmp: TCharClass;
begin
  EscPos := FPos;
  FPos := FPos + 1;              { consume '\' }
  Result.IsClass := False;
  Acc := EmptyClass();
  Result.Cls := Acc;
  Result.Value := 0;

  B := Self.PeekByte();
  if B < 0 then
    Self.FailAt('Trailing backslash', EscPos);
  FPos := FPos + 1;

  { Shorthand classes.  Accumulate in the LOCAL Acc and store into the result
    record once; jumbo-set operations are only reliable on locals. }
  if (B = CH_LC_D) or (B = CH_UC_D) then
  begin
    for I := CH_0 to CH_9 do
      Acc := Acc + [I];
    if B = CH_UC_D then
    begin
      Tmp := ComplementClass(Acc);
      Acc := Tmp;
    end;
    Result.IsClass := True;
    Result.Cls := Acc;
    Exit;
  end;
  if (B = CH_LC_W) or (B = CH_UC_W) then
  begin
    for I := 0 to ASCII_MAX do
      if IsWordByte(I) then
        Acc := Acc + [I];
    if B = CH_UC_W then
    begin
      Tmp := ComplementClass(Acc);
      Acc := Tmp;
    end;
    Result.IsClass := True;
    Result.Cls := Acc;
    Exit;
  end;
  if (B = CH_LC_S) or (B = CH_UC_S) then
  begin
    for I := 0 to ASCII_MAX do
      if IsSpaceByte(I) then
        Acc := Acc + [I];
    if B = CH_UC_S then
    begin
      Tmp := ComplementClass(Acc);
      Acc := Tmp;
    end;
    Result.IsClass := True;
    Result.Cls := Acc;
    Exit;
  end;

  { Control-character escapes. }
  if B = CH_LC_T then begin Result.Value := CH_TAB;   Exit; end;
  if B = CH_LC_N then begin Result.Value := CH_LF;    Exit; end;
  if B = CH_LC_R then begin Result.Value := CH_CR;    Exit; end;
  if B = CH_LC_F then begin Result.Value := CH_FF;    Exit; end;
  if B = CH_LC_V then begin Result.Value := CH_VT;    Exit; end;

  { \0 is NUL; \1..\9 are backreferences outside a class.  Inside a class a
    digit escape is just that digit, since a backreference has no meaning
    there. }
  if IsDigitByte(B) then
  begin
    if B = CH_0 then
    begin
      Result.Value := CH_NUL;
      Exit;
    end;
    if AInClass then
    begin
      Result.Value := B;
      Exit;
    end;
    Result.Value := -(B - CH_0);   { negative marks a backreference }
    Exit;
  end;

  { \b inside a class is not a word boundary (assertions cannot appear in a
    class); treat it as backspace, matching Perl.  Outside a class it is
    handled by ParseAtom before ParseEscape is ever called. }
  if AInClass and (B = CH_LC_B) then
  begin
    Result.Value := 8;
    Exit;
  end;

  { Any other byte after a backslash is that literal byte.  This is what
    makes '\.', '\*', '\\', '\[' and friends work without a metacharacter
    table. }
  Result.Value := B;
end;

{ class := '[', an optional leading '^', zero or more members, ']' }
function TRegex.ParseClass: TRegexNode;
var
  Node: TRegexNode;
  StartPos: Int;
  B: Int;
  Lo, Hi: Int;
  Esc: TEscape;
  MemberPos: Int;
  First: Boolean;
  Negated: Boolean;
  Acc: TCharClass;
  { Distinct destination for the fold and the complement — see BUG-20260720-native-jumbo-set-self-assign. }
  Tmp: TCharClass;
begin
  StartPos := FPos;
  FPos := FPos + 1;                { consume '[' }

  { The class is accumulated in a LOCAL and stored into the node once at the
    end — one write to the node instead of one per class member. }
  Node := TRegexNode.Create(opClass);
  Acc := EmptyClass();
  Negated := False;
  if Self.PeekByte() = CH_CARET then
  begin
    Negated := True;
    FPos := FPos + 1;
  end;

  First := True;
  while True do
  begin
    B := Self.PeekByte();
    if B < 0 then
      Self.FailAt('Unterminated character class', StartPos);
    { A ']' as the very first member is a literal ']', per POSIX/Perl. }
    if (B = CH_RBRACKET) and not First then
    begin
      FPos := FPos + 1;
      Break;
    end;
    First := False;

    MemberPos := FPos;
    if B = CH_BACKSL then
    begin
      Esc := Self.ParseEscape(True);
      if Esc.IsClass then
      begin
        { A shorthand class is a whole set; it cannot be a range endpoint. }
        Tmp := Esc.Cls;
        Acc := Acc + Tmp;
        Continue;
      end;
      Lo := Esc.Value;
    end
    else
    begin
      Lo := B;
      FPos := FPos + 1;
    end;

    { A '-' that is neither first nor last introduces a range. }
    if (Self.PeekByte() = CH_MINUS) and (FPos + 1 < FLen)
       and (Byte(FPat[FPos + 1]) <> CH_RBRACKET) then
    begin
      FPos := FPos + 1;            { consume '-' }
      B := Self.PeekByte();
      if B < 0 then
        Self.FailAt('Unterminated character class', StartPos);
      if B = CH_BACKSL then
      begin
        Esc := Self.ParseEscape(True);
        if Esc.IsClass then
          Self.FailAt('Shorthand class cannot be a range endpoint', MemberPos);
        Hi := Esc.Value;
      end
      else
      begin
        Hi := B;
        FPos := FPos + 1;
      end;

      { Byte-oriented matching makes a non-ASCII range meaningless — see the
        UNICODE POSITION note in the unit header.  Reject rather than
        silently matching an arbitrary byte range. }
      if (Lo > ASCII_MAX) or (Hi > ASCII_MAX) then
        Self.FailAt('Character-class range endpoints must be ASCII', MemberPos);
      if Hi < Lo then
        Self.FailAt('Character-class range is reversed', MemberPos);

      for B := Lo to Hi do
        Acc := Acc + [B];
    end
    else
      Acc := Acc + [Lo];
  end;

  { Fold at COMPILE time so matching costs nothing extra. }
  if roIgnoreCase in FOptions then
  begin
    Tmp := Self.FoldClass(Acc);
    Acc := Tmp;
  end;

  { Negation is applied by expanding the complement here rather than testing
    Negate at match time, so a class test is always a single set membership.
    Negation happens AFTER folding, which is the intended order: [^a-z] with
    roIgnoreCase excludes both cases. }
  if Negated then
  begin
    Tmp := ComplementClass(Acc);
    Acc := Tmp;
  end;

  Node.Negate := False;
  Node.Cls := Acc;
  Result := Node;
end;

{ Add the opposite ASCII case of every ASCII letter already in the set. }
{ Returns ACls with the opposite ASCII case of every ASCII letter added.
  A function over a const set rather than a 'var' procedure — the caller
  always wants a new class, not an in-place edit. }
function TRegex.FoldClass(const ACls: TCharClass): TCharClass;
var
  I: Int;
begin
  Result := ACls;
  for I := CH_UC_A to CH_UC_Z do
    if I in ACls then
      Result := Result + [LowerByte(I)];
  for I := CH_LC_A to CH_LC_Z do
    if I in ACls then
      Result := Result + [UpperByte(I)];
end;

{ group := '(', an optional '?'-prefixed construct, alternation, ')' }
function TRegex.ParseGroup: TRegexNode;
var
  StartPos: Int;
  Node: TRegexNode;
  Body: TRegexNode;
  B: Int;
  Capturing: Boolean;
  Atomic: Boolean;
  Marker: TRegexNode;
  Look: Int;      { 0 none, 1 ahead, 2 behind }
  Neg: Boolean;
begin
  StartPos := FPos;
  FPos := FPos + 1;               { consume '(' }

  Capturing := True;
  Atomic := False;
  Look := 0;
  Neg := False;

  if Self.PeekByte() = CH_QUESTION then
  begin
    FPos := FPos + 1;
    B := Self.PeekByte();
    if B < 0 then
      Self.FailAt('Unterminated group', StartPos);

    if B = 58 then                { ':' — non-capturing }
    begin
      FPos := FPos + 1;
      Capturing := False;
    end
    else if B = CH_GT then        { '>' — atomic }
    begin
      FPos := FPos + 1;
      Capturing := False;
      Atomic := True;
    end
    else if B = CH_EQUALS then    { '=' — positive lookahead }
    begin
      FPos := FPos + 1;
      Capturing := False;
      Look := 1;
    end
    else if B = CH_BANG then      { '!' — negative lookahead }
    begin
      FPos := FPos + 1;
      Capturing := False;
      Look := 1;
      Neg := True;
    end
    else if B = CH_LT then        { '<=' / '<!' — lookbehind }
    begin
      FPos := FPos + 1;
      B := Self.PeekByte();
      if B = CH_EQUALS then
      begin
        FPos := FPos + 1;
        Capturing := False;
        Look := 2;
      end
      else if B = CH_BANG then
      begin
        FPos := FPos + 1;
        Capturing := False;
        Look := 2;
        Neg := True;
      end
      else
        Self.Fail('Unsupported group construct ''(?<''');
    end
    else
      Self.Fail('Unsupported group construct');
  end;

  { The capture number must be allocated BEFORE the body is parsed, so that
    nested groups number left-to-right by opening parenthesis. }
  Node := nil;
  if Capturing then
  begin
    FGroupCount := FGroupCount + 1;
    Node := TRegexNode.Create(opGroup);
    Node.GroupNum := FGroupCount;
  end;

  Body := Self.ParseAlternation();

  if Self.PeekByte() <> CH_RPAREN then
  begin
    if Node <> nil then
      Node.Free()
    else
      Body.Free();
    Self.Fail('Unterminated group — expected '')''');
  end;
  FPos := FPos + 1;               { consume ')' }

  if Look <> 0 then
  begin
    if Look = 1 then
      Node := TRegexNode.Create(opLookahead)
    else
      Node := TRegexNode.Create(opLookbehind);
    Node.Negate := Neg;
    Node.AddKid(Body);
    Result := Node;
    Exit;
  end;

  if Node = nil then
  begin
    { Non-capturing (possibly atomic) group: just a wrapper round the body. }
    Node := TRegexNode.Create(opGroup);
    Node.GroupNum := 0;
    Node.Atomic := Atomic;
    Node.AddKid(Body);
    Result := Node;
    Exit;
  end;

  { Capturing group.  The body is wrapped as a sequence
      capStart(n) , body , capEnd(n)
    so that the start and end registers are written as ordinary zero-width
    steps in the continuation flow.  This is what preserves give-back: if the
    continuation after the group fails, the matcher backtracks INTO the body,
    tries a shorter extent, and re-runs capEnd with the new position.  An
    earlier design resolved the body separately and could only ever offer one
    extent, which broke '(a+)\1', '(a+)ab' and every other pattern needing the
    group to give characters back. }
  Marker := TRegexNode.Create(opCapStart);
  Marker.GroupNum := Node.GroupNum;
  Node.AddKid(Marker);
  Node.AddKid(Body);
  Marker := TRegexNode.Create(opCapEnd);
  Marker.GroupNum := Node.GroupNum;
  Node.AddKid(Marker);
  Node.Atomic := Atomic;
  Result := Node;
end;

function TRegex.ParseAtom: TRegexNode;
var
  B: Int;
  Node: TRegexNode;
  Lit: Int;
  Esc: TEscape;
  FoldPair: TCharClass;
  EscPos: Int;
  I: Int;
begin
  B := Self.PeekByte();
  if B < 0 then
  begin
    Result := TRegexNode.Create(opEmpty);
    Exit;
  end;

  if B = CH_LPAREN then
  begin
    Result := Self.ParseGroup();
    Exit;
  end;

  if B = CH_LBRACKET then
  begin
    Result := Self.ParseClass();
    Exit;
  end;

  if B = CH_DOT then
  begin
    FPos := FPos + 1;
    Result := TRegexNode.Create(opAny);
    Exit;
  end;

  if B = CH_CARET then
  begin
    FPos := FPos + 1;
    Result := TRegexNode.Create(opBOL);
    Exit;
  end;

  if B = CH_DOLLAR then
  begin
    FPos := FPos + 1;
    Result := TRegexNode.Create(opEOL);
    Exit;
  end;

  { A bare quantifier has nothing to attach to. }
  if (B = CH_STAR) or (B = CH_PLUS) or (B = CH_QUESTION) then
    Self.Fail('Nothing to repeat');

  if B = CH_BACKSL then
  begin
    EscPos := FPos;
    { \b and \B are assertions and must be recognised before the general
      escape decoder, which would otherwise return backspace for \b. }
    if (FPos + 1 < FLen) then
    begin
      I := Byte(FPat[FPos + 1]);
      if I = CH_LC_B then
      begin
        FPos := FPos + 2;
        Result := TRegexNode.Create(opWordB);
        Exit;
      end;
      if I = CH_UC_B then
      begin
        FPos := FPos + 2;
        Result := TRegexNode.Create(opNotWordB);
        Exit;
      end;
    end;

    Esc := Self.ParseEscape(False);
    Lit := Esc.Value;
    if Esc.IsClass then
    begin
      Node := TRegexNode.Create(opClass);
      Node.Cls := Esc.Cls;
      { A shorthand class is already case-symmetric for \w, and folding \d or
        \s changes nothing, so no FoldClass call is needed here. }
      Result := Node;
      Exit;
    end;
    if Lit < 0 then
    begin
      { Backreference.  The referenced group must already have been opened,
        which for \1..\9 means it must exist in the pattern at all. }
      Node := TRegexNode.Create(opBackref);
      Node.RefNum := -Lit;
      if Node.RefNum > MAX_BACKREF then
      begin
        Node.Free();
        Self.FailAt('Backreference number out of range', EscPos);
      end;
      Result := Node;
      Exit;
    end;

    Node := TRegexNode.Create(opChar);
    Node.Ch := Byte(Lit);
    { Under roIgnoreCase a literal becomes a two-member class, folded now so
      the matcher stays a plain set test. }
    if (roIgnoreCase in FOptions) and (LowerByte(Lit) <> UpperByte(Lit)) then
    begin
      Node.Op := opClass;
      FoldPair := [Byte(LowerByte(Lit)), Byte(UpperByte(Lit))];
      Node.Cls := FoldPair;
    end;
    Result := Node;
    Exit;
  end;

  { Ordinary literal byte.  Multi-byte UTF-8 needs no special handling: each
    byte becomes its own opChar and they match as a run. }
  FPos := FPos + 1;
  Node := TRegexNode.Create(opChar);
  Node.Ch := Byte(B);
  if (roIgnoreCase in FOptions) and (LowerByte(B) <> UpperByte(B)) then
  begin
    Node.Op := opClass;
    FoldPair := [Byte(LowerByte(B)), Byte(UpperByte(B))];
    Node.Cls := FoldPair;
  end;
  Result := Node;
end;

{ ------------------------------------------------------------------ }
{ Matching                                                            }
{ ------------------------------------------------------------------ }

type
  { A continuation: "having matched up to here, match ANodes[AIdx..] and then
    whatever Next says".  A LINKED FRAME rather than a single (list, index)
    pair, because groups nest: when the matcher steps into a group body it
    must remember both the rest of the body AND the rest of every enclosing
    sequence.  A single pair can only hold one level and silently truncates
    the match at the group's end.

    Frames live on the Pascal call stack (each is a local of the routine that
    pushes it) and are only ever read, so no allocation or freeing is needed. }
  PContinuation = ^TContinuation;
  TContinuation = record
    Nodes: TList<TRegexNode>;
    Idx: Int;
    Next: PContinuation;
  end;

  { All mutable match state lives in this record, allocated per match call.
    Keeping it OFF the TRegex is what makes a compiled TRegex shareable
    across fibers and threads — see the unit header. }
  TMatchState = record
    Input: string;
    InLen: Int;
    Options: TRegexOptions;
    Steps: Int;
    StepLimit: Int;
    { Capture registers, 1-based by group number; index 0 is unused.
      CapStart[g] = -1 means the group has not participated. }
    CapStart: array of Int32;
    CapEnd: array of Int32;
  end;

{ Bump the step counter, raising when the budget is exhausted.  Every
  potentially-backtracking decision calls this, which is what bounds the
  search. }
procedure Step(var AState: TMatchState);
begin
  AState.Steps := AState.Steps + 1;
  if AState.Steps > AState.StepLimit then
    raise ERegexComplexity.Create(
      'Regular-expression step limit of ' + IntToStr(AState.StepLimit) +
      ' exceeded; the pattern may be backtracking catastrophically');
end;

function InputByte(const AState: TMatchState; APos: Int): Int;
begin
  if (APos < 0) or (APos >= AState.InLen) then
    Result := -1
  else
    Result := Byte(AState.Input[APos]);
end;

function IsWordAt(const AState: TMatchState; APos: Int): Boolean;
var
  B: Int;
begin
  B := InputByte(AState, APos);
  Result := (B >= 0) and IsWordByte(B);
end;

{ Forward declarations: the matcher is mutually recursive through the
  continuation chain. }
function MatchNodeList(var AState: TMatchState; ANodes: TList<TRegexNode>;
                       AIdx, APos: Int; ACont: PContinuation;
                       out AEnd: Int): Boolean; forward;

{ Match ANode at APos, then run ACont.  Threading the continuation through
  rather than returning after each node is what lets a quantifier give
  characters back and have the REST of the pattern retried. }
function MatchNode(var AState: TMatchState; ANode: TRegexNode; APos: Int;
                   ACont: PContinuation; out AEnd: Int): Boolean; forward;

{ Run a continuation chain at APos.  An empty chain means the whole pattern
  has matched, so APos is the end of the match. }
function MatchCont(var AState: TMatchState; ACont: PContinuation;
  APos: Int; out AEnd: Int): Boolean;
begin
  if ACont = nil then
  begin
    AEnd := APos;
    Result := True;
    Exit;
  end;
  Result := MatchNodeList(AState, ACont^.Nodes, ACont^.Idx, APos,
                          ACont^.Next, AEnd);
end;

{ Match the sequence ANodes[AIdx..] at APos; on running off the end, fall
  through to ACont. }
function MatchNodeList(var AState: TMatchState; ANodes: TList<TRegexNode>;
  AIdx, APos: Int; ACont: PContinuation; out AEnd: Int): Boolean;
var
  Frame: TContinuation;
begin
  Step(AState);
  if AIdx >= ANodes.Count then
  begin
    Result := MatchCont(AState, ACont, APos, AEnd);
    Exit;
  end;
  { Push "the rest of this sequence" in front of the inherited continuation. }
  Frame.Nodes := ANodes;
  Frame.Idx := AIdx + 1;
  Frame.Next := ACont;
  Result := MatchNode(AState, ANodes.Get(AIdx), APos, @Frame, AEnd);
end;

{ Match ARep's child exactly ACount more times (the mandatory prefix), then
  hand over to the optional tail.  Split out so Min and the optional part can
  share one recursion. }
function MatchRepeat(var AState: TMatchState; ARep: TRegexNode;
                     ADone, APos: Int;
                     ACont: PContinuation; out AEnd: Int): Boolean; forward;

function MatchNode(var AState: TMatchState; ANode: TRegexNode; APos: Int;
  ACont: PContinuation; out AEnd: Int): Boolean;
var
  B: Int;
  I: Int;
  SeqLen: Int;
  Sub: TRegexNode;
  SaveStart, SaveEnd: Int;
  InnerEnd: Int;
  Ok: Boolean;
  RefLen: Int;
  RefStart: Int;
  Back: Int;
  Before, After: Boolean;
begin
  Step(AState);
  Result := False;
  AEnd := -1;

  case ANode.Op of

    opEmpty:
      Result := MatchCont(AState, ACont, APos, AEnd);

    opChar:
      begin
        if InputByte(AState, APos) = ANode.Ch then
          Result := MatchCont(AState, ACont, APos + 1, AEnd);
      end;

    opClass:
      begin
        B := InputByte(AState, APos);
        if (B >= 0) and (B in ANode.Cls) then
          Result := MatchCont(AState, ACont, APos + 1, AEnd);
      end;

    opAny:
      begin
        { '.' consumes a whole UTF-8 codepoint so a capture can never split a
          sequence — see UNICODE POSITION in the unit header. }
        B := InputByte(AState, APos);
        if B < 0 then
          Exit;
        if (B = CH_LF) and not (roDotMatchesNewLine in AState.Options) then
          Exit;
        SeqLen := Utf8SeqLen(B);
        if APos + SeqLen > AState.InLen then
          SeqLen := 1;
        Result := MatchCont(AState, ACont, APos + SeqLen, AEnd);
      end;

    opBOL:
      begin
        if APos = 0 then
          Result := MatchCont(AState, ACont, APos, AEnd)
        else if (roMultiLine in AState.Options)
                and (InputByte(AState, APos - 1) = CH_LF) then
          Result := MatchCont(AState, ACont, APos, AEnd);
      end;

    opEOL:
      begin
        if APos = AState.InLen then
          Result := MatchCont(AState, ACont, APos, AEnd)
        else if (roMultiLine in AState.Options)
                and (InputByte(AState, APos) = CH_LF) then
          Result := MatchCont(AState, ACont, APos, AEnd);
      end;

    opWordB:
      begin
        Before := IsWordAt(AState, APos - 1);
        After := IsWordAt(AState, APos);
        if Before <> After then
          Result := MatchCont(AState, ACont, APos, AEnd);
      end;

    opNotWordB:
      begin
        Before := IsWordAt(AState, APos - 1);
        After := IsWordAt(AState, APos);
        if Before = After then
          Result := MatchCont(AState, ACont, APos, AEnd);
      end;

    opConcat:
      Result := MatchNodeList(AState, ANode.Kids, 0, APos, ACont, AEnd);

    opAlt:
      begin
        { Leftmost-FIRST: the first alternative that lets the WHOLE rest of
          the pattern succeed wins, so the continuation is passed down into
          each branch rather than being applied afterwards. }
        for I := 0 to ANode.Kids.Count - 1 do
        begin
          Step(AState);
          Sub := ANode.Kids.Get(I);
          if MatchNode(AState, Sub, APos, ACont, InnerEnd) then
          begin
            AEnd := InnerEnd;
            Result := True;
            Exit;
          end;
        end;
      end;

    opGroup:
      begin
        if ANode.Atomic then
        begin
          { Atomic: resolve the body independently, commit to its first match,
            and never give any of it back to the continuation. }
          if not MatchNodeList(AState, ANode.Kids, 0, APos, nil, InnerEnd) then
            Exit;
          Result := MatchCont(AState, ACont, InnerEnd, AEnd);
          Exit;
        end;
        { Ordinary group — including a capturing one, whose Kids are
          [capStart, body, capEnd].  Walking the sequence with the outer
          continuation attached is all that is needed. }
        Result := MatchNodeList(AState, ANode.Kids, 0, APos, ACont, AEnd);
      end;

    opCapStart:
      begin
        { Zero-width: record the start, run the continuation, and restore on
          failure so a discarded attempt leaves no stale capture behind. }
        SaveStart := AState.CapStart[ANode.GroupNum];
        AState.CapStart[ANode.GroupNum] := APos;
        Result := MatchCont(AState, ACont, APos, AEnd);
        if not Result then
          AState.CapStart[ANode.GroupNum] := SaveStart;
      end;

    opCapEnd:
      begin
        SaveEnd := AState.CapEnd[ANode.GroupNum];
        AState.CapEnd[ANode.GroupNum] := APos;
        Result := MatchCont(AState, ACont, APos, AEnd);
        if not Result then
          AState.CapEnd[ANode.GroupNum] := SaveEnd;
      end;

    opLookahead:
      begin
        { Zero-width: the body is matched independently and the position is
          NOT advanced, whichever way the assertion goes. }
        Sub := ANode.Kids.Get(0);
        Ok := MatchNode(AState, Sub, APos, nil, InnerEnd);
        if Ok = ANode.Negate then
          Exit;
        Result := MatchCont(AState, ACont, APos, AEnd);
      end;

    opLookbehind:
      begin
        { Byte-oriented variable-length lookbehind: try every start offset
          behind APos and require the body to end exactly at APos.  Simple
          and correct; the cost is bounded by APos, which the step budget
          also covers. }
        Sub := ANode.Kids.Get(0);
        Ok := False;
        for Back := APos downto 0 do
        begin
          Step(AState);
          if MatchNode(AState, Sub, Back, nil, InnerEnd) then
            if InnerEnd = APos then
            begin
              Ok := True;
              Break;
            end;
        end;
        if Ok = ANode.Negate then
          Exit;
        Result := MatchCont(AState, ACont, APos, AEnd);
      end;

    opBackref:
      begin
        if ANode.RefNum >= System.Length(AState.CapStart) then
          Exit;
        RefStart := AState.CapStart[ANode.RefNum];
        if RefStart < 0 then
          Exit;                    { group did not participate }
        RefLen := AState.CapEnd[ANode.RefNum] - RefStart;
        if APos + RefLen > AState.InLen then
          Exit;
        for I := 0 to RefLen - 1 do
        begin
          B := InputByte(AState, APos + I);
          SeqLen := InputByte(AState, RefStart + I);
          if roIgnoreCase in AState.Options then
          begin
            if LowerByte(B) <> LowerByte(SeqLen) then
              Exit;
          end
          else if B <> SeqLen then
            Exit;
        end;
        Result := MatchCont(AState, ACont, APos + RefLen, AEnd);
      end;

    opRepeat:
      Result := MatchRepeat(AState, ANode, 0, APos, ACont, AEnd);

  end;
end;

{ Recursive quantifier engine.  ADone counts iterations already matched.
  Below Min the child is mandatory; at or above Min there is a choice, and
  greedy/lazy/possessive differ only in the order (or existence) of the two
  alternatives. }
function MatchRepeat(var AState: TMatchState; ARep: TRegexNode;
  ADone, APos: Int; ACont: PContinuation;
  out AEnd: Int): Boolean;
var
  Sub: TRegexNode;
  InnerEnd: Int;
  Pos2: Int;
  Count: Int;
begin
  Step(AState);
  Sub := ARep.Kids.Get(0);
  Result := False;
  AEnd := -1;

  { Mandatory iterations: no choice to make, so no backtracking point. }
  if ADone < ARep.RepMin then
  begin
    if not MatchNode(AState, Sub, APos, nil, InnerEnd) then
      Exit;
    { A mandatory iteration that consumed nothing would loop forever. }
    if InnerEnd = APos then
    begin
      Result := MatchRepeat(AState, ARep, ARep.RepMin, APos, ACont, AEnd);
      Exit;
    end;
    Result := MatchRepeat(AState, ARep, ADone + 1, InnerEnd, ACont, AEnd);
    Exit;
  end;

  { Possessive: consume as many iterations as possible, then commit — never
    give any back.  This is exactly an atomic group over the quantifier, and
    it is the cheap defence against catastrophic backtracking. }
  if ARep.Possessive then
  begin
    Pos2 := APos;
    Count := ADone;
    while (ARep.RepMax = UNBOUNDED) or (Count < ARep.RepMax) do
    begin
      Step(AState);
      if not MatchNode(AState, Sub, Pos2, nil, InnerEnd) then
        Break;
      if InnerEnd = Pos2 then
        Break;                     { zero-width iteration — stop }
      Pos2 := InnerEnd;
      Count := Count + 1;
    end;
    Result := MatchCont(AState, ACont, Pos2, AEnd);
    Exit;
  end;

  if ARep.Lazy then
  begin
    { Prefer stopping. }
    if MatchCont(AState, ACont, APos, AEnd) then
    begin
      Result := True;
      Exit;
    end;
    if (ARep.RepMax <> UNBOUNDED) and (ADone >= ARep.RepMax) then
      Exit;
    if not MatchNode(AState, Sub, APos, nil, InnerEnd) then
      Exit;
    if InnerEnd = APos then
      Exit;                        { zero-width — stop, already tried }
    Result := MatchRepeat(AState, ARep, ADone + 1, InnerEnd, ACont, AEnd);
    Exit;
  end;

  { Greedy: prefer one more iteration, fall back to stopping. }
  if (ARep.RepMax = UNBOUNDED) or (ADone < ARep.RepMax) then
  begin
    if MatchNode(AState, Sub, APos, nil, InnerEnd) then
      if InnerEnd <> APos then
        if MatchRepeat(AState, ARep, ADone + 1, InnerEnd, ACont, AEnd) then
        begin
          Result := True;
          Exit;
        end;
  end;
  Result := MatchCont(AState, ACont, APos, AEnd);
end;

{ ------------------------------------------------------------------ }
{ TRegex — public matching API                                        }
{ ------------------------------------------------------------------ }

function TRegex.Match(const AInput: string): TMatch;
begin
  Result := Self.Match(AInput, 0);
end;

function TRegex.Match(const AInput: string; AStartAt: Int): TMatch;
var
  State: TMatchState;
  Start: Int;
  MatchEnd: Int;
  I: Int;
  G: TGroup;
  B: Int;
  Adv: Int;
begin
  Result.Success := False;
  Result.Index := -1;
  Result.Length := 0;
  Result.Value := '';
  SetLength(Result.FGroups, 0);

  State.Input := AInput;
  State.InLen := Length(AInput);
  State.Options := FOptions;
  State.StepLimit := FStepLimit;
  SetLength(State.CapStart, FGroupCount + 1);
  SetLength(State.CapEnd, FGroupCount + 1);

  if AStartAt < 0 then
    AStartAt := 0;

  Start := AStartAt;
  while Start <= State.InLen do
  begin
    { The step counter is per START POSITION, not per Match call: a long
      subject scanned with a cheap pattern must not exhaust the budget merely
      by being long.  The budget bounds the BACKTRACKING at each anchor. }
    State.Steps := 0;
    for I := 0 to FGroupCount do
    begin
      State.CapStart[I] := -1;
      State.CapEnd[I] := -1;
    end;

    if MatchNode(State, FRoot, Start, nil, MatchEnd) then
    begin
      Result.Success := True;
      Result.Index := Start;
      Result.Length := MatchEnd - Start;
      Result.Value := Copy(AInput, Start, MatchEnd - Start);

      SetLength(Result.FGroups, FGroupCount + 1);
      Result.FGroups[0].Index := Start;
      Result.FGroups[0].Length := MatchEnd - Start;
      Result.FGroups[0].Value := Result.Value;
      for I := 1 to FGroupCount do
      begin
        if State.CapStart[I] >= 0 then
        begin
          G.Index := State.CapStart[I];
          G.Length := State.CapEnd[I] - State.CapStart[I];
          G.Value := Copy(AInput, G.Index, G.Length);
        end
        else
        begin
          G.Index := -1;
          G.Length := 0;
          G.Value := '';
        end;
        Result.FGroups[I] := G;
      end;
      Exit;
    end;

    { Advance one whole codepoint so a match can never start mid-sequence. }
    B := InputByte(State, Start);
    if B < 0 then
      Adv := 1
    else
      Adv := Utf8SeqLen(B);
    Start := Start + Adv;
  end;
end;

function TRegex.IsMatch(const AInput: string): Boolean;
begin
  Result := Self.Match(AInput, 0).Success;
end;

function TRegex.IsMatch(const AInput: string; AStartAt: Int): Boolean;
begin
  Result := Self.Match(AInput, AStartAt).Success;
end;

function TRegex.Matches(const AInput: string): TList<TMatch>;
var
  M: TMatch;
  Pos: Int;
  InLen: Int;
  B: Int;
begin
  Result := TList<TMatch>.Create();
  Pos := 0;
  InLen := Length(AInput);
  while Pos <= InLen do
  begin
    M := Self.Match(AInput, Pos);
    if not M.Success then
      Break;
    Result.Add(M);
    if M.Length > 0 then
      Pos := M.Index + M.Length
    else
    begin
      { An empty match must still advance, or this loops forever.  Advance a
        whole codepoint to keep offsets on sequence boundaries. }
      if M.Index >= InLen then
        Break;
      B := Byte(AInput[M.Index]);
      Pos := M.Index + Utf8SeqLen(B);
    end;
  end;
end;

{ Expand '$1'..'$9', '$&' and '$$' in AReplacement against AMatch. }
function ExpandReplacement(const AReplacement: string; const AMatch: TMatch): string;
var
  SB: TStringBuilder;
  I: Int;
  N: Int;
  B: Int;
  M: TMatch;
begin
  M := AMatch;
  SB := TStringBuilder.Create();
  try
    N := Length(AReplacement);
    I := 0;
    while I < N do
    begin
      B := Byte(AReplacement[I]);
      if (B = CH_DOLLAR) and (I + 1 < N) then
      begin
        B := Byte(AReplacement[I + 1]);
        if B = CH_DOLLAR then
        begin
          SB.AppendByte(CH_DOLLAR);
          I := I + 2;
          Continue;
        end;
        if B = CH_AMP then
        begin
          SB.Append(M.Value);
          I := I + 2;
          Continue;
        end;
        if IsDigitByte(B) then
        begin
          SB.Append(M.GroupValue(B - CH_0));
          I := I + 2;
          Continue;
        end;
        { Unknown '$x' — emit verbatim. }
        SB.AppendByte(CH_DOLLAR);
        I := I + 1;
        Continue;
      end;
      SB.AppendByte(Byte(AReplacement[I]));
      I := I + 1;
    end;
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

function TRegex.Replace(const AInput, AReplacement: string): string;
var
  SB: TStringBuilder;
  L: TList<TMatch>;
  I: Int;
  M: TMatch;
  Cursor: Int;
begin
  L := Self.Matches(AInput);
  try
    if L.Count = 0 then
    begin
      Result := AInput;
      Exit;
    end;
    SB := TStringBuilder.Create();
    try
      Cursor := 0;
      for I := 0 to L.Count - 1 do
      begin
        M := L.Get(I);
        if M.Index > Cursor then
          SB.Append(Copy(AInput, Cursor, M.Index - Cursor));
        SB.Append(ExpandReplacement(AReplacement, M));
        Cursor := M.Index + M.Length;
      end;
      if Cursor < Length(AInput) then
        SB.Append(Copy(AInput, Cursor, Length(AInput) - Cursor));
      Result := SB.ToString();
    finally
      SB.Free();
    end;
  finally
    L.Free();
  end;
end;

function TRegex.Split(const AInput: string): TList<String>;
var
  L: TList<TMatch>;
  I: Int;
  M: TMatch;
  Cursor: Int;
begin
  Result := TList<String>.Create();
  L := Self.Matches(AInput);
  try
    Cursor := 0;
    for I := 0 to L.Count - 1 do
    begin
      M := L.Get(I);
      { A zero-width match would produce an endless run of empty pieces;
        skip it, which is what .NET's Regex.Split effectively does for the
        degenerate case. }
      if M.Length = 0 then
        Continue;
      Result.Add(Copy(AInput, Cursor, M.Index - Cursor));
      Cursor := M.Index + M.Length;
    end;
    Result.Add(Copy(AInput, Cursor, Length(AInput) - Cursor));
  finally
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ TRegex — static convenience methods                                 }
{ ------------------------------------------------------------------ }

static function TRegex.IsMatch(const AInput, APattern: string): Boolean;
var
  NoOptions: TRegexOptions;
begin
  NoOptions := [];
  Result := TRegex.IsMatch(AInput, APattern, NoOptions);
end;

static function TRegex.IsMatch(const AInput, APattern: string;
  AOptions: TRegexOptions): Boolean;
var
  R: TRegex;
begin
  R := TRegex.Create(APattern, AOptions);
  try
    Result := R.IsMatch(AInput);
  finally
    R.Free();
  end;
end;

static function TRegex.Match(const AInput, APattern: string): TMatch;
var
  NoOptions: TRegexOptions;
begin
  NoOptions := [];
  Result := TRegex.Match(AInput, APattern, NoOptions);
end;

static function TRegex.Match(const AInput, APattern: string;
  AOptions: TRegexOptions): TMatch;
var
  R: TRegex;
begin
  R := TRegex.Create(APattern, AOptions);
  try
    Result := R.Match(AInput);
  finally
    R.Free();
  end;
end;

static function TRegex.Replace(const AInput, APattern,
  AReplacement: string): string;
var
  R: TRegex;
  Opts: TRegexOptions;
begin
  Opts := [];
  R := TRegex.Create(APattern, Opts);
  try
    Result := R.Replace(AInput, AReplacement);
  finally
    R.Free();
  end;
end;

static function TRegex.Split(const AInput, APattern: string): TList<String>;
var
  R: TRegex;
  Opts: TRegexOptions;
begin
  Opts := [];
  R := TRegex.Create(APattern, Opts);
  try
    Result := R.Split(AInput);
  finally
    R.Free();
  end;
end;

end.
