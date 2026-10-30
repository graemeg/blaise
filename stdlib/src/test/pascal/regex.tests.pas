{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Tests for Text.Regex.  Self-registers via the initialization section. }

unit Regex.Tests;

interface

uses
  blaise.testing, SysUtils, StrUtils, Generics.Collections, Text.Regex;

type
  TRegexTests = class(TTestCase)
  private
    { Helpers keep the assertions terse: compile APattern, match AInput, and
      assert on the outcome. }
    procedure AssertMatchAt(const AMsg, APattern, AInput: string;
                            AIndex: Int; const AValue: string);
    procedure AssertNoMatch(const AMsg, APattern, AInput: string);
  published
    { --- commit 1: core engine --- }
    procedure TestLiteral_MatchAndPosition;
    procedure TestLiteral_NoMatchReturnsMinusOne;
    procedure TestDot;
    procedure TestCharClass_Range;
    procedure TestCharClass_Negated;
    procedure TestEscapedMetacharacters;
    procedure TestGreedyStar;
    procedure TestGreedyPlus;
    procedure TestOptional;
    procedure TestAlternation_LeftmostFirst;
    procedure TestCapturingGroups;
    procedure TestStaticIsMatchAndMatch;
    procedure TestStepLimit_RaisesComplexity;
    procedure TestSyntaxError_UnclosedGroup;

    { --- commit 2: anchors, repetition, classes, options --- }
    procedure TestAnchors;
    procedure TestMultiLine;
    procedure TestBoundedRepetition;
    procedure TestBoundedRepetition_AbsurdRejected;
    procedure TestLazyQuantifiers;
    procedure TestShorthandClasses;
    procedure TestWordBoundary;
    procedure TestNonCapturingGroup;
    procedure TestIgnoreCase_AsciiOnly;
    procedure TestDotMatchesNewLine;
    procedure TestDotIsUtf8Aware;

    { --- commit 3: backtracking-only features --- }
    procedure TestBackreference;
    procedure TestLookahead;
    procedure TestLookbehind;
    procedure TestAtomicGroup;
    procedure TestPossessiveQuantifier;

    { --- commit 4: convenience API --- }
    procedure TestMatches_AllNonOverlapping;
    procedure TestMatches_ForIn;
    procedure TestReplace_GroupReferences;
    procedure TestReplace_WholeMatchReference;
    procedure TestSplit;
    procedure TestStaticReplaceAndSplit;

    { --- unicode position --- }
    procedure TestUtf8LiteralByteOffsets;
    procedure TestCharClass_NonAsciiRangeRejected;

    { --- runtime-built subject (self-hosting byte-read guard) --- }
    procedure TestRuntimeBuiltSubject;
  end;

implementation

{ Compile APattern with the three options given as flags.

  The options are passed as BOOLEANS rather than as a TRegexOptions set
  because a set literal does not match a set-typed parameter whose type came
  from a cached unit interface (BUG-20260719-set-literal-vs-cached-bif) — and TRegexOptions is imported from
  Text.Regex, so even a set-typed parameter on a LOCAL helper cannot be called
  with '[roIgnoreCase]' on an incremental rebuild.  Building the set here,
  where each element is added individually, avoids constructing a set literal
  of the imported type entirely.  Simplify once BUG-20260719-set-literal-vs-cached-bif is fixed. }
function MakeRegex(const APattern: string;
  AIgnoreCase, AMultiLine, ADotAll: Boolean): TRegex;
var
  Opts: TRegexOptions;
begin
  Opts := [];
  if AIgnoreCase then
    Opts := Opts + [roIgnoreCase];
  if AMultiLine then
    Opts := Opts + [roMultiLine];
  if ADotAll then
    Opts := Opts + [roDotMatchesNewLine];
  Result := TRegex.Create(APattern, Opts);
end;

procedure TRegexTests.AssertMatchAt(const AMsg, APattern, AInput: string;
  AIndex: Int; const AValue: string);
var
  R: TRegex;
  M: TMatch;
begin
  R := TRegex.Create(APattern);
  try
    M := R.Match(AInput);
    AssertTrue(AMsg + ': Success', M.Success);
    AssertEquals(AMsg + ': Index', AIndex, M.Index);
    AssertEquals(AMsg + ': Value', AValue, M.Value);
    AssertEquals(AMsg + ': Length', Length(AValue), M.Length);
  finally
    R.Free();
  end;
end;

procedure TRegexTests.AssertNoMatch(const AMsg, APattern, AInput: string);
var
  R: TRegex;
  M: TMatch;
begin
  R := TRegex.Create(APattern);
  try
    M := R.Match(AInput);
    AssertTrue(AMsg + ': not Success', not M.Success);
    AssertEquals(AMsg + ': Index is -1', -1, M.Index);
    AssertTrue(AMsg + ': not IsMatch', not R.IsMatch(AInput));
  finally
    R.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Commit 1 — core engine                                             }
{ ------------------------------------------------------------------ }

procedure TRegexTests.TestLiteral_MatchAndPosition;
begin
  AssertMatchAt('at start', 'abc', 'abcdef', 0, 'abc');
  AssertMatchAt('mid', 'cd', 'abcdef', 2, 'cd');
  AssertMatchAt('at end', 'ef', 'abcdef', 4, 'ef');
  AssertMatchAt('empty pattern', '', 'abc', 0, '');
end;

procedure TRegexTests.TestLiteral_NoMatchReturnsMinusOne;
begin
  AssertNoMatch('absent', 'xyz', 'abcdef');
  AssertNoMatch('longer than subject', 'abcdefg', 'abcdef');
  AssertNoMatch('empty subject', 'a', '');
end;

procedure TRegexTests.TestDot;
begin
  AssertMatchAt('dot any', 'a.c', 'abc', 0, 'abc');
  AssertMatchAt('dot any 2', 'a.c', 'a c', 0, 'a c');
  { '.' does not cross a newline unless roDotMatchesNewLine is set. }
  AssertNoMatch('dot stops at newline', 'a.c', 'a' + #10 + 'c');
end;

procedure TRegexTests.TestCharClass_Range;
begin
  AssertMatchAt('lower range', '[a-z]+', '123abc456', 3, 'abc');
  AssertMatchAt('digit range', '[0-9]+', 'ab123cd', 2, '123');
  AssertMatchAt('multi range', '[a-cx-z]+', 'qqabzyk', 2, 'abzy');
  AssertMatchAt('literal dash last', '[a-]+', 'x-a-y', 1, '-a-');
end;

procedure TRegexTests.TestCharClass_Negated;
begin
  AssertMatchAt('negated', '[^0-9]+', '12abc34', 2, 'abc');
  AssertMatchAt('negated single', '[^a]+', 'aXYZa', 1, 'XYZ');
end;

procedure TRegexTests.TestEscapedMetacharacters;
begin
  AssertMatchAt('escaped dot', 'a\.c', 'abc a.c', 4, 'a.c');
  AssertMatchAt('escaped star', 'a\*', 'xa*y', 1, 'a*');
  AssertMatchAt('escaped paren', '\(x\)', 'a(x)b', 1, '(x)');
  AssertMatchAt('escaped backslash', 'a\\b', 'a\b', 0, 'a\b');
  AssertMatchAt('escaped bracket', '\[', 'a[b', 1, '[');
end;

procedure TRegexTests.TestGreedyStar;
begin
  AssertMatchAt('star greedy', 'a*', 'aaab', 0, 'aaa');
  AssertMatchAt('star zero', 'x*', 'abc', 0, '');
  AssertMatchAt('star in context', 'a*b', 'caaab', 1, 'aaab');
  AssertMatchAt('dot star greedy', '<.*>', 'a<b><c>d', 1, '<b><c>');
end;

procedure TRegexTests.TestGreedyPlus;
begin
  AssertMatchAt('plus greedy', 'a+', 'baaac', 1, 'aaa');
  AssertNoMatch('plus needs one', 'x+', 'abc');
end;

procedure TRegexTests.TestOptional;
begin
  AssertMatchAt('optional present', 'ab?c', 'abc', 0, 'abc');
  AssertMatchAt('optional absent', 'ab?c', 'ac', 0, 'ac');
  AssertMatchAt('optional greedy', 'ab?', 'ab', 0, 'ab');
end;

procedure TRegexTests.TestAlternation_LeftmostFirst;
begin
  { The backtracking engine is leftmost-FIRST (like Perl/.NET), not
    leftmost-LONGEST: the first alternative that succeeds wins. }
  AssertMatchAt('first alt wins', 'foo|foobar', 'foobar', 0, 'foo');
  AssertMatchAt('second alt', 'x|foo', 'foo', 0, 'foo');
  AssertMatchAt('alt in group', 'a(b|c)d', 'acd', 0, 'acd');
  AssertMatchAt('empty alt branch', 'a(b|)c', 'ac', 0, 'ac');
end;

procedure TRegexTests.TestCapturingGroups;
var
  R: TRegex;
  M: TMatch;
begin
  R := TRegex.Create('(a+)(b+)');
  try
    AssertEquals('GroupCount on regex', 2, R.GroupCount);
    M := R.Match('xxaaabbyy');
    AssertTrue('Success', M.Success);
    AssertEquals('whole Index', 2, M.Index);
    AssertEquals('whole Value', 'aaabb', M.Value);
    { Group 0 is the whole match, so GroupCount counts it too. }
    AssertEquals('match GroupCount', 3, M.GroupCount());
    AssertEquals('g0', 'aaabb', M.GroupValue(0));
    AssertEquals('g1', 'aaa', M.GroupValue(1));
    AssertEquals('g2', 'bb', M.GroupValue(2));
    AssertEquals('g1 index', 2, M.Group(1).Index);
    AssertEquals('g2 index', 5, M.Group(2).Index);
    AssertEquals('g2 length', 2, M.Group(2).Length);
    { Out-of-range group returns Index = -1 rather than raising. }
    AssertEquals('oob index', -1, M.Group(9).Index);
    AssertEquals('oob value', '', M.GroupValue(9));
    AssertEquals('negative index', -1, M.Group(-1).Index);
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestStaticIsMatchAndMatch;
var
  M: TMatch;
begin
  AssertTrue('static IsMatch true', TRegex.IsMatch('abc123', '[0-9]+'));
  AssertTrue('static IsMatch false', not TRegex.IsMatch('abc', '[0-9]+'));
  M := TRegex.Match('abc123', '[0-9]+');
  AssertTrue('static Match Success', M.Success);
  AssertEquals('static Match Index', 3, M.Index);
  AssertEquals('static Match Value', '123', M.Value);
end;

procedure TRegexTests.TestStepLimit_RaisesComplexity;
var
  R: TRegex;
  Subject: string;
  I: Int;
  Raised: Boolean;
begin
  { The step budget is the guard that a match ALWAYS terminates.  This test
    pins two halves of that contract.

    Half one: an expensive pattern under a small budget must raise
    ERegexComplexity PROMPTLY rather than run for an unbounded time.  A
    variable-length lookbehind is the clearest case — it retries every start
    offset behind each position, so its cost grows with the subject. }
  Subject := '';
  for I := 0 to 199 do
    Subject := Subject + 'a';

  R := TRegex.Create('(?<=a{1,50})b');
  try
    R.StepLimit := 1000;
    Raised := False;
    try
      R.IsMatch(Subject);
    except
      on E: ERegexComplexity do
        Raised := True;
    end;
    AssertTrue('ERegexComplexity raised under a small budget', Raised);
  finally
    R.Free();
  end;

  { Half two: the SAME pattern completes normally under the default budget,
    so the limit bounds pathological work without breaking ordinary work. }
  R := TRegex.Create('(?<=a{1,50})b');
  try
    AssertTrue('completes under the default budget', not R.IsMatch(Subject));
  finally
    R.Free();
  end;

  { The classic '(a+)+b' blowup is NOT catastrophic in this engine: a greedy
    repeat only recurses when an iteration actually consumed input, which
    collapses the redundant re-partitionings that make it exponential in a
    naive backtracker.  It therefore terminates quickly and correctly on its
    own.  This is asserted so that a future change which reintroduces the
    exponential behaviour is caught here rather than in production — if this
    starts raising ERegexComplexity, the pruning was lost. }
  Subject := '';
  for I := 0 to 29 do
    Subject := Subject + 'a';

  R := TRegex.Create('(a+)+b');
  try
    R.StepLimit := 200000;
    AssertTrue('(a+)+b terminates without blowing a small budget',
               not R.IsMatch(Subject));
    AssertTrue('(a+)+b still matches when it should', R.IsMatch(Subject + 'b'));
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestSyntaxError_UnclosedGroup;
var
  Raised: Boolean;
  Pos: Int;
  R: TRegex;
begin
  Raised := False;
  Pos := -99;
  try
    R := TRegex.Create('a(bc');
    R.Free();
  except
    on E: ERegexSyntaxError do
    begin
      Raised := True;
      Pos := E.Position;
    end;
  end;
  AssertTrue('unclosed group raises', Raised);
  { 0-based position: the pattern ends at offset 4, where ')' was expected. }
  AssertEquals('position', 4, Pos);

  Raised := False;
  try
    R := TRegex.Create('a[bc');
    R.Free();
  except
    on E: ERegexSyntaxError do
      Raised := True;
  end;
  AssertTrue('unclosed class raises', Raised);

  Raised := False;
  try
    R := TRegex.Create('*a');
    R.Free();
  except
    on E: ERegexSyntaxError do
      Raised := True;
  end;
  AssertTrue('dangling quantifier raises', Raised);

  Raised := False;
  try
    R := TRegex.Create('a)');
    R.Free();
  except
    on E: ERegexSyntaxError do
      Raised := True;
  end;
  AssertTrue('unbalanced close paren raises', Raised);

  Raised := False;
  try
    R := TRegex.Create('a\');
    R.Free();
  except
    on E: ERegexSyntaxError do
      Raised := True;
  end;
  AssertTrue('trailing backslash raises', Raised);
end;

{ ------------------------------------------------------------------ }
{ Commit 2 — anchors, repetition, shorthand classes, options          }
{ ------------------------------------------------------------------ }

procedure TRegexTests.TestAnchors;
begin
  AssertMatchAt('caret', '^abc', 'abcdef', 0, 'abc');
  AssertNoMatch('caret not at start', '^bcd', 'abcdef');
  AssertMatchAt('dollar', 'def$', 'abcdef', 3, 'def');
  AssertNoMatch('dollar not at end', 'abc$', 'abcdef');
  AssertMatchAt('both anchors', '^abc$', 'abc', 0, 'abc');
  AssertNoMatch('both anchors fail', '^abc$', 'abcd');
end;

procedure TRegexTests.TestMultiLine;
var
  R: TRegex;
  M: TMatch;
begin
  { Without roMultiLine, ^ and $ only match at the very start/end. }
  AssertNoMatch('no multiline', '^def', 'abc' + #10 + 'def');

  R := MakeRegex('^def', False, True, False);
  try
    M := R.Match('abc' + #10 + 'def');
    AssertTrue('multiline ^ Success', M.Success);
    AssertEquals('multiline ^ Index', 4, M.Index);
  finally
    R.Free();
  end;

  R := MakeRegex('abc$', False, True, False);
  try
    M := R.Match('abc' + #10 + 'def');
    AssertTrue('multiline $ Success', M.Success);
    AssertEquals('multiline $ Index', 0, M.Index);
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestBoundedRepetition;
begin
  AssertMatchAt('exact n', 'a{3}', 'baaaaa', 1, 'aaa');
  AssertMatchAt('n to m', 'a{2,4}', 'baaaaaa', 1, 'aaaa');
  AssertMatchAt('n or more', 'a{2,}', 'baaac', 1, 'aaa');
  AssertNoMatch('too few', 'a{4}', 'baaac');
  AssertMatchAt('zero lower bound', 'ab{0,2}c', 'ac', 0, 'ac');
  AssertMatchAt('braces on group', '(ab){2}', 'xababy', 1, 'abab');
end;

procedure TRegexTests.TestBoundedRepetition_AbsurdRejected;
var
  Raised: Boolean;
  R: TRegex;
begin
  { A huge bound would explode the compiled program size, so it is a
    syntax error rather than an OOM. }
  Raised := False;
  try
    R := TRegex.Create('a{1,100000}');
    R.Free();
  except
    on E: ERegexSyntaxError do
      Raised := True;
  end;
  AssertTrue('absurd upper bound rejected', Raised);

  Raised := False;
  try
    R := TRegex.Create('a{5,2}');
    R.Free();
  except
    on E: ERegexSyntaxError do
      Raised := True;
  end;
  AssertTrue('min greater than max rejected', Raised);
end;

procedure TRegexTests.TestLazyQuantifiers;
begin
  AssertMatchAt('lazy star', '<.*?>', 'a<b><c>d', 1, '<b>');
  AssertMatchAt('lazy plus', 'a+?', 'aaa', 0, 'a');
  AssertMatchAt('lazy optional', 'ab??c', 'abc', 0, 'abc');
  AssertMatchAt('lazy bounded', 'a{2,4}?', 'aaaa', 0, 'aa');
end;

procedure TRegexTests.TestShorthandClasses;
begin
  AssertMatchAt('\d', '\d+', 'ab123cd', 2, '123');
  AssertMatchAt('\D', '\D+', '12ab34', 2, 'ab');
  AssertMatchAt('\w', '\w+', ' a_b9 ', 1, 'a_b9');
  AssertMatchAt('\W', '\W+', 'ab  cd', 2, '  ');
  AssertMatchAt('\s', '\s+', 'ab  cd', 2, '  ');
  AssertMatchAt('\S', '\S+', '  ab  ', 2, 'ab');
  { Shorthands work inside a character class too. }
  AssertMatchAt('class with \d', '[\d.]+', 'x3.14y', 1, '3.14');
  { Escaped whitespace literals. }
  AssertMatchAt('\t', 'a\tb', 'a' + #9 + 'b', 0, 'a' + #9 + 'b');
  AssertMatchAt('\n', 'a\nb', 'a' + #10 + 'b', 0, 'a' + #10 + 'b');
end;

procedure TRegexTests.TestWordBoundary;
begin
  AssertMatchAt('\b at start', '\bcat\b', 'a cat here', 2, 'cat');
  AssertNoMatch('\b rejects inner', '\bcat\b', 'concatenate');
  AssertMatchAt('\B inner', '\Bcat\B', 'concatenate', 3, 'cat');
  AssertMatchAt('\b before end', 'dog\b', 'a dog', 2, 'dog');
end;

procedure TRegexTests.TestNonCapturingGroup;
var
  R: TRegex;
  M: TMatch;
begin
  R := TRegex.Create('(?:ab)+(c)');
  try
    AssertEquals('only one capturing group', 1, R.GroupCount);
    M := R.Match('ababc');
    AssertTrue('Success', M.Success);
    AssertEquals('whole', 'ababc', M.Value);
    AssertEquals('g1 is the c', 'c', M.GroupValue(1));
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestIgnoreCase_AsciiOnly;
var
  R: TRegex;
begin
  R := MakeRegex('abc', True, False, False);
  try
    AssertTrue('upper subject', R.IsMatch('XABCX'));
    AssertTrue('mixed subject', R.IsMatch('AbC'));
  finally
    R.Free();
  end;

  R := MakeRegex('[a-z]+', True, False, False);
  try
    AssertTrue('class folded', R.IsMatch('ABC'));
  finally
    R.Free();
  end;

  { Case folding is ASCII-ONLY by design.  Latin-1 supplement letters such as
    U+00C9 (E-acute, UTF-8 C3 89) and U+00E9 (e-acute, UTF-8 C3 A9) are NOT
    folded onto each other.  This test pins that documented limit — if
    Unicode folding is ever added, this assertion must be revisited
    deliberately, not silently. }
  R := MakeRegex('é', True, False, False);
  try
    AssertTrue('non-ascii matches itself', R.IsMatch('x' + 'é' + 'y'));
    AssertTrue('non-ascii NOT folded', not R.IsMatch('x' + 'É' + 'y'));
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestDotMatchesNewLine;
var
  R: TRegex;
begin
  R := MakeRegex('a.c', False, False, True);
  try
    AssertTrue('dot spans newline', R.IsMatch('a' + #10 + 'c'));
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestDotIsUtf8Aware;
var
  R: TRegex;
  M: TMatch;
begin
  { '.' consumes a whole UTF-8 codepoint, never half a sequence, so a
    captured Value is always valid UTF-8.  U+00E9 is 2 bytes (C3 A9);
    U+20AC (euro) is 3 bytes (E2 82 AC). }
  R := TRegex.Create('a.b');
  try
    M := R.Match('a' + 'é' + 'b');
    AssertTrue('2-byte cp Success', M.Success);
    AssertEquals('2-byte cp Value', 'a' + 'é' + 'b', M.Value);
    AssertEquals('2-byte cp byte Length', 4, M.Length);

    M := R.Match('a' + '€' + 'b');
    AssertTrue('3-byte cp Success', M.Success);
    AssertEquals('3-byte cp Value', 'a' + '€' + 'b', M.Value);
    AssertEquals('3-byte cp byte Length', 5, M.Length);
  finally
    R.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Commit 3 — backtracking-only features                               }
{ ------------------------------------------------------------------ }

procedure TRegexTests.TestBackreference;
var
  R: TRegex;
  M: TMatch;
begin
  AssertMatchAt('backref repeats group', '(a+)\1', 'xaaaay', 1, 'aaaa');
  AssertMatchAt('doubled word', '(\w+) \1', 'the the cat', 0, 'the the');
  AssertNoMatch('backref must match same text', '(a+)\1', 'xaby');

  R := TRegex.Create('(a)(b)\2\1');
  try
    M := R.Match('abba');
    AssertTrue('two backrefs', M.Success);
    AssertEquals('value', 'abba', M.Value);
  finally
    R.Free();
  end;

  { A group that did not participate makes its backreference fail. }
  AssertNoMatch('unparticipating group backref', '(x)?\1y', 'y');
end;

procedure TRegexTests.TestLookahead;
begin
  { Positive lookahead: assert without consuming. }
  AssertMatchAt('positive lookahead', 'foo(?=bar)', 'xfoobar', 1, 'foo');
  AssertNoMatch('positive lookahead fails', 'foo(?=bar)', 'foobaz');
  { The lookahead consumed nothing, so the following text is still available. }
  AssertMatchAt('lookahead zero-width', 'a(?=bc)bc', 'abc', 0, 'abc');
  { Negative lookahead. }
  AssertMatchAt('negative lookahead', 'foo(?!bar)', 'foobaz', 0, 'foo');
  AssertNoMatch('negative lookahead fails', 'foo(?!bar)', 'foobar');
end;

procedure TRegexTests.TestLookbehind;
begin
  { Positive lookbehind: assert what precedes, without consuming it. }
  AssertMatchAt('positive lookbehind', '(?<=foo)bar', 'foobar', 3, 'bar');
  AssertNoMatch('positive lookbehind fails', '(?<=foo)bar', 'bazbar');
  { Negative lookbehind. }
  AssertMatchAt('negative lookbehind', '(?<!foo)bar', 'bazbar', 3, 'bar');
  AssertNoMatch('negative lookbehind fails', '(?<!foo)bar', 'foobar');
  { Lookbehind at position 0 has nothing behind it. }
  AssertMatchAt('negative lookbehind at start', '(?<!x)a', 'ab', 0, 'a');
end;

procedure TRegexTests.TestAtomicGroup;
var
  R: TRegex;
begin
  { An atomic group discards its backtracking positions once it succeeds.
    (?>a+) grabs all the a's and will NOT give one back to let 'ab' match,
    so this fails where the plain (a+)b would succeed. }
  AssertNoMatch('atomic refuses to give back', '(?>a+)ab', 'aaab');
  AssertMatchAt('non-atomic gives back', '(a+)ab', 'aaab', 0, 'aaab');
  { Atomic still matches when no give-back is needed. }
  AssertMatchAt('atomic succeeds', '(?>a+)b', 'aaab', 0, 'aaab');

  { Atomic grouping is the cheap fix for catastrophic backtracking: this
    would blow the budget as (a+)+b but fails fast when made atomic. }
  R := TRegex.Create('(?>a+)+b');
  try
    R.StepLimit := 200000;
    AssertTrue('atomic avoids blowup', not R.IsMatch('aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa'));
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestPossessiveQuantifier;
begin
  { Possessive quantifiers are atomic groups in quantifier clothing. }
  AssertNoMatch('a*+ refuses give-back', 'a*+ab', 'aaab');
  AssertNoMatch('a++ refuses give-back', 'a++ab', 'aaab');
  AssertMatchAt('a++ succeeds', 'a++b', 'aaab', 0, 'aaab');
  AssertMatchAt('a?+ succeeds', 'a?+b', 'ab', 0, 'ab');
  { 'a?+' consumes at most ONE 'a' and will not give it back.  On 'aab' it
    takes the first 'a', leaving 'ab' for the rest of the pattern, so this
    DOES match — the give-back refusal only shows when the single 'a' is the
    one the tail needs.  On 'ab' there is no second 'a', so after 'a?+' has
    eaten the only one, 'ab' cannot match and the whole pattern fails. }
  AssertMatchAt('a?+ leaves the rest', 'a?+ab', 'aab', 0, 'aab');
  AssertNoMatch('a?+ refuses give-back', 'a?+ab', 'ab');
end;

{ ------------------------------------------------------------------ }
{ Commit 4 — convenience API                                          }
{ ------------------------------------------------------------------ }

procedure TRegexTests.TestMatches_AllNonOverlapping;
var
  R: TRegex;
  L: TList<TMatch>;
begin
  R := TRegex.Create('\d+');
  try
    L := R.Matches('a1bb22ccc333');
    try
      AssertEquals('count', 3, L.Count);
      AssertEquals('m0', '1', L.Get(0).Value);
      AssertEquals('m1', '22', L.Get(1).Value);
      AssertEquals('m2', '333', L.Get(2).Value);
      AssertEquals('m0 index', 1, L.Get(0).Index);
      AssertEquals('m1 index', 4, L.Get(1).Index);
      AssertEquals('m2 index', 9, L.Get(2).Index);
    finally
      L.Free();
    end;

    { No matches yields an empty list, not nil and not an exception. }
    L := R.Matches('abc');
    try
      AssertEquals('empty', 0, L.Count);
    finally
      L.Free();
    end;
  finally
    R.Free();
  end;

  { An empty match must still advance, or Matches would loop forever. }
  R := TRegex.Create('x*');
  try
    L := R.Matches('abc');
    try
      { One empty match at each of offsets 0,1,2 and one at the end. }
      AssertEquals('empty-match progress', 4, L.Count);
    finally
      L.Free();
    end;
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestMatches_ForIn;
var
  R: TRegex;
  L: TList<TMatch>;
  M: TMatch;
  Joined: string;
begin
  R := TRegex.Create('\d+');
  try
    L := R.Matches('a1bb22ccc333');
    try
      Joined := '';
      for M in L do
        Joined := Joined + M.Value + ';';
      AssertEquals('for-in over matches', '1;22;333;', Joined);
    finally
      L.Free();
    end;
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestReplace_GroupReferences;
var
  R: TRegex;
begin
  R := TRegex.Create('(\d+)-(\d+)-(\d+)');
  try
    AssertEquals('date reorder', '19/07/2026',
                 R.Replace('2026-07-19', '$3/$2/$1'));
  finally
    R.Free();
  end;

  R := TRegex.Create('(\w+) (\w+)');
  try
    AssertEquals('swap words', 'world hello',
                 R.Replace('hello world', '$2 $1'));
  finally
    R.Free();
  end;

  R := TRegex.Create('\d');
  try
    AssertEquals('replace all', 'a#b#c#', R.Replace('a1b2c3', '#'));
    AssertEquals('no match unchanged', 'xyz', R.Replace('xyz', '#'));
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestReplace_WholeMatchReference;
var
  R: TRegex;
begin
  R := TRegex.Create('\d+');
  try
    AssertEquals('$& whole match', 'a[12]b[345]',
                 R.Replace('a12b345', '[$&]'));
  finally
    R.Free();
  end;

  { '$$' is a literal dollar; an unknown '$x' stays verbatim. }
  R := TRegex.Create('a');
  try
    AssertEquals('escaped dollar', '$b', R.Replace('ab', '$$'));
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestSplit;
var
  R: TRegex;
  L: TList<String>;
begin
  R := TRegex.Create('\s*,\s*');
  try
    L := R.Split('a, b ,c,  d');
    try
      AssertEquals('count', 4, L.Count);
      AssertEquals('0', 'a', L[0]);
      AssertEquals('1', 'b', L[1]);
      AssertEquals('2', 'c', L[2]);
      AssertEquals('3', 'd', L[3]);
    finally
      L.Free();
    end;
  finally
    R.Free();
  end;

  { No separator found: one element, the whole input. }
  R := TRegex.Create(',');
  try
    L := R.Split('abc');
    try
      AssertEquals('no split count', 1, L.Count);
      AssertEquals('no split value', 'abc', L[0]);
    finally
      L.Free();
    end;

    { Leading and trailing separators produce empty elements. }
    L := R.Split(',a,');
    try
      AssertEquals('edge count', 3, L.Count);
      AssertEquals('leading empty', '', L[0]);
      AssertEquals('middle', 'a', L[1]);
      AssertEquals('trailing empty', '', L[2]);
    finally
      L.Free();
    end;
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestStaticReplaceAndSplit;
var
  L: TList<String>;
begin
  AssertEquals('static Replace', '19/07/2026',
               TRegex.Replace('2026-07-19', '(\d+)-(\d+)-(\d+)', '$3/$2/$1'));
  L := TRegex.Split('a,b,c', ',');
  try
    AssertEquals('static Split count', 3, L.Count);
    AssertEquals('static Split 1', 'b', L[1]);
  finally
    L.Free();
  end;
end;

{ ------------------------------------------------------------------ }
{ Unicode position                                                    }
{ ------------------------------------------------------------------ }

procedure TRegexTests.TestUtf8LiteralByteOffsets;
var
  R: TRegex;
  M: TMatch;
  Subject: string;
begin
  { A multi-byte literal in the pattern matches as a byte run, and every
    offset/length reported is a BYTE offset — consistent with Length/Pos/Copy.
    Subject: 'x' + U+00E9 (2 bytes) + 'y' + U+20AC (3 bytes) + 'z'. }
  Subject := 'x' + 'é' + 'y' + '€' + 'z';
  AssertEquals('subject byte length', 8, Length(Subject));

  R := TRegex.Create('€');
  try
    M := R.Match(Subject);
    AssertTrue('euro found', M.Success);
    AssertEquals('euro byte index', 4, M.Index);
    AssertEquals('euro byte length', 3, M.Length);
    AssertEquals('euro value byte-identical', '€', M.Value);
  finally
    R.Free();
  end;

  { A capture around multi-byte text is byte-identical to the source. }
  R := TRegex.Create('x(.+)z');
  try
    M := R.Match(Subject);
    AssertTrue('capture found', M.Success);
    AssertEquals('capture value', 'é' + 'y' + '€', M.GroupValue(1));
    AssertEquals('capture index', 1, M.Group(1).Index);
    AssertEquals('capture length', 6, M.Group(1).Length);
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestCharClass_NonAsciiRangeRejected;
var
  Raised: Boolean;
  R: TRegex;
begin
  { A range whose endpoints are not both ASCII cannot mean what the author
    intends under byte-oriented matching, so it is rejected outright rather
    than silently matching a byte range. }
  Raised := False;
  try
    R := TRegex.Create('[' + 'é' + '-' + 'ÿ' + ']');
    R.Free();
  except
    on E: ERegexSyntaxError do
      Raised := True;
  end;
  AssertTrue('non-ascii range rejected', Raised);

  { A non-ASCII byte as a plain class MEMBER is still allowed (it just
    matches that byte), so this must not raise. }
  R := TRegex.Create('[' + 'é' + 'a]+');
  try
    AssertTrue('non-ascii member allowed', R.IsMatch('a'));
  finally
    R.Free();
  end;
end;

procedure TRegexTests.TestRuntimeBuiltSubject;
var
  SB: TStringBuilder;
  Subject: string;
  R: TRegex;
  M: TMatch;
  L: TList<TMatch>;
  I: Int;
  Total: Int;
begin
  { Every test above matches against a string LITERAL, which the compiler can
    place in read-only data and whose bytes it knows statically.  The matcher
    reads its subject with Byte(S[I]), and that idiom has been observed to
    miscompile under the self-hosted native stage when the string is not a
    literal (see the StrAt/OrdAt note in CLAUDE.md).  This test therefore
    builds the subject AT RUNTIME through a TStringBuilder so the bytes are
    only known dynamically, and checks that matching still agrees exactly with
    the literal case.

    Subject: 'a1bb22ccc333' assembled byte by byte. }
  SB := TStringBuilder.Create();
  try
    SB.AppendByte(97);                                    { a }
    SB.AppendByte(49);                                    { 1 }
    SB.AppendByte(98); SB.AppendByte(98);                 { bb }
    SB.AppendByte(50); SB.AppendByte(50);                 { 22 }
    SB.AppendByte(99); SB.AppendByte(99); SB.AppendByte(99);   { ccc }
    SB.AppendByte(51); SB.AppendByte(51); SB.AppendByte(51);   { 333 }
    Subject := SB.ToString();
  finally
    SB.Free();
  end;

  AssertEquals('runtime subject length', 12, Length(Subject));
  AssertEquals('runtime subject equals the literal', 'a1bb22ccc333', Subject);

  { A byte read straight off the runtime-built string must give the character
    code, not a truncated or garbage value. }
  { Integer() around the byte read: the Byte-typed result matches several
    AssertEquals overloads equally well. }
  AssertEquals('first byte', 97, Int32(Byte(Subject[0])));
  AssertEquals('last byte', 51, Int32(Byte(Subject[11])));
  Total := 0;
  for I := 0 to Length(Subject) - 1 do
    Total := Total + Byte(Subject[I]);
  AssertEquals('byte sum', 892, Total);

  R := TRegex.Create('\d+');
  try
    M := R.Match(Subject);
    AssertTrue('match on runtime subject', M.Success);
    AssertEquals('index', 1, M.Index);
    AssertEquals('value', '1', M.Value);

    L := R.Matches(Subject);
    try
      AssertEquals('matches count', 3, L.Count);
      AssertEquals('m0', '1', L.Get(0).Value);
      AssertEquals('m1', '22', L.Get(1).Value);
      AssertEquals('m2', '333', L.Get(2).Value);
    finally
      L.Free();
    end;

    AssertEquals('replace on runtime subject', 'a#bb#ccc#',
                 R.Replace(Subject, '#'));
  finally
    R.Free();
  end;

  { And with a multi-byte codepoint assembled from raw bytes, so the UTF-8
    aware '.' is exercised on a non-literal subject too.  C3 A9 is U+00E9. }
  SB := TStringBuilder.Create();
  try
    SB.AppendByte(120);                                   { x }
    SB.AppendByte(195); SB.AppendByte(169);               { U+00E9 }
    SB.AppendByte(121);                                   { y }
    Subject := SB.ToString();
  finally
    SB.Free();
  end;
  AssertEquals('utf8 runtime subject length', 4, Length(Subject));

  R := TRegex.Create('x(.)y');
  try
    M := R.Match(Subject);
    AssertTrue('utf8 match on runtime subject', M.Success);
    AssertEquals('whole value', Subject, M.Value);
    { The dot consumed the whole 2-byte sequence, never half of it. }
    AssertEquals('group byte length', 2, M.Group(1).Length);
    AssertEquals('group index', 1, M.Group(1).Index);
  finally
    R.Free();
  end;
end;

initialization
  RegisterTest(TRegexTests);

end.
