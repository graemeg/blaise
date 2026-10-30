{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.strutils;

{ E2E tests for the StrUtils unit.
  Each test compiles a small Blaise program, links it against the RTL,
  executes it, and asserts on stdout.  All string positions and return
  values are 0-based, consistent with the Blaise string model. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EStrUtilsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    { ContainsStr / ContainsText }
    procedure TestRun_ContainsStr_Found;
    procedure TestRun_ContainsStr_NotFound;
    procedure TestRun_ContainsText_CaseInsensitive;

    { StartsStr / StartsText / EndsStr / EndsText }
    procedure TestRun_StartsStr_Matches;
    procedure TestRun_StartsStr_NoMatch;
    procedure TestRun_StartsText_CaseInsensitive;
    procedure TestRun_EndsStr_Matches;
    procedure TestRun_EndsStr_NoMatch;
    procedure TestRun_EndsText_CaseInsensitive;

    { LeftStr / RightStr / MidStr }
    procedure TestRun_LeftStr;
    procedure TestRun_RightStr;
    procedure TestRun_MidStr;
    procedure TestRun_LeftStr_LongerThanString;

    { PosEx }
    procedure TestRun_PosEx_Found;
    procedure TestRun_PosEx_SkipsBeforeStart;
    procedure TestRun_PosEx_NotFound;

    { IndexStr / IndexText }
    procedure TestRun_IndexStr_Found;
    procedure TestRun_IndexStr_NotFound;
    procedure TestRun_IndexText_CaseInsensitive;

    { Replace (first) / ReplaceAll }
    procedure TestRun_Replace_FirstOnly;
    procedure TestRun_Replace_NotFound;
    procedure TestRun_ReplaceAll_SingleOccurrence;
    procedure TestRun_ReplaceAll_MultipleOccurrences;
    procedure TestRun_ReplaceAll_EmptyOld;
    procedure TestRun_ReplaceAll_EmptyNew;

    { DupeString / ReverseString / StuffString }
    procedure TestRun_DupeString;
    procedure TestRun_DupeString_ZeroCount;
    procedure TestRun_ReverseString;
    procedure TestRun_StuffString_InsertReplace;

    { TrimLeft / TrimRight }
    procedure TestRun_TrimLeft;
    procedure TestRun_TrimRight;
    procedure TestRun_TrimLeft_NoLeadingSpace;

    { PadLeft / PadRight }
    procedure TestRun_PadLeft_Default;
    procedure TestRun_PadRight_Default;
    procedure TestRun_PadLeft_AlreadyWide;
    procedure TestRun_PadLeft_CustomPad;

    { CountOccurrences }
    procedure TestRun_CountOccurrences_Multiple;
    procedure TestRun_CountOccurrences_None;
    procedure TestRun_CountOccurrences_NonOverlapping;

    { RemovePrefix / RemoveSuffix }
    procedure TestRun_RemovePrefix_Present;
    procedure TestRun_RemovePrefix_Absent;
    procedure TestRun_RemoveSuffix_Present;
    procedure TestRun_RemoveSuffix_Absent;

    { IsEmptyOrWhitespace }
    procedure TestRun_IsEmptyOrWhitespace_Empty;
    procedure TestRun_IsEmptyOrWhitespace_Spaces;
    procedure TestRun_IsEmptyOrWhitespace_NonBlank;

    { JoinStr }
    procedure TestRun_JoinStr_Multiple;
    procedure TestRun_JoinStr_Single;
    procedure TestRun_JoinStr_EmptySep;

    { TStringBuilder }
    procedure TestRun_TStringBuilder_AppendAndToString;
    procedure TestRun_TStringBuilder_AppendLine;
    procedure TestRun_TStringBuilder_Clear;
    procedure TestRun_TStringBuilder_Length;
    procedure TestRun_TStringBuilder_AppendByte;
    procedure TestRun_TStringBuilder_SpeedVsConcat;

    { UTF-8 Codepoint functions }
    procedure TestRun_CodePointSize;
    procedure TestRun_CodePointLength_ASCII;
    procedure TestRun_CodePointLength_Mixed;
    procedure TestRun_CodePointAt_MultibytePos;
    procedure TestRun_CodePointCopy_Middle;
    procedure TestRun_CodePointPos_Found;
    procedure TestRun_CodePointFromByteIndex;
    procedure TestRun_CodePointByteIndex_Roundtrip;
    procedure TestRun_CodePointToString_ASCII;
    procedure TestRun_CodePointToString_TwoByteBytes;
    procedure TestRun_CodePointToString_Roundtrip;
    procedure TestRun_CodePointToString_OutOfRange;
  end;

implementation

procedure TE2EStrUtilsTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-strutils');
end;

{ ------------------------------------------------------------------ }
{ ContainsStr / ContainsText                                           }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_ContainsStr_Found;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin
      if ContainsStr('hello world', 'world') then WriteLn('yes')
                                              else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('found', 'yes', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_ContainsStr_NotFound;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin
      if ContainsStr('hello', 'xyz') then WriteLn('yes')
                                     else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('not found', 'no', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_ContainsText_CaseInsensitive;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin
      if ContainsText('Hello World', 'WORLD') then WriteLn('yes')
                                              else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('case insensitive', 'yes', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ StartsStr / StartsText / EndsStr / EndsText                          }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_StartsStr_Matches;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin
      if StartsStr('hel', 'hello') then WriteLn('yes') else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('starts match', 'yes', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_StartsStr_NoMatch;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin
      if StartsStr('world', 'hello') then WriteLn('yes') else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('starts no match', 'no', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_StartsText_CaseInsensitive;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin
      if StartsText('HEL', 'hello') then WriteLn('yes') else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('starts text', 'yes', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_EndsStr_Matches;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin
      if EndsStr('rld', 'world') then WriteLn('yes') else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('ends match', 'yes', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_EndsStr_NoMatch;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin
      if EndsStr('hello', 'world') then WriteLn('yes') else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('ends no match', 'no', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_EndsText_CaseInsensitive;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin
      if EndsText('RLD', 'world') then WriteLn('yes') else WriteLn('no')
    end.
    ''', Output, RCode));
  AssertEquals('ends text', 'yes', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ LeftStr / RightStr / MidStr                                          }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_LeftStr;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(LeftStr('hello', 3)) end.
    ''', Output, RCode));
  AssertEquals('hel', 'hel', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_RightStr;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(RightStr('hello', 3)) end.
    ''', Output, RCode));
  AssertEquals('llo', 'llo', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_MidStr;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(MidStr('hello', 1, 3)) end.
    ''', Output, RCode));
  AssertEquals('ell', 'ell', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_LeftStr_LongerThanString;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(LeftStr('hi', 100)) end.
    ''', Output, RCode));
  AssertEquals('hi', 'hi', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ PosEx                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_PosEx_Found;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(PosEx('l', 'hello', 0)) end.
    ''', Output, RCode));
  AssertEquals('first l at 2', '2', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_PosEx_SkipsBeforeStart;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(PosEx('l', 'hello', 3)) end.
    ''', Output, RCode));
  AssertEquals('second l at 3', '3', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_PosEx_NotFound;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(PosEx('z', 'hello', 0)) end.
    ''', Output, RCode));
  AssertEquals('not found = -1', '-1', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ IndexStr / IndexText                                                  }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_IndexStr_Found;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    var Arr: array[0..2] of string;
    begin
      Arr[0] := 'apple'; Arr[1] := 'banana'; Arr[2] := 'cherry';
      WriteLn(IndexStr('banana', Arr))
    end.
    ''', Output, RCode));
  AssertEquals('banana at index 1', '1', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_IndexStr_NotFound;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    var Arr: array[0..2] of string;
    begin
      Arr[0] := 'apple'; Arr[1] := 'banana'; Arr[2] := 'cherry';
      WriteLn(IndexStr('mango', Arr))
    end.
    ''', Output, RCode));
  AssertEquals('not found = -1', '-1', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_IndexText_CaseInsensitive;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    var Arr: array[0..2] of string;
    begin
      Arr[0] := 'Apple'; Arr[1] := 'Banana'; Arr[2] := 'Cherry';
      WriteLn(IndexText('BANANA', Arr))
    end.
    ''', Output, RCode));
  AssertEquals('BANANA matches Banana at 1', '1', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ Replace (first) / ReplaceAll                                         }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_Replace_FirstOnly;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(Replace('aabbaa', 'aa', 'X')) end.
    ''', Output, RCode));
  AssertEquals('only the first match replaced', 'Xbbaa', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_Replace_NotFound;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(Replace('hello', 'z', 'X')) end.
    ''', Output, RCode));
  AssertEquals('unchanged when not found', 'hello', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_ReplaceAll_SingleOccurrence;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(ReplaceAll('hello world', 'world', 'Blaise')) end.
    ''', Output, RCode));
  AssertEquals('hello Blaise', 'hello Blaise', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_ReplaceAll_MultipleOccurrences;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(ReplaceAll('aabbaa', 'aa', 'X')) end.
    ''', Output, RCode));
  AssertEquals('XbbX', 'XbbX', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_ReplaceAll_EmptyOld;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(ReplaceAll('hello', '', 'X')) end.
    ''', Output, RCode));
  AssertEquals('empty old returns unchanged', 'hello', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_ReplaceAll_EmptyNew;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(ReplaceAll('hello', 'l', '')) end.
    ''', Output, RCode));
  AssertEquals('heo', 'heo', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ DupeString / ReverseString / StuffString                             }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_DupeString;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(DupeString('ab', 3)) end.
    ''', Output, RCode));
  AssertEquals('ababab', 'ababab', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_DupeString_ZeroCount;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(DupeString('ab', 0)) end.
    ''', Output, RCode));
  AssertEquals('empty string', '', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_ReverseString;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(ReverseString('hello')) end.
    ''', Output, RCode));
  AssertEquals('olleh', 'olleh', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_StuffString_InsertReplace;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin
      { Delete 3 bytes at pos 1 ('ell'), insert 'a' → 'hao' }
      WriteLn(StuffString('hello', 1, 3, 'a'))
    end.
    ''', Output, RCode));
  AssertEquals('hao', 'hao', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ TrimLeft / TrimRight                                                  }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_TrimLeft;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn('|' + TrimLeft('   hello   ') + '|') end.
    ''', Output, RCode));
  AssertEquals('hello   (trailing intact)', '|hello   |', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_TrimRight;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn('|' + TrimRight('   hello   ') + '|') end.
    ''', Output, RCode));
  AssertEquals('   hello (leading intact)', '|   hello|', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_TrimLeft_NoLeadingSpace;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(TrimLeft('hello')) end.
    ''', Output, RCode));
  AssertEquals('hello unchanged', 'hello', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ PadLeft / PadRight                                                   }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_PadLeft_Default;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn('|' + PadLeft('42', 5) + '|') end.
    ''', Output, RCode));
  AssertEquals('   42', '|   42|', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_PadRight_Default;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn('|' + PadRight('hi', 6) + '|') end.
    ''', Output, RCode));
  AssertEquals('|hi    |', '|hi    |', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_PadLeft_AlreadyWide;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(PadLeft('hello', 3)) end.
    ''', Output, RCode));
  AssertEquals('hello unchanged', 'hello', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_PadLeft_CustomPad;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(PadLeft('7', 4, 48)) end.  { 48 = ord('0') }
    ''', Output, RCode));
  AssertEquals('0007', '0007', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ CountOccurrences                                                      }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_CountOccurrences_Multiple;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(CountOccurrences('l', 'hello world')) end.
    ''', Output, RCode));
  AssertEquals('3 occurrences of l', '3', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_CountOccurrences_None;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(CountOccurrences('z', 'hello')) end.
    ''', Output, RCode));
  AssertEquals('0 occurrences', '0', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_CountOccurrences_NonOverlapping;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(CountOccurrences('aa', 'aaaa')) end.
    ''', Output, RCode));
  AssertEquals('2 non-overlapping aa in aaaa', '2', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ RemovePrefix / RemoveSuffix                                           }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_RemovePrefix_Present;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(RemovePrefix('foobar', 'foo')) end.
    ''', Output, RCode));
  AssertEquals('bar', 'bar', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_RemovePrefix_Absent;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(RemovePrefix('foobar', 'baz')) end.
    ''', Output, RCode));
  AssertEquals('foobar unchanged', 'foobar', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_RemoveSuffix_Present;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(RemoveSuffix('foobar', 'bar')) end.
    ''', Output, RCode));
  AssertEquals('foo', 'foo', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_RemoveSuffix_Absent;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin WriteLn(RemoveSuffix('foobar', 'baz')) end.
    ''', Output, RCode));
  AssertEquals('foobar unchanged', 'foobar', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ IsEmptyOrWhitespace                                                  }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_IsEmptyOrWhitespace_Empty;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin
      if IsEmptyOrWhitespace('') then WriteLn('blank') else WriteLn('not blank')
    end.
    ''', Output, RCode));
  AssertEquals('blank', 'blank', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_IsEmptyOrWhitespace_Spaces;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin
      if IsEmptyOrWhitespace('   ') then WriteLn('blank') else WriteLn('not blank')
    end.
    ''', Output, RCode));
  AssertEquals('blank', 'blank', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_IsEmptyOrWhitespace_NonBlank;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    begin
      if IsEmptyOrWhitespace('  x  ') then WriteLn('blank') else WriteLn('not blank')
    end.
    ''', Output, RCode));
  AssertEquals('not blank', 'not blank', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ JoinStr                                                              }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_JoinStr_Multiple;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    var Parts: array[0..2] of string;
    begin
      Parts[0] := 'one'; Parts[1] := 'two'; Parts[2] := 'three';
      WriteLn(JoinStr(', ', Parts))
    end.
    ''', Output, RCode));
  AssertEquals('one, two, three', 'one, two, three', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_JoinStr_Single;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    var Parts: array[0..0] of string;
    begin
      Parts[0] := 'only';
      WriteLn(JoinStr('-', Parts))
    end.
    ''', Output, RCode));
  AssertEquals('only', 'only', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_JoinStr_EmptySep;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    var Parts: array[0..2] of string;
    begin
      Parts[0] := 'a'; Parts[1] := 'b'; Parts[2] := 'c';
      WriteLn(JoinStr('', Parts))
    end.
    ''', Output, RCode));
  AssertEquals('abc', 'abc', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ TStringBuilder                                                        }
{ ------------------------------------------------------------------ }

procedure TE2EStrUtilsTests.TestRun_TStringBuilder_AppendAndToString;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    var SB: TStringBuilder;
    begin
      SB := TStringBuilder.Create();
      SB.Append('hello');
      SB.Append(' ');
      SB.Append('world');
      WriteLn(SB.ToString());
      SB.Free()
    end.
    ''', Output, RCode));
  AssertEquals('hello world', 'hello world', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_TStringBuilder_AppendLine;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    var SB: TStringBuilder; S: string;
    begin
      SB := TStringBuilder.Create();
      SB.AppendLine('line1');
      SB.AppendLine('line2');
      S := SB.ToString();
      Write(S);
      SB.Free()
    end.
    ''', Output, RCode));
  AssertEquals('two lines', 'line1' + #10 + 'line2' + #10, Output);
end;

procedure TE2EStrUtilsTests.TestRun_TStringBuilder_Clear;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    var SB: TStringBuilder;
    begin
      SB := TStringBuilder.Create();
      SB.Append('old content');
      SB.Clear();
      SB.Append('new');
      WriteLn(SB.ToString());
      SB.Free()
    end.
    ''', Output, RCode));
  AssertEquals('new', 'new', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_TStringBuilder_Length;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    var SB: TStringBuilder;
    begin
      SB := TStringBuilder.Create();
      SB.Append('hello');
      WriteLn(SB.Length);
      SB.Free()
    end.
    ''', Output, RCode));
  AssertEquals('length 5', '5', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_TStringBuilder_AppendByte;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    var SB: TStringBuilder;
    begin
      SB := TStringBuilder.Create();
      SB.AppendByte(65);  { A }
      SB.AppendByte(66);  { B }
      SB.AppendByte(67);  { C }
      WriteLn(SB.ToString());
      SB.Free()
    end.
    ''', Output, RCode));
  AssertEquals('ABC', 'ABC', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_TStringBuilder_SpeedVsConcat;
{ Verifies that TStringBuilder produces correct output for a non-trivial
  number of appends — exercises the Grow path. }
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(
    '''
    program P; uses StrUtils;
    var SB: TStringBuilder; I: Integer;
    begin
      SB := TStringBuilder.Create();
      for I := 1 to 1000 do
        SB.Append('x');
      WriteLn(SB.Length);
      SB.Free()
    end.
    ''', Output, RCode));
  AssertEquals('1000 chars', '1000', Trim(Output));
end;

{ ------------------------------------------------------------------ }
{ UTF-8 Codepoint functions                                            }
{ ------------------------------------------------------------------ }

const
  SrcCodePointSize = '''
    program P;
    uses StrUtils;
    begin
      WriteLn(CodePointSize(65));
      WriteLn(CodePointSize(195));
      WriteLn(CodePointSize(226));
      WriteLn(CodePointSize(240))
    end.
    ''';

  SrcCodePointLengthASCII = '''
    program P;
    uses StrUtils;
    begin
      WriteLn(CodePointLength('Hello'))
    end.
    ''';

  { Chr(195)+Chr(162) = UTF-8 for 'â' (U+00E2) — so S = 'Pâques' (6 codepoints, 7 bytes) }
  SrcCodePointLengthMixed = '''
    program P;
    uses StrUtils;
    var S: string;
    begin
      S := 'P' + Chr(195) + Chr(162) + 'ques';
      WriteLn(CodePointLength(S))
    end.
    ''';

  { S = 'Pâques': CP[0]=80 (P), CP[1]=226 (â), CP[2]=113 (q) }
  SrcCodePointAtMultibyte = '''
    program P;
    uses StrUtils;
    var S: string;
    begin
      S := 'P' + Chr(195) + Chr(162) + 'ques';
      WriteLn(CodePointAt(S, 0));
      WriteLn(CodePointAt(S, 1));
      WriteLn(CodePointAt(S, 2))
    end.
    ''';

  { S = 'Pâques': CodePointCopy(S,1,1) extracts 'â' = 2 bytes (0xC3, 0xA2) }
  SrcCodePointCopyMiddle = '''
    program P;
    uses StrUtils;
    var S, R: string;
    begin
      S := 'P' + Chr(195) + Chr(162) + 'ques';
      R := CodePointCopy(S, 1, 1);
      WriteLn(Length(R));
      WriteLn(OrdAt(R, 0));
      WriteLn(OrdAt(R, 1))
    end.
    ''';

  { S = 'Pâques': 'ques' starts at codepoint index 2 }
  SrcCodePointPosFound = '''
    program P;
    uses StrUtils;
    var S: string;
    begin
      S := 'P' + Chr(195) + Chr(162) + 'ques';
      WriteLn(CodePointPos('ques', S))
    end.
    ''';

  { S = 'Pâques': byte index 1 = start of 'â' (U+00E2 = codepoint 226) }
  SrcCodePointFromByteIndex = '''
    program P;
    uses StrUtils;
    var S: string;
    begin
      S := 'P' + Chr(195) + Chr(162) + 'ques';
      WriteLn(CodePointFromByteIndex(S, 1))
    end.
    ''';

  { S = 'Pâques': CP[0] at byte 0, CP[1] at byte 1, CP[2] at byte 3 }
  SrcCodePointByteIndexRoundtrip = '''
    program P;
    uses StrUtils;
    var S: string;
    begin
      S := 'P' + Chr(195) + Chr(162) + 'ques';
      WriteLn(CodePointByteIndex(S, 0));
      WriteLn(CodePointByteIndex(S, 1));
      WriteLn(CodePointByteIndex(S, 2))
    end.
    ''';

  { ASCII codepoint 'A' (65) must encode to a single byte. }
  SrcCodePointToStringASCII = '''
    program P;
    uses StrUtils;
    var S: string;
    begin
      S := CodePointToString(65);
      WriteLn(Length(S));
      WriteLn(OrdAt(S, 0))
    end.
    ''';

  { Codepoint U+00B1 (177, '±') must encode to the two UTF-8 bytes
    0xC2 0xB1 = 194, 177. }
  SrcCodePointToStringTwoByteBytes = '''
    program P;
    uses StrUtils;
    var S: string;
    begin
      S := CodePointToString(177);
      WriteLn(Length(S));
      WriteLn(OrdAt(S, 0));
      WriteLn(OrdAt(S, 1))
    end.
    ''';

  { CodePointToString is the inverse of CodePointFromByteIndex across a
    representative codepoint from each UTF-8 length class. }
  SrcCodePointToStringRoundtrip = '''
    program P;
    uses StrUtils;
    begin
      WriteLn(CodePointFromByteIndex(CodePointToString(65), 0));
      WriteLn(CodePointFromByteIndex(CodePointToString(177), 0));
      WriteLn(CodePointFromByteIndex(CodePointToString(8364), 0));
      WriteLn(CodePointFromByteIndex(CodePointToString(128512), 0))
    end.
    ''';

  { Out-of-range codepoints yield an empty string. }
  SrcCodePointToStringOutOfRange = '''
    program P;
    uses StrUtils;
    begin
      WriteLn(Length(CodePointToString(-1)));
      WriteLn(Length(CodePointToString(1114112)))
    end.
    ''';

procedure TE2EStrUtilsTests.TestRun_CodePointSize;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCodePointSize, Output, RCode));
  AssertEquals('sizes', '1' + Chr(10) + '2' + Chr(10) + '3' + Chr(10) + '4', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_CodePointLength_ASCII;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCodePointLengthASCII, Output, RCode));
  AssertEquals('length', '5', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_CodePointLength_Mixed;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCodePointLengthMixed, Output, RCode));
  AssertEquals('length', '6', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_CodePointAt_MultibytePos;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCodePointAtMultibyte, Output, RCode));
  AssertEquals('codepoints', '80' + Chr(10) + '226' + Chr(10) + '113', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_CodePointCopy_Middle;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCodePointCopyMiddle, Output, RCode));
  AssertEquals('copy bytes', '2' + Chr(10) + '195' + Chr(10) + '162', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_CodePointPos_Found;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCodePointPosFound, Output, RCode));
  AssertEquals('pos', '2', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_CodePointFromByteIndex;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCodePointFromByteIndex, Output, RCode));
  AssertEquals('codepoint', '226', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_CodePointByteIndex_Roundtrip;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCodePointByteIndexRoundtrip, Output, RCode));
  AssertEquals('byte indices', '0' + Chr(10) + '1' + Chr(10) + '3', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_CodePointToString_ASCII;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCodePointToStringASCII, Output, RCode));
  AssertEquals('len+byte', '1' + Chr(10) + '65', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_CodePointToString_TwoByteBytes;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCodePointToStringTwoByteBytes, Output, RCode));
  AssertEquals('len+bytes', '2' + Chr(10) + '194' + Chr(10) + '177', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_CodePointToString_Roundtrip;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCodePointToStringRoundtrip, Output, RCode));
  AssertEquals('codepoints',
    '65' + Chr(10) + '177' + Chr(10) + '8364' + Chr(10) + '128512', Trim(Output));
end;

procedure TE2EStrUtilsTests.TestRun_CodePointToString_OutOfRange;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcCodePointToStringOutOfRange, Output, RCode));
  AssertEquals('empty', '0' + Chr(10) + '0', Trim(Output));
end;

initialization
  RegisterTest(TE2EStrUtilsTests);

end.
