{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.lexer;

interface

uses
  blaise.testing,
  uLexer, uStrCompat, SysUtils;

type
  TLexerTests = class(TTestCase)
  private
    FLexer: TLexer;
    procedure SetLexer(const ASource: string);
  protected
    procedure TearDown; override;
  published
    { EOF and whitespace }
    procedure TestEmptySource_ReturnsEOF;
    procedure TestWhitespaceOnly_ReturnsEOF;

    { Comment skipping }
    procedure TestLineComment_Skipped;
    procedure TestBlockComment_Skipped;
    procedure TestBlockComment_MultiLine_Skipped;
    procedure TestBlockComment_UTF8Bytes_Skipped;
    procedure TestLineComment_UTF8Bytes_Skipped;
    procedure TestParenStarComment_UTF8Bytes_Skipped;
    procedure TestBlockComment_UTF8_FollowedByCode;

    { Keywords }
    procedure TestKeyword_Program;
    procedure TestKeyword_Uses;
    procedure TestKeyword_Var;
    procedure TestKeyword_Begin;
    procedure TestKeyword_End;
    procedure TestKeywords_CaseInsensitive;
    procedure TestIdent_NotKeyword_Prefix;

    { Inline assembler blocks — asm ... end captured as one raw-text token }
    procedure TestAsmBlock_CapturesRawText;
    procedure TestAsmBlock_EndMentionedInComment_NotTerminator;
    procedure TestAsmBlock_FollowedByDecl_StopsAtEnd;

    { Identifiers }
    procedure TestIdent_Simple;
    procedure TestIdent_WithUnderscore;
    procedure TestIdent_WithDigits;

    { Integer literals — decimal }
    procedure TestIntLit_SingleDigit;
    procedure TestIntLit_MultiDigit;

    { Integer literals — hex }
    procedure TestIntLit_Hex_Lowercase;
    procedure TestIntLit_Hex_Uppercase;
    procedure TestIntLit_Hex_WithUnderscore;

    { Integer literals — binary }
    procedure TestIntLit_Binary;
    procedure TestIntLit_Binary_WithUnderscore;

    { Integer literals — octal }
    procedure TestIntLit_Octal;
    procedure TestIntLit_Octal_WithUnderscore;

    { Integer literals — decimal with underscores }
    procedure TestIntLit_Decimal_WithUnderscore;
    procedure TestIntLit_Decimal_MultipleUnderscores;

    { Float literals — with underscores }
    procedure TestFloatLit_WithUnderscore;

    { String literals }
    procedure TestStringLit_Simple;
    procedure TestStringLit_Empty;
    procedure TestStringLit_EmbeddedQuote;
    { #nnnn / #$hhhh Unicode codepoint -> UTF-8 string literals }
    procedure TestCodepoint_DecimalAscii;
    procedure TestCodepoint_HexBmp_ThreeBytes;
    procedure TestCodepoint_HexAstral_FourBytes;
    procedure TestCodepoint_MergesWithStringAndEachOther;

    { Operators and punctuation }
    procedure TestOp_Plus;
    procedure TestOp_Minus;
    procedure TestOp_Star;
    procedure TestOp_Slash;
    procedure TestOp_Assign;
    procedure TestOp_Colon;
    procedure TestOp_LParen;
    procedure TestOp_RParen;
    procedure TestOp_Comma;
    procedure TestOp_Semicolon;
    procedure TestOp_Dot;

    { Position tracking }
    procedure TestLineTracking_SecondLine;
    procedure TestColTracking_AfterSpaces;

    { Token sequences }
    procedure TestSeq_VarDecl;
    procedure TestSeq_Assignment;
    procedure TestSeq_ProcCall;

    { Conditional compilation (issue #131) }
    procedure TestIfdef_PredefinedBlaise_KeepsBody;
    procedure TestIfdef_Undefined_TakesElse;
    procedure TestIfndef_Undefined_KeepsBody;
    procedure TestDefine_ThenIfdef_KeepsBody;
    procedure TestUndef_ThenIfdef_TakesElse;
    procedure TestAddDefine_KeepsBody;
  end;

  TParseIntLiteralTests = class(TTestCase)
  published
    { Decimal }
    procedure TestDecimal_Simple;
    procedure TestDecimal_WithUnderscore;
    procedure TestDecimal_MultipleUnderscores;
    { Hex }
    procedure TestHex_Simple;
    procedure TestHex_WithUnderscore;
    { Binary }
    procedure TestBinary_Simple;
    procedure TestBinary_WithUnderscore;
    { Octal }
    procedure TestOctal_Simple;
    procedure TestOctal_WithUnderscore;
    { Invalid underscore placement }
    procedure TestInvalid_TrailingUnderscore;
    procedure TestInvalid_LeadingUnderscoreAfterPrefix;
  end;

implementation

procedure TLexerTests.SetLexer(const ASource: string);
begin
  FLexer.Free();
  FLexer := nil;
  FLexer := TLexer.Create(ASource);
end;

procedure TLexerTests.TearDown;
begin
  FLexer.Free();
  FLexer := nil;
end;

{ EOF and whitespace }

procedure TLexerTests.TestEmptySource_ReturnsEOF;
var
  tok: TToken;
begin
  SetLexer('');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkEOF), Ord(tok.Kind));
end;

procedure TLexerTests.TestWhitespaceOnly_ReturnsEOF;
var
  tok: TToken;
begin
  SetLexer('   ' + #10 + '  ');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkEOF), Ord(tok.Kind));
end;

{ Comment skipping }

procedure TLexerTests.TestLineComment_Skipped;
var
  tok: TToken;
begin
  SetLexer('// comment' + #10 + 'begin');
  tok := FLexer.Next();
  AssertEquals('Kind after //', Ord(tkBegin), Ord(tok.Kind));
end;

procedure TLexerTests.TestBlockComment_Skipped;
var
  tok: TToken;
begin
  SetLexer('{ comment } begin');
  tok := FLexer.Next();
  AssertEquals('Kind after {}', Ord(tkBegin), Ord(tok.Kind));
end;

procedure TLexerTests.TestBlockComment_MultiLine_Skipped;
var
  tok: TToken;
begin
  SetLexer('{ line one' + #10 + '  line two }' + #10 + 'end');
  tok := FLexer.Next();
  AssertEquals('Kind after multiline {}', Ord(tkEnd), Ord(tok.Kind));
end;

procedure TLexerTests.TestBlockComment_UTF8Bytes_Skipped;
var
  tok: TToken;
begin
  (* U+00B1 PLUS-MINUS SIGN, U+2264 LESS-THAN-OR-EQUAL, U+1F600 GRINNING FACE.
    High UTF-8 bytes inside a brace comment must not disturb the token stream. *)
  SetLexer('{ tolerance: ' + #$C2#$B1 + ' x, ' + #$E2#$89#$A4 + ' y, ' +
           #$F0#$9F#$98#$80 + ' z } begin');
  tok := FLexer.Next();
  AssertEquals('Kind after {} with UTF-8', Ord(tkBegin), Ord(tok.Kind));
end;

procedure TLexerTests.TestLineComment_UTF8Bytes_Skipped;
var
  tok: TToken;
begin
  SetLexer('// note: ' + #$E2#$86#$92 + ' arrow, ' + #$F0#$9F#$98#$80 + ' emoji' +
           #10 + 'end');
  tok := FLexer.Next();
  AssertEquals('Kind after // with UTF-8', Ord(tkEnd), Ord(tok.Kind));
end;

procedure TLexerTests.TestParenStarComment_UTF8Bytes_Skipped;
var
  tok: TToken;
begin
  SetLexer('(* note ' + #$C2#$B1 + ' epsilon ' + #$E2#$89#$A4 + ' bound *) end');
  tok := FLexer.Next();
  AssertEquals('Kind after (* *) with UTF-8', Ord(tkEnd), Ord(tok.Kind));
end;

procedure TLexerTests.TestBlockComment_UTF8_FollowedByCode;
var
  tok: TToken;
begin
  { Regression: high UTF-8 continuation bytes used to leak into the next
    token boundary, causing spurious identifiers after the comment closed.
    Verify the identifier following the comment lexes cleanly. }
  SetLexer('{ ' + #$C2#$B1 + ' }' + #10 + 'foo');
  tok := FLexer.Next();
  AssertEquals('Kind after UTF-8 comment', Ord(tkIdent), Ord(tok.Kind));
  AssertEquals('Value after UTF-8 comment', 'foo', tok.Value);
end;

{ Keywords }

procedure TLexerTests.TestKeyword_Program;
var
  tok: TToken;
begin
  SetLexer('program');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkProgram), Ord(tok.Kind));
  AssertEquals('Value', 'program', tok.Value);
end;

procedure TLexerTests.TestKeyword_Uses;
var
  tok: TToken;
begin
  SetLexer('uses');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkUses), Ord(tok.Kind));
end;

procedure TLexerTests.TestKeyword_Var;
var
  tok: TToken;
begin
  SetLexer('var');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkVar), Ord(tok.Kind));
end;

procedure TLexerTests.TestKeyword_Begin;
var
  tok: TToken;
begin
  SetLexer('begin');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkBegin), Ord(tok.Kind));
end;

procedure TLexerTests.TestKeyword_End;
var
  tok: TToken;
begin
  SetLexer('end');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkEnd), Ord(tok.Kind));
end;

procedure TLexerTests.TestKeywords_CaseInsensitive;
var
  tok: TToken;
begin
  SetLexer('BEGIN');
  tok := FLexer.Next();
  AssertEquals('Uppercase BEGIN', Ord(tkBegin), Ord(tok.Kind));

  SetLexer('End');
  tok := FLexer.Next();
  AssertEquals('Mixed End', Ord(tkEnd), Ord(tok.Kind));

  SetLexer('PROGRAM');
  tok := FLexer.Next();
  AssertEquals('Uppercase PROGRAM', Ord(tkProgram), Ord(tok.Kind));
end;

procedure TLexerTests.TestIdent_NotKeyword_Prefix;
var
  tok: TToken;
begin
  { "beginning" starts with "begin" but is not a keyword }
  SetLexer('beginning');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIdent), Ord(tok.Kind));
  AssertEquals('Value', 'beginning', tok.Value);
end;

{ Inline assembler blocks }

procedure TLexerTests.TestAsmBlock_CapturesRawText;
var
  tok: TToken;
begin
  { An asm ... end block is returned as ONE tkAsmBlock token whose Value is
    the verbatim text between (exclusive) the asm keyword and the end keyword. }
  SetLexer('asm' + #10 + '  movl %eax, %ebx' + #10 + '  ret' + #10 + 'end');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkAsmBlock), Ord(tok.Kind));
  AssertTrue('has movl', Pos('movl %eax, %ebx', tok.Value) >= 0);
  AssertTrue('has ret', Pos('ret', tok.Value) >= 0);
  AssertTrue('no trailing end keyword captured', Pos('end', tok.Value) < 0);
end;

procedure TLexerTests.TestAsmBlock_EndMentionedInComment_NotTerminator;
var
  tok: TToken;
begin
  { 'end' appearing inside a # line comment must NOT terminate the block —
    only a standalone end keyword does. }
  SetLexer('asm' + #10 + '  ret  # this ends the block' + #10 + 'end');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkAsmBlock), Ord(tok.Kind));
  AssertTrue('comment text preserved', Pos('this ends the block', tok.Value) >= 0);
  AssertTrue('has ret', Pos('ret', tok.Value) >= 0);
end;

procedure TLexerTests.TestAsmBlock_FollowedByDecl_StopsAtEnd;
var
  tok: TToken;
begin
  { After the block's end, normal tokenising resumes — the trailing ';' and the
    next token are produced as usual. }
  SetLexer('asm' + #10 + '  ret' + #10 + 'end; begin');
  tok := FLexer.Next();
  AssertEquals('asm block', Ord(tkAsmBlock), Ord(tok.Kind));
  tok := FLexer.Next();
  AssertEquals('semicolon after end', Ord(tkSemicolon), Ord(tok.Kind));
  tok := FLexer.Next();
  AssertEquals('begin resumes', Ord(tkBegin), Ord(tok.Kind));
end;

{ Identifiers }

procedure TLexerTests.TestIdent_Simple;
var
  tok: TToken;
begin
  SetLexer('Hello');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIdent), Ord(tok.Kind));
  AssertEquals('Value', 'Hello', tok.Value);
end;

procedure TLexerTests.TestIdent_WithUnderscore;
var
  tok: TToken;
begin
  SetLexer('_myVar');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIdent), Ord(tok.Kind));
  AssertEquals('Value', '_myVar', tok.Value);
end;

procedure TLexerTests.TestIdent_WithDigits;
var
  tok: TToken;
begin
  SetLexer('item2');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIdent), Ord(tok.Kind));
  AssertEquals('Value', 'item2', tok.Value);
end;

{ Integer literals }

procedure TLexerTests.TestIntLit_SingleDigit;
var
  tok: TToken;
begin
  SetLexer('7');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIntLit), Ord(tok.Kind));
  AssertEquals('Value', '7', tok.Value);
end;

procedure TLexerTests.TestIntLit_MultiDigit;
var
  tok: TToken;
begin
  SetLexer('42');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIntLit), Ord(tok.Kind));
  AssertEquals('Value', '42', tok.Value);
end;

{ String literals }

procedure TLexerTests.TestStringLit_Simple;
var
  tok: TToken;
begin
  SetLexer('''hello''');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', 'hello', tok.Value);
end;

procedure TLexerTests.TestStringLit_Empty;
var
  tok: TToken;
begin
  SetLexer('''''');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', '', tok.Value);
end;

procedure TLexerTests.TestStringLit_EmbeddedQuote;
var
  tok: TToken;
begin
  { Pascal ''it''''s'' represents it's }
  SetLexer('''it''''s''');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', 'it''s', tok.Value);
end;

{ #nnnn / #$hhhh Unicode codepoint -> UTF-8 string literals }

procedure TLexerTests.TestCodepoint_DecimalAscii;
var tok: TToken;
begin
  SetLexer('#65');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', 'A', tok.Value);   { codepoint 65 -> 1 byte $41 }
end;

procedure TLexerTests.TestCodepoint_HexBmp_ThreeBytes;
var tok: TToken;
begin
  SetLexer('#$20AC');   { EURO SIGN -> UTF-8 E2 82 AC }
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('len', 3, Length(tok.Value));
  AssertEquals('Value', Chr($E2) + Chr($82) + Chr($AC), tok.Value);
end;

procedure TLexerTests.TestCodepoint_HexAstral_FourBytes;
var tok: TToken;
begin
  SetLexer('#$1F600');  { GRINNING FACE -> UTF-8 F0 9F 98 80 }
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('len', 4, Length(tok.Value));
  AssertEquals('Value', Chr($F0) + Chr($9F) + Chr($98) + Chr($80), tok.Value);
end;

procedure TLexerTests.TestCodepoint_MergesWithStringAndEachOther;
var tok: TToken;
begin
  { Adjacent # and '...' literals merge into one compile-time string. }
  SetLexer('#72#73''!''');   { 'H' 'I' '!' }
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkStringLit), Ord(tok.Kind));
  AssertEquals('Value', 'HI!', tok.Value);
end;

{ Operators and punctuation }

procedure TLexerTests.TestOp_Plus;
var
  tok: TToken;
begin
  SetLexer('+');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkPlus), Ord(tok.Kind));
end;

procedure TLexerTests.TestOp_Minus;
var
  tok: TToken;
begin
  SetLexer('-');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkMinus), Ord(tok.Kind));
end;

procedure TLexerTests.TestOp_Star;
var
  tok: TToken;
begin
  SetLexer('*');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkStar), Ord(tok.Kind));
end;

procedure TLexerTests.TestOp_Slash;
var
  tok: TToken;
begin
  SetLexer('/');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkSlash), Ord(tok.Kind));
end;

procedure TLexerTests.TestOp_Assign;
var
  tok: TToken;
begin
  SetLexer(':=');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkAssign), Ord(tok.Kind));
  AssertEquals('Value', ':=', tok.Value);
end;

procedure TLexerTests.TestOp_Colon;
var
  tok: TToken;
begin
  SetLexer(':');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkColon), Ord(tok.Kind));
end;

procedure TLexerTests.TestOp_LParen;
var
  tok: TToken;
begin
  SetLexer('(');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkLParen), Ord(tok.Kind));
end;

procedure TLexerTests.TestOp_RParen;
var
  tok: TToken;
begin
  SetLexer(')');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkRParen), Ord(tok.Kind));
end;

procedure TLexerTests.TestOp_Comma;
var
  tok: TToken;
begin
  SetLexer(',');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkComma), Ord(tok.Kind));
end;

procedure TLexerTests.TestOp_Semicolon;
var
  tok: TToken;
begin
  SetLexer(';');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkSemicolon), Ord(tok.Kind));
end;

procedure TLexerTests.TestOp_Dot;
var
  tok: TToken;
begin
  SetLexer('.');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkDot), Ord(tok.Kind));
end;

{ Position tracking }

procedure TLexerTests.TestLineTracking_SecondLine;
var
  tok: TToken;
begin
  SetLexer('begin' + #10 + 'end');
  tok := FLexer.Next();
  AssertEquals('begin line', 1, tok.Line);
  tok := FLexer.Next();
  AssertEquals('end line', 2, tok.Line);
end;

procedure TLexerTests.TestColTracking_AfterSpaces;
var
  tok: TToken;
begin
  SetLexer('  begin');
  tok := FLexer.Next();
  AssertEquals('begin col', 3, tok.Col);
end;

{ Token sequences }

procedure TLexerTests.TestSeq_VarDecl;
var
  t: array[0..3] of TToken;
  i: Integer;
begin
  SetLexer('x : Integer');
  for i := 0 to 3 do
    t[i] := FLexer.Next();
  AssertEquals('x kind', Ord(tkIdent), Ord(t[0].Kind));
  AssertEquals('x value', 'x', t[0].Value);
  AssertEquals(': kind', Ord(tkColon), Ord(t[1].Kind));
  AssertEquals('Integer kind', Ord(tkIdent), Ord(t[2].Kind));
  AssertEquals('Integer value', 'Integer', t[2].Value);
  AssertEquals('EOF', Ord(tkEOF), Ord(t[3].Kind));
end;

procedure TLexerTests.TestSeq_Assignment;
var
  t: array[0..3] of TToken;
  i: Integer;
begin
  SetLexer('x := 42');
  for i := 0 to 3 do
    t[i] := FLexer.Next();
  AssertEquals('x', Ord(tkIdent), Ord(t[0].Kind));
  AssertEquals(':=', Ord(tkAssign), Ord(t[1].Kind));
  AssertEquals('42 kind', Ord(tkIntLit), Ord(t[2].Kind));
  AssertEquals('42 value', '42', t[2].Value);
  AssertEquals('EOF', Ord(tkEOF), Ord(t[3].Kind));
end;

procedure TLexerTests.TestSeq_ProcCall;
var
  t: array[0..4] of TToken;
  i: Integer;
begin
  SetLexer('WriteLn(''hi'')');
  for i := 0 to 4 do
    t[i] := FLexer.Next();
  AssertEquals('WriteLn kind', Ord(tkIdent), Ord(t[0].Kind));
  AssertEquals('( kind', Ord(tkLParen), Ord(t[1].Kind));
  AssertEquals('str kind', Ord(tkStringLit), Ord(t[2].Kind));
  AssertEquals('str value', 'hi', t[2].Value);
  AssertEquals(') kind', Ord(tkRParen), Ord(t[3].Kind));
  AssertEquals('EOF', Ord(tkEOF), Ord(t[4].Kind));
end;

{ Conditional compilation (issue #131).  Each lexes a snippet with an
  IFDEF/ELSE/ENDIF and asserts which identifier survives — proving which branch
  the lexer kept. }

procedure TLexerTests.TestIfdef_PredefinedBlaise_KeepsBody;
var tok: TToken;
begin
  { BLAISE is always predefined, so the IFDEF body (yes) is kept. }
  SetLexer('{$IFDEF BLAISE}yes{$ELSE}no{$ENDIF}');
  tok := FLexer.Next();
  AssertEquals('kept branch', 'yes', tok.Value);
end;

procedure TLexerTests.TestIfdef_Undefined_TakesElse;
var tok: TToken;
begin
  SetLexer('{$IFDEF NOPE}yes{$ELSE}no{$ENDIF}');
  tok := FLexer.Next();
  AssertEquals('else branch', 'no', tok.Value);
end;

procedure TLexerTests.TestIfndef_Undefined_KeepsBody;
var tok: TToken;
begin
  SetLexer('{$IFNDEF NOPE}yes{$ELSE}no{$ENDIF}');
  tok := FLexer.Next();
  AssertEquals('ifndef body', 'yes', tok.Value);
end;

procedure TLexerTests.TestDefine_ThenIfdef_KeepsBody;
var tok: TToken;
begin
  SetLexer('{$DEFINE FOO}{$IFDEF FOO}yes{$ELSE}no{$ENDIF}');
  tok := FLexer.Next();
  AssertEquals('defined body', 'yes', tok.Value);
end;

procedure TLexerTests.TestUndef_ThenIfdef_TakesElse;
var tok: TToken;
begin
  { UNDEF removes a predefined symbol, so the ELSE branch is taken. }
  SetLexer('{$UNDEF BLAISE}{$IFDEF BLAISE}yes{$ELSE}no{$ENDIF}');
  tok := FLexer.Next();
  AssertEquals('undefed body', 'no', tok.Value);
end;

procedure TLexerTests.TestAddDefine_KeepsBody;
var tok: TToken;
begin
  { AddDefine mirrors the -d command-line flag.  SetLexer creates the lexer;
    AddDefine then defines DEBUG so the IFDEF body is kept. }
  SetLexer('{$IFDEF DEBUG}yes{$ELSE}no{$ENDIF}');
  FLexer.AddDefine('DEBUG');
  tok := FLexer.Next();
  AssertEquals('cli-defined body', 'yes', tok.Value);
end;

{ Hex literals }

procedure TLexerTests.TestIntLit_Hex_Lowercase;
var tok: TToken;
begin
  SetLexer('$ff');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIntLit), Ord(tok.Kind));
  AssertEquals('Value', '$ff', tok.Value);
end;

procedure TLexerTests.TestIntLit_Hex_Uppercase;
var tok: TToken;
begin
  SetLexer('$FF');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIntLit), Ord(tok.Kind));
  AssertEquals('Value', '$FF', tok.Value);
end;

procedure TLexerTests.TestIntLit_Hex_WithUnderscore;
var tok: TToken;
begin
  SetLexer('$FF_EC');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIntLit), Ord(tok.Kind));
  AssertEquals('Value', '$FF_EC', tok.Value);
end;

{ Binary literals }

procedure TLexerTests.TestIntLit_Binary;
var tok: TToken;
begin
  SetLexer('%11111111');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIntLit), Ord(tok.Kind));
  AssertEquals('Value', '%11111111', tok.Value);
end;

procedure TLexerTests.TestIntLit_Binary_WithUnderscore;
var tok: TToken;
begin
  SetLexer('%0010_0101');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIntLit), Ord(tok.Kind));
  AssertEquals('Value', '%0010_0101', tok.Value);
end;

{ Octal literals }

procedure TLexerTests.TestIntLit_Octal;
var tok: TToken;
begin
  SetLexer('&377');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIntLit), Ord(tok.Kind));
  AssertEquals('Value', '&377', tok.Value);
end;

procedure TLexerTests.TestIntLit_Octal_WithUnderscore;
var tok: TToken;
begin
  SetLexer('&3_77');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIntLit), Ord(tok.Kind));
  AssertEquals('Value', '&3_77', tok.Value);
end;

{ Decimal with underscores }

procedure TLexerTests.TestIntLit_Decimal_WithUnderscore;
var tok: TToken;
begin
  SetLexer('1_000');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIntLit), Ord(tok.Kind));
  AssertEquals('Value', '1_000', tok.Value);
end;

procedure TLexerTests.TestIntLit_Decimal_MultipleUnderscores;
var tok: TToken;
begin
  SetLexer('1_234_567');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkIntLit), Ord(tok.Kind));
  AssertEquals('Value', '1_234_567', tok.Value);
end;

{ Float with underscore }

procedure TLexerTests.TestFloatLit_WithUnderscore;
var tok: TToken;
begin
  SetLexer('3.14_15');
  tok := FLexer.Next();
  AssertEquals('Kind', Ord(tkFloatLit), Ord(tok.Kind));
  AssertEquals('Value', '3.14_15', tok.Value);
end;

{ TParseIntLiteralTests }

procedure TParseIntLiteralTests.TestDecimal_Simple;
begin
  AssertEquals('255 decimal', 255, ParseIntLiteral('255'));
end;

procedure TParseIntLiteralTests.TestDecimal_WithUnderscore;
begin
  AssertEquals('1_000', 1000, ParseIntLiteral('1_000'));
end;

procedure TParseIntLiteralTests.TestDecimal_MultipleUnderscores;
begin
  AssertEquals('1_234_567', 1234567, ParseIntLiteral('1_234_567'));
end;

procedure TParseIntLiteralTests.TestHex_Simple;
begin
  AssertEquals('$FF', 255, ParseIntLiteral('$FF'));
end;

procedure TParseIntLiteralTests.TestHex_WithUnderscore;
begin
  AssertEquals('$FF_EC', 65516, ParseIntLiteral('$FF_EC'));
end;

procedure TParseIntLiteralTests.TestBinary_Simple;
begin
  AssertEquals('%11111111', 255, ParseIntLiteral('%11111111'));
end;

procedure TParseIntLiteralTests.TestBinary_WithUnderscore;
begin
  AssertEquals('%0010_0101', 37, ParseIntLiteral('%0010_0101'));
end;

procedure TParseIntLiteralTests.TestOctal_Simple;
begin
  AssertEquals('&377', 255, ParseIntLiteral('&377'));
end;

procedure TParseIntLiteralTests.TestOctal_WithUnderscore;
begin
  AssertEquals('&3_77', 255, ParseIntLiteral('&3_77'));
end;

procedure TParseIntLiteralTests.TestInvalid_TrailingUnderscore;
var Raised: Boolean;
begin
  Raised := False;
  try
    ParseIntLiteral('52_');
  except
    on EConvertError do Raised := True;
  end;
  AssertTrue('trailing underscore raises EConvertError', Raised);
end;

procedure TParseIntLiteralTests.TestInvalid_LeadingUnderscoreAfterPrefix;
var Raised: Boolean;
begin
  Raised := False;
  try
    ParseIntLiteral('$_52');
  except
    on EConvertError do Raised := True;
  end;
  AssertTrue('underscore after prefix raises EConvertError', Raised);
end;

initialization
  RegisterTest(TLexerTests);
  RegisterTest(TParseIntLiteralTests);

end.
