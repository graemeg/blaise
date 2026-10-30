{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Driver program to exercise blaise_str unit — compile with Blaise compiler:
    blaise --source runtime/src/test/pascal/test_blaise_str.pas
           --unit-path runtime/src/main/pascal
}

program test_blaise_str;

uses
  runtime.str;

procedure _libc_puts(S: PChar); external name 'puts';

var
  S: string;
  N: Int;

begin
  { _IntToStr }
  S := _IntToStr(42);
  _libc_puts(PChar(S));

  { _IntToStr negative }
  S := _IntToStr(-7);
  _libc_puts(PChar(S));

  { _StrToInt }
  N := _StrToInt('123');
  S := _IntToStr(N + 1);
  _libc_puts(PChar(S));

  { _StringLength }
  S := _IntToStr(_StringLength('hello'));
  _libc_puts(PChar(S));

  { _StringUpperCase }
  S := _StringUpperCase('hello world');
  _libc_puts(PChar(S));

  { _StringLowerCase }
  S := _StringLowerCase('GOODBYE');
  _libc_puts(PChar(S));

  { _StringTrim }
  S := _StringTrim('  trim me  ');
  _libc_puts(PChar(S));

  { _StringPos }
  N := _StringPos('lo', 'hello');
  S := _IntToStr(N);
  _libc_puts(PChar(S));

  { _StringCopy }
  S := _StringCopy('hello world', 7, 5);
  _libc_puts(PChar(S));

  { _Chr / _UpCase }
  S := _Chr(65);
  _libc_puts(PChar(S));
end.
