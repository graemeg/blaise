{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit runtime.civil;
// Civil-calendar arithmetic for the RTL leaves that have no C library to ask:
// day counts to and from proleptic Gregorian dates (Howard Hinnant's
// days_from_civil and civil_from_days).  Pure arithmetic, no OS calls, so
// every target that needs it shares this one copy.

interface

{ Days since 1970-01-01 for the date Y-M-D, M in 1..12. }
function _DaysFromCivil(Y, M, D: Int64): Int64;

{ The date of day Z, counted from 1970-01-01. }
procedure _CivilFromDays(Z: Int64; var Y, M, D: Int64);

implementation

function _DaysFromCivil(Y, M, D: Int64): Int64;
var
  Era, Yoe, Doy, Doe: Int64;
  YY: Int64;
begin
  if M <= 2 then YY := Y - 1 else YY := Y;
  if YY >= 0 then Era := YY div 400 else Era := (YY - 399) div 400;
  Yoe := YY - Era * 400;
  if M > 2 then
    Doy := (153 * (M - 3) + 2) div 5 + D - 1
  else
    Doy := (153 * (M + 9) + 2) div 5 + D - 1;
  Doe := Yoe * 365 + Yoe div 4 - Yoe div 100 + Doy;
  Result := Era * 146097 + Doe - 719468;
end;

procedure _CivilFromDays(Z: Int64; var Y, M, D: Int64);
var
  Era, Doe, Yoe, Doy, Mp: Int64;
begin
  Z := Z + 719468;
  if Z >= 0 then Era := Z div 146097 else Era := (Z - 146096) div 146097;
  Doe := Z - Era * 146097;
  Yoe := (Doe - Doe div 1460 + Doe div 36524 - Doe div 146096) div 365;
  Y := Yoe + Era * 400;
  Doy := Doe - (365 * Yoe + Yoe div 4 - Yoe div 100);
  Mp := (5 * Doy + 2) div 153;
  D := Doy - (153 * Mp + 2) div 5 + 1;
  if Mp < 10 then M := Mp + 3 else M := Mp - 9;
  if M <= 2 then Y := Y + 1;
end;

end.
