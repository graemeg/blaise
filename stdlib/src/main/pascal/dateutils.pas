{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit DateUtils;

// Blaise RTL — DateUtils unit.
//
// Modern date/time library inspired by Java java.time, Rust chrono, and
// C# DateTimeOffset.  Key design decisions:
//
//   - Five distinct record types (TDate, TTime, TDateTime, TInstant,
//     TDuration) with clear semantic boundaries.  No single god-type.
//   - Integer/Int64 storage throughout — no floating-point, no precision
//     loss, no TDateTime-as-Double.
//   - Immutable value semantics (records, not classes).
//   - ISO 8601 as the only wire format for ToString/Parse.
//   - UTC + fixed offset timezones.  IANA/DST deferred to a later phase.
//
// See docs/language-rationale.adoc for the full rationale.

interface

uses
  SysUtils;

type
  EDateTimeError = class(Exception);

  { ------------------------------------------------------------------ }
  { TTimeZoneOffset — signed fixed UTC offset (+HH:MM / -HH:MM)        }
  { ------------------------------------------------------------------ }

  TTimeZoneOffset = record
    TotalSeconds: Int;  { signed; +05:30 = 19800, -08:00 = -28800 }
    function Hours: Int;
    function Minutes: Int;
    function ToString: string;  { '+05:30', '-08:00', 'Z' }
  end;

  { ------------------------------------------------------------------ }
  { TDate — calendar date, no time, no timezone                         }
  { ------------------------------------------------------------------ }

  TDate = record
    Year:  Int;
    Month: Int;  { 1..12 }
    Day:   Int;  { 1..31 }
    function DayOfWeek: Int;  { 1=Monday .. 7=Sunday (ISO 8601) }
    function IsLeapYear: Boolean;
    function DaysInMonth: Int;
    function ToString: string;    { 'YYYY-MM-DD' }
  end;

  { ------------------------------------------------------------------ }
  { TTime — time of day, no date, no timezone                           }
  { ------------------------------------------------------------------ }

  TTime = record
    Hour:       Int;  { 0..23 }
    Minute:     Int;  { 0..59 }
    Second:     Int;  { 0..59 }
    Nanosecond: Int;  { 0..999999999 }
    function ToString: string;     { 'HH:MM:SS' }
    function ToStringNano: string; { 'HH:MM:SS.nnnnnnnnn' }
  end;

  { ------------------------------------------------------------------ }
  { TDateTime — local date+time, no timezone                            }
  { ------------------------------------------------------------------ }

  TDateTime = record
    Date: TDate;
    Time: TTime;
    function ToString: string;  { 'YYYY-MM-DDTHH:MM:SS' }
  end;

  { ------------------------------------------------------------------ }
  { TDuration — signed span of time (nanosecond precision)              }
  { ------------------------------------------------------------------ }

  TDuration = record
    Nanoseconds: Int64;  { signed; negative means "in the past" }
    function TotalSeconds: Int64;
    function TotalMilliseconds: Int64;
    function TotalMinutes: Int64;
    function TotalHours: Int64;
    function TotalDays: Int64;
    function IsNegative: Boolean;
    function Abs: TDuration;
    function ToString: string;  { ISO 8601: 'PT3H25M10S' }
  end;

  { ------------------------------------------------------------------ }
  { TInstant — unique UTC point in time (nanoseconds since Unix epoch)  }
  { ------------------------------------------------------------------ }

  TInstant = record
    Nanoseconds: Int64;  { ns since 1970-01-01T00:00:00Z, signed }
    function ToUtcDateTime: TDateTime;
    function ToLocalDateTime(Offset: TTimeZoneOffset): TDateTime;
    function ToUnixSeconds: Int64;
    function ToUnixMillis: Int64;
    function ToString: string;
    function ToStringOffset(Offset: TTimeZoneOffset): string;
    function Subtract(Other: TInstant): TDuration;
    function AddDuration(D: TDuration): TInstant;
    function SubtractDuration(D: TDuration): TInstant;
    function IsAfter(Other: TInstant): Boolean;
    function IsBefore(Other: TInstant): Boolean;
    function Equals(Other: TInstant): Boolean;
  end;

{ ------------------------------------------------------------------ }
{ C shim bindings (must be in interface section)                       }
{ ------------------------------------------------------------------ }

function  _TimeNow(): Int64;
  external name '_TimeNow';
function  _TimeLocalOffsetSecs(): Int32;
  external name '_TimeLocalOffsetSecs';
procedure _TimeSplit(Nanos: Int64;
                     out Year, Month, Day,
                         Hour, Min, Sec, NSec: Int32);
  external name '_TimeSplit';
function  _TimeJoin(Year, Month, Day,
                    Hour, Min, Sec, NSec: Int32): Int64;
  external name '_TimeJoin';
function  _TimeIsLeapYear(Year: Int32): Int32;
  external name '_TimeIsLeapYear';
function  _TimeDaysInMonth(Year, Month: Int32): Int32;
  external name '_TimeDaysInMonth';

{ ------------------------------------------------------------------ }
{ Construction                                                          }
{ ------------------------------------------------------------------ }

function MakeDate(Year, Month, Day: Int): TDate;
function MakeTime(Hour, Minute, Second: Int): TTime;
function MakeTimeNano(Hour, Minute, Second, Nanosecond: Int): TTime;
function MakeDateTime(ADate: TDate; ATime: TTime): TDateTime;
function MakeDurationSeconds(Seconds: Int64): TDuration;
function MakeDurationMillis(Millis: Int64): TDuration;
function MakeDurationNanos(Nanos: Int64): TDuration;
function MakeInstantUnix(Seconds: Int64): TInstant;
function MakeInstantUnixMillis(Millis: Int64): TInstant;
function MakeInstantUtc(ADate: TDate; ATime: TTime): TInstant;
function MakeInstantLocal(ADate: TDate; ATime: TTime;
                          Offset: TTimeZoneOffset): TInstant;
function MakeOffset(Hours, Minutes: Int): TTimeZoneOffset;

{ ------------------------------------------------------------------ }
{ Current time                                                          }
{ ------------------------------------------------------------------ }

function InstantNow: TInstant;
function LocalNow(Offset: TTimeZoneOffset): TDateTime;
function SystemOffset: TTimeZoneOffset;

{ ------------------------------------------------------------------ }
{ Parsing                                                               }
{ ------------------------------------------------------------------ }

function ParseDate(const S: string): TDate;
function ParseTime(const S: string): TTime;
function ParseDateTime(const S: string): TDateTime;
function ParseInstant(const S: string): TInstant;
function ParseDuration(const S: string): TDuration;
function ParseOffset(const S: string): TTimeZoneOffset;

{ ------------------------------------------------------------------ }
{ Date arithmetic                                                       }
{ ------------------------------------------------------------------ }

function DateAddDays(D: TDate; Days: Int): TDate;
function DateAddMonths(D: TDate; Months: Int): TDate;
function DateAddYears(D: TDate; Years: Int): TDate;
function DateDiffDays(A, B: TDate): Int;

{ ------------------------------------------------------------------ }
{ Comparison free functions                                             }
{ ------------------------------------------------------------------ }

function DateEquals(A, B: TDate): Boolean;
function DateBefore(A, B: TDate): Boolean;
function DateAfter(A, B: TDate): Boolean;
function DurationAdd(A, B: TDuration): TDuration;
function DurationSubtract(A, B: TDuration): TDuration;
function DurationNegate(D: TDuration): TDuration;

{ ------------------------------------------------------------------ }
{ Utility                                                               }
{ ------------------------------------------------------------------ }

function IsLeapYear(Year: Int): Boolean;
function DaysInMonth(Year, Month: Int): Int;
function DayOfWeek(D: TDate): Int;

implementation

const
  NS_PER_SEC:  Int64 = 1000000000;
  NS_PER_MS:   Int64 = 1000000;
  NS_PER_MIN:  Int64 = 60000000000;
  NS_PER_HOUR: Int64 = 3600000000000;
  NS_PER_DAY:  Int64 = 86400000000000;

{ ================================================================== }
{ Internal helpers                                                      }
{ ================================================================== }

function Pad2(N: Int): string;
var
  S: string;
begin
  S := IntToStr(N);
  if Length(S) < 2 then
    Result := '0' + S
  else
    Result := S
end;

function Pad4(N: Int): string;
var
  S: string;
begin
  S := IntToStr(N);
  while Length(S) < 4 do
    S := '0' + S;
  Result := S
end;

function Pad9(N: Int): string;
var
  S: string;
begin
  S := IntToStr(N);
  while Length(S) < 9 do
    S := '0' + S;
  Result := S
end;

{ Parse a fixed-width decimal integer from S starting at Pos (0-based).
  Advances Pos by Width.  Raises EDateTimeError on non-digit. }
function ScanInt(const S: string; var Pos: Int; Width: Int): Int;
var
  I: Int;
  Ch: Int;
begin
  Result := 0;
  I := 0;
  while I < Width do
  begin
    if Pos >= Length(S) then
      raise EDateTimeError.Create('Date/time string too short');
    Ch := OrdAt(S, Pos);
    if (Ch < Ord('0')) or (Ch > Ord('9')) then
      raise EDateTimeError.Create('Expected digit in date/time string');
    Result := Result * 10 + (Ch - Ord('0'));
    Pos := Pos + 1;
    I   := I + 1
  end
end;

{ Expect a specific literal character at Pos; raise if not found. }
procedure ScanChar(const S: string; var Pos: Int; Expected: Int);
begin
  if Pos >= Length(S) then
    raise EDateTimeError.Create('Date/time string too short');
  if OrdAt(S, Pos) <> Expected then
    raise EDateTimeError.Create('Unexpected character in date/time string');
  Pos := Pos + 1
end;

{ Parse optional decimal fraction (e.g. '.123') into nanoseconds. }
function ScanFraction(const S: string; var Pos: Int): Int;
var
  Digits: Int;
  Ch:     Int;
begin
  Result := 0;
  if (Pos >= Length(S)) or (OrdAt(S, Pos) <> Ord('.')) then Exit;
  Pos    := Pos + 1;
  Digits := 0;
  while (Pos < Length(S)) and (Digits < 9) do
  begin
    Ch := OrdAt(S, Pos);
    if (Ch < Ord('0')) or (Ch > Ord('9')) then Break;
    Result := Result * 10 + (Ch - Ord('0'));
    Pos    := Pos + 1;
    Digits := Digits + 1
  end;
  while Digits < 9 do
  begin
    Result := Result * 10;
    Digits := Digits + 1
  end
end;

{ ================================================================== }
{ IsLeapYear / DaysInMonth / DayOfWeek                                 }
{ ================================================================== }

function IsLeapYear(Year: Int): Boolean;
begin
  Result := _TimeIsLeapYear(Year) <> 0
end;

function DaysInMonth(Year, Month: Int): Int;
begin
  Result := _TimeDaysInMonth(Year, Month)
end;

{ Tomohiko Sakamoto algorithm — returns 0=Sunday .. 6=Saturday;
  we remap to ISO 8601: 1=Monday .. 7=Sunday. }
function DayOfWeek(D: TDate): Int;
var
  Y, M, Day, Dow: Int;
  T: array[0..11] of Int32;
begin
  T[0]  := 0; T[1]  := 3; T[2]  := 2; T[3]  := 5;
  T[4]  := 0; T[5]  := 3; T[6]  := 5; T[7]  := 1;
  T[8]  := 4; T[9]  := 6; T[10] := 2; T[11] := 4;
  Y := D.Year;
  M := D.Month;
  Day := D.Day;
  if M < 3 then Y := Y - 1;
  Dow := (Y + Y div 4 - Y div 100 + Y div 400 + T[M - 1] + Day) mod 7;
  { Dow: 0=Sun,1=Mon,...,6=Sat → ISO: Mon=1..Sun=7 }
  if Dow = 0 then
    Result := 7
  else
    Result := Dow
end;

{ ================================================================== }
{ TTimeZoneOffset                                                       }
{ ================================================================== }

function TTimeZoneOffset.Hours: Int;
var
  Abs: Int;
begin
  Abs := Self.TotalSeconds;
  if Abs < 0 then Abs := -Abs;
  Result := Abs div 3600
end;

function TTimeZoneOffset.Minutes: Int;
var
  Abs: Int;
begin
  Abs := Self.TotalSeconds;
  if Abs < 0 then Abs := -Abs;
  Result := (Abs mod 3600) div 60
end;

function TTimeZoneOffset.ToString: string;
var
  Sign: string;
  H, M: Int;
begin
  if Self.TotalSeconds = 0 then
  begin
    Result := 'Z';
    Exit
  end;
  if Self.TotalSeconds < 0 then
    Sign := '-'
  else
    Sign := '+';
  H := Self.Hours();
  M := Self.Minutes();
  Result := Sign + Pad2(H) + ':' + Pad2(M)
end;

{ ================================================================== }
{ TDate                                                                 }
{ ================================================================== }

function TDate.DayOfWeek: Int;
var
  Y, M, Day, Dow: Int;
  T: array[0..11] of Int32;
begin
  T[0] := 0; T[1] := 3; T[2] := 2; T[3] := 5;
  T[4] := 0; T[5] := 3; T[6] := 5; T[7] := 1;
  T[8] := 4; T[9] := 6; T[10] := 2; T[11] := 4;
  Y := Self.Year; M := Self.Month; Day := Self.Day;
  if M < 3 then Y := Y - 1;
  Dow := (Y + Y div 4 - Y div 100 + Y div 400 + T[M - 1] + Day) mod 7;
  if Dow = 0 then Result := 7 else Result := Dow
end;

function TDate.IsLeapYear: Boolean;
begin
  Result := _TimeIsLeapYear(Self.Year) <> 0
end;

function TDate.DaysInMonth: Int;
begin
  Result := _TimeDaysInMonth(Self.Year, Self.Month)
end;

function TDate.ToString: string;
begin
  Result := Pad4(Self.Year) + '-' + Pad2(Self.Month) + '-' + Pad2(Self.Day)
end;

{ ================================================================== }
{ TTime                                                                 }
{ ================================================================== }

function TTime.ToString: string;
begin
  Result := Pad2(Self.Hour) + ':' + Pad2(Self.Minute) + ':' + Pad2(Self.Second)
end;

function TTime.ToStringNano: string;
begin
  Result := Pad2(Self.Hour) + ':' + Pad2(Self.Minute) + ':' +
            Pad2(Self.Second) + '.' + Pad9(Self.Nanosecond)
end;

{ ================================================================== }
{ TDateTime                                                             }
{ ================================================================== }

function TDateTime.ToString: string;
begin
  Result := Self.Date.ToString() + 'T' + Self.Time.ToString()
end;

{ ================================================================== }
{ TDuration                                                             }
{ ================================================================== }

function TDuration.TotalSeconds: Int64;
begin
  Result := Self.Nanoseconds div NS_PER_SEC
end;

function TDuration.TotalMilliseconds: Int64;
begin
  Result := Self.Nanoseconds div NS_PER_MS
end;

function TDuration.TotalMinutes: Int64;
begin
  Result := Self.Nanoseconds div NS_PER_MIN
end;

function TDuration.TotalHours: Int64;
begin
  Result := Self.Nanoseconds div NS_PER_HOUR
end;

function TDuration.TotalDays: Int64;
begin
  Result := Self.Nanoseconds div NS_PER_DAY
end;

function TDuration.IsNegative: Boolean;
begin
  Result := Self.Nanoseconds < 0
end;

function TDuration.Abs: TDuration;
begin
  if Self.Nanoseconds < 0 then
    Result.Nanoseconds := -Self.Nanoseconds
  else
    Result.Nanoseconds := Self.Nanoseconds
end;

function TDuration.ToString: string;
var
  Rem:  Int64;
  H, M, S: Int64;
begin
  Rem := Self.Nanoseconds;
  if Rem < 0 then Rem := -Rem;
  Rem := Rem div NS_PER_SEC;
  H   := Rem div 3600;
  Rem := Rem mod 3600;
  M   := Rem div 60;
  S   := Rem mod 60;
  Result := 'PT';
  if H > 0 then Result := Result + IntToStr(H) + 'H';
  if M > 0 then Result := Result + IntToStr(M) + 'M';
  if (S > 0) or ((H = 0) and (M = 0)) then
    Result := Result + IntToStr(S) + 'S'
end;

{ ================================================================== }
{ TInstant                                                              }
{ ================================================================== }

function TInstant.ToUnixSeconds: Int64;
begin
  Result := Self.Nanoseconds div NS_PER_SEC
end;

function TInstant.ToUnixMillis: Int64;
begin
  Result := Self.Nanoseconds div NS_PER_MS
end;

function TInstant.ToUtcDateTime: TDateTime;
var
  Y, Mo, D, H, Mi, S, Ns: Int32;
begin
  _TimeSplit(Self.Nanoseconds, Y, Mo, D, H, Mi, S, Ns);
  Result.Date.Year        := Y;
  Result.Date.Month       := Mo;
  Result.Date.Day         := D;
  Result.Time.Hour        := H;
  Result.Time.Minute      := Mi;
  Result.Time.Second      := S;
  Result.Time.Nanosecond  := Ns
end;

function TInstant.ToLocalDateTime(Offset: TTimeZoneOffset): TDateTime;
var
  Shifted: TInstant;
begin
  Shifted.Nanoseconds := Self.Nanoseconds +
                         Int64(Offset.TotalSeconds) * NS_PER_SEC;
  Result := Shifted.ToUtcDateTime()
end;

function TInstant.ToString: string;
var
  DT: TDateTime;
begin
  DT     := Self.ToUtcDateTime();
  Result := DT.Date.ToString() + 'T' + DT.Time.ToString() + 'Z'
end;

function TInstant.ToStringOffset(Offset: TTimeZoneOffset): string;
var
  DT: TDateTime;
begin
  DT     := Self.ToLocalDateTime(Offset);
  Result := DT.Date.ToString() + 'T' + DT.Time.ToString() + Offset.ToString()
end;

function TInstant.Subtract(Other: TInstant): TDuration;
begin
  Result.Nanoseconds := Self.Nanoseconds - Other.Nanoseconds
end;

function TInstant.AddDuration(D: TDuration): TInstant;
begin
  Result.Nanoseconds := Self.Nanoseconds + D.Nanoseconds
end;

function TInstant.SubtractDuration(D: TDuration): TInstant;
begin
  Result.Nanoseconds := Self.Nanoseconds - D.Nanoseconds
end;

function TInstant.IsAfter(Other: TInstant): Boolean;
begin
  Result := Self.Nanoseconds > Other.Nanoseconds
end;

function TInstant.IsBefore(Other: TInstant): Boolean;
begin
  Result := Self.Nanoseconds < Other.Nanoseconds
end;

function TInstant.Equals(Other: TInstant): Boolean;
begin
  Result := Self.Nanoseconds = Other.Nanoseconds
end;

{ ================================================================== }
{ Construction                                                          }
{ ================================================================== }

function MakeDate(Year, Month, Day: Int): TDate;
begin
  Result.Year  := Year;
  Result.Month := Month;
  Result.Day   := Day
end;

function MakeTime(Hour, Minute, Second: Int): TTime;
begin
  Result.Hour       := Hour;
  Result.Minute     := Minute;
  Result.Second     := Second;
  Result.Nanosecond := 0
end;

function MakeTimeNano(Hour, Minute, Second, Nanosecond: Int): TTime;
begin
  Result.Hour       := Hour;
  Result.Minute     := Minute;
  Result.Second     := Second;
  Result.Nanosecond := Nanosecond
end;

function MakeDateTime(ADate: TDate; ATime: TTime): TDateTime;
begin
  Result.Date := ADate;
  Result.Time := ATime
end;

function MakeDurationSeconds(Seconds: Int64): TDuration;
begin
  Result.Nanoseconds := Seconds * NS_PER_SEC
end;

function MakeDurationMillis(Millis: Int64): TDuration;
begin
  Result.Nanoseconds := Millis * NS_PER_MS
end;

function MakeDurationNanos(Nanos: Int64): TDuration;
begin
  Result.Nanoseconds := Nanos
end;

function MakeInstantUnix(Seconds: Int64): TInstant;
begin
  Result.Nanoseconds := Seconds * NS_PER_SEC
end;

function MakeInstantUnixMillis(Millis: Int64): TInstant;
begin
  Result.Nanoseconds := Millis * NS_PER_MS
end;

function MakeInstantUtc(ADate: TDate; ATime: TTime): TInstant;
begin
  Result.Nanoseconds := _TimeJoin(ADate.Year, ADate.Month, ADate.Day,
                                  ATime.Hour, ATime.Minute, ATime.Second,
                                  ATime.Nanosecond)
end;

function MakeInstantLocal(ADate: TDate; ATime: TTime;
                          Offset: TTimeZoneOffset): TInstant;
begin
  Result := MakeInstantUtc(ADate, ATime);
  Result.Nanoseconds := Result.Nanoseconds -
                        Int64(Offset.TotalSeconds) * NS_PER_SEC
end;

function MakeOffset(Hours, Minutes: Int): TTimeZoneOffset;
var
  Sign: Int;
begin
  if Hours < 0 then
  begin
    Sign := -1;
    Hours := -Hours
  end
  else
    Sign := 1;
  Result.TotalSeconds := Sign * (Hours * 3600 + Minutes * 60)
end;

{ ================================================================== }
{ Current time                                                          }
{ ================================================================== }

function InstantNow: TInstant;
begin
  Result.Nanoseconds := _TimeNow()
end;

function LocalNow(Offset: TTimeZoneOffset): TDateTime;
var
  Now: TInstant;
begin
  Now := InstantNow();
  Result := Now.ToLocalDateTime(Offset)
end;

function SystemOffset: TTimeZoneOffset;
begin
  Result.TotalSeconds := _TimeLocalOffsetSecs()
end;

{ ================================================================== }
{ Parsing                                                               }
{ ================================================================== }

function ParseDate(const S: string): TDate;
var
  Pos: Int;
begin
  Pos           := 0;
  Result.Year   := ScanInt(S, Pos, 4);
  ScanChar(S, Pos, Ord('-'));
  Result.Month  := ScanInt(S, Pos, 2);
  ScanChar(S, Pos, Ord('-'));
  Result.Day    := ScanInt(S, Pos, 2)
end;

function ParseTime(const S: string): TTime;
var
  Pos: Int;
begin
  Pos              := 0;
  Result.Hour      := ScanInt(S, Pos, 2);
  ScanChar(S, Pos, Ord(':'));
  Result.Minute    := ScanInt(S, Pos, 2);
  ScanChar(S, Pos, Ord(':'));
  Result.Second    := ScanInt(S, Pos, 2);
  Result.Nanosecond := ScanFraction(S, Pos)
end;

function ParseDateTime(const S: string): TDateTime;
var
  Pos: Int;
begin
  Pos                    := 0;
  Result.Date.Year       := ScanInt(S, Pos, 4);
  ScanChar(S, Pos, Ord('-'));
  Result.Date.Month      := ScanInt(S, Pos, 2);
  ScanChar(S, Pos, Ord('-'));
  Result.Date.Day        := ScanInt(S, Pos, 2);
  ScanChar(S, Pos, Ord('T'));
  Result.Time.Hour       := ScanInt(S, Pos, 2);
  ScanChar(S, Pos, Ord(':'));
  Result.Time.Minute     := ScanInt(S, Pos, 2);
  ScanChar(S, Pos, Ord(':'));
  Result.Time.Second     := ScanInt(S, Pos, 2);
  Result.Time.Nanosecond := ScanFraction(S, Pos)
end;

function ParseOffset(const S: string): TTimeZoneOffset;
var
  Pos:  Int;
  Sign: Int;
  H, M: Int;
  Ch:   Int;
begin
  Pos := 0;
  if Length(S) = 0 then
    raise EDateTimeError.Create('Empty timezone offset string');
  Ch := OrdAt(S, Pos);
  if Ch = Ord('Z') then
  begin
    Result.TotalSeconds := 0;
    Exit
  end;
  if Ch = Ord('+') then
    Sign := 1
  else if Ch = Ord('-') then
    Sign := -1
  else
    raise EDateTimeError.Create('Timezone offset must start with Z, +, or -');
  Pos := Pos + 1;
  H   := ScanInt(S, Pos, 2);
  ScanChar(S, Pos, Ord(':'));
  M   := ScanInt(S, Pos, 2);
  Result.TotalSeconds := Sign * (H * 3600 + M * 60)
end;

function ParseInstant(const S: string): TInstant;
var
  Pos:  Int;
  Y, Mo, D, H, Mi, Se, Ns: Int;
  Ch:   Int;
  Off:  TTimeZoneOffset;
  OffStr: string;
begin
  Pos := 0;
  Y   := ScanInt(S, Pos, 4);
  ScanChar(S, Pos, Ord('-'));
  Mo  := ScanInt(S, Pos, 2);
  ScanChar(S, Pos, Ord('-'));
  D   := ScanInt(S, Pos, 2);
  ScanChar(S, Pos, Ord('T'));
  H   := ScanInt(S, Pos, 2);
  ScanChar(S, Pos, Ord(':'));
  Mi  := ScanInt(S, Pos, 2);
  ScanChar(S, Pos, Ord(':'));
  Se  := ScanInt(S, Pos, 2);
  Ns  := ScanFraction(S, Pos);
  { Parse trailing timezone: Z or ±HH:MM }
  if Pos >= Length(S) then
    raise EDateTimeError.Create('Missing timezone in instant string');
  Ch := OrdAt(S, Pos);
  if Ch = Ord('Z') then
    Off.TotalSeconds := 0
  else
  begin
    OffStr := Copy(S, Pos, Length(S) - Pos);
    Off    := ParseOffset(OffStr)
  end;
  Result.Nanoseconds := _TimeJoin(Y, Mo, D, H, Mi, Se, Ns) -
                        Int64(Off.TotalSeconds) * NS_PER_SEC
end;

function ParseDuration(const S: string): TDuration;
var
  Pos:    Int;
  Ch:     Int;
  N:      Int64;
  Digit:  Int;
  InTime: Boolean;
  Total:  Int64;
begin
  Pos    := 0;
  Total  := 0;
  if (Length(S) = 0) or (OrdAt(S, 0) <> Ord('P')) then
    raise EDateTimeError.Create('Duration must start with P');
  Pos    := 1;
  InTime := False;
  while Pos < Length(S) do
  begin
    Ch := OrdAt(S, Pos);
    if Ch = Ord('T') then
    begin
      InTime := True;
      Pos    := Pos + 1;
      Continue
    end;
    { Read integer value }
    if (Ch < Ord('0')) or (Ch > Ord('9')) then
      raise EDateTimeError.Create('Expected digit in duration');
    N := 0;
    while (Pos < Length(S)) do
    begin
      Digit := OrdAt(S, Pos);
      if (Digit < Ord('0')) or (Digit > Ord('9')) then Break;
      N   := N * 10 + (Digit - Ord('0'));
      Pos := Pos + 1
    end;
    if Pos >= Length(S) then
      raise EDateTimeError.Create('Missing unit designator in duration');
    Ch  := OrdAt(S, Pos);
    Pos := Pos + 1;
    if InTime then
    begin
      if Ch = Ord('H') then Total := Total + N * Int64(3600) * NS_PER_SEC
      else if Ch = Ord('M') then Total := Total + N * Int64(60) * NS_PER_SEC
      else if Ch = Ord('S') then Total := Total + N * NS_PER_SEC
      else raise EDateTimeError.Create('Unknown time unit in duration')
    end
    else
    begin
      if Ch = Ord('D') then Total := Total + N * NS_PER_DAY
      else raise EDateTimeError.Create('Only D supported for date part of duration (use T for time units)')
    end
  end;
  Result.Nanoseconds := Total
end;

{ ================================================================== }
{ Date arithmetic                                                       }
{ ================================================================== }

function DateToInstant(D: TDate): TInstant;
begin
  Result.Nanoseconds := _TimeJoin(D.Year, D.Month, D.Day, 0, 0, 0, 0)
end;

function InstantToDate(I: TInstant): TDate;
var
  Y, Mo, D, H, Mi, S, Ns: Int32;
begin
  _TimeSplit(I.Nanoseconds, Y, Mo, D, H, Mi, S, Ns);
  Result.Year  := Y;
  Result.Month := Mo;
  Result.Day   := D
end;

function DateAddDays(D: TDate; Days: Int): TDate;
var
  I: TInstant;
begin
  I.Nanoseconds := _TimeJoin(D.Year, D.Month, D.Day, 0, 0, 0, 0) +
                   Int64(Days) * NS_PER_DAY;
  Result := InstantToDate(I)
end;

function DateAddMonths(D: TDate; Months: Int): TDate;
var
  TotalMonths: Int;
  NewYear:     Int;
  NewMonth:    Int;
  NewDay:      Int;
  MaxDay:      Int;
begin
  TotalMonths := (D.Year * 12 + D.Month - 1) + Months;
  NewYear     := TotalMonths div 12;
  NewMonth    := TotalMonths mod 12 + 1;
  { Clamp day to the last valid day in the new month }
  MaxDay := _TimeDaysInMonth(NewYear, NewMonth);
  NewDay := D.Day;
  if NewDay > MaxDay then NewDay := MaxDay;
  Result.Year  := NewYear;
  Result.Month := NewMonth;
  Result.Day   := NewDay
end;

function DateAddYears(D: TDate; Years: Int): TDate;
begin
  Result := DateAddMonths(D, Years * 12)
end;

function DateDiffDays(A, B: TDate): Int;
var
  NsA, NsB: Int64;
begin
  NsA    := _TimeJoin(A.Year, A.Month, A.Day, 0, 0, 0, 0);
  NsB    := _TimeJoin(B.Year, B.Month, B.Day, 0, 0, 0, 0);
  Result := Int32((NsB - NsA) div NS_PER_DAY)
end;

{ ================================================================== }
{ Comparison free functions                                             }
{ ================================================================== }

function DateEquals(A, B: TDate): Boolean;
begin
  Result := (A.Year = B.Year) and (A.Month = B.Month) and (A.Day = B.Day)
end;

function DateBefore(A, B: TDate): Boolean;
begin
  if A.Year  <> B.Year  then Result := A.Year  < B.Year
  else if A.Month <> B.Month then Result := A.Month < B.Month
  else Result := A.Day < B.Day
end;

function DateAfter(A, B: TDate): Boolean;
begin
  Result := DateBefore(B, A)
end;

function DurationAdd(A, B: TDuration): TDuration;
begin
  Result.Nanoseconds := A.Nanoseconds + B.Nanoseconds
end;

function DurationSubtract(A, B: TDuration): TDuration;
begin
  Result.Nanoseconds := A.Nanoseconds - B.Nanoseconds
end;

function DurationNegate(D: TDuration): TDuration;
begin
  Result.Nanoseconds := -D.Nanoseconds
end;

end.
