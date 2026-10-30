{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.dateutils;

{ E2E tests for the DateUtils RTL unit.
  Each test compiles a small program that uses DateUtils, runs it through
  QBE+cc, and asserts on stdout.  Covers: construction, ToString/ISO 8601
  formatting, date arithmetic, duration arithmetic, instant arithmetic,
  ISO 8601 parsing, timezone offset handling. }

interface

uses
  classes, blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EDateUtilsTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_InstantNow();
    procedure TestRun_MakeDate_ToString;
    procedure TestRun_MakeTime_ToString;
    procedure TestRun_MakeTimeNano_ToString;
    procedure TestRun_MakeDateTime_ToString;
    procedure TestRun_MakeOffset_ToString;
    procedure TestRun_MakeOffset_UTC;
    procedure TestRun_MakeInstantUtc_RoundTrip;
    procedure TestRun_Instant_ToUnixSeconds;
    procedure TestRun_Instant_AddDuration;
    procedure TestRun_Instant_SubtractDuration;
    procedure TestRun_Instant_Subtract;
    procedure TestRun_Instant_IsAfter_IsBefore;
    procedure TestRun_Instant_Equals;
    procedure TestRun_Instant_ToStringOffset;
    procedure TestRun_Instant_ToLocalDateTime;
    procedure TestRun_Duration_TotalAccessors;
    procedure TestRun_Duration_ToString;
    procedure TestRun_Duration_Negative;
    procedure TestRun_DurationAdd_Subtract;
    procedure TestRun_ParseDate;
    procedure TestRun_ParseTime;
    procedure TestRun_ParseDateTime;
    procedure TestRun_ParseInstant_UTC;
    procedure TestRun_ParseInstant_Offset;
    procedure TestRun_ParseDuration;
    procedure TestRun_ParseOffset;
    procedure TestRun_IsLeapYear;
    procedure TestRun_DaysInMonth;
    procedure TestRun_DayOfWeek;
    procedure TestRun_DateAddDays;
    procedure TestRun_DateAddMonths_Clamp;
    procedure TestRun_DateAddYears;
    procedure TestRun_DateDiffDays;
    procedure TestRun_SystemOffset;
    procedure TestRun_MakeInstantLocal;
  end;

implementation

const
  SrcInstantNow =
    '''
    program P;
    uses DateUtils;
    var I: TInstant;
    begin
      I := InstantNow();
      { Must be after 2020-01-01T00:00:00Z = Unix epoch 1577836800 }
      WriteLn(I.ToUnixSeconds() > 1577836800)
    end.
    ''';

  SrcMakeDateToString =
    '''
    program P;
    uses DateUtils;
    var D: TDate;
    begin
      D := MakeDate(2025, 5, 15);
      WriteLn(D.ToString())
    end.
    ''';

  SrcMakeTimeToString =
    '''
    program P;
    uses DateUtils;
    var T: TTime;
    begin
      T := MakeTime(14, 30, 45);
      WriteLn(T.ToString())
    end.
    ''';

  SrcMakeTimeNanoToString =
    '''
    program P;
    uses DateUtils;
    var T: TTime;
    begin
      T := MakeTimeNano(9, 5, 3, 123000000);
      WriteLn(T.ToStringNano())
    end.
    ''';

  SrcMakeDateTimeToString =
    '''
    program P;
    uses DateUtils;
    var D: TDate; T: TTime; DT: TDateTime;
    begin
      D  := MakeDate(2025, 5, 15);
      T  := MakeTime(14, 30, 45);
      DT := MakeDateTime(D, T);
      WriteLn(DT.ToString())
    end.
    ''';

  SrcMakeOffsetToString =
    '''
    program P;
    uses DateUtils;
    var OA, OB, OC: TTimeZoneOffset;
    begin
      OA := MakeOffset(5, 30);
      OB := MakeOffset(-8, 0);
      OC := MakeOffset(0, 0);
      WriteLn(OA.ToString());
      WriteLn(OB.ToString());
      WriteLn(OC.ToString())
    end.
    ''';

  SrcMakeOffsetUTC =
    '''
    program P;
    uses DateUtils;
    var O: TTimeZoneOffset;
    begin
      O := MakeOffset(0, 0);
      WriteLn(O.TotalSeconds);
      WriteLn(O.Hours());
      WriteLn(O.Minutes())
    end.
    ''';

  SrcInstantUtcRoundTrip =
    '''
    program P;
    uses DateUtils;
    var D: TDate; T: TTime; I: TInstant; DT: TDateTime;
    begin
      D  := MakeDate(2025, 5, 15);
      T  := MakeTime(14, 30, 45);
      I  := MakeInstantUtc(D, T);
      DT := I.ToUtcDateTime();
      WriteLn(DT.Date.Year);
      WriteLn(DT.Date.Month);
      WriteLn(DT.Date.Day);
      WriteLn(DT.Time.Hour);
      WriteLn(DT.Time.Minute);
      WriteLn(DT.Time.Second)
    end.
    ''';

  SrcInstantToUnixSeconds =
    '''
    program P;
    uses DateUtils;
    var I: TInstant;
    begin
      { 1970-01-01T00:00:01Z = Unix second 1 }
      I := MakeInstantUnix(1);
      WriteLn(I.ToUnixSeconds());
      WriteLn(I.ToUnixMillis())
    end.
    ''';

  SrcInstantAddDuration =
    '''
    program P;
    uses DateUtils;
    var D: TDate; T: TTime; I, I2: TInstant; DT: TDateTime;
    begin
      D  := MakeDate(2025, 1, 1);
      T  := MakeTime(0, 0, 0);
      I  := MakeInstantUtc(D, T);
      I2 := I.AddDuration(MakeDurationSeconds(3600));
      DT := I2.ToUtcDateTime();
      WriteLn(DT.Time.Hour);
      WriteLn(DT.Time.Minute);
      WriteLn(DT.Time.Second)
    end.
    ''';

  SrcInstantSubtractDuration =
    '''
    program P;
    uses DateUtils;
    var D: TDate; T: TTime; I, I2: TInstant; DT: TDateTime;
    begin
      D  := MakeDate(2025, 1, 1);
      T  := MakeTime(1, 0, 0);
      I  := MakeInstantUtc(D, T);
      I2 := I.SubtractDuration(MakeDurationSeconds(3600));
      DT := I2.ToUtcDateTime();
      WriteLn(DT.Time.Hour);
      WriteLn(DT.Date.Day)
    end.
    ''';

  SrcInstantSubtract =
    '''
    program P;
    uses DateUtils;
    var A, B: TInstant; Dur: TDuration;
    begin
      A   := MakeInstantUnix(1000);
      B   := MakeInstantUnix(1003);
      Dur := B.Subtract(A);
      WriteLn(Dur.TotalSeconds())
    end.
    ''';

  SrcInstantIsAfterIsBefore =
    '''
    program P;
    uses DateUtils;
    var A, B: TInstant;
    begin
      A := MakeInstantUnix(100);
      B := MakeInstantUnix(200);
      WriteLn(A.IsBefore(B));
      WriteLn(A.IsAfter(B));
      WriteLn(B.IsAfter(A))
    end.
    ''';

  SrcInstantEquals =
    '''
    program P;
    uses DateUtils;
    var A, B, C: TInstant;
    begin
      A := MakeInstantUnix(42);
      B := MakeInstantUnix(42);
      C := MakeInstantUnix(43);
      WriteLn(A.Equals(B));
      WriteLn(A.Equals(C))
    end.
    ''';

  SrcInstantToStringOffset =
    '''
    program P;
    uses DateUtils;
    var I: TInstant; O: TTimeZoneOffset;
    begin
      I := MakeInstantUtc(MakeDate(2025, 5, 15), MakeTime(14, 30, 45));
      WriteLn(I.ToString());
      O := MakeOffset(5, 30);
      WriteLn(I.ToStringOffset(O))
    end.
    ''';

  SrcInstantToLocalDateTime =
    '''
    program P;
    uses DateUtils;
    var I: TInstant; O: TTimeZoneOffset; DT: TDateTime;
    begin
      I  := MakeInstantUtc(MakeDate(2025, 5, 15), MakeTime(14, 0, 0));
      O  := MakeOffset(5, 30);
      DT := I.ToLocalDateTime(O);
      WriteLn(DT.Time.Hour);
      WriteLn(DT.Time.Minute)
    end.
    ''';

  SrcDurationTotalAccessors =
    '''
    program P;
    uses DateUtils;
    var D: TDuration;
    begin
      { 2 hours + 30 min + 10 sec = 9010 s = 9010000 ms }
      D := MakeDurationSeconds(9010);
      WriteLn(D.TotalSeconds());
      WriteLn(D.TotalMilliseconds());
      WriteLn(D.TotalMinutes());
      WriteLn(D.TotalHours())
    end.
    ''';

  SrcDurationToString =
    '''
    program P;
    uses DateUtils;
    begin
      WriteLn(MakeDurationSeconds(3661).ToString());
      WriteLn(MakeDurationSeconds(86400).ToString());
      WriteLn(MakeDurationSeconds(0).ToString());
      WriteLn(MakeDurationSeconds(59).ToString())
    end.
    ''';

  SrcDurationNegative =
    '''
    program P;
    uses DateUtils;
    var D, A: TDuration;
    begin
      D := MakeDurationSeconds(-120);
      WriteLn(D.IsNegative());
      A := D.Abs();
      WriteLn(A.IsNegative());
      WriteLn(A.TotalSeconds())
    end.
    ''';

  SrcDurationAddSubtract =
    '''
    program P;
    uses DateUtils;
    var A, B, C, S: TDuration;
    begin
      A := MakeDurationSeconds(100);
      B := MakeDurationSeconds(50);
      C := DurationAdd(A, B);
      S := DurationSubtract(A, B);
      WriteLn(C.TotalSeconds());
      WriteLn(S.TotalSeconds());
      WriteLn(DurationNegate(A).TotalSeconds())
    end.
    ''';

  SrcParseDate =
    '''
    program P;
    uses DateUtils;
    var D: TDate;
    begin
      D := ParseDate('2025-05-15');
      WriteLn(D.Year);
      WriteLn(D.Month);
      WriteLn(D.Day);
      WriteLn(D.ToString())
    end.
    ''';

  SrcParseTime =
    '''
    program P;
    uses DateUtils;
    var T: TTime;
    begin
      T := ParseTime('14:30:45');
      WriteLn(T.Hour);
      WriteLn(T.Minute);
      WriteLn(T.Second);
      WriteLn(T.ToString())
    end.
    ''';

  SrcParseDateTime =
    '''
    program P;
    uses DateUtils;
    var DT: TDateTime;
    begin
      DT := ParseDateTime('2025-05-15T14:30:45');
      WriteLn(DT.Date.Year);
      WriteLn(DT.Date.Month);
      WriteLn(DT.Date.Day);
      WriteLn(DT.Time.Hour);
      WriteLn(DT.Time.Minute);
      WriteLn(DT.Time.Second);
      WriteLn(DT.ToString())
    end.
    ''';

  SrcParseInstantUTC =
    '''
    program P;
    uses DateUtils;
    var I: TInstant; DT: TDateTime;
    begin
      I  := ParseInstant('2025-05-15T14:30:45Z');
      DT := I.ToUtcDateTime();
      WriteLn(DT.Date.Year);
      WriteLn(DT.Date.Month);
      WriteLn(DT.Date.Day);
      WriteLn(DT.Time.Hour);
      WriteLn(DT.Time.Minute);
      WriteLn(DT.Time.Second);
      WriteLn(I.ToString())
    end.
    ''';

  SrcParseInstantOffset =
    '''
    program P;
    uses DateUtils;
    var A, B: TInstant;
    begin
      { +05:00 offset means 14:30 local = 09:30 UTC }
      A := ParseInstant('2025-05-15T14:30:00+05:00');
      B := ParseInstant('2025-05-15T09:30:00Z');
      WriteLn(A.Equals(B))
    end.
    ''';

  SrcParseDuration =
    '''
    program P;
    uses DateUtils;
    var D: TDuration;
    begin
      D := ParseDuration('PT3H25M10S');
      WriteLn(D.TotalSeconds());
      WriteLn(D.ToString());
      D := ParseDuration('PT0S');
      WriteLn(D.TotalSeconds())
    end.
    ''';

  SrcParseOffset =
    '''
    program P;
    uses DateUtils;
    var O: TTimeZoneOffset;
    begin
      O := ParseOffset('+05:30');
      WriteLn(O.TotalSeconds);
      O := ParseOffset('-08:00');
      WriteLn(O.TotalSeconds);
      O := ParseOffset('Z');
      WriteLn(O.TotalSeconds)
    end.
    ''';

  SrcIsLeapYear =
    '''
    program P;
    uses DateUtils;
    begin
      WriteLn(IsLeapYear(2000));
      WriteLn(IsLeapYear(1900));
      WriteLn(IsLeapYear(2024));
      WriteLn(IsLeapYear(2025))
    end.
    ''';

  SrcDaysInMonth =
    '''
    program P;
    uses DateUtils;
    begin
      WriteLn(DaysInMonth(2024, 2));
      WriteLn(DaysInMonth(2025, 2));
      WriteLn(DaysInMonth(2025, 1));
      WriteLn(DaysInMonth(2025, 4))
    end.
    ''';

  SrcDayOfWeek =
    '''
    program P;
    uses DateUtils;
    var D: TDate;
    begin
      { 2025-05-15 is a Thursday = 4 (ISO: Mon=1 .. Sun=7) }
      D := MakeDate(2025, 5, 15);
      WriteLn(DayOfWeek(D));
      WriteLn(D.DayOfWeek());
      { 2025-05-19 is a Monday = 1 }
      D := MakeDate(2025, 5, 19);
      WriteLn(D.DayOfWeek())
    end.
    ''';

  SrcDateAddDays =
    '''
    program P;
    uses DateUtils;
    var D: TDate;
    begin
      D := DateAddDays(MakeDate(2025, 1, 30), 5);
      WriteLn(D.ToString());
      { Cross year boundary }
      D := DateAddDays(MakeDate(2024, 12, 31), 1);
      WriteLn(D.ToString())
    end.
    ''';

  SrcDateAddMonthsClamp =
    '''
    program P;
    uses DateUtils;
    var D: TDate;
    begin
      { Jan 31 + 1 month = Feb 28 (2025 is not a leap year) }
      D := DateAddMonths(MakeDate(2025, 1, 31), 1);
      WriteLn(D.ToString());
      { Jan 31 + 1 month = Feb 29 (2024 is a leap year) }
      D := DateAddMonths(MakeDate(2024, 1, 31), 1);
      WriteLn(D.ToString());
      { Cross year boundary: Nov + 3 months }
      D := DateAddMonths(MakeDate(2025, 11, 15), 3);
      WriteLn(D.ToString())
    end.
    ''';

  SrcDateAddYears =
    '''
    program P;
    uses DateUtils;
    var D: TDate;
    begin
      D := DateAddYears(MakeDate(2025, 5, 15), 3);
      WriteLn(D.ToString());
      { Feb 29 leap year + 1 year → Feb 28 }
      D := DateAddYears(MakeDate(2024, 2, 29), 1);
      WriteLn(D.ToString())
    end.
    ''';

  SrcDateDiffDays =
    '''
    program P;
    uses DateUtils;
    var A, B: TDate;
    begin
      A := MakeDate(2025, 1, 1);
      B := MakeDate(2025, 1, 11);
      WriteLn(DateDiffDays(A, B));
      WriteLn(DateDiffDays(B, A))
    end.
    ''';

  SrcSystemOffset =
    '''
    program P;
    uses DateUtils;
    var O: TTimeZoneOffset;
    begin
      O := SystemOffset();
      { UTC offset must be within +/-14 hours = +/-50400 seconds }
      WriteLn(O.TotalSeconds >= -50400);
      WriteLn(O.TotalSeconds <= 50400)
    end.
    ''';

  SrcMakeInstantLocal =
    '''
    program P;
    uses DateUtils;
    var D: TDate; T: TTime; O: TTimeZoneOffset; I: TInstant; DT: TDateTime;
    begin
      D  := MakeDate(2025, 5, 15);
      T  := MakeTime(19, 30, 45);
      O  := MakeOffset(5, 30);
      I  := MakeInstantLocal(D, T, O);
      DT := I.ToUtcDateTime();
      WriteLn(DT.Time.Hour);
      WriteLn(DT.Time.Minute);
      WriteLn(DT.Time.Second)
    end.
    ''';

{ ------------------------------------------------------------------ }
{ Setup                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EDateUtilsTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-dateutils')
end;

{ ------------------------------------------------------------------ }
{ Tests                                                                }
{ ------------------------------------------------------------------ }

procedure TE2EDateUtilsTests.TestRun_InstantNow();
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInstantNow, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('InstantNow > 2020 epoch', 'True', Trim(Output));
end;

procedure TE2EDateUtilsTests.TestRun_MakeDate_ToString;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcMakeDateToString, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Date ISO 8601', '2025-05-15', Trim(Output));
end;

procedure TE2EDateUtilsTests.TestRun_MakeTime_ToString;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcMakeTimeToString, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Time ISO 8601', '14:30:45', Trim(Output));
end;

procedure TE2EDateUtilsTests.TestRun_MakeTimeNano_ToString;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcMakeTimeNanoToString, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Time with nanos', '09:05:03.123000000', Trim(Output));
end;

procedure TE2EDateUtilsTests.TestRun_MakeDateTime_ToString;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcMakeDateTimeToString, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('DateTime ISO 8601', '2025-05-15T14:30:45', Trim(Output));
end;

procedure TE2EDateUtilsTests.TestRun_MakeOffset_ToString;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcMakeOffsetToString, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('+05:30', '+05:30', Lines.Strings[0]);
    AssertEquals('-08:00', '-08:00', Lines.Strings[1]);
    AssertEquals('Z for UTC', 'Z',   Lines.Strings[2]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_MakeOffset_UTC;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcMakeOffsetUTC, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('TotalSeconds=0', '0', Lines.Strings[0]);
    AssertEquals('Hours=0',        '0', Lines.Strings[1]);
    AssertEquals('Minutes=0',      '0', Lines.Strings[2]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_MakeInstantUtc_RoundTrip;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInstantUtcRoundTrip, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Year=2025',   '2025', Lines.Strings[0]);
    AssertEquals('Month=5',     '5',    Lines.Strings[1]);
    AssertEquals('Day=15',      '15',   Lines.Strings[2]);
    AssertEquals('Hour=14',     '14',   Lines.Strings[3]);
    AssertEquals('Minute=30',   '30',   Lines.Strings[4]);
    AssertEquals('Second=45',   '45',   Lines.Strings[5]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_Instant_ToUnixSeconds;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInstantToUnixSeconds, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('ToUnixSeconds=1', '1',    Lines.Strings[0]);
    AssertEquals('ToUnixMillis=1000', '1000', Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_Instant_AddDuration;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInstantAddDuration, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Hour=1 after +3600s', '1', Lines.Strings[0]);
    AssertEquals('Min=0',               '0', Lines.Strings[1]);
    AssertEquals('Sec=0',               '0', Lines.Strings[2]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_Instant_SubtractDuration;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInstantSubtractDuration, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Hour=0 after -3600s',   '0', Lines.Strings[0]);
    AssertEquals('Day=1 (no day change)', '1', Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_Instant_Subtract;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInstantSubtract, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('Diff=3s', '3', Trim(Output));
end;

procedure TE2EDateUtilsTests.TestRun_Instant_IsAfter_IsBefore;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInstantIsAfterIsBefore, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('A.IsBefore(B)=true',  'True',  Lines.Strings[0]);
    AssertEquals('A.IsAfter(B)=false',  'False', Lines.Strings[1]);
    AssertEquals('B.IsAfter(A)=true',   'True',  Lines.Strings[2]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_Instant_Equals;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInstantEquals, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('A.Equals(B)=true',  'True',  Lines.Strings[0]);
    AssertEquals('A.Equals(C)=false', 'False', Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_Instant_ToStringOffset;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInstantToStringOffset, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('UTC string',    '2025-05-15T14:30:45Z',       Lines.Strings[0]);
    AssertEquals('+05:30 string', '2025-05-15T20:00:45+05:30',  Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_Instant_ToLocalDateTime;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcInstantToLocalDateTime, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    { 14:00 UTC + 05:30 = 19:30 local }
    AssertEquals('Hour=19',   '19', Lines.Strings[0]);
    AssertEquals('Minute=30', '30', Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_Duration_TotalAccessors;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDurationTotalAccessors, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('TotalSeconds=9010',       '9010',    Lines.Strings[0]);
    AssertEquals('TotalMilliseconds=9010000','9010000', Lines.Strings[1]);
    AssertEquals('TotalMinutes=150',         '150',     Lines.Strings[2]);
    AssertEquals('TotalHours=2',             '2',       Lines.Strings[3]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_Duration_ToString;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDurationToString, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('3661s = PT1H1M1S',    'PT1H1M1S',  Lines.Strings[0]);
    AssertEquals('86400s = PT24H',      'PT24H',     Lines.Strings[1]);
    AssertEquals('0s = PT0S',           'PT0S',      Lines.Strings[2]);
    AssertEquals('59s = PT59S',         'PT59S',     Lines.Strings[3]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_Duration_Negative;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDurationNegative, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('IsNegative=true',       'True',  Lines.Strings[0]);
    AssertEquals('Abs.IsNegative=false',  'False', Lines.Strings[1]);
    AssertEquals('Abs.TotalSeconds=120',  '120', Lines.Strings[2]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_DurationAdd_Subtract;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDurationAddSubtract, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Add=150s',      '150',  Lines.Strings[0]);
    AssertEquals('Subtract=50s',  '50',   Lines.Strings[1]);
    AssertEquals('Negate=-100s',  '-100', Lines.Strings[2]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_ParseDate;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcParseDate, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Year=2025',         '2025',       Lines.Strings[0]);
    AssertEquals('Month=5',           '5',          Lines.Strings[1]);
    AssertEquals('Day=15',            '15',         Lines.Strings[2]);
    AssertEquals('ToString round-trip','2025-05-15', Lines.Strings[3]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_ParseTime;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcParseTime, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Hour=14',            '14',      Lines.Strings[0]);
    AssertEquals('Minute=30',          '30',      Lines.Strings[1]);
    AssertEquals('Second=45',          '45',      Lines.Strings[2]);
    AssertEquals('ToString round-trip','14:30:45', Lines.Strings[3]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_ParseDateTime;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcParseDateTime, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Year=2025',   '2025',               Lines.Strings[0]);
    AssertEquals('Month=5',     '5',                  Lines.Strings[1]);
    AssertEquals('Day=15',      '15',                 Lines.Strings[2]);
    AssertEquals('Hour=14',     '14',                 Lines.Strings[3]);
    AssertEquals('Minute=30',   '30',                 Lines.Strings[4]);
    AssertEquals('Second=45',   '45',                 Lines.Strings[5]);
    AssertEquals('ToString',    '2025-05-15T14:30:45', Lines.Strings[6]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_ParseInstant_UTC;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcParseInstantUTC, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Year=2025',   '2025',                  Lines.Strings[0]);
    AssertEquals('Month=5',     '5',                     Lines.Strings[1]);
    AssertEquals('Day=15',      '15',                    Lines.Strings[2]);
    AssertEquals('Hour=14',     '14',                    Lines.Strings[3]);
    AssertEquals('Minute=30',   '30',                    Lines.Strings[4]);
    AssertEquals('Second=45',   '45',                    Lines.Strings[5]);
    AssertEquals('ToString',    '2025-05-15T14:30:45Z',  Lines.Strings[6]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_ParseInstant_Offset;
var
  Output: string;
  RCode:  Int;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcParseInstantOffset, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('offset == UTC equivalent', 'True', Trim(Output));
end;

procedure TE2EDateUtilsTests.TestRun_ParseDuration;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcParseDuration, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    { 3*3600 + 25*60 + 10 = 10800 + 1500 + 10 = 12310 }
    AssertEquals('PT3H25M10S seconds=12310', '12310',      Lines.Strings[0]);
    AssertEquals('PT3H25M10S round-trip',    'PT3H25M10S', Lines.Strings[1]);
    AssertEquals('PT0S seconds=0',           '0',          Lines.Strings[2]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_ParseOffset;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcParseOffset, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('+05:30 = 19800s',  '19800',  Lines.Strings[0]);
    AssertEquals('-08:00 = -28800s', '-28800', Lines.Strings[1]);
    AssertEquals('Z = 0s',           '0',      Lines.Strings[2]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_IsLeapYear;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcIsLeapYear, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('2000 is leap',  'True',  Lines.Strings[0]);
    AssertEquals('1900 not leap', 'False', Lines.Strings[1]);
    AssertEquals('2024 is leap',  'True',  Lines.Strings[2]);
    AssertEquals('2025 not leap', 'False', Lines.Strings[3]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_DaysInMonth;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDaysInMonth, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Feb 2024 leap=29',  '29', Lines.Strings[0]);
    AssertEquals('Feb 2025 non=28',   '28', Lines.Strings[1]);
    AssertEquals('Jan=31',            '31', Lines.Strings[2]);
    AssertEquals('Apr=30',            '30', Lines.Strings[3]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_DayOfWeek;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDayOfWeek, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('2025-05-15 Thursday=4 (free fn)', '4', Lines.Strings[0]);
    AssertEquals('2025-05-15 Thursday=4 (method)',  '4', Lines.Strings[1]);
    AssertEquals('2025-05-19 Monday=1',             '1', Lines.Strings[2]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_DateAddDays;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  { Dual-backend again: the native segfault on DateAddDays(MakeDate(...), 5) was
    a stack-alignment bug in the record-call-argument hoist (buffer 16 + 8-byte
    saved pointer = 24, leaving %rsp 8 off 16-alignment), which only faulted once
    the callee chain reached a movdqa (libm mktime).  Fixed by padding the hoist
    region to a 16-byte multiple. }
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDateAddDays, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Jan 30 +5 days = Feb 4', '2025-02-04', Lines.Strings[0]);
    AssertEquals('Dec 31 +1 day = Jan 1',  '2025-01-01', Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_DateAddMonths_Clamp;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDateAddMonthsClamp, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('Jan31+1m(2025)=Feb28', '2025-02-28', Lines.Strings[0]);
    AssertEquals('Jan31+1m(2024)=Feb29', '2024-02-29', Lines.Strings[1]);
    AssertEquals('Nov15+3m=Feb15',       '2026-02-15', Lines.Strings[2]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_DateAddYears;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDateAddYears, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('2025-05-15 +3y = 2028-05-15', '2028-05-15', Lines.Strings[0]);
    AssertEquals('2024-02-29 +1y = 2025-02-28', '2025-02-28', Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_DateDiffDays;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcDateDiffDays, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('B-A = 10 days',  '10',  Lines.Strings[0]);
    AssertEquals('A-B = -10 days', '-10', Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_SystemOffset;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcSystemOffset, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    AssertEquals('>= -50400s', 'True', Lines.Strings[0]);
    AssertEquals('<= +50400s', 'True', Lines.Strings[1]);
  finally
    Lines.Free()
  end
end;

procedure TE2EDateUtilsTests.TestRun_MakeInstantLocal;
var
  Output: string;
  RCode:  Int;
  Lines:  TStringList;
begin
  if not ToolchainAvailable() then begin Fail('<toolchain-missing>'); Exit end;
  AssertTrue('compile+run', CompileAndRunWithRTL(SrcMakeInstantLocal, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  Lines := TStringList.Create();
  try
    Lines.Text := Trim(Output);
    { 19:30:45 local +05:30 → 14:00:45 UTC }
    AssertEquals('UTC Hour=14',   '14', Lines.Strings[0]);
    AssertEquals('UTC Minute=0',  '0',  Lines.Strings[1]);
    AssertEquals('UTC Second=45', '45', Lines.Strings[2]);
  finally
    Lines.Free()
  end
end;

initialization
  RegisterTest(TE2EDateUtilsTests);

end.
