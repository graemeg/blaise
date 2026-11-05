{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
{
  Exception unwind facts: what each routine of one object owns, collected
  while a native backend emits the routine, and written at the end of the
  object as one unwind block in the unwind section (ELF blaise_unwind,
  Mach-O __DATA,__blaise_unw).  runtime.exc reads the blocks when an
  exception is raised and releases what a frame it unwinds past owns.
  See docs/exception-unwind-cleanup-design.adoc ("Table format").

  Block (8-aligned; all fields little-endian, code positions are 32-bit
  offsets from the block's anchor, the object's first routine):
    u32 Magic 'BUW1'   u32 Bytes        u64 Anchor
    u32 TextLen        u32 NRoutines    u32 NPtrs     u32 Reserved
    u64 Ptrs[NPtrs]
    Routine[NRoutines] (32 bytes): u32 Start, Len, CovLo, CovHi (CovLo and
      CovHi from Start), u32 FirstSlot, FirstRange, NSlots, NRanges
    Slot[...] (8 bytes): i32 Loc (frame-pointer offset), u8 Kind, u8 Flags,
      u16 Aux
    Range[...] (16 bytes): u32 Lo, Hi (from Start), i32 Loc, u8 Kind,
      u8 Flags, u16 Aux

  Labels are local and numbered by the collector, not by the backend, so
  the backend's own label numbering (and with it the rest of its output) is
  the same with and without the tables.
}
unit uUnwindFacts;

interface

uses
  SysUtils, Classes, StrUtils, Generics.Collections;

const
  UNW_MAGIC = 827807042;       { 'BUW1' as a little-endian u32 }
  UNW_HDR_SIZE = 32;
  UNW_ROUTINE_SIZE = 32;
  UNW_SLOT_SIZE = 8;
  UNW_RANGE_SIZE = 16;

  { Slot kinds, as runtime.exc reads them }
  UNW_STR = 1;
  UNW_CLASS = 2;
  UNW_INTF = 3;
  UNW_DYN = 4;
  UNW_REFENV = 5;
  UNW_WEAK = 6;
  UNW_AGG = 7;

  { Slot flags }
  UNW_F_INDIRECT = 1;          { the slot holds the value's address }

var
  { --no-unwind-tables: a diagnostic that suppresses every unwind label,
    block and call, for the .text identity test and the benchmark
    baseline (docs/exception-unwind-cleanup-design.adoc, D6).  Build with
    a fresh unit cache when comparing. }
  GNoUnwindTables: Boolean;

type
  EUnwindFacts = class(Exception);

  TUnwFactSlot = class
  public
    Loc: Int;
    Kind: Int;
    Flags: Int;
    Aux: Int;
  end;

  TUnwRoutine = class
  public
    StartLbl, CovLoLbl, CovHiLbl, EndLbl: string;
    Slots: TList<TUnwFactSlot>;
    constructor Create(const AStart: string);
  end;

  TUnwindFacts = class
  private
    FRoutines: TList<TUnwRoutine>;
    FCur: TUnwRoutine;
    FLabelN: Int;
    FPrefix: string;
    FPtrs: TStringList;          { symbols of the block's Ptrs[] }
  public
    { ALocalPrefix: the target's local-label prefix ('L' on Darwin, '.L' on
      ELF). }
    constructor Create(const ALocalPrefix: string);
    destructor Destroy; override;
    function NewLabel(const AName: string): string;
    { The routine whose code starts at AStartLbl; facts until EndRoutine
      belong to it.  Routines do not nest: their code is contiguous. }
    procedure BeginRoutine(const AStartLbl: string);
    { Slot coverage: from ALoLbl (after the prologue has zeroed every
      managed slot) up to AHiLbl (the exit label: the epilogue releases
      the slots itself and does not nil them). }
    procedure SetCoverage(const ALoLbl, AHiLbl: string);
    procedure AddSlot(ALoc, AKind, AFlags, AAux: Int);
    { The index of ASym in the block's pointer table (added once). }
    function AddPtr(const ASym: string): Int;
    procedure EndRoutine(const AEndLbl: string);
    { Forget the open routine (a backend that re-emits a routine). }
    procedure DiscardRoutine;
    function InRoutine: Boolean;
    { Rollback support for a backend that emits a routine twice and keeps
      the second attempt: the routines recorded since RoutineCount was N
      are dropped, and so is an open one. }
    function RoutineCount: Int;
    procedure TruncateTo(N: Int);
    { The object's block, as assembly: the section switch, then the block.
      AWord is the 32-bit data directive ('.word' on arm64, '.long' on
      x86-64), AAlign8 an 8-byte alignment directive, AHiLbl a label at the
      end of the object's text (unused, and need not be emitted, when no
      routine was recorded: see RoutineCount). }
    function BlockText(const ASection, AAlign8, AWord, AHiLbl: string): string;
  end;

implementation

constructor TUnwRoutine.Create(const AStart: string);
begin
  inherited Create();
  StartLbl := AStart;
  Slots := TList<TUnwFactSlot>.Create();
end;

constructor TUnwindFacts.Create(const ALocalPrefix: string);
begin
  inherited Create();
  FRoutines := TList<TUnwRoutine>.Create();
  FPtrs := TStringList.Create();
  FPrefix := ALocalPrefix;
end;

destructor TUnwindFacts.Destroy;
begin
  FRoutines.Free();
  FPtrs.Free();
  inherited Destroy();
end;

function TUnwindFacts.NewLabel(const AName: string): string;
begin
  Result := FPrefix + 'unw_' + AName + IntToStr(FLabelN);
  FLabelN := FLabelN + 1;
end;

procedure TUnwindFacts.BeginRoutine(const AStartLbl: string);
begin
  if FCur <> nil then
    raise EUnwindFacts.Create('unwind facts: routine ' + AStartLbl +
      ' begins inside routine ' + FCur.StartLbl);
  FCur := TUnwRoutine.Create(AStartLbl);
end;

procedure TUnwindFacts.SetCoverage(const ALoLbl, AHiLbl: string);
begin
  if FCur = nil then
    raise EUnwindFacts.Create('unwind facts: coverage outside a routine');
  FCur.CovLoLbl := ALoLbl;
  FCur.CovHiLbl := AHiLbl;
end;

procedure TUnwindFacts.AddSlot(ALoc, AKind, AFlags, AAux: Int);
var
  S: TUnwFactSlot;
begin
  if FCur = nil then
    raise EUnwindFacts.Create('unwind facts: slot outside a routine');
  S := TUnwFactSlot.Create();
  S.Loc := ALoc;
  S.Kind := AKind;
  S.Flags := AFlags;
  S.Aux := AAux;
  FCur.Slots.Add(S);
end;

function TUnwindFacts.AddPtr(const ASym: string): Int;
begin
  Result := FPtrs.IndexOf(ASym);
  if Result < 0 then
    Result := FPtrs.Add(ASym);
end;

procedure TUnwindFacts.EndRoutine(const AEndLbl: string);
begin
  if FCur = nil then
    raise EUnwindFacts.Create('unwind facts: end outside a routine');
  if FCur.CovLoLbl = '' then
    raise EUnwindFacts.Create('unwind facts: routine ' + FCur.StartLbl +
      ' has no coverage');
  FCur.EndLbl := AEndLbl;
  FRoutines.Add(FCur);
  FCur := nil;
end;

procedure TUnwindFacts.DiscardRoutine;
begin
  FCur := nil;
end;

function TUnwindFacts.RoutineCount: Int;
begin
  Result := FRoutines.Count;
end;

procedure TUnwindFacts.TruncateTo(N: Int);
begin
  FCur := nil;
  while FRoutines.Count > N do
    FRoutines.Delete(FRoutines.Count - 1);
end;

function TUnwindFacts.InRoutine: Boolean;
begin
  Result := FCur <> nil;
end;

function TUnwindFacts.BlockText(const ASection, AAlign8, AWord,
  AHiLbl: string): string;
var
  SB: TStringBuilder;
  I, J, NSlots, Bytes: Int;
  R: TUnwRoutine;
  S: TUnwFactSlot;
  Anchor: string;

  procedure W(const ALine: string);
  begin
    SB.Append(ALine);
    SB.Append(LineEnding);
  end;

begin
  if FCur <> nil then
    raise EUnwindFacts.Create('unwind facts: routine ' + FCur.StartLbl +
      ' still open at the end of the object');
  NSlots := 0;
  for I := 0 to FRoutines.Count - 1 do
    NSlots := NSlots + FRoutines.Get(I).Slots.Count;
  Bytes := UNW_HDR_SIZE + FPtrs.Count * 8 + FRoutines.Count * UNW_ROUTINE_SIZE +
    NSlots * UNW_SLOT_SIZE;
  { the anchor is the first routine; an object with none (its text may be
    empty, so no label can go there) describes no text at all }
  if FRoutines.Count > 0 then
    Anchor := FRoutines.Get(0).StartLbl
  else
    Anchor := '';
  SB := TStringBuilder.Create();
  try
    W(ASection);
    W(AAlign8);
    W(#9 + AWord + ' ' + IntToStr(UNW_MAGIC));
    W(#9 + AWord + ' ' + IntToStr(Bytes));
    if Anchor = '' then
    begin
      W(#9'.quad 0');
      W(#9 + AWord + ' 0');
    end
    else
    begin
      W(#9'.quad ' + Anchor);
      W(#9 + AWord + ' ' + AHiLbl + ' - ' + Anchor);
    end;
    W(#9 + AWord + ' ' + IntToStr(FRoutines.Count));
    W(#9 + AWord + ' ' + IntToStr(FPtrs.Count));
    W(#9 + AWord + ' 0');                 { Reserved }
    for I := 0 to FPtrs.Count - 1 do
      W(#9'.quad ' + FPtrs.Strings[I]);
    J := 0;
    for I := 0 to FRoutines.Count - 1 do
    begin
      R := FRoutines.Get(I);
      W(#9 + AWord + ' ' + R.StartLbl + ' - ' + Anchor);
      W(#9 + AWord + ' ' + R.EndLbl + ' - ' + R.StartLbl);
      W(#9 + AWord + ' ' + R.CovLoLbl + ' - ' + R.StartLbl);
      W(#9 + AWord + ' ' + R.CovHiLbl + ' - ' + R.StartLbl);
      W(#9 + AWord + ' ' + IntToStr(J));  { FirstSlot }
      W(#9 + AWord + ' 0');               { FirstRange }
      W(#9 + AWord + ' ' + IntToStr(R.Slots.Count));
      W(#9 + AWord + ' 0');               { NRanges }
      J := J + R.Slots.Count;
    end;
    for I := 0 to FRoutines.Count - 1 do
    begin
      R := FRoutines.Get(I);
      for J := 0 to R.Slots.Count - 1 do
      begin
        S := R.Slots.Get(J);
        W(#9 + AWord + ' ' + IntToStr(S.Loc));
        W(#9 + AWord + ' ' + IntToStr(S.Kind or (S.Flags shl 8) or
          (S.Aux shl 16)));
      end;
    end;
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

end.
