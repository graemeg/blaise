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
    u32 TextLen        u32 NRoutines    u32 NPtrs     u32 NSlots (total)
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
  { Range flags }
  UNW_F_SPANS_TRY = 2;         { open across a try: not released in the frame
                                 whose handler catches (that statement is
                                 still running and releases it) }

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

  { An owned temporary's live range: the frame owns the value at Loc from
    LoLbl up to HiLbl.  A depth range's Loc is a depth below the frame
    reserve, resolved to a frame-pointer offset when the routine ends. }
  TUnwFactRange = class
  public
    LoLbl, HiLbl: string;
    Loc: Int;
    Kind: Int;
    Flags: Int;
    Aux: Int;
    IsDepth: Boolean;
    { a call that can raise lies inside: a range without one is dropped
      (a raise cannot happen while it is open) }
    MayRaise: Boolean;
  end;

  TUnwRoutine = class
  public
    StartLbl, CovLoLbl, CovHiLbl, EndLbl: string;
    Slots: TList<TUnwFactSlot>;
    Ranges: TList<TUnwFactRange>;
    constructor Create(const AStart: string);
  end;

  TUnwindFacts = class
  private
    FRoutines: TList<TUnwRoutine>;
    FCur: TUnwRoutine;
    FLabelN: Int;
    FPrefix: string;
    FPtrs: TStringList;          { symbols of the block's Ptrs[] }
    FOpen: Int;                  { ranges open in the current routine }
    { the first routine's start label: the block's anchor, so the block
      covers every routine's code, recorded or not (a frame outside every
      block reads as foreign and ends the walk) }
    FFirstStart: string;
    FNoRaise: TStringList;       { sorted: helpers that cannot raise }
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
    { Open an owned temporary's range; ALbl is the label to emit at the
      point the frame starts to own it.  Returns a handle for CloseRange, or
      -1 outside a routine (a program main or unit initialisation, whose
      temporaries the tables do not describe), when ALbl is ''. }
    function OpenRange(AKind, ALoc, AFlags, AAux: Int; AIsDepth: Boolean;
      out ALbl: string): Int;
    { Close it: ALbl is to be emitted where ownership ends (before the
      release call, so a destructor that raises during it cannot make the
      walk release the value again). }
    procedure CloseRange(AHandle: Int; out ALbl: string);
    { The kind of a range opened before its value's kind was known. }
    procedure SetRangeKind(AHandle, AKind: Int);
    procedure SetRangeShape(AHandle, AKind, AFlags, AAux: Int);
    { Mark every open range as spanning a try (the backend is emitting one). }
    procedure NoteTry;
    { An emitted line: a call that can raise marks every open range. }
    procedure NoteLine(const ALine: string);
    function HasOpenRanges: Boolean;
    { AFrameReserve: the routine's final frame reserve, which resolves its
      depth ranges.  Every range must be closed. }
    procedure EndRoutine(const AEndLbl: string; AFrameReserve: Int = 0);
    { Forget the open routine (a backend that re-emits a routine). }
    procedure DiscardRoutine;
    function InRoutine: Boolean;
    { Rollback support for a backend that emits a routine twice and keeps
      the second attempt: the routines recorded since RoutineCount was N
      are dropped, and so is an open one. }
    function RoutineCount: Int;
    { some routine was emitted (so the end-of-text label has text to end) }
    function HasText: Boolean;
    procedure TruncateTo(N: Int);
    { the anchor so far ('' before the first routine), saved and restored
      around a rolled-back emission like RoutineCount }
    property FirstStart: string read FFirstStart write FFirstStart;
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
  Ranges := TList<TUnwFactRange>.Create();
end;

constructor TUnwindFacts.Create(const ALocalPrefix: string);
begin
  inherited Create();
  FRoutines := TList<TUnwRoutine>.Create();
  FPtrs := TStringList.Create();
  FPrefix := ALocalPrefix;
  { runtime helpers that neither raise nor run user code (a release that
    can run a destructor -- _ClassRelease, _DynArrayRelease -- is not here) }
  FNoRaise := TStringList.Create();
  FNoRaise.Sorted := True;
  FNoRaise.Add('StringAddRef');
  FNoRaise.Add('StringRelease');
  FNoRaise.Add('StringConcat');
  FNoRaise.Add('ClassAddRef');
  FNoRaise.Add('DynArrayAddRef');
  FNoRaise.Add('WeakAssign');
  FNoRaise.Add('WeakClear');
  FNoRaise.Add('Int64ToStr');
  FNoRaise.Add('UInt64ToStr');
  FNoRaise.Add('memcpy');
  FNoRaise.Add('memset');
  FNoRaise.Add('memmove');
end;

destructor TUnwindFacts.Destroy;
begin
  FRoutines.Free();
  FPtrs.Free();
  FNoRaise.Free();
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
  if FFirstStart = '' then
    FFirstStart := AStartLbl;
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

function TUnwindFacts.OpenRange(AKind, ALoc, AFlags, AAux: Int;
  AIsDepth: Boolean; out ALbl: string): Int;
var
  R: TUnwFactRange;
begin
  ALbl := '';
  Result := -1;
  if FCur = nil then Exit;
  R := TUnwFactRange.Create();
  R.LoLbl := NewLabel('rl');
  R.Kind := AKind;
  R.Loc := ALoc;
  R.Flags := AFlags;
  R.Aux := AAux;
  R.IsDepth := AIsDepth;
  FCur.Ranges.Add(R);
  FOpen := FOpen + 1;
  ALbl := R.LoLbl;
  Result := FCur.Ranges.Count - 1;
end;

procedure TUnwindFacts.CloseRange(AHandle: Int; out ALbl: string);
var
  R: TUnwFactRange;
begin
  ALbl := '';
  if (AHandle < 0) or (FCur = nil) then Exit;
  R := FCur.Ranges.Get(AHandle);
  if R.HiLbl <> '' then
    raise EUnwindFacts.Create('unwind facts: range ' + R.LoLbl +
      ' closed twice');
  R.HiLbl := NewLabel('rh');
  ALbl := R.HiLbl;
  FOpen := FOpen - 1;
end;

function TUnwindFacts.HasOpenRanges: Boolean;
begin
  Result := FOpen > 0;
end;

procedure TUnwindFacts.NoteLine(const ALine: string);
var
  P, E, I: Int;
  Sym: string;
begin
  if FOpen <= 0 then Exit;
  { #9'bl <sym>', #9'blr <reg>', #9'callq <sym>' or #9'callq *<reg>' }
  if (Length(ALine) < 4) or (ALine[0] <> 9) then Exit;
  if (ALine[1] = Ord('b')) and (ALine[2] = Ord('l')) then
  begin
    if ALine[3] = Ord('r') then
      P := -1                                    { blr: indirect }
    else if ALine[3] = Ord(' ') then
      P := 4
    else
      Exit;
  end
  else if Copy(ALine, 1, 6) = 'callq ' then
  begin
    P := 7;
    if (Length(ALine) > 7) and (ALine[7] = Ord('*')) then P := -1;
  end
  else
    Exit;
  if P >= 0 then
  begin
    E := Length(ALine);
    while (P < E) and (ALine[P] = Ord('_')) do P := P + 1;
    Sym := Copy(ALine, P, E - P);
    if FNoRaise.IndexOf(Sym) >= 0 then Exit;
  end;
  for I := 0 to FCur.Ranges.Count - 1 do
    if FCur.Ranges.Get(I).HiLbl = '' then
      FCur.Ranges.Get(I).MayRaise := True;
end;

procedure TUnwindFacts.SetRangeKind(AHandle, AKind: Int);
begin
  if (AHandle < 0) or (FCur = nil) then Exit;
  FCur.Ranges.Get(AHandle).Kind := AKind;
end;

procedure TUnwindFacts.SetRangeShape(AHandle, AKind, AFlags, AAux: Int);
var
  R: TUnwFactRange;
begin
  if (AHandle < 0) or (FCur = nil) then Exit;
  R := FCur.Ranges.Get(AHandle);
  R.Kind := AKind;
  R.Flags := (R.Flags and UNW_F_SPANS_TRY) or AFlags;
  R.Aux := AAux;
end;

procedure TUnwindFacts.NoteTry;
var
  I: Int;
begin
  if FCur = nil then Exit;
  for I := 0 to FCur.Ranges.Count - 1 do
    if FCur.Ranges.Get(I).HiLbl = '' then
      FCur.Ranges.Get(I).Flags := FCur.Ranges.Get(I).Flags or UNW_F_SPANS_TRY;
end;

procedure TUnwindFacts.EndRoutine(const AEndLbl: string; AFrameReserve: Int);
var
  I: Int;
  R: TUnwFactRange;
begin
  if FCur = nil then
    raise EUnwindFacts.Create('unwind facts: end outside a routine');
  if FCur.CovLoLbl = '' then
    raise EUnwindFacts.Create('unwind facts: routine ' + FCur.StartLbl +
      ' has no coverage');
  for I := 0 to FCur.Ranges.Count - 1 do
  begin
    R := FCur.Ranges.Get(I);
    if R.HiLbl = '' then
      raise EUnwindFacts.Create('unwind facts: range ' + R.LoLbl + ' in ' +
        FCur.StartLbl + ' is never closed');
    if R.IsDepth then
    begin
      R.Loc := -(AFrameReserve + R.Loc);
      R.IsDepth := False;
    end;
  end;
  { ranges no raise can happen in, or that release nothing (kind 0: a
    raise statement's operand base, left to leak), are of no use }
  for I := FCur.Ranges.Count - 1 downto 0 do
    if (not FCur.Ranges.Get(I).MayRaise) or (FCur.Ranges.Get(I).Kind = 0) then
      FCur.Ranges.Delete(I);
  FCur.EndLbl := AEndLbl;
  { a routine that owns nothing needs no record: the walk finds no routine
    for its frames and passes them by }
  if (FCur.Slots.Count > 0) or (FCur.Ranges.Count > 0) then
    FRoutines.Add(FCur);
  FCur := nil;
  FOpen := 0;
end;

procedure TUnwindFacts.DiscardRoutine;
begin
  FCur := nil;
  FOpen := 0;
end;

function TUnwindFacts.RoutineCount: Int;
begin
  Result := FRoutines.Count;
end;

function TUnwindFacts.HasText: Boolean;
begin
  Result := FFirstStart <> '';
end;

procedure TUnwindFacts.TruncateTo(N: Int);
begin
  FCur := nil;
  FOpen := 0;
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
  I, J, K, NSlots, NRanges, Bytes: Int;
  R: TUnwRoutine;
  S: TUnwFactSlot;
  G: TUnwFactRange;
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
  NRanges := 0;
  for I := 0 to FRoutines.Count - 1 do
  begin
    NSlots := NSlots + FRoutines.Get(I).Slots.Count;
    NRanges := NRanges + FRoutines.Get(I).Ranges.Count;
  end;
  Bytes := UNW_HDR_SIZE + FPtrs.Count * 8 + FRoutines.Count * UNW_ROUTINE_SIZE +
    NSlots * UNW_SLOT_SIZE + NRanges * UNW_RANGE_SIZE;
  { the anchor is the first routine emitted; an object with none (its text
    may be empty, so no label can go there) describes no text at all }
  Anchor := FFirstStart;
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
    W(#9 + AWord + ' ' + IntToStr(NSlots));
    for I := 0 to FPtrs.Count - 1 do
      W(#9'.quad ' + FPtrs.Strings[I]);
    J := 0;
    K := 0;
    for I := 0 to FRoutines.Count - 1 do
    begin
      R := FRoutines.Get(I);
      W(#9 + AWord + ' ' + R.StartLbl + ' - ' + Anchor);
      W(#9 + AWord + ' ' + R.EndLbl + ' - ' + R.StartLbl);
      W(#9 + AWord + ' ' + R.CovLoLbl + ' - ' + R.StartLbl);
      W(#9 + AWord + ' ' + R.CovHiLbl + ' - ' + R.StartLbl);
      W(#9 + AWord + ' ' + IntToStr(J));  { FirstSlot }
      W(#9 + AWord + ' ' + IntToStr(K));  { FirstRange }
      W(#9 + AWord + ' ' + IntToStr(R.Slots.Count));
      W(#9 + AWord + ' ' + IntToStr(R.Ranges.Count));
      J := J + R.Slots.Count;
      K := K + R.Ranges.Count;
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
    for I := 0 to FRoutines.Count - 1 do
    begin
      R := FRoutines.Get(I);
      for J := 0 to R.Ranges.Count - 1 do
      begin
        G := R.Ranges.Get(J);
        W(#9 + AWord + ' ' + G.LoLbl + ' - ' + R.StartLbl);
        W(#9 + AWord + ' ' + G.HiLbl + ' - ' + R.StartLbl);
        W(#9 + AWord + ' ' + IntToStr(G.Loc));
        W(#9 + AWord + ' ' + IntToStr(G.Kind or (G.Flags shl 8) or
          (G.Aux shl 16)));
      end;
    end;
    Result := SB.ToString();
  finally
    SB.Free();
  end;
end;

end.
