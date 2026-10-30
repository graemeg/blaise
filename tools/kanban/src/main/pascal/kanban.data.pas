{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit kanban.data;

interface

uses Classes, Contnrs, StrUtils, DateUtils;

type
  TTaskStatus = (tsTodo, tsInProgress, tsDone);

  TIntHolder = class
    FValue: Int;
  end;

  TTask = class
    FId: Int;
    FTitle: string;
    FStatus: TTaskStatus;
    FCreated: string;
    FPriority: string;
    property Id: Int read FId;
    property Title: string read FTitle write FTitle;
    property Status: TTaskStatus read FStatus write FStatus;
    property Created: string read FCreated;
    property Priority: string read FPriority write FPriority;
  end;

  TBoard = class
    FTasks: TObjectList;
    FNextId: Int;
    FFilePath: string;
    FLastMtime: Int64;
    FDeletedIds: TObjectList;
    function GetCount: Int;
    procedure ParseLine(const Line: string; CurrentStatus: TTaskStatus);
    function FormatTask(Task: TTask): string;
    function IsDeleted(AId: Int): Boolean;
  public
    constructor Create(const AFilePath: string);
    procedure Load;
    procedure Save;
    function AddTask(const ATitle: string; AStatus: TTaskStatus): TTask;
    procedure DeleteTask(AId: Int);
    procedure MoveTask(AId: Int; NewStatus: TTaskStatus);
    function FindById(AId: Int): TTask;
    function CountByStatus(AStatus: TTaskStatus): Int;
    function GetByStatusAt(AStatus: TTaskStatus; Index: Int): TTask;
    function GetDetailPath(AId: Int): string;
    function HasDetail(AId: Int): Boolean;
    function LoadDetail(AId: Int): string;
    procedure SaveDetail(AId: Int; const AContent: string);
    function HasExternalChanges: Boolean;
    function MergeFromDisk: Int;
    property Count: Int read GetCount;
    property FilePath: string read FFilePath;
  end;

function CreatedToLocalDate(const AUtcStr: string): string;

implementation

constructor TBoard.Create(const AFilePath: string);
begin
  inherited Create();
  FFilePath := AFilePath;
  FTasks := TObjectList.Create(True);
  FDeletedIds := TObjectList.Create(True);
  FNextId := 1;
  FLastMtime := -1
end;

function TBoard.GetCount: Int;
begin
  Result := FTasks.Count
end;

procedure TBoard.ParseLine(const Line: string; CurrentStatus: TTaskStatus);
var
  S, Part, Key, Val: string;
  Task: TTask;
  PipePos, EqPos, TaskId: Int;
begin
  S := Trim(Line);
  if Length(S) < 4 then Exit;
  if (S[0] <> '-') or (S[1] <> ' ') then Exit;

  S := Trim(Copy(S, 2, Length(S) - 2));

  PipePos := Pos('|', S);
  if PipePos < 0 then
  begin
    TaskId := StrToInt(Trim(S));
    Task := TTask.Create();
    Task.FId := TaskId;
    Task.FTitle := '(untitled)';
    Task.FStatus := CurrentStatus;
    Task.FCreated := '';
    Task.FPriority := '';
    FTasks.Add(Task);
    if TaskId >= FNextId then
      FNextId := TaskId + 1;
    Exit
  end;

  TaskId := StrToInt(Trim(Copy(S, 0, PipePos)));
  S := Trim(Copy(S, PipePos + 1, Length(S) - PipePos - 1));

  PipePos := Pos('|', S);
  if PipePos < 0 then
  begin
    Task := TTask.Create();
    Task.FId := TaskId;
    Task.FTitle := Trim(S);
    Task.FStatus := CurrentStatus;
    Task.FCreated := '';
    Task.FPriority := '';
    FTasks.Add(Task);
    if TaskId >= FNextId then
      FNextId := TaskId + 1;
    Exit
  end;

  Task := TTask.Create();
  Task.FId := TaskId;
  Task.FTitle := Trim(Copy(S, 0, PipePos));
  Task.FStatus := CurrentStatus;
  Task.FCreated := '';
  Task.FPriority := '';

  S := Trim(Copy(S, PipePos + 1, Length(S) - PipePos - 1));
  while Length(S) > 0 do
  begin
    PipePos := Pos('|', S);
    if PipePos < 0 then
    begin
      Part := Trim(S);
      S := ''
    end
    else
    begin
      Part := Trim(Copy(S, 0, PipePos));
      S := Trim(Copy(S, PipePos + 1, Length(S) - PipePos - 1))
    end;

    EqPos := Pos(':', Part);
    if EqPos >= 0 then
    begin
      Key := Trim(Copy(Part, 0, EqPos));
      Val := Trim(Copy(Part, EqPos + 1, Length(Part) - EqPos - 1));
      if Key = 'priority' then
        Task.FPriority := Val
      else if Key = 'created' then
        Task.FCreated := Val
    end
  end;

  FTasks.Add(Task);
  if Task.FId >= FNextId then
    FNextId := Task.FId + 1
end;

function TBoard.FormatTask(Task: TTask): string;
var
  S: string;
begin
  S := '- ' + IntToStr(Task.FId) + ' | ' + Task.FTitle;
  if Length(Task.FPriority) > 0 then
    S := S + ' | priority:' + Task.FPriority;
  if Length(Task.FCreated) > 0 then
    S := S + ' | created:' + Task.FCreated;
  Result := S
end;

procedure TBoard.Load;
var
  Lines: TStringList;
  I: Int;
  Line: string;
  CurrentStatus: TTaskStatus;
  IdLine: string;
begin
  if not FileExists(FFilePath) then Exit;

  Lines := TStringList.Create();
  Lines.LoadFromFile(FFilePath);
  CurrentStatus := tsTodo;
  I := 0;
  while I < Lines.Count do
  begin
    Line := Lines.Get(I);
    if StartsStr('## Todo', Line) then
      CurrentStatus := tsTodo
    else if StartsStr('## In Progress', Line) then
      CurrentStatus := tsInProgress
    else if StartsStr('## Done', Line) then
      CurrentStatus := tsDone
    else if StartsStr('#next-id:', Line) then
    begin
      IdLine := Trim(Copy(Line, 9, Length(Line) - 9));
      FNextId := StrToInt(IdLine)
    end
    else if StartsStr('- ', Line) then
      Self.ParseLine(Line, CurrentStatus);
    I := I + 1
  end;
  FLastMtime := FileAge(FFilePath)
end;

procedure TBoard.Save;
var
  Lines: TStringList;
  I: Int;
  Task: TTask;
begin
  if Self.HasExternalChanges() then
    Self.MergeFromDisk();
  Lines := TStringList.Create();
  Lines.Add('#next-id: ' + IntToStr(FNextId));
  Lines.Add('');
  Lines.Add('## Todo');
  I := 0;
  while I < FTasks.Count do
  begin
    Task := TTask(FTasks.Get(I));
    if Task.FStatus = tsTodo then
      Lines.Add(Self.FormatTask(Task));
    I := I + 1
  end;

  Lines.Add('');
  Lines.Add('## In Progress');
  I := 0;
  while I < FTasks.Count do
  begin
    Task := TTask(FTasks.Get(I));
    if Task.FStatus = tsInProgress then
      Lines.Add(Self.FormatTask(Task));
    I := I + 1
  end;

  Lines.Add('');
  Lines.Add('## Done');
  I := 0;
  while I < FTasks.Count do
  begin
    Task := TTask(FTasks.Get(I));
    if Task.FStatus = tsDone then
      Lines.Add(Self.FormatTask(Task));
    I := I + 1
  end;

  Lines.SaveToFile(FFilePath);
  FLastMtime := FileAge(FFilePath)
end;

function TBoard.AddTask(const ATitle: string; AStatus: TTaskStatus): TTask;
var
  Now: TInstant;
  UtcDT: TDateTime;
begin
  Now := InstantNow();
  UtcDT := Now.ToUtcDateTime();
  Result := TTask.Create();
  Result.FId := FNextId;
  Result.FTitle := ATitle;
  Result.FStatus := AStatus;
  Result.FCreated := UtcDT.ToString();
  Result.FPriority := '';
  FNextId := FNextId + 1;
  FTasks.Add(Result)
end;

function TBoard.IsDeleted(AId: Int): Boolean;
var
  I: Int;
begin
  I := 0;
  while I < FDeletedIds.Count do
  begin
    if TIntHolder(FDeletedIds.Get(I)).FValue = AId then
      Exit(True);
    I := I + 1
  end;
  Result := False
end;

procedure TBoard.DeleteTask(AId: Int);
var
  I: Int;
  Task: TTask;
  DetailPath: string;
  Holder: TIntHolder;
begin
  I := 0;
  while I < FTasks.Count do
  begin
    Task := TTask(FTasks.Get(I));
    if Task.FId = AId then
    begin
      DetailPath := Self.GetDetailPath(AId);
      if FileExists(DetailPath) then
        DeleteFile(DetailPath);
      FTasks.Delete(I);
      Holder := TIntHolder.Create();
      Holder.FValue := AId;
      FDeletedIds.Add(Holder);
      Exit
    end;
    I := I + 1
  end
end;

procedure TBoard.MoveTask(AId: Int; NewStatus: TTaskStatus);
var
  Task: TTask;
begin
  Task := Self.FindById(AId);
  if Task <> nil then
    Task.FStatus := NewStatus
end;

function TBoard.FindById(AId: Int): TTask;
var
  I: Int;
  Task: TTask;
begin
  I := 0;
  while I < FTasks.Count do
  begin
    Task := TTask(FTasks.Get(I));
    if Task.FId = AId then
      Exit(Task);
    I := I + 1
  end;
  Result := nil
end;

function TBoard.CountByStatus(AStatus: TTaskStatus): Int;
var
  I: Int;
  Task: TTask;
begin
  Result := 0;
  I := 0;
  while I < FTasks.Count do
  begin
    Task := TTask(FTasks.Get(I));
    if Task.FStatus = AStatus then
      Result := Result + 1;
    I := I + 1
  end
end;

function TBoard.GetByStatusAt(AStatus: TTaskStatus; Index: Int): TTask;
var
  I, Cnt: Int;
  Task: TTask;
begin
  Cnt := 0;
  I := 0;
  while I < FTasks.Count do
  begin
    Task := TTask(FTasks.Get(I));
    if Task.FStatus = AStatus then
    begin
      if Cnt = Index then
        Exit(Task);
      Cnt := Cnt + 1
    end;
    I := I + 1
  end;
  Result := nil
end;

function TBoard.GetDetailPath(AId: Int): string;
var
  DirPath: string;
begin
  DirPath := FFilePath + '.d';
  Result := DirPath + '/' + IntToStr(AId) + '.txt'
end;

function TBoard.HasDetail(AId: Int): Boolean;
begin
  Result := FileExists(Self.GetDetailPath(AId))
end;

function TBoard.LoadDetail(AId: Int): string;
var
  Path: string;
begin
  Path := Self.GetDetailPath(AId);
  if FileExists(Path) then
    Result := ReadFile(Path)
  else
    Result := ''
end;

procedure TBoard.SaveDetail(AId: Int; const AContent: string);
var
  DirPath: string;
begin
  DirPath := FFilePath + '.d';
  if not DirectoryExists(DirPath) then
    ForceDirectories(DirPath);
  WriteFile(Self.GetDetailPath(AId), AContent)
end;

function TBoard.HasExternalChanges: Boolean;
var
  CurrentMtime: Int64;
begin
  CurrentMtime := FileAge(FFilePath);
  Result := (CurrentMtime <> -1) and (CurrentMtime <> FLastMtime)
end;

function TBoard.MergeFromDisk: Int;
var
  DiskBoard: TBoard;
  I, Merged, MaxId: Int;
  DiskTask, MemTask, NewTask: TTask;
begin
  Merged := 0;
  DiskBoard := TBoard.Create(FFilePath);
  DiskBoard.Load();

  MaxId := FNextId;
  if DiskBoard.FNextId > MaxId then
    MaxId := DiskBoard.FNextId;

  I := 0;
  while I < DiskBoard.FTasks.Count do
  begin
    DiskTask := TTask(DiskBoard.FTasks.Get(I));
    if Self.IsDeleted(DiskTask.FId) then
    begin
      I := I + 1;
      Continue
    end;
    MemTask := Self.FindById(DiskTask.FId);
    if MemTask = nil then
    begin
      NewTask := TTask.Create();
      NewTask.FId := DiskTask.FId;
      NewTask.FTitle := DiskTask.FTitle;
      NewTask.FStatus := DiskTask.FStatus;
      NewTask.FCreated := DiskTask.FCreated;
      NewTask.FPriority := DiskTask.FPriority;
      FTasks.Add(NewTask);
      Merged := Merged + 1
    end
    else if MemTask.FTitle <> DiskTask.FTitle then
    begin
      MemTask.FId := MaxId;
      MaxId := MaxId + 1;
      NewTask := TTask.Create();
      NewTask.FId := DiskTask.FId;
      NewTask.FTitle := DiskTask.FTitle;
      NewTask.FStatus := DiskTask.FStatus;
      NewTask.FCreated := DiskTask.FCreated;
      NewTask.FPriority := DiskTask.FPriority;
      FTasks.Add(NewTask);
      Merged := Merged + 1
    end;
    I := I + 1
  end;
  FNextId := MaxId;
  FLastMtime := FileAge(FFilePath);
  Result := Merged
end;

function CreatedToLocalDate(const AUtcStr: string): string;
var
  UtcDT: TDateTime;
  Inst: TInstant;
  LocalDT: TDateTime;
begin
  if Length(AUtcStr) = 0 then
    Exit('');
  UtcDT := ParseDateTime(AUtcStr);
  Inst := MakeInstantUtc(UtcDT.Date, UtcDT.Time);
  LocalDT := Inst.ToLocalDateTime(SystemOffset());
  Result := LocalDT.Date.ToString()
end;

end.
