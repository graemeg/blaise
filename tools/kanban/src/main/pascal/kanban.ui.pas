{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit kanban.ui;

interface

uses
  kanban.terminal, kanban.data, Classes, StrUtils;

type
  TViewMode = (vmBoard, vmDetail, vmInput);

  TKanbanUI = class
    FTerm: TTerminal;
    FBoard: TBoard;
    FActiveCol: Int;
    FActiveRow: Int;
    FViewMode: TViewMode;
    FDetailScroll: Int;
    FDetailTask: TTask;
    FInputBuf: string;
    FInputPrompt: string;
    FStatusMsg: string;
    FNeedsRedraw: Boolean;
    FPollCounter: Int;
    procedure DrawBoard;
    procedure DrawColumn(ColIndex: Int; Row, Col, Width, Height: Int);
    procedure DrawStatusBar;
    procedure DrawInputBar;
    procedure DrawDetailView;
    function ColumnTitle(ColIndex: Int): string;
    function ColumnStatus(ColIndex: Int): TTaskStatus;
    function ColumnColor(ColIndex: Int): Int;
    function GetActiveTask: TTask;
    procedure ClampRow;
    procedure HandleBoardKey(Key: Int);
    procedure HandleDetailKey(Key: Int);
    procedure HandleInputKey(Key: Int);
    procedure StartInput(const APrompt: string);
    procedure FinishInput;
    procedure CancelInput;
  public
    constructor Create(ATerm: TTerminal; ABoard: TBoard);
    procedure Run;
  end;

implementation

constructor TKanbanUI.Create(ATerm: TTerminal; ABoard: TBoard);
begin
  inherited Create();
  FTerm := ATerm;
  FBoard := ABoard;
  FActiveCol := 0;
  FActiveRow := 0;
  FViewMode := vmBoard;
  FDetailScroll := 0;
  FDetailTask := nil;
  FInputBuf := '';
  FInputPrompt := '';
  FStatusMsg := 'q:quit  a:add  d:delete  Enter:details  h/l:move task  ?:help';
  FNeedsRedraw := True;
  FPollCounter := 0
end;

function TKanbanUI.ColumnTitle(ColIndex: Int): string;
begin
  if ColIndex = 0 then Exit('Todo');
  if ColIndex = 1 then Exit('In Progress');
  Result := 'Done'
end;

function TKanbanUI.ColumnStatus(ColIndex: Int): TTaskStatus;
begin
  if ColIndex = 0 then Exit(tsTodo);
  if ColIndex = 1 then Exit(tsInProgress);
  Result := tsDone
end;

function TKanbanUI.ColumnColor(ColIndex: Int): Int;
begin
  if ColIndex = 0 then Exit(COLOR_CYAN);
  if ColIndex = 1 then Exit(COLOR_YELLOW);
  Result := COLOR_GREEN
end;

function TKanbanUI.GetActiveTask: TTask;
begin
  Result := FBoard.GetByStatusAt(Self.ColumnStatus(FActiveCol), FActiveRow)
end;

procedure TKanbanUI.ClampRow;
var
  MaxRow: Int;
begin
  MaxRow := FBoard.CountByStatus(Self.ColumnStatus(FActiveCol)) - 1;
  if MaxRow < 0 then MaxRow := 0;
  if FActiveRow > MaxRow then
    FActiveRow := MaxRow
end;

procedure TKanbanUI.DrawBoard;
var
  ColWidth, ContentH, I: Int;
begin
  FTerm.QuerySize();
  FTerm.BufClear();
  FTerm.HideCursor();
  FTerm.ClearScreen();

  FTerm.MoveTo(1, 1);
  FTerm.SetBold();
  FTerm.SetFg(COLOR_CYAN);
  FTerm.BufWrite(' KANBAN BOARD');
  FTerm.ResetAttr();
  FTerm.SetFg(COLOR_GREY);
  FTerm.BufWrite('  ' + FBoard.FilePath);
  FTerm.ResetAttr();

  ColWidth := (FTerm.Cols - 2) div 3;
  ContentH := FTerm.Rows - 4;
  if ContentH < 5 then ContentH := 5;

  I := 0;
  while I < 3 do
  begin
    Self.DrawColumn(I, 3, 1 + I * ColWidth, ColWidth, ContentH);
    I := I + 1
  end;

  Self.DrawStatusBar();
  FTerm.BufFlush()
end;

procedure TKanbanUI.DrawColumn(ColIndex: Int; Row, Col, Width, Height: Int);
var
  TaskCount, I, Y, MaxW: Int;
  Task: TTask;
  Line, Prefix, PrioStr: string;
  IsActive: Boolean;
  Status: TTaskStatus;
begin
  FTerm.DrawBox(Row, Col, Width, Height, Self.ColumnColor(ColIndex), Self.ColumnTitle(ColIndex));

  Status := Self.ColumnStatus(ColIndex);
  TaskCount := FBoard.CountByStatus(Status);
  MaxW := Width - 4;
  if MaxW < 10 then MaxW := 10;

  I := 0;
  while I < TaskCount do
  begin
    Y := Row + 1 + I;
    if Y >= Row + Height - 1 then Break;

    Task := FBoard.GetByStatusAt(Status, I);
    IsActive := (ColIndex = FActiveCol) and (I = FActiveRow);

    FTerm.MoveTo(Y, Col + 1);

    if IsActive then
    begin
      FTerm.SetBg(Self.ColumnColor(ColIndex));
      FTerm.BufWrite(Chr(27) + '[38;5;0m')
    end;

    Prefix := ' ';
    if FBoard.HasDetail(Task.Id) then
      Prefix := '+';

    PrioStr := '';
    if Task.Priority = 'high' then
      PrioStr := '! '
    else if Task.Priority = 'low' then
      PrioStr := '. ';

    Line := Prefix + PrioStr + Task.Title;
    if Length(Line) > MaxW then
      Line := Copy(Line, 0, MaxW - 1) + '~';

    FTerm.BufWrite(Line);

    if IsActive then
      FTerm.BufWrite(DupeString(' ', MaxW - Length(Line) + 2));

    FTerm.ResetAttr();

    I := I + 1
  end;

  if TaskCount = 0 then
  begin
    FTerm.MoveTo(Row + 1, Col + 2);
    FTerm.SetFg(COLOR_GREY);
    FTerm.BufWrite('(empty)');
    FTerm.ResetAttr()
  end
end;

procedure TKanbanUI.DrawStatusBar;
var
  Pad: Int;
begin
  FTerm.MoveTo(FTerm.Rows, 1);
  FTerm.SetBg(COLOR_WHITE);
  FTerm.BufWrite(Chr(27) + '[38;5;0m');
  FTerm.BufWrite(' ' + FStatusMsg);
  Pad := FTerm.Cols - Length(FStatusMsg) - 1;
  if Pad > 0 then
    FTerm.BufWrite(DupeString(' ', Pad));
  FTerm.ResetAttr()
end;

procedure TKanbanUI.DrawInputBar;
begin
  FTerm.MoveTo(FTerm.Rows, 1);
  FTerm.ResetAttr();
  FTerm.BufWrite(DupeString(' ', FTerm.Cols));
  FTerm.MoveTo(FTerm.Rows, 1);
  FTerm.SetBold();
  FTerm.BufWrite(FInputPrompt);
  FTerm.ResetAttr();
  FTerm.BufWrite(FInputBuf);
  FTerm.ShowCursor();
  FTerm.BufFlush()
end;

procedure TKanbanUI.DrawDetailView;
var
  Content: string;
  Lines: TStringList;
  I, Y, StartLine: Int;
  Line, StatusBar: string;
begin
  if FDetailTask = nil then Exit;

  FTerm.QuerySize();
  FTerm.BufClear();
  FTerm.HideCursor();
  FTerm.ClearScreen();

  FTerm.MoveTo(1, 1);
  FTerm.SetBold();
  FTerm.SetFg(COLOR_CYAN);
  FTerm.BufWrite(' Task #' + IntToStr(FDetailTask.Id) + ': ');
  FTerm.ResetAttr();
  FTerm.SetBold();
  FTerm.BufWrite(FDetailTask.Title);
  FTerm.ResetAttr();

  FTerm.MoveTo(2, 1);
  FTerm.SetFg(COLOR_GREY);
  FTerm.BufWrite(' Status: ' + Self.ColumnTitle(FActiveCol));
  if Length(FDetailTask.Priority) > 0 then
    FTerm.BufWrite('  Priority: ' + FDetailTask.Priority);
  if Length(FDetailTask.Created) > 0 then
    FTerm.BufWrite('  Created: ' + CreatedToLocalDate(FDetailTask.Created));
  FTerm.ResetAttr();

  FTerm.DrawHLine(3, 1, FTerm.Cols);

  Content := FBoard.LoadDetail(FDetailTask.Id);
  if Length(Content) = 0 then
  begin
    FTerm.MoveTo(5, 3);
    FTerm.SetFg(COLOR_GREY);
    FTerm.BufWrite('No details yet. Press ''e'' to edit with $EDITOR.');
    FTerm.ResetAttr()
  end
  else
  begin
    Lines := TStringList.Create();
    Lines.Text := Content;
    StartLine := FDetailScroll;
    if StartLine > Lines.Count - 1 then
      StartLine := Lines.Count - 1;
    if StartLine < 0 then StartLine := 0;

    I := StartLine;
    Y := 4;
    while (I < Lines.Count) and (Y <= FTerm.Rows - 2) do
    begin
      FTerm.MoveTo(Y, 2);
      Line := Lines.Get(I);
      if Length(Line) > FTerm.Cols - 3 then
        Line := Copy(Line, 0, FTerm.Cols - 3);
      FTerm.BufWrite(Line);
      I := I + 1;
      Y := Y + 1
    end
  end;

  StatusBar := ' Esc:back  e:edit  j/k:scroll';
  FTerm.MoveTo(FTerm.Rows, 1);
  FTerm.SetBg(COLOR_WHITE);
  FTerm.BufWrite(Chr(27) + '[38;5;0m');
  FTerm.BufWrite(StatusBar);
  FTerm.BufWrite(DupeString(' ', FTerm.Cols - Length(StatusBar)));
  FTerm.ResetAttr();

  FTerm.BufFlush()
end;

procedure TKanbanUI.StartInput(const APrompt: string);
begin
  FViewMode := vmInput;
  FInputPrompt := APrompt;
  FInputBuf := '';
  Self.DrawInputBar()
end;

procedure TKanbanUI.FinishInput;
begin
  FViewMode := vmBoard;
  FNeedsRedraw := True
end;

procedure TKanbanUI.CancelInput;
begin
  FInputBuf := '';
  FViewMode := vmBoard;
  FNeedsRedraw := True
end;

procedure TKanbanUI.HandleBoardKey(Key: Int);
var
  Task: TTask;
  NewStatus: TTaskStatus;
begin
  if Key = KEY_NONE then Exit;

  if (Key = 113) or (Key = 81) then
  begin
    FTerm.ClearScreen();
    FTerm.ShowCursor();
    FTerm.BufFlush();
    FTerm.DisableRawMode();
    FBoard.MergeFromDisk();
    FBoard.Save();
    Halt(0)
  end;

  if (Key = KEY_DOWN) or (Key = 106) then
  begin
    FActiveRow := FActiveRow + 1;
    Self.ClampRow();
    FNeedsRedraw := True;
    Exit
  end;

  if (Key = KEY_UP) or (Key = 107) then
  begin
    if FActiveRow > 0 then
      FActiveRow := FActiveRow - 1;
    FNeedsRedraw := True;
    Exit
  end;

  if Key = KEY_TAB then
  begin
    FActiveCol := (FActiveCol + 1) mod 3;
    Self.ClampRow();
    FNeedsRedraw := True;
    Exit
  end;

  if (Key = KEY_RIGHT) or (Key = KEY_LEFT) then
  begin
    if Key = KEY_RIGHT then
      FActiveCol := (FActiveCol + 1) mod 3
    else
    begin
      FActiveCol := FActiveCol - 1;
      if FActiveCol < 0 then FActiveCol := 2
    end;
    Self.ClampRow();
    FNeedsRedraw := True;
    Exit
  end;

  // 'a' — add task
  if Key = 97 then
  begin
    Self.StartInput('New task: ');
    Exit
  end;

  // 'd' — delete task
  if Key = 100 then
  begin
    Task := Self.GetActiveTask();
    if Task <> nil then
    begin
      FBoard.DeleteTask(Task.Id);
      FBoard.Save();
      Self.ClampRow();
      FStatusMsg := 'Task deleted.';
      FNeedsRedraw := True
    end;
    Exit
  end;

  // Enter — open detail view
  if Key = KEY_ENTER then
  begin
    Task := Self.GetActiveTask();
    if Task <> nil then
    begin
      FDetailTask := Task;
      FDetailScroll := 0;
      FViewMode := vmDetail;
      FNeedsRedraw := True
    end;
    Exit
  end;

  // 'h' — move task left (toward Todo)
  if Key = 104 then
  begin
    Task := Self.GetActiveTask();
    if Task <> nil then
    begin
      if Task.Status = tsInProgress then
        NewStatus := tsTodo
      else if Task.Status = tsDone then
        NewStatus := tsInProgress
      else
        Exit;
      FBoard.MoveTask(Task.Id, NewStatus);
      FActiveCol := FActiveCol - 1;
      if FActiveCol < 0 then FActiveCol := 0;
      Self.ClampRow();
      FBoard.Save();
      FStatusMsg := 'Moved: ' + Task.Title;
      FNeedsRedraw := True
    end;
    Exit
  end;

  // 'l' — move task right (toward Done)
  if Key = 108 then
  begin
    Task := Self.GetActiveTask();
    if Task <> nil then
    begin
      if Task.Status = tsTodo then
        NewStatus := tsInProgress
      else if Task.Status = tsInProgress then
        NewStatus := tsDone
      else
        Exit;
      FBoard.MoveTask(Task.Id, NewStatus);
      FActiveCol := FActiveCol + 1;
      if FActiveCol > 2 then FActiveCol := 2;
      Self.ClampRow();
      FBoard.Save();
      FStatusMsg := 'Moved: ' + Task.Title;
      FNeedsRedraw := True
    end;
    Exit
  end;

  // 'p' — cycle priority
  if Key = 112 then
  begin
    Task := Self.GetActiveTask();
    if Task <> nil then
    begin
      if Task.Priority = '' then
        Task.Priority := 'high'
      else if Task.Priority = 'high' then
        Task.Priority := 'low'
      else
        Task.Priority := '';
      FBoard.Save();
      FStatusMsg := 'Priority: ' + Task.Title;
      FNeedsRedraw := True
    end;
    Exit
  end;

  // '?' — help
  if Key = 63 then
  begin
    FStatusMsg := 'j/k:up/down  Tab/arrows:columns  a:add  d:delete  h/l:move  p:priority  Enter:details  q:quit';
    FNeedsRedraw := True;
    Exit
  end
end;

procedure TKanbanUI.HandleDetailKey(Key: Int);
var
  Editor, Cmd, Path: string;
  ExitCode: Int;
begin
  if Key = KEY_NONE then Exit;

  if Key = KEY_ESCAPE then
  begin
    FViewMode := vmBoard;
    FNeedsRedraw := True;
    Exit
  end;

  // scroll down
  if (Key = KEY_DOWN) or (Key = 106) then
  begin
    FDetailScroll := FDetailScroll + 1;
    FNeedsRedraw := True;
    Exit
  end;

  // scroll up
  if (Key = KEY_UP) or (Key = 107) then
  begin
    if FDetailScroll > 0 then
      FDetailScroll := FDetailScroll - 1;
    FNeedsRedraw := True;
    Exit
  end;

  // 'e' — edit in $EDITOR
  if Key = 101 then
  begin
    if FDetailTask = nil then Exit;
    Path := FBoard.GetDetailPath(FDetailTask.Id);
    if not FBoard.HasDetail(FDetailTask.Id) then
      FBoard.SaveDetail(FDetailTask.Id, '');

    Editor := GetEnvVar('EDITOR');
    if Length(Editor) = 0 then
      Editor := 'nano';

    FTerm.ClearScreen();
    FTerm.ShowCursor();
    FTerm.BufFlush();
    FTerm.DisableRawMode();

    Cmd := Editor + ' ' + Path;
    ExitCode := Exec(Cmd);

    FTerm.EnableRawMode();
    FNeedsRedraw := True;
    Exit
  end
end;

procedure TKanbanUI.HandleInputKey(Key: Int);
var
  Task: TTask;
begin
  if Key = KEY_NONE then Exit;

  if Key = KEY_ESCAPE then
  begin
    Self.CancelInput();
    Exit
  end;

  if Key = KEY_ENTER then
  begin
    if Length(FInputBuf) > 0 then
    begin
      Task := FBoard.AddTask(FInputBuf, Self.ColumnStatus(FActiveCol));
      FBoard.Save();
      FStatusMsg := 'Added: ' + FInputBuf
    end;
    Self.FinishInput();
    Exit
  end;

  if Key = KEY_BACKSPACE then
  begin
    if Length(FInputBuf) > 0 then
      FInputBuf := Copy(FInputBuf, 0, Length(FInputBuf) - 1);
    Self.DrawInputBar();
    Exit
  end;

  if (Key >= 32) and (Key < 127) then
  begin
    FInputBuf := FInputBuf + Chr(Key);
    Self.DrawInputBar();
    Exit
  end
end;

procedure TKanbanUI.Run;
var
  Key, Merged: Int;
begin
  FTerm.EnableRawMode();
  try
    while True do
    begin
      if FNeedsRedraw then
      begin
        if FViewMode = vmBoard then
          Self.DrawBoard()
        else if FViewMode = vmDetail then
          Self.DrawDetailView();
        FNeedsRedraw := False
      end;

      Key := FTerm.ReadKey();

      if Key = KEY_NONE then
      begin
        FPollCounter := FPollCounter + 1;
        if FPollCounter >= 20 then
        begin
          FPollCounter := 0;
          if FBoard.HasExternalChanges() then
          begin
            Merged := FBoard.MergeFromDisk();
            if Merged > 0 then
            begin
              FStatusMsg := 'Reloaded ' + IntToStr(Merged) + ' new task(s) from disk';
              Self.ClampRow();
              FNeedsRedraw := True
            end
          end
        end
      end
      else
        FPollCounter := 0;

      if FViewMode = vmBoard then
        Self.HandleBoardKey(Key)
      else if FViewMode = vmDetail then
        Self.HandleDetailKey(Key)
      else if FViewMode = vmInput then
        Self.HandleInputKey(Key)
    end
  finally
    FTerm.ClearScreen();
    FTerm.ShowCursor();
    FTerm.BufFlush();
    FTerm.DisableRawMode()
  end
end;

end.
