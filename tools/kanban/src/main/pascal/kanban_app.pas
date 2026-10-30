{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

program KanbanApp;

{ TUI Kanban board — a three-column task tracker.

  Interactive mode:
    kanban [board.kanban]

  CLI mode:
    kanban board.kanban --add "Task title"
    kanban board.kanban --add "Title" --detail "Detail text"
    kanban board.kanban --add "Title" --priority high
    kanban board.kanban --add "Title" --status progress
    kanban board.kanban --add "Title" --detail-file notes.txt }

uses
  kanban.terminal, kanban.data, kanban.ui, StrUtils;

var
  FilePath: string;
  Term: TTerminal;
  Board: TBoard;
  UI: TKanbanUI;
  I: Int;
  AddTitle: string;
  DetailText: string;
  DetailFile: string;
  PriorityVal: string;
  StatusVal: TTaskStatus;
  CliMode: Boolean;
  Task: TTask;
  Arg: string;

procedure PrintUsage;
begin
  WriteLn('Usage:');
  WriteLn('  kanban [board.kanban]                    Interactive TUI mode');
  WriteLn('  kanban board.kanban --add "Title"        Add a task from the CLI');
  WriteLn('');
  WriteLn('Options for --add:');
  WriteLn('  --detail "text"      Set detail text inline');
  WriteLn('  --detail-file path   Read detail text from a file');
  WriteLn('  --priority high|low  Set priority');
  WriteLn('  --status todo|progress|done  Set status (default: todo)');
  Halt(0)
end;

begin
  FilePath := 'board.kanban';
  AddTitle := '';
  DetailText := '';
  DetailFile := '';
  PriorityVal := '';
  StatusVal := tsTodo;
  CliMode := False;

  I := 1;
  while I <= ParamCount() do
  begin
    Arg := ParamStr(I);

    if (Arg = '--help') or (Arg = '-h') then
      PrintUsage()

    else if Arg = '--add' then
    begin
      CliMode := True;
      if I + 1 <= ParamCount() then
      begin
        I := I + 1;
        AddTitle := ParamStr(I)
      end
    end

    else if Arg = '--detail' then
    begin
      if I + 1 <= ParamCount() then
      begin
        I := I + 1;
        DetailText := ParamStr(I)
      end
    end

    else if Arg = '--detail-file' then
    begin
      if I + 1 <= ParamCount() then
      begin
        I := I + 1;
        DetailFile := ParamStr(I)
      end
    end

    else if Arg = '--priority' then
    begin
      if I + 1 <= ParamCount() then
      begin
        I := I + 1;
        PriorityVal := ParamStr(I)
      end
    end

    else if Arg = '--status' then
    begin
      if I + 1 <= ParamCount() then
      begin
        I := I + 1;
        Arg := ParamStr(I);
        if (Arg = 'progress') or (Arg = 'inprogress') then
          StatusVal := tsInProgress
        else if Arg = 'done' then
          StatusVal := tsDone
        else
          StatusVal := tsTodo
      end
    end

    else if not StartsStr('--', Arg) then
      FilePath := Arg;

    I := I + 1
  end;

  if CliMode then
  begin
    if Length(AddTitle) = 0 then
    begin
      WriteLn('Error: --add requires a task title');
      Halt(1)
    end;

    Board := TBoard.Create(FilePath);
    try
      Board.Load();
      Task := Board.AddTask(AddTitle, StatusVal);
      if Length(PriorityVal) > 0 then
        Task.Priority := PriorityVal;

      if Length(DetailFile) > 0 then
      begin
        if FileExists(DetailFile) then
          DetailText := ReadFile(DetailFile)
        else
        begin
          WriteLn('Error: file not found: ', DetailFile);
          Halt(1)
        end
      end;

      if Length(DetailText) > 0 then
        Board.SaveDetail(Task.Id, DetailText);

      Board.Save();
      WriteLn('Added task #', Task.Id, ': ', AddTitle)
    finally
      Board.Free()
    end
  end
  else
  begin
    Term := TTerminal.Create();
    Board := TBoard.Create(FilePath);
    UI := TKanbanUI.Create(Term, Board);
    try
      Board.Load();
      UI.Run()
    finally
      UI.Free();
      Board.Free();
      Term.Free()
    end
  end
end.
