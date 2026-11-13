{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}
unit iowatch.tests;

interface

uses
  IO.Files, SysUtils, Generics.Collections, blaise.testing, IO.Watch;

type
  TIOWatchTests = class(TTestCase)
  private
    FDir: string;
    procedure WriteText(const APath, AText: string);
    { The kinds reported for APath within a second, as 'C' and 'D'. }
    function Collect(W: TFileWatcher; const APath: string): string;
  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    procedure TestModifiedFile;
    procedure TestDeletedFile;
    procedure TestRenamedAway;
    procedure TestDirectoryEntries;
    procedure TestUnwatchAndMissing;
    procedure TestQuietTimesOut;
  end;

implementation

procedure TIOWatchTests.SetUp;
begin
  FDir := ExcludeTrailingPathDelimiter(GetTempDir()) + '/blaise-iowatch-' + IntToStr(GetProcessID());
  if GetFileKind(FDir, False) <> fkNone then
    DeleteTree(FDir);
  ForceDirectories(FDir);
end;

procedure TIOWatchTests.TearDown;
begin
  if GetFileKind(FDir, False) <> fkNone then
    DeleteTree(FDir);
end;

procedure TIOWatchTests.WriteText(const APath, AText: string);
begin
  WriteFile(APath, AText);
end;

function TIOWatchTests.Collect(W: TFileWatcher; const APath: string): string;
var
  Changes: TList<TFileChange>;
  I, Round: Int;
begin
  Result := '';
  for Round := 1 to 10 do
  begin
    Changes := W.Wait(100);
    for I := 0 to Changes.Count - 1 do
      if Changes[I].Path = APath then
        if Changes[I].Kind = fcDeleted then
          Result := Result + 'D'
        else if Pos('C', Result) < 0 then
          Result := Result + 'C';
    if Pos('D', Result) >= 0 then
      Exit;
  end;
end;

procedure TIOWatchTests.TestModifiedFile;
var
  W: TFileWatcher;
  P: string;
begin
  P := FDir + '/a.txt';
  WriteText(P, 'one');
  W := TFileWatcher.Create();
  AssertTrue(W.Watch(P));
  AssertTrue(W.Watching(P));
  WriteText(P, 'two');
  AssertEquals('C', Collect(W, P));
  AssertTrue('still watched after a change', W.Watching(P));
  WriteText(P, 'three');
  AssertEquals('again', 'C', Collect(W, P));
end;

procedure TIOWatchTests.TestDeletedFile;
var
  W: TFileWatcher;
  P: string;
begin
  P := FDir + '/a.txt';
  WriteText(P, 'one');
  W := TFileWatcher.Create();
  W.Watch(P);
  DeleteFile(P);
  AssertTrue(Pos('D', Collect(W, P)) >= 0);
  AssertFalse('a deleted file is no longer watched', W.Watching(P));
end;

procedure TIOWatchTests.TestRenamedAway;
var
  W: TFileWatcher;
  P: string;
begin
  { How editors save atomically: write a new file, rename it over the old. }
  P := FDir + '/a.txt';
  WriteText(P, 'one');
  W := TFileWatcher.Create();
  W.Watch(P);
  RenameFile(P, FDir + '/b.txt');
  AssertTrue(Pos('D', Collect(W, P)) >= 0);
end;

procedure TIOWatchTests.TestDirectoryEntries;
var
  W: TFileWatcher;
begin
  W := TFileWatcher.Create();
  AssertTrue(W.Watch(FDir));
  WriteText(FDir + '/c.txt', 'new');
  AssertEquals('a new entry changes the directory', 'C', Collect(W, FDir));
  DeleteFile(FDir + '/c.txt');
  AssertEquals('so does a removed one', 'C', Collect(W, FDir));
end;

procedure TIOWatchTests.TestUnwatchAndMissing;
var
  W: TFileWatcher;
  P: string;
begin
  P := FDir + '/a.txt';
  WriteText(P, 'one');
  W := TFileWatcher.Create();
  AssertFalse('a missing path cannot be watched', W.Watch(FDir + '/missing.txt'));
  W.Watch(P);
  W.Unwatch(P);
  AssertFalse(W.Watching(P));
  WriteText(P, 'two');
  AssertEquals('', Collect(W, P));
end;

procedure TIOWatchTests.TestQuietTimesOut;
var
  W: TFileWatcher;
begin
  W := TFileWatcher.Create();
  W.Watch(FDir);
  AssertEquals(0, W.Wait(50).Count);
end;

initialization
  RegisterTest(TIOWatchTests);
end.
