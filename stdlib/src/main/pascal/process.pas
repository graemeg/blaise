{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Process;

// Blaise RTL — Process unit.
//
// Provides TProcess: a class for launching subprocesses and capturing
// their combined stdout+stderr output.  The implementation delegates to
// C helpers in blaise_process.c via compiler built-ins.
//
// Usage pattern (compatible with the FPC Process unit for the methods
// that Blaise.pas uses):
//
//   Proc := TProcess.Create(nil);
//   Proc.Executable := 'qbe';
//   Proc.Parameters.Add('-o');
//   Proc.Parameters.Add(OutFile);
//   Proc.Execute;                     // non-blocking fork+exec
//   repeat
//     Chunk := Proc.ReadOutput;       // blocking read, '' = EOF
//     Output := Output + Chunk;
//   until (Chunk = '') and not Proc.Running;
//   Proc.WaitOnExit;
//   ExitCode := Proc.ExitCode;
//   Proc.Free;

interface

uses Generics.Collections;

type
  TProcess = class
    FHandle: Pointer;
    FExe: string;
    FParameters: TList<string>;
    function GetRunning: Boolean;
    function GetExitCode: Integer;
    constructor Create(AOwner: TObject);
    destructor Destroy; override;
    procedure Execute;
    function ReadOutput: string;
    procedure WaitOnExit;
    property Executable: string read FExe write FExe;
    property Parameters: TList<string> read FParameters;
    property Running: Boolean read GetRunning;
    property ExitCode: Integer read GetExitCode;
  end;

implementation

constructor TProcess.Create(AOwner: TObject);
begin
  Self.FHandle := ProcessCreate();
  Self.FParameters := TList<string>.Create()
end;

destructor TProcess.Destroy;
begin
  ProcessFree(Self.FHandle);
  Self.FParameters.Destroy()
end;

function TProcess.GetRunning: Boolean;
begin
  Result := ProcessRunning(Self.FHandle)
end;

function TProcess.GetExitCode: Integer;
begin
  Result := ProcessExitCode(Self.FHandle)
end;

procedure TProcess.Execute;
var
  I: Integer;
begin
  ProcessSetExe(Self.FHandle, Self.FExe);
  I := 0;
  while I < Self.FParameters.Count do
  begin
    ProcessAddArg(Self.FHandle, Self.FParameters.Get(I));
    I := I + 1
  end;
  ProcessExecute(Self.FHandle)
end;

function TProcess.ReadOutput: string;
begin
  Result := ProcessReadOutput(Self.FHandle)
end;

procedure TProcess.WaitOnExit;
begin
  ProcessWaitOnExit(Self.FHandle)
end;

end.
