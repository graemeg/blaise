{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit Net.Ftp.Server;

// L5 FTP wave: an FTP SERVER (RFC 959, passive mode) over Net.Tcp.  TFtpServer
// runs the fiber-per-control-connection accept loop of Net.Tcp.TTcpServer; each
// control connection gets a session fiber that:
//
//   * writes the 220 greeting,
//   * authenticates USER/PASS against a supplied IFtpFileStore,
//   * handles PWD/CWD/TYPE,
//   * on PASV opens an ephemeral data listener (OS-chosen port), replies 227
//     with the server's ip + that port, and accepts the client's data
//     connection ON THE SAME FIBER for the next transfer,
//   * RETR sends file bytes over the data connection (150/226 on control),
//   * STOR receives bytes to EOF and stores them,
//   * NLST / LIST send a directory listing over the data connection,
//   * DELE deletes a file,
//   * QUIT replies 221 and closes.
//
// The virtual filesystem is behind IFtpFileStore so the application (or a test)
// supplies any backing store - an in-memory map, a rooted real directory, etc.
// The data channel is a short-lived accept-per-transfer on the control fiber
// (one transfer at a time per session, which is the FTP model).
//
// PASSIVE mode only (ACTIVE / PORT deferred).  Plaintext (internal linker);
// FTPS deferred.  NATIVE BACKEND ONLY.

interface

uses
  SysUtils, Net.Tcp, async.fibers;

type
  { The application-supplied virtual filesystem + authenticator.  All paths are
    whatever the client sends (the server does not itself impose a layout); an
    implementation is free to root them under a real directory or key an
    in-memory map.  A listing is returned as bare names separated by LF. }
  IFtpFileStore = interface
    { True if (AUser, APass) are valid credentials. }
    function Authenticate(const AUser: string; const APass: string): Boolean;
    { Fetch AData for ARemotePath; True if the file exists. }
    function GetFile(const ARemotePath: string; out AData: string): Boolean;
    { Store AData at ARemotePath (create or overwrite); True on success. }
    function PutFile(const ARemotePath: string; const AData: string): Boolean;
    { Delete ARemotePath; True if it existed and was removed. }
    function DeleteFile(const ARemotePath: string): Boolean;
    { Bare-name listing of ADir (LF-separated).  ADir '' means the root. }
    function List(const ADir: string): string;
  end;

  { A fiber-per-control-connection FTP server.  Start binds+listens; Serve runs
    the accept loop until Stop.  Drive Serve from inside a fiber. }
  TFtpServer = class
  private
    FPort: UInt16;
    FServer: TTcpServer;      { ARC-owned; freed in Destroy }
    FStore: IFtpFileStore;
  public
    constructor Create(APort: UInt16);
    destructor Destroy; override;

    { Bind + listen on 127.0.0.1:Port.  Returns False on failure. }
    function Start: Boolean;

    { Run the accept loop, spawning a session handler fiber per control
      connection, each backed by AStore.  Returns when Stop is called. }
    procedure Serve(AStore: IFtpFileStore);

    { Stop the accept loop and close the listen socket. }
    procedure Stop;

    property Port: UInt16 read FPort;
  end;

implementation

uses
  Net.Sockets, async.io, Net.Mail.Reply;

type
  { The IConnHandler run per control connection.  Holds the store ref (which
    outlives every connection via the server) and drives one FTP session. }
  TFtpSessionHandler = class(IConnHandler)
  private
    FStore: IFtpFileStore;
    { Per-session state.  A fresh handler is NOT created per connection (the
      TCP server reuses the one IConnHandler for every fiber), so per-session
      mutable state must live in locals inside Handle, not in fields.  These
      fields are read-only shared config. }
  public
    constructor Create(AStore: IFtpFileStore);
    procedure Handle(AConn: TTcpConn);
  end;

constructor TFtpSessionHandler.Create(AStore: IFtpFileStore);
begin
  FStore := AStore;
end;

{ Extract the argument after the 4-char command word (everything past the first
  space).  Returns '' when the command has no argument. }
function CmdArg(const ALine: string): string;
var
  I, Len: Int;
begin
  Result := '';
  Len := Length(ALine);
  I := 0;
  while (I < Len) and (Byte(ALine[I]) <> 32) do
    I := I + 1;
  { skip the space(s) }
  while (I < Len) and (Byte(ALine[I]) = 32) do
    I := I + 1;
  if I < Len then
    Result := Copy(ALine, I, Len - I);
end;

{ Convert an LF-joined list of names into CRLF-terminated wire lines.  An empty
  input yields an empty string. }
function NamesToCrlf(const ANames: string): string;
var
  I, Len, Start: Int;
  R, Name: string;
begin
  R := '';
  Len := Length(ANames);
  Start := 0;
  I := 0;
  while I <= Len do
  begin
    if (I = Len) or (Byte(ANames[I]) = 10) then
    begin
      Name := Copy(ANames, Start, I - Start);
      if Name <> '' then
        R := R + Name + CRLF;
      Start := I + 1;
      if I = Len then
        Break;
    end;
    I := I + 1;
  end;
  Result := R;
end;

{ Open an ephemeral data listener on loopback, send the 227 reply on AConn, and
  accept the client's data connection on this fiber.  Returns the connected data
  conn (caller owns / closes it) or nil on failure. }
function OpenPassiveData(AConn: TTcpConn): TTcpConn;
var
  ListenFd, DataFd: Int;
  DataPort: UInt16;
  P: Int;
begin
  Result := nil;
  ListenFd := TcpListenEphemeral(INADDR_LOOPBACK, 8, DataPort);
  if ListenFd < 0 then
  begin
    AConn.Write('425 cannot open data connection' + CRLF);
    Exit;
  end;
  SetNonBlocking(ListenFd);
  P := DataPort;
  { server is on loopback, so advertise 127,0,0,1 }
  AConn.Write('227 Entering Passive Mode (127,0,0,1,'
    + IntToStr(P div 256) + ',' + IntToStr(P mod 256) + ').' + CRLF);
  DataFd := FiberAccept(ListenFd);
  CloseSocket(ListenFd);
  if DataFd < 0 then
    Exit;
  Result := TTcpConn.Create(DataFd);
end;

procedure TFtpSessionHandler.Handle(AConn: TTcpConn);
var
  Line, U, Arg, PendingUser, Data, Listing: string;
  Authed: Boolean;
  DataConn: TTcpConn;
  Chunk: string;
begin
  Authed := False;
  PendingUser := '';
  DataConn := nil;      { the data conn opened by the most recent PASV }
  AConn.Write('220 Blaise FTP server ready' + CRLF);
  while AConn.ReadLine(Line) do
  begin
    U := UpperCase(Line);
    Arg := CmdArg(Line);
    if Copy(U, 0, 4) = 'USER' then
    begin
      PendingUser := Arg;
      AConn.Write('331 need password' + CRLF);
    end
    else if Copy(U, 0, 4) = 'PASS' then
    begin
      Authed := FStore.Authenticate(PendingUser, Arg);
      if Authed then
        AConn.Write('230 logged in' + CRLF)
      else
        AConn.Write('530 login incorrect' + CRLF);
    end
    else if Copy(U, 0, 4) = 'TYPE' then
      AConn.Write('200 type set' + CRLF)
    else if U = 'PWD' then
      AConn.Write('257 "/" is current directory' + CRLF)
    else if Copy(U, 0, 3) = 'CWD' then
      AConn.Write('250 directory changed' + CRLF)
    else if U = 'PASV' then
    begin
      if not Authed then
        AConn.Write('530 not logged in' + CRLF)
      else
      begin
        if DataConn <> nil then
        begin
          DataConn.Close();
          DataConn.Free();
        end;
        DataConn := OpenPassiveData(AConn);
      end;
    end
    else if Copy(U, 0, 4) = 'RETR' then
    begin
      if not Authed then
        AConn.Write('530 not logged in' + CRLF)
      else if DataConn = nil then
        AConn.Write('425 use PASV first' + CRLF)
      else
      begin
        if FStore.GetFile(Arg, Data) then
        begin
          AConn.Write('150 opening data connection' + CRLF);
          DataConn.Write(Data);
          DataConn.Close();
          AConn.Write('226 transfer complete' + CRLF);
        end
        else
        begin
          DataConn.Close();
          AConn.Write('550 no such file' + CRLF);
        end;
        DataConn.Free();
        DataConn := nil;
      end;
    end
    else if Copy(U, 0, 4) = 'STOR' then
    begin
      if not Authed then
        AConn.Write('530 not logged in' + CRLF)
      else if DataConn = nil then
        AConn.Write('425 use PASV first' + CRLF)
      else
      begin
        AConn.Write('150 opening data connection' + CRLF);
        Data := '';
        while True do
        begin
          Chunk := DataConn.Read(4096);
          if Chunk = '' then
            Break;
          Data := Data + Chunk;
        end;
        DataConn.Close();
        DataConn.Free();
        DataConn := nil;
        if FStore.PutFile(Arg, Data) then
          AConn.Write('226 transfer complete' + CRLF)
        else
          AConn.Write('550 store failed' + CRLF);
      end;
    end
    else if (Copy(U, 0, 4) = 'NLST') or (Copy(U, 0, 4) = 'LIST') then
    begin
      if not Authed then
        AConn.Write('530 not logged in' + CRLF)
      else if DataConn = nil then
        AConn.Write('425 use PASV first' + CRLF)
      else
      begin
        AConn.Write('150 here comes the listing' + CRLF);
        Listing := FStore.List(Arg);
        { normalise LF-joined names to CRLF lines on the wire }
        DataConn.Write(NamesToCrlf(Listing));
        DataConn.Close();
        DataConn.Free();
        DataConn := nil;
        AConn.Write('226 listing complete' + CRLF);
      end;
    end
    else if Copy(U, 0, 4) = 'DELE' then
    begin
      if not Authed then
        AConn.Write('530 not logged in' + CRLF)
      else if FStore.DeleteFile(Arg) then
        AConn.Write('250 file deleted' + CRLF)
      else
        AConn.Write('550 no such file' + CRLF);
    end
    else if U = 'QUIT' then
    begin
      AConn.Write('221 bye' + CRLF);
      Break;
    end
    else
      AConn.Write('500 unknown command' + CRLF);
  end;
  if DataConn <> nil then
  begin
    DataConn.Close();
    DataConn.Free();
  end;
  { The TCP server's connection trampoline closes+frees AConn after we return. }
end;

{ ---- TFtpServer ---- }

constructor TFtpServer.Create(APort: UInt16);
begin
  FPort := APort;
  FServer := TTcpServer.Create(APort);
  FStore := nil;
end;

destructor TFtpServer.Destroy;
begin
  if FServer <> nil then
  begin
    FServer.Free();
    FServer := nil;
  end;
  inherited Destroy();
end;

function TFtpServer.Start: Boolean;
begin
  Result := FServer.Start();
end;

procedure TFtpServer.Serve(AStore: IFtpFileStore);
var
  H: IConnHandler;
begin
  FStore := AStore;
  H := TFtpSessionHandler.Create(AStore);
  FServer.Serve(H);
end;

procedure TFtpServer.Stop;
begin
  FServer.Stop();
end;

end.
