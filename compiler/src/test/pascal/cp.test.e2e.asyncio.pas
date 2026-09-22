{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.asyncio;

{ E2E test for L2 (reactor) + L3 (fiber I/O) of the fiber runtime
  (docs/async-networking-design.adoc, [#reactor], [#fiber-io]): a fiber echo
  server on a loopback TCP port plus a fiber client that connects, sends, and
  reads back the echo — the full compile -> QBE/native -> run integration proof
  the IR/stdlib harness cannot give.

  BACKEND POSTURE: async.fibers/async.io pull in the inline-asm context leaf, so
  this runs on the NATIVE backend only. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TAsyncIoE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestFiberEchoServerClient_RoundTrip;
    { Phase 7 (anonymous methods x concurrency): the 'reference to'-typed
      TTaskGroup.Spawn overload.  The loop-spawn pattern with a block-scoped
      var spawns N DISTINCT captured values (per-iteration envs, Phase 4);
      the routine-level shared-variable form is the documented trap — every
      child observes the final value. }
    procedure TestTaskGroup_SpawnClosure_BlockVarSnapshots;
    procedure TestTaskGroup_SpawnClosure_SharedVarTrap;
  end;

implementation

const
  LE = #10;

  { A fiber echo server and a fiber client cooperating on one single-worker
    scheduler.  The server accepts one connection, echoes what it receives; the
    client connects, sends 'hello', reads the echo, and prints it. }
  SrcEchoServerClient =
    '''
    program echoe2e;
    uses SysUtils, async.io, async.fibers, net.sockets;
    const PORT = 29377;
    var
      ListenFd: Integer;

    procedure ServerFiber(AArg: Pointer);
    var
      Conn: Integer;
      Buf: array[0..63] of Byte;
      N: Int64;
    begin
      Conn := FiberAccept(ListenFd);
      if Conn < 0 then begin WriteLn('ACCFAIL'); Exit; end;
      N := FiberRecv(Conn, @Buf[0], 64);
      if N > 0 then
        FiberSend(Conn, @Buf[0], N);
      Close(Conn);
    end;

    procedure ClientFiber(AArg: Pointer);
    var
      Fd, Rc, I: Integer;
      SA: TSockAddrIn;
      Buf: array[0..63] of Byte;
      N: Int64;
      S: string;
    begin
      Fd := Socket(AF_INET, SOCK_STREAM, 0);
      SetNonBlocking(Fd);
      FillSockAddr(SA, INADDR_LOOPBACK, PORT);
      Rc := FiberConnect(Fd, @SA, 16);
      if Rc <> 0 then begin WriteLn('CONNFAIL'); Exit; end;
      FiberSend(Fd, PChar('hello'), 5);
      N := FiberRecv(Fd, @Buf[0], 64);
      S := '';
      for I := 0 to Integer(N) - 1 do S := S + Chr(Buf[I]);
      WriteLn('ECHO:', S);
      Close(Fd);
    end;

    begin
      ListenFd := TcpListenLocal(PORT, 8);
      if ListenFd < 0 then begin WriteLn('LISTENFAIL'); Halt(1); end;
      SetNonBlocking(ListenFd);
      SpawnFiber(@ServerFiber, nil);
      SpawnFiber(@ClientFiber, nil);
      RunScheduler();
      Close(ListenFd);
      WriteLn('DONE');
    end.
    ''';

procedure TAsyncIoE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-asyncio')
end;

procedure TAsyncIoE2ETests.TestFiberEchoServerClient_RoundTrip;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'asyncio-echo', SrcEchoServerClient,
    'ECHO:hello' + LE + 'DONE' + LE, 0)
end;

const
  SrcSpawnClosureSnapshots =
    '''
    program tgclos;
    uses SysUtils, async.fibers, async.sync;

    procedure Driver(AArg: Pointer);
    var
      G: TTaskGroup;
      I: Integer;
    begin
      G := TTaskGroup.Create();
      try
        for I := 0 to 2 do
        begin
          var Snap: Integer := I;
          G.Spawn(procedure
            begin
              WriteLn(Snap)
            end);
        end;
        if G.Wait() then
          WriteLn('OK')
        else
          WriteLn('FAIL');
      finally
        G.Free();
      end;
    end;

    begin
      SpawnFiber(@Driver, nil);
      RunScheduler();
      WriteLn('DONE');
    end.
    ''';

  SrcSpawnClosureSharedTrap =
    '''
    program tgtrap;
    uses SysUtils, async.fibers, async.sync;

    procedure Driver(AArg: Pointer);
    var
      G: TTaskGroup;
      I: Integer;
    begin
      G := TTaskGroup.Create();
      try
        for I := 0 to 2 do
          G.Spawn(procedure
            begin
              WriteLn(I)
            end);
        if G.Wait() then
          WriteLn('OK')
        else
          WriteLn('FAIL');
      finally
        G.Free();
      end;
    end;

    begin
      SpawnFiber(@Driver, nil);
      RunScheduler();
      WriteLn('DONE');
    end.
    ''';

procedure TAsyncIoE2ETests.TestTaskGroup_SpawnClosure_BlockVarSnapshots;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'tg-closure-snap', SrcSpawnClosureSnapshots,
    '0' + LE + '1' + LE + '2' + LE + 'OK' + LE + 'DONE' + LE, 0)
end;

procedure TAsyncIoE2ETests.TestTaskGroup_SpawnClosure_SharedVarTrap;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { All three children read the SAME captured I, which the loop has already
    advanced to 3 by the time they run — the documented shared-env trap
    (use a block-scoped var for per-iteration snapshots). }
  AssertRTLRunsOnOne(beNative, 'tg-closure-trap', SrcSpawnClosureSharedTrap,
    '3' + LE + '3' + LE + '3' + LE + 'OK' + LE + 'DONE' + LE, 0)
end;

initialization
  RegisterTest(TAsyncIoE2ETests);

end.
