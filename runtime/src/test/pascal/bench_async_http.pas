{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ ===========================================================================
  GO/NO-GO benchmark gate for the fiber-runtime networking design
  (docs/async-networking-design.adoc, GO/NO-GO gate + [#performance]).

  Compares THREE HTTP/1.1 server models under an identical in-process load:

    1. fiber      — THttpFiberServer on RunSchedulerMC(N): one handler fiber per
                    connection, keep-alive (the design under test).
    2. one-shot   — the existing THttpServer.ServeOnce loop: one connection at a
                    time (the current baseline).
    3. thread     — thread-per-connection (the Indy model): one OS pthread per
                    accepted connection.

  The load generator is a fan-out of K raw OS-thread clients, each opening one
  connection and issuing R sequential keep-alive GET requests on it.  Peak
  concurrency == K (all K connect near-simultaneously).  We scale K up and
  record, per model: max K sustained with zero client errors, total req/s, and
  where throughput collapses.  Timing uses MonotonicNowNs.

  The gate signal is RELATIVE: the fiber model must sustain HIGH concurrency
  (thousands of live connections) at throughput where the thread-per-connection
  model degrades or errors.  Absolute 10k conns is machine-dependent (fd + RAM
  limits); the crossover is the proof.

  Second gate condition (exception/allocator survival under the 100k-fiber
  joint stress) is covered by the stdlib TAsyncStressTests; this program prints
  a reminder to run it.

  Build (native only — pulls in the inline-asm fiber context leaf):
    compiler/target/blaise --source runtime/src/test/pascal/bench_async_http.pas \
      --backend native --output /tmp/bench_async_http \
      --unit-path compiler/src/main/pascal \
      --unit-path runtime/src/main/pascal \
      --unit-path stdlib/src/main/pascal
  =========================================================================== }

program bench_async_http;

uses
  SysUtils,
  StrUtils,
  runtime.thread,
  runtime.atomic,
  async.fibers,
  Net.Sockets,
  Net.Tcp,
  Net.Http.Server;

const
  { Listen ports MUST sit BELOW the ephemeral range (Linux default
    32768–60999): the load generator opens ~100k+ short-lived client sockets,
    each grabbing an ephemeral port, and a listen port inside that range
    collides with a client's TIME_WAIT socket and fails to bind.  18000 is
    safely below the ephemeral floor. }
  BASE_PORT = 18000;

{ ---- setrlimit(RLIMIT_NOFILE) so high-concurrency runs are not fd-capped ---- }

type
  TRLimit = record
    RlimCur: UInt64;
    RlimMax: UInt64;
  end;

function c_setrlimit(AResource: Integer; ARlim: Pointer): Integer;
  external name 'setrlimit';
function c_getrlimit(AResource: Integer; ARlim: Pointer): Integer;
  external name 'getrlimit';

const
  { Linux x86_64 = 7, FreeBSD = 8 (the resource NUMBER differs per OS). }
  {$IFDEF FREEBSD}
  RLIMIT_NOFILE = 8;
  {$ELSE}
  RLIMIT_NOFILE = 7;
  {$ENDIF}
  SO_RCVTIMEO   = 20;   { Linux x86_64 }

type
  TTimeVal = record
    TvSec: Int64;
    TvUsec: Int64;
  end;

{ Cap how long a client blocks in recv, so a starved connection (the one-shot
  server that never gets to it) fails fast instead of hanging for the whole
  run.  Without this a single-server model at high K takes minutes. }
procedure SetRecvTimeout(AFd, AMillis: Integer);
var
  Tv: TTimeVal;
begin
  Tv.TvSec := AMillis div 1000;
  Tv.TvUsec := (Int64(AMillis) mod 1000) * 1000;
  SetSockOpt(AFd, SOL_SOCKET(), SO_RCVTIMEO, @Tv, 16);
end;

{ Raise the soft NOFILE limit toward the hard limit (or ADesired, whichever is
  smaller).  Returns the resulting soft limit. }
function RaiseFdLimit(ADesired: UInt64): UInt64;
var
  Rl: TRLimit;
begin
  if c_getrlimit(RLIMIT_NOFILE, @Rl) <> 0 then
    Exit(0);
  if ADesired > Rl.RlimMax then
    Rl.RlimCur := Rl.RlimMax
  else
    Rl.RlimCur := ADesired;
  c_setrlimit(RLIMIT_NOFILE, @Rl);
  if c_getrlimit(RLIMIT_NOFILE, @Rl) <> 0 then
    Exit(0);
  Result := Rl.RlimCur;
end;

{ ---- the application handler (shared by all three server models) ---- }

type
  TBenchHandler = class(IRequestHandler)
    procedure Handle(ARequest: THttpRequest; AResponse: THttpResponse);
  end;

procedure TBenchHandler.Handle(ARequest: THttpRequest; AResponse: THttpResponse);
begin
  AResponse.SetText(200, 'text/plain', 'ok');
end;

{ ---- shared load-generator (raw OS-thread clients) ---- }

{ One client's work order + result, shared with its OS thread. }
type
  PInteger = ^Integer;
  PClientCtx = ^TClientCtx;
  TClientCtx = record
    Port: UInt16;
    Requests: Integer;    { R sequential keep-alive requests }
    Ok: Integer;          { requests that got a 200 back }
    Failed: Integer;      { connect or request failures }
    StartGateVal: PInteger; { spin until the coordinator opens the gate }
  end;

var
  GLiveConns: Integer;    { current open client connections (atomic) }
  GPeakConns: Integer;    { high-water mark of GLiveConns (atomic) }

{ Atomic load via a fetch-and-add-0 (runtime.atomic has no bare load). }
function _AtomicLoadInt32(APtr: Pointer): Integer;
begin
  Result := _AtomicAddInt32(APtr, 0);
end;

procedure BumpPeak;
var
  Live, Peak: Integer;
begin
  Live := _AtomicLoadInt32(@GLiveConns);
  Peak := _AtomicLoadInt32(@GPeakConns);
  while Live > Peak do
  begin
    { best-effort: another thread may race, but the max still converges }
    _AtomicAddInt32(@GPeakConns, Live - Peak);
    Peak := _AtomicLoadInt32(@GPeakConns);
    Live := _AtomicLoadInt32(@GLiveConns);
  end;
end;

{ A blocking-socket HTTP/1.1 keep-alive client run on its own OS thread.  It
  opens one connection, does R GETs on it, counts 200s, then closes.  Written
  with the raw Net.Sockets blocking API (no fibers) so the load generator is
  independent of the server's scheduler. }
procedure ClientThread(AArg: Pointer);
var
  Ctx: PClientCtx;
  Fd, I, Sep, ClPos, Eol, CLen, HeadLen, BodyHave: Integer;
  Req, Acc, Chunk, Head, Lower, Line: string;
begin
  Ctx := PClientCtx(AArg);
  { Wait for the coordinator to open the start gate (so all K connect together,
    maximising simultaneous concurrency). }
  while _AtomicLoadInt32(Ctx^.StartGateVal) = 0 do
    ;

  Fd := TcpConnectLocal(Ctx^.Port);
  if Fd < 0 then
  begin
    Ctx^.Failed := Ctx^.Requests;
    Exit;
  end;
  SetRecvTimeout(Fd, 5000);   { starved client fails within 5 s, never hangs }
  _AtomicAddInt32(@GLiveConns, 1);
  BumpPeak();

  for I := 0 to Ctx^.Requests - 1 do
  begin
    if I = Ctx^.Requests - 1 then
      Req := 'GET /bench HTTP/1.1'#13#10'Host: x'#13#10'Connection: close'#13#10#13#10
    else
      Req := 'GET /bench HTTP/1.1'#13#10'Host: x'#13#10'Connection: keep-alive'#13#10#13#10;
    if not SendAll(Fd, Req) then
    begin
      Ctx^.Failed := Ctx^.Failed + (Ctx^.Requests - I);
      Break;
    end;
    { read one response head + body (Content-Length) }
    Acc := '';
    Sep := -1;
    while True do
    begin
      Sep := PosEx(#13#10#13#10, Acc, 0);
      if Sep >= 0 then
        Break;
      Chunk := RecvString(Fd, 4096);
      if Chunk = '' then
        Break;
      Acc := Acc + Chunk;
    end;
    if Sep < 0 then
    begin
      Ctx^.Failed := Ctx^.Failed + (Ctx^.Requests - I);
      Break;
    end;
    HeadLen := Sep + 4;
    Head := Copy(Acc, 0, Sep);
    CLen := 0;
    Lower := LowerCase(Head);
    ClPos := PosEx('content-length:', Lower, 0);
    if ClPos >= 0 then
    begin
      Eol := PosEx(#13#10, Head, ClPos);
      if Eol < 0 then
        Eol := Length(Head);
      Line := Trim(Copy(Head, ClPos + 15, Eol - (ClPos + 15)));
      if Line <> '' then
        CLen := StrToInt(Line);
    end;
    BodyHave := Length(Acc) - HeadLen;
    while BodyHave < CLen do
    begin
      Chunk := RecvString(Fd, CLen - BodyHave);
      if Chunk = '' then
        Break;
      BodyHave := BodyHave + Length(Chunk);
    end;
    if ContainsStr(Head, '200') then
      Ctx^.Ok := Ctx^.Ok + 1
    else
      Ctx^.Failed := Ctx^.Failed + 1;
  end;

  CloseSocket(Fd);
  _AtomicAddInt32(@GLiveConns, -1);
end;

{ Run K client threads, each doing R requests, against APort.  Returns wall-time
  nanoseconds and fills AOkOut / AFailOut / APeakOut. }
procedure DriveLoad(APort: UInt16; AK, AR: Integer;
  out AWallNs: Int64; out AOkOut, AFailOut, APeakOut: Integer);
var
  Threads: array of Int64;
  Ctxs: array of TClientCtx;
  Gate: Integer;
  I, TotalOk, TotalFail: Integer;
  T0: Int64;
begin
  SetLength(Threads, AK);
  SetLength(Ctxs, AK);
  Gate := 0;
  GLiveConns := 0;
  GPeakConns := 0;

  for I := 0 to AK - 1 do
  begin
    Ctxs[I].Port := APort;
    Ctxs[I].Requests := AR;
    Ctxs[I].Ok := 0;
    Ctxs[I].Failed := 0;
    Ctxs[I].StartGateVal := @Gate;
  end;

  for I := 0 to AK - 1 do
    pthread_create(@Threads[I], nil, Pointer(@ClientThread), @Ctxs[I]);

  { open the gate and start the clock together }
  T0 := MonotonicNowNs();
  _AtomicAddInt32(@Gate, 1);

  for I := 0 to AK - 1 do
    pthread_join(Threads[I], nil);
  AWallNs := MonotonicNowNs() - T0;

  TotalOk := 0;
  TotalFail := 0;
  for I := 0 to AK - 1 do
  begin
    TotalOk := TotalOk + Ctxs[I].Ok;
    TotalFail := TotalFail + Ctxs[I].Failed;
  end;
  AOkOut := TotalOk;
  AFailOut := TotalFail;
  APeakOut := _AtomicLoadInt32(@GPeakConns);
end;

{ ---- server model 1: fiber (THttpFiberServer on RunSchedulerMC) ---- }

var
  GFiberSrv: THttpFiberServer;
  GFiberHandler: IRequestHandler;

procedure FiberServeFiber(AArg: Pointer);
begin
  GFiberSrv.Serve(GFiberHandler);
end;

{ The fiber server runs on its OWN OS thread (its own RunSchedulerMC), because
  the main thread drives the load and there is one global MC scheduler state. }
procedure FiberServerThread(AArg: Pointer);
begin
  SpawnFiber(@FiberServeFiber, nil);
  RunSchedulerMC(Integer(AArg));   { N workers }
end;

{ ---- server model 2: one-at-a-time baseline (THttpServer.ServeOnce) ---- }

var
  GBaseSrv: THttpServer;
  GBaseHandler: IRequestHandler;
  GBaseRunning: Integer;

procedure BaselineServerThread(AArg: Pointer);
begin
  GBaseSrv.SetNonBlocking();
  while _AtomicLoadInt32(@GBaseRunning) = 1 do
    GBaseSrv.PollOnce(GBaseHandler);   { non-blocking: services one if pending }
end;

{ ---- server model 3: thread-per-connection (the Indy model) ---- }

var
  GTpcListen: Integer;
  GTpcRunning: Integer;
  GTpcHandler: IRequestHandler;

{ Per-connection worker: read one request head, serve keep-alive requests until
  close, on its OWN OS thread.  A fresh THttpRequest/Response per request via
  ParseRequest (the shared contract). }
procedure TpcConnThread(AArg: Pointer);
var
  Fd, Sep: Integer;
  Acc, Chunk, Raw: string;
  Req: THttpRequest;
  Resp: THttpResponse;
  Head: string;
  KeepAlive: Boolean;
begin
  Fd := Integer(Int64(AArg));
  while True do
  begin
    { read a head }
    Acc := '';
    Sep := -1;
    while True do
    begin
      Sep := PosEx(#13#10#13#10, Acc, 0);
      if Sep >= 0 then
        Break;
      Chunk := RecvString(Fd, 4096);
      if Chunk = '' then
        Break;
      Acc := Acc + Chunk;
    end;
    if Sep < 0 then
      Break;                 { peer closed }
    Raw := Copy(Acc, 0, Sep + 4);
    Req := ParseRequest(Raw);
    KeepAlive := not ContainsStr(LowerCase(Raw), 'connection: close');
    Resp := THttpResponse.Create();
    GTpcHandler.Handle(Req, Resp);
    if KeepAlive then
      Head := 'HTTP/1.1 200 OK'#13#10'Content-Type: ' + Resp.ContentType +
              #13#10'Content-Length: ' + IntToStr(Length(Resp.Body)) +
              #13#10'Connection: keep-alive'#13#10#13#10
    else
      Head := 'HTTP/1.1 200 OK'#13#10'Content-Type: ' + Resp.ContentType +
              #13#10'Content-Length: ' + IntToStr(Length(Resp.Body)) +
              #13#10'Connection: close'#13#10#13#10;
    SendAll(Fd, Head + Resp.Body);
    Resp.Free();
    Req.Free();
    if not KeepAlive then
      Break;
  end;
  CloseSocket(Fd);
end;

procedure TpcAcceptThread(AArg: Pointer);
var
  ConnFd: Integer;
  Tid: Int64;
begin
  MakeNonBlocking(GTpcListen);
  while _AtomicLoadInt32(@GTpcRunning) = 1 do
  begin
    ConnFd := AcceptConn(GTpcListen);
    if ConnFd < 0 then
      Continue;                { non-blocking: nothing pending, spin lightly }
    pthread_create(@Tid, nil, Pointer(@TpcConnThread), Pointer(Int64(ConnFd)));
  end;
end;

{ ---- reporting ---- }

function ReqPerSec(AOk: Integer; AWallNs: Int64): Int64;
begin
  if AWallNs <= 0 then
    Exit(0);
  Result := (Int64(AOk) * Int64(1000000000)) div AWallNs;
end;

procedure PrintRow(const AModel: string; AK, AR, AOk, AFail, APeak: Integer;
  AWallNs: Int64);
var
  Rps: Int64;
begin
  Rps := ReqPerSec(AOk, AWallNs);
  WriteLn(Format('%-10s  K=%-6d  peak=%-6d  ok=%-8d  fail=%-6d  %6d ms  %8d req/s',
    [AModel, AK, APeak, AOk, AFail, Integer(AWallNs div 1000000), Integer(Rps)]));
end;

{ ---- drivers per model ---- }

procedure RunFiberModel(APort: UInt16; AWorkers, AK, AR: Integer);
var
  SrvTid: Int64;
  WallNs: Int64;
  Ok, Fail, Peak, Tries: Integer;
  Started: Boolean;
begin
  Started := False;
  Tries := 0;
  while (not Started) and (Tries < 20) do
  begin
    GFiberSrv := THttpFiberServer.Create(APort);
    Started := GFiberSrv.Start();
    if not Started then
    begin
      GFiberSrv.Free();
      Sleep(250);          { transient EADDRINUSE from a TIME_WAIT socket }
    end;
    Tries := Tries + 1;
  end;
  if not Started then
  begin
    WriteLn('fiber: server start FAILED on port ', APort, ' after ', Tries, ' tries');
    Exit;
  end;
  GFiberHandler := TBenchHandler.Create();
  pthread_create(@SrvTid, nil, Pointer(@FiberServerThread), Pointer(AWorkers));
  { give the server a moment to enter its accept loop }
  Sleep(60);

  DriveLoad(APort, AK, AR, WallNs, Ok, Fail, Peak);
  PrintRow('fiber', AK, AR, Ok, Fail, Peak, WallNs);

  GFiberSrv.Stop();
  pthread_join(SrvTid, nil);
  GFiberSrv.Free();
  GFiberHandler := nil;
end;

procedure RunBaselineModel(APort: UInt16; AK, AR: Integer);
var
  SrvTid: Int64;
  WallNs: Int64;
  Ok, Fail, Peak: Integer;
begin
  GBaseSrv := THttpServer.Create(APort);
  if not GBaseSrv.Start() then
  begin
    WriteLn('one-shot: server start FAILED on port ', APort);
    GBaseSrv.Free();
    Exit;
  end;
  GBaseHandler := TBenchHandler.Create();
  GBaseRunning := 1;
  pthread_create(@SrvTid, nil, Pointer(@BaselineServerThread), nil);
  Sleep(60);

  DriveLoad(APort, AK, AR, WallNs, Ok, Fail, Peak);
  PrintRow('one-shot', AK, AR, Ok, Fail, Peak, WallNs);

  _AtomicAddInt32(@GBaseRunning, -1);
  pthread_join(SrvTid, nil);
  GBaseSrv.Free();
  GBaseHandler := nil;
end;

procedure RunThreadModel(APort: UInt16; AK, AR: Integer);
var
  AccTid: Int64;
  WallNs: Int64;
  Ok, Fail, Peak: Integer;
begin
  GTpcListen := TcpListenLocal(APort, 512);
  if GTpcListen < 0 then
  begin
    WriteLn('thread: server start FAILED on port ', APort);
    Exit;
  end;
  GTpcHandler := TBenchHandler.Create();
  GTpcRunning := 1;
  pthread_create(@AccTid, nil, Pointer(@TpcAcceptThread), nil);
  Sleep(60);

  DriveLoad(APort, AK, AR, WallNs, Ok, Fail, Peak);
  PrintRow('thread', AK, AR, Ok, Fail, Peak, WallNs);

  _AtomicAddInt32(@GTpcRunning, -1);
  pthread_join(AccTid, nil);
  CloseSocket(GTpcListen);
  { The per-connection threads are DETACHED (never joined) — the Indy model
    spawns one per accept and lets it run to completion.  A client that hit its
    5 s recv timeout and closed early can leave a connection thread still
    reading; give those a moment to drain before the next level reuses the
    globals.  Deliberately do NOT nil GTpcHandler: a lingering connection thread
    would then call through a freed interface (a teardown UAF).  Leaking one
    handler per level is harmless for a benchmark. }
  Sleep(300);
end;

{ ---- main ---- }

var
  Port: UInt16;
  Ks: array[0..5] of Integer;
  I, R, Workers, SoftLimit, NLevels: Integer;

begin
  IgnoreSigPipe();
  SoftLimit := Integer(RaiseFdLimit(200000));
  Workers := GetCPUCount();

  WriteLn('=== Blaise fiber-networking GO/NO-GO benchmark ===');
  WriteLn('CPU workers for fiber model : ', Workers);
  WriteLn('RLIMIT_NOFILE (soft)        : ', SoftLimit);
  WriteLn('requests per connection (R) : 20');
  WriteLn('client recv timeout         : 5000 ms (starved client fails fast)');
  WriteLn('');
  WriteLn('model       concurrency(K)  peak-conns  ok  fail  wall  throughput');
  WriteLn('-------------------------------------------------------------------------');

  R := 20;
  { Concurrency ladder.  Adjust upward on a bigger box. }
  Ks[0] := 100;
  Ks[1] := 500;
  Ks[2] := 1000;
  Ks[3] := 2000;
  Ks[4] := 5000;
  Ks[5] := 8000;
  NLevels := 6;

  for I := 0 to NLevels - 1 do
  begin
    { A wide, non-overlapping port block per level so a listen port is never
      reused across the run — thousands of short-lived client sockets leave
      TIME_WAIT entries on nearby ephemeral ports, and a fixed listen port that
      collides with one of them fails to bind.  Each level gets ports
      BASE_PORT + I*100 (+0 fiber, +1 thread, +2 one-shot). }
    Port := BASE_PORT + I * 100;
    WriteLn('--- K = ', Ks[I], ' ---');
    RunFiberModel(Port, Workers, Ks[I], R);
    RunThreadModel(Port + 1, Ks[I], R);
    { The one-at-a-time baseline is proven to collapse; run it only at the two
      lowest K (each higher K just wastes minutes hitting the 5 s client
      timeout on thousands of starved connections). }
    if I <= 1 then
      RunBaselineModel(Port + 2, Ks[I], R);
    Sleep(400);        { let TIME_WAIT drain before the next level }
    WriteLn('');
  end;

  WriteLn('NOTE: also run the 100k-fiber joint stress (stdlib TAsyncStressTests)');
  WriteLn('      to confirm the exception/allocator model survives — gate cond 2.');
  WriteLn('DONE');
end.
