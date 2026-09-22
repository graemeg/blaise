{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.nntp;

{ E2E test for the L5 NEWS wave (Net.Nntp + Net.Nntp.Server).  A program spins up
  a real TNntpServer (backed by an in-memory single-group store) plus a
  TNntpClient fiber over a loopback port; the client selects a group, POSTs an
  article, re-selects (now non-empty), fetches the article back byte-exact, and
  LISTs.  The program prints markers proving the compile -> native -> run
  round-trip that the IR/stdlib harness cannot give - in particular that the
  dot-stuffed multi-line POST + ARTICLE transfer carries the bytes (including a
  leading-dot line and a NUL) byte-exact end to end.

  Plaintext only (internal linker); NNTPS would need --linker external.

  BACKEND POSTURE: Net.Tcp/async.io pull in the inline-asm context leaf, so this
  runs on the NATIVE backend only. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TeNntpE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestNntpClientServer_RoundTrip;
  end;

implementation

const
  LE = #10;

  SrcNntp =
    '''
    program nntpe2e;
    uses SysUtils, Net.Tcp, Net.Nntp, Net.Nntp.Server, async.fibers,
      Generics.Collections;
    const
      PORT = 29691;
      ART = 'Subject: hi'#10'From: bob'#10#10'body one'#10'.dotted'#10'x'#0'y'#10'end';
    type
      TStore = class(INntpStore)
        FData: string;
        FHave: Boolean;
        function ListGroups: string;
        function SelectGroup(const AName: string; out ACount: Integer;
          out AFirst: Integer; out ALast: Integer): Boolean;
        function GetArticle(const AGroup: string; ANumber: Integer;
          out AArticle: string): Boolean;
        function PostArticle(const AArticle: string; out ANumber: Integer): Boolean;
      end;
    var
      GSrv: TNntpServer;
      GStore: INntpStore;
      GStoreObj: TStore;
      GGroupOk: Boolean;
      GPostOk: Boolean;
      GCount1: Integer;
      GFetch: string;
      GFetchOk: Boolean;
      GList: string;

    function TStore.ListGroups: string;
    begin
      if FHave then Result := 'comp.test 1 1 y' else Result := 'comp.test 0 1 y';
    end;
    function TStore.SelectGroup(const AName: string; out ACount: Integer;
      out AFirst: Integer; out ALast: Integer): Boolean;
    begin
      if AName <> 'comp.test' then begin ACount := 0; AFirst := 0; ALast := 0; Result := False; Exit; end;
      if FHave then begin ACount := 1; AFirst := 1; ALast := 1; end
      else begin ACount := 0; AFirst := 0; ALast := 0; end;
      Result := True;
    end;
    function TStore.GetArticle(const AGroup: string; ANumber: Integer;
      out AArticle: string): Boolean;
    begin
      if FHave and (ANumber = 1) then begin AArticle := FData; Result := True; end
      else begin AArticle := ''; Result := False; end;
    end;
    function TStore.PostArticle(const AArticle: string; out ANumber: Integer): Boolean;
    begin
      FData := AArticle; FHave := True; ANumber := 1; Result := True;
    end;

    procedure ServerFiber(AArg: Pointer);
    begin
      GSrv.Serve(GStore);
    end;

    procedure ClientFiber(AArg: Pointer);
    var
      Cli: TNntpClient;
      Groups: TList<string>;
      C, F, L, I: Integer;
    begin
      Cli := TNntpClient.Create();
      if Cli.Connect('127.0.0.1', PORT) then
      begin
        Cli.ModeReader();
        GGroupOk := Cli.SelectGroup('comp.test', C, F, L);
        GPostOk := Cli.Post(ART);
        Cli.SelectGroup('comp.test', C, F, L);
        GCount1 := C;
        GFetchOk := Cli.FetchArticle(IntToStr(L), GFetch);
        if Cli.ListGroups(Groups) then
        begin
          GList := '';
          for I := 0 to Groups.Count - 1 do
            GList := GList + Groups[I] + #10;
        end;
        Groups.Free();
        Cli.Quit();
      end;
      Cli.Free();
      GSrv.Stop();
    end;

    begin
      GGroupOk := False;
      GPostOk := False;
      GCount1 := 0;
      GFetch := '';
      GFetchOk := False;
      GList := '';
      GStoreObj := TStore.Create();
      GStore := GStoreObj;
      GSrv := TNntpServer.Create(PORT);
      if not GSrv.Start() then begin WriteLn('STARTFAIL'); Halt(1); end;
      SpawnFiber(@ServerFiber, nil);
      SpawnFiber(@ClientFiber, nil);
      RunScheduler();
      GSrv.Free();
      if GGroupOk then WriteLn('GROUP:ok');
      if GPostOk then WriteLn('POST:ok');
      if GCount1 = 1 then WriteLn('COUNT:ok');
      if GFetchOk then WriteLn('FETCH:ok');
      if GFetch = ART then WriteLn('BYTES:ok');
      if Pos('comp.test', GList) >= 0 then WriteLn('LIST:ok');
      WriteLn('DONE');
    end.
    ''';

procedure TeNntpE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-nntp')
end;

procedure TeNntpE2ETests.TestNntpClientServer_RoundTrip;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'nntpe2e', SrcNntp,
    'GROUP:ok' + LE + 'POST:ok' + LE + 'COUNT:ok' + LE + 'FETCH:ok' + LE
    + 'BYTES:ok' + LE + 'LIST:ok' + LE + 'DONE' + LE, 0)
end;

initialization
  RegisterTest(TeNntpE2ETests);

end.
