{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.mail;

{ E2E test for the L5 MAIL wave (Net.Smtp).  A program spins up a mock SMTP
  server fiber plus an SMTP client fiber over a loopback port; the client runs
  SendMail, the server records the transcript, and the program prints a marker
  proving the compile -> native -> run round-trip the IR/stdlib harness cannot
  give.

  Plaintext only (internal linker); the STARTTLS/SMTPS variants pull in libssl
  and would need --linker external.

  BACKEND POSTURE: Net.Tcp/async.io pull in the inline-asm context leaf, so this
  runs on the NATIVE backend only. }

interface

uses
  SysUtils, blaise.testing, cp.test.e2e.base;

type
  TeMailE2ETests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestSmtpSendMail_Transcript;
  end;

implementation

const
  LE = #10;

  { A mock SMTP server fiber (on Net.Tcp) that speaks just enough SMTP, plus a
    client fiber that runs SendMail against it.  The server records whether it
    saw MAIL FROM / RCPT TO / the DATA body; the program prints a compact marker
    for each so the e2e harness can assert on stdout. }
  SrcSmtp =
    '''
    program smtpe2e;
    uses SysUtils, Net.Tcp, Net.Smtp, Net.Mail.Reply, async.fibers;
    const PORT = 29541;
    type
      TMock = class(IConnHandler)
        procedure Handle(AConn: TTcpConn);
      end;
    var
      GSrv: TTcpServer;
      GHandler: IConnHandler;
      GSawMail: Boolean;
      GSawRcpt: Boolean;
      GSawBody: Boolean;
      GOk: Boolean;

    procedure TMock.Handle(AConn: TTcpConn);
    var
      Line, U: string;
      InData: Boolean;
    begin
      AConn.Write('220 mock ESMTP'#13#10);
      InData := False;
      while AConn.ReadLine(Line) do
      begin
        if InData then
        begin
          if Line = '.' then
          begin
            InData := False;
            AConn.Write('250 Ok queued'#13#10);
            Continue;
          end;
          if Pos('Hello Bob', Line) >= 0 then GSawBody := True;
          Continue;
        end;
        U := UpperCase(Line);
        if Copy(U, 0, 4) = 'EHLO' then
          AConn.Write('250 mock'#13#10)
        else if Copy(U, 0, 4) = 'MAIL' then
        begin
          GSawMail := True;
          AConn.Write('250 Ok'#13#10);
        end
        else if Copy(U, 0, 4) = 'RCPT' then
        begin
          GSawRcpt := True;
          AConn.Write('250 Ok'#13#10);
        end
        else if U = 'DATA' then
        begin
          AConn.Write('354 go'#13#10);
          InData := True;
        end
        else if U = 'QUIT' then
        begin
          AConn.Write('221 Bye'#13#10);
          Break;
        end
        else
          AConn.Write('250 Ok'#13#10);
      end;
    end;

    procedure ServerFiber(AArg: Pointer);
    begin
      GSrv.Serve(GHandler);
    end;

    procedure ClientFiber(AArg: Pointer);
    var
      Cli: TSmtpClient;
    begin
      Cli := TSmtpClient.Create();
      GOk := Cli.SendMail('127.0.0.1', PORT,
        'alice@example.com', 'bob@example.com', 'Hi', 'Hello Bob');
      Cli.Free();
      GSrv.Stop();
    end;

    begin
      GSawMail := False;
      GSawRcpt := False;
      GSawBody := False;
      GOk := False;
      GSrv := TTcpServer.Create(PORT);
      if not GSrv.Start() then begin WriteLn('STARTFAIL'); Halt(1); end;
      GHandler := TMock.Create();
      SpawnFiber(@ServerFiber, nil);
      SpawnFiber(@ClientFiber, nil);
      RunScheduler();
      GSrv.Free();
      if GSawMail then WriteLn('MAIL:ok');
      if GSawRcpt then WriteLn('RCPT:ok');
      if GSawBody then WriteLn('BODY:ok');
      if GOk then WriteLn('SEND:ok');
      WriteLn('DONE');
    end.
    ''';

procedure TeMailE2ETests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-mail')
end;

procedure TeMailE2ETests.TestSmtpSendMail_Transcript;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRTLRunsOnOne(beNative, 'smtpe2e', SrcSmtp,
    'MAIL:ok' + LE + 'RCPT:ok' + LE + 'BODY:ok' + LE + 'SEND:ok' + LE
    + 'DONE' + LE, 0)
end;

initialization
  RegisterTest(TeMailE2ETests);

end.
