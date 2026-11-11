program m3rtl;

{ Windows milestone M3 program under test, built from the command line
  (blaise --target windows-x86_64) with the Windows runtime: strings,
  dynamic arrays, for-in, classes and ARC, exceptions through recursion,
  try/finally, threadvars and SysUtils.Format.  scripts/windows-vm.sh
  crosscheck compares its output with m3rtl.expected, which is what the
  macOS build prints. }

uses SysUtils;

type
  TNode = class
  public
    Value: Int;
    Next: TNode;
    constructor Create(AValue: Int);
    destructor Destroy; override;
  end;

  EMine = class(Exception);

var
  Freed: Int;

threadvar
  Depth: Int;
  Tag: string;

constructor TNode.Create(AValue: Int);
begin
  Value := AValue;
end;

destructor TNode.Destroy;
begin
  Inc(Freed);
  inherited Destroy();
end;

procedure Deep(N: Int);
begin
  Depth := Depth + 1;
  if N = 0 then
    raise EMine.Create('bottom reached at ' + IntToStr(Depth));
  Deep(N - 1);
end;

function Build(N: Int): TNode;
var
  I: Int;
  H: TNode;
begin
  H := nil;
  for I := 1 to N do
  begin
    Result := TNode.Create(I);
    Result.Next := H;
    H := Result;
  end;
end;

var
  L: TNode;
  A: array of Int;
  S: string;
  I, Sum: Int;
begin
  S := 'Blaise';
  S := S + ' on ' + 'Windows';
  WriteLn(UpperCase(S), ' ', Length(S), ' ', Pos('on', S));
  SetLength(A, 10);
  for I := 0 to High(A) do
    A[I] := I * I;
  Sum := 0;
  for I in A do
    Sum := Sum + I;
  WriteLn('sum ', Sum);
  L := Build(5);
  WriteLn('head ', L.Value);
  L := nil;
  WriteLn('freed ', Freed);
  Tag := 'tv';
  try
    Deep(3);
  except
    on E: EMine do
      WriteLn('caught ', E.ClassName, ': ', E.Message);
  end;
  try
    try
      raise Exception.Create('inner');
    finally
      WriteLn('finally ran, tag ', Tag);
    end;
  except
    on E: Exception do
      WriteLn('outer caught ', E.Message);
  end;
  WriteLn(Format('%d-%s-%.3f', [42, 'x', 1.5]));
end.
