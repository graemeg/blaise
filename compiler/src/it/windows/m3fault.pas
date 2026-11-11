program m3fault;

{ Windows milestone M3 program under test: the fault handler of
  runtime.start.windows (design decision D7).  The first argument picks the
  fault -- nil (an access violation), div (integer division by zero) or
  stack (unbounded recursion) -- and scripts/windows-vm.sh crosscheck
  expects the report on standard error and the NTSTATUS code as the exit
  code. }
type
  PInt = ^Int;

function Recurse(N: Int): Int;
var
  Pad: array[0..63] of Int;
begin
  Pad[0] := N;
  Result := Recurse(N + 1) + Pad[0];
end;

var
  P: PInt;
  A, B: Int;
begin
  WriteLn('mode ', ParamStr(1));
  if ParamStr(1) = 'nil' then
  begin
    P := nil;
    P^ := 1;
  end
  else if ParamStr(1) = 'div' then
  begin
    A := 1;
    B := ParamCount() - 1;
    WriteLn(A div B);
  end
  else
    WriteLn(Recurse(0));
  WriteLn('not reached');
end.
