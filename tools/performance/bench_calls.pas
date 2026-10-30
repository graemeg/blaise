{
  Runtime codegen benchmark — small-leaf call overhead / inlining.

  A tight loop over tiny leaf functions (clamp + wrapping mix), the shape
  phase-1 inlining targets.  Deterministic output: 99950000000.
  Compile with each backend and time the EXECUTION.  See README.adoc.
}
program BenchCalls;

function Clamp(V, Lo, Hi: Int): Int;
begin
  if V < Lo then Exit(Lo);
  if V > Hi then Exit(Hi);
  Result := V;
end;

function Mix(A, B: Int): Int;
begin
  Result := Clamp(A + B, 0, 4000) + Clamp(A - B, -50, 50);
end;

function Run(N: Int): Int64;
var
  I: Int;
begin
  Result := 0;
  for I := 0 to N - 1 do
    Result := Result + Mix(I mod 2000, (N - I) mod 2000);
end;

begin
  WriteLn(Run(50000000));
end.
