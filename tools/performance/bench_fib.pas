{
  Runtime codegen benchmark — recursion / call-heavy.

  Naive recursive Fibonacci repeated 20x.  Stresses call overhead and
  local-variable register pressure — the case where a good register
  allocator (QBE) most out-performs a spill-everything backend (native).

  Deterministic output: 114057740.  Compile with each backend and time
  the EXECUTION (not the compile).  See README.adoc.
}
program BenchFib;

function Fib(N: Int): Int64;
begin
  if N < 2 then
    Result := N
  else
    Result := Fib(N - 1) + Fib(N - 2);
end;

var
  i: Int;
  sum: Int64;
begin
  sum := 0;
  for i := 1 to 20 do
    sum := sum + Fib(34);
  WriteLn(sum);
end.
