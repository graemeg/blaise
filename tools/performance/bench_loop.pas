{
  Runtime codegen benchmark — tight integer arithmetic loop.

  50 million iterations of integer mod/mul/add — no recursion, no calls.
  Measures raw arithmetic codegen quality; the backends are closer here
  than on the call-heavy bench_fib.

  Deterministic output: 349999994.  Compile with each backend and time
  the EXECUTION (not the compile).  See README.adoc.
}
program BenchLoop;

var
  i, j: Int;
  acc: Int64;
begin
  acc := 0;
  for i := 1 to 50000000 do
  begin
    j := i mod 7;
    acc := acc + j * 3 - (i mod 5);
  end;
  WriteLn(acc);
end.
