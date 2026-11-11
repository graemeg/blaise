# windows-run.ps1 -- the guest half of scripts/windows-vm.sh run.
#
# Runs one executable with the arguments in args.txt beside it (one command
# line, already quoted for Windows), streaming its output, and exits with its
# exit code.  The full 32-bit code is also written to standard error when it
# is not 0: ssh passes on only the low 8 bits, which turns 0xC0000005 into 5
# (design decision D7 makes the NTSTATUS code the exit code of a fault).
# A run that outlives the timeout -- a hang, or a crash that Windows Error
# Reporting holds open -- is killed and exits 124.  -Quiet leaves out the
# exit-code line, for callers that compare the program's output.
param([string]$Exe, [int]$TimeoutSec = 300, [switch]$Quiet)
$argFile = Join-Path (Split-Path $Exe) 'args.txt'
$argLine = ''
if (Test-Path $argFile) {
  $raw = Get-Content -Raw $argFile
  if ($raw) { $argLine = $raw.Trim() }
}
if ($argLine -ne '') {
  $p = Start-Process -PassThru -NoNewWindow -FilePath $Exe -ArgumentList $argLine
} else {
  $p = Start-Process -PassThru -NoNewWindow -FilePath $Exe
}
$null = $p.Handle
if (-not $p.WaitForExit($TimeoutSec * 1000)) {
  Get-Process WerFault -ErrorAction SilentlyContinue | Stop-Process -Force
  try { $p.Kill() } catch { }
  [Console]::Error.WriteLine("windows-vm: timed out after $TimeoutSec s")
  exit 124
}
$code = $p.ExitCode
if (($code -ne 0) -and -not $Quiet) {
  [Console]::Error.WriteLine(('windows-vm: exit code 0x{0:X8}' -f $code))
}
exit $code
