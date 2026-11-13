# windows-ci-check.ps1 -- the Windows half of the windows-crosscheck CI job
# (docs/windows-x86_64-backend-design.adoc, "Layer 2").  The Linux job
# cross-builds blaise.exe, the fixtures and the Layer 3 DLL into -Bin; this
# runs them on a real x64 Windows host and applies the self-hosting gate:
# blaise.exe compiles a program, then itself, and the result must be
# byte-identical to the cross-built blaise.exe.
#
#   pwsh scripts/windows-ci-check.ps1 -Bin target/windows
#
# Run from the checkout root (the expected outputs and the source the
# self-hosting step compiles are read from it).  Prints WINDOWS_CI_OK.
param(
  [Parameter(Mandatory = $true)][string]$Bin
)
# Continue: a native program's standard error is data here (m3fault reports
# on it), and Windows PowerShell 5.1 turns it into a terminating error
# under 'Stop'.  Every step checks the exit code itself.
$ErrorActionPreference = 'Continue'
$Root = (Get-Location).Path
$Bin = (Resolve-Path $Bin).Path
$Failed = $false

function Fail([string]$Msg) {
  Write-Host "FAIL: $Msg"
  $script:Failed = $true
}

# Out <exe> [args]: the program's standard output, LF line ends, and its
# exit code in $script:Code.
function Out([string]$Exe) {
  $Lines = & $Exe @args
  $script:Code = $LASTEXITCODE
  return (($Lines | ForEach-Object { $_.TrimEnd("`r") }) -join "`n")
}

function Expected([string]$Name) {
  $Text = [IO.File]::ReadAllText("$Root/compiler/src/it/windows/$Name.expected")
  return $Text.Replace("`r", '').TrimEnd("`n")
}

foreach ($Name in 'm3rtl', 'm7unwind', 'l3ffi') {
  Write-Host "=== $Name ==="
  $Got = Out "$Bin/$Name.exe"
  Write-Host $Got
  if ($script:Code -ne 0) { Fail "$Name.exe exited $script:Code" }
  elseif ($Got -ne (Expected $Name)) { Fail "$Name.exe output differs from $Name.expected" }
}

# D7: a fault is reported, and its NTSTATUS code is the exit code.
foreach ($F in @(@('nil', 'access violation', 'C0000005'),
                 @('div', 'integer division by zero', 'C0000094'),
                 @('stack', 'stack overflow', 'C00000FD'))) {
  Write-Host "=== m3fault $($F[0]) ==="
  $Err = & "$Bin/m3fault.exe" $F[0] 2>&1 | Out-String
  $Hex = '{0:X8}' -f $LASTEXITCODE
  Write-Host "$($Err.Trim()) (exit 0x$Hex)"
  if ($Hex -ne $F[2]) { Fail "m3fault $($F[0]) exited 0x$Hex, want 0x$($F[2])" }
  elseif (-not $Err.Contains("Runtime error: $($F[1]) (0x$($F[2]))")) {
    Fail "m3fault $($F[0]) did not report '$($F[1])'"
  }
}

# The self-hosting gate.
Write-Host '=== selfhost ==='
$Work = Join-Path $Bin 'selfhost'
New-Item -ItemType Directory -Force -Path "$Work/s2" | Out-Null
Copy-Item "$Bin/blaise.exe" "$Work/blaise.exe"
Set-Content -Path "$Work/hello.pas" -Value "program hello;`nbegin`n  WriteLn('Hello from blaise.exe');`nend."
$Rtl = "$Root/compiler/src/main/pascal"
$Std = "$Root/stdlib/src/main/pascal"
Push-Location $Work
try {
  & ./blaise.exe --source hello.pas --output hello --rtl-src $Rtl
  if ($LASTEXITCODE -ne 0) { Fail 'blaise.exe could not compile hello.pas' }
  else {
    $Got = Out ./hello.exe
    if ($Got -ne 'Hello from blaise.exe') { Fail "hello.exe printed '$Got'" }
  }
  # The native-host export check: kernel32 exports no ExitProcesz, and a
  # native link must say so rather than build an image that cannot load.
  Set-Content -Path badimport.pas -Value ("program badimport;`nprocedure ExitProcesz(C: UInt32); " +
    "external 'kernel32' name 'ExitProcesz';`nbegin`n  ExitProcesz(0);`nend.")
  $Log = cmd /c "blaise.exe --source badimport.pas --output badimport --rtl-src $Rtl 2>&1"
  if ($LASTEXITCODE -eq 0) { Fail 'blaise.exe linked an import kernel32 does not export' }
  elseif (-not (($Log | Out-String).Contains('not exported'))) {
    Fail "blaise.exe refused badimport.pas for another reason: $($Log | Out-String)"
  }
  else { Write-Host 'export check: the misspelt import was refused' }
  $Watch = [Diagnostics.Stopwatch]::StartNew()
  & ./blaise.exe --source "$Rtl/Blaise.pas" --unit-path $Rtl --unit-path $Std `
    --rtl-src $Rtl --output s2/blaise
  if ($LASTEXITCODE -ne 0) { Fail 'blaise.exe could not compile itself' }
  else {
    $A = (Get-FileHash ./blaise.exe -Algorithm SHA256).Hash
    $B = (Get-FileHash ./s2/blaise.exe -Algorithm SHA256).Hash
    Write-Host "cross-built $A"
    Write-Host "self-built  $B ($([int]$Watch.Elapsed.TotalSeconds)s)"
    if ($A -ne $B) { Fail 'the self-built blaise.exe differs from the cross-built one' }
  }
} finally {
  Pop-Location
}

if ($Failed) { exit 1 }
Write-Host 'WINDOWS_CI_OK'
