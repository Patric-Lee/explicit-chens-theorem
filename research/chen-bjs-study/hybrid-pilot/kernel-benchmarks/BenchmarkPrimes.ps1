param([string]$RepoRoot='', [string[]]$Modules=@('BJSHybridPrimeBatch0','BJSHybridPrimeBatch100','BJSHybridPrimeBlock900'))
$ErrorActionPreference='Stop'
if(-not $RepoRoot){$RepoRoot=(Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..\..\..')).Path}
$src=Join-Path $PSScriptRoot 'prime'
$build=Join-Path $RepoRoot '.lake\build\hybrid-prime-benchmark'
New-Item -ItemType Directory -Force -Path $build | Out-Null
$old=$env:LEAN_PATH
$env:LEAN_PATH=$build+';'+(Join-Path $RepoRoot '.lake\build\chen-bjs-study')+';'+(Join-Path $RepoRoot '.lake\build\chen-effective')+';'+(Join-Path $RepoRoot '.lake\build\chen-dusart')
$lake=Join-Path $env:USERPROFILE '.elan\toolchains\leanprover--lean4---v4.33.0-rc1\bin\lake.exe'
$rows=@()
Push-Location -LiteralPath $RepoRoot
try {
 foreach($name in $Modules){
  if($name -notin @('BJSHybridPrimeBatch0','BJSHybridPrimeBatch100','BJSHybridPrimeBlock900')){throw 'Only previously successful small batches are enabled; the failed 1000-prefix source is retained as a study artifact.'}
  $log=Join-Path $build ($name+'.log')
  $watch=[Diagnostics.Stopwatch]::StartNew()
  & $lake env lean -DwarningAsError=true -R $src -o (Join-Path $build ($name+'.olean')) (Join-Path $src ($name+'.lean')) *> $log
  $code=$LASTEXITCODE
  $watch.Stop()
  $rows+=@{module=$name;seconds=$watch.Elapsed.TotalSeconds;exitCode=$code}
  $rows | ConvertTo-Json | Set-Content -Encoding utf8 (Join-Path $build 'timings.json')
  Get-Content -LiteralPath $log
  if($code-ne0){throw "Failed prime batch: $name"}
 }
} finally {$env:LEAN_PATH=$old; Pop-Location}

