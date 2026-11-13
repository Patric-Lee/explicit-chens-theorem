param([string]$FromModule='ZetaLean.Rigor', [string]$RepoRoot='')
$ErrorActionPreference='Stop'
if(-not $RepoRoot){$RepoRoot=(Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..\..\..')).Path}
$src=Join-Path $PSScriptRoot 'zero'
$build=Join-Path $RepoRoot '.lake\build\hybrid-zero-benchmark'
New-Item -ItemType Directory -Force -Path $build | Out-Null
$old=$env:LEAN_PATH
$env:LEAN_PATH=$build
$modules=@('ZetaLean.Rigor','ZetaLean.IntervalExp','ZetaLean.IntervalCExp','ZetaLean.HardyZ',
 'RSBoundsCompat.Arctan','HardyFirstZero.Spine','HardyFirstZero.Phase',
 'HardyFirstZero.EulerMaclaurin','HardyFirstZero.BoxSupport','HardyFirstZero.Boxes','HardyFirstZero.FirstZero','AuditFirstZero')
$index=[Array]::IndexOf($modules,$FromModule)
if($index-lt0){throw 'Unknown module'}
$modules=$modules[$index..($modules.Length-1)]
$timingPath=Join-Path $build 'timings.json'
$rows=if(Test-Path -LiteralPath $timingPath){@(Get-Content $timingPath -Raw | ConvertFrom-Json | Where-Object {$_.module-notin$modules})}else{@()}
Push-Location -LiteralPath $repoRoot
try {
 foreach($n in $modules){
  $rel=$n.Replace('.', '\')
  $out=Join-Path $build ($rel+'.olean')
  New-Item -ItemType Directory -Force -Path (Split-Path $out) | Out-Null
  $log=Join-Path $build ($n+'.log')
  $watch=[Diagnostics.Stopwatch]::StartNew()
  & C:\Users\89270\.elan\toolchains\leanprover--lean4---v4.33.0-rc1\bin\lake.exe env lean -DwarningAsError=true '-Dlinter.unnecessarySeqFocus=false' -R $src -o $out (Join-Path $src ($rel+'.lean')) *> $log
  $code=$LASTEXITCODE
  $watch.Stop()
  $rows+=@{module=$n;seconds=$watch.Elapsed.TotalSeconds;exitCode=$code;status=if($code-eq0){'kernel_compiled'}else{'failed'}}
  $rows | ConvertTo-Json | Set-Content -Encoding utf8 (Join-Path $build 'timings.json')
  Get-Content $log
  Write-Output "$n elapsed $($watch.Elapsed.TotalSeconds) seconds; exit $code"
  if($code-ne0){exit $code}
 }
} finally {$env:LEAN_PATH=$old; Pop-Location}



