param([string[]]$Modules=@('BJSHybridSieveData1000','BJSHybridSieveBoolBench1000','BJSHybridSieveData10000','BJSHybridSieveBoolBench10000','BJSHybridSieveData100000','BJSHybridSieveSerialBench100000','BJSHybridSieveInterval1000'), [int]$MaxSeconds=180, [long]$MaxWorkingSetBytes=4294967296, [int]$Threads=2, [string[]]$ExpectedFailures=@(), [string]$RepoRoot='')
$ErrorActionPreference='Stop'
if(-not $RepoRoot){$RepoRoot=(Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..\..\..')).Path}
$repo=$RepoRoot
$stage=Join-Path $PSScriptRoot 'benchmarks'
$build=Join-Path $repo '.lake\build\hybrid-primecert-benchmark'
New-Item -ItemType Directory -Force -Path $build | Out-Null
$old=$env:LEAN_PATH
$env:LEAN_PATH=$build+';'+(Join-Path $repo '.lake\build\chen-bjs-study')+';'+(Join-Path $repo '.lake\build\chen-effective')+';'+(Join-Path $repo '.lake\build\chen-dusart')
$lake=Join-Path $env:USERPROFILE '.elan\toolchains\leanprover--lean4---v4.33.0-rc1\bin\lake.exe'
$records=Join-Path $build 'hybrid-sieve-benchmark.json'
$rows=if(Test-Path -LiteralPath $records){@(Get-Content -Raw -LiteralPath $records | ConvertFrom-Json)}else{@()}
try {
 foreach($name in $Modules){
  if($name -notmatch '^[A-Za-z0-9]+$'){throw 'Invalid module name'}
  $log=Join-Path $build ($name+'.log'); $err=Join-Path $build ($name+'.stderr.log')
  $out=Join-Path $build ($name+'.olean'); $src=Join-Path $stage ($name+'.lean')
  $watch=[Diagnostics.Stopwatch]::StartNew()
  $argv=@('env','lean',"-j$Threads",'-DwarningAsError=true','-R',('"'+$stage+'"'),'-o',('"'+$out+'"'),('"'+$src+'"'))
  $proc=Start-Process -FilePath $lake -ArgumentList $argv -WorkingDirectory $repo -WindowStyle Hidden -PassThru -RedirectStandardOutput $log -RedirectStandardError $err
  $peak=0L; $cpu=0.0; $stopReason=$null; $childIds=@()
  while(-not $proc.WaitForExit(500)){
   foreach($child in @(Get-CimInstance Win32_Process -Filter "ParentProcessId=$($proc.Id) AND Name='lean.exe'")){
    $childIds+=@($child.ProcessId); $childIds=@($childIds | Select-Object -Unique)
    $p=Get-Process -Id $child.ProcessId -ErrorAction SilentlyContinue
    if($p){$peak=[Math]::Max($peak,$p.PeakWorkingSet64); $cpu=[Math]::Max($cpu,$p.CPU)}
   }
   if($watch.Elapsed.TotalSeconds -gt $MaxSeconds){$stopReason='wall_time_limit'}
   if($peak -gt $MaxWorkingSetBytes){$stopReason='memory_limit'}
   if($stopReason){
    foreach($idValue in $childIds){
      $owned=Get-CimInstance Win32_Process -Filter "ProcessId=$idValue" -ErrorAction SilentlyContinue
      if($owned -and $owned.ParentProcessId-eq$proc.Id -and $owned.Name-eq'lean.exe'){
        Stop-Process -Id $idValue -ErrorAction SilentlyContinue
      }
    }
    Stop-Process -Id $proc.Id -ErrorAction SilentlyContinue
    break
   }
  }
  $proc.WaitForExit(); $watch.Stop(); $code=$proc.ExitCode
  if($null-eq$code){$code=-1}
  $text=(Get-Content -LiteralPath $log -Raw -ErrorAction SilentlyContinue)+(Get-Content -LiteralPath $err -Raw -ErrorAction SilentlyContinue)
  $expected=$name-in$ExpectedFailures
  $passed=if($expected){$code-ne0 -and -not $stopReason -and $text-match '(?s)Tactic.*decide.*is false'}else{$code-eq0 -and -not $stopReason -and $text-notmatch 'sorryAx|error:'}
  $status=if($stopReason){$stopReason}elseif($expected-and$passed){'rejected_corrupt_certificate'}elseif($passed){'kernel_checked'}else{'failed'}
  $rows=@($rows | Where-Object {$_.module-ne$name})+@([ordered]@{module=$name;seconds=$watch.Elapsed.TotalSeconds;observedPeakLeanWorkingSetBytes=$peak;observedLeanCpuSeconds=$cpu;exitCode=$code;status=$status;threads=$Threads;sourceSha256=(Get-FileHash -LiteralPath $src).Hash.ToLower();maxSeconds=$MaxSeconds;maxWorkingSetBytes=$MaxWorkingSetBytes})
  $rows | ConvertTo-Json -Depth 6 | Set-Content -Encoding utf8 $records
  Write-Output "${name}: $status; $([Math]::Round($watch.Elapsed.TotalSeconds,3)) seconds; observed peak $peak bytes"
  if(-not $passed){Write-Output $text; throw "Sieve benchmark failed: $name ($status)"}
 }
} finally {$env:LEAN_PATH=$old}
