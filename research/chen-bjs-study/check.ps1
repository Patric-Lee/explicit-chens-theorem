param([string]$RepoRoot='', [string]$FromModule='BJSIntervalOrder')
$ErrorActionPreference='Stop'
& (Join-Path $PSScriptRoot 'source-audit.ps1')
if(-not $RepoRoot){$RepoRoot=(Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..')).Path}
$build=Join-Path $RepoRoot '.lake\build\chen-bjs-study'
$production=Join-Path $RepoRoot '.lake\build\chen-effective'
$previousLeanPath=$env:LEAN_PATH
$env:LEAN_PATH=(Join-Path $RepoRoot '.lake\build\chen-dusart')+';'+$build+';'+$production
$lake=Join-Path $env:USERPROFILE '.elan\toolchains\leanprover--lean4---v4.33.0-rc1\bin\lake.exe'
$modules=@('BJSIntervalOrder','BJSLayerQuadrature','BJSLayerTwo','BJSLayerTwoSharp','BJSSharpHat','BJSSharpRecurrence','BJSLayerTableData','BJSGridCertificate','BJSGridProfile','BJSLayerTableChecks','BJSAnalyticTail','BJSLayerProfile','BJSParitySums','BJSDiscreteEnvelope','BJSDiscreteAnalytic','BJSDiscreteInduction','BJSDiscreteParity','BJSSharpDensity','BJSStudyInputs','BJSProvedProductProfile','BJSStudyElementaryMertens','BJSReciprocalIntervalBridge','BJSMertensThetaTarget','DusartThetaTail','DusartMertens','DusartZeroKernel','BJSStudyProducts','BJSStudyAssembly','BJSStudyFiniteCap','BJSStudyGeometry','BJSStudyGoldbach','BJSStudyBase','BJSStudyMedium','BJSStudyMediumReciprocal','BJSStudyAggregate','BJSStudyLower','BJSReciprocalLargeEndpoint','BJSCanonicalMertensUpper','BJSFiniteLogBounds','BJSSmallPrefixCertificate','BJSSmallSignedPrefix','BJSReciprocalTail3300','BJSReciprocalRemainingRange','BJSStudyMertens','BJSStudyLogGate','BJSStudySelbergDivisors','BJSStudySelbergMoments','BJSStudySelbergDenominator','BJSStudyTriple','BJSStudyChen','BJSStudyH36','BJSStudyFiniteTail','BJSStudyCompatibility','AuditBJSStudy')
$index=[Array]::IndexOf($modules,$FromModule)
if($index -lt 0){throw "Unknown module: $FromModule"}
New-Item -ItemType Directory -Force -Path $build | Out-Null
Push-Location -LiteralPath $RepoRoot
try {
 foreach($name in $modules[$index..($modules.Length-1)]){
  if($name-eq'BJSStudyProducts'){ & (Join-Path $RepoRoot 'research\chen-dusart\check.ps1') -RepoRoot $RepoRoot; if($LASTEXITCODE-ne0){throw 'Dusart prerequisites failed'} }
  & $lake env lean -DwarningAsError=true -R $PSScriptRoot -o "$build\$name.olean" "$PSScriptRoot\$name.lean" *> "$build\$name.log"
  if($LASTEXITCODE -ne 0){Get-Content "$build\$name.log"; throw "Lean failed: $name"}
  if(Select-String -LiteralPath "$build\$name.log" -Pattern 'sorryAx' -Quiet){throw "Placeholder in $name"}
  Write-Output "Verified module $name"
 }
 Get-Content "$build\AuditBJSStudy.log"
} finally {
 $env:LEAN_PATH=$previousLeanPath
 Pop-Location
}
