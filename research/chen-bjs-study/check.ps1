param([string]$RepoRoot='', [string]$FromModule='BJSIntervalOrder')
$ErrorActionPreference='Stop'
& (Join-Path $PSScriptRoot 'source-audit.ps1')
if(-not $RepoRoot){$RepoRoot=(Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..')).Path}
$build=Join-Path $RepoRoot '.lake\build-434\chen-bjs-study'
$production=Join-Path $RepoRoot '.lake\build-434\chen-effective'
$previousLeanPath=$env:LEAN_PATH
$env:LEAN_PATH=(Join-Path $RepoRoot '.lake\build-434\chen-dusart')+';'+$build+';'+$production
$lake=Join-Path $env:USERPROFILE '.elan\toolchains\leanprover--lean4---v4.34.1\bin\lake.exe'
$modules=@('BJSIntervalOrder','BJSLayerQuadrature','BJSLayerTwo','BJSLayerTwoSharp','BJSSharpHat','BJSSharpRecurrence','BJSLayerTableData','BJSGridCertificate','BJSGridProfile','BJSLayerTableChecks','BJSAnalyticTail','BJSLayerProfile','BJSParitySums','BJSDiscreteEnvelope','BJSDiscreteAnalytic','BJSDiscreteInduction','BJSDiscreteParity','BJSSharpDensity','BJSStudyInputs','BJSProvedProductProfile','BJSStudyElementaryMertens','BJSReciprocalIntervalBridge','BJSMertensThetaTarget','DusartThetaTail','DusartMertens','DusartZeroKernel','BJSStudyProducts','BJSStudyAssembly','BJSStudyFiniteCap','BJSStudyGeometry','BJSStudyGoldbach','BJSStudyBase','BJSStudyMedium','BJSStudyMediumReciprocal','BJSStudyAggregate','BJSStudyLower','BJSReciprocalLargeEndpoint','BJSCanonicalMertensUpper','BJSFiniteLogBounds','BJSSmallPrefixCertificate','BJSSmallSignedPrefix','BJSReciprocalTail3300','BJSReciprocalRemainingRange','BJSStudyMertens','BJSStudyLogGate','BJSStudySelbergDivisors','BJSStudySelbergMoments','BJSStudySelbergDenominator','BJSStudyTriple','BJSStudyChen','BJSStudyH36','BJSStudyFiniteTail','BJSStudyCompatibility','AuditBJSStudy','BJSSelbergSpecialization','BJSJointBudget','BJSSelbergLogEnvelope','BJSJointTriple','BJSJointChen','AuditBJSJoint','BJSHarmonicKernel','BJSPowerTails','BJSSquareHarmonic','BJSSquareHarmonicMass','BJSSelbergSignedMoment','BJSSelbergTwoTermIdentity','BJSSelbergCriticalKernel','BJSSelbergCriticalMass','BJSConvolutionRemainder','BJSSelbergSquareKernel','BJSSelbergSquareConvolution','BJSSelbergSquareRemainder','AuditBJSSelbergExpansion','BJSExpandedDenominator','BJSExpandedChen','AuditBJSExpandedChen','BJSTightPrimePairThreshold','BJSTightPrimePairInterval','BJSTightMediumPrimeGrid','BJSTightMediumPrimeSum','BJSTightMediumPrimeShift','BJSTightGeometry','BJSTightGoldbach','BJSH30PrimeIntervals','BJSH30PrimePairGrid','BJSH30PrimePairMain','BJSH30Parameters','BJSH30PanQuotient','BJSH30PanPrimePrefix','BJSH30PanLow','BJSH30PanPrincipalPNT','BJSH30PanPrincipal','BJSH30PanLedger','BJSH30PanUnweighted','BJSH30PanEnvelope','BJSH30PanWeighted','BJSH30PanSource','BJSH30PanNormalization','BJSH30PanR1','BJSH30SelbergRemainder','BJSH30SquareConstants','BJSH30SquareCap','BJSH30Denominator','BJSH30SquareTriple','BJSH30MertensProduct','BJSH30GoldbachProduct','BJSH30SourceMass','BJSH30SourceUpperMass','BJSH30MassCap','BJSH30DistributionGeometry','BJSH30WeightedDistribution','BJSH30Distribution','BJSH30BaseDistribution','BJSH30Geometry','BJSTightBase','BJSTightMedium','BJSTightMediumReciprocal','BJSTightAggregate','BJSTightFiniteCap','BJSTightLower','BJSTightChen','BJSH30Budget','AuditBJSTightBudget','BJSH30FifthConstants','BJSH30FifthCap','BJSH30FifthTriple','BJSH30SmallEndpoint','AuditBJSH30Triple','BJSHybridPrimePowers','BJSHybridZeroKernel','BJSHybridMomentResidual','BJSHybridProductBridge','AuditBJSHybridPilot','BJSHybridZeroReindex','BJSHybridZeroSplit','BJSHybridHeadDerivative','BJSHybridUnsmoothing','BJSHybridPsiPrimitive','BJSHybridWeightedBridge','BJSHybridMertensTransfer','BJSHybridIntegratedEnvelope','BJSHybridIntegralBounds','BJSHybridPrimePowerIntegral','BJSHybridAnalyticBridge','BJSHybridPrimeCertificate','BJSHybridPrimeBlock','AuditBJSHybridBridge','BJSHybridSieveCore','BJSHybridSieveHelpers','BJSHybridSieveCorrect','BJSHybridSieveSums','BJSHybridSieveBlocks','BJSHybridSievePacked','AuditBJSHybridSieve','BJSHybridSharpPrimePowers','BJSHybridSharpPrimePowerIntegral','BJSHybridSharpAnalyticBridge','AuditBJSHybridSharpBridge')
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
 if(Test-Path -LiteralPath "$build\AuditBJSJoint.log"){Get-Content "$build\AuditBJSJoint.log"}
 if(Test-Path -LiteralPath "$build\AuditBJSSelbergExpansion.log"){Get-Content "$build\AuditBJSSelbergExpansion.log"}
 if(Test-Path -LiteralPath "$build\AuditBJSExpandedChen.log"){Get-Content "$build\AuditBJSExpandedChen.log"}
 if(Test-Path -LiteralPath "$build\AuditBJSTightBudget.log"){Get-Content "$build\AuditBJSTightBudget.log"}
 if(Test-Path -LiteralPath "$build\AuditBJSH30Triple.log"){Get-Content "$build\AuditBJSH30Triple.log"}
 if(Test-Path -LiteralPath "$build\AuditBJSHybridPilot.log"){Get-Content "$build\AuditBJSHybridPilot.log"}
 if(Test-Path -LiteralPath "$build\AuditBJSHybridBridge.log"){Get-Content "$build\AuditBJSHybridBridge.log"}
 if(Test-Path -LiteralPath "$build\AuditBJSHybridSieve.log"){Get-Content "$build\AuditBJSHybridSieve.log"}
} finally {
 $env:LEAN_PATH=$previousLeanPath
 Pop-Location
}
