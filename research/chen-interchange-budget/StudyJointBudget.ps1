param([string]$OutputPath=(Join-Path $PSScriptRoot 'joint-results.json'))
$ErrorActionPreference='Stop'
Import-Module (Join-Path $PSScriptRoot 'JointBudget.psm1') -Force
$rows=@(
 Get-ChenJointRow -H 188 -LogU (120*[Math]::Log(3))
 foreach($H in @(33,30,29)) {
  Get-ChenJointRow -H $H -LogU ([Math]::Log(1e7))
  Get-ChenJointRow -H $H -LogU ([Math]::Log(1e7)) -TripleErrorCap 1e8
  Get-ChenJointRow -H $H -LogU ([Math]::Log(1e7)) -TripleErrorCap 1e8 -MomentCoefficient 100 -MomentPower 2
 }
)
$report=[ordered]@{
 status='Numerical studies only. Candidate estimates are explicit inputs, never axioms or Lean producers.'
 currentChenCutoff='3^(3^171)'; currentChenH=187.95674918986347
 provedRelaxedDenominatorCutoff='3^(3^83)'
 provedRelaxedDenominatorH=83*[Math]::Log(3)+[Math]::Log([Math]::Log(3))
 relaxedDenominatorK=8.1
 publishedSquareRootRemainderStatus='Not formalized or assigned numerical uniform constants'
 rows=$rows
}
[IO.File]::WriteAllText($OutputPath,($report|ConvertTo-Json -Depth 8)+"`n")
$rows|Select-Object H,denominatorK,@{n='shift';e={'{0:G6}'-f$_.geometryShift}},
 @{n='margin';e={'{0:G6}'-f$_.finalMargin}},
 @{n='denominatorError';e={'{0:G6}'-f$_.denominatorNormalizedError}},denominatorFits,algebraicallyFeasible,
 @{n='unpaid';e={$_.missingEstimates.Count}}|Format-Table -AutoSize|Out-String -Width 180
