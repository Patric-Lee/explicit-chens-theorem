$ErrorActionPreference='Stop'
Import-Module (Join-Path $PSScriptRoot 'JointBudget.psm1') -Force
function Assert-Joint([bool]$Condition,[string]$Message){if(-not$Condition){throw $Message}}
$current=Get-ChenJointRow -H 188 -LogU (120*[Math]::Log(3))
Assert-Joint ($current.denominatorFits-and$current.finalMargin-gt0) 'Known large-cutoff allocation must remain feasible.'
$raw=Get-ChenJointRow -H 30 -LogU ([Math]::Log(1e7))
Assert-Joint ($raw.finalMargin-lt0-and -not$raw.denominatorFits) 'Current remainder and moment bounds cannot prove H=30.'
$candidate=Get-ChenJointRow -H 30 -LogU ([Math]::Log(1e7)) -TripleErrorCap 1e8 -MomentCoefficient 100 -MomentPower 2
Assert-Joint ($candidate.algebraicallyFeasible-and -not$candidate.provedChenCutoff) 'A feasible candidate must never become a theorem.'
Assert-Joint ('sharper_uniform_normalized_Selberg_error'-in$candidate.missingEstimates) 'A hypothetical moment bound needs a proof obligation.'
Assert-Joint ('sharper_actual_square_and_triple_remainder'-in$candidate.missingEstimates) 'A reduced triple constant needs an actual producer.'
Assert-Joint ('mass_and_distribution_producers_at_this_cutoff'-in$candidate.missingEstimates) 'Distribution thresholds must not disappear.'
$looser=Get-ChenJointRow -H 30 -LogU ([Math]::Log(1e7)) -DenominatorK 8.2 -TripleErrorCap 1e8 -MomentCoefficient 100 -MomentPower 2
Assert-Joint ($looser.denominatorAllowance-gt$candidate.denominatorAllowance-and$looser.finalMargin-lt$candidate.finalMargin) 'Relaxing the denominator must consume triple margin.'
$bad=Get-ChenJointRow -H 30 -LogU ([Math]::Log(1e7)) -ProductError .001 -TripleErrorCap 1e8 -MomentCoefficient 100 -MomentPower 2
Assert-Joint (-not$bad.algebraicallyFeasible-and'density_adapter_for_larger_product_error'-in$bad.missingEstimates) 'An unsupported product tolerance must not be accepted.'
Write-Output 'Joint-budget normalization, sensitivity, and missing-input checks passed.'
