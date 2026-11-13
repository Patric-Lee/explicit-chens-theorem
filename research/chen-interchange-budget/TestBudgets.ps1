$ErrorActionPreference='Stop'
Import-Module (Join-Path $PSScriptRoot 'BudgetEngine.psm1') -Force
$catalog=Get-Content -Raw (Join-Path $PSScriptRoot 'catalog.json')|ConvertFrom-Json -AsHashtable
$checks=0
function Assert-Budget([bool]$Condition,[string]$Message){if(-not$Condition){throw $Message};$script:checks++}
function Copy-Catalog {return ($catalog|ConvertTo-Json -Depth 12|ConvertFrom-Json -AsHashtable)}

$inverse=Get-ChenEnvelopeLog @{kind='inverse_log';coefficient=2e40;logPower=1} 29
Assert-Budget ([Math]::Abs($inverse-([Math]::Log(2)+40*[Math]::Log(10)-29))-lt1e-10) 'Inverse-log remainder was flattened or normalized incorrectly.'
$power=Get-ChenEnvelopeLog @{kind='power_log';coefficient=3;logPower=2;saving=.1} 10
Assert-Budget ([Math]::Abs($power-([Math]::Log(3)+20-.1*[Math]::Exp(10)))-lt1e-9) 'Power saving lost its dependence on N.'
$tiny=ConvertTo-ChenMagnitude (Get-ChenEnvelopeLog @{kind='power_log';coefficient=3;logPower=2;saving=.1} 1000)
Assert-Budget ($tiny.underflow-and$tiny.logValue-lt-1e300) 'Tiny positive errors must retain a finite logarithmic envelope.'
$zero=ConvertTo-ChenMagnitude (Get-ChenEnvelopeLog @{kind='constant';coefficient=0} 29)
Assert-Budget ($zero.display-eq'0'-and -not$zero.underflow) 'Exact zero must be distinguished from floating-point underflow.'

$row=@(Get-ChenBudgetRows $catalog @(29) @('million_with_verified_sieve'))[0]
Assert-Budget ($row.localMarginBeforeTripleRemainder-gt0-and$row.fullMargin-lt0) 'A positive local sieve margin must still pay the full triple remainder.'
Assert-Budget ($row.missingEstimates.Count-gt0-and -not$row.closedLeanCertificateAtThisH) 'An unproved target profile must not become a closed theorem.'
Assert-Budget ('cutoff_not_paid:current_mass_distribution_cap'-in$row.missingEstimates) 'Producer cutoffs must remain visible.'

$provedDensity=@(Get-ChenBudgetRows $catalog @(29) @('small_endpoint_with_bjs_sieve'))[0]
Assert-Budget ($provedDensity.temporaryAssumptions.Count-eq0) 'Proved BJS density adapters must not remain in the temporary-axiom ledger.'
$conditionalProduct=@(Get-ChenBudgetRows $catalog @(188) @('bjs_components'))[0]
Assert-Budget ($conditionalProduct.temporaryAssumptions.Count-eq0) 'The proved active product must not retain the removed interval axiom.'

$slot=@(Get-ChenBudgetRows $catalog @(29) @('improved_selberg_slot'))[0]
Assert-Budget ($null-eq$slot.tripleRemainder-and$null-eq$slot.fullMargin-and -not$slot.algebraicallyPositive) 'A missing triple formula was treated as a zero error.'
$switched=@(Get-ChenBudgetRows $catalog @(29) @('switched_triple_slot'))[0]
Assert-Budget ('incompatible_counting_model_or_normalization'-in$switched.missingEstimates) 'A switched counting model needs a proved normalization/counting adapter.'

$copy=Copy-Catalog
$copy.triples[0].normalization='different_scale'
$mismatch=@(Get-ChenBudgetRows $copy @(29) @('million_with_verified_sieve'))[0]
Assert-Budget ($null-eq$mismatch.fullMargin-and'incompatible_counting_model_or_normalization'-in$mismatch.missingEstimates) 'Normalization mismatch was silently accepted.'
$copy=Copy-Catalog
$copy.kernels[0].productTolerance=1e-10
$copy.kernels[0].epsilon=1e-10
$badProfile=@(Get-ChenBudgetRows $copy @(29) @('million_with_verified_sieve'))[0]
Assert-Budget (-not$badProfile.productFitsKernel-and$null-eq$badProfile.fullMargin) 'An incompatible product error was accepted by the kernel budget.'

$huge=@(Get-ChenBudgetRows $catalog @(3187) @('production_components'))[0]
Assert-Budget ($huge.sieveWindowValid-and$huge.algebraicallyPositive-and -not$huge.closedLeanCertificateAtThisH) 'A numerical calculation must not fabricate a Lean certificate, even above a known cutoff.'
Assert-Budget ($huge.tripleRemainder.underflow-and$huge.tripleRemainder.logValue-lt0) 'The huge-cutoff calculation discarded the positive remainder envelope.'

$copy=Copy-Catalog
$copy.scenarios[0].kernel='missing_kernel'
$rejected=$false
try {$null=Test-ChenBudgetCatalog $copy} catch {$rejected=$true}
Assert-Budget $rejected 'A missing component reference must be rejected.'
Write-Output "$checks meaningful numerical/contract checks passed."
