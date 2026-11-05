Set-StrictMode -Version Latest

function Get-ChenLogSum([double]$A,[double]$B) {
 if([double]::IsNegativeInfinity($A)){return $B}
 if([double]::IsNegativeInfinity($B)){return $A}
 $largest=[Math]::Max($A,$B)
 return $largest+[Math]::Log([Math]::Exp($A-$largest)+[Math]::Exp($B-$largest))
}

function Get-ChenEnvelopeLog([hashtable]$Term,[double]$H) {
 $coefficient=[double]$Term.coefficient
 if(-not [double]::IsFinite($coefficient)-or $coefficient-lt0){throw 'Envelope coefficient must be finite and nonnegative.'}
 if($coefficient-eq0){return [double]::NegativeInfinity}
 $answer=[Math]::Log($coefficient)
 switch($Term.kind){
  'constant' {return $answer}
  'inverse_log' {
   if([double]$Term.logPower-lt0){throw 'Inverse-log power must be nonnegative.'}
   return $answer-[double]$Term.logPower*$H
  }
  'power_log' {
   if([double]$Term.saving-le0-or [double]$Term.logPower-lt0){throw 'A power-saving envelope needs positive saving and nonnegative log power.'}
   $logDecay=$H+[Math]::Log([double]$Term.saving)
   # Capping the subtracted decay gives a conservative finite log upper bound.
   return $answer+[double]$Term.logPower*$H-[Math]::Exp([Math]::Min([double]700,$logDecay))
  }
  'loglog_over_log' {
   if($H-le-1-or [double]$Term.loglogPower-lt0-or [double]$Term.logPower-lt0){throw 'Invalid log-log envelope parameters.'}
   return $answer+[double]$Term.loglogPower*[Math]::Log(1+$H)-[double]$Term.logPower*$H
  }
  default {throw "Unknown envelope kind: $($Term.kind)"}
 }
}

function ConvertTo-ChenMagnitude([double]$LogValue) {
 $overflow=$LogValue-gt700
 $underflow=$LogValue-lt-740-and -not[double]::IsNegativeInfinity($LogValue)
 $value=if($overflow){$null}elseif($LogValue-lt-740){0.0}else{[Math]::Exp($LogValue)}
 $display=if([double]::IsNegativeInfinity($LogValue)){'0'}elseif($overflow-or$underflow){'exp({0:G8})'-f$LogValue}else{'{0:G8}'-f$value}
 return [ordered]@{logValue=if([double]::IsNegativeInfinity($LogValue)){'-Infinity'}else{$LogValue};value=$value;display=$display;overflow=$overflow;underflow=$underflow}
}

function Test-ChenBudgetCatalog([hashtable]$Catalog) {
 if($Catalog.schemaVersion-ne1){throw 'Unsupported budget schema.'}
 foreach($group in @('kernels','products','triples','scenarios')){
  $seen=[Collections.Generic.HashSet[string]]::new()
  foreach($item in $Catalog[$group]){if(-not$seen.Add($item.id)){throw "Duplicate $group ID: $($item.id)"}}
 }
 foreach($s in $Catalog.scenarios){
  foreach($pair in @(@('product','products'),@('kernel','kernels'),@('triple','triples'))){
   if(@($Catalog[$pair[1]]|Where-Object id -eq $s[$pair[0]]).Count-ne1){throw "Unknown $($pair[0]) in scenario $($s.id)"}
  }
 }
 foreach($k in $Catalog.kernels){
  if($k.epsilon-le0-or$k.productTolerance-le0-or$k.productTolerance-gt$k.epsilon-or$k.upperC-lt0-or$k.lowerC-lt0){throw "Invalid kernel: $($k.id)"}
 }
 foreach($p in $Catalog.products){if(-not[double]::IsFinite($p.logU)-or$p.logU-le1){throw "Invalid product endpoint: $($p.id)"}}
 foreach($t in $Catalog.triples){foreach($e in $t.errors){$null=Get-ChenEnvelopeLog $e 29}}
 return $true
}

function Get-ChenProductError([hashtable]$Product) {
 $logU=[double]$Product.logU
 switch($Product.kind){
  'power_profile' {$exponentLog=[Math]::Log(130000000000000)-$logU/68}
  'reciprocal_interval' {
   # Finite-subset reciprocal estimate plus a conservative square tail.
   $exponentLog=Get-ChenLogSum (-2*[Math]::Log($logU)) ([Math]::Log(24)-[Math]::Log([Math]::Exp($logU)-1))
  }
  'asymmetric_product_target' {
   $u=[Math]::Exp($logU)
   $square=if($Product.ContainsKey('primeSquareBound')){[double]$Product.primeSquareBound}else{2/($u-1)}
   $exponentLog=[Math]::Log(1.131e-7+($u/($u-2)+.501)*$square)
  }
  default {throw "Unknown product profile: $($Product.kind)"}
 }
 # exp(x)-1 <= 2x only on 0<=x<=1; outside that range no small-error claim.
 if($exponentLog-gt0){return [ordered]@{relativeBound=$null;logRelativeBound=$null;smallErrorRange=$false}}
 return [ordered]@{relativeBound=2*[Math]::Exp($exponentLog);logRelativeBound=[Math]::Log(2)+$exponentLog;smallErrorRange=$true}
}

function Get-ChenBudgetRows([hashtable]$Catalog,[double[]]$HValues,[string[]]$ScenarioIds=@()) {
 $null=Test-ChenBudgetCatalog $Catalog
 $scenarios=@($Catalog.scenarios|Where-Object { $ScenarioIds.Count-eq0-or$_.id-in$ScenarioIds })
 foreach($id in $ScenarioIds){if($id-notin@($Catalog.scenarios|ForEach-Object id)){throw "Unknown scenario: $id"}}
 foreach($H in $HValues){
  if(-not[double]::IsFinite($H)-or$H-le0){throw 'H must be finite and positive.'}
  foreach($scenario in $scenarios){
   $product=@($Catalog.products|Where-Object id -eq $scenario.product)[0]
   $kernel=@($Catalog.kernels|Where-Object id -eq $scenario.kernel)[0]
   $triple=@($Catalog.triples|Where-Object id -eq $scenario.triple)[0]
   $missing=[Collections.Generic.List[string]]::new()
   $assumptions=[Collections.Generic.List[string]]::new()
   $missing.Add('certify_evaluated_allocations_in_Lean')
   foreach($part in @($product,$kernel)){
    if($part.ContainsKey('obligations')){foreach($obligation in $part.obligations){
     if($obligation-like'bjsStudy_*'){$assumptions.Add($obligation)}else{$missing.Add($obligation)}
    }}
   }
   if($triple.ContainsKey('obligations')){foreach($obligation in $triple.obligations){$missing.Add($obligation)}}
   $compatible=$triple.model-eq$Catalog.model-and$triple.normalization-eq$Catalog.normalization
   if(-not$compatible){$missing.Add('incompatible_counting_model_or_normalization')}
   $productError=Get-ChenProductError $product
   $productFits=$productError.smallErrorRange-and$productError.relativeBound-le$kernel.productTolerance
   if(-not$productFits){$missing.Add('product_error_exceeds_kernel_tolerance')}
   # Work in logarithmic coordinates: N itself is never constructed.
   $logQCharge=Get-ChenLogSum ([Math]::Log([Math]::Log(2))) ([Math]::Log(2)+[double]$product.logU)
   $logDelta=[Math]::Log(10)+$logQCharge-$H
   $deltaMag=ConvertTo-ChenMagnitude $logDelta
   $delta=if($deltaMag.overflow){[double]::PositiveInfinity}else{[double]$deltaMag.value}
   $baseFixed=1/(6*[double]$Catalog.baseMassBudget)
   $window=$delta+$baseFixed-le.5-and$delta+10/([double]$Catalog.mediumMassBudget)-le(1.0/6)
   if(-not$window){$missing.Add('sieve_coordinate_outside_proved_window')}
   $baseDensity=3*$delta+1/(2*[double]$Catalog.baseMassBudget)+$kernel.lowerC*$kernel.epsilon/16
   $mediumDensity=18*$delta+$kernel.upperC*$kernel.epsilon
   $t=1/[double]$Catalog.baseMassBudget
   $v=1/[double]$Catalog.mediumMassBudget
   $baseLoss=$Catalog.normalizationFactorCap*$baseDensity+40*$t*$Catalog.baseFactorCap+$t
   $mediumLoss=$Catalog.normalizationFactorCap*(1e-7+$mediumDensity*$Catalog.mediumReciprocalCap)+
     300*$v*(120+1e-7+$mediumDensity*$Catalog.mediumReciprocalCap)+$v
   $weighted=$Catalog.mainWeightedFloor-$baseLoss-$mediumLoss/2-$Catalog.boundaryError
   foreach($gate in $Catalog.sharedProofGates){if($H-lt$gate.H){$missing.Add('cutoff_not_paid:'+ $gate.id)}}
   if($triple.ContainsKey('proofGates')){foreach($gate in $triple.proofGates){if($H-lt$gate.H){$missing.Add('cutoff_not_paid:'+$gate.id)}}}
   if($triple.ContainsKey('proofGateH')-and$H-lt$triple.proofGateH){$missing.Add('cutoff_not_paid:triple_producer')}
   $logError=[double]::NegativeInfinity
   foreach($term in $triple.errors){$logError=Get-ChenLogSum $logError (Get-ChenEnvelopeLog $term $H)}
   $remainder=ConvertTo-ChenMagnitude $logError
   $hasTriple=$null-ne$triple.main-and$compatible
   $local=$null;$full=$null;$headroom=$null
   if($window-and$productFits-and$hasTriple){
    $local=$weighted-[double]$triple.main/2
    $headroom=2*$weighted-[double]$triple.main
    if(-not$remainder.overflow){$full=$local-[double]$remainder.value/2}
   }
   $moment=ConvertTo-ChenMagnitude (Get-ChenEnvelopeLog @{
     kind='loglog_over_log';coefficient=1e24;loglogPower=6;logPower=1} $H)
   if($scenario.triple-eq'current_selberg'-and([double]$moment.logValue-gt[Math]::Log(1e-12))){$missing.Add('current_selberg_moment_payment_fails')}
   [pscustomobject][ordered]@{
    H=$H;scenario=$scenario.id;classification='numerical_budget_only';model=$Catalog.model
    product=$product.id;kernel=$kernel.id;triple=$triple.id
    productRelativeErrorBound=$productError.relativeBound;productFitsKernel=$productFits
    geometryCharge=$deltaMag;sieveWindowValid=$window
    lowerErrors=[ordered]@{
     lowerDensityError=$baseDensity;upperDensityError=$mediumDensity
     lowerSieveKernel=$kernel.lowerC*$kernel.epsilon/16;upperSieveKernel=$kernel.upperC*$kernel.epsilon
     lowerLevelRounding=3*$delta+1/(2*[double]$Catalog.baseMassBudget);upperLevelRounding=18*$delta
     baseMassAndRemainder=40*$t*$Catalog.baseFactorCap+$t
     mediumIntegralRounding=$Catalog.normalizationFactorCap*1e-7
     mediumMassAndDistribution=300*$v*(120+1e-7+$mediumDensity*$Catalog.mediumReciprocalCap)+$v
     baseCoefficient=$baseLoss;mediumCoefficient=$mediumLoss;boundary=$Catalog.boundaryError
    }
    weightedFloor=if([double]::IsFinite($weighted)){$weighted}else{$null}
    localMarginBeforeTripleRemainder=$local
    maximumTripleRemainder=$headroom
    maximumTripleTotalCoefficient=if($window-and$productFits-and[double]::IsFinite($weighted)){2*$weighted}else{$null}
    tripleRemainder=if($hasTriple){$remainder}else{$null};fullMargin=$full
    algebraicallyPositive=($null-ne$full-and$full-gt0)
    currentSelbergMomentEnvelope=$moment
    temporaryAssumptions=@($assumptions|Sort-Object -Unique)
    missingEstimates=@($missing|Sort-Object -Unique)
    closedLeanCertificateAtThisH=$false
   }
  }
 }
}

Export-ModuleMember -Function Get-ChenEnvelopeLog,ConvertTo-ChenMagnitude,Test-ChenBudgetCatalog,Get-ChenBudgetRows
