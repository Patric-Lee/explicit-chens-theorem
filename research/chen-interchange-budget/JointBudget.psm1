Set-StrictMode -Version Latest

function Get-ChenJointRow {
 param(
  [double]$H,
  [double]$LogU,
  [double]$DenominatorK=8.1,
  [double]$TripleErrorCap=1e40,
  [double]$MomentCoefficient=1e24,
  [int]$MomentPower=6,
  [double]$ProductError=.00025,
  [double]$BaseMassBudget=2e7,
  [double]$MediumMassBudget=1e12
 )
 foreach($number in @($H,$LogU,$DenominatorK,$TripleErrorCap,$MomentCoefficient,$ProductError,$BaseMassBudget,$MediumMassBudget)) {
  if(-not [double]::IsFinite($number)-or$number-le0){throw 'Joint inputs must be finite and positive.'}
 }
 if($H-gt700-or$LogU-gt700-or$MomentPower-lt0-or$DenominatorK-le8){throw 'Unsupported joint input range.'}
 $L=[Math]::Exp($H)
 $U=[Math]::Exp($LogU)
 $delta=10*([Math]::Log(2)+2*$U)/$L
 $epsilon=1e-10
 $weight=.49254+1e-7
 # These are the same explicit source-allocation formulas as BudgetEngine.
 # Their use below is a numerical study, not a producer at the evaluated H.
 $lowerKernel=220*$ProductError/16
 $upperKernel=220*$ProductError
 $baseDensity=3*$delta+1/(2*$BaseMassBudget)+$lowerKernel
 $mediumDensity=18*$delta+$upperKernel
 $baseLoss=12.5*$baseDensity+40*6/$BaseMassBudget+1/$BaseMassBudget
 $mediumLoss=12.5*(1e-7+1.6*$mediumDensity)+
   300/$MediumMassBudget*(120+1e-7+1.6*$mediumDensity)+1/$MediumMassBudget
 $weighted=2.6408-$baseLoss-$mediumLoss/2-1.0/20000
 $tripleMain=$DenominatorK*$weight
 # S(N)>=1/2 gives the normalized triple error 2*C/log(N).
 $tripleError=2*$TripleErrorCap/$L
 $margin=$weighted-($tripleMain+$tripleError)/2
 $momentLog=[Math]::Log($MomentCoefficient)+$MomentPower*[Math]::Log(1+$H)-$H
 $momentError=if($momentLog-gt700){[double]::PositiveInfinity}else{[Math]::Exp($momentLog)}
 $denominatorAllowance=1.0/8-1/$DenominatorK-$epsilon/4-[Math]::Log(2)/(2*$L)
 $window=$delta+1/(6*$BaseMassBudget)-le.5-and$delta+10/$MediumMassBudget-le(1.0/6)
 $missing=[Collections.Generic.List[string]]::new()
 if($LogU-lt120*[Math]::Log(3)){$missing.Add('small_endpoint_relative_product')}
 if($ProductError-gt1.0/4000){$missing.Add('density_adapter_for_larger_product_error')}
 if($H-lt187.29658754069436){$missing.Add('mass_and_distribution_producers_at_this_cutoff')}
 if($delta-gt1e-7){$missing.Add('source_count_bounds_with_reallocated_geometry')}
 if($MomentCoefficient-ne1e24-or$MomentPower-ne6){$missing.Add('sharper_uniform_normalized_Selberg_error')}
 if($TripleErrorCap-ne1e40){$missing.Add('sharper_actual_square_and_triple_remainder')}
 if(-not$window){$missing.Add('sieve_coordinate_windows')}
 if($H-lt184.30085526714038){$missing.Add('square_analytic_and_prime_pair_thresholds')}
 if($H-lt33.05241648765999){$missing.Add('small_endpoint_divisor_product')}
 $missing.Add('certify_all_numerical_allocations_and_uniformity_in_Lean')
 [pscustomobject][ordered]@{
  classification='conditional_numerical_study'; H=$H; logU=$LogU
  denominatorK=$DenominatorK; productError=$ProductError; geometryShift=$delta
  sieveWindowValid=$window; baseLoss=$baseLoss; mediumLoss=$mediumLoss
  weightedFloor=$weighted; tripleMain=$tripleMain; normalizedTripleRemainder=$tripleError
  finalMargin=$margin; maximumTripleErrorCap=($weighted-$tripleMain/2)*$L
  denominatorNormalizedErrorLog=$momentLog; denominatorNormalizedError=$momentError
  denominatorAllowance=$denominatorAllowance
  denominatorFits=($momentError-le$denominatorAllowance)
  maximumDenominatorK=if($weighted-$TripleErrorCap/$L-gt0){2*($weighted-$TripleErrorCap/$L)/$weight}else{$null}
  algebraicallyFeasible=($window-and$ProductError-le1.0/4000-and$margin-gt0-and$momentError-le$denominatorAllowance)
  missingEstimates=@($missing); provedChenCutoff=$false
 }
}

Export-ModuleMember -Function Get-ChenJointRow
