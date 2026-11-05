param([string]$InputPath=(Join-Path $PSScriptRoot 'comparison.json'),[string]$OutputPath=(Join-Path $PSScriptRoot 'comparison.md'))
$ErrorActionPreference='Stop'
$report=Get-Content -Raw -LiteralPath $InputPath|ConvertFrom-Json -AsHashtable
$lines=[Collections.Generic.List[string]]::new()
$lines.Add('# Interchangeable Chen budget: target comparison')
$lines.Add('')
$lines.Add('Numerical exploration only. Positive local margins below assume the listed product and analytic inputs. No new cutoff is certified by this report.')
$lines.Add('')
$lines.Add('| H | Product / sieve | Local margin before triple remainder | Maximum allowed extra triple coefficient | Current triple remainder formula |')
$lines.Add('|---:|---|---:|---:|---:|')
foreach($r in $report.rows|Where-Object {$_.scenario-in@('million_with_verified_sieve','small_endpoint_with_bjs_sieve')}){
 $label=if($r.scenario-eq'million_with_verified_sieve'){'U=10^6 / verified 4806'}else{'U=1500 / assumed BJS 110'}
 $local=if($null-eq$r.localMarginBeforeTripleRemainder){'outside sieve window'}else{'{0:F6}'-f$r.localMarginBeforeTripleRemainder}
 $room=if($null-eq$r.maximumTripleRemainder){'unavailable'}else{'{0:F6}'-f$r.maximumTripleRemainder}
 $lines.Add(('| {0:G6} | {1} | {2} | {3} | {4} |'-f$r.H,$label,$local,$room,$r.tripleRemainder.display))
}
$lines.Add('')
$lines.Add('These formulas are evaluated outside several known validity ranges. The JSON ledger retains those unpaid cutoffs; the displayed values are not asserted as bounds on the actual counts at these targets.')
$lines.Add('')
$lines.Add('The local margin includes base, medium, mass/remainder allocations, level rounding, the endpoint allocation and half of the current triple main coefficient 3.94033. The current inverse-log triple remainder is still enormous at these targets; it is never replaced by the 0.01 allocation paid at the much larger proved cutoff.')
$lines.Add('')
$lines.Add('The U=10^6 profile needs an unproved all-interval asymmetric prime-product estimate and endpoint bridges. The U=1500 profile additionally needs a port of the external prime-square certificate and uses the two existing temporary BJS density assumptions. Neither profile supplies mass/distribution estimates at these H values.')
$lines.Add('')
$lines.Add('Research slots for improved Selberg moments and a switched bilinear triple estimate are present in catalog.json. Missing formulas remain unavailable. The switched route also needs a proved counting-model and normalization adapter.')
$lines.Add('')
$lines.Add('Known Lean certificates remain 3^(3^2900) with Dirichlet only and 3^(3^171) with the three existing temporary BJS assumptions. They are reproduced by the new route adapters, independently of their old final Chen proofs.')
[IO.File]::WriteAllText($OutputPath,($lines-join"`n")+"`n")
Write-Output $OutputPath
