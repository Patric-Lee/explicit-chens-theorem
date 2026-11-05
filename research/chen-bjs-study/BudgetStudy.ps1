param([string]$OutputPath='')
$ErrorActionPreference='Stop'
$log3=[Math]::Log(3)
$loglog3=[Math]::Log($log3)
$results=[ordered]@{
 status='PROVISIONAL; only the ordered interval assumption remains'
 production_commit='6b412908'
 production_H=2900*$log3+$loglog3
 provisional_cutoff='3^(3^171)'
 provisional_H=171*$log3+$loglog3
 provisional_weighted_coefficient=2.6408-1.0/20-1.13/2-1.0/20000
 provisional_margin=2.6408-1.0/20-1.13/2-1.0/20000-3.94033/2-.01/2
 presieve_log_U=120*$log3
 actual_geometry_sufficient_H=[Math]::Log(1e20)+[Math]::Log(2)+120*$log3
 shared_finite_cap_H=[Math]::Log(20)+80*[Math]::Log(10)+$loglog3
 elementary_mertens_divisor_H=30*$log3+$loglog3
 denominator_and_prime_pair_H=80*[Math]::Log(10)+$loglog3
 triple_remainder_H=[Math]::Log(200)+40*[Math]::Log(10)
 temporary_axioms=@('bjsStudy_interval')
 H36=[ordered]@{
  status='Scalar feasibility only; NOT a Chen theorem'
  presieve_U=1e9
  geometry_ratio_bound=(10*(1+2e9))/[Math]::Exp(36)
  geometry_budget=1e-5
  lower_density_error=3e-5+110.0/2000/16+1.0/(2*20000000)
  upper_density_error=18e-5+110.0/2000
  final_margin=.040585
  missing=@('Uniform small-endpoint product bridge','Mass and distribution estimates at H=36','Triple moment and remainder estimates at H=36')
 }
}
$json=$results|ConvertTo-Json -Depth 6
if($OutputPath){[IO.File]::WriteAllText($OutputPath,$json+"`n")}
$json
