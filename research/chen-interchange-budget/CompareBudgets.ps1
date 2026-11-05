param(
 [string]$CatalogPath=(Join-Path $PSScriptRoot 'catalog.json'),
 [double[]]$HValues=@(29,25,20,15),
 [string[]]$ScenarioIds=@(),
 [string]$OutputPath=''
)
$ErrorActionPreference='Stop'
Import-Module (Join-Path $PSScriptRoot 'BudgetEngine.psm1') -Force
$catalog=Get-Content -Raw -LiteralPath $CatalogPath|ConvertFrom-Json -AsHashtable
$rows=@(Get-ChenBudgetRows $catalog $HValues $ScenarioIds)
$report=[ordered]@{
 status='Numerical exploration. Only the separately listed Lean route certificates prove a cutoff.'
 formalRoutes=$catalog.formalRoutes
 rows=$rows
}
if($OutputPath){[IO.File]::WriteAllText($OutputPath,($report|ConvertTo-Json -Depth 12)+"`n")}
$rows|Select-Object H,scenario,sieveWindowValid,productFitsKernel,localMarginBeforeTripleRemainder,
 @{n='tripleError';e={if($null-eq$_.tripleRemainder){'unavailable'}else{$_.tripleRemainder.display}}},@{n='fullMargin';e={if($null-ne$_.fullMargin){'{0:G6}'-f$_.fullMargin}else{'--'}}},
 @{n='unpaid';e={$_.missingEstimates.Count}}|Format-Table -AutoSize|Out-String -Width 220
