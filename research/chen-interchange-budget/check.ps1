param([string]$RepoRoot='', [string]$FromModule='ChenRouteBudget')
$ErrorActionPreference='Stop'
if(-not$RepoRoot){$RepoRoot=(Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..')).Path}
& (Join-Path $PSScriptRoot 'source-audit.ps1')
& (Join-Path $PSScriptRoot 'TestBudgets.ps1')
& (Join-Path $PSScriptRoot 'TestJointBudget.ps1')
$build=Join-Path $RepoRoot '.lake\build-434\chen-interchange-budget'
$previousLeanPath=$env:LEAN_PATH
$env:LEAN_PATH=$build+';'+"$RepoRoot\.lake\build-434\chen-bjs-study;$RepoRoot\.lake\build-434\chen-effective"
$lake=Join-Path $env:USERPROFILE '.elan\toolchains\leanprover--lean4---v4.34.1\bin\lake.exe'
$modules=@('ChenRouteBudget','ChenRouteSource','ChenRouteProduction','ChenRouteBJS','ChenRouteMixing','AuditChenRoutes')
$index=[Array]::IndexOf($modules,$FromModule)
if($index-lt0){throw "Unknown module: $FromModule"}
New-Item -ItemType Directory -Force -Path $build|Out-Null
Push-Location -LiteralPath $RepoRoot
try {
 foreach($name in $modules[$index..($modules.Length-1)]){
  & $lake env lean -DwarningAsError=true -R $PSScriptRoot -o "$build\$name.olean" "$PSScriptRoot\$name.lean" *> "$build\$name.log"
  if($LASTEXITCODE-ne0){Get-Content "$build\$name.log"; throw "Lean failed: $name"}
  if(Select-String -LiteralPath "$build\$name.log" -Pattern 'sorryAx' -Quiet){throw "Placeholder in $name"}
  Write-Output "Verified $name"
 }
 Get-Content "$build\AuditChenRoutes.log"
} finally {
 $env:LEAN_PATH=$previousLeanPath
 Pop-Location
}
