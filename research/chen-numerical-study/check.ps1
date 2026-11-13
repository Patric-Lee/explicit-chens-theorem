param([string]$RepoRoot='', [string]$FromModule='BJSH30ConditionalProducts')
$ErrorActionPreference='Stop'
& (Join-Path $PSScriptRoot 'source-audit.ps1')
if(-not $RepoRoot){$RepoRoot=(Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..')).Path}
$build=Join-Path $RepoRoot '.lake\build-434\chen-numerical-study'
$previousLeanPath=$env:LEAN_PATH
$env:LEAN_PATH=$build+';'+(Join-Path $RepoRoot '.lake\build-434\chen-bjs-study')+';'+(Join-Path $RepoRoot '.lake\build-434\chen-effective')+';'+(Join-Path $RepoRoot '.lake\build-434\chen-dusart')
$lake=Join-Path $env:USERPROFILE '.elan\toolchains\leanprover--lean4---v4.34.1\bin\lake.exe'
$modules=@('BJSH30ConditionalProducts','BJSH30ConditionalGeometry','BJSH30ConditionalGoldbach',
 'BJSH30ConditionalMediumPrimeGrid','BJSH30ConditionalMediumPrimeSum','BJSH30ConditionalMediumPrimeShift',
 'BJSH30ConditionalMediumReciprocal','BJSH30ConditionalBase','BJSH30ConditionalMedium',
 'BJSH30ConditionalAggregate','BJSH30ConditionalChen','AuditBJSH30Conditional')
$index=[Array]::IndexOf($modules,$FromModule)
if($index -lt 0){throw "Unknown module: $FromModule"}
New-Item -ItemType Directory -Force -Path $build | Out-Null
Push-Location -LiteralPath $RepoRoot
try {
 foreach($name in $modules[$index..($modules.Length-1)]){
  & $lake env lean -DwarningAsError=true -R $PSScriptRoot -o "$build\$name.olean" "$PSScriptRoot\$name.lean" *> "$build\$name.log"
  if($LASTEXITCODE -ne 0){Get-Content "$build\$name.log"; throw "Lean failed: $name"}
  if(Select-String -LiteralPath "$build\$name.log" -Pattern 'sorryAx' -Quiet){throw "Placeholder in $name"}
  Write-Output "Verified $name"
 }
 Get-Content "$build\AuditBJSH30Conditional.log"
} finally {Pop-Location; $env:LEAN_PATH=$previousLeanPath}
