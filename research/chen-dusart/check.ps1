param([string]$RepoRoot='', [string]$FromModule='')
$ErrorActionPreference='Stop'
& (Join-Path $PSScriptRoot 'source-audit.ps1')
if(-not $RepoRoot){$RepoRoot=(Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..')).Path}
$build=Join-Path $RepoRoot '.lake\build\chen-dusart'
$modules=@(Get-Content -Raw (Join-Path $PSScriptRoot 'modules.json')|ConvertFrom-Json)
$index=0
if($FromModule){
 $index=[Array]::IndexOf($modules,$FromModule)
 if($index-lt0){throw "Unknown module: $FromModule"}
}
$previousLeanPath=$env:LEAN_PATH
$env:LEAN_PATH=$build+';'+(Join-Path $RepoRoot '.lake\build\chen-bjs-study')+';'+(Join-Path $RepoRoot '.lake\build\chen-effective')
$lake=Join-Path $env:USERPROFILE '.elan\toolchains\leanprover--lean4---v4.33.0-rc1\bin\lake.exe'
Push-Location -LiteralPath $RepoRoot
try {
 foreach($name in $modules[$index..($modules.Length-1)]){
  $rel=$name.Replace('.','\')
  $out=Join-Path $build ($rel+'.olean')
  New-Item -ItemType Directory -Force -Path ([IO.Path]::GetDirectoryName($out))|Out-Null
  $log=Join-Path $build ($name.Replace('.','_')+'.log')
  & $lake env lean -DwarningAsError=true -R $PSScriptRoot -o $out (Join-Path $PSScriptRoot ($rel+'.lean')) *> $log
  if($LASTEXITCODE-ne0){Get-Content -LiteralPath $log;throw "Lean failed: $name"}
  if(Select-String -LiteralPath $log -Pattern 'sorryAx' -Quiet){throw "Placeholder in $name"}
  Write-Output "Verified module $name"
 }
 Get-Content (Join-Path $build 'AuditDusart.log')
} finally {
 $env:LEAN_PATH=$previousLeanPath
 Pop-Location
}
