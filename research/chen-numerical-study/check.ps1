param([string]$RepoRoot='', [string]$FromModule='BJSH30ConditionalProducts')
$ErrorActionPreference='Stop'
& (Join-Path $PSScriptRoot 'source-audit.ps1')
if(-not $RepoRoot){$RepoRoot=(Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..')).Path}
$modules=@('BJSH30ConditionalProducts','BJSH30ConditionalGeometry','BJSH30ConditionalGoldbach',
 'BJSH30ConditionalMediumPrimeGrid','BJSH30ConditionalMediumPrimeSum','BJSH30ConditionalMediumPrimeShift',
 'BJSH30ConditionalMediumReciprocal','BJSH30ConditionalBase','BJSH30ConditionalMedium',
 'BJSH30ConditionalAggregate','BJSH30ConditionalChen','AuditBJSH30Conditional')
if($FromModule -notin $modules){throw "Unknown module: $FromModule"}
$oldJobs=$env:CHEN_BUILD_JOBS
$oldMemory=$env:CHEN_LEAN_MEMORY_MB
if(-not $env:CHEN_BUILD_JOBS){$env:CHEN_BUILD_JOBS='1'}
if(-not $env:CHEN_LEAN_MEMORY_MB){$env:CHEN_LEAN_MEMORY_MB='8192'}
Push-Location -LiteralPath $RepoRoot
try {
 & node (Join-Path $RepoRoot 'OpenAI\tools\build-source.mjs') $FromModule AuditBJSH30Conditional
 if($LASTEXITCODE -ne 0){throw 'Chen proof or final transitive audit failed'}
 Get-Content -LiteralPath (Join-Path $RepoRoot '.lake\build-434\source-build-logs\AuditBJSH30Conditional.log')
} finally {
 Pop-Location
 $env:CHEN_BUILD_JOBS=$oldJobs
 $env:CHEN_LEAN_MEMORY_MB=$oldMemory
}
