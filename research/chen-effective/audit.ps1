param([switch]$Rebuild)
$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..')).Path
$artifactDir = Join-Path $repoRoot '.lake\build\chen-effective'

# Full rebuild is optional; by default rebuild the compatibility bridge and audit.
if ($Rebuild) { & (Join-Path $PSScriptRoot 'check.ps1') }
else { & (Join-Path $PSScriptRoot 'check.ps1') -FromModule NumericalChenCompatibility }

# Strip nested Lean block comments, line comments and string literals before
# scanning. Comment-only mentions of a forbidden token are not proof holes.
function Remove-LeanCommentsAndStrings([string]$text) {
    $out = [Text.StringBuilder]::new()
    $depth = 0
    $lineComment = $false
    $inString = $false
    for ($i = 0; $i -lt $text.Length; $i++) {
        $c = $text[$i]
        $next = if ($i + 1 -lt $text.Length) { $text[$i + 1] } else { [char]0 }
        if ($lineComment) {
            if ($c -eq "`n") { $lineComment = $false; [void]$out.Append($c) }
            continue
        }
        if ($depth -gt 0) {
            if ($c -eq '/' -and $next -eq '-') { $depth++; $i++ }
            elseif ($c -eq '-' -and $next -eq '/') { $depth--; $i++ }
            elseif ($c -eq "`n") { [void]$out.Append($c) }
            continue
        }
        if ($inString) {
            if ($c -eq '\') { $i++ }
            elseif ($c -eq '"') { $inString = $false }
            elseif ($c -eq "`n") { [void]$out.Append($c) }
            continue
        }
        if ($c -eq '-' -and $next -eq '-') { $lineComment = $true; $i++; [void]$out.Append(' ') }
        elseif ($c -eq '/' -and $next -eq '-') { $depth = 1; $i++; [void]$out.Append(' ') }
        elseif ($c -eq '"') { $inString = $true; [void]$out.Append(' ') }
        else { [void]$out.Append($c) }
    }
    if ($depth -ne 0 -or $inString) { throw 'Unterminated Lean comment or string in source audit' }
    return $out.ToString()
}

# Include every research source, including unused declarations, and all locally
# imported project sources. External library proof dependencies are covered by
# the exact transitive Lean axiom whitelist in audit/AuditChen.lean.
$queue = [Collections.Generic.Queue[string]]::new()
$seenFiles = [Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
Get-ChildItem -LiteralPath $PSScriptRoot -Filter '*.lean' | ForEach-Object { $queue.Enqueue($_.FullName) }
$bad = '\b(sorry|admit|sorryAx|native_decide|axiom|unsafe|implemented_by|extern|ofReduceBool|trustCompiler|skipKernelTC|trustLevel)\b'
$axiomCount = 0
while ($queue.Count -gt 0) {
    $path = $queue.Dequeue()
    if (-not $seenFiles.Add($path)) { continue }
    $text = [IO.File]::ReadAllText($path)
    if ($text -match $bad) {
        $code = Remove-LeanCommentsAndStrings $text
        foreach ($match in [regex]::Matches($code, $bad)) {
            if ($match.Value -ne 'axiom') { throw "Forbidden proof token '$($match.Value)' in $path" }
            $tail = $code.Substring($match.Index)
            if ($path -ne (Join-Path $PSScriptRoot 'ExplicitSiegel.lean') -or
                $tail -notmatch '^axiom\s+dirichlet_seven_eighths\b') {
                throw "Unexpected axiom declaration in $path"
            }
            $axiomCount++
        }
    }
    foreach ($match in [regex]::Matches($text, '(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_.]+)')) {
        $module = $match.Groups[1].Value
        if ($module -match '^(OAI|ComparatorChallenges|OpenAI)(\.|$)' -or
            $module -match 'LiLiuGoldbach|Goldbach\.(OnePlusOneNine|All)') {
            throw "Forbidden import in source audit: $module"
        }
        $relative = $module.Replace('.', '\') + '.lean'
        $local = Join-Path $PSScriptRoot $relative
        $project = Join-Path $repoRoot $relative
        if (Test-Path -LiteralPath $local) { $queue.Enqueue($local) }
        elseif (Test-Path -LiteralPath $project) { $queue.Enqueue($project) }
    }
}
if ($axiomCount -ne 1) { throw "Expected exactly one local/project axiom, found $axiomCount" }
Write-Output "Source audit passed: $($seenFiles.Count) research/project files; no proof placeholders, native_decide, unsafe declarations, compiler bypasses, or extra axioms."

$lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
$lakePath = if ($lakeCommand) { $lakeCommand.Source } else { Join-Path $env:USERPROFILE '.elan\bin\lake.exe' }
$previousLeanPath = $env:LEAN_PATH
$env:LEAN_PATH = if ($previousLeanPath) { $artifactDir + ';' + $previousLeanPath } else { $artifactDir }
Push-Location -LiteralPath $repoRoot
try {
    foreach ($fixtureName in @('AuditElementaryMertens','AuditChen')) {
        $fixture = Join-Path $PSScriptRoot "audit\$fixtureName.lean"
        $logName = if ($fixtureName -eq 'AuditChen') { 'FinalAudit.log' } else { 'ElementaryMertensAudit.log' }
        & $lakePath env lean -DwarningAsError=true -R $PSScriptRoot $fixture 2>&1 |
            Tee-Object -FilePath (Join-Path $artifactDir $logName)
        if ($LASTEXITCODE -ne 0) { throw "Lean audit failed for $fixtureName (exit $LASTEXITCODE)" }
    }
} finally {
    $env:LEAN_PATH = $previousLeanPath
    Pop-Location
}
Write-Output 'Final audit passed: original statement types, exact axiom whitelist, and no use of old implicit proofs.'
