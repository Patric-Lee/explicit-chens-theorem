param([string]$FromModule = '')
$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..')).Path
$artifactDir = Join-Path $repoRoot '.lake\build\chen-effective'
New-Item -ItemType Directory -Path $artifactDir -Force | Out-Null
$lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
$lakePath = if ($lakeCommand) { $lakeCommand.Source } else {
    Join-Path $env:USERPROFILE '.elan\bin\lake.exe'
}

$previousLeanPath = $env:LEAN_PATH
$env:LEAN_PATH = if ($previousLeanPath) { $artifactDir + ';' + $previousLeanPath } else { $artifactDir }
Push-Location -LiteralPath $repoRoot
try {
    $modules = @('ExplicitSiegel', 'NumericalThresholds', 'ExplicitLowConductor',
        'ExplicitLogBounds', 'ExplicitBVHigh', 'ExplicitBVPayload', 'ExplicitBVAssembly',
        'ExplicitChenTriple', 'ExplicitChenLower',
        'NumericalSmoothing', 'NumericalMellin', 'NumericalLogDerivative',
        'NumericalDirichletStrip', 'NumericalZetaStrip', 'NumericalRightTail',
        'NumericalPrimitiveContour', 'NumericalPrimitivePower', 'NumericalLowConductor',
        'NumericalPrincipalContour', 'NumericalContourEdges')
    if ($FromModule) {
        $startIndex = [Array]::IndexOf($modules, $FromModule)
        if ($startIndex -lt 0) { throw "Unknown research module: $FromModule" }
        $modules = $modules[$startIndex..($modules.Length - 1)]
    }
    foreach ($name in $modules) {
        $source = Join-Path $PSScriptRoot "$name.lean"
        $output = Join-Path $artifactDir "$name.olean"
        $log = Join-Path $artifactDir "$name.log"
        Set-Content -LiteralPath $log -Value ''
        & $lakePath env lean -DwarningAsError=true -R $PSScriptRoot -o $output $source 2>&1 |
            Tee-Object -FilePath $log
        if ($LASTEXITCODE -ne 0) { throw "Lean failed for $name (exit $LASTEXITCODE)" }
        if (Select-String -LiteralPath $log -Pattern 'sorryAx' -Quiet) {
            throw "Unexpected proof placeholder in $name"
        }
    }

    $seen = [System.Collections.Generic.HashSet[string]]::new()
    $queue = [System.Collections.Generic.Queue[string]]::new()
    Get-ChildItem -LiteralPath $PSScriptRoot -Filter '*.lean' | ForEach-Object {
        $queue.Enqueue($_.FullName)
    }
    while ($queue.Count -gt 0) {
        foreach ($line in [System.IO.File]::ReadLines($queue.Dequeue())) {
            if ($line -match '^\s*(?:public\s+|private\s+)?import\s+([A-Za-z0-9_.]+)') {
                $module = $Matches[1]
                if ($seen.Add($module)) {
                    $path = Join-Path $repoRoot ($module.Replace('.', '\') + '.lean')
                    if (Test-Path -LiteralPath $path) { $queue.Enqueue($path) }
                }
            }
        }
    }
    $forbidden = @($seen | Where-Object {
        $_ -match '^(OAI|ComparatorChallenges|OpenAI)(\.|$)' -or
        $_ -match 'LiLiuGoldbach|Goldbach\.(OnePlusOneNine|All)'
    })
    if ($forbidden.Count -gt 0) { throw "Unexpected imports: $forbidden" }
    $axioms = @(Get-ChildItem -LiteralPath $PSScriptRoot -Filter '*.lean' |
        Select-String -Pattern '^\s*axiom\s+')
    if ($axioms.Count -ne 1 -or $axioms[0].Line -notmatch 'dirichlet_seven_eighths') {
        throw 'Expected exactly the one declared Dirichlet axiom'
    }
    Write-Output "All $($modules.Count) research modules compiled with warnings treated as errors."
    Write-Output 'Exactly one local axiom; zero OpenAI imports; zero Li-Liu theorem imports.'
    Write-Output 'Existing shared LiLiu-named helpers in the project-side import closure:'
    $seen | Where-Object { $_ -match 'LiLiu' } | Sort-Object
    Write-Output "Artifacts and axiom reports: $artifactDir"
} finally {
    $env:LEAN_PATH = $previousLeanPath
    Pop-Location
}
