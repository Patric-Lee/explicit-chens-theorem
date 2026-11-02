$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..')).Path
$artifactDir = Join-Path $repoRoot '.lake\build\chen-effective'
New-Item -ItemType Directory -Path $artifactDir -Force | Out-Null
$lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
$lakePath = if ($lakeCommand) { $lakeCommand.Source } else {
    Join-Path $env:USERPROFILE '.elan\bin\lake.exe'
}

Push-Location -LiteralPath $repoRoot
try {
    foreach ($name in @('ExplicitSiegel', 'NumericalThresholds', 'ExplicitLowConductor')) {
        $source = Join-Path $PSScriptRoot "$name.lean"
        $output = Join-Path $artifactDir "$name.olean"
        $log = Join-Path $artifactDir "$name.log"
        & $lakePath env lean -DwarningAsError=true -o $output $source 2>&1 |
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
    Write-Output 'All three research modules compiled with warnings treated as errors.'
    Write-Output 'Exactly one local axiom; zero OpenAI imports; zero Li-Liu theorem imports.'
    Write-Output 'Existing shared LiLiu-named helpers in the project-side import closure:'
    $seen | Where-Object { $_ -match 'LiLiu' } | Sort-Object
    Write-Output "Artifacts and axiom reports: $artifactDir"
} finally {
    Pop-Location
}
