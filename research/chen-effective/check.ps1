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
    $modules = @(
        'ExplicitSiegel',
        'NumericalThresholds',
        'ExplicitLowConductor',
        'ExplicitLogBounds',
        'ExplicitBVPayload',
        'NumericalSmoothing',
        'NumericalLogDerivative',
        'NumericalElementaryMertens',
        'NumericalPanLargeSieve',
        'NumericalCorrectionProfile',
        'ExplicitBVHigh',
        'ExplicitChenTriple',
        'NumericalMellin',
        'NumericalDirichletStrip',
        'NumericalPrincipalElementary',
        'NumericalSuzukiGate',
        'NumericalMertensGlobal',
        'NumericalRealLogBounds',
        'NumericalPanShort',
        'ExplicitBVAssembly',
        'NumericalZetaStrip',
        'NumericalRightTail',
        'NumericalMainTerm',
        'NumericalSuzukiAbsorption',
        'NumericalGoldbachInterval',
        'NumericalC1Scalar',
        'NumericalPanLong',
        'ExplicitChenLower',
        'NumericalPrimitiveContour',
        'NumericalPrincipalContour',
        'NumericalSuzukiHat',
        'NumericalLocalProduct',
        'NumericalProductExponential',
        'NumericalPrimitivePower',
        'NumericalContourEdges',
        'NumericalResidueAssembly',
        'NumericalLowerFactor',
        'NumericalSuzukiNormalization',
        'NumericalProductSplit',
        'NumericalSqrtAbsorption',
        'NumericalLowConductor',
        'NumericalPrincipalSmoothed',
        'NumericalSuzukiLowStripScalar',
        'NumericalSuzukiCaseOne',
        'NumericalHatCompact',
        'NumericalUpperFactor',
        'NumericalRefinedLocalProduct',
        'NumericalPrincipalPower',
        'SuzukiCoefficientAssembly',
        'NumericalHatLower',
        'NumericalFiniteHat',
        'NumericalHatComparison',
        'NumericalPrincipalPNT',
        'NumericalQuotientEnvelope',
        'NumericalC1Order',
        'NumericalRelativeHat',
        'NumericalReverseEnvelope',
        'NumericalBV',
        'NumericalMertens',
        'NumericalJointEnvelope',
        'NumericalReverseRatio',
        'NumericalWeightedMass',
        'NumericalMertensProduct',
        'NumericalLogarithmicScalar',
        'NumericalPanQuotient',
        'NumericalHatBarrier',
        'NumericalC1Endpoint',
        'NumericalForwardEnvelope',
        'NumericalWeightedEnvelope',
        'NumericalGoldbachProduct',
        'NumericalSmallQuotient',
        'NumericalCaseABounded',
        'NumericalPanPrincipalPNT',
        'NumericalPanPrimePrefix',
        'NumericalPanCell',
        'NumericalSharpHatProfile',
        'NumericalCompactDerivative',
        'NumericalWeightedDistribution',
        'NumericalSingularNormalization',
        'SuzukiFixedKAssembly',
        'NumericalPanBudget',
        'NumericalPanAggregate',
        'NumericalPolynomialTail',
        'NumericalCaseBCutoff',
        'NumericalVaryingCorrections',
        'NumericalSourceMass',
        'NumericalPanPrincipal',
        'NumericalPanLow',
        'NumericalPolynomialKernel',
        'NumericalSourceGeometry',
        'NumericalUpperDistribution',
        'NumericalPanLedger',
        'NumericalUniversalTail',
        'NumericalPolynomialTransport',
        'NumericalSourceLogDomination',
        'NumericalSigmaZeroCutoff',
        'NumericalLowerEndpoint',
        'NumericalPanUnweighted',
        'NumericalPolynomialMiddle',
        'NumericalSourceRatio',
        'NumericalPanEnvelope',
        'NumericalStrongLogGate',
        'NumericalPolynomialCompact',
        'NumericalDerivativeCertificate',
        'NumericalPanWeighted',
        'NumericalPolynomialGate',
        'NumericalPolynomialSmall',
        'NumericalClaim146Monotone',
        'NumericalPanSource',
        'NumericalHatTail',
        'NumericalPanNormalization',
        'NumericalPerturbation',
        'NumericalPanR1',
        'NumericalSelbergDivisorGeometry',
        'NumericalWeightedHead',
        'NumericalSelbergRemainder',
        'NumericalSelbergDivisorProduct',
        'NumericalMovingTail',
        'NumericalSquareConstants',
        'NumericalSelbergDivisorLog',
        'NumericalClaim146Tail',
        'NumericalSquareAssembly',
        'NumericalClaim146',
        'NumericalSelbergEulerMajorant',
        'NumericalSigmaTwelveContraction',
        'NumericalErrorTransport',
        'NumericalSelbergRoot',
        'NumericalCaseIICoreDecay',
        'NumericalC1Geometry',
        'NumericalSelbergMoments',
        'NumericalCaseIIGap',
        'NumericalC1Tools',
        'NumericalCaseIITransport',
        'NumericalSelbergDenominator',
        'NumericalCaseIStrict',
        'NumericalCaseIEven',
        'NumericalCaseII',
        'NumericalSelbergDenominatorClosed',
        'NumericalSuzukiC1',
        'NumericalPrimePairThreshold',
        'NumericalPolynomialMixedCore',
        'NumericalPrimePairInterval',
        'NumericalGenuineLiPointwise',
        'NumericalMixedObjects',
        'NumericalPrimePairGrid',
        'NumericalSourceUpperMass',
        'NumericalMediumPrimeGrid',
        'NumericalMixedGap',
        'NumericalGenuineLiSum',
        'NumericalMediumPrimeSum',
        'NumericalMixedFinish',
        'NumericalSquareThresholdCap',
        'NumericalMediumPrimeShift',
        'NumericalMixedCaseI',
        'NumericalMixedEven',
        'NumericalMixedCaseIIScalar',
        'NumericalNSquare',
        'NumericalMixedCaseIITransfer',
        'NumericalMixedCaseII',
        'NumericalMixedBase',
        'NumericalMixedInduction',
        'NumericalMixedWindow',
        'NumericalSeparateCoefficients',
        'NumericalBaseDensity',
        'NumericalMixedUpper',
        'NumericalBaseCandidates',
        'NumericalMediumUpperDensity',
        'NumericalMediumAggregate',
        'NumericalChenCutoff',
        'NumericalTowerTools',
        'NumericalTowerSource',
        'NumericalTowerHeads',
        'NumericalTowerC1',
        'NumericalC1SingleExponential',
        'NumericalSmallQuotientChen',
        'NumericalMixedCoefficientCap',
        'NumericalPolynomialChen',
        'NumericalTowerCoefficient',
        'NumericalSuzukiSharpBudget',
        'NumericalTowerFinite',
        'NumericalTowerThresholds',
        'NumericalDoubleExponential',
        'NumericalExplicitTower',
        'NumericalChenCompatibility',
        'NumericalMertensPower',
        'NumericalEulerProductPower',
        'NumericalSieveErrorRecurrence',
        'NumericalSieveKernel',
        'NumericalSieveLayerDecay',
        'NumericalSieveRelativeAbel',
        'NumericalSieveKernelRecurrence',
        'NumericalSieveSourceDomination',
        'NumericalSieveSourceStep',
        'NumericalSieveSourceGeometry',
        'NumericalSieveSourceAnalytic',
        'NumericalSieveSourceInduction',
        'NumericalSieveSourceParity',
        'NumericalPresievedSourceLayers')
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
