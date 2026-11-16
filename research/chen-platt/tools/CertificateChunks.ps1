# Finds bundled Node and Git without permanent PATH changes.
$ErrorActionPreference = 'Stop'
$certNodeCommand = Get-Command node.exe -CommandType Application -ErrorAction SilentlyContinue | Select-Object -First 1
$certNodeExecutable = if ($certNodeCommand) { $certNodeCommand.Source } else { $null }
if (-not $certNodeExecutable) {
    $certCandidates = @()
    if (Get-Command Get-AppxPackage -ErrorAction SilentlyContinue) {
        $certCandidates += @(Get-AppxPackage -Name 'OpenAI.CodexPrimaryRuntime*' -ErrorAction SilentlyContinue |
            Sort-Object Version -Descending | ForEach-Object {
                Join-Path $_.InstallLocation 'dependencies\node\bin\node.exe'
            })
    }
    $certCandidates += 'C:\Program Files\WindowsApps\OpenAI.CodexPrimaryRuntime.v26-1111-570-0_26.1111.570.0_x64__3k8sg7r9htsxt\dependencies\node\bin\node.exe'
    $certNodeExecutable = $certCandidates | Where-Object { Test-Path -LiteralPath $_ } | Select-Object -First 1
}
if (-not $certNodeExecutable) { throw 'Node.js was not found in PATH or the installed Codex runtime.' }
$certGitCommand = Get-Command git.exe -CommandType Application -ErrorAction SilentlyContinue | Select-Object -First 1
$certGitExecutable = if ($certGitCommand) { $certGitCommand.Source } else { $null }
if (-not $certGitExecutable) {
    $certDependencies = Split-Path -Parent (Split-Path -Parent (Split-Path -Parent $certNodeExecutable))
    $certGitCandidates = @(
        (Join-Path $certDependencies 'native\git\cmd\git.exe'),
        (Join-Path (Split-Path -Parent (Split-Path -Parent (Split-Path -Parent 'C:\Program Files\WindowsApps\OpenAI.CodexPrimaryRuntime.v26-1111-570-0_26.1111.570.0_x64__3k8sg7r9htsxt\dependencies\node\bin\node.exe'))) 'native\git\cmd\git.exe'),
        (Join-Path $env:ProgramFiles 'Git\cmd\git.exe')
    )
    $certGitExecutable = $certGitCandidates | Where-Object { Test-Path -LiteralPath $_ } | Select-Object -First 1
}
if (-not $certGitExecutable) { throw 'Git was not found in PATH or the installed Codex runtime. No dependency directories were changed.' }
$certOriginalPath = $env:Path
try {
    $env:Path = (Split-Path -Parent $certNodeExecutable) + ';' + (Split-Path -Parent $certGitExecutable) + ';' + $certOriginalPath
    & $certNodeExecutable (Join-Path $PSScriptRoot 'CertificateChunks.mjs') @args
    $certExitCode = $LASTEXITCODE
} finally {
    $env:Path = $certOriginalPath
}
exit $certExitCode
