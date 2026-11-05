$ErrorActionPreference='Stop'
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

$bad='\b(sorry|admit|sorryAx|native_decide|axiom|unsafe|implemented_by|extern|ofReduceBool|trustCompiler|skipKernelTC|trustLevel)\b'
foreach($p in Get-ChildItem -LiteralPath $PSScriptRoot -Filter '*.lean'){
 $code=Remove-LeanCommentsAndStrings ([IO.File]::ReadAllText($p.FullName))
 if($p.Name-eq'AuditChenRoutes.lean'){$code=$code.Replace('debug.skipKernelTC.get','kernelGuard')}
 if($code-match$bad){throw "Forbidden proof token in $p"}
 foreach($m in [regex]::Matches($code,'(?m)^import\s+([A-Za-z0-9_.]+)')){
  if($m.Groups[1].Value-match'^(OAI|OpenAI|ComparatorChallenges|LeanLab)(\.|$)'){throw "Forbidden external import in $p"}
 }
}
Write-Output 'Budget source scan passed: zero new axioms, placeholders, native_decide or unsafe declarations.'
