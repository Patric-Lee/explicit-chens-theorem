param([int]$Layers=12)
$ErrorActionPreference='Stop'
$mesh=32
$precision=[Numerics.BigInteger]::Pow(10,12)
$rows=[Collections.Generic.List[object]]::new()
$tails=[Collections.Generic.List[object]]::new()
$profiles=[Collections.Generic.List[int]]::new()
$first=[Numerics.BigInteger[]]::new(3*$mesh+1)
for($i=1;$i-lt$first.Length;$i++){$first[$i]=[Numerics.BigInteger]::Divide((3*$mesh-$i)*$precision+$i-1,$i)}
$rows.Add($first);$tails.Add([Numerics.BigInteger[]]::new(0));$profiles.Add(1000000)
for($n=2;$n-le$Layers;$n++){
 $prev=$rows[$n-2]
 $end=($n+2)*$mesh
 $start=(2+$n%2)*$mesh
 $tail=[Numerics.BigInteger[]]::new($end+1)
 for($j=$end-1;$j-ge$start;$j--){$tail[$j]=$tail[$j+1]+$prev[$j-$mesh]}
 $row=[Numerics.BigInteger[]]::new($end+1)
 for($i=1;$i-le$end;$i++){$row[$i]=[Numerics.BigInteger]::Divide($tail[[Math]::Max($i,$start)]+$i-1,$i)}
 $a=0.0
 for($i=(2-$n%2)*$mesh;$i-lt$end;$i++){
  $x=($i+1)/[double]$mesh
  $k=[Math]::Max(0,$i+1-2*$mesh)
  $v=([double]$row[$i]/[double]$precision)*[Math]::Max([double]3,$x)*[Math]::Pow(65.0/63,$k)/6
  $a=[Math]::Max($a,$v)
 }
 $p=[int][Math]::Ceiling($a*1e6)+1
 $rows.Add($row);$tails.Add($tail);$profiles.Add($p)
 Write-Output "layer $n profile $p/1000000"
}
$lines=[Collections.Generic.List[string]]::new()
$lines.Add('import Mathlib.Tactic')
$lines.Add('')
$lines.Add('/-! Exact integer data for the early continuous-layer upper Riemann sums.')
$lines.Add('Generated candidates are checked in Lean; the generator is not trusted. -/')
$lines.Add('namespace ChenEffective')
$lines.Add('def bjsGridMesh : ℕ := 32')
$lines.Add('def bjsGridPrecision : ℕ := 1000000000000')
for($n=1;$n-le$Layers;$n++){
 $lines.Add("def bjsGridRow$n : Array ℕ := #["+($rows[$n-1]-join',')+']')
 if($n-ge2){$lines.Add("def bjsGridTail$n : Array ℕ := #["+($tails[$n-1]-join',')+']')}
}
$lines.Add('def bjsGridRows : Array (Array ℕ) := #['+((1..$Layers|ForEach-Object {"bjsGridRow$_"})-join',')+']')
$lines.Add('def bjsGridTails : Array (Array ℕ) := #[#[],'+((2..$Layers|ForEach-Object {"bjsGridTail$_"})-join',')+']')
$lines.Add('def bjsGridProfileNumerators : Array ℕ := #['+($profiles-join',')+']')
$lines.Add('end ChenEffective')
[IO.File]::WriteAllText((Join-Path $PSScriptRoot 'BJSLayerTableData.lean'),($lines-join"`n")+"`n")
foreach($seed in @(10,12,14,16)|Where-Object {$_-le$Layers}){
 $pa=1.0;$tau=3.0;$odd=3.0;$even=0.0
 for($n=2;$n-le600;$n++){
  $a=if($n-le$seed){$profiles[$n-1]/1e6}else{$pa*.964}
  $r=if($n%2){.9295}else{.9655}
  $tau=$r*$tau+7.34*$pa+4.01*$a
  if($n%2){$odd+=$tau}else{$even+=$tau}
  $pa=$a
 }
 Write-Output "seed $seed exploratory parity sums $odd $even"
}
