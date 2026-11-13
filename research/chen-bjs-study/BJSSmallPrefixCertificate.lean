import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.FinCases
import BJSFiniteLogBounds

/-! Candidate endpoint bounds generated from rounded approximations.
The theorem below checks every candidate by exact rational arithmetic in
the Lean kernel; the generator and floating-point operations are untrusted.
-/
namespace ChenEffective
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bjsSmallLogRows : Array (ℕ × ℚ × ℕ × ℚ) := #[
  (0, 0, 0, 0),
  (0, 0, 0, 0),
  (1, 10988/10000, 0, 944/10000),
  (2, 13864/10000, 0, 3269/10000),
  (2, 16096/10000, 0, 4761/10000),
  (2, 17919/10000, 0, 5834/10000),
  (2, 19461/10000, 0, 6660/10000),
  (3, 20796/10000, 1, 7323/10000),
  (3, 21974/10000, 1, 7874/10000),
  (3, 23027/10000, 1, 8342/10000),
  (3, 23980/10000, 1, 8748/10000),
  (3, 24851/10000, 1, 9105/10000),
  (3, 25651/10000, 1, 9421/10000),
  (3, 26392/10000, 1, 9706/10000),
  (3, 27082/10000, 1, 9964/10000),
  (4, 27727/10000, 1, 10200/10000),
  (4, 28334/10000, 1, 10416/10000),
  (4, 28905/10000, 1, 10616/10000),
  (4, 29446/10000, 1, 10801/10000),
  (4, 29959/10000, 1, 10974/10000),
  (4, 30447/10000, 1, 11136/10000),
  (4, 30912/10000, 1, 11287/10000),
  (4, 31356/10000, 1, 11430/10000),
  (4, 31782/10000, 1, 11565/10000),
  (4, 32190/10000, 1, 11692/10000),
  (4, 32582/10000, 1, 11813/10000),
  (4, 32960/10000, 1, 11929/10000),
  (4, 33324/10000, 1, 12038/10000),
  (4, 33674/10000, 1, 12143/10000),
  (4, 34013/10000, 1, 12243/10000),
  (4, 34341/10000, 1, 12339/10000),
  (5, 34659/10000, 1, 12431/10000),
  (5, 34967/10000, 1, 12520/10000),
  (5, 35265/10000, 1, 12605/10000),
  (5, 35555/10000, 1, 12686/10000),
  (5, 35837/10000, 1, 12765/10000),
  (5, 36111/10000, 1, 12842/10000),
  (5, 36377/10000, 1, 12915/10000),
  (5, 36637/10000, 1, 12986/10000),
  (5, 36890/10000, 1, 13055/10000),
  (5, 37137/10000, 1, 13122/10000),
  (5, 37378/10000, 1, 13186/10000),
  (5, 37614/10000, 1, 13249/10000),
  (5, 37843/10000, 1, 13310/10000),
  (5, 38068/10000, 1, 13369/10000),
  (5, 38288/10000, 1, 13427/10000),
  (5, 38503/10000, 1, 13483/10000),
  (5, 38714/10000, 1, 13538/10000),
  (5, 38920/10000, 1, 13591/10000),
  (5, 39122/10000, 1, 13642/10000),
  (5, 39320/10000, 1, 13693/10000),
  (5, 39514/10000, 1, 13742/10000),
  (5, 39704/10000, 1, 13790/10000),
  (5, 39891/10000, 1, 13837/10000),
  (5, 40075/10000, 2, 13883/10000),
  (5, 40255/10000, 2, 13928/10000),
  (5, 40432/10000, 2, 13972/10000),
  (5, 40606/10000, 2, 14015/10000),
  (5, 40777/10000, 2, 14057/10000),
  (5, 40945/10000, 2, 14098/10000),
  (5, 41110/10000, 2, 14138/10000),
  (5, 41273/10000, 2, 14178/10000),
  (5, 41433/10000, 2, 14216/10000),
  (6, 41590/10000, 2, 14254/10000),
  (6, 41745/10000, 2, 14291/10000),
  (6, 41898/10000, 2, 14328/10000),
  (6, 42048/10000, 2, 14364/10000),
  (6, 42197/10000, 2, 14399/10000),
  (6, 42343/10000, 2, 14434/10000),
  (6, 42486/10000, 2, 14467/10000),
  (6, 42628/10000, 2, 14501/10000),
  (6, 42768/10000, 2, 14534/10000),
  (6, 42906/10000, 2, 14566/10000),
  (6, 43042/10000, 2, 14597/10000),
  (6, 43176/10000, 2, 14628/10000),
  (6, 43309/10000, 2, 14659/10000),
  (6, 43440/10000, 2, 14689/10000),
  (6, 43569/10000, 2, 14719/10000),
  (6, 43696/10000, 2, 14748/10000),
  (6, 43822/10000, 2, 14777/10000),
  (6, 43946/10000, 2, 14805/10000),
  (6, 44069/10000, 2, 14833/10000),
  (6, 44190/10000, 2, 14861/10000),
  (6, 44310/10000, 2, 14888/10000),
  (6, 44428/10000, 2, 14914/10000),
  (6, 44545/10000, 2, 14941/10000),
  (6, 44661/10000, 2, 14967/10000),
  (6, 44775/10000, 2, 14992/10000),
  (6, 44888/10000, 2, 15017/10000),
  (6, 45000/10000, 2, 15042/10000),
  (6, 45110/10000, 2, 15067/10000),
  (6, 45219/10000, 2, 15091/10000),
  (6, 45327/10000, 2, 15115/10000),
  (6, 45434/10000, 2, 15138/10000),
  (6, 45540/10000, 2, 15162/10000),
  (6, 45645/10000, 2, 15185/10000),
  (6, 45749/10000, 2, 15207/10000),
  (6, 45851/10000, 2, 15230/10000),
  (6, 45953/10000, 2, 15252/10000),
  (6, 46053/10000, 2, 15274/10000),
  (6, 46153/10000, 2, 15295/10000),
  (6, 46251/10000, 2, 15316/10000),
  (6, 46349/10000, 2, 15338/10000),
  (6, 46445/10000, 2, 15358/10000),
  (6, 46541/10000, 2, 15379/10000),
  (6, 46636/10000, 2, 15399/10000),
  (6, 46730/10000, 2, 15420/10000),
  (6, 46823/10000, 2, 15439/10000),
  (6, 46915/10000, 2, 15459/10000),
  (6, 47006/10000, 2, 15478/10000),
  (6, 47097/10000, 2, 15498/10000),
  (6, 47186/10000, 2, 15517/10000),
  (6, 47275/10000, 2, 15535/10000),
  (6, 47363/10000, 2, 15554/10000),
  (6, 47451/10000, 2, 15573/10000),
  (6, 47537/10000, 2, 15591/10000),
  (6, 47623/10000, 2, 15609/10000),
  (6, 47708/10000, 2, 15627/10000),
  (6, 47793/10000, 2, 15644/10000),
  (6, 47876/10000, 2, 15662/10000),
  (6, 47959/10000, 2, 15679/10000),
  (6, 48042/10000, 2, 15696/10000),
  (6, 48123/10000, 2, 15713/10000),
  (6, 48204/10000, 2, 15730/10000),
  (6, 48285/10000, 2, 15747/10000),
  (6, 48364/10000, 2, 15763/10000),
  (6, 48443/10000, 2, 15780/10000),
  (7, 48522/10000, 2, 15796/10000),
  (7, 48600/10000, 2, 15812/10000),
  (7, 48677/10000, 2, 15828/10000),
  (7, 48753/10000, 2, 15843/10000),
  (7, 48830/10000, 2, 15859/10000),
  (7, 48905/10000, 2, 15874/10000),
  (7, 48980/10000, 2, 15890/10000),
  (7, 49054/10000, 2, 15905/10000),
  (7, 49128/10000, 2, 15920/10000),
  (7, 49201/10000, 2, 15935/10000),
  (7, 49274/10000, 2, 15950/10000),
  (7, 49346/10000, 2, 15964/10000),
  (7, 49418/10000, 2, 15979/10000),
  (7, 49489/10000, 2, 15993/10000),
  (7, 49560/10000, 2, 16007/10000),
  (7, 49630/10000, 2, 16022/10000),
  (7, 49700/10000, 2, 16036/10000),
  (7, 49769/10000, 2, 16050/10000),
  (7, 49838/10000, 2, 16063/10000),
  (7, 49906/10000, 2, 16077/10000),
  (7, 49974/10000, 2, 16091/10000),
  (7, 50041/10000, 2, 16104/10000),
  (7, 50108/10000, 2, 16117/10000),
  (7, 50174/10000, 2, 16131/10000),
  (7, 50240/10000, 2, 16144/10000),
  (7, 50306/10000, 2, 16157/10000),
  (7, 50371/10000, 2, 16170/10000),
  (7, 50436/10000, 2, 16183/10000),
  (7, 50500/10000, 2, 16195/10000),
  (7, 50564/10000, 2, 16208/10000),
  (7, 50627/10000, 2, 16220/10000),
  (7, 50691/10000, 2, 16233/10000),
  (7, 50753/10000, 2, 16245/10000),
  (7, 50816/10000, 2, 16258/10000),
  (7, 50877/10000, 2, 16270/10000),
  (7, 50939/10000, 2, 16282/10000),
  (7, 51000/10000, 2, 16294/10000),
  (7, 51061/10000, 2, 16306/10000),
  (7, 51121/10000, 2, 16318/10000),
  (7, 51181/10000, 2, 16329/10000),
  (7, 51241/10000, 2, 16341/10000),
  (7, 51300/10000, 2, 16353/10000),
  (7, 51359/10000, 2, 16364/10000),
  (7, 51418/10000, 2, 16376/10000),
  (7, 51476/10000, 2, 16387/10000),
  (7, 51534/10000, 2, 16398/10000),
  (7, 51592/10000, 2, 16409/10000),
  (7, 51649/10000, 2, 16420/10000),
  (7, 51706/10000, 2, 16431/10000),
  (7, 51763/10000, 2, 16442/10000),
  (7, 51819/10000, 2, 16453/10000),
  (7, 51875/10000, 2, 16464/10000),
  (7, 51931/10000, 2, 16475/10000),
  (7, 51986/10000, 2, 16485/10000),
  (7, 52042/10000, 2, 16496/10000),
  (7, 52096/10000, 2, 16507/10000),
  (7, 52151/10000, 2, 16517/10000),
  (7, 52205/10000, 2, 16527/10000),
  (7, 52259/10000, 2, 16538/10000),
  (7, 52313/10000, 2, 16548/10000),
  (7, 52366/10000, 2, 16558/10000),
  (7, 52419/10000, 2, 16568/10000),
  (7, 52472/10000, 2, 16578/10000),
  (7, 52524/10000, 2, 16588/10000),
  (7, 52576/10000, 2, 16598/10000),
  (7, 52628/10000, 2, 16608/10000),
  (7, 52680/10000, 2, 16618/10000),
  (7, 52731/10000, 2, 16628/10000),
  (7, 52783/10000, 2, 16638/10000),
  (7, 52834/10000, 2, 16647/10000),
  (7, 52884/10000, 2, 16657/10000),
  (7, 52935/10000, 2, 16666/10000),
  (7, 52985/10000, 2, 16676/10000),
  (7, 53035/10000, 2, 16685/10000),
  (7, 53084/10000, 2, 16694/10000),
  (7, 53134/10000, 2, 16704/10000),
  (7, 53183/10000, 2, 16713/10000),
  (7, 53232/10000, 2, 16722/10000),
  (7, 53280/10000, 2, 16731/10000),
  (7, 53329/10000, 2, 16740/10000),
  (7, 53377/10000, 2, 16749/10000),
  (7, 53425/10000, 2, 16758/10000),
  (7, 53473/10000, 2, 16767/10000),
  (7, 53520/10000, 2, 16776/10000),
  (7, 53567/10000, 2, 16785/10000),
  (7, 53614/10000, 2, 16794/10000),
  (7, 53661/10000, 2, 16803/10000),
  (7, 53708/10000, 2, 16811/10000),
  (7, 53754/10000, 2, 16820/10000),
  (7, 53800/10000, 2, 16828/10000),
  (7, 53846/10000, 2, 16837/10000),
  (7, 53892/10000, 2, 16845/10000),
  (7, 53938/10000, 2, 16854/10000),
  (7, 53983/10000, 2, 16862/10000),
  (7, 54028/10000, 2, 16871/10000),
  (7, 54073/10000, 2, 16879/10000),
  (7, 54118/10000, 2, 16887/10000),
  (7, 54163/10000, 2, 16896/10000),
  (7, 54207/10000, 2, 16904/10000),
  (7, 54251/10000, 2, 16912/10000),
  (7, 54295/10000, 2, 16920/10000),
  (7, 54339/10000, 2, 16928/10000),
  (7, 54382/10000, 2, 16936/10000),
  (7, 54426/10000, 2, 16944/10000),
  (7, 54469/10000, 2, 16952/10000),
  (7, 54512/10000, 2, 16960/10000),
  (7, 54555/10000, 2, 16968/10000),
  (7, 54597/10000, 2, 16975/10000),
  (7, 54640/10000, 2, 16983/10000),
  (7, 54682/10000, 2, 16991/10000),
  (7, 54724/10000, 2, 16999/10000),
  (7, 54766/10000, 2, 17006/10000),
  (7, 54808/10000, 2, 17014/10000),
  (7, 54849/10000, 2, 17021/10000),
  (7, 54891/10000, 2, 17029/10000),
  (7, 54932/10000, 2, 17037/10000),
  (7, 54973/10000, 2, 17044/10000),
  (7, 55014/10000, 2, 17052/10000),
  (7, 55055/10000, 2, 17059/10000),
  (7, 55095/10000, 2, 17066/10000),
  (7, 55136/10000, 2, 17074/10000),
  (7, 55176/10000, 2, 17081/10000),
  (7, 55216/10000, 2, 17088/10000),
  (7, 55256/10000, 2, 17095/10000),
  (7, 55296/10000, 2, 17103/10000),
  (7, 55335/10000, 2, 17110/10000),
  (7, 55375/10000, 2, 17117/10000),
  (7, 55414/10000, 2, 17124/10000),
  (8, 55453/10000, 2, 17131/10000),
  (8, 55492/10000, 2, 17138/10000),
  (8, 55531/10000, 2, 17145/10000),
  (8, 55570/10000, 2, 17152/10000),
  (8, 55608/10000, 2, 17159/10000),
  (8, 55647/10000, 2, 17166/10000),
  (8, 55685/10000, 2, 17173/10000),
  (8, 55723/10000, 2, 17180/10000),
  (8, 55761/10000, 2, 17186/10000),
  (8, 55799/10000, 2, 17193/10000),
  (8, 55836/10000, 2, 17200/10000),
  (8, 55874/10000, 2, 17207/10000),
  (8, 55911/10000, 2, 17213/10000),
  (8, 55949/10000, 2, 17220/10000),
  (8, 55986/10000, 2, 17227/10000),
  (8, 56023/10000, 2, 17233/10000),
  (8, 56060/10000, 2, 17240/10000),
  (8, 56096/10000, 2, 17246/10000),
  (8, 56133/10000, 2, 17253/10000),
  (8, 56169/10000, 2, 17259/10000),
  (8, 56206/10000, 2, 17266/10000),
  (8, 56242/10000, 2, 17272/10000),
  (8, 56278/10000, 2, 17279/10000),
  (8, 56314/10000, 2, 17285/10000),
  (8, 56349/10000, 2, 17291/10000),
  (8, 56385/10000, 2, 17298/10000),
  (8, 56421/10000, 2, 17304/10000),
  (8, 56456/10000, 2, 17310/10000),
  (8, 56491/10000, 2, 17316/10000),
  (8, 56526/10000, 2, 17323/10000),
  (8, 56561/10000, 2, 17329/10000),
  (8, 56596/10000, 2, 17335/10000)
]

def bjsSmallPrefixQ (n : ℕ) : ℚ :=
  ∑ p ∈ range (n+1), if p.Prime then 1/(p : ℚ) else 0

def bjsSmallPrefixCertificate (n : ℕ) : Prop :=
  let (k,u,l,v) := bjsSmallLogRows[n]!
  (2 : ℚ)^k ≤ n+1 ∧ bjsLogUpper (n+1) k ≤ u ∧
  (2 : ℚ)^l ≤ u ∧ bjsLogUpper u l ≤ v ∧ 1 ≤ u ∧
  v+27/100-1/(2*u^2) ≤ bjsSmallPrefixQ n

instance (n : ℕ) : Decidable (bjsSmallPrefixCertificate n) := by
  unfold bjsSmallPrefixCertificate
  infer_instance

set_option Elab.async false

private theorem bjsSmallPrefixQ_step (n : ℕ) :
    bjsSmallPrefixQ (n+1) = bjsSmallPrefixQ n +
      (if (n+1).Prime then 1/((n+1 : ℕ) : ℚ) else 0) := by
  unfold bjsSmallPrefixQ
  rw [Finset.sum_range_succ]

private theorem bjsSmallPrefixQ_value000 : bjsSmallPrefixQ 0 = ((0 : ℚ)/1) := by
  norm_num [bjsSmallPrefixQ]

private theorem bjsSmallPrefixQ_value001 : bjsSmallPrefixQ 1 = ((0 : ℚ)/1) := by
  rw [bjsSmallPrefixQ_step 0, bjsSmallPrefixQ_value000]
  norm_num

private theorem bjsSmallPrefixQ_value002 : bjsSmallPrefixQ 2 = ((1 : ℚ)/2) := by
  rw [bjsSmallPrefixQ_step 1, bjsSmallPrefixQ_value001]
  norm_num

private theorem bjsSmallPrefixQ_value003 : bjsSmallPrefixQ 3 = ((5 : ℚ)/6) := by
  rw [bjsSmallPrefixQ_step 2, bjsSmallPrefixQ_value002]
  norm_num

private theorem bjsSmallPrefixQ_value004 : bjsSmallPrefixQ 4 = ((5 : ℚ)/6) := by
  rw [bjsSmallPrefixQ_step 3, bjsSmallPrefixQ_value003]
  norm_num

private theorem bjsSmallPrefixQ_value005 : bjsSmallPrefixQ 5 = ((31 : ℚ)/30) := by
  rw [bjsSmallPrefixQ_step 4, bjsSmallPrefixQ_value004]
  norm_num

private theorem bjsSmallPrefixQ_value006 : bjsSmallPrefixQ 6 = ((31 : ℚ)/30) := by
  rw [bjsSmallPrefixQ_step 5, bjsSmallPrefixQ_value005]
  norm_num

private theorem bjsSmallPrefixQ_value007 : bjsSmallPrefixQ 7 = ((247 : ℚ)/210) := by
  rw [bjsSmallPrefixQ_step 6, bjsSmallPrefixQ_value006]
  norm_num

private theorem bjsSmallPrefixQ_value008 : bjsSmallPrefixQ 8 = ((247 : ℚ)/210) := by
  rw [bjsSmallPrefixQ_step 7, bjsSmallPrefixQ_value007]
  norm_num

private theorem bjsSmallPrefixQ_value009 : bjsSmallPrefixQ 9 = ((247 : ℚ)/210) := by
  rw [bjsSmallPrefixQ_step 8, bjsSmallPrefixQ_value008]
  norm_num

private theorem bjsSmallPrefixQ_value010 : bjsSmallPrefixQ 10 = ((247 : ℚ)/210) := by
  rw [bjsSmallPrefixQ_step 9, bjsSmallPrefixQ_value009]
  norm_num

private theorem bjsSmallPrefixQ_value011 : bjsSmallPrefixQ 11 = ((2927 : ℚ)/2310) := by
  rw [bjsSmallPrefixQ_step 10, bjsSmallPrefixQ_value010]
  norm_num

private theorem bjsSmallPrefixQ_value012 : bjsSmallPrefixQ 12 = ((2927 : ℚ)/2310) := by
  rw [bjsSmallPrefixQ_step 11, bjsSmallPrefixQ_value011]
  norm_num

private theorem bjsSmallPrefixQ_value013 : bjsSmallPrefixQ 13 = ((40361 : ℚ)/30030) := by
  rw [bjsSmallPrefixQ_step 12, bjsSmallPrefixQ_value012]
  norm_num

private theorem bjsSmallPrefixQ_value014 : bjsSmallPrefixQ 14 = ((40361 : ℚ)/30030) := by
  rw [bjsSmallPrefixQ_step 13, bjsSmallPrefixQ_value013]
  norm_num

private theorem bjsSmallPrefixQ_value015 : bjsSmallPrefixQ 15 = ((40361 : ℚ)/30030) := by
  rw [bjsSmallPrefixQ_step 14, bjsSmallPrefixQ_value014]
  norm_num

private theorem bjsSmallPrefixQ_value016 : bjsSmallPrefixQ 16 = ((40361 : ℚ)/30030) := by
  rw [bjsSmallPrefixQ_step 15, bjsSmallPrefixQ_value015]
  norm_num

private theorem bjsSmallPrefixQ_value017 : bjsSmallPrefixQ 17 = ((716167 : ℚ)/510510) := by
  rw [bjsSmallPrefixQ_step 16, bjsSmallPrefixQ_value016]
  norm_num

private theorem bjsSmallPrefixQ_value018 : bjsSmallPrefixQ 18 = ((716167 : ℚ)/510510) := by
  rw [bjsSmallPrefixQ_step 17, bjsSmallPrefixQ_value017]
  norm_num

private theorem bjsSmallPrefixQ_value019 : bjsSmallPrefixQ 19 = ((14117683 : ℚ)/9699690) := by
  rw [bjsSmallPrefixQ_step 18, bjsSmallPrefixQ_value018]
  norm_num

private theorem bjsSmallPrefixQ_value020 : bjsSmallPrefixQ 20 = ((14117683 : ℚ)/9699690) := by
  rw [bjsSmallPrefixQ_step 19, bjsSmallPrefixQ_value019]
  norm_num

private theorem bjsSmallPrefixQ_value021 : bjsSmallPrefixQ 21 = ((14117683 : ℚ)/9699690) := by
  rw [bjsSmallPrefixQ_step 20, bjsSmallPrefixQ_value020]
  norm_num

private theorem bjsSmallPrefixQ_value022 : bjsSmallPrefixQ 22 = ((14117683 : ℚ)/9699690) := by
  rw [bjsSmallPrefixQ_step 21, bjsSmallPrefixQ_value021]
  norm_num

private theorem bjsSmallPrefixQ_value023 : bjsSmallPrefixQ 23 = ((334406399 : ℚ)/223092870) := by
  rw [bjsSmallPrefixQ_step 22, bjsSmallPrefixQ_value022]
  norm_num

private theorem bjsSmallPrefixQ_value024 : bjsSmallPrefixQ 24 = ((334406399 : ℚ)/223092870) := by
  rw [bjsSmallPrefixQ_step 23, bjsSmallPrefixQ_value023]
  norm_num

private theorem bjsSmallPrefixQ_value025 : bjsSmallPrefixQ 25 = ((334406399 : ℚ)/223092870) := by
  rw [bjsSmallPrefixQ_step 24, bjsSmallPrefixQ_value024]
  norm_num

private theorem bjsSmallPrefixQ_value026 : bjsSmallPrefixQ 26 = ((334406399 : ℚ)/223092870) := by
  rw [bjsSmallPrefixQ_step 25, bjsSmallPrefixQ_value025]
  norm_num

private theorem bjsSmallPrefixQ_value027 : bjsSmallPrefixQ 27 = ((334406399 : ℚ)/223092870) := by
  rw [bjsSmallPrefixQ_step 26, bjsSmallPrefixQ_value026]
  norm_num

private theorem bjsSmallPrefixQ_value028 : bjsSmallPrefixQ 28 = ((334406399 : ℚ)/223092870) := by
  rw [bjsSmallPrefixQ_step 27, bjsSmallPrefixQ_value027]
  norm_num

private theorem bjsSmallPrefixQ_value029 : bjsSmallPrefixQ 29 = ((9920878441 : ℚ)/6469693230) := by
  rw [bjsSmallPrefixQ_step 28, bjsSmallPrefixQ_value028]
  norm_num

private theorem bjsSmallPrefixQ_value030 : bjsSmallPrefixQ 30 = ((9920878441 : ℚ)/6469693230) := by
  rw [bjsSmallPrefixQ_step 29, bjsSmallPrefixQ_value029]
  norm_num

private theorem bjsSmallPrefixQ_value031 : bjsSmallPrefixQ 31 = ((314016924901 : ℚ)/200560490130) := by
  rw [bjsSmallPrefixQ_step 30, bjsSmallPrefixQ_value030]
  norm_num

private theorem bjsSmallPrefixQ_value032 : bjsSmallPrefixQ 32 = ((314016924901 : ℚ)/200560490130) := by
  rw [bjsSmallPrefixQ_step 31, bjsSmallPrefixQ_value031]
  norm_num

private theorem bjsSmallPrefixQ_value033 : bjsSmallPrefixQ 33 = ((314016924901 : ℚ)/200560490130) := by
  rw [bjsSmallPrefixQ_step 32, bjsSmallPrefixQ_value032]
  norm_num

private theorem bjsSmallPrefixQ_value034 : bjsSmallPrefixQ 34 = ((314016924901 : ℚ)/200560490130) := by
  rw [bjsSmallPrefixQ_step 33, bjsSmallPrefixQ_value033]
  norm_num

private theorem bjsSmallPrefixQ_value035 : bjsSmallPrefixQ 35 = ((314016924901 : ℚ)/200560490130) := by
  rw [bjsSmallPrefixQ_step 34, bjsSmallPrefixQ_value034]
  norm_num

private theorem bjsSmallPrefixQ_value036 : bjsSmallPrefixQ 36 = ((314016924901 : ℚ)/200560490130) := by
  rw [bjsSmallPrefixQ_step 35, bjsSmallPrefixQ_value035]
  norm_num

private theorem bjsSmallPrefixQ_value037 : bjsSmallPrefixQ 37 = ((11819186711467 : ℚ)/7420738134810) := by
  rw [bjsSmallPrefixQ_step 36, bjsSmallPrefixQ_value036]
  norm_num

private theorem bjsSmallPrefixQ_value038 : bjsSmallPrefixQ 38 = ((11819186711467 : ℚ)/7420738134810) := by
  rw [bjsSmallPrefixQ_step 37, bjsSmallPrefixQ_value037]
  norm_num

private theorem bjsSmallPrefixQ_value039 : bjsSmallPrefixQ 39 = ((11819186711467 : ℚ)/7420738134810) := by
  rw [bjsSmallPrefixQ_step 38, bjsSmallPrefixQ_value038]
  norm_num

private theorem bjsSmallPrefixQ_value040 : bjsSmallPrefixQ 40 = ((11819186711467 : ℚ)/7420738134810) := by
  rw [bjsSmallPrefixQ_step 39, bjsSmallPrefixQ_value039]
  norm_num

private theorem bjsSmallPrefixQ_value041 : bjsSmallPrefixQ 41 = ((492007393304957 : ℚ)/304250263527210) := by
  rw [bjsSmallPrefixQ_step 40, bjsSmallPrefixQ_value040]
  norm_num

private theorem bjsSmallPrefixQ_value042 : bjsSmallPrefixQ 42 = ((492007393304957 : ℚ)/304250263527210) := by
  rw [bjsSmallPrefixQ_step 41, bjsSmallPrefixQ_value041]
  norm_num

private theorem bjsSmallPrefixQ_value043 : bjsSmallPrefixQ 43 = ((21460568175640361 : ℚ)/13082761331670030) := by
  rw [bjsSmallPrefixQ_step 42, bjsSmallPrefixQ_value042]
  norm_num

private theorem bjsSmallPrefixQ_value044 : bjsSmallPrefixQ 44 = ((21460568175640361 : ℚ)/13082761331670030) := by
  rw [bjsSmallPrefixQ_step 43, bjsSmallPrefixQ_value043]
  norm_num

private theorem bjsSmallPrefixQ_value045 : bjsSmallPrefixQ 45 = ((21460568175640361 : ℚ)/13082761331670030) := by
  rw [bjsSmallPrefixQ_step 44, bjsSmallPrefixQ_value044]
  norm_num

private theorem bjsSmallPrefixQ_value046 : bjsSmallPrefixQ 46 = ((21460568175640361 : ℚ)/13082761331670030) := by
  rw [bjsSmallPrefixQ_step 45, bjsSmallPrefixQ_value045]
  norm_num

private theorem bjsSmallPrefixQ_value047 : bjsSmallPrefixQ 47 = ((1021729465586766997 : ℚ)/614889782588491410) := by
  rw [bjsSmallPrefixQ_step 46, bjsSmallPrefixQ_value046]
  norm_num

private theorem bjsSmallPrefixQ_value048 : bjsSmallPrefixQ 48 = ((1021729465586766997 : ℚ)/614889782588491410) := by
  rw [bjsSmallPrefixQ_step 47, bjsSmallPrefixQ_value047]
  norm_num

private theorem bjsSmallPrefixQ_value049 : bjsSmallPrefixQ 49 = ((1021729465586766997 : ℚ)/614889782588491410) := by
  rw [bjsSmallPrefixQ_step 48, bjsSmallPrefixQ_value048]
  norm_num

private theorem bjsSmallPrefixQ_value050 : bjsSmallPrefixQ 50 = ((1021729465586766997 : ℚ)/614889782588491410) := by
  rw [bjsSmallPrefixQ_step 49, bjsSmallPrefixQ_value049]
  norm_num

private theorem bjsSmallPrefixQ_value051 : bjsSmallPrefixQ 51 = ((1021729465586766997 : ℚ)/614889782588491410) := by
  rw [bjsSmallPrefixQ_step 50, bjsSmallPrefixQ_value050]
  norm_num

private theorem bjsSmallPrefixQ_value052 : bjsSmallPrefixQ 52 = ((1021729465586766997 : ℚ)/614889782588491410) := by
  rw [bjsSmallPrefixQ_step 51, bjsSmallPrefixQ_value051]
  norm_num

private theorem bjsSmallPrefixQ_value053 : bjsSmallPrefixQ 53 = ((54766551458687142251 : ℚ)/32589158477190044730) := by
  rw [bjsSmallPrefixQ_step 52, bjsSmallPrefixQ_value052]
  norm_num

private theorem bjsSmallPrefixQ_value054 : bjsSmallPrefixQ 54 = ((54766551458687142251 : ℚ)/32589158477190044730) := by
  rw [bjsSmallPrefixQ_step 53, bjsSmallPrefixQ_value053]
  norm_num

private theorem bjsSmallPrefixQ_value055 : bjsSmallPrefixQ 55 = ((54766551458687142251 : ℚ)/32589158477190044730) := by
  rw [bjsSmallPrefixQ_step 54, bjsSmallPrefixQ_value054]
  norm_num

private theorem bjsSmallPrefixQ_value056 : bjsSmallPrefixQ 56 = ((54766551458687142251 : ℚ)/32589158477190044730) := by
  rw [bjsSmallPrefixQ_step 55, bjsSmallPrefixQ_value055]
  norm_num

private theorem bjsSmallPrefixQ_value057 : bjsSmallPrefixQ 57 = ((54766551458687142251 : ℚ)/32589158477190044730) := by
  rw [bjsSmallPrefixQ_step 56, bjsSmallPrefixQ_value056]
  norm_num

private theorem bjsSmallPrefixQ_value058 : bjsSmallPrefixQ 58 = ((54766551458687142251 : ℚ)/32589158477190044730) := by
  rw [bjsSmallPrefixQ_step 57, bjsSmallPrefixQ_value057]
  norm_num

private theorem bjsSmallPrefixQ_value059 : bjsSmallPrefixQ 59 = ((3263815694539731437539 : ℚ)/1922760350154212639070) := by
  rw [bjsSmallPrefixQ_step 58, bjsSmallPrefixQ_value058]
  norm_num

private theorem bjsSmallPrefixQ_value060 : bjsSmallPrefixQ 60 = ((3263815694539731437539 : ℚ)/1922760350154212639070) := by
  rw [bjsSmallPrefixQ_step 59, bjsSmallPrefixQ_value059]
  norm_num

private theorem bjsSmallPrefixQ_value061 : bjsSmallPrefixQ 61 = ((201015517717077830328949 : ℚ)/117288381359406970983270) := by
  rw [bjsSmallPrefixQ_step 60, bjsSmallPrefixQ_value060]
  norm_num

private theorem bjsSmallPrefixQ_value062 : bjsSmallPrefixQ 62 = ((201015517717077830328949 : ℚ)/117288381359406970983270) := by
  rw [bjsSmallPrefixQ_step 61, bjsSmallPrefixQ_value061]
  norm_num

private theorem bjsSmallPrefixQ_value063 : bjsSmallPrefixQ 63 = ((201015517717077830328949 : ℚ)/117288381359406970983270) := by
  rw [bjsSmallPrefixQ_step 62, bjsSmallPrefixQ_value062]
  norm_num

private theorem bjsSmallPrefixQ_value064 : bjsSmallPrefixQ 64 = ((201015517717077830328949 : ℚ)/117288381359406970983270) := by
  rw [bjsSmallPrefixQ_step 63, bjsSmallPrefixQ_value063]
  norm_num

private theorem bjsSmallPrefixQ_value065 : bjsSmallPrefixQ 65 = ((201015517717077830328949 : ℚ)/117288381359406970983270) := by
  rw [bjsSmallPrefixQ_step 64, bjsSmallPrefixQ_value064]
  norm_num

private theorem bjsSmallPrefixQ_value066 : bjsSmallPrefixQ 66 = ((201015517717077830328949 : ℚ)/117288381359406970983270) := by
  rw [bjsSmallPrefixQ_step 65, bjsSmallPrefixQ_value065]
  norm_num

private theorem bjsSmallPrefixQ_value067 : bjsSmallPrefixQ 67 = ((13585328068403621603022853 : ℚ)/7858321551080267055879090) := by
  rw [bjsSmallPrefixQ_step 66, bjsSmallPrefixQ_value066]
  norm_num

private theorem bjsSmallPrefixQ_value068 : bjsSmallPrefixQ 68 = ((13585328068403621603022853 : ℚ)/7858321551080267055879090) := by
  rw [bjsSmallPrefixQ_step 67, bjsSmallPrefixQ_value067]
  norm_num

private theorem bjsSmallPrefixQ_value069 : bjsSmallPrefixQ 69 = ((13585328068403621603022853 : ℚ)/7858321551080267055879090) := by
  rw [bjsSmallPrefixQ_step 68, bjsSmallPrefixQ_value068]
  norm_num

private theorem bjsSmallPrefixQ_value070 : bjsSmallPrefixQ 70 = ((13585328068403621603022853 : ℚ)/7858321551080267055879090) := by
  rw [bjsSmallPrefixQ_step 69, bjsSmallPrefixQ_value069]
  norm_num

private theorem bjsSmallPrefixQ_value071 : bjsSmallPrefixQ 71 = ((972416614407737400870501653 : ℚ)/557940830126698960967415390) := by
  rw [bjsSmallPrefixQ_step 70, bjsSmallPrefixQ_value070]
  norm_num

private theorem bjsSmallPrefixQ_value072 : bjsSmallPrefixQ 72 = ((972416614407737400870501653 : ℚ)/557940830126698960967415390) := by
  rw [bjsSmallPrefixQ_step 71, bjsSmallPrefixQ_value071]
  norm_num

private theorem bjsSmallPrefixQ_value073 : bjsSmallPrefixQ 73 = ((71544353681891529224514036059 : ℚ)/40729680599249024150621323470) := by
  rw [bjsSmallPrefixQ_step 72, bjsSmallPrefixQ_value072]
  norm_num

private theorem bjsSmallPrefixQ_value074 : bjsSmallPrefixQ 74 = ((71544353681891529224514036059 : ℚ)/40729680599249024150621323470) := by
  rw [bjsSmallPrefixQ_step 73, bjsSmallPrefixQ_value073]
  norm_num

private theorem bjsSmallPrefixQ_value075 : bjsSmallPrefixQ 75 = ((71544353681891529224514036059 : ℚ)/40729680599249024150621323470) := by
  rw [bjsSmallPrefixQ_step 74, bjsSmallPrefixQ_value074]
  norm_num

private theorem bjsSmallPrefixQ_value076 : bjsSmallPrefixQ 76 = ((71544353681891529224514036059 : ℚ)/40729680599249024150621323470) := by
  rw [bjsSmallPrefixQ_step 75, bjsSmallPrefixQ_value075]
  norm_num

private theorem bjsSmallPrefixQ_value077 : bjsSmallPrefixQ 77 = ((71544353681891529224514036059 : ℚ)/40729680599249024150621323470) := by
  rw [bjsSmallPrefixQ_step 76, bjsSmallPrefixQ_value076]
  norm_num

private theorem bjsSmallPrefixQ_value078 : bjsSmallPrefixQ 78 = ((71544353681891529224514036059 : ℚ)/40729680599249024150621323470) := by
  rw [bjsSmallPrefixQ_step 77, bjsSmallPrefixQ_value077]
  norm_num

private theorem bjsSmallPrefixQ_value079 : bjsSmallPrefixQ 79 = ((5692733621468679832887230172131 : ℚ)/3217644767340672907899084554130) := by
  rw [bjsSmallPrefixQ_step 78, bjsSmallPrefixQ_value078]
  norm_num

private theorem bjsSmallPrefixQ_value080 : bjsSmallPrefixQ 80 = ((5692733621468679832887230172131 : ℚ)/3217644767340672907899084554130) := by
  rw [bjsSmallPrefixQ_step 79, bjsSmallPrefixQ_value079]
  norm_num

private theorem bjsSmallPrefixQ_value081 : bjsSmallPrefixQ 81 = ((5692733621468679832887230172131 : ℚ)/3217644767340672907899084554130) := by
  rw [bjsSmallPrefixQ_step 80, bjsSmallPrefixQ_value080]
  norm_num

private theorem bjsSmallPrefixQ_value082 : bjsSmallPrefixQ 82 = ((5692733621468679832887230172131 : ℚ)/3217644767340672907899084554130) := by
  rw [bjsSmallPrefixQ_step 81, bjsSmallPrefixQ_value081]
  norm_num

private theorem bjsSmallPrefixQ_value083 : bjsSmallPrefixQ 83 = ((475714535349241099037539188841003 : ℚ)/267064515689275851355624017992790) := by
  rw [bjsSmallPrefixQ_step 82, bjsSmallPrefixQ_value082]
  norm_num

private theorem bjsSmallPrefixQ_value084 : bjsSmallPrefixQ 84 = ((475714535349241099037539188841003 : ℚ)/267064515689275851355624017992790) := by
  rw [bjsSmallPrefixQ_step 83, bjsSmallPrefixQ_value083]
  norm_num

private theorem bjsSmallPrefixQ_value085 : bjsSmallPrefixQ 85 = ((475714535349241099037539188841003 : ℚ)/267064515689275851355624017992790) := by
  rw [bjsSmallPrefixQ_step 84, bjsSmallPrefixQ_value084]
  norm_num

private theorem bjsSmallPrefixQ_value086 : bjsSmallPrefixQ 86 = ((475714535349241099037539188841003 : ℚ)/267064515689275851355624017992790) := by
  rw [bjsSmallPrefixQ_step 85, bjsSmallPrefixQ_value085]
  norm_num

private theorem bjsSmallPrefixQ_value087 : bjsSmallPrefixQ 87 = ((475714535349241099037539188841003 : ℚ)/267064515689275851355624017992790) := by
  rw [bjsSmallPrefixQ_step 86, bjsSmallPrefixQ_value086]
  norm_num

private theorem bjsSmallPrefixQ_value088 : bjsSmallPrefixQ 88 = ((475714535349241099037539188841003 : ℚ)/267064515689275851355624017992790) := by
  rw [bjsSmallPrefixQ_step 87, bjsSmallPrefixQ_value087]
  norm_num

private theorem bjsSmallPrefixQ_value089 : bjsSmallPrefixQ 89 = ((42605658161771733665696611824842057 : ℚ)/23768741896345550770650537601358310) := by
  rw [bjsSmallPrefixQ_step 88, bjsSmallPrefixQ_value088]
  norm_num

private theorem bjsSmallPrefixQ_value090 : bjsSmallPrefixQ 90 = ((42605658161771733665696611824842057 : ℚ)/23768741896345550770650537601358310) := by
  rw [bjsSmallPrefixQ_step 89, bjsSmallPrefixQ_value089]
  norm_num

private theorem bjsSmallPrefixQ_value091 : bjsSmallPrefixQ 91 = ((42605658161771733665696611824842057 : ℚ)/23768741896345550770650537601358310) := by
  rw [bjsSmallPrefixQ_step 90, bjsSmallPrefixQ_value090]
  norm_num

private theorem bjsSmallPrefixQ_value092 : bjsSmallPrefixQ 92 = ((42605658161771733665696611824842057 : ℚ)/23768741896345550770650537601358310) := by
  rw [bjsSmallPrefixQ_step 91, bjsSmallPrefixQ_value091]
  norm_num

private theorem bjsSmallPrefixQ_value093 : bjsSmallPrefixQ 93 = ((42605658161771733665696611824842057 : ℚ)/23768741896345550770650537601358310) := by
  rw [bjsSmallPrefixQ_step 92, bjsSmallPrefixQ_value092]
  norm_num

private theorem bjsSmallPrefixQ_value094 : bjsSmallPrefixQ 94 = ((42605658161771733665696611824842057 : ℚ)/23768741896345550770650537601358310) := by
  rw [bjsSmallPrefixQ_step 93, bjsSmallPrefixQ_value093]
  norm_num

private theorem bjsSmallPrefixQ_value095 : bjsSmallPrefixQ 95 = ((42605658161771733665696611824842057 : ℚ)/23768741896345550770650537601358310) := by
  rw [bjsSmallPrefixQ_step 94, bjsSmallPrefixQ_value094]
  norm_num

private theorem bjsSmallPrefixQ_value096 : bjsSmallPrefixQ 96 = ((42605658161771733665696611824842057 : ℚ)/23768741896345550770650537601358310) := by
  rw [bjsSmallPrefixQ_step 95, bjsSmallPrefixQ_value095]
  norm_num

private theorem bjsSmallPrefixQ_value097 : bjsSmallPrefixQ 97 = ((4156517583588203716343221884611037839 : ℚ)/2305567963945518424753102147331756070) := by
  rw [bjsSmallPrefixQ_step 96, bjsSmallPrefixQ_value096]
  norm_num

private theorem bjsSmallPrefixQ_value098 : bjsSmallPrefixQ 98 = ((4156517583588203716343221884611037839 : ℚ)/2305567963945518424753102147331756070) := by
  rw [bjsSmallPrefixQ_step 97, bjsSmallPrefixQ_value097]
  norm_num

private theorem bjsSmallPrefixQ_value099 : bjsSmallPrefixQ 99 = ((4156517583588203716343221884611037839 : ℚ)/2305567963945518424753102147331756070) := by
  rw [bjsSmallPrefixQ_step 98, bjsSmallPrefixQ_value098]
  norm_num

private theorem bjsSmallPrefixQ_value100 : bjsSmallPrefixQ 100 = ((4156517583588203716343221884611037839 : ℚ)/2305567963945518424753102147331756070) := by
  rw [bjsSmallPrefixQ_step 99, bjsSmallPrefixQ_value099]
  norm_num

private theorem bjsSmallPrefixQ_value101 : bjsSmallPrefixQ 101 = ((422113843906354093775418512493046577809 : ℚ)/232862364358497360900063316880507363070) := by
  rw [bjsSmallPrefixQ_step 100, bjsSmallPrefixQ_value100]
  norm_num

private theorem bjsSmallPrefixQ_value102 : bjsSmallPrefixQ 102 = ((422113843906354093775418512493046577809 : ℚ)/232862364358497360900063316880507363070) := by
  rw [bjsSmallPrefixQ_step 101, bjsSmallPrefixQ_value101]
  norm_num

private theorem bjsSmallPrefixQ_value103 : bjsSmallPrefixQ 103 = ((43710588286712969019768170103664304877397 : ℚ)/23984823528925228172706521638692258396210) := by
  rw [bjsSmallPrefixQ_step 102, bjsSmallPrefixQ_value102]
  norm_num

private theorem bjsSmallPrefixQ_value104 : bjsSmallPrefixQ 104 = ((43710588286712969019768170103664304877397 : ℚ)/23984823528925228172706521638692258396210) := by
  rw [bjsSmallPrefixQ_step 103, bjsSmallPrefixQ_value103]
  norm_num

private theorem bjsSmallPrefixQ_value105 : bjsSmallPrefixQ 105 = ((43710588286712969019768170103664304877397 : ℚ)/23984823528925228172706521638692258396210) := by
  rw [bjsSmallPrefixQ_step 104, bjsSmallPrefixQ_value104]
  norm_num

private theorem bjsSmallPrefixQ_value106 : bjsSmallPrefixQ 106 = ((43710588286712969019768170103664304877397 : ℚ)/23984823528925228172706521638692258396210) := by
  rw [bjsSmallPrefixQ_step 105, bjsSmallPrefixQ_value105]
  norm_num

private theorem bjsSmallPrefixQ_value107 : bjsSmallPrefixQ 107 = ((4701017770207212913287900722730772880277689 : ℚ)/2566376117594999414479597815340071648394470) := by
  rw [bjsSmallPrefixQ_step 106, bjsSmallPrefixQ_value106]
  norm_num

private theorem bjsSmallPrefixQ_value108 : bjsSmallPrefixQ 108 = ((4701017770207212913287900722730772880277689 : ℚ)/2566376117594999414479597815340071648394470) := by
  rw [bjsSmallPrefixQ_step 107, bjsSmallPrefixQ_value107]
  norm_num

private theorem bjsSmallPrefixQ_value109 : bjsSmallPrefixQ 109 = ((514977313070181206962860776592994315598662571 : ℚ)/279734996817854936178276161872067809674997230) := by
  rw [bjsSmallPrefixQ_step 108, bjsSmallPrefixQ_value108]
  norm_num

private theorem bjsSmallPrefixQ_value110 : bjsSmallPrefixQ 110 = ((514977313070181206962860776592994315598662571 : ℚ)/279734996817854936178276161872067809674997230) := by
  rw [bjsSmallPrefixQ_step 109, bjsSmallPrefixQ_value109]
  norm_num

private theorem bjsSmallPrefixQ_value111 : bjsSmallPrefixQ 111 = ((514977313070181206962860776592994315598662571 : ℚ)/279734996817854936178276161872067809674997230) := by
  rw [bjsSmallPrefixQ_step 110, bjsSmallPrefixQ_value110]
  norm_num

private theorem bjsSmallPrefixQ_value112 : bjsSmallPrefixQ 112 = ((514977313070181206962860776592994315598662571 : ℚ)/279734996817854936178276161872067809674997230) := by
  rw [bjsSmallPrefixQ_step 111, bjsSmallPrefixQ_value111]
  norm_num

private theorem bjsSmallPrefixQ_value113 : bjsSmallPrefixQ 113 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 112, bjsSmallPrefixQ_value112]
  norm_num

private theorem bjsSmallPrefixQ_value114 : bjsSmallPrefixQ 114 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 113, bjsSmallPrefixQ_value113]
  norm_num

private theorem bjsSmallPrefixQ_value115 : bjsSmallPrefixQ 115 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 114, bjsSmallPrefixQ_value114]
  norm_num

private theorem bjsSmallPrefixQ_value116 : bjsSmallPrefixQ 116 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 115, bjsSmallPrefixQ_value115]
  norm_num

private theorem bjsSmallPrefixQ_value117 : bjsSmallPrefixQ 117 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 116, bjsSmallPrefixQ_value116]
  norm_num

private theorem bjsSmallPrefixQ_value118 : bjsSmallPrefixQ 118 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 117, bjsSmallPrefixQ_value117]
  norm_num

private theorem bjsSmallPrefixQ_value119 : bjsSmallPrefixQ 119 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 118, bjsSmallPrefixQ_value118]
  norm_num

private theorem bjsSmallPrefixQ_value120 : bjsSmallPrefixQ 120 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 119, bjsSmallPrefixQ_value119]
  norm_num

private theorem bjsSmallPrefixQ_value121 : bjsSmallPrefixQ 121 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 120, bjsSmallPrefixQ_value120]
  norm_num

private theorem bjsSmallPrefixQ_value122 : bjsSmallPrefixQ 122 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 121, bjsSmallPrefixQ_value121]
  norm_num

private theorem bjsSmallPrefixQ_value123 : bjsSmallPrefixQ 123 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 122, bjsSmallPrefixQ_value122]
  norm_num

private theorem bjsSmallPrefixQ_value124 : bjsSmallPrefixQ 124 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 123, bjsSmallPrefixQ_value123]
  norm_num

private theorem bjsSmallPrefixQ_value125 : bjsSmallPrefixQ 125 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 124, bjsSmallPrefixQ_value124]
  norm_num

private theorem bjsSmallPrefixQ_value126 : bjsSmallPrefixQ 126 = ((58472171373748331322981543916880425472323867753 : ℚ)/31610054640417607788145206291543662493274686990) := by
  rw [bjsSmallPrefixQ_step 125, bjsSmallPrefixQ_value125]
  norm_num

private theorem bjsSmallPrefixQ_value127 : bjsSmallPrefixQ 127 = ((7457575819106455685806801283735357697478405891621 : ℚ)/4014476939333036189094441199026045136645885247730) := by
  rw [bjsSmallPrefixQ_step 126, bjsSmallPrefixQ_value126]
  norm_num

private theorem bjsSmallPrefixQ_value128 : bjsSmallPrefixQ 128 = ((7457575819106455685806801283735357697478405891621 : ℚ)/4014476939333036189094441199026045136645885247730) := by
  rw [bjsSmallPrefixQ_step 127, bjsSmallPrefixQ_value127]
  norm_num

private theorem bjsSmallPrefixQ_value129 : bjsSmallPrefixQ 129 = ((7457575819106455685806801283735357697478405891621 : ℚ)/4014476939333036189094441199026045136645885247730) := by
  rw [bjsSmallPrefixQ_step 128, bjsSmallPrefixQ_value128]
  norm_num

private theorem bjsSmallPrefixQ_value130 : bjsSmallPrefixQ 130 = ((7457575819106455685806801283735357697478405891621 : ℚ)/4014476939333036189094441199026045136645885247730) := by
  rw [bjsSmallPrefixQ_step 129, bjsSmallPrefixQ_value129]
  norm_num

private theorem bjsSmallPrefixQ_value131 : bjsSmallPrefixQ 131 = ((980956909242278731029785409368357903506317057050081 : ℚ)/525896479052627740771371797072411912900610967452630) := by
  rw [bjsSmallPrefixQ_step 130, bjsSmallPrefixQ_value130]
  norm_num

private theorem bjsSmallPrefixQ_value132 : bjsSmallPrefixQ 132 = ((980956909242278731029785409368357903506317057050081 : ℚ)/525896479052627740771371797072411912900610967452630) := by
  rw [bjsSmallPrefixQ_step 131, bjsSmallPrefixQ_value131]
  norm_num

private theorem bjsSmallPrefixQ_value133 : bjsSmallPrefixQ 133 = ((980956909242278731029785409368357903506317057050081 : ℚ)/525896479052627740771371797072411912900610967452630) := by
  rw [bjsSmallPrefixQ_step 132, bjsSmallPrefixQ_value132]
  norm_num

private theorem bjsSmallPrefixQ_value134 : bjsSmallPrefixQ 134 = ((980956909242278731029785409368357903506317057050081 : ℚ)/525896479052627740771371797072411912900610967452630) := by
  rw [bjsSmallPrefixQ_step 133, bjsSmallPrefixQ_value133]
  norm_num

private theorem bjsSmallPrefixQ_value135 : bjsSmallPrefixQ 135 = ((980956909242278731029785409368357903506317057050081 : ℚ)/525896479052627740771371797072411912900610967452630) := by
  rw [bjsSmallPrefixQ_step 134, bjsSmallPrefixQ_value134]
  norm_num

private theorem bjsSmallPrefixQ_value136 : bjsSmallPrefixQ 136 = ((980956909242278731029785409368357903506317057050081 : ℚ)/525896479052627740771371797072411912900610967452630) := by
  rw [bjsSmallPrefixQ_step 135, bjsSmallPrefixQ_value135]
  norm_num

private theorem bjsSmallPrefixQ_value137 : bjsSmallPrefixQ 137 = ((134916993045244813891851972880537444693266047783313727 : ℚ)/72047817630210000485677936198920432067383702541010310) := by
  rw [bjsSmallPrefixQ_step 136, bjsSmallPrefixQ_value136]
  norm_num

private theorem bjsSmallPrefixQ_value138 : bjsSmallPrefixQ 138 = ((134916993045244813891851972880537444693266047783313727 : ℚ)/72047817630210000485677936198920432067383702541010310) := by
  rw [bjsSmallPrefixQ_step 137, bjsSmallPrefixQ_value137]
  norm_num

private theorem bjsSmallPrefixQ_value139 : bjsSmallPrefixQ 139 = ((18825509850919239131453102166593625244431364344421618363 : ℚ)/10014646650599190067509233131649940057366334653200433090) := by
  rw [bjsSmallPrefixQ_step 138, bjsSmallPrefixQ_value138]
  norm_num

private theorem bjsSmallPrefixQ_value140 : bjsSmallPrefixQ 140 = ((18825509850919239131453102166593625244431364344421618363 : ℚ)/10014646650599190067509233131649940057366334653200433090) := by
  rw [bjsSmallPrefixQ_step 139, bjsSmallPrefixQ_value139]
  norm_num

private theorem bjsSmallPrefixQ_value141 : bjsSmallPrefixQ 141 = ((18825509850919239131453102166593625244431364344421618363 : ℚ)/10014646650599190067509233131649940057366334653200433090) := by
  rw [bjsSmallPrefixQ_step 140, bjsSmallPrefixQ_value140]
  norm_num

private theorem bjsSmallPrefixQ_value142 : bjsSmallPrefixQ 142 = ((18825509850919239131453102166593625244431364344421618363 : ℚ)/10014646650599190067509233131649940057366334653200433090) := by
  rw [bjsSmallPrefixQ_step 141, bjsSmallPrefixQ_value141]
  norm_num

private theorem bjsSmallPrefixQ_value143 : bjsSmallPrefixQ 143 = ((18825509850919239131453102166593625244431364344421618363 : ℚ)/10014646650599190067509233131649940057366334653200433090) := by
  rw [bjsSmallPrefixQ_step 142, bjsSmallPrefixQ_value142]
  norm_num

private theorem bjsSmallPrefixQ_value144 : bjsSmallPrefixQ 144 = ((18825509850919239131453102166593625244431364344421618363 : ℚ)/10014646650599190067509233131649940057366334653200433090) := by
  rw [bjsSmallPrefixQ_step 143, bjsSmallPrefixQ_value143]
  norm_num

private theorem bjsSmallPrefixQ_value145 : bjsSmallPrefixQ 145 = ((18825509850919239131453102166593625244431364344421618363 : ℚ)/10014646650599190067509233131649940057366334653200433090) := by
  rw [bjsSmallPrefixQ_step 144, bjsSmallPrefixQ_value144]
  norm_num

private theorem bjsSmallPrefixQ_value146 : bjsSmallPrefixQ 146 = ((18825509850919239131453102166593625244431364344421618363 : ℚ)/10014646650599190067509233131649940057366334653200433090) := by
  rw [bjsSmallPrefixQ_step 145, bjsSmallPrefixQ_value145]
  norm_num

private theorem bjsSmallPrefixQ_value147 : bjsSmallPrefixQ 147 = ((18825509850919239131453102166593625244431364344421618363 : ℚ)/10014646650599190067509233131649940057366334653200433090) := by
  rw [bjsSmallPrefixQ_step 146, bjsSmallPrefixQ_value146]
  norm_num

private theorem bjsSmallPrefixQ_value148 : bjsSmallPrefixQ 148 = ((18825509850919239131453102166593625244431364344421618363 : ℚ)/10014646650599190067509233131649940057366334653200433090) := by
  rw [bjsSmallPrefixQ_step 147, bjsSmallPrefixQ_value147]
  norm_num

private theorem bjsSmallPrefixQ_value149 : bjsSmallPrefixQ 149 = ((2815015614437565820654021455954100101477639621972021569177 : ℚ)/1492182350939279320058875736615841068547583863326864530410) := by
  rw [bjsSmallPrefixQ_step 148, bjsSmallPrefixQ_value148]
  norm_num

private theorem bjsSmallPrefixQ_value150 : bjsSmallPrefixQ 150 = ((2815015614437565820654021455954100101477639621972021569177 : ℚ)/1492182350939279320058875736615841068547583863326864530410) := by
  rw [bjsSmallPrefixQ_step 149, bjsSmallPrefixQ_value149]
  norm_num

private theorem bjsSmallPrefixQ_value151 : bjsSmallPrefixQ 151 = ((426559540131011718238816115585684956391671166781102121476137 : ℚ)/225319534991831177328890236228992001350685163362356544091910) := by
  rw [bjsSmallPrefixQ_step 150, bjsSmallPrefixQ_value150]
  norm_num

private theorem bjsSmallPrefixQ_value152 : bjsSmallPrefixQ 152 = ((426559540131011718238816115585684956391671166781102121476137 : ℚ)/225319534991831177328890236228992001350685163362356544091910) := by
  rw [bjsSmallPrefixQ_step 151, bjsSmallPrefixQ_value151]
  norm_num

private theorem bjsSmallPrefixQ_value153 : bjsSmallPrefixQ 153 = ((426559540131011718238816115585684956391671166781102121476137 : ℚ)/225319534991831177328890236228992001350685163362356544091910) := by
  rw [bjsSmallPrefixQ_step 152, bjsSmallPrefixQ_value152]
  norm_num

private theorem bjsSmallPrefixQ_value154 : bjsSmallPrefixQ 154 = ((426559540131011718238816115585684956391671166781102121476137 : ℚ)/225319534991831177328890236228992001350685163362356544091910) := by
  rw [bjsSmallPrefixQ_step 153, bjsSmallPrefixQ_value153]
  norm_num

private theorem bjsSmallPrefixQ_value155 : bjsSmallPrefixQ 155 = ((426559540131011718238816115585684956391671166781102121476137 : ℚ)/225319534991831177328890236228992001350685163362356544091910) := by
  rw [bjsSmallPrefixQ_step 154, bjsSmallPrefixQ_value154]
  norm_num

private theorem bjsSmallPrefixQ_value156 : bjsSmallPrefixQ 156 = ((426559540131011718238816115585684956391671166781102121476137 : ℚ)/225319534991831177328890236228992001350685163362356544091910) := by
  rw [bjsSmallPrefixQ_step 155, bjsSmallPrefixQ_value155]
  norm_num

private theorem bjsSmallPrefixQ_value157 : bjsSmallPrefixQ 157 = ((67195167335560670940823020383181530154843058347995389615845419 : ℚ)/35375166993717494840635767087951744212057570647889977422429870) := by
  rw [bjsSmallPrefixQ_step 156, bjsSmallPrefixQ_value156]
  norm_num

private theorem bjsSmallPrefixQ_value158 : bjsSmallPrefixQ 158 = ((67195167335560670940823020383181530154843058347995389615845419 : ℚ)/35375166993717494840635767087951744212057570647889977422429870) := by
  rw [bjsSmallPrefixQ_step 157, bjsSmallPrefixQ_value157]
  norm_num

private theorem bjsSmallPrefixQ_value159 : bjsSmallPrefixQ 159 = ((67195167335560670940823020383181530154843058347995389615845419 : ℚ)/35375166993717494840635767087951744212057570647889977422429870) := by
  rw [bjsSmallPrefixQ_step 158, bjsSmallPrefixQ_value158]
  norm_num

private theorem bjsSmallPrefixQ_value160 : bjsSmallPrefixQ 160 = ((67195167335560670940823020383181530154843058347995389615845419 : ℚ)/35375166993717494840635767087951744212057570647889977422429870) := by
  rw [bjsSmallPrefixQ_step 159, bjsSmallPrefixQ_value159]
  norm_num

private theorem bjsSmallPrefixQ_value161 : bjsSmallPrefixQ 161 = ((67195167335560670940823020383181530154843058347995389615845419 : ℚ)/35375166993717494840635767087951744212057570647889977422429870) := by
  rw [bjsSmallPrefixQ_step 160, bjsSmallPrefixQ_value160]
  norm_num

private theorem bjsSmallPrefixQ_value162 : bjsSmallPrefixQ 162 = ((67195167335560670940823020383181530154843058347995389615845419 : ℚ)/35375166993717494840635767087951744212057570647889977422429870) := by
  rw [bjsSmallPrefixQ_step 161, bjsSmallPrefixQ_value161]
  norm_num

private theorem bjsSmallPrefixQ_value163 : bjsSmallPrefixQ 163 = ((10988187442690106858194788089546541159451476081371138484805233167 : ℚ)/5766152219975951659023630035336134306565384015606066319856068810) := by
  rw [bjsSmallPrefixQ_step 162, bjsSmallPrefixQ_value162]
  norm_num

private theorem bjsSmallPrefixQ_value164 : bjsSmallPrefixQ 164 = ((10988187442690106858194788089546541159451476081371138484805233167 : ℚ)/5766152219975951659023630035336134306565384015606066319856068810) := by
  rw [bjsSmallPrefixQ_step 163, bjsSmallPrefixQ_value163]
  norm_num

private theorem bjsSmallPrefixQ_value165 : bjsSmallPrefixQ 165 = ((10988187442690106858194788089546541159451476081371138484805233167 : ℚ)/5766152219975951659023630035336134306565384015606066319856068810) := by
  rw [bjsSmallPrefixQ_step 164, bjsSmallPrefixQ_value164]
  norm_num

private theorem bjsSmallPrefixQ_value166 : bjsSmallPrefixQ 166 = ((10988187442690106858194788089546541159451476081371138484805233167 : ℚ)/5766152219975951659023630035336134306565384015606066319856068810) := by
  rw [bjsSmallPrefixQ_step 165, bjsSmallPrefixQ_value165]
  norm_num

private theorem bjsSmallPrefixQ_value167 : bjsSmallPrefixQ 167 = ((1840793455149223796977553240989608507934961889604586193282330007699 : ℚ)/962947420735983927056946215901134429196419130606213075415963491270) := by
  rw [bjsSmallPrefixQ_step 166, bjsSmallPrefixQ_value166]
  norm_num

private theorem bjsSmallPrefixQ_value168 : bjsSmallPrefixQ 168 = ((1840793455149223796977553240989608507934961889604586193282330007699 : ℚ)/962947420735983927056946215901134429196419130606213075415963491270) := by
  rw [bjsSmallPrefixQ_step 167, bjsSmallPrefixQ_value167]
  norm_num

private theorem bjsSmallPrefixQ_value169 : bjsSmallPrefixQ 169 = ((1840793455149223796977553240989608507934961889604586193282330007699 : ℚ)/962947420735983927056946215901134429196419130606213075415963491270) := by
  rw [bjsSmallPrefixQ_step 168, bjsSmallPrefixQ_value168]
  norm_num

private theorem bjsSmallPrefixQ_value170 : bjsSmallPrefixQ 170 = ((1840793455149223796977553240989608507934961889604586193282330007699 : ℚ)/962947420735983927056946215901134429196419130606213075415963491270) := by
  rw [bjsSmallPrefixQ_step 169, bjsSmallPrefixQ_value169]
  norm_num

private theorem bjsSmallPrefixQ_value171 : bjsSmallPrefixQ 171 = ((1840793455149223796977553240989608507934961889604586193282330007699 : ℚ)/962947420735983927056946215901134429196419130606213075415963491270) := by
  rw [bjsSmallPrefixQ_step 170, bjsSmallPrefixQ_value170]
  norm_num

private theorem bjsSmallPrefixQ_value172 : bjsSmallPrefixQ 172 = ((1840793455149223796977553240989608507934961889604586193282330007699 : ℚ)/962947420735983927056946215901134429196419130606213075415963491270) := by
  rw [bjsSmallPrefixQ_step 171, bjsSmallPrefixQ_value171]
  norm_num

private theorem bjsSmallPrefixQ_value173 : bjsSmallPrefixQ 173 = ((319420215161551700804173656907103406301944826032199624513259054823197 : ℚ)/166589903787325219380851695350896256250980509594874862046961683989710) := by
  rw [bjsSmallPrefixQ_step 172, bjsSmallPrefixQ_value172]
  norm_num

private theorem bjsSmallPrefixQ_value174 : bjsSmallPrefixQ 174 = ((319420215161551700804173656907103406301944826032199624513259054823197 : ℚ)/166589903787325219380851695350896256250980509594874862046961683989710) := by
  rw [bjsSmallPrefixQ_step 173, bjsSmallPrefixQ_value173]
  norm_num

private theorem bjsSmallPrefixQ_value175 : bjsSmallPrefixQ 175 = ((319420215161551700804173656907103406301944826032199624513259054823197 : ℚ)/166589903787325219380851695350896256250980509594874862046961683989710) := by
  rw [bjsSmallPrefixQ_step 174, bjsSmallPrefixQ_value174]
  norm_num

private theorem bjsSmallPrefixQ_value176 : bjsSmallPrefixQ 176 = ((319420215161551700804173656907103406301944826032199624513259054823197 : ℚ)/166589903787325219380851695350896256250980509594874862046961683989710) := by
  rw [bjsSmallPrefixQ_step 175, bjsSmallPrefixQ_value175]
  norm_num

private theorem bjsSmallPrefixQ_value177 : bjsSmallPrefixQ 177 = ((319420215161551700804173656907103406301944826032199624513259054823197 : ℚ)/166589903787325219380851695350896256250980509594874862046961683989710) := by
  rw [bjsSmallPrefixQ_step 176, bjsSmallPrefixQ_value176]
  norm_num

private theorem bjsSmallPrefixQ_value178 : bjsSmallPrefixQ 178 = ((319420215161551700804173656907103406301944826032199624513259054823197 : ℚ)/166589903787325219380851695350896256250980509594874862046961683989710) := by
  rw [bjsSmallPrefixQ_step 177, bjsSmallPrefixQ_value177]
  norm_num

private theorem bjsSmallPrefixQ_value179 : bjsSmallPrefixQ 179 = ((57342808417705079663327936281722405984299104369358607649920332497341973 : ℚ)/29819592777931214269172453467810429868925511217482600306406141434158090) := by
  rw [bjsSmallPrefixQ_step 178, bjsSmallPrefixQ_value178]
  norm_num

private theorem bjsSmallPrefixQ_value180 : bjsSmallPrefixQ 180 = ((57342808417705079663327936281722405984299104369358607649920332497341973 : ℚ)/29819592777931214269172453467810429868925511217482600306406141434158090) := by
  rw [bjsSmallPrefixQ_step 179, bjsSmallPrefixQ_value179]
  norm_num

private theorem bjsSmallPrefixQ_value181 : bjsSmallPrefixQ 181 = ((10408867916382550633331528920459565913027063402071390584941986323453055203 : ℚ)/5397346292805549782720214077673687806275517530364350655459511599582614290) := by
  rw [bjsSmallPrefixQ_step 180, bjsSmallPrefixQ_value180]
  norm_num

private theorem bjsSmallPrefixQ_value182 : bjsSmallPrefixQ 182 = ((10408867916382550633331528920459565913027063402071390584941986323453055203 : ℚ)/5397346292805549782720214077673687806275517530364350655459511599582614290) := by
  rw [bjsSmallPrefixQ_step 181, bjsSmallPrefixQ_value181]
  norm_num

private theorem bjsSmallPrefixQ_value183 : bjsSmallPrefixQ 183 = ((10408867916382550633331528920459565913027063402071390584941986323453055203 : ℚ)/5397346292805549782720214077673687806275517530364350655459511599582614290) := by
  rw [bjsSmallPrefixQ_step 182, bjsSmallPrefixQ_value182]
  norm_num

private theorem bjsSmallPrefixQ_value184 : bjsSmallPrefixQ 184 = ((10408867916382550633331528920459565913027063402071390584941986323453055203 : ℚ)/5397346292805549782720214077673687806275517530364350655459511599582614290) := by
  rw [bjsSmallPrefixQ_step 183, bjsSmallPrefixQ_value183]
  norm_num

private theorem bjsSmallPrefixQ_value185 : bjsSmallPrefixQ 185 = ((10408867916382550633331528920459565913027063402071390584941986323453055203 : ℚ)/5397346292805549782720214077673687806275517530364350655459511599582614290) := by
  rw [bjsSmallPrefixQ_step 184, bjsSmallPrefixQ_value184]
  norm_num

private theorem bjsSmallPrefixQ_value186 : bjsSmallPrefixQ 186 = ((10408867916382550633331528920459565913027063402071390584941986323453055203 : ℚ)/5397346292805549782720214077673687806275517530364350655459511599582614290) := by
  rw [bjsSmallPrefixQ_step 185, bjsSmallPrefixQ_value185]
  norm_num

private theorem bjsSmallPrefixQ_value187 : bjsSmallPrefixQ 187 = ((10408867916382550633331528920459565913027063402071390584941986323453055203 : ℚ)/5397346292805549782720214077673687806275517530364350655459511599582614290) := by
  rw [bjsSmallPrefixQ_step 186, bjsSmallPrefixQ_value186]
  norm_num

private theorem bjsSmallPrefixQ_value188 : bjsSmallPrefixQ 188 = ((10408867916382550633331528920459565913027063402071390584941986323453055203 : ℚ)/5397346292805549782720214077673687806275517530364350655459511599582614290) := by
  rw [bjsSmallPrefixQ_step 187, bjsSmallPrefixQ_value187]
  norm_num

private theorem bjsSmallPrefixQ_value189 : bjsSmallPrefixQ 189 = ((10408867916382550633331528920459565913027063402071390584941986323453055203 : ℚ)/5397346292805549782720214077673687806275517530364350655459511599582614290) := by
  rw [bjsSmallPrefixQ_step 188, bjsSmallPrefixQ_value188]
  norm_num

private theorem bjsSmallPrefixQ_value190 : bjsSmallPrefixQ 190 = ((10408867916382550633331528920459565913027063402071390584941986323453055203 : ℚ)/5397346292805549782720214077673687806275517530364350655459511599582614290) := by
  rw [bjsSmallPrefixQ_step 189, bjsSmallPrefixQ_value189]
  norm_num

private theorem bjsSmallPrefixQ_value191 : bjsSmallPrefixQ 191 = ((1993491118321872720749042237885450777194444627325999952379378899379116158063 : ℚ)/1030893141925860008499560888835674370998623848299590975192766715520279329390) := by
  rw [bjsSmallPrefixQ_step 190, bjsSmallPrefixQ_value190]
  norm_num

private theorem bjsSmallPrefixQ_value192 : bjsSmallPrefixQ 192 = ((1993491118321872720749042237885450777194444627325999952379378899379116158063 : ℚ)/1030893141925860008499560888835674370998623848299590975192766715520279329390) := by
  rw [bjsSmallPrefixQ_step 191, bjsSmallPrefixQ_value191]
  norm_num

private theorem bjsSmallPrefixQ_value193 : bjsSmallPrefixQ 193 = ((385774678978047295113064712800727674369526436922217581784412894295689697835549 : ℚ)/198962376391690981640415251545285153602734402721821058212203976095413910572270) := by
  rw [bjsSmallPrefixQ_step 192, bjsSmallPrefixQ_value192]
  norm_num

private theorem bjsSmallPrefixQ_value194 : bjsSmallPrefixQ 194 = ((385774678978047295113064712800727674369526436922217581784412894295689697835549 : ℚ)/198962376391690981640415251545285153602734402721821058212203976095413910572270) := by
  rw [bjsSmallPrefixQ_step 193, bjsSmallPrefixQ_value193]
  norm_num

private theorem bjsSmallPrefixQ_value195 : bjsSmallPrefixQ 195 = ((385774678978047295113064712800727674369526436922217581784412894295689697835549 : ℚ)/198962376391690981640415251545285153602734402721821058212203976095413910572270) := by
  rw [bjsSmallPrefixQ_step 194, bjsSmallPrefixQ_value194]
  norm_num

private theorem bjsSmallPrefixQ_value196 : bjsSmallPrefixQ 196 = ((385774678978047295113064712800727674369526436922217581784412894295689697835549 : ℚ)/198962376391690981640415251545285153602734402721821058212203976095413910572270) := by
  rw [bjsSmallPrefixQ_step 195, bjsSmallPrefixQ_value195]
  norm_num

private theorem bjsSmallPrefixQ_value197 : bjsSmallPrefixQ 197 = ((76196574135067008118914163673288637004399442476398684669741544152346284384175423 : ℚ)/39195588149163123383161804554421175259738677336198748467804183290796540382737190) := by
  rw [bjsSmallPrefixQ_step 196, bjsSmallPrefixQ_value196]
  norm_num

private theorem bjsSmallPrefixQ_value198 : bjsSmallPrefixQ 198 = ((76196574135067008118914163673288637004399442476398684669741544152346284384175423 : ℚ)/39195588149163123383161804554421175259738677336198748467804183290796540382737190) := by
  rw [bjsSmallPrefixQ_step 197, bjsSmallPrefixQ_value197]
  norm_num

private theorem bjsSmallPrefixQ_value199 : bjsSmallPrefixQ 199 = ((15202313841027497739047080375538859939135227730139536997746371469607707132833646367 : ℚ)/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) := by
  rw [bjsSmallPrefixQ_step 198, bjsSmallPrefixQ_value198]
  norm_num

private theorem bjsSmallPrefixQ_value200 : bjsSmallPrefixQ 200 = ((15202313841027497739047080375538859939135227730139536997746371469607707132833646367 : ℚ)/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) := by
  rw [bjsSmallPrefixQ_step 199, bjsSmallPrefixQ_value199]
  norm_num

private theorem bjsSmallPrefixQ_value201 : bjsSmallPrefixQ 201 = ((15202313841027497739047080375538859939135227730139536997746371469607707132833646367 : ℚ)/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) := by
  rw [bjsSmallPrefixQ_step 200, bjsSmallPrefixQ_value200]
  norm_num

private theorem bjsSmallPrefixQ_value202 : bjsSmallPrefixQ 202 = ((15202313841027497739047080375538859939135227730139536997746371469607707132833646367 : ℚ)/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) := by
  rw [bjsSmallPrefixQ_step 201, bjsSmallPrefixQ_value201]
  norm_num

private theorem bjsSmallPrefixQ_value203 : bjsSmallPrefixQ 203 = ((15202313841027497739047080375538859939135227730139536997746371469607707132833646367 : ℚ)/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) := by
  rw [bjsSmallPrefixQ_step 202, bjsSmallPrefixQ_value202]
  norm_num

private theorem bjsSmallPrefixQ_value204 : bjsSmallPrefixQ 204 = ((15202313841027497739047080375538859939135227730139536997746371469607707132833646367 : ℚ)/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) := by
  rw [bjsSmallPrefixQ_step 203, bjsSmallPrefixQ_value203]
  norm_num

private theorem bjsSmallPrefixQ_value205 : bjsSmallPrefixQ 205 = ((15202313841027497739047080375538859939135227730139536997746371469607707132833646367 : ℚ)/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) := by
  rw [bjsSmallPrefixQ_step 204, bjsSmallPrefixQ_value204]
  norm_num

private theorem bjsSmallPrefixQ_value206 : bjsSmallPrefixQ 206 = ((15202313841027497739047080375538859939135227730139536997746371469607707132833646367 : ℚ)/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) := by
  rw [bjsSmallPrefixQ_step 205, bjsSmallPrefixQ_value205]
  norm_num

private theorem bjsSmallPrefixQ_value207 : bjsSmallPrefixQ 207 = ((15202313841027497739047080375538859939135227730139536997746371469607707132833646367 : ℚ)/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) := by
  rw [bjsSmallPrefixQ_step 206, bjsSmallPrefixQ_value206]
  norm_num

private theorem bjsSmallPrefixQ_value208 : bjsSmallPrefixQ 208 = ((15202313841027497739047080375538859939135227730139536997746371469607707132833646367 : ℚ)/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) := by
  rw [bjsSmallPrefixQ_step 207, bjsSmallPrefixQ_value207]
  norm_num

private theorem bjsSmallPrefixQ_value209 : bjsSmallPrefixQ 209 = ((15202313841027497739047080375538859939135227730139536997746371469607707132833646367 : ℚ)/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) := by
  rw [bjsSmallPrefixQ_step 208, bjsSmallPrefixQ_value208]
  norm_num

private theorem bjsSmallPrefixQ_value210 : bjsSmallPrefixQ 210 = ((15202313841027497739047080375538859939135227730139536997746371469607707132833646367 : ℚ)/7799922041683461553249199106329813876687996789903550945093032474868511536164700810) := by
  rw [bjsSmallPrefixQ_step 209, bjsSmallPrefixQ_value209]
  norm_num

private theorem bjsSmallPrefixQ_value211 : bjsSmallPrefixQ 211 = ((3215488142498485484492183158345029261034221047849345857469577412562094716564064084247 : ℚ)/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) := by
  rw [bjsSmallPrefixQ_step 210, bjsSmallPrefixQ_value210]
  norm_num

private theorem bjsSmallPrefixQ_value212 : bjsSmallPrefixQ 212 = ((3215488142498485484492183158345029261034221047849345857469577412562094716564064084247 : ℚ)/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) := by
  rw [bjsSmallPrefixQ_step 211, bjsSmallPrefixQ_value211]
  norm_num

private theorem bjsSmallPrefixQ_value213 : bjsSmallPrefixQ 213 = ((3215488142498485484492183158345029261034221047849345857469577412562094716564064084247 : ℚ)/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) := by
  rw [bjsSmallPrefixQ_step 212, bjsSmallPrefixQ_value212]
  norm_num

private theorem bjsSmallPrefixQ_value214 : bjsSmallPrefixQ 214 = ((3215488142498485484492183158345029261034221047849345857469577412562094716564064084247 : ℚ)/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) := by
  rw [bjsSmallPrefixQ_step 213, bjsSmallPrefixQ_value213]
  norm_num

private theorem bjsSmallPrefixQ_value215 : bjsSmallPrefixQ 215 = ((3215488142498485484492183158345029261034221047849345857469577412562094716564064084247 : ℚ)/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) := by
  rw [bjsSmallPrefixQ_step 214, bjsSmallPrefixQ_value214]
  norm_num

private theorem bjsSmallPrefixQ_value216 : bjsSmallPrefixQ 216 = ((3215488142498485484492183158345029261034221047849345857469577412562094716564064084247 : ℚ)/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) := by
  rw [bjsSmallPrefixQ_step 215, bjsSmallPrefixQ_value215]
  norm_num

private theorem bjsSmallPrefixQ_value217 : bjsSmallPrefixQ 217 = ((3215488142498485484492183158345029261034221047849345857469577412562094716564064084247 : ℚ)/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) := by
  rw [bjsSmallPrefixQ_step 216, bjsSmallPrefixQ_value216]
  norm_num

private theorem bjsSmallPrefixQ_value218 : bjsSmallPrefixQ 218 = ((3215488142498485484492183158345029261034221047849345857469577412562094716564064084247 : ℚ)/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) := by
  rw [bjsSmallPrefixQ_step 217, bjsSmallPrefixQ_value217]
  norm_num

private theorem bjsSmallPrefixQ_value219 : bjsSmallPrefixQ 219 = ((3215488142498485484492183158345029261034221047849345857469577412562094716564064084247 : ℚ)/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) := by
  rw [bjsSmallPrefixQ_step 218, bjsSmallPrefixQ_value218]
  norm_num

private theorem bjsSmallPrefixQ_value220 : bjsSmallPrefixQ 220 = ((3215488142498485484492183158345029261034221047849345857469577412562094716564064084247 : ℚ)/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) := by
  rw [bjsSmallPrefixQ_step 219, bjsSmallPrefixQ_value219]
  norm_num

private theorem bjsSmallPrefixQ_value221 : bjsSmallPrefixQ 221 = ((3215488142498485484492183158345029261034221047849345857469577412562094716564064084247 : ℚ)/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) := by
  rw [bjsSmallPrefixQ_step 220, bjsSmallPrefixQ_value220]
  norm_num

private theorem bjsSmallPrefixQ_value222 : bjsSmallPrefixQ 222 = ((3215488142498485484492183158345029261034221047849345857469577412562094716564064084247 : ℚ)/1645783550795210387735581011435590727981167322669649249414629852197255934130751870910) := by
  rw [bjsSmallPrefixQ_step 221, bjsSmallPrefixQ_value221]
  norm_num

private theorem bjsSmallPrefixQ_value223 : bjsSmallPrefixQ 223 = ((718699639327957473429492425322377115938612460993073775465130392853544377727917042657991 : ℚ)/367009731827331916465034565550136732339800312955331782619462457039988073311157667212930) := by
  rw [bjsSmallPrefixQ_step 222, bjsSmallPrefixQ_value222]
  norm_num

private theorem bjsSmallPrefixQ_value224 : bjsSmallPrefixQ 224 = ((718699639327957473429492425322377115938612460993073775465130392853544377727917042657991 : ℚ)/367009731827331916465034565550136732339800312955331782619462457039988073311157667212930) := by
  rw [bjsSmallPrefixQ_step 223, bjsSmallPrefixQ_value223]
  norm_num

private theorem bjsSmallPrefixQ_value225 : bjsSmallPrefixQ 225 = ((718699639327957473429492425322377115938612460993073775465130392853544377727917042657991 : ℚ)/367009731827331916465034565550136732339800312955331782619462457039988073311157667212930) := by
  rw [bjsSmallPrefixQ_step 224, bjsSmallPrefixQ_value224]
  norm_num

private theorem bjsSmallPrefixQ_value226 : bjsSmallPrefixQ 226 = ((718699639327957473429492425322377115938612460993073775465130392853544377727917042657991 : ℚ)/367009731827331916465034565550136732339800312955331782619462457039988073311157667212930) := by
  rw [bjsSmallPrefixQ_step 225, bjsSmallPrefixQ_value225]
  norm_num

private theorem bjsSmallPrefixQ_value227 : bjsSmallPrefixQ 227 = ((163511827859273678384959815113729742050404828958383078813204061634794561817548326350576887 : ℚ)/83311209124804345037562846379881038241134671040860314654617977748077292641632790457335110) := by
  rw [bjsSmallPrefixQ_step 226, bjsSmallPrefixQ_value226]
  norm_num

private theorem bjsSmallPrefixQ_value228 : bjsSmallPrefixQ 228 = ((163511827859273678384959815113729742050404828958383078813204061634794561817548326350576887 : ℚ)/83311209124804345037562846379881038241134671040860314654617977748077292641632790457335110) := by
  rw [bjsSmallPrefixQ_step 227, bjsSmallPrefixQ_value227]
  norm_num

private theorem bjsSmallPrefixQ_value229 : bjsSmallPrefixQ 229 = ((37527519788898476695193360507423991967783840502510585362878348092116031948860199524739442233 : ℚ)/19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190) := by
  rw [bjsSmallPrefixQ_step 228, bjsSmallPrefixQ_value228]
  norm_num

private theorem bjsSmallPrefixQ_value230 : bjsSmallPrefixQ 230 = ((37527519788898476695193360507423991967783840502510585362878348092116031948860199524739442233 : ℚ)/19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190) := by
  rw [bjsSmallPrefixQ_step 229, bjsSmallPrefixQ_value229]
  norm_num

private theorem bjsSmallPrefixQ_value231 : bjsSmallPrefixQ 231 = ((37527519788898476695193360507423991967783840502510585362878348092116031948860199524739442233 : ℚ)/19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190) := by
  rw [bjsSmallPrefixQ_step 230, bjsSmallPrefixQ_value230]
  norm_num

private theorem bjsSmallPrefixQ_value232 : bjsSmallPrefixQ 232 = ((37527519788898476695193360507423991967783840502510585362878348092116031948860199524739442233 : ℚ)/19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190) := by
  rw [bjsSmallPrefixQ_step 231, bjsSmallPrefixQ_value231]
  norm_num

private theorem bjsSmallPrefixQ_value233 : bjsSmallPrefixQ 233 = ((8762990377702925264993654890050782886250854676753323401606562622367345144099360398279019780479 : ℚ)/4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270) := by
  rw [bjsSmallPrefixQ_step 232, bjsSmallPrefixQ_value232]
  norm_num

private theorem bjsSmallPrefixQ_value234 : bjsSmallPrefixQ 234 = ((8762990377702925264993654890050782886250854676753323401606562622367345144099360398279019780479 : ℚ)/4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270) := by
  rw [bjsSmallPrefixQ_step 233, bjsSmallPrefixQ_value233]
  norm_num

private theorem bjsSmallPrefixQ_value235 : bjsSmallPrefixQ 235 = ((8762990377702925264993654890050782886250854676753323401606562622367345144099360398279019780479 : ℚ)/4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270) := by
  rw [bjsSmallPrefixQ_step 234, bjsSmallPrefixQ_value234]
  norm_num

private theorem bjsSmallPrefixQ_value236 : bjsSmallPrefixQ 236 = ((8762990377702925264993654890050782886250854676753323401606562622367345144099360398279019780479 : ℚ)/4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270) := by
  rw [bjsSmallPrefixQ_step 235, bjsSmallPrefixQ_value235]
  norm_num

private theorem bjsSmallPrefixQ_value237 : bjsSmallPrefixQ 237 = ((8762990377702925264993654890050782886250854676753323401606562622367345144099360398279019780479 : ℚ)/4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270) := by
  rw [bjsSmallPrefixQ_step 236, bjsSmallPrefixQ_value236]
  norm_num

private theorem bjsSmallPrefixQ_value238 : bjsSmallPrefixQ 238 = ((8762990377702925264993654890050782886250854676753323401606562622367345144099360398279019780479 : ℚ)/4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270) := by
  rw [bjsSmallPrefixQ_step 237, bjsSmallPrefixQ_value237]
  norm_num

private theorem bjsSmallPrefixQ_value239 : bjsSmallPrefixQ 239 = ((2098799936456271323771652759516428422371386490386771476792994918184499649543226735989117756998751 : ℚ)/1062411448280052319722448549835623701226301211611796930357321893850294264731624591303255041960530) := by
  rw [bjsSmallPrefixQ_step 238, bjsSmallPrefixQ_value238]
  norm_num

private theorem bjsSmallPrefixQ_value240 : bjsSmallPrefixQ 240 = ((2098799936456271323771652759516428422371386490386771476792994918184499649543226735989117756998751 : ℚ)/1062411448280052319722448549835623701226301211611796930357321893850294264731624591303255041960530) := by
  rw [bjsSmallPrefixQ_step 239, bjsSmallPrefixQ_value239]
  norm_num

private theorem bjsSmallPrefixQ_value241 : bjsSmallPrefixQ 241 = ((506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521 : ℚ)/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) := by
  rw [bjsSmallPrefixQ_step 240, bjsSmallPrefixQ_value240]
  norm_num

private theorem bjsSmallPrefixQ_value242 : bjsSmallPrefixQ 242 = ((506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521 : ℚ)/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) := by
  rw [bjsSmallPrefixQ_step 241, bjsSmallPrefixQ_value241]
  norm_num

private theorem bjsSmallPrefixQ_value243 : bjsSmallPrefixQ 243 = ((506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521 : ℚ)/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) := by
  rw [bjsSmallPrefixQ_step 242, bjsSmallPrefixQ_value242]
  norm_num

private theorem bjsSmallPrefixQ_value244 : bjsSmallPrefixQ 244 = ((506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521 : ℚ)/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) := by
  rw [bjsSmallPrefixQ_step 243, bjsSmallPrefixQ_value243]
  norm_num

private theorem bjsSmallPrefixQ_value245 : bjsSmallPrefixQ 245 = ((506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521 : ℚ)/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) := by
  rw [bjsSmallPrefixQ_step 244, bjsSmallPrefixQ_value244]
  norm_num

private theorem bjsSmallPrefixQ_value246 : bjsSmallPrefixQ 246 = ((506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521 : ℚ)/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) := by
  rw [bjsSmallPrefixQ_step 245, bjsSmallPrefixQ_value245]
  norm_num

private theorem bjsSmallPrefixQ_value247 : bjsSmallPrefixQ 247 = ((506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521 : ℚ)/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) := by
  rw [bjsSmallPrefixQ_step 246, bjsSmallPrefixQ_value246]
  norm_num

private theorem bjsSmallPrefixQ_value248 : bjsSmallPrefixQ 248 = ((506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521 : ℚ)/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) := by
  rw [bjsSmallPrefixQ_step 247, bjsSmallPrefixQ_value247]
  norm_num

private theorem bjsSmallPrefixQ_value249 : bjsSmallPrefixQ 249 = ((506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521 : ℚ)/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) := by
  rw [bjsSmallPrefixQ_step 248, bjsSmallPrefixQ_value248]
  norm_num

private theorem bjsSmallPrefixQ_value250 : bjsSmallPrefixQ 250 = ((506873196134241441348690763593294873492730445394823722837469097176314709804649267964680634478659521 : ℚ)/256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730) := by
  rw [bjsSmallPrefixQ_step 249, bjsSmallPrefixQ_value249]
  norm_num

private theorem bjsSmallPrefixQ_value251 : bjsSmallPrefixQ 251 = ((127481213388730094387574491762427398558670880386099197492420857967672913078767287785638923719256027501 : ℚ)/64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230) := by
  rw [bjsSmallPrefixQ_step 250, bjsSmallPrefixQ_value250]
  norm_num

private theorem bjsSmallPrefixQ_value252 : bjsSmallPrefixQ 252 = ((127481213388730094387574491762427398558670880386099197492420857967672913078767287785638923719256027501 : ℚ)/64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230) := by
  rw [bjsSmallPrefixQ_step 251, bjsSmallPrefixQ_value251]
  norm_num

private theorem bjsSmallPrefixQ_value253 : bjsSmallPrefixQ 253 = ((127481213388730094387574491762427398558670880386099197492420857967672913078767287785638923719256027501 : ℚ)/64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230) := by
  rw [bjsSmallPrefixQ_step 252, bjsSmallPrefixQ_value252]
  norm_num

private theorem bjsSmallPrefixQ_value254 : bjsSmallPrefixQ 254 = ((127481213388730094387574491762427398558670880386099197492420857967672913078767287785638923719256027501 : ℚ)/64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230) := by
  rw [bjsSmallPrefixQ_step 253, bjsSmallPrefixQ_value253]
  norm_num

private theorem bjsSmallPrefixQ_value255 : bjsSmallPrefixQ 255 = ((127481213388730094387574491762427398558670880386099197492420857967672913078767287785638923719256027501 : ℚ)/64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230) := by
  rw [bjsSmallPrefixQ_step 254, bjsSmallPrefixQ_value254]
  norm_num

private theorem bjsSmallPrefixQ_value256 : bjsSmallPrefixQ 256 = ((127481213388730094387574491762427398558670880386099197492420857967672913078767287785638923719256027501 : ℚ)/64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230) := by
  rw [bjsSmallPrefixQ_step 255, bjsSmallPrefixQ_value255]
  norm_num

private theorem bjsSmallPrefixQ_value257 : bjsSmallPrefixQ 257 = ((32826938171821542902478975018171948142889296445819102963666405256372836811611073664061728596592033487987 : ℚ)/16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110) := by
  rw [bjsSmallPrefixQ_step 256, bjsSmallPrefixQ_value256]
  norm_num

private theorem bjsSmallPrefixQ_value258 : bjsSmallPrefixQ 258 = ((32826938171821542902478975018171948142889296445819102963666405256372836811611073664061728596592033487987 : ℚ)/16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110) := by
  rw [bjsSmallPrefixQ_step 257, bjsSmallPrefixQ_value257]
  norm_num

private theorem bjsSmallPrefixQ_value259 : bjsSmallPrefixQ 259 = ((32826938171821542902478975018171948142889296445819102963666405256372836811611073664061728596592033487987 : ℚ)/16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110) := by
  rw [bjsSmallPrefixQ_step 258, bjsSmallPrefixQ_value258]
  norm_num

private theorem bjsSmallPrefixQ_value260 : bjsSmallPrefixQ 260 = ((32826938171821542902478975018171948142889296445819102963666405256372836811611073664061728596592033487987 : ℚ)/16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110) := by
  rw [bjsSmallPrefixQ_step 259, bjsSmallPrefixQ_value259]
  norm_num

private theorem bjsSmallPrefixQ_value261 : bjsSmallPrefixQ 261 = ((32826938171821542902478975018171948142889296445819102963666405256372836811611073664061728596592033487987 : ℚ)/16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110) := by
  rw [bjsSmallPrefixQ_step 260, bjsSmallPrefixQ_value260]
  norm_num

private theorem bjsSmallPrefixQ_value262 : bjsSmallPrefixQ 262 = ((32826938171821542902478975018171948142889296445819102963666405256372836811611073664061728596592033487987 : ℚ)/16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110) := by
  rw [bjsSmallPrefixQ_step 261, bjsSmallPrefixQ_value261]
  norm_num

private theorem bjsSmallPrefixQ_value263 : bjsSmallPrefixQ 263 = ((8650001186234968305084159403032845786900781173204467645929625485407046906098257714358433597494716053339691 : ℚ)/4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930) := by
  rw [bjsSmallPrefixQ_step 262, bjsSmallPrefixQ_value262]
  norm_num

private theorem bjsSmallPrefixQ_value264 : bjsSmallPrefixQ 264 = ((8650001186234968305084159403032845786900781173204467645929625485407046906098257714358433597494716053339691 : ℚ)/4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930) := by
  rw [bjsSmallPrefixQ_step 263, bjsSmallPrefixQ_value263]
  norm_num

private theorem bjsSmallPrefixQ_value265 : bjsSmallPrefixQ 265 = ((8650001186234968305084159403032845786900781173204467645929625485407046906098257714358433597494716053339691 : ℚ)/4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930) := by
  rw [bjsSmallPrefixQ_step 264, bjsSmallPrefixQ_value264]
  norm_num

private theorem bjsSmallPrefixQ_value266 : bjsSmallPrefixQ 266 = ((8650001186234968305084159403032845786900781173204467645929625485407046906098257714358433597494716053339691 : ℚ)/4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930) := by
  rw [bjsSmallPrefixQ_step 265, bjsSmallPrefixQ_value265]
  norm_num

private theorem bjsSmallPrefixQ_value267 : bjsSmallPrefixQ 267 = ((8650001186234968305084159403032845786900781173204467645929625485407046906098257714358433597494716053339691 : ℚ)/4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930) := by
  rw [bjsSmallPrefixQ_step 266, bjsSmallPrefixQ_value266]
  norm_num

private theorem bjsSmallPrefixQ_value268 : bjsSmallPrefixQ 268 = ((8650001186234968305084159403032845786900781173204467645929625485407046906098257714358433597494716053339691 : ℚ)/4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930) := by
  rw [bjsSmallPrefixQ_step 267, bjsSmallPrefixQ_value267]
  norm_num

private theorem bjsSmallPrefixQ_value269 : bjsSmallPrefixQ 269 = ((2331194144670278837283204579381538477535705838283915254740719173058496204621946749769200968569514576046142809 : ℚ)/1168489079156465704987173290774096471177444024124720198139827803196157871127649219224446996884272620699035170) := by
  rw [bjsSmallPrefixQ_step 268, bjsSmallPrefixQ_value268]
  norm_num

private theorem bjsSmallPrefixQ_value270 : bjsSmallPrefixQ 270 = ((2331194144670278837283204579381538477535705838283915254740719173058496204621946749769200968569514576046142809 : ℚ)/1168489079156465704987173290774096471177444024124720198139827803196157871127649219224446996884272620699035170) := by
  rw [bjsSmallPrefixQ_step 269, bjsSmallPrefixQ_value269]
  norm_num

private theorem bjsSmallPrefixQ_value271 : bjsSmallPrefixQ 271 = ((632922102284802030608735614303171023883353726199065754232874723702048629323675218406677909479222722729203736409 : ℚ)/316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070) := by
  rw [bjsSmallPrefixQ_step 270, bjsSmallPrefixQ_value270]
  norm_num

private theorem bjsSmallPrefixQ_value272 : bjsSmallPrefixQ 272 = ((632922102284802030608735614303171023883353726199065754232874723702048629323675218406677909479222722729203736409 : ℚ)/316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070) := by
  rw [bjsSmallPrefixQ_step 271, bjsSmallPrefixQ_value271]
  norm_num

private theorem bjsSmallPrefixQ_value273 : bjsSmallPrefixQ 273 = ((632922102284802030608735614303171023883353726199065754232874723702048629323675218406677909479222722729203736409 : ℚ)/316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070) := by
  rw [bjsSmallPrefixQ_step 272, bjsSmallPrefixQ_value272]
  norm_num

private theorem bjsSmallPrefixQ_value274 : bjsSmallPrefixQ 274 = ((632922102284802030608735614303171023883353726199065754232874723702048629323675218406677909479222722729203736409 : ℚ)/316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070) := by
  rw [bjsSmallPrefixQ_step 273, bjsSmallPrefixQ_value273]
  norm_num

private theorem bjsSmallPrefixQ_value275 : bjsSmallPrefixQ 275 = ((632922102284802030608735614303171023883353726199065754232874723702048629323675218406677909479222722729203736409 : ℚ)/316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070) := by
  rw [bjsSmallPrefixQ_step 274, bjsSmallPrefixQ_value274]
  norm_num

private theorem bjsSmallPrefixQ_value276 : bjsSmallPrefixQ 276 = ((632922102284802030608735614303171023883353726199065754232874723702048629323675218406677909479222722729203736409 : ℚ)/316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070) := by
  rw [bjsSmallPrefixQ_step 275, bjsSmallPrefixQ_value275]
  norm_num

private theorem bjsSmallPrefixQ_value277 : bjsSmallPrefixQ 277 = ((175636082873341564684671289123778153759378069487679013096202191800133629105733628437059606061900332076198873516363 : ℚ)/87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390) := by
  rw [bjsSmallPrefixQ_step 276, bjsSmallPrefixQ_value276]
  norm_num

private theorem bjsSmallPrefixQ_value278 : bjsSmallPrefixQ 278 = ((175636082873341564684671289123778153759378069487679013096202191800133629105733628437059606061900332076198873516363 : ℚ)/87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390) := by
  rw [bjsSmallPrefixQ_step 277, bjsSmallPrefixQ_value277]
  norm_num

private theorem bjsSmallPrefixQ_value279 : bjsSmallPrefixQ 279 = ((175636082873341564684671289123778153759378069487679013096202191800133629105733628437059606061900332076198873516363 : ℚ)/87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390) := by
  rw [bjsSmallPrefixQ_step 278, bjsSmallPrefixQ_value278]
  norm_num

private theorem bjsSmallPrefixQ_value280 : bjsSmallPrefixQ 280 = ((175636082873341564684671289123778153759378069487679013096202191800133629105733628437059606061900332076198873516363 : ℚ)/87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390) := by
  rw [bjsSmallPrefixQ_step 279, bjsSmallPrefixQ_value279]
  norm_num

private theorem bjsSmallPrefixQ_value281 : bjsSmallPrefixQ 281 = ((49441454257114018087468904381200200306187114716596773051146578349540075761623088834753270866109105006229897931204393 : ℚ)/24647906487115793512432470614609487044327490547070674282967249490409801198254927547005559122946385681862066942895590) := by
  rw [bjsSmallPrefixQ_step 280, bjsSmallPrefixQ_value280]
  norm_num

private theorem bjsSmallPrefixQ_value282 : bjsSmallPrefixQ 282 = ((49441454257114018087468904381200200306187114716596773051146578349540075761623088834753270866109105006229897931204393 : ℚ)/24647906487115793512432470614609487044327490547070674282967249490409801198254927547005559122946385681862066942895590) := by
  rw [bjsSmallPrefixQ_step 281, bjsSmallPrefixQ_value281]
  norm_num

private theorem bjsSmallPrefixQ_value283 : bjsSmallPrefixQ 283 = ((14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809 : ℚ)/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) := by
  rw [bjsSmallPrefixQ_step 282, bjsSmallPrefixQ_value282]
  norm_num

private theorem bjsSmallPrefixQ_value284 : bjsSmallPrefixQ 284 = ((14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809 : ℚ)/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) := by
  rw [bjsSmallPrefixQ_step 283, bjsSmallPrefixQ_value283]
  norm_num

private theorem bjsSmallPrefixQ_value285 : bjsSmallPrefixQ 285 = ((14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809 : ℚ)/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) := by
  rw [bjsSmallPrefixQ_step 284, bjsSmallPrefixQ_value284]
  norm_num

private theorem bjsSmallPrefixQ_value286 : bjsSmallPrefixQ 286 = ((14016579461250382912266132410494266173695280955343957447757448922410251241737589067782181214231823102444923181473738809 : ℚ)/6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970) := by
  rw [bjsSmallPrefixQ_step 285, bjsSmallPrefixQ_value285]
  norm_num

private theorem bjsSmallPrefixRow002 : bjsSmallPrefixCertificate 2 := by
  change (2 : ℚ)^1 ≤ (2 : ℚ)+1 ∧
    bjsLogUpper ((2 : ℚ)+1) 1 ≤ ((10988 : ℚ)/10000) ∧
    (2 : ℚ)^0 ≤ ((10988 : ℚ)/10000) ∧ bjsLogUpper ((10988 : ℚ)/10000) 0 ≤ ((944 : ℚ)/10000) ∧
    1 ≤ ((10988 : ℚ)/10000) ∧ ((944 : ℚ)/10000)+27/100-1/(2*((10988 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 2
  rw [bjsSmallPrefixQ_value002]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow003 : bjsSmallPrefixCertificate 3 := by
  change (2 : ℚ)^2 ≤ (3 : ℚ)+1 ∧
    bjsLogUpper ((3 : ℚ)+1) 2 ≤ ((13864 : ℚ)/10000) ∧
    (2 : ℚ)^0 ≤ ((13864 : ℚ)/10000) ∧ bjsLogUpper ((13864 : ℚ)/10000) 0 ≤ ((3269 : ℚ)/10000) ∧
    1 ≤ ((13864 : ℚ)/10000) ∧ ((3269 : ℚ)/10000)+27/100-1/(2*((13864 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 3
  rw [bjsSmallPrefixQ_value003]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow004 : bjsSmallPrefixCertificate 4 := by
  change (2 : ℚ)^2 ≤ (4 : ℚ)+1 ∧
    bjsLogUpper ((4 : ℚ)+1) 2 ≤ ((16096 : ℚ)/10000) ∧
    (2 : ℚ)^0 ≤ ((16096 : ℚ)/10000) ∧ bjsLogUpper ((16096 : ℚ)/10000) 0 ≤ ((4761 : ℚ)/10000) ∧
    1 ≤ ((16096 : ℚ)/10000) ∧ ((4761 : ℚ)/10000)+27/100-1/(2*((16096 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 4
  rw [bjsSmallPrefixQ_value004]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow005 : bjsSmallPrefixCertificate 5 := by
  change (2 : ℚ)^2 ≤ (5 : ℚ)+1 ∧
    bjsLogUpper ((5 : ℚ)+1) 2 ≤ ((17919 : ℚ)/10000) ∧
    (2 : ℚ)^0 ≤ ((17919 : ℚ)/10000) ∧ bjsLogUpper ((17919 : ℚ)/10000) 0 ≤ ((5834 : ℚ)/10000) ∧
    1 ≤ ((17919 : ℚ)/10000) ∧ ((5834 : ℚ)/10000)+27/100-1/(2*((17919 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 5
  rw [bjsSmallPrefixQ_value005]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow006 : bjsSmallPrefixCertificate 6 := by
  change (2 : ℚ)^2 ≤ (6 : ℚ)+1 ∧
    bjsLogUpper ((6 : ℚ)+1) 2 ≤ ((19461 : ℚ)/10000) ∧
    (2 : ℚ)^0 ≤ ((19461 : ℚ)/10000) ∧ bjsLogUpper ((19461 : ℚ)/10000) 0 ≤ ((6660 : ℚ)/10000) ∧
    1 ≤ ((19461 : ℚ)/10000) ∧ ((6660 : ℚ)/10000)+27/100-1/(2*((19461 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 6
  rw [bjsSmallPrefixQ_value006]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow007 : bjsSmallPrefixCertificate 7 := by
  change (2 : ℚ)^3 ≤ (7 : ℚ)+1 ∧
    bjsLogUpper ((7 : ℚ)+1) 3 ≤ ((20796 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((20796 : ℚ)/10000) ∧ bjsLogUpper ((20796 : ℚ)/10000) 1 ≤ ((7323 : ℚ)/10000) ∧
    1 ≤ ((20796 : ℚ)/10000) ∧ ((7323 : ℚ)/10000)+27/100-1/(2*((20796 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 7
  rw [bjsSmallPrefixQ_value007]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow008 : bjsSmallPrefixCertificate 8 := by
  change (2 : ℚ)^3 ≤ (8 : ℚ)+1 ∧
    bjsLogUpper ((8 : ℚ)+1) 3 ≤ ((21974 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((21974 : ℚ)/10000) ∧ bjsLogUpper ((21974 : ℚ)/10000) 1 ≤ ((7874 : ℚ)/10000) ∧
    1 ≤ ((21974 : ℚ)/10000) ∧ ((7874 : ℚ)/10000)+27/100-1/(2*((21974 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 8
  rw [bjsSmallPrefixQ_value008]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow009 : bjsSmallPrefixCertificate 9 := by
  change (2 : ℚ)^3 ≤ (9 : ℚ)+1 ∧
    bjsLogUpper ((9 : ℚ)+1) 3 ≤ ((23027 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((23027 : ℚ)/10000) ∧ bjsLogUpper ((23027 : ℚ)/10000) 1 ≤ ((8342 : ℚ)/10000) ∧
    1 ≤ ((23027 : ℚ)/10000) ∧ ((8342 : ℚ)/10000)+27/100-1/(2*((23027 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 9
  rw [bjsSmallPrefixQ_value009]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow010 : bjsSmallPrefixCertificate 10 := by
  change (2 : ℚ)^3 ≤ (10 : ℚ)+1 ∧
    bjsLogUpper ((10 : ℚ)+1) 3 ≤ ((23980 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((23980 : ℚ)/10000) ∧ bjsLogUpper ((23980 : ℚ)/10000) 1 ≤ ((8748 : ℚ)/10000) ∧
    1 ≤ ((23980 : ℚ)/10000) ∧ ((8748 : ℚ)/10000)+27/100-1/(2*((23980 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 10
  rw [bjsSmallPrefixQ_value010]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow011 : bjsSmallPrefixCertificate 11 := by
  change (2 : ℚ)^3 ≤ (11 : ℚ)+1 ∧
    bjsLogUpper ((11 : ℚ)+1) 3 ≤ ((24851 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((24851 : ℚ)/10000) ∧ bjsLogUpper ((24851 : ℚ)/10000) 1 ≤ ((9105 : ℚ)/10000) ∧
    1 ≤ ((24851 : ℚ)/10000) ∧ ((9105 : ℚ)/10000)+27/100-1/(2*((24851 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 11
  rw [bjsSmallPrefixQ_value011]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow012 : bjsSmallPrefixCertificate 12 := by
  change (2 : ℚ)^3 ≤ (12 : ℚ)+1 ∧
    bjsLogUpper ((12 : ℚ)+1) 3 ≤ ((25651 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((25651 : ℚ)/10000) ∧ bjsLogUpper ((25651 : ℚ)/10000) 1 ≤ ((9421 : ℚ)/10000) ∧
    1 ≤ ((25651 : ℚ)/10000) ∧ ((9421 : ℚ)/10000)+27/100-1/(2*((25651 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 12
  rw [bjsSmallPrefixQ_value012]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow013 : bjsSmallPrefixCertificate 13 := by
  change (2 : ℚ)^3 ≤ (13 : ℚ)+1 ∧
    bjsLogUpper ((13 : ℚ)+1) 3 ≤ ((26392 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((26392 : ℚ)/10000) ∧ bjsLogUpper ((26392 : ℚ)/10000) 1 ≤ ((9706 : ℚ)/10000) ∧
    1 ≤ ((26392 : ℚ)/10000) ∧ ((9706 : ℚ)/10000)+27/100-1/(2*((26392 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 13
  rw [bjsSmallPrefixQ_value013]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow014 : bjsSmallPrefixCertificate 14 := by
  change (2 : ℚ)^3 ≤ (14 : ℚ)+1 ∧
    bjsLogUpper ((14 : ℚ)+1) 3 ≤ ((27082 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((27082 : ℚ)/10000) ∧ bjsLogUpper ((27082 : ℚ)/10000) 1 ≤ ((9964 : ℚ)/10000) ∧
    1 ≤ ((27082 : ℚ)/10000) ∧ ((9964 : ℚ)/10000)+27/100-1/(2*((27082 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 14
  rw [bjsSmallPrefixQ_value014]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow015 : bjsSmallPrefixCertificate 15 := by
  change (2 : ℚ)^4 ≤ (15 : ℚ)+1 ∧
    bjsLogUpper ((15 : ℚ)+1) 4 ≤ ((27727 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((27727 : ℚ)/10000) ∧ bjsLogUpper ((27727 : ℚ)/10000) 1 ≤ ((10200 : ℚ)/10000) ∧
    1 ≤ ((27727 : ℚ)/10000) ∧ ((10200 : ℚ)/10000)+27/100-1/(2*((27727 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 15
  rw [bjsSmallPrefixQ_value015]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow016 : bjsSmallPrefixCertificate 16 := by
  change (2 : ℚ)^4 ≤ (16 : ℚ)+1 ∧
    bjsLogUpper ((16 : ℚ)+1) 4 ≤ ((28334 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((28334 : ℚ)/10000) ∧ bjsLogUpper ((28334 : ℚ)/10000) 1 ≤ ((10416 : ℚ)/10000) ∧
    1 ≤ ((28334 : ℚ)/10000) ∧ ((10416 : ℚ)/10000)+27/100-1/(2*((28334 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 16
  rw [bjsSmallPrefixQ_value016]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow017 : bjsSmallPrefixCertificate 17 := by
  change (2 : ℚ)^4 ≤ (17 : ℚ)+1 ∧
    bjsLogUpper ((17 : ℚ)+1) 4 ≤ ((28905 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((28905 : ℚ)/10000) ∧ bjsLogUpper ((28905 : ℚ)/10000) 1 ≤ ((10616 : ℚ)/10000) ∧
    1 ≤ ((28905 : ℚ)/10000) ∧ ((10616 : ℚ)/10000)+27/100-1/(2*((28905 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 17
  rw [bjsSmallPrefixQ_value017]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow018 : bjsSmallPrefixCertificate 18 := by
  change (2 : ℚ)^4 ≤ (18 : ℚ)+1 ∧
    bjsLogUpper ((18 : ℚ)+1) 4 ≤ ((29446 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((29446 : ℚ)/10000) ∧ bjsLogUpper ((29446 : ℚ)/10000) 1 ≤ ((10801 : ℚ)/10000) ∧
    1 ≤ ((29446 : ℚ)/10000) ∧ ((10801 : ℚ)/10000)+27/100-1/(2*((29446 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 18
  rw [bjsSmallPrefixQ_value018]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow019 : bjsSmallPrefixCertificate 19 := by
  change (2 : ℚ)^4 ≤ (19 : ℚ)+1 ∧
    bjsLogUpper ((19 : ℚ)+1) 4 ≤ ((29959 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((29959 : ℚ)/10000) ∧ bjsLogUpper ((29959 : ℚ)/10000) 1 ≤ ((10974 : ℚ)/10000) ∧
    1 ≤ ((29959 : ℚ)/10000) ∧ ((10974 : ℚ)/10000)+27/100-1/(2*((29959 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 19
  rw [bjsSmallPrefixQ_value019]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow020 : bjsSmallPrefixCertificate 20 := by
  change (2 : ℚ)^4 ≤ (20 : ℚ)+1 ∧
    bjsLogUpper ((20 : ℚ)+1) 4 ≤ ((30447 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((30447 : ℚ)/10000) ∧ bjsLogUpper ((30447 : ℚ)/10000) 1 ≤ ((11136 : ℚ)/10000) ∧
    1 ≤ ((30447 : ℚ)/10000) ∧ ((11136 : ℚ)/10000)+27/100-1/(2*((30447 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 20
  rw [bjsSmallPrefixQ_value020]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow021 : bjsSmallPrefixCertificate 21 := by
  change (2 : ℚ)^4 ≤ (21 : ℚ)+1 ∧
    bjsLogUpper ((21 : ℚ)+1) 4 ≤ ((30912 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((30912 : ℚ)/10000) ∧ bjsLogUpper ((30912 : ℚ)/10000) 1 ≤ ((11287 : ℚ)/10000) ∧
    1 ≤ ((30912 : ℚ)/10000) ∧ ((11287 : ℚ)/10000)+27/100-1/(2*((30912 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 21
  rw [bjsSmallPrefixQ_value021]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow022 : bjsSmallPrefixCertificate 22 := by
  change (2 : ℚ)^4 ≤ (22 : ℚ)+1 ∧
    bjsLogUpper ((22 : ℚ)+1) 4 ≤ ((31356 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((31356 : ℚ)/10000) ∧ bjsLogUpper ((31356 : ℚ)/10000) 1 ≤ ((11430 : ℚ)/10000) ∧
    1 ≤ ((31356 : ℚ)/10000) ∧ ((11430 : ℚ)/10000)+27/100-1/(2*((31356 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 22
  rw [bjsSmallPrefixQ_value022]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow023 : bjsSmallPrefixCertificate 23 := by
  change (2 : ℚ)^4 ≤ (23 : ℚ)+1 ∧
    bjsLogUpper ((23 : ℚ)+1) 4 ≤ ((31782 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((31782 : ℚ)/10000) ∧ bjsLogUpper ((31782 : ℚ)/10000) 1 ≤ ((11565 : ℚ)/10000) ∧
    1 ≤ ((31782 : ℚ)/10000) ∧ ((11565 : ℚ)/10000)+27/100-1/(2*((31782 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 23
  rw [bjsSmallPrefixQ_value023]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow024 : bjsSmallPrefixCertificate 24 := by
  change (2 : ℚ)^4 ≤ (24 : ℚ)+1 ∧
    bjsLogUpper ((24 : ℚ)+1) 4 ≤ ((32190 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((32190 : ℚ)/10000) ∧ bjsLogUpper ((32190 : ℚ)/10000) 1 ≤ ((11692 : ℚ)/10000) ∧
    1 ≤ ((32190 : ℚ)/10000) ∧ ((11692 : ℚ)/10000)+27/100-1/(2*((32190 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 24
  rw [bjsSmallPrefixQ_value024]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow025 : bjsSmallPrefixCertificate 25 := by
  change (2 : ℚ)^4 ≤ (25 : ℚ)+1 ∧
    bjsLogUpper ((25 : ℚ)+1) 4 ≤ ((32582 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((32582 : ℚ)/10000) ∧ bjsLogUpper ((32582 : ℚ)/10000) 1 ≤ ((11813 : ℚ)/10000) ∧
    1 ≤ ((32582 : ℚ)/10000) ∧ ((11813 : ℚ)/10000)+27/100-1/(2*((32582 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 25
  rw [bjsSmallPrefixQ_value025]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow026 : bjsSmallPrefixCertificate 26 := by
  change (2 : ℚ)^4 ≤ (26 : ℚ)+1 ∧
    bjsLogUpper ((26 : ℚ)+1) 4 ≤ ((32960 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((32960 : ℚ)/10000) ∧ bjsLogUpper ((32960 : ℚ)/10000) 1 ≤ ((11929 : ℚ)/10000) ∧
    1 ≤ ((32960 : ℚ)/10000) ∧ ((11929 : ℚ)/10000)+27/100-1/(2*((32960 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 26
  rw [bjsSmallPrefixQ_value026]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow027 : bjsSmallPrefixCertificate 27 := by
  change (2 : ℚ)^4 ≤ (27 : ℚ)+1 ∧
    bjsLogUpper ((27 : ℚ)+1) 4 ≤ ((33324 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((33324 : ℚ)/10000) ∧ bjsLogUpper ((33324 : ℚ)/10000) 1 ≤ ((12038 : ℚ)/10000) ∧
    1 ≤ ((33324 : ℚ)/10000) ∧ ((12038 : ℚ)/10000)+27/100-1/(2*((33324 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 27
  rw [bjsSmallPrefixQ_value027]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow028 : bjsSmallPrefixCertificate 28 := by
  change (2 : ℚ)^4 ≤ (28 : ℚ)+1 ∧
    bjsLogUpper ((28 : ℚ)+1) 4 ≤ ((33674 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((33674 : ℚ)/10000) ∧ bjsLogUpper ((33674 : ℚ)/10000) 1 ≤ ((12143 : ℚ)/10000) ∧
    1 ≤ ((33674 : ℚ)/10000) ∧ ((12143 : ℚ)/10000)+27/100-1/(2*((33674 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 28
  rw [bjsSmallPrefixQ_value028]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow029 : bjsSmallPrefixCertificate 29 := by
  change (2 : ℚ)^4 ≤ (29 : ℚ)+1 ∧
    bjsLogUpper ((29 : ℚ)+1) 4 ≤ ((34013 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((34013 : ℚ)/10000) ∧ bjsLogUpper ((34013 : ℚ)/10000) 1 ≤ ((12243 : ℚ)/10000) ∧
    1 ≤ ((34013 : ℚ)/10000) ∧ ((12243 : ℚ)/10000)+27/100-1/(2*((34013 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 29
  rw [bjsSmallPrefixQ_value029]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow030 : bjsSmallPrefixCertificate 30 := by
  change (2 : ℚ)^4 ≤ (30 : ℚ)+1 ∧
    bjsLogUpper ((30 : ℚ)+1) 4 ≤ ((34341 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((34341 : ℚ)/10000) ∧ bjsLogUpper ((34341 : ℚ)/10000) 1 ≤ ((12339 : ℚ)/10000) ∧
    1 ≤ ((34341 : ℚ)/10000) ∧ ((12339 : ℚ)/10000)+27/100-1/(2*((34341 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 30
  rw [bjsSmallPrefixQ_value030]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow031 : bjsSmallPrefixCertificate 31 := by
  change (2 : ℚ)^5 ≤ (31 : ℚ)+1 ∧
    bjsLogUpper ((31 : ℚ)+1) 5 ≤ ((34659 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((34659 : ℚ)/10000) ∧ bjsLogUpper ((34659 : ℚ)/10000) 1 ≤ ((12431 : ℚ)/10000) ∧
    1 ≤ ((34659 : ℚ)/10000) ∧ ((12431 : ℚ)/10000)+27/100-1/(2*((34659 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 31
  rw [bjsSmallPrefixQ_value031]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow032 : bjsSmallPrefixCertificate 32 := by
  change (2 : ℚ)^5 ≤ (32 : ℚ)+1 ∧
    bjsLogUpper ((32 : ℚ)+1) 5 ≤ ((34967 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((34967 : ℚ)/10000) ∧ bjsLogUpper ((34967 : ℚ)/10000) 1 ≤ ((12520 : ℚ)/10000) ∧
    1 ≤ ((34967 : ℚ)/10000) ∧ ((12520 : ℚ)/10000)+27/100-1/(2*((34967 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 32
  rw [bjsSmallPrefixQ_value032]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow033 : bjsSmallPrefixCertificate 33 := by
  change (2 : ℚ)^5 ≤ (33 : ℚ)+1 ∧
    bjsLogUpper ((33 : ℚ)+1) 5 ≤ ((35265 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((35265 : ℚ)/10000) ∧ bjsLogUpper ((35265 : ℚ)/10000) 1 ≤ ((12605 : ℚ)/10000) ∧
    1 ≤ ((35265 : ℚ)/10000) ∧ ((12605 : ℚ)/10000)+27/100-1/(2*((35265 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 33
  rw [bjsSmallPrefixQ_value033]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow034 : bjsSmallPrefixCertificate 34 := by
  change (2 : ℚ)^5 ≤ (34 : ℚ)+1 ∧
    bjsLogUpper ((34 : ℚ)+1) 5 ≤ ((35555 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((35555 : ℚ)/10000) ∧ bjsLogUpper ((35555 : ℚ)/10000) 1 ≤ ((12686 : ℚ)/10000) ∧
    1 ≤ ((35555 : ℚ)/10000) ∧ ((12686 : ℚ)/10000)+27/100-1/(2*((35555 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 34
  rw [bjsSmallPrefixQ_value034]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow035 : bjsSmallPrefixCertificate 35 := by
  change (2 : ℚ)^5 ≤ (35 : ℚ)+1 ∧
    bjsLogUpper ((35 : ℚ)+1) 5 ≤ ((35837 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((35837 : ℚ)/10000) ∧ bjsLogUpper ((35837 : ℚ)/10000) 1 ≤ ((12765 : ℚ)/10000) ∧
    1 ≤ ((35837 : ℚ)/10000) ∧ ((12765 : ℚ)/10000)+27/100-1/(2*((35837 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 35
  rw [bjsSmallPrefixQ_value035]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow036 : bjsSmallPrefixCertificate 36 := by
  change (2 : ℚ)^5 ≤ (36 : ℚ)+1 ∧
    bjsLogUpper ((36 : ℚ)+1) 5 ≤ ((36111 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((36111 : ℚ)/10000) ∧ bjsLogUpper ((36111 : ℚ)/10000) 1 ≤ ((12842 : ℚ)/10000) ∧
    1 ≤ ((36111 : ℚ)/10000) ∧ ((12842 : ℚ)/10000)+27/100-1/(2*((36111 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 36
  rw [bjsSmallPrefixQ_value036]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow037 : bjsSmallPrefixCertificate 37 := by
  change (2 : ℚ)^5 ≤ (37 : ℚ)+1 ∧
    bjsLogUpper ((37 : ℚ)+1) 5 ≤ ((36377 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((36377 : ℚ)/10000) ∧ bjsLogUpper ((36377 : ℚ)/10000) 1 ≤ ((12915 : ℚ)/10000) ∧
    1 ≤ ((36377 : ℚ)/10000) ∧ ((12915 : ℚ)/10000)+27/100-1/(2*((36377 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 37
  rw [bjsSmallPrefixQ_value037]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow038 : bjsSmallPrefixCertificate 38 := by
  change (2 : ℚ)^5 ≤ (38 : ℚ)+1 ∧
    bjsLogUpper ((38 : ℚ)+1) 5 ≤ ((36637 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((36637 : ℚ)/10000) ∧ bjsLogUpper ((36637 : ℚ)/10000) 1 ≤ ((12986 : ℚ)/10000) ∧
    1 ≤ ((36637 : ℚ)/10000) ∧ ((12986 : ℚ)/10000)+27/100-1/(2*((36637 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 38
  rw [bjsSmallPrefixQ_value038]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow039 : bjsSmallPrefixCertificate 39 := by
  change (2 : ℚ)^5 ≤ (39 : ℚ)+1 ∧
    bjsLogUpper ((39 : ℚ)+1) 5 ≤ ((36890 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((36890 : ℚ)/10000) ∧ bjsLogUpper ((36890 : ℚ)/10000) 1 ≤ ((13055 : ℚ)/10000) ∧
    1 ≤ ((36890 : ℚ)/10000) ∧ ((13055 : ℚ)/10000)+27/100-1/(2*((36890 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 39
  rw [bjsSmallPrefixQ_value039]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow040 : bjsSmallPrefixCertificate 40 := by
  change (2 : ℚ)^5 ≤ (40 : ℚ)+1 ∧
    bjsLogUpper ((40 : ℚ)+1) 5 ≤ ((37137 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((37137 : ℚ)/10000) ∧ bjsLogUpper ((37137 : ℚ)/10000) 1 ≤ ((13122 : ℚ)/10000) ∧
    1 ≤ ((37137 : ℚ)/10000) ∧ ((13122 : ℚ)/10000)+27/100-1/(2*((37137 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 40
  rw [bjsSmallPrefixQ_value040]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow041 : bjsSmallPrefixCertificate 41 := by
  change (2 : ℚ)^5 ≤ (41 : ℚ)+1 ∧
    bjsLogUpper ((41 : ℚ)+1) 5 ≤ ((37378 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((37378 : ℚ)/10000) ∧ bjsLogUpper ((37378 : ℚ)/10000) 1 ≤ ((13186 : ℚ)/10000) ∧
    1 ≤ ((37378 : ℚ)/10000) ∧ ((13186 : ℚ)/10000)+27/100-1/(2*((37378 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 41
  rw [bjsSmallPrefixQ_value041]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow042 : bjsSmallPrefixCertificate 42 := by
  change (2 : ℚ)^5 ≤ (42 : ℚ)+1 ∧
    bjsLogUpper ((42 : ℚ)+1) 5 ≤ ((37614 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((37614 : ℚ)/10000) ∧ bjsLogUpper ((37614 : ℚ)/10000) 1 ≤ ((13249 : ℚ)/10000) ∧
    1 ≤ ((37614 : ℚ)/10000) ∧ ((13249 : ℚ)/10000)+27/100-1/(2*((37614 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 42
  rw [bjsSmallPrefixQ_value042]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow043 : bjsSmallPrefixCertificate 43 := by
  change (2 : ℚ)^5 ≤ (43 : ℚ)+1 ∧
    bjsLogUpper ((43 : ℚ)+1) 5 ≤ ((37843 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((37843 : ℚ)/10000) ∧ bjsLogUpper ((37843 : ℚ)/10000) 1 ≤ ((13310 : ℚ)/10000) ∧
    1 ≤ ((37843 : ℚ)/10000) ∧ ((13310 : ℚ)/10000)+27/100-1/(2*((37843 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 43
  rw [bjsSmallPrefixQ_value043]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow044 : bjsSmallPrefixCertificate 44 := by
  change (2 : ℚ)^5 ≤ (44 : ℚ)+1 ∧
    bjsLogUpper ((44 : ℚ)+1) 5 ≤ ((38068 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((38068 : ℚ)/10000) ∧ bjsLogUpper ((38068 : ℚ)/10000) 1 ≤ ((13369 : ℚ)/10000) ∧
    1 ≤ ((38068 : ℚ)/10000) ∧ ((13369 : ℚ)/10000)+27/100-1/(2*((38068 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 44
  rw [bjsSmallPrefixQ_value044]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow045 : bjsSmallPrefixCertificate 45 := by
  change (2 : ℚ)^5 ≤ (45 : ℚ)+1 ∧
    bjsLogUpper ((45 : ℚ)+1) 5 ≤ ((38288 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((38288 : ℚ)/10000) ∧ bjsLogUpper ((38288 : ℚ)/10000) 1 ≤ ((13427 : ℚ)/10000) ∧
    1 ≤ ((38288 : ℚ)/10000) ∧ ((13427 : ℚ)/10000)+27/100-1/(2*((38288 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 45
  rw [bjsSmallPrefixQ_value045]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow046 : bjsSmallPrefixCertificate 46 := by
  change (2 : ℚ)^5 ≤ (46 : ℚ)+1 ∧
    bjsLogUpper ((46 : ℚ)+1) 5 ≤ ((38503 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((38503 : ℚ)/10000) ∧ bjsLogUpper ((38503 : ℚ)/10000) 1 ≤ ((13483 : ℚ)/10000) ∧
    1 ≤ ((38503 : ℚ)/10000) ∧ ((13483 : ℚ)/10000)+27/100-1/(2*((38503 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 46
  rw [bjsSmallPrefixQ_value046]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow047 : bjsSmallPrefixCertificate 47 := by
  change (2 : ℚ)^5 ≤ (47 : ℚ)+1 ∧
    bjsLogUpper ((47 : ℚ)+1) 5 ≤ ((38714 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((38714 : ℚ)/10000) ∧ bjsLogUpper ((38714 : ℚ)/10000) 1 ≤ ((13538 : ℚ)/10000) ∧
    1 ≤ ((38714 : ℚ)/10000) ∧ ((13538 : ℚ)/10000)+27/100-1/(2*((38714 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 47
  rw [bjsSmallPrefixQ_value047]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow048 : bjsSmallPrefixCertificate 48 := by
  change (2 : ℚ)^5 ≤ (48 : ℚ)+1 ∧
    bjsLogUpper ((48 : ℚ)+1) 5 ≤ ((38920 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((38920 : ℚ)/10000) ∧ bjsLogUpper ((38920 : ℚ)/10000) 1 ≤ ((13591 : ℚ)/10000) ∧
    1 ≤ ((38920 : ℚ)/10000) ∧ ((13591 : ℚ)/10000)+27/100-1/(2*((38920 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 48
  rw [bjsSmallPrefixQ_value048]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow049 : bjsSmallPrefixCertificate 49 := by
  change (2 : ℚ)^5 ≤ (49 : ℚ)+1 ∧
    bjsLogUpper ((49 : ℚ)+1) 5 ≤ ((39122 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((39122 : ℚ)/10000) ∧ bjsLogUpper ((39122 : ℚ)/10000) 1 ≤ ((13642 : ℚ)/10000) ∧
    1 ≤ ((39122 : ℚ)/10000) ∧ ((13642 : ℚ)/10000)+27/100-1/(2*((39122 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 49
  rw [bjsSmallPrefixQ_value049]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow050 : bjsSmallPrefixCertificate 50 := by
  change (2 : ℚ)^5 ≤ (50 : ℚ)+1 ∧
    bjsLogUpper ((50 : ℚ)+1) 5 ≤ ((39320 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((39320 : ℚ)/10000) ∧ bjsLogUpper ((39320 : ℚ)/10000) 1 ≤ ((13693 : ℚ)/10000) ∧
    1 ≤ ((39320 : ℚ)/10000) ∧ ((13693 : ℚ)/10000)+27/100-1/(2*((39320 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 50
  rw [bjsSmallPrefixQ_value050]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow051 : bjsSmallPrefixCertificate 51 := by
  change (2 : ℚ)^5 ≤ (51 : ℚ)+1 ∧
    bjsLogUpper ((51 : ℚ)+1) 5 ≤ ((39514 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((39514 : ℚ)/10000) ∧ bjsLogUpper ((39514 : ℚ)/10000) 1 ≤ ((13742 : ℚ)/10000) ∧
    1 ≤ ((39514 : ℚ)/10000) ∧ ((13742 : ℚ)/10000)+27/100-1/(2*((39514 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 51
  rw [bjsSmallPrefixQ_value051]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow052 : bjsSmallPrefixCertificate 52 := by
  change (2 : ℚ)^5 ≤ (52 : ℚ)+1 ∧
    bjsLogUpper ((52 : ℚ)+1) 5 ≤ ((39704 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((39704 : ℚ)/10000) ∧ bjsLogUpper ((39704 : ℚ)/10000) 1 ≤ ((13790 : ℚ)/10000) ∧
    1 ≤ ((39704 : ℚ)/10000) ∧ ((13790 : ℚ)/10000)+27/100-1/(2*((39704 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 52
  rw [bjsSmallPrefixQ_value052]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow053 : bjsSmallPrefixCertificate 53 := by
  change (2 : ℚ)^5 ≤ (53 : ℚ)+1 ∧
    bjsLogUpper ((53 : ℚ)+1) 5 ≤ ((39891 : ℚ)/10000) ∧
    (2 : ℚ)^1 ≤ ((39891 : ℚ)/10000) ∧ bjsLogUpper ((39891 : ℚ)/10000) 1 ≤ ((13837 : ℚ)/10000) ∧
    1 ≤ ((39891 : ℚ)/10000) ∧ ((13837 : ℚ)/10000)+27/100-1/(2*((39891 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 53
  rw [bjsSmallPrefixQ_value053]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow054 : bjsSmallPrefixCertificate 54 := by
  change (2 : ℚ)^5 ≤ (54 : ℚ)+1 ∧
    bjsLogUpper ((54 : ℚ)+1) 5 ≤ ((40075 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((40075 : ℚ)/10000) ∧ bjsLogUpper ((40075 : ℚ)/10000) 2 ≤ ((13883 : ℚ)/10000) ∧
    1 ≤ ((40075 : ℚ)/10000) ∧ ((13883 : ℚ)/10000)+27/100-1/(2*((40075 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 54
  rw [bjsSmallPrefixQ_value054]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow055 : bjsSmallPrefixCertificate 55 := by
  change (2 : ℚ)^5 ≤ (55 : ℚ)+1 ∧
    bjsLogUpper ((55 : ℚ)+1) 5 ≤ ((40255 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((40255 : ℚ)/10000) ∧ bjsLogUpper ((40255 : ℚ)/10000) 2 ≤ ((13928 : ℚ)/10000) ∧
    1 ≤ ((40255 : ℚ)/10000) ∧ ((13928 : ℚ)/10000)+27/100-1/(2*((40255 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 55
  rw [bjsSmallPrefixQ_value055]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow056 : bjsSmallPrefixCertificate 56 := by
  change (2 : ℚ)^5 ≤ (56 : ℚ)+1 ∧
    bjsLogUpper ((56 : ℚ)+1) 5 ≤ ((40432 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((40432 : ℚ)/10000) ∧ bjsLogUpper ((40432 : ℚ)/10000) 2 ≤ ((13972 : ℚ)/10000) ∧
    1 ≤ ((40432 : ℚ)/10000) ∧ ((13972 : ℚ)/10000)+27/100-1/(2*((40432 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 56
  rw [bjsSmallPrefixQ_value056]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow057 : bjsSmallPrefixCertificate 57 := by
  change (2 : ℚ)^5 ≤ (57 : ℚ)+1 ∧
    bjsLogUpper ((57 : ℚ)+1) 5 ≤ ((40606 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((40606 : ℚ)/10000) ∧ bjsLogUpper ((40606 : ℚ)/10000) 2 ≤ ((14015 : ℚ)/10000) ∧
    1 ≤ ((40606 : ℚ)/10000) ∧ ((14015 : ℚ)/10000)+27/100-1/(2*((40606 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 57
  rw [bjsSmallPrefixQ_value057]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow058 : bjsSmallPrefixCertificate 58 := by
  change (2 : ℚ)^5 ≤ (58 : ℚ)+1 ∧
    bjsLogUpper ((58 : ℚ)+1) 5 ≤ ((40777 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((40777 : ℚ)/10000) ∧ bjsLogUpper ((40777 : ℚ)/10000) 2 ≤ ((14057 : ℚ)/10000) ∧
    1 ≤ ((40777 : ℚ)/10000) ∧ ((14057 : ℚ)/10000)+27/100-1/(2*((40777 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 58
  rw [bjsSmallPrefixQ_value058]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow059 : bjsSmallPrefixCertificate 59 := by
  change (2 : ℚ)^5 ≤ (59 : ℚ)+1 ∧
    bjsLogUpper ((59 : ℚ)+1) 5 ≤ ((40945 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((40945 : ℚ)/10000) ∧ bjsLogUpper ((40945 : ℚ)/10000) 2 ≤ ((14098 : ℚ)/10000) ∧
    1 ≤ ((40945 : ℚ)/10000) ∧ ((14098 : ℚ)/10000)+27/100-1/(2*((40945 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 59
  rw [bjsSmallPrefixQ_value059]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow060 : bjsSmallPrefixCertificate 60 := by
  change (2 : ℚ)^5 ≤ (60 : ℚ)+1 ∧
    bjsLogUpper ((60 : ℚ)+1) 5 ≤ ((41110 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((41110 : ℚ)/10000) ∧ bjsLogUpper ((41110 : ℚ)/10000) 2 ≤ ((14138 : ℚ)/10000) ∧
    1 ≤ ((41110 : ℚ)/10000) ∧ ((14138 : ℚ)/10000)+27/100-1/(2*((41110 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 60
  rw [bjsSmallPrefixQ_value060]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow061 : bjsSmallPrefixCertificate 61 := by
  change (2 : ℚ)^5 ≤ (61 : ℚ)+1 ∧
    bjsLogUpper ((61 : ℚ)+1) 5 ≤ ((41273 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((41273 : ℚ)/10000) ∧ bjsLogUpper ((41273 : ℚ)/10000) 2 ≤ ((14178 : ℚ)/10000) ∧
    1 ≤ ((41273 : ℚ)/10000) ∧ ((14178 : ℚ)/10000)+27/100-1/(2*((41273 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 61
  rw [bjsSmallPrefixQ_value061]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow062 : bjsSmallPrefixCertificate 62 := by
  change (2 : ℚ)^5 ≤ (62 : ℚ)+1 ∧
    bjsLogUpper ((62 : ℚ)+1) 5 ≤ ((41433 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((41433 : ℚ)/10000) ∧ bjsLogUpper ((41433 : ℚ)/10000) 2 ≤ ((14216 : ℚ)/10000) ∧
    1 ≤ ((41433 : ℚ)/10000) ∧ ((14216 : ℚ)/10000)+27/100-1/(2*((41433 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 62
  rw [bjsSmallPrefixQ_value062]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow063 : bjsSmallPrefixCertificate 63 := by
  change (2 : ℚ)^6 ≤ (63 : ℚ)+1 ∧
    bjsLogUpper ((63 : ℚ)+1) 6 ≤ ((41590 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((41590 : ℚ)/10000) ∧ bjsLogUpper ((41590 : ℚ)/10000) 2 ≤ ((14254 : ℚ)/10000) ∧
    1 ≤ ((41590 : ℚ)/10000) ∧ ((14254 : ℚ)/10000)+27/100-1/(2*((41590 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 63
  rw [bjsSmallPrefixQ_value063]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow064 : bjsSmallPrefixCertificate 64 := by
  change (2 : ℚ)^6 ≤ (64 : ℚ)+1 ∧
    bjsLogUpper ((64 : ℚ)+1) 6 ≤ ((41745 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((41745 : ℚ)/10000) ∧ bjsLogUpper ((41745 : ℚ)/10000) 2 ≤ ((14291 : ℚ)/10000) ∧
    1 ≤ ((41745 : ℚ)/10000) ∧ ((14291 : ℚ)/10000)+27/100-1/(2*((41745 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 64
  rw [bjsSmallPrefixQ_value064]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow065 : bjsSmallPrefixCertificate 65 := by
  change (2 : ℚ)^6 ≤ (65 : ℚ)+1 ∧
    bjsLogUpper ((65 : ℚ)+1) 6 ≤ ((41898 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((41898 : ℚ)/10000) ∧ bjsLogUpper ((41898 : ℚ)/10000) 2 ≤ ((14328 : ℚ)/10000) ∧
    1 ≤ ((41898 : ℚ)/10000) ∧ ((14328 : ℚ)/10000)+27/100-1/(2*((41898 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 65
  rw [bjsSmallPrefixQ_value065]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow066 : bjsSmallPrefixCertificate 66 := by
  change (2 : ℚ)^6 ≤ (66 : ℚ)+1 ∧
    bjsLogUpper ((66 : ℚ)+1) 6 ≤ ((42048 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((42048 : ℚ)/10000) ∧ bjsLogUpper ((42048 : ℚ)/10000) 2 ≤ ((14364 : ℚ)/10000) ∧
    1 ≤ ((42048 : ℚ)/10000) ∧ ((14364 : ℚ)/10000)+27/100-1/(2*((42048 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 66
  rw [bjsSmallPrefixQ_value066]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow067 : bjsSmallPrefixCertificate 67 := by
  change (2 : ℚ)^6 ≤ (67 : ℚ)+1 ∧
    bjsLogUpper ((67 : ℚ)+1) 6 ≤ ((42197 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((42197 : ℚ)/10000) ∧ bjsLogUpper ((42197 : ℚ)/10000) 2 ≤ ((14399 : ℚ)/10000) ∧
    1 ≤ ((42197 : ℚ)/10000) ∧ ((14399 : ℚ)/10000)+27/100-1/(2*((42197 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 67
  rw [bjsSmallPrefixQ_value067]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow068 : bjsSmallPrefixCertificate 68 := by
  change (2 : ℚ)^6 ≤ (68 : ℚ)+1 ∧
    bjsLogUpper ((68 : ℚ)+1) 6 ≤ ((42343 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((42343 : ℚ)/10000) ∧ bjsLogUpper ((42343 : ℚ)/10000) 2 ≤ ((14434 : ℚ)/10000) ∧
    1 ≤ ((42343 : ℚ)/10000) ∧ ((14434 : ℚ)/10000)+27/100-1/(2*((42343 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 68
  rw [bjsSmallPrefixQ_value068]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow069 : bjsSmallPrefixCertificate 69 := by
  change (2 : ℚ)^6 ≤ (69 : ℚ)+1 ∧
    bjsLogUpper ((69 : ℚ)+1) 6 ≤ ((42486 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((42486 : ℚ)/10000) ∧ bjsLogUpper ((42486 : ℚ)/10000) 2 ≤ ((14467 : ℚ)/10000) ∧
    1 ≤ ((42486 : ℚ)/10000) ∧ ((14467 : ℚ)/10000)+27/100-1/(2*((42486 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 69
  rw [bjsSmallPrefixQ_value069]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow070 : bjsSmallPrefixCertificate 70 := by
  change (2 : ℚ)^6 ≤ (70 : ℚ)+1 ∧
    bjsLogUpper ((70 : ℚ)+1) 6 ≤ ((42628 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((42628 : ℚ)/10000) ∧ bjsLogUpper ((42628 : ℚ)/10000) 2 ≤ ((14501 : ℚ)/10000) ∧
    1 ≤ ((42628 : ℚ)/10000) ∧ ((14501 : ℚ)/10000)+27/100-1/(2*((42628 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 70
  rw [bjsSmallPrefixQ_value070]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow071 : bjsSmallPrefixCertificate 71 := by
  change (2 : ℚ)^6 ≤ (71 : ℚ)+1 ∧
    bjsLogUpper ((71 : ℚ)+1) 6 ≤ ((42768 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((42768 : ℚ)/10000) ∧ bjsLogUpper ((42768 : ℚ)/10000) 2 ≤ ((14534 : ℚ)/10000) ∧
    1 ≤ ((42768 : ℚ)/10000) ∧ ((14534 : ℚ)/10000)+27/100-1/(2*((42768 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 71
  rw [bjsSmallPrefixQ_value071]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow072 : bjsSmallPrefixCertificate 72 := by
  change (2 : ℚ)^6 ≤ (72 : ℚ)+1 ∧
    bjsLogUpper ((72 : ℚ)+1) 6 ≤ ((42906 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((42906 : ℚ)/10000) ∧ bjsLogUpper ((42906 : ℚ)/10000) 2 ≤ ((14566 : ℚ)/10000) ∧
    1 ≤ ((42906 : ℚ)/10000) ∧ ((14566 : ℚ)/10000)+27/100-1/(2*((42906 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 72
  rw [bjsSmallPrefixQ_value072]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow073 : bjsSmallPrefixCertificate 73 := by
  change (2 : ℚ)^6 ≤ (73 : ℚ)+1 ∧
    bjsLogUpper ((73 : ℚ)+1) 6 ≤ ((43042 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((43042 : ℚ)/10000) ∧ bjsLogUpper ((43042 : ℚ)/10000) 2 ≤ ((14597 : ℚ)/10000) ∧
    1 ≤ ((43042 : ℚ)/10000) ∧ ((14597 : ℚ)/10000)+27/100-1/(2*((43042 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 73
  rw [bjsSmallPrefixQ_value073]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow074 : bjsSmallPrefixCertificate 74 := by
  change (2 : ℚ)^6 ≤ (74 : ℚ)+1 ∧
    bjsLogUpper ((74 : ℚ)+1) 6 ≤ ((43176 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((43176 : ℚ)/10000) ∧ bjsLogUpper ((43176 : ℚ)/10000) 2 ≤ ((14628 : ℚ)/10000) ∧
    1 ≤ ((43176 : ℚ)/10000) ∧ ((14628 : ℚ)/10000)+27/100-1/(2*((43176 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 74
  rw [bjsSmallPrefixQ_value074]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow075 : bjsSmallPrefixCertificate 75 := by
  change (2 : ℚ)^6 ≤ (75 : ℚ)+1 ∧
    bjsLogUpper ((75 : ℚ)+1) 6 ≤ ((43309 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((43309 : ℚ)/10000) ∧ bjsLogUpper ((43309 : ℚ)/10000) 2 ≤ ((14659 : ℚ)/10000) ∧
    1 ≤ ((43309 : ℚ)/10000) ∧ ((14659 : ℚ)/10000)+27/100-1/(2*((43309 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 75
  rw [bjsSmallPrefixQ_value075]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow076 : bjsSmallPrefixCertificate 76 := by
  change (2 : ℚ)^6 ≤ (76 : ℚ)+1 ∧
    bjsLogUpper ((76 : ℚ)+1) 6 ≤ ((43440 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((43440 : ℚ)/10000) ∧ bjsLogUpper ((43440 : ℚ)/10000) 2 ≤ ((14689 : ℚ)/10000) ∧
    1 ≤ ((43440 : ℚ)/10000) ∧ ((14689 : ℚ)/10000)+27/100-1/(2*((43440 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 76
  rw [bjsSmallPrefixQ_value076]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow077 : bjsSmallPrefixCertificate 77 := by
  change (2 : ℚ)^6 ≤ (77 : ℚ)+1 ∧
    bjsLogUpper ((77 : ℚ)+1) 6 ≤ ((43569 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((43569 : ℚ)/10000) ∧ bjsLogUpper ((43569 : ℚ)/10000) 2 ≤ ((14719 : ℚ)/10000) ∧
    1 ≤ ((43569 : ℚ)/10000) ∧ ((14719 : ℚ)/10000)+27/100-1/(2*((43569 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 77
  rw [bjsSmallPrefixQ_value077]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow078 : bjsSmallPrefixCertificate 78 := by
  change (2 : ℚ)^6 ≤ (78 : ℚ)+1 ∧
    bjsLogUpper ((78 : ℚ)+1) 6 ≤ ((43696 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((43696 : ℚ)/10000) ∧ bjsLogUpper ((43696 : ℚ)/10000) 2 ≤ ((14748 : ℚ)/10000) ∧
    1 ≤ ((43696 : ℚ)/10000) ∧ ((14748 : ℚ)/10000)+27/100-1/(2*((43696 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 78
  rw [bjsSmallPrefixQ_value078]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow079 : bjsSmallPrefixCertificate 79 := by
  change (2 : ℚ)^6 ≤ (79 : ℚ)+1 ∧
    bjsLogUpper ((79 : ℚ)+1) 6 ≤ ((43822 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((43822 : ℚ)/10000) ∧ bjsLogUpper ((43822 : ℚ)/10000) 2 ≤ ((14777 : ℚ)/10000) ∧
    1 ≤ ((43822 : ℚ)/10000) ∧ ((14777 : ℚ)/10000)+27/100-1/(2*((43822 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 79
  rw [bjsSmallPrefixQ_value079]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow080 : bjsSmallPrefixCertificate 80 := by
  change (2 : ℚ)^6 ≤ (80 : ℚ)+1 ∧
    bjsLogUpper ((80 : ℚ)+1) 6 ≤ ((43946 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((43946 : ℚ)/10000) ∧ bjsLogUpper ((43946 : ℚ)/10000) 2 ≤ ((14805 : ℚ)/10000) ∧
    1 ≤ ((43946 : ℚ)/10000) ∧ ((14805 : ℚ)/10000)+27/100-1/(2*((43946 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 80
  rw [bjsSmallPrefixQ_value080]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow081 : bjsSmallPrefixCertificate 81 := by
  change (2 : ℚ)^6 ≤ (81 : ℚ)+1 ∧
    bjsLogUpper ((81 : ℚ)+1) 6 ≤ ((44069 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((44069 : ℚ)/10000) ∧ bjsLogUpper ((44069 : ℚ)/10000) 2 ≤ ((14833 : ℚ)/10000) ∧
    1 ≤ ((44069 : ℚ)/10000) ∧ ((14833 : ℚ)/10000)+27/100-1/(2*((44069 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 81
  rw [bjsSmallPrefixQ_value081]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow082 : bjsSmallPrefixCertificate 82 := by
  change (2 : ℚ)^6 ≤ (82 : ℚ)+1 ∧
    bjsLogUpper ((82 : ℚ)+1) 6 ≤ ((44190 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((44190 : ℚ)/10000) ∧ bjsLogUpper ((44190 : ℚ)/10000) 2 ≤ ((14861 : ℚ)/10000) ∧
    1 ≤ ((44190 : ℚ)/10000) ∧ ((14861 : ℚ)/10000)+27/100-1/(2*((44190 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 82
  rw [bjsSmallPrefixQ_value082]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow083 : bjsSmallPrefixCertificate 83 := by
  change (2 : ℚ)^6 ≤ (83 : ℚ)+1 ∧
    bjsLogUpper ((83 : ℚ)+1) 6 ≤ ((44310 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((44310 : ℚ)/10000) ∧ bjsLogUpper ((44310 : ℚ)/10000) 2 ≤ ((14888 : ℚ)/10000) ∧
    1 ≤ ((44310 : ℚ)/10000) ∧ ((14888 : ℚ)/10000)+27/100-1/(2*((44310 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 83
  rw [bjsSmallPrefixQ_value083]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow084 : bjsSmallPrefixCertificate 84 := by
  change (2 : ℚ)^6 ≤ (84 : ℚ)+1 ∧
    bjsLogUpper ((84 : ℚ)+1) 6 ≤ ((44428 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((44428 : ℚ)/10000) ∧ bjsLogUpper ((44428 : ℚ)/10000) 2 ≤ ((14914 : ℚ)/10000) ∧
    1 ≤ ((44428 : ℚ)/10000) ∧ ((14914 : ℚ)/10000)+27/100-1/(2*((44428 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 84
  rw [bjsSmallPrefixQ_value084]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow085 : bjsSmallPrefixCertificate 85 := by
  change (2 : ℚ)^6 ≤ (85 : ℚ)+1 ∧
    bjsLogUpper ((85 : ℚ)+1) 6 ≤ ((44545 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((44545 : ℚ)/10000) ∧ bjsLogUpper ((44545 : ℚ)/10000) 2 ≤ ((14941 : ℚ)/10000) ∧
    1 ≤ ((44545 : ℚ)/10000) ∧ ((14941 : ℚ)/10000)+27/100-1/(2*((44545 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 85
  rw [bjsSmallPrefixQ_value085]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow086 : bjsSmallPrefixCertificate 86 := by
  change (2 : ℚ)^6 ≤ (86 : ℚ)+1 ∧
    bjsLogUpper ((86 : ℚ)+1) 6 ≤ ((44661 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((44661 : ℚ)/10000) ∧ bjsLogUpper ((44661 : ℚ)/10000) 2 ≤ ((14967 : ℚ)/10000) ∧
    1 ≤ ((44661 : ℚ)/10000) ∧ ((14967 : ℚ)/10000)+27/100-1/(2*((44661 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 86
  rw [bjsSmallPrefixQ_value086]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow087 : bjsSmallPrefixCertificate 87 := by
  change (2 : ℚ)^6 ≤ (87 : ℚ)+1 ∧
    bjsLogUpper ((87 : ℚ)+1) 6 ≤ ((44775 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((44775 : ℚ)/10000) ∧ bjsLogUpper ((44775 : ℚ)/10000) 2 ≤ ((14992 : ℚ)/10000) ∧
    1 ≤ ((44775 : ℚ)/10000) ∧ ((14992 : ℚ)/10000)+27/100-1/(2*((44775 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 87
  rw [bjsSmallPrefixQ_value087]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow088 : bjsSmallPrefixCertificate 88 := by
  change (2 : ℚ)^6 ≤ (88 : ℚ)+1 ∧
    bjsLogUpper ((88 : ℚ)+1) 6 ≤ ((44888 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((44888 : ℚ)/10000) ∧ bjsLogUpper ((44888 : ℚ)/10000) 2 ≤ ((15017 : ℚ)/10000) ∧
    1 ≤ ((44888 : ℚ)/10000) ∧ ((15017 : ℚ)/10000)+27/100-1/(2*((44888 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 88
  rw [bjsSmallPrefixQ_value088]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow089 : bjsSmallPrefixCertificate 89 := by
  change (2 : ℚ)^6 ≤ (89 : ℚ)+1 ∧
    bjsLogUpper ((89 : ℚ)+1) 6 ≤ ((45000 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((45000 : ℚ)/10000) ∧ bjsLogUpper ((45000 : ℚ)/10000) 2 ≤ ((15042 : ℚ)/10000) ∧
    1 ≤ ((45000 : ℚ)/10000) ∧ ((15042 : ℚ)/10000)+27/100-1/(2*((45000 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 89
  rw [bjsSmallPrefixQ_value089]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow090 : bjsSmallPrefixCertificate 90 := by
  change (2 : ℚ)^6 ≤ (90 : ℚ)+1 ∧
    bjsLogUpper ((90 : ℚ)+1) 6 ≤ ((45110 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((45110 : ℚ)/10000) ∧ bjsLogUpper ((45110 : ℚ)/10000) 2 ≤ ((15067 : ℚ)/10000) ∧
    1 ≤ ((45110 : ℚ)/10000) ∧ ((15067 : ℚ)/10000)+27/100-1/(2*((45110 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 90
  rw [bjsSmallPrefixQ_value090]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow091 : bjsSmallPrefixCertificate 91 := by
  change (2 : ℚ)^6 ≤ (91 : ℚ)+1 ∧
    bjsLogUpper ((91 : ℚ)+1) 6 ≤ ((45219 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((45219 : ℚ)/10000) ∧ bjsLogUpper ((45219 : ℚ)/10000) 2 ≤ ((15091 : ℚ)/10000) ∧
    1 ≤ ((45219 : ℚ)/10000) ∧ ((15091 : ℚ)/10000)+27/100-1/(2*((45219 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 91
  rw [bjsSmallPrefixQ_value091]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow092 : bjsSmallPrefixCertificate 92 := by
  change (2 : ℚ)^6 ≤ (92 : ℚ)+1 ∧
    bjsLogUpper ((92 : ℚ)+1) 6 ≤ ((45327 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((45327 : ℚ)/10000) ∧ bjsLogUpper ((45327 : ℚ)/10000) 2 ≤ ((15115 : ℚ)/10000) ∧
    1 ≤ ((45327 : ℚ)/10000) ∧ ((15115 : ℚ)/10000)+27/100-1/(2*((45327 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 92
  rw [bjsSmallPrefixQ_value092]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow093 : bjsSmallPrefixCertificate 93 := by
  change (2 : ℚ)^6 ≤ (93 : ℚ)+1 ∧
    bjsLogUpper ((93 : ℚ)+1) 6 ≤ ((45434 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((45434 : ℚ)/10000) ∧ bjsLogUpper ((45434 : ℚ)/10000) 2 ≤ ((15138 : ℚ)/10000) ∧
    1 ≤ ((45434 : ℚ)/10000) ∧ ((15138 : ℚ)/10000)+27/100-1/(2*((45434 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 93
  rw [bjsSmallPrefixQ_value093]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow094 : bjsSmallPrefixCertificate 94 := by
  change (2 : ℚ)^6 ≤ (94 : ℚ)+1 ∧
    bjsLogUpper ((94 : ℚ)+1) 6 ≤ ((45540 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((45540 : ℚ)/10000) ∧ bjsLogUpper ((45540 : ℚ)/10000) 2 ≤ ((15162 : ℚ)/10000) ∧
    1 ≤ ((45540 : ℚ)/10000) ∧ ((15162 : ℚ)/10000)+27/100-1/(2*((45540 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 94
  rw [bjsSmallPrefixQ_value094]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow095 : bjsSmallPrefixCertificate 95 := by
  change (2 : ℚ)^6 ≤ (95 : ℚ)+1 ∧
    bjsLogUpper ((95 : ℚ)+1) 6 ≤ ((45645 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((45645 : ℚ)/10000) ∧ bjsLogUpper ((45645 : ℚ)/10000) 2 ≤ ((15185 : ℚ)/10000) ∧
    1 ≤ ((45645 : ℚ)/10000) ∧ ((15185 : ℚ)/10000)+27/100-1/(2*((45645 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 95
  rw [bjsSmallPrefixQ_value095]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow096 : bjsSmallPrefixCertificate 96 := by
  change (2 : ℚ)^6 ≤ (96 : ℚ)+1 ∧
    bjsLogUpper ((96 : ℚ)+1) 6 ≤ ((45749 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((45749 : ℚ)/10000) ∧ bjsLogUpper ((45749 : ℚ)/10000) 2 ≤ ((15207 : ℚ)/10000) ∧
    1 ≤ ((45749 : ℚ)/10000) ∧ ((15207 : ℚ)/10000)+27/100-1/(2*((45749 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 96
  rw [bjsSmallPrefixQ_value096]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow097 : bjsSmallPrefixCertificate 97 := by
  change (2 : ℚ)^6 ≤ (97 : ℚ)+1 ∧
    bjsLogUpper ((97 : ℚ)+1) 6 ≤ ((45851 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((45851 : ℚ)/10000) ∧ bjsLogUpper ((45851 : ℚ)/10000) 2 ≤ ((15230 : ℚ)/10000) ∧
    1 ≤ ((45851 : ℚ)/10000) ∧ ((15230 : ℚ)/10000)+27/100-1/(2*((45851 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 97
  rw [bjsSmallPrefixQ_value097]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow098 : bjsSmallPrefixCertificate 98 := by
  change (2 : ℚ)^6 ≤ (98 : ℚ)+1 ∧
    bjsLogUpper ((98 : ℚ)+1) 6 ≤ ((45953 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((45953 : ℚ)/10000) ∧ bjsLogUpper ((45953 : ℚ)/10000) 2 ≤ ((15252 : ℚ)/10000) ∧
    1 ≤ ((45953 : ℚ)/10000) ∧ ((15252 : ℚ)/10000)+27/100-1/(2*((45953 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 98
  rw [bjsSmallPrefixQ_value098]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow099 : bjsSmallPrefixCertificate 99 := by
  change (2 : ℚ)^6 ≤ (99 : ℚ)+1 ∧
    bjsLogUpper ((99 : ℚ)+1) 6 ≤ ((46053 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((46053 : ℚ)/10000) ∧ bjsLogUpper ((46053 : ℚ)/10000) 2 ≤ ((15274 : ℚ)/10000) ∧
    1 ≤ ((46053 : ℚ)/10000) ∧ ((15274 : ℚ)/10000)+27/100-1/(2*((46053 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 99
  rw [bjsSmallPrefixQ_value099]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow100 : bjsSmallPrefixCertificate 100 := by
  change (2 : ℚ)^6 ≤ (100 : ℚ)+1 ∧
    bjsLogUpper ((100 : ℚ)+1) 6 ≤ ((46153 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((46153 : ℚ)/10000) ∧ bjsLogUpper ((46153 : ℚ)/10000) 2 ≤ ((15295 : ℚ)/10000) ∧
    1 ≤ ((46153 : ℚ)/10000) ∧ ((15295 : ℚ)/10000)+27/100-1/(2*((46153 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 100
  rw [bjsSmallPrefixQ_value100]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow101 : bjsSmallPrefixCertificate 101 := by
  change (2 : ℚ)^6 ≤ (101 : ℚ)+1 ∧
    bjsLogUpper ((101 : ℚ)+1) 6 ≤ ((46251 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((46251 : ℚ)/10000) ∧ bjsLogUpper ((46251 : ℚ)/10000) 2 ≤ ((15316 : ℚ)/10000) ∧
    1 ≤ ((46251 : ℚ)/10000) ∧ ((15316 : ℚ)/10000)+27/100-1/(2*((46251 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 101
  rw [bjsSmallPrefixQ_value101]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow102 : bjsSmallPrefixCertificate 102 := by
  change (2 : ℚ)^6 ≤ (102 : ℚ)+1 ∧
    bjsLogUpper ((102 : ℚ)+1) 6 ≤ ((46349 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((46349 : ℚ)/10000) ∧ bjsLogUpper ((46349 : ℚ)/10000) 2 ≤ ((15338 : ℚ)/10000) ∧
    1 ≤ ((46349 : ℚ)/10000) ∧ ((15338 : ℚ)/10000)+27/100-1/(2*((46349 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 102
  rw [bjsSmallPrefixQ_value102]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow103 : bjsSmallPrefixCertificate 103 := by
  change (2 : ℚ)^6 ≤ (103 : ℚ)+1 ∧
    bjsLogUpper ((103 : ℚ)+1) 6 ≤ ((46445 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((46445 : ℚ)/10000) ∧ bjsLogUpper ((46445 : ℚ)/10000) 2 ≤ ((15358 : ℚ)/10000) ∧
    1 ≤ ((46445 : ℚ)/10000) ∧ ((15358 : ℚ)/10000)+27/100-1/(2*((46445 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 103
  rw [bjsSmallPrefixQ_value103]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow104 : bjsSmallPrefixCertificate 104 := by
  change (2 : ℚ)^6 ≤ (104 : ℚ)+1 ∧
    bjsLogUpper ((104 : ℚ)+1) 6 ≤ ((46541 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((46541 : ℚ)/10000) ∧ bjsLogUpper ((46541 : ℚ)/10000) 2 ≤ ((15379 : ℚ)/10000) ∧
    1 ≤ ((46541 : ℚ)/10000) ∧ ((15379 : ℚ)/10000)+27/100-1/(2*((46541 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 104
  rw [bjsSmallPrefixQ_value104]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow105 : bjsSmallPrefixCertificate 105 := by
  change (2 : ℚ)^6 ≤ (105 : ℚ)+1 ∧
    bjsLogUpper ((105 : ℚ)+1) 6 ≤ ((46636 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((46636 : ℚ)/10000) ∧ bjsLogUpper ((46636 : ℚ)/10000) 2 ≤ ((15399 : ℚ)/10000) ∧
    1 ≤ ((46636 : ℚ)/10000) ∧ ((15399 : ℚ)/10000)+27/100-1/(2*((46636 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 105
  rw [bjsSmallPrefixQ_value105]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow106 : bjsSmallPrefixCertificate 106 := by
  change (2 : ℚ)^6 ≤ (106 : ℚ)+1 ∧
    bjsLogUpper ((106 : ℚ)+1) 6 ≤ ((46730 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((46730 : ℚ)/10000) ∧ bjsLogUpper ((46730 : ℚ)/10000) 2 ≤ ((15420 : ℚ)/10000) ∧
    1 ≤ ((46730 : ℚ)/10000) ∧ ((15420 : ℚ)/10000)+27/100-1/(2*((46730 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 106
  rw [bjsSmallPrefixQ_value106]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow107 : bjsSmallPrefixCertificate 107 := by
  change (2 : ℚ)^6 ≤ (107 : ℚ)+1 ∧
    bjsLogUpper ((107 : ℚ)+1) 6 ≤ ((46823 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((46823 : ℚ)/10000) ∧ bjsLogUpper ((46823 : ℚ)/10000) 2 ≤ ((15439 : ℚ)/10000) ∧
    1 ≤ ((46823 : ℚ)/10000) ∧ ((15439 : ℚ)/10000)+27/100-1/(2*((46823 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 107
  rw [bjsSmallPrefixQ_value107]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow108 : bjsSmallPrefixCertificate 108 := by
  change (2 : ℚ)^6 ≤ (108 : ℚ)+1 ∧
    bjsLogUpper ((108 : ℚ)+1) 6 ≤ ((46915 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((46915 : ℚ)/10000) ∧ bjsLogUpper ((46915 : ℚ)/10000) 2 ≤ ((15459 : ℚ)/10000) ∧
    1 ≤ ((46915 : ℚ)/10000) ∧ ((15459 : ℚ)/10000)+27/100-1/(2*((46915 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 108
  rw [bjsSmallPrefixQ_value108]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow109 : bjsSmallPrefixCertificate 109 := by
  change (2 : ℚ)^6 ≤ (109 : ℚ)+1 ∧
    bjsLogUpper ((109 : ℚ)+1) 6 ≤ ((47006 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((47006 : ℚ)/10000) ∧ bjsLogUpper ((47006 : ℚ)/10000) 2 ≤ ((15478 : ℚ)/10000) ∧
    1 ≤ ((47006 : ℚ)/10000) ∧ ((15478 : ℚ)/10000)+27/100-1/(2*((47006 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 109
  rw [bjsSmallPrefixQ_value109]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow110 : bjsSmallPrefixCertificate 110 := by
  change (2 : ℚ)^6 ≤ (110 : ℚ)+1 ∧
    bjsLogUpper ((110 : ℚ)+1) 6 ≤ ((47097 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((47097 : ℚ)/10000) ∧ bjsLogUpper ((47097 : ℚ)/10000) 2 ≤ ((15498 : ℚ)/10000) ∧
    1 ≤ ((47097 : ℚ)/10000) ∧ ((15498 : ℚ)/10000)+27/100-1/(2*((47097 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 110
  rw [bjsSmallPrefixQ_value110]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow111 : bjsSmallPrefixCertificate 111 := by
  change (2 : ℚ)^6 ≤ (111 : ℚ)+1 ∧
    bjsLogUpper ((111 : ℚ)+1) 6 ≤ ((47186 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((47186 : ℚ)/10000) ∧ bjsLogUpper ((47186 : ℚ)/10000) 2 ≤ ((15517 : ℚ)/10000) ∧
    1 ≤ ((47186 : ℚ)/10000) ∧ ((15517 : ℚ)/10000)+27/100-1/(2*((47186 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 111
  rw [bjsSmallPrefixQ_value111]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow112 : bjsSmallPrefixCertificate 112 := by
  change (2 : ℚ)^6 ≤ (112 : ℚ)+1 ∧
    bjsLogUpper ((112 : ℚ)+1) 6 ≤ ((47275 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((47275 : ℚ)/10000) ∧ bjsLogUpper ((47275 : ℚ)/10000) 2 ≤ ((15535 : ℚ)/10000) ∧
    1 ≤ ((47275 : ℚ)/10000) ∧ ((15535 : ℚ)/10000)+27/100-1/(2*((47275 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 112
  rw [bjsSmallPrefixQ_value112]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow113 : bjsSmallPrefixCertificate 113 := by
  change (2 : ℚ)^6 ≤ (113 : ℚ)+1 ∧
    bjsLogUpper ((113 : ℚ)+1) 6 ≤ ((47363 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((47363 : ℚ)/10000) ∧ bjsLogUpper ((47363 : ℚ)/10000) 2 ≤ ((15554 : ℚ)/10000) ∧
    1 ≤ ((47363 : ℚ)/10000) ∧ ((15554 : ℚ)/10000)+27/100-1/(2*((47363 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 113
  rw [bjsSmallPrefixQ_value113]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow114 : bjsSmallPrefixCertificate 114 := by
  change (2 : ℚ)^6 ≤ (114 : ℚ)+1 ∧
    bjsLogUpper ((114 : ℚ)+1) 6 ≤ ((47451 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((47451 : ℚ)/10000) ∧ bjsLogUpper ((47451 : ℚ)/10000) 2 ≤ ((15573 : ℚ)/10000) ∧
    1 ≤ ((47451 : ℚ)/10000) ∧ ((15573 : ℚ)/10000)+27/100-1/(2*((47451 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 114
  rw [bjsSmallPrefixQ_value114]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow115 : bjsSmallPrefixCertificate 115 := by
  change (2 : ℚ)^6 ≤ (115 : ℚ)+1 ∧
    bjsLogUpper ((115 : ℚ)+1) 6 ≤ ((47537 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((47537 : ℚ)/10000) ∧ bjsLogUpper ((47537 : ℚ)/10000) 2 ≤ ((15591 : ℚ)/10000) ∧
    1 ≤ ((47537 : ℚ)/10000) ∧ ((15591 : ℚ)/10000)+27/100-1/(2*((47537 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 115
  rw [bjsSmallPrefixQ_value115]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow116 : bjsSmallPrefixCertificate 116 := by
  change (2 : ℚ)^6 ≤ (116 : ℚ)+1 ∧
    bjsLogUpper ((116 : ℚ)+1) 6 ≤ ((47623 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((47623 : ℚ)/10000) ∧ bjsLogUpper ((47623 : ℚ)/10000) 2 ≤ ((15609 : ℚ)/10000) ∧
    1 ≤ ((47623 : ℚ)/10000) ∧ ((15609 : ℚ)/10000)+27/100-1/(2*((47623 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 116
  rw [bjsSmallPrefixQ_value116]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow117 : bjsSmallPrefixCertificate 117 := by
  change (2 : ℚ)^6 ≤ (117 : ℚ)+1 ∧
    bjsLogUpper ((117 : ℚ)+1) 6 ≤ ((47708 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((47708 : ℚ)/10000) ∧ bjsLogUpper ((47708 : ℚ)/10000) 2 ≤ ((15627 : ℚ)/10000) ∧
    1 ≤ ((47708 : ℚ)/10000) ∧ ((15627 : ℚ)/10000)+27/100-1/(2*((47708 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 117
  rw [bjsSmallPrefixQ_value117]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow118 : bjsSmallPrefixCertificate 118 := by
  change (2 : ℚ)^6 ≤ (118 : ℚ)+1 ∧
    bjsLogUpper ((118 : ℚ)+1) 6 ≤ ((47793 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((47793 : ℚ)/10000) ∧ bjsLogUpper ((47793 : ℚ)/10000) 2 ≤ ((15644 : ℚ)/10000) ∧
    1 ≤ ((47793 : ℚ)/10000) ∧ ((15644 : ℚ)/10000)+27/100-1/(2*((47793 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 118
  rw [bjsSmallPrefixQ_value118]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow119 : bjsSmallPrefixCertificate 119 := by
  change (2 : ℚ)^6 ≤ (119 : ℚ)+1 ∧
    bjsLogUpper ((119 : ℚ)+1) 6 ≤ ((47876 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((47876 : ℚ)/10000) ∧ bjsLogUpper ((47876 : ℚ)/10000) 2 ≤ ((15662 : ℚ)/10000) ∧
    1 ≤ ((47876 : ℚ)/10000) ∧ ((15662 : ℚ)/10000)+27/100-1/(2*((47876 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 119
  rw [bjsSmallPrefixQ_value119]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow120 : bjsSmallPrefixCertificate 120 := by
  change (2 : ℚ)^6 ≤ (120 : ℚ)+1 ∧
    bjsLogUpper ((120 : ℚ)+1) 6 ≤ ((47959 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((47959 : ℚ)/10000) ∧ bjsLogUpper ((47959 : ℚ)/10000) 2 ≤ ((15679 : ℚ)/10000) ∧
    1 ≤ ((47959 : ℚ)/10000) ∧ ((15679 : ℚ)/10000)+27/100-1/(2*((47959 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 120
  rw [bjsSmallPrefixQ_value120]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow121 : bjsSmallPrefixCertificate 121 := by
  change (2 : ℚ)^6 ≤ (121 : ℚ)+1 ∧
    bjsLogUpper ((121 : ℚ)+1) 6 ≤ ((48042 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((48042 : ℚ)/10000) ∧ bjsLogUpper ((48042 : ℚ)/10000) 2 ≤ ((15696 : ℚ)/10000) ∧
    1 ≤ ((48042 : ℚ)/10000) ∧ ((15696 : ℚ)/10000)+27/100-1/(2*((48042 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 121
  rw [bjsSmallPrefixQ_value121]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow122 : bjsSmallPrefixCertificate 122 := by
  change (2 : ℚ)^6 ≤ (122 : ℚ)+1 ∧
    bjsLogUpper ((122 : ℚ)+1) 6 ≤ ((48123 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((48123 : ℚ)/10000) ∧ bjsLogUpper ((48123 : ℚ)/10000) 2 ≤ ((15713 : ℚ)/10000) ∧
    1 ≤ ((48123 : ℚ)/10000) ∧ ((15713 : ℚ)/10000)+27/100-1/(2*((48123 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 122
  rw [bjsSmallPrefixQ_value122]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow123 : bjsSmallPrefixCertificate 123 := by
  change (2 : ℚ)^6 ≤ (123 : ℚ)+1 ∧
    bjsLogUpper ((123 : ℚ)+1) 6 ≤ ((48204 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((48204 : ℚ)/10000) ∧ bjsLogUpper ((48204 : ℚ)/10000) 2 ≤ ((15730 : ℚ)/10000) ∧
    1 ≤ ((48204 : ℚ)/10000) ∧ ((15730 : ℚ)/10000)+27/100-1/(2*((48204 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 123
  rw [bjsSmallPrefixQ_value123]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow124 : bjsSmallPrefixCertificate 124 := by
  change (2 : ℚ)^6 ≤ (124 : ℚ)+1 ∧
    bjsLogUpper ((124 : ℚ)+1) 6 ≤ ((48285 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((48285 : ℚ)/10000) ∧ bjsLogUpper ((48285 : ℚ)/10000) 2 ≤ ((15747 : ℚ)/10000) ∧
    1 ≤ ((48285 : ℚ)/10000) ∧ ((15747 : ℚ)/10000)+27/100-1/(2*((48285 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 124
  rw [bjsSmallPrefixQ_value124]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow125 : bjsSmallPrefixCertificate 125 := by
  change (2 : ℚ)^6 ≤ (125 : ℚ)+1 ∧
    bjsLogUpper ((125 : ℚ)+1) 6 ≤ ((48364 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((48364 : ℚ)/10000) ∧ bjsLogUpper ((48364 : ℚ)/10000) 2 ≤ ((15763 : ℚ)/10000) ∧
    1 ≤ ((48364 : ℚ)/10000) ∧ ((15763 : ℚ)/10000)+27/100-1/(2*((48364 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 125
  rw [bjsSmallPrefixQ_value125]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow126 : bjsSmallPrefixCertificate 126 := by
  change (2 : ℚ)^6 ≤ (126 : ℚ)+1 ∧
    bjsLogUpper ((126 : ℚ)+1) 6 ≤ ((48443 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((48443 : ℚ)/10000) ∧ bjsLogUpper ((48443 : ℚ)/10000) 2 ≤ ((15780 : ℚ)/10000) ∧
    1 ≤ ((48443 : ℚ)/10000) ∧ ((15780 : ℚ)/10000)+27/100-1/(2*((48443 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 126
  rw [bjsSmallPrefixQ_value126]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow127 : bjsSmallPrefixCertificate 127 := by
  change (2 : ℚ)^7 ≤ (127 : ℚ)+1 ∧
    bjsLogUpper ((127 : ℚ)+1) 7 ≤ ((48522 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((48522 : ℚ)/10000) ∧ bjsLogUpper ((48522 : ℚ)/10000) 2 ≤ ((15796 : ℚ)/10000) ∧
    1 ≤ ((48522 : ℚ)/10000) ∧ ((15796 : ℚ)/10000)+27/100-1/(2*((48522 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 127
  rw [bjsSmallPrefixQ_value127]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow128 : bjsSmallPrefixCertificate 128 := by
  change (2 : ℚ)^7 ≤ (128 : ℚ)+1 ∧
    bjsLogUpper ((128 : ℚ)+1) 7 ≤ ((48600 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((48600 : ℚ)/10000) ∧ bjsLogUpper ((48600 : ℚ)/10000) 2 ≤ ((15812 : ℚ)/10000) ∧
    1 ≤ ((48600 : ℚ)/10000) ∧ ((15812 : ℚ)/10000)+27/100-1/(2*((48600 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 128
  rw [bjsSmallPrefixQ_value128]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow129 : bjsSmallPrefixCertificate 129 := by
  change (2 : ℚ)^7 ≤ (129 : ℚ)+1 ∧
    bjsLogUpper ((129 : ℚ)+1) 7 ≤ ((48677 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((48677 : ℚ)/10000) ∧ bjsLogUpper ((48677 : ℚ)/10000) 2 ≤ ((15828 : ℚ)/10000) ∧
    1 ≤ ((48677 : ℚ)/10000) ∧ ((15828 : ℚ)/10000)+27/100-1/(2*((48677 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 129
  rw [bjsSmallPrefixQ_value129]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow130 : bjsSmallPrefixCertificate 130 := by
  change (2 : ℚ)^7 ≤ (130 : ℚ)+1 ∧
    bjsLogUpper ((130 : ℚ)+1) 7 ≤ ((48753 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((48753 : ℚ)/10000) ∧ bjsLogUpper ((48753 : ℚ)/10000) 2 ≤ ((15843 : ℚ)/10000) ∧
    1 ≤ ((48753 : ℚ)/10000) ∧ ((15843 : ℚ)/10000)+27/100-1/(2*((48753 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 130
  rw [bjsSmallPrefixQ_value130]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow131 : bjsSmallPrefixCertificate 131 := by
  change (2 : ℚ)^7 ≤ (131 : ℚ)+1 ∧
    bjsLogUpper ((131 : ℚ)+1) 7 ≤ ((48830 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((48830 : ℚ)/10000) ∧ bjsLogUpper ((48830 : ℚ)/10000) 2 ≤ ((15859 : ℚ)/10000) ∧
    1 ≤ ((48830 : ℚ)/10000) ∧ ((15859 : ℚ)/10000)+27/100-1/(2*((48830 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 131
  rw [bjsSmallPrefixQ_value131]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow132 : bjsSmallPrefixCertificate 132 := by
  change (2 : ℚ)^7 ≤ (132 : ℚ)+1 ∧
    bjsLogUpper ((132 : ℚ)+1) 7 ≤ ((48905 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((48905 : ℚ)/10000) ∧ bjsLogUpper ((48905 : ℚ)/10000) 2 ≤ ((15874 : ℚ)/10000) ∧
    1 ≤ ((48905 : ℚ)/10000) ∧ ((15874 : ℚ)/10000)+27/100-1/(2*((48905 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 132
  rw [bjsSmallPrefixQ_value132]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow133 : bjsSmallPrefixCertificate 133 := by
  change (2 : ℚ)^7 ≤ (133 : ℚ)+1 ∧
    bjsLogUpper ((133 : ℚ)+1) 7 ≤ ((48980 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((48980 : ℚ)/10000) ∧ bjsLogUpper ((48980 : ℚ)/10000) 2 ≤ ((15890 : ℚ)/10000) ∧
    1 ≤ ((48980 : ℚ)/10000) ∧ ((15890 : ℚ)/10000)+27/100-1/(2*((48980 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 133
  rw [bjsSmallPrefixQ_value133]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow134 : bjsSmallPrefixCertificate 134 := by
  change (2 : ℚ)^7 ≤ (134 : ℚ)+1 ∧
    bjsLogUpper ((134 : ℚ)+1) 7 ≤ ((49054 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49054 : ℚ)/10000) ∧ bjsLogUpper ((49054 : ℚ)/10000) 2 ≤ ((15905 : ℚ)/10000) ∧
    1 ≤ ((49054 : ℚ)/10000) ∧ ((15905 : ℚ)/10000)+27/100-1/(2*((49054 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 134
  rw [bjsSmallPrefixQ_value134]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow135 : bjsSmallPrefixCertificate 135 := by
  change (2 : ℚ)^7 ≤ (135 : ℚ)+1 ∧
    bjsLogUpper ((135 : ℚ)+1) 7 ≤ ((49128 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49128 : ℚ)/10000) ∧ bjsLogUpper ((49128 : ℚ)/10000) 2 ≤ ((15920 : ℚ)/10000) ∧
    1 ≤ ((49128 : ℚ)/10000) ∧ ((15920 : ℚ)/10000)+27/100-1/(2*((49128 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 135
  rw [bjsSmallPrefixQ_value135]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow136 : bjsSmallPrefixCertificate 136 := by
  change (2 : ℚ)^7 ≤ (136 : ℚ)+1 ∧
    bjsLogUpper ((136 : ℚ)+1) 7 ≤ ((49201 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49201 : ℚ)/10000) ∧ bjsLogUpper ((49201 : ℚ)/10000) 2 ≤ ((15935 : ℚ)/10000) ∧
    1 ≤ ((49201 : ℚ)/10000) ∧ ((15935 : ℚ)/10000)+27/100-1/(2*((49201 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 136
  rw [bjsSmallPrefixQ_value136]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow137 : bjsSmallPrefixCertificate 137 := by
  change (2 : ℚ)^7 ≤ (137 : ℚ)+1 ∧
    bjsLogUpper ((137 : ℚ)+1) 7 ≤ ((49274 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49274 : ℚ)/10000) ∧ bjsLogUpper ((49274 : ℚ)/10000) 2 ≤ ((15950 : ℚ)/10000) ∧
    1 ≤ ((49274 : ℚ)/10000) ∧ ((15950 : ℚ)/10000)+27/100-1/(2*((49274 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 137
  rw [bjsSmallPrefixQ_value137]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow138 : bjsSmallPrefixCertificate 138 := by
  change (2 : ℚ)^7 ≤ (138 : ℚ)+1 ∧
    bjsLogUpper ((138 : ℚ)+1) 7 ≤ ((49346 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49346 : ℚ)/10000) ∧ bjsLogUpper ((49346 : ℚ)/10000) 2 ≤ ((15964 : ℚ)/10000) ∧
    1 ≤ ((49346 : ℚ)/10000) ∧ ((15964 : ℚ)/10000)+27/100-1/(2*((49346 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 138
  rw [bjsSmallPrefixQ_value138]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow139 : bjsSmallPrefixCertificate 139 := by
  change (2 : ℚ)^7 ≤ (139 : ℚ)+1 ∧
    bjsLogUpper ((139 : ℚ)+1) 7 ≤ ((49418 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49418 : ℚ)/10000) ∧ bjsLogUpper ((49418 : ℚ)/10000) 2 ≤ ((15979 : ℚ)/10000) ∧
    1 ≤ ((49418 : ℚ)/10000) ∧ ((15979 : ℚ)/10000)+27/100-1/(2*((49418 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 139
  rw [bjsSmallPrefixQ_value139]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow140 : bjsSmallPrefixCertificate 140 := by
  change (2 : ℚ)^7 ≤ (140 : ℚ)+1 ∧
    bjsLogUpper ((140 : ℚ)+1) 7 ≤ ((49489 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49489 : ℚ)/10000) ∧ bjsLogUpper ((49489 : ℚ)/10000) 2 ≤ ((15993 : ℚ)/10000) ∧
    1 ≤ ((49489 : ℚ)/10000) ∧ ((15993 : ℚ)/10000)+27/100-1/(2*((49489 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 140
  rw [bjsSmallPrefixQ_value140]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow141 : bjsSmallPrefixCertificate 141 := by
  change (2 : ℚ)^7 ≤ (141 : ℚ)+1 ∧
    bjsLogUpper ((141 : ℚ)+1) 7 ≤ ((49560 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49560 : ℚ)/10000) ∧ bjsLogUpper ((49560 : ℚ)/10000) 2 ≤ ((16007 : ℚ)/10000) ∧
    1 ≤ ((49560 : ℚ)/10000) ∧ ((16007 : ℚ)/10000)+27/100-1/(2*((49560 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 141
  rw [bjsSmallPrefixQ_value141]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow142 : bjsSmallPrefixCertificate 142 := by
  change (2 : ℚ)^7 ≤ (142 : ℚ)+1 ∧
    bjsLogUpper ((142 : ℚ)+1) 7 ≤ ((49630 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49630 : ℚ)/10000) ∧ bjsLogUpper ((49630 : ℚ)/10000) 2 ≤ ((16022 : ℚ)/10000) ∧
    1 ≤ ((49630 : ℚ)/10000) ∧ ((16022 : ℚ)/10000)+27/100-1/(2*((49630 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 142
  rw [bjsSmallPrefixQ_value142]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow143 : bjsSmallPrefixCertificate 143 := by
  change (2 : ℚ)^7 ≤ (143 : ℚ)+1 ∧
    bjsLogUpper ((143 : ℚ)+1) 7 ≤ ((49700 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49700 : ℚ)/10000) ∧ bjsLogUpper ((49700 : ℚ)/10000) 2 ≤ ((16036 : ℚ)/10000) ∧
    1 ≤ ((49700 : ℚ)/10000) ∧ ((16036 : ℚ)/10000)+27/100-1/(2*((49700 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 143
  rw [bjsSmallPrefixQ_value143]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow144 : bjsSmallPrefixCertificate 144 := by
  change (2 : ℚ)^7 ≤ (144 : ℚ)+1 ∧
    bjsLogUpper ((144 : ℚ)+1) 7 ≤ ((49769 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49769 : ℚ)/10000) ∧ bjsLogUpper ((49769 : ℚ)/10000) 2 ≤ ((16050 : ℚ)/10000) ∧
    1 ≤ ((49769 : ℚ)/10000) ∧ ((16050 : ℚ)/10000)+27/100-1/(2*((49769 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 144
  rw [bjsSmallPrefixQ_value144]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow145 : bjsSmallPrefixCertificate 145 := by
  change (2 : ℚ)^7 ≤ (145 : ℚ)+1 ∧
    bjsLogUpper ((145 : ℚ)+1) 7 ≤ ((49838 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49838 : ℚ)/10000) ∧ bjsLogUpper ((49838 : ℚ)/10000) 2 ≤ ((16063 : ℚ)/10000) ∧
    1 ≤ ((49838 : ℚ)/10000) ∧ ((16063 : ℚ)/10000)+27/100-1/(2*((49838 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 145
  rw [bjsSmallPrefixQ_value145]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow146 : bjsSmallPrefixCertificate 146 := by
  change (2 : ℚ)^7 ≤ (146 : ℚ)+1 ∧
    bjsLogUpper ((146 : ℚ)+1) 7 ≤ ((49906 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49906 : ℚ)/10000) ∧ bjsLogUpper ((49906 : ℚ)/10000) 2 ≤ ((16077 : ℚ)/10000) ∧
    1 ≤ ((49906 : ℚ)/10000) ∧ ((16077 : ℚ)/10000)+27/100-1/(2*((49906 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 146
  rw [bjsSmallPrefixQ_value146]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow147 : bjsSmallPrefixCertificate 147 := by
  change (2 : ℚ)^7 ≤ (147 : ℚ)+1 ∧
    bjsLogUpper ((147 : ℚ)+1) 7 ≤ ((49974 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((49974 : ℚ)/10000) ∧ bjsLogUpper ((49974 : ℚ)/10000) 2 ≤ ((16091 : ℚ)/10000) ∧
    1 ≤ ((49974 : ℚ)/10000) ∧ ((16091 : ℚ)/10000)+27/100-1/(2*((49974 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 147
  rw [bjsSmallPrefixQ_value147]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow148 : bjsSmallPrefixCertificate 148 := by
  change (2 : ℚ)^7 ≤ (148 : ℚ)+1 ∧
    bjsLogUpper ((148 : ℚ)+1) 7 ≤ ((50041 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50041 : ℚ)/10000) ∧ bjsLogUpper ((50041 : ℚ)/10000) 2 ≤ ((16104 : ℚ)/10000) ∧
    1 ≤ ((50041 : ℚ)/10000) ∧ ((16104 : ℚ)/10000)+27/100-1/(2*((50041 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 148
  rw [bjsSmallPrefixQ_value148]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow149 : bjsSmallPrefixCertificate 149 := by
  change (2 : ℚ)^7 ≤ (149 : ℚ)+1 ∧
    bjsLogUpper ((149 : ℚ)+1) 7 ≤ ((50108 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50108 : ℚ)/10000) ∧ bjsLogUpper ((50108 : ℚ)/10000) 2 ≤ ((16117 : ℚ)/10000) ∧
    1 ≤ ((50108 : ℚ)/10000) ∧ ((16117 : ℚ)/10000)+27/100-1/(2*((50108 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 149
  rw [bjsSmallPrefixQ_value149]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow150 : bjsSmallPrefixCertificate 150 := by
  change (2 : ℚ)^7 ≤ (150 : ℚ)+1 ∧
    bjsLogUpper ((150 : ℚ)+1) 7 ≤ ((50174 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50174 : ℚ)/10000) ∧ bjsLogUpper ((50174 : ℚ)/10000) 2 ≤ ((16131 : ℚ)/10000) ∧
    1 ≤ ((50174 : ℚ)/10000) ∧ ((16131 : ℚ)/10000)+27/100-1/(2*((50174 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 150
  rw [bjsSmallPrefixQ_value150]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow151 : bjsSmallPrefixCertificate 151 := by
  change (2 : ℚ)^7 ≤ (151 : ℚ)+1 ∧
    bjsLogUpper ((151 : ℚ)+1) 7 ≤ ((50240 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50240 : ℚ)/10000) ∧ bjsLogUpper ((50240 : ℚ)/10000) 2 ≤ ((16144 : ℚ)/10000) ∧
    1 ≤ ((50240 : ℚ)/10000) ∧ ((16144 : ℚ)/10000)+27/100-1/(2*((50240 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 151
  rw [bjsSmallPrefixQ_value151]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow152 : bjsSmallPrefixCertificate 152 := by
  change (2 : ℚ)^7 ≤ (152 : ℚ)+1 ∧
    bjsLogUpper ((152 : ℚ)+1) 7 ≤ ((50306 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50306 : ℚ)/10000) ∧ bjsLogUpper ((50306 : ℚ)/10000) 2 ≤ ((16157 : ℚ)/10000) ∧
    1 ≤ ((50306 : ℚ)/10000) ∧ ((16157 : ℚ)/10000)+27/100-1/(2*((50306 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 152
  rw [bjsSmallPrefixQ_value152]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow153 : bjsSmallPrefixCertificate 153 := by
  change (2 : ℚ)^7 ≤ (153 : ℚ)+1 ∧
    bjsLogUpper ((153 : ℚ)+1) 7 ≤ ((50371 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50371 : ℚ)/10000) ∧ bjsLogUpper ((50371 : ℚ)/10000) 2 ≤ ((16170 : ℚ)/10000) ∧
    1 ≤ ((50371 : ℚ)/10000) ∧ ((16170 : ℚ)/10000)+27/100-1/(2*((50371 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 153
  rw [bjsSmallPrefixQ_value153]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow154 : bjsSmallPrefixCertificate 154 := by
  change (2 : ℚ)^7 ≤ (154 : ℚ)+1 ∧
    bjsLogUpper ((154 : ℚ)+1) 7 ≤ ((50436 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50436 : ℚ)/10000) ∧ bjsLogUpper ((50436 : ℚ)/10000) 2 ≤ ((16183 : ℚ)/10000) ∧
    1 ≤ ((50436 : ℚ)/10000) ∧ ((16183 : ℚ)/10000)+27/100-1/(2*((50436 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 154
  rw [bjsSmallPrefixQ_value154]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow155 : bjsSmallPrefixCertificate 155 := by
  change (2 : ℚ)^7 ≤ (155 : ℚ)+1 ∧
    bjsLogUpper ((155 : ℚ)+1) 7 ≤ ((50500 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50500 : ℚ)/10000) ∧ bjsLogUpper ((50500 : ℚ)/10000) 2 ≤ ((16195 : ℚ)/10000) ∧
    1 ≤ ((50500 : ℚ)/10000) ∧ ((16195 : ℚ)/10000)+27/100-1/(2*((50500 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 155
  rw [bjsSmallPrefixQ_value155]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow156 : bjsSmallPrefixCertificate 156 := by
  change (2 : ℚ)^7 ≤ (156 : ℚ)+1 ∧
    bjsLogUpper ((156 : ℚ)+1) 7 ≤ ((50564 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50564 : ℚ)/10000) ∧ bjsLogUpper ((50564 : ℚ)/10000) 2 ≤ ((16208 : ℚ)/10000) ∧
    1 ≤ ((50564 : ℚ)/10000) ∧ ((16208 : ℚ)/10000)+27/100-1/(2*((50564 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 156
  rw [bjsSmallPrefixQ_value156]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow157 : bjsSmallPrefixCertificate 157 := by
  change (2 : ℚ)^7 ≤ (157 : ℚ)+1 ∧
    bjsLogUpper ((157 : ℚ)+1) 7 ≤ ((50627 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50627 : ℚ)/10000) ∧ bjsLogUpper ((50627 : ℚ)/10000) 2 ≤ ((16220 : ℚ)/10000) ∧
    1 ≤ ((50627 : ℚ)/10000) ∧ ((16220 : ℚ)/10000)+27/100-1/(2*((50627 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 157
  rw [bjsSmallPrefixQ_value157]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow158 : bjsSmallPrefixCertificate 158 := by
  change (2 : ℚ)^7 ≤ (158 : ℚ)+1 ∧
    bjsLogUpper ((158 : ℚ)+1) 7 ≤ ((50691 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50691 : ℚ)/10000) ∧ bjsLogUpper ((50691 : ℚ)/10000) 2 ≤ ((16233 : ℚ)/10000) ∧
    1 ≤ ((50691 : ℚ)/10000) ∧ ((16233 : ℚ)/10000)+27/100-1/(2*((50691 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 158
  rw [bjsSmallPrefixQ_value158]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow159 : bjsSmallPrefixCertificate 159 := by
  change (2 : ℚ)^7 ≤ (159 : ℚ)+1 ∧
    bjsLogUpper ((159 : ℚ)+1) 7 ≤ ((50753 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50753 : ℚ)/10000) ∧ bjsLogUpper ((50753 : ℚ)/10000) 2 ≤ ((16245 : ℚ)/10000) ∧
    1 ≤ ((50753 : ℚ)/10000) ∧ ((16245 : ℚ)/10000)+27/100-1/(2*((50753 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 159
  rw [bjsSmallPrefixQ_value159]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow160 : bjsSmallPrefixCertificate 160 := by
  change (2 : ℚ)^7 ≤ (160 : ℚ)+1 ∧
    bjsLogUpper ((160 : ℚ)+1) 7 ≤ ((50816 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50816 : ℚ)/10000) ∧ bjsLogUpper ((50816 : ℚ)/10000) 2 ≤ ((16258 : ℚ)/10000) ∧
    1 ≤ ((50816 : ℚ)/10000) ∧ ((16258 : ℚ)/10000)+27/100-1/(2*((50816 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 160
  rw [bjsSmallPrefixQ_value160]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow161 : bjsSmallPrefixCertificate 161 := by
  change (2 : ℚ)^7 ≤ (161 : ℚ)+1 ∧
    bjsLogUpper ((161 : ℚ)+1) 7 ≤ ((50877 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50877 : ℚ)/10000) ∧ bjsLogUpper ((50877 : ℚ)/10000) 2 ≤ ((16270 : ℚ)/10000) ∧
    1 ≤ ((50877 : ℚ)/10000) ∧ ((16270 : ℚ)/10000)+27/100-1/(2*((50877 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 161
  rw [bjsSmallPrefixQ_value161]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow162 : bjsSmallPrefixCertificate 162 := by
  change (2 : ℚ)^7 ≤ (162 : ℚ)+1 ∧
    bjsLogUpper ((162 : ℚ)+1) 7 ≤ ((50939 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((50939 : ℚ)/10000) ∧ bjsLogUpper ((50939 : ℚ)/10000) 2 ≤ ((16282 : ℚ)/10000) ∧
    1 ≤ ((50939 : ℚ)/10000) ∧ ((16282 : ℚ)/10000)+27/100-1/(2*((50939 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 162
  rw [bjsSmallPrefixQ_value162]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow163 : bjsSmallPrefixCertificate 163 := by
  change (2 : ℚ)^7 ≤ (163 : ℚ)+1 ∧
    bjsLogUpper ((163 : ℚ)+1) 7 ≤ ((51000 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51000 : ℚ)/10000) ∧ bjsLogUpper ((51000 : ℚ)/10000) 2 ≤ ((16294 : ℚ)/10000) ∧
    1 ≤ ((51000 : ℚ)/10000) ∧ ((16294 : ℚ)/10000)+27/100-1/(2*((51000 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 163
  rw [bjsSmallPrefixQ_value163]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow164 : bjsSmallPrefixCertificate 164 := by
  change (2 : ℚ)^7 ≤ (164 : ℚ)+1 ∧
    bjsLogUpper ((164 : ℚ)+1) 7 ≤ ((51061 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51061 : ℚ)/10000) ∧ bjsLogUpper ((51061 : ℚ)/10000) 2 ≤ ((16306 : ℚ)/10000) ∧
    1 ≤ ((51061 : ℚ)/10000) ∧ ((16306 : ℚ)/10000)+27/100-1/(2*((51061 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 164
  rw [bjsSmallPrefixQ_value164]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow165 : bjsSmallPrefixCertificate 165 := by
  change (2 : ℚ)^7 ≤ (165 : ℚ)+1 ∧
    bjsLogUpper ((165 : ℚ)+1) 7 ≤ ((51121 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51121 : ℚ)/10000) ∧ bjsLogUpper ((51121 : ℚ)/10000) 2 ≤ ((16318 : ℚ)/10000) ∧
    1 ≤ ((51121 : ℚ)/10000) ∧ ((16318 : ℚ)/10000)+27/100-1/(2*((51121 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 165
  rw [bjsSmallPrefixQ_value165]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow166 : bjsSmallPrefixCertificate 166 := by
  change (2 : ℚ)^7 ≤ (166 : ℚ)+1 ∧
    bjsLogUpper ((166 : ℚ)+1) 7 ≤ ((51181 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51181 : ℚ)/10000) ∧ bjsLogUpper ((51181 : ℚ)/10000) 2 ≤ ((16329 : ℚ)/10000) ∧
    1 ≤ ((51181 : ℚ)/10000) ∧ ((16329 : ℚ)/10000)+27/100-1/(2*((51181 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 166
  rw [bjsSmallPrefixQ_value166]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow167 : bjsSmallPrefixCertificate 167 := by
  change (2 : ℚ)^7 ≤ (167 : ℚ)+1 ∧
    bjsLogUpper ((167 : ℚ)+1) 7 ≤ ((51241 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51241 : ℚ)/10000) ∧ bjsLogUpper ((51241 : ℚ)/10000) 2 ≤ ((16341 : ℚ)/10000) ∧
    1 ≤ ((51241 : ℚ)/10000) ∧ ((16341 : ℚ)/10000)+27/100-1/(2*((51241 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 167
  rw [bjsSmallPrefixQ_value167]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow168 : bjsSmallPrefixCertificate 168 := by
  change (2 : ℚ)^7 ≤ (168 : ℚ)+1 ∧
    bjsLogUpper ((168 : ℚ)+1) 7 ≤ ((51300 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51300 : ℚ)/10000) ∧ bjsLogUpper ((51300 : ℚ)/10000) 2 ≤ ((16353 : ℚ)/10000) ∧
    1 ≤ ((51300 : ℚ)/10000) ∧ ((16353 : ℚ)/10000)+27/100-1/(2*((51300 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 168
  rw [bjsSmallPrefixQ_value168]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow169 : bjsSmallPrefixCertificate 169 := by
  change (2 : ℚ)^7 ≤ (169 : ℚ)+1 ∧
    bjsLogUpper ((169 : ℚ)+1) 7 ≤ ((51359 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51359 : ℚ)/10000) ∧ bjsLogUpper ((51359 : ℚ)/10000) 2 ≤ ((16364 : ℚ)/10000) ∧
    1 ≤ ((51359 : ℚ)/10000) ∧ ((16364 : ℚ)/10000)+27/100-1/(2*((51359 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 169
  rw [bjsSmallPrefixQ_value169]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow170 : bjsSmallPrefixCertificate 170 := by
  change (2 : ℚ)^7 ≤ (170 : ℚ)+1 ∧
    bjsLogUpper ((170 : ℚ)+1) 7 ≤ ((51418 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51418 : ℚ)/10000) ∧ bjsLogUpper ((51418 : ℚ)/10000) 2 ≤ ((16376 : ℚ)/10000) ∧
    1 ≤ ((51418 : ℚ)/10000) ∧ ((16376 : ℚ)/10000)+27/100-1/(2*((51418 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 170
  rw [bjsSmallPrefixQ_value170]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow171 : bjsSmallPrefixCertificate 171 := by
  change (2 : ℚ)^7 ≤ (171 : ℚ)+1 ∧
    bjsLogUpper ((171 : ℚ)+1) 7 ≤ ((51476 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51476 : ℚ)/10000) ∧ bjsLogUpper ((51476 : ℚ)/10000) 2 ≤ ((16387 : ℚ)/10000) ∧
    1 ≤ ((51476 : ℚ)/10000) ∧ ((16387 : ℚ)/10000)+27/100-1/(2*((51476 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 171
  rw [bjsSmallPrefixQ_value171]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow172 : bjsSmallPrefixCertificate 172 := by
  change (2 : ℚ)^7 ≤ (172 : ℚ)+1 ∧
    bjsLogUpper ((172 : ℚ)+1) 7 ≤ ((51534 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51534 : ℚ)/10000) ∧ bjsLogUpper ((51534 : ℚ)/10000) 2 ≤ ((16398 : ℚ)/10000) ∧
    1 ≤ ((51534 : ℚ)/10000) ∧ ((16398 : ℚ)/10000)+27/100-1/(2*((51534 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 172
  rw [bjsSmallPrefixQ_value172]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow173 : bjsSmallPrefixCertificate 173 := by
  change (2 : ℚ)^7 ≤ (173 : ℚ)+1 ∧
    bjsLogUpper ((173 : ℚ)+1) 7 ≤ ((51592 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51592 : ℚ)/10000) ∧ bjsLogUpper ((51592 : ℚ)/10000) 2 ≤ ((16409 : ℚ)/10000) ∧
    1 ≤ ((51592 : ℚ)/10000) ∧ ((16409 : ℚ)/10000)+27/100-1/(2*((51592 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 173
  rw [bjsSmallPrefixQ_value173]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow174 : bjsSmallPrefixCertificate 174 := by
  change (2 : ℚ)^7 ≤ (174 : ℚ)+1 ∧
    bjsLogUpper ((174 : ℚ)+1) 7 ≤ ((51649 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51649 : ℚ)/10000) ∧ bjsLogUpper ((51649 : ℚ)/10000) 2 ≤ ((16420 : ℚ)/10000) ∧
    1 ≤ ((51649 : ℚ)/10000) ∧ ((16420 : ℚ)/10000)+27/100-1/(2*((51649 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 174
  rw [bjsSmallPrefixQ_value174]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow175 : bjsSmallPrefixCertificate 175 := by
  change (2 : ℚ)^7 ≤ (175 : ℚ)+1 ∧
    bjsLogUpper ((175 : ℚ)+1) 7 ≤ ((51706 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51706 : ℚ)/10000) ∧ bjsLogUpper ((51706 : ℚ)/10000) 2 ≤ ((16431 : ℚ)/10000) ∧
    1 ≤ ((51706 : ℚ)/10000) ∧ ((16431 : ℚ)/10000)+27/100-1/(2*((51706 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 175
  rw [bjsSmallPrefixQ_value175]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow176 : bjsSmallPrefixCertificate 176 := by
  change (2 : ℚ)^7 ≤ (176 : ℚ)+1 ∧
    bjsLogUpper ((176 : ℚ)+1) 7 ≤ ((51763 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51763 : ℚ)/10000) ∧ bjsLogUpper ((51763 : ℚ)/10000) 2 ≤ ((16442 : ℚ)/10000) ∧
    1 ≤ ((51763 : ℚ)/10000) ∧ ((16442 : ℚ)/10000)+27/100-1/(2*((51763 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 176
  rw [bjsSmallPrefixQ_value176]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow177 : bjsSmallPrefixCertificate 177 := by
  change (2 : ℚ)^7 ≤ (177 : ℚ)+1 ∧
    bjsLogUpper ((177 : ℚ)+1) 7 ≤ ((51819 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51819 : ℚ)/10000) ∧ bjsLogUpper ((51819 : ℚ)/10000) 2 ≤ ((16453 : ℚ)/10000) ∧
    1 ≤ ((51819 : ℚ)/10000) ∧ ((16453 : ℚ)/10000)+27/100-1/(2*((51819 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 177
  rw [bjsSmallPrefixQ_value177]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow178 : bjsSmallPrefixCertificate 178 := by
  change (2 : ℚ)^7 ≤ (178 : ℚ)+1 ∧
    bjsLogUpper ((178 : ℚ)+1) 7 ≤ ((51875 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51875 : ℚ)/10000) ∧ bjsLogUpper ((51875 : ℚ)/10000) 2 ≤ ((16464 : ℚ)/10000) ∧
    1 ≤ ((51875 : ℚ)/10000) ∧ ((16464 : ℚ)/10000)+27/100-1/(2*((51875 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 178
  rw [bjsSmallPrefixQ_value178]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow179 : bjsSmallPrefixCertificate 179 := by
  change (2 : ℚ)^7 ≤ (179 : ℚ)+1 ∧
    bjsLogUpper ((179 : ℚ)+1) 7 ≤ ((51931 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51931 : ℚ)/10000) ∧ bjsLogUpper ((51931 : ℚ)/10000) 2 ≤ ((16475 : ℚ)/10000) ∧
    1 ≤ ((51931 : ℚ)/10000) ∧ ((16475 : ℚ)/10000)+27/100-1/(2*((51931 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 179
  rw [bjsSmallPrefixQ_value179]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow180 : bjsSmallPrefixCertificate 180 := by
  change (2 : ℚ)^7 ≤ (180 : ℚ)+1 ∧
    bjsLogUpper ((180 : ℚ)+1) 7 ≤ ((51986 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((51986 : ℚ)/10000) ∧ bjsLogUpper ((51986 : ℚ)/10000) 2 ≤ ((16485 : ℚ)/10000) ∧
    1 ≤ ((51986 : ℚ)/10000) ∧ ((16485 : ℚ)/10000)+27/100-1/(2*((51986 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 180
  rw [bjsSmallPrefixQ_value180]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow181 : bjsSmallPrefixCertificate 181 := by
  change (2 : ℚ)^7 ≤ (181 : ℚ)+1 ∧
    bjsLogUpper ((181 : ℚ)+1) 7 ≤ ((52042 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52042 : ℚ)/10000) ∧ bjsLogUpper ((52042 : ℚ)/10000) 2 ≤ ((16496 : ℚ)/10000) ∧
    1 ≤ ((52042 : ℚ)/10000) ∧ ((16496 : ℚ)/10000)+27/100-1/(2*((52042 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 181
  rw [bjsSmallPrefixQ_value181]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow182 : bjsSmallPrefixCertificate 182 := by
  change (2 : ℚ)^7 ≤ (182 : ℚ)+1 ∧
    bjsLogUpper ((182 : ℚ)+1) 7 ≤ ((52096 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52096 : ℚ)/10000) ∧ bjsLogUpper ((52096 : ℚ)/10000) 2 ≤ ((16507 : ℚ)/10000) ∧
    1 ≤ ((52096 : ℚ)/10000) ∧ ((16507 : ℚ)/10000)+27/100-1/(2*((52096 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 182
  rw [bjsSmallPrefixQ_value182]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow183 : bjsSmallPrefixCertificate 183 := by
  change (2 : ℚ)^7 ≤ (183 : ℚ)+1 ∧
    bjsLogUpper ((183 : ℚ)+1) 7 ≤ ((52151 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52151 : ℚ)/10000) ∧ bjsLogUpper ((52151 : ℚ)/10000) 2 ≤ ((16517 : ℚ)/10000) ∧
    1 ≤ ((52151 : ℚ)/10000) ∧ ((16517 : ℚ)/10000)+27/100-1/(2*((52151 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 183
  rw [bjsSmallPrefixQ_value183]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow184 : bjsSmallPrefixCertificate 184 := by
  change (2 : ℚ)^7 ≤ (184 : ℚ)+1 ∧
    bjsLogUpper ((184 : ℚ)+1) 7 ≤ ((52205 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52205 : ℚ)/10000) ∧ bjsLogUpper ((52205 : ℚ)/10000) 2 ≤ ((16527 : ℚ)/10000) ∧
    1 ≤ ((52205 : ℚ)/10000) ∧ ((16527 : ℚ)/10000)+27/100-1/(2*((52205 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 184
  rw [bjsSmallPrefixQ_value184]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow185 : bjsSmallPrefixCertificate 185 := by
  change (2 : ℚ)^7 ≤ (185 : ℚ)+1 ∧
    bjsLogUpper ((185 : ℚ)+1) 7 ≤ ((52259 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52259 : ℚ)/10000) ∧ bjsLogUpper ((52259 : ℚ)/10000) 2 ≤ ((16538 : ℚ)/10000) ∧
    1 ≤ ((52259 : ℚ)/10000) ∧ ((16538 : ℚ)/10000)+27/100-1/(2*((52259 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 185
  rw [bjsSmallPrefixQ_value185]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow186 : bjsSmallPrefixCertificate 186 := by
  change (2 : ℚ)^7 ≤ (186 : ℚ)+1 ∧
    bjsLogUpper ((186 : ℚ)+1) 7 ≤ ((52313 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52313 : ℚ)/10000) ∧ bjsLogUpper ((52313 : ℚ)/10000) 2 ≤ ((16548 : ℚ)/10000) ∧
    1 ≤ ((52313 : ℚ)/10000) ∧ ((16548 : ℚ)/10000)+27/100-1/(2*((52313 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 186
  rw [bjsSmallPrefixQ_value186]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow187 : bjsSmallPrefixCertificate 187 := by
  change (2 : ℚ)^7 ≤ (187 : ℚ)+1 ∧
    bjsLogUpper ((187 : ℚ)+1) 7 ≤ ((52366 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52366 : ℚ)/10000) ∧ bjsLogUpper ((52366 : ℚ)/10000) 2 ≤ ((16558 : ℚ)/10000) ∧
    1 ≤ ((52366 : ℚ)/10000) ∧ ((16558 : ℚ)/10000)+27/100-1/(2*((52366 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 187
  rw [bjsSmallPrefixQ_value187]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow188 : bjsSmallPrefixCertificate 188 := by
  change (2 : ℚ)^7 ≤ (188 : ℚ)+1 ∧
    bjsLogUpper ((188 : ℚ)+1) 7 ≤ ((52419 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52419 : ℚ)/10000) ∧ bjsLogUpper ((52419 : ℚ)/10000) 2 ≤ ((16568 : ℚ)/10000) ∧
    1 ≤ ((52419 : ℚ)/10000) ∧ ((16568 : ℚ)/10000)+27/100-1/(2*((52419 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 188
  rw [bjsSmallPrefixQ_value188]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow189 : bjsSmallPrefixCertificate 189 := by
  change (2 : ℚ)^7 ≤ (189 : ℚ)+1 ∧
    bjsLogUpper ((189 : ℚ)+1) 7 ≤ ((52472 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52472 : ℚ)/10000) ∧ bjsLogUpper ((52472 : ℚ)/10000) 2 ≤ ((16578 : ℚ)/10000) ∧
    1 ≤ ((52472 : ℚ)/10000) ∧ ((16578 : ℚ)/10000)+27/100-1/(2*((52472 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 189
  rw [bjsSmallPrefixQ_value189]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow190 : bjsSmallPrefixCertificate 190 := by
  change (2 : ℚ)^7 ≤ (190 : ℚ)+1 ∧
    bjsLogUpper ((190 : ℚ)+1) 7 ≤ ((52524 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52524 : ℚ)/10000) ∧ bjsLogUpper ((52524 : ℚ)/10000) 2 ≤ ((16588 : ℚ)/10000) ∧
    1 ≤ ((52524 : ℚ)/10000) ∧ ((16588 : ℚ)/10000)+27/100-1/(2*((52524 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 190
  rw [bjsSmallPrefixQ_value190]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow191 : bjsSmallPrefixCertificate 191 := by
  change (2 : ℚ)^7 ≤ (191 : ℚ)+1 ∧
    bjsLogUpper ((191 : ℚ)+1) 7 ≤ ((52576 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52576 : ℚ)/10000) ∧ bjsLogUpper ((52576 : ℚ)/10000) 2 ≤ ((16598 : ℚ)/10000) ∧
    1 ≤ ((52576 : ℚ)/10000) ∧ ((16598 : ℚ)/10000)+27/100-1/(2*((52576 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 191
  rw [bjsSmallPrefixQ_value191]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow192 : bjsSmallPrefixCertificate 192 := by
  change (2 : ℚ)^7 ≤ (192 : ℚ)+1 ∧
    bjsLogUpper ((192 : ℚ)+1) 7 ≤ ((52628 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52628 : ℚ)/10000) ∧ bjsLogUpper ((52628 : ℚ)/10000) 2 ≤ ((16608 : ℚ)/10000) ∧
    1 ≤ ((52628 : ℚ)/10000) ∧ ((16608 : ℚ)/10000)+27/100-1/(2*((52628 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 192
  rw [bjsSmallPrefixQ_value192]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow193 : bjsSmallPrefixCertificate 193 := by
  change (2 : ℚ)^7 ≤ (193 : ℚ)+1 ∧
    bjsLogUpper ((193 : ℚ)+1) 7 ≤ ((52680 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52680 : ℚ)/10000) ∧ bjsLogUpper ((52680 : ℚ)/10000) 2 ≤ ((16618 : ℚ)/10000) ∧
    1 ≤ ((52680 : ℚ)/10000) ∧ ((16618 : ℚ)/10000)+27/100-1/(2*((52680 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 193
  rw [bjsSmallPrefixQ_value193]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow194 : bjsSmallPrefixCertificate 194 := by
  change (2 : ℚ)^7 ≤ (194 : ℚ)+1 ∧
    bjsLogUpper ((194 : ℚ)+1) 7 ≤ ((52731 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52731 : ℚ)/10000) ∧ bjsLogUpper ((52731 : ℚ)/10000) 2 ≤ ((16628 : ℚ)/10000) ∧
    1 ≤ ((52731 : ℚ)/10000) ∧ ((16628 : ℚ)/10000)+27/100-1/(2*((52731 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 194
  rw [bjsSmallPrefixQ_value194]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow195 : bjsSmallPrefixCertificate 195 := by
  change (2 : ℚ)^7 ≤ (195 : ℚ)+1 ∧
    bjsLogUpper ((195 : ℚ)+1) 7 ≤ ((52783 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52783 : ℚ)/10000) ∧ bjsLogUpper ((52783 : ℚ)/10000) 2 ≤ ((16638 : ℚ)/10000) ∧
    1 ≤ ((52783 : ℚ)/10000) ∧ ((16638 : ℚ)/10000)+27/100-1/(2*((52783 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 195
  rw [bjsSmallPrefixQ_value195]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow196 : bjsSmallPrefixCertificate 196 := by
  change (2 : ℚ)^7 ≤ (196 : ℚ)+1 ∧
    bjsLogUpper ((196 : ℚ)+1) 7 ≤ ((52834 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52834 : ℚ)/10000) ∧ bjsLogUpper ((52834 : ℚ)/10000) 2 ≤ ((16647 : ℚ)/10000) ∧
    1 ≤ ((52834 : ℚ)/10000) ∧ ((16647 : ℚ)/10000)+27/100-1/(2*((52834 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 196
  rw [bjsSmallPrefixQ_value196]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow197 : bjsSmallPrefixCertificate 197 := by
  change (2 : ℚ)^7 ≤ (197 : ℚ)+1 ∧
    bjsLogUpper ((197 : ℚ)+1) 7 ≤ ((52884 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52884 : ℚ)/10000) ∧ bjsLogUpper ((52884 : ℚ)/10000) 2 ≤ ((16657 : ℚ)/10000) ∧
    1 ≤ ((52884 : ℚ)/10000) ∧ ((16657 : ℚ)/10000)+27/100-1/(2*((52884 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 197
  rw [bjsSmallPrefixQ_value197]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow198 : bjsSmallPrefixCertificate 198 := by
  change (2 : ℚ)^7 ≤ (198 : ℚ)+1 ∧
    bjsLogUpper ((198 : ℚ)+1) 7 ≤ ((52935 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52935 : ℚ)/10000) ∧ bjsLogUpper ((52935 : ℚ)/10000) 2 ≤ ((16666 : ℚ)/10000) ∧
    1 ≤ ((52935 : ℚ)/10000) ∧ ((16666 : ℚ)/10000)+27/100-1/(2*((52935 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 198
  rw [bjsSmallPrefixQ_value198]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow199 : bjsSmallPrefixCertificate 199 := by
  change (2 : ℚ)^7 ≤ (199 : ℚ)+1 ∧
    bjsLogUpper ((199 : ℚ)+1) 7 ≤ ((52985 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((52985 : ℚ)/10000) ∧ bjsLogUpper ((52985 : ℚ)/10000) 2 ≤ ((16676 : ℚ)/10000) ∧
    1 ≤ ((52985 : ℚ)/10000) ∧ ((16676 : ℚ)/10000)+27/100-1/(2*((52985 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 199
  rw [bjsSmallPrefixQ_value199]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow200 : bjsSmallPrefixCertificate 200 := by
  change (2 : ℚ)^7 ≤ (200 : ℚ)+1 ∧
    bjsLogUpper ((200 : ℚ)+1) 7 ≤ ((53035 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53035 : ℚ)/10000) ∧ bjsLogUpper ((53035 : ℚ)/10000) 2 ≤ ((16685 : ℚ)/10000) ∧
    1 ≤ ((53035 : ℚ)/10000) ∧ ((16685 : ℚ)/10000)+27/100-1/(2*((53035 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 200
  rw [bjsSmallPrefixQ_value200]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow201 : bjsSmallPrefixCertificate 201 := by
  change (2 : ℚ)^7 ≤ (201 : ℚ)+1 ∧
    bjsLogUpper ((201 : ℚ)+1) 7 ≤ ((53084 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53084 : ℚ)/10000) ∧ bjsLogUpper ((53084 : ℚ)/10000) 2 ≤ ((16694 : ℚ)/10000) ∧
    1 ≤ ((53084 : ℚ)/10000) ∧ ((16694 : ℚ)/10000)+27/100-1/(2*((53084 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 201
  rw [bjsSmallPrefixQ_value201]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow202 : bjsSmallPrefixCertificate 202 := by
  change (2 : ℚ)^7 ≤ (202 : ℚ)+1 ∧
    bjsLogUpper ((202 : ℚ)+1) 7 ≤ ((53134 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53134 : ℚ)/10000) ∧ bjsLogUpper ((53134 : ℚ)/10000) 2 ≤ ((16704 : ℚ)/10000) ∧
    1 ≤ ((53134 : ℚ)/10000) ∧ ((16704 : ℚ)/10000)+27/100-1/(2*((53134 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 202
  rw [bjsSmallPrefixQ_value202]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow203 : bjsSmallPrefixCertificate 203 := by
  change (2 : ℚ)^7 ≤ (203 : ℚ)+1 ∧
    bjsLogUpper ((203 : ℚ)+1) 7 ≤ ((53183 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53183 : ℚ)/10000) ∧ bjsLogUpper ((53183 : ℚ)/10000) 2 ≤ ((16713 : ℚ)/10000) ∧
    1 ≤ ((53183 : ℚ)/10000) ∧ ((16713 : ℚ)/10000)+27/100-1/(2*((53183 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 203
  rw [bjsSmallPrefixQ_value203]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow204 : bjsSmallPrefixCertificate 204 := by
  change (2 : ℚ)^7 ≤ (204 : ℚ)+1 ∧
    bjsLogUpper ((204 : ℚ)+1) 7 ≤ ((53232 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53232 : ℚ)/10000) ∧ bjsLogUpper ((53232 : ℚ)/10000) 2 ≤ ((16722 : ℚ)/10000) ∧
    1 ≤ ((53232 : ℚ)/10000) ∧ ((16722 : ℚ)/10000)+27/100-1/(2*((53232 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 204
  rw [bjsSmallPrefixQ_value204]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow205 : bjsSmallPrefixCertificate 205 := by
  change (2 : ℚ)^7 ≤ (205 : ℚ)+1 ∧
    bjsLogUpper ((205 : ℚ)+1) 7 ≤ ((53280 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53280 : ℚ)/10000) ∧ bjsLogUpper ((53280 : ℚ)/10000) 2 ≤ ((16731 : ℚ)/10000) ∧
    1 ≤ ((53280 : ℚ)/10000) ∧ ((16731 : ℚ)/10000)+27/100-1/(2*((53280 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 205
  rw [bjsSmallPrefixQ_value205]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow206 : bjsSmallPrefixCertificate 206 := by
  change (2 : ℚ)^7 ≤ (206 : ℚ)+1 ∧
    bjsLogUpper ((206 : ℚ)+1) 7 ≤ ((53329 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53329 : ℚ)/10000) ∧ bjsLogUpper ((53329 : ℚ)/10000) 2 ≤ ((16740 : ℚ)/10000) ∧
    1 ≤ ((53329 : ℚ)/10000) ∧ ((16740 : ℚ)/10000)+27/100-1/(2*((53329 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 206
  rw [bjsSmallPrefixQ_value206]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow207 : bjsSmallPrefixCertificate 207 := by
  change (2 : ℚ)^7 ≤ (207 : ℚ)+1 ∧
    bjsLogUpper ((207 : ℚ)+1) 7 ≤ ((53377 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53377 : ℚ)/10000) ∧ bjsLogUpper ((53377 : ℚ)/10000) 2 ≤ ((16749 : ℚ)/10000) ∧
    1 ≤ ((53377 : ℚ)/10000) ∧ ((16749 : ℚ)/10000)+27/100-1/(2*((53377 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 207
  rw [bjsSmallPrefixQ_value207]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow208 : bjsSmallPrefixCertificate 208 := by
  change (2 : ℚ)^7 ≤ (208 : ℚ)+1 ∧
    bjsLogUpper ((208 : ℚ)+1) 7 ≤ ((53425 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53425 : ℚ)/10000) ∧ bjsLogUpper ((53425 : ℚ)/10000) 2 ≤ ((16758 : ℚ)/10000) ∧
    1 ≤ ((53425 : ℚ)/10000) ∧ ((16758 : ℚ)/10000)+27/100-1/(2*((53425 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 208
  rw [bjsSmallPrefixQ_value208]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow209 : bjsSmallPrefixCertificate 209 := by
  change (2 : ℚ)^7 ≤ (209 : ℚ)+1 ∧
    bjsLogUpper ((209 : ℚ)+1) 7 ≤ ((53473 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53473 : ℚ)/10000) ∧ bjsLogUpper ((53473 : ℚ)/10000) 2 ≤ ((16767 : ℚ)/10000) ∧
    1 ≤ ((53473 : ℚ)/10000) ∧ ((16767 : ℚ)/10000)+27/100-1/(2*((53473 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 209
  rw [bjsSmallPrefixQ_value209]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow210 : bjsSmallPrefixCertificate 210 := by
  change (2 : ℚ)^7 ≤ (210 : ℚ)+1 ∧
    bjsLogUpper ((210 : ℚ)+1) 7 ≤ ((53520 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53520 : ℚ)/10000) ∧ bjsLogUpper ((53520 : ℚ)/10000) 2 ≤ ((16776 : ℚ)/10000) ∧
    1 ≤ ((53520 : ℚ)/10000) ∧ ((16776 : ℚ)/10000)+27/100-1/(2*((53520 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 210
  rw [bjsSmallPrefixQ_value210]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow211 : bjsSmallPrefixCertificate 211 := by
  change (2 : ℚ)^7 ≤ (211 : ℚ)+1 ∧
    bjsLogUpper ((211 : ℚ)+1) 7 ≤ ((53567 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53567 : ℚ)/10000) ∧ bjsLogUpper ((53567 : ℚ)/10000) 2 ≤ ((16785 : ℚ)/10000) ∧
    1 ≤ ((53567 : ℚ)/10000) ∧ ((16785 : ℚ)/10000)+27/100-1/(2*((53567 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 211
  rw [bjsSmallPrefixQ_value211]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow212 : bjsSmallPrefixCertificate 212 := by
  change (2 : ℚ)^7 ≤ (212 : ℚ)+1 ∧
    bjsLogUpper ((212 : ℚ)+1) 7 ≤ ((53614 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53614 : ℚ)/10000) ∧ bjsLogUpper ((53614 : ℚ)/10000) 2 ≤ ((16794 : ℚ)/10000) ∧
    1 ≤ ((53614 : ℚ)/10000) ∧ ((16794 : ℚ)/10000)+27/100-1/(2*((53614 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 212
  rw [bjsSmallPrefixQ_value212]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow213 : bjsSmallPrefixCertificate 213 := by
  change (2 : ℚ)^7 ≤ (213 : ℚ)+1 ∧
    bjsLogUpper ((213 : ℚ)+1) 7 ≤ ((53661 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53661 : ℚ)/10000) ∧ bjsLogUpper ((53661 : ℚ)/10000) 2 ≤ ((16803 : ℚ)/10000) ∧
    1 ≤ ((53661 : ℚ)/10000) ∧ ((16803 : ℚ)/10000)+27/100-1/(2*((53661 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 213
  rw [bjsSmallPrefixQ_value213]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow214 : bjsSmallPrefixCertificate 214 := by
  change (2 : ℚ)^7 ≤ (214 : ℚ)+1 ∧
    bjsLogUpper ((214 : ℚ)+1) 7 ≤ ((53708 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53708 : ℚ)/10000) ∧ bjsLogUpper ((53708 : ℚ)/10000) 2 ≤ ((16811 : ℚ)/10000) ∧
    1 ≤ ((53708 : ℚ)/10000) ∧ ((16811 : ℚ)/10000)+27/100-1/(2*((53708 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 214
  rw [bjsSmallPrefixQ_value214]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow215 : bjsSmallPrefixCertificate 215 := by
  change (2 : ℚ)^7 ≤ (215 : ℚ)+1 ∧
    bjsLogUpper ((215 : ℚ)+1) 7 ≤ ((53754 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53754 : ℚ)/10000) ∧ bjsLogUpper ((53754 : ℚ)/10000) 2 ≤ ((16820 : ℚ)/10000) ∧
    1 ≤ ((53754 : ℚ)/10000) ∧ ((16820 : ℚ)/10000)+27/100-1/(2*((53754 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 215
  rw [bjsSmallPrefixQ_value215]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow216 : bjsSmallPrefixCertificate 216 := by
  change (2 : ℚ)^7 ≤ (216 : ℚ)+1 ∧
    bjsLogUpper ((216 : ℚ)+1) 7 ≤ ((53800 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53800 : ℚ)/10000) ∧ bjsLogUpper ((53800 : ℚ)/10000) 2 ≤ ((16828 : ℚ)/10000) ∧
    1 ≤ ((53800 : ℚ)/10000) ∧ ((16828 : ℚ)/10000)+27/100-1/(2*((53800 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 216
  rw [bjsSmallPrefixQ_value216]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow217 : bjsSmallPrefixCertificate 217 := by
  change (2 : ℚ)^7 ≤ (217 : ℚ)+1 ∧
    bjsLogUpper ((217 : ℚ)+1) 7 ≤ ((53846 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53846 : ℚ)/10000) ∧ bjsLogUpper ((53846 : ℚ)/10000) 2 ≤ ((16837 : ℚ)/10000) ∧
    1 ≤ ((53846 : ℚ)/10000) ∧ ((16837 : ℚ)/10000)+27/100-1/(2*((53846 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 217
  rw [bjsSmallPrefixQ_value217]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow218 : bjsSmallPrefixCertificate 218 := by
  change (2 : ℚ)^7 ≤ (218 : ℚ)+1 ∧
    bjsLogUpper ((218 : ℚ)+1) 7 ≤ ((53892 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53892 : ℚ)/10000) ∧ bjsLogUpper ((53892 : ℚ)/10000) 2 ≤ ((16845 : ℚ)/10000) ∧
    1 ≤ ((53892 : ℚ)/10000) ∧ ((16845 : ℚ)/10000)+27/100-1/(2*((53892 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 218
  rw [bjsSmallPrefixQ_value218]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow219 : bjsSmallPrefixCertificate 219 := by
  change (2 : ℚ)^7 ≤ (219 : ℚ)+1 ∧
    bjsLogUpper ((219 : ℚ)+1) 7 ≤ ((53938 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53938 : ℚ)/10000) ∧ bjsLogUpper ((53938 : ℚ)/10000) 2 ≤ ((16854 : ℚ)/10000) ∧
    1 ≤ ((53938 : ℚ)/10000) ∧ ((16854 : ℚ)/10000)+27/100-1/(2*((53938 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 219
  rw [bjsSmallPrefixQ_value219]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow220 : bjsSmallPrefixCertificate 220 := by
  change (2 : ℚ)^7 ≤ (220 : ℚ)+1 ∧
    bjsLogUpper ((220 : ℚ)+1) 7 ≤ ((53983 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((53983 : ℚ)/10000) ∧ bjsLogUpper ((53983 : ℚ)/10000) 2 ≤ ((16862 : ℚ)/10000) ∧
    1 ≤ ((53983 : ℚ)/10000) ∧ ((16862 : ℚ)/10000)+27/100-1/(2*((53983 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 220
  rw [bjsSmallPrefixQ_value220]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow221 : bjsSmallPrefixCertificate 221 := by
  change (2 : ℚ)^7 ≤ (221 : ℚ)+1 ∧
    bjsLogUpper ((221 : ℚ)+1) 7 ≤ ((54028 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54028 : ℚ)/10000) ∧ bjsLogUpper ((54028 : ℚ)/10000) 2 ≤ ((16871 : ℚ)/10000) ∧
    1 ≤ ((54028 : ℚ)/10000) ∧ ((16871 : ℚ)/10000)+27/100-1/(2*((54028 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 221
  rw [bjsSmallPrefixQ_value221]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow222 : bjsSmallPrefixCertificate 222 := by
  change (2 : ℚ)^7 ≤ (222 : ℚ)+1 ∧
    bjsLogUpper ((222 : ℚ)+1) 7 ≤ ((54073 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54073 : ℚ)/10000) ∧ bjsLogUpper ((54073 : ℚ)/10000) 2 ≤ ((16879 : ℚ)/10000) ∧
    1 ≤ ((54073 : ℚ)/10000) ∧ ((16879 : ℚ)/10000)+27/100-1/(2*((54073 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 222
  rw [bjsSmallPrefixQ_value222]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow223 : bjsSmallPrefixCertificate 223 := by
  change (2 : ℚ)^7 ≤ (223 : ℚ)+1 ∧
    bjsLogUpper ((223 : ℚ)+1) 7 ≤ ((54118 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54118 : ℚ)/10000) ∧ bjsLogUpper ((54118 : ℚ)/10000) 2 ≤ ((16887 : ℚ)/10000) ∧
    1 ≤ ((54118 : ℚ)/10000) ∧ ((16887 : ℚ)/10000)+27/100-1/(2*((54118 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 223
  rw [bjsSmallPrefixQ_value223]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow224 : bjsSmallPrefixCertificate 224 := by
  change (2 : ℚ)^7 ≤ (224 : ℚ)+1 ∧
    bjsLogUpper ((224 : ℚ)+1) 7 ≤ ((54163 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54163 : ℚ)/10000) ∧ bjsLogUpper ((54163 : ℚ)/10000) 2 ≤ ((16896 : ℚ)/10000) ∧
    1 ≤ ((54163 : ℚ)/10000) ∧ ((16896 : ℚ)/10000)+27/100-1/(2*((54163 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 224
  rw [bjsSmallPrefixQ_value224]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow225 : bjsSmallPrefixCertificate 225 := by
  change (2 : ℚ)^7 ≤ (225 : ℚ)+1 ∧
    bjsLogUpper ((225 : ℚ)+1) 7 ≤ ((54207 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54207 : ℚ)/10000) ∧ bjsLogUpper ((54207 : ℚ)/10000) 2 ≤ ((16904 : ℚ)/10000) ∧
    1 ≤ ((54207 : ℚ)/10000) ∧ ((16904 : ℚ)/10000)+27/100-1/(2*((54207 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 225
  rw [bjsSmallPrefixQ_value225]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow226 : bjsSmallPrefixCertificate 226 := by
  change (2 : ℚ)^7 ≤ (226 : ℚ)+1 ∧
    bjsLogUpper ((226 : ℚ)+1) 7 ≤ ((54251 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54251 : ℚ)/10000) ∧ bjsLogUpper ((54251 : ℚ)/10000) 2 ≤ ((16912 : ℚ)/10000) ∧
    1 ≤ ((54251 : ℚ)/10000) ∧ ((16912 : ℚ)/10000)+27/100-1/(2*((54251 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 226
  rw [bjsSmallPrefixQ_value226]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow227 : bjsSmallPrefixCertificate 227 := by
  change (2 : ℚ)^7 ≤ (227 : ℚ)+1 ∧
    bjsLogUpper ((227 : ℚ)+1) 7 ≤ ((54295 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54295 : ℚ)/10000) ∧ bjsLogUpper ((54295 : ℚ)/10000) 2 ≤ ((16920 : ℚ)/10000) ∧
    1 ≤ ((54295 : ℚ)/10000) ∧ ((16920 : ℚ)/10000)+27/100-1/(2*((54295 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 227
  rw [bjsSmallPrefixQ_value227]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow228 : bjsSmallPrefixCertificate 228 := by
  change (2 : ℚ)^7 ≤ (228 : ℚ)+1 ∧
    bjsLogUpper ((228 : ℚ)+1) 7 ≤ ((54339 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54339 : ℚ)/10000) ∧ bjsLogUpper ((54339 : ℚ)/10000) 2 ≤ ((16928 : ℚ)/10000) ∧
    1 ≤ ((54339 : ℚ)/10000) ∧ ((16928 : ℚ)/10000)+27/100-1/(2*((54339 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 228
  rw [bjsSmallPrefixQ_value228]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow229 : bjsSmallPrefixCertificate 229 := by
  change (2 : ℚ)^7 ≤ (229 : ℚ)+1 ∧
    bjsLogUpper ((229 : ℚ)+1) 7 ≤ ((54382 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54382 : ℚ)/10000) ∧ bjsLogUpper ((54382 : ℚ)/10000) 2 ≤ ((16936 : ℚ)/10000) ∧
    1 ≤ ((54382 : ℚ)/10000) ∧ ((16936 : ℚ)/10000)+27/100-1/(2*((54382 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 229
  rw [bjsSmallPrefixQ_value229]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow230 : bjsSmallPrefixCertificate 230 := by
  change (2 : ℚ)^7 ≤ (230 : ℚ)+1 ∧
    bjsLogUpper ((230 : ℚ)+1) 7 ≤ ((54426 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54426 : ℚ)/10000) ∧ bjsLogUpper ((54426 : ℚ)/10000) 2 ≤ ((16944 : ℚ)/10000) ∧
    1 ≤ ((54426 : ℚ)/10000) ∧ ((16944 : ℚ)/10000)+27/100-1/(2*((54426 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 230
  rw [bjsSmallPrefixQ_value230]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow231 : bjsSmallPrefixCertificate 231 := by
  change (2 : ℚ)^7 ≤ (231 : ℚ)+1 ∧
    bjsLogUpper ((231 : ℚ)+1) 7 ≤ ((54469 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54469 : ℚ)/10000) ∧ bjsLogUpper ((54469 : ℚ)/10000) 2 ≤ ((16952 : ℚ)/10000) ∧
    1 ≤ ((54469 : ℚ)/10000) ∧ ((16952 : ℚ)/10000)+27/100-1/(2*((54469 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 231
  rw [bjsSmallPrefixQ_value231]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow232 : bjsSmallPrefixCertificate 232 := by
  change (2 : ℚ)^7 ≤ (232 : ℚ)+1 ∧
    bjsLogUpper ((232 : ℚ)+1) 7 ≤ ((54512 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54512 : ℚ)/10000) ∧ bjsLogUpper ((54512 : ℚ)/10000) 2 ≤ ((16960 : ℚ)/10000) ∧
    1 ≤ ((54512 : ℚ)/10000) ∧ ((16960 : ℚ)/10000)+27/100-1/(2*((54512 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 232
  rw [bjsSmallPrefixQ_value232]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow233 : bjsSmallPrefixCertificate 233 := by
  change (2 : ℚ)^7 ≤ (233 : ℚ)+1 ∧
    bjsLogUpper ((233 : ℚ)+1) 7 ≤ ((54555 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54555 : ℚ)/10000) ∧ bjsLogUpper ((54555 : ℚ)/10000) 2 ≤ ((16968 : ℚ)/10000) ∧
    1 ≤ ((54555 : ℚ)/10000) ∧ ((16968 : ℚ)/10000)+27/100-1/(2*((54555 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 233
  rw [bjsSmallPrefixQ_value233]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow234 : bjsSmallPrefixCertificate 234 := by
  change (2 : ℚ)^7 ≤ (234 : ℚ)+1 ∧
    bjsLogUpper ((234 : ℚ)+1) 7 ≤ ((54597 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54597 : ℚ)/10000) ∧ bjsLogUpper ((54597 : ℚ)/10000) 2 ≤ ((16975 : ℚ)/10000) ∧
    1 ≤ ((54597 : ℚ)/10000) ∧ ((16975 : ℚ)/10000)+27/100-1/(2*((54597 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 234
  rw [bjsSmallPrefixQ_value234]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow235 : bjsSmallPrefixCertificate 235 := by
  change (2 : ℚ)^7 ≤ (235 : ℚ)+1 ∧
    bjsLogUpper ((235 : ℚ)+1) 7 ≤ ((54640 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54640 : ℚ)/10000) ∧ bjsLogUpper ((54640 : ℚ)/10000) 2 ≤ ((16983 : ℚ)/10000) ∧
    1 ≤ ((54640 : ℚ)/10000) ∧ ((16983 : ℚ)/10000)+27/100-1/(2*((54640 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 235
  rw [bjsSmallPrefixQ_value235]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow236 : bjsSmallPrefixCertificate 236 := by
  change (2 : ℚ)^7 ≤ (236 : ℚ)+1 ∧
    bjsLogUpper ((236 : ℚ)+1) 7 ≤ ((54682 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54682 : ℚ)/10000) ∧ bjsLogUpper ((54682 : ℚ)/10000) 2 ≤ ((16991 : ℚ)/10000) ∧
    1 ≤ ((54682 : ℚ)/10000) ∧ ((16991 : ℚ)/10000)+27/100-1/(2*((54682 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 236
  rw [bjsSmallPrefixQ_value236]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow237 : bjsSmallPrefixCertificate 237 := by
  change (2 : ℚ)^7 ≤ (237 : ℚ)+1 ∧
    bjsLogUpper ((237 : ℚ)+1) 7 ≤ ((54724 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54724 : ℚ)/10000) ∧ bjsLogUpper ((54724 : ℚ)/10000) 2 ≤ ((16999 : ℚ)/10000) ∧
    1 ≤ ((54724 : ℚ)/10000) ∧ ((16999 : ℚ)/10000)+27/100-1/(2*((54724 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 237
  rw [bjsSmallPrefixQ_value237]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow238 : bjsSmallPrefixCertificate 238 := by
  change (2 : ℚ)^7 ≤ (238 : ℚ)+1 ∧
    bjsLogUpper ((238 : ℚ)+1) 7 ≤ ((54766 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54766 : ℚ)/10000) ∧ bjsLogUpper ((54766 : ℚ)/10000) 2 ≤ ((17006 : ℚ)/10000) ∧
    1 ≤ ((54766 : ℚ)/10000) ∧ ((17006 : ℚ)/10000)+27/100-1/(2*((54766 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 238
  rw [bjsSmallPrefixQ_value238]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow239 : bjsSmallPrefixCertificate 239 := by
  change (2 : ℚ)^7 ≤ (239 : ℚ)+1 ∧
    bjsLogUpper ((239 : ℚ)+1) 7 ≤ ((54808 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54808 : ℚ)/10000) ∧ bjsLogUpper ((54808 : ℚ)/10000) 2 ≤ ((17014 : ℚ)/10000) ∧
    1 ≤ ((54808 : ℚ)/10000) ∧ ((17014 : ℚ)/10000)+27/100-1/(2*((54808 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 239
  rw [bjsSmallPrefixQ_value239]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow240 : bjsSmallPrefixCertificate 240 := by
  change (2 : ℚ)^7 ≤ (240 : ℚ)+1 ∧
    bjsLogUpper ((240 : ℚ)+1) 7 ≤ ((54849 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54849 : ℚ)/10000) ∧ bjsLogUpper ((54849 : ℚ)/10000) 2 ≤ ((17021 : ℚ)/10000) ∧
    1 ≤ ((54849 : ℚ)/10000) ∧ ((17021 : ℚ)/10000)+27/100-1/(2*((54849 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 240
  rw [bjsSmallPrefixQ_value240]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow241 : bjsSmallPrefixCertificate 241 := by
  change (2 : ℚ)^7 ≤ (241 : ℚ)+1 ∧
    bjsLogUpper ((241 : ℚ)+1) 7 ≤ ((54891 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54891 : ℚ)/10000) ∧ bjsLogUpper ((54891 : ℚ)/10000) 2 ≤ ((17029 : ℚ)/10000) ∧
    1 ≤ ((54891 : ℚ)/10000) ∧ ((17029 : ℚ)/10000)+27/100-1/(2*((54891 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 241
  rw [bjsSmallPrefixQ_value241]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow242 : bjsSmallPrefixCertificate 242 := by
  change (2 : ℚ)^7 ≤ (242 : ℚ)+1 ∧
    bjsLogUpper ((242 : ℚ)+1) 7 ≤ ((54932 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54932 : ℚ)/10000) ∧ bjsLogUpper ((54932 : ℚ)/10000) 2 ≤ ((17037 : ℚ)/10000) ∧
    1 ≤ ((54932 : ℚ)/10000) ∧ ((17037 : ℚ)/10000)+27/100-1/(2*((54932 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 242
  rw [bjsSmallPrefixQ_value242]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow243 : bjsSmallPrefixCertificate 243 := by
  change (2 : ℚ)^7 ≤ (243 : ℚ)+1 ∧
    bjsLogUpper ((243 : ℚ)+1) 7 ≤ ((54973 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((54973 : ℚ)/10000) ∧ bjsLogUpper ((54973 : ℚ)/10000) 2 ≤ ((17044 : ℚ)/10000) ∧
    1 ≤ ((54973 : ℚ)/10000) ∧ ((17044 : ℚ)/10000)+27/100-1/(2*((54973 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 243
  rw [bjsSmallPrefixQ_value243]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow244 : bjsSmallPrefixCertificate 244 := by
  change (2 : ℚ)^7 ≤ (244 : ℚ)+1 ∧
    bjsLogUpper ((244 : ℚ)+1) 7 ≤ ((55014 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55014 : ℚ)/10000) ∧ bjsLogUpper ((55014 : ℚ)/10000) 2 ≤ ((17052 : ℚ)/10000) ∧
    1 ≤ ((55014 : ℚ)/10000) ∧ ((17052 : ℚ)/10000)+27/100-1/(2*((55014 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 244
  rw [bjsSmallPrefixQ_value244]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow245 : bjsSmallPrefixCertificate 245 := by
  change (2 : ℚ)^7 ≤ (245 : ℚ)+1 ∧
    bjsLogUpper ((245 : ℚ)+1) 7 ≤ ((55055 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55055 : ℚ)/10000) ∧ bjsLogUpper ((55055 : ℚ)/10000) 2 ≤ ((17059 : ℚ)/10000) ∧
    1 ≤ ((55055 : ℚ)/10000) ∧ ((17059 : ℚ)/10000)+27/100-1/(2*((55055 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 245
  rw [bjsSmallPrefixQ_value245]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow246 : bjsSmallPrefixCertificate 246 := by
  change (2 : ℚ)^7 ≤ (246 : ℚ)+1 ∧
    bjsLogUpper ((246 : ℚ)+1) 7 ≤ ((55095 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55095 : ℚ)/10000) ∧ bjsLogUpper ((55095 : ℚ)/10000) 2 ≤ ((17066 : ℚ)/10000) ∧
    1 ≤ ((55095 : ℚ)/10000) ∧ ((17066 : ℚ)/10000)+27/100-1/(2*((55095 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 246
  rw [bjsSmallPrefixQ_value246]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow247 : bjsSmallPrefixCertificate 247 := by
  change (2 : ℚ)^7 ≤ (247 : ℚ)+1 ∧
    bjsLogUpper ((247 : ℚ)+1) 7 ≤ ((55136 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55136 : ℚ)/10000) ∧ bjsLogUpper ((55136 : ℚ)/10000) 2 ≤ ((17074 : ℚ)/10000) ∧
    1 ≤ ((55136 : ℚ)/10000) ∧ ((17074 : ℚ)/10000)+27/100-1/(2*((55136 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 247
  rw [bjsSmallPrefixQ_value247]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow248 : bjsSmallPrefixCertificate 248 := by
  change (2 : ℚ)^7 ≤ (248 : ℚ)+1 ∧
    bjsLogUpper ((248 : ℚ)+1) 7 ≤ ((55176 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55176 : ℚ)/10000) ∧ bjsLogUpper ((55176 : ℚ)/10000) 2 ≤ ((17081 : ℚ)/10000) ∧
    1 ≤ ((55176 : ℚ)/10000) ∧ ((17081 : ℚ)/10000)+27/100-1/(2*((55176 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 248
  rw [bjsSmallPrefixQ_value248]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow249 : bjsSmallPrefixCertificate 249 := by
  change (2 : ℚ)^7 ≤ (249 : ℚ)+1 ∧
    bjsLogUpper ((249 : ℚ)+1) 7 ≤ ((55216 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55216 : ℚ)/10000) ∧ bjsLogUpper ((55216 : ℚ)/10000) 2 ≤ ((17088 : ℚ)/10000) ∧
    1 ≤ ((55216 : ℚ)/10000) ∧ ((17088 : ℚ)/10000)+27/100-1/(2*((55216 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 249
  rw [bjsSmallPrefixQ_value249]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow250 : bjsSmallPrefixCertificate 250 := by
  change (2 : ℚ)^7 ≤ (250 : ℚ)+1 ∧
    bjsLogUpper ((250 : ℚ)+1) 7 ≤ ((55256 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55256 : ℚ)/10000) ∧ bjsLogUpper ((55256 : ℚ)/10000) 2 ≤ ((17095 : ℚ)/10000) ∧
    1 ≤ ((55256 : ℚ)/10000) ∧ ((17095 : ℚ)/10000)+27/100-1/(2*((55256 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 250
  rw [bjsSmallPrefixQ_value250]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow251 : bjsSmallPrefixCertificate 251 := by
  change (2 : ℚ)^7 ≤ (251 : ℚ)+1 ∧
    bjsLogUpper ((251 : ℚ)+1) 7 ≤ ((55296 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55296 : ℚ)/10000) ∧ bjsLogUpper ((55296 : ℚ)/10000) 2 ≤ ((17103 : ℚ)/10000) ∧
    1 ≤ ((55296 : ℚ)/10000) ∧ ((17103 : ℚ)/10000)+27/100-1/(2*((55296 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 251
  rw [bjsSmallPrefixQ_value251]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow252 : bjsSmallPrefixCertificate 252 := by
  change (2 : ℚ)^7 ≤ (252 : ℚ)+1 ∧
    bjsLogUpper ((252 : ℚ)+1) 7 ≤ ((55335 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55335 : ℚ)/10000) ∧ bjsLogUpper ((55335 : ℚ)/10000) 2 ≤ ((17110 : ℚ)/10000) ∧
    1 ≤ ((55335 : ℚ)/10000) ∧ ((17110 : ℚ)/10000)+27/100-1/(2*((55335 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 252
  rw [bjsSmallPrefixQ_value252]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow253 : bjsSmallPrefixCertificate 253 := by
  change (2 : ℚ)^7 ≤ (253 : ℚ)+1 ∧
    bjsLogUpper ((253 : ℚ)+1) 7 ≤ ((55375 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55375 : ℚ)/10000) ∧ bjsLogUpper ((55375 : ℚ)/10000) 2 ≤ ((17117 : ℚ)/10000) ∧
    1 ≤ ((55375 : ℚ)/10000) ∧ ((17117 : ℚ)/10000)+27/100-1/(2*((55375 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 253
  rw [bjsSmallPrefixQ_value253]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow254 : bjsSmallPrefixCertificate 254 := by
  change (2 : ℚ)^7 ≤ (254 : ℚ)+1 ∧
    bjsLogUpper ((254 : ℚ)+1) 7 ≤ ((55414 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55414 : ℚ)/10000) ∧ bjsLogUpper ((55414 : ℚ)/10000) 2 ≤ ((17124 : ℚ)/10000) ∧
    1 ≤ ((55414 : ℚ)/10000) ∧ ((17124 : ℚ)/10000)+27/100-1/(2*((55414 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 254
  rw [bjsSmallPrefixQ_value254]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow255 : bjsSmallPrefixCertificate 255 := by
  change (2 : ℚ)^8 ≤ (255 : ℚ)+1 ∧
    bjsLogUpper ((255 : ℚ)+1) 8 ≤ ((55453 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55453 : ℚ)/10000) ∧ bjsLogUpper ((55453 : ℚ)/10000) 2 ≤ ((17131 : ℚ)/10000) ∧
    1 ≤ ((55453 : ℚ)/10000) ∧ ((17131 : ℚ)/10000)+27/100-1/(2*((55453 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 255
  rw [bjsSmallPrefixQ_value255]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow256 : bjsSmallPrefixCertificate 256 := by
  change (2 : ℚ)^8 ≤ (256 : ℚ)+1 ∧
    bjsLogUpper ((256 : ℚ)+1) 8 ≤ ((55492 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55492 : ℚ)/10000) ∧ bjsLogUpper ((55492 : ℚ)/10000) 2 ≤ ((17138 : ℚ)/10000) ∧
    1 ≤ ((55492 : ℚ)/10000) ∧ ((17138 : ℚ)/10000)+27/100-1/(2*((55492 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 256
  rw [bjsSmallPrefixQ_value256]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow257 : bjsSmallPrefixCertificate 257 := by
  change (2 : ℚ)^8 ≤ (257 : ℚ)+1 ∧
    bjsLogUpper ((257 : ℚ)+1) 8 ≤ ((55531 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55531 : ℚ)/10000) ∧ bjsLogUpper ((55531 : ℚ)/10000) 2 ≤ ((17145 : ℚ)/10000) ∧
    1 ≤ ((55531 : ℚ)/10000) ∧ ((17145 : ℚ)/10000)+27/100-1/(2*((55531 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 257
  rw [bjsSmallPrefixQ_value257]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow258 : bjsSmallPrefixCertificate 258 := by
  change (2 : ℚ)^8 ≤ (258 : ℚ)+1 ∧
    bjsLogUpper ((258 : ℚ)+1) 8 ≤ ((55570 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55570 : ℚ)/10000) ∧ bjsLogUpper ((55570 : ℚ)/10000) 2 ≤ ((17152 : ℚ)/10000) ∧
    1 ≤ ((55570 : ℚ)/10000) ∧ ((17152 : ℚ)/10000)+27/100-1/(2*((55570 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 258
  rw [bjsSmallPrefixQ_value258]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow259 : bjsSmallPrefixCertificate 259 := by
  change (2 : ℚ)^8 ≤ (259 : ℚ)+1 ∧
    bjsLogUpper ((259 : ℚ)+1) 8 ≤ ((55608 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55608 : ℚ)/10000) ∧ bjsLogUpper ((55608 : ℚ)/10000) 2 ≤ ((17159 : ℚ)/10000) ∧
    1 ≤ ((55608 : ℚ)/10000) ∧ ((17159 : ℚ)/10000)+27/100-1/(2*((55608 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 259
  rw [bjsSmallPrefixQ_value259]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow260 : bjsSmallPrefixCertificate 260 := by
  change (2 : ℚ)^8 ≤ (260 : ℚ)+1 ∧
    bjsLogUpper ((260 : ℚ)+1) 8 ≤ ((55647 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55647 : ℚ)/10000) ∧ bjsLogUpper ((55647 : ℚ)/10000) 2 ≤ ((17166 : ℚ)/10000) ∧
    1 ≤ ((55647 : ℚ)/10000) ∧ ((17166 : ℚ)/10000)+27/100-1/(2*((55647 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 260
  rw [bjsSmallPrefixQ_value260]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow261 : bjsSmallPrefixCertificate 261 := by
  change (2 : ℚ)^8 ≤ (261 : ℚ)+1 ∧
    bjsLogUpper ((261 : ℚ)+1) 8 ≤ ((55685 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55685 : ℚ)/10000) ∧ bjsLogUpper ((55685 : ℚ)/10000) 2 ≤ ((17173 : ℚ)/10000) ∧
    1 ≤ ((55685 : ℚ)/10000) ∧ ((17173 : ℚ)/10000)+27/100-1/(2*((55685 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 261
  rw [bjsSmallPrefixQ_value261]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow262 : bjsSmallPrefixCertificate 262 := by
  change (2 : ℚ)^8 ≤ (262 : ℚ)+1 ∧
    bjsLogUpper ((262 : ℚ)+1) 8 ≤ ((55723 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55723 : ℚ)/10000) ∧ bjsLogUpper ((55723 : ℚ)/10000) 2 ≤ ((17180 : ℚ)/10000) ∧
    1 ≤ ((55723 : ℚ)/10000) ∧ ((17180 : ℚ)/10000)+27/100-1/(2*((55723 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 262
  rw [bjsSmallPrefixQ_value262]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow263 : bjsSmallPrefixCertificate 263 := by
  change (2 : ℚ)^8 ≤ (263 : ℚ)+1 ∧
    bjsLogUpper ((263 : ℚ)+1) 8 ≤ ((55761 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55761 : ℚ)/10000) ∧ bjsLogUpper ((55761 : ℚ)/10000) 2 ≤ ((17186 : ℚ)/10000) ∧
    1 ≤ ((55761 : ℚ)/10000) ∧ ((17186 : ℚ)/10000)+27/100-1/(2*((55761 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 263
  rw [bjsSmallPrefixQ_value263]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow264 : bjsSmallPrefixCertificate 264 := by
  change (2 : ℚ)^8 ≤ (264 : ℚ)+1 ∧
    bjsLogUpper ((264 : ℚ)+1) 8 ≤ ((55799 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55799 : ℚ)/10000) ∧ bjsLogUpper ((55799 : ℚ)/10000) 2 ≤ ((17193 : ℚ)/10000) ∧
    1 ≤ ((55799 : ℚ)/10000) ∧ ((17193 : ℚ)/10000)+27/100-1/(2*((55799 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 264
  rw [bjsSmallPrefixQ_value264]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow265 : bjsSmallPrefixCertificate 265 := by
  change (2 : ℚ)^8 ≤ (265 : ℚ)+1 ∧
    bjsLogUpper ((265 : ℚ)+1) 8 ≤ ((55836 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55836 : ℚ)/10000) ∧ bjsLogUpper ((55836 : ℚ)/10000) 2 ≤ ((17200 : ℚ)/10000) ∧
    1 ≤ ((55836 : ℚ)/10000) ∧ ((17200 : ℚ)/10000)+27/100-1/(2*((55836 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 265
  rw [bjsSmallPrefixQ_value265]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow266 : bjsSmallPrefixCertificate 266 := by
  change (2 : ℚ)^8 ≤ (266 : ℚ)+1 ∧
    bjsLogUpper ((266 : ℚ)+1) 8 ≤ ((55874 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55874 : ℚ)/10000) ∧ bjsLogUpper ((55874 : ℚ)/10000) 2 ≤ ((17207 : ℚ)/10000) ∧
    1 ≤ ((55874 : ℚ)/10000) ∧ ((17207 : ℚ)/10000)+27/100-1/(2*((55874 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 266
  rw [bjsSmallPrefixQ_value266]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow267 : bjsSmallPrefixCertificate 267 := by
  change (2 : ℚ)^8 ≤ (267 : ℚ)+1 ∧
    bjsLogUpper ((267 : ℚ)+1) 8 ≤ ((55911 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55911 : ℚ)/10000) ∧ bjsLogUpper ((55911 : ℚ)/10000) 2 ≤ ((17213 : ℚ)/10000) ∧
    1 ≤ ((55911 : ℚ)/10000) ∧ ((17213 : ℚ)/10000)+27/100-1/(2*((55911 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 267
  rw [bjsSmallPrefixQ_value267]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow268 : bjsSmallPrefixCertificate 268 := by
  change (2 : ℚ)^8 ≤ (268 : ℚ)+1 ∧
    bjsLogUpper ((268 : ℚ)+1) 8 ≤ ((55949 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55949 : ℚ)/10000) ∧ bjsLogUpper ((55949 : ℚ)/10000) 2 ≤ ((17220 : ℚ)/10000) ∧
    1 ≤ ((55949 : ℚ)/10000) ∧ ((17220 : ℚ)/10000)+27/100-1/(2*((55949 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 268
  rw [bjsSmallPrefixQ_value268]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow269 : bjsSmallPrefixCertificate 269 := by
  change (2 : ℚ)^8 ≤ (269 : ℚ)+1 ∧
    bjsLogUpper ((269 : ℚ)+1) 8 ≤ ((55986 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((55986 : ℚ)/10000) ∧ bjsLogUpper ((55986 : ℚ)/10000) 2 ≤ ((17227 : ℚ)/10000) ∧
    1 ≤ ((55986 : ℚ)/10000) ∧ ((17227 : ℚ)/10000)+27/100-1/(2*((55986 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 269
  rw [bjsSmallPrefixQ_value269]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow270 : bjsSmallPrefixCertificate 270 := by
  change (2 : ℚ)^8 ≤ (270 : ℚ)+1 ∧
    bjsLogUpper ((270 : ℚ)+1) 8 ≤ ((56023 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56023 : ℚ)/10000) ∧ bjsLogUpper ((56023 : ℚ)/10000) 2 ≤ ((17233 : ℚ)/10000) ∧
    1 ≤ ((56023 : ℚ)/10000) ∧ ((17233 : ℚ)/10000)+27/100-1/(2*((56023 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 270
  rw [bjsSmallPrefixQ_value270]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow271 : bjsSmallPrefixCertificate 271 := by
  change (2 : ℚ)^8 ≤ (271 : ℚ)+1 ∧
    bjsLogUpper ((271 : ℚ)+1) 8 ≤ ((56060 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56060 : ℚ)/10000) ∧ bjsLogUpper ((56060 : ℚ)/10000) 2 ≤ ((17240 : ℚ)/10000) ∧
    1 ≤ ((56060 : ℚ)/10000) ∧ ((17240 : ℚ)/10000)+27/100-1/(2*((56060 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 271
  rw [bjsSmallPrefixQ_value271]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow272 : bjsSmallPrefixCertificate 272 := by
  change (2 : ℚ)^8 ≤ (272 : ℚ)+1 ∧
    bjsLogUpper ((272 : ℚ)+1) 8 ≤ ((56096 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56096 : ℚ)/10000) ∧ bjsLogUpper ((56096 : ℚ)/10000) 2 ≤ ((17246 : ℚ)/10000) ∧
    1 ≤ ((56096 : ℚ)/10000) ∧ ((17246 : ℚ)/10000)+27/100-1/(2*((56096 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 272
  rw [bjsSmallPrefixQ_value272]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow273 : bjsSmallPrefixCertificate 273 := by
  change (2 : ℚ)^8 ≤ (273 : ℚ)+1 ∧
    bjsLogUpper ((273 : ℚ)+1) 8 ≤ ((56133 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56133 : ℚ)/10000) ∧ bjsLogUpper ((56133 : ℚ)/10000) 2 ≤ ((17253 : ℚ)/10000) ∧
    1 ≤ ((56133 : ℚ)/10000) ∧ ((17253 : ℚ)/10000)+27/100-1/(2*((56133 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 273
  rw [bjsSmallPrefixQ_value273]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow274 : bjsSmallPrefixCertificate 274 := by
  change (2 : ℚ)^8 ≤ (274 : ℚ)+1 ∧
    bjsLogUpper ((274 : ℚ)+1) 8 ≤ ((56169 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56169 : ℚ)/10000) ∧ bjsLogUpper ((56169 : ℚ)/10000) 2 ≤ ((17259 : ℚ)/10000) ∧
    1 ≤ ((56169 : ℚ)/10000) ∧ ((17259 : ℚ)/10000)+27/100-1/(2*((56169 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 274
  rw [bjsSmallPrefixQ_value274]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow275 : bjsSmallPrefixCertificate 275 := by
  change (2 : ℚ)^8 ≤ (275 : ℚ)+1 ∧
    bjsLogUpper ((275 : ℚ)+1) 8 ≤ ((56206 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56206 : ℚ)/10000) ∧ bjsLogUpper ((56206 : ℚ)/10000) 2 ≤ ((17266 : ℚ)/10000) ∧
    1 ≤ ((56206 : ℚ)/10000) ∧ ((17266 : ℚ)/10000)+27/100-1/(2*((56206 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 275
  rw [bjsSmallPrefixQ_value275]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow276 : bjsSmallPrefixCertificate 276 := by
  change (2 : ℚ)^8 ≤ (276 : ℚ)+1 ∧
    bjsLogUpper ((276 : ℚ)+1) 8 ≤ ((56242 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56242 : ℚ)/10000) ∧ bjsLogUpper ((56242 : ℚ)/10000) 2 ≤ ((17272 : ℚ)/10000) ∧
    1 ≤ ((56242 : ℚ)/10000) ∧ ((17272 : ℚ)/10000)+27/100-1/(2*((56242 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 276
  rw [bjsSmallPrefixQ_value276]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow277 : bjsSmallPrefixCertificate 277 := by
  change (2 : ℚ)^8 ≤ (277 : ℚ)+1 ∧
    bjsLogUpper ((277 : ℚ)+1) 8 ≤ ((56278 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56278 : ℚ)/10000) ∧ bjsLogUpper ((56278 : ℚ)/10000) 2 ≤ ((17279 : ℚ)/10000) ∧
    1 ≤ ((56278 : ℚ)/10000) ∧ ((17279 : ℚ)/10000)+27/100-1/(2*((56278 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 277
  rw [bjsSmallPrefixQ_value277]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow278 : bjsSmallPrefixCertificate 278 := by
  change (2 : ℚ)^8 ≤ (278 : ℚ)+1 ∧
    bjsLogUpper ((278 : ℚ)+1) 8 ≤ ((56314 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56314 : ℚ)/10000) ∧ bjsLogUpper ((56314 : ℚ)/10000) 2 ≤ ((17285 : ℚ)/10000) ∧
    1 ≤ ((56314 : ℚ)/10000) ∧ ((17285 : ℚ)/10000)+27/100-1/(2*((56314 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 278
  rw [bjsSmallPrefixQ_value278]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow279 : bjsSmallPrefixCertificate 279 := by
  change (2 : ℚ)^8 ≤ (279 : ℚ)+1 ∧
    bjsLogUpper ((279 : ℚ)+1) 8 ≤ ((56349 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56349 : ℚ)/10000) ∧ bjsLogUpper ((56349 : ℚ)/10000) 2 ≤ ((17291 : ℚ)/10000) ∧
    1 ≤ ((56349 : ℚ)/10000) ∧ ((17291 : ℚ)/10000)+27/100-1/(2*((56349 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 279
  rw [bjsSmallPrefixQ_value279]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow280 : bjsSmallPrefixCertificate 280 := by
  change (2 : ℚ)^8 ≤ (280 : ℚ)+1 ∧
    bjsLogUpper ((280 : ℚ)+1) 8 ≤ ((56385 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56385 : ℚ)/10000) ∧ bjsLogUpper ((56385 : ℚ)/10000) 2 ≤ ((17298 : ℚ)/10000) ∧
    1 ≤ ((56385 : ℚ)/10000) ∧ ((17298 : ℚ)/10000)+27/100-1/(2*((56385 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 280
  rw [bjsSmallPrefixQ_value280]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow281 : bjsSmallPrefixCertificate 281 := by
  change (2 : ℚ)^8 ≤ (281 : ℚ)+1 ∧
    bjsLogUpper ((281 : ℚ)+1) 8 ≤ ((56421 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56421 : ℚ)/10000) ∧ bjsLogUpper ((56421 : ℚ)/10000) 2 ≤ ((17304 : ℚ)/10000) ∧
    1 ≤ ((56421 : ℚ)/10000) ∧ ((17304 : ℚ)/10000)+27/100-1/(2*((56421 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 281
  rw [bjsSmallPrefixQ_value281]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow282 : bjsSmallPrefixCertificate 282 := by
  change (2 : ℚ)^8 ≤ (282 : ℚ)+1 ∧
    bjsLogUpper ((282 : ℚ)+1) 8 ≤ ((56456 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56456 : ℚ)/10000) ∧ bjsLogUpper ((56456 : ℚ)/10000) 2 ≤ ((17310 : ℚ)/10000) ∧
    1 ≤ ((56456 : ℚ)/10000) ∧ ((17310 : ℚ)/10000)+27/100-1/(2*((56456 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 282
  rw [bjsSmallPrefixQ_value282]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow283 : bjsSmallPrefixCertificate 283 := by
  change (2 : ℚ)^8 ≤ (283 : ℚ)+1 ∧
    bjsLogUpper ((283 : ℚ)+1) 8 ≤ ((56491 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56491 : ℚ)/10000) ∧ bjsLogUpper ((56491 : ℚ)/10000) 2 ≤ ((17316 : ℚ)/10000) ∧
    1 ≤ ((56491 : ℚ)/10000) ∧ ((17316 : ℚ)/10000)+27/100-1/(2*((56491 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 283
  rw [bjsSmallPrefixQ_value283]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow284 : bjsSmallPrefixCertificate 284 := by
  change (2 : ℚ)^8 ≤ (284 : ℚ)+1 ∧
    bjsLogUpper ((284 : ℚ)+1) 8 ≤ ((56526 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56526 : ℚ)/10000) ∧ bjsLogUpper ((56526 : ℚ)/10000) 2 ≤ ((17323 : ℚ)/10000) ∧
    1 ≤ ((56526 : ℚ)/10000) ∧ ((17323 : ℚ)/10000)+27/100-1/(2*((56526 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 284
  rw [bjsSmallPrefixQ_value284]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow285 : bjsSmallPrefixCertificate 285 := by
  change (2 : ℚ)^8 ≤ (285 : ℚ)+1 ∧
    bjsLogUpper ((285 : ℚ)+1) 8 ≤ ((56561 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56561 : ℚ)/10000) ∧ bjsLogUpper ((56561 : ℚ)/10000) 2 ≤ ((17329 : ℚ)/10000) ∧
    1 ≤ ((56561 : ℚ)/10000) ∧ ((17329 : ℚ)/10000)+27/100-1/(2*((56561 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 285
  rw [bjsSmallPrefixQ_value285]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

private theorem bjsSmallPrefixRow286 : bjsSmallPrefixCertificate 286 := by
  change (2 : ℚ)^8 ≤ (286 : ℚ)+1 ∧
    bjsLogUpper ((286 : ℚ)+1) 8 ≤ ((56596 : ℚ)/10000) ∧
    (2 : ℚ)^2 ≤ ((56596 : ℚ)/10000) ∧ bjsLogUpper ((56596 : ℚ)/10000) 2 ≤ ((17335 : ℚ)/10000) ∧
    1 ≤ ((56596 : ℚ)/10000) ∧ ((17335 : ℚ)/10000)+27/100-1/(2*((56596 : ℚ)/10000)^2) ≤ bjsSmallPrefixQ 286
  rw [bjsSmallPrefixQ_value286]
  norm_num [bjsLogUpper, Finset.sum_range_succ]

theorem bjsSmallPrefixCertificates :
    ∀ n : Fin 287, 2 ≤ n.val → bjsSmallPrefixCertificate n.val := by
  intro n hn
  fin_cases n
  · norm_num at hn
  · norm_num at hn
  · exact bjsSmallPrefixRow002
  · exact bjsSmallPrefixRow003
  · exact bjsSmallPrefixRow004
  · exact bjsSmallPrefixRow005
  · exact bjsSmallPrefixRow006
  · exact bjsSmallPrefixRow007
  · exact bjsSmallPrefixRow008
  · exact bjsSmallPrefixRow009
  · exact bjsSmallPrefixRow010
  · exact bjsSmallPrefixRow011
  · exact bjsSmallPrefixRow012
  · exact bjsSmallPrefixRow013
  · exact bjsSmallPrefixRow014
  · exact bjsSmallPrefixRow015
  · exact bjsSmallPrefixRow016
  · exact bjsSmallPrefixRow017
  · exact bjsSmallPrefixRow018
  · exact bjsSmallPrefixRow019
  · exact bjsSmallPrefixRow020
  · exact bjsSmallPrefixRow021
  · exact bjsSmallPrefixRow022
  · exact bjsSmallPrefixRow023
  · exact bjsSmallPrefixRow024
  · exact bjsSmallPrefixRow025
  · exact bjsSmallPrefixRow026
  · exact bjsSmallPrefixRow027
  · exact bjsSmallPrefixRow028
  · exact bjsSmallPrefixRow029
  · exact bjsSmallPrefixRow030
  · exact bjsSmallPrefixRow031
  · exact bjsSmallPrefixRow032
  · exact bjsSmallPrefixRow033
  · exact bjsSmallPrefixRow034
  · exact bjsSmallPrefixRow035
  · exact bjsSmallPrefixRow036
  · exact bjsSmallPrefixRow037
  · exact bjsSmallPrefixRow038
  · exact bjsSmallPrefixRow039
  · exact bjsSmallPrefixRow040
  · exact bjsSmallPrefixRow041
  · exact bjsSmallPrefixRow042
  · exact bjsSmallPrefixRow043
  · exact bjsSmallPrefixRow044
  · exact bjsSmallPrefixRow045
  · exact bjsSmallPrefixRow046
  · exact bjsSmallPrefixRow047
  · exact bjsSmallPrefixRow048
  · exact bjsSmallPrefixRow049
  · exact bjsSmallPrefixRow050
  · exact bjsSmallPrefixRow051
  · exact bjsSmallPrefixRow052
  · exact bjsSmallPrefixRow053
  · exact bjsSmallPrefixRow054
  · exact bjsSmallPrefixRow055
  · exact bjsSmallPrefixRow056
  · exact bjsSmallPrefixRow057
  · exact bjsSmallPrefixRow058
  · exact bjsSmallPrefixRow059
  · exact bjsSmallPrefixRow060
  · exact bjsSmallPrefixRow061
  · exact bjsSmallPrefixRow062
  · exact bjsSmallPrefixRow063
  · exact bjsSmallPrefixRow064
  · exact bjsSmallPrefixRow065
  · exact bjsSmallPrefixRow066
  · exact bjsSmallPrefixRow067
  · exact bjsSmallPrefixRow068
  · exact bjsSmallPrefixRow069
  · exact bjsSmallPrefixRow070
  · exact bjsSmallPrefixRow071
  · exact bjsSmallPrefixRow072
  · exact bjsSmallPrefixRow073
  · exact bjsSmallPrefixRow074
  · exact bjsSmallPrefixRow075
  · exact bjsSmallPrefixRow076
  · exact bjsSmallPrefixRow077
  · exact bjsSmallPrefixRow078
  · exact bjsSmallPrefixRow079
  · exact bjsSmallPrefixRow080
  · exact bjsSmallPrefixRow081
  · exact bjsSmallPrefixRow082
  · exact bjsSmallPrefixRow083
  · exact bjsSmallPrefixRow084
  · exact bjsSmallPrefixRow085
  · exact bjsSmallPrefixRow086
  · exact bjsSmallPrefixRow087
  · exact bjsSmallPrefixRow088
  · exact bjsSmallPrefixRow089
  · exact bjsSmallPrefixRow090
  · exact bjsSmallPrefixRow091
  · exact bjsSmallPrefixRow092
  · exact bjsSmallPrefixRow093
  · exact bjsSmallPrefixRow094
  · exact bjsSmallPrefixRow095
  · exact bjsSmallPrefixRow096
  · exact bjsSmallPrefixRow097
  · exact bjsSmallPrefixRow098
  · exact bjsSmallPrefixRow099
  · exact bjsSmallPrefixRow100
  · exact bjsSmallPrefixRow101
  · exact bjsSmallPrefixRow102
  · exact bjsSmallPrefixRow103
  · exact bjsSmallPrefixRow104
  · exact bjsSmallPrefixRow105
  · exact bjsSmallPrefixRow106
  · exact bjsSmallPrefixRow107
  · exact bjsSmallPrefixRow108
  · exact bjsSmallPrefixRow109
  · exact bjsSmallPrefixRow110
  · exact bjsSmallPrefixRow111
  · exact bjsSmallPrefixRow112
  · exact bjsSmallPrefixRow113
  · exact bjsSmallPrefixRow114
  · exact bjsSmallPrefixRow115
  · exact bjsSmallPrefixRow116
  · exact bjsSmallPrefixRow117
  · exact bjsSmallPrefixRow118
  · exact bjsSmallPrefixRow119
  · exact bjsSmallPrefixRow120
  · exact bjsSmallPrefixRow121
  · exact bjsSmallPrefixRow122
  · exact bjsSmallPrefixRow123
  · exact bjsSmallPrefixRow124
  · exact bjsSmallPrefixRow125
  · exact bjsSmallPrefixRow126
  · exact bjsSmallPrefixRow127
  · exact bjsSmallPrefixRow128
  · exact bjsSmallPrefixRow129
  · exact bjsSmallPrefixRow130
  · exact bjsSmallPrefixRow131
  · exact bjsSmallPrefixRow132
  · exact bjsSmallPrefixRow133
  · exact bjsSmallPrefixRow134
  · exact bjsSmallPrefixRow135
  · exact bjsSmallPrefixRow136
  · exact bjsSmallPrefixRow137
  · exact bjsSmallPrefixRow138
  · exact bjsSmallPrefixRow139
  · exact bjsSmallPrefixRow140
  · exact bjsSmallPrefixRow141
  · exact bjsSmallPrefixRow142
  · exact bjsSmallPrefixRow143
  · exact bjsSmallPrefixRow144
  · exact bjsSmallPrefixRow145
  · exact bjsSmallPrefixRow146
  · exact bjsSmallPrefixRow147
  · exact bjsSmallPrefixRow148
  · exact bjsSmallPrefixRow149
  · exact bjsSmallPrefixRow150
  · exact bjsSmallPrefixRow151
  · exact bjsSmallPrefixRow152
  · exact bjsSmallPrefixRow153
  · exact bjsSmallPrefixRow154
  · exact bjsSmallPrefixRow155
  · exact bjsSmallPrefixRow156
  · exact bjsSmallPrefixRow157
  · exact bjsSmallPrefixRow158
  · exact bjsSmallPrefixRow159
  · exact bjsSmallPrefixRow160
  · exact bjsSmallPrefixRow161
  · exact bjsSmallPrefixRow162
  · exact bjsSmallPrefixRow163
  · exact bjsSmallPrefixRow164
  · exact bjsSmallPrefixRow165
  · exact bjsSmallPrefixRow166
  · exact bjsSmallPrefixRow167
  · exact bjsSmallPrefixRow168
  · exact bjsSmallPrefixRow169
  · exact bjsSmallPrefixRow170
  · exact bjsSmallPrefixRow171
  · exact bjsSmallPrefixRow172
  · exact bjsSmallPrefixRow173
  · exact bjsSmallPrefixRow174
  · exact bjsSmallPrefixRow175
  · exact bjsSmallPrefixRow176
  · exact bjsSmallPrefixRow177
  · exact bjsSmallPrefixRow178
  · exact bjsSmallPrefixRow179
  · exact bjsSmallPrefixRow180
  · exact bjsSmallPrefixRow181
  · exact bjsSmallPrefixRow182
  · exact bjsSmallPrefixRow183
  · exact bjsSmallPrefixRow184
  · exact bjsSmallPrefixRow185
  · exact bjsSmallPrefixRow186
  · exact bjsSmallPrefixRow187
  · exact bjsSmallPrefixRow188
  · exact bjsSmallPrefixRow189
  · exact bjsSmallPrefixRow190
  · exact bjsSmallPrefixRow191
  · exact bjsSmallPrefixRow192
  · exact bjsSmallPrefixRow193
  · exact bjsSmallPrefixRow194
  · exact bjsSmallPrefixRow195
  · exact bjsSmallPrefixRow196
  · exact bjsSmallPrefixRow197
  · exact bjsSmallPrefixRow198
  · exact bjsSmallPrefixRow199
  · exact bjsSmallPrefixRow200
  · exact bjsSmallPrefixRow201
  · exact bjsSmallPrefixRow202
  · exact bjsSmallPrefixRow203
  · exact bjsSmallPrefixRow204
  · exact bjsSmallPrefixRow205
  · exact bjsSmallPrefixRow206
  · exact bjsSmallPrefixRow207
  · exact bjsSmallPrefixRow208
  · exact bjsSmallPrefixRow209
  · exact bjsSmallPrefixRow210
  · exact bjsSmallPrefixRow211
  · exact bjsSmallPrefixRow212
  · exact bjsSmallPrefixRow213
  · exact bjsSmallPrefixRow214
  · exact bjsSmallPrefixRow215
  · exact bjsSmallPrefixRow216
  · exact bjsSmallPrefixRow217
  · exact bjsSmallPrefixRow218
  · exact bjsSmallPrefixRow219
  · exact bjsSmallPrefixRow220
  · exact bjsSmallPrefixRow221
  · exact bjsSmallPrefixRow222
  · exact bjsSmallPrefixRow223
  · exact bjsSmallPrefixRow224
  · exact bjsSmallPrefixRow225
  · exact bjsSmallPrefixRow226
  · exact bjsSmallPrefixRow227
  · exact bjsSmallPrefixRow228
  · exact bjsSmallPrefixRow229
  · exact bjsSmallPrefixRow230
  · exact bjsSmallPrefixRow231
  · exact bjsSmallPrefixRow232
  · exact bjsSmallPrefixRow233
  · exact bjsSmallPrefixRow234
  · exact bjsSmallPrefixRow235
  · exact bjsSmallPrefixRow236
  · exact bjsSmallPrefixRow237
  · exact bjsSmallPrefixRow238
  · exact bjsSmallPrefixRow239
  · exact bjsSmallPrefixRow240
  · exact bjsSmallPrefixRow241
  · exact bjsSmallPrefixRow242
  · exact bjsSmallPrefixRow243
  · exact bjsSmallPrefixRow244
  · exact bjsSmallPrefixRow245
  · exact bjsSmallPrefixRow246
  · exact bjsSmallPrefixRow247
  · exact bjsSmallPrefixRow248
  · exact bjsSmallPrefixRow249
  · exact bjsSmallPrefixRow250
  · exact bjsSmallPrefixRow251
  · exact bjsSmallPrefixRow252
  · exact bjsSmallPrefixRow253
  · exact bjsSmallPrefixRow254
  · exact bjsSmallPrefixRow255
  · exact bjsSmallPrefixRow256
  · exact bjsSmallPrefixRow257
  · exact bjsSmallPrefixRow258
  · exact bjsSmallPrefixRow259
  · exact bjsSmallPrefixRow260
  · exact bjsSmallPrefixRow261
  · exact bjsSmallPrefixRow262
  · exact bjsSmallPrefixRow263
  · exact bjsSmallPrefixRow264
  · exact bjsSmallPrefixRow265
  · exact bjsSmallPrefixRow266
  · exact bjsSmallPrefixRow267
  · exact bjsSmallPrefixRow268
  · exact bjsSmallPrefixRow269
  · exact bjsSmallPrefixRow270
  · exact bjsSmallPrefixRow271
  · exact bjsSmallPrefixRow272
  · exact bjsSmallPrefixRow273
  · exact bjsSmallPrefixRow274
  · exact bjsSmallPrefixRow275
  · exact bjsSmallPrefixRow276
  · exact bjsSmallPrefixRow277
  · exact bjsSmallPrefixRow278
  · exact bjsSmallPrefixRow279
  · exact bjsSmallPrefixRow280
  · exact bjsSmallPrefixRow281
  · exact bjsSmallPrefixRow282
  · exact bjsSmallPrefixRow283
  · exact bjsSmallPrefixRow284
  · exact bjsSmallPrefixRow285
  · exact bjsSmallPrefixRow286

end ChenEffective
