import GRHJointBounds
import GRHSharpRootMoment
import GRHDivisorMoments
import DusartPort.Application
import BJSH30MertensProduct
import MathlibNt.SieveTheory.Switching.RosserSieveAsymptotics
import NumericalSingularNormalization
import NumericalUniversalTail
import NumericalGenuineLiPointwise
import ExplicitLogBounds
import GRHSourceTail
import NumericalWeightedMass
import GRHTruncatedSieveBounds
import GRHPrimeAPMaxima
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean
import MathlibNt.SieveTheory.LinearSieve.Richert.Richert1969Ordinary418Specialization
import NumericalPreSieveDistribution
import NumericalLowerFactor
import SharperSieveDensity
import NumericalBaseCandidates
import ChenBudget
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import BJSHybridProductBridge
import NumericalPreSieveCounting
import NumericalPrimePairInterval
import NumericalUpperFactor
import NumericalPrimePairGrid
import NumericalPanAggregate
import NumericalPanBudget
import BJSH30PanQuotient
import BJSH30PanPrimePrefix
import NumericalPrincipalPNT
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrincipalMoving
import BJSH30PanLedger
import BJSH30PanPrincipal
import BJSH30PanUnweighted
import BJSH30PanWeighted
import BJSH30PanNormalization
import BJSH30PanR1
import MathlibNt.SieveTheory.Switching.WeightedCounting
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries
import MathlibNt.ChensTheorem
import BJSExpandedDenominator
import ExplicitChenTriple
import Goldbach.Statement
import GRHQuarterTruncatedBounds
import GRHConditionedQuarterTail
set_option maxErrors 100

/-! Complete analytic propagation to the candidate 3^119081 cutoff.
Grouped to avoid repeatedly loading the common analytic environment. -/
set_option maxErrors 100

/- Grouped source: GRHQuarterChenBudget -/

noncomputable section
namespace ChenEffective.GRHQuarterChenBudget
open Real
set_option maxHeartbeats 3000000

/-- Specialize to the logarithmic degree actually used by the low moving
lane, rather than paying the old unused degree-100 box. -/

private opaque exponentCertificate : {n : ℕ // n=119081} := ⟨119081,rfl⟩
def targetExponent : ℕ := exponentCertificate.1
theorem targetExponent_eq : targetExponent=119081 := exponentCertificate.2
def targetCutoff : ℕ := 3^targetExponent
theorem target_log_lower {N : ℕ} (hN : targetCutoff≤ N) : (130690:ℝ)≤ log (N:ℝ) := by
  have hpow : (2:ℝ)^84≤(3:ℝ)^53 := by norm_num
  have hh := log_le_log (by positivity : (0:ℝ)<(2:ℝ)^84) hpow
  rw [log_pow,log_pow] at hh
  have h3 : (439/400:ℝ)≤ log 3 := by
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh,log_two_gt_d9]
  have he : (0:ℝ)<(targetCutoff:ℕ) := by
    exact_mod_cast (show 0<targetCutoff by unfold targetCutoff; positivity)
  have hl := log_le_log he (show (targetCutoff:ℝ)≤ N by exact_mod_cast hN)
  simp only [targetCutoff,Nat.cast_pow,Nat.cast_ofNat,log_pow] at hl
  rw [targetExponent_eq] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl,h3]

theorem targetCutoff_lt_double_exp_13 : (targetCutoff:ℝ)<exp (exp (13:ℝ)) := by
  have he1 : (2718/1000:ℝ)≤ exp 1 := by linarith only [exp_one_gt_d9]
  have he11 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 11
  rw [← exp_nat_mul] at he11
  norm_num only [Nat.cast_ofNat,mul_one] at he11
  have h311 : (3:ℝ)^10≤ exp 11 := by norm_num at he11 ⊢; linarith only [he11]
  have hlog3 := log_le_log (by positivity : (0:ℝ)<(3:ℝ)^10) h311
  rw [log_pow,log_exp] at hlog3
  have hlog : log (targetCutoff:ℝ)≤131000 := by
    simp only [targetCutoff,Nat.cast_pow,Nat.cast_ofNat,log_pow]
    rw [targetExponent_eq]
    norm_num only [Nat.cast_ofNat] at hlog3 ⊢
    linarith only [hlog3]
  have he13 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 13
  rw [← exp_nat_mul] at he13
  norm_num only [Nat.cast_ofNat,mul_one] at he13
  have he : (131000:ℝ)<exp (13:ℝ) := by norm_num at he13; linarith only [he13]
  have htpos : (0:ℝ)<(targetCutoff:ℕ) := by
    exact_mod_cast (show 0<targetCutoff by unfold targetCutoff; positivity)
  apply (log_lt_log_iff htpos (exp_pos _)).mp
  rw [log_exp]
  exact hlog.trans_lt he

theorem targetCutoff_lt_double_exp_12 : (targetCutoff:ℝ)<exp (exp (12:ℝ)) := by
  have he1 : (2718/1000:ℝ)≤ exp 1 := by linarith only [exp_one_gt_d9]
  have he11 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 11
  rw [← exp_nat_mul] at he11
  norm_num only [Nat.cast_ofNat,mul_one] at he11
  have h311 : (3:ℝ)^10≤ exp 11 := by norm_num at he11 ⊢; linarith only [he11]
  have hlog3 := log_le_log (by positivity : (0:ℝ)<(3:ℝ)^10) h311
  rw [log_pow,log_exp] at hlog3
  have hlog : log (targetCutoff:ℝ)≤131000 := by
    simp only [targetCutoff,Nat.cast_pow,Nat.cast_ofNat,log_pow]
    rw [targetExponent_eq]
    norm_num only [Nat.cast_ofNat] at hlog3 ⊢
    linarith only [hlog3]
  have he12 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 12
  rw [← exp_nat_mul] at he12
  norm_num only [Nat.cast_ofNat,mul_one] at he12
  have he : (131000:ℝ)<exp 12 := by norm_num at he12; linarith only [he12]
  have htpos : (0:ℝ)<(targetCutoff:ℕ) := by exact_mod_cast (show 0<targetCutoff by unfold targetCutoff; positivity)
  apply (log_lt_log_iff htpos (exp_pos _)).mp
  rw [log_exp]
  exact hlog.trans_lt he

theorem targetCutoff_lt_double_exp_13_37 : (targetCutoff:ℝ)<exp (exp (1337/100:ℝ)) :=
  targetCutoff_lt_double_exp_13.trans (exp_lt_exp.mpr (exp_lt_exp.mpr (by norm_num)))

theorem pan_log_log_cap {L : ℝ} (hL : (130690:ℝ)≤ L) : log L≤ L/10880 := by
  have hl : 0<L := by linarith only [hL]
  have he1 : (2718/1000:ℝ)≤ exp 1 := by linarith only [exp_one_gt_d9]
  have he12 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 12
  rw [← exp_nat_mul] at he12
  norm_num only [Nat.cast_ofNat,mul_one] at he12
  have hb : (130690:ℝ)≤ exp 12 := by norm_num at he12; linarith only [he12]
  have hlog := log_le_log (by norm_num : (0:ℝ)<130690) hb
  rw [log_exp] at hlog
  have hh := log_le_sub_one_of_pos (show 0<L/130690 by positivity)
  rw [log_div hl.ne' (by norm_num : (130690:ℝ)≠0)] at hh
  linarith only [hh,hlog,hL]

end ChenEffective.GRHQuarterChenBudget


/- Grouped source: GRHQuarterChenTruncationPayment -/

/-! Direct payment of the complete pre-sieve error envelope. The old
intermediate exponential decay rate is deliberately not required. -/
noncomputable section
namespace ChenEffective.GRHQuarterChenBudget
open Real
set_option maxHeartbeats 3000000

theorem sharp_medium_truncation_payment {L : ℝ} (hL : 130690 ≤ L) :
    336*L^6*exp ((1799/100:ℝ)+log 2/4-13*L/10000) ≤ (1e-12:ℝ) := by
  have hLp : 0<L := by linarith only [hL]
  have he1 : (2718/1000:ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
  have he14 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 12
  rw [← exp_nat_mul] at he14
  norm_num only [Nat.cast_ofNat,mul_one] at he14
  have hn14 : (130690:ℝ) ≤ (2718/1000:ℝ)^13 := by norm_num
  have hlog14 : log (130690:ℝ) ≤ 12 := by
    have hx : (130690:ℝ)≤ exp 12 := by norm_num at he14; linarith only [he14]
    have hh := log_le_log (by norm_num : (0:ℝ)<130690) hx
    rwa [log_exp] at hh
  have hratio := log_le_sub_one_of_pos (div_pos hLp (by norm_num : (0:ℝ)<130690))
  rw [log_div hLp.ne' (by norm_num)] at hratio
  have hlog : 6*log L ≤ L/10000+60 := by
    linarith only [hratio,hlog14,hL]
  have he6 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 6
  rw [← exp_nat_mul] at he6
  norm_num only [Nat.cast_ofNat,mul_one] at he6
  have hn6 : (336:ℝ) ≤ (2718/1000:ℝ)^6 := by norm_num
  have hc : (336:ℝ) ≤ exp 6 := by norm_num at he6; linarith only [he6]
  have hl2 : log (2:ℝ) ≤ 1 := by
    linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hpoly : L^6=exp (6*log L) := by
    have hh := exp_nat_mul (log L) 6
    norm_num only [Nat.cast_ofNat] at hh
    rw [exp_log hLp] at hh
    exact hh.symm
  have he30 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 30
  rw [← exp_nat_mul] at he30
  norm_num only [Nat.cast_ofNat,mul_one] at he30
  have hn30 : (1e12:ℝ) ≤ (2718/1000:ℝ)^30 := by norm_num
  have hsmall : exp (-30:ℝ) ≤ (1e-12:ℝ) := by
    have hx : (1e12:ℝ)≤ exp 30 := by norm_num at he30; linarith only [he30]
    have hh := mul_le_mul_of_nonneg_right hx (exp_pos (-30:ℝ)).le
    rw [← exp_add] at hh
    norm_num at hh
    linarith only [hh]
  calc
    _ ≤ exp 6*L^6*exp ((1799/100:ℝ)+log 2/4-13*L/10000) := by gcongr
    _ = exp (6+6*log L+(1799/100:ℝ)+log 2/4-13*L/10000) := by
      rw [hpoly,← exp_add,← exp_add]
      congr 1
      ring
    _ ≤ exp (-30:ℝ) := exp_le_exp.mpr (by linarith only [hlog,hl2,hL])
    _ ≤ _ := hsmall

#print axioms sharp_medium_truncation_payment
end ChenEffective.GRHQuarterChenBudget


/- Grouped source: GRHQuarterChenMertens -/

/-! Preserve the proved power-decaying theta error at the very large
endpoints used by Chen, instead of absorbing it at the smallest endpoint. -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000

theorem mertens_power_payment {L : ℝ} (hL : 1000≤ L) :
    (3/4)*(17*L+16)*exp (-L/16)≤1/10000 := by
  have ht := add_one_le_exp ((L-1000)/16)
  have hlin : (3/4:ℝ)*(17*L+16)≤(3/4)*17016*exp ((L-1000)/16) := by
    nlinarith only [ht,hL]
  have he := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2)
    (by linarith only [exp_one_gt_d9] : (2:ℝ)≤ exp 1) 60
  rw [← exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat,mul_one] at he
  have hmono : exp (60:ℝ)≤ exp (1000/16:ℝ) := exp_le_exp.mpr (by norm_num)
  have hnum : (3/4:ℝ)*17016≤ exp (1000/16:ℝ)/10000 := by
    norm_num at he
    linarith only [he,hmono]
  calc
    _ ≤ ((3/4)*17016*exp ((L-1000)/16))*exp (-L/16) :=
      mul_le_mul_of_nonneg_right hlin (exp_pos _).le
    _ = ((3/4)*17016)*exp (-1000/16:ℝ) := by
      rw [mul_assoc,← exp_add]
      congr 2
      ring
    _ ≤ (exp (1000/16:ℝ)/10000)*exp (-1000/16:ℝ) :=
      mul_le_mul_of_nonneg_right hnum (exp_pos _).le
    _ = _ := by rw [div_mul_eq_mul_div,← exp_add]; norm_num

theorem sharp_mertens_large {x : ℝ} (hx : (3:ℝ)^120≤ x)
    (hlog : 1000≤ log x) :
    |primeReciprocalSum ⌊x⌋₊-(log (log x)+mertensSecondConstant)|≤
      1/(10000*(log x)^2) := by
  have hx0 : 0<x := lt_of_lt_of_le (by positivity : (0:ℝ)<3^120) hx
  have hl : 0<log x := by linarith only [hlog]
  have hx9 : 9≤ x := by linarith only [hlog,log_le_sub_one_of_pos hx0]
  have hh := bjsStudy_mertens_of_theta_target hx9
    (fun _t ht => Dusart.numerical_theta_target (hx.trans ht))
  apply hh.trans
  have hr : x^(-1/16:ℝ)=exp (-log x/16) := by
    rw [rpow_def_of_pos hx0]
    congr 1
    ring
  rw [hr,div_mul_eq_mul_div]
  have hp := mertens_power_payment hlog
  have heq : (1:ℝ)/(10000*(log x)^2)=(1/10000)/(log x)^2 := by ring
  rw [heq]
  exact div_le_div_of_nonneg_right hp (sq_nonneg _)

#print axioms sharp_mertens_large
end ChenEffective.GRHQuarterChen


/- Grouped source: GRHQuarterChenMertensProduct -/

noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real
open AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def mertensProductThreshold (r : ℕ) : ℕ := max (logPowerCutoff 2) (3^(Nat.sqrt (6*r)+2))

theorem numerical_mertens_product {n r : ℕ} (hr : 0<r)
    (hn : mertensProductThreshold r≤ n) :
    |primeProduct n*log (n:ℝ)*exp eulerMascheroniConstant-1|≤1/(r:ℝ) := by
  have hc : logPowerCutoff 2≤ n := (le_max_left _ _).trans hn
  have hp : 3^(Nat.sqrt (6*r)+2)≤ n := (le_max_right _ _).trans hn
  have hn9 : 9≤ n := (logPowerCutoff_nine_le _).trans hc
  have hl : 0<log (n:ℝ) := log_pos (by exact_mod_cast (show 1<n by omega))
  have hrR : (1:ℝ)≤ r := by exact_mod_cast hr
  have hL := log_ge_power_three hp
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hL
  have hpay : 6/log (n:ℝ)^2≤1/(r:ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hl) (by positivity : (0:ℝ)<r)).mpr
    have hs := Nat.lt_succ_sqrt' (6*r)
    have hsR : (6:ℝ)*r < ((Nat.sqrt (6*r):ℝ)+1)^2 := by exact_mod_cast hs
    have ht : ((Nat.sqrt (6*r):ℝ)+1)^2 ≤ log (n:ℝ)^2 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith only [hL]
    linarith only [hsR,ht]
  let E := log (primeProduct n)+log (log (n:ℝ))+eulerMascheroniConstant
  have he : |E|≤3/log (n:ℝ)^2 := H30.sharp_mertens_product_log hc
  have he1 : |E|≤1 := by
    have hi : 1/(r:ℝ)≤1 := div_le_self (by norm_num) hrR
    have hh : 2*(3/log (n:ℝ)^2)≤1/(r:ℝ) := by
      calc
        _ = 6/log (n:ℝ)^2 := by ring
        _ ≤ _ := hpay
    linarith only [he,hh,hi,abs_nonneg E]
  have hb := (abs_exp_sub_one_le he1).trans (mul_le_mul_of_nonneg_left he (by norm_num))
  have hid : exp E=primeProduct n*log (n:ℝ)*exp eulerMascheroniConstant := by
    dsimp only [E]
    rw [exp_add,exp_add,exp_log (primeProduct_pos n),exp_log hl]
  rw [hid] at hb
  exact hb.trans (by
    calc
      _ = 6/log (n:ℝ)^2 := by ring
      _ ≤ _ := hpay)

#print axioms numerical_mertens_product
end ChenEffective.GRHQuarterChen


/- Grouped source: GRHQuarterChenGoldbachProduct -/

namespace ChenEffective.GRHQuarterChen
open Real
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def chenProductThreshold (r : ℕ) : ℕ := (mertensProductThreshold r + 1) ^ 10

theorem numerical_source_cutoff {N k : ℕ} (hk : 2 ≤ k) (hN : (k + 1) ^ 10 ≤ N) :
    k ≤ jurkatRichertSourceZ N - 1 := by
  have hh := correctedChenZ_sub_one_ge_of_N_ge hk hN
  unfold correctedChenZ at hh
  unfold jurkatRichertSourceZ
  omega

theorem numerical_chen_prime_product_lower {N r : ℕ} (hr : 0 < r)
    (hN : chenProductThreshold r ≤ N) :
    10 * (1 - 1 / (r : ℝ)) * Real.exp (-Real.eulerMascheroniConstant) /
        Real.log (N : ℝ) ≤
      AnalyticNumberTheory.Mertens.primeProduct (jurkatRichertSourceZ N - 1) := by
  let n := jurkatRichertSourceZ N - 1
  let P := AnalyticNumberTheory.Mertens.primeProduct n
  have hcut9 : 9 ≤ mertensProductThreshold r :=
    (logPowerCutoff_nine_le _).trans (le_max_left _ _)
  have hn : mertensProductThreshold r ≤ n := numerical_source_cutoff (by omega) hN
  have hn9 : 9 ≤ n := hcut9.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnf : (n : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    dsimp [n, jurkatRichertSourceZ]
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hNpos : 0 < N := by
    have hh : 0 < chenProductThreshold r := pow_pos (Nat.succ_pos _) 10
    omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : 1 < (N : ℝ) := by
    by_contra hh
    have hpow : (N : ℝ) ^ (1 / 10 : ℝ) ≤ 1 := Real.rpow_le_one hN0.le (by linarith) (by norm_num)
    have hh9 : (9 : ℝ) ≤ n := by exact_mod_cast hn9
    linarith only [hnf, hpow, hh9]
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hl : Real.log (n : ℝ) ≤ (1 / 10 : ℝ) * Real.log (N : ℝ) := by
    have hh := Real.log_le_log hn0 hnf
    rwa [Real.log_rpow hN0] at hh
  have hp0 : 0 ≤ P := (AnalyticNumberTheory.Mertens.primeProduct_pos n).le
  have hb := (abs_le.mp (numerical_mertens_product hr hn)).1
  have he := mul_le_mul_of_nonneg_left hl (mul_nonneg hp0 (Real.exp_pos Real.eulerMascheroniConstant).le)
  have hbase : 1 - 1 / (r : ℝ) ≤ P * ((1 / 10 : ℝ) * Real.log (N : ℝ)) *
      Real.exp Real.eulerMascheroniConstant := by
    change -(1 / (r : ℝ)) ≤ P * Real.log (n : ℝ) * Real.exp Real.eulerMascheroniConstant - 1 at hb
    nlinarith only [hb, he]
  have hscale := mul_le_mul_of_nonneg_right hbase
    (show 0 ≤ 10 * Real.exp (-Real.eulerMascheroniConstant) by positivity)
  have hexp : Real.exp Real.eulerMascheroniConstant * Real.exp (-Real.eulerMascheroniConstant) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  apply (div_le_iff₀ hlN).mpr
  change _ ≤ P * Real.log (N : ℝ)
  calc
    _ ≤ (P * ((1 / 10 : ℝ) * Real.log (N : ℝ)) * Real.exp Real.eulerMascheroniConstant) *
        (10 * Real.exp (-Real.eulerMascheroniConstant)) := by nlinarith only [hscale]
    _ = P * Real.log (N : ℝ) := by
      calc
        _ = P * Real.log (N : ℝ) *
            (Real.exp Real.eulerMascheroniConstant * Real.exp (-Real.eulerMascheroniConstant)) := by ring
        _ = _ := by rw [hexp, mul_one]

/-- Numerical Mertens normalization at Chen's literal finite source cutoff. -/
theorem numerical_source_goldbach_product_lower {N r : ℕ} (hr : 0 < r)
    (hN : chenProductThreshold r ≤ N) (hEven : Even N) :
    10 * (1 - 1 / (r : ℝ)) * Real.exp (-Real.eulerMascheroniConstant) *
        SingularSeries.singularSeriesTruncated N (jurkatRichertSourceZ N - 1) /
        Real.log (N : ℝ) ≤
      MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
  have hcut9 : 9 ≤ mertensProductThreshold r :=
    (logPowerCutoff_nine_le _).trans (le_max_left _ _)
  have hz := numerical_source_cutoff (by omega : 2 ≤ mertensProductThreshold r) hN
  have hS := SingularSeries.singularSeriesTruncated_pos N (jurkatRichertSourceZ N - 1) (by omega)
  rw [MertensTheorem.sieveProduct_identity N _ (by omega) hEven,
    MertensTheorem.primeProduct_eq_analyticNumberTheory]
  have hh := mul_le_mul_of_nonneg_right (numerical_chen_prime_product_lower hr hN) hS.le
  calc
    _ = (10 * (1 - 1 / (r : ℝ)) * Real.exp (-Real.eulerMascheroniConstant) /
        Real.log (N : ℝ)) *
        SingularSeries.singularSeriesTruncated N (jurkatRichertSourceZ N - 1) := by ring
    _ ≤ _ := hh

#print axioms numerical_source_goldbach_product_lower
end ChenEffective.GRHQuarterChen


/- Grouped source: GRHQuarterChenSourceMass -/

namespace ChenEffective.GRHQuarterChen
open Real
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def sourceMassThreshold (r : ℕ) : ℕ :=
  max (chenProductThreshold r) (singularNormalizationThreshold r)

/-- Numerical source mass, including the genuine Liu singular-series normalization. -/
theorem numerical_source_mass_lower {N r : ℕ} (hr : 0 < r)
    (hN : sourceMassThreshold r ≤ N) (hEven : Even N) :
    (20 * Real.exp (-Real.eulerMascheroniConstant) - 40 / (r : ℝ)) *
        SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) ≤
      (jurkatRichertSourceBoundingSieve N).totalMass *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) := by
  have hNP : chenProductThreshold r ≤ N := (le_max_left _ _).trans hN
  have hNS : singularNormalizationThreshold r ≤ N := (le_max_right _ _).trans hN
  have hNbig : 2 ^ 110 + 1 ≤ N := (le_max_left _ _).trans hNS
  have hN2 : 2 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let t : ℝ := 1 / (r : ℝ)
  let e : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  let S := SingularSeries.liuSingularSeries N
  let T := SingularSeries.singularSeriesTruncated N (jurkatRichertSourceZ N - 1)
  let V := MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := div_le_self (by norm_num) (by exact_mod_cast hr)
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [Real.one_half_lt_eulerMascheroniConstant])
  have hS0 : 0 ≤ S := (SingularSeries.liuSingularSeries_pos N).le
  have hT0 : 0 ≤ T := by
    apply le_of_lt (SingularSeries.singularSeriesTruncated_pos N _ ?_)
    have hcut9 : 9 ≤ mertensProductThreshold r :=
      (logPowerCutoff_nine_le _).trans (le_max_left _ _)
    have hh := numerical_source_cutoff (by omega : 2 ≤ mertensProductThreshold r) hNP
    omega
  have hseries : 2 * S ≤ (1 + t) * T := numerical_source_singular_lower hr hNS hEven
  have hprod : 10 * (1 - t) * e * T / Real.log (N : ℝ) ≤ V :=
    numerical_source_goldbach_product_lower hr hNP hEven
  have hST : 2 * (1 - t) * S ≤ T := by
    have hh := mul_le_mul_of_nonneg_left hseries (sub_nonneg.mpr ht1)
    have hp := mul_nonneg (sq_nonneg t) hT0
    nlinarith only [hh, hp]
  have hnorm : 20 * (1 - t) ^ (2 : ℕ) * e * S / Real.log (N : ℝ) ≤ V := by
    calc
      _ = (10 * (1 - t) * e / Real.log (N : ℝ)) * (2 * (1 - t) * S) := by ring
      _ ≤ (10 * (1 - t) * e / Real.log (N : ℝ)) * T :=
        mul_le_mul_of_nonneg_left hST (by positivity)
      _ = 10 * (1 - t) * e * T / Real.log (N : ℝ) := by ring
      _ ≤ _ := hprod
  have hV0 : 0 ≤ V :=
    (by positivity : 0 ≤ 20 * (1 - t) ^ (2 : ℕ) * e * S / Real.log (N : ℝ)).trans hnorm
  have hmass : (N : ℝ) / Real.log (N : ℝ) ≤
      (jurkatRichertSourceBoundingSieve N).totalMass :=
    LiuWeight.div_log_le_liuLogarithmicIntegral (by exact_mod_cast hN2)
  have hpay : 20 * e - 40 / (r : ℝ) ≤ 20 * (1 - t) ^ (2 : ℕ) * e := by
    have hh := mul_nonneg ht0 (sub_nonneg.mpr he1)
    have hp := mul_nonneg he0 (sq_nonneg t)
    change 20 * e - 40 / (r : ℝ) ≤ _
    rw [show (40 : ℝ) / r = 40 * t by dsimp [t]; ring]
    nlinarith only [hh, hp]
  rw [jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct N hEven]
  change _ ≤ (jurkatRichertSourceBoundingSieve N).totalMass * V
  calc
    _ ≤ 20 * (1 - t) ^ (2 : ℕ) * e * S * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpay hS0) hN0.le)
        (sq_nonneg _)
    _ = ((N : ℝ) / Real.log (N : ℝ)) *
        (20 * (1 - t) ^ (2 : ℕ) * e * S / Real.log (N : ℝ)) := by ring
    _ ≤ ((N : ℝ) / Real.log (N : ℝ)) * V :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hmass hV0

/-- One concrete coefficient budget; no analytic witness remains in its threshold. -/
theorem numerical_source_mass_one_40000 {N : ℕ}
    (hN : sourceMassThreshold 1600000 ≤ N) (hEven : Even N) :
    (20 * Real.exp (-Real.eulerMascheroniConstant) - 1 / 40000) *
        SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) ≤
      (jurkatRichertSourceBoundingSieve N).totalMass *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) := by
  simpa only [Nat.cast_ofNat, show (40 : ℝ) / 1600000 = 1 / 40000 by norm_num] using
    numerical_source_mass_lower (r := 1600000) (by norm_num) hN hEven

#print axioms numerical_source_mass_lower
#print axioms numerical_source_mass_one_40000
end ChenEffective.GRHQuarterChen


/- Grouped source: GRHQuarterChenSourceUpperMass -/

noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
attribute [local irreducible] logPowerCutoff mertensProductThreshold chenProductThreshold

def sourceUpperMassThreshold (r : ℕ) : ℕ :=
  max (chenProductThreshold r)
    (max ((2*r+1)^10) (max (3^(40*r+1)) (logPowerCutoff 2)))

theorem numerical_source_prime_product_upper {N r : ℕ} (hr : 0 < r)
    (hN : sourceUpperMassThreshold r ≤ N) :
    AnalyticNumberTheory.Mertens.primeProduct (jurkatRichertSourceZ N-1) ≤
      10*(1+1/(r : ℝ))^2*Real.exp (-Real.eulerMascheroniConstant)/Real.log (N : ℝ) := by
  let n := jurkatRichertSourceZ N-1
  have hM9 : 9 ≤ mertensProductThreshold r := by
    unfold mertensProductThreshold
    exact (logPowerCutoff_nine_le 2).trans (le_max_left _ _)
  have hn : mertensProductThreshold r ≤ n := numerical_source_cutoff (by omega)
    (by simpa only [chenProductThreshold] using (show chenProductThreshold r ≤ N from (le_max_left _ _).trans hN))
  have hnr : 2*r ≤ n := numerical_source_cutoff (by omega : 2 ≤ 2*r)
    ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hn2 : 2 ≤ n := by omega
  have hL : 40*(r : ℝ) ≤ Real.log (N : ℝ) := by
    have hh := log_ge_power_three ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
    push_cast at hh
    linarith only [hh]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hNpos : 0 < N := by
    have h := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
    have h9 := (logPowerCutoff_nine_le 2).trans h
    omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hl0 : 0 < Real.log (N : ℝ) := by linarith only [hL,hr1]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hfloor : (N : ℝ)^(1/10 : ℝ) ≤ 2*(n : ℝ) := by
    have hh : (N : ℝ)^(1/10 : ℝ) < (n : ℝ)+1 := by
      simpa only [n,jurkatRichertSourceZ,Nat.add_sub_cancel] using Nat.lt_floor_add_one ((N : ℝ)^(1/10 : ℝ))
    linarith only [hh,hnR]
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hN0 _) hfloor
  rw [Real.log_rpow hN0,Real.log_mul (by norm_num) hn0.ne'] at hlog
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hcoef : Real.log (N : ℝ) ≤ 10*(1+1/(r : ℝ))*Real.log (n : ℝ) := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have he : (r : ℝ)*(1+1/(r : ℝ)) = (r : ℝ)+1 := by field_simp
    apply (mul_le_mul_iff_left₀ hr0).mp
    have hh := mul_le_mul_of_nonneg_left (show Real.log (N : ℝ)/10-1 ≤ Real.log (n : ℝ) by linarith only [hlog,hlog2])
      (show 0 ≤ (r : ℝ)+1 by positivity)
    rw [show 10*(1+1/(r : ℝ))*Real.log (n : ℝ)*(r : ℝ) = 10*((r : ℝ)*(1+1/(r : ℝ)))*Real.log (n : ℝ) by ring,he]
    nlinarith only [hh,hL,hr1]
  have hP0 := (AnalyticNumberTheory.Mertens.primeProduct_pos n).le
  have hupper := (abs_le.mp (numerical_mertens_product hr hn)).2
  have hmul := mul_le_mul_of_nonneg_left hcoef
    (show 0 ≤ AnalyticNumberTheory.Mertens.primeProduct n*Real.exp Real.eulerMascheroniConstant by positivity)
  have hExp : Real.exp Real.eulerMascheroniConstant*Real.exp (-Real.eulerMascheroniConstant)=1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hfirst : AnalyticNumberTheory.Mertens.primeProduct n*Real.log (N : ℝ)*Real.exp Real.eulerMascheroniConstant ≤
      10*(1+1/(r : ℝ))^2 := by
    have hh := mul_le_mul_of_nonneg_left (show
      AnalyticNumberTheory.Mertens.primeProduct n*Real.log (n : ℝ)*Real.exp Real.eulerMascheroniConstant ≤ 1+1/(r : ℝ) by linarith only [hupper])
      (show 0 ≤ 10*(1+1/(r : ℝ)) by positivity)
    nlinarith only [hh,hmul]
  apply (le_div_iff₀ hl0).mpr
  have hh := mul_le_mul_of_nonneg_right hfirst (Real.exp_pos (-Real.eulerMascheroniConstant)).le
  calc
    _ = (AnalyticNumberTheory.Mertens.primeProduct n*Real.log (N : ℝ)*Real.exp Real.eulerMascheroniConstant)*Real.exp (-Real.eulerMascheroniConstant) := by rw [mul_assoc, mul_assoc,hExp,mul_one]
    _ ≤ _ := hh

theorem numerical_liu_mass_upper {N r : ℕ} (hr : 0 < r)
    (hN : sourceUpperMassThreshold r ≤ N) :
    LiuWeight.liuLogarithmicIntegral (2/Real.log 2) N ≤ (1+1/(r : ℝ))*N/Real.log (N : ℝ) := by
  have hcut : logPowerCutoff 2 ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have h9 := (logPowerCutoff_nine_le 2).trans hcut
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hL : 40*(r : ℝ) ≤ Real.log (N : ℝ) := by
    have hh := log_ge_power_three ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
    push_cast at hh
    linarith only [hh]
  have hh := (abs_le.mp (numerical_genuine_li_pointwise (x := (N : ℝ)) (by exact_mod_cast hcut))).2
  have heq : LiuWeight.liuLogarithmicIntegral (2/Real.log 2) N = LiuWeight.liuLogarithmicIntegral 2 N+(2/Real.log 2-2) := by
    unfold LiuWeight.liuLogarithmicIntegral
    ring
  have hconst : (2 : ℝ)/Real.log 2-2 ≤ 2 := by
    have h := Real.log_two_gt_d9
    have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hh : (2 : ℝ)/Real.log 2 ≤ 4 := (div_le_iff₀ hl2).mpr (by linarith only [h])
    linarith only [hh]
  have hscale : 1 ≤ (N : ℝ)/Real.log (N : ℝ)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hl0)).mpr
    simpa only [one_mul] using (log_pow_le_sqrt_explicit hcut).trans (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1 ≤ N by omega))))
  have hpay : 12/Real.log (N : ℝ) ≤ 1/(r : ℝ) := by
    apply (div_le_div_iff₀ hl0 (by exact_mod_cast hr : (0 : ℝ) < r)).mpr
    linarith only [hL]
  have hmul := mul_le_mul_of_nonneg_right hpay (div_nonneg hN0.le hl0.le)
  unfold LiuWeight.liuLogarithmicIntegralRemainder at hh
  rw [heq]
  simp only [div_eq_mul_inv,← inv_pow] at hh hscale hmul hconst ⊢
  nlinarith only [hh,hconst,hscale,hmul]

/-- Common density of every conditioned source, with a numerical relative budget. -/
theorem numerical_source_mass_upper {N r : ℕ} (hr : 0 < r) (hr10 : 10≤ r)
    (hN : sourceUpperMassThreshold r ≤ N) (hEven : Even N) :
    (jurkatRichertSourceBoundingSieve N).totalMass*
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) ≤
      (jurkatRichertMertensFactor+(125/2)/(r : ℝ))*
        (SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2) := by
  have hcut : logPowerCutoff 2 ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have h9 := (logPowerCutoff_nine_le 2).trans hcut
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let n := jurkatRichertSourceZ N-1
  have hn : 2*r ≤ n := numerical_source_cutoff (by omega : 2 ≤ 2*r)
    ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hn2 : 2 ≤ n := by omega
  have hz3 : 3 ≤ jurkatRichertSourceZ N := by dsimp [n] at hn2; omega
  let t : ℝ := 1/(r : ℝ)
  let e := Real.exp (-Real.eulerMascheroniConstant)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1/10 := by
    dsimp [t]
    exact one_div_le_one_div_of_le (by norm_num : (0:ℝ)<10) (by exact_mod_cast hr10)
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ (5/8:ℝ) := by
    have hh := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤1/2) 3
    norm_num [Finset.sum_range_succ,Nat.factorial] at hh
    have hg : exp (1/2:ℝ)≤ exp eulerMascheroniConstant := exp_le_exp.mpr (by linarith only [Real.one_half_lt_eulerMascheroniConstant])
    have hp := mul_le_mul_of_nonneg_right (hh.trans hg) (exp_pos (-eulerMascheroniConstant)).le
    rw [← exp_add] at hp
    norm_num at hp
    dsimp only [e]
    linarith only [hp]
  have hs := numerical_singular_truncated_upper (by omega : 0 < N) hr hn
  have htrunc : SingularSeries.singularSeriesTruncated N n ≤
      2*(1+t)*SingularSeries.liuSingularSeries N := by
    rw [SingularSeries.singularSeriesTruncated_eq_two_mul_liuSingularSeriesTruncated N n hEven hn2]
    change _ ≤ 2*(1+1/(r : ℝ))*SingularSeries.liuSingularSeries N
    nlinarith only [hs]
  have hp := numerical_source_prime_product_upper hr hN
  have hprod : MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) ≤
      20*e*(1+t)^3*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) := by
    rw [MertensTheorem.sieveProduct_identity N _ (by omega : 2 ≤ jurkatRichertSourceZ N) hEven,MertensTheorem.primeProduct_eq_analyticNumberTheory]
    have hh := mul_le_mul hp htrunc (SingularSeries.singularSeriesTruncated_pos N n (by omega : 1 ≤ n)).le
      (show 0 ≤ 10*(1+1/(r : ℝ))^2*Real.exp (-Real.eulerMascheroniConstant)/Real.log (N : ℝ) by positivity)
    calc
      _ = AnalyticNumberTheory.Mertens.primeProduct (jurkatRichertSourceZ N-1)*SingularSeries.singularSeriesTruncated N n := by ring
      _ ≤ (10*(1+1/(r : ℝ))^2*Real.exp (-Real.eulerMascheroniConstant)/Real.log (N : ℝ))*
          (2*(1+t)*SingularSeries.liuSingularSeries N) := hh
      _ = _ := by dsimp [t,e]; ring
  have hli := numerical_liu_mass_upper hr hN
  have hV0 : 0 ≤ MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
    rw [← jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct N hEven]
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    exact prod_nonneg (fun p hp => sub_nonneg.mpr
      ((jurkatRichertSourceBoundingSieve N).nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
        ((Nat.mem_primeFactors_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp).2).le)
  have hh := mul_le_mul hli hprod hV0 (show 0 ≤ (1+1/(r : ℝ))*(N : ℝ)/Real.log (N : ℝ) by positivity)
  have h2 : t^2 ≤ t/10 := by nlinarith only [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have h3 : t^3 ≤ t/100 := by nlinarith only [mul_le_mul_of_nonneg_left h2 ht0,h2]
  have h4 : t^4 ≤ t/1000 := by nlinarith only [mul_le_mul_of_nonneg_left h3 ht0,h2]
  have hpoly : (1+t)^4 ≤ 1+5*t := by nlinarith only [h2,h3,h4]
  have hcoef : 20*e*(1+t)^4 ≤ jurkatRichertMertensFactor+(125/2)/(r : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ 20*e by positivity)
    change _ ≤ 20*e+(125/2)/(r : ℝ)
    have he := mul_nonneg ht0 (sub_nonneg.mpr he1)
    rw [show (125/2 : ℝ)/(r : ℝ)=(125/2)*t by dsimp [t]; ring]
    nlinarith only [h,he]
  have hS0 := (SingularSeries.liuSingularSeries_pos N).le
  have hM : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 := by positivity
  have hpay := mul_le_mul_of_nonneg_right hcoef hM
  rw [jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct N hEven]
  change LiuWeight.liuLogarithmicIntegral (2/Real.log 2) N*_ ≤ _
  apply hh.trans
  calc
    _ = (20*e*(1+t)^4)*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by dsimp [t]; ring
    _ ≤ _ := hpay

#print axioms numerical_source_prime_product_upper
#print axioms numerical_liu_mass_upper
#print axioms numerical_source_mass_upper
end ChenEffective.GRHQuarterChen


/- Grouped source: GRHQuarterChenAnalytic -/

/-! Smaller-cutoff analytic assembly. Components are grouped to avoid
repeated loading of the common analytic environment. The certificate-inclusive
Chen theorem and axiom audit are in AuditGRHQuarterChenChen. -/
set_option maxErrors 100

/- Component: GRHQuarterChenErrorBudget -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real
set_option maxHeartbeats 3000000
def targetExponent : ℕ := GRHQuarterChenBudget.targetExponent
theorem targetExponent_eq : targetExponent=119081 := GRHQuarterChenBudget.targetExponent_eq
def targetCutoff : ℕ := 3^targetExponent
theorem targetCutoff_eq : targetCutoff=3^119081 := by unfold targetCutoff; rw [targetExponent_eq]
theorem target_log_lower {N : ℕ} (hN : targetCutoff≤ N) : (130690:ℝ)≤ log (N:ℝ) := GRHQuarterChenBudget.target_log_lower hN
theorem targetCutoff_lt_double_exp_13_37 : (targetCutoff:ℝ)<exp (exp (1337/100:ℝ)) := GRHQuarterChenBudget.targetCutoff_lt_double_exp_13_37
theorem targetCutoff_lt_double_exp_14 : (targetCutoff:ℝ)<exp (exp (14:ℝ)) :=
  targetCutoff_lt_double_exp_13_37.trans (exp_lt_exp.mpr (exp_lt_exp.mpr (by norm_num)))
theorem target_nine_le {N : ℕ} (hN : targetCutoff≤ N) : 9≤ N := by
  have hl := target_log_lower hN
  have hn : 0<N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hh := log_le_sub_one_of_pos (show (0:ℝ)<N by exact_mod_cast hn)
  exact_mod_cast (by linarith only [hl,hh] : (9:ℝ)≤ N)
theorem log_power_at_target {N k : ℕ} {δ : ℝ} (hN : targetCutoff≤ N)
    (hk : k≤100) (hδ : (1/100:ℝ)≤δ) : log (N:ℝ)^k≤(N:ℝ)^δ := by
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by have := target_nine_le hN; omega)
  have hh := mul_le_mul_of_nonneg_left (GRHQuarterChenBudget.pan_log_log_cap hL) (Nat.cast_nonneg (α:=ℝ) k)
  have hkR : (k:ℝ)≤100 := by exact_mod_cast hk
  have hm := mul_le_mul_of_nonneg_right hkR (show 0≤ 29*log (N:ℝ)/500000 by positivity)
  have hd := mul_le_mul_of_nonneg_right hδ hl.le
  rw [rpow_def_of_pos hn]
  have he := exp_nat_mul (log (log (N:ℝ))) k
  rw [exp_log hl] at he
  rw [← he]
  apply exp_le_exp.mpr
  nlinarith only [hh,hm,hd,hl]
theorem polynomial_error_payment {L C α : ℝ} {k : ℕ}
    (hL : (130690:ℝ)≤ L) (hC : C≤(1e30:ℝ)) (hα : (1/500:ℝ)≤α) (hk : k≤12) :
    C*L^k*exp (-α*L)≤(1e-6:ℝ) := by
  have hl : 0<L := by linarith only [hL]
  have hlog := GRHQuarterChenBudget.pan_log_log_cap hL
  have he1 : (27/10:ℝ)≤ exp 1 := by linarith only [exp_one_gt_d9]
  have he100 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10) he1 70
  rw [← exp_nat_mul] at he100
  norm_num only [Nat.cast_ofNat,mul_one] at he100
  have hc : (1e30:ℝ)≤ exp 70 := by norm_num at he100; linarith only [he100]
  have hp : L^k≤ exp (12*L/10880) := by
    calc
      _ ≤ L^12 := pow_le_pow_right₀ (by linarith only [hL] : (1:ℝ)≤ L) hk
      _ = exp (12*log L) := by
        have he := exp_nat_mul (log L) 12
        norm_num only [Nat.cast_ofNat] at he
        rw [exp_log hl] at he
        exact he.symm
      _ ≤ _ := exp_le_exp.mpr (by linarith only [hlog])
  have he20 : (1e6:ℝ)≤ exp 30 := by
    have he := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10) he1 30
    rw [← exp_nat_mul] at he
    norm_num at he ⊢
    linarith only [he]
  have hs : exp (-30:ℝ)≤(1e-6:ℝ) := by
    have h := mul_le_mul_of_nonneg_right he20 (exp_pos (-30:ℝ)).le
    rw [← exp_add] at h
    norm_num at h
    linarith only [h]
  calc
    _ ≤ exp 70*exp (12*L/10880)*exp (-α*L) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hC.trans hc) hp (pow_nonneg hl.le _) (exp_pos _).le) (exp_pos _).le
    _ = exp (70+12*L/10880-α*L) := by rw [← exp_add,← exp_add]; congr 1; ring
    _ ≤ exp (-30:ℝ) := exp_le_exp.mpr (by nlinarith only [hL,mul_nonneg hl.le (sub_nonneg.mpr hα)])
    _ ≤ _ := hs
theorem distribution_error_payment {L C α : ℝ} {k : ℕ}
    (hL : (130690:ℝ)≤ L) (hC : C≤(1e30:ℝ)) (hα : (1/500:ℝ)≤α) (hk : k≤12) :
    C*L^k*exp (-α*L)≤(1e-6:ℝ) := polynomial_error_payment hL hC hα hk
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenSourceMassCaps -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 256

theorem small_power_le_target {a : ℕ} (ha : a ≤ 3^20) : a^10 ≤ targetCutoff := by
  rw [targetCutoff_eq]
  calc
    _ ≤ ((3:ℕ)^20)^10 := Nat.pow_le_pow_left ha 10
    _ = 3^200 := by rw [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem source_product_threshold_cap {r : ℕ} (hr : r ≤ 20000000) :
    chenProductThreshold r ≤ targetCutoff := by
  have hm : mertensProductThreshold r ≤ 3^11000 := by
    unfold mertensProductThreshold
    apply max_le
    · unfold logPowerCutoff
      apply Nat.pow_le_pow_right (by norm_num)
      norm_num
    · apply Nat.pow_le_pow_right (by norm_num)
      have hs : Nat.sqrt (6*r) < 10999 := Nat.sqrt_lt.mpr (by nlinarith only [hr])
      omega
  have hplus : mertensProductThreshold r+1 ≤ 3^11001 := by
    have hp : 1 ≤ (3:ℕ)^11000 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [show (11001:ℕ)=11000+1 by norm_num,Nat.pow_succ]
    omega
  unfold chenProductThreshold
  rw [targetCutoff_eq]
  calc
    _ ≤ ((3:ℕ)^11001)^10 := Nat.pow_le_pow_left hplus 10
    _ = 3^110010 := by rw [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem source_lower_mass_threshold_cap {r : ℕ} (hr : r ≤ 20000000) :
    sourceMassThreshold r ≤ targetCutoff := by
  unfold sourceMassThreshold
  apply max_le (source_product_threshold_cap hr)
  unfold singularNormalizationThreshold
  apply max_le
  · have hh : (2:ℕ)^110+1 ≤ 3^100 := by norm_num
    apply hh.trans
    rw [targetCutoff_eq]
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · apply small_power_le_target
    nlinarith only [hr]

theorem source_upper_mass_threshold_cap {r : ℕ} (hr : r ≤ 2977) :
    sourceUpperMassThreshold r ≤ targetCutoff := by
  unfold sourceUpperMassThreshold
  apply max_le (source_product_threshold_cap (by omega))
  apply max_le (small_power_le_target (by nlinarith only [hr]))
  apply max_le
  · rw [targetCutoff_eq]
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  · rw [targetCutoff_eq]
    unfold logPowerCutoff
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem source_mass_at_target {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    (20*exp (-eulerMascheroniConstant)-(1/500000:ℝ))*
        (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) ≤
      (jurkatRichertSourceBoundingSieve N).totalMass*
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) ∧
    (jurkatRichertSourceBoundingSieve N).totalMass*
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) ≤
      (jurkatRichertMertensFactor+(21/1000:ℝ))*
        (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  constructor
  · have hh := numerical_source_mass_lower (r:=20000000) (by norm_num)
      ((source_lower_mass_threshold_cap (by norm_num)).trans hN) hEven
    convert hh using 1 <;> norm_num <;> ring
  · have hh := numerical_source_mass_upper (r:=2977) (by norm_num) (by norm_num)
      ((source_upper_mass_threshold_cap (by norm_num)).trans hN) hEven
    have hM0 : 0≤ SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2 := by positivity [SingularSeries.liuSingularSeries_pos N]
    norm_num at hh
    nlinarith only [hh,hM0]

#print axioms source_mass_at_target
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenTruncationBudget -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real
set_option maxHeartbeats 3000000

theorem truncated_polynomial_payment {L A α : ℝ} {k : ℕ}
    (hL : (130690:ℝ)≤ L) (hA : A≤(1e30:ℝ)) (hα : (1/500:ℝ)≤α) (hk : k≤12) :
    A*L^k*exp (-α*L)≤(1e-6:ℝ) := polynomial_error_payment hL hA hα hk

noncomputable def preSieveTruncation (N : ℕ) : ℕ :=
  Nat.floor ((N:ℝ)^(13/2500:ℝ))

theorem truncation_log_lower {N : ℕ} (hN : targetCutoff ≤ N) :
    0 < preSieveTruncation N ∧
    26*log (N:ℝ)/5000-log 2 ≤ log (preSieveTruncation N:ℝ) := by
  have hL := target_log_lower hN
  have hn : 0 < N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hnR : (0:ℝ) < N := by exact_mod_cast hn
  let x := (N:ℝ)^(13/2500:ℝ)
  have hx : 0 < x := rpow_pos_of_pos hnR _
  have hlogx : log x=26*log (N:ℝ)/5000 := by
    dsimp only [x]
    rw [log_rpow hnR]
    ring
  have hl2 : log (2:ℝ) ≤ 1 := by
    linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hx2 : (2:ℝ) ≤ x := by
    apply (log_le_log_iff (by norm_num : (0:ℝ) < 2) hx).mp
    rw [hlogx]
    linarith only [hL,hl2]
  have hc : 0 < preSieveTruncation N := Nat.floor_pos.mpr (by linarith only [hx2])
  have hf : x < (preSieveTruncation N:ℝ)+1 := Nat.lt_floor_add_one x
  have hhalf : x/2 ≤ (preSieveTruncation N:ℝ) := by linarith only [hf,hx2]
  refine ⟨hc,?_⟩
  have hh := log_le_log (div_pos hx (by norm_num)) hhalf
  rw [log_div hx.ne' (by norm_num),hlogx] at hh
  exact hh

theorem truncation_tail_at_target {N : ℕ} (hN : targetCutoff≤ N) :
    exp (1799/100:ℝ)/H10Band.quarterRoot (preSieveTruncation N:ℝ)≤ exp ((1799/100:ℝ)+log 2/4-13*log (N:ℝ)/10000) := by
  have hc := truncation_log_lower hN
  have hCp : (0:ℝ)<preSieveTruncation N := by exact_mod_cast hc.1
  have hr : 1/H10Band.quarterRoot (preSieveTruncation N:ℝ)=exp (-log (preSieveTruncation N:ℝ)/4) := by
    rw [H10Band.quarterRoot_rpow hCp.le,rpow_def_of_pos hCp,one_div,← exp_neg]
    congr 1
    ring
  rw [div_eq_mul_one_div,hr,← exp_add]
  apply exp_le_exp.mpr
  linarith only [hc.2]
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenLowerGeometry -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

noncomputable def lowerDelta (N q : ℕ) : ℝ :=
  (N:ℝ)^(1241/2500:ℝ)/(2*(q:ℝ)*(preSieveTruncation N:ℝ))
noncomputable def lowerLevel (N q : ℕ) : ℕ := Nat.floor (lowerDelta N q)+1
noncomputable def lowerRatio (N q : ℕ) : ℝ :=
  log (lowerDelta N q)/log ((N:ℝ)^(1/10:ℝ))

theorem truncation_log_upper {N : ℕ} (hN : targetCutoff ≤ N) :
    log (preSieveTruncation N:ℝ) ≤ 26*log (N:ℝ)/5000 := by
  have hn : 0<N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hc : (0:ℝ)<preSieveTruncation N := by
    exact_mod_cast (truncation_log_lower hN).1
  have hh := log_le_log hc (Nat.floor_le (rpow_nonneg (Nat.cast_nonneg N) (13/2500:ℝ)))
  rw [log_rpow hnR] at hh
  convert hh using 1 <;> ring

theorem lower_ratio_shift {N q : ℕ} (hN : targetCutoff ≤ N) (hq : 0<q) :
    0 ≤ (5-10*(log (q:ℝ)/log (N:ℝ)))-lowerRatio N q ∧
    (5-10*(log (q:ℝ)/log (N:ℝ)))-lowerRatio N q ≤ 89/1000 := by
  have hL := target_log_lower hN
  have hLp : 0<log (N:ℝ) := by linarith only [hL]
  have hn : 0<N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hc : (0:ℝ)<preSieveTruncation N := by exact_mod_cast (truncation_log_lower hN).1
  have hcl : 0 ≤ log (preSieveTruncation N:ℝ) :=
    log_nonneg (by exact_mod_cast (truncation_log_lower hN).1)
  have hcu := truncation_log_upper hN
  have hl2 : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
  have hl2u : log (2:ℝ) ≤ 1 := by
    linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have heq : (5-10*(log (q:ℝ)/log (N:ℝ)))-lowerRatio N q =
      (9/250:ℝ)+10*(log 2+log (preSieveTruncation N:ℝ))/log (N:ℝ) := by
    unfold lowerRatio lowerDelta
    rw [log_div (rpow_pos_of_pos hnR _).ne' (by positivity),
      log_mul (by positivity : (2:ℝ)*q ≠ 0) hc.ne',
      log_mul (by norm_num : (2:ℝ) ≠ 0) hqR.ne',log_rpow hnR,log_rpow hnR]
    field_simp [hLp.ne']
    ring
  rw [heq]
  constructor
  · positivity
  · have hh : 10*(log 2+log (preSieveTruncation N:ℝ))/log (N:ℝ) ≤ 53/1000 := by
      apply (div_le_iff₀ hLp).mpr
      linarith only [hcu,hL,hl2u]
    linarith only [hh]

theorem lower_endpoint_parameters {N : ℕ} (hN : targetCutoff ≤ N) :
    2<N ∧ (2:ℝ) ≤ (N:ℝ)^(1/10:ℝ) := by
  have hL := target_log_lower hN
  have hn : 0<N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hh := log_le_sub_one_of_pos hnR
  constructor
  · exact_mod_cast (by linarith only [hh,hL] : (2:ℝ)<N)
  · apply (log_le_log_iff (by norm_num) (rpow_pos_of_pos hnR _)).mp
    rw [log_rpow hnR]
    linarith only [hL,log_two_lt_d9]

theorem lower_base_ratio {N : ℕ} (hN : targetCutoff ≤ N) :
    (4911/1000:ℝ) ≤ lowerRatio N 1 ∧ lowerRatio N 1 ≤ 5 := by
  have hh := lower_ratio_shift hN (q:=1) (by norm_num)
  norm_num only [Nat.cast_one,log_one,zero_div,mul_zero,sub_zero] at hh
  constructor <;> linarith only [hh.1,hh.2]

theorem lower_medium_ratio {N q : ℕ} (hN : targetCutoff ≤ N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
    (3/2:ℝ) ≤ lowerRatio N q ∧ lowerRatio N q ≤ 4 := by
  have hNp := (lower_endpoint_parameters hN).1
  have hqp := (mem_filter.mp hq).2.1.pos
  have hh := lower_ratio_shift hN hqp
  have hc := jurkatRichertSourceMediumPrime_log_mem (by omega : 1<N) hq
  constructor <;> linarith only [hh.1,hh.2,hc.1,hc.2]

theorem lower_level_geometry {N q : ℕ} (hN : targetCutoff ≤ N) (hq : 0<q)
    (hs : 3/2 ≤ lowerRatio N q) :
    let D := lowerLevel N q
    let Z := Nat.ceil ((D:ℝ)^(1/lowerRatio N q))
    1<D ∧ Z≤ D ∧ ((N:ℝ)^(1/10:ℝ)) < (D:ℝ)^(1/lowerRatio N q) ∧
      ((q*preSieveTruncation N*D:ℕ):ℝ) ≤ (N:ℝ)^(1241/2500:ℝ) := by
  have hz := (lower_endpoint_parameters hN).2
  have hn : 0<N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hc : (0:ℝ)<preSieveTruncation N := by exact_mod_cast (truncation_log_lower hN).1
  have hdel : 0<lowerDelta N q := by unfold lowerDelta; positivity
  obtain ⟨hD,hDelta,hroot,hZ⟩ := real_level_to_natCeil_geometry hz hdel rfl hs
  change 2≤ lowerLevel N q at hD
  refine ⟨by exact hD,?_,hroot,?_⟩
  · apply Nat.ceil_le.mpr
    exact rpow_le_self_of_one_le (by exact_mod_cast (show 1≤ lowerLevel N q by omega))
      ((div_le_one (by linarith only [hs] : 0<lowerRatio N q)).mpr (by linarith only [hs]))
  · have hlz : 0<log ((N:ℝ)^(1/10:ℝ)) := log_pos (by linarith only [hz])
    have hlog : 0<log (lowerDelta N q) := by
      have hh := (le_div_iff₀ hlz).mp hs
      nlinarith only [hh,hlz]
    have hd1 : 1≤ lowerDelta N q := (log_pos_iff hdel.le).mp hlog |>.le
    have hf := Nat.floor_le hdel.le
    have hid : ((q:ℝ)*preSieveTruncation N)*(lowerDelta N q)=(N:ℝ)^(1241/2500:ℝ)/2 := by
      unfold lowerDelta
      field_simp
    have hprod := mul_le_mul_of_nonneg_left hf (le_of_lt (mul_pos hqR hc))
    have hsmall := mul_le_mul_of_nonneg_left hd1 (le_of_lt (mul_pos hqR hc))
    change ((q*preSieveTruncation N*(Nat.floor (lowerDelta N q)+1):ℕ):ℝ) ≤ _
    push_cast
    nlinarith only [hid,hprod,hsmall]

theorem lower_level_le_endpoint {N q : ℕ} (hN : targetCutoff ≤ N) (hq : 0<q)
    (hs : 3/2≤ lowerRatio N q) : lowerLevel N q≤ N := by
  have hg := (lower_level_geometry hN hq hs).2.2.2
  have hc := (truncation_log_lower hN).1
  have hmult : lowerLevel N q≤ q*preSieveTruncation N*lowerLevel N q := by
    have hh := Nat.mul_le_mul_right (lowerLevel N q) (show 1≤ q*preSieveTruncation N from Nat.mul_pos hq hc)
    simpa only [one_mul] using hh
  have hN1 : (1:ℝ)≤ N := by exact_mod_cast (show 1≤ N by have := (lower_endpoint_parameters hN).1; omega)
  have hpow : (N:ℝ)^(1241/2500:ℝ)≤ N := rpow_le_self_of_one_le hN1 (by norm_num)
  have hmreal : (lowerLevel N q:ℝ)≤((q*preSieveTruncation N*lowerLevel N q:ℕ):ℝ) := by exact_mod_cast hmult
  exact_mod_cast hmreal.trans (hg.trans hpow)

theorem lower_level_in_source {N q : ℕ} (hN : targetCutoff ≤ N) (hq : 0<q)
    (hs : 3/2≤ lowerRatio N q) :
    preSieveTruncation N*lowerLevel N q≤ jurkatRichertSourceUpperLevel N q (9/2500:ℝ) := by
  have hg := (lower_level_geometry hN hq hs).2.2.2
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hh : ((preSieveTruncation N*lowerLevel N q:ℕ):ℝ)≤(N:ℝ)^(1241/2500:ℝ)/(q:ℝ) := by
    apply (le_div_iff₀ hqR).mpr
    simpa only [Nat.cast_mul,mul_assoc,mul_comm,mul_left_comm] using hg
  unfold jurkatRichertSourceUpperLevel
  norm_num only [show (1/2-(9/2500:ℝ))=(1241/2500:ℝ) by norm_num]
  exact (Nat.le_floor hh).trans (Nat.le_succ _)

#print axioms lower_level_geometry
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenLowerTailPayment -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem source_mass_absolute_cap {N : ℕ} (hN : targetCutoff ≤ N) :
    |(jurkatRichertSourceBoundingSieve N).totalMass| ≤ 10*(N:ℝ) := by
  have hlarge := (lower_endpoint_parameters hN).1
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hh := LiuWeight.liuLogarithmicIntegral_abs_le (2/log 2)
    (show (2:ℝ)≤ N by exact_mod_cast (show 2≤ N by omega))
  have hl2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hκ : (2:ℝ)/log 2 ≤ 4 := (div_le_iff₀ hl2).mpr (by linarith only [log_two_gt_d9])
  have hκ0 : 0≤(2:ℝ)/log 2 := by positivity
  have hc : LiuWeight.liuLogarithmicIntegralUpperConstant (2/log 2) ≤ 10 := by
    unfold LiuWeight.liuLogarithmicIntegralUpperConstant
    rw [abs_of_nonneg hκ0]
    linarith only [hκ]
  apply hh.trans
  apply (div_le_iff₀ hl).mpr
  have hh := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg N)
  nlinarith only [hh,hL,mul_nonneg (Nat.cast_nonneg N) (show 0≤ log (N:ℝ)-1 by linarith only [hL])]

theorem source_tail_paid_at_target {N D : ℕ} (hN : targetCutoff ≤ N)
    (hEven : Even N) (hD : 1≤ D) (hDN : D≤ N) :
    let S := jurkatRichertSourceBoundingSieve N
    let Q := smallSievePrimeProduct S 4000000
    let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d<D)
    (∑ d ∈ F, ∑ a ∈ Q.divisors, H10Band.quarterRoot (a:ℝ)*|S.rem (a*d)|)/
        H10Band.quarterRoot (preSieveTruncation N:ℝ) ≤ (1e-12:ℝ)*N/log (N:ℝ)^2 := by
  let L := log (N:ℝ)
  have hL : (130690:ℝ)≤ L := target_log_lower hN
  have hLp : 0<L := by linarith only [hL]
  have hm := source_mass_absolute_cap hN
  have hdecay := truncation_tail_at_target hN
  have hlogD : log (D:ℝ)≤ L :=
    log_le_log (by exact_mod_cast (show 0<D by omega)) (by exact_mod_cast hDN)
  have hlogD0 : 0≤ log (D:ℝ) := log_nonneg (by exact_mod_cast hD)
  have hpoly : (1+log (D:ℝ))^2 ≤ 4*L^2 := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+log (D:ℝ))
      (show 1+log (D:ℝ)≤2*L by linarith only [hlogD,hL]) 2
    nlinarith only [hh]
  have he : exp (1799/100:ℝ)≤ exp (1799/100:ℝ) := exp_le_exp.mpr (by norm_num)
  have hnum : (N:ℝ)*exp (1799/100:ℝ)+|(jurkatRichertSourceBoundingSieve N).totalMass| * exp (1799/100:ℝ) ≤
      11*(N:ℝ)*exp (1799/100:ℝ) := by
    have ha := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)
    have hb := mul_le_mul_of_nonneg_right hm (exp_pos (1799/100:ℝ)).le
    nlinarith only [ha,hb]
  have hpayBig := GRHQuarterChenBudget.sharp_medium_truncation_payment hL
  have hpL : L^4≤ L^6 := pow_le_pow_right₀ (by linarith only [hL] : (1:ℝ)≤ L) (by norm_num)
  have hpaySmall : (44:ℝ)*L^4*exp ((1799/100:ℝ)+log 2/4-13*L/10000)≤(1e-12:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hpL (exp_pos ((1799/100:ℝ)+log 2/4-13*L/10000)).le
    have hnon : 0≤ L^6*exp ((1799/100:ℝ)+log 2/4-13*L/10000) := by positivity
    nlinarith only [hpayBig,hh,hnon]
  have hagg := H10Band.source_quarter_tail_aggregate (lower_endpoint_parameters hN).1 hEven hD
    (C:=preSieveTruncation N)
  apply hagg.trans
  calc
    _ ≤ (11*(N:ℝ)*exp (1799/100:ℝ))*(4*L^2)/H10Band.quarterRoot (preSieveTruncation N:ℝ) := by
      apply div_le_div_of_nonneg_right _ (H10Band.quarterRoot_nonneg _)
      exact mul_le_mul hnum hpoly (sq_nonneg _) (by positivity)
    _ = (44*(N:ℝ)*L^2)*(exp (1799/100:ℝ)/H10Band.quarterRoot (preSieveTruncation N:ℝ)) := by ring
    _ ≤ (44*(N:ℝ)*L^2)*exp ((1799/100:ℝ)+log 2/4-13*L/10000) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = ((44:ℝ)*L^4*exp ((1799/100:ℝ)+log 2/4-13*L/10000))*((N:ℝ)/L^2) := by
      field_simp [hLp.ne']
    _ ≤ (1e-12:ℝ)*((N:ℝ)/L^2) := mul_le_mul_of_nonneg_right hpaySmall (by positivity)
    _ = _ := by ring

#print axioms source_tail_paid_at_target
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenMediumTailPayment -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem conditioned_mass_absolute_cap {N q : ℕ} (hN : targetCutoff ≤ N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
    |(jurkatRichertSourceConditionedBoundingSieve N q).totalMass| ≤ 20*(N:ℝ)/(q:ℝ) := by
  have hqp := (mem_filter.mp hq).2.1.two_le
  have hqR : (2:ℝ)≤ q := by exact_mod_cast hqp
  have hqm : 0<(q:ℝ)-1 := by linarith only [hqR]
  have hq0 : (0:ℝ)<q := by linarith only [hqR]
  have hm := source_mass_absolute_cap hN
  change |(jurkatRichertSourceBoundingSieve N).totalMass/((q:ℝ)-1)| ≤ _
  rw [abs_div,abs_of_nonneg hqm.le]
  apply (div_le_div_of_nonneg_right hm hqm.le).trans
  apply (div_le_div_iff₀ hqm hq0).mpr
  nlinarith only [mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hqR)]

theorem conditioned_tail_bound_at_target {N q D : ℕ} (hN : targetCutoff ≤ N)
    (hEven : Even N) (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hD : 1≤ D) (hDN : D≤ N) :
    let S := jurkatRichertSourceConditionedBoundingSieve N q
    let Q := smallSievePrimeProduct S 4000000
    let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d<D)
    (∑ d ∈ F, ∑ a ∈ Q.divisors, H10Band.quarterRoot (a:ℝ)*|S.rem (a*d)|)/H10Band.quarterRoot (preSieveTruncation N:ℝ) ≤
      (84:ℝ)*(N:ℝ)/(q:ℝ)*(log (N:ℝ))^2*exp ((1799/100:ℝ)+log 2/4-13*log (N:ℝ)/10000) := by
  have hL := target_log_lower hN
  have hm := conditioned_mass_absolute_cap hN hq
  rw [show (20:ℝ)*N/q=20*((N:ℝ)/(q:ℝ)) by ring] at hm
  have hdecay := truncation_tail_at_target hN
  have hlogD : log (D:ℝ)≤ log (N:ℝ) :=
    log_le_log (by exact_mod_cast (show 0<D by omega)) (by exact_mod_cast hDN)
  have hpoly : (1+log (D:ℝ))^2≤4*(log (N:ℝ))^2 := by
    have hh := pow_le_pow_left₀
      (show 0≤1+log (D:ℝ) by have := log_nonneg (show (1:ℝ)≤ D by exact_mod_cast hD); linarith)
      (show 1+log (D:ℝ)≤2*log (N:ℝ) by linarith only [hlogD,hL]) 2
    nlinarith only [hh]
  have he : exp (1799/100:ℝ)≤ exp (1799/100:ℝ) := exp_le_exp.mpr (by norm_num)
  have hnum : ((N:ℝ)/(q:ℝ))*exp (1799/100:ℝ)+
      |(jurkatRichertSourceConditionedBoundingSieve N q).totalMass| * exp (1799/100:ℝ) ≤
        (21:ℝ)*((N:ℝ)/(q:ℝ))*exp (1799/100:ℝ) := by
    have ha := mul_le_mul_of_nonneg_left he (show 0≤(N:ℝ)/(q:ℝ) by positivity)
    have hb := mul_le_mul_of_nonneg_right hm (exp_pos (1799/100:ℝ)).le
    nlinarith only [ha,hb]
  have hagg := H10Band.conditioned_quarter_tail_aggregate (lower_endpoint_parameters hN).1 hEven hq hD
    (C:=preSieveTruncation N)
  apply hagg.trans
  calc
    _ ≤ (21*((N:ℝ)/(q:ℝ))*exp (1799/100:ℝ))*(4*(log (N:ℝ))^2)/H10Band.quarterRoot (preSieveTruncation N:ℝ) := by
      apply div_le_div_of_nonneg_right _ (H10Band.quarterRoot_nonneg _)
      exact mul_le_mul hnum hpoly (sq_nonneg _) (by positivity)
    _ = (84*((N:ℝ)/(q:ℝ))*(log (N:ℝ))^2)*(exp (1799/100:ℝ)/H10Band.quarterRoot (preSieveTruncation N:ℝ)) := by ring
    _ ≤ (84*((N:ℝ)/(q:ℝ))*(log (N:ℝ))^2)*exp ((1799/100:ℝ)+log 2/4-13*log (N:ℝ)/10000) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = _ := by ring

theorem medium_tail_paid_at_target {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (D : ℕ → ℕ) (hD : ∀ q ∈ jurkatRichertSourceMediumPrimes N, 1≤ D q)
    (hDN : ∀ q ∈ jurkatRichertSourceMediumPrimes N, D q≤ N) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      let S := jurkatRichertSourceConditionedBoundingSieve N q
      let Q := smallSievePrimeProduct S 4000000
      let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d<D q)
      (∑ d ∈ F, ∑ a ∈ Q.divisors, H10Band.quarterRoot (a:ℝ)*|S.rem (a*d)|)/H10Band.quarterRoot (preSieveTruncation N:ℝ)) ≤
      (1e-12:ℝ)*N/log (N:ℝ)^2 := by
  let L := log (N:ℝ)
  have hL : (130690:ℝ)≤ L := target_log_lower hN
  have hLp : 0<L := by linarith only [hL]
  have hN1 : 1≤ N := by have := (lower_endpoint_parameters hN).1; omega
  have hmass := numerical_totient_weight_mass 1 hN1 (jurkatRichertSourceMediumPrimes N)
    (by
      intro q hq
      exact mem_Icc.mpr ⟨(mem_filter.mp hq).2.1.one_lt.le,
        by have hh := mem_range.mp (mem_filter.mp hq).1; omega⟩)
    (fun q hq => (mem_filter.mp hq).2.1.squarefree)
  norm_num only [Nat.cast_one,one_pow,show 2*1=2 by norm_num] at hmass
  have hrec : (∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/(q:ℝ)) ≤4*L^2 := by
    have hh : (∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/(q:ℝ))≤(1+L)^2 := by
      apply le_trans _ hmass
      apply sum_le_sum
      intro q hq
      apply one_div_le_one_div_of_le
        (by exact_mod_cast Nat.totient_pos.mpr (mem_filter.mp hq).2.1.pos)
      exact_mod_cast Nat.totient_le q
    have hp := pow_le_pow_left₀ (by linarith only [hL] : (0:ℝ)≤1+L)
      (show 1+L≤2*L by linarith only [hL]) 2
    nlinarith only [hh,hp]
  have hpay := GRHQuarterChenBudget.sharp_medium_truncation_payment hL
  calc
    _ ≤ ∑ q ∈ jurkatRichertSourceMediumPrimes N,
        (84:ℝ)*(N:ℝ)/(q:ℝ)*L^2*exp ((1799/100:ℝ)+log 2/4-13*L/10000) :=
      sum_le_sum (fun q hq => conditioned_tail_bound_at_target hN hEven hq (hD q hq) (hDN q hq))
    _ = (84*(N:ℝ)*L^2*exp ((1799/100:ℝ)+log 2/4-13*L/10000))*
        (∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/(q:ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ (84*(N:ℝ)*L^2*exp ((1799/100:ℝ)+log 2/4-13*L/10000))*(4*L^2) :=
      mul_le_mul_of_nonneg_left hrec (by positivity)
    _ = ((336:ℝ)*L^6*exp ((1799/100:ℝ)+log 2/4-13*L/10000))*((N:ℝ)/L^2) := by field_simp [hLp.ne'] <;> ring
    _ ≤ (1e-12:ℝ)*((N:ℝ)/L^2) := mul_le_mul_of_nonneg_right hpay (by positivity)
    _ = _ := by ring

#print axioms medium_tail_paid_at_target
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenWeightedDistribution -/
/-! A direct squarefree weighted distribution estimate at the H<14 target.
Only the elementary ordered-divisor mean is used from the existing Fouvry
prerequisite file; no Li--Liu analytic theorem is used. -/
namespace ChenEffective.GRHQuarterChen
open ChenEffective.GRH
open Real Finset
open MathlibNt.SieveTheory.BombieriVinogradov
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

private theorem divisor_weight_squarefree (n : ℕ) (hn : Squarefree n) :
    fouvryTau 3 n = 3^n.primeFactors.card := by
  rw [← (fouvryTau_multiplicative 3).prod_primeFactors hn]
  have hp (p : ℕ) (hpm : p ∈ n.primeFactors) : fouvryTau 3 p = 3 := by
    have hh := fouvryTau_prime_pow (Nat.prime_of_mem_primeFactors hpm) 3 1
    simpa [Nat.multichoose_eq] using hh
  simp_rw [Finset.prod_congr rfl hp]
  simp

theorem three_omega_mass (D : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 D)
    (hsq : ∀ d ∈ S, Squarefree d) :
    (∑ d ∈ S, (3:ℝ)^d.primeFactors.card) ≤ (D:ℝ)*(1+Real.log D)^2 := by
  have hh := sum_fouvryTau_le 2 D
  apply le_trans _ hh
  calc
    _ = ∑ d ∈ S, (fouvryTau 3 d:ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [divisor_weight_squarefree d (hsq d hd),Nat.cast_pow,Nat.cast_ofNat]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        have hh := Finset.mem_Icc.mp (hS hd)
        exact Finset.mem_Ioc.mpr ⟨by omega,hh.2⟩
      · intro d _ _
        positivity

theorem weighted_prefix_AP_numerical {N D : ℕ}
    (hL : (130690:ℝ) ≤ Real.log N) (hD : 1 ≤ D)
    (hlevel : (D:ℝ) ≤ (N:ℝ)^(1241/2500:ℝ)) (S : Finset ℕ)
    (hS : S ⊆ Icc 1 D) (hsq : ∀ d ∈ S, Squarefree d) :
    (∑ d ∈ S, (3:ℝ)^d.primeFactors.card*standardPrimeAPPrefixMaxError N d) ≤
      (1e-12:ℝ)*N/(Real.log N)^2 := by
  let L := Real.log (N:ℝ)
  let Y := (N:ℝ)^(501/1000:ℝ)
  have hN2 : 2 ≤ N := by
    by_contra hn
    have hh : N ≤ 1 := by omega
    interval_cases N <;> norm_num at hL
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 < L := by dsimp only [L]; linarith only [hL]
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith only [hL]
  have hY0 : 0 ≤ Y := by dsimp only [Y]; positivity
  have hD0 : (0:ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hDN : (D:ℝ) ≤ N := hlevel.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
      (show (1241/2500:ℝ) ≤ 1 by norm_num))
  have hlogD : Real.log (D:ℝ) ≤ L := Real.log_le_log hD0 hDN
  have hlogD0 : 0 ≤ Real.log (D:ℝ) := Real.log_nonneg (by exact_mod_cast hD)
  have hE (d : ℕ) (hd : d ∈ S) : standardPrimeAPPrefixMaxError N d ≤
      (8*10^16:ℝ)*L^3*Y := by
    obtain ⟨hd1,hdD⟩ := Finset.mem_Icc.mp (hS hd)
    have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hlogd : Real.log (d:ℝ) ≤ L :=
      Real.log_le_log hd0 ((by exact_mod_cast hdD : (d:ℝ)≤ D).trans hDN)
    calc
      _ ≤ (10^16:ℝ)*(Real.log d+Real.log N)^3*(N:ℝ)^(501/1000:ℝ) :=
        prime_AP_max_numerical hN2 (by linarith only [hL]) (by omega)
      _ ≤ (10^16:ℝ)*(2*L)^3*Y := by gcongr; linarith only [hlogd]
      _ = _ := by ring
  have hsum : (∑ d ∈ S, (3:ℝ)^d.primeFactors.card*standardPrimeAPPrefixMaxError N d) ≤
      (8*10^16:ℝ)*L^3*Y*((D:ℝ)*(1+Real.log D)^2) := by
    calc
      _ ≤ ∑ d ∈ S, (3:ℝ)^d.primeFactors.card*((8*10^16:ℝ)*L^3*Y) := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (hE d hd) (by positivity)
      _ = ((8*10^16:ℝ)*L^3*Y)*(∑ d ∈ S, (3:ℝ)^d.primeFactors.card) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (three_omega_mass D S hS hsq) (by positivity)
  have hprod : Y*(N:ℝ)^(1241/2500:ℝ) = (N:ℝ)^(4987/5000:ℝ) := by
    dsimp only [Y]
    rw [← Real.rpow_add hN0]
    congr 1
    norm_num
  have hmain : (∑ d ∈ S, (3:ℝ)^d.primeFactors.card*standardPrimeAPPrefixMaxError N d) ≤
      (320000000000000000:ℝ)*L^5*(N:ℝ)^(4987/5000:ℝ) := by
    apply hsum.trans
    calc
      _ ≤ (8*10^16:ℝ)*L^3*Y*((N:ℝ)^(1241/2500:ℝ)*(2*L)^2) := by gcongr; linarith only [hlogD,hL1]
      _ = (320000000000000000:ℝ)*L^5*(Y*(N:ℝ)^(1241/2500:ℝ)) := by ring
      _ = _ := by rw [hprod]
  have hexp : (N:ℝ)^(4987/5000:ℝ) = (N:ℝ)*Real.exp (-13*L/5000) := by
    rw [Real.rpow_def_of_pos hN0]
    change Real.exp (L*(4987/5000:ℝ)) = _
    rw [show L*(4987/5000:ℝ) = L+(-13*L/5000) by ring,Real.exp_add]
    rw [show Real.exp L = (N:ℝ) from Real.exp_log hN0]
  have hpayBig := distribution_error_payment hL (C := (320000000000000000000000:ℝ))
    (by norm_num) (α := 13/5000) (by norm_num) (k := 7) (by norm_num)
  have hpay : (320000000000000000:ℝ)*L^7*Real.exp (-(13/5000:ℝ)*L) ≤ (1e-12:ℝ) := by
    have heq : (320000000000000000000000:ℝ)*L^7*Real.exp (-(13/5000:ℝ)*L) =
        (1000000:ℝ)*((320000000000000000:ℝ)*L^7*Real.exp (-(13/5000:ℝ)*L)) := by ring
    rw [heq] at hpayBig
    nlinarith only [hpayBig]
  have hid : (320000000000000000:ℝ)*L^5*(N:ℝ)^(4987/5000:ℝ) =
      ((320000000000000000:ℝ)*L^7*Real.exp (-(13/5000:ℝ)*L))*((N:ℝ)/L^2) := by
    rw [hexp,show -(13/5000:ℝ)*L = -13*L/5000 by ring]
    field_simp [hL0.ne']
  calc
    _ ≤ (320000000000000000:ℝ)*L^5*(N:ℝ)^(4987/5000:ℝ) := hmain
    _ = _ := hid
    _ ≤ (1e-12:ℝ)*((N:ℝ)/L^2) :=
      mul_le_mul_of_nonneg_right hpay (by positivity)
    _ = _ := by ring

theorem weighted_AP_numerical {N D : ℕ}
    (hN : GRHQuarterChen.targetCutoff ≤ N) (hD : 1 ≤ D)
    (hlevel : (D:ℝ) ≤ (N:ℝ)^(1241/2500:ℝ)) (S : Finset ℕ)
    (hS : S ⊆ Icc 1 D) (hsq : ∀ d ∈ S, Squarefree d) :
    (∑ d ∈ S, (3:ℝ)^d.primeFactors.card*standardPrimeAPMaxError N d) ≤
      (1e-12:ℝ)*N/(Real.log N)^2 := by
  apply le_trans _ (weighted_prefix_AP_numerical (GRHQuarterChen.target_log_lower hN) hD hlevel S hS hsq)
  apply Finset.sum_le_sum
  intro d _
  exact mul_le_mul_of_nonneg_left (standardPrimeAPMaxError_le_prefixMaxError N d) (by positivity)

#print axioms three_omega_mass
#print axioms weighted_AP_numerical
end ChenEffective.GRHQuarterChen

/- Component: GRHQuarterChenChenDistribution -/
/-! Connection to the project's actual reduced Chen distribution sum.
There is no assumed BV estimate here: the bound is supplied by the proved
GRH character estimates and the exact combined-modulus reindexing. -/
namespace ChenEffective.GRHQuarterChen
open ChenEffective.GRH
open Real Finset
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.Richert1969
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem combined_modulus_squarefree {N d : ℕ} {ε : ℝ}
    (hd : d ∈ chenReducedCombinedModuli N ε) : Squarefree d := by
  rcases Finset.mem_biUnion.mp hd with ⟨q,hq,hmImage⟩
  rcases Finset.mem_image.mp hmImage with ⟨r,hr,rfl⟩
  have hqSource := (Finset.mem_filter.mp hq).1
  have hqPrime := (Finset.mem_filter.mp hqSource).2.1
  have hrDiv : r ∣ jurkatRichertSourceSiftingProduct N :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hr).1
  have hrSquarefree := (jurkatRichertSourceSiftingProduct_squarefree N).squarefree_of_dvd hrDiv
  have hcop := jurkatRichertSourceMediumPrime_coprime_siftingDivisor hqSource hrDiv
  exact (Nat.squarefree_mul hcop).mpr ⟨hqPrime.squarefree,hrSquarefree⟩

theorem chen_weighted_distribution {N : ℕ} (hN : GRHQuarterChen.targetCutoff ≤ N) :
    jurkatRichertSourceReducedWeightedBVSum N (9/2500:ℝ) ≤
      (1e-12:ℝ)*N/(Real.log N)^2 := by
  let D := LiuWeight.liuSourceDEpsilon N (9/2500:ℝ)
  let S := chenReducedCombinedModuli N (9/2500:ℝ)
  have hL := GRHQuarterChen.target_log_lower hN
  have hN1 : (1:ℝ) ≤ N := by
    have hn : 1 ≤ N := by
      by_contra hh
      have hz : N=0 := by omega
      subst N
      norm_num at hL
    exact_mod_cast hn
  have hD : 1 ≤ D := by
    unfold D LiuWeight.liuSourceDEpsilon
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hN1
      (by norm_num : (0:ℝ) ≤ 1/2-(9/2500:ℝ))
  have hlevel : (D:ℝ) ≤ (N:ℝ)^(1241/2500:ℝ) := by
    dsimp only [D,LiuWeight.liuSourceDEpsilon]
    norm_num only [show (1/2-(9/2500:ℝ))=(1241/2500:ℝ) by norm_num]
    exact Nat.floor_le (by positivity)
  have hS : S ⊆ Finset.Icc 1 D := by
    intro d hd
    have hs := combined_modulus_squarefree hd
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hs.ne_zero,
      chenReducedCombinedModuli_le_liuSourceDEpsilon hd⟩
  apply (chenReducedWeightedBVSum_le_combinedMass N (9/2500:ℝ)).trans
  simpa only [threeOmegaErrorMass] using
    weighted_AP_numerical hN hD hlevel S hS (fun d hd => combined_modulus_squarefree hd)

#print axioms combined_modulus_squarefree
#print axioms chen_weighted_distribution
end ChenEffective.GRHQuarterChen

/- Component: GRHQuarterChenBaseDistribution -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem base_source_distribution {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    jurkatRichertSourceRemainderSum N (9/2500:ℝ) ≤ (2e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hlarge := (lower_endpoint_parameters hN).1
  have hL := target_log_lower hN
  have hLp : 0<log (N:ℝ) := by linarith only [hL]
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤ N := by exact_mod_cast (show 1≤ N by omega)
  let D := LiuWeight.liuSourceDEpsilon N (9/2500:ℝ)
  let F := (jurkatRichertSourceSiftingProduct N).divisors.filter
    (fun d : ℕ => (d:ℝ)≤(N:ℝ)^(1/2-(9/2500:ℝ)))
  have hD : 1≤ D := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using one_le_rpow hN1
      (by norm_num : (0:ℝ)≤1/2-(9/2500:ℝ))
  have hlevel : (D:ℝ)≤(N:ℝ)^(1241/2500:ℝ) := by
    dsimp only [D,LiuWeight.liuSourceDEpsilon]
    norm_num only [show (1/2-(9/2500:ℝ))=(1241/2500:ℝ) by norm_num]
    exact Nat.floor_le (by positivity)
  have hsq : ∀ d ∈ F, Squarefree d := fun d hd =>
    (jurkatRichertSourceSiftingProduct_squarefree N).squarefree_of_dvd
      (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
  have hF : F ⊆ Icc 1 D := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (hsq d hd).ne_zero,
      Nat.le_floor (mem_filter.mp hd).2⟩
  have hw := weighted_AP_numerical hN hD hlevel F hF hsq
  have hsum : (∑ d ∈ F, BombieriVinogradov.standardPrimeAPMaxError N d) ≤
      (1e-12:ℝ)*N/log (N:ℝ)^2 := by
    apply le_trans _ hw
    apply sum_le_sum
    intro d _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by norm_num : (1:ℝ)≤3) : (1:ℝ)≤3^d.primeFactors.card)
      (BombieriVinogradov.standardPrimeAPMaxError_nonneg N d)
  have he := jurkatRichertSource_exceptional_endpoint_le N (9/2500:ℝ)
    (by omega) (by norm_num) (by norm_num)
  have hr := jurkatRichertSourceRemainderSum_le_standardMax_add_exceptional N (9/2500:ℝ) hEven hlarge
  have hl2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hePow : (N:ℝ)^(1/2-(9/2500:ℝ)) ≤ (N:ℝ)^(1/2:ℝ) :=
    rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have heSimple : 2*(N:ℝ)^(1/2-(9/2500:ℝ))*log (N:ℝ)/log 2 ≤
      4*(N:ℝ)^(1/2:ℝ)*log (N:ℝ) := by
    apply (div_le_iff₀ hl2).mpr
    have hh := mul_le_mul_of_nonneg_right hePow hLp.le
    have hp := mul_nonneg (show 0≤(N:ℝ)^(1/2:ℝ)*log (N:ℝ) by positivity)
      (show 0≤ log (2:ℝ)-1/2 by linarith only [log_two_gt_d9])
    nlinarith only [hh,hp]
  have hp := truncated_polynomial_payment hL (A:=(4000000:ℝ)) (by norm_num)
    (α:=(1/2:ℝ)) (by norm_num) (k:=3) (by norm_num)
  have hsmall : (4:ℝ)*(log (N:ℝ))^3*exp (-(1/2:ℝ)*log (N:ℝ))≤(1e-12:ℝ) := by
    nlinarith only [hp]
  have hid : 4*(N:ℝ)^(1/2:ℝ)*log (N:ℝ) =
      ((4:ℝ)*(log (N:ℝ))^3*exp (-(1/2:ℝ)*log (N:ℝ)))*((N:ℝ)/log (N:ℝ)^2) := by
    have hnp : (N:ℝ)^(1/2:ℝ)=(N:ℝ)*exp (-(1/2:ℝ)*log (N:ℝ)) := by
      calc
        _ = exp (log (N:ℝ)*(1/2:ℝ)) := rpow_def_of_pos hNp _
        _ = exp (log (N:ℝ))*exp (-(1/2:ℝ)*log (N:ℝ)) := by
          rw [← exp_add]
          congr 1
          ring
        _ = _ := by rw [exp_log hNp]
    rw [hnp]
    field_simp [hLp.ne']
  have hpaid : 4*(N:ℝ)^(1/2:ℝ)*log (N:ℝ)≤(1e-12:ℝ)*N/log (N:ℝ)^2 := by
    rw [hid]
    exact (mul_le_mul_of_nonneg_right hsmall (by positivity)).trans_eq (by ring)
  change jurkatRichertSourceRemainderSum N (9/2500:ℝ)≤_ at hr
  change _ ≤ (∑ d ∈ F, BombieriVinogradov.standardPrimeAPMaxError N d)+_ at hr
  calc
    _ ≤ (∑ d ∈ F, BombieriVinogradov.standardPrimeAPMaxError N d)+
        2*(N:ℝ)^(1/2-(9/2500:ℝ))*log (N:ℝ)/log 2 := hr.trans (add_le_add le_rfl he)
    _ ≤ (1e-12:ℝ)*N/log (N:ℝ)^2+(1e-12:ℝ)*N/log (N:ℝ)^2 :=
      add_le_add hsum (heSimple.trans hpaid)
    _ = _ := by ring

theorem base_remainder_below {N L : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (hlevel : (L:ℝ)≤(N:ℝ)^(1241/2500:ℝ)) :
    sieveRemainderBelow (jurkatRichertSourceBoundingSieve N) L ≤
      (2e-12:ℝ)*N/log (N:ℝ)^2 := by
  apply le_trans _ (base_source_distribution hN hEven)
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    refine mem_filter.mpr ⟨(mem_filter.mp hd).1,?_⟩
    have hh : (d:ℝ)<L := by exact_mod_cast (mem_filter.mp hd).2
    norm_num only [show (1/2-(9/2500:ℝ))=(1241/2500:ℝ) by norm_num]
    exact hh.le.trans hlevel
  · intro _ _ _
    exact abs_nonneg _

#print axioms base_source_distribution
end ChenEffective.GRHQuarterChen
end

/- Component: GRHQuarterChenMediumDistribution -/
noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem varying_correction_at_target {N : ℕ} (hN : targetCutoff ≤ N) :
    jurkatRichertSourceVaryingQUnconditionalCorrection N (9/2500:ℝ) ≤
      (1e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hlarge := (lower_endpoint_parameters hN).1
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN9 : 9≤ N := by
    have hh := log_le_sub_one_of_pos hn
    exact_mod_cast (by linarith only [hh,hL] : (9:ℝ)≤ N)
  have hb := numerical_varying_correction hN9 (by norm_num : (0:ℝ)≤9/2500)
  have hp := truncated_polynomial_payment hL (A:=(3000000000:ℝ)) (by norm_num)
    (α:=(1/10:ℝ)) (by norm_num) (k:=9) (by norm_num)
  have hs : (3000:ℝ)*(log (N:ℝ))^9*exp (-(1/10:ℝ)*log (N:ℝ))≤(1e-12:ℝ) := by
    nlinarith only [hp]
  have hid : (N:ℝ)^(9/10:ℝ)=(N:ℝ)*exp (-(1/10:ℝ)*log (N:ℝ)) := by
    calc
      _ = exp (log (N:ℝ)*(9/10:ℝ)) := rpow_def_of_pos hn _
      _ = exp (log (N:ℝ))*exp (-(1/10:ℝ)*log (N:ℝ)) := by
        rw [← exp_add]
        congr 1
        ring
      _ = _ := by rw [exp_log hn]
  apply hb.trans
  calc
    _ = ((3000:ℝ)*(log (N:ℝ))^9*exp (-(1/10:ℝ)*log (N:ℝ)))*
        ((N:ℝ)/log (N:ℝ)^2) := by rw [hid]; field_simp [hl.ne']
    _ ≤ (1e-12:ℝ)*((N:ℝ)/log (N:ℝ)^2) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by ring

theorem medium_source_distribution {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    preSieveVaryingRemainder N (9/2500:ℝ) ≤ (2e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hh := preSieve_unweighted_varying_remainder_le_BV N (9/2500:ℝ) hEven
    (lower_endpoint_parameters hN).1
  have hw := chen_weighted_distribution hN
  have hc := varying_correction_at_target hN
  calc
    _ ≤ _ := hh
    _ ≤ (1e-12:ℝ)*N/log (N:ℝ)^2+(1e-12:ℝ)*N/log (N:ℝ)^2 := add_le_add hw hc
    _ = _ := by ring

theorem medium_truncated_remainders {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (D : ℕ → ℕ) (hD : ∀ q ∈ jurkatRichertSourceMediumPrimes N, 1≤ D q)
    (hDN : ∀ q ∈ jurkatRichertSourceMediumPrimes N, D q≤ N)
    (hlevel : ∀ q ∈ jurkatRichertSourceMediumPrimes N,
      preSieveTruncation N*D q≤ jurkatRichertSourceUpperLevel N q (9/2500:ℝ)) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      QuarterTruncation.truncatedRemainderBound (jurkatRichertSourceConditionedBoundingSieve N q) 4000000
        (D q) (preSieveTruncation N)) ≤ (3e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hl : (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      sieveRemainderBelow (jurkatRichertSourceConditionedBoundingSieve N q)
        (preSieveTruncation N*D q)) ≤ preSieveVaryingRemainder N (9/2500:ℝ) := by
    apply sum_le_sum
    intro q hq
    exact sieveRemainderBelow_mono _ (hlevel q hq)
  have ht := medium_tail_paid_at_target hN hEven D hD hDN
  unfold QuarterTruncation.truncatedRemainderBound
  rw [sum_add_distrib]
  calc
    _ ≤ preSieveVaryingRemainder N (9/2500:ℝ)+(1e-12:ℝ)*N/log (N:ℝ)^2 := add_le_add hl ht
    _ ≤ (2e-12:ℝ)*N/log (N:ℝ)^2+(1e-12:ℝ)*N/log (N:ℝ)^2 :=
      add_le_add (medium_source_distribution hN hEven) le_rfl
    _ = _ := by ring

theorem base_truncated_remainder {N D : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (hD : 1≤ D) (hDN : D≤ N)
    (hlevel : ((preSieveTruncation N*D:ℕ):ℝ)≤(N:ℝ)^(1241/2500:ℝ)) :
    QuarterTruncation.truncatedRemainderBound (jurkatRichertSourceBoundingSieve N) 4000000 D
      (preSieveTruncation N) ≤ (3e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hl := base_remainder_below hN hEven hlevel
  have ht := source_tail_paid_at_target hN hEven hD hDN
  unfold QuarterTruncation.truncatedRemainderBound
  calc
    _ ≤ (2e-12:ℝ)*N/log (N:ℝ)^2+(1e-12:ℝ)*N/log (N:ℝ)^2 := add_le_add hl ht
    _ = _ := by ring

#print axioms medium_truncated_remainders
#print axioms base_truncated_remainder
end ChenEffective.GRHQuarterChen
end

