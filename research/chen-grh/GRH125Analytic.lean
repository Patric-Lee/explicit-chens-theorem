import GRH125Moments
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

/-! Complete analytic propagation to the candidate 3^240000 cutoff.
Grouped to avoid repeatedly loading the common analytic environment. -/
set_option maxErrors 100

/- Grouped source: GRH125Budget -/

noncomputable section
namespace ChenEffective.GRH125Budget
open Real
set_option maxHeartbeats 3000000

/-- Specialize to the logarithmic degree actually used by the low moving
lane, rather than paying the old unused degree-100 box. -/

private opaque exponentCertificate : {n : ℕ // n=240000} := ⟨240000,rfl⟩
def targetExponent : ℕ := exponentCertificate.1
theorem targetExponent_eq : targetExponent=240000 := exponentCertificate.2
def targetCutoff : ℕ := 3^targetExponent
theorem target_log_lower {N : ℕ} (hN : targetCutoff≤ N) : (263000:ℝ)≤ log (N:ℝ) := by
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
  have hlog : log (targetCutoff:ℝ)≤264000 := by
    simp only [targetCutoff,Nat.cast_pow,Nat.cast_ofNat,log_pow]
    rw [targetExponent_eq]
    norm_num only [Nat.cast_ofNat] at hlog3 ⊢
    linarith only [hlog3]
  have he13 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 13
  rw [← exp_nat_mul] at he13
  norm_num only [Nat.cast_ofNat,mul_one] at he13
  have he : (264000:ℝ)<exp (13:ℝ) := by norm_num at he13; linarith only [he13]
  have htpos : (0:ℝ)<(targetCutoff:ℕ) := by
    exact_mod_cast (show 0<targetCutoff by unfold targetCutoff; positivity)
  apply (log_lt_log_iff htpos (exp_pos _)).mp
  rw [log_exp]
  exact hlog.trans_lt he

theorem targetCutoff_lt_double_exp_12_5 : (targetCutoff:ℝ)<exp (exp (25/2:ℝ)) := by
  have he1 : (2718/1000:ℝ)≤ exp 1 := by linarith only [exp_one_gt_d9]
  have he11 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 11
  rw [← exp_nat_mul] at he11
  norm_num only [Nat.cast_ofNat,mul_one] at he11
  have h311 : (3:ℝ)^10≤ exp 11 := by norm_num at he11 ⊢; linarith only [he11]
  have hlog3 := log_le_log (by positivity : (0:ℝ)<(3:ℝ)^10) h311
  rw [log_pow,log_exp] at hlog3
  have hlog : log (targetCutoff:ℝ)≤264000 := by
    simp only [targetCutoff,Nat.cast_pow,Nat.cast_ofNat,log_pow]
    rw [targetExponent_eq]
    norm_num only [Nat.cast_ofNat] at hlog3 ⊢
    linarith only [hlog3]
  have he12 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 12
  rw [← exp_nat_mul] at he12
  norm_num only [Nat.cast_ofNat,mul_one] at he12
  have hehalf : (79/48:ℝ)≤ exp (1/2:ℝ) := by
    have hh := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤1/2) 4
    norm_num [Finset.sum_range_succ,Nat.factorial] at hh
    linarith only [hh]
  have hm := mul_le_mul he12 hehalf (by norm_num : (0:ℝ)≤79/48) (exp_pos _).le
  rw [← exp_add] at hm
  have he : (264000:ℝ)<exp (25/2:ℝ) := by norm_num at hm; linarith only [hm]
  have htpos : (0:ℝ)<(targetCutoff:ℕ) := by exact_mod_cast (show 0<targetCutoff by unfold targetCutoff; positivity)
  apply (log_lt_log_iff htpos (exp_pos _)).mp
  rw [log_exp]
  exact hlog.trans_lt he

theorem targetCutoff_lt_double_exp_13_37 : (targetCutoff:ℝ)<exp (exp (1337/100:ℝ)) :=
  targetCutoff_lt_double_exp_13.trans (exp_lt_exp.mpr (exp_lt_exp.mpr (by norm_num)))

theorem pan_log_log_cap {L : ℝ} (hL : (263000:ℝ)≤ L) :
    log L≤ L/20000 := by
  have hl : 0<L := by linarith only [hL]
  have he := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000)
    (by linarith only [exp_one_gt_d9] : (2718/1000:ℝ)≤ exp 1) 13
  rw [← exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat,mul_one] at he
  have hn : (263000:ℝ)≤(2718/1000:ℝ)^13 := by norm_num
  have hlog : log (263000:ℝ)≤13 := by
    have hx : (263000:ℝ)≤ exp 13 := by norm_num at he; linarith only [he]
    have hh := log_le_log (by norm_num : (0:ℝ)<263000) hx
    rwa [log_exp] at hh
  have hh := log_le_sub_one_of_pos (show 0<L/263000 by positivity)
  rw [log_div hl.ne' (by norm_num : (263000:ℝ)≠0)] at hh
  linarith only [hh,hlog,hL]


end ChenEffective.GRH125Budget


/- Grouped source: GRH125TruncationPayment -/

/-! Direct payment of the complete pre-sieve error envelope. The old
intermediate exponential decay rate is deliberately not required. -/
noncomputable section
namespace ChenEffective.GRH125Budget
open Real
set_option maxHeartbeats 3000000

theorem sharp_medium_truncation_payment {L : ℝ} (hL : 263000 ≤ L) :
    336*L^6*exp (512+log 2/2-L/400) ≤ (1e-12:ℝ) := by
  have hLp : 0<L := by linarith only [hL]
  have he1 : (2718/1000:ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
  have he14 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 13
  rw [← exp_nat_mul] at he14
  norm_num only [Nat.cast_ofNat,mul_one] at he14
  have hn14 : (263000:ℝ) ≤ (2718/1000:ℝ)^13 := by norm_num
  have hlog14 : log (263000:ℝ) ≤ 13 := by
    have hx : (263000:ℝ)≤ exp 13 := by norm_num at he14; linarith only [he14]
    have hh := log_le_log (by norm_num : (0:ℝ)<263000) hx
    rwa [log_exp] at hh
  have hratio := log_le_sub_one_of_pos (div_pos hLp (by norm_num : (0:ℝ)<263000))
  rw [log_div hLp.ne' (by norm_num)] at hratio
  have hlog : 6*log L ≤ L/10000+52 := by
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
    _ ≤ exp 6*L^6*exp (512+log 2/2-L/400) := by gcongr
    _ = exp (6+6*log L+512+log 2/2-L/400) := by
      rw [hpoly,← exp_add,← exp_add]
      congr 1
      ring
    _ ≤ exp (-30:ℝ) := exp_le_exp.mpr (by linarith only [hlog,hl2,hL])
    _ ≤ _ := hsmall

#print axioms sharp_medium_truncation_payment
end ChenEffective.GRH125Budget


/- Grouped source: GRH125Mertens -/

/-! Preserve the proved power-decaying theta error at the very large
endpoints used by Chen, instead of absorbing it at the smallest endpoint. -/
noncomputable section
namespace ChenEffective.GRH125
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
end ChenEffective.GRH125


/- Grouped source: GRH125MertensProduct -/

noncomputable section
namespace ChenEffective.GRH125
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
end ChenEffective.GRH125


/- Grouped source: GRH125GoldbachProduct -/

namespace ChenEffective.GRH125
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
end ChenEffective.GRH125


/- Grouped source: GRH125SourceMass -/

namespace ChenEffective.GRH125
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
end ChenEffective.GRH125


/- Grouped source: GRH125SourceUpperMass -/

noncomputable section
namespace ChenEffective.GRH125
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
end ChenEffective.GRH125


/- Grouped source: GRH125Analytic -/

/-! Smaller-cutoff analytic assembly. Components are grouped to avoid
repeated loading of the common analytic environment. The certificate-inclusive
Chen theorem and axiom audit are in AuditGRH125Chen. -/
set_option maxErrors 100

/- Component: GRH125ErrorBudget -/
noncomputable section
namespace ChenEffective.GRH125
open Real
set_option maxHeartbeats 3000000
def targetExponent : ℕ := GRH125Budget.targetExponent
theorem targetExponent_eq : targetExponent=240000 := GRH125Budget.targetExponent_eq
def targetCutoff : ℕ := 3^targetExponent
theorem targetCutoff_eq : targetCutoff=3^240000 := by unfold targetCutoff; rw [targetExponent_eq]
theorem target_log_lower {N : ℕ} (hN : targetCutoff≤ N) : (263000:ℝ)≤ log (N:ℝ) := GRH125Budget.target_log_lower hN
theorem targetCutoff_lt_double_exp_13_37 : (targetCutoff:ℝ)<exp (exp (1337/100:ℝ)) := GRH125Budget.targetCutoff_lt_double_exp_13_37
theorem targetCutoff_lt_double_exp_14 : (targetCutoff:ℝ)<exp (exp (14:ℝ)) :=
  targetCutoff_lt_double_exp_13_37.trans (exp_lt_exp.mpr (exp_lt_exp.mpr (by norm_num)))
theorem target_nine_le {N : ℕ} (hN : targetCutoff≤ N) : 9≤ N := by
  have hl := target_log_lower hN
  have hn : 0<N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hh := log_le_sub_one_of_pos (show (0:ℝ)<N by exact_mod_cast hn)
  exact_mod_cast (by linarith only [hl,hh] : (9:ℝ)≤ N)
theorem log_power_at_target {N k : ℕ} {δ : ℝ} (hN : targetCutoff≤ N)
    (hk : k≤190) (hδ : (1/100:ℝ)≤δ) : log (N:ℝ)^k≤(N:ℝ)^δ := by
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by have := target_nine_le hN; omega)
  have hh := mul_le_mul_of_nonneg_left (GRH125Budget.pan_log_log_cap hL) (Nat.cast_nonneg (α:=ℝ) k)
  have hkR : (k:ℝ)≤190 := by exact_mod_cast hk
  have hm := mul_le_mul_of_nonneg_right hkR (show 0≤ log (N:ℝ)/20000 by positivity)
  have hd := mul_le_mul_of_nonneg_right hδ hl.le
  rw [rpow_def_of_pos hn]
  have he := exp_nat_mul (log (log (N:ℝ))) k
  rw [exp_log hl] at he
  rw [← he]
  apply exp_le_exp.mpr
  nlinarith only [hh,hm,hd,hl]
theorem polynomial_error_payment {L C α : ℝ} {k : ℕ}
    (hL : (263000:ℝ)≤ L) (hC : C≤(1e30:ℝ)) (hα : (1/1000:ℝ)≤α) (hk : k≤12) :
    C*L^k*exp (-α*L)≤(1e-6:ℝ) := by
  have hl : 0<L := by linarith only [hL]
  have hlog := GRH125Budget.pan_log_log_cap hL
  have he1 : (27/10:ℝ)≤ exp 1 := by linarith only [exp_one_gt_d9]
  have he100 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10) he1 70
  rw [← exp_nat_mul] at he100
  norm_num only [Nat.cast_ofNat,mul_one] at he100
  have hc : (1e30:ℝ)≤ exp 70 := by norm_num at he100; linarith only [he100]
  have hp : L^k≤ exp (12*L/20000) := by
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
    _ ≤ exp 70*exp (12*L/20000)*exp (-α*L) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hC.trans hc) hp (pow_nonneg hl.le _) (exp_pos _).le) (exp_pos _).le
    _ = exp (70+12*L/20000-α*L) := by rw [← exp_add,← exp_add]; congr 1; ring
    _ ≤ exp (-30:ℝ) := exp_le_exp.mpr (by nlinarith only [hL,mul_nonneg hl.le (sub_nonneg.mpr hα)])
    _ ≤ _ := hs
theorem distribution_error_payment {L C α : ℝ} {k : ℕ}
    (hL : (263000:ℝ)≤ L) (hC : C≤(1e30:ℝ)) (hα : (1/1000:ℝ)≤α) (hk : k≤12) :
    C*L^k*exp (-α*L)≤(1e-6:ℝ) := polynomial_error_payment hL hC hα hk
end ChenEffective.GRH125
end

/- Component: GRH125SourceMassCaps -/
noncomputable section
namespace ChenEffective.GRH125
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
  have hm : mertensProductThreshold r ≤ 3^20000 := by
    unfold mertensProductThreshold
    apply max_le
    · unfold logPowerCutoff
      apply Nat.pow_le_pow_right (by norm_num)
      norm_num
    · apply Nat.pow_le_pow_right (by norm_num)
      have hs : Nat.sqrt (6*r) < 19999 := Nat.sqrt_lt.mpr (by nlinarith only [hr])
      omega
  have hplus : mertensProductThreshold r+1 ≤ 3^20001 := by
    have hp : 1 ≤ (3:ℕ)^20000 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [show (20001:ℕ)=20000+1 by norm_num,Nat.pow_succ]
    omega
  unfold chenProductThreshold
  rw [targetCutoff_eq]
  calc
    _ ≤ ((3:ℕ)^20001)^10 := Nat.pow_le_pow_left hplus 10
    _ = 3^200010 := by rw [← pow_mul]
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

theorem source_upper_mass_threshold_cap {r : ℕ} (hr : r ≤ 5000) :
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
      (jurkatRichertMertensFactor+(3/200:ℝ))*
        (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  constructor
  · have hh := numerical_source_mass_lower (r:=20000000) (by norm_num)
      ((source_lower_mass_threshold_cap (by norm_num)).trans hN) hEven
    convert hh using 1 <;> norm_num <;> ring
  · have hh := numerical_source_mass_upper (r:=5000) (by norm_num) (by norm_num)
      ((source_upper_mass_threshold_cap (by norm_num)).trans hN) hEven
    have hM0 : 0≤ SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2 := by positivity [SingularSeries.liuSingularSeries_pos N]
    norm_num at hh
    nlinarith only [hh,hM0]

#print axioms source_mass_at_target
end ChenEffective.GRH125
end

/- Component: GRH125TruncationBudget -/
noncomputable section
namespace ChenEffective.GRH125
open Real
set_option maxHeartbeats 3000000

theorem truncated_polynomial_payment {L A α : ℝ} {k : ℕ}
    (hL : (263000:ℝ)≤ L) (hA : A≤(1e30:ℝ)) (hα : (1/1000:ℝ)≤α) (hk : k≤12) :
    A*L^k*exp (-α*L)≤(1e-6:ℝ) := polynomial_error_payment hL hA hα hk

noncomputable def preSieveTruncation (N : ℕ) : ℕ :=
  Nat.floor ((N:ℝ)^(1/200:ℝ))

theorem truncation_log_lower {N : ℕ} (hN : targetCutoff ≤ N) :
    0 < preSieveTruncation N ∧
    log (N:ℝ)/200-log 2 ≤ log (preSieveTruncation N:ℝ) := by
  have hL := target_log_lower hN
  have hn : 0 < N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hnR : (0:ℝ) < N := by exact_mod_cast hn
  let x := (N:ℝ)^(1/200:ℝ)
  have hx : 0 < x := rpow_pos_of_pos hnR _
  have hlogx : log x=log (N:ℝ)/200 := by
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
    exp 512/sqrt (preSieveTruncation N:ℝ)≤ exp (512+log 2/2-log (N:ℝ)/400) := by
  have hc := truncation_log_lower hN
  have hCp : (0:ℝ)<preSieveTruncation N := by exact_mod_cast hc.1
  have hr : 1/sqrt (preSieveTruncation N:ℝ)=exp (-log (preSieveTruncation N:ℝ)/2) := by
    rw [sqrt_eq_rpow,rpow_def_of_pos hCp,one_div,← exp_neg]
    congr 1
    ring
  rw [div_eq_mul_one_div,hr,← exp_add]
  apply exp_le_exp.mpr
  linarith only [hc.2]
end ChenEffective.GRH125
end

/- Component: GRH125MomentAggregate -/
noncomputable section
namespace ChenEffective.GRH125
open ChenEffective.GRH
open Real Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem source_root_rem_moment {N d : ℕ} (hN : 2 < N) (hEven : Even N)
    (hd : d ∣ restrictedSievePrimeProduct (jurkatRichertSourceBoundingSieve N) 4000000) :
    let S := jurkatRichertSourceBoundingSieve N
    let Q := smallSievePrimeProduct S 4000000
    (∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|) ≤
      (N:ℝ)/(d:ℝ)*exp 500+|S.totalMass| * S.nu d*exp 512 := by
  let S := jurkatRichertSourceBoundingSieve N
  let Q := smallSievePrimeProduct S 4000000
  let R := restrictedSievePrimeProduct S 4000000
  have hcop : Q.Coprime R := sieve_prime_partition_coprime S 4000000
  have hpart : Q*R=S.prodPrimes := sieve_prime_partition S 4000000
  have hdS : d ∣ S.prodPrimes := by
    rw [← hpart]
    exact hd.trans (dvd_mul_left R Q)
  have hnud : 0 ≤ S.nu d := (S.nu_pos_of_dvd_prodPrimes hdS).le
  have hmajor : ∀ a ∈ Q.divisors,
      |S.rem (a*d)| ≤ ((N:ℝ)/(d:ℝ))/(a:ℝ)+(|S.totalMass| * S.nu d)*S.nu a := by
    intro a ha
    have haQ := Nat.dvd_of_mem_divisors ha
    have hadS : a*d ∣ S.prodPrimes := by rw [← hpart]; exact Nat.mul_dvd_mul haQ hd
    have hnu := S.nu_mult.map_mul_of_coprime ((hcop.of_dvd_left haQ).of_dvd_right hd)
    have hh := source_rem_majorant hN hEven hadS
    change |S.rem (a*d)| ≤ (N:ℝ)/((a*d:ℕ):ℝ)+S.nu (a*d)*|S.totalMass| at hh
    apply hh.trans_eq
    rw [hnu,Nat.cast_mul]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hm := source_small_prime_divisor_moments_sharp N
  change (∑ a ∈ Q.divisors, 1/sqrt (a:ℝ)) ≤ exp 500 ∧
    (∑ a ∈ Q.divisors, sqrt (a:ℝ)*S.nu a) ≤ exp 512 at hm
  calc
    _ ≤ ∑ a ∈ Q.divisors, sqrt (a:ℝ)*
        (((N:ℝ)/(d:ℝ))/(a:ℝ)+(|S.totalMass| * S.nu d)*S.nu a) := by
      apply sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hmajor a ha) (sqrt_nonneg _)
    _ = ((N:ℝ)/(d:ℝ))*(∑ a ∈ Q.divisors, 1/sqrt (a:ℝ))+
        (|S.totalMass| * S.nu d)*(∑ a ∈ Q.divisors, sqrt (a:ℝ)*S.nu a) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro a _
      have hh := sqrt_div_self' (x:=(a:ℝ))
      calc
        _ = ((N:ℝ)/(d:ℝ))*(sqrt (a:ℝ)/(a:ℝ))+
          (|S.totalMass| * S.nu d)*(sqrt (a:ℝ)*S.nu a) := by ring
        _ = _ := by rw [hh]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hm.1 (by positivity))
      (mul_le_mul_of_nonneg_left hm.2 (mul_nonneg (abs_nonneg _) hnud))

theorem source_reciprocal_divisor_mass (N D : ℕ) (hD : 1 ≤ D) :
    let S := jurkatRichertSourceBoundingSieve N
    let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d < D)
    (∑ d ∈ F, 1/(d:ℝ)) ≤ (1+log (D:ℝ))^2 ∧
    (∑ d ∈ F, S.nu d) ≤ (1+log (D:ℝ))^2 := by
  let S := jurkatRichertSourceBoundingSieve N
  let R := restrictedSievePrimeProduct S 4000000
  let F := R.divisors.filter (fun d => d < D)
  have hR : R ∣ S.prodPrimes := by rw [← sieve_prime_partition S 4000000]; exact dvd_mul_left _ _
  have hdS : ∀ d ∈ F, d ∣ S.prodPrimes :=
    fun d hd => (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1).trans hR
  have hsq : ∀ d ∈ F, Squarefree d :=
    fun d hd => S.prodPrimes_squarefree.squarefree_of_dvd (hdS d hd)
  have hF : F ⊆ Icc 1 D := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (hsq d hd).ne_zero,
      (mem_filter.mp hd).2.le⟩
  have hh := numerical_totient_weight_mass 1 hD F hF hsq
  norm_num only [Nat.cast_one,one_pow,show 2*1=2 by norm_num] at hh
  have hnu : (∑ d ∈ F, S.nu d)=(∑ d ∈ F, 1/(d.totient:ℝ)) := by
    apply sum_congr rfl
    intro d hd
    exact jurkatRichertSource_goldbachNu_eq_inv_totient (hdS d hd)
  constructor
  · apply le_trans _ hh
    apply sum_le_sum
    intro d hd
    have hp : (0:ℝ) < d.totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hsq d hd).ne_zero)
    apply one_div_le_one_div_of_le hp
    exact_mod_cast Nat.totient_le d
  · rw [hnu]
    exact hh

theorem source_tail_moment_aggregate {N D C : ℕ} (hN : 2 < N) (hEven : Even N)
    (hD : 1 ≤ D) :
    let S := jurkatRichertSourceBoundingSieve N
    let Q := smallSievePrimeProduct S 4000000
    let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d < D)
    (∑ d ∈ F, ∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|)/sqrt (C:ℝ) ≤
      ((N:ℝ)*exp 500+|S.totalMass| * exp 512)*(1+log (D:ℝ))^2/sqrt (C:ℝ) := by
  let S := jurkatRichertSourceBoundingSieve N
  let Q := smallSievePrimeProduct S 4000000
  let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d < D)
  have hm := source_reciprocal_divisor_mass N D hD
  apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
  calc
    _ ≤ ∑ d ∈ F, ((N:ℝ)/(d:ℝ)*exp 500+|S.totalMass| * S.nu d*exp 512) := by
      apply sum_le_sum
      intro d hd
      exact source_root_rem_moment hN hEven (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
    _ = ((N:ℝ)*exp 500)*(∑ d ∈ F, 1/(d:ℝ))+
        (|S.totalMass| * exp 512)*(∑ d ∈ F, S.nu d) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ ((N:ℝ)*exp 500)*(1+log (D:ℝ))^2+
        (|S.totalMass| * exp 512)*(1+log (D:ℝ))^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hm.1 (by positivity))
        (mul_le_mul_of_nonneg_left hm.2 (by positivity))
    _ = _ := by ring

#print axioms source_tail_moment_aggregate
end ChenEffective.GRH125
end

/- Component: GRH125LowerGeometry -/
noncomputable section
namespace ChenEffective.GRH125
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

noncomputable def lowerDelta (N q : ℕ) : ℝ :=
  (N:ℝ)^(249/500:ℝ)/(2*(q:ℝ)*(preSieveTruncation N:ℝ))
noncomputable def lowerLevel (N q : ℕ) : ℕ := Nat.floor (lowerDelta N q)+1
noncomputable def lowerRatio (N q : ℕ) : ℝ :=
  log (lowerDelta N q)/log ((N:ℝ)^(1/10:ℝ))

theorem truncation_log_upper {N : ℕ} (hN : targetCutoff ≤ N) :
    log (preSieveTruncation N:ℝ) ≤ log (N:ℝ)/200 := by
  have hn : 0<N := lt_of_lt_of_le (by unfold targetCutoff; positivity) hN
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hc : (0:ℝ)<preSieveTruncation N := by
    exact_mod_cast (truncation_log_lower hN).1
  have hh := log_le_log hc (Nat.floor_le (rpow_nonneg (Nat.cast_nonneg N) (1/200:ℝ)))
  rw [log_rpow hnR] at hh
  convert hh using 1 <;> ring

theorem lower_ratio_shift {N q : ℕ} (hN : targetCutoff ≤ N) (hq : 0<q) :
    0 ≤ (5-10*(log (q:ℝ)/log (N:ℝ)))-lowerRatio N q ∧
    (5-10*(log (q:ℝ)/log (N:ℝ)))-lowerRatio N q ≤ 71/1000 := by
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
      (1/50:ℝ)+10*(log 2+log (preSieveTruncation N:ℝ))/log (N:ℝ) := by
    unfold lowerRatio lowerDelta
    rw [log_div (rpow_pos_of_pos hnR _).ne' (by positivity),
      log_mul (by positivity : (2:ℝ)*q ≠ 0) hc.ne',
      log_mul (by norm_num : (2:ℝ) ≠ 0) hqR.ne',log_rpow hnR,log_rpow hnR]
    field_simp [hLp.ne']
    ring
  rw [heq]
  constructor
  · positivity
  · have hh : 10*(log 2+log (preSieveTruncation N:ℝ))/log (N:ℝ) ≤ 51/1000 := by
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
    (4929/1000:ℝ) ≤ lowerRatio N 1 ∧ lowerRatio N 1 ≤ 5 := by
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
      ((q*preSieveTruncation N*D:ℕ):ℝ) ≤ (N:ℝ)^(249/500:ℝ) := by
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
    have hid : ((q:ℝ)*preSieveTruncation N)*(lowerDelta N q)=(N:ℝ)^(249/500:ℝ)/2 := by
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
  have hpow : (N:ℝ)^(249/500:ℝ)≤ N := rpow_le_self_of_one_le hN1 (by norm_num)
  have hmreal : (lowerLevel N q:ℝ)≤((q*preSieveTruncation N*lowerLevel N q:ℕ):ℝ) := by exact_mod_cast hmult
  exact_mod_cast hmreal.trans (hg.trans hpow)

theorem lower_level_in_source {N q : ℕ} (hN : targetCutoff ≤ N) (hq : 0<q)
    (hs : 3/2≤ lowerRatio N q) :
    preSieveTruncation N*lowerLevel N q≤ jurkatRichertSourceUpperLevel N q (1/500:ℝ) := by
  have hg := (lower_level_geometry hN hq hs).2.2.2
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hh : ((preSieveTruncation N*lowerLevel N q:ℕ):ℝ)≤(N:ℝ)^(249/500:ℝ)/(q:ℝ) := by
    apply (le_div_iff₀ hqR).mpr
    simpa only [Nat.cast_mul,mul_assoc,mul_comm,mul_left_comm] using hg
  unfold jurkatRichertSourceUpperLevel
  norm_num only [show (1/2-(1/500:ℝ))=(249/500:ℝ) by norm_num]
  exact (Nat.le_floor hh).trans (Nat.le_succ _)

#print axioms lower_level_geometry
end ChenEffective.GRH125
end

/- Component: GRH125LowerTailPayment -/
noncomputable section
namespace ChenEffective.GRH125
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
    (∑ d ∈ F, ∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|)/
        sqrt (preSieveTruncation N:ℝ) ≤ (1e-12:ℝ)*N/log (N:ℝ)^2 := by
  let L := log (N:ℝ)
  have hL : (263000:ℝ)≤ L := target_log_lower hN
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
  have he : exp (500:ℝ)≤ exp 512 := exp_le_exp.mpr (by norm_num)
  have hnum : (N:ℝ)*exp 500+|(jurkatRichertSourceBoundingSieve N).totalMass| * exp 512 ≤
      11*(N:ℝ)*exp 512 := by
    have ha := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)
    have hb := mul_le_mul_of_nonneg_right hm (exp_pos (512:ℝ)).le
    nlinarith only [ha,hb]
  have hpayBig := GRH125Budget.sharp_medium_truncation_payment hL
  have hpL : L^4≤ L^6 := pow_le_pow_right₀ (by linarith only [hL] : (1:ℝ)≤ L) (by norm_num)
  have hpaySmall : (44:ℝ)*L^4*exp (512+log 2/2-L/400)≤(1e-12:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hpL (exp_pos (512+log 2/2-L/400)).le
    have hnon : 0≤ L^6*exp (512+log 2/2-L/400) := by positivity
    nlinarith only [hpayBig,hh,hnon]
  have hagg := source_tail_moment_aggregate (lower_endpoint_parameters hN).1 hEven hD
    (C:=preSieveTruncation N)
  apply hagg.trans
  calc
    _ ≤ (11*(N:ℝ)*exp 512)*(4*L^2)/sqrt (preSieveTruncation N:ℝ) := by
      apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
      exact mul_le_mul hnum hpoly (sq_nonneg _) (by positivity)
    _ = (44*(N:ℝ)*L^2)*(exp 512/sqrt (preSieveTruncation N:ℝ)) := by ring
    _ ≤ (44*(N:ℝ)*L^2)*exp (512+log 2/2-L/400) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = ((44:ℝ)*L^4*exp (512+log 2/2-L/400))*((N:ℝ)/L^2) := by
      field_simp [hLp.ne']
    _ ≤ (1e-12:ℝ)*((N:ℝ)/L^2) := mul_le_mul_of_nonneg_right hpaySmall (by positivity)
    _ = _ := by ring

#print axioms source_tail_paid_at_target
end ChenEffective.GRH125
end

/- Component: GRH125ConditionedTail -/
noncomputable section
namespace ChenEffective.GRH125
open ChenEffective.GRH
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem conditioned_multSum_eq {N q d : ℕ}
    (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) :
    (jurkatRichertSourceConditionedBoundingSieve N q).multSum d =
      (jurkatRichertSourceBoundingSieve N).multSum (q*d) := by
  classical
  have hcop := jurkatRichertSourceMediumPrime_coprime_siftingDivisor hq hd
  unfold BoundingSieve.multSum
  change (∑ a ∈ (jurkatRichertSourceUnsiftedComplements N).filter (fun a => q ∣ a),
    if d ∣ a then (1:ℝ) else 0) = _
  rw [sum_filter]
  apply sum_congr rfl
  intro a ha
  change (if q ∣ a then (if d ∣ a then (1:ℝ) else 0) else 0) =
    (if q*d ∣ a then 1 else 0)
  by_cases hqa : q ∣ a
  · by_cases hda : d ∣ a
    · simp [hqa,hda,hcop.mul_dvd_of_dvd_of_dvd hqa hda]
    · have hh : ¬ q*d ∣ a := fun h => hda ((dvd_mul_left d q).trans h)
      simp [hqa,hda,hh]
  · have hh : ¬ q*d ∣ a := fun h => hqa ((dvd_mul_right q d).trans h)
    simp [hqa,hh]

theorem conditioned_rem_majorant {N q d : ℕ} (hN : 2<N) (hEven : Even N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ jurkatRichertSourceSiftingProduct N) :
    let S := jurkatRichertSourceConditionedBoundingSieve N q
    |S.rem d| ≤ (N:ℝ)/((q:ℝ)*d)+S.nu d*|S.totalMass| := by
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  have hqp : 0<q := (mem_filter.mp hq).2.1.pos
  have hdp : 0<d := by
    apply Nat.pos_of_ne_zero
    intro hz
    subst d
    exact jurkatRichertSourceSiftingProduct_ne_zero N (zero_dvd_iff.mp hd)
  have hc := source_multSum_le hN hEven (Nat.mul_pos hqp hdp)
  rw [← conditioned_multSum_eq hq hd,Nat.cast_mul] at hc
  have hc0 : 0≤ S.multSum d := by
    unfold BoundingSieve.multSum
    apply sum_nonneg
    intro a _
    split_ifs <;> norm_num [S,jurkatRichertSourceConditionedBoundingSieve]
  have hnu : 0≤ S.nu d := (S.nu_pos_of_dvd_prodPrimes hd).le
  change |S.multSum d-S.nu d*S.totalMass| ≤ _
  calc
    _ ≤ |S.multSum d|+|S.nu d*S.totalMass| := abs_sub _ _
    _ = S.multSum d+S.nu d*|S.totalMass| := by
      rw [abs_of_nonneg hc0,abs_mul,abs_of_nonneg hnu]
    _ ≤ _ := add_le_add hc le_rfl

theorem conditioned_root_rem_moment {N q d : ℕ} (hN : 2<N) (hEven : Even N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∣ restrictedSievePrimeProduct (jurkatRichertSourceBoundingSieve N) 4000000) :
    let S := jurkatRichertSourceConditionedBoundingSieve N q
    let Q := smallSievePrimeProduct S 4000000
    (∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|) ≤
      ((N:ℝ)/(q:ℝ))/(d:ℝ)*exp 500+|S.totalMass| * S.nu d*exp 512 := by
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  let Q := smallSievePrimeProduct S 4000000
  let R := restrictedSievePrimeProduct S 4000000
  have hcop : Q.Coprime R := sieve_prime_partition_coprime S 4000000
  have hpart : Q*R=S.prodPrimes := sieve_prime_partition S 4000000
  have hdR : d ∣ R := hd
  have hdS : d ∣ S.prodPrimes := by rw [← hpart]; exact hdR.trans (dvd_mul_left R Q)
  have hnud : 0≤ S.nu d := (S.nu_pos_of_dvd_prodPrimes hdS).le
  have hmajor : ∀ a ∈ Q.divisors,
      |S.rem (a*d)| ≤ (((N:ℝ)/(q:ℝ))/(d:ℝ))/(a:ℝ)+(|S.totalMass| * S.nu d)*S.nu a := by
    intro a ha
    have haQ := Nat.dvd_of_mem_divisors ha
    have hadS : a*d ∣ S.prodPrimes := by rw [← hpart]; exact Nat.mul_dvd_mul haQ hdR
    have hnu := S.nu_mult.map_mul_of_coprime ((hcop.of_dvd_left haQ).of_dvd_right hdR)
    have hh := conditioned_rem_majorant hN hEven hq hadS
    change |S.rem (a*d)| ≤ (N:ℝ)/((q:ℝ)*((a*d:ℕ):ℝ))+S.nu (a*d)*|S.totalMass| at hh
    apply hh.trans_eq
    rw [hnu,Nat.cast_mul]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hm := source_small_prime_divisor_moments_sharp N
  change (∑ a ∈ Q.divisors, 1/sqrt (a:ℝ)) ≤ exp 500 ∧
    (∑ a ∈ Q.divisors, sqrt (a:ℝ)*S.nu a) ≤ exp 512 at hm
  calc
    _ ≤ ∑ a ∈ Q.divisors, sqrt (a:ℝ)*
        ((((N:ℝ)/(q:ℝ))/(d:ℝ))/(a:ℝ)+(|S.totalMass| * S.nu d)*S.nu a) := by
      apply sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hmajor a ha) (sqrt_nonneg _)
    _ = (((N:ℝ)/(q:ℝ))/(d:ℝ))*(∑ a ∈ Q.divisors, 1/sqrt (a:ℝ))+
        (|S.totalMass| * S.nu d)*(∑ a ∈ Q.divisors, sqrt (a:ℝ)*S.nu a) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro a _
      calc
        _ = (((N:ℝ)/(q:ℝ))/(d:ℝ))*(sqrt (a:ℝ)/(a:ℝ))+
          (|S.totalMass| * S.nu d)*(sqrt (a:ℝ)*S.nu a) := by ring
        _ = _ := by rw [sqrt_div_self']
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hm.1 (by positivity))
      (mul_le_mul_of_nonneg_left hm.2 (mul_nonneg (abs_nonneg _) hnud))

theorem conditioned_tail_moment_aggregate {N q D C : ℕ} (hN : 2<N) (hEven : Even N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N) (hD : 1≤ D) :
    let S := jurkatRichertSourceConditionedBoundingSieve N q
    let Q := smallSievePrimeProduct S 4000000
    let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d<D)
    (∑ d ∈ F, ∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|)/sqrt (C:ℝ) ≤
      (((N:ℝ)/(q:ℝ))*exp 500+|S.totalMass| * exp 512)*(1+log (D:ℝ))^2/sqrt (C:ℝ) := by
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  let Q := smallSievePrimeProduct S 4000000
  let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d<D)
  have hm := source_reciprocal_divisor_mass N D hD
  apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
  calc
    _ ≤ ∑ d ∈ F, (((N:ℝ)/(q:ℝ))/(d:ℝ)*exp 500+|S.totalMass| * S.nu d*exp 512) := by
      apply sum_le_sum
      intro d hd
      exact conditioned_root_rem_moment hN hEven hq (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
    _ = (((N:ℝ)/(q:ℝ))*exp 500)*(∑ d ∈ F, 1/(d:ℝ))+
        (|S.totalMass| * exp 512)*(∑ d ∈ F, S.nu d) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ (((N:ℝ)/(q:ℝ))*exp 500)*(1+log (D:ℝ))^2+
        (|S.totalMass| * exp 512)*(1+log (D:ℝ))^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hm.1 (by positivity))
        (mul_le_mul_of_nonneg_left hm.2 (by positivity))
    _ = _ := by ring

#print axioms conditioned_tail_moment_aggregate
end ChenEffective.GRH125
end

/- Component: GRH125MediumTailPayment -/
noncomputable section
namespace ChenEffective.GRH125
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
    (∑ d ∈ F, ∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|)/sqrt (preSieveTruncation N:ℝ) ≤
      (84:ℝ)*(N:ℝ)/(q:ℝ)*(log (N:ℝ))^2*exp (512+log 2/2-log (N:ℝ)/400) := by
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
  have he : exp (500:ℝ)≤ exp 512 := exp_le_exp.mpr (by norm_num)
  have hnum : ((N:ℝ)/(q:ℝ))*exp 500+
      |(jurkatRichertSourceConditionedBoundingSieve N q).totalMass| * exp 512 ≤
        (21:ℝ)*((N:ℝ)/(q:ℝ))*exp 512 := by
    have ha := mul_le_mul_of_nonneg_left he (show 0≤(N:ℝ)/(q:ℝ) by positivity)
    have hb := mul_le_mul_of_nonneg_right hm (exp_pos (512:ℝ)).le
    nlinarith only [ha,hb]
  have hagg := conditioned_tail_moment_aggregate (lower_endpoint_parameters hN).1 hEven hq hD
    (C:=preSieveTruncation N)
  apply hagg.trans
  calc
    _ ≤ (21*((N:ℝ)/(q:ℝ))*exp 512)*(4*(log (N:ℝ))^2)/sqrt (preSieveTruncation N:ℝ) := by
      apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
      exact mul_le_mul hnum hpoly (sq_nonneg _) (by positivity)
    _ = (84*((N:ℝ)/(q:ℝ))*(log (N:ℝ))^2)*(exp 512/sqrt (preSieveTruncation N:ℝ)) := by ring
    _ ≤ (84*((N:ℝ)/(q:ℝ))*(log (N:ℝ))^2)*exp (512+log 2/2-log (N:ℝ)/400) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = _ := by ring

theorem medium_tail_paid_at_target {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (D : ℕ → ℕ) (hD : ∀ q ∈ jurkatRichertSourceMediumPrimes N, 1≤ D q)
    (hDN : ∀ q ∈ jurkatRichertSourceMediumPrimes N, D q≤ N) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      let S := jurkatRichertSourceConditionedBoundingSieve N q
      let Q := smallSievePrimeProduct S 4000000
      let F := (restrictedSievePrimeProduct S 4000000).divisors.filter (fun d => d<D q)
      (∑ d ∈ F, ∑ a ∈ Q.divisors, sqrt (a:ℝ)*|S.rem (a*d)|)/sqrt (preSieveTruncation N:ℝ)) ≤
      (1e-12:ℝ)*N/log (N:ℝ)^2 := by
  let L := log (N:ℝ)
  have hL : (263000:ℝ)≤ L := target_log_lower hN
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
  have hpay := GRH125Budget.sharp_medium_truncation_payment hL
  calc
    _ ≤ ∑ q ∈ jurkatRichertSourceMediumPrimes N,
        (84:ℝ)*(N:ℝ)/(q:ℝ)*L^2*exp (512+log 2/2-L/400) :=
      sum_le_sum (fun q hq => conditioned_tail_bound_at_target hN hEven hq (hD q hq) (hDN q hq))
    _ = (84*(N:ℝ)*L^2*exp (512+log 2/2-L/400))*
        (∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/(q:ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ (84*(N:ℝ)*L^2*exp (512+log 2/2-L/400))*(4*L^2) :=
      mul_le_mul_of_nonneg_left hrec (by positivity)
    _ = ((336:ℝ)*L^6*exp (512+log 2/2-L/400))*((N:ℝ)/L^2) := by field_simp [hLp.ne'] <;> ring
    _ ≤ (1e-12:ℝ)*((N:ℝ)/L^2) := mul_le_mul_of_nonneg_right hpay (by positivity)
    _ = _ := by ring

#print axioms medium_tail_paid_at_target
end ChenEffective.GRH125
end

/- Component: GRH125WeightedDistribution -/
/-! A direct squarefree weighted distribution estimate at the H<14 target.
Only the elementary ordered-divisor mean is used from the existing Fouvry
prerequisite file; no Li--Liu analytic theorem is used. -/
namespace ChenEffective.GRH125
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
    (hL : (263000:ℝ) ≤ Real.log N) (hD : 1 ≤ D)
    (hlevel : (D:ℝ) ≤ (N:ℝ)^(249/500:ℝ)) (S : Finset ℕ)
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
      (show (249/500:ℝ) ≤ 1 by norm_num))
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
  have hprod : Y*(N:ℝ)^(249/500:ℝ) = (N:ℝ)^(999/1000:ℝ) := by
    dsimp only [Y]
    rw [← Real.rpow_add hN0]
    congr 1
    norm_num
  have hmain : (∑ d ∈ S, (3:ℝ)^d.primeFactors.card*standardPrimeAPPrefixMaxError N d) ≤
      (320000000000000000:ℝ)*L^5*(N:ℝ)^(999/1000:ℝ) := by
    apply hsum.trans
    calc
      _ ≤ (8*10^16:ℝ)*L^3*Y*((N:ℝ)^(249/500:ℝ)*(2*L)^2) := by gcongr; linarith only [hlogD,hL1]
      _ = (320000000000000000:ℝ)*L^5*(Y*(N:ℝ)^(249/500:ℝ)) := by ring
      _ = _ := by rw [hprod]
  have hexp : (N:ℝ)^(999/1000:ℝ) = (N:ℝ)*Real.exp (-L/1000) := by
    rw [Real.rpow_def_of_pos hN0]
    change Real.exp (L*(999/1000:ℝ)) = _
    rw [show L*(999/1000:ℝ) = L+(-L/1000) by ring,Real.exp_add]
    rw [show Real.exp L = (N:ℝ) from Real.exp_log hN0]
  have hpayBig := distribution_error_payment hL (C := (320000000000000000000000:ℝ))
    (by norm_num) (α := 1/1000) le_rfl (k := 7) (by norm_num)
  have hpay : (320000000000000000:ℝ)*L^7*Real.exp (-(1/1000:ℝ)*L) ≤ (1e-12:ℝ) := by
    have heq : (320000000000000000000000:ℝ)*L^7*Real.exp (-(1/1000:ℝ)*L) =
        (1000000:ℝ)*((320000000000000000:ℝ)*L^7*Real.exp (-(1/1000:ℝ)*L)) := by ring
    rw [heq] at hpayBig
    nlinarith only [hpayBig]
  have hid : (320000000000000000:ℝ)*L^5*(N:ℝ)^(999/1000:ℝ) =
      ((320000000000000000:ℝ)*L^7*Real.exp (-(1/1000:ℝ)*L))*((N:ℝ)/L^2) := by
    rw [hexp,show -(1/1000:ℝ)*L = -L/1000 by ring]
    field_simp [hL0.ne']
  calc
    _ ≤ (320000000000000000:ℝ)*L^5*(N:ℝ)^(999/1000:ℝ) := hmain
    _ = _ := hid
    _ ≤ (1e-12:ℝ)*((N:ℝ)/L^2) :=
      mul_le_mul_of_nonneg_right hpay (by positivity)
    _ = _ := by ring

theorem weighted_AP_numerical {N D : ℕ}
    (hN : GRH125.targetCutoff ≤ N) (hD : 1 ≤ D)
    (hlevel : (D:ℝ) ≤ (N:ℝ)^(249/500:ℝ)) (S : Finset ℕ)
    (hS : S ⊆ Icc 1 D) (hsq : ∀ d ∈ S, Squarefree d) :
    (∑ d ∈ S, (3:ℝ)^d.primeFactors.card*standardPrimeAPMaxError N d) ≤
      (1e-12:ℝ)*N/(Real.log N)^2 := by
  apply le_trans _ (weighted_prefix_AP_numerical (GRH125.target_log_lower hN) hD hlevel S hS hsq)
  apply Finset.sum_le_sum
  intro d _
  exact mul_le_mul_of_nonneg_left (standardPrimeAPMaxError_le_prefixMaxError N d) (by positivity)

#print axioms three_omega_mass
#print axioms weighted_AP_numerical
end ChenEffective.GRH125

/- Component: GRH125ChenDistribution -/
/-! Connection to the project's actual reduced Chen distribution sum.
There is no assumed BV estimate here: the bound is supplied by the proved
GRH character estimates and the exact combined-modulus reindexing. -/
namespace ChenEffective.GRH125
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

theorem chen_weighted_distribution {N : ℕ} (hN : GRH125.targetCutoff ≤ N) :
    jurkatRichertSourceReducedWeightedBVSum N (1/500:ℝ) ≤
      (1e-12:ℝ)*N/(Real.log N)^2 := by
  let D := LiuWeight.liuSourceDEpsilon N (1/500:ℝ)
  let S := chenReducedCombinedModuli N (1/500:ℝ)
  have hL := GRH125.target_log_lower hN
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
      (by norm_num : (0:ℝ) ≤ 1/2-(1/500:ℝ))
  have hlevel : (D:ℝ) ≤ (N:ℝ)^(249/500:ℝ) := by
    dsimp only [D,LiuWeight.liuSourceDEpsilon]
    norm_num only [show (1/2-(1/500:ℝ))=(249/500:ℝ) by norm_num]
    exact Nat.floor_le (by positivity)
  have hS : S ⊆ Finset.Icc 1 D := by
    intro d hd
    have hs := combined_modulus_squarefree hd
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hs.ne_zero,
      chenReducedCombinedModuli_le_liuSourceDEpsilon hd⟩
  apply (chenReducedWeightedBVSum_le_combinedMass N (1/500:ℝ)).trans
  simpa only [threeOmegaErrorMass] using
    weighted_AP_numerical hN hD hlevel S hS (fun d hd => combined_modulus_squarefree hd)

#print axioms combined_modulus_squarefree
#print axioms chen_weighted_distribution
end ChenEffective.GRH125

/- Component: GRH125BaseDistribution -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem base_source_distribution {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    jurkatRichertSourceRemainderSum N (1/500:ℝ) ≤ (2e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hlarge := (lower_endpoint_parameters hN).1
  have hL := target_log_lower hN
  have hLp : 0<log (N:ℝ) := by linarith only [hL]
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤ N := by exact_mod_cast (show 1≤ N by omega)
  let D := LiuWeight.liuSourceDEpsilon N (1/500:ℝ)
  let F := (jurkatRichertSourceSiftingProduct N).divisors.filter
    (fun d : ℕ => (d:ℝ)≤(N:ℝ)^(1/2-(1/500:ℝ)))
  have hD : 1≤ D := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using one_le_rpow hN1
      (by norm_num : (0:ℝ)≤1/2-(1/500:ℝ))
  have hlevel : (D:ℝ)≤(N:ℝ)^(249/500:ℝ) := by
    dsimp only [D,LiuWeight.liuSourceDEpsilon]
    norm_num only [show (1/2-(1/500:ℝ))=(249/500:ℝ) by norm_num]
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
  have he := jurkatRichertSource_exceptional_endpoint_le N (1/500:ℝ)
    (by omega) (by norm_num) (by norm_num)
  have hr := jurkatRichertSourceRemainderSum_le_standardMax_add_exceptional N (1/500:ℝ) hEven hlarge
  have hl2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hePow : (N:ℝ)^(1/2-(1/500:ℝ)) ≤ (N:ℝ)^(1/2:ℝ) :=
    rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have heSimple : 2*(N:ℝ)^(1/2-(1/500:ℝ))*log (N:ℝ)/log 2 ≤
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
  change jurkatRichertSourceRemainderSum N (1/500:ℝ)≤_ at hr
  change _ ≤ (∑ d ∈ F, BombieriVinogradov.standardPrimeAPMaxError N d)+_ at hr
  calc
    _ ≤ (∑ d ∈ F, BombieriVinogradov.standardPrimeAPMaxError N d)+
        2*(N:ℝ)^(1/2-(1/500:ℝ))*log (N:ℝ)/log 2 := hr.trans (add_le_add le_rfl he)
    _ ≤ (1e-12:ℝ)*N/log (N:ℝ)^2+(1e-12:ℝ)*N/log (N:ℝ)^2 :=
      add_le_add hsum (heSimple.trans hpaid)
    _ = _ := by ring

theorem base_remainder_below {N L : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (hlevel : (L:ℝ)≤(N:ℝ)^(249/500:ℝ)) :
    sieveRemainderBelow (jurkatRichertSourceBoundingSieve N) L ≤
      (2e-12:ℝ)*N/log (N:ℝ)^2 := by
  apply le_trans _ (base_source_distribution hN hEven)
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    refine mem_filter.mpr ⟨(mem_filter.mp hd).1,?_⟩
    have hh : (d:ℝ)<L := by exact_mod_cast (mem_filter.mp hd).2
    norm_num only [show (1/2-(1/500:ℝ))=(249/500:ℝ) by norm_num]
    exact hh.le.trans hlevel
  · intro _ _ _
    exact abs_nonneg _

#print axioms base_source_distribution
end ChenEffective.GRH125
end

/- Component: GRH125MediumDistribution -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem varying_correction_at_target {N : ℕ} (hN : targetCutoff ≤ N) :
    jurkatRichertSourceVaryingQUnconditionalCorrection N (1/500:ℝ) ≤
      (1e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hlarge := (lower_endpoint_parameters hN).1
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN9 : 9≤ N := by
    have hh := log_le_sub_one_of_pos hn
    exact_mod_cast (by linarith only [hh,hL] : (9:ℝ)≤ N)
  have hb := numerical_varying_correction hN9 (by norm_num : (0:ℝ)≤1/500)
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
    preSieveVaryingRemainder N (1/500:ℝ) ≤ (2e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hh := preSieve_unweighted_varying_remainder_le_BV N (1/500:ℝ) hEven
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
      preSieveTruncation N*D q≤ jurkatRichertSourceUpperLevel N q (1/500:ℝ)) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      GRH.truncatedRemainderBound (jurkatRichertSourceConditionedBoundingSieve N q) 4000000
        (D q) (preSieveTruncation N)) ≤ (3e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hl : (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      sieveRemainderBelow (jurkatRichertSourceConditionedBoundingSieve N q)
        (preSieveTruncation N*D q)) ≤ preSieveVaryingRemainder N (1/500:ℝ) := by
    apply sum_le_sum
    intro q hq
    exact sieveRemainderBelow_mono _ (hlevel q hq)
  have ht := medium_tail_paid_at_target hN hEven D hD hDN
  unfold GRH.truncatedRemainderBound
  rw [sum_add_distrib]
  calc
    _ ≤ preSieveVaryingRemainder N (1/500:ℝ)+(1e-12:ℝ)*N/log (N:ℝ)^2 := add_le_add hl ht
    _ ≤ (2e-12:ℝ)*N/log (N:ℝ)^2+(1e-12:ℝ)*N/log (N:ℝ)^2 :=
      add_le_add (medium_source_distribution hN hEven) le_rfl
    _ = _ := by ring

theorem base_truncated_remainder {N D : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (hD : 1≤ D) (hDN : D≤ N)
    (hlevel : ((preSieveTruncation N*D:ℕ):ℝ)≤(N:ℝ)^(249/500:ℝ)) :
    GRH.truncatedRemainderBound (jurkatRichertSourceBoundingSieve N) 4000000 D
      (preSieveTruncation N) ≤ (3e-12:ℝ)*N/log (N:ℝ)^2 := by
  have hl := base_remainder_below hN hEven hlevel
  have ht := source_tail_paid_at_target hN hEven hD hDN
  unfold GRH.truncatedRemainderBound
  calc
    _ ≤ (2e-12:ℝ)*N/log (N:ℝ)^2+(1e-12:ℝ)*N/log (N:ℝ)^2 := add_le_add hl ht
    _ = _ := by ring

#print axioms medium_truncated_remainders
#print axioms base_truncated_remainder
end ChenEffective.GRH125
end

/- Component: GRH125LowerFactor -/
noncomputable section
namespace ChenEffective.GRH125
open Real Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem inner_integral_quarter {u : ℝ} (hu3 : 3≤ u) (hu4 : u≤4) :
    0≤ jurkatRichertInnerIntegral u ∧ jurkatRichertInnerIntegral u≤1/4 := by
  have hcont : ContinuousOn (fun t : ℝ => log (t-1)/t) (Icc 2 (u-1)) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht
      change t-1≠0
      linarith only [ht.1]
    · exact continuousOn_id
    · intro t ht
      linarith only [ht.1]
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ:=volume) (show (2:ℝ)≤ u-1 by linarith) hcont
  have hpoint (t : ℝ) (ht : t∈Icc 2 (u-1)) : log (t-1)/t≤(t-2)/2 := by
    have ht0 : 0<t := by linarith only [ht.1]
    have hl := log_le_sub_one_of_pos (show 0<t-1 by linarith only [ht.1])
    apply (div_le_iff₀ ht0).mpr
    nlinarith only [hl,sq_nonneg (t-2)]
  have hbound : jurkatRichertInnerIntegral u ≤ (u-3)^2/4 := by
    unfold jurkatRichertInnerIntegral
    calc
      _ ≤ ∫ t in (2:ℝ)..u-1, (t-2)/2 :=
        intervalIntegral.integral_mono_on (by linarith) hi
          (((continuous_id.sub continuous_const).div_const 2).intervalIntegrable _ _) hpoint
      _ = _ := by
        have heq : (∫ t in (2:ℝ)..u-1, t-2) =
            (∫ t in (2:ℝ)..u-1, t) - ∫ _t in (2:ℝ)..u-1, (2:ℝ) :=
          intervalIntegral.integral_sub (continuous_id.intervalIntegrable _ _) intervalIntegrable_const
        rw [intervalIntegral.integral_div,heq,integral_id,intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  refine ⟨(numerical_inner_integral hu3 hu4).1,?_⟩
  nlinarith only [hbound,hu3,hu4,mul_nonneg (show 0≤ u-3 by linarith) (show 0≤4-u by linarith)]

theorem lower_factor_scaled_loss {s : ℝ} (hs : (49/10:ℝ)≤ s) (hs5 : s≤5) :
    jurkatRichertMertensFactor*
      (dimensionOneLowerLinearSieveFactor 5-dimensionOneLowerLinearSieveFactor s) ≤
        (41/100:ℝ)*(5-s) := by
  let B := fun t : ℝ => log (t-1)+∫ u in (3:ℝ)..t-1, jurkatRichertInnerIntegral u/u
  have hs0 : 0<s := by linarith only [hs]
  have hsp : 0<s-1 := by linarith only [hs]
  have h3s : (3:ℝ)≤ s-1 := by linarith only [hs]
  have hs4 : s-1≤(4:ℝ) := by linarith only [hs5]
  have hδ : 0≤5-s := by linarith only [hs5]
  have hi1 := numerical_outer_interval (le_refl (3:ℝ)) h3s hs4
  have hi2 := numerical_outer_interval h3s hs4 (le_refl (4:ℝ))
  have hl : log 4-log (s-1) ≤ (5-s)/(s-1) := by
    have hh := log_le_sub_one_of_pos (show 0<(4:ℝ)/(s-1) by positivity)
    rw [log_div (by norm_num) hsp.ne'] at hh
    convert hh using 1 <;> field_simp <;> ring
  have hint : (∫ u in s-1..(4:ℝ), jurkatRichertInnerIntegral u/u) ≤
      (5-s)/(4*(s-1)) := by
    calc
      _ ≤ ∫ _u in s-1..(4:ℝ), (1/4:ℝ)/(s-1) := by
        apply intervalIntegral.integral_mono_on hs4 hi2 intervalIntegrable_const
        intro u hu
        have hu0 : 0<u := by linarith only [h3s,hu.1]
        apply (div_le_div_of_nonneg_right (inner_integral_quarter (h3s.trans hu.1) hu.2).2 hu0.le).trans
        exact div_le_div_of_nonneg_left (by norm_num) hsp hu.1
      _ = _ := by simp only [intervalIntegral.integral_const,smul_eq_mul]; field_simp [hsp.ne'] <;> ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hsum : B 5-B s ≤ (5/4:ℝ)*(5-s)/(s-1) := by
    dsimp only [B]
    norm_num only [show (5:ℝ)-1=4 by norm_num]
    have heq : (5-s)/(s-1)+(5-s)/(4*(s-1))=(5/4:ℝ)*(5-s)/(s-1) := by field_simp [hsp.ne'] <;> ring
    linarith only [hl,hint,hadd,heq]
  have hdiff : B 5-B s ≤ (25/78:ℝ)*(5-s) := by
    apply hsum.trans
    apply (div_le_iff₀ hsp).mpr
    nlinarith only [mul_nonneg hδ (show 0≤ s-49/10 by linarith only [hs])]
  have hlog39 : (27/20:ℝ)≤ log (39/10:ℝ) := by
    have hh := sum_range_le_log_div (by norm_num : (0:ℝ)≤29/49)
      (by norm_num : (29/49:ℝ)<1) 3
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  have hBs : (27/20:ℝ)≤ B s := by
    have hlog := log_le_log (by norm_num : (0:ℝ)<39/10) (show (39/10:ℝ)≤ s-1 by linarith only [hs])
    have hI : 0≤∫ u in (3:ℝ)..s-1, jurkatRichertInnerIntegral u/u := by
      apply intervalIntegral.integral_nonneg h3s
      intro u hu
      exact (numerical_outer_integrand ⟨hu.1,hu.2.trans hs4⟩).1
    dsimp only [B]
    linarith only [hlog,hlog39,hI]
  have hquot : (27/100:ℝ)≤ B s/s := (le_div_iff₀ hs0).mpr (by linarith only [hBs,hs5])
  have hcompare : (27/500:ℝ)*(5-s)≤ B s/s-B s/5 := by
    have hh := mul_le_mul_of_nonneg_right hquot hδ
    have heq : (B s/s)*(5-s)=5*(B s/s-B s/5) := by field_simp <;> ring
    linarith only [hh,heq]
  have hscaled : B 5/5-B s/s ≤ (41/4000:ℝ)*(5-s) := by
    nlinarith only [hdiff,hcompare,hδ]
  have hcancel : jurkatRichertMertensFactor*(2*exp eulerMascheroniConstant)=40 := by
    unfold jurkatRichertMertensFactor
    have hh : exp (-eulerMascheroniConstant)*exp eulerMascheroniConstant=1 := by
      rw [← exp_add,neg_add_cancel,exp_zero]
    nlinarith only [hh]
  calc
    _ = (jurkatRichertMertensFactor*(2*exp eulerMascheroniConstant))*(B 5/5-B s/s) := by
      unfold dimensionOneLowerLinearSieveFactor
      dsimp only [B]
      ring
    _ = 40*(B 5/5-B s/s) := by rw [hcancel]
    _ ≤ _ := by linarith only [hscaled]

theorem lower_hat_window {s : ℝ} (hs : (49/10:ℝ)≤ s) :
    exp 2*sieveHat s ≤ (1/28:ℝ) := by
  have he := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤29/10) 7
  norm_num [Finset.sum_range_succ] at he
  have he' : (120/7:ℝ)≤ exp (29/10) := by linarith only [he]
  have hid : exp 2*exp (-(49/10:ℝ))*exp (29/10)=1 := by
    rw [← exp_add,← exp_add]
    norm_num
  calc
    _ ≤ exp 2*sieveHat (49/10) := mul_le_mul_of_nonneg_left (sieveHat_antitone hs) (exp_pos 2).le
    _ = (30/49)/exp (29/10) := by
      norm_num [sieveHat]
      field_simp
      nlinarith only [hid]
    _ ≤ _ := (div_le_iff₀ (exp_pos _)).mpr (by linarith only [he'])

theorem lower_factor_upper {s : ℝ} (hs : (4:ℝ)≤ s) (hs5 : s≤5) :
    dimensionOneLowerLinearSieveFactor s ≤ 6 := by
  have hs0 : 0<s := by linarith only [hs]
  have h3s : (3:ℝ)≤ s-1 := by linarith only [hs]
  have hs4 : s-1≤(4:ℝ) := by linarith only [hs5]
  have hI0 : 0≤∫ u in (3:ℝ)..s-1, jurkatRichertInnerIntegral u/u := by
    apply intervalIntegral.integral_nonneg h3s
    intro u hu
    exact (numerical_outer_integrand ⟨hu.1,hu.2.trans hs4⟩).1
  have hI : (∫ u in (3:ℝ)..s-1, jurkatRichertInnerIntegral u/u)≤1 := by
    calc
      _ ≤ ∫ _u in (3:ℝ)..s-1, (1:ℝ) := intervalIntegral.integral_mono_on h3s
        (numerical_outer_interval (le_refl (3:ℝ)) h3s hs4) intervalIntegrable_const
        (fun u hu => (numerical_outer_integrand ⟨hu.1,hu.2.trans hs4⟩).2)
      _ = s-4 := by simp; ring
      _ ≤ 1 := by linarith only [hs5]
  have hlog0 : 0≤ log (s-1) := log_nonneg (by linarith only [hs])
  have hlog : log (s-1)≤3 := (log_le_sub_one_of_pos (by linarith only [hs])).trans (by linarith only [hs5])
  have he : exp eulerMascheroniConstant≤3 :=
    (exp_le_exp.mpr (eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num))).trans
      (exp_one_lt_d9.le.trans (by norm_num))
  have hquot : 2*exp eulerMascheroniConstant/s≤3/2 :=
    (div_le_iff₀ hs0).mpr (by linarith only [he,hs])
  unfold dimensionOneLowerLinearSieveFactor
  apply (mul_le_mul hquot (show log (s-1)+(∫ u in (3:ℝ)..s-1, jurkatRichertInnerIntegral u/u)≤4 by linarith only [hlog,hI])
    (by linarith only [hlog0,hI0]) (by norm_num)).trans
  norm_num

theorem mertens_factor_lower_one : (1:ℝ)≤ jurkatRichertMertensFactor := by
  have he : exp eulerMascheroniConstant≤3 :=
    (exp_le_exp.mpr (eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num))).trans
      (exp_one_lt_d9.le.trans (by norm_num))
  have hb : 0≤ jurkatRichertMertensFactor := by unfold jurkatRichertMertensFactor; positivity
  have hc : jurkatRichertMertensFactor*exp eulerMascheroniConstant=20 := by
    unfold jurkatRichertMertensFactor
    rw [mul_assoc,← exp_add,neg_add_cancel,exp_zero,mul_one]
  have hh := mul_le_mul_of_nonneg_left he hb
  linarith only [hh,hc]

theorem lower_density_budget {s : ℝ} (hs : (4929/1000:ℝ)≤ s) (hs5 : s≤5) :
    jurkatRichertBaseMainCoefficient jurkatRichertJ-(27/500:ℝ) ≤
      jurkatRichertMertensFactor*(dimensionOneLowerLinearSieveFactor s-
        110*(1/2000:ℝ)*exp 2*sieveHat s) := by
  have hscaled := lower_factor_scaled_loss (show (49/10:ℝ)≤ s by linarith only [hs]) hs5
  have hhat := lower_hat_window (show (49/10:ℝ)≤ s by linarith only [hs])
  have hBpos : 0≤ jurkatRichertMertensFactor := by unfold jurkatRichertMertensFactor; positivity
  have hh := mul_le_mul budget_mertens_factor_cap hhat
    (mul_nonneg (exp_pos 2).le (sieveHat_pos s).le) (by norm_num : (0:ℝ)≤25/2)
  rw [dimensionOneLowerLinearSieveFactor_five] at hscaled
  have hab := jurkatRichert_sieveFactor_mul_mertensFactor
  nlinarith only [hscaled,hh,hs,hs5,hab]

#print axioms lower_density_budget
#print axioms lower_factor_scaled_loss
#print axioms lower_hat_window
end ChenEffective.GRH125
end

/- Component: GRH125RelativeProduct -/
noncomputable section
namespace ChenEffective.GRH125
variable [Fact HybridProduct.HybridPrefixWindow]
open Real Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- This generic counting proof takes a proved window as an explicit instance.
The concrete Platt-backed witness is supplied in BJSH29ConditionalChen. -/
theorem reciprocal_prefix_window : HybridProduct.HybridPrefixWindow :=
  Fact.out

noncomputable def lowerPresieveStart : ℝ := 4000000

theorem lower_interval_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (u z : ℝ)
    (hu : lowerPresieveStart ≤ u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹) ≤ (1+(1/4000:ℝ))*(log z/log u) :=
  HybridProduct.hybrid_interval_product reciprocal_prefix_window s hs u z hu huz hinterval

theorem lower_presieved_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (hpresieve : ∀ p ∈ s, lowerPresieveStart ≤ (p : ℝ))
    (u z : ℝ) (hu : 1 < u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹) ≤ (1+(1/4000:ℝ))*(log z/log u) := by
  by_cases hUu : lowerPresieveStart ≤ u
  · exact lower_interval_product s hs u z hUu huz hinterval
  have huU : u ≤ lowerPresieveStart := le_of_not_ge hUu
  have hlu : 0 < log u := log_pos hu
  have hlz : 0 < log z := log_pos (hu.trans_le huz)
  by_cases hzU : z ≤ lowerPresieveStart
  · have hempty : s=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      linarith only [hpresieve p hp,(hinterval p hp).2,hzU]
    rw [hempty,Finset.prod_empty]
    have hr : 1 ≤ log z/log u := (le_div_iff₀ hlu).mpr
      (by simpa using log_le_log (by linarith only [hu] : 0 < u) huz)
    nlinarith only [hr,(by norm_num : (0:ℝ) ≤ 1/4000)]
  have hUz : lowerPresieveStart ≤ z := le_of_not_ge hzU
  apply (lower_interval_product s hs lowerPresieveStart z le_rfl hUz
    (fun p hp => ⟨hpresieve p hp,(hinterval p hp).2⟩)).trans
  apply mul_le_mul_of_nonneg_left _ (by linarith only [(by norm_num : (0:ℝ) ≤ 1/4000)])
  exact div_le_div_of_nonneg_left hlz.le hlu (log_le_log (by linarith only [hu] : 0 < u) huU)


theorem lower_product_relative (S : BoundingSieve)
    (hodd : ∀ p ∈ S.prodPrimes.primeFactors, 2 < p)
    (hnu : ∀ p ∈ S.prodPrimes.primeFactors, S.nu p=1/((p : ℝ)-1)) :
    HasRelativeSieveProduct (preSieveCounting S lowerPresieveStart) (1/4000:ℝ) := by
  intro u z hu huz
  unfold suzukiLocalRatio
  change (∏ p ∈ (restrictSievePrimes S lowerPresieveStart).prodPrimes.primeFactors.filter
    (fun p : ℕ => u ≤ (p : ℝ) ∧ (p : ℝ) < z), (1-S.nu p)⁻¹) ≤ _
  rw [restrictSievePrimes_primeFactors]
  let s := (S.prodPrimes.primeFactors.filter (fun p : ℕ => lowerPresieveStart ≤ (p : ℝ))).filter
    (fun p : ℕ => u ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hP := (mem_filter.mp (mem_filter.mp hp).1).1
    exact ⟨Nat.prime_of_mem_primeFactors hP,hodd p hP⟩
  have hid : (∏ p ∈ s, (1-S.nu p)⁻¹) = ∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹ := by
    apply prod_congr rfl
    intro p hp
    rw [hnu p (mem_filter.mp (mem_filter.mp hp).1).1]
  change (∏ p ∈ s, (1-S.nu p)⁻¹) ≤ _
  rw [hid]
  exact lower_presieved_product s hs (fun _ hp => (mem_filter.mp (mem_filter.mp hp).1).2)
    u z hu huz (fun _ hp => (mem_filter.mp hp).2)


#print axioms lower_product_relative
theorem lower_source_relative (N : ℕ) :
    HasRelativeSieveProduct (preSieveCounting (jurkatRichertSourceBoundingSieve N) 4000000)
      (1/4000:ℝ) := by
  apply lower_product_relative
  · intro p hp
    exact (prime_dvd_jurkatRichertSourceSiftingProduct (Nat.prime_of_mem_primeFactors hp)).mp
      (Nat.dvd_of_mem_primeFactors hp) |>.1
  · intro p hp
    exact AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (Nat.prime_of_mem_primeFactors hp)

theorem lower_conditioned_relative (N q : ℕ) :
    HasRelativeSieveProduct (preSieveCounting (jurkatRichertSourceConditionedBoundingSieve N q) 4000000)
      (1/4000:ℝ) := lower_source_relative N

end ChenEffective.GRH125
end

/- Component: GRH125BaseCandidates -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
variable [Fact HybridProduct.HybridPrefixWindow]
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem base_candidates_at_target {N : ℕ} (hN : targetCutoff   ≤   N) (hEven : Even N) :
    (jurkatRichertBaseMainCoefficient jurkatRichertJ-(3/50:ℝ))*
        (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2)   ≤
      ((jurkatRichertSourceCandidates N).card:ℝ) := by
  let S := jurkatRichertSourceBoundingSieve N
  let s := lowerRatio N 1
  let D := lowerLevel N 1
  let Z := Nat.ceil ((D:ℝ)^(1/s))
  let c := dimensionOneLowerLinearSieveFactor s-110*(1/2000:ℝ)*exp 2*sieveHat s
  let M := SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2
  let B := jurkatRichertMertensFactor
  let A := jurkatRichertBaseMainCoefficient jurkatRichertJ
  have hNbig := (lower_endpoint_parameters hN).1
  have hbase := lower_base_ratio hN
  have hslo : 4  ≤  s := by dsimp only [s]; linarith only [hbase.1]
  have hshi : s  ≤  5 := hbase.2
  obtain ⟨hD,hZD,hroot,hlevel⟩ := lower_level_geometry hN (q:=1) (by norm_num)
    (show 3/2  ≤  s by linarith only [hslo])
  have hDN : D  ≤  N := lower_level_le_endpoint hN (q:=1) (by norm_num) (by linarith only [hslo])
  have hcut : ∀ p ∈ (preSieveCounting S 4000000).prodPrimes.primeFactors, p<Z := by
    intro p hp
    change p∈(restrictSievePrimes S 4000000).prodPrimes.primeFactors at hp
    rw [restrictSievePrimes_primeFactors] at hp
    have hpf := (mem_filter.mp hp).1
    have hh := (prime_dvd_jurkatRichertSourceSiftingProduct (Nat.prime_of_mem_primeFactors hpf)).mp
      (Nat.dvd_of_mem_primeFactors hpf) |>.2.1
    exact Nat.lt_ceil.mpr (hh.trans_lt hroot)
  have hmass0 : 0  ≤  S.totalMass := LiuWeight.liuLogarithmicIntegral_nonneg (2/log 2)
    (by positivity) (by exact_mod_cast (show 2  ≤  N by omega))
  have hfinite := GRH.truncated_preSieveCounting_lower_bound S 4000000 hmass0
    (by norm_num : (0:ℝ)  ≤  1/4000) le_rfl (lower_source_relative N)
    D Z (preSieveTruncation N) (truncation_log_lower hN).1 hD hslo hshi rfl hZD hcut
  have hrem := base_truncated_remainder hN hEven (show 1  ≤  D by omega) hDN
    (by simpa only [Nat.one_mul] using hlevel)
  change GRH.truncatedRemainderBound S 4000000 D (preSieveTruncation N) ≤
    (3e-12:ℝ)*N/log (N:ℝ)^2 at hrem
  have hM0 : 0  ≤  M := by dsimp [M]; positivity [SingularSeries.liuSingularSeries_pos N]
  have hBpos : 0<B := by dsimp [B]; unfold jurkatRichertMertensFactor; positivity
  have hBmin : (1:ℝ)  ≤  B := mertens_factor_lower_one
  have hcoef : A-27/500  ≤  B*c := lower_density_budget hbase.1 hbase.2
  have hAmin : (2/5:ℝ)  ≤  A := by
    have hh := mul_le_mul_of_nonneg_right numerical_base_factor_caps.1 hBpos.le
    have hab := jurkatRichert_sieveFactor_mul_mertensFactor
    have hb := mul_le_mul_of_nonneg_left hBmin (by norm_num : (0:ℝ)  ≤  2/5)
    dsimp only [A,B] at *
    nlinarith only [hh,hab,hb]
  have hc0 : 0  ≤  c := by
    by_contra hh
    have hm := mul_neg_of_pos_of_neg hBpos (lt_of_not_ge hh)
    linarith only [hm,hcoef,hAmin]
  have hc6 : c  ≤  6 := by
    have hh := lower_factor_upper hslo hshi
    have hp : 0  ≤  110*(1/2000:ℝ)*exp 2*sieveHat s := by
      exact mul_nonneg (by positivity) (sieveHat_pos s).le
    dsimp only [c]
    linarith only [hh,hp]
  have hmass := (source_mass_at_target hN hEven).1
  change (B-1/500000)*M  ≤  S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S at hmass
  have hpaid := mul_le_mul_of_nonneg_left hmass hc0
  have hcoefM := mul_le_mul_of_nonneg_right hcoef hM0
  have hcM := mul_le_mul_of_nonneg_right hc6 hM0
  have hremM : GRH.truncatedRemainderBound S 4000000 D (preSieveTruncation N)  ≤  (6e-12:ℝ)*M := by
    have hh := mul_le_mul_of_nonneg_right (half_le_liuSingularSeries N)
      (show 0  ≤  (6e-12:ℝ)*((N:ℝ)/log (N:ℝ)^2) by positivity)
    dsimp only [M]
    simp only [div_eq_mul_inv] at hrem hh ⊢
    nlinarith only [hrem,hh]
  have hcount : (A-3/50)*M  ≤  S.siftedSum := by
    change S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S*c-
      GRH.truncatedRemainderBound S 4000000 D (preSieveTruncation N)  ≤  S.siftedSum at hfinite
    nlinarith only [hfinite,hpaid,hcoefM,hcM,hremM,hM0]
  rw [jurkatRichertSourceBoundingSieve_siftedSum_eq_card N] at hcount
  exact hcount

#print axioms base_candidates_at_target
end ChenEffective.GRH125
end

/- Component: GRH125PrimeIntervals -/
/-! Sharp reciprocal-prime intervals at the endpoints used by Chen.
The existing Dusart producer is already applicable here at H <= 30. -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LiuWeight PrimeReciprocalLogScale
open AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem lower_prime_parameters_of_log {N : ℕ} (hL : (263000:ℝ) ≤ log (N:ℝ)) :
    9 ≤ N ∧ (263000:ℝ) ≤ log (N:ℝ) ∧
      (logPowerCutoff 2:ℝ) ≤ (N:ℝ)^(1/10:ℝ) ∧
      (logPowerCutoff 2:ℝ) ≤ (N:ℝ)^(1/10:ℝ) := by
  have hn : 0<N := by
    by_contra h
    have he : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hh := log_le_sub_one_of_pos hnR
  have hn9 : 9 ≤ N := by exact_mod_cast (by linarith only [hL,hh] : (9:ℝ) ≤ N)
  have hroot : (logPowerCutoff 2:ℝ) ≤ (N:ℝ)^(1/10:ℝ) := by
    simp only [logPowerCutoff,Nat.cast_pow,Nat.cast_ofNat]
    apply (log_le_log_iff (by positivity) (rpow_pos_of_pos hnR _)).mp
    rw [log_pow,log_rpow hnR]
    have hl3 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    norm_num only [Nat.cast_ofNat,Nat.reduceAdd,Nat.reducePow,Nat.reduceMul]
    linarith only [hL,hl3]
  exact ⟨hn9,hL,hroot,hroot⟩

theorem lower_prime_prefix_of_log {N : ℕ} (hL : (263000:ℝ) ≤ log (N:ℝ))
    {a : ℝ} (ha : 1/10 ≤ a) :
    |MertensTheorem.primeReciprocalSum (rpowFloor N a)-
      (log a+log (log (N:ℝ))+mertensSecondConstant)| ≤ (1/2)/log (N:ℝ)^2 := by
  have hn9 := (lower_prime_parameters_of_log hL).1
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have ha0 : 0<a := by linarith only [ha]
  have hx : (3:ℝ)^120 ≤ (N:ℝ)^a := by
    apply (log_le_log_iff (by positivity) (rpow_pos_of_pos hn _)).mp
    rw [log_pow,log_rpow hn]
    have hla := mul_le_mul_of_nonneg_right ha hl.le
    have hl3 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    norm_num only [Nat.cast_ofNat]
    linarith only [hL,hla,hl3]
  have hlogx : 1000≤ log ((N:ℝ)^a) := by
    rw [log_rpow hn]
    have hh := mul_le_mul_of_nonneg_right ha hl.le
    linarith only [hh,hL]
  have hh := sharp_mertens_large hx hlogx
  rw [log_rpow hn,log_mul ha0.ne' hl.ne'] at hh
  rw [MertensTheorem.primeReciprocalSum_eq_analyticNumberTheory,rpowFloor]
  apply hh.trans
  apply (div_le_div_iff₀ (by positivity : 0<10000*(a*log (N:ℝ))^2) (sq_pos_of_pos hl)).mpr
  have hla := mul_le_mul_of_nonneg_right ha hl.le
  have hs := pow_le_pow_left₀ (show 0 ≤ log (N:ℝ)/10 by positivity)
    (show log (N:ℝ)/10 ≤ a*log (N:ℝ) by linarith only [hla]) 2
  nlinarith only [hs]

theorem lower_prime_interval_of_log {N : ℕ} (hL : (263000:ℝ) ≤ log (N:ℝ))
    {a b : ℝ} (ha : 1/10 ≤ a) (hab : a ≤ b) (_hb : b ≤ 1) :
    primeReciprocalLogInterval N a b ≤ log (b/a)+1/log (N:ℝ)^2 := by
  have hn9 := (lower_prime_parameters_of_log hL).1
  have hpa := lower_prime_prefix_of_log hL ha
  have hpb := lower_prime_prefix_of_log hL (ha.trans hab)
  rw [primeReciprocalLogInterval_eq_sub N (by omega) hab,
    log_div (by linarith only [ha,hab] : b≠0) (by linarith only [ha] : a≠0)]
  simp only [div_eq_mul_inv] at hpa hpb ⊢
  linarith only [(abs_le.mp hpa).1,(abs_le.mp hpb).2]

#print axioms lower_prime_interval_of_log
end ChenEffective.GRH125
end

/- Component: GRH125MediumPrimeSum -/
section
noncomputable section
namespace ChenEffective.GRH125
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
def primePairThreshold : ℕ := targetCutoff

theorem numerical_prime_pair_parameters {N : ℕ} (hN : primePairThreshold  ≤  N) :
    9  ≤  N ∧ (263000:ℝ) ≤ log (N:ℝ) ∧
      (logPowerCutoff 2:ℝ)  ≤  (N:ℝ)^(1/10:ℝ) ∧
      (logPowerCutoff 2:ℝ)  ≤  (N:ℝ)^(1/10:ℝ) :=
  lower_prime_parameters_of_log (by have h := target_log_lower hN; linarith only [h])

theorem numerical_prime_pair_interval {N : ℕ} (hN : primePairThreshold  ≤  N)
    {a b : ℝ} (ha : 1/10  ≤  a) (hab : a  ≤  b) (hb : b  ≤  1) :
    PrimeReciprocalLogScale.primeReciprocalLogInterval N a b  ≤
      log (b/a)+1/log (N:ℝ)^2 :=
  lower_prime_interval_of_log (numerical_prime_pair_parameters hN).2.1 ha hab hb


theorem numerical_prime_interval_carrier (N : ℕ) (a b : ℝ) :
    (Finset.Ioc (MertensTheorem.rpowFloor N a) (MertensTheorem.rpowFloor N b)).filter Nat.Prime =
      (Finset.range (PrimeReciprocalLogScale.rpowFloor N b+1)).filter
        (fun p : ℕ => p.Prime ∧ (N : ℝ)^a < (p : ℝ) ∧ (p : ℝ)  ≤  (N : ℝ)^b) := by
  ext p
  simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_range,Nat.lt_succ_iff,MertensTheorem.rpowFloor,
    PrimeReciprocalLogScale.rpowFloor,Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg N) a),
    Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) b)]
  tauto

theorem numerical_medium_profile_integrable {a b : ℝ} (ha : 1/10  ≤  a) (hab : a  ≤  b) (hb : b  ≤  1/3) :
    IntervalIntegrable (fun x => mediumPrimeProfile x/x) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
  · apply (show ContinuousOn mediumPrimeProfile (Icc (1/10 : ℝ) (1/3)) from
      jurkatRichertUpperLinearSieveFactor_zeroEpsilon_continuousOn).mono
    intro x hx
    exact ⟨ha.trans hx.1,hx.2.trans hb⟩
  · exact continuousOn_id
  · intro x hx
    linarith only [ha,hx.1]

/-- A quantitative one-dimensional logarithmic Darboux cell. -/
theorem numerical_medium_prime_cell {N : ℕ} (hN : primePairThreshold  ≤  N) {a b : ℝ}
    (ha : 1/10  ≤  a) (hab : a  ≤  b) (hb : b  ≤  1/3) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b  ≤
      (∫ x in a..b, mediumPrimeProfile x/x)+3600*(b-a)^2+
        192*(1/Real.log (N : ℝ)^2) := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  have hL : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha0 : 0 < a := by linarith only [ha]
  have hb0 : 0 < b := ha0.trans_le hab
  let h := b-a
  let e := 1/Real.log (N : ℝ)^2
  have hh0 : 0  ≤  h := sub_nonneg.mpr hab
  have hh1 : h  ≤  1 := by dsimp [h]; linarith only [ha,hb]
  have he0 : 0  ≤  e := by dsimp [e]; positivity
  obtain ⟨hf0,hf12,_⟩ := numerical_medium_profile ⟨ha,hab.trans hb⟩ ⟨ha,hab.trans hb⟩
  have htest : MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b  ≤
      (mediumPrimeProfile a+180*h)*PrimeReciprocalLogScale.primeReciprocalLogInterval N a b := by
    unfold MertensTheorem.weightedPrimeReciprocalLogSum
    unfold PrimeReciprocalLogScale.primeReciprocalLogInterval
    rw [← numerical_prime_interval_carrier,Finset.mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpc,hprime⟩ := mem_filter.mp hp
    obtain ⟨hpa,hpb⟩ := MertensTheorem.mem_Ioc_rpowFloor_iff.mp hpc
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have halog := Real.log_le_log (Real.rpow_pos_of_pos hN0 a) hpa.le
    have hblog := Real.log_le_log hp0 hpb
    rw [Real.log_rpow hN0] at halog hblog
    have hpinterval : Real.log (p : ℝ)/Real.log (N : ℝ) ∈ Icc a b :=
      ⟨(le_div_iff₀ hL).mpr (by nlinarith only [halog]),(div_le_iff₀ hL).mpr hblog⟩
    have hdiff := (numerical_medium_profile
      ⟨ha.trans hpinterval.1,hpinterval.2.trans hb⟩ ⟨ha,hab.trans hb⟩).2.2
    have habs : |Real.log (p : ℝ)/Real.log (N : ℝ)-a|  ≤  h := by
      rw [abs_of_nonneg (sub_nonneg.mpr hpinterval.1)]
      dsimp [h]
      linarith only [hpinterval.2]
    have hf : mediumPrimeProfile (Real.log (p : ℝ)/Real.log (N : ℝ))  ≤  mediumPrimeProfile a+180*h := by
      have h := (le_abs_self _).trans hdiff
      linarith only [h,habs]
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hf hp0.le
  have hmass := numerical_prime_pair_interval hN ha hab (by linarith only [hb] : b  ≤  1)
  have htest' := htest.trans (mul_le_mul_of_nonneg_left hmass (show 0  ≤  mediumPrimeProfile a+180*h by positivity))
  have hlog0 : 0  ≤  Real.log (b/a) := Real.log_nonneg ((le_div_iff₀ ha0).mpr (by simpa using hab))
  have hlog10 : Real.log (b/a)  ≤  10*h := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    have heq : b/a-1 = h/a := by dsimp [h]; field_simp
    apply hh.trans
    rw [heq]
    apply (div_le_iff₀ ha0).mpr
    nlinarith only [ha,mul_nonneg hh0 (sub_nonneg.mpr ha)]
  have hone : IntervalIntegrable (fun x : ℝ => 1/x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_const.div continuousOn_id (by intro x hx; linarith only [ha,hx.1])
  have hIntegral : (mediumPrimeProfile a-180*h)*Real.log (b/a)  ≤  ∫ x in a..b, mediumPrimeProfile x/x := by
    have hc := intervalIntegral.integral_mono_on hab (hone.const_mul (mediumPrimeProfile a-180*h))
      (numerical_medium_profile_integrable ha hab hb) (fun x hx => ?_)
    · rw [intervalIntegral.integral_const_mul,integral_one_div_of_pos ha0 hb0] at hc
      exact hc
    · have hdiff := (numerical_medium_profile ⟨ha,hab.trans hb⟩ ⟨ha.trans hx.1,hx.2.trans hb⟩).2.2
      have habs : |a-x|  ≤  h := by
        rw [abs_of_nonpos (sub_nonpos.mpr hx.1)]
        dsimp [h]
        linarith only [hx.2]
      have hf : mediumPrimeProfile a-180*h  ≤  mediumPrimeProfile x := by
        have hh := (le_abs_self _).trans hdiff
        linarith only [hh,habs]
      simpa only [mul_one_div] using div_le_div_of_nonneg_right hf (show 0  ≤  x by linarith only [ha,hx.1])
  have hmesh := mul_le_mul_of_nonneg_left hlog10 (show 0  ≤  360*h by positivity)
  have he := mul_le_mul_of_nonneg_right (show mediumPrimeProfile a+180*h  ≤  192 by linarith only [hf12,hh1]) he0
  change _  ≤  _+3600*h^2+192*e
  change _  ≤  (mediumPrimeProfile a+180*h)*(Real.log (b/a)+e) at htest'
  nlinarith only [htest',hIntegral,hmesh,he]

def mediumPrimeGridPoint (n i : ℕ) : ℝ := 1/10+(7/30 : ℝ)*(i : ℝ)/n

theorem mediumPrimeGridPoint_mono {n : ℕ} (hn : 0 < n) : Monotone (mediumPrimeGridPoint n) := by
  intro i j hij
  unfold mediumPrimeGridPoint
  gcongr

theorem weightedPrimeLogSum_add {N : ℕ} {a b c : ℝ} (hN : 1  ≤  N) (hab : a  ≤  b) (hbc : b  ≤  c) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a b+
      MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N b c =
      MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N a c := by
  unfold MertensTheorem.weightedPrimeReciprocalLogSum
  simp only [Finset.sum_filter]
  apply Finset.sum_Ioc_consecutive
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hab)
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hbc)

theorem numerical_medium_grid_partition {N n : ℕ} (hN : 1  ≤  N) (hn : 0 < n) (k : ℕ) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N
      (mediumPrimeGridPoint n 0) (mediumPrimeGridPoint n k) =
        ∑ i ∈ range k, MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N
          (mediumPrimeGridPoint n i) (mediumPrimeGridPoint n (i+1)) := by
  induction k with
  | zero => simp [MertensTheorem.weightedPrimeReciprocalLogSum]
  | succ k ih =>
    rw [Finset.sum_range_succ,← ih]
    exact (weightedPrimeLogSum_add hN (mediumPrimeGridPoint_mono hn (Nat.zero_le k))
      (mediumPrimeGridPoint_mono hn (Nat.le_succ k))).symm

#print axioms numerical_medium_prime_cell
end ChenEffective.GRH125

end
end

/- Derived from research/chen-numerical-study/proof-sources/H30Conditional/BJSH30ConditionalMediumPrimeSum.lean; checked as new H29 proof source. -/
section
/- Threshold-specialized companion to research/chen-effective/NumericalMediumPrimeSum.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.GRH125. -/

noncomputable section
namespace ChenEffective.GRH125
open Real Set Finset MeasureTheory
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
attribute [local irreducible] logPowerCutoff

def mediumPrimeIntegral : ℝ := ∫ a in (1/10 : ℝ)..(1/3 : ℝ), mediumPrimeProfile a/a

theorem numerical_medium_integral_caps : 0  ≤  mediumPrimeIntegral ∧ mediumPrimeIntegral  ≤  120 := by
  have hf (a : ℝ) (ha : a ∈ Icc (1/10 : ℝ) (1/3)) :
      0  ≤  mediumPrimeProfile a/a ∧ mediumPrimeProfile a/a  ≤  120 := by
    have hh := numerical_medium_profile ha ha
    have ha0 : 0 < a := by linarith only [ha.1]
    exact ⟨div_nonneg hh.1 ha0.le,(div_le_iff₀ ha0).mpr (by linarith only [hh.2.1,ha.1])⟩
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun a ha => (hf a ha).1)
  · unfold mediumPrimeIntegral
    calc
      _  ≤  ∫ _a in (1/10 : ℝ)..(1/3 : ℝ), (120 : ℝ) := intervalIntegral.integral_mono_on
        (by norm_num) (numerical_medium_profile_integrable (by norm_num) (by norm_num) (by norm_num))
        intervalIntegrable_const (fun a ha => (hf a ha).2)
      _  ≤  120 := by norm_num

theorem numerical_medium_integral_coefficient :
    jurkatRichertMertensFactor*mediumPrimeIntegral = jurkatRichertQ1MainCoefficient jurkatRichertK := by
  have hh : mediumPrimeIntegral = 2*Real.exp Real.eulerMascheroniConstant/5*(Real.log 8+jurkatRichertK/2) :=
    jurkatRichertUpperLinearSieveFactor_zeroEpsilon_integral
  rw [hh]
  unfold jurkatRichertMertensFactor jurkatRichertQ1MainCoefficient
  have he : Real.exp (-Real.eulerMascheroniConstant)*Real.exp Real.eulerMascheroniConstant=1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  calc
    _ = 8*(Real.exp (-Real.eulerMascheroniConstant)*Real.exp Real.eulerMascheroniConstant)*(Real.log 8+jurkatRichertK/2) := by ring
    _ = _ := by rw [he, mul_one]

theorem numerical_medium_prime_grid {N n : ℕ} (hN : primePairThreshold  ≤  N) (hn : 0 < n) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3)  ≤
      mediumPrimeIntegral+196/(n : ℝ)+192*(n : ℝ)*(1/Real.log (N : ℝ)^2) := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  let c := mediumPrimeGridPoint n
  let h : ℝ := (7/30 : ℝ)/n
  let e : ℝ := 1/Real.log (N : ℝ)^2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hstart : c 0 = 1/10 := by simp [c,mediumPrimeGridPoint]
  have hend : c n = 1/3 := by dsimp [c,mediumPrimeGridPoint]; field_simp; ring
  have hmono : Monotone c := mediumPrimeGridPoint_mono hn
  have hc (i : ℕ) (hi : i  ≤  n) : c i ∈ Icc (1/10 : ℝ) (1/3) := by
    have h1 := hmono (Nat.zero_le i)
    have h2 := hmono hi
    rw [hstart] at h1
    rw [hend] at h2
    exact ⟨h1,h2⟩
  have hstep (i : ℕ) : c (i+1)-c i=h := by dsimp [c,h,mediumPrimeGridPoint]; push_cast; ring
  have hint (i : ℕ) (hi : i < n) : IntervalIntegrable (fun a => mediumPrimeProfile a/a) volume (c i) (c (i+1)) :=
    numerical_medium_profile_integrable (hc i (by omega)).1 (hmono (by omega)) (hc (i+1) (by omega)).2
  have hsum := Finset.sum_le_sum (s := range n) (fun i hi =>
    numerical_medium_prime_cell hN (hc i (by have h := mem_range.mp hi; omega)).1
      (hmono (by omega)) (hc (i+1) (by have h := mem_range.mp hi; omega)).2)
  have hpartition := numerical_medium_grid_partition (N := N) (by omega : 1  ≤  N) hn n
  have hI := intervalIntegral.sum_integral_adjacent_intervals hint
  change (∑ i ∈ range n, ∫ x in c i..c (i+1), mediumPrimeProfile x/x) = _ at hI
  rw [hstart,hend] at hI
  change _ = mediumPrimeIntegral at hI
  change MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (c 0) (c n) = _ at hpartition
  rw [hstart,hend] at hpartition
  rw [← hpartition] at hsum
  simp only [hstep,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  rw [hI] at hsum
  have heq : (n : ℝ)*(3600*h^2)=196/(n : ℝ) := by dsimp [h]; field_simp; ring
  simpa only [heq,mul_assoc,mul_left_comm,e] using hsum

theorem numerical_medium_prime_unshifted {N : ℕ} (hN : primePairThreshold  ≤  N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3)  ≤
      mediumPrimeIntegral+13/2000 := by
  have hh := numerical_medium_prime_grid (n := 65000) hN (by norm_num)
  have hL := (numerical_prime_pair_parameters hN).2.1
  have hl : 0 < Real.log (N:ℝ) := by linarith only [hL]
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)  ≤  263000) hL 2
  have he : (192:ℝ)*65000*(1/log (N:ℝ)^2)  ≤  13/4000 := by
    rw [show (192:ℝ)*65000*(1/log (N:ℝ)^2) = (192*65000*1)/log (N:ℝ)^2 by ring]
    apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
    linarith only [hs]
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh,he]

#print axioms numerical_medium_prime_unshifted
end ChenEffective.GRH125
end
end

/- Component: GRH125MediumKernelCertificates -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def mediumCellStart (i : Fin 64) : ℝ := 1/10+(7/1920:ℝ)*i.val
def mediumCellRatio (i : Fin 64) : ℝ := 5-10*(mediumCellStart i+7/1920)-(71/1000:ℝ)
def mediumKernelCell (i : Fin 64) : ℝ := (7/1920:ℝ)/(mediumCellStart i*(mediumCellRatio i)^2)
def mediumExpPolynomial (u : ℝ) : ℝ := 1+u+u^2/2+u^3/6+u^4/24+u^5/120+u^6/720
def mediumHatEnvelope (s : ℝ) : ℝ :=
  if s ≤ 2 then 1 else if s ≤ 3 then 1/mediumExpPolynomial (s-2) else (3/s)/mediumExpPolynomial (s-2)
def mediumHatCell (i : Fin 64) : ℝ := (7/1920:ℝ)*mediumHatEnvelope (mediumCellRatio i)/mediumCellStart i
def mediumKernelCaps : Fin 64 → ℕ := ![240620,236566,232911,229619,226661,224010,221643,219541,217686,216064,214660,213463,212463,211651,211019,210561,210270,210142,210173,210359,210698,211187,211825,212611,213545,214627,215858,217238,218769,220455,222296,224297,226461,228793,231297,233979,236844,239900,243154,246614,250289,254188,258323,262705,267346,272262,277465,282974,288806,294981,301520,308447,315787,323569,331824,340585,349890,359780,370300,381502,393439,406174,419776,434321]
def mediumHatCaps : Fin 64 → ℕ := ![424847,428997,433775,439164,445152,451733,458900,466655,474997,483932,493467,503610,514374,525770,537816,550528,563927,578033,592871,608467,624848,642044,660088,679015,698862,715131,727791,740937,754578,768721,783376,798554,814266,830523,847337,864721,882689,901254,920432,940238,960688,981798,1003587,1026072,1049273,1073209,1097900,1123367,1149633,1176720,1204651,1233451,1258993,1243340,1228071,1213172,1198631,1184434,1170569,1157025,1143791,1130857,1118211,1105846]

theorem medium_kernel_cell_certificate (i : Fin 64) :
    mediumKernelCell i  ≤  (mediumKernelCaps i:ℝ)/100000000 := by
  fin_cases i <;> norm_num [mediumKernelCell,mediumCellStart,mediumCellRatio,mediumKernelCaps]

theorem medium_hat_cell_certificate (i : Fin 64) :
    mediumHatCell i  ≤  (mediumHatCaps i:ℝ)/100000000 := by
  fin_cases i <;> norm_num [mediumHatCell,mediumCellStart,mediumCellRatio,
    mediumHatEnvelope,mediumExpPolynomial,mediumHatCaps]

theorem medium_kernel_grid_certificate : (∑ i : Fin 64, mediumKernelCell i)  ≤  (1661/10000:ℝ) := by
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 64))) => medium_kernel_cell_certificate i)
  apply hh.trans
  norm_num [mediumKernelCaps,Fin.sum_univ_succ]

theorem medium_hat_grid_certificate : (∑ i : Fin 64, mediumHatCell i)  ≤  (53/100:ℝ) := by
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 64))) => medium_hat_cell_certificate i)
  apply hh.trans
  norm_num [mediumHatCaps,Fin.sum_univ_succ]

#print axioms medium_kernel_grid_certificate
#print axioms medium_hat_grid_certificate
end ChenEffective.GRH125
end

/- Component: GRH125MediumFactor -/
noncomputable section
namespace ChenEffective.GRH125
open Real Set
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem upper_aux_mono {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 4) :
    upperFactorAux s ≤ upperFactorAux t := by
  have hmax : max (3:ℝ) s ≤ max 3 t := max_le_max_left _ hst
  exact (sub_nonneg.mp (numerical_inner_increment (le_max_left _ _) hmax (max_le (by norm_num) ht)).1)

theorem upper_factor_shift {s t : ℝ} (hs : (3/2:ℝ) ≤ s) (hst : s ≤ t) (ht : t ≤ 4) :
    jurkatRichertMertensFactor*
      (jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor t) ≤ 50*(t-s)/(s*t) := by
  have hs0 : 0<s := by linarith only [hs]
  have ht0 : 0<t := hs0.trans_le hst
  have haux := upper_aux_mono hst ht
  have hquarter := (inner_integral_quarter (le_max_left (3:ℝ) t) (max_le (by norm_num) ht)).2
  change upperFactorAux t ≤ 1/4 at hquarter
  have haux0 := (upperFactorAux_bounds ht).1
  have hB0 : 0 ≤ jurkatRichertMertensFactor := by unfold jurkatRichertMertensFactor; positivity
  have hA0 : 0 ≤ 2*exp eulerMascheroniConstant := by positivity
  have hab : jurkatRichertMertensFactor*(2*exp eulerMascheroniConstant)=40 := by
    unfold jurkatRichertMertensFactor
    have hh : exp (-eulerMascheroniConstant)*exp eulerMascheroniConstant=1 := by
      rw [← exp_add,neg_add_cancel,exp_zero]
    nlinarith only [hh]
  have hmain : jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor t ≤ (2*exp eulerMascheroniConstant)*(1+upperFactorAux t)*(t-s)/(s*t) := by
    rw [numerical_upper_factor_formula,numerical_upper_factor_formula]
    have hh := mul_le_mul_of_nonneg_left haux (div_nonneg hA0 hs0.le)
    have heq : (2*exp eulerMascheroniConstant)/s*(1+upperFactorAux t)-
        (2*exp eulerMascheroniConstant)/t*(1+upperFactorAux t) =
        (2*exp eulerMascheroniConstant)*(1+upperFactorAux t)*(t-s)/(s*t) := by
      field_simp
    linarith only [hh,heq]
  calc
    _ ≤ jurkatRichertMertensFactor*
        ((2*exp eulerMascheroniConstant)*(1+upperFactorAux t)*(t-s)/(s*t)) :=
      mul_le_mul_of_nonneg_left hmain hB0
    _ = (jurkatRichertMertensFactor*(2*exp eulerMascheroniConstant))*
        ((1+upperFactorAux t)*(t-s)/(s*t)) := by ring
    _ = 40*(1+upperFactorAux t)*(t-s)/(s*t) := by rw [hab]; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg hs0.le ht0.le)
      nlinarith only [mul_nonneg (show 0 ≤ t-s by linarith only [hst])
        (show 0 ≤ 1/4-upperFactorAux t by linarith only [hquarter])]

theorem upper_factor_window {s t : ℝ} (hs : (3/2:ℝ) ≤ s) (hst : s ≤ t) (ht : t ≤ 4)
    (hshift : t-s ≤ 71/1000) :
    jurkatRichertMertensFactor*
      (jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor t) ≤ (71/20:ℝ)/(t-71/1000)^2 := by
  have hs0 : 0<s := by linarith only [hs]
  have ht0 : 0<t := hs0.trans_le hst
  have hden0 : 0<t-71/1000 := by linarith only [hs,hst]
  have hden : (t-71/1000)^2 ≤ s*t := by
    have ha : 0 ≤ s-(t-71/1000) := by linarith only [hshift]
    have hb : 0 ≤ t-(t-71/1000) := by norm_num
    nlinarith only [mul_nonneg ha ht0.le,mul_nonneg hb hden0.le]
  apply (upper_factor_shift hs hst ht).trans
  apply (div_le_div_iff₀ (mul_pos hs0 ht0) (sq_pos_of_pos hden0)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hshift (sq_nonneg (t-71/1000)),hden]

theorem medium_exp_polynomial_bounds {u : ℝ} (hu : 0 ≤ u) :
    1 ≤ mediumExpPolynomial u ∧ mediumExpPolynomial u ≤ exp u := by
  constructor
  · unfold mediumExpPolynomial
    have hh : 0 ≤ u+u^2/2+u^3/6+u^4/24+u^5/120+u^6/720 := by positivity
    linarith only [hh]
  · have hh := sum_le_exp_of_nonneg hu 7
    norm_num [Finset.sum_range_succ] at hh
    convert hh using 1 <;> unfold mediumExpPolynomial <;> ring

theorem medium_hat_envelope_bound {s : ℝ} (hs : (3/2:ℝ) ≤ s) :
    exp 2*sieveHat s ≤ mediumHatEnvelope s := by
  have hs0 : 0<s := by linarith only [hs]
  unfold mediumHatEnvelope
  by_cases hs2 : s ≤ 2
  · rw [if_pos hs2]
    unfold sieveHat
    rw [if_pos hs2,← exp_add]
    norm_num
  · rw [if_neg hs2]
    have hu : 0 ≤ s-2 := by linarith only [hs2]
    have hp := medium_exp_polynomial_bounds hu
    have hrec : 1/exp (s-2) ≤ 1/mediumExpPolynomial (s-2) :=
      one_div_le_one_div_of_le (by linarith only [hp.1]) hp.2
    have heq : exp 2*exp (-s)=1/exp (s-2) := by
      rw [← exp_add,one_div,← exp_neg]
      congr 1
      ring
    by_cases hs3 : s ≤ 3
    · rw [if_pos hs3]
      unfold sieveHat
      rw [if_neg hs2,if_pos hs3,heq]
      exact hrec
    · rw [if_neg hs3]
      unfold sieveHat
      rw [if_neg hs2,if_neg hs3]
      have hh := mul_le_mul_of_nonneg_left hrec
        (show 0 ≤ (3:ℝ)/s by positivity)
      calc
        _ = (3/s)*(exp 2*exp (-s)) := by ring
        _ = (3/s)*(1/exp (s-2)) := by rw [heq]
        _ ≤ (3/s)*(1/mediumExpPolynomial (s-2)) := hh
        _ = _ := by ring

#print axioms upper_factor_window
#print axioms medium_hat_envelope_bound
end ChenEffective.GRH125
end

/- Component: GRH125MediumGrid -/
noncomputable section
namespace ChenEffective.GRH125
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

def mediumGridNat (i : ℕ) : ℝ := 1/10+(7/1920:ℝ)*i

theorem medium_grid_mono : Monotone mediumGridNat := by
  intro i j hij
  unfold mediumGridNat
  gcongr

theorem weighted_log_add (f : ℝ → ℝ) {N : ℕ} {a b c : ℝ}
    (hN : 1 ≤ N) (hab : a ≤ b) (hbc : b ≤ c) :
    MertensTheorem.weightedPrimeReciprocalLogSum f N a b+
      MertensTheorem.weightedPrimeReciprocalLogSum f N b c=
      MertensTheorem.weightedPrimeReciprocalLogSum f N a c := by
  unfold MertensTheorem.weightedPrimeReciprocalLogSum
  simp only [sum_filter]
  apply sum_Ioc_consecutive
  · exact Nat.floor_mono (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hab)
  · exact Nat.floor_mono (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hbc)

theorem medium_grid_partition (f : ℝ → ℝ) {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    MertensTheorem.weightedPrimeReciprocalLogSum f N (mediumGridNat 0) (mediumGridNat n)=
      ∑ i : Fin n, MertensTheorem.weightedPrimeReciprocalLogSum f N
        (mediumGridNat i.val) (mediumGridNat (i.val+1)) := by
  induction n with
  | zero => simp [MertensTheorem.weightedPrimeReciprocalLogSum]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [← ih]
    exact (weighted_log_add f hN (medium_grid_mono (Nat.zero_le n))
      (medium_grid_mono (Nat.le_succ n))).symm

theorem medium_darboux_cell (f : ℝ → ℝ) {N : ℕ} (hN : targetCutoff ≤ N)
    {a b U : ℝ} (ha : 1/10 ≤ a) (hab : a ≤ b) (hb : b ≤ 1/3)
    (hU : 0 ≤ U) (hf : ∀ x ∈ Icc a b, f x ≤ U) :
    MertensTheorem.weightedPrimeReciprocalLogSum f N a b ≤ U*((b-a)/a+1/log (N:ℝ)^2) := by
  have hL := target_log_lower hN
  have hLp : 0<log (N:ℝ) := by linarith only [hL]
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by have := (numerical_prime_pair_parameters hN).1; omega)
  have ha0 : 0<a := by linarith only [ha]
  have hb0 : 0<b := ha0.trans_le hab
  have htest : MertensTheorem.weightedPrimeReciprocalLogSum f N a b ≤ U*PrimeReciprocalLogScale.primeReciprocalLogInterval N a b := by
    unfold MertensTheorem.weightedPrimeReciprocalLogSum
    unfold PrimeReciprocalLogScale.primeReciprocalLogInterval
    rw [← numerical_prime_interval_carrier,mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpc,hprime⟩ := mem_filter.mp hp
    obtain ⟨hpa,hpb⟩ := MertensTheorem.mem_Ioc_rpowFloor_iff.mp hpc
    have hp0 : (0:ℝ)<p := by exact_mod_cast hprime.pos
    have halog := log_le_log (rpow_pos_of_pos hNp a) hpa.le
    have hblog := log_le_log hp0 hpb
    rw [log_rpow hNp] at halog hblog
    have hx : log (p:ℝ)/log (N:ℝ)∈Icc a b :=
      ⟨(le_div_iff₀ hLp).mpr (by nlinarith only [halog]),(div_le_iff₀ hLp).mpr hblog⟩
    simpa only [mul_one_div] using div_le_div_of_nonneg_right (hf _ hx) hp0.le
  have hm := numerical_prime_pair_interval hN ha hab (by linarith only [hb])
  have hl : log (b/a) ≤ (b-a)/a := by
    have hh := log_le_sub_one_of_pos (div_pos hb0 ha0)
    convert hh using 1 <;> field_simp <;> ring
  exact htest.trans (mul_le_mul_of_nonneg_left (hm.trans (add_le_add hl le_rfl)) hU)

theorem medium_darboux_grid (f : ℝ → ℝ) {N : ℕ} (hN : targetCutoff ≤ N)
    (U : Fin 64 → ℝ) (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1)
    (hf : ∀ i x, x∈Icc (mediumCellStart i) (mediumCellStart i+7/1920) → f x ≤ U i) :
    MertensTheorem.weightedPrimeReciprocalLogSum f N (1/10) (1/3) ≤ (∑ i : Fin 64, U i*((7/1920:ℝ)/mediumCellStart i))+64*(1/log (N:ℝ)^2) := by
  have hN1 : 1 ≤ N := by have := (numerical_prime_pair_parameters hN).1; omega
  have hsum := Finset.sum_le_sum (fun i (_ : i∈(univ : Finset (Fin 64))) =>
    medium_darboux_cell f hN (a:=mediumCellStart i) (b:=mediumCellStart i+7/1920)
      (by unfold mediumCellStart; have hi := Nat.cast_nonneg (α:=ℝ) i.val; linarith only [hi])
      (by linarith)
      (by
        have hi : (i.val:ℝ) ≤ 63 := by exact_mod_cast (show i.val ≤ 63 by omega)
        unfold mediumCellStart
        linarith only [hi])
      (hU i).1 (hf i))
  have hp := medium_grid_partition f hN1 64
  have hc0 : mediumGridNat 0=(1/10:ℝ) := by norm_num [mediumGridNat]
  have hc64 : mediumGridNat 64=(1/3:ℝ) := by norm_num [mediumGridNat]
  rw [hc0,hc64] at hp
  have heq (i : Fin 64) : mediumGridNat i.val=mediumCellStart i ∧
      mediumGridNat (i.val+1)=mediumCellStart i+7/1920 := by
    constructor
    · rfl
    · unfold mediumGridNat mediumCellStart
      push_cast
      ring
  simp_rw [(heq _).1,(heq _).2] at hp
  rw [← hp] at hsum
  have hmass : (∑ i : Fin 64, U i) ≤ 64 := by
    have hh := sum_le_sum (fun i (_ : i∈(univ : Finset (Fin 64))) => (hU i).2)
    simpa using hh
  have hh := mul_le_mul_of_nonneg_right hmass (show 0 ≤ 1/log (N:ℝ)^2 by positivity)
  have hsplit : (∑ i : Fin 64, U i*((mediumCellStart i+7/1920-mediumCellStart i)/mediumCellStart i+
      1/log (N:ℝ)^2)) =
      (∑ i : Fin 64, U i*((7/1920:ℝ)/mediumCellStart i))+
        (∑ i : Fin 64, U i)*(1/log (N:ℝ)^2) := by
    rw [sum_mul,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hsplit] at hsum
  linarith only [hsum,hh]

def mediumKernelProfile (a : ℝ) : ℝ := 1/(5-10*a-(71/1000:ℝ))^2
def mediumHatProfile (a : ℝ) : ℝ := exp 2*sieveHat (5-10*a-(71/1000:ℝ))

theorem medium_cell_ratio_lower (i : Fin 64) : (3/2:ℝ) ≤ mediumCellRatio i := by
  have hi : (i.val:ℝ) ≤ 63 := by exact_mod_cast (show i.val ≤ 63 by omega)
  unfold mediumCellRatio mediumCellStart
  linarith only [hi]

theorem medium_kernel_prime_sum {N : ℕ} (hN : targetCutoff ≤ N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumKernelProfile N (1/10) (1/3) ≤ (1/6:ℝ) := by
  let U := fun i : Fin 64 => 1/(mediumCellRatio i)^2
  have hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1 := by
    intro i
    have hs := medium_cell_ratio_lower i
    dsimp only [U]
    constructor
    · positivity
    · apply (div_le_iff₀ (by nlinarith only [hs] : 0<(mediumCellRatio i)^2)).mpr
      nlinarith only [hs,sq_nonneg (mediumCellRatio i-1)]
  have hf : ∀ i x, x∈Icc (mediumCellStart i) (mediumCellStart i+7/1920) → mediumKernelProfile x ≤ U i := by
    intro i x hx
    have hs := medium_cell_ratio_lower i
    have hle : mediumCellRatio i ≤ 5-10*x-(71/1000:ℝ) := by unfold mediumCellRatio; linarith only [hx.2]
    apply one_div_le_one_div_of_le (by nlinarith only [hs] : 0<(mediumCellRatio i)^2)
    exact pow_le_pow_left₀ (by linarith only [hs]) hle 2
  have hh := medium_darboux_grid mediumKernelProfile hN U hU hf
  have hc : (∑ i : Fin 64, U i*((7/1920:ℝ)/mediumCellStart i)) ≤ (1661/10000:ℝ) := by
    convert medium_kernel_grid_certificate using 1
    apply sum_congr rfl
    intro i _
    dsimp only [U,mediumKernelCell]
    ring
  have hL := target_log_lower hN
  have he : 64*(1/log (N:ℝ)^2) ≤ (1/1000000:ℝ) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 263000) hL 2
    rw [show 64*(1/log (N:ℝ)^2)=64/log (N:ℝ)^2 by ring]
    apply (div_le_iff₀ (by nlinarith only [hL] : 0<log (N:ℝ)^2)).mpr
    nlinarith only [hp]
  linarith only [hh,hc,he]

theorem medium_hat_prime_sum {N : ℕ} (hN : targetCutoff ≤ N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumHatProfile N (1/10) (1/3) ≤ (11/20:ℝ) := by
  let U := fun i : Fin 64 => exp 2*sieveHat (mediumCellRatio i)
  have hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1 := by
    intro i
    constructor
    · exact mul_nonneg (exp_pos 2).le (sieveHat_pos _).le
    · exact sieveHat_normalized_le_one _
  have hf : ∀ i x, x∈Icc (mediumCellStart i) (mediumCellStart i+7/1920) → mediumHatProfile x ≤ U i := by
    intro i x hx
    have hle : mediumCellRatio i ≤ 5-10*x-(71/1000:ℝ) := by unfold mediumCellRatio; linarith only [hx.2]
    exact mul_le_mul_of_nonneg_left (sieveHat_antitone hle) (exp_pos 2).le
  have hh := medium_darboux_grid mediumHatProfile hN U hU hf
  have hc : (∑ i : Fin 64, U i*((7/1920:ℝ)/mediumCellStart i)) ≤ (53/100:ℝ) := by
    apply le_trans _ medium_hat_grid_certificate
    apply sum_le_sum
    intro i _
    have ha : 0 ≤ (7/1920:ℝ)/mediumCellStart i := by unfold mediumCellStart; positivity
    have hp := mul_le_mul_of_nonneg_right
      (medium_hat_envelope_bound (medium_cell_ratio_lower i)) ha
    dsimp only [U,mediumHatCell]
    convert hp using 1 <;> ring
  have hL := target_log_lower hN
  have he : 64*(1/log (N:ℝ)^2) ≤ (1/1000000:ℝ) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 263000) hL 2
    rw [show 64*(1/log (N:ℝ)^2)=64/log (N:ℝ)^2 by ring]
    apply (div_le_iff₀ (by nlinarith only [hL] : 0<log (N:ℝ)^2)).mpr
    nlinarith only [hp]
  linarith only [hh,hc,he]

#print axioms medium_kernel_prime_sum
#print axioms medium_hat_prime_sum
end ChenEffective.GRH125
end

/- Component: GRH125MediumIntegralCaps -/
noncomputable section
namespace ChenEffective.GRH125
open Real Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem medium_K_bounds : 0 ≤ jurkatRichertK ∧ jurkatRichertK ≤ (5/8:ℝ) := by
  have hpoint (u : ℝ) (hu : u∈Icc (3:ℝ) 4) :
      0 ≤ 10/(u*(5-u))*jurkatRichertInnerIntegral u ∧
      10/(u*(5-u))*jurkatRichertInnerIntegral u ≤ (5/8:ℝ) := by
    have hd : (4:ℝ) ≤ u*(5-u) := by
      nlinarith only [hu.1,hu.2,mul_nonneg (sub_nonneg.mpr hu.1) (sub_nonneg.mpr hu.2)]
    have hp := inner_integral_quarter hu.1 hu.2
    have hr : (10:ℝ)/(u*(5-u)) ≤ 5/2 :=
      (div_le_iff₀ (by linarith only [hd])).mpr (by linarith only [hd])
    constructor
    · exact mul_nonneg (by positivity) hp.1
    · exact (mul_le_mul hr hp.2 hp.1 (by norm_num)).trans (by norm_num)
  have hc : ContinuousOn (fun u : ℝ => 10/(u*(5-u))*jurkatRichertInnerIntegral u) (Icc 3 4) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      intro u hu
      have hu0 : 0<u := by linarith only [hu.1]
      have hu5 : 0<5-u := by linarith only [hu.2]
      exact (mul_pos hu0 hu5).ne'
    · apply continuousOn_jurkatRichertInnerIntegral_three_five.mono
      intro u hu
      exact ⟨hu.1,hu.2.trans (by norm_num)⟩
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ:=volume) (by norm_num : (3:ℝ) ≤ 4) hc
  unfold jurkatRichertK
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun u hu => (hpoint u hu).1)
  · calc
      _ ≤ ∫ _u in (3:ℝ)..4, (5/8:ℝ) := intervalIntegral.integral_mono_on
        (by norm_num) hi intervalIntegrable_const (fun u hu => (hpoint u hu).2)
      _ = _ := by norm_num

theorem medium_integral_small_cap : 0 ≤ mediumPrimeIntegral ∧ mediumPrimeIntegral ≤ 3 := by
  have hI0 := numerical_medium_integral_caps.1
  have hK := medium_K_bounds
  have hlog0 : 0 ≤ log (8:ℝ) := log_nonneg (by norm_num)
  have hlog : log (8:ℝ) ≤ 21/10 := by
    rw [show (8:ℝ)=2^3 by norm_num,log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [log_two_lt_d9]
  have hE : exp eulerMascheroniConstant ≤ 3 :=
    (exp_le_exp.mpr (eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num))).trans
      (exp_one_lt_d9.le.trans (by norm_num))
  have heq : mediumPrimeIntegral=(2*exp eulerMascheroniConstant/5)*(log 8+jurkatRichertK/2) :=
    jurkatRichertUpperLinearSieveFactor_zeroEpsilon_integral
  refine ⟨hI0,?_⟩
  rw [heq]
  apply (mul_le_mul (show 2*exp eulerMascheroniConstant/5 ≤ (6/5:ℝ) by linarith only [hE])
    (show log 8+jurkatRichertK/2 ≤ (5/2:ℝ) by linarith only [hlog,hK.2])
    (show 0 ≤ log 8+jurkatRichertK/2 by linarith only [hlog0,hK.1]) (by norm_num)).trans
  norm_num

#print axioms medium_integral_small_cap
end ChenEffective.GRH125
end

/- Component: GRH125MediumProfile -/
noncomputable section
namespace ChenEffective.GRH125
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

def mediumUpperProfile (a : ℝ) : ℝ :=
  (jurkatRichertMertensFactor+3/200)*mediumPrimeProfile a+
    (14413/4000:ℝ)*mediumKernelProfile a+(27533/40000:ℝ)*mediumHatProfile a

theorem medium_pointwise_budget {a s : ℝ} (ha : a∈Icc (1/10:ℝ) (1/3))
    (hs : (3/2:ℝ) ≤ s) (hst : s ≤ 5-10*a) (hshift : 5-10*a-s ≤ 71/1000) :
    (jurkatRichertMertensFactor+3/200)*
      (jurkatRichertUpperLinearSieveFactor s+110*(1/2000:ℝ)*exp 2*sieveHat s) ≤ mediumUpperProfile a := by
  let B := jurkatRichertMertensFactor
  let X := jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor (5-10*a)
  have hBmin : (1:ℝ) ≤ B := mertens_factor_lower_one
  have hBpos : 0 ≤ B := by linarith only [hBmin]
  have hK : 0 ≤ mediumKernelProfile a := by unfold mediumKernelProfile; positivity
  have hstep : B*X ≤ (71/20:ℝ)*mediumKernelProfile a := by
    have hh := upper_factor_window hs hst (show 5-10*a ≤ (4:ℝ) by linarith only [ha.1]) hshift
    convert hh using 1 <;> dsimp only [B,X,mediumKernelProfile] <;> ring
  have hX : (B+3/200)*X ≤ (14413/4000:ℝ)*mediumKernelProfile a := by
    by_cases hx : 0 ≤ X
    · have hh := mul_le_mul_of_nonneg_right hBmin hx
      have hh' := mul_le_mul_of_nonneg_left hstep (by norm_num : (0:ℝ) ≤ 203/200)
      nlinarith only [hh,hh',hstep]
    · have hx' : X ≤ 0 := le_of_not_ge hx
      have hh := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ B+3/200 by linarith only [hBpos]) hx'
      nlinarith only [hh,hK]
  have hHat : exp 2*sieveHat s ≤ mediumHatProfile a := by
    unfold mediumHatProfile
    apply mul_le_mul_of_nonneg_left _ (exp_pos 2).le
    apply sieveHat_antitone
    linarith only [hshift]
  have hHat0 : 0 ≤ exp 2*sieveHat s := mul_nonneg (exp_pos 2).le (sieveHat_pos s).le
  have hHatScaled := mul_le_mul
    (show B+3/200 ≤ (2503/200:ℝ) by have := budget_mertens_factor_cap; dsimp only [B]; linarith)
    hHat hHat0 (by norm_num : (0:ℝ) ≤ 2503/200)
  unfold mediumUpperProfile mediumPrimeProfile
  dsimp only [X,B] at *
  nlinarith only [hX,hHatScaled]

theorem medium_profile_nonneg {a : ℝ} (ha : a∈Icc (1/10:ℝ) (1/3)) :
    0 ≤ mediumUpperProfile a := by
  have hf := (numerical_medium_profile ha ha).1
  have hB : 0 ≤ jurkatRichertMertensFactor := by unfold jurkatRichertMertensFactor; positivity
  have hk : 0 ≤ mediumKernelProfile a := by unfold mediumKernelProfile; positivity
  have hh : 0 ≤ mediumHatProfile a := mul_nonneg (exp_pos 2).le (sieveHat_pos _).le
  unfold mediumUpperProfile
  positivity

theorem medium_profile_prime_sum {N : ℕ} (hN : targetCutoff ≤ N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumUpperProfile N (1/10) (1/3) ≤ jurkatRichertQ1MainCoefficient jurkatRichertK+(277/250:ℝ) := by
  let B := jurkatRichertMertensFactor
  have hBpos : 0 ≤ B := by dsimp only [B]; unfold jurkatRichertMertensFactor; positivity
  have hbase := mul_le_mul_of_nonneg_left (numerical_medium_prime_unshifted hN)
    (show 0 ≤ B+3/200 by linarith only [hBpos])
  have hk := mul_le_mul_of_nonneg_left (medium_kernel_prime_sum hN) (by norm_num : (0:ℝ) ≤ 14413/4000)
  have hh := mul_le_mul_of_nonneg_left (medium_hat_prime_sum hN) (by norm_num : (0:ℝ) ≤ 27533/40000)
  have heq : MertensTheorem.weightedPrimeReciprocalLogSum mediumUpperProfile N (1/10) (1/3) =
      (B+3/200)*MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3)+
      (14413/4000:ℝ)*MertensTheorem.weightedPrimeReciprocalLogSum mediumKernelProfile N (1/10) (1/3)+
      (27533/40000:ℝ)*MertensTheorem.weightedPrimeReciprocalLogSum mediumHatProfile N (1/10) (1/3) := by
    unfold MertensTheorem.weightedPrimeReciprocalLogSum
    rw [mul_sum,mul_sum,mul_sum,← sum_add_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    dsimp only [mediumUpperProfile,B]
    ring
  have hI := medium_integral_small_cap.2
  have hBc : B ≤ (25/2:ℝ) := budget_mertens_factor_cap
  have hmain := numerical_medium_integral_coefficient
  rw [heq]
  dsimp only [B] at *
  nlinarith only [hbase,hk,hh,hI,hBc,hmain]

theorem medium_prime_large {N q : ℕ} (hN : targetCutoff ≤ N)
    (hq : q∈jurkatRichertSourceMediumPrimes N) : 1000001 ≤ q := by
  have hr := (numerical_prime_pair_parameters hN).2.2.1
  have hc : (1000000:ℝ) ≤ (logPowerCutoff 2:ℝ) := by
    exact_mod_cast (show (1000000:ℕ) ≤ logPowerCutoff 2 by unfold logPowerCutoff; norm_num)
  have hqLower := (mem_filter.mp hq).2.2.1
  have hh : (1000000:ℝ)<q := (hc.trans hr).trans_lt hqLower
  exact_mod_cast hh

theorem medium_profile_source_sum {N : ℕ} (hN : targetCutoff ≤ N) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1)) ≤ jurkatRichertQ1MainCoefficient jurkatRichertK+(1109/1000:ℝ) := by
  have hN9 := (numerical_prime_pair_parameters hN).1
  have hN1 : 1 ≤ N := by have := (numerical_prime_pair_parameters hN).1; omega
  have hsum : (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/(q:ℝ)) =
      MertensTheorem.weightedPrimeReciprocalLogSum mediumUpperProfile N (1/10) (1/3) := by
    rw [jurkatRichertSourceMediumPrimes_eq_Ioc_rpowFloor hN1]
    rfl
  have hpoint : ∀ q ∈ jurkatRichertSourceMediumPrimes N,
      mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1) ≤ (1+1/1000000:ℝ)*(mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/(q:ℝ)) := by
    intro q hq
    have hqBig : (1000001:ℝ) ≤ q := by exact_mod_cast medium_prime_large hN hq
    have hq0 : (0:ℝ)<q := by linarith only [hqBig]
    have hqm : 0<(q:ℝ)-1 := by linarith only [hqBig]
    have hf := medium_profile_nonneg (jurkatRichertSourceMediumPrime_log_mem (by omega : 1<N) hq)
    have hr : (1:ℝ)/((q:ℝ)-1) ≤ (1+1/1000000:ℝ)/(q:ℝ) :=
      (div_le_div_iff₀ hqm hq0).mpr (by nlinarith only [hqBig])
    have hh := mul_le_mul_of_nonneg_left hr hf
    convert hh using 1 <;> ring
  have hh := sum_le_sum hpoint
  rw [← mul_sum,hsum] at hh
  have hp := mul_le_mul_of_nonneg_left (medium_profile_prime_sum hN)
    (by norm_num : (0:ℝ) ≤ 1+1/1000000)
  have hQ : jurkatRichertQ1MainCoefficient jurkatRichertK ≤ (75/2:ℝ) := by
    rw [← numerical_medium_integral_coefficient]
    exact (mul_le_mul budget_mertens_factor_cap medium_integral_small_cap.2
      medium_integral_small_cap.1 (by norm_num)).trans (by norm_num)
  linarith only [hh,hp,hQ]

#print axioms medium_profile_source_sum
end ChenEffective.GRH125
end

/- Component: GRH125MediumAggregate -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
variable [Fact HybridProduct.HybridPrefixWindow]
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem conditioned_sifted_upper {N q : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (hq : q∈jurkatRichertSourceMediumPrimes N) :
    (jurkatRichertSourceConditionedBoundingSieve N q).siftedSum ≤ (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2)*
        (mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1))+
      GRH.truncatedRemainderBound (jurkatRichertSourceConditionedBoundingSieve N q)
        4000000 (lowerLevel N q) (preSieveTruncation N) := by
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  let S₀ := jurkatRichertSourceBoundingSieve N
  let s := lowerRatio N q
  let D := lowerLevel N q
  let Z := Nat.ceil ((D:ℝ)^(1/s))
  let c := jurkatRichertUpperLinearSieveFactor s+110*(1/2000:ℝ)*exp 2*sieveHat s
  let M := SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2
  let B := jurkatRichertMertensFactor
  have hNbig := (lower_endpoint_parameters hN).1
  have hqp := (mem_filter.mp hq).2.1
  have hq0 : (0:ℝ)<q := by exact_mod_cast hqp.pos
  have hqm : 0<(q:ℝ)-1 := by
    have hh : (1:ℝ)<q := by exact_mod_cast hqp.one_lt
    linarith only [hh]
  have hs := lower_medium_ratio hN hq
  obtain ⟨hD,hZD,hroot,hlevel⟩ := lower_level_geometry hN hqp.pos hs.1
  have hcut : ∀ p∈(preSieveCounting S 4000000).prodPrimes.primeFactors, p<Z := by
    intro p hp
    change p∈(restrictSievePrimes S 4000000).prodPrimes.primeFactors at hp
    rw [restrictSievePrimes_primeFactors] at hp
    have hh := jurkatRichertSourceConditioned_primeFactor_le_cutoff N q p (mem_filter.mp hp).1
    exact Nat.lt_ceil.mpr (hh.trans_lt hroot)
  have hmass0 : 0 ≤ S.totalMass := div_nonneg
    (LiuWeight.liuLogarithmicIntegral_nonneg (2/log 2) (by positivity)
      (by exact_mod_cast (show 2 ≤ N by omega))) hqm.le
  have hf := GRH.truncated_preSieveCounting_upper_bound S 4000000 hmass0
    (by norm_num : (0:ℝ) ≤ 1/4000) le_rfl (lower_conditioned_relative N q)
    D Z (preSieveTruncation N) (truncation_log_lower hN).1 hD hs.1 hs.2 rfl hZD hcut
  have hc0 : 0 ≤ c := by
    have hh := (numerical_upper_factor_regular ⟨by linarith only [hs.1],hs.2⟩
      ⟨by linarith only [hs.1],hs.2⟩).1
    have hp : 0 ≤ 110*(1/2000:ℝ)*exp 2*sieveHat s := mul_nonneg (by positivity) (sieveHat_pos s).le
    dsimp only [c]
    linarith only [hh,hp]
  have hmass := (source_mass_at_target hN hEven).2
  change S₀.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S₀ ≤ (B+3/200)*M at hmass
  have hcond : S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S ≤ (B+3/200)*M/((q:ℝ)-1) := by
    have heq : S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S =
        (S₀.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S₀)/((q:ℝ)-1) := by
      change ((S₀.totalMass/((q:ℝ)-1))*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S₀) =
        (S₀.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S₀)/((q:ℝ)-1)
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hmass hqm.le
  have hm := mul_le_mul_of_nonneg_right hcond hc0
  have ha := jurkatRichertSourceMediumPrime_log_mem (by omega : 1<N) hq
  have hshift := lower_ratio_shift hN hqp.pos
  have hp := medium_pointwise_budget ha hs.1 (by linarith only [hshift.1]) hshift.2
  change (B+3/200)*c ≤ mediumUpperProfile (log (q:ℝ)/log (N:ℝ)) at hp
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity [SingularSeries.liuSingularSeries_pos N]
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hM0) hqm.le
  have hm' : S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S*c ≤ M*(mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1)) := by
    apply hm.trans
    convert hh using 1 <;> ring
  change S.siftedSum ≤ S.totalMass*AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S*c+
    GRH.truncatedRemainderBound S 4000000 D (preSieveTruncation N) at hf
  exact hf.trans (add_le_add hm' le_rfl)

theorem medium_aggregate_at_target {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    jurkatRichertSourceMediumPrimeAggregate N ≤ (jurkatRichertQ1MainCoefficient jurkatRichertK+(111/100:ℝ))*
        (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  let M := SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2
  let D := lowerLevel N
  let R := fun q => GRH.truncatedRemainderBound (jurkatRichertSourceConditionedBoundingSieve N q)
    4000000 (D q) (preSieveTruncation N)
  have hD : ∀ q∈jurkatRichertSourceMediumPrimes N, 1 ≤ D q := by
    intro q hq
    have hh := (lower_level_geometry hN (mem_filter.mp hq).2.1.pos (lower_medium_ratio hN hq).1).1
    change 1 < D q at hh
    omega
  have hDN : ∀ q∈jurkatRichertSourceMediumPrimes N, D q ≤ N := fun q hq =>
    lower_level_le_endpoint hN (mem_filter.mp hq).2.1.pos (lower_medium_ratio hN hq).1
  have hlevel : ∀ q∈jurkatRichertSourceMediumPrimes N,
      preSieveTruncation N*D q ≤ jurkatRichertSourceUpperLevel N q (1/500:ℝ) := fun q hq =>
    lower_level_in_source hN (mem_filter.mp hq).2.1.pos (lower_medium_ratio hN hq).1
  have hr := medium_truncated_remainders hN hEven D hD hDN hlevel
  change (∑ q∈jurkatRichertSourceMediumPrimes N, R q) ≤ (3e-12:ℝ)*N/log (N:ℝ)^2 at hr
  have hs := sum_le_sum (fun q (_ : q∈jurkatRichertSourceMediumPrimes N) =>
    conditioned_sifted_upper hN hEven ‹q∈jurkatRichertSourceMediumPrimes N›)
  have heq : (∑ q∈jurkatRichertSourceMediumPrimes N,
      (jurkatRichertSourceConditionedBoundingSieve N q).siftedSum)=jurkatRichertSourceMediumPrimeAggregate N := by
    unfold jurkatRichertSourceMediumPrimeAggregate
    apply sum_congr rfl
    intro q _
    exact jurkatRichertSourceConditionedBoundingSieve_siftedSum_eq_card N q
  rw [heq,sum_add_distrib,← mul_sum] at hs
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity [SingularSeries.liuSingularSeries_pos N]
  have hp := mul_le_mul_of_nonneg_left (medium_profile_source_sum hN) hM0
  have hrM : (∑ q∈jurkatRichertSourceMediumPrimes N, R q) ≤ (6e-12:ℝ)*M := by
    have hh := mul_le_mul_of_nonneg_right (half_le_liuSingularSeries N)
      (show 0 ≤ (6e-12:ℝ)*((N:ℝ)/log (N:ℝ)^2) by positivity)
    dsimp only [M]
    simp only [div_eq_mul_inv] at hr hh ⊢
    nlinarith only [hr,hh]
  change jurkatRichertSourceMediumPrimeAggregate N ≤ _
  change jurkatRichertSourceMediumPrimeAggregate N ≤ M*(∑ q∈jurkatRichertSourceMediumPrimes N, mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1))+
      ∑ q∈jurkatRichertSourceMediumPrimes N, R q at hs
  nlinarith only [hs,hp,hrM,hM0]

#print axioms medium_aggregate_at_target
end ChenEffective.GRH125
end

/- Component: GRH125WeightedLower -/
noncomputable section
namespace ChenEffective.GRH125
open Real
open MathlibNt.SieveTheory SwitchingPrinciple
variable [Fact HybridProduct.HybridPrefixWindow]
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

omit [Fact HybridProduct.HybridPrefixWindow] in
theorem endpoint_payment_at_target {N : ℕ} (hN : targetCutoff ≤ N) :
    60*(N:ℝ)^(9/10:ℝ) ≤ (1/20000:ℝ)*
      (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by have := (lower_endpoint_parameters hN).1; omega)
  have hp := truncated_polynomial_payment hL (A:=(60:ℝ)) (by norm_num)
    (α:=(1/10:ℝ)) (by norm_num) (k:=2) (by norm_num)
  have hid : (N:ℝ)^(9/10:ℝ)=(N:ℝ)*exp (-(1/10:ℝ)*log (N:ℝ)) := by
    calc
      _ = exp (log (N:ℝ)*(9/10:ℝ)) := rpow_def_of_pos hn _
      _ = exp (log (N:ℝ))*exp (-(1/10:ℝ)*log (N:ℝ)) := by
        rw [← exp_add]
        congr 1
        ring
      _ = _ := by rw [exp_log hn]
  have hfirst : 60*(N:ℝ)^(9/10:ℝ) ≤ (1e-6:ℝ)*((N:ℝ)/log (N:ℝ)^2) := by
    calc
      _ = ((60:ℝ)*(log (N:ℝ))^2*exp (-(1/10:ℝ)*log (N:ℝ)))*
          ((N:ℝ)/log (N:ℝ)^2) := by rw [hid]; field_simp [hl.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)
  have hs := half_le_liuSingularSeries N
  have hc : (1e-6:ℝ) ≤ (1/20000:ℝ)*SingularSeries.liuSingularSeries N := by linarith only [hs]
  have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ (N:ℝ)/log (N:ℝ)^2 by positivity)
  apply hfirst.trans
  convert hh using 1 <;> ring

omit [Fact HybridProduct.HybridPrefixWindow] in
theorem source_boundary_at_target {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    jurkatRichertSourceWeightedCount N ≤ jurkatRichertWeightedCount N+
      (1/20000:ℝ)*(SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hsmall : (2:ℕ)^110+1 ≤ 3^100 := by norm_num
  have hpower : (3:ℕ)^100 ≤ targetCutoff := by
    rw [targetCutoff_eq]
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hbig : (2:ℕ)^110<N := by have hh := hsmall.trans (hpower.trans hN); omega
  have hb := jurkatRichertSourceWeightedCount_sub_boundary_le_distinct N hbig hEven
  have hp := jurkatRichertDistinctWeightedCount_sub_proper_le N hbig hEven
  have he := endpoint_payment_at_target hN
  have hn : 0 ≤ (N:ℝ)^(9/10:ℝ) := rpow_nonneg (Nat.cast_nonneg N) _
  nlinarith only [hb,hp,he,hn]

theorem weighted_lower_of_window {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    (2.02575:ℝ)*(SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) ≤
      jurkatRichertWeightedCount N := by
  let b : ChenBudget := ⟨3/50,111/100,1/20000,0,0⟩
  have hh := chen_budget_weighted b (base_candidates_at_target hN hEven)
    (medium_aggregate_at_target hN hEven) (source_boundary_at_target hN hEven)
  convert hh using 1
  norm_num [b,ChenBudget.weighted]

#print axioms weighted_lower_of_window
end ChenEffective.GRH125
end

/- Component: GRH125PrimePairGrid -/
/-! A width-sensitive rectangle error, avoiding a fixed error per grid cell. -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open LiuWeight PrimeReciprocalLogScale PrimeReciprocalLogRectangle
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def pairIntervalError (N : ℕ) : ℝ := 1/log (N:ℝ)^2

private opaque pairGridCertificate : {n : ℕ // n=200000} := ⟨200000,rfl⟩
def pairGrid : ℕ := pairGridCertificate.1
theorem pairGrid_eq : pairGrid=200000 := pairGridCertificate.2
theorem pairGrid_pos : 0<pairGrid := by rw [pairGrid_eq]; norm_num

theorem pair_log_mass {a b : ℝ} (ha : 1/10 ≤ a) (hab : a ≤ b) :
    0 ≤ log (b/a) ∧ log (b/a) ≤ 10*(b-a) := by
  have ha0 : 0<a := by linarith only [ha]
  have hb0 : 0<b := ha0.trans_le hab
  refine ⟨log_nonneg ((le_div_iff₀ ha0).mpr (by simpa using hab)), ?_⟩
  have hh := log_le_sub_one_of_pos (div_pos hb0 ha0)
  have he : b/a-1=(b-a)/a := by field_simp
  rw [he] at hh
  apply hh.trans
  apply (div_le_iff₀ ha0).mpr
  nlinarith only [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ 10*a-1 by linarith only [ha])]

theorem pair_rectangle {N : ℕ} (hN : targetCutoff ≤ N) {a₀ a₁ b₀ b₁ : ℝ}
    (ha : 1/10 ≤ a₀) (haa : a₀ ≤ a₁) (ha1 : a₁ ≤ 1)
    (hb : 1/10 ≤ b₀) (hbb : b₀ ≤ b₁) (hb1 : b₁ ≤ 1) :
    primeReciprocalLogRectangle N a₀ a₁ b₀ b₁ ≤
      logarithmicRectangleMass a₀ a₁ b₀ b₁+
        10*((a₁-a₀)+(b₁-b₀))*pairIntervalError N+pairIntervalError N^2 := by
  have hd0 : 0 ≤ pairIntervalError N := by unfold pairIntervalError; positivity
  have hA := numerical_prime_pair_interval hN ha haa ha1
  have hB := numerical_prime_pair_interval hN hb hbb hb1
  change _ ≤ log (a₁/a₀)+pairIntervalError N at hA
  change _ ≤ log (b₁/b₀)+pairIntervalError N at hB
  have hAn : 0 ≤ primeReciprocalLogInterval N a₀ a₁ := sum_nonneg fun _ _ => by positivity
  have hBn : 0 ≤ primeReciprocalLogInterval N b₀ b₁ := sum_nonneg fun _ _ => by positivity
  have hma := pair_log_mass ha haa
  have hmb := pair_log_mass hb hbb
  have hh := mul_le_mul hA hB hBn (add_nonneg hma.1 hd0)
  have hda := mul_le_mul_of_nonneg_right hma.2 hd0
  have hdb := mul_le_mul_of_nonneg_right hmb.2 hd0
  rw [primeReciprocalLogRectangle_eq_mul,logarithmicRectangleMass]
  nlinarith only [hh,hda,hdb]

theorem pair_grid (n N : ℕ) (hn : 0<n) (hN : targetCutoff ≤ N) :
    liuLogGridMajorant n N ≤ liuLogGridUpperSum n+
      30*(n:ℝ)*pairIntervalError N+5*(n:ℝ)^2*pairIntervalError N^2 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hd0 : 0 ≤ pairIntervalError N := by unfold pairIntervalError; positivity
  have hcard : ((liuLogGridCells n).card:ℝ) ≤ (n:ℝ)^2 := by
    have hh := card_le_univ (liuLogGridCells n)
    have hc : (liuLogGridCells n).card ≤ n*n := by simpa using hh
    simpa only [pow_two,Nat.cast_mul] using (show ((liuLogGridCells n).card:ℝ)≤(n*n:ℕ) by exact_mod_cast hc)
  have he0 : 0 ≤ 30*pairIntervalError N/(n:ℝ)+5*pairIntervalError N^2 := by positivity
  have hcells : liuLogGridMajorant n N ≤ liuLogGridUpperSum n+
      ((liuLogGridCells n).card:ℝ)*(30*pairIntervalError N/(n:ℝ)+5*pairIntervalError N^2) := by
    unfold liuLogGridMajorant liuLogGridUpperSum
    rw [show ((liuLogGridCells n).card:ℝ)*(30*pairIntervalError N/(n:ℝ)+5*pairIntervalError N^2) =
      ∑ _q ∈ liuLogGridCells n, (30*pairIntervalError N/(n:ℝ)+5*pairIntervalError N^2) by simp only [sum_const,nsmul_eq_mul] <;> ring]
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro q hq
    have ha0 : 1/10 ≤ liuAlphaGridPoint n q.1 := by
      rw [liuAlphaGridPoint_eq_step hn]
      exact le_add_of_nonneg_right (by positivity [liuAlphaGridStep_pos hn])
    have hb0 : 1/10 ≤ liuBetaGridPoint n q.2 := by
      rw [liuBetaGridPoint_eq_step hn]
      have hh : 0≤(q.2:ℝ)*liuBetaGridStep n := by positivity [liuBetaGridStep_pos hn]
      linarith only [hh]
    have hb1 := ChenEffective.numerical_beta_grid_endpoint hn q.2.isLt
    have hr := pair_rectangle hN ha0 (liuAlphaGridPoint_lt_succ hn).le
      ((liuAlphaGridPoint_succ_le_end hn q.1.isLt).trans (by norm_num)) hb0
      (liuBetaGridPoint_lt_succ hn).le (hb1.trans (by norm_num))
    have hw : 10*((liuAlphaGridPoint n (q.1+1)-liuAlphaGridPoint n q.1)+
        (liuBetaGridPoint n (q.2+1)-liuBetaGridPoint n q.2)) ≤ 6/(n:ℝ) := by
      rw [liuAlphaGridPoint_eq_step hn,liuAlphaGridPoint_eq_step hn,
        liuBetaGridPoint_eq_step hn,liuBetaGridPoint_eq_step hn]
      simp only [Nat.cast_add,Nat.cast_one,liuAlphaGridStep,liuBetaGridStep]
      field_simp <;> ring_nf <;> norm_num
    have hk := liuLogGrid_upperKernel_le_five hn hq
    have hk0 : 0 ≤ 1/(1-liuAlphaGridPoint n (q.1+1)-liuBetaGridPoint n (q.2+1)) := by
      have hh := liuLogGridCell_upperCorner_lt_one hn hq
      apply div_nonneg (by norm_num)
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_left hr hk0
    have her := mul_le_mul_of_nonneg_right hw hd0
    have hep := mul_le_mul_of_nonneg_left (show
      10*((liuAlphaGridPoint n (q.1+1)-liuAlphaGridPoint n q.1)+
        (liuBetaGridPoint n (q.2+1)-liuBetaGridPoint n q.2))*pairIntervalError N+
        pairIntervalError N^2 ≤ 6/(n:ℝ)*pairIntervalError N+pairIntervalError N^2 by
          linarith only [her]) hk0
    have he := mul_le_mul_of_nonneg_right hk (show
      0 ≤ 6/(n:ℝ)*pairIntervalError N+pairIntervalError N^2 by positivity)
    have hid : 5*(6/(n:ℝ)*pairIntervalError N+pairIntervalError N^2)=
      30*pairIntervalError N/(n:ℝ)+5*pairIntervalError N^2 := by ring
    rw [hid] at he
    nlinarith only [hh,hep,he]
  apply hcells.trans
  have hh := mul_le_mul_of_nonneg_right hcard he0
  have hid : (n:ℝ)^2*(30*pairIntervalError N/(n:ℝ)+5*pairIntervalError N^2)=
      30*(n:ℝ)*pairIntervalError N+5*(n:ℝ)^2*pairIntervalError N^2 := by field_simp <;> ring
  rw [hid] at hh
  linarith only [hh]

theorem pair_proxy_at_target {N : ℕ} (hN : targetCutoff ≤ N) :
    log (N:ℝ)*liuSourceReciprocalLogSum N ≤ (0.49644:ℝ) := by
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hn9 := (numerical_prime_pair_parameters hN).1
  have he0 : 0 ≤ pairIntervalError N := by unfold pairIntervalError; positivity
  have he : pairIntervalError N ≤ (1/65000000000:ℝ) := by
    unfold pairIntervalError
    apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
    nlinarith only [hL,sq_nonneg (log (N:ℝ)-263000)]
  have hes := pow_le_pow_left₀ he0 he 2
  have hg := pair_grid pairGrid N pairGrid_pos hN
  have hm := liuLogGridUpperSum_sub_source_le pairGrid pairGrid_pos
  have hc := liuPairLogKernelSum_le_logGridMajorant pairGrid N pairGrid_pos (by omega)
  rw [← log_mul_liuSourceReciprocalLogSum_eq_pairLogKernelSum N (by omega)] at hc
  have hmesh : 759/(pairGrid:ℝ)≤(0.003795:ℝ) := by rw [pairGrid_eq]; norm_num
  have hfinite : 30*(pairGrid:ℝ)*pairIntervalError N+
      5*(pairGrid:ℝ)^2*pairIntervalError N^2≤(0.0001:ℝ) := by
    rw [pairGrid_eq]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [he,hes]
  linarith only [hg,hm,hc,hmesh,hfinite,liuSourceMainIntegral_lt]

#print axioms pair_proxy_at_target
end ChenEffective.GRH125
end

/- Component: GRH125PrimePairMain -/
noncomputable section
namespace ChenEffective.GRH125
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

theorem numerical_prime_pair_reciprocal {N : ℕ} (hN : targetCutoff ≤ N) :
    liuWeightPairReciprocalSum N ≤ 1/2 := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  have hL0 : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hsum : liuWeightPairReciprocalSum N ≤ liuPairLogKernelSum N := by
    apply sum_le_sum
    intro p hp
    have hpp : (0 : ℝ) < (p.1 : ℝ)*p.2 := by exact_mod_cast liuWeightPairs_product_pos hp
    have hden := one_sub_primeLogExponent_pos (by omega : 8 ≤ N) hp
    have ha0 : 0 ≤ primeLogExponent N p.1 := div_nonneg (Real.log_natCast_nonneg _) hL0.le
    have hb0 : 0 ≤ primeLogExponent N p.2 := div_nonneg (Real.log_natCast_nonneg _) hL0.le
    apply one_div_le_one_div_of_le (mul_pos hpp hden)
    nlinarith only [mul_nonneg hpp.le ha0,mul_nonneg hpp.le hb0]
  rw [← log_mul_liuSourceReciprocalLogSum_eq_pairLogKernelSum N (by omega)] at hsum
  exact hsum.trans ((pair_proxy_at_target hN).trans (by norm_num))

theorem numerical_genuine_li_sum {N : ℕ} (hN : targetCutoff ≤ N) :
    |liuGenuineLiRemainderSum 2 N| ≤ (1 : ℝ)/5000*N/Real.log (N : ℝ) := by
  obtain ⟨hN9,hlog,_,hcut⟩ := numerical_prime_pair_parameters hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hpair : ∀ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
      |liuLogarithmicIntegralRemainder 2 ((N : ℝ)/(p.1*p.2))| ≤
        9*10*(N : ℝ)/(((p.1 : ℝ)*p.2)*Real.log (N : ℝ)^2) := by
    intro p hp
    apply liuLogarithmicIntegralRemainder_pair_le 2 10 (by norm_num) N (by omega) p hp
    apply numerical_genuine_li_pointwise
    have hpp : (0 : ℝ) < (p.1 : ℝ)*p.2 := by exact_mod_cast liuWeightPairs_product_pos hp
    have hx0 : 0 < (N : ℝ)/((p.1 : ℝ)*p.2) := div_pos hN0 hpp
    have hxlog := one_third_mul_log_le_log_div_of_mem_liuWeightPairs (by omega : 8 ≤ N) hp
    have hroot : (N : ℝ)^(1/10 : ℝ) ≤ (N : ℝ)/((p.1 : ℝ)*p.2) := by
      apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hN0 _) hx0).mp
      rw [Real.log_rpow hN0]
      linarith only [hxlog,hL0]
    exact hcut.trans hroot
  have hsum : |liuGenuineLiRemainderSum 2 N| ≤ 45*(N : ℝ)/Real.log (N : ℝ)^2 := by
    unfold liuGenuineLiRemainderSum
    calc
      _ ≤ ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
          |liuLogarithmicIntegralRemainder 2 ((N : ℝ)/(p.1*p.2))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
          9*10*(N : ℝ)/(((p.1 : ℝ)*p.2)*Real.log (N : ℝ)^2) := sum_le_sum hpair
      _ = (9*10*(N : ℝ)/Real.log (N : ℝ)^2)*liuWeightPairReciprocalSum N :=
        liuGenuineLiRemainderSum_factor 10 N
      _ ≤ (9*10*(N : ℝ)/Real.log (N : ℝ)^2)*(1/2) :=
        mul_le_mul_of_nonneg_left (numerical_prime_pair_reciprocal hN) (by positivity)
      _ = _ := by ring
  apply hsum.trans
  apply (div_le_div_iff₀ (sq_pos_of_pos hL0) hL0).mpr
  have hcoef : (45 : ℝ) ≤ Real.log (N : ℝ)/5000 := by
    norm_num at hlog ⊢
    linarith only [hlog]
  have hh := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (N : ℝ)*Real.log (N : ℝ) by positivity)
  nlinarith only [hh]

theorem numerical_prime_pair_main {N : ℕ} (hN : targetCutoff ≤ N) :
    LiuGenuineLiWeightMainSumBound 2 (0.498) N := by
  obtain ⟨hN9,hlog,_,_⟩ := numerical_prime_pair_parameters hN
  have hL0 : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hsrc := pair_proxy_at_target hN
  have hrem := numerical_genuine_li_sum hN
  have hproxy : liuWeightMainSum (fun x : ℝ => x/Real.log x) N ≤
      (0.49644 : ℝ)*N/Real.log (N : ℝ) := by
    rw [liuWeightMainSum_div_log_eq N (by omega)]
    apply (le_div_iff₀ hL0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hsrc (Nat.cast_nonneg (α := ℝ) N)]
  refine ⟨liuWeightMainSum_logarithmicIntegral_nonneg 2 (by norm_num) N (by omega),?_⟩
  rw [liuWeightMainSum_logarithmicIntegral_eq_proxy_add_remainder]
  have htail := (le_abs_self (liuGenuineLiRemainderSum 2 N)).trans hrem
  have hNn : 0 ≤ (N : ℝ)/Real.log (N : ℝ) := by positivity
  simp only [div_eq_mul_inv] at hproxy htail hNn ⊢
  nlinarith only [hproxy,htail,hNn]

#print axioms numerical_prime_pair_main
end ChenEffective.GRH125
end

/- Component: GRH125High -/
noncomputable section
namespace ChenEffective.GRH125.High
open Classical Complex Finset Filter MeasureTheory
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open ChenEffective.NumericalPanHigh
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
theorem numerical_high_log_four {N : ℕ} (hN : GRH125.targetCutoff≤ N) : 4≤ Real.log (N:ℝ) := by
  have h := GRH125.target_log_lower hN
  linarith only [h]
theorem numerical_source_power {B N : ℕ} (hN : GRH125.targetCutoff≤ N) (hB : B≤38) :
    (N : ℝ)^(2/3 : ℝ) ≤ upperConductor N (B : ℝ)^2 := by
  have hL := numerical_high_log_four hN
  have hl0 : 0 < Real.log (N : ℝ) := by linarith only [hL]
  have hN9 := GRH125.target_nine_le hN
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hp := GRH125.log_power_at_target hN (k:=2*B) (by omega) (δ:=1/3) (by norm_num)
  have heq : lowConductor N (B : ℝ)^2 = Real.log (N : ℝ)^(2*B) := by
    rw [lowConductor, Real.rpow_natCast, ← pow_mul, Nat.mul_comm B 2]
  rw [upperConductor_square, le_div_iff₀ (by unfold lowConductor; positivity), heq]
  calc
    _ ≤ (N : ℝ)^(2/3 : ℝ) * (N : ℝ)^(1/3 : ℝ) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hN0.le _)
    _ = _ := by rw [← Real.rpow_add hN0]; norm_num

theorem numerical_source_cell_uniform (B N : ℕ) (hN : GRH125.targetCutoff≤ N) (hB : B≤38)
    (j m A₁ A₂ k : ℕ) (f : ℕ → ℂ) (hAN : A₂ ≤ N)
    (hRD : conductorRadius N (B : ℝ) j ≤ upperConductor N (B : ℝ))
    (hA : (A₂ : ℝ) ≤ (N : ℝ)^(2/3 : ℝ))
    (hAlow : Real.log (N : ℝ)^((2 : ℝ)*B) ≤ A₁)
    (hf : ∀ n, ‖f n‖ ≤ 1) :
    sourceCell f m N A₁ A₂ k (conductorRadius N (B : ℝ) j) ≤
      6*liuPanPerronHalfStep N^(1/2 : ℝ)*
        (panShortConstant*Real.sqrt N*Real.log N^(1-(B : ℝ)))*Real.log (1+panSourceHeight N) +
      6*liuPanPerronHalfStep N^panSourceSigma N*
        (panLongConstant*Real.log N^2/Real.log N^(B : ℝ))*Real.log (1+panSourceHeight N) +
      776/(N : ℝ) := by
  have hlog := numerical_high_log_four hN
  have hl1 : 1 ≤ Real.log (N : ℝ) := by linarith only [hlog]
  have hNpos : 1 ≤ N := source_pos_of_log hl1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR := conductorRadius_ge_one j hl1 (Nat.cast_nonneg B)
  have hH := shortCutoff_le_x hl1 (Nat.cast_nonneg B) (by linarith only [hR]) hRD
  obtain ⟨_, rfl, _, hlong⟩ := NumericalPanHigh.chosen_long_mean_uniform
  have hmain := source_cell_bound_of_means f hf m A₁ A₂ k hlog hNpos le_rfl hAN hR hH
    (show 0 ≤ panShortConstant*Real.sqrt N*Real.log N^(1-(B : ℝ)) by
      unfold panShortConstant; have hh := panSharpConstant_pos; positivity)
    (show 0 ≤ panLongConstant*Real.log N^2/Real.log N^(B : ℝ) by
      unfold panLongConstant; have hh := panSharpConstant_pos; positivity)
    (fun s hs => shortMean_le_log_scale f hf m A₁ A₂ k N (Nat.cast_nonneg B) hl1 hR hRD
      (hA.trans (numerical_source_power hN hB)) s hs)
    (fun s hs => hlong (B : ℝ) N N j m A₁ A₂ k f s (Nat.cast_nonneg B) hl1 le_rfl hAlow hf hs)
  apply hmain.trans
  apply add_le_add le_rfl
  have hRx : conductorRadius N (B : ℝ) j ≤ (N : ℝ) :=
    hRD.trans ((upperConductor_le_sqrt hl1 (Nat.cast_nonneg B)).trans
      (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hNpos))))
  calc
    _ ≤ 2*(N : ℝ)*(388/(N : ℝ)^2) := by gcongr
    _ = _ := by field_simp; norm_num

theorem numerical_source_cell_log_saving (B x : ℕ) (hx : GRH125.targetCutoff≤ x) (hBcap : B≤38)
    (j m A₁ A₂ k : ℕ) (f : ℕ → ℂ)
    (hAx : A₂ ≤ x) (hRD : conductorRadius x (B : ℝ) j ≤ upperConductor x (B : ℝ))
    (hApower : (A₂ : ℝ) ≤ (x : ℝ)^(2/3 : ℝ))
    (hAlow : Real.log (x : ℝ)^((2 : ℝ)*B) ≤ A₁) (hf : ∀ n, ‖f n‖ ≤ 1) :
    sourceCell f m x A₁ A₂ k (conductorRadius x (B : ℝ) j) ≤
      panCellConstant * x * Real.log x^(4-(B : ℝ)) + 776/(x : ℝ) := by
  have hxlog := numerical_high_log_four hx
  have hCs : 0 < panShortConstant := by unfold panShortConstant; exact mul_pos (by norm_num) panSharpConstant_pos
  have hCl : 0 < panLongConstant := by unfold panLongConstant; have := panSharpConstant_pos; positivity
  have hxlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hxpos := source_pos_of_log hxlog1
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hxpos
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hmain := numerical_source_cell_uniform B x hx hBcap j m A₁ A₂ k f hAx hRD hApower hAlow hf
  have hsqrt : liuPanPerronHalfStep x ^ (1 / 2 : ℝ) ≤ 2 * Real.sqrt x := by
    rw [← Real.sqrt_eq_rpow]
    have hsq := Real.sq_sqrt (halfStep_pos x).le
    have hxq := Real.sq_sqrt hx0.le
    have hp := Real.sqrt_nonneg (liuPanPerronHalfStep x)
    have hxp := Real.sqrt_nonneg (x : ℝ)
    unfold liuPanPerronHalfStep at hsq hp ⊢
    nlinarith
  have hlogT := log_source_height_le hxlog1
  have hlognonneg : 0 ≤ Real.log (1 + panSourceHeight x) :=
    Real.log_nonneg (by have : 0 < panSourceHeight x := Real.exp_pos _; linarith)
  have hshort :
      6 * liuPanPerronHalfStep x ^ (1 / 2 : ℝ) *
          (panShortConstant * Real.sqrt x * Real.log x ^ (1 - (B : ℝ))) * Real.log (1 + panSourceHeight x) ≤
        36 * panShortConstant * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) := by
    calc
      _ ≤ 6 * (2 * Real.sqrt x) * (panShortConstant * Real.sqrt x * Real.log x ^ (1 - (B : ℝ))) *
          (3 * (Real.log x) ^ 2) := by gcongr
      _ = 36 * panShortConstant * (x : ℝ) * Real.log x ^ (3 - (B : ℝ)) := by
        rw [show (3 - (B : ℝ) : ℝ) = (1 - (B : ℝ)) + 2 by ring, Real.rpow_add hlogpos,
          Real.rpow_two]
        calc
          _ = 36 * panShortConstant * (Real.sqrt (x : ℝ)) ^ 2 *
              (Real.log x ^ (1 - (B : ℝ)) * (Real.log x) ^ 2) := by ring
          _ = _ := by rw [Real.sq_sqrt hx0.le]
      _ ≤ _ := by
        gcongr
        norm_num
  have hlong :
      6 * liuPanPerronHalfStep x ^ panSourceSigma x *
          (panLongConstant * (Real.log x) ^ 2 / Real.log x ^ (B : ℝ)) * Real.log (1 + panSourceHeight x) ≤
        (36 * Real.exp 2 * panLongConstant) * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) := by
    calc
      _ ≤ 6 * (2 * Real.exp 2 * (x : ℝ)) *
          (panLongConstant * (Real.log x) ^ 2 / Real.log x ^ (B : ℝ)) * (3 * (Real.log x) ^ 2) := by
        gcongr
        exact halfStep_source_power_le_linear hxlog hxpos le_rfl
      _ = _ := by
        rw [Real.rpow_sub hlogpos, Real.rpow_ofNat]
        ring
  refine hmain.trans (add_le_add (add_le_add hshort hlong) le_rfl |>.trans ?_)
  exact le_of_eq (by unfold panCellConstant; ring)


theorem numerical_high_source_depth_saving (B x : ℕ) (hx : GRH125.targetCutoff≤ x) (hBcap : B≤38)
    (m A₁ A₂ : ℕ) (f : ℕ → ℂ) (hAx : A₂ ≤ x)
    (hApower : (A₂ : ℝ) ≤ (x : ℝ)^(2/3 : ℝ))
    (hAlow : Real.log (x : ℝ)^((2 : ℝ)*B) ≤ A₁) (hf : ∀ n, ‖f n‖ ≤ 1) :
    panIymHigh (panSourceG f m) (panSourceD m) x A₁ A₂
      ⌊lowConductor x (B : ℝ)⌋₊ ⌊upperConductor x (B : ℝ)⌋₊ ≤
    (Nat.log 2 x + 1 : ℝ)^2 *
      (panCellConstant*x*Real.log x^(4-(B : ℝ)) + 776/(x : ℝ)) := by
  have hxlog := numerical_high_log_four hx
  have hC : 0 < panCellConstant := by
    unfold panCellConstant panShortConstant panLongConstant
    have := panSharpConstant_pos
    positivity
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hxlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hA₁ : 0 < A₁ := by
    have hp : (0 : ℝ) < Real.log x ^ ((2 : ℝ) * B) :=
      Real.rpow_pos_of_pos (by linarith only [hxlog]) _
    have : (0 : ℝ) < A₁ := hp.trans_le hAlow
    exact_mod_cast this
  let M := panCellConstant * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) + 776 / (x : ℝ)
  have hM : 0 ≤ M := by
    dsimp [M]
    have : 0 ≤ Real.log (x : ℝ) := by linarith
    positivity
  let s := (range (Nat.log 2 x + 1)).filter
    (fun j => conductorRadius x (B : ℝ) j ≤ upperConductor x (B : ℝ))
  have hs : s.card ≤ Nat.log 2 x + 1 :=
    (card_filter_le _ _).trans_eq (card_range _)
  calc
    _ ≤ ∑ j ∈ s, ∑ k ∈ range (panDyadicDepth A₁ A₂),
        sourceCell f m x A₁ A₂ k (conductorRadius x (B : ℝ) j) :=
      panIymHigh_le_sum_active_sourceCells f m x A₁ A₂ B hxlog1 hB hA₁
    _ ≤ ∑ j ∈ s, ∑ _k ∈ range (panDyadicDepth A₁ A₂), M := by
      apply sum_le_sum
      intro j hj
      apply sum_le_sum
      intro k hk
      exact numerical_source_cell_log_saving B x hx hBcap j m A₁ A₂ k f hAx
        (mem_filter.mp hj).2 hApower hAlow hf
    _ = (s.card : ℝ) * (panDyadicDepth A₁ A₂ : ℝ) * M := by simp; ring
    _ ≤ (Nat.log 2 x + 1 : ℝ) * (Nat.log 2 x + 1 : ℝ) * M := by
      gcongr
      · exact_mod_cast hs
      · exact_mod_cast source_depth_le (A₁ := A₁) hAx
    _ = _ := by rw [pow_two]



theorem numerical_high_source_log_saving (B x : ℕ) (hx : GRH125.targetCutoff≤ x) (hBcap : B≤38)
    (m A₁ A₂ : ℕ) (f : ℕ → ℂ) (hAx : A₂ ≤ x)
    (hApower : (A₂ : ℝ) ≤ (x : ℝ)^(2/3 : ℝ))
    (hAlow : Real.log (x : ℝ)^((2 : ℝ)*B) ≤ A₁) (hf : ∀ n, ‖f n‖ ≤ 1) :
    panIymHigh (panSourceG f m) (panSourceD m) x A₁ A₂
      ⌊lowConductor x (B : ℝ)⌋₊ ⌊upperConductor x (B : ℝ)⌋₊ ≤
    panHighConstant*x*Real.log x^(6-(B : ℝ)) + 6984*Real.log x^2/(x : ℝ) := by
  have hxlog := numerical_high_log_four hx
  have hC : 0 < panCellConstant := by
    unfold panCellConstant panShortConstant panLongConstant
    have := panSharpConstant_pos
    positivity
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  calc
    _ ≤ (Nat.log 2 x + 1 : ℝ) ^ 2 *
        (panCellConstant * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) + 776 / (x : ℝ)) :=
      numerical_high_source_depth_saving B x hx hBcap m A₁ A₂ f hAx hApower hAlow hf
    _ ≤ (3 * Real.log x) ^ 2 *
        (panCellConstant * (x : ℝ) * Real.log x ^ (4 - (B : ℝ)) + 776 / (x : ℝ)) := by
      gcongr
      exact log_depth_le_three_log hxlog
    _ = _ := by
      rw [show (6 - (B : ℝ) : ℝ) = 2 + (4 - (B : ℝ)) by ring, Real.rpow_add hlogpos,
        Real.rpow_two]
      unfold panHighConstant
      ring


theorem numerical_pan_conductor_bounds (B N : ℕ) (hN : GRH125.targetCutoff≤ N) (hB : B≤38) :
    1 ≤ Real.log (N : ℝ) ∧ 1 ≤ ⌊lowConductor N (B : ℝ)⌋₊ ∧
      ⌊lowConductor N (B : ℝ)⌋₊ ≤ panModulusCutoff N (B : ℝ) ∧
      (panModulusCutoff N (B : ℝ) : ℝ) ≤ Real.sqrt N ∧
      panModulusCutoff N (B : ℝ) ≤ N := by
  have hl := numerical_high_log_four hN
  have hlog : 1 ≤ Real.log (N : ℝ) := by linarith only [hl]
  have hN9 := GRH125.target_nine_le hN
  have hbound := GRH125.log_power_at_target hN (k:=2*B) (by omega) (δ:=1/2) (by norm_num)
  have hd : 1 ≤ lowConductor N (B : ℝ) := lowConductor_ge_one hlog (Nat.cast_nonneg B)
  have hdp : 0 < lowConductor N (B : ℝ) := zero_lt_one.trans_le hd
  have hsq : lowConductor N (B : ℝ)*lowConductor N (B : ℝ) ≤ Real.sqrt N := by
    rw [lowConductor, Real.rpow_natCast, ← pow_two, ← pow_mul, Nat.mul_comm B 2,
      Real.sqrt_eq_rpow]
    exact hbound
  have horder : lowConductor N (B : ℝ) ≤ upperConductor N (B : ℝ) :=
    (le_div_iff₀ hdp).mpr hsq
  have hfloor : (panModulusCutoff N (B : ℝ) : ℝ) ≤ Real.sqrt N := by
    rw [panModulusCutoff_eq_upper]
    exact (Nat.floor_le (by unfold upperConductor; positivity)).trans
      (upperConductor_le_sqrt hlog (Nat.cast_nonneg B))
  refine ⟨hlog, Nat.le_floor (by simpa using hd), ?_, hfloor, ?_⟩
  · rw [panModulusCutoff_eq_upper]
    exact Nat.floor_mono horder
  · exact_mod_cast hfloor.trans (Real.sqrt_le_self_iff.mpr
      (Or.inr (by exact_mod_cast (show 1 ≤ N by omega))))

theorem numerical_pan_budget (U b N : ℕ) (hN : GRH125.targetCutoff≤ N) (hUb : U+b+1≤189)
    (K : ℝ) (hK : 0 ≤ K) (m A₂ Q : ℕ)
    (hm : 1 ≤ m) (hmN : (m : ℝ) ≤ Real.sqrt N)
    (hA : (A₂ : ℝ) ≤ (N : ℝ)^(2/3 : ℝ))
    (hQ : (Q : ℝ) ≤ Real.log (N : ℝ)^b) :
    (Q : ℝ)*((K*N/Real.log (N : ℝ)^(U+b+2))*(1+Real.log N)+
      (A₂ : ℝ)*(m.primeFactors.card : ℝ)) ≤
        (2*K+2)*N/Real.log (N : ℝ)^U := by
  have hN9 := GRH125.target_nine_le hN
  have hL : 1 ≤ Real.log (N : ℝ) := log_one_le_of_eight_le (by omega)
  have hlog := GRH125.log_power_at_target hN (k:=U+b+1) (by omega) (δ:=1/3) (by norm_num)
  have hlog' : Real.log (N : ℝ)^((U : ℝ)+(b : ℝ)+1) ≤ (N : ℝ)^(1/3 : ℝ) := by
    rw [show (U : ℝ)+(b : ℝ)+1 = ((U+b+1 : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_natCast]
    exact hlog
  have hmX : (m : ℝ) ≤ N := hmN.trans
    (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1 ≤ N by omega))))
  have hcard := PanLow.primeFactors_card_le_log_of_le (by omega : 0 < m) hmX
  have htwo : (Real.log 2)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀' (Real.log_pos (by norm_num))]
    linarith [Real.log_two_gt_d9]
  have hW : (m.primeFactors.card : ℝ) ≤ 2*Real.log (N : ℝ) :=
    hcard.trans (mul_le_mul_of_nonneg_right htwo (zero_le_one.trans hL))
  have hh := PanLow.low_budget_scalar
    (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega)) hL
    (Nat.cast_nonneg A₂) (Nat.cast_nonneg m.primeFactors.card) (Nat.cast_nonneg Q)
    hK (by norm_num : (0 : ℝ) ≤ 2) hA hW
    (show (Q : ℝ) ≤ Real.log (N : ℝ)^(b : ℝ) by simpa only [Real.rpow_natCast] using hQ) hlog'
  simpa only [show (U : ℝ)+(b : ℝ)+2 = ((U+b+2 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast] using hh


end ChenEffective.GRH125.High
end

/- Strong moving input, proved independently for log N >= 10000. -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LiuWeight AnalyticNumberTheory.LargeSieve
theorem pan_log_log_cap {L : ℝ} (hL : (263000:ℝ)≤ L) : log L≤ L/20000 := GRH125Budget.pan_log_log_cap hL

theorem pan_prime_moving {N : ℕ} (hN : targetCutoff≤ N) {b s : ℕ}
    (hb : b≤40) (hs : s≤72) (a : ℕ) (ha : 1≤ a)
    (haN : (a:ℝ)≤(N:ℝ)^(2/3:ℝ)) (q : ℕ) (hq2 : 2≤ q)
    (hq : (q:ℝ)≤ Real.log (N:ℝ)^b) (χ : PrimitiveCharacter q) (hχ : χ.1≠1) :
    ‖PanLow.primePrefix χ.1 (N/a)‖≤((N:ℝ)/Real.log (N:ℝ)^s)/(a:ℝ) :=
  GRHStrongMoving.pan_prime_moving (by linarith only [target_log_lower hN]) hb hs a ha haN q hq2 hq χ hχ

theorem pan_principal_moving {N : ℕ} (hN : targetCutoff≤ N) {s : ℕ}
    (hs : s≤70) (a : ℕ) (ha : 1≤ a) (haN : (a:ℝ)≤(N:ℝ)^(2/3:ℝ)) :
    |PanPrincipal.primeCount (N/a)-liuLogarithmicIntegral (2/Real.log 2) ((N:ℝ)/a)|≤
      ((N:ℝ)/Real.log (N:ℝ)^s)/(a:ℝ) :=
  GRHStrongMoving.pan_principal_moving (by linarith only [target_log_lower hN]) hs a ha haN
end ChenEffective.GRH125
end

/- Component: GRH125PanEndpoints -/
noncomputable section
namespace ChenEffective.GRH125
open Real Complex Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem pan_log_cutoff_at_target {k N : ℕ} (hk : k≤121) (hN : targetCutoff≤ N) :
    logPowerCutoff k≤ N := by
  apply le_trans _ hN
  rw [targetCutoff_eq]
  unfold logPowerCutoff
  apply Nat.pow_le_pow_right (by norm_num)
  have hh := Nat.pow_le_pow_left (by omega : k+1≤122) 2
  nlinarith only [hh]

theorem pan_low_at_target (U b N : ℕ) (hN : targetCutoff≤ N)
    (hU : U≤32) (hb : b≤38)
    (m A₁ A₂ Q : ℕ) (g : ℕ→ℂ) (hm : 1≤ m) (hmN : (m:ℝ)≤ Real.sqrt N)
    (hA : (A₂:ℝ)≤(N:ℝ)^(2/3:ℝ)) (hQ : (Q:ℝ)≤ Real.log (N:ℝ)^b)
    (hg : ∀ a∈Ioc A₁ A₂, ‖g a‖≤1) :
    PanLow.nonprincipalLow g (fun n => if n.Prime ∧ n.Coprime m then 1 else 0)
      N A₁ A₂ Q≤4*N/Real.log (N:ℝ)^U :=
  GRHStrongMoving.pan_low_of_log U b N (by linarith only [target_log_lower hN]) hU hb m A₁ A₂ Q g hm hmN hA hQ hg

theorem pan_principal_at_target (s N : ℕ) (hN : targetCutoff≤ N) (hs : s≤32)
    (q A₁ A₂ : ℕ) (hq : 1≤ q) (hqN : (q:ℝ)≤ Real.sqrt N)
    (hA : (A₂:ℝ)≤(N:ℝ)^(2/3:ℝ)) :
    |PanPrincipal.principalError N A₁ A₂ q|≤4*N/Real.log (N:ℝ)^s :=
  GRHStrongMoving.pan_principal_of_log s N (by linarith only [target_log_lower hN]) hs q A₁ A₂ hq hqN hA

theorem pan_actual_paid_principal (s N : ℕ) (hN : targetCutoff≤ N) (hs : s≤32)
    (B : ℝ) (q : ℕ) (hq : 1≤ q) (hqN : (q:ℝ)≤ Real.sqrt N) :
    liuPanActualError (2/Real.log 2) N B q ≤
      (liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N B)
        (liuPanSourceIntervalUpper N) q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))+
        4*N/Real.log (N:ℝ)^s)/q.totient := by
  have hp := pan_principal_at_target s N hN hs q
    (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) hq hqN
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  rw [principalError_eq_liuPanActualPrincipalRaw] at hp
  exact (liuWeight_intervalMaxL_le_nonprincipal_add_principal (2/Real.log 2)
    N (liuSourceZ10 N) (liuSourceY3 N) _ _ q hq).trans
      (div_le_div_of_nonneg_right (add_le_add le_rfl hp) (Nat.cast_nonneg _))

#print axioms pan_low_at_target
#print axioms pan_principal_at_target
end ChenEffective.GRH125
end

/- Component: GRH125PanLedger -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def panLedgerConstant (_U : ℕ) : ℝ := 4+panHighConstant+6984
def panPrincipalConstant (_s : ℕ) : ℝ := 4
theorem panLedgerConstant_pos (U : ℕ) : 0<panLedgerConstant U := by
  unfold panLedgerConstant panHighConstant panCellConstant panShortConstant panLongConstant
  have := panSharpConstant_pos
  positivity
theorem panPrincipalConstant_pos (s : ℕ) : 0<panPrincipalConstant s := by norm_num [panPrincipalConstant]
theorem numerical_pan_ledger (U N : ℕ) (hN : targetCutoff ≤ N) (hU : U≤32)
    (m : ℕ) (hm : m ∈ Icc 1 (panModulusCutoff N ((U+6 : ℕ) : ℝ))) :
    liuPanPrimitiveCofactorLedger N (liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ))
      (liuPanSourceIntervalUpper N) (panModulusCutoff N ((U+6 : ℕ) : ℝ)) m
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
        panLedgerConstant U*N/Real.log (N : ℝ)^U := by
  have hNR : logPowerCutoff (U+2)≤ N := pan_log_cutoff_at_target (by omega) hN
  obtain ⟨hlog, hD1, hD, hDN, hcut⟩ := High.numerical_pan_conductor_bounds (U+6) N hN (by omega)
  have hN9 := (logPowerCutoff_nine_le _).trans hNR
  obtain ⟨hmpos, hmcutoff⟩ := mem_Icc.mp hm
  have hmN : (m : ℝ) ≤ Real.sqrt N :=
    (show (m : ℝ) ≤ panModulusCutoff N ((U+6 : ℕ) : ℝ) by exact_mod_cast hmcutoff).trans hDN
  have hA : (liuPanSourceIntervalUpper N : ℝ) ≤ (N : ℝ)^(2/3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hAN : liuPanSourceIntervalUpper N ≤ N := by
    exact_mod_cast hA.trans (Real.rpow_le_self_of_one_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num))
  have hf : ∀ a, ‖(liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)‖ ≤ 1 := by
    intro a
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_liuWeight] using
      liuWeight_le_one N (liuSourceZ10 N) (liuSourceY3 N) a
  have hlow := pan_low_at_target U (U+6) N hN hU (by omega) m
    (liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ)) (liuPanSourceIntervalUpper N)
    ⌊lowConductor N ((U+6 : ℕ) : ℝ)⌋₊
    (panSourceG (fun a => (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)) m)
    hmpos hmN hA (by
      have hl0 : 0 ≤ Real.log (N : ℝ) := by linarith only [hlog]
      simpa only [lowConductor, Real.rpow_natCast] using
        (Nat.floor_le (Real.rpow_nonneg hl0 ((U+6 : ℕ) : ℝ)))) (by
      intro a _
      unfold panSourceG
      split_ifs
      · exact hf a
      · simp)
  have hhigh := High.numerical_high_source_log_saving (U+6) N hN (by omega) m
    (liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ)) (liuPanSourceIntervalUpper N)
    (fun a => (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)) hAN hA
    (log_rpow_lt_liuPanSourceIntervalLower N ((U+6 : ℕ) : ℝ)).le hf
  have he : 6-((U+6 : ℕ) : ℝ) = -(U : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg (show 0 ≤ Real.log (N : ℝ) by linarith only [hlog]),
    Real.rpow_natCast, ← div_eq_mul_inv] at hhigh
  have hDfun : panSourceD m = (fun n => if n.Prime ∧ n.Coprime m then (1 : ℂ) else 0) := by
    funext n
    simp only [panSourceD, and_comm]
  rw [liuPanPrimitiveCofactorLedger_eq_source,
    PanLow.nonprincipalLow_eq_low_add_high _ _ _ _ _ _ _ hD1 hD,
    panModulusCutoff_eq_upper]
  rw [← hDfun] at hlow
  have hr := H30.numerical_pan_high_remainder U N hNR
  calc
    _ ≤ 4*N/Real.log (N : ℝ)^U +
        (panHighConstant*N/Real.log (N : ℝ)^U + 6984*Real.log (N : ℝ)^2/N) :=
      add_le_add hlow hhigh
    _ ≤ 4*N/Real.log (N : ℝ)^U +
        (panHighConstant*N/Real.log (N : ℝ)^U + 6984*N/Real.log (N : ℝ)^U) := by
      exact add_le_add le_rfl (add_le_add le_rfl hr)
    _ = _ := by unfold panLedgerConstant; ring


#print axioms numerical_pan_ledger
end ChenEffective.GRH125
end

/- Component: GRH125PanUnweighted -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
def panUnweightedConstant (A : ℕ) : ℝ := 4*(panLedgerConstant (A+2)+panPrincipalConstant (A+2))
theorem panUnweightedConstant_pos (A : ℕ) : 0 < panUnweightedConstant A := by
  unfold panUnweightedConstant
  have := panLedgerConstant_pos (A+2)
  have := panPrincipalConstant_pos (A+2)
  positivity

theorem numerical_pan_unweighted (A N : ℕ) (hN : targetCutoff ≤ N) (hA : A≤30) :
    liuPanUnweightedTheorem2Sum (2/Real.log 2) N ((A+8 : ℕ) : ℝ) ≤
      panUnweightedConstant A*N/Real.log (N : ℝ)^(A : ℝ) := by
  have hNk := hN
  have hNp := hN
  obtain ⟨hlog, _, _, hDroot, hDN⟩ := High.numerical_pan_conductor_bounds (A+8) N hN (by omega)
  let K := panLedgerConstant (A+2)
  let P := panPrincipalConstant (A+2)
  have hK : 0 < K := panLedgerConstant_pos _
  have hP : 0 < P := panPrincipalConstant_pos _
  have hpaid := pan_actual_paid_principal (A+2) N hNp (by omega)
  let D := panModulusCutoff N ((A+8 : ℕ) : ℝ)
  let M := K * N / Real.log (N : ℝ) ^ (((A+2 : ℕ) : ℝ))
  let T := P * N / Real.log (N : ℝ) ^ (((A+2 : ℕ) : ℝ))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hmass := liuPanActualNonprincipal_sum_le_log_sq N (liuPanSourceIntervalLower N ((A+8 : ℕ) : ℝ))
    (liuPanSourceIntervalUpper N) D (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
    M hM hDN (by
      simpa only [M, K, D, Real.rpow_natCast, Nat.add_assoc, Nat.reduceAdd] using
        numerical_pan_ledger (A+2) N hNk (by omega))
  have hprincipal : T * ∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ ≤
      T * (1 + Real.log (N : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_left (PanCofactor.reciprocal_totient_mass_le_log_sq hDN) hT
  calc
    _ ≤ ∑ q ∈ Icc 1 D, liuPanActualError (2 / Real.log 2) N ((A+8 : ℕ) : ℝ) q :=
      liuPanUnweightedTheorem2Sum_le_closed _ _ _
    _ ≤ ∑ q ∈ Icc 1 D,
        (liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N ((A+8 : ℕ) : ℝ))
          (liuPanSourceIntervalUpper N) q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) + T) /
            q.totient := by
      apply sum_le_sum
      intro q hq
      simpa only [T, P, panPrincipalConstant, Real.rpow_natCast] using hpaid ((A+8 : ℕ) : ℝ) q (mem_Icc.mp hq).1
        ((by exact_mod_cast (mem_Icc.mp hq).2 : (q : ℝ) ≤ D).trans hDroot)
    _ = (∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ *
        liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N ((A+8 : ℕ) : ℝ))
          (liuPanSourceIntervalUpper N) q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) +
        T * ∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ := by
      simp only [add_div, sum_add_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ M * (1 + Real.log (N : ℝ)) ^ 2 + T * (1 + Real.log (N : ℝ)) ^ 2 :=
      add_le_add hmass hprincipal
    _ = ((K + P) * N / Real.log (N : ℝ) ^ (((A+2 : ℕ) : ℝ))) * (1 + Real.log (N : ℝ)) ^ 2 := by
      dsimp [M, T]
      ring
    _ ≤ _ := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, panUnweightedConstant] using
        pan_log_sq_payment N (A : ℝ) (K + P) (by positivity) hlog


#print axioms numerical_pan_unweighted
end ChenEffective.GRH125
end

/- Component: GRH125PanWeighted -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
def panWeightedSaving (A : ℕ) : ℕ := 2*A+20
def panWeightedCutoff (A : ℕ) : ℕ := panWeightedSaving A+8
def panWeightedSquareConstant (A : ℕ) : ℝ :=
  2^20*H30.panActualEnvelopeConstant (2/Real.log 2)*panUnweightedConstant (panWeightedSaving A)
def panWeightedConstant (A : ℕ) : ℝ := Real.sqrt (panWeightedSquareConstant A)+1

theorem numerical_pan_weighted_square (κ : ℝ) (N : ℕ) (B : ℝ)
    (hN : 2 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) (hB : 0 ≤ B) :
    liuPanWangDingCorollary230Sum κ N B^2 ≤
      (1+Real.log (N : ℝ))^20 * (H30.panActualEnvelopeConstant κ*N*
        liuPanUnweightedTheorem2Sum κ N B) := by
  let S := liuPanSquarefreeCarrier N B
  let E := liuPanActualError κ N B
  let X := H30.panActualEnvelopeConstant κ*N*(1+Real.log (N : ℝ))^2
  have hX : 0 ≤ X := by dsimp [X]; positivity [H30.panActualEnvelopeConstant_pos κ]
  have hsq : ∀ q ∈ S, Squarefree q := fun q hq => (mem_filter.mp hq).2
  have hpos : ∀ q ∈ S, 0 < q := fun q hq => Nat.pos_of_ne_zero (hsq q hq).ne_zero
  have hE : ∀ q ∈ S, 0 ≤ E q := fun q _ => liuPanActualError_nonneg κ N B q
  have hSN : S ⊆ Icc 1 N := by
    intro q hq
    exact mem_Icc.mpr ⟨hpos q hq,
      panSourceStrictModulusCutoff_mem_le (by omega) hlog hB (mem_filter.mp hq).1⟩
  have hc := numerical_totient_cauchy S
    (fun q => (3 : ℝ)^q.primeFactors.card) E X hpos hE (by
      intro q hq
      exact H30.numerical_pan_envelope κ N _ _ q hN
        (hpos q hq) (mem_Icc.mp (hSN hq)).2)
  have hm : (∑ q ∈ S, ((3 : ℝ)^q.primeFactors.card)^2/q.totient) ≤
      (1+Real.log (N : ℝ))^18 := by
    calc
      _ = ∑ q ∈ S, (9 : ℝ)^q.primeFactors.card/q.totient := by
        apply sum_congr rfl
        intro q _
        rw [pow_two, ← mul_pow]
        norm_num
      _ ≤ _ := numerical_totient_nine_mass (by omega) S hSN hsq
  have ho : (∑ q ∈ S, E q) ≤ liuPanUnweightedTheorem2Sum κ N B :=
    liuPanSquarefreeErrorSum_le_unweighted κ N B
  rw [liuPanWeightedSum_eq_squarefree]
  calc
    _ ≤ (∑ q ∈ S, ((3 : ℝ)^q.primeFactors.card)^2/q.totient)*(X*∑ q ∈ S, E q) := hc
    _ ≤ (1+Real.log (N : ℝ))^18*(X*liuPanUnweightedTheorem2Sum κ N B) :=
      mul_le_mul hm (mul_le_mul_of_nonneg_left ho hX)
        (mul_nonneg hX (sum_nonneg hE)) (by positivity)
    _ = _ := by dsimp [X]; ring

theorem numerical_pan_weighted (A N : ℕ) (hN : targetCutoff ≤ N) (hA : A≤5) :
    liuPanWangDingCorollary230Sum (2/Real.log 2) N (panWeightedCutoff A : ℝ) ≤
      panWeightedConstant A*N/Real.log (N : ℝ)^A := by
  have hlog : 1≤ Real.log (N:ℝ) := by have := target_log_lower hN; linarith
  have hN2 : 2≤ N := by
    have := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
    omega
  have hl0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hK := panUnweightedConstant_pos (panWeightedSaving A)
  have hsrc := numerical_pan_unweighted (panWeightedSaving A) N
    hN (by unfold panWeightedSaving; omega)
  rw [Real.rpow_natCast] at hsrc
  have hs := numerical_pan_weighted_square (2/Real.log 2) N (panWeightedCutoff A : ℝ)
    hN2 hlog (Nat.cast_nonneg _)
  have henv := H30.panActualEnvelopeConstant_pos (2/Real.log 2)
  have hD : 0 ≤ panWeightedSquareConstant A := by unfold panWeightedSquareConstant; positivity
  have hmajor : liuPanWangDingCorollary230Sum (2/Real.log 2) N (panWeightedCutoff A : ℝ)^2 ≤
      panWeightedSquareConstant A*((N : ℝ)/Real.log (N : ℝ)^A)^2 := by
    calc
      _ ≤ (1+Real.log (N : ℝ))^20*(H30.panActualEnvelopeConstant (2/Real.log 2)*N*
          (panUnweightedConstant (panWeightedSaving A)*N/Real.log (N : ℝ)^(panWeightedSaving A))) :=
        hs.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsrc (by positivity)) (by positivity))
      _ ≤ (2*Real.log (N : ℝ))^20*(H30.panActualEnvelopeConstant (2/Real.log 2)*N*
          (panUnweightedConstant (panWeightedSaving A)*N/Real.log (N : ℝ)^(panWeightedSaving A))) := by
        gcongr
        linarith only [hlog]
      _ = _ := by
        unfold panWeightedSaving panWeightedSquareConstant
        rw [pow_add, pow_mul]
        field_simp [hl0.ne']
        simp only [panWeightedSaving, Nat.mul_comm]
        ring
  have hleft : 0 ≤ liuPanWangDingCorollary230Sum (2/Real.log 2) N (panWeightedCutoff A : ℝ) := by
    unfold liuPanWangDingCorollary230Sum
    exact sum_nonneg fun q _ => mul_nonneg (by positivity) (liuMainPanCoprimeIntervalMaxL_nonneg ..)
  have ht : 0 ≤ panWeightedConstant A*N/Real.log (N : ℝ)^A := by unfold panWeightedConstant; positivity
  have hDs : panWeightedSquareConstant A ≤ panWeightedConstant A^2 := by
    unfold panWeightedConstant
    nlinarith only [Real.sq_sqrt hD, Real.sqrt_nonneg (panWeightedSquareConstant A)]
  apply (sq_le_sq₀ hleft ht).mp
  exact hmajor.trans ((mul_le_mul_of_nonneg_right hDs (sq_nonneg _)).trans_eq (by ring))


#print axioms numerical_pan_weighted
end ChenEffective.GRH125
end

/- Component: GRH125PanSource -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LiuWeight
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem pan_log_power_at_target {N : ℕ} (hN : targetCutoff≤ N) {k : ℕ}
    (hk : k≤39) {δ : ℝ} (hδ : (1/500:ℝ)≤δ) :
    log (N:ℝ)^k≤(N:ℝ)^δ := by
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hn : 0<N := by
    by_contra h
    have hh : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hkR : (k:ℝ)≤39 := by exact_mod_cast hk
  have hh := mul_le_mul_of_nonneg_left (pan_log_log_cap hL) (Nat.cast_nonneg k)
  have hm := mul_le_mul_of_nonneg_right hkR (show 0≤ log (N:ℝ)/20000 by positivity)
  have hd := mul_le_mul_of_nonneg_right hδ hl.le
  rw [Real.rpow_def_of_pos hnR]
  calc
    _ = exp ((k:ℝ)*log (log (N:ℝ))) := by rw [exp_nat_mul (log (log (N:ℝ))) k,exp_log hl]
    _ ≤ _ := exp_le_exp.mpr (by nlinarith only [hh,hm,hd,hl])

theorem pan_source_support_at_target {N : ℕ} (hN : targetCutoff≤ N) :
    liuPanSourceIntervalLower N (38:ℝ)<liuSourceZ10 N := by
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hp := log_power_at_target hN (k:=76) (by norm_num) (δ:=(1/20:ℝ)) (by norm_num)
  have hlarge : 2^20≤ N := by
    have hh := pan_log_cutoff_at_target (k:=1) (by norm_num) hN
    have hc : 2^20≤ logPowerCutoff 1 := by norm_num [logPowerCutoff]
    exact hc.trans hh
  have htwo : (2:ℝ)≤(N:ℝ)^(1/20:ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num : (0:ℝ)≤2) hn.le (by norm_num : (0:ℝ)<20)).mpr
    norm_num
    exact_mod_cast hlarge
  have hs : ((N:ℝ)^(1/20:ℝ))^2=(N:ℝ)^(1/10:ℝ) := by
    rw [← rpow_natCast,← rpow_mul hn.le]
    norm_num
  have hb : log (N:ℝ)^76+2≤(N:ℝ)^(1/10:ℝ) := by nlinarith only [hp,htwo,hs]
  have hh := Nat.floor_mono hb
  have hL := target_log_lower hN
  have hl : 0≤ log (N:ℝ) := by linarith only [hL]
  have hadd : ⌊log (N:ℝ)^76+2⌋₊=⌊log (N:ℝ)^76⌋₊+2 := by
    convert Nat.floor_add_natCast (pow_nonneg hl 76) 2 using 1 <;> norm_num
  rw [hadd] at hh
  unfold liuPanSourceIntervalLower liuSourceZ10
  norm_num only [rpow_ofNat]
  omega

theorem pan_source_level_at_target {N : ℕ} (hN : targetCutoff≤ N) :
    liuSourceDEpsilon N (1/500:ℝ)≤ panModulusCutoff N (39:ℝ) := by
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hp := pan_log_power_at_target hN (k:=39) (by norm_num) (δ:=(1/500:ℝ)) (by norm_num)
  unfold liuSourceDEpsilon panModulusCutoff
  apply Nat.floor_mono
  rw [rpow_sub hn]
  norm_num only [rpow_ofNat]
  exact div_le_div_of_nonneg_left (rpow_nonneg hn.le _) (pow_pos hl 39) hp

theorem pan_source_at_target {N : ℕ} (hN : targetCutoff≤ N) :
    LiuPaperQCoprimeRBound (liuLogarithmicIntegral (2/log 2)) N (1/500:ℝ)
      (5:ℝ) (panWeightedConstant 5) := by
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hL := target_log_lower hN
  have hlog : 1<log (N:ℝ) := by linarith only [hL]
  have hb := numerical_pan_weighted 5 N hN (by norm_num)
  have hc := pan_source_level_at_target hN
  apply liuPaperQCoprimeRBound_of_liuMainPanEndpointMeanValueAt
    (liuLogarithmicIntegral (2/log 2)) N (1/500:ℝ) (5:ℝ) (39:ℝ)
    (panWeightedConstant 5) hc
  have hh := H30.liuMainPanEndpointWeightedSum_le_corollary230Sum (2/log 2) N
    (38:ℝ) (fun _ _ => liuMainPanCoprimeSum_eq_panSourceInterval _ (by omega)
      (pan_source_support_at_target hN))
    (range_panModulusCutoff_add_one_subset_sourceStrict N (38:ℝ) (by omega) hlog)
  norm_num only [panWeightedCutoff,panWeightedSaving,Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at hb
  unfold LiuMainPanEndpointMeanValueAt
  convert hh.trans hb using 1 <;> norm_num only [rpow_ofNat]

#print axioms pan_source_at_target
end ChenEffective.GRH125
end

/- Component: GRH125PanCanonical -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def panDivisorConstant : ℝ := H30.panDivisorConstant
def panNormalizationConstant : ℝ := H30.panNormalizationConstant
def panCanonicalConstant (A : ℕ) : ℝ := panWeightedConstant A+panNormalizationConstant
theorem numerical_pan_full_divisor {N w : ℕ} (hN : mertensProductThreshold 2 ≤ N)
    (hw : w ≤ N) :
    paperQStyleFullDivisorWeightSum N w ≤ panDivisorConstant*Real.log (N : ℝ)^3 := by
  have hprod := numerical_mertens_product (by norm_num : 0 < (2 : ℕ)) hN
  have hNP := (le_max_left _ _).trans hN
  have hN9 := (logPowerCutoff_nine_le _).trans hNP
  have hl0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hP := AnalyticNumberTheory.Mertens.primeProduct_pos N
  have hlow := (abs_le.mp hprod).1
  have hi : (AnalyticNumberTheory.Mertens.primeProduct N)⁻¹ ≤
      2*Real.exp Real.eulerMascheroniConstant*Real.log (N : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hP).mpr
    norm_num only [Nat.cast_ofNat] at hlow
    nlinarith only [hlow]
  have hh := paperQStyleFullDivisorWeightSum_le_primeProduct_inv_cube N w hw
  rw [MertensTheorem.primeProduct_eq_analyticNumberTheory] at hh
  exact hh.trans ((pow_le_pow_left₀ (by positivity) hi 3).trans_eq
    (by unfold panDivisorConstant H30.panDivisorConstant; ring))


theorem numerical_pan_canonical {N : ℕ} (hN : targetCutoff≤ N) :
    LiuPaperQCoprimeRBound (liuLogarithmicIntegral 2) N (1/500:ℝ)
      (5:ℝ) (panCanonicalConstant 5) := by
  have hm : 0<(500:ℕ) := by norm_num

  have hNM : mertensProductThreshold 2≤ N := by
    unfold mertensProductThreshold
    apply max_le (pan_log_cutoff_at_target (k:=2) (by norm_num) hN)
    exact (by
      unfold logPowerCutoff
      apply Nat.pow_le_pow_right (by norm_num)
      have hh := Nat.sqrt_le_self (6*2)
      omega : 3^(Nat.sqrt (6*2)+2)≤ logPowerCutoff 0).trans
      (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hNP : logPowerCutoff 24≤ N := pan_log_cutoff_at_target (by norm_num) hN
  have hN9 := (logPowerCutoff_nine_le _).trans hNP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hε : 0 ≤ 1/(500 : ℝ) := by positivity
  have hmass := sum_liuWeight_Icc_le_three_mul_rpow_two_thirds N
    (liuSourceZ10 N) (liuSourceY3 N) (by omega)
  have hcut := (paperQSourceCutoff_le_floor_cuberoot N (1/(500 : ℝ)) (by omega) hε).trans
    (liuSourceY3_le N (by omega))
  have hdiv := numerical_pan_full_divisor hNM hcut
  have hmass0 : 0 ≤ ∑ a ∈ Icc 1 N, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a := by
    apply sum_nonneg
    intro a _
    exact liuWeight_nonneg _ _ _ _
  have hfactor : 0 ≤ paperQStyleFullDivisorWeightSum N (paperQSourceCutoff N (1/(500 : ℝ))) := by
    unfold paperQStyleFullDivisorWeightSum
    positivity
  have hnorm := liuPaperQSourceCoprimeDistributionMajorant_li_normalization_le
    2 (2/Real.log 2) N (1/(500 : ℝ))
  have hloss : |2-2/Real.log 2| *
      (∑ a ∈ Icc 1 N, liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a)*
      paperQStyleFullDivisorWeightSum N (paperQSourceCutoff N (1/(500 : ℝ))) ≤
        panNormalizationConstant*N/Real.log (N : ℝ)^5 := by
    have hp := log_pow_le_rpow_inv_explicit (k := 5+3) (m := 3)
      (by norm_num) (le_refl _) hNP
    norm_num only [Nat.cast_ofNat] at hp
    have hscale : (N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^3 ≤ N/Real.log (N : ℝ)^5 := by
      apply (le_div_iff₀ (pow_pos hlog 5)).mpr
      calc
        _ = (N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^(5+3) := by rw [pow_add]; ring
        _ ≤ (N : ℝ)^(2/3 : ℝ)*(N : ℝ)^(1/3 : ℝ) := by gcongr
        _ = _ := by rw [← Real.rpow_add hN0]; norm_num
    calc
      _ ≤ |2-2/Real.log 2| *(3*(N : ℝ)^(2/3 : ℝ))*(panDivisorConstant*Real.log (N : ℝ)^3) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmass (abs_nonneg _)) hdiv hfactor
          (by positivity)
      _ = panNormalizationConstant*((N : ℝ)^(2/3 : ℝ)*Real.log (N : ℝ)^3) := by
        unfold panNormalizationConstant H30.panNormalizationConstant panDivisorConstant; ring
      _ ≤ panNormalizationConstant*(N/Real.log (N : ℝ)^5) := by
        apply mul_le_mul_of_nonneg_left hscale
        unfold panNormalizationConstant H30.panNormalizationConstant H30.panDivisorConstant
        positivity
      _ = _ := by ring
  unfold LiuPaperQCoprimeRBound
  norm_num only [Real.rpow_natCast,Real.rpow_ofNat]
  have hsource := pan_source_at_target hN
  unfold LiuPaperQCoprimeRBound at hsource
  norm_num only [Real.rpow_natCast,Real.rpow_ofNat] at hsource
  exact hnorm.trans ((add_le_add hsource hloss).trans_eq (by unfold panCanonicalConstant; ring))


#print axioms numerical_pan_canonical
end ChenEffective.GRH125
end

/- Component: GRH125SelbergRemainder -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LiuWeight
open AnalyticNumberTheory.LargeSieve
open NumericalPanHigh AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def selbergRemainderConstant (A : ℕ) : ℝ :=
  panCanonicalConstant A+1920*liuLogarithmicIntegralUpperConstant 2

theorem numerical_selberg_remainder {N : ℕ} (hN : targetCutoff≤ N) (lam : ℕ→ℝ)
    (hlam : LiuSelbergLambdaAdmissible N (1/500:ℝ) lam) :
    |liuSelbergRemainder (liuLogarithmicIntegral 2) N (1/500:ℝ) lam| ≤
      selbergRemainderConstant 5*N/Real.log (N:ℝ)^5 := by

  have hNP : logPowerCutoff 110≤ N := pan_log_cutoff_at_target (by norm_num) hN
  have hN9 := (logPowerCutoff_nine_le _).trans hNP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL := log_one_le_of_eight_le (by omega : 8 ≤ N)
  have hl0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL
  have hε : 0 ≤ 1/(500 : ℝ) := by positivity
  have hcop := numerical_pan_canonical hN
  unfold LiuPaperQCoprimeRBound at hcop
  norm_num only [Real.rpow_natCast,Real.rpow_ofNat] at hcop
  have hp := log_pow_le_rpow_inv_explicit (k := 5+6) (m := 10)
    (by norm_num) (le_refl _) hNP
  norm_num only [Nat.cast_ofNat] at hp
  have hscale : (N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^6 ≤ N/Real.log (N : ℝ)^5 := by
    apply (le_div_iff₀ (pow_pos hl0 5)).mpr
    calc
      _ = (N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^(5+6) := by rw [pow_add]; ring
      _ ≤ (N : ℝ)^(9/10 : ℝ)*(N : ℝ)^(1/10 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hN0]; norm_num
  have hr := H30.numerical_pan_r1 2 N (1/(500 : ℝ)) hN9 hε
  have hpaid : liuPaperQSourceR1Majorant (liuLogarithmicIntegral 2) N (1/(500 : ℝ)) ≤
      1920*liuLogarithmicIntegralUpperConstant 2*N/Real.log (N : ℝ)^5 := by
    have hC := liuLogarithmicIntegralUpperConstant_nonneg 2
    calc
      _ ≤ 30*liuLogarithmicIntegralUpperConstant 2*(N : ℝ)^(9/10 : ℝ)*
          (1+Real.log (N : ℝ))^6 := hr
      _ ≤ 30*liuLogarithmicIntegralUpperConstant 2*(N : ℝ)^(9/10 : ℝ)*
          (2*Real.log (N : ℝ))^6 := by
        gcongr
        linarith only [hL]
      _ = (1920*liuLogarithmicIntegralUpperConstant 2)*
          ((N : ℝ)^(9/10 : ℝ)*Real.log (N : ℝ)^6) := by ring
      _ ≤ (1920*liuLogarithmicIntegralUpperConstant 2)*(N/Real.log (N : ℝ)^5) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by ring
  exact (abs_liuSelbergRemainder_le_fullDistributionMajorant _ N _ lam (by omega) hlam).trans
    ((liuPaperQSourceFullDistributionMajorant_le_coprime_add_r1 _ N _ (by omega) hε).trans
      ((add_le_add hcop hpaid).trans_eq (by unfold selbergRemainderConstant; ring)))


#print axioms numerical_selberg_remainder
end ChenEffective.GRH125
end

/- Component: GRH125TripleConstants -/
noncomputable section
namespace ChenEffective.GRH125
open Real
open MathlibNt.SieveTheory LiuWeight
open NumericalPanHigh
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem selberg_remainder_constant_cap : selbergRemainderConstant 5≤(1e12:ℝ) := by
  have hlog : 0<log (2:ℝ) := log_pos (by norm_num)
  have hq : (2:ℝ)/log 2≤4 := (div_le_iff₀ hlog).mpr (by linarith only [log_two_gt_d9])
  have hs : panSharpConstant≤32 := by unfold panSharpConstant; linarith only [pi_lt_four]
  have hshort : panShortConstant≤512 := by unfold panShortConstant; linarith only [hs]
  have hlong : panLongConstant≤2560 := by
    unfold panLongConstant
    calc
      _ ≤ (16:ℝ)*32*(1+4) := by gcongr
      _ = _ := by norm_num
  have he : exp (2:ℝ)≤9 := by
    rw [show (2:ℝ)=1+1 by norm_num,exp_add]
    nlinarith only [exp_one_lt_d9,exp_pos (1:ℝ)]
  have hlong0 : 0≤ panLongConstant := by
    unfold panLongConstant
    have := panSharpConstant_pos
    positivity
  have hhigh : panHighConstant≤(1e9:ℝ) := by
    unfold panHighConstant panCellConstant
    calc
      _ ≤ (9:ℝ)*(36*512+36*9*2560) := by gcongr
      _ ≤ _ := by norm_num
  have hU : panUnweightedConstant 30≤(1e10:ℝ) := by
    unfold panUnweightedConstant panLedgerConstant panPrincipalConstant
    linarith only [hhigh]
  have hU0 := (panUnweightedConstant_pos 30).le
  have henv0 := (H30.panActualEnvelopeConstant_pos (2/log 2)).le
  have hLi : liuLogarithmicIntegralUpperConstant (2/log 2)≤10 := by
    unfold liuLogarithmicIntegralUpperConstant
    rw [abs_of_nonneg (by positivity : (0:ℝ)≤2/log 2)]
    linarith only [hq]
  have henv : H30.panActualEnvelopeConstant (2/log 2)≤26 := by
    unfold H30.panActualEnvelopeConstant liuPanLiEnvelopeConstant
    have hh : liuLogarithmicIntegralUpperConstant (2/log 2)/log 2≤20 :=
      (div_le_iff₀ hlog).mpr (by linarith only [hLi,log_two_gt_d9])
    linarith only [hh]
  have hD : panWeightedSquareConstant 5≤(1e10:ℝ)^2 := by
    unfold panWeightedSquareConstant
    norm_num only [panWeightedSaving,Nat.reduceMul,Nat.reduceAdd]
    calc
      _ ≤ (2:ℝ)^20*26*1e10 := by
        gcongr <;> norm_num
      _ ≤ _ := by norm_num
  have hW : panWeightedConstant 5≤(1e10:ℝ)+1 := by
    unfold panWeightedConstant
    have hh := Real.sqrt_le_iff.mpr ⟨(by norm_num : (0:ℝ)≤1e10),hD⟩
    linarith only [hh]
  have hgamma : exp eulerMascheroniConstant≤3 := by
    have hh : exp eulerMascheroniConstant≤ exp 1 :=
      exp_le_exp.mpr (by linarith only [eulerMascheroniConstant_lt_two_thirds])
    exact hh.trans (by linarith only [exp_one_lt_d9])
  have hdiv : H30.panDivisorConstant≤216 := by
    unfold H30.panDivisorConstant
    calc
      _ ≤ ((2:ℝ)*3)^3 := by gcongr
      _ = _ := by norm_num
  have hdelta : |(2:ℝ)-2/log 2|≤2 := by
    rw [abs_le]
    constructor <;> linarith only [hq,div_nonneg (by norm_num : (0:ℝ)≤2) hlog.le]
  have hnorm : panNormalizationConstant≤1296 := by
    unfold panNormalizationConstant H30.panNormalizationConstant
    calc
      _ ≤ (3:ℝ)*216*2 := by gcongr
      _ = _ := by norm_num
  have hLi2 : liuLogarithmicIntegralUpperConstant 2≤8 := by
    norm_num only [liuLogarithmicIntegralUpperConstant,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [hq]
  unfold selbergRemainderConstant panCanonicalConstant
  linarith only [hW,hnorm,hLi2]

theorem selberg_remainder_paid {N : ℕ} (hN : targetCutoff≤ N) :
    selbergRemainderConstant 5*N/log (N:ℝ)^5 ≤
      (1/1000:ℝ)*(SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hL := target_log_lower hN
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hs := half_le_liuSingularSeries N
  have hc : selbergRemainderConstant 5/log (N:ℝ)^3 ≤
      (1/1000:ℝ)*SingularSeries.liuSingularSeries N := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤263000) hL 3
    apply (div_le_iff₀ (pow_pos hl 3)).mpr
    have hh := mul_le_mul hs hp (by norm_num : (0:ℝ)≤263000^3)
      (SingularSeries.liuSingularSeries_pos N).le
    nlinarith only [hh,selberg_remainder_constant_cap]
  have hh := mul_le_mul_of_nonneg_right hc
    (show 0≤(N:ℝ)/log (N:ℝ)^2 by positivity)
  convert hh using 1 <;> field_simp [hl.ne']

#print axioms selberg_remainder_paid
end ChenEffective.GRH125
end

/- Component: GRH125ScalarBudget -/
/-! Conditional adapter for actual Chen counts at the H<14 target. The
analytic lower and complete triple inequalities remain explicit premises. -/
noncomputable section
open Real
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
namespace ChenEffective.GRH125
/-- These are bounds on actual counts, not numerical sieve axioms. -/
theorem representation_of_target_counts {N : ℕ} (hN : targetCutoff ≤ N)
    (hlower : (2.02575 : ℝ)*(SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2) ≤
      MathlibNt.SieveTheory.SwitchingPrinciple.jurkatRichertWeightedCount N)
    (htriple : MathlibNt.SieveTheory.SwitchingPrinciple.correctedChenTriplePenalty N ≤
      ((81/10 : ℝ)*(0.49254+1/10000)+1/1000)*
        (SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2)) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  have hN9 : 9 ≤ N := by
    have hE : 2 ≤ targetExponent := by rw [targetExponent_eq]; norm_num
    exact (show (9 : ℕ)=3^2 by norm_num).le.trans
      ((Nat.pow_le_pow_right (by norm_num : 1 ≤ (3 : ℕ)) hE).trans hN)
  have hM : 0 < SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2 := by
    exact div_pos (mul_pos (SingularSeries.liuSingularSeries_pos N)
      (by exact_mod_cast (show 0 < N by omega)))
      (pow_pos (log_pos (by exact_mod_cast (show 1 < N by omega))) 2)
  have hb := corrected_counting_bridge_public_of_nine_le hN9
  rw [correctedChenKeyCount_eq_jurkatRichertWeightedCount_sub_triple] at hb
  have hcard : 0 < (chenGoodRepresentations N).card := by
    exact_mod_cast (show (0:ℝ) < ((chenGoodRepresentations N).card:ℝ) by
      nlinarith only [hb,hlower,htriple,hM])
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations,Finset.mem_filter,Finset.mem_range] at hp
  exact ⟨p,N-p,hp.2.1,MathlibNt.ChensTheorem.semiprime_iff.mp
    ⟨hp.2.2.1,hp.2.2.2⟩,by omega⟩

#print axioms representation_of_target_counts
end ChenEffective.GRH125
end

/- Component: GRH125SelbergBudget -/
/-! The actual Selberg denominator at the H<14 target, uniformly in the
sieving radius parameter. These statements are unconditional. They remove
the restriction to the old fixed epsilon; they do not assert the complete
triple count, whose off-diagonal and prime-pair errors still need work. -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
theorem normalized_error {N R : ℕ} {ε : ℝ} (hε : ε ≤ 1/1000)
    (hN : 0<N) (hL : (263000:ℝ)≤ log (N:ℝ)) (hR : 1≤ R)
    (hlogR : (1/4-ε/2)*log (N:ℝ)-log 2≤ log (R:ℝ)) :
    ((20/sqrt R)*exp (1096+log (N:ℝ)/16))*liuSingularSeries N≤1 := by
  have hRp : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hroot : 1/sqrt (R:ℝ)=exp (-log (R:ℝ)/2) := by
    rw [sqrt_eq_rpow,rpow_def_of_pos hRp,one_div,← exp_neg]
    congr 1
    ring
  have hlog2 : log (2:ℝ)≤1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have he : 1096+log (N:ℝ)/16+(822+3*log (N:ℝ)/64)-log (R:ℝ)/2≤-20 := by
    have hεL := mul_le_mul_of_nonneg_right hε (show 0 ≤ log (N:ℝ) by linarith only [hL])
    linarith only [hL,hlogR,hlog2,hεL]
  have h20 : (20:ℝ)≤ exp 20 := by linarith only [add_one_le_exp (20:ℝ)]
  calc
    _ ≤ ((20/sqrt R)*exp (1096+log (N:ℝ)/16))*exp (822+3*log (N:ℝ)/64) :=
      mul_le_mul_of_nonneg_left (expanded_singular_series_cap hN) (by positivity)
    _ = 20*exp (1096+log (N:ℝ)/16+(822+3*log (N:ℝ)/64)-log (R:ℝ)/2) := by
      rw [show (20:ℝ)/sqrt R=20*(1/sqrt R) by ring,hroot]
      calc
        _ = 20*(exp (-log (R:ℝ)/2)*exp (1096+log (N:ℝ)/16)*
            exp (822+3*log (N:ℝ)/64)) := by ring
        _ = _ := by rw [← exp_add,← exp_add]; congr 1; ring
    _ ≤ 20*exp (-20:ℝ) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (by norm_num)
    _ ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_right h20 (exp_pos (-20:ℝ)).le
      rw [← exp_add] at hh
      norm_num at hh
      exact hh

theorem denominator_81_of_log {N : ℕ} {ε : ℝ} (hε : ε ≤ 1/1000)
    (hL : (263000:ℝ)≤ log (N:ℝ)) (hEven : Even N) :
    log (N:ℝ)/((81/10:ℝ)*liuSingularSeries N)≤ liuSelbergDenominator N ε := by
  have hn : 0<N := by
    by_contra h
    have hh : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hN256 : 256≤ N := by
    have hh := log_le_sub_one_of_pos hnR
    exact_mod_cast (by linarith only [hh,hL] : (256:ℝ)≤ N)
  obtain ⟨hlogR,hR⟩ := numerical_selberg_log_floor hN256
    (show (1/8:ℝ)≤1/4-ε/2 by linarith only [hε])
  change 2≤ paperQSourceCutoff N ε at hR
  change (1/4-ε/2)*log (N:ℝ)-log 2≤ log (paperQSourceCutoff N ε:ℝ) at hlogR
  have hexp := selberg_uniform_two_term_expansion hEven hn (show 1≤ paperQSourceCutoff N ε by omega)
  rw [← liuSelbergDenominator_eq_sum_Icc hEven (by omega)] at hexp
  have hlo := (abs_le.mp hexp).1
  have hSp := liuSingularSeries_pos N
  have hmul := mul_le_mul_of_nonneg_right hlo hSp.le
  have herr := normalized_error hε hn hL (show 1≤ paperQSourceCutoff N ε by omega) hlogR
  have hc := (selberg_specialized_secondary_pos N).le
  have hmain : ((log (paperQSourceCutoff N ε:ℝ)+selbergSpecializedSecondary N)/
      (2*liuSingularSeries N))*liuSingularSeries N=
      (log (paperQSourceCutoff N ε:ℝ)+selbergSpecializedSecondary N)/2 := by field_simp
  rw [sub_mul,hmain] at hmul
  apply (div_le_iff₀ (mul_pos (by norm_num) hSp)).mpr
  have hl2 : log (2:ℝ)≤1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hεL := mul_le_mul_of_nonneg_right hε (show 0≤ log (N:ℝ) by linarith only [hL])
  nlinarith only [hmul,herr,hc,hlogR,hL,hl2,hεL]


theorem denominator_at_target {N : ℕ} (hN : targetCutoff ≤ N)
    (hEven : Even N) {ε : ℝ} (hε : ε ≤ 1/1000) :
    log (N:ℝ)/((81/10:ℝ)*liuSingularSeries N) ≤ liuSelbergDenominator N ε :=
  denominator_81_of_log hε (target_log_lower hN) hEven

#print axioms denominator_at_target
end ChenEffective.GRH125
end

/- Component: GRH125RadiusBudget -/
/-! Joint choice of the actual Selberg radius and its main coefficient.
The radius can now match the GRH distribution level N^0.498. No complete
triple estimate is asserted merely from this denominator bound. -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
theorem normalized_radius_error {N R : ℕ} {ε : ℝ} (hε : ε ≤ 1/200)
    (hN : 0<N) (hL : (263000:ℝ)≤ log (N:ℝ)) (hR : 1≤ R)
    (hlogR : (1/4-ε/2)*log (N:ℝ)-log 2≤ log (R:ℝ)) :
    ((20/sqrt R)*exp (1096+log (N:ℝ)/16))*liuSingularSeries N≤1 := by
  have hRp : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hroot : 1/sqrt (R:ℝ)=exp (-log (R:ℝ)/2) := by
    rw [sqrt_eq_rpow,rpow_def_of_pos hRp,one_div,← exp_neg]
    congr 1
    ring
  have hlog2 : log (2:ℝ)≤1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have he : 1096+log (N:ℝ)/16+(822+3*log (N:ℝ)/64)-log (R:ℝ)/2≤-20 := by
    have hεL := mul_le_mul_of_nonneg_right hε (show 0 ≤ log (N:ℝ) by linarith only [hL])
    linarith only [hL,hlogR,hlog2,hεL]
  have h20 : (20:ℝ)≤ exp 20 := by linarith only [add_one_le_exp (20:ℝ)]
  calc
    _ ≤ ((20/sqrt R)*exp (1096+log (N:ℝ)/16))*exp (822+3*log (N:ℝ)/64) :=
      mul_le_mul_of_nonneg_left (expanded_singular_series_cap hN) (by positivity)
    _ = 20*exp (1096+log (N:ℝ)/16+(822+3*log (N:ℝ)/64)-log (R:ℝ)/2) := by
      rw [show (20:ℝ)/sqrt R=20*(1/sqrt R) by ring,hroot]
      calc
        _ = 20*(exp (-log (R:ℝ)/2)*exp (1096+log (N:ℝ)/16)*
            exp (822+3*log (N:ℝ)/64)) := by ring
        _ = _ := by rw [← exp_add,← exp_add]; congr 1; ring
    _ ≤ 20*exp (-20:ℝ) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (by norm_num)
    _ ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_right h20 (exp_pos (-20:ℝ)).le
      rw [← exp_add] at hh
      norm_num at hh
      exact hh

theorem denominator_of_radius_budget {N : ℕ} {ε K : ℝ}
    (hε : ε ≤ 1/200) (hK : 0 < K)
    (hgap : 1/K+(1/150000:ℝ) ≤ 1/8-ε/4)
    (hL : (263000:ℝ)≤ log (N:ℝ)) (hEven : Even N) :
    log (N:ℝ)/(K*liuSingularSeries N)≤ liuSelbergDenominator N ε := by
  have hn : 0<N := by
    by_contra h
    have hh : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hN256 : 256≤ N := by
    have hh := log_le_sub_one_of_pos hnR
    exact_mod_cast (by linarith only [hh,hL] : (256:ℝ)≤ N)
  obtain ⟨hlogR,hR⟩ := numerical_selberg_log_floor hN256
    (show (1/8:ℝ)≤1/4-ε/2 by linarith only [hε])
  change 2≤ paperQSourceCutoff N ε at hR
  change (1/4-ε/2)*log (N:ℝ)-log 2≤ log (paperQSourceCutoff N ε:ℝ) at hlogR
  have hexp := selberg_uniform_two_term_expansion hEven hn (show 1≤ paperQSourceCutoff N ε by omega)
  rw [← liuSelbergDenominator_eq_sum_Icc hEven (by omega)] at hexp
  have hlo := (abs_le.mp hexp).1
  have hSp := liuSingularSeries_pos N
  have hmul := mul_le_mul_of_nonneg_right hlo hSp.le
  have herr := normalized_radius_error hε hn hL (show 1≤ paperQSourceCutoff N ε by omega) hlogR
  have hc := (selberg_specialized_secondary_pos N).le
  have hmain : ((log (paperQSourceCutoff N ε:ℝ)+selbergSpecializedSecondary N)/
      (2*liuSingularSeries N))*liuSingularSeries N=
      (log (paperQSourceCutoff N ε:ℝ)+selbergSpecializedSecondary N)/2 := by field_simp
  rw [sub_mul,hmain] at hmul
  have hl2 : log (2:ℝ) ≤ 1 := by
    linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hpaid := mul_le_mul_of_nonneg_right hgap
    (show 0 ≤ log (N:ℝ) by linarith only [hL])
  have hlinear : log (N:ℝ)/K ≤ liuSelbergDenominator N ε*liuSingularSeries N := by
    rw [div_eq_mul_inv]
    simp only [one_div] at hpaid
    nlinarith only [hmul,herr,hc,hlogR,hL,hl2,hpaid]
  rw [← div_div]
  exact (div_le_iff₀ hSp).mpr hlinear


theorem denominator_80326_at_target {N : ℕ} (hN : targetCutoff ≤ N)
    (hEven : Even N) :
    log (N:ℝ)/((80326/10000:ℝ)*liuSingularSeries N) ≤
      liuSelbergDenominator N (1/500:ℝ) := by
  exact denominator_of_radius_budget (by norm_num) (by norm_num)
    (by norm_num) (target_log_lower hN) hEven

theorem improved_radius_margin :
    (2.02575:ℝ)-((80326/10000:ℝ)*(0.49254+1/10000)+1/1000)/2 =
      (0.046659968:ℝ) := by norm_num

#print axioms denominator_80326_at_target
end ChenEffective.GRH125
end

/- Component: GRH125TripleBridge -/
/-! The actual triple-to-square bridge at the proposed H<14 cutoff.
The square estimate is an explicit premise. No numerical estimate of the
square remainder is inferred from the denominator alone. -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem triple_residual_cutoff_le_target : tripleResidualThreshold ≤ targetCutoff := by
  rw [targetCutoff_eq]
  unfold tripleResidualThreshold logPowerCutoff
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem triple_of_square_at_target {N : ℕ} (hN : targetCutoff ≤ N)
    (hEven : Even N) {ε A E : ℝ} (hε : 0 ≤ ε) (hεHalf : ε ≤ 1/2)
    (hSquare : liuSelbergSquareCount N ε (liuSelbergOptimalLambda N ε) ≤
      A*(liuSingularSeries N*N/log (N:ℝ)^2)+E) :
    correctedChenTriplePenalty N ≤
      A*(liuSingularSeries N*N/log (N:ℝ)^2)+E+19*N/log (N:ℝ)^3 := by
  have hres := triple_residual_cutoff_le_target.trans hN
  have hlarge := tripleResidualThreshold_large.trans hres
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR : 1 ≤ paperQSourceCutoff N ε := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hN1
      (show 0 ≤ 1/4-ε/2 by linarith only [hεHalf])
  have hs := liuSelbergCorrectedSourceTripleCount_le_square_add_QResidual
    (epsilon:=ε) hEven hR
  have hc := explicit_triple_complement hres
  have hp := explicit_triple_paper_residual hres ε hε
  unfold correctedChenTriplePenalty
  calc
    _ ≤ liuSelbergCorrectedSourceTripleCount N+13*N/log (N:ℝ)^3 := hc
    _ ≤ (liuSelbergSquareCount N ε (liuSelbergOptimalLambda N ε)+
        liuSelbergCorrectedSourceTripleQResidual N ε)+13*N/log (N:ℝ)^3 :=
      add_le_add hs le_rfl
    _ ≤ (A*(liuSingularSeries N*N/log (N:ℝ)^2)+E+6*N/log (N:ℝ)^3)+
        13*N/log (N:ℝ)^3 := add_le_add (add_le_add hSquare hp) le_rfl
    _ = _ := by ring

theorem triple_residual_payment {N : ℕ} (hN : targetCutoff ≤ N) :
    19*N/log (N:ℝ)^3 ≤
      (1/6000:ℝ)*(liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hL := target_log_lower hN
  have hl : 0 < log (N:ℝ) := by linarith only [hL]
  have hS := half_le_liuSingularSeries N
  have hcoeff : (19:ℝ)/log (N:ℝ) ≤ (1/6000:ℝ)*liuSingularSeries N := by
    apply (div_le_iff₀ hl).mpr
    have hh := mul_le_mul_of_nonneg_right hS hl.le
    nlinarith only [hh,hL]
  have hp := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ (N:ℝ)/log (N:ℝ)^2 by positivity)
  convert hp using 1 <;> field_simp [hl.ne']

/-- A square estimate with this explicit remaining error budget suffices
for the proposed Chen endgame. -/
theorem chen_of_lower_and_square {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N)
    (hLower : (2.02575:ℝ)*(liuSingularSeries N*N/log (N:ℝ)^2) ≤
      jurkatRichertWeightedCount N)
    (hSquare : liuSelbergSquareCount N (1/500:ℝ)
        (liuSelbergOptimalLambda N (1/500:ℝ)) ≤
      ((81/10:ℝ)*(0.49254+1/10000)+5/6000)*
        (liuSingularSeries N*N/log (N:ℝ)^2)) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  apply representation_of_target_counts hN hLower
  have ht := triple_of_square_at_target hN hEven
    (ε:=(1/500:ℝ)) (A:=((81/10:ℝ)*(0.49254+1/10000)+5/6000))
    (E:=0) (by norm_num) (by norm_num) (by simpa using hSquare)
  have hp := triple_residual_payment hN
  nlinarith only [ht,hp]

#print axioms chen_of_lower_and_square
end ChenEffective.GRH125
end

/- Component: GRH125TripleUpper -/
/-! The actual square and corrected triple estimates at the target.
The distribution remainder is supplied by the explicit Pan assembly. -/
noncomputable section
namespace ChenEffective.GRH125
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem selberg_square_at_target {N : ℕ} (hN : targetCutoff≤ N) (hEven : Even N) :
    liuSelbergSquareCount N (1/500:ℝ) (liuSelbergOptimalLambda N (1/500:ℝ)) ≤
      ((80326/10000:ℝ)*0.498+1/1000)*
        (liuSingularSeries N*N/log (N:ℝ)^2) := by
  let ε : ℝ := 1/500
  let lam := liuSelbergOptimalLambda N ε
  let K : ℝ := 80326/10000
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hn1 : (1:ℝ)≤ N := by exact_mod_cast (show 1≤ N by omega)
  have hR : 1≤ paperQSourceCutoff N ε := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using Real.one_le_rpow hn1
      (show 0≤1/4-ε/2 by norm_num [ε])
  have hadm : LiuSelbergLambdaAdmissible N ε lam :=
    ⟨fun _ hd => liuSelbergOptimalLambda_support hd,
      fun d => abs_liuSelbergOptimalLambda_le_one hEven hR⟩
  have hcoef : LiuSelbergCoefficientFactorBound (K-8) N ε lam := by
    unfold LiuSelbergCoefficientFactorBound
    rw [liuSelbergCoefficientFactor_optimalLambda hEven hR]
    have hh := one_div_liuSelbergDenominator_le (delta:=K-8)
      (by norm_num [K]) (by omega) hEven hR
      (by simpa [K,ε] using denominator_80326_at_target hN hEven)
    simpa using hh
  have hmain := liuSelbergMainTerm_le_of_componentBounds 2 (K-8) (0.498:ℝ)
    N ε lam hEven hadm (by norm_num [K]) (liuSingularSeries_pos N).le
    (log_pos (by exact_mod_cast (show 1<N by omega))) hcoef (numerical_prime_pair_main hN)
  have hr := numerical_selberg_remainder hN lam hadm
  have hp := selberg_remainder_paid hN
  rw [liuSelbergSquareCount_eq_switchedCount,
    liuSelbergSwitchedCount_eq_logarithmicIntegralMainTerm_add_remainder 2]
  have hh := add_le_add hmain ((le_abs_self _).trans (hr.trans hp))
  convert hh using 1 <;> dsimp [K,ε,lam] <;> ring

theorem triple_upper {N : ℕ} (hN : targetCutoff≤ N) (hEven : Even N) :
    correctedChenTriplePenalty N ≤
      (4.0015:ℝ)*(liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hh := triple_of_square_at_target hN hEven
    (ε:=(1/500:ℝ)) (A:=(80326/10000:ℝ)*0.498+1/1000) (E:=0)
    (by norm_num) (by norm_num) (by simpa using selberg_square_at_target hN hEven)
  have hp := triple_residual_payment hN
  have hm : 0≤ liuSingularSeries N*N/log (N:ℝ)^2 :=
    div_nonneg (mul_nonneg (liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  nlinarith only [hh,hp,hm]

#print axioms selberg_square_at_target
#print axioms triple_upper
end ChenEffective.GRH125
end

/- Component: GRH125ChenBridge -/
noncomputable section
namespace ChenEffective.GRH125
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple

/-- Actual prime plus at-most-two-prime-factor representation at the explicit
cutoff. The complete lower and upper counting estimates supply all premises. -/
theorem chen_of_weighted_lower {N : ℕ} (hN : targetCutoff≤ N) (hEven : Even N)
    (hLower : (2.02575:ℝ)*(SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2)≤
      jurkatRichertWeightedCount N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  have hN9 := (logPowerCutoff_nine_le 0).trans (pan_log_cutoff_at_target (k:=0) (by norm_num) hN)
  have hM : 0<SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2 :=
    div_pos (mul_pos (SingularSeries.liuSingularSeries_pos N)
      (by exact_mod_cast (show 0<N by omega)))
      (pow_pos (Real.log_pos (by exact_mod_cast (show 1<N by omega))) 2)
  have htriple := triple_upper hN hEven
  have hb := corrected_counting_bridge_public_of_nine_le hN9
  rw [correctedChenKeyCount_eq_jurkatRichertWeightedCount_sub_triple] at hb
  have hcard : 0<(chenGoodRepresentations N).card := by
    exact_mod_cast (show (0:ℝ)<((chenGoodRepresentations N).card:ℝ) by
      nlinarith only [hb,hLower,htriple,hM])
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations,Finset.mem_filter,Finset.mem_range] at hp
  exact ⟨p,N-p,hp.2.1,MathlibNt.ChensTheorem.semiprime_iff.mp
    ⟨hp.2.2.1,hp.2.2.2⟩,by omega⟩

#print axioms chen_of_weighted_lower

theorem target_of_double_exp_14 {N : ℕ}
    (hN : Real.exp (Real.exp (14:ℝ))≤ N) : targetCutoff≤ N := by
  exact_mod_cast targetCutoff_lt_double_exp_14.le.trans hN

end ChenEffective.GRH125
end
