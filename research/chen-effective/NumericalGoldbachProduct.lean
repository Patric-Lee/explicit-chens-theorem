import NumericalMertensProduct
import MathlibNt.SieveTheory.Switching.RosserSieveAsymptotics

namespace ChenEffective
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
end ChenEffective
