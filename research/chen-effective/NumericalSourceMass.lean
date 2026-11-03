import NumericalSingularNormalization

namespace ChenEffective
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
end ChenEffective
