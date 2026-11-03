import NumericalSuzukiHat
import MathlibNt.SieveTheory.LinearSieve.DimensionOneLowerFactor

namespace ChenEffective
open Set Real MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem numerical_inner_integral {u : ℝ} (hu3 : 3 ≤ u) (hu4 : u ≤ 4) :
    0 ≤ jurkatRichertInnerIntegral u ∧ jurkatRichertInnerIntegral u ≤ 1 := by
  have hint : IntervalIntegrable (fun t : ℝ => Real.log (t - 1) / t) volume 2 (u - 1) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith : (2 : ℝ) ≤ u - 1)]
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht
      change t - 1 ≠ 0
      linarith only [ht.1]
    · exact continuousOn_id
    · intro t ht
      linarith only [ht.1]
  have hpoint (t : ℝ) (ht : t ∈ Icc (2 : ℝ) (u - 1)) :
      0 ≤ Real.log (t - 1) / t ∧ Real.log (t - 1) / t ≤ 1 := by
    have ht0 : 0 < t := by linarith only [ht.1]
    have hl0 : 0 ≤ Real.log (t - 1) := Real.log_nonneg (by linarith only [ht.1])
    have hl := Real.log_le_sub_one_of_pos (show 0 < t - 1 by linarith only [ht.1])
    exact ⟨div_nonneg hl0 ht0.le, (div_le_one ht0).mpr (by linarith only [hl])⟩
  unfold jurkatRichertInnerIntegral
  refine ⟨intervalIntegral.integral_nonneg (by linarith) (fun t ht => (hpoint t ht).1), ?_⟩
  calc
    _ ≤ ∫ _t in (2 : ℝ)..u - 1, (1 : ℝ) :=
      intervalIntegral.integral_mono_on (by linarith) hint intervalIntegrable_const
        (fun t ht => (hpoint t ht).2)
    _ = u - 3 := by simp; ring
    _ ≤ 1 := by linarith only [hu4]

theorem numerical_outer_integrand {u : ℝ} (hu : u ∈ Icc (3 : ℝ) 4) :
    0 ≤ jurkatRichertInnerIntegral u / u ∧ jurkatRichertInnerIntegral u / u ≤ 1 := by
  have hh := numerical_inner_integral hu.1 hu.2
  have hu0 : 0 < u := by linarith only [hu.1]
  exact ⟨div_nonneg hh.1 hu0.le, (div_le_one hu0).mpr (by linarith only [hh.2, hu.1])⟩

theorem numerical_outer_interval {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) (hb : b ≤ 4) :
    IntervalIntegrable (fun u => jurkatRichertInnerIntegral u / u) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
  · apply continuousOn_jurkatRichertInnerIntegral_three_five.mono
    intro u hu
    exact ⟨ha.trans hu.1, hu.2.trans (hb.trans (by norm_num))⟩
  · exact continuousOn_id
  · intro u hu
    linarith only [ha, hu.1]

/-- Quantitative continuity at Chen's ratio; the constant is deliberately loose. -/
theorem numerical_lower_factor_near_five {s : ℝ} (hs4 : 4 ≤ s) (hs5 : s ≤ 5) :
    dimensionOneLowerLinearSieveFactor 5 - 3 * (5 - s) ≤
      dimensionOneLowerLinearSieveFactor s := by
  let A := 2 * Real.exp Real.eulerMascheroniConstant
  let B := fun t : ℝ => Real.log (t - 1) +
    ∫ u in (3 : ℝ)..t - 1, jurkatRichertInnerIntegral u / u
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA6 : A ≤ 6 := by
    have hh : Real.eulerMascheroniConstant ≤ 1 :=
      Real.eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num)
    have he := (Real.exp_le_exp.mpr hh).trans (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 3))
    dsimp [A]
    linarith only [he]
  have hs0 : 0 < s := by linarith only [hs4]
  have hsp : 0 < s - 1 := by linarith only [hs4]
  have h3s : (3 : ℝ) ≤ s - 1 := by linarith only [hs4]
  have hs4' : s - 1 ≤ (4 : ℝ) := by linarith only [hs5]
  have hint1 := numerical_outer_interval (le_refl (3 : ℝ)) h3s hs4'
  have hint2 := numerical_outer_interval h3s hs4' (le_refl (4 : ℝ))
  have hB0 : 0 ≤ B s := by
    dsimp [B]
    apply add_nonneg (Real.log_nonneg (by linarith only [hs4]))
    apply intervalIntegral.integral_nonneg h3s
    intro u hu
    exact (numerical_outer_integrand ⟨hu.1, hu.2.trans hs4'⟩).1
  have hlog : Real.log 4 - Real.log (s - 1) ≤ 5 - s := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / (s - 1) by positivity)
    rw [Real.log_div (by norm_num) hsp.ne'] at hh
    apply hh.trans
    calc
      (4 : ℝ) / (s - 1) - 1 = (5 - s) / (s - 1) := by field_simp; ring
      _ ≤ 5 - s := by
        apply (div_le_iff₀ hsp).mpr
        nlinarith only [hs4, hs5, mul_nonneg (show 0 ≤ 5 - s by linarith only [hs5])
          (show 0 ≤ s - 2 by linarith only [hs4])]
  have hint : (∫ u in s - 1..(4 : ℝ), jurkatRichertInnerIntegral u / u) ≤ 5 - s := by
    calc
      _ ≤ ∫ _u in s - 1..(4 : ℝ), (1 : ℝ) :=
        intervalIntegral.integral_mono_on hs4' hint2 intervalIntegrable_const
          (fun u hu => (numerical_outer_integrand ⟨h3s.trans hu.1, hu.2⟩).2)
      _ = 5 - s := by simp; ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have hB : B 5 - B s ≤ 2 * (5 - s) := by
    dsimp [B]
    norm_num only [show (5 : ℝ) - 1 = 4 by norm_num]
    linarith only [hlog, hint, hadd]
  have hcompare : A / 5 * B s ≤ A / s * B s := by
    apply mul_le_mul_of_nonneg_right _ hB0
    exact div_le_div_of_nonneg_left hA0 hs0 hs5
  have hdiff := mul_le_mul_of_nonneg_left hB (show 0 ≤ A / 5 by positivity)
  have hcoef := mul_le_mul_of_nonneg_right hA6 (show 0 ≤ 5 - s by linarith only [hs5])
  change A / 5 * B 5 - 3 * (5 - s) ≤ A / s * B s
  nlinarith only [hcompare, hdiff, hcoef, hs5]

noncomputable def lowerSieveEpsilon (r : ℕ) : ℝ := 1 / (60 * (r : ℝ))

theorem numerical_lower_epsilon (r : ℕ) (hr : 0 < r) :
    0 < lowerSieveEpsilon r ∧ lowerSieveEpsilon r < 1 / 10 ∧
      dimensionOneLowerLinearSieveFactor 5 - 1 / (2 * (r : ℝ)) ≤
        dimensionOneLowerLinearSieveFactor (chenS (lowerSieveEpsilon r)) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have he0 : 0 < lowerSieveEpsilon r := by unfold lowerSieveEpsilon; positivity
  have he : lowerSieveEpsilon r ≤ 1 / 60 := by
    unfold lowerSieveEpsilon
    apply one_div_le_one_div_of_le (by norm_num)
    linarith only [hrR]
  refine ⟨he0, by linarith only [he], ?_⟩
  have hh := numerical_lower_factor_near_five
    (s := chenS (lowerSieveEpsilon r)) (by unfold chenS; linarith only [he])
    (by unfold chenS; linarith only [he0])
  have hid : 3 * (5 - chenS (lowerSieveEpsilon r)) = 1 / (2 * (r : ℝ)) := by
    unfold chenS lowerSieveEpsilon
    field_simp
    ring
  rwa [hid] at hh

#print axioms numerical_lower_factor_near_five
#print axioms numerical_lower_epsilon
end ChenEffective
