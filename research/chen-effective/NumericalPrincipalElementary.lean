import ExplicitLogBounds
import MathlibNt.AnalyticNumberTheory.LargeSieve.PrincipalPNTSourceFromMediumPNT
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

namespace ChenEffective
open Set Filter Real MeasureTheory
open AnalyticNumberTheory.LargeSieve
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem reciprocal_log_nonintegrable_at_one {a b : ℝ} (hab : a ≠ b)
    (hone : (1 : ℝ) ∈ Set.uIcc a b) :
    ¬IntervalIntegrable (fun x : ℝ => 1 / Real.log x) volume a b := by
  have hh : (fun x : ℝ => Real.log x) =O[nhds (1 : ℝ)] (fun x => x - 1) := by
    simpa only [Real.log_one, sub_zero] using (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).isBigO_sub
  have hz : ∀ᶠ x : ℝ in nhdsWithin 1 {1}ᶜ, Real.log x = 0 → x - 1 = 0 := by
    have hxevt : ∀ᶠ x : ℝ in nhdsWithin 1 {1}ᶜ, x ∈ Ioo (1 / 2 : ℝ) (3 / 2) :=
      nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
    filter_upwards [hxevt] with x hx
    intro he
    rcases Real.log_eq_zero.mp he with h | h | h
    · linarith only [hx.1, h]
    · simp [h]
    · linarith only [hx.1, h]
  have hi := (hh.mono nhdsWithin_le_nhds).inv_rev hz
  apply not_intervalIntegrable_of_sub_inv_isBigO_punctured _ hab hone
  simpa only [one_div] using hi

theorem numerical_global_li_discrete_bound (N : ℕ) :
    globalChebyshevToLiSourcePrefixMaxError N ≤ 4 := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have htwo : (2 : ℝ) / Real.log 2 ≤ 4 := by
    apply (div_le_iff₀ (by linarith only [hlog])).mpr
    linarith only [hlog]
  have hzero : (∫ x in (2 : ℝ)..0, 1 / Real.log x) = 0 :=
    intervalIntegral.integral_undef (reciprocal_log_nonintegrable_at_one (by norm_num) (by norm_num [Set.uIcc]))
  have hone : (∫ x in (2 : ℝ)..1, 1 / Real.log x) = 0 :=
    intervalIntegral.integral_undef (reciprocal_log_nonintegrable_at_one (by norm_num) (by norm_num [Set.uIcc]))
  simp only [one_div] at hzero hone
  apply (globalChebyshevToLiSourcePrefixMaxError_le_bound N).trans
  unfold globalLiDiscreteErrorBound
  apply max_le _ (max_le _ htwo)
  all_goals
    norm_num [globalChebyshevToLiSourceError, discreteAbelLiMain, reciprocalLogWeight,
      MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral,
      MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral, hzero, hone,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.log 2)]
    exact htwo

theorem numerical_discrete_abel_bound (N : ℕ) : discreteAbelAmplifierPrefixMax N ≤ 4 := by
  apply (discreteAbelAmplifierPrefixMax_le_two_div_log_two N).trans
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  linarith [Real.log_two_gt_d9]

#print axioms numerical_global_li_discrete_bound
end ChenEffective
