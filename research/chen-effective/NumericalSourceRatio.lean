import NumericalSourceLogDomination

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def sourceRatioHead : ℝ := max (Real.exp 2309) (sourceLogM 1 102400 16)
noncomputable def sourceRatioCutoff : ℝ :=
  max (sourceLogCutoff 1 102400 16) (sourceLowerCutoff sourceRatioHead)

/-- Explicit delayed/current domination on the entire moving source range. -/
theorem numerical_source_ratio {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) {D : ℝ} (hD : sourceRatioCutoff ≤ D) :
    sourceRatioHead ≤ sourceSigma D 16 ∧
    ∀ (sign : ErrorSign) (t : ℝ), sourceRatioHead ≤ t → t ≤ sourceSigma D 16 →
      2 * (16 + 1 : ℝ) * max 1 (Real.log (1 + t^(16 : ℝ) / Real.log D)) *
        weightedHat H sign t ≤ t * H.T sign.opposite (t-1) := by
  refine ⟨numerical_sourceSigma_lower 16 sourceRatioHead (by norm_num) D
    ((le_max_right _ _).trans hD), ?_⟩
  intro sign t ht htσ
  have htcut : Real.exp 2309 ≤ t := (le_max_left _ _).trans ht
  have ht4 : 4 ≤ t := by
    have h := Real.add_one_le_exp (2309 : ℝ)
    linarith only [h, htcut]
  have ht0 : 0 < t := by linarith only [ht4]
  have hQ := numerical_Qhat_forward_shift hH htcut
  have hcomp := numerical_Qhat_le_hat hH sign.opposite
    (show 3 ≤ t-1 by linarith only [ht4])
  have hTQ : H.T sign t ≤ section13Qhat H t := by
    have hp := (hH.positive .plus t ht0).le
    have hm := (hH.positive .minus t ht0).le
    cases sign <;> dsimp [section13Qhat] <;> linarith only [hp, hm]
  have hloget : 0 < Real.log (Real.exp 1 * t) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) ht0.ne', Real.log_exp]
    have hl := Real.log_nonneg (show 1 ≤ t by linarith only [ht4])
    linarith only [hl]
  have hqcoef : 0 ≤ 2 / (t * Real.log (Real.exp 1 * t)) := by positivity
  have hT : H.T sign t ≤
      (102400 / (t * Real.log (Real.exp 1 * t))) * H.T sign.opposite (t-1) := by
    calc
      _ ≤ section13Qhat H t := hTQ
      _ ≤ 2 / (t * Real.log (Real.exp 1 * t)) * section13Qhat H (t-1) := hQ
      _ ≤ 2 / (t * Real.log (Real.exp 1 * t)) *
          (51200 * H.T sign.opposite (t-1)) :=
        mul_le_mul_of_nonneg_left hcomp hqcoef
      _ = _ := by ring
  have hW : weightedHat H sign t ≤
      (102400 / Real.log (Real.exp 1 * t)) * (t * H.T sign.opposite (t-1)) := by
    calc
      _ ≤ t^2 * ((102400 / (t * Real.log (Real.exp 1 * t))) *
          H.T sign.opposite (t-1)) := mul_le_mul_of_nonneg_left hT (sq_nonneg t)
      _ = _ := by field_simp
  have hlogdom := (numerical_source_log_domination
    (K := (1 : ℝ)) (A := 102400) (d := 16)
    (by norm_num) (by norm_num) (by norm_num) D ((le_max_left _ _).trans hD)).2 t
    ((le_max_right _ _).trans ht) htσ
  norm_num only [one_pow, mul_one] at hlogdom
  have hmax : 0 ≤ max 1 (Real.log (1+t^(16 : ℝ)/Real.log D)) :=
    zero_le_one.trans (le_max_left _ _)
  have hcoef : (2 * (16+1 : ℝ) * max 1 (Real.log (1+t^(16 : ℝ)/Real.log D))) *
      (102400 / Real.log (Real.exp 1 * t)) ≤ 1 := by
    rw [← mul_div_assoc]
    exact (div_le_one hloget).mpr (by nlinarith only [hlogdom])
  have hT0 := (hH.positive sign.opposite (t-1) (by linarith only [ht4])).le
  calc
    _ ≤ (2 * (16+1 : ℝ) * max 1 (Real.log (1+t^(16 : ℝ)/Real.log D))) *
        ((102400 / Real.log (Real.exp 1 * t)) *
          (t * H.T sign.opposite (t-1))) :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    _ = ((2 * (16+1 : ℝ) * max 1 (Real.log (1+t^(16 : ℝ)/Real.log D))) *
        (102400 / Real.log (Real.exp 1 * t))) *
          (t * H.T sign.opposite (t-1)) := by ring
    _ ≤ 1 * (t * H.T sign.opposite (t-1)) :=
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg ht0.le hT0)
    _ = _ := one_mul _

#print axioms numerical_source_ratio
end ChenEffective
