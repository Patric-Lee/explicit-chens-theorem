import GRHContour
import GRHMellin
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Logarithmic, rather than length-proportional, control of the left
Perron edge. This keeps the useful growth when smoothing is removed. -/
namespace ChenEffective.GRH
open Set Function Filter Complex Real MeasureTheory
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

private noncomputable def reciprocalEdge (t : ℝ) : ℝ := (1+|t|)⁻¹

private theorem reciprocalEdge_continuous : Continuous reciprocalEdge := by
  unfold reciprocalEdge
  exact (continuous_const.add continuous_abs).inv₀
    (fun t => show (1+|t|:ℝ) ≠ 0 from ne_of_gt (by positivity))

private theorem reciprocalEdge_integral {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, reciprocalEdge t) = 2*Real.log (1+T) := by
  have hip := reciprocalEdge_continuous.intervalIntegrable (μ := volume) 0 T
  have hin := reciprocalEdge_continuous.intervalIntegrable (μ := volume) (-T) 0
  have hp : (∫ t in 0..T, reciprocalEdge t) = Real.log (1+T) := by
    have heq : (∫ t in 0..T, reciprocalEdge t) = ∫ t in 0..T, (1+t)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hT] at ht
      simp only [reciprocalEdge,abs_of_nonneg ht.1]
    rw [heq]
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0:ℝ)) (b := T) (f := fun t : ℝ => Real.log (1+t))
      (f' := fun t : ℝ => (1+t)⁻¹) (fun t ht => by
        rw [uIcc_of_le hT] at ht
        have hn : (1+t:ℝ) ≠ 0 := by linarith only [ht.1]
        simpa using
          ((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).log hn)
      (by
        have hc : ContinuousOn (fun t : ℝ => (1+t)⁻¹) (Icc 0 T) := by
          apply (continuous_const.add continuous_id).continuousOn.inv₀
          intro t ht
          change (1+t:ℝ) ≠ 0
          linarith only [ht.1]
        exact hc.intervalIntegrable_of_Icc hT)
    simpa using hh
  have hn : (∫ t in -T..0, reciprocalEdge t) = ∫ t in 0..T, reciprocalEdge t := by
    have hh := intervalIntegral.integral_comp_neg (f := reciprocalEdge) (a := (0:ℝ)) (b := T)
    simpa only [reciprocalEdge,abs_neg,neg_zero] using hh.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hin hip,hn,hp]
  ring

theorem perron_left_logarithmic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ T ε X J : ℝ}
    (hσ : (1/2:ℝ) ≤ σ) (hσ2 : σ ≤ 2) (hT : 0 ≤ T)
    (hε : 0 < ε) (hε1 : ε < 1) (hX : 1 ≤ X) (hJ : 0 ≤ J)
    (hlog : ∀ t : ℝ, |t| ≤ T →
      ‖deriv χ.LFunction ((σ:ℂ)+t*I)/χ.LFunction ((σ:ℂ)+t*I)‖ ≤ J) :
    ‖VIntegral (χ.twistedSmoothedPerronIntegrand numericalSmoothing ε X) σ (-T) T‖ ≤
      4608*J*X^σ*Real.log (1+T) := by
  let F := χ.twistedSmoothedPerronIntegrand numericalSmoothing ε X
  let K : ℝ := 2304*J*X^σ
  have hpoint (t : ℝ) (ht : t ∈ Ioc (-T) T) :
      ‖F ((σ:ℂ)+t*I)‖ ≤ K*reciprocalEdge t := by
    have hll := hlog t (abs_le.mpr ⟨ht.1.le,ht.2⟩)
    have hs : (((σ:ℂ)+t*I):ℂ).re = σ := by simp
    have him : (((σ:ℂ)+t*I):ℂ).im = t := by simp
    have hn : (1/2:ℝ) ≤ ‖(σ:ℂ)+t*I‖ := by
      have hh := Complex.re_le_norm ((σ:ℂ)+t*I)
      rw [hs] at hh
      exact hσ.trans hh
    have hat : |t| ≤ ‖(σ:ℂ)+t*I‖ := by
      simpa only [him] using Complex.abs_im_le_norm ((σ:ℂ)+t*I)
    have hi : ‖(σ:ℂ)+t*I‖⁻¹ ≤ 3*(1+|t|)⁻¹ := by
      rw [← one_div,← div_eq_mul_inv]
      apply (div_le_div_iff₀ (by linarith only [hn]) (by positivity)).mpr
      linarith only [hn,hat]
    have hmm := smoothed_mellin_low_frequency
      (s := (σ:ℂ)+t*I) (by rw [hs]; linarith only [hσ]) (by rw [hs]; exact hσ2) hε hε1
    have hm : ‖mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) ((σ:ℂ)+t*I)‖ ≤
        2304*(1+|t|)⁻¹ := by
      exact hmm.trans (by
        calc
          _ ≤ 768*(3*(1+|t|)⁻¹) := mul_le_mul_of_nonneg_left hi (by norm_num)
          _ = _ := by ring)
    calc
      ‖F ((σ:ℂ)+t*I)‖ =
          ‖deriv χ.LFunction ((σ:ℂ)+t*I)/χ.LFunction ((σ:ℂ)+t*I)‖ *
          ‖mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) ((σ:ℂ)+t*I)‖*X^σ := by
        dsimp only [F,DirichletCharacter.twistedSmoothedPerronIntegrand]
        rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
        simp only [neg_div,norm_neg,hs]
      _ ≤ J*(2304*(1+|t|)⁻¹)*X^σ := by gcongr
      _ = K*reciprocalEdge t := by dsimp only [K,reciprocalEdge]; ring
  rw [VIntegral,norm_smul,norm_I,one_mul]
  have hb := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun t => F ((σ:ℂ)+t*I)) (g := fun t => K*reciprocalEdge t)
    (by linarith only [hT]) (Filter.Eventually.of_forall fun t ht => hpoint t ht)
    (reciprocalEdge_continuous.const_mul K |>.intervalIntegrable (μ := volume) (-T) T)
  apply hb.trans_eq
  rw [intervalIntegral.integral_const_mul,reciprocalEdge_integral hT]
  dsimp only [K]
  ring

#print axioms perron_left_logarithmic
end ChenEffective.GRH
