import NumericalPrimitiveContour
import NumericalZetaStrip

namespace ChenEffective
open Set Function Filter Complex Real MeasureTheory
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem numerical_perron_left {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {T ε X J : ℝ}
    (hT : 1 ≤ T) (hε : 0 < ε) (hε1 : ε < 1) (hX : 1 ≤ X) (hJ : 0 ≤ J)
    (hlog : ∀ t : ℝ, |t| ≤ T →
      ‖deriv χ.LFunction ((15 / 16 : ℝ) + t * I) /
        χ.LFunction ((15 / 16 : ℝ) + t * I)‖ ≤ J) :
    ‖VIntegral (χ.twistedSmoothedPerronIntegrand numericalSmoothing ε X) (15 / 16) (-T) T‖ ≤
      6144 * J * T * X ^ (15 / 16 : ℝ) / ε := by
  let F := χ.twistedSmoothedPerronIntegrand numericalSmoothing ε X
  have hpoint (t : ℝ) (ht : t ∈ Ioc (-T) T) :
      ‖F ((15 / 16 : ℝ) + t * I)‖ ≤ J * (3072 / ε) * X ^ (15 / 16 : ℝ) := by
    have hll := hlog t (abs_le.mpr ⟨ht.1.le, ht.2⟩)
    have hmm := numerical_smoothed_mellin_bound (1 / 2) (by norm_num)
      ((15 / 16 : ℝ) + t * I) (by norm_num) (by norm_num) ε hε hε1
    have hn : (1 / 4 : ℝ) ≤ ‖((15 / 16 : ℝ) : ℂ) + t * I‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      nlinarith [sq_nonneg t]
    have hi : (ε * ‖((15 / 16 : ℝ) : ℂ) + t * I‖ ^ 2)⁻¹ ≤ 4 / ε := by
      have hh := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hn
      norm_num at hh
      rw [mul_inv_rev]
      change _ ≤ 4 * ε⁻¹
      simpa only [ofReal_div, ofReal_ofNat] using
        mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr hε.le)
    have hmm' : ‖mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ))
        ((15 / 16 : ℝ) + t * I)‖ ≤ 3072 / ε :=
      hmm.trans (by calc
        _ ≤ 768 * (4 / ε) := mul_le_mul_of_nonneg_left hi (by norm_num)
        _ = _ := by ring)
    dsimp only [F, DirichletCharacter.twistedSmoothedPerronIntegrand]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul, sub_self, add_zero]
    gcongr
    simpa only [neg_div, norm_neg] using hll
  rw [VIntegral, norm_smul, norm_I, one_mul]
  calc
    _ ≤ (J * (3072 / ε) * X ^ (15 / 16 : ℝ)) * |T - -T| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (by
        intro t ht
        rw [uIoc_of_le (by linarith : -T ≤ T)] at ht
        exact hpoint t ht)
    _ = _ := by rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)]; ring

theorem numerical_principal_edge_log_bound {T : ℝ} (hT : 1 ≤ T)
    (s : ℂ) (hs : (15 / 16 : ℝ) ≤ s.re) (hs2 : s.re ≤ 2) (ht : |s.im| ≤ T)
    (hedge : s.re = 15 / 16 ∨ |s.im| = T) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤
      8192 * Real.log (32 * (T + 6) ^ 2) + 16 := by
  have hn : (1 / 16 : ℝ) ≤ ‖s - 1‖ := by
    rcases hedge with h | h
    · have hh := abs_re_le_norm (s - 1)
      simp only [sub_re, one_re, h] at hh
      norm_num at hh
      exact hh
    · have hh := abs_im_le_norm (s - 1)
      simp only [sub_im, one_im, sub_zero, h] at hh
      linarith only [hh, hT]
  have hne : s ≠ 1 := by intro h; norm_num [h] at hn
  have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 16) hn
  norm_num at hi
  have hh := numerical_zeta_logDerivative_strip s hs hs2 hne
  apply hh.trans
  apply add_le_add _ hi
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.log_le_log (by positivity)
  gcongr

#print axioms numerical_principal_edge_log_bound
end ChenEffective
