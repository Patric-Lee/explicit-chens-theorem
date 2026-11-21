import GRHLogDerivative
import NumericalZetaStrip

/-! Near-critical-line bounds for the principal PNT input. The removed
zeta pole is treated explicitly; GRH is used only to exclude zeros. -/
namespace ChenEffective.GRH
open Complex Set Metric MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem zeta_ne_zero_right {s : ℂ} (hs : (1/2:ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  by_cases h1 : s.re < 1
  · intro hz
    have hh := zeta_zeros_on_line s (by linarith only [hs]) h1 hz
    linarith only [hh,hs]
  · exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h1)

theorem regularized_zeta_ne_zero_GRH {s : ℂ} (hs : (1/2:ℝ) < s.re) :
    riemannZeta₁ s ≠ 0 := by
  by_cases h : s = 1
  · simp [h]
  · rw [regularized_zeta_eq h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (zeta_ne_zero_right hs)

theorem regularized_zeta_logDerivative_gap
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (s : ℂ) (hs : (1/2:ℝ)+a ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ ≤
      (64/a^2) * Real.log (32 * (|s.im| + 6) ^ 2) := by
  let c : ℂ := 2 + I * s.im
  let f : ℂ → ℂ := fun z => riemannZeta₁ (c + z)
  let U : ℝ := 16 * (|s.im| + 6) ^ 2
  have hU : 1 ≤ U := by dsimp [U]; nlinarith [abs_nonneg s.im, sq_nonneg (|s.im|)]
  have hf : DifferentiableOn ℂ f (ball 0 (3 / 2)) := by fun_prop
  have hRe (z : ℂ) (hz : z ∈ ball (0 : ℂ) (3 / 2)) : (1 / 2 : ℝ) < (c + z).re := by
    have hn : ‖z‖ < 3 / 2 := mem_ball_zero_iff.mp hz
    have hre := (neg_le_abs z.re).trans (abs_re_le_norm z)
    dsimp [c]
    simp only [mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self]
    linarith only [hn, hre]
  have hzero : ∀ z ∈ ball (0 : ℂ) (3 / 2), f z ≠ 0 := by
    intro z hz
    exact regularized_zeta_ne_zero_GRH (hRe z hz)
  have hbound : ∀ z ∈ ball (0 : ℂ) (3 / 2), ‖f z‖ ≤ U := by
    intro z hz
    have hre := hRe z hz
    have hn : ‖z‖ < 3 / 2 := mem_ball_zero_iff.mp hz
    have hc : ‖c‖ ≤ 2 + |s.im| := by
      dsimp [c]
      simpa only [norm_ofNat, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
        using norm_add_le (2 : ℂ) (I * s.im)
    have hnorm : ‖c + z‖ ≤ |s.im| + 4 := by
      have ht := norm_add_le c z
      linarith only [ht, hc, hn]
    have hsub : ‖c + z - 1‖ ≤ |s.im| + 5 := by
      have ht := norm_sub_le (c + z) (1 : ℂ)
      norm_num at ht
      linarith only [ht, hnorm]
    have hratio : ‖c + z‖ / (c + z).re ≤ 2 * (|s.im| + 4) := by
      apply (div_le_iff₀ (by linarith only [hre])).mpr
      have hp := mul_le_mul_of_nonneg_left hre.le (show 0 ≤ 2 * (|s.im| + 4) by positivity)
      nlinarith only [hp, hnorm, abs_nonneg s.im]
    calc
      _ ≤ 1 + ‖c + z - 1‖ * (2 + ‖c + z‖ / (c + z).re) :=
        regularized_zeta_weak_bound (c + z) (by linarith only [hre])
      _ ≤ 1 + (|s.im| + 5) * (2 + 2 * (|s.im| + 4)) := by gcongr
      _ ≤ U := by dsimp [U]; nlinarith [abs_nonneg s.im, sq_nonneg (|s.im|)]
  have hcenter : (1 / 2 : ℝ) ≤ ‖f 0‖ := by
    have hcne : c ≠ 1 := by intro h; have hh := congrArg Complex.re h; norm_num [c] at hh
    have hl : (1 / 2 : ℝ) ≤ ‖riemannZeta c‖ := by
      simpa only [DirichletCharacter.LFunction_modOne_eq, c] using
        dirichlet_L_at_two_lower (1 : DirichletCharacter ℂ 1) s.im
    have hn : (1 : ℝ) ≤ ‖c - 1‖ := by
      have hh := re_le_norm (c - 1)
      norm_num [c] at hh ⊢
      exact hh
    change (1 / 2 : ℝ) ≤ ‖riemannZeta₁ (c + 0)‖
    rw [add_zero, regularized_zeta_eq hcne, norm_mul]
    nlinarith only [hl, hn]
  have hz : ‖s - c‖ ≤ 3/2-a := by
    have heq : s - c = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [hs2])]
    linarith only [hs]
  have hd := logDerivative_disk_gap f U a ha ha1 hU hf hzero hbound hcenter hz
  have hident : c + (s - c) = s := by ring
  have hderiv : deriv f (s - c) = deriv riemannZeta₁ s := by
    have h := (differentiable_riemannZeta₁ (c + (s - c))).hasDerivAt.comp (s - c)
      ((hasDerivAt_const (s - c) c).add (hasDerivAt_id (s - c)))
    simpa only [f, Function.comp_def, hident, zero_add, mul_one] using h.deriv
  simpa only [hderiv, f, hident, U, show (2 : ℝ) * (16 * (|s.im| + 6) ^ 2) =
    32 * (|s.im| + 6) ^ 2 by ring] using hd


theorem zeta_logDerivative_regularized_GRH {s : ℂ}
    (hs : (1/2:ℝ) < s.re) (hne : s ≠ 1) :
    deriv riemannZeta s/riemannZeta s =
      deriv riemannZeta₁ s/riemannZeta₁ s-(s-1)⁻¹ := by
  have hd := deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hne
  rw [hd,riemannZeta_eq_inv_sub_mul hne]
  have hreg := regularized_zeta_ne_zero_GRH hs
  have hsub : s-1 ≠ 0 := sub_ne_zero.mpr hne
  field_simp
  ring

theorem zeta_logDerivative_gap {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (s : ℂ) (hs : (1/2:ℝ)+a ≤ s.re) (hs2 : s.re ≤ 2) (hne : s ≠ 1) :
    ‖deriv riemannZeta s/riemannZeta s‖ ≤
      (64/a^2)*Real.log (32*(|s.im|+6)^2)+‖s-1‖⁻¹ := by
  rw [zeta_logDerivative_regularized_GRH (by linarith only [hs,ha]) hne]
  exact (norm_sub_le _ _).trans (add_le_add
    (regularized_zeta_logDerivative_gap ha ha1 s hs hs2) (le_of_eq (norm_inv _)))

#print axioms zeta_logDerivative_gap
end ChenEffective.GRH
