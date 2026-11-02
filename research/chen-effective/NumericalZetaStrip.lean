import NumericalDirichletStrip
import PrimeNumberTheoremAnd.ZetaBounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace ChenEffective
open Complex Set Metric MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem regularized_zeta_eq {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

theorem regularized_zeta_ne_zero {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    riemannZeta₁ s ≠ 0 := by
  by_cases h : s = 1
  · simp [h]
  · rw [regularized_zeta_eq h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (zeta_ne_zero hs h)

/-- A crude Euler--Maclaurin bound, valid right up to the removed pole. -/
theorem regularized_zeta_weak_bound (s : ℂ) (hs : 0 < s.re) :
    ‖riemannZeta₁ s‖ ≤ 1 + ‖s - 1‖ * (2 + ‖s‖ / s.re) := by
  by_cases h : s = 1
  · simp [h]
  have hs0 : s ≠ 0 := by intro he; simp [he] at hs
  let J : ℂ := ∫ x in Ioi (1 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)
  have hJ : ‖J‖ ≤ 1 / s.re := by
    have he : ((s.re : ℂ) + s.im * I) = s := by apply Complex.ext <;> simp
    have hh := ZetaBnd_aux1b 1 (by norm_num) (σ := s.re) (t := s.im) hs
    simpa only [he, Nat.cast_one, Real.one_rpow] using hh
  have hz := Zeta0EqZeta (N := 1) (by norm_num) hs h
  have hz' : riemannZeta s = 1 + 1 / (s - 1) - 1 / 2 + s * J := by
    rw [← hz, riemannZeta0]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
      Nat.cast_one, Complex.zero_cpow hs0, div_zero, one_cpow, div_one, zero_add]
    dsimp [J]
    have he : (1 - s : ℂ) = -(s - 1) := by ring
    rw [he, div_neg]
    ring
  have hidentity : riemannZeta₁ s = 1 + (s - 1) * ((1 / 2 : ℂ) + s * J) := by
    rw [regularized_zeta_eq h, hz']
    field_simp
    ring
  rw [hidentity]
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(s - 1) * ((1 / 2 : ℂ) + s * J)‖ := norm_add_le _ _
    _ = 1 + ‖s - 1‖ * ‖(1 / 2 : ℂ) + s * J‖ := by rw [norm_one, norm_mul]
    _ ≤ 1 + ‖s - 1‖ * (2 + ‖s‖ / s.re) := by
      gcongr
      calc
        _ ≤ ‖(1 / 2 : ℂ)‖ + ‖s * J‖ := norm_add_le _ _
        _ ≤ 1 / 2 + ‖s‖ * (1 / s.re) := by
          rw [norm_mul]
          norm_num
          gcongr
          simpa only [one_div] using hJ
        _ ≤ 2 + ‖s‖ / s.re := by rw [← div_eq_mul_one_div]; linarith

theorem numerical_regularized_zeta_logDerivative_strip
    (s : ℂ) (hs : (15 / 16 : ℝ) ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ ≤
      8192 * Real.log (32 * (|s.im| + 6) ^ 2) := by
  let c : ℂ := 2 + I * s.im
  let f : ℂ → ℂ := fun z => riemannZeta₁ (c + z)
  let U : ℝ := 16 * (|s.im| + 6) ^ 2
  have hU : 1 ≤ U := by dsimp [U]; nlinarith [abs_nonneg s.im, sq_nonneg (|s.im|)]
  have hf : DifferentiableOn ℂ f (ball 0 (9 / 8)) := by fun_prop
  have hRe (z : ℂ) (hz : z ∈ ball (0 : ℂ) (9 / 8)) : (7 / 8 : ℝ) < (c + z).re := by
    have hn : ‖z‖ < 9 / 8 := mem_ball_zero_iff.mp hz
    have hre := (neg_le_abs z.re).trans (abs_re_le_norm z)
    dsimp [c]
    simp only [mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self]
    linarith only [hn, hre]
  have hzero : ∀ z ∈ ball (0 : ℂ) (9 / 8), f z ≠ 0 := by
    intro z hz
    exact regularized_zeta_ne_zero (hRe z hz)
  have hbound : ∀ z ∈ ball (0 : ℂ) (9 / 8), ‖f z‖ ≤ U := by
    intro z hz
    have hre := hRe z hz
    have hn : ‖z‖ < 9 / 8 := mem_ball_zero_iff.mp hz
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
  have hz : ‖s - c‖ ≤ 17 / 16 := by
    have heq : s - c = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [hs2])]
    linarith only [hs]
  have hd := numerical_logDerivative_on_disk f U hU hf hzero hbound hcenter hz
  have hident : c + (s - c) = s := by ring
  have hderiv : deriv f (s - c) = deriv riemannZeta₁ s := by
    have h := (differentiable_riemannZeta₁ (c + (s - c))).hasDerivAt.comp (s - c)
      ((hasDerivAt_const (s - c) c).add (hasDerivAt_id (s - c)))
    simpa only [f, Function.comp_def, hident, zero_add, mul_one] using h.deriv
  simpa only [hderiv, f, hident, U, show (2 : ℝ) * (16 * (|s.im| + 6) ^ 2) =
    32 * (|s.im| + 6) ^ 2 by ring] using hd

theorem zeta_logDerivative_eq_regularized {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hne : s ≠ 1) :
    deriv riemannZeta s / riemannZeta s =
      deriv riemannZeta₁ s / riemannZeta₁ s - (s - 1)⁻¹ := by
  have hd := deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hne
  rw [hd, riemannZeta_eq_inv_sub_mul hne]
  have hreg := regularized_zeta_ne_zero hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hne
  field_simp
  ring

theorem numerical_zeta_logDerivative_strip (s : ℂ)
    (hs : (15 / 16 : ℝ) ≤ s.re) (hs2 : s.re ≤ 2) (hne : s ≠ 1) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤
      8192 * Real.log (32 * (|s.im| + 6) ^ 2) + ‖s - 1‖⁻¹ := by
  rw [zeta_logDerivative_eq_regularized (by linarith) hne]
  exact (norm_sub_le _ _).trans (add_le_add
    (numerical_regularized_zeta_logDerivative_strip s hs hs2) (le_of_eq (norm_inv _)))

#print axioms regularized_zeta_weak_bound
#print axioms numerical_regularized_zeta_logDerivative_strip
end ChenEffective
