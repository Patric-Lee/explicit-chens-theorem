import ExplicitSiegel
import NumericalLogDerivative
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds

/-! Fixed-strip numerical logarithmic derivative from the single local
Dirichlet 7/8 axiom. This avoids choosing a zero-free width from compactness. -/
namespace ChenEffective
open Complex Set Metric
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem dirichlet_L_at_two_lower {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 2 : ℝ) ≤ ‖χ.LFunction (2 + I * t)‖ := by
  have hprincipal : ‖DirichletCharacter.LFunctionTrivChar q 2‖ ≤ 2 := by
    simpa only [DirichletCharacter.LFunctionTrivChar, ofReal_ofNat, ofReal_zero,
      mul_zero, add_zero, show (1 + 1 / (2 - 1) : ℝ) = 2 by norm_num]
      using norm_dirichletLFunction_le (1 : DirichletCharacter ℂ q) 2 0 (by norm_num)
  have hsquare : ‖(χ ^ 2).LFunction (2 + 2 * I * t)‖ ≤ 2 := by
    have h := norm_dirichletLFunction_le (χ ^ 2) 2 (2 * t) (by norm_num)
    norm_num at h ⊢
    convert h using 1
    congr 2
    ring
  have hprod := χ.norm_LFunction_product_ge_one (by norm_num : (0 : ℝ) < 1) t
  norm_num [norm_mul, norm_pow] at hprod
  have hmajor : 1 ≤ 16 * ‖χ.LFunction (2 + I * t)‖ ^ 4 := by
    calc
      _ ≤ ‖DirichletCharacter.LFunctionTrivChar q 2‖ ^ 3 *
          ‖χ.LFunction (2 + I * t)‖ ^ 4 * ‖(χ ^ 2).LFunction (2 + 2 * I * t)‖ := hprod
      _ ≤ 2 ^ 3 * ‖χ.LFunction (2 + I * t)‖ ^ 4 * 2 := by gcongr
      _ = _ := by ring
  by_contra h
  have hsmall : ‖χ.LFunction (2 + I * t)‖ < 1 / 2 := not_le.mp h
  have hp := pow_lt_pow_left₀ hsmall (norm_nonneg (χ.LFunction (2 + I * t))) (by decide : 4 ≠ 0)
  norm_num at hp
  linarith only [hp, hmajor]

theorem dirichlet_L_weak_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ (q : ℝ) * (1 + ‖s‖ / s.re) := by
  have h := DirichletLConditionalValueSeries.norm_orderedValueSeries_sub_sum_range_le
    χ hχ s hs (m := 1) (by norm_num)
  rw [DirichletLConditionalValueSeries.orderedValueSeries_eq_LFunction_of_re_pos χ hχ s hs] at h
  simpa only [Finset.sum_range_one,
    DirichletLConditionalValueSeries.character_nat_zero_of_ne_one χ hχ,
    mul_zero, sub_zero, Nat.cast_one, Real.one_rpow, mul_one] using h

theorem numerical_dirichlet_logDerivative_strip {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : (15 / 16 : ℝ) ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖deriv χ.LFunction s / χ.LFunction s‖ ≤
      8192 * Real.log (16 * (q : ℝ) * (|s.im| + 4)) := by
  let c : ℂ := 2 + I * s.im
  let f : ℂ → ℂ := fun z => χ.LFunction (c + z)
  let U : ℝ := 8 * (q : ℝ) * (|s.im| + 4)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hU : 1 ≤ U := by dsimp [U]; nlinarith only [hq, abs_nonneg s.im]
  have hf : DifferentiableOn ℂ f (ball 0 (9 / 8)) := by
    fun_prop
  have hRe (z : ℂ) (hz : z ∈ ball (0 : ℂ) (9 / 8)) : (7 / 8 : ℝ) < (c + z).re := by
    have hn : ‖z‖ < 9 / 8 := mem_ball_zero_iff.mp hz
    have hre := (neg_le_abs z.re).trans (abs_re_le_norm z)
    dsimp [c]
    simp only [mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self]
    linarith only [hn, hre]
  have hzero : ∀ z ∈ ball (0 : ℂ) (9 / 8), f z ≠ 0 := by
    intro z hz
    exact dirichlet_seven_eighths χ (hRe z hz) (by tauto)
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
    have hratio : ‖c + z‖ / (c + z).re ≤ 2 * (|s.im| + 4) := by
      apply (div_le_iff₀ (by linarith only [hre])).mpr
      have hp := mul_le_mul_of_nonneg_left hre.le (show 0 ≤ 2 * (|s.im| + 4) by positivity)
      nlinarith only [hp, hnorm, abs_nonneg s.im]
    exact (dirichlet_L_weak_bound χ hχ (c + z) (by linarith only [hre])).trans (by
      change (q : ℝ) * (1 + ‖c + z‖ / (c + z).re) ≤ 8 * (q : ℝ) * (|s.im| + 4)
      have hp := mul_le_mul_of_nonneg_left hratio hq0
      have hp2 := mul_nonneg hq0 (abs_nonneg s.im)
      nlinarith only [hp, hq0, hp2])
  have hcenter : (1 / 2 : ℝ) ≤ ‖f 0‖ := by
    simpa only [f, add_zero, c] using dirichlet_L_at_two_lower χ s.im
  have hz : ‖s - c‖ ≤ 17 / 16 := by
    have heq : s - c = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [c]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [hs2])]
    linarith only [hs]
  have hd := numerical_logDerivative_on_disk f U hU hf hzero hbound hcenter hz
  have hident : c + (s - c) = s := by ring
  have hderiv : deriv f (s - c) = deriv χ.LFunction s := by
    have h := ((χ.differentiable_LFunction hχ (c + (s - c))).hasDerivAt).comp (s - c)
      ((hasDerivAt_const (s - c) c).add (hasDerivAt_id (s - c)))
    simpa only [f, Function.comp_def, hident, zero_add, mul_one] using h.deriv
  simpa only [hderiv, f, hident, U, show (2 : ℝ) * (8 * (q : ℝ) * (|s.im| + 4)) =
    16 * (q : ℝ) * (|s.im| + 4) by ring] using hd

#print axioms numerical_dirichlet_logDerivative_strip
end ChenEffective
