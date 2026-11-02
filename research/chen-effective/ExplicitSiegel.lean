import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4QuadraticSmallValueRealZero
import MathlibNt.AnalyticNumberTheory.LargeSieve.LandauSiegelToStandardBVCanonicalSmoothing

/-!
One local hypothesis, matching the statement (not the `sorry` proof) in
OpenAI's ComparatorChallenges/DirichletSevenEighths.lean.
No OpenAI modules or additional packages are imported.
-/
namespace ChenEffective

open Complex DirichletCharacter
open AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4

axiom dirichlet_seven_eighths
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    χ.LFunction s ≠ 0

/-- The zeta statement follows from the same axiom at modulus one, away from
the pole; no second axiom is needed. -/
theorem zeta_ne_zero {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) (hne : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  simpa only [LFunction_modOne_eq] using
    (dirichlet_seven_eighths (1 : DirichletCharacter ℂ 1) hs (by tauto))

theorem zeta_real_im (x : ℝ) : (riemannZeta (x : ℂ)).im = 0 := by
  have h := congrArg Complex.im (riemannZeta_conj (x : ℂ))
  simp only [Complex.conj_ofReal, Complex.conj_im] at h
  linarith

/-- Propagate the known negative sign near the pole across the zero-free
real interval. The neighborhood witness is used only to prove a sign, never
as a numerical constant in the final bound. -/
theorem zeta_real_negative {ε : ℝ} (hε : 0 < ε) (hε16 : ε ≤ 1 / 16) :
    (riemannZeta ((1 - ε : ℝ) : ℂ)).re < 0 := by
  obtain ⟨ε₀, hε₀, _, hneg⟩ := exists_zeta_negative_left_neighborhood
  let δ : ℝ := min ε ε₀ / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ ≤ ε := by dsimp [δ]; linarith [min_le_left ε ε₀]
  have hδε₀ : δ ≤ ε₀ := by dsimp [δ]; linarith [min_le_right ε ε₀]
  have hb := hneg δ hδ hδε₀
  have hc : ContinuousOn (fun t : ℝ => (riemannZeta (t : ℂ)).re)
      (Set.Icc (1 - ε) (1 - δ)) := by
    intro t ht
    have ht1 : (t : ℂ) ≠ 1 := by
      have : t < 1 := by linarith [ht.2]
      exact_mod_cast (ne_of_lt this)
    exact (Complex.continuous_re.continuousAt.comp
      ((differentiableAt_riemannZeta ht1).continuousAt.comp
        Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  by_contra ha
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc' (by linarith : 1 - ε ≤ 1 - δ)
    hc ⟨hb.le, not_lt.mp ha⟩
  have ht1 : (t : ℂ) ≠ 1 := by
    exact_mod_cast (show t ≠ 1 by linarith [ht.2])
  apply zeta_ne_zero (s := (t : ℂ)) (by simp only [ofReal_re]; linarith [ht.1]) ht1
  exact Complex.ext hz (zeta_real_im t)

theorem quadratic_L_real_positive
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1)
    {ε : ℝ} (hε : 0 < ε) (hε16 : ε ≤ 1 / 16) :
    0 < (χ.LFunction ((1 - ε : ℝ) : ℂ)).re := by
  have hpos := LFunction_apply_one_re_pos_of_sq_eq_one hquad hχ
  have hc : Continuous (fun t : ℝ => (χ.LFunction (t : ℂ)).re) :=
    Complex.continuous_re.comp ((χ.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  by_contra ha
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc (by linarith : 1 - ε ≤ 1)
    hc.continuousOn ⟨not_lt.mp ha, by simpa using hpos.le⟩
  apply dirichlet_seven_eighths χ
    (s := (t : ℂ)) (by simp only [ofReal_re]; linarith [ht.1]) (by tauto)
  exact Complex.ext hz
    (LFunction_ofReal_im_eq_zero_of_sq_eq_one χ hχ hquad t (by linarith [ht.1]))

noncomputable def siegelEpsilon (η : ℝ) : ℝ := min (1 / 16) (η / 8)
noncomputable def siegelConstant (η : ℝ) : ℝ :=
  siegelEpsilon η / (4 * (648 : ℝ) ^ (4 * siegelEpsilon η))

theorem siegelConstant_pos {η : ℝ} (hη : 0 < η) : 0 < siegelConstant η := by
  have : 0 < siegelEpsilon η := lt_min (by norm_num) (by positivity)
  unfold siegelConstant
  positivity

/-- Explicit replacement for the primitive quadratic Siegel lower bound. -/
theorem explicit_quadratic_L_one_lower_bound
    {η : ℝ} (hη : 0 < η) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1) :
    siegelConstant η * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re := by
  let ε := siegelEpsilon η
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε16 : ε ≤ 1 / 16 := min_le_left _ _
  have hεη : ε ≤ η / 8 := min_le_right _ _
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hlarge : ε / (4 * (648 * (q : ℝ)) ^ (4 * ε)) < (χ.LFunction 1).re := by
    by_contra h
    have hp := IsPrimitive.re_zeta_mul_LFunction_pos_of_small_value
      χ hprim hχ hquad hε (by linarith) (not_lt.mp h)
    have hz := zeta_real_negative hε hε16
    have hL := quadratic_L_real_positive χ hχ hquad hε hε16
    have him := LFunction_ofReal_im_eq_zero_of_sq_eq_one χ hχ hquad (1 - ε)
      (by linarith)
    rw [mul_re, him, mul_zero, sub_zero] at hp
    exact (not_lt_of_ge (le_of_lt (mul_neg_of_neg_of_pos hz hL))) hp
  have hthreshold : siegelConstant η * (q : ℝ) ^ (-(4 * ε)) =
      ε / (4 * (648 * (q : ℝ)) ^ (4 * ε)) := by
    change (ε / (4 * (648 : ℝ) ^ (4 * ε))) * (q : ℝ) ^ (-(4 * ε)) = _
    simp only [Real.rpow_neg hq0.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 648) hq0.le,
      div_eq_mul_inv, mul_inv_rev]
    ring
  calc
    _ ≤ siegelConstant η * (q : ℝ) ^ (-(4 * ε)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq (by linarith))
        (siegelConstant_pos hη).le
    _ = _ := hthreshold
    _ ≤ _ := hlarge.le

theorem explicit_rawLandauSiegelLowerBound :
    AnalyticNumberTheory.LargeSieve.RawLandauSiegelLowerBound := by
  intro η hη
  exact ⟨siegelConstant η, siegelConstant_pos hη,
    fun _ _ χ hprim hquad hχ => explicit_quadratic_L_one_lower_bound hη χ hprim hχ hquad⟩

/-- Plug the explicit constant into the existing low-conductor analytic route.
This interface still hides a numerical starting point in an eventual filter. -/
theorem nonprincipal_source_from_explicit_siegel :
    AnalyticNumberTheory.LargeSieve.NonprincipalPrimitivePsiSiegelWalfiszSource := by
  open AnalyticNumberTheory.LargeSieve in
    exact nonprincipalPrimitivePsiSiegelWalfiszSource_of_rawLandauSiegelLowerBound
      explicit_rawLandauSiegelLowerBound standardBVCanonicalSmoothing_contDiff
      standardBVCanonicalSmoothing_nonneg standardBVCanonicalSmoothing_support
      standardBVCanonicalSmoothing_mass_one

/-- The existing BV contract can use the replacement without invoking the
ineffective fixed-witness Siegel theorem. This is still an asymptotic contract. -/
theorem standardBV_from_explicit_siegel :
    MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov :=
  AnalyticNumberTheory.LargeSieve.standardBombieriVinogradov_of_nonprincipalPrimitivePsi
    nonprincipal_source_from_explicit_siegel

#print axioms explicit_quadratic_L_one_lower_bound
#print axioms standardBV_from_explicit_siegel
end ChenEffective
