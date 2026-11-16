import PlattContourDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Polynomial-decay Mellin inversion and the prime-series vertical integral.
Proof adaptations from calr3 ExplicitFormula at the pinned source revision;
original licenses are retained in Calr3. No new prime bound is assumed here. -/
noncomputable section
namespace ChenEffective.PlattWindow.ContourDecay
open Complex MeasureTheory Set Filter Metric TernaryGoldbach.Explicit
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure PolynomialSmoothing (φ : ℝ → ℂ) (K : ℝ) : Prop where
  continuousAt : ∀ y : ℝ, 0 < y → ContinuousAt φ y
  conv : MellinConvergent φ ((3/2:ℝ):ℂ)
  diff : ∀ s : ℂ, -1 < s.re → DifferentiableAt ℂ (mellin φ) s
  strip : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 3/2 →
    ‖mellin φ s‖ ≤ K/(1+|s.im|)^2

theorem PolynomialSmoothing.K_nonneg {φ : ℝ → ℂ} {K : ℝ} (hφ : PolynomialSmoothing φ K) :
    0 ≤ K := by
  have h := hφ.strip 0 (by norm_num) (by norm_num)
  norm_num at h
  exact (norm_nonneg _).trans h

theorem PolynomialSmoothing.continuous_line {φ : ℝ → ℂ} {K : ℝ} (hφ : PolynomialSmoothing φ K)
    {σ : ℝ} (hσ : -1 < σ) : Continuous fun t : ℝ => mellin φ ((σ:ℂ)+t*I) :=
  continuous_iff_continuousAt.mpr fun t =>
    ((hφ.diff _ (by simpa using hσ)).continuousAt).comp (by fun_prop)

theorem PolynomialSmoothing.integrable_line {φ : ℝ → ℂ} {K : ℝ} (hφ : PolynomialSmoothing φ K)
    {σ : ℝ} (h1 : -1/2 ≤ σ) (h2 : σ ≤ 3/2) :
    Integrable fun t : ℝ => mellin φ ((σ:ℂ)+t*I) := by
  have hK := hφ.K_nonneg
  refine (integrable_inv_one_add_sq.const_mul K).mono'
    (hφ.continuous_line (by linarith only [h1])).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have h := hφ.strip ((σ:ℂ)+t*I) (by simpa using h1) (by simpa using h2)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at h
  apply h.trans
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ hK
  apply inv_anti₀ (by positivity)
  have ht := abs_nonneg t
  nlinarith only [sq_abs t,ht]

theorem PolynomialSmoothing.eq_mellinInv {φ : ℝ → ℂ} {K : ℝ} (hφ : PolynomialSmoothing φ K) {y : ℝ}
    (hy : 0 < y) :
    φ y = (1 / (2 * π)) • ∫ t : ℝ, (y : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * I)) •
      mellin φ (((3 / 2 : ℝ) : ℂ) + t * I) := by
  have hvert : Complex.VerticalIntegrable (mellin φ) (3 / 2) := by
    rw [Complex.VerticalIntegrable]
    exact hφ.integrable_line (σ := 3 / 2) (by norm_num) le_rfl
  have h := mellinInv_mellin_eq (3 / 2) φ hy hφ.conv hvert (hφ.continuousAt y hy)
  rw [← h, mellinInv]


theorem eq_integral_Fterm {φ : ℝ → ℂ} {K : ℝ} (hφ : PolynomialSmoothing φ K) {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : 0 < n) : φ (n / x) = (1 / (2 * π) : ℂ) * ∫ t, Fterm φ x n t := by
  rw [hφ.eq_mellinInv (by positivity : (0:ℝ) < n / x), Complex.real_smul]
  congr 1
  push_cast; ring

theorem integrable_Fterm {φ : ℝ → ℂ} {K : ℝ} (hφ : PolynomialSmoothing φ K) {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : 0 < n) : Integrable (Fterm φ x n) := by
  have hGi := hφ.integrable_line (σ := 3 / 2) (by norm_num) le_rfl
  have hGc := hφ.continuous_line (σ := 3 / 2) (by norm_num)
  refine (hGi.norm.const_mul (((n : ℝ) / x) ^ (-(3 / 2 : ℝ)))).mono' ?_ (Eventually.of_forall fun t => ?_)
  · refine (Continuous.mul ?_ hGc).aestronglyMeasurable
    refine continuous_iff_continuousAt.2 fun t => ?_
    exact (continuousAt_const_cpow (Complex.ofReal_ne_zero.2
      (by positivity : (0:ℝ) < n / x).ne')).comp (by fun_prop)
  · rw [Fterm, norm_mul, norm_ratio_cpow hn hx]


theorem SsumG_eq_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {φ : ℝ → ℂ} {K : ℝ}
    (hφ : PolynomialSmoothing φ K) {x : ℝ} (hx : 0 < x) :
    SsumG χ φ x = (1 / (2 * π) : ℂ) * ∫ t : ℝ, Fline χ φ x (((3 / 2 : ℝ) : ℂ) + t * I) := by
  set F : ℕ → ℝ → ℂ := fun n t => (Λ n : ℂ) * χ n * Fterm φ x n t with hF
  have hterm : ∀ n : ℕ, (Λ n : ℂ) * χ n * φ (n / x) = (1 / (2 * π) : ℂ) * ∫ t, F n t := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF]
    · rw [eq_integral_Fterm hφ hx hn, hF]
      simp only
      rw [integral_const_mul]; ring
  have hFi : ∀ n, Integrable (F n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : F 0 = fun _ => 0 := by ext t; simp [hF]
      rw [this]; exact integrable_zero _ _ _
    · exact (integrable_Fterm hφ hx hn).const_mul _
  have hFs : Summable fun n => ∫ t, ‖F n t‖ := by
    have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num)
    have hΛ' : Summable fun n : ℕ => Λ n * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      refine hΛ.norm.congr fun n => ?_
      rw [LSeries.norm_term_eq]
      split_ifs with h0
      · simp [h0]
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
        simp
    refine (hΛ'.mul_right (x ^ (3 / 2 : ℝ) * ∫ t : ℝ, ‖mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)‖)).of_nonneg_of_le
      (fun n => integral_nonneg fun t => norm_nonneg _) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF]
    · have e : ∀ t, ‖F n t‖ = (Λ n * ‖χ n‖) * ‖Fterm φ x n t‖ := by
        intro t
        rw [hF]; simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      simp_rw [e]
      rw [integral_const_mul, integral_norm_Fterm φ hx hn]
      have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
      have hG0 : 0 ≤ ∫ t : ℝ, ‖mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ :=
        integral_nonneg fun t => norm_nonneg _
      have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have hn0 : 0 ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) := by positivity
      calc Λ n * ‖χ n‖ * ((n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) *
            ∫ t : ℝ, ‖mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)‖)
          ≤ Λ n * 1 * ((n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) *
            ∫ t : ℝ, ‖mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)‖) := by gcongr
        _ = Λ n * (n : ℝ) ^ (-(3 / 2 : ℝ)) * (x ^ (3 / 2 : ℝ) *
            ∫ t : ℝ, ‖mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)‖) := by ring
  rw [SsumG, tsum_congr hterm, tsum_mul_left, integral_tsum_of_summable_integral_norm hFi hFs]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  exact tsum_Fterm_eq χ φ hx t

/-! ## Part B: no zeros in `−1 < ℜs < 0`, and the rectangle identity -/

theorem gammaFactor_ne_zero_strip {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ} (h1 : -1 < z.re)
    (h2 : z.re < 0) : DirichletCharacter.gammaFactor χ z ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def, Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at this; linarith
    · have : (1:ℝ) ≤ n := by exact_mod_cast hpos
      linarith
  · rw [ho.gammaFactor_def, Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at this; linarith
    · have : (1:ℝ) ≤ n := by exact_mod_cast hpos
      linarith


#print axioms PolynomialSmoothing.eq_mellinInv
#print axioms SsumG_eq_line
end ChenEffective.PlattWindow.ContourDecay
