import NumericalSmoothing
/-! Explicit Mellin and smoothing-removal constants. Proofs adapted from
MellinCalculus and the pointwise SW source (repository Apache-2.0). -/
open Set Function Filter Complex Real MeasureTheory
namespace ChenEffective
set_option backward.isDefEq.respectTransparency false
local notation "𝓜" => mellin

 theorem mellin_bound_of_derivative
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    (D : ℝ) (hD : 0 < D) (hderiv : ∀ x ∈ Icc (1 / 2) 2, ‖deriv ν x‖ ≤ D) :
    ∀ (σ₁ : ℝ), 0 < σ₁ → ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 2 →
      ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ (6 * D) * ‖s‖⁻¹ := by
  let f := fun (x : ℝ) ↦ ‖deriv ν x‖
  let σ₂ : ℝ := 2
  let C : ℝ := D * 2 ^ σ₂ * (3 / 2)
  have mainBnd : ∀ (σ₁ : ℝ), 0 < σ₁ → ∀ (s : ℂ), σ₁ ≤ s.re → s.re ≤ 2 →
      ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
    intro σ₁ σ₁pos s hs₁ hs₂
    have s_ne_zero: s ≠ 0 := fun h ↦ by linarith [zero_re ▸ h ▸ hs₁]
    simp only [mellin, MellinOfPsi_aux diffν suppν s_ne_zero, norm_mul, smul_eq_mul, mul_comm]
    gcongr
    · simp
    calc
      _ ≤ ∫ (x : ℝ) in Ioi 0, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ = ∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ ≤ ‖∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖‖ :=
          le_abs_self _
      _ ≤ _ := ?_
    · simp_rw [norm_integral_le_integral_norm]
    · apply SetIntegral.integral_eq_integral_inter_of_support_subset_Icc
      · simp only [Function.support_abs, Function.support_mul, Function.support_ofReal]
        apply subset_trans (by apply inter_subset_left) <| Function.support_deriv_subset_Icc suppν
      · exact (Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num)
    · have := intervalIntegral.norm_integral_le_of_norm_le_const' (C := D * 2 ^ σ₂)
        (f := fun x ↦ f x * ‖(x : ℂ) ^ s‖) (a := (1 / 2 : ℝ)) ( b := 2) (by norm_num) ?_
      · simp only [Real.norm_eq_abs, norm_real, norm_mul] at this ⊢
        rwa [(by norm_num: |(2 : ℝ) - 1 / 2| = 3 / 2),
            intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at this
      · intro x hx;
        have f_bound := hderiv x hx
        have pow_bound : ‖(x : ℂ) ^ s‖ ≤ 2 ^ σ₂ := by
          rw [norm_cpow_eq_rpow_re_of_pos (by linarith [mem_Icc.mp hx])]
          have xpos : 0 ≤ x := by linarith [(mem_Icc.mp hx).1]
          have h := rpow_le_rpow xpos (mem_Icc.mp hx).2 (by linarith : 0 ≤ s.re)
          exact le_trans h <| rpow_le_rpow_of_exponent_le (by norm_num) hs₂
        rw [Real.norm_of_nonneg (by dsimp [f]; positivity)]
        exact mul_le_mul f_bound pow_bound (norm_nonneg _) hD.le
  intro σ₁ hσ₁ s hs₁ hs₂
  calc
    _ ≤ C * ‖s‖⁻¹ := mainBnd σ₁ hσ₁ s hs₁ hs₂
    _ = _ := by dsimp [C, σ₂]; norm_num only [Real.rpow_two]; ring

 theorem numerical_mellin_bound : ∀ (σ₁ : ℝ), 0 < σ₁ → ∀ s : ℂ,
    σ₁ ≤ s.re → s.re ≤ 2 →
      ‖𝓜 (fun x ↦ (numericalSmoothing x : ℂ)) s‖ ≤ 768 * ‖s‖⁻¹ := by
  simpa only [show (6 : ℝ) * 128 = 768 by norm_num] using
    mellin_bound_of_derivative numericalSmoothing_contDiff numericalSmoothing_support
      128 (by norm_num) (fun _ hx => numericalSmoothing_deriv_bound hx)

open AnalyticNumberTheory.LargeSieve
 theorem numerical_smoothed_mellin_bound : ∀ (σ₁ : ℝ), 0 < σ₁ →
    ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 2 → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖𝓜 (fun x ↦ (Smooth1 numericalSmoothing ε x : ℂ)) s‖ ≤
        768 * (ε * ‖s‖ ^ 2)⁻¹ := by
  intro σ₁ hσ s hs1 hs2 ε hε hε1
  rw [MellinOfSmooth1a numericalSmoothing_contDiff numericalSmoothing_support
    hε (lt_of_lt_of_le hσ hs1)]
  have hh1 : ε * σ₁ ≤ (ε * s).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith only [hs1, hε]
  have hh2 : (ε * s).re ≤ 2 := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith only [hs1, hs2, hε, hε1, hσ]
  calc
    ‖s⁻¹ * 𝓜 (fun x ↦ (numericalSmoothing x : ℂ)) (ε * s)‖ =
      ‖s⁻¹‖ * ‖𝓜 (fun x ↦ (numericalSmoothing x : ℂ)) (ε * s)‖ := norm_mul _ _
    _ ≤ ‖s⁻¹‖ * (768 * (ε * ‖s‖)⁻¹) := by
      gcongr
      convert! numerical_mellin_bound (ε * σ₁) (by positivity) (ε * s) hh1 hh2 using 1
      simp [abs_eq_self.mpr hε.le]
    _ = 768 * (ε * ‖s‖ ^ 2)⁻¹ := by
      simp only [norm_inv, mul_inv_rev]
      ring
theorem numerical_smoothing_removal
    {SmoothingF : ℝ → ℝ} (_diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      (X : ℝ), 3 < X → ∀ (ε : ℝ), 0 < ε → ε < 1 → 2 < X * ε →
      ‖DirichletCharacter.twistedSmoothedPsi χ SmoothingF ε X -
        lambdaCharacterPrefix ⌊X⌋₊ q χ‖ ≤ 60 * ε * X * Real.log X := by
  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ :=
    Smooth1Properties_below suppSmoothingF mass_one
  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ :=
    Smooth1Properties_above suppSmoothingF
  have c₁_lt : c₁ < 1 := by
    rw [c₁_eq]
    exact lt_trans Real.log_two_lt_d9 (by norm_num)
  have c₂_lt : c₂ < 2 := by
    rw [c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    · rfl
    · exact lt_trans Real.log_two_lt_d9 (by norm_num)
    · exact Real.log_nonneg (by norm_num)
    · positivity
  let C₀ : ℝ := 6 * (3 * c₁ + c₂)
  have C₀_pos : 0 < C₀ := by dsimp [C₀]; positivity
  intro q _ χ X X_gt_three ε ε_pos ε_lt_one Xε_gt_two
  have X_pos : 0 < X := by linarith
  have n_div_X_pos {n : ℕ} (hn : 0 < n) : 0 < (n : ℝ) / X := by positivity
  have smoothAbove (n : ℕ) (hn : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one ε_pos (n_div_X_pos hn)
  have smoothBelow (n : ℕ) (hn : 0 < n) :
      0 ≤ Smooth1 SmoothingF ε (n / X) :=
    Smooth1Nonneg SmoothingFnonneg (n_div_X_pos hn) ε_pos
  have smoothOne (n : ℕ) (hn : 0 < n)
      (hnle : (n : ℝ) ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) ε_pos (n_div_X_pos hn)
    exact (div_le_iff₀' X_pos).mpr hnle
  have smoothZero (n : ℕ)
      (hn : 1 + c₂ * ε ≤ (n : ℝ) / X) :
      Smooth1 SmoothingF ε (n / X) = 0 :=
    hc₂ (ε := ε) (n / X) ⟨ε_pos, ε_lt_one⟩ hn
  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw [c₁_eq, ← div_le_iff₀]
    · have h : 1 / Real.log 2 < 2 := by
        nth_rewrite 2 [← one_div_one_div 2]
        rw [one_div_lt_one_div]
        · exact lt_of_le_of_lt (by norm_num) Real.log_two_gt_d9
        · exact Real.log_pos (by norm_num)
        · norm_num
      exact le_of_lt (h.trans Xε_gt_two)
    · exact Real.log_pos (by norm_num)
  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw [c₂_eq, ← div_le_iff₀]
    · have h : 1 / (2 * Real.log 2) < 2 := by
        nth_rewrite 3 [← one_div_one_div 2]
        rw [one_div_lt_one_div, ← one_mul (1 / 2)]
        · apply mul_lt_mul
          · norm_num
          · exact le_of_lt (lt_trans (by norm_num) Real.log_two_gt_d9)
          · norm_num
          · norm_num
        · norm_num
          exact Real.log_pos (by norm_num)
        · norm_num
      exact le_of_lt (h.trans Xε_gt_two)
    · norm_num
      exact Real.log_pos (by norm_num)
  have haux := DirichletCharacter.twistedSmoothedPsiClose_aux
    SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C₀ rfl
    ε ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2
    smoothAbove smoothBelow smoothOne smoothZero χ

  have hlog : 0 < Real.log X := Real.log_pos (by linarith only [X_gt_three])
  exact haux.trans (by
    gcongr
    linarith only [c₁_lt, c₂_lt])

#print axioms numerical_mellin_bound
#print axioms numerical_smoothed_mellin_bound
#print axioms numerical_smoothing_removal
end ChenEffective
