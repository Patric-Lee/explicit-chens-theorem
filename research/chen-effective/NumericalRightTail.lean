import NumericalMellin
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedSmoothedRightTailQuantitative

open Set Function Filter Complex Real MeasureTheory
namespace DirichletCharacter
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
private theorem integral_right_inv_one_add_sq_le_inv
    {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in Ici T, (1 + t ^ 2)⁻¹ ≤ T⁻¹ := by
  rw [integral_Ici_eq_integral_Ioi]
  have hmono : ∀ᵐ t ∂volume.restrict (Ioi T),
      (1 + t ^ 2)⁻¹ ≤ t ^ (-2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := (lt_of_lt_of_le zero_lt_one hT).trans ht
    rw [Real.rpow_neg (le_of_lt ht0), Real.rpow_two]
    exact inv_anti₀ (sq_pos_of_pos ht0) (by nlinarith)
  calc
    ∫ t in Ioi T, (1 + t ^ 2)⁻¹ ≤ ∫ t in Ioi T, t ^ (-2 : ℝ) := by
      refine integral_mono_ae integrable_inv_one_add_sq.integrableOn
        (integrableOn_Ioi_rpow_of_lt (by norm_num) (lt_of_lt_of_le zero_lt_one hT)) hmono
    _ = T⁻¹ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) (lt_of_lt_of_le zero_lt_one hT)]
      norm_num [Real.rpow_neg_one]

private theorem integral_left_inv_one_add_sq_le_inv
    {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in Iic (-T), (1 + t ^ 2)⁻¹ ≤ T⁻¹ := by
  calc
    ∫ t in Iic (-T), (1 + t ^ 2)⁻¹ =
        ∫ t in Ioi T, (1 + t ^ 2)⁻¹ := by
          rw [integral_Iic_inv_one_add_sq, integral_Ioi_inv_one_add_sq,
            Real.arctan_neg]
          ring
    _ ≤ T⁻¹ := by
      simpa [integral_Ici_eq_integral_Ioi] using
        integral_right_inv_one_add_sq_le_inv hT


local notation "𝓜" => mellin
theorem twistedSmoothedPerron_right_tails_of_mellin_bound
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    (C : ℝ) (Cpos : 0 < C)
    (hC : ∀ σ₁ : ℝ, 0 < σ₁ → ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 2 →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹) :
    ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {δ ε X T : ℝ}, 0 < δ → δ ≤ 1 → 0 < ε → ε < 1 → 0 < X → 1 ≤ T →
      ‖∫ t in Iic (-T),
          twistedSmoothedPerronIntegrand χ ν ε X (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤
          (6 * C) * X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) ∧
      ‖∫ t in Ici T,
          twistedSmoothedPerronIntegrand χ ν ε X (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤
          (6 * C) * X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) := by
  intro q _ χ δ ε X T hδ hδ1 hε hε1 hX hT
  have hσ : 1 < 1 + δ := by linarith
  have hσ2 : 1 + δ ≤ 2 := by linarith
  let f : ℝ → ℂ := fun t =>
    twistedSmoothedPerronIntegrand χ ν ε X (((1 + δ : ℝ) : ℂ) + t * I)
  let g : ℝ → ℝ := fun t =>
    6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ) * (1 + t ^ 2)⁻¹
  have hf : Integrable f := by
    simpa only [f] using
      (twistedSmoothedPerronIntegrand_integrable_right (q := q) (σ := 1 + δ)
        (X := X) (ε := ε) χ diffν νpos suppν mass_one hX hε hε1 hσ hσ2)
  have hg : Integrable g := by
    dsimp [g]
    exact integrable_inv_one_add_sq.const_mul _
  have hpoint (t : ℝ) : ‖f t‖ ≤ g t := by
    have hsre : 1 < (((1 + δ : ℝ) : ℂ) + t * I).re := by simp; linarith
    have hsum : Summable (fun n : ℕ =>
        twistedVonMangoldtCoeff χ n /
          (n : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)) := by
      have h := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hsre
      rw [LSeriesSummable] at h
      convert h using 1
      ext n
      by_cases hn : n = 0
      · simp [LSeries.term, twistedVonMangoldtCoeff, hn]
      · simp [LSeries.term, twistedVonMangoldtCoeff, hn, mul_comm]
    have hseries := norm_tsum_le_tsum_norm hsum.norm
    have hmellin := hC ((1 + δ) / 2) (by positivity)
      (((1 + δ : ℝ) : ℂ) + t * I) (by simp; linarith) (by simp; linarith)
      ε hε hε1
    have hmaj := twistedVonMangoldtRightMajorant_le χ hδ hδ1 t
    dsimp [f, g, twistedSmoothedPerronIntegrand]
    rw [neg_logDeriv_LFunction_eq_tsum_twistedVonMangoldtCoeff χ hsre,
      norm_mul, norm_mul]
    have hseries' :
        ‖∑' n : ℕ, twistedVonMangoldtCoeff χ n /
          (n : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤
          twistedVonMangoldtRightMajorant χ δ t := by
      simpa [twistedVonMangoldtRightMajorant] using hseries
    have hmajor0 : 0 ≤ twistedVonMangoldtRightMajorant χ δ t :=
      tsum_nonneg fun _ => norm_nonneg _
    have hmellinR0 :
        0 ≤ C * (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹ := by positivity
    have hXnorm :
        ‖(X : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖ = X ^ (1 + δ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
      simp
    have hXpow0 : 0 ≤ X ^ (1 + δ) := Real.rpow_nonneg hX.le _
    have hfirst :
        ‖∑' n : ℕ, twistedVonMangoldtCoeff χ n /
          (n : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤
          twistedVonMangoldtRightMajorant χ δ t *
            (C * (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹) := by
      calc
        _ ≤ twistedVonMangoldtRightMajorant χ δ t *
            ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (((1 + δ : ℝ) : ℂ) + t * I)‖ :=
          mul_le_mul_of_nonneg_right hseries' (norm_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hmellin hmajor0
    have hnormsq : 1 + t ^ 2 ≤ ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      nlinarith
    have hinvnorm :
        (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹ ≤
          ε⁻¹ * (1 + t ^ 2)⁻¹ := by
      rw [mul_inv_rev]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right
        (inv_anti₀ (by nlinarith [sq_nonneg t]) hnormsq) (inv_nonneg.mpr hε.le)
    calc
      ‖∑' n : ℕ, twistedVonMangoldtCoeff χ n /
          (n : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (((1 + δ : ℝ) : ℂ) + t * I)‖ *
              ‖(X : ℂ) ^ (((1 + δ : ℝ) : ℂ) + t * I)‖
          ≤ (twistedVonMangoldtRightMajorant χ δ t *
            (C * (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹)) *
              X ^ (1 + δ) := by rw [← hXnorm]; gcongr
      _ ≤ (6 * (1 + δ⁻¹ ^ 2) *
            (C * (ε * ‖(((1 + δ : ℝ) : ℂ) + t * I)‖ ^ 2)⁻¹)) *
              X ^ (1 + δ) := by
                gcongr
      _ ≤ (6 * (1 + δ⁻¹ ^ 2) * (C * (ε⁻¹ * (1 + t ^ 2)⁻¹))) *
              X ^ (1 + δ) := by
                gcongr
      _ = 6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ) * (1 + t ^ 2)⁻¹ := by
        ring
  have htail (s : Set ℝ)
      (hdecay : ∫ t in s, (1 + t ^ 2)⁻¹ ≤ T⁻¹) :
      ‖∫ t in s, f t‖ ≤ 6 * C * X ^ (1 + δ) * (1 + δ⁻¹ ^ 2) / (ε * T) := by
    calc
      ‖∫ t in s, f t‖ ≤ ∫ t in s, ‖f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in s, g t :=
        integral_mono_ae hf.norm.integrableOn hg.integrableOn (Filter.Eventually.of_forall hpoint)
      _ = (6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ)) *
          ∫ t in s, (1 + t ^ 2)⁻¹ := by
        dsimp only [g]
        rw [integral_const_mul]
      _ ≤ (6 * (1 + δ⁻¹ ^ 2) * C / ε * X ^ (1 + δ)) * T⁻¹ :=
        mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = _ := by ring
  exact ⟨htail (Iic (-T)) (integral_left_inv_one_add_sq_le_inv hT),
    htail (Ici T) (integral_right_inv_one_add_sq_le_inv hT)⟩

end DirichletCharacter
