import NumericalMixedObjects

open scoped Classical BigOperators Interval
namespace ChenEffective
variable [profile : CorrectionProfile]
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiLemma144KappaOne SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

@[irreducible] def mixedEndpointC1 : ℕ := caseIOrderC1 (2 + 600 * reverseRatioCap)

omit profile in
theorem mixedEndpointC1_one : (1 : ℝ) ≤ mixedEndpointC1 := by
  unfold mixedEndpointC1 caseIOrderC1
  exact real_nat_three_pow_one _

omit profile in
theorem mixedEndpointC1_gate : logPowerCutoff 32 ≤ mixedEndpointC1 := by
  unfold logPowerCutoff mixedEndpointC1 caseIOrderC1
  apply Nat.pow_le_pow_right (by norm_num : 0 < 3)
  norm_num [reverseRatioCap_nat_eq]

omit profile in
theorem mixedEndpointC1_eq : mixedEndpointC1 = 3 ^ (2400 * reverseRatioCap + 9) := by
  unfold mixedEndpointC1 caseIOrderC1
  apply congrArg (fun n : ℕ => 3 ^ n)
  ring

omit profile in
theorem mixedEndpointC1_budget : (mixedEndpointC1 : ℝ) ≤ Real.exp (10 ^ 15 : ℝ) := by
  have hn : 2400 * reverseRatioCap + 9 ≤ 10 ^ 13 := by norm_num [reverseRatioCap_nat_eq]
  have hnR : ((2400 * reverseRatioCap + 9 : ℕ) : ℝ) ≤ 10 ^ 13 := by exact_mod_cast hn
  have h3 : Real.log (3 : ℝ) ≤ 2 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  rw [mixedEndpointC1_eq, Nat.cast_pow, Nat.cast_ofNat]
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  rw [Real.log_pow]
  change ((2400 * reverseRatioCap + 9 : ℕ) : ℝ) * Real.log 3 ≤ (10 ^ 15 : ℝ)
  have hh := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg (2400 * reverseRatioCap + 9))
  nlinarith only [hh, hnR]

noncomputable def mixedStrictC1 : ℝ := max 1 (max (mixedEndpointC1 : ℝ)
  (max (caseIScalarC1 : ℝ) (max sigmaZeroC1 (max 1 (Real.log caseIStrictDcut)))))
noncomputable def mixedEvenC1 : ℝ := max 1 (max (mixedEndpointC1 : ℝ)
  (max (caseIScalarC1 : ℝ) (max sigmaZeroC1 (max 1 (Real.log caseIEvenDcut)))))
noncomputable def mixedSuzukiSeparator : ℝ := max numericalSuzukiC1 (mixedEndpointC1 : ℝ)

omit profile in
theorem mixed_endpoint_order_uniform (C1 K D A : ℝ)
    (hC1 : (mixedEndpointC1 : ℝ) ≤ C1) (hK : 2 ≤ K) (hD : 2 ≤ D)
    (_hA : 0 ≤ A) (hAcap : A ≤ 1 + 2 * 144 * (reverseRatioCap : ℝ) + 12 * (reverseRatioCap : ℝ))
    (hlarge : C1 * K ^ (7 : ℝ) < Real.log D) :
    ∃ q : Lemma144StrictFactor,
      q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma D 16) (1 / 2)) / 2 ∧
      caseISourceOrderCoefficient A D 16 ≤ (1 - q.ρ) / 2 := by
  have ha : 2 * A ≤ ((2 + 600 * reverseRatioCap : ℕ) : ℝ) := by
    push_cast
    linarith only [hAcap]
  unfold mixedEndpointC1 at hC1
  obtain ⟨q, hq, hh⟩ := numerical_caseI_order_gap (a := 2 + 600 * reverseRatioCap) ha hC1 hK hD hlarge
  refine ⟨q, hq, ?_⟩
  unfold caseISourceOrderCoefficient at hh ⊢
  rw [mul_div_assoc] at hh
  linarith only [hh]

omit profile in
theorem mixed_three_remainders_half_gap
    {x₀ x₁ x₂ a₀ a₁ a₂ B D d ρ : ℝ} (hB : 0 ≤ B)
    (h₀ : x₀ ≤ a₀ * caseI1423RemainderUnit B D (sourceSigma D d))
    (h₁ : x₁ ≤ a₁ * caseI1423RemainderUnit B D (sourceSigma D d))
    (h₂ : x₂ ≤ a₂ * caseI1423RemainderUnit B D (sourceSigma D d))
    (hgap : caseISourceOrderCoefficient (a₀ + a₁ + a₂) D d ≤ (1 - ρ) / 2) :
    x₀ + x₁ + x₂ ≤ ((1 - ρ) / 2) * B := by
  calc
    _ ≤ (a₀ + a₁ + a₂) * caseI1423RemainderUnit B D (sourceSigma D d) := by linarith
    _ = caseISourceOrderCoefficient (a₀ + a₁ + a₂) D d * B := by
      unfold caseI1423RemainderUnit caseISourceOrderCoefficient
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hgap hB

omit profile in
theorem mixed_caseI_gap_lower {σ ρ : ℝ} (hσ : 1 < σ)
    (hρ : ρ = (1 + sigma12ContractionMultiplier σ (1 / 2)) / 2) :
    1 / (4 * σ) ≤ 1 - ρ := by
  obtain ⟨q, hq, hh⟩ := caseI_midpoint_gap_lower
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hσ
  rw [hq, ← hρ] at hh
  convert hh using 1
  ring

omit profile in
theorem mixed_gap_arithmetic {B P extra side σ ρ : ℝ}
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hσ : 2 ≤ σ)
    (hgap : 1 / (4 * σ) ≤ 1 - ρ)
    (hside : side ≤ ((1 - ρ) / 2) * B)
    (hextra : (16 ≤ σ ∧ extra ≤ (11 / 12 : ℝ) * P) ∨ extra ≤ B / (100 * σ)) :
    ρ * B + side + extra ≤ (1 - 1 / (10 * σ)) * (B + P) := by
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hbase : ρ * B + side ≤ (1 - 1 / (8 * σ)) * B := by
    have hh := mul_le_mul_of_nonneg_right hgap hB
    have heq : (1 / (4 * σ)) * B / 2 = (1 / (8 * σ)) * B := by ring
    nlinarith only [hside, hh, heq]
  have hr0 : 0 ≤ 1 - 1 / (10 * σ) := by
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity : 0 < 10 * σ)).mpr
    linarith only [hσ]
  rcases hextra with ⟨h16, he⟩ | he
  · have hr : (11 / 12 : ℝ) ≤ 1 - 1 / (10 * σ) := by
      apply (le_sub_iff_add_le).mpr
      have hh : 1 / (10 * σ) ≤ 1 / 12 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith only [h16])
      linarith only [hh]
    have hless : 1 - 1 / (8 * σ) ≤ 1 - 1 / (10 * σ) := by
      have hh := one_div_le_one_div_of_le (by positivity : 0 < 8 * σ)
        (show 8 * σ ≤ 10 * σ by linarith only [hσ0])
      linarith only [hh]
    nlinarith only [hbase, he, mul_le_mul_of_nonneg_right hr hP,
      mul_le_mul_of_nonneg_right hless hB]
  · have hmargin : (1 - 1 / (8 * σ)) + 1 / (100 * σ) ≤ 1 - 1 / (10 * σ) := by
      field_simp
      linarith only [hσ0]
    have hh := mul_le_mul_of_nonneg_right hmargin hB
    have hp := mul_nonneg hr0 hP
    have he' : extra ≤ (1 / (100 * σ)) * B := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using he
    nlinarith only [hbase, he', hh, hp]

omit profile in
theorem mixed_polynomial_coarse
    {S : BoundingSieve} {D z : ℕ} {w s σ K : ℝ}
    (hD : 1 < (D : ℝ)) (hz2 : 2 ≤ (D : ℝ) ^ (1 / s)) (hw2 : 2 ≤ w)
    (hwz : w ≤ (D : ℝ) ^ (1 / s)) (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hw : w = (D : ℝ) ^ (1 / σ)) (hs : 2 ≤ s) (hsσ : s ≤ σ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hlevel : 288 * K ^ 2 ≤ Real.log w) :
    polynomialInheritedSum S D z σ s ≤ (3 / 8 : ℝ) * (Real.log (D : ℝ)) ^ (-(5 / 8 : ℝ)) := by
  apply (polynomialInheritedSum_le_prime_sum S hD hs le_rfl hz rfl hw).trans
  have hh := mul_le_mul_of_nonneg_left
    (numerical_polynomial_transport_coarse hD hz2 hw2 hwz rfl hw hs hsσ hK hlocal hlevel)
    (Real.rpow_nonneg (Real.log_pos hD).le (-(5 / 8 : ℝ)))
  simpa only [mul_comm] using hh

#print axioms mixed_endpoint_order_uniform
#print axioms mixed_gap_arithmetic
end ChenEffective
