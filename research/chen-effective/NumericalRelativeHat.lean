import NumericalHatComparison

open scoped Classical BigOperators Interval
namespace ChenEffective
open Real Set
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem relative_hat_initial_eq {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {u : ℝ} (hu : 0 < u) (hut : u ≤ 2 + sign.epsilon) :
    weightedHat H sign u = weightedHat H sign (2 + sign.epsilon) := by
  cases sign with
  | plus =>
    norm_num only [ErrorSign.epsilon] at hut ⊢
    rw [hH.initial_plus u hu (by linarith only [hut]), hH.initial_plus 3 (by norm_num) (by norm_num)]
  | minus =>
    norm_num only [ErrorSign.epsilon] at hut ⊢
    rw [hH.initial_minus u hu hut, hH.initial_minus 2 (by norm_num) (by norm_num)]

theorem relative_weighted_hat_antitone {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    weightedHat H sign b ≤ weightedHat H sign a := by
  have ht : 0 < 2 + sign.epsilon := by cases sign <;> norm_num [ErrorSign.epsilon]
  by_cases hb : b ≤ 2 + sign.epsilon
  · rw [relative_hat_initial_eq hH sign (ha.trans_le hab) hb,
      relative_hat_initial_eq hH sign ha (hab.trans hb)]
  · by_cases ha' : a ≤ 2 + sign.epsilon
    · rw [relative_hat_initial_eq hH sign ha ha']
      exact weightedHat_antitoneOn_Icc_closed hH sign (s := 2 + sign.epsilon) (M := b) le_rfl
        ⟨le_rfl, (le_of_not_ge hb)⟩ ⟨le_of_not_ge hb, le_rfl⟩ (le_of_not_ge hb)
    · exact weightedHat_antitoneOn_Icc_closed hH sign (s := a) (M := b) (le_of_not_ge ha')
        ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- The lower endpoint is a neighbouring value, not an absolute hat floor. -/
theorem relative_hat_half_step {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {s : ℝ} (hs : 3 < s) (hs10 : s ≤ 10) :
    weightedHat H sign.opposite (s - 1 / 2) / 22 ≤ weightedHat H sign s := by
  simpa only [show (2 : ℝ) * (10 + 1) = 22 by norm_num] using numerical_hat_half_step hH sign
    (by cases sign <;> simp only [ErrorSign.epsilon] <;> linarith only [hs])
    (by linarith only [hs]) hs10 (by
      intro u hu
      exact relative_weighted_hat_antitone hH sign.opposite
        (by linarith only [hu.1, hs]) hu.2)

theorem relative_hat_unit_step {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {s : ℝ} (hs : 4 ≤ s) (hs10 : s ≤ 10) :
    weightedHat H sign (s - 1) ≤ 484 * weightedHat H sign s := by
  have h₁ := relative_hat_half_step hH sign (by linarith only [hs]) hs10
  have h₂ := relative_hat_half_step hH sign.opposite
    (s := s - 1 / 2) (by linarith only [hs]) (by linarith only [hs10])
  have hop : sign.opposite.opposite = sign := by cases sign <;> rfl
  rw [hop, show s - 1 / 2 - 1 / 2 = s - 1 by ring] at h₂
  linarith only [h₁, h₂]

theorem relative_Qhat_unit_step {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {s : ℝ} (hs : 4 ≤ s) (hs10 : s ≤ 10) :
    section13Qhat H (s - 1) ≤ 968 * section13Qhat H s := by
  have hp := relative_hat_unit_step hH .plus hs hs10
  have hm := relative_hat_unit_step hH .minus hs hs10
  have hQ0 : 0 ≤ section13Qhat H s :=
    (section13Qhat_pos hH (by linarith only [hs])).le
  have hsq : s ^ 2 ≤ 2 * (s - 1) ^ 2 := by nlinarith only [hs, sq_nonneg (s - 4)]
  have hmul := mul_le_mul_of_nonneg_right hsq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 484) hQ0)
  have hsum : (s - 1) ^ 2 * section13Qhat H (s - 1) ≤ 484 * s ^ 2 * section13Qhat H s := by
    dsimp [weightedHat] at hp hm
    unfold section13Qhat
    nlinarith only [hp, hm]
  have hfactor : 0 < (s - 1) ^ 2 := sq_pos_of_pos (by linarith only [hs])
  apply le_of_mul_le_mul_left (a := (s - 1) ^ 2) _ hfactor
  nlinarith only [hsum, hmul]

theorem relative_Qhat_initial_ratio {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {s : ℝ} (hs : s ∈ Icc (3 : ℝ) 10) :
    section13Qhat H (s - 1) / (s * section13Qhat H s) ≤ 10000 := by
  have hs0 : 0 < s := by linarith only [hs.1]
  have hQ0 := section13Qhat_pos hH hs0
  apply (div_le_iff₀ (mul_pos hs0 hQ0)).mpr
  by_cases hs4 : 4 ≤ s
  · have hh := relative_Qhat_unit_step hH hs4 hs.2
    have hh' := mul_le_mul_of_nonneg_right hs.1 hQ0.le
    nlinarith only [hh, hh', hQ0.le]
  · have hp := numerical_hat_compact_four hH .plus (by linarith only [hs.1]) (le_of_not_ge hs4)
    have hm := numerical_hat_compact_four hH .minus (by linarith only [hs.1]) (le_of_not_ge hs4)
    have hpp := numerical_hat_upper_two hH .plus (s := s - 1) (by linarith only [hs.1])
    have hmp := numerical_hat_upper_two hH .minus (s := s - 1) (by linarith only [hs.1])
    have hlo : (1 / 6400 : ℝ) ≤ section13Qhat H s := by unfold section13Qhat; linarith only [hp, hm]
    have hhi : section13Qhat H (s - 1) ≤ 4 := by unfold section13Qhat; linarith only [hpp, hmp]
    have hh := mul_le_mul_of_nonneg_right hs.1 hQ0.le
    nlinarith only [hlo, hhi, hh]

#print axioms relative_Qhat_initial_ratio
end ChenEffective
