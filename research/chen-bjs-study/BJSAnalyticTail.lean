import BJSLayerQuadrature

noncomputable section
namespace ChenEffective
open Real Set MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem bjsStudy_layer_hat_step {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ t ∈ closedDomain 2 m, layer 2 m t ≤ 2*exp 2*c*sieveHat t) :
    ∀ s ∈ closedDomain 2 (m+1),
      layer 2 (m+1) s ≤ 2*exp 2*(c*(241/250 : ℝ))*sieveHat s := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  intro s hs
  have hp := (sieveHat_pos s).le
  have hs0 := closedDomain_pos (by norm_num : (1 : ℝ) < 2) hs
  let a : ℝ := max s (2 + eps (n + 2))
  let b : ℝ := 2 + ((n : ℝ) + 2)
  have heps : (eps (n + 2) : ℝ) ≤ 1 := by
    exact_mod_cast (show eps (n + 2) ≤ 1 by unfold eps; omega)
  have hb3 : 3 ≤ b := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    dsimp [b]; linarith
  by_cases hsb : b ≤ s
  · have hl : lower 2 s (n + 2) = b := by
      unfold lower
      simpa only [Nat.cast_add, Nat.cast_ofNat, b] using min_eq_right (hsb.trans (le_max_left s (2 + (eps (n + 2) : ℝ))))
    rw [layer, hl]
    change s⁻¹ * (∫ t in b..b, layer 2 (n + 1) (t - 1)) ≤ _
    rw [integral_same, mul_zero]
    positivity
  have hab : a ≤ b := max_le (le_of_not_ge hsb) (by linarith only [heps, hb3])
  have hl : lower 2 s (n + 2) = a := by
    unfold lower
    simpa only [Nat.cast_add, Nat.cast_ofNat, b, a] using min_eq_left hab
  have ha : 2 + (eps (n + 2) : ℝ) ≤ a := le_max_right _ _
  have hprev : ∀ t ∈ Icc a b, t - 1 ∈ closedDomain 2 (n + 1) := by
    intro t ht
    exact shifted_mem_previous (ha.trans ht.1)
  have hint : IntervalIntegrable (fun t => layer 2 (n + 1) (t - 1)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    apply ((regular (by norm_num : (1 : ℝ) < 2) (n + 1)).continuous).comp
      (continuous_id.sub continuous_const).continuousOn
    exact hprev
  have hhatint : IntervalIntegrable (fun t => sieveHat (t - 1)) volume a b := by
    have hi : IntervalIntegrable sieveHat volume (a - 1) (b - 1) := by
      rw [intervalIntegrable_iff, uIoc_of_le (sub_le_sub_right hab 1)]
      exact (sieveHat_integrable (a - 1)).mono_set (by intro t ht; exact ht.1)
    simpa using hi.comp_sub_right 1
  let C : ℝ := 2 * exp 2 * c
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmain : (∫ t in a..b, layer 2 (n + 1) (t - 1)) ≤
      C * (∫ t in a..b, sieveHat (t - 1)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on hab hint (hhatint.const_mul C)
    intro t ht
    simpa only [C] using hbound (t - 1) (hprev t ht)
  have htail : sieveHatTail a ≤ (241 / 250 : ℝ) * s * sieveHat s := by
    by_cases hp : eps (n + 2) = 0
    · have hs2 : 2 ≤ s := by
        have he := eps_succ_succ_add n
        have hs' := hs
        simp only [closedDomain, mem_Ici, hp, Nat.cast_zero, sub_zero] at hs'
        exact hs'
      have ha' : a = s := by simp [a, hp, max_eq_left hs2]
      rw [ha']
      exact sieveHatTail_contraction hs2
    · have hp1 : eps (n + 2) = 1 := by unfold eps at *; omega
      have hs1 : 1 ≤ s := by
        have hs' := hs
        simp only [closedDomain, mem_Ici, hp1] at hs'
        norm_num at hs'
        linarith
      have ha' : a = max s 3 := by norm_num [a, hp1]
      rw [ha']
      exact sieveHatTail_parity hs1
  have hI := (mul_le_mul_of_nonneg_left (sieve_integral_shift_hat_le_tail a b) hC)
  have hT := mul_le_mul_of_nonneg_left htail hC
  rw [layer, hl]
  change s⁻¹ * (∫ t in a..b, layer 2 (n + 1) (t - 1)) ≤ _
  have hgoal : s⁻¹ * (C * ((241 / 250 : ℝ) * s * sieveHat s)) =
      2 * exp 2 * (c * (241 / 250 : ℝ)) * sieveHat s := by
    dsimp [C]
    field_simp
  rw [← hgoal]
  exact mul_le_mul_of_nonneg_left (hmain.trans (hI.trans hT)) (inv_nonneg.mpr hs0.le)


#print axioms bjsStudy_layer_hat_step
end ChenEffective
