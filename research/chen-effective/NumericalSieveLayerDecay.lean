import NumericalSieveKernel
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteContinuousLayersKappaOne

namespace ChenEffective
open Real Set MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open KappaOneModel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private theorem integral_shift_hat_le_tail (a b : ℝ) :
    (∫ t in a..b, sieveHat (t - 1)) ≤ sieveHatTail a := by
  rw [intervalIntegral.integral_comp_sub_right]
  have hs := integral_interval_add_Ioi (sieveHat_integrable (a - 1))
    (sieveHat_integrable (b - 1))
  have hn : 0 ≤ ∫ t in Ioi (b - 1), sieveHat t := by
    apply MeasureTheory.integral_nonneg
    intro t; exact (sieveHat_pos t).le
  unfold sieveHatTail
  linarith

theorem sieve_integral_shift_hat_le_tail (a b : ℝ) :
    (∫ t in a..b, sieveHat (t - 1)) ≤ sieveHatTail a :=
  integral_shift_hat_le_tail a b

private theorem layer_base_hat {s : ℝ} (hs : s ∈ closedDomain 2 1) :
    layer 2 1 s ≤ 2 * exp 2 * sieveHat s := by
  have hs1 : 1 ≤ s := by simp only [closedDomain, mem_Ici, eps] at hs; norm_num at hs; linarith
  have hs0 : 0 < s := by linarith
  have hp := (sieveHat_pos s).le
  by_cases hs3 : 3 ≤ s
  · simp only [layer, show (2 : ℝ) + 1 = 3 by norm_num, min_eq_right hs3,
      integral_same, mul_zero]
    positivity
  have hs3' : s ≤ 3 := le_of_not_ge hs3
  have hh := mul_le_mul_of_nonneg_left (sieveHat_weighted_compact hs1 hs3')
    (show 0 ≤ 2 * exp (2 : ℝ) by positivity)
  have he : 2 * exp (2 : ℝ) * exp (-2) = 2 := by
    rw [mul_assoc, ← exp_add]; norm_num
  rw [he] at hh
  simp only [layer, show (2 : ℝ) + 1 = 3 by norm_num, min_eq_left hs3',
    intervalIntegral.integral_const, smul_eq_mul, mul_one]
  rw [← div_eq_inv_mul]
  apply (div_le_iff₀ hs0).mpr
  nlinarith only [hh, hs1]

/-- The actual source-normalized finite continuous layers, not a newly
invented scalar sequence, decay geometrically against the analytic hat.
Both closed parity endpoints are included. -/
theorem sieve_continuous_layer_decay (n : ℕ) :
    ∀ s ∈ closedDomain 2 n,
      layer 2 n s ≤ 2 * exp 2 * (241 / 250 : ℝ) ^ (n - 1) * sieveHat s := by
  induction n using Nat.twoStepInduction with
  | zero =>
    intro s _
    simp only [layer]
    have hp := (sieveHat_pos s).le
    positivity
  | one =>
    intro s hs
    have hp := (sieveHat_pos s).le
    simpa using layer_base_hat hs
  | more n _ ih =>
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
    let C : ℝ := 2 * exp 2 * (241 / 250 : ℝ) ^ n
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hmain : (∫ t in a..b, layer 2 (n + 1) (t - 1)) ≤
        C * (∫ t in a..b, sieveHat (t - 1)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply integral_mono_on hab hint (hhatint.const_mul C)
      intro t ht
      simpa only [Nat.add_sub_cancel, C] using ih (t - 1) (hprev t ht)
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
    have hI := (mul_le_mul_of_nonneg_left (integral_shift_hat_le_tail a b) hC)
    have hT := mul_le_mul_of_nonneg_left htail hC
    rw [layer, hl]
    change s⁻¹ * (∫ t in a..b, layer 2 (n + 1) (t - 1)) ≤ _
    have hgoal : s⁻¹ * (C * ((241 / 250 : ℝ) * s * sieveHat s)) =
        2 * exp 2 * (241 / 250 : ℝ) ^ ((n + 2) - 1) * sieveHat s := by
      rw [show n + 2 - 1 = n + 1 by omega, pow_succ]
      dsimp [C]
      field_simp
    rw [← hgoal]
    exact mul_le_mul_of_nonneg_left (hmain.trans (hI.trans hT)) (inv_nonneg.mpr hs0.le)

theorem actual_suzuki_layer_decay (n : ℕ) {s : ℝ} (hs : s ∈ closedDomain 2 n) :
    suzukiLayer 1 2 n s ≤ 2 * exp 2 * (241 / 250 : ℝ) ^ (n - 1) * sieveHat s := by
  rw [← layer_eq_suzukiLayer]
  exact sieve_continuous_layer_decay n s hs

#print axioms actual_suzuki_layer_decay
end ChenEffective
