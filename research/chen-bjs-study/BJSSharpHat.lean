import NumericalSieveSourceAnalytic

namespace ChenEffective
open Real Set
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
set_option maxHeartbeats 2000000

theorem bjsStudy_hat_shift (s : ℝ) : sieveHat (s - 1) ≤ (11/3 : ℝ) * sieveHat s := by
  have h2 : max 2 s ≤ max 2 (s - 1) + 1 := by
    apply max_le
    · have := le_max_left (2 : ℝ) (s - 1); linarith
    · have := le_max_right (2 : ℝ) (s - 1); linarith
  have h3 : max 3 s ≤ (4 / 3 : ℝ) * max 3 (s - 1) := by
    have hlo := le_max_left (3 : ℝ) (s - 1)
    have hh : max 3 s ≤ max 3 (s - 1) + 1 := by
      apply max_le
      · linarith
      · have := le_max_right (3 : ℝ) (s - 1); linarith
    linarith
  have hE : exp (-max 2 (s - 1)) ≤ exp 1 * exp (-max 2 s) := by
    rw [← exp_add]
    exact exp_le_exp.mpr (by linarith only [h2])
  have hR : 3 / max 3 (s - 1) ≤ (4 / 3 : ℝ) * (3 / max 3 s) := by
    have hp : 0 < max 3 (s - 1) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hq : 0 < max 3 s := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    rw [show (4 / 3 : ℝ) * (3 / max 3 s) = 4 / max 3 s by ring]
    exact (div_le_div_iff₀ hp hq).mpr (by nlinarith only [h3])
  rw [sieveHat_max_formula (s - 1), sieveHat_max_formula s]
  have hh := mul_le_mul hE hR (by positivity) (by positivity)
  have he := mul_le_mul_of_nonneg_right (show exp 1 ≤ (11/4 : ℝ) from by linarith only [Real.exp_one_lt_d9])
    (show 0 ≤ exp (-max 2 s) * (3 / max 3 s) by positivity)
  nlinarith only [hh, he]


theorem bjsStudy_hat_tail_odd {s : ℝ} (hs : 1 ≤ s) :
    sieveHatTail (max s 3) ≤ (116/125 : ℝ)*s*sieveHat s := by
  by_cases hs3 : s ≤ 3
  · rw [max_eq_right hs3]
    exact sieveHatTail_compact hs hs3
  · rw [max_eq_left (le_of_not_ge hs3)]
    have hh := sieveHatTail_contraction_high (le_of_not_ge hs3)
    have hp := mul_pos (by linarith : 0 < s) (sieveHat_pos s)
    nlinarith only [hh,hp]

theorem bjsStudy_source_hat_boundary {n : ℕ} {s : ℝ} (hs : s ∈ closedDomain 2 (n + 1)) :
    let a : ℝ := max s (2 + (eps (n + 1) : ℝ))
    (a / s) * sieveHat (a - 1) ≤ (11/3 : ℝ) * sieveHat s := by
  dsimp only
  have hs0 := closedDomain_pos (by norm_num : (1 : ℝ) < 2) hs
  by_cases hp : eps (n + 1) = 0
  · have hs2 : 2 ≤ s := by simpa only [closedDomain, mem_Ici, hp, Nat.cast_zero, sub_zero] using hs
    simp only [hp, Nat.cast_zero, add_zero, max_eq_left hs2, div_self hs0.ne', one_mul]
    exact bjsStudy_hat_shift s
  · have hp1 : eps (n + 1) = 1 := by unfold eps at *; omega
    have hs1 : 1 ≤ s := by
      have hh := hs
      norm_num only [closedDomain, mem_Ici, hp1, Nat.cast_one] at hh
      linarith
    norm_num only [hp1, Nat.cast_one, show (2 : ℝ) + 1 = 3 by norm_num]
    by_cases hs3 : 3 ≤ s
    · rw [max_eq_left hs3, div_self hs0.ne', one_mul]
      exact bjsStudy_hat_shift s
    · rw [max_eq_right (le_of_not_ge hs3)]
      have hc := sieveHat_weighted_compact hs1 (le_of_not_ge hs3)
      have he : sieveHat (3 - 1) = exp (-2) := by norm_num [sieveHat]
      rw [he]
      have hid : (3 / s) * exp (-2) = (3 * exp (-2)) / s := by ring
      rw [hid]
      apply (div_le_iff₀ hs0).mpr
      nlinarith only [hc, mul_pos hs0 (sieveHat_pos s)]


#print axioms bjsStudy_source_hat_boundary
#print axioms bjsStudy_hat_shift
#print axioms bjsStudy_hat_tail_odd
end ChenEffective
