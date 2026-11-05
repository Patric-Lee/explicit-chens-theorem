import NumericalSieveSourceGeometry

namespace ChenEffective
open Real Set MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem source_hat_boundary {n : ℕ} {s : ℝ} (hs : s ∈ closedDomain 2 (n + 1)) :
    let a : ℝ := max s (2 + (eps (n + 1) : ℝ))
    (a / s) * sieveHat (a - 1) ≤ 4 * sieveHat s := by
  dsimp only
  have hs0 := closedDomain_pos (by norm_num : (1 : ℝ) < 2) hs
  by_cases hp : eps (n + 1) = 0
  · have hs2 : 2 ≤ s := by simpa only [closedDomain, mem_Ici, hp, Nat.cast_zero, sub_zero] using hs
    simp only [hp, Nat.cast_zero, add_zero, max_eq_left hs2, div_self hs0.ne', one_mul]
    exact sieveHat_shift s
  · have hp1 : eps (n + 1) = 1 := by unfold eps at *; omega
    have hs1 : 1 ≤ s := by
      have hh := hs
      norm_num only [closedDomain, mem_Ici, hp1, Nat.cast_one] at hh
      linarith
    norm_num only [hp1, Nat.cast_one, show (2 : ℝ) + 1 = 3 by norm_num]
    by_cases hs3 : 3 ≤ s
    · rw [max_eq_left hs3, div_self hs0.ne', one_mul]
      exact sieveHat_shift s
    · rw [max_eq_right (le_of_not_ge hs3)]
      have hc := sieveHat_weighted_compact hs1 (le_of_not_ge hs3)
      have he : sieveHat (3 - 1) = exp (-2) := by norm_num [sieveHat]
      rw [he]
      have hid : (3 / s) * exp (-2) = (3 * exp (-2)) / s := by ring
      rw [hid]
      apply (div_le_iff₀ hs0).mpr
      nlinarith only [hc, mul_pos hs0 (sieveHat_pos s)]

theorem source_test_boundary {n : ℕ} {s ε : ℝ} (hε : 0 ≤ ε)
    (hs : s ∈ closedDomain 2 (n + 1)) :
    let a : ℝ := max s (2 + (eps (n + 1) : ℝ))
    (a / s) * sourceLayerTest n ε a ≤
      (2 * exp 2 * (241 / 250 : ℝ) ^ (n - 1) + ε * kernelSieveError (n - 1) * exp 2) *
        (4 * sieveHat s) := by
  dsimp only
  let a : ℝ := max s (2 + (eps (n + 1) : ℝ))
  have hs0 := closedDomain_pos (by norm_num : (1 : ℝ) < 2) hs
  have hparR : (eps (n + 1) : ℝ) + eps n = 1 := by exact_mod_cast eps_succ_add n
  have ha : 3 - (eps n : ℝ) ≤ a := by
    have hh := le_max_right s (2 + (eps (n + 1) : ℝ))
    dsimp [a]; linarith
  have hdom : a - 1 ∈ closedDomain 2 n := by change (2 : ℝ) - (eps n : ℝ) ≤ a - 1; linarith
  have hf := sieve_continuous_layer_decay n (a - 1) hdom
  let C := 2 * exp 2 * (241 / 250 : ℝ) ^ (n - 1) + ε * kernelSieveError (n - 1) * exp 2
  have hC : 0 ≤ C := by
    have ht := kernelSieveError_nonneg (n - 1)
    dsimp [C]; positivity
  have hbound : sourceLayerTest n ε a ≤ C * sieveHat (a - 1) := by
    rw [sourceLayerTest_eq n ε ha]
    unfold sourceLayerEnvelope C
    nlinarith only [hf]
  have hpos : 0 ≤ a / s := div_nonneg (hs0.le.trans (le_max_left _ _)) hs0.le
  have hscaled := mul_le_mul_of_nonneg_left hbound hpos
  have htail := mul_le_mul_of_nonneg_left (source_hat_boundary hs) hC
  dsimp only [C] at hscaled htail ⊢
  nlinarith only [hscaled, htail]

theorem source_test_integral {n : ℕ} {s ε : ℝ} (hn : 0 < n) (hε : 0 ≤ ε)
    (hs : s ∈ closedDomain 2 (n + 1))
    (has : max s (2 + (eps (n + 1) : ℝ)) ≤ (n : ℝ) + 3) :
    (∫ t in max s (2 + (eps (n + 1) : ℝ))..((n : ℝ) + 3), sourceLayerTest n ε t) ≤
      s * layer 2 (n + 1) s +
        ε * kernelSieveError (n - 1) * exp 2 * ((241 / 250 : ℝ) * s * sieveHat s) := by
  let a : ℝ := max s (2 + (eps (n + 1) : ℝ))
  let b : ℝ := (n : ℝ) + 3
  have hs0 := closedDomain_pos (by norm_num : (1 : ℝ) < 2) hs
  have hparR : (eps (n + 1) : ℝ) + eps n = 1 := by exact_mod_cast eps_succ_add n
  have ha : 3 - (eps n : ℝ) ≤ a := by
    have hh := le_max_right s (2 + (eps (n + 1) : ℝ))
    dsimp [a]; linarith
  have hdom : ∀ t ∈ Icc a b, t - 1 ∈ closedDomain 2 n := by
    intro t ht
    change (2 : ℝ) - (eps n : ℝ) ≤ t - 1
    linarith [ht.1]
  have hInt : IntervalIntegrable (fun t => layer 2 n (t - 1)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le has]
    apply (regular (by norm_num : (1 : ℝ) < 2) n).continuous.comp
      (continuous_id.sub continuous_const).continuousOn hdom
  have hHatInt : IntervalIntegrable (fun t => sieveHat (t - 1)) volume a b :=
    (sieveHat_continuous.comp (continuous_id.sub continuous_const)).intervalIntegrable a b
  have hsplit : (∫ t in a..b, sourceLayerTest n ε t) =
      (∫ t in a..b, layer 2 n (t - 1)) +
        ε * kernelSieveError (n - 1) * exp 2 * (∫ t in a..b, sieveHat (t - 1)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hInt
      (hHatInt.const_mul (ε * kernelSieveError (n - 1) * exp 2))]
    apply integral_congr
    intro t ht
    rw [uIcc_of_le has] at ht
    rw [sourceLayerTest_eq n ε (ha.trans ht.1)]
    rfl
  have hmain : (∫ t in a..b, layer 2 n (t - 1)) = s * layer 2 (n + 1) s := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [layer]
    have hl : lower 2 s (k + 2) = a := by
      unfold lower
      have hb : (2 : ℝ) + (k + 2 : ℕ) = b := by dsimp [b]; push_cast; ring
      rw [hb]
      exact min_eq_left has
    rw [hl]
    have hb : (2 : ℝ) + ((k : ℝ) + 2) = b := by dsimp [b]; push_cast; ring
    rw [hb]
    field_simp
  have htail : sieveHatTail a ≤ (241 / 250 : ℝ) * s * sieveHat s := by
    by_cases hp : eps (n + 1) = 0
    · have hs2 : 2 ≤ s := by simpa only [closedDomain, mem_Ici, hp, Nat.cast_zero, sub_zero] using hs
      have hh : a = s := by simp [a, hp, max_eq_left hs2]
      rw [hh]; exact sieveHatTail_contraction hs2
    · have hp1 : eps (n + 1) = 1 := by unfold eps at *; omega
      have hs1 : 1 ≤ s := by
        have hh := hs
        norm_num only [closedDomain, mem_Ici, hp1, Nat.cast_one] at hh
        linarith
      have hh : a = max s 3 := by norm_num [a, hp1]
      rw [hh]; exact sieveHatTail_parity hs1
  have hhat := (sieve_integral_shift_hat_le_tail a b).trans htail
  have hC : 0 ≤ ε * kernelSieveError (n - 1) * exp 2 := by
    have ht := kernelSieveError_nonneg (n - 1)
    positivity
  rw [hsplit, hmain]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hhat hC)

#print axioms source_test_integral

theorem source_analytic_successor {n : ℕ} {s ε : ℝ} (hn : 0 < n)
    (hε : 0 ≤ ε) (hεcap : ε ≤ 1 / 10000)
    (hs : s ∈ closedDomain 2 (n + 1))
    (has : max s (2 + (eps (n + 1) : ℝ)) ≤ (n : ℝ) + 3) :
    let a : ℝ := max s (2 + (eps (n + 1) : ℝ))
    ((1 + ε) ^ 2 / s) * (∫ t in a..((n : ℝ) + 3), sourceLayerTest n ε t) +
      (1 + ε) * ε * (a / s) * sourceLayerTest n ε a ≤ sourceLayerEnvelope (n + 1) ε s := by
  dsimp only
  let a : ℝ := max s (2 + (eps (n + 1) : ℝ))
  let K : ℝ := 1 + ε
  let T : ℝ := kernelSieveError (n - 1)
  let J : ℝ := (241 / 250 : ℝ) ^ (n - 1)
  let F : ℝ := layer 2 (n + 1) s
  have hs0 := closedDomain_pos (by norm_num : (1 : ℝ) < 2) hs
  have hT : 0 ≤ T := kernelSieveError_nonneg _
  have hI := source_test_integral hn hε hs has
  have hB := source_test_boundary hε hs
  have hF := sieve_continuous_layer_decay (n + 1) s hs
  simp only [Nat.add_sub_cancel] at hF
  have hpow : (241 / 250 : ℝ) ^ n = J * (241 / 250) := by
    dsimp [J]
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  have hK2 : 0 ≤ K ^ 2 - 1 := by dsimp [K]; nlinarith
  have hscaledF := mul_le_mul_of_nonneg_left hF hK2
  have hscalar := kernel_sieve_step_cap hε hεcap hT (n - 1)
  have hweight : 0 ≤ ε * exp 2 * sieveHat s := by have hh := (sieveHat_pos s).le; positivity
  have hscaled := mul_le_mul_of_nonneg_left hscalar hweight
  have hrec : kernelSieveError n = (965 / 1000 : ℝ) * T + 12 * J := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [kernelSieveError]
    norm_num [T, J]
  change (K ^ 2 / s) * (∫ t in a..((n : ℝ) + 3), sourceLayerTest n ε t) +
    K * ε * (a / s) * sourceLayerTest n ε a ≤ _
  calc
    _ ≤ (K ^ 2 / s) * (s * F + ε * T * exp 2 * ((241 / 250 : ℝ) * s * sieveHat s)) +
        (K * ε) * ((2 * exp 2 * J + ε * T * exp 2) * (4 * sieveHat s)) := by
      have hi := mul_le_mul_of_nonneg_left hI (div_nonneg (sq_nonneg K) hs0.le)
      have hb := mul_le_mul_of_nonneg_left hB (show 0 ≤ K * ε by dsimp [K]; positivity)
      have hh := add_le_add hi hb
      convert! hh using 1; ring
    _ = K ^ 2 * F + ε * exp 2 * sieveHat s *
        (((K ^ 2 * (241 / 250 : ℝ) + K * ε * 4) * T) + 8 * K * J) := by
      field_simp [hs0.ne']
      ring
    _ = F + (K ^ 2 - 1) * F + ε * exp 2 * sieveHat s *
        (((K ^ 2 * (241 / 250 : ℝ) + K * ε * 4) * T) + 8 * K * J) := by ring
    _ ≤ F + (K ^ 2 - 1) * (2 * exp 2 * (241 / 250 : ℝ) ^ n * sieveHat s) +
        ε * exp 2 * sieveHat s * (((K ^ 2 * (241 / 250 : ℝ) + K * ε * 4) * T) + 8 * K * J) := by
      exact add_le_add (add_le_add le_rfl hscaledF) le_rfl
    _ = F + ε * exp 2 * sieveHat s *
        (((K ^ 2 * (241 / 250 : ℝ) + K * ε * 4) * T) +
          (8 * K + 2 * (2 + ε) * (241 / 250 : ℝ)) * J) := by
      rw [hpow]
      dsimp [K]
      ring
    _ ≤ F + ε * exp 2 * sieveHat s * ((965 / 1000 : ℝ) * T + 12 * J) :=
      add_le_add le_rfl (by
        simpa only [K, J, show (964 / 1000 : ℝ) = 241 / 250 by norm_num] using hscaled)
    _ = sourceLayerEnvelope (n + 1) ε s := by
      rw [← hrec]
      simp only [sourceLayerEnvelope, Nat.add_sub_cancel]
      dsimp [F]
      ring

#print axioms source_analytic_successor
end ChenEffective
