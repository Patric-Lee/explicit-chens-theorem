import NumericalSuzukiNormalization

namespace ChenEffective
open Real Set Filter MeasureTheory
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- One half-step of the positive tail identity, with a fixed upper endpoint. -/
theorem numerical_hat_half_step {H : Section13HatLayers}
    (hH : Section13HatContract H 2) (sign : ErrorSign) {s M b : ℝ}
    (hs : 2 + sign.epsilon < s) (hs2 : 2 < s) (hsM : s ≤ M)
    (hlower : ∀ u ∈ Icc (s - 1) (s - 1 / 2), b ≤ weightedHat H sign.opposite u) :
    b / (2 * (M + 1)) ≤ weightedHat H sign s := by
  have hM0 : 0 < M + 1 := by linarith only [hs2, hsM]
  have hi := integrableOn_hatTailIntegrand_Ioi hH sign hs
  have hsub : Ioc s (s + 1 / 2) ⊆ Ioi s := fun _ ht => ht.1
  have hint : IntervalIntegrable (hatTailIntegrand H sign) volume s (s + 1 / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : s ≤ s + 1 / 2)).mpr
      (hi.mono_set hsub)
  have hpoint (t : ℝ) (ht : t ∈ Icc s (s + 1 / 2)) :
      b / (M + 1) ≤ hatTailIntegrand H sign t := by
    have hu : t - 1 ∈ Icc (s - 1) (s - 1 / 2) := by
      constructor <;> linarith only [ht.1, ht.2]
    have hb := hlower (t - 1) hu
    have hT : 0 ≤ H.T sign.opposite (t - 1) :=
      (hH.positive sign.opposite (t - 1) (by linarith only [hs2, ht.1])).le
    have hfac : (t - 1) ^ (2 : ℕ) ≤ (M + 1) * t := by
      have hh : 0 ≤ t * (M + 2 - t) := mul_nonneg
        (by linarith only [hs2, ht.1]) (by linarith only [hsM, ht.2])
      nlinarith only [hh, ht.1, hs2]
    have hh := mul_le_mul_of_nonneg_right hfac hT
    apply (div_le_iff₀ hM0).mpr
    dsimp [weightedHat] at hb
    dsimp [hatTailIntegrand]
    nlinarith only [hb, hh]
  have htail : (∫ t in s..s + 1 / 2, hatTailIntegrand H sign t) ≤
      weightedHat H sign s := by
    have hn : 0 ≤ᵐ[volume.restrict (Ioi s)] hatTailIntegrand H sign := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hst : s < t := ht
      exact mul_nonneg (by linarith only [hs2, hst] : 0 ≤ t)
        (hH.positive sign.opposite (t - 1) (by linarith only [hs2, hst])).le
    have hh := setIntegral_mono_set (s := Ioc s (s + 1 / 2)) (t := Ioi s) hi hn
      (Filter.Eventually.of_forall (fun _ ht => hsub ht))
    rw [← intervalIntegral.integral_of_le (by linarith : s ≤ s + 1 / 2),
      integral_Ioi_hatTailIntegrand hH sign hs] at hh
    exact hh
  calc
    _ = ∫ _t in s..s + 1 / 2, b / (M + 1) := by simp; field_simp
    _ ≤ ∫ t in s..s + 1 / 2, hatTailIntegrand H sign t :=
      intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hint hpoint
    _ ≤ _ := htail

theorem numerical_weighted_hat_initial {H : Section13HatLayers}
    (hH : Section13HatContract H 2) (sign : ErrorSign) {s : ℝ}
    (hs2 : 2 ≤ s) (hs3 : s ≤ 3) : (1 / 8 : ℝ) ≤ weightedHat H sign s := by
  have hs0 : 0 < s := by linarith only [hs2]
  cases sign with
  | plus =>
      rw [hH.initial_plus s hs0 (by linarith only [hs3])]
      norm_num
  | minus =>
      by_cases hh : s = 2
      · subst s
        rw [hH.initial_minus 2 (by norm_num) (le_refl _)]
        norm_num
      · have hs : 2 < s := lt_of_le_of_ne hs2 (Ne.symm hh)
        have hb := numerical_hat_half_step hH .minus (M := 3) (b := 1)
          (by simpa [ErrorSign.epsilon] using hs) hs hs3 (by
            intro u hu
            have hu0 : 0 < u := by linarith only [hu.1, hs2]
            have hu3 : u ≤ 2 + 1 := by linarith only [hu.2, hs3]
            have he : weightedHat H .plus u = 1 :=
              (hH.initial_plus u hu0 hu3).trans (by norm_num)
            exact he.ge)
        norm_num at hb ⊢
        exact hb

/-- Two half-steps suffice on [2,4]; no eight-step compact floor is needed. -/
theorem numerical_hat_compact_four {H : Section13HatLayers}
    (hH : Section13HatContract H 2) (sign : ErrorSign) {s : ℝ}
    (hs2 : 2 ≤ s) (hs4 : s ≤ 4) : (1/12800 : ℝ) ≤ H.T sign s := by
  have hfirst (sgn : ErrorSign) (u : ℝ) (hu2 : 2 ≤ u) (hu : u ≤ 7/2) :
      (1/80 : ℝ) ≤ weightedHat H sgn u := by
    by_cases hu3 : u ≤ 3
    · exact (by norm_num : (1/80 : ℝ) ≤ 1/8).trans
        (numerical_weighted_hat_initial hH sgn hu2 hu3)
    · have hgt : 3 < u := lt_of_not_ge hu3
      have hthreshold : 2+sgn.epsilon < u := by
        cases sgn <;> simp only [ErrorSign.epsilon] <;> linarith only [hgt]
      have hh := numerical_hat_half_step hH sgn (M := 4) (b := 1/8)
        hthreshold (by linarith only [hgt]) (by linarith only [hu]) (by
          intro v hv
          exact numerical_weighted_hat_initial hH sgn.opposite
            (by linarith only [hv.1,hgt]) (by linarith only [hv.2,hu]))
      norm_num at hh
      exact hh
  have hw : (1/800 : ℝ) ≤ weightedHat H sign s := by
    by_cases hs : s ≤ 7/2
    · exact (by norm_num : (1/800 : ℝ) ≤ 1/80).trans (hfirst sign s hs2 hs)
    · have hgt : 7/2 < s := lt_of_not_ge hs
      have hthreshold : 2+sign.epsilon < s := by
        cases sign <;> simp only [ErrorSign.epsilon] <;> linarith only [hgt]
      have hh := numerical_hat_half_step hH sign (M := 4) (b := 1/80)
        hthreshold (by linarith only [hgt]) hs4 (by
          intro u hu
          exact hfirst sign.opposite u (by linarith only [hu.1,hgt])
            (by linarith only [hu.2,hs4]))
      norm_num at hh
      exact hh
  have hT0 := (hH.positive sign s (by linarith only [hs2])).le
  have hsSq : s^2 ≤ (4 : ℝ)^2 := pow_le_pow_left₀ (by linarith only [hs2]) hs4 2
  have hh := mul_le_mul_of_nonneg_right hsSq hT0
  dsimp [weightedHat] at hw
  norm_num only [Nat.reducePow] at hh
  nlinarith only [hw,hh]
noncomputable def compactHatLower (m : ℕ) : ℝ :=
  ((1 / 8 : ℝ) * (1 / (2 * ((m : ℝ) + 1))) ^ (2 * m)) / (m : ℝ) ^ (2 : ℕ)

theorem compactHatLower_pos {m : ℕ} (hm : 3 ≤ m) : 0 < compactHatLower m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold compactHatLower
  positivity

/-- A completely explicit replacement for a compactness-selected hat minimum. -/
theorem numerical_hat_compact {H : Section13HatLayers}
    (hH : Section13HatContract H 2) {m : ℕ} (hm : 3 ≤ m)
    (sign : ErrorSign) {s : ℝ} (hs2 : 2 ≤ s) (hsm : s ≤ m) :
    compactHatLower m ≤ H.T sign s := by
  let q : ℝ := 1 / (2 * ((m : ℝ) + 1))
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith only [hmR]
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    apply (div_le_one (by positivity : 0 < 2 * ((m : ℝ) + 1))).mpr
    linarith only [hmR]
  have hsteps (n : ℕ) : ∀ (sign : ErrorSign) (s : ℝ),
      2 ≤ s → s ≤ m → s ≤ 3 + (n : ℝ) / 2 →
      (1 / 8 : ℝ) * q ^ n ≤ weightedHat H sign s := by
    induction n with
    | zero =>
        intro sign s hs2 hsm hs3
        norm_num only [Nat.cast_zero, zero_div, add_zero, pow_zero, mul_one] at hs3 ⊢
        exact numerical_weighted_hat_initial hH sign hs2 hs3
    | succ n ih =>
        intro sign s hs2 hsm hsn
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hb0 : 0 ≤ (1 / 8 : ℝ) * q ^ n := by positivity
        by_cases hold : s ≤ 3 + (n : ℝ) / 2
        · have hh := ih sign s hs2 hsm hold
          have hp := mul_le_mul_of_nonneg_left hq1 hb0
          rw [pow_succ]
          nlinarith only [hh, hp]
        · have hs3 : 3 < s := by linarith only [hold, hn0]
          have hthreshold : 2 + sign.epsilon < s := by
            cases sign <;> simp only [ErrorSign.epsilon] <;> linarith only [hs3]
          have hh := numerical_hat_half_step hH sign hthreshold (by linarith only [hs3]) hsm (by
            intro u hu
            apply ih sign.opposite u
            · linarith only [hu.1, hs3]
            · linarith only [hu.2, hsm]
            · norm_num only [Nat.cast_add, Nat.cast_one] at hsn
              linarith only [hu.2, hsn])
          change (1 / 8 : ℝ) * q ^ (n + 1) ≤ _
          rw [pow_succ]
          change (1 / 8 : ℝ) * (q ^ n * q) ≤ _
          have hid : (1 / 8 : ℝ) * (q ^ n * q) =
              ((1 / 8 : ℝ) * q ^ n) / (2 * ((m : ℝ) + 1)) := by dsimp [q]; ring
          rwa [hid]
  have hb := hsteps (2 * m) sign s hs2 hsm (by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hsm])
  have hT0 : 0 ≤ H.T sign s := (hH.positive sign s (by linarith only [hs2])).le
  have hsq : s ^ (2 : ℕ) ≤ (m : ℝ) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by linarith only [hs2]) hsm 2
  have hh := mul_le_mul_of_nonneg_right hsq hT0
  unfold compactHatLower
  apply (div_le_iff₀ (sq_pos_of_pos hm0)).mpr
  change (1 / 8 : ℝ) * q ^ (2 * m) ≤ _
  dsimp [weightedHat] at hb
  nlinarith only [hb, hh]

#print axioms numerical_hat_compact
end ChenEffective
