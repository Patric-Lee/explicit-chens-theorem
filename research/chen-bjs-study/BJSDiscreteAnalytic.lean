import BJSDiscreteEnvelope

noncomputable section
namespace ChenEffective
open Real Set MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

def bjsHatTailRate (n : ℕ) : ℝ := if eps n=0 then 241/250 else 116/125
theorem bjs_test_boundary {n : ℕ} {s ε : ℝ} (hε : 0 ≤ ε)
    (hs : s ∈ closedDomain 2 (n + 1)) :
    let a : ℝ := max s (2 + (eps (n + 1) : ℝ))
    (a / s) * bjsLayerTest n ε a ≤
      (2 * exp 2 * bjsSharpProfile n + ε * bjsSharpError (n - 1) * exp 2) *
        ((11/3 : ℝ) * sieveHat s) := by
  dsimp only
  let a : ℝ := max s (2 + (eps (n + 1) : ℝ))
  have hs0 := closedDomain_pos (by norm_num : (1 : ℝ) < 2) hs
  have hparR : (eps (n + 1) : ℝ) + eps n = 1 := by exact_mod_cast eps_succ_add n
  have ha : 3 - (eps n : ℝ) ≤ a := by
    have hh := le_max_right s (2 + (eps (n + 1) : ℝ))
    dsimp [a]; linarith
  have hdom : a - 1 ∈ closedDomain 2 n := by change (2 : ℝ) - (eps n : ℝ) ≤ a - 1; linarith
  have hf := bjsSharpProfile_bound n (a - 1) hdom
  let C := 2 * exp 2 * bjsSharpProfile n + ε * bjsSharpError (n - 1) * exp 2
  have hC : 0 ≤ C := by
    have ht := bjsSharpError_nonneg (n - 1)
    have hp := bjsSharpProfile_nonneg n
    dsimp [C]; positivity
  have hbound : bjsLayerTest n ε a ≤ C * sieveHat (a - 1) := by
    rw [bjsLayerTest_eq n ε ha]
    unfold bjsLayerEnvelope C
    nlinarith only [hf]
  have hpos : 0 ≤ a / s := div_nonneg (hs0.le.trans (le_max_left _ _)) hs0.le
  have hscaled := mul_le_mul_of_nonneg_left hbound hpos
  have htail := mul_le_mul_of_nonneg_left (bjsStudy_source_hat_boundary hs) hC
  dsimp only [C] at hscaled htail ⊢
  nlinarith only [hscaled, htail]

theorem bjs_test_integral {n : ℕ} {s ε : ℝ} (hn : 0 < n) (hε : 0 ≤ ε)
    (hs : s ∈ closedDomain 2 (n + 1))
    (has : max s (2 + (eps (n + 1) : ℝ)) ≤ (n : ℝ) + 3) :
    (∫ t in max s (2 + (eps (n + 1) : ℝ))..((n : ℝ) + 3), bjsLayerTest n ε t) ≤
      s * layer 2 (n + 1) s +
        ε * bjsSharpError (n - 1) * exp 2 * (bjsHatTailRate (n+1) * s * sieveHat s) := by
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
  have hsplit : (∫ t in a..b, bjsLayerTest n ε t) =
      (∫ t in a..b, layer 2 n (t - 1)) +
        ε * bjsSharpError (n - 1) * exp 2 * (∫ t in a..b, sieveHat (t - 1)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hInt
      (hHatInt.const_mul (ε * bjsSharpError (n - 1) * exp 2))]
    apply integral_congr
    intro t ht
    rw [uIcc_of_le has] at ht
    rw [bjsLayerTest_eq n ε (ha.trans ht.1)]
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
  have htail : sieveHatTail a ≤ bjsHatTailRate (n+1) * s * sieveHat s := by
    by_cases hp : eps (n + 1) = 0
    · have hs2 : 2 ≤ s := by simpa only [closedDomain, mem_Ici, hp, Nat.cast_zero, sub_zero] using hs
      have hh : a = s := by simp [a, hp, max_eq_left hs2]
      rw [hh,bjsHatTailRate,if_pos hp]; exact sieveHatTail_contraction hs2
    · have hp1 : eps (n + 1) = 1 := by unfold eps at *; omega
      have hs1 : 1 ≤ s := by
        have hh := hs
        norm_num only [closedDomain, mem_Ici, hp1, Nat.cast_one] at hh
        linarith
      have hh : a = max s 3 := by norm_num [a, hp1]
      rw [hh,bjsHatTailRate,if_neg hp]; exact bjsStudy_hat_tail_odd hs1
  have hhat := (sieve_integral_shift_hat_le_tail a b).trans htail
  have hC : 0 ≤ ε * bjsSharpError (n - 1) * exp 2 := by
    have ht := bjsSharpError_nonneg (n - 1)
    positivity
  rw [hsplit, hmain]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hhat hC)

theorem bjs_error_scalar_step {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hε : 0≤ε) (hc : ε≤1/4000) :
    (((1+ε)^2*bjsHatTailRate (n+1)+(1+ε)*ε*(11/3))*bjsSharpError (n-1))+
      (22/3)*(1+ε)*bjsSharpProfile n+2*(2+ε)*bjsSharpProfile (n+1) ≤ bjsSharpError n := by
  have hchild : eps (n+1)=(n-1)%2 := by unfold eps; omega
  have hcoef : (1+ε)^2*bjsHatTailRate (n+1)+(1+ε)*ε*(11/3) ≤ bjsSharpStepRate (n-1) := by
    by_cases he : (n-1)%2=0
    · simpa only [bjsHatTailRate,bjsSharpStepRate,hchild,if_pos he] using bjsStudy_even_error_coefficient hε hc
    · simpa only [bjsHatTailRate,bjsSharpStepRate,hchild,if_neg he] using bjsStudy_odd_error_coefficient hε hc
  have ht := mul_le_mul_of_nonneg_right hcoef (bjsSharpError_nonneg (n-1))
  have hf := bjsStudy_profile_forcing_cap hc (bjsSharpProfile_nonneg n) (bjsSharpProfile_nonneg (n+1))
  have hrec : bjsSharpError n=bjsSharpStepRate (n-1)*bjsSharpError (n-1)+
      (367/50 : ℝ)*bjsSharpProfile n+(401/100 : ℝ)*bjsSharpProfile (n+1) := by
    cases n with
    | zero => omega
    | succ k => rfl
  rw [hrec]
  linarith only [ht,hf]

theorem bjs_analytic_successor {n : ℕ} {s ε : ℝ} (hn : 0 < n)
    (hε : 0≤ε) (hc : ε≤1/4000) (hs : s∈closedDomain 2 (n+1))
    (has : max s (2+(eps (n+1) : ℝ)) ≤ (n : ℝ)+3) :
    let a : ℝ := max s (2+(eps (n+1) : ℝ))
    ((1+ε)^2/s)*(∫ t in a..((n : ℝ)+3), bjsLayerTest n ε t)+
      (1+ε)*ε*(a/s)*bjsLayerTest n ε a ≤ bjsLayerEnvelope (n+1) ε s := by
  dsimp only
  let a : ℝ := max s (2+(eps (n+1) : ℝ))
  let K : ℝ := 1+ε
  let T : ℝ := bjsSharpError (n-1)
  let F : ℝ := layer 2 (n+1) s
  have hs0 := closedDomain_pos (by norm_num : (1 : ℝ)<2) hs
  have hI := bjs_test_integral hn hε hs has
  have hB := bjs_test_boundary hε hs
  have hF := bjsSharpProfile_bound (n+1) s hs
  have hK : 0 ≤ K^2-1 := by dsimp [K]; nlinarith only [hε]
  have hscaledF := mul_le_mul_of_nonneg_left hF hK
  have hw : 0≤ε*exp 2*sieveHat s := by have hh:=(sieveHat_pos s).le; positivity
  have hscalar := mul_le_mul_of_nonneg_left (bjs_error_scalar_step hn hε hc) hw
  change (K^2/s)*(∫ t in a..((n : ℝ)+3), bjsLayerTest n ε t)+
    K*ε*(a/s)*bjsLayerTest n ε a ≤ _
  calc
    _ ≤ (K^2/s)*(s*F+ε*T*exp 2*(bjsHatTailRate (n+1)*s*sieveHat s))+
        (K*ε)*((2*exp 2*bjsSharpProfile n+ε*T*exp 2)*((11/3 : ℝ)*sieveHat s)) := by
      have hi := mul_le_mul_of_nonneg_left hI (div_nonneg (sq_nonneg K) hs0.le)
      have hb := mul_le_mul_of_nonneg_left hB (show 0 ≤ K*ε by dsimp [K]; positivity)
      convert! add_le_add hi hb using 1
      ring
    _ = F+(K^2-1)*F+ε*exp 2*sieveHat s*
        (((K^2*bjsHatTailRate (n+1)+K*ε*(11/3))*T)+(22/3)*K*bjsSharpProfile n) := by
      field_simp [hs0.ne']
      ring
    _ ≤ F+(K^2-1)*(2*exp 2*bjsSharpProfile (n+1)*sieveHat s)+ε*exp 2*sieveHat s*
        (((K^2*bjsHatTailRate (n+1)+K*ε*(11/3))*T)+(22/3)*K*bjsSharpProfile n) :=
      add_le_add (add_le_add le_rfl hscaledF) le_rfl
    _ = F+ε*exp 2*sieveHat s*
        (((K^2*bjsHatTailRate (n+1)+K*ε*(11/3))*T)+(22/3)*K*bjsSharpProfile n+
          2*(2+ε)*bjsSharpProfile (n+1)) := by dsimp [K]; ring
    _ ≤ F+ε*exp 2*sieveHat s*bjsSharpError n := by
      exact add_le_add le_rfl (by simpa only [K,T] using hscalar)
    _ = bjsLayerEnvelope (n+1) ε s := by simp only [bjsLayerEnvelope,Nat.add_sub_cancel]; dsimp [F]; ring

#print axioms bjs_analytic_successor
end ChenEffective
