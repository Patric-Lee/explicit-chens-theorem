import NumericalGoldbachInterval

namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Keep the exponent symbolic during arithmetic elaboration. -/
@[irreducible] def localProductExponent : ℕ := 4 * globalMertensBudget + 52
noncomputable def numericalLocalProductK : ℝ :=
  ((localProductExponent : ℝ) + 2) * (3 : ℝ) ^ (2 * localProductExponent)

/-- The elementary Mertens budget makes the local-product cap a literal integer. -/
theorem numericalLocalProductK_eq : numericalLocalProductK = (94*3^184 : ℕ) := by
  norm_num [numericalLocalProductK,localProductExponent,globalMertensBudget]

theorem numericalLocalProductK_lt : numericalLocalProductK < (10^90 : ℝ) := by
  rw [numericalLocalProductK_eq]
  norm_num
theorem two_le_product_cap (E : ℕ) : (2 : ℝ) ≤ ((E : ℝ) + 2) * (3 : ℝ) ^ (2 * E) := by
  have hp : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * E) := one_le_pow₀ (by norm_num)
  have he : (0 : ℝ) ≤ E := Nat.cast_nonneg E
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ (E : ℝ) + 2 by positivity)
  linarith only [hh, he]

theorem numerical_local_product_two : 2 ≤ numericalLocalProductK := by
  unfold numericalLocalProductK
  exact two_le_product_cap localProductExponent

/-- A literal integer cap for the real Mertens interval constant. -/
theorem interval_constant_cap {C : ℝ} {E : ℕ} (hC : 0 ≤ C)
    (hE : 4 * C + 52 ≤ (E : ℝ)) :
    goldbachIntervalConstant C ≤ ((E : ℝ) + 2) * (3 : ℝ) ^ (2 * E) := by
  let D : ℝ := 2 * (2 * C + 24) + 2 * Real.log 2
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlog1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hDE : D ≤ E := by dsimp [D]; linarith only [hlog1, hE]
  have hdiv : D / Real.log 2 ≤ ((2 * E : ℕ) : ℝ) := by
    apply (div_le_iff₀ hlog0).mpr
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hh := mul_le_mul_of_nonneg_left hloghalf hE0
    nlinarith only [hh, hDE]
  have hexp : Real.exp (D / Real.log 2) ≤ (3 : ℝ) ^ (2 * E) := by
    calc
      _ ≤ Real.exp (((2 * E : ℕ) : ℝ)) := Real.exp_le_exp.mpr hdiv
      _ = (Real.exp 1) ^ (2 * E) := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le
        (Real.exp_one_lt_d9.le.trans (by norm_num)) _
  have hp : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * E) := one_le_pow₀ (by norm_num)
  change D * Real.exp (D / Real.log 2) + 2 ≤ _
  have hh := mul_le_mul hDE hexp (Real.exp_pos _).le hE0
  nlinarith only [hh, hp]

theorem numerical_interval_constant_cap : intervalGoldbachConstant ≤ numericalLocalProductK := by
  have hE : 4 * (globalMertensBudget : ℝ) + 52 ≤ (localProductExponent : ℝ) := by
    rw [localProductExponent, Nat.cast_add, Nat.cast_mul]
    exact le_refl _
  have hh := interval_constant_cap (C := (globalMertensBudget : ℝ))
    (E := localProductExponent) (Nat.cast_nonneg globalMertensBudget) hE
  change goldbachIntervalConstant (globalMertensBudget : ℝ) ≤
    ((localProductExponent : ℝ) + 2) * (3 : ℝ) ^ (2 * localProductExponent)
  exact hh

theorem numerical_goldbach_interval (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (z₁ z₂ : ℝ) (hz₁ : 2 ≤ z₁) (hz₁₂ : z₁ ≤ z₂)
    (hsinterval : ∀ p ∈ s, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂) :
    (∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      Real.log z₂ / Real.log z₁ * (1 + (numericalLocalProductK : ℝ) / Real.log z₁) := by
  have hl1 : 0 < Real.log z₁ := Real.log_pos (by linarith only [hz₁])
  have hl2 : 0 ≤ Real.log z₂ := Real.log_nonneg (by linarith only [hz₁, hz₁₂])
  apply (numerical_goldbach_inverse_interval_bound s hs z₁ z₂ hz₁ hz₁₂ hsinterval).trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hl2 hl1.le)
  exact add_le_add (le_refl _) (div_le_div_of_nonneg_right numerical_interval_constant_cap hl1.le)

theorem numerical_source_local_product (N : ℕ) :
    HasDimensionOneLocalProductBound (jurkatRichertSourceBoundingSieve N) (numericalLocalProductK : ℝ) := by
  have hinterval := numerical_goldbach_interval
  intro z₁ z₂ hz₁ hz₁₂
  let s : Finset ℕ :=
    (jurkatRichertSourceSiftingProduct N).primeFactors.filter
      (fun p : ℕ => z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hp' :
        p ∈ (jurkatRichertSourceSiftingProduct N).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [s] using hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hpdiv : p ∣ jurkatRichertSourceSiftingProduct N :=
      (Nat.mem_primeFactors_of_ne_zero
        (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp'.1 |>.2
    exact ⟨hprime,
      (prime_dvd_jurkatRichertSourceSiftingProduct hprime).mp hpdiv |>.1⟩
  have hsinterval : ∀ p ∈ s, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
    intro p hp
    have hp' :
        p ∈ (jurkatRichertSourceSiftingProduct N).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [s] using hp
    exact hp'.2
  have hbound := hinterval s hs z₁ z₂ hz₁ hz₁₂ hsinterval
  change (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) ≤
    Real.log z₂ / Real.log z₁ * (1 + (numericalLocalProductK : ℝ) / Real.log z₁)
  calc
    (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) =
        ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (hs p hp).1]
    _ ≤ Real.log z₂ / Real.log z₁ * (1 + (numericalLocalProductK : ℝ) / Real.log z₁) := hbound



#print axioms numerical_source_local_product
#print axioms numerical_local_product_two
#print axioms numerical_interval_constant_cap
#print axioms numerical_goldbach_interval
end ChenEffective
