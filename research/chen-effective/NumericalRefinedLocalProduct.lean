import NumericalProductSplit
import NumericalLocalProduct
namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable def refinedLocalProductK : ℝ := 10 ^ 12
theorem refined_local_product_two : 2 ≤ refinedLocalProductK := by norm_num [refinedLocalProductK]
theorem refined_local_product_cap : refinedLocalProductK ≤ (10 ^ 12 : ℝ) := le_rfl

theorem numerical_refined_source_local_product (N : ℕ) :
    HasDimensionOneLocalProductBound (jurkatRichertSourceBoundingSieve N) (refinedLocalProductK : ℝ) := by
  have hinterval := numerical_goldbach_split_interval
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
    Real.log z₂ / Real.log z₁ * (1 + (refinedLocalProductK : ℝ) / Real.log z₁)
  calc
    (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) =
        ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (hs p hp).1]
    _ ≤ Real.log z₂ / Real.log z₁ * (1 + (refinedLocalProductK : ℝ) / Real.log z₁) := hbound



#print axioms numerical_refined_source_local_product
end ChenEffective
