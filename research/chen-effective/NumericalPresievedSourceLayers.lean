import NumericalSieveSourceParity
import NumericalEulerProductPower

namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers KappaOneModel
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable def restrictedSievePrimeProduct (S : BoundingSieve) (U : ℝ) : ℕ :=
  ∏ p ∈ S.prodPrimes.primeFactors.filter (fun p : ℕ => U ≤ (p : ℝ)), p

theorem restrictedSievePrimeProduct_dvd (S : BoundingSieve) (U : ℝ) :
    restrictedSievePrimeProduct S U ∣ S.prodPrimes := by
  have hh := Finset.prod_dvd_prod_of_subset
    (S.prodPrimes.primeFactors.filter (fun p : ℕ => U ≤ (p : ℝ))) S.prodPrimes.primeFactors id
    (Finset.filter_subset _ _)
  exact hh.trans (Nat.prod_primeFactors_dvd _)

/-- Restrict only the prime carrier. Exact pre-sieving of sequence weights and
the subsequent QD remainder assembly are separate from the layer estimate. -/
noncomputable def restrictSievePrimes (S : BoundingSieve) (U : ℝ) : BoundingSieve where
  support := S.support
  weights := S.weights
  weights_nonneg := S.weights_nonneg
  totalMass := S.totalMass
  prodPrimes := restrictedSievePrimeProduct S U
  prodPrimes_squarefree := S.prodPrimes_squarefree.squarefree_of_dvd
    (restrictedSievePrimeProduct_dvd S U)
  nu := S.nu
  nu_mult := S.nu_mult
  nu_pos_of_prime := fun p hp hd => S.nu_pos_of_prime p hp
    (hd.trans (restrictedSievePrimeProduct_dvd S U))
  nu_lt_one_of_prime := fun p hp hd => S.nu_lt_one_of_prime p hp
    (hd.trans (restrictedSievePrimeProduct_dvd S U))

theorem restrictSievePrimes_primeFactors (S : BoundingSieve) (U : ℝ) :
    (restrictSievePrimes S U).prodPrimes.primeFactors =
      S.prodPrimes.primeFactors.filter (fun p : ℕ => U ≤ (p : ℝ)) := by
  change (∏ p ∈ S.prodPrimes.primeFactors.filter (fun p : ℕ => U ≤ (p : ℝ)), p).primeFactors = _
  apply Nat.primeFactors_prod
  intro p hp
  exact Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1

theorem restricted_source_relative (N : ℕ) :
    HasRelativeSieveProduct
      (restrictSievePrimes (jurkatRichertSourceBoundingSieve N) powerPresieveStart)
      (1 / 10000000) := by
  intro u z hu huz
  unfold suzukiLocalRatio
  rw [restrictSievePrimes_primeFactors]
  simpa only [restrictSievePrimes, jurkatRichertSourceBoundingSieve, Finset.filter_filter,
    and_assoc] using numerical_presieved_source_product N u z hu huz

theorem restricted_conditioned_relative (N q : ℕ) :
    HasRelativeSieveProduct
      (restrictSievePrimes (jurkatRichertSourceConditionedBoundingSieve N q) powerPresieveStart)
      (1 / 10000000) := by
  intro u z hu huz
  unfold suzukiLocalRatio
  rw [restrictSievePrimes_primeFactors]
  simpa only [restrictSievePrimes, jurkatRichertSourceConditionedBoundingSieve, Finset.filter_filter,
    and_assoc] using numerical_presieved_source_product N u z hu huz

theorem numerical_presieved_source_layers (M N D z : ℕ) {s : ℝ}
    (hD : 1 < D) (hs : s ∈ closedDomain 2 N) (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    let S := restrictSievePrimes (jurkatRichertSourceBoundingSieve M) powerPresieveStart
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      suzukiVProduct S ((D : ℝ) ^ (1 / s)) *
        (finiteSourceLayer 1 2 N s + (1 / 10000000 : ℝ) * 6000 * exp 2 * sieveHat s) :=
  actual_source_parity_domination (by norm_num) (by norm_num) (restricted_source_relative M)
    N D z hD hs hz

theorem numerical_presieved_conditioned_layers (M q N D z : ℕ) {s : ℝ}
    (hD : 1 < D) (hs : s ∈ closedDomain 2 N) (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    let S := restrictSievePrimes (jurkatRichertSourceConditionedBoundingSieve M q) powerPresieveStart
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      suzukiVProduct S ((D : ℝ) ^ (1 / s)) *
        (finiteSourceLayer 1 2 N s + (1 / 10000000 : ℝ) * 6000 * exp 2 * sieveHat s) :=
  actual_source_parity_domination (by norm_num) (by norm_num) (restricted_conditioned_relative M q)
    N D z hD hs hz

#print axioms numerical_presieved_source_layers
#print axioms numerical_presieved_conditioned_layers
end ChenEffective
