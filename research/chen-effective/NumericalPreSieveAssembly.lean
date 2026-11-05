import NumericalPreSieveDensity

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem preSieveCounting_mass_product (S : BoundingSieve) (U : ℝ) :
    (preSieveCounting S U).totalMass *
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (preSieveCounting S U) =
    S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
  have hsmall : (smallSievePrimeProduct S U).primeFactors =
      S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < U) := by
    apply Nat.primeFactors_prod
    intro p hp
    exact Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  change (S.totalMass * smallSieveEuler S U) *
    (∏ p ∈ (restrictSievePrimes S U).prodPrimes.primeFactors, (1-S.nu p)) = _
  rw [restrictSievePrimes_primeFactors]
  unfold smallSieveEuler AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
  rw [hsmall, mul_assoc]
  congr 1
  simpa only [not_lt] using Finset.prod_filter_mul_prod_filter_not
    S.prodPrimes.primeFactors (fun p : ℕ => (p : ℝ) < U) (fun p => 1-S.nu p)

theorem preSieveCounting_mass_nonneg {S : BoundingSieve} (U : ℝ)
    (hS : 0 ≤ S.totalMass) : 0 ≤ (preSieveCounting S U).totalMass := by
  apply mul_nonneg hS
  apply prod_nonneg
  intro p hp
  have hd := (Nat.mem_primeFactors_of_ne_zero
    (S.prodPrimes_squarefree.squarefree_of_dvd (smallSievePrimeProduct_dvd S U)).ne_zero).mp hp
  exact (sub_pos.mpr (S.nu_lt_one_of_prime p hd.1
    (hd.2.trans (smallSievePrimeProduct_dvd S U)))).le

theorem sieveRemainderBelow_mono (S : BoundingSieve) {a b : ℕ} (hab : a ≤ b) :
    sieveRemainderBelow S a ≤ sieveRemainderBelow S b := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact mem_filter.mpr ⟨(mem_filter.mp hd).1, (mem_filter.mp hd).2.trans_le hab⟩
  · intro d _ _; exact abs_nonneg (S.rem d)

/-- Exact pre-sieved lower count. The only distribution remainder is the
original sequence remainder below QD; it carries no extra Q factor. -/
theorem preSieveCounting_lower_bound (S : BoundingSieve) (U : ℝ)
    {ε s : ℝ} (hS : 0 ≤ S.totalMass)
    (hε : 0 ≤ ε) (hεcap : ε ≤ 1/10000)
    (hrel : HasRelativeSieveProduct (preSieveCounting S U) ε)
    (D z : ℕ) (hD : 1 < D) (hs4 : 4 ≤ s) (hs5 : s ≤ 5)
    (hz : z = ⌈(D : ℝ)^(1/s)⌉₊) (hzD : z ≤ D)
    (hcut : ∀ p ∈ (preSieveCounting S U).prodPrimes.primeFactors, p < z) :
    S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (dimensionOneLowerLinearSieveFactor s-6000*ε) -
      sieveRemainderBelow S (smallSievePrimeProduct S U*D) ≤ S.siftedSum := by
  let T := preSieveCounting S U
  let weight := lowerRosserWeight T.prodPrimes D
  have hsupport := lowerRosserWeight_hasLowerLevelSupport T.prodPrimes D
  have hfinite := mainSum_sub_lowerErrSum_le_siftedSum (S := T) D weight
    (lowerRosserWeight_certificate T.prodPrimes_squarefree T.prodPrimes_ne_zero
      (fun p hp => (hcut p hp).trans_le hzD)) hsupport
  rw [← errSum_eq_lowerErrSum hsupport] at hfinite
  have hrem := preSieveCounting_errSum_QD S U D weight hsupport
    (fun d _ => abs_lowerRosserWeight_le_one T.prodPrimes D d)
  have hdensity := relative_lower_rosser_density hε hεcap hrel D z hD hs4 hs5 hz hzD hcut
  have hpaid := mul_le_mul_of_nonneg_left hdensity (preSieveCounting_mass_nonneg U hS)
  rw [← mul_assoc, preSieveCounting_mass_product] at hpaid
  rw [preSieveCounting_siftedSum] at hfinite
  dsimp only [T, weight] at hfinite hrem
  linarith only [hpaid, hrem, hfinite]

/-- The corresponding exact upper count, with the same QD assembly. -/
theorem preSieveCounting_upper_bound (S : BoundingSieve) (U : ℝ)
    {ε s : ℝ} (hS : 0 ≤ S.totalMass)
    (hε : 0 ≤ ε) (hεcap : ε ≤ 1/10000)
    (hrel : HasRelativeSieveProduct (preSieveCounting S U) ε)
    (D z : ℕ) (hD : 1 < D) (hslo : 3/2 ≤ s) (hshi : s ≤ 4)
    (hz : z = ⌈(D : ℝ)^(1/s)⌉₊) (hzD : z ≤ D)
    (hcut : ∀ p ∈ (preSieveCounting S U).prodPrimes.primeFactors, p < z) :
    S.siftedSum ≤ S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (jurkatRichertUpperLinearSieveFactor s+6000*ε) +
      sieveRemainderBelow S (smallSievePrimeProduct S U*D) := by
  let T := preSieveCounting S U
  let weight := upperRosserWeight T.prodPrimes D
  have hsupport := upperRosserWeight_hasUpperLevelSupport T.prodPrimes D
  have hfinite := siftedSum_le_mainSum_add_upperErrSum_upperRosser (S := T) D
    (upperRosserWeight_certificate T.prodPrimes_squarefree T.prodPrimes_ne_zero hD
      (fun p hp => (hcut p hp).trans_le hzD))
  rw [← errSum_eq_upperErrSum hsupport] at hfinite
  have hrem := preSieveCounting_errSum_QD S U D weight hsupport
    (fun d _ => abs_upperRosserWeight_le_one T.prodPrimes D d)
  have hdensity := relative_upper_rosser_density hε hεcap hrel D z hD hslo hshi hz hzD hcut
  have hpaid := mul_le_mul_of_nonneg_left hdensity (preSieveCounting_mass_nonneg U hS)
  rw [← mul_assoc, preSieveCounting_mass_product] at hpaid
  rw [preSieveCounting_siftedSum] at hfinite
  dsimp only [T, weight] at hfinite hrem
  linarith only [hpaid, hrem, hfinite]

#print axioms preSieveCounting_lower_bound
#print axioms preSieveCounting_upper_bound
end ChenEffective
