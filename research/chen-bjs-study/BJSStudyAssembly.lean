import BJSStudyInputs
import NumericalPreSieveAssembly

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- Exact pre-sieved lower count. The only distribution remainder is the
original sequence remainder below QD; it carries no extra Q factor. -/
theorem bjsStudy_preSieveCounting_lower_bound (S : BoundingSieve) (U : ℝ)
    {ε s : ℝ} (hS : 0 ≤ S.totalMass)
    (_hε : 0 ≤ ε) (hεcap : ε ≤ 1/4000)
    (hrel : HasRelativeSieveProduct (preSieveCounting S U) ε)
    (D z : ℕ) (hD : 1 < D) (hs4 : 4 ≤ s) (hs5 : s ≤ 5)
    (hz : z = ⌈(D : ℝ)^(1/s)⌉₊) (hzD : z ≤ D)
    (hcut : ∀ p ∈ (preSieveCounting S U).prodPrimes.primeFactors, p < z) :
    S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (dimensionOneLowerLinearSieveFactor s-110*(1/2000:ℝ)*exp 2*sieveHat s) -
      sieveRemainderBelow S (smallSievePrimeProduct S U*D) ≤ S.siftedSum := by
  have hrel' : HasRelativeSieveProduct (preSieveCounting S U) (1/4000) := by
    intro u z hu huz
    have hh := hrel u z hu huz
    have hr : 0 ≤ log z/log u := div_nonneg (log_nonneg (by linarith only [hu,huz])) (log_pos hu).le
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith only [hεcap]) hr)
  let T := preSieveCounting S U
  let weight := lowerRosserWeight T.prodPrimes D
  have hsupport := lowerRosserWeight_hasLowerLevelSupport T.prodPrimes D
  have hfinite := mainSum_sub_lowerErrSum_le_siftedSum (S := T) D weight
    (lowerRosserWeight_certificate T.prodPrimes_squarefree T.prodPrimes_ne_zero
      (fun p hp => (hcut p hp).trans_le hzD)) hsupport
  rw [← errSum_eq_lowerErrSum hsupport] at hfinite
  have hrem := preSieveCounting_errSum_QD S U D weight hsupport
    (fun d _ => abs_lowerRosserWeight_le_one T.prodPrimes D d)
  have hdensity := bjsStudy_lower_density hrel' D z hD hs4 hs5 hz hzD hcut
  have hpaid := mul_le_mul_of_nonneg_left hdensity (preSieveCounting_mass_nonneg U hS)
  rw [← mul_assoc, preSieveCounting_mass_product] at hpaid
  rw [preSieveCounting_siftedSum] at hfinite
  dsimp only [T, weight] at hfinite hrem
  linarith only [hpaid, hrem, hfinite]

/-- The corresponding exact upper count, with the same QD assembly. -/
theorem bjsStudy_preSieveCounting_upper_bound (S : BoundingSieve) (U : ℝ)
    {ε s : ℝ} (hS : 0 ≤ S.totalMass)
    (_hε : 0 ≤ ε) (hεcap : ε ≤ 1/4000)
    (hrel : HasRelativeSieveProduct (preSieveCounting S U) ε)
    (D z : ℕ) (hD : 1 < D) (hslo : 3/2 ≤ s) (hshi : s ≤ 4)
    (hz : z = ⌈(D : ℝ)^(1/s)⌉₊) (hzD : z ≤ D)
    (hcut : ∀ p ∈ (preSieveCounting S U).prodPrimes.primeFactors, p < z) :
    S.siftedSum ≤ S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (jurkatRichertUpperLinearSieveFactor s+110*(1/2000:ℝ)*exp 2*sieveHat s) +
      sieveRemainderBelow S (smallSievePrimeProduct S U*D) := by
  have hrel' : HasRelativeSieveProduct (preSieveCounting S U) (1/4000) := by
    intro u z hu huz
    have hh := hrel u z hu huz
    have hr : 0 ≤ log z/log u := div_nonneg (log_nonneg (by linarith only [hu,huz])) (log_pos hu).le
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith only [hεcap]) hr)
  let T := preSieveCounting S U
  let weight := upperRosserWeight T.prodPrimes D
  have hsupport := upperRosserWeight_hasUpperLevelSupport T.prodPrimes D
  have hfinite := siftedSum_le_mainSum_add_upperErrSum_upperRosser (S := T) D
    (upperRosserWeight_certificate T.prodPrimes_squarefree T.prodPrimes_ne_zero hD
      (fun p hp => (hcut p hp).trans_le hzD))
  rw [← errSum_eq_upperErrSum hsupport] at hfinite
  have hrem := preSieveCounting_errSum_QD S U D weight hsupport
    (fun d _ => abs_upperRosserWeight_le_one T.prodPrimes D d)
  have hdensity := bjsStudy_upper_density hrel' D z hD hslo hshi hz hzD hcut
  have hpaid := mul_le_mul_of_nonneg_left hdensity (preSieveCounting_mass_nonneg U hS)
  rw [← mul_assoc, preSieveCounting_mass_product] at hpaid
  rw [preSieveCounting_siftedSum] at hfinite
  dsimp only [T, weight] at hfinite hrem
  linarith only [hpaid, hrem, hfinite]

#print axioms bjsStudy_preSieveCounting_lower_bound
#print axioms bjsStudy_preSieveCounting_upper_bound
end ChenEffective
