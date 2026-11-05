import NumericalPreSieveSharpProduct
import NumericalPreSieveRemainder
import NumericalMediumUpperDensity

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne
open JurkatRichert1965ChenGammaOneQOne
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem sieveHat_normalized_le_one (s : ℝ) : exp 2 * sieveHat s ≤ 1 := by
  have hh : sieveHat s ≤ exp (-2) := by
    by_cases hs : s ≤ 2
    · simp only [sieveHat, if_pos hs]; exact le_rfl
    · exact (sieveHat_le_exp s).trans (exp_le_exp.mpr (by linarith))
  have he := mul_le_mul_of_nonneg_left hh (exp_pos 2).le
  simpa only [← exp_add, add_neg_cancel, exp_zero] using he

/-- The analytic recurrence controls the actual discrete parity aggregate,
uniformly in its carrier-adaptive depth. -/
theorem relative_actual_parity_bound {S : BoundingSieve} {ε s : ℝ}
    (hε : 0 ≤ ε) (hεcap : ε ≤ 1/10000) (hrel : HasRelativeSieveProduct S ε)
    (n D z : ℕ) (hD : 1 < D) (hs : s ∈ KappaOneModel.closedDomain 2 n)
    (hz : z = ⌈(D : ℝ)^(1/s)⌉₊) :
    suzukiActualT S n D z ≤ suzukiVProduct S (z : ℝ) *
      (finiteSourceLayer 1 2 n s + 6000*ε) := by
  have hh := actual_source_parity_domination hε hεcap hrel n D z hD hs hz
  rw [sourceParityIndices_eq_actualParityCarrier, ← suzukiActualT_eq_parity_sum] at hh
  rw [← SwitchingPrinciple.suzukiVProduct_natCeil_eq S hz] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (suzukiVProduct_pos S _).le
  have he := mul_le_mul_of_nonneg_left (sieveHat_normalized_le_one s)
    (show 0 ≤ ε*6000 by positivity)
  nlinarith only [he]

/-- Lower Rosser density without a selected Suzuki coefficient or source cutoff. -/
theorem relative_lower_rosser_density {S : BoundingSieve} {ε s : ℝ}
    (hε : 0 ≤ ε) (hεcap : ε ≤ 1/10000) (hrel : HasRelativeSieveProduct S ε)
    (D z : ℕ) (hD : 1 < D) (hs4 : 4 ≤ s) (hs5 : s ≤ 5)
    (hz : z = ⌈(D : ℝ)^(1/s)⌉₊) (hzD : z ≤ D)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, p < z) :
    AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
      (dimensionOneLowerLinearSieveFactor s - 6000*ε) ≤
      S.mainSum (lowerRosserWeight S.prodPrimes D) := by
  let n := 2*((suzukiSupportedBelow S z).card+1)
  have hsdom : s ∈ KappaOneModel.closedDomain 2 n := by
    simp only [KappaOneModel.closedDomain, KappaOneModel.eps, n, Nat.mul_mod_right,
      Nat.cast_zero, sub_zero, Set.mem_Ici]
    linarith only [hs4]
  have hh := relative_actual_parity_bound hε hεcap hrel n D z hD hsdom hz
  have hf := suzukiContinuousLowerFactor_le_adaptive_finiteLowerFactor
    jr1965Section13HatSourceContract (suzukiSupportedBelow S z) (by linarith only [hs4])
  rw [suzukiContinuousLowerFactor_eq_dimensionOne_of_sourceContract
    jr1965Section13HatSourceContract hs4 (by linarith only [hs5])] at hf
  have hb := suzukiDensityProduct_lowerRosserWeight_exact_bridge S D z hcut
    (fun p hp => (hcut p hp).trans_le hzD)
  have hd := lowerRosserSetDensitySum_eq_euler_sub_suzukiActualT_all_supported S hD hzD
  rw [sourceDiscreteEuler_eq_suzukiVProduct_nat, ← hb.1, hb.2.1] at hd
  rw [hb.2.1] at hh
  have hV : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    rw [← hb.2.1]; exact (suzukiVProduct_pos S _).le
  have hfv := mul_le_mul_of_nonneg_left hf hV
  dsimp only [suzukiFiniteLowerFactor] at hfv
  change _ = _ - suzukiActualT S n D z at hd
  nlinarith only [hh, hfv, hd]

/-- Upper Rosser density with the same depth-uniform error budget. -/
theorem relative_upper_rosser_density {S : BoundingSieve} {ε s : ℝ}
    (hε : 0 ≤ ε) (hεcap : ε ≤ 1/10000) (hrel : HasRelativeSieveProduct S ε)
    (D z : ℕ) (hD : 1 < D) (hslo : 3/2 ≤ s) (hshi : s ≤ 4)
    (hz : z = ⌈(D : ℝ)^(1/s)⌉₊) (hzD : z ≤ D)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, p < z) :
    S.mainSum (upperRosserWeight S.prodPrimes D) ≤
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (jurkatRichertUpperLinearSieveFactor s + 6000*ε) := by
  let n := 2*S.prodPrimes.primeFactors.card+1
  have hsdom : s ∈ KappaOneModel.closedDomain 2 n := by
    norm_num [KappaOneModel.closedDomain, KappaOneModel.eps, n, Nat.add_mod,
      Nat.mul_mod_right, Set.mem_Ici]
    linarith only [hslo]
  have hh := relative_actual_parity_bound hε hεcap hrel n D z hD hsdom hz
  have hVeq := suzukiDensityProduct_lowerRosserWeight_exact_bridge S D z hcut
    (fun p hp => (hcut p hp).trans_le hzD)
  rw [hVeq.2.1] at hh
  have hf := finiteSourceLayer_odd_le_suzukiContinuousUpperFactor_sub_one
    jr1965Section13HatLayers jr1965Section13HatSourceContract S.prodPrimes.primeFactors.card
    (by linarith only [hslo] : 1 < s)
  rw [suzukiContinuousUpperFactor_eq_jurkatRichertUpperLinearSieveFactor_of_sourceContract
    jr1965Section13HatLayers jr1965Section13HatSourceContract hslo hshi] at hf
  have hV : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    rw [← hVeq.2.1]; exact (suzukiVProduct_pos S _).le
  have hfv := mul_le_mul_of_nonneg_left hf hV
  have hb := upperRosserSuzukiExactBridge S D z hD
    (fun p hp => (hcut p hp).trans_le hzD) hcut
  change _ ≤ _ + suzukiActualT S n D z at hb
  nlinarith only [hh, hfv, hb]

#print axioms relative_lower_rosser_density
#print axioms relative_upper_rosser_density
end ChenEffective
