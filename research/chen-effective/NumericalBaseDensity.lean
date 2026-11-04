import NumericalMixedWindow
import NumericalSqrtAbsorption
import NumericalLowerFactor
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiChenVaryingFamilyLowerDensity

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory
open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne
open SwitchingPrinciple.SuzukiLemma144Equation1410
open JurkatRichert1965ChenGammaOneQOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- Integer caps of closed numerical formulas, with no selected witnesses. -/
def baseSuzukiC : ℕ := ⌈max 1 numericalEffectiveSuzukiCoefficient⌉₊
def baseSuzukiK : ℕ := ⌈max 1 refinedLocalProductK⌉₊

theorem baseSuzukiK_eq : baseSuzukiK = 10 ^ 12 := by
  norm_num [baseSuzukiK, refinedLocalProductK]

theorem baseSuzukiC_bound : numericalEffectiveSuzukiCoefficient ≤ baseSuzukiC :=
  (le_max_right _ _).trans (Nat.le_ceil _)
theorem baseSuzukiK_bound : refinedLocalProductK ≤ baseSuzukiK :=
  (le_max_right _ _).trans (Nat.le_ceil _)
theorem baseSuzukiK_one : 1 ≤ baseSuzukiK := by
  have h : (1 : ℝ) ≤ baseSuzukiK := (le_max_left _ _).trans (Nat.le_ceil _)
  exact_mod_cast h
theorem numericalEffectiveSuzukiCoefficient_nonneg : 0 ≤ numericalEffectiveSuzukiCoefficient := by
  unfold numericalEffectiveSuzukiCoefficient
  exact mul_nonneg (by norm_num) ((by norm_num : (0 : ℝ) ≤ 36).trans (le_max_left _ _))

def baseDensityThreshold (r : ℕ) : ℕ :=
  max 2 (max suzukiCoordinateThreshold (sqrtSuzukiErrorThreshold baseSuzukiC baseSuzukiK r))

/-- Pointwise adaptive-depth lower density at Chen's literal floor level.
The source-family index and recursion depth are independent. -/
theorem numerical_base_density {N r : ℕ} {ε : ℝ}
    (hN : baseDensityThreshold r ≤ N) (hr : 0 < r)
    (hε0 : 0 ≤ ε) (hε : ε < 1/10) :
    AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) *
        (dimensionOneLowerLinearSieveFactor (chenS ε) - 1/(r : ℝ)) ≤
      (jurkatRichertSourceBoundingSieve N).mainSum (jurkatRichertBaseLowerRosserWeight N ε) := by
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hgate : suzukiCoordinateThreshold ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have herr : sqrtSuzukiErrorThreshold baseSuzukiC baseSuzukiK r ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let S := jurkatRichertSourceBoundingSieve N
  let D := chenLevel N ε
  let s := chenS ε
  let z := chenZ N ε
  let depth := 2*((suzukiSupportedBelow S z).card+1)
  have hs4 : 4 ≤ s := by dsimp [s,chenS]; linarith only [hε]
  have hs5 : s ≤ 5 := by dsimp [s,chenS]; linarith only [hε0]
  have hD2 : 2 ≤ D := by
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hp := Real.one_lt_rpow hNr (show 0 < 1/2-ε by linarith only [hε])
    have hd : (1 : ℝ) < D := hp.trans (lt_cast_floor_add_one _)
    have hdNat : 1 < D := by exact_mod_cast hd
    omega
  have hzD : z ≤ D := chenZ_le_chenLevel hD2 (by linarith only [hs4])
  have hz2 : 2 ≤ z := by
    have hp := Real.one_lt_rpow (show (1 : ℝ) < D by exact_mod_cast (show 1 < D by omega))
      (show 0 < 1/s by positivity)
    have hh : (1 : ℝ) < z := hp.trans_le (Nat.le_ceil _)
    have hzNat : 1 < z := by exact_mod_cast hh
    omega
  have hdepth : 1 ≤ depth := by dsimp [depth]; omega
  have heven : Even depth := by dsimp [depth]; exact even_two_mul _
  have hsdom : s ∈ KappaOneModel.parityDomain 2 depth := by
    simp [KappaOneModel.parityDomain,Nat.even_iff.mp heven,show 2 ≤ s by linarith only [hs4]]
  have hsigma : s ≤ sourceSigma (D : ℝ) 16 := numerical_suzuki_coordinate_gate hgate hε0 hε
  have hSuzuki := numerical_mixed_suzuki_window jr1965Section13HatLayers jr1965Section13HatSourceContract
    refined_local_product_two (show mixedSuzukiSeparator ≤ mixedSuzukiSeparator from le_rfl) S
    (numerical_refined_source_local_product N) depth D hdepth hD2 s hsdom (by linarith only [hs4]) hs5 hsigma hz2
  have hdensity := lowerRosserSetDensitySum_eq_euler_sub_suzukiActualT_all_supported
    S (show 1 < D by omega) hzD
  have hEuler := sourceDiscreteEuler_eq_suzukiVProduct_nat S z
  have hfactor := suzukiContinuousLowerFactor_le_adaptive_finiteLowerFactor
    jr1965Section13HatSourceContract (suzukiSupportedBelow S z) (show 2 ≤ s by linarith only [hs4])
  rw [suzukiContinuousLowerFactor_eq_dimensionOne_of_sourceContract
    jr1965Section13HatSourceContract hs4 (by linarith only [hs5])] at hfactor
  have hV : 0 ≤ suzukiVProduct S (z : ℝ) := (suzukiVProduct_pos S _).le
  have hfactorV := mul_le_mul_of_nonneg_left hfactor hV
  have hError := numerical_chen_sqrt_suzuki_error herr baseSuzukiK_one hr
    numericalEffectiveSuzukiCoefficient_nonneg baseSuzukiC_bound baseSuzukiK_bound hε0 hε depth
  have hbound : suzukiVProduct S (z : ℝ)*(dimensionOneLowerLinearSieveFactor s-1/(r : ℝ)) ≤
      lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) := by
    rw [hdensity,hEuler]
    dsimp only [suzukiFiniteLowerFactor] at hfactorV
    change _ < 1/(r : ℝ) at hError
    have he := mul_le_mul_of_nonneg_left hError.le hV
    dsimp only [depth,z,chenZ,D,s,S,numericalEffectiveSuzukiCoefficient,mixedSuzukiCoefficient] at hSuzuki hfactorV he ⊢
    linarith only [hSuzuki,hfactorV,he]
  have hcutZ : ∀ p ∈ S.prodPrimes.primeFactors, p < z := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpDvd := (Nat.mem_primeFactors_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp |>.2
    exact chen_le_tenth_rpow_imp_lt_chenZ (by omega) hε0 hε
      ((prime_dvd_jurkatRichertSourceSiftingProduct hpPrime).mp hpDvd).2.1
  have hbridge := suzukiDensityProduct_lowerRosserWeight_exact_bridge S D z hcutZ
    (fun p hp => (hcutZ p hp).trans_le hzD)
  rw [← hbridge.1,hbridge.2.1] at hbound
  exact hbound

/-- Explicit continuity and explicit Suzuki absorption share a single budget. -/
theorem numerical_base_density_near_five {N r : ℕ} (hr : 0 < r)
    (hN : baseDensityThreshold (2*r) ≤ N) :
    (jurkatRichertBaseSieveFactor jurkatRichertJ-1/(r : ℝ))*
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) ≤
      (jurkatRichertSourceBoundingSieve N).mainSum
        (jurkatRichertBaseLowerRosserWeight N (lowerSieveEpsilon r)) := by
  obtain ⟨he0,he,hfactor⟩ := numerical_lower_epsilon r hr
  have hh := numerical_base_density hN (by omega : 0 < 2*r) he0.le he
  have hprod : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) := by
    rw [← suzukiVProduct_eq_sieveProductPrimeFactors_of_all_lt
      (jurkatRichertSourceBoundingSieve N) (z := (chenZ N (lowerSieveEpsilon r) : ℝ)) ?_]
    · exact (suzukiVProduct_pos _ _).le
    · intro p hp
      exact_mod_cast chen_le_tenth_rpow_imp_lt_chenZ
        (show 1 ≤ N by have h := (le_max_left _ _).trans hN; omega) he0.le he
        ((prime_dvd_jurkatRichertSourceSiftingProduct (Nat.prime_of_mem_primeFactors hp)).mp
          ((Nat.mem_primeFactors_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp).2).2.1
  rw [dimensionOneLowerLinearSieveFactor_five] at hfactor
  apply le_trans (mul_le_mul_of_nonneg_right (show
    jurkatRichertBaseSieveFactor jurkatRichertJ-1/(r : ℝ) ≤
      dimensionOneLowerLinearSieveFactor (chenS (lowerSieveEpsilon r))-1/((2*r : ℕ) : ℝ) by
        push_cast
        have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
        have heq : 1/(r : ℝ) = 2*(1/(2*(r : ℝ))) := by field_simp
        linarith only [hfactor,heq]) hprod)
  simpa only [mul_comm] using hh

#print axioms numerical_base_density
#print axioms numerical_base_density_near_five
end ChenEffective
