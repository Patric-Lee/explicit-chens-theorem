import NumericalMixedUpper
import NumericalBaseDensity
import NumericalMediumPrimeShift
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserDensityEndpointDirect
import MathlibNt.SieveTheory.Switching.PrimePenaltyAsymptotics

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne
open JurkatRichert1965ChenGammaOneQOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
attribute [local irreducible] logPowerCutoff

def mediumUpperScalarThreshold (r : ℕ) : ℕ :=
  sqrtSuzukiScalarThreshold (sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK) r
def mediumUpperDensityThreshold (r : ℕ) : ℕ := (mediumUpperScalarThreshold r+1)^10

theorem mediumUpperScalarThreshold_three (r : ℕ) : 3 ≤ mediumUpperScalarThreshold r := by
  have hh : 1 ≤ max (logPowerCutoff 32) (max 152587890625 (4096*(sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK+1)^2*r^2)) :=
    (by norm_num : 1 ≤ 152587890625).trans ((le_max_left _ _).trans (le_max_right _ _))
  exact (show 3^1 ≤ 3^max (logPowerCutoff 32) (max 152587890625 (4096*(sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK+1)^2*r^2)) from
    Nat.pow_le_pow_right (by norm_num) hh)

theorem numerical_upper_level_parameters {D r : ℕ} (hD : mediumUpperScalarThreshold r ≤ D) :
    1 < (D : ℝ) ∧ (5 : ℝ)^16 ≤ Real.log (D : ℝ) ∧ 4 ≤ sourceSigma (D : ℝ) 16 := by
  have hD3 : 3 ≤ D := (mediumUpperScalarThreshold_three r).trans hD
  have hD1 : (1 : ℝ) < D := by exact_mod_cast (show 1 < D by omega)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlog := log_ge_power_three hD
  have hL5 : (5 : ℝ)^16 ≤ Real.log (D : ℝ) := by
    have hh : (152587890625 : ℝ) ≤
        (max (logPowerCutoff 32) (max 152587890625 (4096*(sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK+1)^2*r^2)) : ℕ) :=
      by exact_mod_cast ((le_max_left 152587890625 (4096*(sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK+1)^2*r^2)).trans (le_max_right _ _))
    norm_num only [Nat.reducePow] at hh ⊢
    exact hh.trans hlog
  have hL0 : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have hroot : (4 : ℝ) ≤ (Real.log (D : ℝ))^(1/16 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) hL0.le (by norm_num : (0 : ℝ) < 16)).mpr
    norm_num at hL5 ⊢
    linarith only [hL5]
  have hinner : Real.exp 1 ≤ Real.log (27*(D : ℝ)) := by
    rw [Real.log_mul (by norm_num) hD0.ne']
    have h27 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 27)
    have he := Real.exp_one_lt_d9
    norm_num only [Nat.reducePow] at hL5
    linarith only [h27,he,hL5]
  have hll : 1 ≤ Real.log (Real.log (27*(D : ℝ))) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hinner
  refine ⟨hD1,hL5,?_⟩
  unfold sourceSigma
  simpa only [mul_one] using mul_le_mul hroot hll (by norm_num : (0 : ℝ) ≤ 1) (Real.rpow_nonneg hL0.le _)

theorem numerical_upper_suzuki_error {D r depth : ℕ} (hD : mediumUpperScalarThreshold r ≤ D)
    (hr : 0 < r) (hdepth : Odd depth) {s : ℝ} (hs : 3/2 ≤ s) (hs4 : s ≤ 4) :
    numericalEffectiveSuzukiCoefficient*Real.exp (Real.sqrt refinedLocalProductK)*
        errorEnvelope jr1965Section13HatLayers depth D 16 s*(Real.log (D : ℝ))^(-(1/2 : ℝ)) < 1/(r : ℝ) := by
  obtain ⟨hD1,hL5,_⟩ := numerical_upper_level_parameters hD
  have hL0 : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have he := numerical_exp_sqrt_round_bound baseSuzukiK_one baseSuzukiK_bound
  let a := numericalEffectiveSuzukiCoefficient*Real.exp (Real.sqrt refinedLocalProductK)*16
  have ha0 : 0 ≤ a := by dsimp [a]; exact mul_nonneg (mul_nonneg numericalEffectiveSuzukiCoefficient_nonneg (Real.exp_pos _).le) (by norm_num)
  have haM : a ≤ sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK := by
    have hc : (0 : ℝ) ≤ baseSuzukiC := Nat.cast_nonneg _
    have hh := mul_le_mul baseSuzukiC_bound he (Real.exp_pos _).le hc
    dsimp [a,sqrtSuzukiAmplitudeCap]
    push_cast
    nlinarith only [hh,mul_nonneg hc (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Nat.sqrt baseSuzukiK + 1))]
  have hscalar := numerical_suzuki_scalar_absorption ((sqrt_scalar_old_le _ _).trans hD) hr (s := 1) (by norm_num) (by norm_num) ha0 haM
  have hE := errorEnvelope_odd_le_sixteen_on_upper_window jr1965Section13HatLayers
    jr1965Section13HatSourceContract.toSection13HatContract hdepth (by norm_num) hD1
    (show (4 : ℝ)^(16 : ℝ) ≤ Real.log (D : ℝ) by norm_num at hL5 ⊢; linarith only [hL5]) hs hs4
  have hbase : 1 ≤ (1+(1 : ℝ)^16/Real.log (D : ℝ))^(1 : ℝ) := by norm_num; positivity
  have hdecay : 0 ≤ (Real.log (D : ℝ))^(-(1/2 : ℝ)) := Real.rpow_nonneg hL0.le _
  calc
    _ ≤ a*(Real.log (D : ℝ))^(-(1/2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE
        (mul_nonneg numericalEffectiveSuzukiCoefficient_nonneg (Real.exp_pos _).le)) hdecay
    _ ≤ a*(1+(1 : ℝ)^16/Real.log (D : ℝ))^(1 : ℝ)*(Real.log (D : ℝ))^(-(1/2 : ℝ)) := by
      have hh := mul_le_mul_of_nonneg_left hbase ha0
      exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hh) hdecay
    _ < _ := hscalar

theorem numerical_conditioned_upper_density {N q r : ℕ} (hr : 0 < r)
    (hN2 : 2 ≤ N) (hN : mediumUpperDensityThreshold r ≤ N)
    (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
    (jurkatRichertSourceConditionedBoundingSieve N q).mainSum (jurkatRichertSourceVaryingQUpperRosserWeight N q mediumPrimeEpsilon) ≤
      (jurkatRichertUpperLinearSieveFactor (jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon)+1/(r : ℝ))*
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceConditionedBoundingSieve N q) := by
  let S := jurkatRichertSourceConditionedBoundingSieve N q
  let z : ℝ := (N : ℝ)^(1/10 : ℝ)
  let Δ : ℝ := (N : ℝ)^(1/2-mediumPrimeEpsilon)/(q : ℝ)
  let s := jurkatRichertSourceUpperSieveRatio N q mediumPrimeEpsilon
  let D := Nat.floor Δ+1
  have hk3 := mediumUpperScalarThreshold_three r
  have hcut : mediumUpperScalarThreshold r ≤ jurkatRichertSourceZ N-1 := numerical_source_cutoff (by omega) hN
  have hzcut : (mediumUpperScalarThreshold r : ℝ) ≤ z := by
    have hh : (mediumUpperScalarThreshold r : ℝ) ≤ (jurkatRichertSourceZ N-1 : ℕ) := by exact_mod_cast hcut
    have hfloor : ((jurkatRichertSourceZ N-1 : ℕ) : ℝ) ≤ z := by
      dsimp only [z,jurkatRichertSourceZ]
      simp only [Nat.add_sub_cancel]
      exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) (1/10 : ℝ))
    exact hh.trans hfloor
  have hz2 : 2 ≤ z := (show (2 : ℝ) ≤ mediumUpperScalarThreshold r by exact_mod_cast (show 2 ≤ mediumUpperScalarThreshold r by omega)).trans hzcut
  have hqprime := (mem_filter.mp hq).2.1
  have hΔ : 0 < Δ := div_pos (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _) (by exact_mod_cast hqprime.pos)
  have hs := jurkatRichertSourceUpperSieveRatio_mem (by omega : 1 < N) numerical_medium_epsilon.1 numerical_medium_epsilon.2 hq
  have hgeom := real_level_to_natCeil_geometry hz2 hΔ (s := s) rfl hs.1
  obtain ⟨hD2,hΔD,hzroot,hzceil⟩ := hgeom
  have hzD : z < (D : ℝ) := hzroot.trans_le
    (Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ D by omega)) ((div_le_one (by linarith only [hs.1] : 0 < s)).mpr (by linarith only [hs.1])))
  have hDcut : mediumUpperScalarThreshold r ≤ D := by exact_mod_cast hzcut.trans hzD.le
  have hSigma : s ≤ sourceSigma (D : ℝ) 16 := hs.2.trans (numerical_upper_level_parameters hDcut).2.2
  have hlocal := jurkatRichertSourceConditioned_dimensionOneLocalProductBound (q := q) (numerical_refined_source_local_product N)
  let depth := 2 * S.prodPrimes.primeFactors.card + 1
  have hodd : Odd depth := by dsimp [depth]; exact ⟨_, rfl⟩
  have hsdom : s ∈ KappaOneModel.parityDomain 2 depth := by
    simp only [KappaOneModel.parityDomain, Nat.odd_iff.mp hodd, ite_true, Set.mem_Ioi]
    linarith only [hs.1]
  have hSuzuki := numerical_mixed_suzuki_window jr1965Section13HatLayers jr1965Section13HatSourceContract
    refined_local_product_two (show mixedSuzukiSeparator ≤ mixedSuzukiSeparator from le_rfl) S hlocal
    depth D (by dsimp [depth]; omega) hD2 s hsdom hs.1 (hs.2.trans (by norm_num : (4 : ℝ) ≤ 5)) hSigma hzceil (sqrt_scalar_log_gate hDcut)
  have hpoint := upperRosserDensity_at_natCeil_of_point jr1965Section13HatLayers jr1965Section13HatSourceContract S
    (C := numericalEffectiveSuzukiCoefficient) (K := refinedLocalProductK) (d := (16 : ℝ)) (Δ := (1 / 2 : ℝ))
    D s hD2 hs.1 hs.2
    (fun p hp => Nat.lt_ceil.mpr ((jurkatRichertSourceConditioned_primeFactor_le_cutoff N q p hp).trans_lt hzroot))
    (by simpa only [numericalEffectiveSuzukiCoefficient, depth] using hSuzuki)
  have hfactor := suzukiContinuousUpperFactor_eq_jurkatRichertUpperLinearSieveFactor_of_sourceContract
    jr1965Section13HatLayers jr1965Section13HatSourceContract hs.1 hs.2
  rw [hfactor] at hpoint
  have hError := numerical_upper_suzuki_error hDcut hr (show Odd (2*S.prodPrimes.primeFactors.card+1) from ⟨_,rfl⟩) hs.1 hs.2
  have hV0 : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    exact prod_nonneg (fun p hp => sub_nonneg.mpr (S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
      ((Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp).2).le)
  have hh := mul_le_mul_of_nonneg_left hError.le hV0
  change S.mainSum (upperRosserWeight S.prodPrimes D) ≤ _
  dsimp only [numericalEffectiveSuzukiCoefficient,mixedSuzukiCoefficient,s,S] at hpoint hh ⊢
  nlinarith only [hpoint,hh]

#print axioms numerical_conditioned_upper_density
end ChenEffective
