import ExplicitBVAssembly
import NumericalThresholds
import MathlibNt.SieveTheory.Switching.RosserSieveAsymptotics

/-! Pointwise propagation of a finite BV bound into Chen's base-sieve
distribution remainder, including numerical modulus and exceptional-fibre
cutoffs. This is the distribution input to the lower bound, not the full
weighted lower-sieve theorem. -/
namespace ChenEffective
open MathlibNt.SieveTheory
open SwitchingPrinciple SingularSeries
open Finset
noncomputable section

def lowerDistributionThreshold (m d b : ℕ) : ℕ :=
  max (highBVThreshold 3)
    (max (logPowerCutoff (m * highBVExponent 3))
      (max (logPowerCutoff 4) (3 ^ (4 * b * d + 16 * d + 1))))

theorem explicit_source_modulus_in_BV
    (B m N : ℕ) (hm : 0 < m) (hN : logPowerCutoff (m * B) ≤ N) :
    LiuWeight.liuSourceDEpsilon N (1 / (m : ℝ)) ≤ LiuWeight.panModulusCutoff N (B : ℝ) := by
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hg := log_pow_le_rpow_inv_explicit hm (le_refl (m * B)) hN
  unfold LiuWeight.liuSourceDEpsilon LiuWeight.panModulusCutoff
  apply Nat.floor_mono
  rw [Real.rpow_sub hN0]
  rw [Real.rpow_natCast]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _)
    (pow_pos hlog B) hg

/-- A finite BV estimate of order three pays the base-sieve remainder
with target coefficient 1/d, at a completely specified additional cutoff. -/
theorem explicit_base_distribution_from_BV
    (m d b N : ℕ) (hm : 3 ≤ m) (hd : 0 < d)
    (hN : lowerDistributionThreshold m d b ≤ N) (hEven : Even N)
    (C : ℝ) (hC : C ≤ b)
    (hBV : (∑ q ∈ Finset.Icc 1 (LiuWeight.panModulusCutoff N (highBVExponent 3 : ℝ)),
      BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
        C * (N : ℝ) / Real.log N ^ (3 : ℕ)) :
    jurkatRichertSourceRemainderSum N (1 / (m : ℝ)) ≤
      (1 / (d : ℝ)) * liuSingularSeries N * (N : ℝ) / Real.log N ^ (2 : ℕ) := by
  have hhigh : highBVThreshold 3 ≤ N := (le_max_left _ _).trans hN
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hhigh
  have hroot : logPowerCutoff (m * highBVExponent 3) ≤ N := by
    unfold lowerDistributionThreshold at hN; omega
  have hfour : logPowerCutoff 4 ≤ N := by unfold lowerDistributionThreshold at hN; omega
  have hscalar : 3 ^ (4 * b * d + 16 * d + 1) ≤ N := by
    unfold lowerDistributionThreshold at hN; omega
  have hL := log_ge_power_three hscalar
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hL
  clear hN hhigh hscalar
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have heps : 0 < 1 / (m : ℝ) := one_div_pos.mpr hmR
  have hepsHalf : 1 / (m : ℝ) < 1 / 2 :=
    (div_lt_div_iff₀ hmR (by norm_num : (0 : ℝ) < 2)).mpr
      (by
        have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
        linarith only [hm3])
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcut : LiuWeight.liuSourceDEpsilon N (1 / (m : ℝ)) ≤
      LiuWeight.panModulusCutoff N (highBVExponent 3 : ℝ) :=
    explicit_source_modulus_in_BV _ m N (by omega) hroot
  clear hroot
  let D := (jurkatRichertSourceSiftingProduct N).divisors.filter
    (fun q : ℕ => (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 - 1 / (m : ℝ)))
  let E := jurkatRichertSourceExceptionalPrimes N
  let Q := Finset.Icc 1 (LiuWeight.panModulusCutoff N (highBVExponent 3 : ℝ))
  have hDsub : D ⊆ Q := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hdiv, hlevel⟩
    have hq0 : q ≠ 0 := by
      intro hz
      have hdiv' := Nat.dvd_of_mem_divisors hdiv
      rw [hz] at hdiv'
      exact jurkatRichertSourceSiftingProduct_ne_zero N (by simpa using hdiv')
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hq0,
      (Nat.le_floor hlevel).trans hcut⟩
  have hmax : (∑ q ∈ D, BombieriVinogradov.standardPrimeAPMaxError N q) ≤
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) := by
    calc
      _ ≤ ∑ q ∈ Q, BombieriVinogradov.standardPrimeAPMaxError N q :=
        Finset.sum_le_sum_of_subset_of_nonneg hDsub
          (fun q _ _ => BombieriVinogradov.standardPrimeAPMaxError_nonneg N q)
      _ ≤ ∑ q ∈ Q, BombieriVinogradov.standardPrimeAPPrefixMaxError N q :=
        BombieriVinogradov.sum_standardPrimeAPMaxError_le_prefixMaxError N Q
      _ ≤ _ := hBV
  have hcoef : C ≤ (1 / (4 * (d : ℝ))) * Real.log N := by
    calc
      C ≤ Real.log N / (4 * (d : ℝ)) := by
        apply (le_div_iff₀ (by positivity : 0 < 4 * (d : ℝ))).mpr
        nlinarith only [hC, hL, hdR, show (0 : ℝ) ≤ b from Nat.cast_nonneg b]
      _ = _ := by ring
  have hmaxPaid : (∑ q ∈ D, BombieriVinogradov.standardPrimeAPMaxError N q) ≤
      (1 / (4 * (d : ℝ))) * N / Real.log N ^ (2 : ℕ) := by
    apply hmax.trans
    apply (div_le_div_iff₀ (pow_pos hlog 3) (pow_pos hlog 2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg (Real.log (N : ℝ))))]
  have hgrowth : 16 * (d : ℝ) * Real.log N ^ (3 : ℕ) ≤ Real.sqrt N := by
    calc
      _ ≤ Real.log N * Real.log N ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_right (by
          nlinarith only [hL, hdR, show (0 : ℝ) ≤ b from Nat.cast_nonneg b])
          (pow_nonneg hlog.le 3)
      _ = Real.log N ^ (4 : ℕ) := by ring
      _ ≤ _ := log_pow_le_sqrt_explicit hfour
  have hendpointPaid : (D.card : ℝ) * E.card ≤
      (1 / (4 * (d : ℝ))) * N / Real.log N ^ (2 : ℕ) := by
    have hep := jurkatRichertSource_exceptional_endpoint_le N (1 / (m : ℝ))
      (by omega) heps hepsHalf
    have hp : (N : ℝ) ^ (1 / 2 - 1 / (m : ℝ)) ≤ Real.sqrt N := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [heps])
    have hlogtwo : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hstep : 2 * (N : ℝ) ^ (1 / 2 - 1 / (m : ℝ)) * Real.log N / Real.log 2 ≤
        4 * Real.sqrt N * Real.log N := by
      apply (div_le_iff₀ (by linarith only [hlogtwo])).mpr
      have hmul := mul_le_mul_of_nonneg_right hp hlog.le
      have hmul2 := mul_le_mul_of_nonneg_right hlogtwo.le
        (show 0 ≤ 4 * Real.sqrt N * Real.log N by positivity)
      nlinarith only [hmul, hmul2]
    have hfinal : 4 * Real.sqrt N * Real.log N ≤
        (1 / (4 * (d : ℝ))) * N / Real.log N ^ (2 : ℕ) := by
      apply (le_div_iff₀ (pow_pos hlog 2)).mpr
      have hs := mul_le_mul_of_nonneg_right hgrowth (Real.sqrt_nonneg (N : ℝ))
      rw [Real.mul_self_sqrt hN0.le] at hs
      calc
        _ ≤ (N : ℝ) / (4 * (d : ℝ)) := by
          apply (le_div_iff₀ (by positivity : 0 < 4 * (d : ℝ))).mpr
          nlinarith only [hs]
        _ = _ := by ring
    exact hep.trans (hstep.trans hfinal)
  have hreduction := jurkatRichertSourceRemainderSum_le_standardMax_add_exceptional
    N (1 / (m : ℝ)) hEven (by omega)
  have hS := half_le_liuSingularSeries N
  have hscale : 0 ≤ (N : ℝ) / Real.log N ^ (2 : ℕ) := by positivity
  calc
    _ ≤ (∑ q ∈ D, BombieriVinogradov.standardPrimeAPMaxError N q) +
          (D.card : ℝ) * E.card := hreduction
    _ ≤ (1 / (4 * (d : ℝ))) * N / Real.log N ^ (2 : ℕ) +
          (1 / (4 * (d : ℝ))) * N / Real.log N ^ (2 : ℕ) :=
      add_le_add hmaxPaid hendpointPaid
    _ = (1 / (d : ℝ)) * (1 / 2) * (N : ℝ) / Real.log N ^ (2 : ℕ) := by ring
    _ ≤ _ := by
      have hc := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 1 / (d : ℝ))
      simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_right hc hscale

/-- Join the finite BV assembly directly to Chen's base distribution input.
At exponent three, the conductor cutoff exponent is 106, the primitive
logarithmic saving is 114, and the principal saving is 6. -/
theorem explicit_base_distribution_of_low_inputs
    (m d b N : ℕ) (hm : 3 ≤ m) (hd : 0 < d)
    (hN : lowerDistributionThreshold m d b ≤ N) (hEven : Even N)
    (Kpsi Kprincipal : ℝ) (hKpsi : 0 < Kpsi) (hKprincipal : 0 < Kprincipal)
    (hConstant : bvConstant Kpsi Kprincipal ≤ b)
    (hPsi : ∀ q ∈ Finset.Icc 2 (AnalyticNumberTheory.LargeSieve.logConductorThreshold N 106),
      ∀ ψ : AnalyticNumberTheory.LargeSieve.PrimitiveCharacter q, ψ.1 ≠ 1 →
        AnalyticNumberTheory.LargeSieve.primitivePrefixAmplitude
          AnalyticNumberTheory.LargeSieve.vonMangoldtIntegerCoeff N q ψ ≤
            Kpsi * (N : ℝ) / Real.log N ^ (114 : ℕ))
    (hPrincipal : AnalyticNumberTheory.LargeSieve.globalPartialSummationSource N ≤
      Kprincipal * (N : ℝ) / Real.log N ^ (6 : ℕ)) :
    jurkatRichertSourceRemainderSum N (1 / (m : ℝ)) ≤
      (1 / (d : ℝ)) * liuSingularSeries N * (N : ℝ) / Real.log N ^ (2 : ℕ) := by
  have hh : highBVThreshold 3 ≤ N := (le_max_left _ _).trans hN
  have hBV := explicit_BV_at 3 N hh Kpsi Kprincipal hKpsi hKprincipal
    (by simpa only [highBVConductorExponent, Nat.reduceAdd, Nat.reduceMul] using hPsi)
    hPrincipal
  exact explicit_base_distribution_from_BV m d b N hm hd hN hEven
    (bvConstant Kpsi Kprincipal) hConstant hBV

#print axioms explicit_base_distribution_from_BV
#print axioms explicit_base_distribution_of_low_inputs
end
end ChenEffective
