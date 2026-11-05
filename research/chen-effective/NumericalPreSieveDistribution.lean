import NumericalPreSieveAssembly
import NumericalUpperDistribution

noncomputable section
namespace ChenEffective
open Finset Real
open MathlibNt.SieveTheory SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable def preSieveVaryingRemainder (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ q ∈ jurkatRichertSourceMediumPrimes N,
    sieveRemainderBelow (jurkatRichertSourceConditionedBoundingSieve N q)
      (jurkatRichertSourceUpperLevel N q ε)

theorem preSieve_unweighted_varying_remainder_le_BV
    (N : ℕ) (ε : ℝ) (hEven : Even N) (hN : 2 < N) :
    preSieveVaryingRemainder N ε ≤
      jurkatRichertSourceReducedWeightedBVSum N ε +
        jurkatRichertSourceVaryingQUnconditionalCorrection N ε := by
  let Q := jurkatRichertSourceMediumPrimes N
  let P := jurkatRichertSourceSiftingProduct N
  let E : ℝ := (jurkatRichertSourceExceptionalPrimes N).card
  let D : ℕ → Finset ℕ := fun q =>
    P.divisors.filter (fun d => d < jurkatRichertSourceUpperLevel N q ε)
  let w : ℕ → ℝ := fun d => (3 : ℝ) ^ d.primeFactors.card
  let R : ℕ → ℝ := fun q =>
    sieveRemainderBelow (jurkatRichertSourceConditionedBoundingSieve N q) (jurkatRichertSourceUpperLevel N q ε)
  let M : ℕ → ℝ := fun q =>
    ∑ d ∈ D q, w d
  let B : ℕ → ℝ := fun q =>
    ∑ d ∈ D q, w d *
      BombieriVinogradov.standardPrimeAPMaxError N (q * d)
  let C : ℕ → ℝ := fun q =>
    ∑ d ∈ D q, w d *
      (BombieriVinogradov.trueLogarithmicIntegral N / Nat.totient (q * d))
  have hredPoint : ∀ q ∈ Q, ¬q ∣ N → R q ≤ B q + E * M q := by
    intro q hq hqN
    have hq' : q ∈ jurkatRichertSourceMediumPrimes N := by simpa [Q] using hq
    unfold R sieveRemainderBelow
    change (∑ d ∈ D q,
      |(jurkatRichertSourceConditionedBoundingSieve N q).rem d|) ≤ _
    calc
      (∑ d ∈ D q,
          |(jurkatRichertSourceConditionedBoundingSieve N q).rem d|) ≤
          ∑ d ∈ D q, w d *
            (BombieriVinogradov.standardPrimeAPMaxError N (q * d) + E) := by
        apply Finset.sum_le_sum
        intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hdDivMem, _⟩
        have hdvd : d ∣ jurkatRichertSourceSiftingProduct N :=
          Nat.dvd_of_mem_divisors hdDivMem
        simpa only [one_mul] using mul_le_mul
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))
          (by
            simpa [E] using
              (abs_jurkatRichertSourceConditionedRem_le_standardMax_add_exceptional
                N q d hEven hN hq' hdvd hqN))
          (abs_nonneg _) (pow_nonneg (by norm_num) _)
      _ = B q + E * M q := by
        simp only [B, M]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        ring
  have hbadPoint : ∀ q ∈ Q, q ∣ N → R q ≤ M q + C q := by
    intro q hq hqN
    have hq' : q ∈ jurkatRichertSourceMediumPrimes N := by simpa [Q] using hq
    unfold R sieveRemainderBelow
    change (∑ d ∈ D q,
      |(jurkatRichertSourceConditionedBoundingSieve N q).rem d|) ≤ _
    calc
      (∑ d ∈ D q,
          |(jurkatRichertSourceConditionedBoundingSieve N q).rem d|) ≤
          ∑ d ∈ D q, w d *
            (1 + BombieriVinogradov.trueLogarithmicIntegral N /
              Nat.totient (q * d)) := by
        apply Finset.sum_le_sum
        intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hdDivMem, _⟩
        have hdvd : d ∣ jurkatRichertSourceSiftingProduct N :=
          Nat.dvd_of_mem_divisors hdDivMem
        simpa only [one_mul] using mul_le_mul
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))
          (abs_jurkatRichertSourceConditionedRem_le_one_add_center_of_dvd
            N q d hEven hN hq' hdvd hqN)
          (abs_nonneg _) (pow_nonneg (by norm_num) _)
      _ = M q + C q := by
        simp only [M, C, w]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        ring
  have hsplit :
      ∑ q ∈ Q, R q =
        (∑ q ∈ Q.filter (fun q => ¬q ∣ N), R q) +
          ∑ q ∈ Q.filter (fun q => q ∣ N), R q := by
    have hs := Finset.sum_filter_add_sum_filter_not Q (fun q => q ∣ N) R
    calc
      ∑ q ∈ Q, R q =
          (∑ q ∈ Q.filter (fun q => q ∣ N), R q) +
            ∑ q ∈ Q.filter (fun q => ¬q ∣ N), R q := hs.symm
      _ = _ := add_comm _ _
  have hred :
      (∑ q ∈ Q.filter (fun q => ¬q ∣ N), R q) ≤
        (∑ q ∈ Q.filter (fun q => ¬q ∣ N), B q) +
          E * ∑ q ∈ Q.filter (fun q => ¬q ∣ N), M q := by
    calc
      (∑ q ∈ Q.filter (fun q => ¬q ∣ N), R q) ≤
          ∑ q ∈ Q.filter (fun q => ¬q ∣ N), (B q + E * M q) := by
        apply Finset.sum_le_sum
        intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqQ, hqN⟩
        exact hredPoint q hqQ hqN
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hbad :
      (∑ q ∈ Q.filter (fun q => q ∣ N), R q) ≤
        (∑ q ∈ Q.filter (fun q => q ∣ N), M q) +
          ∑ q ∈ Q.filter (fun q => q ∣ N), C q := by
    calc
      (∑ q ∈ Q.filter (fun q => q ∣ N), R q) ≤
          ∑ q ∈ Q.filter (fun q => q ∣ N), (M q + C q) := by
        apply Finset.sum_le_sum
        intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqQ, hqN⟩
        exact hbadPoint q hqQ hqN
      _ = _ := Finset.sum_add_distrib
  have hMnonneg : ∀ q, 0 ≤ M q := by
    intro q
    apply Finset.sum_nonneg
    intro d hd
    exact pow_nonneg (by norm_num) _
  have hMred :
      (∑ q ∈ Q.filter (fun q => ¬q ∣ N), M q) ≤ ∑ q ∈ Q, M q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun q _ _ => hMnonneg q)
  have hMbad :
      (∑ q ∈ Q.filter (fun q => q ∣ N), M q) ≤ ∑ q ∈ Q, M q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun q _ _ => hMnonneg q)
  unfold preSieveVaryingRemainder
  change (∑ q ∈ Q, R q) ≤ _
  rw [hsplit]
  calc
    (∑ q ∈ Q.filter (fun q => ¬q ∣ N), R q) +
          ∑ q ∈ Q.filter (fun q => q ∣ N), R q ≤
        ((∑ q ∈ Q.filter (fun q => ¬q ∣ N), B q) +
          E * ∑ q ∈ Q.filter (fun q => ¬q ∣ N), M q) +
        ((∑ q ∈ Q.filter (fun q => q ∣ N), M q) +
          ∑ q ∈ Q.filter (fun q => q ∣ N), C q) :=
      add_le_add hred hbad
    _ ≤ (∑ q ∈ Q.filter (fun q => ¬q ∣ N), B q) +
        (E + 1) * (∑ q ∈ Q, M q) +
          ∑ q ∈ Q.filter (fun q => q ∣ N), C q := by
      have hE : 0 ≤ E := by dsimp [E]; positivity
      nlinarith [mul_le_mul_of_nonneg_left hMred hE, hMbad]
    _ = jurkatRichertSourceReducedWeightedBVSum N ε +
        jurkatRichertSourceVaryingQUnconditionalCorrection N ε := by
      simp only [jurkatRichertSourceReducedWeightedBVSum,
        jurkatRichertSourceVaryingQUnconditionalCorrection,
        jurkatRichertSourceVaryingQWeightMass,
        jurkatRichertSourceNonreducedCenterSum, Q, P, E, D, w, B, C, M]
      ring

theorem preSieve_varying_remainder_cube (m N : ℕ) (hm : 0 < m)
    (hN : max (weightedNumericalThreshold 3 m) (logPowerCutoff 100) ≤ N) (hEven : Even N) :
    preSieveVaryingRemainder N (1 / (m : ℝ)) ≤
      (varyingNumericalBudget : ℝ) * N / Real.log N ^ (3 : ℕ) := by
  have hw := numerical_weighted_distribution 3 m N hm ((le_max_left _ _).trans hN)
  have hcut : logPowerCutoff 100 ≤ N := (le_max_right _ _).trans hN
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hcut
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp := log_pow_le_rpow_inv_explicit (k := 10) (m := 10) (by norm_num) (by norm_num) hcut
  have hc := numerical_varying_correction hN9
    (show (0 : ℝ) ≤ 1 / (m : ℝ) by positivity)
  have hc' : jurkatRichertSourceVaryingQUnconditionalCorrection N (1 / (m : ℝ)) ≤
      3000 * N / Real.log N ^ (3 : ℕ) := by
    apply hc.trans
    apply (le_div_iff₀ (pow_pos hl 3)).mpr
    have he : (N : ℝ) ^ (9 / 10 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) = N := by
      rw [← Real.rpow_add hN0]
      norm_num
    have hh := mul_le_mul_of_nonneg_left hp
      (show 0 ≤ 3000 * (N : ℝ) ^ (9 / 10 : ℝ) by positivity)
    norm_num only [Nat.cast_ofNat] at hh
    have he' : 3000 * (N : ℝ) ^ (9 / 10 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) = 3000 * N := by
      rw [mul_assoc, he]
    have ht : Real.log (N : ℝ) ^ (7 : ℕ) * Real.log N ^ (3 : ℕ) = Real.log N ^ (10 : ℕ) := by ring
    nlinarith only [hh, he', congrArg (fun x : ℝ => 3000 * (N : ℝ) ^ (9 / 10 : ℝ) * x) ht]
  have hf := preSieve_unweighted_varying_remainder_le_BV
    N (1 / (m : ℝ)) hEven (by omega)
  rw [varyingNumericalBudget_eq]
  calc
    _ ≤ _ := hf
    _ ≤ weightedNumericalConstant 3 * N / Real.log N ^ (3 : ℕ) +
        3000 * N / Real.log N ^ (3 : ℕ) := add_le_add hw hc'
    _ = _ := by ring

theorem preSieve_varying_distribution (m d N : ℕ) (hm : 0 < m) (hd : 0 < d)
    (hN : varyingNumericalThreshold m d ≤ N) (hEven : Even N) :
    preSieveVaryingRemainder N (1 / (m : ℝ)) ≤
      (1 / (d : ℝ)) * SingularSeries.liuSingularSeries N * N / Real.log N ^ (2 : ℕ) := by
  have hcut : max (weightedNumericalThreshold 3 m) (logPowerCutoff 100) ≤ N :=
    (le_max_left _ _).trans hN
  have hb := preSieve_varying_remainder_cube m N hm hcut hEven
  have hlog := log_ge_power_three ((le_max_right _ _).trans hN)
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le 100).trans ((le_max_right _ _).trans hcut)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog' : 2 * (varyingNumericalBudget : ℝ) * d ≤ Real.log N := by
    push_cast at hlog
    linarith only [hlog]
  have hs := half_le_liuSingularSeries N
  have hnum : (varyingNumericalBudget : ℝ) ≤
      ((1 / (d : ℝ)) * SingularSeries.liuSingularSeries N) * Real.log N := by
    have hh := mul_le_mul_of_nonneg_right hs hl.le
    calc
      _ ≤ (SingularSeries.liuSingularSeries N * Real.log N) / d := by
        apply (le_div_iff₀ hdR).mpr
        nlinarith only [hh, hlog']
      _ = _ := by ring
  apply hb.trans
  apply (div_le_div_iff₀ (pow_pos hl 3) (pow_pos hl 2)).mpr
  have hh := mul_le_mul_of_nonneg_right hnum
    (show 0 ≤ (N : ℝ) * Real.log N ^ (2 : ℕ) by positivity)
  nlinarith only [hh]


#print axioms preSieve_varying_distribution
end ChenEffective