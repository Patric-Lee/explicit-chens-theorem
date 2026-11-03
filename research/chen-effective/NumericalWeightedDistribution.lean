import NumericalWeightedEnvelope
import ExplicitChenLower

namespace ChenEffective
open Finset Real
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.Richert1969
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem numerical_combined_squarefree {N d : ℕ} {ε : ℝ}
    (hd : d ∈ chenReducedCombinedModuli N ε) : Squarefree d := by
  rcases Finset.mem_biUnion.mp hd with ⟨q, hq, hmImage⟩
  rcases Finset.mem_image.mp hmImage with ⟨r, hr, rfl⟩
  have hqSource := (Finset.mem_filter.mp hq).1
  have hqPrime := (Finset.mem_filter.mp hqSource).2.1
  have hrDiv : r ∣ jurkatRichertSourceSiftingProduct N :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hr).1
  have hrSquarefree := (jurkatRichertSourceSiftingProduct_squarefree N).squarefree_of_dvd hrDiv
  have hcop := jurkatRichertSourceMediumPrime_coprime_siftingDivisor hqSource hrDiv
  exact (Nat.squarefree_mul hcop).mpr ⟨hqPrime.squarefree, hrSquarefree⟩

def weightedSaving (A : ℕ) : ℕ := 2 * A + 18
def weightedNumericalConstant (A : ℕ) : ℝ :=
  3145728 * (numericalBVConstant (weightedSaving A) + 1)
def weightedNumericalThreshold (A m : ℕ) : ℕ :=
  max (numericalBVThreshold (weightedSaving A))
    (logPowerCutoff (m * highBVExponent (weightedSaving A)))

theorem numerical_weighted_distribution (A m N : ℕ) (hm : 0 < m)
    (hN : weightedNumericalThreshold A m ≤ N) :
    jurkatRichertSourceReducedWeightedBVSum N (1 / (m : ℝ)) ≤
      weightedNumericalConstant A * (N : ℝ) / Real.log N ^ A := by
  let U := weightedSaving A
  let Q := LiuWeight.panModulusCutoff N (highBVExponent U : ℝ)
  let S := chenReducedCombinedModuli N (1 / (m : ℝ))
  let E := BombieriVinogradov.standardPrimeAPMaxError N
  let K := numericalBVConstant U
  have hBVcut : numericalBVThreshold U ≤ N := (le_max_left _ _).trans hN
  have hroot : logPowerCutoff (m * highBVExponent U) ≤ N := (le_max_right _ _).trans hN
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hroot
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ N by exact_mod_cast (show 3 ≤ N by omega))
    linarith only [hh, one_le_log_three]
  have hl : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hK : 0 ≤ K := by
    dsimp [K, numericalBVConstant, bvConstant, primitiveNumericalConstant, principalNumericalConstant]
    positivity
  have hcut := explicit_source_modulus_in_BV (highBVExponent U) m N hm hroot
  have hQN : Q ≤ N := panModulusCutoff_le_endpoint N (highBVExponent U : ℝ)
    (by omega) (by positivity)
  have hS : S ⊆ Finset.Icc 1 Q := by
    intro d hd
    have hs := numerical_combined_squarefree hd
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hs.ne_zero,
      (chenReducedCombinedModuli_le_liuSourceDEpsilon hd).trans hcut⟩
  have hSN : S ⊆ Finset.Icc 1 N := hS.trans (Finset.Icc_subset_Icc_right hQN)
  have hE : ∀ d ∈ S, 0 ≤ E d := fun d _ => BombieriVinogradov.standardPrimeAPMaxError_nonneg N d
  have hsum : (∑ d ∈ S, E d) ≤ K * (N : ℝ) / Real.log N ^ U := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 Q, E d := Finset.sum_le_sum_of_subset_of_nonneg hS (fun d _ _ =>
        BombieriVinogradov.standardPrimeAPMaxError_nonneg N d)
      _ ≤ ∑ d ∈ Finset.Icc 1 Q, BombieriVinogradov.standardPrimeAPPrefixMaxError N d :=
        BombieriVinogradov.sum_standardPrimeAPMaxError_le_prefixMaxError N _
      _ ≤ _ := numerical_BV U N hBVcut
  have hmoment := numerical_totient_nine_mass (by omega : 1 ≤ N) S
    hSN (fun d hd => numerical_combined_squarefree hd)
  have hc := numerical_totient_cauchy S (fun d => (3 : ℝ) ^ d.primeFactors.card) E (12 * N)
    (fun d hd => (Finset.mem_Icc.mp (hSN hd)).1) hE
    (fun d hd => numerical_totient_standard_error hN9 (Finset.mem_Icc.mp (hSN hd)).1
      (Finset.mem_Icc.mp (hSN hd)).2)
  have heq : (∑ d ∈ S, ((3 : ℝ) ^ d.primeFactors.card) ^ 2 / d.totient) =
      ∑ d ∈ S, (9 : ℝ) ^ d.primeFactors.card / d.totient := by
    apply Finset.sum_congr rfl
    intro d _
    rw [pow_two, ← mul_pow]
    norm_num
  rw [heq] at hc
  have hm0 : 0 ≤ ∑ d ∈ S, (9 : ℝ) ^ d.primeFactors.card / d.totient :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hs0 : 0 ≤ ∑ d ∈ S, E d := Finset.sum_nonneg hE
  have hbig : threeOmegaErrorMass S E ^ 2 ≤
      (1 + Real.log N) ^ (18 : ℕ) * (12 * N * (K * N / Real.log N ^ U)) := by
    exact hc.trans (mul_le_mul hmoment
      (mul_le_mul_of_nonneg_left hsum (by positivity)) (by positivity)
      (by positivity))
  have hw0 : 0 ≤ jurkatRichertSourceReducedWeightedBVSum N (1 / (m : ℝ)) := by
    unfold jurkatRichertSourceReducedWeightedBVSum
    exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun d _ => by
      exact mul_nonneg (pow_nonneg (by norm_num) _)
        (BombieriVinogradov.standardPrimeAPMaxError_nonneg N (q * d))
  have ht0 : 0 ≤ threeOmegaErrorMass S E := Finset.sum_nonneg fun d hd =>
    mul_nonneg (pow_nonneg (by norm_num) _) (hE d hd)
  have hwsq := (sq_le_sq₀ hw0 ht0).2 (chenReducedWeightedBVSum_le_combinedMass N (1 / (m : ℝ)))
  have hlogbound : (1 + Real.log N) ^ (18 : ℕ) ≤ (2 * Real.log N) ^ (18 : ℕ) := by
    gcongr
    linarith only [hlog]
  have hsquare : jurkatRichertSourceReducedWeightedBVSum N (1 / (m : ℝ)) ^ 2 ≤
      (3145728 * K) * ((N : ℝ) / Real.log N ^ A) ^ 2 := by
    apply hwsq.trans (hbig.trans _)
    calc
      _ ≤ (2 * Real.log N) ^ (18 : ℕ) * (12 * N * (K * N / Real.log N ^ U)) :=
        mul_le_mul_of_nonneg_right hlogbound (by positivity)
      _ = _ := by
        dsimp [U, weightedSaving]
        rw [pow_add, pow_mul]
        field_simp
        ring
  have hC : 1 ≤ weightedNumericalConstant A := by
    change 1 ≤ 3145728 * (K + 1)
    linarith only [hK]
  have hCbig : 3145728 * K ≤ weightedNumericalConstant A ^ 2 := by
    have hh : 3145728 * K ≤ weightedNumericalConstant A := by
      change 3145728 * K ≤ 3145728 * (K + 1)
      linarith
    nlinarith only [hh, hC, sq_nonneg (weightedNumericalConstant A - 1)]
  have hp := mul_le_mul_of_nonneg_right hCbig (sq_nonneg ((N : ℝ) / Real.log N ^ A))
  have hh := hsquare.trans hp
  have hC0 : 0 ≤ weightedNumericalConstant A * (N : ℝ) / Real.log N ^ A := by
    apply div_nonneg (mul_nonneg (by linarith only [hC]) hN0.le) (pow_nonneg hl.le _)
  apply (sq_le_sq₀ hw0 hC0).mp
  convert hh using 1
  ring

#print axioms numerical_weighted_distribution
end ChenEffective
