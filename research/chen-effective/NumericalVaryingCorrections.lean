import NumericalWeightedDistribution

namespace ChenEffective
open Finset Real
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem numerical_upper_level_divisor_le {N q d : ℕ} {ε : ℝ}
    (hN : 1 ≤ N) (hε : 0 ≤ ε) (hq : q ∈ jurkatRichertSourceMediumPrimes N)
    (hd : d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
      (fun d => d < jurkatRichertSourceUpperLevel N q ε)) :
    0 < d ∧ (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
  have hdDiv := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hdp := Nat.pos_of_dvd_of_pos hdDiv
    (Nat.pos_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N))
  have hqp := (Finset.mem_filter.mp hq).2.1.pos
  have hh := jurkatRichertSourceUpperLevel_mul_le hq (Finset.mem_filter.mp hd).2
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ N by exact_mod_cast hN) (show 1 / 2 - ε ≤ (1 / 2 : ℝ) by linarith)
  exact ⟨hdp, (show (d : ℝ) ≤ (q * d : ℕ) by
    exact_mod_cast Nat.le_mul_of_pos_left d hqp).trans (hh.trans hpow)⟩

theorem numerical_upper_level_totient_mass {N q : ℕ} {ε : ℝ}
    (hN : 1 ≤ N) (hε : 0 ≤ ε) (hq : q ∈ jurkatRichertSourceMediumPrimes N) :
    (∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
        (fun d => d < jurkatRichertSourceUpperLevel N q ε),
      (3 : ℝ) ^ d.primeFactors.card / d.totient) ≤ (1 + Real.log N) ^ (6 : ℕ) := by
  apply numerical_totient_weight_mass 3 hN
  · intro d hd
    have hh := numerical_upper_level_divisor_le hN hε hq hd
    have hpow : (N : ℝ) ^ (1 / 2 : ℝ) ≤ N := by
      calc
        _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast hN) (by norm_num)
        _ = _ := Real.rpow_one _
    exact Finset.mem_Icc.mpr ⟨hh.1, by exact_mod_cast hh.2.trans hpow⟩
  · intro d hd
    exact (jurkatRichertSourceSiftingProduct_squarefree N).squarefree_of_dvd
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)

theorem numerical_varying_weight_mass {N : ℕ} {ε : ℝ} (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    jurkatRichertSourceVaryingQWeightMass N ε ≤
      2 * (N : ℝ) ^ (5 / 6 : ℝ) * (1 + Real.log N) ^ (6 : ℕ) := by
  let D := fun q => (jurkatRichertSourceSiftingProduct N).divisors.filter
    (fun d => d < jurkatRichertSourceUpperLevel N q ε)
  let L := (N : ℝ) ^ (1 / 2 : ℝ)
  have hinner : ∀ q ∈ jurkatRichertSourceMediumPrimes N,
      (∑ d ∈ D q, (3 : ℝ) ^ d.primeFactors.card) ≤ L * (1 + Real.log N) ^ (6 : ℕ) := by
    intro q hq
    calc
      _ ≤ ∑ d ∈ D q, L * ((3 : ℝ) ^ d.primeFactors.card / d.totient) := by
        apply Finset.sum_le_sum
        intro d hd
        have hh := numerical_upper_level_divisor_le hN hε hq hd
        have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hh.1
        have hφL : (d.totient : ℝ) ≤ L :=
          (show (d.totient : ℝ) ≤ d by exact_mod_cast Nat.totient_le d).trans hh.2
        calc
          _ = (d.totient : ℝ) * ((3 : ℝ) ^ d.primeFactors.card / d.totient) := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_right hφL (by positivity)
      _ = L * (∑ d ∈ D q, (3 : ℝ) ^ d.primeFactors.card / d.totient) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (numerical_upper_level_totient_mass hN hε hq)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  unfold jurkatRichertSourceVaryingQWeightMass
  calc
    _ ≤ ∑ _q ∈ jurkatRichertSourceMediumPrimes N, L * (1 + Real.log N) ^ (6 : ℕ) :=
      Finset.sum_le_sum hinner
    _ = ((jurkatRichertSourceMediumPrimes N).card : ℝ) * (L * (1 + Real.log N) ^ (6 : ℕ)) := by simp
    _ ≤ (2 * (N : ℝ) ^ (1 / 3 : ℝ)) * (L * (1 + Real.log N) ^ (6 : ℕ)) :=
      mul_le_mul_of_nonneg_right (jurkatRichertSourceMediumPrimes_card_cast_le N hN) (by positivity)
    _ = _ := by
      dsimp [L]
      rw [show 2 * (N : ℝ) ^ (1 / 3 : ℝ) *
        ((N : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log N) ^ (6 : ℕ)) =
        2 * ((N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ)) *
          (1 + Real.log N) ^ (6 : ℕ) by ring, ← Real.rpow_add (by positivity : (0 : ℝ) < N)]
      norm_num

theorem numerical_nonreduced_center {N : ℕ} {ε : ℝ} (hN : 3 ≤ N) (hε : 0 ≤ ε) :
    jurkatRichertSourceNonreducedCenterSum N ε ≤
      (Real.log N / Real.log 2) *
        ((2 * BombieriVinogradov.trueLogarithmicIntegral N / (N : ℝ) ^ (1 / 10 : ℝ)) *
          (1 + Real.log N) ^ (6 : ℕ)) := by
  let D := fun q => (jurkatRichertSourceSiftingProduct N).divisors.filter
    (fun d => d < jurkatRichertSourceUpperLevel N q ε)
  let Q := (jurkatRichertSourceMediumPrimes N).filter (fun q => q ∣ N)
  let li := BombieriVinogradov.trueLogarithmicIntegral N
  have hli : 0 ≤ li := LiuWeight.liuLogarithmicIntegral_nonneg (2 / Real.log 2)
    (by positivity) (by exact_mod_cast (show 2 ≤ N by omega))
  have hpow : 0 < (N : ℝ) ^ (1 / 10 : ℝ) := by positivity
  have hinner : ∀ q ∈ Q,
      (∑ d ∈ D q, (3 : ℝ) ^ d.primeFactors.card * (li / Nat.totient (q * d))) ≤
        (2 * li / (N : ℝ) ^ (1 / 10 : ℝ)) * (1 + Real.log N) ^ (6 : ℕ) := by
    intro q hq
    have hqm := (Finset.mem_filter.mp hq).1
    have hqp := (Finset.mem_filter.mp hqm).2.1
    have hql := (Finset.mem_filter.mp hqm).2.2.1
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hqp.two_le
    have hsub : 0 < (q : ℝ) - 1 := by linarith only [hq2]
    have hi : 1 / ((q : ℝ) - 1) ≤ 2 / (N : ℝ) ^ (1 / 10 : ℝ) := by
      rw [div_le_div_iff₀ hsub hpow]
      nlinarith only [hq2, hql]
    have hf : li / ((q : ℝ) - 1) ≤ 2 * li / (N : ℝ) ^ (1 / 10 : ℝ) := by
      calc
        _ = li * (1 / ((q : ℝ) - 1)) := by ring
        _ ≤ li * (2 / (N : ℝ) ^ (1 / 10 : ℝ)) := mul_le_mul_of_nonneg_left hi hli
        _ = _ := by ring
    calc
      _ = (li / ((q : ℝ) - 1)) * (∑ d ∈ D q, (3 : ℝ) ^ d.primeFactors.card / d.totient) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        have hdvd := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
        have hcop := jurkatRichertSourceMediumPrime_coprime_siftingDivisor hqm hdvd
        have hdp := Nat.pos_of_dvd_of_pos hdvd
          (Nat.pos_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N))
        have hφ : (d.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hdp).ne'
        rw [Nat.totient_mul hcop, Nat.totient_prime hqp]
        push_cast [hqp.one_lt.le]
        field_simp [hsub.ne', hφ]
      _ ≤ (2 * li / (N : ℝ) ^ (1 / 10 : ℝ)) *
          (∑ d ∈ D q, (3 : ℝ) ^ d.primeFactors.card / d.totient) :=
        mul_le_mul_of_nonneg_right hf (Finset.sum_nonneg fun _ _ => by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (numerical_upper_level_totient_mass (by omega : 1 ≤ N) hε hqm) (by positivity)
  have hcard : (Q.card : ℝ) ≤ Real.log N / Real.log 2 := by
    calc
      _ ≤ (N.primeFactors.card : ℝ) := by
        exact_mod_cast jurkatRichertSourceNonreducedPrimes_card_le_primeFactors N (by omega)
      _ ≤ _ := LiuWeight.primeFactors_card_cast_le_log (by omega)
  unfold jurkatRichertSourceNonreducedCenterSum
  calc
    _ ≤ ∑ _q ∈ Q, (2 * li / (N : ℝ) ^ (1 / 10 : ℝ)) *
        (1 + Real.log N) ^ (6 : ℕ) := Finset.sum_le_sum hinner
    _ = (Q.card : ℝ) * ((2 * li / (N : ℝ) ^ (1 / 10 : ℝ)) *
        (1 + Real.log N) ^ (6 : ℕ)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

theorem numerical_varying_correction {N : ℕ} {ε : ℝ} (hN : 9 ≤ N) (hε : 0 ≤ ε) :
    jurkatRichertSourceVaryingQUnconditionalCorrection N ε ≤
      3000 * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (7 : ℕ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog := log_one_le_of_eight_le (show 8 ≤ N by omega)
  have hl : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hr : Real.log (N : ℝ) / Real.log 2 ≤ 2 * Real.log N := by
    apply (div_le_iff₀ (by linarith only [hlog2])).mpr
    have hh := mul_le_mul_of_nonneg_left hlog2 hl.le
    linarith only [hh]
  have hE := jurkatRichertSourceExceptionalPrimes_card_le_log N (by omega)
  have hE3 : ((jurkatRichertSourceExceptionalPrimes N).card : ℝ) + 1 ≤ 3 * Real.log N := by
    linarith only [hE, hr, hlog]
  have hp : (1 + Real.log (N : ℝ)) ^ (6 : ℕ) ≤ 64 * Real.log N ^ (6 : ℕ) := by
    calc
      _ ≤ (2 * Real.log N) ^ (6 : ℕ) := by gcongr; linarith only [hlog]
      _ = _ := by ring
  have hmass : jurkatRichertSourceVaryingQWeightMass N ε ≤
      128 * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (6 : ℕ) := by
    have hh := numerical_varying_weight_mass (by omega : 1 ≤ N) hε
    apply hh.trans
    have he := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (5 / 6 : ℝ) ≤ 9 / 10)
    calc
      _ ≤ 2 * (N : ℝ) ^ (9 / 10 : ℝ) * (64 * Real.log N ^ (6 : ℕ)) := by gcongr
      _ = _ := by ring
  have hfirst : (((jurkatRichertSourceExceptionalPrimes N).card : ℝ) + 1) *
      jurkatRichertSourceVaryingQWeightMass N ε ≤
        384 * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (7 : ℕ) := by
    have hm0 : 0 ≤ jurkatRichertSourceVaryingQWeightMass N ε := by
      unfold jurkatRichertSourceVaryingQWeightMass
      positivity
    calc
      _ ≤ (3 * Real.log N) * (128 * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (6 : ℕ)) :=
        mul_le_mul hE3 hmass hm0 (by positivity)
      _ = _ := by ring
  have hli : BombieriVinogradov.trueLogarithmicIntegral N ≤ 10 * (N : ℝ) :=
    (le_abs_self _).trans (numerical_true_li_bound hN)
  have hpow : (N : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ) = (N : ℝ) ^ (9 / 10 : ℝ) := by
    rw [show (9 / 10 : ℝ) = 1 - 1 / 10 by norm_num, Real.rpow_sub hN0, Real.rpow_one]
  have hli2 : 2 * BombieriVinogradov.trueLogarithmicIntegral N / (N : ℝ) ^ (1 / 10 : ℝ) ≤
      20 * (N : ℝ) ^ (9 / 10 : ℝ) := by
    calc
      _ ≤ 2 * (10 * (N : ℝ)) / (N : ℝ) ^ (1 / 10 : ℝ) := by gcongr
      _ = 20 * ((N : ℝ) / (N : ℝ) ^ (1 / 10 : ℝ)) := by ring
      _ = _ := by rw [hpow]
  have hsecond : jurkatRichertSourceNonreducedCenterSum N ε ≤
      2560 * (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (7 : ℕ) := by
    apply (numerical_nonreduced_center (by omega : 3 ≤ N) hε).trans
    have hli0 : 0 ≤ BombieriVinogradov.trueLogarithmicIntegral N :=
      LiuWeight.liuLogarithmicIntegral_nonneg (2 / Real.log 2) (by positivity)
        (by exact_mod_cast (show 2 ≤ N by omega))
    calc
      _ ≤ (2 * Real.log N) * ((20 * (N : ℝ) ^ (9 / 10 : ℝ)) *
          (64 * Real.log N ^ (6 : ℕ))) := by gcongr
      _ = _ := by ring
  unfold jurkatRichertSourceVaryingQUnconditionalCorrection
  have hh := add_le_add hfirst hsecond
  nlinarith only [hh, mul_nonneg (Real.rpow_nonneg hN0.le (9 / 10 : ℝ)) (pow_nonneg hl.le 7)]

#print axioms numerical_varying_weight_mass
#print axioms numerical_nonreduced_center
#print axioms numerical_varying_correction
end ChenEffective
