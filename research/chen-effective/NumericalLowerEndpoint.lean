import NumericalUpperDistribution
import MathlibNt.SieveTheory.Switching.PrimePenaltyAsymptotics

namespace ChenEffective
open Real
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def lowerEndpointThreshold : ℕ :=
  max (2 ^ 110 + 1) (max (logPowerCutoff 30) (3 ^ 2400000))

theorem numerical_lower_endpoint_loss {N : ℕ} (hN : lowerEndpointThreshold ≤ N) :
    60 * (N : ℝ) ^ (9 / 10 : ℝ) ≤
      (1 / 20000 : ℝ) * SingularSeries.liuSingularSeries N * N / Real.log N ^ (2 : ℕ) := by
  have hcut : logPowerCutoff 30 ≤ N := by unfold lowerEndpointThreshold at hN; omega
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hcut
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp := power_saving_payment_explicit (k := 3) (m := 10)
    (by norm_num) (le_refl _) hcut 60 (by norm_num)
  have hp' : 60 * (N : ℝ) ^ (9 / 10 : ℝ) ≤ 60 * N / Real.log N ^ (3 : ℕ) := by
    convert hp using 1
    norm_num
  have hlog : (2400000 : ℝ) ≤ Real.log N :=
    log_ge_power_three (b := 2400000) (show 3 ^ 2400000 ≤ N by unfold lowerEndpointThreshold at hN; omega)
  have hs := half_le_liuSingularSeries N
  have hcoef : (60 : ℝ) ≤ ((1 / 20000 : ℝ) * SingularSeries.liuSingularSeries N) * Real.log N := by
    have hh := mul_le_mul_of_nonneg_right hs hl.le
    nlinarith only [hh, hlog]
  apply hp'.trans
  apply (div_le_div_iff₀ (pow_pos hl 3) (pow_pos hl 2)).mpr
  have hh := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ (N : ℝ) * Real.log N ^ (2 : ℕ) by positivity)
  nlinarith only [hh]

/-- The remaining lower-sieve producer must supply the displayed source
coefficient. Boundary and proper-power losses have a numerical cutoff here. -/
theorem numerical_lower_from_source {N : ℕ} (hN : lowerEndpointThreshold ≤ N)
    (hEven : Even N)
    (hSource : (2.64075 : ℝ) * SingularSeries.liuSingularSeries N * N / Real.log N ^ (2 : ℕ) ≤
      jurkatRichertSourceWeightedCount N) :
    (2.6407 : ℝ) * SingularSeries.liuSingularSeries N * N / Real.log N ^ (2 : ℕ) ≤
      jurkatRichertWeightedCount N := by
  have hbig : 2 ^ 110 < N := by unfold lowerEndpointThreshold at hN; omega
  have hb := jurkatRichertSourceWeightedCount_sub_boundary_le_distinct N hbig hEven
  have hp := jurkatRichertDistinctWeightedCount_sub_proper_le N hbig hEven
  have he := numerical_lower_endpoint_loss hN
  have hn : 0 ≤ (N : ℝ) ^ (9 / 10 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  let M := SingularSeries.liuSingularSeries N * N / Real.log N ^ (2 : ℕ)
  have hs' : (2.64075 : ℝ) * M ≤ jurkatRichertSourceWeightedCount N := by
    convert hSource using 1
    dsimp [M]
    ring
  have he' : 60 * (N : ℝ) ^ (9 / 10 : ℝ) ≤ (1 / 20000 : ℝ) * M := by
    convert he using 1
    dsimp [M]
    ring
  calc
    _ = (2.6407 : ℝ) * M := by dsimp [M]; ring
    _ ≤ _ := by nlinarith only [hb, hp, he', hs', hn]

theorem numerical_lower_from_density_bounds {N : ℕ} (hN : lowerEndpointThreshold ≤ N)
    (hEven : Even N)
    (hBase : (jurkatRichertBaseMainCoefficient jurkatRichertJ - 1 / 40000) *
        (SingularSeries.liuSingularSeries N * N / Real.log N ^ (2 : ℕ)) ≤
      ((jurkatRichertSourceCandidates N).card : ℝ))
    (hUpper : jurkatRichertSourceMediumPrimeAggregate N ≤
      (jurkatRichertQ1MainCoefficient jurkatRichertK + 1 / 20000) *
        (SingularSeries.liuSingularSeries N * N / Real.log N ^ (2 : ℕ))) :
    (2.6407 : ℝ) * SingularSeries.liuSingularSeries N * N / Real.log N ^ (2 : ℕ) ≤
      jurkatRichertWeightedCount N := by
  apply numerical_lower_from_source hN hEven
  have hc := jurkatRichert_mainCoefficient_ge_twoPoint6408
    jurkatRichertJ jurkatRichertK jurkatRichert_integralEstimate
  let M := SingularSeries.liuSingularSeries N * N / Real.log N ^ (2 : ℕ)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N))
      (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hc hM
  rw [jurkatRichertSourceWeightedCount_eq]
  have he : (2.64075 : ℝ) * SingularSeries.liuSingularSeries N * N / Real.log N ^ (2 : ℕ) =
      (2.64075 : ℝ) * M := by dsimp [M]; ring
  rw [he]
  change (jurkatRichertBaseMainCoefficient jurkatRichertJ - 1 / 40000) * M ≤ _ at hBase
  change _ ≤ (jurkatRichertQ1MainCoefficient jurkatRichertK + 1 / 20000) * M at hUpper
  nlinarith only [hh, hBase, hUpper]

#print axioms numerical_lower_from_source
#print axioms numerical_lower_from_density_bounds
end ChenEffective
