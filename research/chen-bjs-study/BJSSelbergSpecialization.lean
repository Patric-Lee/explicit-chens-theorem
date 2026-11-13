import BJSStudySelbergDenominator

/-! Explicit specialization of the squarefree multiplicative denominator.
The local identities below are unconditional. The denominator adapter keeps
its normalized arithmetic error and desired coefficient independent; it does
not assert an unproved uniform remainder from a paper. -/
noncomputable section
namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def selbergSpecializedPrimeWeight (p : ℝ) : ℝ := 1 / (p - 2)

theorem selberg_specialized_prime_expansion {p : ℝ} (hp : 2 < p) :
    selbergSpecializedPrimeWeight p - 1 / p = 2 / (p * (p - 2)) := by
  unfold selbergSpecializedPrimeWeight
  have hp0 : p ≠ 0 := ne_of_gt (by linarith)
  have hp2 : p - 2 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- The extra prime sum in the convolution theorem's secondary term vanishes. -/
theorem selberg_specialized_secondary_cancellation {p : ℝ} (hp : 2 < p) :
    1 - (p - 2) * selbergSpecializedPrimeWeight p = 0 := by
  unfold selbergSpecializedPrimeWeight
  have hp2 : p - 2 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  norm_num

/-- Multiplying by the singular series is done before taking bounds. -/
theorem selberg_specialized_normalized_nondisor {p : ℝ} (hp : 2 < p) :
    (1 + 3 / (p * (p - 2))) * (p * (p - 2) / (p - 1)^2) =
      1 + 2 / (p - 1)^2 := by
  have hp0 : p ≠ 0 := ne_of_gt (by linarith)
  have hp1 : p - 1 ≠ 0 := ne_of_gt (by linarith)
  have hp2 : p - 2 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

theorem selberg_specialized_normalized_divisor {p : ℝ} (hp : 2 < p) :
    (1 + 1 / p) * (p / (p - 1)) = (p + 1) / (p - 1) := by
  have hp0 : p ≠ 0 := ne_of_gt (by linarith)
  have hp1 : p - 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp

/-- Relative to the universal normalized factor, the divisor correction
costs at most two powers of the elementary divisor product. -/
theorem selberg_specialized_divisor_ratio {p : ℝ} (hp : 3 ≤ p) :
    (p + 1) / (p - 1) ≤
      (1 + 2 / (p - 1)^2) * (1 + 1 / p)^2 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  field_simp
  nlinarith [sq_nonneg p]

def selbergSpecializedSecondary (N : ℕ) : ℝ :=
  eulerMascheroniConstant + ∑ p ∈ N.primeFactors, log p / ((p : ℝ) - 1)

theorem selberg_specialized_secondary_pos (N : ℕ) :
    0 < selbergSpecializedSecondary N := by
  have hs : 0 ≤ ∑ p ∈ N.primeFactors, log p / ((p : ℝ) - 1) := by
    apply sum_nonneg
    intro p hp
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    apply div_nonneg (log_natCast_nonneg p)
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  unfold selbergSpecializedSecondary
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-- Direct sufficient scalar condition for the actual denominator. K need
not be 8+10^-7. E bounds the actual singular-series-normalized correction. -/
theorem selberg_denominator_from_joint_error {N : ℕ}
    (hN : 256 ≤ N) (hEven : Even N) {ε K E : ℝ}
    (hβ : 1/8 ≤ 1/4 - ε/2) (hK : 0 < K)
    (herror : (2*liuSelbergAbsoluteLogMoment N+liuSelbergAbsoluteMass N)*
      liuSingularSeries N ≤ E)
    (hbudget : log (N : ℝ)/K + E + ε*log (N : ℝ)/4 + log 2/2 ≤
      log (N : ℝ)/8) :
    log (N : ℝ)/(K*liuSingularSeries N) ≤ liuSelbergDenominator N ε := by
  have hn : 0 < N := by omega
  obtain ⟨hlogR,hR⟩ := numerical_selberg_log_floor hN hβ
  change (1/4-ε/2)*log (N : ℝ)-log 2 ≤
    log (paperQSourceCutoff N ε) at hlogR
  change 2 ≤ paperQSourceCutoff N ε at hR
  have herr := abs_liuSelbergArithmetic_sum_Icc_sub_log_main_le_uniform_reduction
    hEven hn hR
  rw [← liuSelbergDenominator_eq_sum_Icc hEven (by omega)] at herr
  have hlo := (abs_le.mp herr).1
  have hS := liuSingularSeries_pos N
  have hs := mul_le_mul_of_nonneg_right hlo hS.le
  have hcancel : log (paperQSourceCutoff N ε)/(2*liuSingularSeries N)*
      liuSingularSeries N = log (paperQSourceCutoff N ε)/2 := by
    field_simp
  rw [sub_mul, hcancel] at hs
  apply (div_le_iff₀ (mul_pos hK hS)).mpr
  have hpaid := (div_le_iff₀ hK).mp (show log (N : ℝ)/K ≤
      liuSelbergDenominator N ε*liuSingularSeries N by
    nlinarith only [hs,herror,hlogR,hbudget])
  nlinarith only [hpaid]

theorem selberg_denominator_from_current_envelope {N : ℕ}
    (hN : 256 ≤ N) (hDiv : bjsStudyDivisorThreshold ≤ N) (hEven : Even N)
    {ε K : ℝ} (hβ : 1/8 ≤ 1/4 - ε/2) (hK : 0 < K)
    (hbudget : log (N : ℝ)/K + 10^24*(1+log (log (N : ℝ)))^6 +
      ε*log (N : ℝ)/4 + log 2/2 ≤ log (N : ℝ)/8) :
    log (N : ℝ)/(K*liuSingularSeries N) ≤ liuSelbergDenominator N ε :=
  selberg_denominator_from_joint_error hN hEven hβ hK
    (bjsStudy_selberg_euler_numerator hDiv hEven) hbudget

#print axioms selberg_denominator_from_joint_error
#print axioms selberg_specialized_secondary_pos
end ChenEffective
