import BJSJointTriple
import BJSStudyChen

/-! An actual end-to-end producer check for the relaxed denominator. The
cutoff is deliberately unchanged: the distribution and remainder caps still
dominate. This proof uses the counting inputs, not the old final Chen proof. -/
noncomputable section
namespace ChenEffective
open Real
open MathlibNt.SieveTheory LiuWeight SingularSeries SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 512

private theorem double_power_mono {a b : ℕ} (hab : a ≤ b) :
    (3 : ℕ)^(3^a) ≤ 3^(3^b) :=
  Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hab)

theorem joint_denominator_threshold_le_current :
    jointSelbergDenominatorThreshold ≤ bjsStudyN0 := by
  rw [jointSelbergDenominatorThreshold_eq,bjsStudyN0_eq]
  exact double_power_mono (by norm_num : 83 ≤ 171)

theorem joint_chen_81 {N : ℕ} (hN : bjsStudyN0 ≤ N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  have hSA : squareAnalyticThreshold ≤ N :=
    (numerical_square_analytic_cap.trans bjsStudy_power_cap).trans hN
  have hRes : tripleResidualThreshold ≤ N := by
    apply le_trans _ (bjsStudy_power_cap.trans hN)
    unfold tripleResidualThreshold
    apply numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  have hPair : primePairThreshold ≤ N :=
    (le_max_left primePairThreshold ((mediumPrimeBudget+2)^10)).trans
      (bjsStudyCap_preSieve_prime_sum.trans (bjsStudy_finite_cap.trans hN))
  have ht := joint_triple_81 (joint_denominator_threshold_le_current.trans hN)
    hSA hRes hEven (numerical_prime_pair_main hPair)
  have hl := bjsStudy_weighted_lower hN hEven
  have he := bjsStudy_inverse_log_payment hN
  have hN9 : 9 ≤ N := by
    have hEnd := bjsStudy_endpoint hN
    have hh : 2^110+1 ≤ N := (le_max_left _ _).trans hEnd
    omega
  apply joint_selberg_existence hN9
    (K:=81/10) (η:=1/10^7) (extra:=1/10^5) (remainder:=1/100)
    (by norm_num)
  · convert hl using 1
    norm_num [bjsStudyBudget,ChenBudget.weighted]
    ring
  · have hM : 0 ≤ liuSingularSeries N*N/log (N:ℝ)^2 :=
      div_nonneg (mul_nonneg (liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
    norm_num only [liuM1Eta] at ht
    simp only [mul_div_assoc,mul_assoc] at ht he hM ⊢
    nlinarith only [ht,he,hM]

#print axioms joint_chen_81
end ChenEffective
