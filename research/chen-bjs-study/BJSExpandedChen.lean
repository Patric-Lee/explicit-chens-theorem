import BJSExpandedDenominator
import BJSJointChen
import Goldbach.Statement

/-! The expanded denominator is propagated through the actual square and
triple counts. The lower-count geometry, not the denominator, determines the
final cutoff. K is interchangeable throughout the permitted open budget. -/
noncomputable section
namespace ChenEffective
open Real
open MathlibNt.SieveTheory LiuWeight SingularSeries SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512

def expandedChenN0 : ℕ := bjsStudyGeometryThreshold
theorem expandedChenN0_eq : expandedChenN0=3^(3^171) := bjsStudyGeometryThreshold_eq

def expandedChenK : ℝ := 8.2257261896036
def expandedChenRemainder : ℝ := 1/10^40

theorem expanded_chen_margin :
    (jointSelbergBudget expandedChenK (1/10^7) 0 expandedChenRemainder).margin=
      (0.00000000000001194782:ℝ)-1/(2*10^40) := by
  rw [joint_selberg_margin]
  norm_num [expandedChenK,expandedChenRemainder]

/-- The supremum is explicit; strict positive margin means there is no
largest admissible K. The representative above lies below it by < 5e-14. -/
theorem expanded_chen_budget_iff (K : ℝ) :
    K*(0.49254+1/10^7)+expandedChenRemainder<4.0515 ↔
      K<(4.0515-expandedChenRemainder)/(0.49254+1/10^7) := by
  rw [lt_div_iff₀ (by norm_num : (0:ℝ)<0.49254+1/10^7)]
  constructor <;> intro h <;> linarith

theorem expanded_chen_K_near_boundary :
    expandedChenK<(4.0515-expandedChenRemainder)/(0.49254+1/10^7) ∧
    (4.0515-expandedChenRemainder)/(0.49254+1/10^7)-expandedChenK<5/10^14 := by
  norm_num [expandedChenK,expandedChenRemainder]

theorem expanded_final_log {N : ℕ} (hN : expandedChenN0≤N) : (1000000:ℝ)≤log (N:ℝ) := by
  rw [expandedChenN0_eq] at hN
  have hh := log_ge_power_three hN
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hh
  exact (by norm_num : (1000000:ℝ)≤3^171).trans hh

theorem expanded_inverse_log_payment {N : ℕ} (hN : expandedChenN0≤N) :
    (numericalTripleErrorCap:ℝ)*N/log (N:ℝ)^3≤
      expandedChenRemainder*liuSingularSeries N*N/log (N:ℝ)^2 := by
  have hn := hN
  rw [expandedChenN0_eq] at hn
  have hL := log_ge_power_three hn
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hL
  have hlog : 0<log (N:ℝ) := lt_of_lt_of_le (by norm_num : (0:ℝ)<3^171) hL
  have hcap : (2*10^80:ℝ)≤log (N:ℝ) := (by norm_num : (2*10^80:ℝ)≤3^171).trans hL
  have hpay : (numericalTripleErrorCap:ℝ)≤expandedChenRemainder*liuSingularSeries N*log (N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (half_le_liuSingularSeries N) hlog.le
    norm_num [expandedChenRemainder,numericalTripleErrorCap] at *
    nlinarith only [hh,hcap]
  apply (div_le_div_iff₀ (pow_pos hlog 3) (pow_pos hlog 2)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hpay
    (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg (log (N:ℝ))))]

theorem expanded_triple {N : ℕ} (hN : expandedChenN0≤N) (hEven : Even N)
    {K : ℝ} (hK : 81/10≤K) :
    correctedChenTriplePenalty N≤
      (K*(0.49254+1/10^7)+expandedChenRemainder)*
        (liuSingularSeries N*N/log (N:ℝ)^2) := by
  have hSA : squareAnalyticThreshold≤N :=
    (numerical_square_analytic_cap.trans bjsStudy_power_cap).trans hN
  have hRes : tripleResidualThreshold≤N := by
    apply le_trans _ (bjsStudy_power_cap.trans hN)
    unfold tripleResidualThreshold
    apply numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  have hPair : primePairThreshold≤N :=
    (le_max_left primePairThreshold ((mediumPrimeBudget+2)^10)).trans
      (bjsStudyCap_preSieve_prime_sum.trans (bjsStudy_finite_cap.trans hN))
  have hs := joint_selberg_square hSA hEven (lt_of_lt_of_le (by norm_num) hK)
    (expanded_selberg_denominator_of_log (expanded_final_log hN) hEven hK)
    (numerical_prime_pair_main hPair)
  have ht := joint_triple_from_square hRes hEven hs
  have htc := ht.trans (add_le_add le_rfl (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right numerical_square_error_cap (Nat.cast_nonneg N))
    (pow_nonneg (log_natCast_nonneg N) 3)))
  have hp := expanded_inverse_log_payment hN
  norm_num only [liuM1Eta] at htc
  simp only [mul_div_assoc,mul_assoc] at htc hp ⊢
  linarith only [htc,hp]

theorem expanded_chen_from_budget {N : ℕ} (hN : expandedChenN0≤N) (hEven : Even N)
    {K : ℝ} (hK : 81/10≤K)
    (hbudget : K*(0.49254+1/10^7)+expandedChenRemainder<4.0515) :
    ∃ p q : ℕ,p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ,r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  have hl := bjsStudy_weighted_lower hN hEven
  have hN9 : 9≤N := by
    have hEnd := bjsStudy_endpoint hN
    have hh : 2^110+1≤N := (le_max_left _ _).trans hEnd
    omega
  apply joint_selberg_existence hN9 (K:=K) (η:=1/10^7) (extra:=0)
    (remainder:=expandedChenRemainder) (by simpa only [add_zero] using hbudget)
  · convert hl using 1
    norm_num [bjsStudyBudget,ChenBudget.weighted]
    ring
  · simpa only [add_zero] using expanded_triple hN hEven hK

theorem expanded_chen {N : ℕ} (hN : expandedChenN0≤N) (hEven : Even N) :
    ∃ p q : ℕ,p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ,r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  apply expanded_chen_from_budget hN hEven (K:=expandedChenK)
  · norm_num [expandedChenK]
  · norm_num [expandedChenK,expandedChenRemainder]

theorem expanded_original_chen : Goldbach.ChenTheorem :=
  ⟨expandedChenN0,fun _ hN hEven => expanded_chen hN hEven⟩

#print axioms expanded_chen
end ChenEffective
