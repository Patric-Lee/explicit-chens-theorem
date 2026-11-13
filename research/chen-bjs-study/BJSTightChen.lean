import BJSTightLower
import BJSH30SquareTriple
import Goldbach.Statement

noncomputable section
namespace ChenEffective.TightBudget
open Real
open MathlibNt.SieveTheory SingularSeries SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512

def chenCutoff : ℕ := bjsStudyGeometryThreshold
theorem chenCutoff_eq : chenCutoff=3^(3^134) := bjsStudyGeometryThreshold_eq
def chosenK : ℝ := 8.2
def tripleAllocation : ℝ := 1/10^20

private theorem upper_cutoff_power_bound {j : ℕ}
    (hj : H30.primePairPowerExponent ≤ j) : H30.squareClosedThreshold ≤ 3^j := by
  unfold H30.squareClosedThreshold
  exact Nat.pow_le_pow_right (by norm_num) hj

theorem upper_cutoff_le_lower : H30.squareClosedThreshold≤chenCutoff := by
  rw [chenCutoff_eq]
  exact upper_cutoff_power_bound (by rw [H30.primePairPowerExponent_eq]; norm_num)

theorem inverse_log_payment {N : ℕ} (hN : chenCutoff≤N) :
    (H30.numericalTripleErrorCap:ℝ)*N/log (N:ℝ)^3≤
      tripleAllocation*liuSingularSeries N*N/log (N:ℝ)^2 := by
  have hn := hN
  rw [chenCutoff_eq] at hn
  have hL := log_ge_power_three hn
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hL
  have hl : 0<log (N:ℝ) := lt_of_lt_of_le (by norm_num : (0:ℝ)<3^134) hL
  have hcap : (2*10^60:ℝ)≤log (N:ℝ) := (by norm_num : (2*10^60:ℝ)≤3^134).trans hL
  have hpay : (H30.numericalTripleErrorCap:ℝ)≤tripleAllocation*liuSingularSeries N*log (N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (half_le_liuSingularSeries N) hl.le
    norm_num [tripleAllocation,H30.numericalTripleErrorCap]
    nlinarith only [hh,hcap]
  apply (div_le_div_iff₀ (pow_pos hl 3) (pow_pos hl 2)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hpay
    (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg (log (N:ℝ))))]

theorem chen_from_budget {N : ℕ} (hN : chenCutoff≤N) (hEven : Even N)
    {K : ℝ} (hK : 8.2≤K)
    (hbudget : K*(0.49254+1/10000)+tripleAllocation<4.0515) :
    ∃ p q : ℕ,p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ,r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  have hl := bjsStudy_weighted_lower hN hEven
  have ht := H30.joint_triple_closed (upper_cutoff_le_lower.trans hN) hEven
    (by simpa only [show (82/10:ℝ)=8.2 by norm_num] using hK)
  have hp := inverse_log_payment hN
  have hN9 : 9≤N := by
    have he := bjsStudy_endpoint hN
    have hh : 2^110+1≤N := (le_max_left _ _).trans he
    omega
  apply joint_selberg_existence hN9 (K:=K) (η:=1/10000) (extra:=0)
    (remainder:=tripleAllocation) (by simpa only [add_zero] using hbudget)
  · convert hl using 1
    norm_num [bjsStudyBudget,ChenBudget.weighted]
    ring
  · simp only [mul_div_assoc,mul_assoc,add_zero] at ht hp ⊢
    linarith only [ht,hp]

theorem chosen_margin : (jointSelbergBudget chosenK (1/10000) 0 tripleAllocation).margin=
    (0.005926:ℝ)-1/(2*10^20) := by
  rw [joint_selberg_margin]
  norm_num [chosenK,tripleAllocation]

theorem chen {N : ℕ} (hN : chenCutoff≤N) (hEven : Even N) :
    ∃ p q : ℕ,p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ,r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  apply chen_from_budget hN hEven (K:=chosenK)
  · norm_num [chosenK]
  · norm_num [chosenK,tripleAllocation]

theorem original_chen : Goldbach.ChenTheorem := ⟨chenCutoff,fun _ hN he => chen hN he⟩

#print axioms chen
end ChenEffective.TightBudget
