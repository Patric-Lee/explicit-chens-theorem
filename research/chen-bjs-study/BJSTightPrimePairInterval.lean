/- Threshold-specialized companion to research/chen-effective/NumericalPrimePairInterval.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.TightBudget. -/
import BJSTightPrimePairThreshold

noncomputable section
namespace ChenEffective.TightBudget
open MathlibNt.SieveTheory
open LiuWeight PrimeReciprocalLogScale
open AnalyticNumberTheory.Mertens
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

theorem numerical_prime_pair_prefix {N : ℕ} (hN : primePairThreshold ≤ N) {a : ℝ}
    (ha : 1/10 ≤ a) :
    |MertensTheorem.primeReciprocalSum (rpowFloor N a)-
      (Real.log a+Real.log (Real.log (N : ℝ))+mertensSecondConstant)| ≤
      9000000000000/Real.log (N : ℝ) := by
  obtain ⟨hN9,hlog,hP,_⟩ := numerical_prime_pair_parameters hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL0 : 0 < Real.log (N : ℝ) := by linarith only [hlog]
  have ha0 : 0 < a := by linarith only [ha]
  have hx := hP.trans (Real.rpow_le_rpow_of_exponent_le hN1 ha)
  have hh := numerical_mertens_second hx
  rw [Real.log_rpow hN0,Real.log_mul ha0.ne' hL0.ne'] at hh
  rw [MertensTheorem.primeReciprocalSum_eq_analyticNumberTheory,rpowFloor]
  apply hh.trans
  apply (div_le_div_iff₀ (mul_pos ha0 hL0) hL0).mpr
  nlinarith only [ha,mul_pos ha0 hL0,mul_nonneg (sub_nonneg.mpr ha) hL0.le]

theorem numerical_prime_pair_interval {N : ℕ} (hN : primePairThreshold ≤ N) {a b : ℝ}
    (ha : 1/10 ≤ a) (hab : a ≤ b) (_hb : b ≤ 1) :
    primeReciprocalLogInterval N a b ≤ Real.log (b/a)+18000000000000/Real.log (N : ℝ) := by
  obtain ⟨hN9,_,_,_⟩ := numerical_prime_pair_parameters hN
  have hpa := numerical_prime_pair_prefix hN ha
  have hpb := numerical_prime_pair_prefix hN (ha.trans hab)
  rw [primeReciprocalLogInterval_eq_sub N (by omega) hab]
  rw [Real.log_div (by linarith only [ha,hab] : b ≠ 0) (by linarith only [ha] : a ≠ 0)]
  simp only [div_eq_mul_inv] at hpa hpb ⊢
  linarith only [(abs_le.mp hpa).1,(abs_le.mp hpb).2]

theorem numerical_prime_pair_log_mass {a b : ℝ} (ha : 1/10 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    0 ≤ Real.log (b/a) ∧ Real.log (b/a) ≤ 10 := by
  have ha0 : 0 < a := by linarith only [ha]
  have hr1 : 1 ≤ b/a := (le_div_iff₀ ha0).mpr (by simpa using hab)
  have hr10 : b/a ≤ 10 := (div_le_iff₀ ha0).mpr (by linarith only [ha,hb])
  exact ⟨Real.log_nonneg hr1,(Real.log_le_sub_one_of_pos (by linarith only [hr1])).trans
    (by linarith only [hr10])⟩

#print axioms numerical_prime_pair_interval
end ChenEffective.TightBudget
