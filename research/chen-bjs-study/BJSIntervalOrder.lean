import ChenBudgetProducts

/-! Endpoint-order regression for the reciprocal-prime interval input.
The version without a <= b is false even for the empty prime set.
This file imports no provisional BJS assumptions.
-/
namespace ChenEffective
open Real Finset

theorem bjsStudy_reversed_interval_counterexample :
    1 < exp (20 : ℝ) ∧ 286 ≤ exp (10 : ℝ) ∧
      (∑ p ∈ (∅ : Finset ℕ), 1/(p : ℝ)) >
        log (log (exp 10)/log (exp 20)) + 1/(log (exp 20))^2 := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10) 5
  norm_num [Finset.sum_range_succ] at he
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨(Real.one_lt_exp_iff.mpr (by norm_num)), (by linarith only [he]), ?_⟩
  simp only [Finset.sum_empty, Real.log_exp]
  norm_num at hl ⊢
  linarith only [hl]

#print axioms bjsStudy_reversed_interval_counterexample
end ChenEffective
