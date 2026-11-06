import BJSSmallSignedPrefix
import BJSReciprocalTail3300

/-! The remaining analytic range, after the proved finite base and tail.
These are theorem hypotheses, not axioms; neither is claimed to be proved.
-/
noncomputable section
namespace ChenEffective
open Real Finset AnalyticNumberTheory.Mertens
set_option maxHeartbeats 0

theorem bjsStudy_interval_of_remaining_prefix
    (hL : ∀ x : ℝ, 286 < x → x < (3 : ℝ)^(3072 : ℕ) →
      log (log x)+mertensSecondConstant-1/(2*(log x)^2) ≤ primeReciprocalSum ⌊x⌋₊)
    (hU : ∀ x : ℝ, 286 ≤ x → x < (3 : ℝ)^(3072 : ℕ) →
      primeReciprocalSum ⌊x⌋₊ ≤ log (log x)+mertensSecondConstant+1/(2*(log x)^2))
    (s : Finset ℕ) (a b : ℝ) (ha : 1 < a) (hb : 286 ≤ b) (hab : a ≤ b)
    (hs : ∀ p ∈ s, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) :
    (∑ p ∈ s, 1/(p : ℝ)) ≤ log (log b/log a)+1/(log a)^2 := by
  apply bjsStudy_interval_of_half_log_squared_prefix
    (B := mertensSecondConstant) ?_ ?_ s a b ha hb hab hs
  · intro x hx
    by_cases hsmall : x ≤ 286
    · exact bjsSmallSignedPrefix_lower hx hsmall
    · by_cases hlarge : (3 : ℝ)^(3072 : ℕ) ≤ x
      · have he := (abs_le.mp (bjsStudy_reciprocal_prefix_from_3072 hlarge)).1
        linarith only [he]
      · exact hL x (lt_of_not_ge hsmall) (lt_of_not_ge hlarge)
  · intro x hx
    by_cases hlarge : (3 : ℝ)^(3072 : ℕ) ≤ x
    · have he := (abs_le.mp (bjsStudy_reciprocal_prefix_from_3072 hlarge)).2
      linarith only [he]
    · exact hU x hx (lt_of_not_ge hlarge)

#print axioms bjsStudy_interval_of_remaining_prefix
end ChenEffective
