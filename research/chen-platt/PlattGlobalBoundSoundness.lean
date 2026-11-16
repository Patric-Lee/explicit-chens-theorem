import PlattGlobalBoundKernel
import PlattAssemblySoundness

noncomputable section
set_option autoImplicit false
namespace ChenEffective.PlattWindow
open AnalyticNumberTheory.Mertens

theorem reciprocalBound_sound {a b lower upper : ℕ}
    (h : ReciprocalBound a b lower upper) :
    (lower:ℝ) ≤ (2:ℝ)^48*(primeReciprocalSum b-primeReciprocalSum a) ∧
      (2:ℝ)^48*(primeReciprocalSum b-primeReciprocalSum a) ≤ (upper:ℝ) := by
  induction h with
  | zero => simp
  | block hcert hcheck => exact checked_increment_summary_sound hcert hcheck
  | append h₁ h₂ ih₁ ih₂ =>
    simpa only [Nat.cast_add] using cumulative_bounds_join ih₁ ih₂
  | relabel hl hu h ih => simpa only [← hl,← hu] using ih

#print axioms reciprocalBound_sound
end ChenEffective.PlattWindow
