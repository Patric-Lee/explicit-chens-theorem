import PlattSchoenfeldEnvelope
import PlattFarAnchor

/-! CONDITIONAL2e9 window assembly. SourcePsiBound and the full finite
certificate are explicit premises. Neither has been installed as an axiom.
This file does not replace the currently checked1e10 analytic route. -/
noncomputable section
namespace ChenEffective.PlattWindow.Schoenfeld
open Real AnalyticNumberTheory.Mertens
set_option autoImplicit false
set_option exponentiation.threshold 1024
variable [Fact TernaryGoldbach.PlattZetaRH]

theorem analytic_error_of_source (hsource : SourcePsiBound) {x : ℝ}
    (hx : reference ≤ x) (hxhi : x ≤ (3:ℝ)^120) :
    |reciprocalError x| ≤ analyticBudget := by
  apply error_of_source_and_far hsource ?_ ?_ hx (hxhi.trans (by norm_num [analyticTop]))
  · exact farAnchor_error
  · exact Dusart.numerical_theta_target farAnchor_large

theorem prefix_window_of_source_and_finite (hsource : SourcePsiBound)
    (hfinite : ∀ x : ℝ, 4000000 ≤ x → x ≤ reference →
      |(primeReciprocalSum ⌊x⌋₊-primeReciprocalSum ⌊reference⌋₊)-
        (log (log x)-log (log reference))| ≤ finiteBudget) :
    ∀ x : ℝ, 4000000 ≤ x → x ≤ (3:ℝ)^120 → |reciprocalError x| ≤ (1/9000:ℝ) := by
  intro x hx hxhi
  by_cases hxr : x ≤ reference
  · apply absolute_of_relative
      (analytic_error_of_source hsource le_rfl (by norm_num [reference]))
    rw [reciprocalError_sub]
    exact hfinite x hx hxr
  · exact (analytic_error_of_source hsource (le_of_not_ge hxr) hxhi).trans
      (by norm_num [analyticBudget])

#print axioms analytic_error_of_source
#print axioms prefix_window_of_source_and_finite
#check @prefix_window_of_source_and_finite
end ChenEffective.PlattWindow.Schoenfeld
