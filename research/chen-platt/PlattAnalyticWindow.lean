import PlattAnalyticEnvelope
import PlattFarAnchor

noncomputable section
namespace ChenEffective.PlattWindow
open Real
set_option exponentiation.threshold 1024
variable [Fact TernaryGoldbach.PlattZetaRH]

theorem numerical_analytic_error {x : ℝ}
    (hx : (10:ℝ)^10 ≤ x) (hxb : x ≤ analyticTop) :
    |reciprocalError x| ≤ analyticAllowance := by
  apply analytic_envelope_of_far ?_ ?_ hx hxb
  · exact farAnchor_error
  · exact Dusart.numerical_theta_target farAnchor_large

theorem numerical_reference_error :
    |reciprocalError ((10:ℝ)^10)| ≤ analyticAllowance :=
  numerical_analytic_error le_rfl (by norm_num [analyticTop])

theorem numerical_analytic_tail {x : ℝ}
    (hx : (10:ℝ)^10 ≤ x) (hxb : x ≤ (3:ℝ)^120) :
    |reciprocalError x| ≤ (1/9000:ℝ) := by
  apply (numerical_analytic_error hx (hxb.trans (by norm_num [analyticTop]))).trans
  norm_num [analyticAllowance]

#print axioms numerical_reference_error
#print axioms numerical_analytic_tail

/-- All analytic inputs to the H30 prefix window are discharged here.
The remaining premise is precisely the finite relative certificate on
[4000000,10^10]; no temporary prefix axiom is used. -/
theorem numerical_prefix_window_of_finite
    (finite : ∀ x : ℝ, 4000000 ≤ x → x ≤ (10:ℝ)^10 →
      |(AnalyticNumberTheory.Mertens.primeReciprocalSum ⌊x⌋₊-
          AnalyticNumberTheory.Mertens.primeReciprocalSum ⌊(10:ℝ)^10⌋₊)-
        (log (log x)-log (log ((10:ℝ)^10)))| ≤ finiteAllowance) :
    ∀ x : ℝ, 4000000 ≤ x → x ≤ (3:ℝ)^120 →
      |reciprocalError x| ≤ (1/9000:ℝ) :=
  prefix_window_of_relative numerical_reference_error finite
    (fun _ hx hxb => numerical_analytic_tail hx hxb)

#print axioms numerical_prefix_window_of_finite
end ChenEffective.PlattWindow
