import AnalyticNumberTheory.Mertens.PartialSummation
import PlattWindowBudget

/-! Direct theta-to-reciprocal transfer. This file assumes no numerical data
and introduces no axiom. The finite relative certificate and analytic anchor
are separate obligations. -/
noncomputable section
namespace ChenEffective.PlattWindow
open Real Set MeasureTheory AnalyticNumberTheory.Mertens

def reciprocalError (x : ℝ) : ℝ :=
  primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)

def thetaEndpoint (x : ℝ) : ℝ :=
  (Chebyshev.theta x-x)/(x*log x)

theorem reciprocalError_sub (x r : ℝ) :
    reciprocalError x - reciprocalError r =
      (primeReciprocalSum ⌊x⌋₊ - primeReciprocalSum ⌊r⌋₊) -
        (log (log x)-log (log r)) := by
  unfold reciprocalError
  ring

theorem theta_prefix_transfer {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    reciprocalError a = reciprocalError b + thetaEndpoint a - thetaEndpoint b -
      ∫ t in a..b, thetaErrorKernel t := by
  have hea := mertensSecond_error_decomposition ha
  have heb := mertensSecond_error_decomposition (ha.trans hab)
  have hi := intervalIntegral.integral_Ioi_sub_Ioi
    (integrableOn_thetaErrorKernel.mono_set (by intro t ht; exact lt_of_le_of_lt ha ht)) hab
  unfold reciprocalError thetaEndpoint
  linarith only [hea, heb, hi]

theorem theta_prefix_budget {a b R Ua Ub J : ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b)
    (hb : |reciprocalError b| ≤ R)
    (hua : |thetaEndpoint a| ≤ Ua) (hub : |thetaEndpoint b| ≤ Ub)
    (hj : |∫ t in a..b, thetaErrorKernel t| ≤ J) :
    |reciprocalError a| ≤ R+Ua+Ub+J := by
  rw [theta_prefix_transfer ha hab]
  have h1 := abs_add_le (reciprocalError b) (thetaEndpoint a)
  have h2 := abs_sub (reciprocalError b+thetaEndpoint a) (thetaEndpoint b)
  have h3 := abs_sub (reciprocalError b+thetaEndpoint a-thetaEndpoint b)
    (∫ t in a..b, thetaErrorKernel t)
  linarith only [h1,h2,h3,hb,hua,hub,hj]

/-- The common Mertens constant cancels: no numerical enclosure of it is
needed by the finite certificate. -/
theorem prefix_window_of_relative {r : ℝ}
    (anchor : |reciprocalError r| ≤ analyticAllowance)
    (finite : ∀ x : ℝ, 4000000 ≤ x → x ≤ r →
      |(primeReciprocalSum ⌊x⌋₊-primeReciprocalSum ⌊r⌋₊)-
        (log (log x)-log (log r))| ≤ finiteAllowance)
    (tail : ∀ x : ℝ, r ≤ x → x ≤ (3:ℝ)^120 →
      |reciprocalError x| ≤ (1/9000:ℝ)) :
    ∀ x : ℝ, 4000000 ≤ x → x ≤ (3:ℝ)^120 →
      |reciprocalError x| ≤ (1/9000:ℝ) := by
  intro x hx hxmax
  by_cases hxr : x ≤ r
  · apply absolute_of_relative anchor
    rw [reciprocalError_sub]
    exact finite x hx hxr
  · exact tail x (le_of_not_ge hxr) hxmax

#print axioms theta_prefix_transfer
#print axioms prefix_window_of_relative
end ChenEffective.PlattWindow
