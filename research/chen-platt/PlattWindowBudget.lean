import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Exact scalar allocation for a Platt-based prefix estimate. The analytic
and finite certificate producers must prove the allocated bounds separately. -/
noncomputable section
namespace ChenEffective.PlattWindow
open Real

def analyticAllowance : ℝ := 59/1000000
def finiteAllowance : ℝ := 1/20000

def anchorEnvelope : ℝ :=
  1/10^8 + 1/10^8 + (75/2)/(100000*23) +
  2*(75/2)*(24/23^2)*(1/100000-1/(3:ℝ)^11) +
  2*(1177/25)*(25/24^2)/(3:ℝ)^11 +
  2*74*(30/29^2)/3000000 +
  2*202*(35/34^2)/30000000 +
  (1/2000000)*(3+1/39) +
  2*1147*(40/39^2)/300000000 +
  (42*10^9)/(10^17*39)

theorem anchorEnvelope_paid : anchorEnvelope ≤ analyticAllowance := by
  norm_num [anchorEnvelope, analyticAllowance]

theorem window_budget_paid : analyticAllowance + finiteAllowance ≤ (1/9000 : ℝ) := by
  norm_num [analyticAllowance, finiteAllowance]

/-- A relative prime-sum certificate avoids assuming a numerical enclosure
of the canonical Mertens constant: the common constant cancels. -/
theorem absolute_of_relative {ex er : ℝ}
    (hr : |er| ≤ analyticAllowance) (hx : |ex-er| ≤ finiteAllowance) :
    |ex| ≤ (1/9000 : ℝ) := by
  have h := (abs_add_le (ex-er) er).trans (add_le_add hx hr)
  have hp := window_budget_paid
  rw [sub_add_cancel] at h
  linarith

end ChenEffective.PlattWindow
