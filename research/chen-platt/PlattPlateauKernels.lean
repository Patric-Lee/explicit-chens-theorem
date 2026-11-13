import PlattKernelBounds

noncomputable section
namespace ChenEffective.PlattWindow
open Real Set MeasureTheory
set_option maxHeartbeats 1200000

def linearKernel (t : ℝ) : ℝ := (log t+1)/(t*(log t)^2)
def constantKernel (t : ℝ) : ℝ := (log t+1)/(t*log t)^2

theorem linearKernel_derivative {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => log (log t)-(log t)⁻¹) (linearKernel t) t := by
  have ht0 : t ≠ 0 := by linarith only [ht]
  have hl : log t ≠ 0 := (log_pos ht).ne'
  have hd := (hasDerivAt_log hl).comp t (hasDerivAt_log ht0)
  have hi := (hasDerivAt_log ht0).inv hl
  convert hd.sub hi using 1 <;> first | rfl | ((try dsimp [linearKernel]); field_simp [ht0,hl]; ring)

theorem constantKernel_derivative {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => -(t*log t)⁻¹) (constantKernel t) t := by
  have ht0 : t ≠ 0 := by linarith only [ht]
  have hl : log t ≠ 0 := (log_pos ht).ne'
  have hd := (((hasDerivAt_id t).mul (hasDerivAt_log ht0)).inv (mul_ne_zero ht0 hl)).neg
  convert hd using 1 <;> first | rfl | ((try dsimp [constantKernel]); field_simp [ht0,hl] <;> ring)

theorem linearKernel_integrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable linearKernel volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro t ht
  have ht1 : 1 < t := ha.trans_le ht.1
  have ht0 : t ≠ 0 := by linarith only [ht1]
  have hl : log t ≠ 0 := (log_pos ht1).ne'
  unfold linearKernel
  fun_prop (disch := simp [ht0,hl])

theorem constantKernel_integrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable constantKernel volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro t ht
  have ht1 : 1 < t := ha.trans_le ht.1
  have ht0 : t ≠ 0 := by linarith only [ht1]
  have hl : log t ≠ 0 := (log_pos ht1).ne'
  unfold constantKernel
  fun_prop (disch := simp [ht0,hl])

theorem integral_linearKernel {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, linearKernel t) =
      log (log b)-log (log a)+1/log a-1/log b := by
  have hd : ∀ t ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => log (log t)-(log t)⁻¹) (linearKernel t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact linearKernel_derivative (ha.trans_le ht.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (linearKernel_integrable ha hab)]
  simp only [one_div]
  ring

theorem integral_constantKernel {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, constantKernel t) = 1/(a*log a)-1/(b*log b) := by
  have hd : ∀ t ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => -(t*log t)⁻¹) (constantKernel t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact constantKernel_derivative (ha.trans_le ht.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (constantKernel_integrable ha hab)]
  simp only [one_div]
  ring

#print axioms integral_linearKernel
#print axioms integral_constantKernel
end ChenEffective.PlattWindow
