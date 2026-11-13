import BJSHybridPsiPrimitive
import AnalyticNumberTheory.Mertens.PartialSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
namespace ChenEffective.HybridProduct
open Real Set MeasureTheory
open scoped Interval
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def prefixWeight (x : ℝ) : ℝ := (log x+1)/(x*log x)^2
def prefixSlope (x : ℝ) : ℝ := (2*(log x)^2+3*log x+2)/(x^3*(log x)^3)

theorem prefix_weight_derivative {x : ℝ} (hx : 1 < x) :
    HasDerivAt prefixWeight (-prefixSlope x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hl : log x ≠ 0 := (log_pos hx).ne'
  have hd := ((hasDerivAt_log hx0).add_const 1).div
    (((hasDerivAt_id x).mul (hasDerivAt_log hx0)).pow 2)
    (pow_ne_zero 2 (mul_ne_zero hx0 hl))
  convert! hd using 1
  simp only [prefixSlope, Pi.pow_apply, Pi.mul_apply, id_eq]
  field_simp
  ring

theorem prefix_weight_continuousOn {a b : ℝ} (ha : 1 < a) (_hab : a ≤ b) :
    ContinuousOn prefixWeight (Icc a b) := by
  intro x hx
  exact (prefix_weight_derivative (ha.trans_le hx.1)).continuousAt.continuousWithinAt

theorem prefix_slope_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn prefixSlope (Icc a b) := by
  intro x hx
  have hx1 : 1 < x := ha.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx1)
  have hl : log x ≠ 0 := (log_pos hx1).ne'
  have hxpos : 0 < x := zero_lt_one.trans hx1
  have hlpos : 0 < log x := log_pos hx1
  unfold prefixSlope
  fun_prop (disch := positivity)

/-- Integration by parts for the actual integrated Chebyshev error, including
its integer kinks via right derivatives. -/
theorem actual_psi_weighted_parts {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b,(Chebyshev.psi t-t)*prefixWeight t =
      psi1Error b*prefixWeight b-psi1Error a*prefixWeight a+
        ∫ t in a..b,psi1Error t*prefixSlope t := by
  have hF : ContinuousOn psi1Error (Icc a b) := by
    intro x hx
    exact ((psi1_continuousAt (by linarith only [ha,hx.1])).sub
      (by fun_prop)).continuousWithinAt
  have hq := prefix_weight_continuousOn ha hab
  have hq' := prefix_slope_continuousOn (b:=b) ha
  have hpsi : IntervalIntegrable (fun t : ℝ => Chebyshev.psi t-t) volume a b :=
    (show IntervalIntegrable Chebyshev.psi volume a b from
      Chebyshev.psi_mono.intervalIntegrable).sub (continuous_id.intervalIntegrable a b)
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (u:=psi1Error) (v:=prefixWeight) (u':=fun t => Chebyshev.psi t-t)
    (v':=fun t => -prefixSlope t)
    (by simpa only [uIcc_of_le hab, Pi.neg_def, Pi.mul_def] using hF)
    (by simpa only [uIcc_of_le hab, Pi.neg_def, Pi.mul_def] using hq)
    (by intro x hx; simp only [min_eq_left hab,max_eq_right hab] at hx
        exact psi1_error_right_derivative (by linarith only [ha,hx.1]))
    (by intro x hx; simp only [min_eq_left hab,max_eq_right hab] at hx
        exact (prefix_weight_derivative (ha.trans hx.1)).hasDerivWithinAt)
    hpsi (by simpa only [uIcc_of_le hab, Pi.neg_def, Pi.mul_def] using (hq'.neg.mono (by rw [uIcc_of_le hab])).intervalIntegrable)
  have hprod : IntervalIntegrable (fun t => psi1Error t*prefixSlope t) volume a b :=
    (by simpa only [uIcc_of_le hab, Pi.neg_def, Pi.mul_def] using ((hF.mul hq').mono (by rw [uIcc_of_le hab])).intervalIntegrable)
  have hfirst := hpsi.mul_continuousOn (by simpa only [uIcc_of_le hab, Pi.neg_def, Pi.mul_def] using hq)
  simp only [mul_neg,← sub_eq_add_neg] at hparts
  rw [intervalIntegral.integral_sub hfirst hprod] at hparts
  linarith only [hparts]

/-- Exact bridge from the actual theta kernel to the integrated psi1 error.
The prime-power correction is retained, rather than silently replacing theta by psi. -/
theorem actual_theta_weighted_parts {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b,AnalyticNumberTheory.Mertens.thetaErrorKernel t =
      psi1Error b*prefixWeight b-psi1Error a*prefixWeight a+
        (∫ t in a..b,psi1Error t*prefixSlope t)-
        ∫ t in a..b,(Chebyshev.psi t-Chebyshev.theta t)*prefixWeight t := by
  have ha1 : 1 < a := by linarith only [ha]
  have hq := prefix_weight_continuousOn ha1 hab
  have hpsi : IntervalIntegrable Chebyshev.psi volume a b := Chebyshev.psi_mono.intervalIntegrable
  have htheta : IntervalIntegrable Chebyshev.theta volume a b := Chebyshev.theta_mono.intervalIntegrable
  have hpow := (hpsi.sub htheta).mul_continuousOn (by simpa only [uIcc_of_le hab, Pi.neg_def, Pi.mul_def] using hq)
  have hfirst := (hpsi.sub (continuous_id.intervalIntegrable a b)).mul_continuousOn
    (by simpa only [uIcc_of_le hab, Pi.neg_def, Pi.mul_def] using hq)
  have he : (fun t => AnalyticNumberTheory.Mertens.thetaErrorKernel t)=
      (fun t => (Chebyshev.psi t-t)*prefixWeight t-
        (Chebyshev.psi t-Chebyshev.theta t)*prefixWeight t) := by
    funext t
    unfold AnalyticNumberTheory.Mertens.thetaErrorKernel prefixWeight
    ring
  simp only [id_eq] at hfirst
  rw [he,intervalIntegral.integral_sub hfirst hpow,actual_psi_weighted_parts ha1 hab]

#print axioms actual_theta_weighted_parts
end ChenEffective.HybridProduct









