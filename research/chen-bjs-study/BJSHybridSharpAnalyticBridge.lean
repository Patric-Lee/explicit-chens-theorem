import BJSHybridAnalyticBridge
import BJSHybridSharpPrimePowerIntegral
noncomputable section
namespace ChenEffective.HybridProduct.SharpPrimePowers
open Complex.Hadamard Real Set MeasureTheory
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def unsmoothedEnvelope (x h A W : ℝ) : ℝ :=
  h/2+2+A*sqrt (x+h)+W*((x+h)^(15/8:ℝ)+x^(15/8:ℝ))/h+2/h

def rawPsi1Envelope (x W : ℝ) : ℝ :=
  (3/25)*x^(3/2:ℝ)+W*x^(15/8:ℝ)+2*x+1000000000

def integratedEnvelope (a W : ℝ) : ℝ := slopeCoefficient (log a)*
  ((6/25)*a^(-1/2:ℝ)+8*W*a^(-1/8:ℝ)+2*a^(-1:ℝ)+500000000*a^(-2:ℝ))

def primePowerEnvelope (a : ℝ) : ℝ := 4*(1/log a+1/(log a)^2)*a^(-1/2:ℝ)

def thetaEndpointEnvelope (x h A W : ℝ) : ℝ :=
  (unsmoothedEnvelope x h A W+2*sqrt x)/(x*log x)

theorem actual_theta_endpoint_bound (H : Finset DusartXiZero) {x h A W : ℝ}
    (hx : 1 < x-h) (hlarge : (3:ℝ)^16 ≤ x) (hh : 0 < h)
    (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2)
    (hA : headDerivativeMass H ≤ A)
    (hW : (∑' p : {p : DusartXiZero // p ∉ H},absoluteXiWeight p) ≤ W) :
    |(Chebyshev.theta x-x)/(x*log x)| ≤ thetaEndpointEnvelope x h A W := by
  have hx1 : 1 < x := by linarith only [hx,hh]
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hL : 0 < log x := log_pos hx1
  have hpsi := actual_psi_bound H hx hh hline hA hW
  have hgap : |Chebyshev.psi x-Chebyshev.theta x| ≤ 2*sqrt x := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))]
    exact prime_power_gap_two hlarge
  have he : Chebyshev.theta x-x=(Chebyshev.psi x-x)-(Chebyshev.psi x-Chebyshev.theta x) := by ring
  unfold thetaEndpointEnvelope
  rw [abs_div,abs_of_pos (mul_pos hx0 hL),he]
  exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add hpsi hgap)) (mul_pos hx0 hL).le

theorem actual_psi1_endpoint_bound (H : Finset DusartXiZero) {x W : ℝ}
    (hx : 1 < x) (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2)
    (hW : (∑' p : {p : DusartXiZero // p ∉ H},absoluteXiWeight p) ≤ W) :
    |psi1Error x*prefixWeight x| ≤ rawPsi1Envelope x W*prefixWeight x := by
  rw [abs_mul,abs_of_nonneg (prefix_weight_nonneg hx)]
  exact mul_le_mul_of_nonneg_right (psi1_error_envelope H hx hline hW) (prefix_weight_nonneg hx)

/-- Complete finite analytic bridge. The finite-head and scalar budgets are
explicit hypotheses to be supplied by kernel-checked certificates. No zero
completeness or finite-height RH hypothesis is required. -/
theorem actual_prefix_from_head (H : Finset DusartXiZero) {a b h k A W R : ℝ}
    (ha : 2 ≤ a) (hlarge : (3:ℝ)^16 ≤ a) (hab : a ≤ b) (hxa : 1 < a-h) (hxb : 1 < b-k)
    (hh : 0 < h) (hk : 0 < k)
    (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2)
    (hA : headDerivativeMass H ≤ A)
    (hW : (∑' p : {p : DusartXiZero // p ∉ H},absoluteXiWeight p) ≤ W)
    (hb : |prefixError b| ≤ R) :
    |prefixError a| ≤ R+thetaEndpointEnvelope a h A W+thetaEndpointEnvelope b k A W+
      rawPsi1Envelope a W*prefixWeight a+rawPsi1Envelope b W*prefixWeight b+
      integratedEnvelope a W+primePowerEnvelope a := by
  have ha1 : 1 < a := by linarith only [ha]
  exact actual_prefix_budget ha hab hb
    (actual_theta_endpoint_bound H hxa hlarge hh hline hA hW)
    (actual_theta_endpoint_bound H hxb (hlarge.trans hab) hk hline hA hW)
    (actual_psi1_endpoint_bound H ha1 hline hW)
    (actual_psi1_endpoint_bound H (ha1.trans_le hab) hline hW)
    (actual_integrated_psi1_bound H ha1 hab hline hW)
    (actual_prime_power_integral_bound ha1 hlarge hab)

/-- The terminal signed prefix bound comes from the existing proved Dusart
branch; it is not a separate analytic assumption. -/
theorem actual_prefix_from_head_dusart (H : Finset DusartXiZero) {a b h k A W : ℝ}
    (ha : 2 ≤ a) (hlarge : (3:ℝ)^16 ≤ a) (hab : a ≤ b) (hb : (3:ℝ)^120 ≤ b)
    (hxa : 1 < a-h) (hxb : 1 < b-k) (hh : 0 < h) (hk : 0 < k)
    (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2)
    (hA : headDerivativeMass H ≤ A)
    (hW : (∑' p : {p : DusartXiZero // p ∉ H},absoluteXiWeight p) ≤ W) :
    |prefixError a| ≤ 1/(2*(log b)^2)+thetaEndpointEnvelope a h A W+thetaEndpointEnvelope b k A W+
      rawPsi1Envelope a W*prefixWeight a+rawPsi1Envelope b W*prefixWeight b+
      integratedEnvelope a W+primePowerEnvelope a := by
  exact actual_prefix_from_head H ha hlarge hab hxa hxb hh hk hline hA hW (dusart_sharp_mertens hb)

#print axioms actual_prefix_from_head_dusart

/-- A proved, nonvacuous fallback using the empty head and the already proved
global moment. It needs no numerical zero table or certificate assumptions. -/
theorem actual_prefix_without_zero_table {a b h k : ℝ}
    (ha : 2 ≤ a) (hlarge : (3:ℝ)^16 ≤ a) (hab : a ≤ b) (hb : (3:ℝ)^120 ≤ b)
    (hxa : 1 < a-h) (hxb : 1 < b-k) (hh : 0 < h) (hk : 0 < k) :
    |prefixError a| ≤ 1/(2*(log b)^2)+thetaEndpointEnvelope a h 0 (9/100)+
      thetaEndpointEnvelope b k 0 (9/100)+
      rawPsi1Envelope a (9/100)*prefixWeight a+rawPsi1Envelope b (9/100)*prefixWeight b+
      integratedEnvelope a (9/100)+primePowerEnvelope a := by
  have hw := finite_head_moment_residual (∅ : Finset DusartXiZero)
  simp only [Finset.sum_empty,sub_zero] at hw
  have hW : (∑' p : {p : DusartXiZero // p ∉ (∅ : Finset DusartXiZero)},
      absoluteXiWeight p) ≤ (9/100:ℝ) := by
    linarith only [hw,dusart_completed_zero_upper]
  exact actual_prefix_from_head_dusart (∅ : Finset DusartXiZero) ha hlarge hab hb hxa hxb hh hk
    (by simp) (by simp [headDerivativeMass]) hW

#print axioms actual_prefix_without_zero_table
end ChenEffective.HybridProduct.SharpPrimePowers
