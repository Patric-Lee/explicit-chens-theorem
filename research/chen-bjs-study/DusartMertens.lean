import DusartThetaTail

/-! The Abel-summation step used in Dusart's reciprocal-prime estimates.
The theta estimate is an explicit hypothesis, not a new axiom. -/
noncomputable section
namespace ChenEffective
open Real Set MeasureTheory Filter AnalyticNumberTheory.Mertens
open scoped Topology
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

private theorem log_kernel_deriv (n : ℕ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => -((log t)⁻¹ ^ (n + 1)) / (n + 1 : ℝ))
      (t⁻¹ / (log t) ^ (n + 2)) t := by
  convert! ((hasDerivAt_inv_log (by linarith : t ≠ 0)
    (by linarith : t ≠ 1) (by linarith : t ≠ -1)).pow (n + 1)).neg.div_const
      (n + 1 : ℝ) using 1
  push_cast
  simp only [inv_pow]
  have hl : log t ≠ 0 := ne_of_gt (log_pos ht)
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hl, hn, pow_succ]
  ring

private theorem log_kernel_limit (n : ℕ) :
    Tendsto (fun t : ℝ => -((log t)⁻¹ ^ (n + 1)) / (n + 1 : ℝ))
      atTop (𝓝 0) := by
  simpa using ((tendsto_log_atTop.inv_tendsto_atTop.pow (n + 1)).neg.div_const
    (n + 1 : ℝ))

theorem dusart_log_kernel_integrable (n : ℕ) {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun t : ℝ => t⁻¹ / (log t) ^ (n + 2)) (Ioi x) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (fun t ht => log_kernel_deriv n (hx.trans_le ht)) _ (log_kernel_limit n)
  intro t ht
  have ht0 : 0 < t := by linarith only [hx, ht.out]
  have hl : 0 < log t := log_pos (hx.trans ht.out)
  positivity

theorem dusart_log_kernel_integral (n : ℕ) {x : ℝ} (hx : 1 < x) :
    (∫ t in Ioi x, t⁻¹ / (log t) ^ (n + 2)) =
      1 / ((n + 1 : ℝ) * (log x) ^ (n + 1)) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => log_kernel_deriv n (hx.trans_le ht))
    (dusart_log_kernel_integrable n hx) (log_kernel_limit n)]
  simp only [zero_sub, neg_div, neg_neg, inv_pow]
  field_simp

theorem dusart_mertens_of_theta_log_squared {x : ℝ} (hx : 9 ≤ x)
    (hθ : ∀ t : ℝ, x ≤ t → |Chebyshev.theta t - t| ≤ 4 * t / (log t) ^ 2) :
    |primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)| ≤
      2 / (log x) ^ 2 + 16 / (3 * (log x) ^ 3) := by
  have hx1 : 1 < x := by linarith only [hx]
  have hx0 : 0 < x := by linarith only [hx]
  have hl : 0 < log x := log_pos hx1
  have hk (t : ℝ) (ht : x ≤ t) :
      ‖thetaErrorKernel t‖ ≤ 4 * (t⁻¹ / (log t) ^ 3 + t⁻¹ / (log t) ^ 4) := by
    have ht0 : 0 < t := hx0.trans_le ht
    have hlt : 0 < log t := log_pos (hx1.trans_le ht)
    have hn : ‖thetaErrorKernel t‖ =
        |Chebyshev.theta t - t| * ((log t + 1) / (t * log t) ^ 2) := by
      unfold thetaErrorKernel
      rw [Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_nonneg (by linarith only [hlt] : 0 ≤ log t + 1),
        abs_of_nonneg (sq_nonneg (t * log t))]
      ring
    rw [hn]
    calc
      _ ≤ (4 * t / (log t) ^ 2) * ((log t + 1) / (t * log t) ^ 2) :=
        mul_le_mul_of_nonneg_right (hθ t ht) (by positivity)
      _ = _ := by field_simp
  have hi3 := dusart_log_kernel_integrable 1 hx1
  have hi4 := dusart_log_kernel_integrable 2 hx1
  have htail : ‖∫ t in Ioi x, thetaErrorKernel t‖ ≤
      2 / (log x) ^ 2 + 4 / (3 * (log x) ^ 3) := by
    calc
      _ ≤ ∫ t in Ioi x, 4 * (t⁻¹ / (log t) ^ 3 + t⁻¹ / (log t) ^ 4) := by
        apply norm_integral_le_of_norm_le ((hi3.add hi4).const_mul 4)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hk t ht.le
      _ = _ := by
        rw [integral_const_mul, integral_add hi3 hi4,
          dusart_log_kernel_integral 1 hx1, dusart_log_kernel_integral 2 hx1]
        norm_num
        ring
  have hend : |(Chebyshev.theta x - x) / (x * log x)| ≤ 4 / (log x) ^ 3 := by
    rw [abs_div, abs_of_pos (mul_pos hx0 hl)]
    calc
      _ ≤ (4 * x / (log x) ^ 2) / (x * log x) :=
        div_le_div_of_nonneg_right (hθ x le_rfl) (by positivity)
      _ = _ := by field_simp
  rw [mertensSecond_error_decomposition (by linarith only [hx])]
  have hh := abs_sub ((Chebyshev.theta x - x) / (x * log x))
    (∫ t in Ioi x, thetaErrorKernel t)
  rw [Real.norm_eq_abs] at htail
  have heq : 4 / (log x) ^ 3 + (2 / (log x) ^ 2 + 4 / (3 * (log x) ^ 3)) =
      2 / (log x) ^ 2 + 16 / (3 * (log x) ^ 3) := by ring
  exact hh.trans (by rw [← heq]; exact add_le_add hend htail)

theorem dusart_mertens_log_squared_tail {x : ℝ}
    (hx : 0 < x) (hlog : 3400 ≤ log x) :
    |primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)| ≤
      2 / (log x) ^ 2 + 16 / (3 * (log x) ^ 3) := by
  apply dusart_mertens_of_theta_log_squared
    (by linarith only [hlog, log_le_sub_one_of_pos hx])
  intro t ht
  exact dusart_theta_log_squared_tail (hx.trans_le ht)
    (hlog.trans (log_le_log hx ht))

/-- Only the bounded logarithmic range is needed in addition to the
already proved far tail. This hypothesis remains to be established. -/
theorem dusart_mertens_of_middle_range {x : ℝ} (hx : 9 ≤ x)
    (hmiddle : ∀ t : ℝ, x ≤ t → log t < 3400 →
      |Chebyshev.theta t - t| ≤ 4 * t / (log t) ^ 2) :
    |primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)| ≤
      2 / (log x) ^ 2 + 16 / (3 * (log x) ^ 3) := by
  apply dusart_mertens_of_theta_log_squared hx
  intro t ht
  by_cases hlog : 3400 ≤ log t
  · exact dusart_theta_log_squared_tail (by linarith only [hx, ht]) hlog
  · exact hmiddle t ht (lt_of_not_ge hlog)

/-- The complete two-endpoint prefix error fits the small exponential
budget already at log(x)=131; no factor-two exponential conversion. -/
theorem dusart_two_prefix_payment {L : ℝ} (hL : 131 ≤ L) :
    4 / L ^ 2 + 32 / (3 * L ^ 3) ≤ (3 / 12500 : ℝ) := by
  have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 131) hL 2
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 131) hL 3
  have h2i := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 131 ^ 2) h2
  have h3i := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 131 ^ 3) h3
  norm_num at h2i h3i
  have heq : 4 / L ^ 2 + 32 / (3 * L ^ 3) =
      4 * (1 / L ^ 2) + (32 / 3) * (1 / L ^ 3) := by ring
  rw [heq]
  simp only [one_div]
  linarith only [h2i, h3i]

theorem dusart_small_exp_payment {δ : ℝ} (hδ : δ ≤ 3 / 12500) :
    exp δ ≤ 1 + (1 / 4000 : ℝ) := by
  have ht := add_one_le_exp (-(3 / 12500 : ℝ))
  have hh := mul_le_mul_of_nonneg_right ht (exp_pos (3 / 12500 : ℝ)).le
  have heq : exp (-(3 / 12500 : ℝ)) * exp (3 / 12500) = 1 := by
    rw [← exp_add]
    norm_num
  rw [heq] at hh
  exact (exp_le_exp.mpr hδ).trans (by linarith only [hh])

#print axioms dusart_mertens_of_theta_log_squared
#print axioms dusart_mertens_log_squared_tail
#print axioms dusart_mertens_of_middle_range
#print axioms dusart_two_prefix_payment
#print axioms dusart_small_exp_payment
end ChenEffective
