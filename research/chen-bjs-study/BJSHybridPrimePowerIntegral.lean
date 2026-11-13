import BJSHybridIntegralBounds

noncomputable section
namespace ChenEffective.HybridProduct
open Real Set MeasureTheory Filter
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem prefix_weight_bound {a t : ℝ} (ha : 1 < a) (hat : a ≤ t) :
    prefixWeight t ≤ (1/log a+1/(log a)^2)*t^(-2:ℝ) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have ht0 : 0 < t := ha0.trans_le hat
  have hla : 0 < log a := log_pos ha
  have hlog := log_le_log ha0 hat
  have h1 := one_div_le_one_div_of_le hla hlog
  have h2 := one_div_le_one_div_of_le (pow_pos hla 2)
    (pow_le_pow_left₀ hla.le hlog 2)
  have hc : 1/log t+1/(log t)^2 ≤ 1/log a+1/(log a)^2 := add_le_add h1 h2
  have he : prefixWeight t=(1/log t+1/(log t)^2)*t^(-2:ℝ) := by
    rw [rpow_neg ht0.le,rpow_ofNat]
    unfold prefixWeight
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_right hc (rpow_nonneg ht0.le _)

theorem prime_power_weight_envelope {a t : ℝ} (ha : 1 < a) (hat : a ≤ t) :
    |(Chebyshev.psi t-Chebyshev.theta t)*prefixWeight t| ≤
      (17*(1/log a+1/(log a)^2))*t^(-3/2:ℝ) := by
  have ht : 1 < t := ha.trans_le hat
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hgap := prime_power_gap_seventeen t
  have hq := prefix_weight_bound ha hat
  rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t)),
    abs_of_nonneg (prefix_weight_nonneg ht)]
  calc
    _ ≤ (17*sqrt t)*((1/log a+1/(log a)^2)*t^(-2:ℝ)) :=
      mul_le_mul hgap hq (prefix_weight_nonneg ht) (by positivity)
    _ = _ := by
      rw [sqrt_eq_rpow]
      have he : t^(1/2:ℝ)*t^(-2:ℝ)=t^(-3/2:ℝ) := by
        rw [← rpow_add ht0]; norm_num
      linear_combination 17*(1/log a+1/(log a)^2)*he

theorem actual_prime_power_integral_bound {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    |∫ t in a..b,(Chebyshev.psi t-Chebyshev.theta t)*prefixWeight t| ≤
      34*(1/log a+1/(log a)^2)*a^(-1/2:ℝ) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hlog : 0 < log a := log_pos ha
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (f:=fun t : ℝ => (Chebyshev.psi t-Chebyshev.theta t)*prefixWeight t) hab
    (Eventually.of_forall (fun t (ht : t ∈ Ioc a b) => by
      simpa only [Real.norm_eq_abs] using prime_power_weight_envelope ha ht.1.le))
    ((power_interval_integrable (r:=(-3/2:ℝ)) ha0 hab).const_mul
      (17*(1/log a+1/(log a)^2)))
  rw [Real.norm_eq_abs,intervalIntegral.integral_const_mul] at hnorm
  have hb := decaying_power_integral_bound (r:=(3/2:ℝ)) ha0 hab (by norm_num)
  norm_num only at hb
  apply hnorm.trans
  have hc : 0 ≤ 17*(1/log a+1/(log a)^2) := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left hb hc]

#print axioms actual_prime_power_integral_bound
end ChenEffective.HybridProduct
