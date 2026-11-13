import BJSHybridIntegratedEnvelope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace ChenEffective.HybridProduct
open Complex.Hadamard
open Real Set MeasureTheory Filter
open scoped Interval
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem power_interval_integrable {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => t^r) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact (continuousAt_id.rpow_const (Or.inl (ne_of_gt (ha.trans_le ht.1)))).continuousWithinAt

theorem decaying_power_integral_bound {a b r : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hr : r < 2) :
    (∫ t in a..b,t^(r-3)) ≤ a^(r-2)/(2-r) := by
  have hrn : r-3 ≠ -1 := by linarith only [hr]
  have hz : (0:ℝ) ∉ [[a,b]] := by rw [uIcc_of_le hab]; simp only [mem_Icc,not_and]; intro hh; linarith only [ha,hh]
  rw [integral_rpow (Or.inr ⟨hrn,hz⟩)]
  have he : r-3+1=r-2 := by ring
  rw [he]
  calc
    _ = (a^(r-2)-b^(r-2))/(2-r) := by
      rw [show 2-r=-(r-2) by ring,div_neg]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (sub_le_self _ (rpow_nonneg (ha.trans_le hab).le _)) (by linarith only [hr])

/-- The actual integrated error has a uniform decaying bound. The large
constant residue occurs only with x^-2 here, rather than with x^-1/16. -/
theorem actual_integrated_psi1_bound (H : Finset DusartXiZero) {a b W : ℝ}
    (ha : 1 < a) (hab : a ≤ b)
    (hline : ∀ p ∈ H,(divisorZeroIndex₀_val p).re=1/2)
    (hW : (∑' p : {p : DusartXiZero // p ∉ H},absoluteXiWeight p) ≤ W) :
    |∫ t in a..b,psi1Error t*prefixSlope t| ≤ slopeCoefficient (log a)*
      ((6/25)*a^(-1/2:ℝ)+8*W*a^(-1/8:ℝ)+2*a^(-1:ℝ)+500000000*a^(-2:ℝ)) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hW0 : 0 ≤ W := (tsum_nonneg (fun _ => norm_nonneg _)).trans hW
  have hC0 : 0 ≤ slopeCoefficient (log a) := by unfold slopeCoefficient; have := log_pos ha; positivity
  have hi1 := power_interval_integrable (r:=(-3/2:ℝ)) ha0 hab
  have hi2 := power_interval_integrable (r:=(-9/8:ℝ)) ha0 hab
  have hi3 := power_interval_integrable (r:=(-2:ℝ)) ha0 hab
  have hi4 := power_interval_integrable (r:=(-3:ℝ)) ha0 hab
  have hg1 := hi1.const_mul (3/25:ℝ)
  have hg2 := hi2.const_mul W
  have hg3 := hi3.const_mul (2:ℝ)
  have hg4 := hi4.const_mul (1000000000:ℝ)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (f:=fun t : ℝ => psi1Error t*prefixSlope t) hab
    (Eventually.of_forall (fun t (ht : t ∈ Ioc a b) => by
      simpa only [Real.norm_eq_abs] using psi1_slope_envelope H ha ht.1.le hline hW))
    (((hg1.add hg2).add hg3).add hg4 |>.const_mul (slopeCoefficient (log a)))
  rw [Real.norm_eq_abs] at hnorm
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hg1.add hg2).add hg3) hg4,
    intervalIntegral.integral_add (hg1.add hg2) hg3,
    intervalIntegral.integral_add hg1 hg2,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hnorm
  have h1 := decaying_power_integral_bound (r:=(3/2:ℝ)) ha0 hab (by norm_num)
  have h2 := decaying_power_integral_bound (r:=(15/8:ℝ)) ha0 hab (by norm_num)
  have h3 := decaying_power_integral_bound (r:=(1:ℝ)) ha0 hab (by norm_num)
  have h4 := decaying_power_integral_bound (r:=(0:ℝ)) ha0 hab (by norm_num)
  norm_num only at h1 h2 h3 h4
  apply hnorm.trans
  apply mul_le_mul_of_nonneg_left _ hC0
  nlinarith only [h1,h3,h4,mul_le_mul_of_nonneg_left h2 hW0]

#print axioms actual_integrated_psi1_bound
end ChenEffective.HybridProduct

