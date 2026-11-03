import NumericalPrimePairThreshold

noncomputable section
namespace ChenEffective
open Real Set MeasureTheory
open scoped Interval
open MathlibNt.SieveTheory.LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem numerical_log_squared_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1/Real.log t^2) volume a b := by
  apply intervalIntegral.intervalIntegrable_one_div
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [ht.1])))
  · apply (Real.continuousOn_log.mono ?_).pow 2
    intro t ht
    rw [uIcc_of_le hab] at ht
    simp only [mem_compl_iff,mem_singleton_iff]
    linarith [ht.1]

theorem numerical_genuine_li_pointwise {x : ℝ} (hx : (logPowerCutoff 2 : ℝ) ≤ x) :
    |liuLogarithmicIntegralRemainder 2 x| ≤ 10*x/Real.log x^2 := by
  have hx9 := real_log_power_cutoff_nine hx
  have hx2 : 2 ≤ x := by linarith only [hx9]
  have hx0 : 0 < x := by linarith only [hx9]
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith only [hx9])
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hs0 := Real.sqrt_nonneg x
  have hs2 : 2 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).mpr (by linarith only [hx9])
  have hsx : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith only [hx9]))
  have hint₁ := numerical_log_squared_integrable (le_refl (2 : ℝ)) hs2
  have hint₂ := numerical_log_squared_integrable hs2 hsx
  have hfirst : (∫ t in (2 : ℝ)..Real.sqrt x, 1/Real.log t^2) ≤ 4*Real.sqrt x := by
    calc
      _ ≤ ∫ _t in (2 : ℝ)..Real.sqrt x, (4 : ℝ) := by
        apply intervalIntegral.integral_mono_on hs2 hint₁ intervalIntegrable_const
        intro t ht
        have htlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht.1
        apply (div_le_iff₀ (sq_pos_of_pos (hlog2.trans_le htlog))).mpr
        nlinarith only [Real.log_two_gt_d9,htlog,sq_nonneg (Real.log t-Real.log 2)]
      _ ≤ _ := by simp only [intervalIntegral.integral_const,smul_eq_mul]; linarith
  have hsecond : (∫ t in Real.sqrt x..x, 1/Real.log t^2) ≤ 4*x/Real.log x^2 := by
    calc
      _ ≤ ∫ _t in Real.sqrt x..x, 4/Real.log x^2 := by
        apply intervalIntegral.integral_mono_on hsx hint₂ intervalIntegrable_const
        intro t ht
        have hlog := Real.log_le_log (Real.sqrt_pos.mpr hx0) ht.1
        rw [Real.log_sqrt hx0.le] at hlog
        have htpos : 0 < Real.log t := by linarith only [hlog,hl0]
        apply (div_le_div_iff₀ (sq_pos_of_pos htpos) (sq_pos_of_pos hl0)).mpr
        nlinarith only [hlog,hl0,sq_nonneg (Real.log t-Real.log x/2)]
      _ = (x-Real.sqrt x)*(4/Real.log x^2) := by simp only [intervalIntegral.integral_const,smul_eq_mul]
      _ ≤ _ := by
        rw [show 4*x/Real.log x^2 = x*(4/Real.log x^2) by ring]
        exact mul_le_mul_of_nonneg_right (sub_le_self x hs0) (by positivity)
  have hp := real_log_pow_le_sqrt (k := 2) hx
  have hroot : Real.sqrt x ≤ x/Real.log x^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hl0)).mpr
    have hh := mul_le_mul_of_nonneg_left hp hs0
    nlinarith only [hh,Real.sq_sqrt hx0.le]
  have hI : |∫ t in (2 : ℝ)..x, 1/Real.log t^2| ≤ 8*x/Real.log x^2 := by
    rw [abs_of_nonneg (intervalIntegral.integral_nonneg hx2 (by intro t _; positivity)),
      ← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂]
    simp only [div_eq_mul_inv,one_mul] at hfirst hsecond hroot ⊢
    linarith only [hfirst,hsecond,hroot]
  have hconst : |(2 : ℝ)-2/Real.log 2| ≤ 2 := by
    have hh : (2 : ℝ)/Real.log 2 ≤ 4 := (div_le_iff₀ hlog2).mpr (by linarith only [Real.log_two_gt_d9])
    rw [abs_le]
    constructor <;> linarith only [hh,div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlog2.le]
  have hscale : 1 ≤ x/Real.log x^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hl0)).mpr
    simpa only [one_mul] using hp.trans hsx
  rw [liuLogarithmicIntegralRemainder_eq 2 hx2]
  have hh := abs_add_le ((2 : ℝ)-2/Real.log 2) (∫ t in (2 : ℝ)..x, 1/Real.log t^2)
  simp only [div_eq_mul_inv,one_mul] at hI hscale hh hconst ⊢
  nlinarith only [hh,hI,hconst,hscale]

#print axioms numerical_genuine_li_pointwise
end ChenEffective
