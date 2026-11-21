import NumericalMellin

/-! Low-frequency Mellin control for the actual smoothing kernel. Together
with the existing high-frequency bound, this avoids paying 1/epsilon on
the entire vertical contour. No GRH assumption is used in this file. -/
namespace ChenEffective.GRH
open Set Function Filter Complex Real MeasureTheory
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

private theorem kernel_amplitude {x : ℝ} (hx : x ∈ Icc (1/2:ℝ) 2) :
    ‖numericalSmoothing x‖ ≤ 64 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (numericalSmoothing_nonneg x)]
  unfold numericalSmoothing positiveSquare
  rw [max_eq_left (by linarith only [hx.1]), max_eq_left (by linarith only [hx.2])]
  calc
    _ ≤ (320/81:ℝ)*2*(3/2:ℝ)^2*(3/2:ℝ)^2 := by gcongr <;> linarith only [hx.1,hx.2]
    _ ≤ _ := by norm_num

theorem kernel_mellin_low_frequency {s : ℂ} (hs : 0 ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖mellin (fun x => (numericalSmoothing x : ℂ)) s‖ ≤ 768 := by
  let f : ℝ → ℂ := fun x => (x : ℂ)^(s-1)*(numericalSmoothing x : ℂ)
  have hsupport : support f ⊆ Icc (1/2:ℝ) 2 := by
    intro x hx
    apply numericalSmoothing_support
    intro hn
    apply hx
    simp [f,hn]
  have heq : mellin (fun x => (numericalSmoothing x : ℂ)) s =
      ∫ x in (1/2:ℝ)..2, f x := by
    unfold mellin
    simp only [smul_eq_mul]
    rw [SetIntegral.integral_eq_integral_inter_of_support_subset_Icc hsupport
      (show Icc (1/2:ℝ) 2 ⊆ Ioi 0 by
        intro x hx
        change 0 < x
        linarith only [hx.1])]
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num)]
  rw [heq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const'
    (f := f) (C := 512) (a := (1/2:ℝ)) (b := 2) (by norm_num) (by
      intro x hx
      have hx0 : 0 < x := by linarith only [hx.1]
      have hp : ‖(x : ℂ)^(s-1)‖ ≤ 8 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        simp only [sub_re, one_re]
        rw [Real.rpow_sub hx0, Real.rpow_one]
        have ht : x^s.re ≤ 4 := by
          calc
            _ ≤ (2:ℝ)^s.re := Real.rpow_le_rpow hx0.le hx.2 hs
            _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs2
            _ = _ := by norm_num
        apply (div_le_iff₀ hx0).mpr
        linarith only [ht,hx.1]
      calc
        ‖f x‖ = ‖(x:ℂ)^(s-1)‖*‖numericalSmoothing x‖ := by simp only [f,norm_mul,Complex.norm_real]
        _ ≤ (8:ℝ)*64 := mul_le_mul hp (kernel_amplitude hx) (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num)
  norm_num at hb
  exact hb

theorem smoothed_mellin_low_frequency {s : ℂ} (hs : 0 < s.re) (hs2 : s.re ≤ 2)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ‖mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) s‖ ≤ 768*‖s‖⁻¹ := by
  rw [MellinOfSmooth1a numericalSmoothing_contDiff numericalSmoothing_support hε hs,norm_mul,norm_inv]
  have hlo : 0 ≤ ((ε:ℂ)*s).re := by
    simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
    positivity
  have hhi : ((ε:ℂ)*s).re ≤ 2 := by
    simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
    nlinarith only [hε,hε1,hs,hs2]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (kernel_mellin_low_frequency hlo hhi) (inv_nonneg.mpr (norm_nonneg s))

theorem smoothed_mellin_min {s : ℂ} (hs : 0 < s.re) (hs2 : s.re ≤ 2)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ‖mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) s‖ ≤
      min (768*‖s‖⁻¹) (768*(ε*‖s‖^2)⁻¹) := by
  exact le_min (smoothed_mellin_low_frequency hs hs2 hε hε1)
    (numerical_smoothed_mellin_bound s.re hs s le_rfl hs2 ε hε hε1)

#print axioms smoothed_mellin_min
end ChenEffective.GRH
