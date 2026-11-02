import NumericalMellin

namespace ChenEffective
open Complex Real Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem numerical_mellin_main_term {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ‖mellin (fun x => (Smooth1 numericalSmoothing ε x : ℂ)) 1 - 1‖ ≤ 2 * ε := by
  let S := Icc (1 / 2 : ℝ) 2
  let w : ℝ → ℝ := fun x => numericalSmoothing x / x
  have hxpos : ∀ x ∈ S, 0 < x := by intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1
  have hws : Function.support w ⊆ S := by
    rw [Function.support_div]
    exact inter_subset_left.trans numericalSmoothing_support
  have hw1 : ∫ x in S, w x = 1 := by
    rw [← SetIntegral.integral_eq_integral_inter_of_support_subset_Icc hws hxpos]
    exact numericalSmoothing_mass_one
  have hwc : ContinuousOn w S := numericalSmoothing_contDiff.continuous.continuousOn.div
    continuousOn_id (fun x hx => (hxpos x hx).ne')
  have hrc : ContinuousOn (fun x : ℝ => x ^ ε) S :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (hxpos x hx).ne')
  have hwi : IntegrableOn w S := hwc.integrableOn_Icc
  have hri : IntegrableOn (fun x => w x * x ^ ε) S := (hwc.mul hrc).integrableOn_Icc
  have hwp (x : ℝ) (hx : x ∈ S) : 0 ≤ w x :=
    div_nonneg (numericalSmoothing_nonneg x) (hxpos x hx).le
  have hlogx (x : ℝ) (hx : x ∈ S) : |Real.log x| ≤ 1 := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hx.1
    have hu := Real.log_le_log (hxpos x hx) hx.2
    norm_num only [Real.log_div, Real.log_one] at hl
    rw [abs_le]
    constructor <;> linarith [Real.log_two_lt_d9]
  have hdiff (x : ℝ) (hx : x ∈ S) : |x ^ ε - 1| ≤ 2 * ε := by
    rw [Real.rpow_def_of_pos (hxpos x hx)]
    have ha : |Real.log x * ε| ≤ ε := by
      rw [abs_mul, abs_of_pos hε]
      exact mul_le_of_le_one_left hε.le (hlogx x hx)
    exact (Real.abs_exp_sub_one_le (ha.trans hε1.le)).trans (by linarith only [ha])
  have hsupp : Function.support (fun x : ℝ => (x : ℂ) ^ ((ε : ℂ) - 1) *
      (numericalSmoothing x : ℂ)) ⊆ S := by
    apply (Function.support_mul_subset_right _ _).trans
    simpa only [Function.support_ofReal] using numericalSmoothing_support
  have hm : mellin (fun x => (numericalSmoothing x : ℂ)) (ε : ℂ) =
      ((∫ x in S, w x * x ^ ε : ℝ) : ℂ) := by
    unfold mellin
    simp only [smul_eq_mul]
    rw [SetIntegral.integral_eq_integral_inter_of_support_subset_Icc (s := Ioi (0 : ℝ))
      hsupp (by intro x hx; exact hxpos x hx)]
    calc
      _ = ∫ x in S, ((w x * x ^ ε : ℝ) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        change (x : ℂ) ^ ((ε : ℂ) - 1) * (numericalSmoothing x : ℂ) =
          ((w x * x ^ ε : ℝ) : ℂ)
        rw [show (ε : ℂ) - 1 = ((ε - 1 : ℝ) : ℂ) by push_cast; rfl,
          ← Complex.ofReal_cpow (hxpos x hx).le,
          Real.rpow_sub_one (hxpos x hx).ne']
        dsimp [w]
        push_cast
        ring
      _ = _ := integral_ofReal
  rw [MellinOfSmooth1a numericalSmoothing_contDiff numericalSmoothing_support hε (by norm_num : (0 : ℝ) < (1 : ℂ).re)]
  simp only [inv_one, mul_one, one_mul]
  rw [hm, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    ← hw1, ← integral_sub hri hwi]
  calc
    _ ≤ ∫ x in S, |w x * x ^ ε - w x| := abs_integral_le_integral_abs
    _ ≤ ∫ x in S, (2 * ε) * w x := by
      apply integral_mono_ae ((hri.sub hwi).abs) (hwi.const_mul (2 * ε))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      change |w x * x ^ ε - w x| ≤ _
      rw [show w x * x ^ ε - w x = w x * (x ^ ε - 1) by ring,
        abs_mul, abs_of_nonneg (hwp x hx)]
      nlinarith only [mul_le_mul_of_nonneg_left (hdiff x hx) (hwp x hx)]
    _ = 2 * ε := by rw [integral_const_mul, hw1, mul_one]

#print axioms numerical_mellin_main_term
end ChenEffective
