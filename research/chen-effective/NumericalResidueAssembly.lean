import NumericalPrimitiveContour

namespace ChenEffective
open Set Complex Real MeasureTheory
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false

theorem numerical_residue_assembly (F : ℂ → ℂ) (A : ℂ)
    {a b T Vl Hu Hl Tl Tu : ℝ} (_hT : 0 ≤ T)
    (hf : Integrable (fun t : ℝ => F ((b : ℂ) + t * I)))
    (hrect : RectangleIntegral' F ((a : ℂ) - I * T) ((b : ℂ) + I * T) = A)
    (hleft : ‖VIntegral F a (-T) T‖ ≤ Vl)
    (htop : ‖HIntegral F a b T‖ ≤ Hu)
    (hbottom : ‖HIntegral F a b (-T)‖ ≤ Hl)
    (htlow : ‖∫ t in Iic (-T), F ((b : ℂ) + t * I)‖ ≤ Tl)
    (htupper : ‖∫ t in Ici T, F ((b : ℂ) + t * I)‖ ≤ Tu) :
    ‖VerticalIntegral' F b - A‖ ≤ Tl + (Vl + Hu + Hl) + Tu := by
  let n : ℂ := 1 / (2 * (Real.pi : ℂ) * I)
  have hn : ‖n‖ ≤ 1 := by
    dsimp [n]
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, norm_I]
    norm_num [abs_of_pos Real.pi_pos]
    have hh := (inv_le_one₀ Real.pi_pos).2 (by linarith [Real.pi_gt_three])
    nlinarith [inv_nonneg.mpr Real.pi_pos.le]
  have hsplit := verticalIntegral_split_three (f := F) (σ := b) (-T) T hf
  have hmid : VIntegral F b (-T) T =
      VIntegral F a (-T) T + HIntegral F a b T - HIntegral F a b (-T) + (2 * π * I) * A := by
    simp only [RectangleIntegral', RectangleIntegral, smul_eq_mul,
      sub_re, add_re, sub_im, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
      I_re, I_im, zero_mul, mul_zero, add_zero, zero_add, one_mul, sub_self,
      sub_zero, zero_sub] at hrect
    have hn0 : n ≠ 0 := by dsimp [n]; exact one_div_ne_zero (by simp [Real.pi_ne_zero])
    have he : n * (2 * π * I) = 1 := by dsimp [n]; field_simp
    change n * _ = A at hrect
    apply (mul_left_cancel₀ hn0)
    linear_combination hrect - A * he
  have hid : VerticalIntegral' F b - A = n *
      (I * (∫ t in Iic (-T), F ((b : ℂ) + t * I)) +
       VIntegral F a (-T) T + HIntegral F a b T - HIntegral F a b (-T) +
       I * (∫ t in Ici T, F ((b : ℂ) + t * I))) := by
    change n * VerticalIntegral F b - A = _
    rw [hsplit, hmid]
    simp only [smul_eq_mul]
    have he : n * (2 * π * I) = 1 := by dsimp [n]; field_simp
    linear_combination A * he
  rw [hid, norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hn).trans
  have hh := norm_add_le
    (I * (∫ t in Iic (-T), F ((b : ℂ) + t * I)) + VIntegral F a (-T) T +
      HIntegral F a b T - HIntegral F a b (-T))
    (I * (∫ t in Ici T, F ((b : ℂ) + t * I)))
  have hh2 := norm_sub_le
    (I * (∫ t in Iic (-T), F ((b : ℂ) + t * I)) + VIntegral F a (-T) T + HIntegral F a b T)
    (HIntegral F a b (-T))
  have hh3 := norm_add_le
    (I * (∫ t in Iic (-T), F ((b : ℂ) + t * I)) + VIntegral F a (-T) T) (HIntegral F a b T)
  have hh4 := norm_add_le (I * (∫ t in Iic (-T), F ((b : ℂ) + t * I))) (VIntegral F a (-T) T)
  simp only [norm_mul, norm_I, one_mul] at hh hh2 hh3 hh4
  linarith only [hh, hh2, hh3, hh4, hleft, htop, hbottom, htlow, htupper]

#print axioms numerical_residue_assembly
end ChenEffective
