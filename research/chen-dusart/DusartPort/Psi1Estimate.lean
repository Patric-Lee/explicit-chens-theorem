/- Selected elementary explicit-formula adapters from LeanLab,
commit 2fdf0dc222e35d60ab0043d4597b68ebc2abe4cb, Apache 2.0.
The numerical zero-sum bound is supplied by our proved 7/8 argument. -/
import DusartPort.ZeroBridge
import DusartPort.Unsmoothing
import DusartPort.Lab.ExplicitPsi1.TrivialLimit
import NumericalZetaStrip

noncomputable section
namespace ChenEffective.Dusart
open Complex Set Filter Topology
open scoped Real
open DusartPort.Lab.ExplicitPsi1 DusartPort.Lab.ZetaZeros
open DusartPort.Lab.ExplicitPsi1.Trivial
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
local notation "ζ" => riemannZeta

theorem logDeriv_zeta_zero : deriv ζ 0 / ζ 0 = Real.log (2 * π) := by
  rw [deriv_riemannZeta_zero, riemannZeta_zero]
  rw [show (2 : ℂ) * π = ((2 * π : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log (by positivity)]
  field_simp
theorem tsum_w1_eq {y : ℝ} (hy : 0 < y) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (DusartPort.Lab.ZetaZeros.w1 (n / y) : ℂ) =
      ((ChenEffective.Dusart.psi1 y / y : ℝ) : ℂ) := by
  rw [tsum_eq_sum (s := Finset.Iic ⌊y⌋₊) ?_]
  · unfold ChenEffective.Dusart.psi1
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff hy.le).mp (Finset.mem_Iic.mp hn)
    have hw : DusartPort.Lab.ZetaZeros.w1 (n / y) = (y - n) / y := by
      unfold DusartPort.Lab.ZetaZeros.w1
      rw [max_eq_right]
      · field_simp
      · rw [sub_nonneg, div_le_one hy]; exact hny
    rw [hw]
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    push_cast
    field_simp
  · intro n hn
    have hlt : ⌊y⌋₊ < n := by
      have := Finset.mem_Iic.not.mp hn; omega
    have hyn : y < n := Nat.lt_of_floor_lt hlt
    have hw : DusartPort.Lab.ZetaZeros.w1 (n / y) = 0 := by
      unfold DusartPort.Lab.ZetaZeros.w1
      apply max_eq_left
      rw [sub_nonpos, le_div_iff₀ hy]; linarith
    rw [hw]; simp

/-- The real trivial zero term `y^{-2(n+1)}/((2n + 2)(2n + 1))`. -/
noncomputable def tb (y : ℝ) (n : ℕ) : ℝ := y ^ (-2 * ((n : ℝ) + 1)) / ((2 * n + 2) * (2 * n + 1))

lemma tterm_eq {y : ℝ} (hy : 0 < y) (n : ℕ) : tterm y n = ((tb y n : ℝ) : ℂ) := by
  unfold tterm tb
  have e : (-2 * ((n : ℂ) + 1)) = ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [e, ← Complex.ofReal_cpow hy.le]
  push_cast
  ring

lemma tb_nonneg {y : ℝ} (hy : 0 < y) (n : ℕ) : 0 ≤ tb y n := by
  unfold tb; have := Real.rpow_nonneg hy.le (-2 * ((n : ℝ) + 1)); positivity

lemma y_tb_le {y : ℝ} (hy : 1 ≤ y) (n : ℕ) : y * tb y n ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  unfold tb
  have hy0 : 0 < y := by linarith
  have hp : y * y ^ (-2 * ((n : ℝ) + 1)) ≤ 1 := by
    rw [← Real.rpow_one_add' hy0.le (by nlinarith [Nat.cast_nonneg (α := ℝ) n])]
    exact Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : ((n : ℝ) + 1) ^ 2 ≤ (2 * n + 2) * (2 * n + 1) := by nlinarith
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Real.rpow_nonneg hy0.le (-2 * ((n : ℝ) + 1))]

lemma summable_tb {y : ℝ} (hy : 1 ≤ y) : Summable (tb y) := by
  have hy0 : 0 < y := by linarith
  have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  have h2 : Summable (fun n => y * tb y n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg hy0.le (tb_nonneg hy0 n)) (y_tb_le hy) h1
  have := h2.mul_left (1 / y)
  refine this.congr (fun n => ?_)
  field_simp

/-- `0 ≤ y Σₙ tb(y, n) ≤ π²/6`. -/
lemma y_tsum_tb_bounds {y : ℝ} (hy : 1 ≤ y) : 0 ≤ y * ∑' n, tb y n ∧ y * ∑' n, tb y n ≤ π ^ 2 / 6 := by
  have hy0 : 0 < y := by linarith
  refine ⟨mul_nonneg hy0.le (tsum_nonneg (tb_nonneg hy0)), ?_⟩
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  rw [← tsum_mul_left]
  have h2 : Summable (fun n => y * tb y n) := (summable_tb hy).mul_left y
  calc ∑' n, y * tb y n ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := h2.tsum_le_tsum (y_tb_le hy) hz.summable
    _ = π ^ 2 / 6 := hz.tsum_eq

/-- The real zero sum `Z(y) = Re y Σ_ρ m(ρ) y^ρ/(ρ(ρ + 1))`. -/
noncomputable def Zreal (y : ℝ) : ℝ := ((y : ℂ) * ∑' ρ : Zall, zterm y ρ).re

/-- **The explicit formula for `ψ₁` itself**, `y > 1`:
`ψ₁(y) = y²/2 - y log 2π - Z(y) + Re (ζ'/ζ)(-1) - y Σₙ tb(y, n)`. -/
theorem psi1_formula {y : ℝ} (hy : 1 < y) :
    ChenEffective.Dusart.psi1 y =
      y ^ 2 / 2 - y * Real.log (2 * π) - Zreal y + (deriv ζ (-1) / ζ (-1)).re -
        y * ∑' n, tb y n := by
  have hy0 : 0 < y := by linarith
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  have h := explicit_formula_psi1_trivial hy
  rw [tsum_w1_eq hy0, logDeriv_zeta_zero, Complex.cpow_neg_one] at h
  have hts : ∑' n : ℕ, tterm y n = ((∑' n, tb y n : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; exact tsum_congr (tterm_eq hy0)
  rw [hts] at h
  have e : ((ChenEffective.Dusart.psi1 y : ℝ) : ℂ) =
      (y : ℂ) * ((ChenEffective.Dusart.psi1 y / y : ℝ) : ℂ) := by
    push_cast; field_simp
  have hc : ((ChenEffective.Dusart.psi1 y : ℝ) : ℂ) =
      (((y ^ 2 / 2 - y * Real.log (2 * π)) : ℝ) : ℂ) - (y : ℂ) * ∑' ρ : Zall, zterm y ρ +
        deriv ζ (-1) / ζ (-1) - ((y * ∑' n, tb y n : ℝ) : ℂ) := by
    rw [e, h]; push_cast; field_simp
  have := congr_arg Complex.re hc
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.add_re] at this
  rw [this, Zreal]

/-- `Re (ζ'/ζ)(-1) = log 2π - 1 + γ - Re ζ'/ζ(2)`. -/
lemma re_logDeriv_neg_one :
    (deriv ζ (-1) / ζ (-1)).re =
      Real.log (2 * π) - 1 + Real.eulerMascheroniConstant - (deriv ζ 2 / ζ 2).re := by
  rw [logDeriv_zeta_neg_one]
  have e : Complex.log (2 * π) = ((Real.log (2 * π) : ℝ) : ℂ) := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_log (by positivity)]
  rw [e]
  simp


theorem numerical_zero_sum {x : ℝ} (hx : 1 ≤ x) :
    ‖∑' ρ : Zall, zterm x ρ‖ ≤ (3 / 25) * x ^ (7 / 8 : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hp (ρ : Zall) : ‖zterm x ρ‖ ≤ x ^ (7 / 8 : ℝ) * hw ρ := by
    have hstrip := dusart_xi_zero_strip (dusart_zeta_zero_is_xi_zero ρ.property.1 ρ.property.2)
    have he := Real.rpow_le_rpow_of_exponent_le hx hstrip.2
    unfold zterm hw
    rw [norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_natCast]
    calc
      _ = x ^ (ρ : ℂ).re * ((analyticOrderNatAt ζ ρ : ℝ) / ‖(ρ : ℂ) * (ρ + 1)‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right he (by positivity)
  have hs := (summable_zterm hx0).norm
  have hle := hs.tsum_le_tsum hp (summable_hw.mul_left (x ^ (7 / 8 : ℝ)))
  rw [tsum_mul_left] at hle
  calc
    _ ≤ ∑' ρ : Zall, ‖zterm x ρ‖ := norm_tsum_le_tsum_norm hs
    _ ≤ _ := hle
    _ ≤ x ^ (7 / 8 : ℝ) * (3 / 25) :=
      mul_le_mul_of_nonneg_left dusart_zeta_zero_absolute_moment (by positivity)
    _ = _ := by ring

theorem numerical_Zreal {x : ℝ} (hx : 1 ≤ x) :
    |Zreal x| ≤ (3 / 25) * x ^ (15 / 8 : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hp : x * x ^ (7 / 8 : ℝ) = x ^ (15 / 8 : ℝ) := by
    nth_rw 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx0]
    norm_num
  calc
    _ ≤ ‖(x : ℂ) * ∑' ρ : Zall, zterm x ρ‖ := Complex.abs_re_le_norm _
    _ = x * ‖∑' ρ : Zall, zterm x ρ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    _ ≤ x * ((3 / 25) * x ^ (7 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left (numerical_zero_sum hx) hx0.le
    _ = _ := by nlinarith only [hp]

theorem numerical_zeta_two_bound : ‖deriv ζ 2 / ζ 2‖ ≤ (10000000 : ℝ) := by
  have hh := numerical_zeta_logDerivative_strip (2 : ℂ) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hh
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1152)
  rw [norm_div]
  linarith only [hh, hl]

theorem numerical_residue_bound : |(deriv ζ (-1) / ζ (-1)).re| ≤ (100000000 : ℝ) := by
  have hh := (Complex.abs_re_le_norm (deriv ζ 2 / ζ 2)).trans numerical_zeta_two_bound
  have hl : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  rw [re_logDeriv_neg_one]
  rcases abs_le.mp hh with ⟨hlo, hhi⟩
  apply abs_le.mpr
  constructor <;> linarith only [hlo, hhi, hl, log_two_pi_le,
    Real.eulerMascheroniConstant_lt_two_thirds, Real.one_half_lt_eulerMascheroniConstant]

theorem psi1_error_envelope {x : ℝ} (hx : 1 < x) :
    |psi1 x - x ^ 2 / 2| ≤ (3 / 25) * x ^ (15 / 8 : ℝ) + 2 * x + 1000000000 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hl : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  obtain ⟨ht0, ht1⟩ := y_tsum_tb_bounds hx.le
  have htail : x * ∑' n, tb x n ≤ 2 := by
    have hπ := Real.pi_lt_d2
    nlinarith only [ht1, hπ, Real.pi_pos]
  have htri : |psi1 x - x ^ 2 / 2| ≤ |Zreal x| + x * Real.log (2 * Real.pi) +
      |(deriv ζ (-1) / ζ (-1)).re| + x * ∑' n, tb x n := by
    rw [psi1_formula hx]
    have heq : x ^ 2 / 2 - x * Real.log (2 * Real.pi) - Zreal x +
        (deriv ζ (-1) / ζ (-1)).re - x * ∑' n, tb x n - x ^ 2 / 2 =
        ((-Zreal x) + (-(x * Real.log (2 * Real.pi))) +
          (deriv ζ (-1) / ζ (-1)).re) + (-(x * ∑' n, tb x n)) := by ring
    rw [heq]
    have h1 := abs_add_le ((-Zreal x) + (-(x * Real.log (2 * Real.pi))) +
      (deriv ζ (-1) / ζ (-1)).re) (-(x * ∑' n, tb x n))
    have h2 := abs_add_le ((-Zreal x) + (-(x * Real.log (2 * Real.pi))))
      (deriv ζ (-1) / ζ (-1)).re
    have h3 := abs_add_le (-Zreal x) (-(x * Real.log (2 * Real.pi)))
    simp only [abs_neg, abs_mul, abs_of_pos hx0, abs_of_nonneg hl,
      abs_of_nonneg ht0] at h1 h2 h3
    linarith only [h1, h2, h3]
  have hlog := mul_le_mul_of_nonneg_left log_two_pi_le hx0.le
  linarith only [htri, numerical_Zreal hx.le, numerical_residue_bound, htail, hlog]

theorem numerical_psi1 {x : ℝ} (hx : (3 : ℝ) ^ (100 : ℕ) ≤ x) :
    |psi1 x - x ^ 2 / 2| ≤ (121 / 1000) * x ^ (15 / 8 : ℝ) := by
  have hx1 : 1 < x := (by norm_num : (1 : ℝ) < 3 ^ (100 : ℕ)).trans_le hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hp : (1000000002000 : ℝ) ≤ x ^ (7 / 8 : ℝ) := by
    have hc : ((3 : ℝ) ^ (100 : ℕ)) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ (50 : ℕ) := by
      rw [← Real.rpow_natCast (3 : ℝ) 100, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc
      _ ≤ (3 : ℝ) ^ (50 : ℕ) := by norm_num
      _ = _ := hc.symm
      _ ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hx (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
  have hm : x * x ^ (7 / 8 : ℝ) = x ^ (15 / 8 : ℝ) := by
    nth_rw 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx0]
    norm_num
  have hh := mul_le_mul_of_nonneg_left hp hx0.le
  rw [hm] at hh
  have he := psi1_error_envelope hx1
  nlinarith only [hh, he, hx1]

theorem numerical_theta_target {x : ℝ} (hx : (3 : ℝ) ^ (120 : ℕ) ≤ x) :
    |Chebyshev.theta x - x| ≤ (3 / 4) * x ^ (15 / 16 : ℝ) := by
  exact theta_of_numerical_psi hx (numerical_unsmoothing hx (fun y hy => numerical_psi1 hy))

#print axioms numerical_zero_sum
#print axioms numerical_psi1
#print axioms numerical_theta_target
end ChenEffective.Dusart
