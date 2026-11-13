import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

noncomputable section
namespace ChenEffective.HybridProduct
open Real
set_option maxHeartbeats 2000000

theorem prime_power_gap_seventeen (x : ℝ) :
    Chebyshev.psi x-Chebyshev.theta x ≤ 17*sqrt x := by
  have hlog : log (4:ℝ) ≤ 5/3 := by
    rw [show (4:ℝ)=2^2 by norm_num,log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [log_two_lt_d9]
  by_cases hx : x ≤ 1
  · rw [Chebyshev.theta_eq_zero_of_le_one hx,Chebyshev.psi_eq_zero_of_le_one hx]
    simp only [sub_self]
    positivity
  have hx1 : 1 ≤ x := (lt_of_not_ge hx).le
  have hp (n : ℕ) (hn : 2 ≤ n) :
      Chebyshev.psi (x^(1/(n:ℝ))) ≤ (log 4+4)*sqrt x := by
    grw [Chebyshev.psi_le_const_mul_self (rpow_nonneg (by linarith only [hx1]) _),
      sqrt_eq_rpow]
    gcongr
    norm_cast
  have hh := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := hp 2 le_rfl
  have h3 := hp 3 (by norm_num)
  have h5 := hp 5 (by norm_num)
  norm_num only [one_div] at h2 h3 h5
  nlinarith only [hh,h2,h3,h5,mul_le_mul_of_nonneg_right hlog (sqrt_nonneg x)]

/-- The coefficient in an integrated psi1-error bound. It is deliberately
separate from the unproved analytic integration-by-parts application. -/
def integratedCoefficient (L r : ℝ) : ℝ :=
  1/L+1/L^2+(2/L+3/L^2+2/L^3)/(2-r)

theorem integrated_low_coefficient (L : ℝ) :
    integratedCoefficient L (3/2)=5/L+7/L^2+4/L^3 := by
  unfold integratedCoefficient
  ring

theorem integrated_high_coefficient (L : ℝ) :
    integratedCoefficient L (15/8)=17/L+25/L^2+16/L^3 := by
  unfold integratedCoefficient
  ring

theorem relaxed_product_payment :
    (2/17000:ℝ)+24/3999999 ≤ 1/8000 := by norm_num

theorem exp_le_reciprocal {t : ℝ} (ht : t < 1) : exp t ≤ 1/(1-t) := by
  have hh := mul_le_mul_of_nonneg_right (add_one_le_exp (-t)) (exp_pos t).le
  have he : exp (-t)*exp t=1 := by rw [← exp_add]; simp
  rw [he] at hh
  apply (le_div_iff₀ (sub_pos.mpr ht)).mpr
  nlinarith only [hh]

/-- An absolute prefix error 1/9000 is sufficient when the exponential
conversion preserves its first-order constant. -/
theorem hybrid_product_payment :
    exp ((2/9000:ℝ)+24/3999999) ≤ 1+1/4000 := by
  exact (exp_le_reciprocal (by norm_num)).trans (by norm_num)

theorem smoothing_scalar {v : ℝ} (hv : 0 < v) :
    ((101/50:ℝ)*v)/2+(20201/10000)*v^2/((101/50)*v) ≤ (101/50)*v := by
  field_simp
  nlinarith only [hv]

#print axioms prime_power_gap_seventeen
end ChenEffective.HybridProduct

