import TernaryGoldbach.Explicit.PsiRanges1e8
import TernaryGoldbach.Explicit.PsiPlateau1e8
import BJSHybridSharpPrimePowers

/-! Conversion of the modulus-one finite-RH psi estimates to the actual
Mathlib theta function. The finite-RH statement is an explicit hypothesis. -/
noncomputable section
namespace ChenEffective.PlattWindow
open Real TernaryGoldbach.Explicit

theorem psiR_eq_chebyshev (x : ℝ) : psiR x = Chebyshev.psi x := by
  unfold psiR TernaryGoldbach.Helfgott.psi
  rw [Chebyshev.psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]

theorem theta_error_of_psi {x F : ℝ} (hx : (3:ℝ)^16 ≤ x)
    (hpsi : |Chebyshev.psi x-x| ≤ F) :
    |Chebyshev.theta x-x| ≤ F+2*sqrt x := by
  have hgap := HybridProduct.prime_power_gap_two hx
  have hnonneg := Chebyshev.theta_le_psi x
  rw [abs_le] at hpsi ⊢
  constructor <;> linarith [sqrt_nonneg x]

theorem cW8_le_4508 {x : ℝ} (hx : x ≤ (10:ℝ)^13) :
    cW8 x ≤ (1127/25:ℝ) := by
  unfold cW8
  by_cases h0 : x ≤ (3200000:ℝ)
  · rw [ite_eq_left h0] <;> norm_num
  rw [ite_eq_right h0]
  by_cases h1 : x ≤ (10000000:ℝ)
  · rw [ite_eq_left h1] <;> norm_num
  rw [ite_eq_right h1]
  by_cases h2 : x ≤ (32000000:ℝ)
  · rw [ite_eq_left h2] <;> norm_num
  rw [ite_eq_right h2]
  by_cases h3 : x ≤ (100000000:ℝ)
  · rw [ite_eq_left h3] <;> norm_num
  rw [ite_eq_right h3]
  by_cases h4 : x ≤ (320000000:ℝ)
  · rw [ite_eq_left h4] <;> norm_num
  rw [ite_eq_right h4]
  by_cases h5 : x ≤ (1000000000:ℝ)
  · rw [ite_eq_left h5] <;> norm_num
  rw [ite_eq_right h5]
  by_cases h6 : x ≤ (3200000000:ℝ)
  · rw [ite_eq_left h6] <;> norm_num
  rw [ite_eq_right h6]
  by_cases h7 : x ≤ (10000000000:ℝ)
  · rw [ite_eq_left h7] <;> norm_num
  rw [ite_eq_right h7]
  by_cases h8 : x ≤ (32000000000:ℝ)
  · rw [ite_eq_left h8] <;> norm_num
  rw [ite_eq_right h8]
  by_cases h9 : x ≤ (100000000000:ℝ)
  · rw [ite_eq_left h9] <;> norm_num
  rw [ite_eq_right h9]
  by_cases h10 : x ≤ (320000000000:ℝ)
  · rw [ite_eq_left h10] <;> norm_num
  rw [ite_eq_right h10]
  by_cases h11 : x ≤ (1000000000000:ℝ)
  · rw [ite_eq_left h11] <;> norm_num
  rw [ite_eq_right h11]
  by_cases h12 : x ≤ (3200000000000:ℝ)
  · rw [ite_eq_left h12] <;> norm_num
  rw [ite_eq_right h12]
  by_cases h13 : x ≤ (10000000000000:ℝ)
  · rw [ite_eq_left h13] <;> norm_num
  rw [ite_eq_right h13]
  exfalso
  norm_num at hx
  linarith only [hx,h13]


variable [Fact TernaryGoldbach.PlattZetaRH]

theorem theta_mid {x : ℝ} (hx : (3:ℝ)^16 ≤ x)
    (hhi : x ≤ (10:ℝ)^17) :
    |Chebyshev.theta x-x| ≤ (cW8 x+2)*sqrt x := by
  have hlo : (1e6:ℝ) ≤ x := (by norm_num : (1e6:ℝ) ≤ 3^16).trans hx
  have h := psi_mid8 hlo (by norm_num at hhi ⊢; exact hhi)
  rw [psiR_eq_chebyshev] at h
  have hb := theta_error_of_psi hx h
  nlinarith only [hb]

theorem theta_first {x : ℝ} (hx : (10:ℝ)^10 ≤ x)
    (hhi : x ≤ (3:ℝ)^22) :
    |Chebyshev.theta x-x| ≤ (75/2:ℝ)*sqrt x := by
  have hpos : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hlo : (3:ℝ)^16 ≤ x := (by norm_num : (3:ℝ)^16 ≤ 10^10).trans hx
  have h := theta_mid hlo (hhi.trans (by norm_num))
  have hc := cW8_le_355 hpos (hhi.trans (by norm_num))
  have hm := mul_le_mul_of_nonneg_right hc (sqrt_nonneg x)
  nlinarith only [h,hm]

theorem theta_second {x : ℝ} (hx : (3:ℝ)^22 ≤ x)
    (hhi : x ≤ (10:ℝ)^13) :
    |Chebyshev.theta x-x| ≤ (1177/25:ℝ)*sqrt x := by
  have hlo : (3:ℝ)^16 ≤ x := (by norm_num : (3:ℝ)^16 ≤ 3^22).trans hx
  have h := theta_mid hlo (hhi.trans (by norm_num))
  have hc := cW8_le_4508 hhi
  have hm := mul_le_mul_of_nonneg_right hc (sqrt_nonneg x)
  nlinarith only [h,hm]

theorem theta_third {x : ℝ} (hx : (10:ℝ)^13 ≤ x)
    (hhi : x ≤ (10:ℝ)^15) :
    |Chebyshev.theta x-x| ≤ 74*sqrt x := by
  have hlo : (3:ℝ)^16 ≤ x := (by norm_num : (3:ℝ)^16 ≤ 10^13).trans hx
  have h := theta_mid hlo (hhi.trans (by norm_num))
  have hc := cW8_le_72 (by norm_num at hhi ⊢; exact hhi)
  have hm := mul_le_mul_of_nonneg_right hc (sqrt_nonneg x)
  nlinarith only [h,hm]

theorem theta_fourth {x : ℝ} (hx : (10:ℝ)^15 ≤ x)
    (hhi : x ≤ (10:ℝ)^17) :
    |Chebyshev.theta x-x| ≤ 202*sqrt x := by
  have hlo : (3:ℝ)^16 ≤ x := (by norm_num : (3:ℝ)^16 ≤ 10^15).trans hx
  have h := theta_mid hlo hhi
  have hc := cW8_le_200 x
  have hm := mul_le_mul_of_nonneg_right hc (sqrt_nonneg x)
  nlinarith only [h,hm]

theorem theta_plateau {x : ℝ} (hx : (10:ℝ)^17 ≤ x) :
    |Chebyshev.theta x-x| ≤
      (1/2000000:ℝ)*x+1147*sqrt x+42*10^9 := by
  have hlo : (3:ℝ)^16 ≤ x := (by norm_num : (3:ℝ)^16 ≤ 10^17).trans hx
  have h := psi_plateau8 (by norm_num at hx ⊢; exact hx)
  rw [psiR_eq_chebyshev] at h
  have hb := theta_error_of_psi hlo h
  have hx0 : 0 ≤ x := (by positivity : (0:ℝ) ≤ 10^17).trans hx
  nlinarith only [hb,hx0]

#print axioms theta_first
#print axioms theta_plateau
end ChenEffective.PlattWindow
