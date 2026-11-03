import NumericalSelbergDivisorGeometry

noncomputable section
namespace ChenEffective
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open LiuWeight
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
attribute [local irreducible] mertensProductThreshold logPowerCutoff

/-- Keep the enormous integer symbolic during kernel checking. The equality
certificate fixes it to the displayed numerical formula; no choice is used. -/
private opaque selbergMertensEndpointCertificate : {n : ℕ // n=mertensProductThreshold 2} :=
  ⟨mertensProductThreshold 2,rfl⟩
def selbergMertensEndpoint : ℕ := selbergMertensEndpointCertificate.1
theorem selbergMertensEndpoint_eq : selbergMertensEndpoint=mertensProductThreshold 2 :=
  selbergMertensEndpointCertificate.2

@[irreducible] def selbergDivisorThreshold : ℕ :=
  3^(max selbergMertensEndpoint (logPowerCutoff 6))

theorem numerical_selberg_divisor_logs_aux (M : ℕ) {N : ℕ} (hN : 3^(max M (logPowerCutoff 6)) ≤ N) :
    (M : ℝ) ≤ Real.log (N : ℝ) ∧
    (logPowerCutoff 6 : ℝ) ≤ Real.log (N : ℝ) ∧ 2 ≤ Real.log (N : ℝ) := by
  have hn := hN
  have hh := log_ge_power_three hn
  have h1a : (M : ℝ) ≤ (max M (logPowerCutoff 6) : ℕ) := by
    exact_mod_cast le_max_left M (logPowerCutoff 6)
  have h2a : (logPowerCutoff 6 : ℝ) ≤ (max M (logPowerCutoff 6) : ℕ) := by
    exact_mod_cast le_max_right M (logPowerCutoff 6)
  have h1 := h1a.trans hh
  have h2 := h2a.trans hh
  have h9 : (9 : ℝ) ≤ logPowerCutoff 6 := by exact_mod_cast logPowerCutoff_nine_le 6
  exact ⟨h1,h2,by linarith only [h2,h9]⟩

theorem numerical_selberg_divisor_logs {N : ℕ} (hN : selbergDivisorThreshold ≤ N) :
    (selbergMertensEndpoint : ℝ) ≤ Real.log (N : ℝ) ∧
    (logPowerCutoff 6 : ℝ) ≤ Real.log (N : ℝ) ∧ 2 ≤ Real.log (N : ℝ) := by
  unfold selbergDivisorThreshold at hN
  exact numerical_selberg_divisor_logs_aux selbergMertensEndpoint hN

theorem numerical_selberg_mertens_inverse {y : ℕ} (hy : mertensProductThreshold 2 ≤ y) :
    (MertensTheorem.primeProduct y)⁻¹ ≤ 6*Real.log (y : ℝ) := by
  have hh := numerical_mertens_product (by norm_num : 0 < (2 : ℕ)) hy
  unfold mertensProductThreshold at hy
  have hyP := (le_max_left _ _).trans hy
  have hy9 := (logPowerCutoff_nine_le _).trans hyP
  have hl0 : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hP := AnalyticNumberTheory.Mertens.primeProduct_pos y
  have hlo := (abs_le.mp hh).1
  have hi : (AnalyticNumberTheory.Mertens.primeProduct y)⁻¹ ≤
      2*Real.exp Real.eulerMascheroniConstant*Real.log (y : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hP).mpr
    norm_num only [Nat.cast_ofNat] at hlo
    nlinarith only [hlo]
  have he : Real.exp Real.eulerMascheroniConstant ≤ 3 := by
    have he1 : Real.exp Real.eulerMascheroniConstant ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by linarith only [Real.eulerMascheroniConstant_lt_two_thirds])
    exact he1.trans (by linarith only [Real.exp_one_lt_d9])
  rw [MertensTheorem.primeProduct_eq_analyticNumberTheory]
  exact hi.trans (by nlinarith only [mul_le_mul_of_nonneg_right he hl0.le])

theorem numerical_selberg_divisor_product {N : ℕ} (hN : selbergDivisorThreshold ≤ N) :
    liuPrimeDivisorProduct N ≤ 54*(1+Real.log (Real.log (N : ℝ))) := by
  obtain ⟨hM, _, hl⟩ := numerical_selberg_divisor_logs hN
  have hNpos : 0 < N := by
    by_contra hh
    have he : N=0 := by omega
    subst N
    norm_num at hl
  let y := liuPrimeDivisorCutoff N
  have hNy : Real.log (N : ℝ) ≤ (y : ℝ) := Nat.le_ceil _
  have hy2 : 2 ≤ y := by exact_mod_cast hl.trans hNy
  have hyM' : selbergMertensEndpoint ≤ y := by exact_mod_cast hM.trans hNy
  have hyM : mertensProductThreshold 2 ≤ y := by simpa only [selbergMertensEndpoint_eq] using hyM'
  have hsmall := (small_prime_divisor_product_le (N := N) (y := y)).trans
    (numerical_selberg_mertens_inverse hyM)
  have hlarge := large_prime_divisor_product_le hNpos hy2 hNy
  have hlog2 : (Real.log (2 : ℝ))⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀' (Real.log_pos (by norm_num))]
    linarith only [Real.log_two_gt_d9]
  have he2 : Real.exp (2 : ℝ) ≤ 9 := by
    rw [show (2 : ℝ)=1+1 by norm_num, Real.exp_add]
    nlinarith only [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
  have hlarge9 := hlarge.trans ((Real.exp_le_exp.mpr hlog2).trans he2)
  have hsplit : liuPrimeDivisorProduct N =
      (N.primeFactors.filter (· ≤ y)).prod (fun p => 1+((p : ℝ)⁻¹))*
      (N.primeFactors.filter (y < ·)).prod (fun p => 1+((p : ℝ)⁻¹)) := by
    rw [liuPrimeDivisorProduct, ← prod_filter_mul_prod_filter_not N.primeFactors (· ≤ y)]
    simp only [not_le]
  rw [hsplit]
  have hly := log_liuPrimeDivisorCutoff_le hl
  calc
    _ ≤ (6*Real.log (y : ℝ))*9 := mul_le_mul hsmall hlarge9 (by positivity)
      (by have hyy : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
          exact mul_nonneg (by norm_num) (Real.log_nonneg hyy))
    _ ≤ _ := by dsimp [y] at *; linarith only [hly]

#print axioms numerical_selberg_divisor_product
end ChenEffective
