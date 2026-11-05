import OptimizedMertensPower
import NumericalSelbergDivisorProduct

noncomputable section
namespace ChenEffective
open Real AnalyticNumberTheory.Mertens
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 512

private opaque qualitativeMertensCertificate : {n : ℕ // n=3^2176} := ⟨3^2176,rfl⟩
def qualitativeMertensEndpoint : ℕ := qualitativeMertensCertificate.1
theorem qualitativeMertensEndpoint_eq : qualitativeMertensEndpoint=3^2176 :=
  qualitativeMertensCertificate.2

private theorem qualitative_power_mono (a b : ℕ) (h : a ≤ b) : (3 : ℕ)^a ≤ 3^b :=
  Nat.pow_le_pow_right (by norm_num) h

/-- A coarse absolute Mertens product bound obtained directly from the power
saving. Its endpoint will be applied at log N, rather than N. -/
theorem qualitative_mertens_product {n : ℕ} (hn : qualitativeMertensEndpoint ≤ n) :
    |primeProduct n*log (n : ℝ)*exp eulerMascheroniConstant-1| ≤ 1/2 := by
  have hn' := hn
  rw [qualitativeMertensEndpoint_eq] at hn'
  have hn32 : 3^32 ≤ n := (qualitative_power_mono 32 2176 (by norm_num)).trans hn'
  have hn9 : 9 ≤ n := (by norm_num : 9 ≤ (3 : ℕ)^32).trans hn32
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hm := optimized_mertens_power (show (9 : ℝ) ≤ n by exact_mod_cast hn9)
  rw [Nat.floor_natCast] at hm
  have hc := logarithmicCorrection_tail_norm_le_div n (show 1 ≤ n by omega)
  rw [Real.norm_eq_abs] at hc
  have hnR : (3 : ℝ)^(2176 : ℕ) ≤ n := by exact_mod_cast hn'
  have hp : (n : ℝ)^(-1/68 : ℝ) ≤ ((3 : ℝ)^32)⁻¹ := by
    have hh := rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (3 : ℝ)^(2176 : ℕ)) hnR
      (by norm_num : (-1/68 : ℝ) ≤ 0)
    rw [← rpow_natCast, ← rpow_mul (by norm_num : (0 : ℝ) ≤ 3)] at hh
    norm_num [rpow_neg] at hh
    rw [neg_div, rpow_neg (Nat.cast_nonneg n)]
    norm_num only [Nat.reducePow]
    simpa only [one_div] using hh
  have hcorr : 2/(n : ℝ) ≤ 2/(3 : ℝ)^32 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by exact_mod_cast hn32)
  let E := log (primeProduct n)+log (log (n : ℝ))+eulerMascheroniConstant
  have hE : |E| ≤ 1/4 := by
    dsimp only [E]
    rw [← mertensConstant_eq_eulerMascheroni, log_primeProduct_error_eq]
    have hh := abs_add_le (-(primeReciprocalSum n-(log (log (n : ℝ))+mertensSecondConstant)))
      (logarithmicCorrectionLimit-logarithmicCorrection n)
    rw [abs_neg] at hh
    have hm' := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 30000000000000)
    norm_num only [Nat.reducePow] at hm' hcorr
    nlinarith only [hh,hm,hc,hm',hcorr]
  have he := (Real.abs_exp_sub_one_le (hE.trans (by norm_num : (1/4 : ℝ) ≤ 1))).trans
    (mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 2))
  have hid : exp E=primeProduct n*log (n : ℝ)*exp eulerMascheroniConstant := by
    dsimp only [E]
    rw [exp_add,exp_add,exp_log (primeProduct_pos n),exp_log hl]
  rw [hid] at he
  exact he.trans (by norm_num)

theorem qualitative_mertens_inverse {n : ℕ} (hn : qualitativeMertensEndpoint ≤ n) :
    (MathlibNt.SieveTheory.MertensTheorem.primeProduct n)⁻¹ ≤ 6*log (n : ℝ) := by
  have hh := qualitative_mertens_product hn
  have hn' := hn
  rw [qualitativeMertensEndpoint_eq] at hn'
  have hn9 : 9 ≤ n := (show 9 ≤ (3 : ℕ)^2 by norm_num).trans
    ((qualitative_power_mono 2 2176 (by norm_num)).trans hn')
  have hl : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hP := primeProduct_pos n
  have hlo := (abs_le.mp hh).1
  have hi : (primeProduct n)⁻¹ ≤ 2*exp eulerMascheroniConstant*log (n : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hP).mpr
    nlinarith only [hlo]
  have he : exp eulerMascheroniConstant ≤ 3 :=
    (exp_le_exp.mpr (by linarith only [eulerMascheroniConstant_lt_two_thirds] :
      eulerMascheroniConstant ≤ 1)).trans (by linarith only [exp_one_lt_d9])
  rw [MathlibNt.SieveTheory.MertensTheorem.primeProduct_eq_analyticNumberTheory]
  exact hi.trans (by nlinarith only [mul_le_mul_of_nonneg_right he hl.le])

#print axioms qualitative_mertens_product
#print axioms qualitative_mertens_inverse
end ChenEffective
