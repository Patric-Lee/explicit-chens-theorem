import BJSStudyElementaryMertens
import NumericalSelbergDivisorProduct

noncomputable section
namespace ChenEffective
open Real AnalyticNumberTheory.Mertens
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 512

private opaque bjsStudyMertensCertificate : {n : ℕ // n=3^30} := ⟨3^30,rfl⟩
def bjsStudyMertensEndpoint : ℕ := bjsStudyMertensCertificate.1
theorem bjsStudyMertensEndpoint_eq : bjsStudyMertensEndpoint=3^30 :=
  bjsStudyMertensCertificate.2

private theorem bjsStudy_power_mono (a b : ℕ) (h : a ≤ b) : (3 : ℕ)^a ≤ 3^b :=
  Nat.pow_le_pow_right (by norm_num) h

/-- A one-sided Mertens product bound from the proved elementary 10/log error.
Only the lower product is needed for the divisor normalization. -/
theorem bjsStudy_mertens_product {n : ℕ} (hn : bjsStudyMertensEndpoint ≤ n) :
    (1/2:ℝ) ≤ primeProduct n*log (n : ℝ)*exp eulerMascheroniConstant := by
  have hn' := hn
  rw [bjsStudyMertensEndpoint_eq] at hn'
  have hn2 : 3^2 ≤ n := (bjsStudy_power_mono 2 30 (by norm_num)).trans hn'
  have hn9 : 9 ≤ n := (by norm_num : 9 ≤ (3 : ℕ)^2).trans hn2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hm := bjsStudy_reciprocal_elementary (by omega : 2 ≤ n)
  have hlog := log_ge_power_three hn'
  have hml : |primeReciprocalSum n-(log (log (n:ℝ))+mertensSecondConstant)| ≤ 1/3 := by
    apply hm.trans
    apply (div_le_iff₀ hl).mpr
    norm_num only [Nat.cast_ofNat] at hlog
    linarith only [hlog]
  have hc := logarithmicCorrection_tail_norm_le_div n (show 1 ≤ n by omega)
  rw [Real.norm_eq_abs] at hc
  have hcorr : 2/(n:ℝ) ≤ 2/(3:ℝ)^30 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by exact_mod_cast hn')
  let E := log (primeProduct n)+log (log (n : ℝ))+eulerMascheroniConstant
  have hE : |E| ≤ 1/2 := by
    dsimp only [E]
    rw [← mertensConstant_eq_eulerMascheroni, log_primeProduct_error_eq]
    have hh := abs_add_le (-(primeReciprocalSum n-(log (log (n : ℝ))+mertensSecondConstant)))
      (logarithmicCorrectionLimit-logarithmicCorrection n)
    rw [abs_neg] at hh
    norm_num only [Nat.reducePow] at hcorr
    nlinarith only [hh,hml,hc,hcorr]
  have he := Real.add_one_le_exp E
  have hid : exp E=primeProduct n*log (n : ℝ)*exp eulerMascheroniConstant := by
    dsimp only [E]
    rw [exp_add,exp_add,exp_log (primeProduct_pos n),exp_log hl]
  rw [hid] at he
  linarith only [he,(abs_le.mp hE).1]

theorem bjsStudy_mertens_inverse {n : ℕ} (hn : bjsStudyMertensEndpoint ≤ n) :
    (MathlibNt.SieveTheory.MertensTheorem.primeProduct n)⁻¹ ≤ 6*log (n : ℝ) := by
  have hh := bjsStudy_mertens_product hn
  have hn' := hn
  rw [bjsStudyMertensEndpoint_eq] at hn'
  have hn9 : 9 ≤ n := (show 9 ≤ (3 : ℕ)^2 by norm_num).trans
    ((bjsStudy_power_mono 2 30 (by norm_num)).trans hn')
  have hl : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hP := primeProduct_pos n
  have hlo := hh
  have hi : (primeProduct n)⁻¹ ≤ 2*exp eulerMascheroniConstant*log (n : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hP).mpr
    nlinarith only [hlo]
  have he : exp eulerMascheroniConstant ≤ 3 :=
    (exp_le_exp.mpr (by linarith only [eulerMascheroniConstant_lt_two_thirds] :
      eulerMascheroniConstant ≤ 1)).trans (by linarith only [exp_one_lt_d9])
  rw [MathlibNt.SieveTheory.MertensTheorem.primeProduct_eq_analyticNumberTheory]
  exact hi.trans (by nlinarith only [mul_le_mul_of_nonneg_right he hl.le])

#print axioms bjsStudy_mertens_product
#print axioms bjsStudy_mertens_inverse
end ChenEffective
