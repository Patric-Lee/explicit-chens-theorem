import ChenBudgetProducts

/-! The proved product profile used by the active BJS sieve.
The larger starting point pays the existing power error without a new
reciprocal-prime or theta hypothesis. All arithmetic is kernel checked.
-/
noncomputable section
namespace ChenEffective
open Real
set_option maxHeartbeats 2000000

noncomputable def bjsStudyPresieveStart : ℝ := (3 : ℝ)^(2652 : ℕ)

def bjsStudyProductProfile : PrimeProductProfile where
  cutoff := bjsStudyPresieveStart
  error := 1/10000
  cutoff_ten := by
    unfold bjsStudyPresieveStart
    exact (show (10 : ℝ) ≤ 3^(3 : ℕ) by norm_num).trans
      (pow_le_pow_right₀ (by norm_num) (by norm_num : 3 ≤ 2652))
  error_nonneg := by norm_num
  error_cap := le_rfl
  power_error := by
    unfold bjsStudyPresieveStart
    rw [← rpow_natCast (3 : ℝ) 2652,← rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num [rpow_neg]

theorem bjsStudy_product_error_cap : bjsStudyProductProfile.error ≤ (1/4000 : ℝ) := by
  norm_num [bjsStudyProductProfile]

#print axioms bjsStudyProductProfile
end ChenEffective
