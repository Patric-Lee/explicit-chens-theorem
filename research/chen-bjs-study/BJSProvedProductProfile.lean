import ChenBudgetProducts

/-! Retained coarse power-saving product profile.
The active smaller-cutoff sieve instead uses the proved Dusart interval
theorem. This independent profile remains available for comparison.
-/
noncomputable section
namespace ChenEffective
open Real
set_option maxHeartbeats 2000000

noncomputable def bjsPowerPresieveStart : ℝ := (3 : ℝ)^(2652 : ℕ)

def bjsPowerProductProfile : PrimeProductProfile where
  cutoff := bjsPowerPresieveStart
  error := 1/10000
  cutoff_ten := by
    unfold bjsPowerPresieveStart
    exact (show (10 : ℝ) ≤ 3^(3 : ℕ) by norm_num).trans
      (pow_le_pow_right₀ (by norm_num) (by norm_num : 3 ≤ 2652))
  error_nonneg := by norm_num
  error_cap := le_rfl
  power_error := by
    unfold bjsPowerPresieveStart
    rw [← rpow_natCast (3 : ℝ) 2652,← rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num [rpow_neg]

theorem bjsPower_product_error_cap : bjsPowerProductProfile.error ≤ (1/4000 : ℝ) := by
  norm_num [bjsPowerProductProfile]

#print axioms bjsPowerProductProfile
end ChenEffective
