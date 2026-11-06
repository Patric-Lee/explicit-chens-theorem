import BJSStudyInputs
import BJSProvedProductProfile

/-! The active sieve uses the proved power-saving Euler product at 3^2652.
No sharp small-endpoint reciprocal-prime interval estimate is assumed.
-/
noncomputable section
namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem bjsStudy_interval_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p) (u z : ℝ)
    (hu : bjsStudyPresieveStart ≤ u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹) ≤ (1+(1/4000 : ℝ))*(log z/log u) := by
  have hh := budget_interval_product bjsStudyProductProfile s hs u z hu huz hinterval
  have hu10 : 10 ≤ u := bjsStudyProductProfile.cutoff_ten.trans hu
  have hr : 0 ≤ log z/log u := div_nonneg
    (log_nonneg (by linarith only [hu10,huz])) (log_nonneg (by linarith only [hu10]))
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith only [bjsStudy_product_error_cap]) hr)

theorem bjsStudy_presieved_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p)
    (hpresieve : ∀ p ∈ s, bjsStudyPresieveStart ≤ (p : ℝ))
    (u z : ℝ) (hu : 1 < u) (huz : u ≤ z)
    (hinterval : ∀ p ∈ s, u ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    (∏ p ∈ s, (1-1/((p : ℝ)-1))⁻¹) ≤ (1+(1/4000 : ℝ))*(log z/log u) := by
  have hh := budget_presieved_product bjsStudyProductProfile s hs hpresieve u z hu huz hinterval
  have hr : 0 ≤ log z/log u := div_nonneg (log_nonneg (hu.trans_le huz).le) (log_pos hu).le
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith only [bjsStudy_product_error_cap]) hr)

theorem bjsStudy_product_relative (S : BoundingSieve)
    (hodd : ∀ p ∈ S.prodPrimes.primeFactors, 2 < p)
    (hnu : ∀ p ∈ S.prodPrimes.primeFactors, S.nu p=1/((p : ℝ)-1)) :
    HasRelativeSieveProduct (preSieveCounting S bjsStudyPresieveStart) (1/4000 : ℝ) := by
  have hp := product_profile_relative bjsStudyProductProfile S hodd hnu
  intro u z hu huz
  have hh := hp u z hu huz
  have hr : 0 ≤ log z/log u := div_nonneg (log_nonneg (hu.trans_le huz).le) (log_pos hu).le
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith only [bjsStudy_product_error_cap]) hr)

#print axioms bjsStudy_product_relative
end ChenEffective
