import ChenBudget

/-! A scalar feasibility test, NOT a Chen theorem at H=36.
The stronger small-endpoint product profile, distribution estimates and triple
estimate at this cutoff remain separate proof obligations. No provisional
axiom is used by the certificates in this file.
-/
noncomputable section
namespace ChenEffective
open Real
set_option maxHeartbeats 2000000

theorem bjsStudy_exp36_lower : (21*10^14:ℝ) ≤ exp 36 := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1) 4
  norm_num [Finset.sum_range_succ] at he
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/3) he 36
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat,mul_one] at hp
  norm_num at hp ⊢
  linarith only [hp]

theorem bjsStudy_h36_geometry {L q : ℝ} (hL : exp 36 ≤ L)
    (hq : log (2*q) ≤ 1+2*(10:ℝ)^9) :
    10*log (2*q)/L ≤ (1/100000:ℝ) := by
  have hlarge := bjsStudy_exp36_lower.trans hL
  apply (div_le_iff₀ (by linarith only [hlarge] : 0 < L)).mpr
  norm_num only [Nat.reducePow] at hq hlarge ⊢
  nlinarith only [hq,hlarge]

def bjsStudyH36Budget : ChenBudget := ⟨3/50,113/100,1/20000,3.94033,1/100⟩

theorem bjsStudy_h36_margin : bjsStudyH36Budget.margin=0.040585 := by
  norm_num [bjsStudyH36Budget,ChenBudget.margin,ChenBudget.weighted]

/-- Room for lower density shift 3*delta, kernel 110*epsilon/16,
and the original fixed-power level loss 1/(2*baseCandidateBudget). -/
theorem bjsStudy_h36_lower_density_payment :
    3*(1/100000:ℝ)+110*(1/2000:ℝ)/16+1/(2*20000000:ℝ) ≤ 1/250 := by
  norm_num

theorem bjsStudy_h36_upper_density_payment :
    18*(1/100000:ℝ)+110*(1/2000:ℝ) ≤ 7/125 := by
  norm_num

/-- Conservative base mass/remainder payment, for A<=6 and B<=25/2. -/
theorem bjsStudy_h36_base_payment {A B : ℝ} (hA : A ≤ 6) (hB : B ≤ 25/2) :
    A*B-3/50 ≤ (A-1/250)*(B-40*(1/20000000:ℝ))-1/20000000 := by
  nlinarith only [hA,hB]

#print axioms bjsStudy_h36_geometry
#print axioms bjsStudy_h36_margin
end ChenEffective
