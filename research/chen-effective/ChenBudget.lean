import SharperSieveAssembly
import NumericalLowerEndpoint

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple SingularSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem budget_mertens_factor_cap : jurkatRichertMertensFactor ≤ 25/2 := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) 3
  norm_num [Finset.sum_range_succ] at he
  have hg := Real.one_half_lt_eulerMascheroniConstant
  have hExp : 8/5 ≤ exp eulerMascheroniConstant :=
    (show (8/5 : ℝ) ≤ exp (1/2) by linarith only [he]).trans (exp_le_exp.mpr hg.le)
  have hprod : exp (-eulerMascheroniConstant)*exp eulerMascheroniConstant=1 := by
    rw [← exp_add,neg_add_cancel,exp_zero]
  have hh := mul_le_mul_of_nonneg_left hExp (exp_pos (-eulerMascheroniConstant)).le
  unfold jurkatRichertMertensFactor
  nlinarith only [hh,hprod]

/-- The allocations are independent parameters. Their feasibility is checked
against actual counting estimates, rather than a fixed target coefficient. -/
structure ChenBudget where
  baseLoss : ℝ
  mediumLoss : ℝ
  endpointLoss : ℝ
  tripleMain : ℝ
  tripleRemainder : ℝ

def ChenBudget.weighted (b : ChenBudget) : ℝ :=
  2.6408-b.baseLoss-b.mediumLoss/2-b.endpointLoss

def ChenBudget.margin (b : ChenBudget) : ℝ :=
  b.weighted-b.tripleMain/2-b.tripleRemainder/2

theorem chen_budget_weighted (b : ChenBudget) {N : ℕ}
    (hbase : (jurkatRichertBaseMainCoefficient jurkatRichertJ-b.baseLoss)*
      (liuSingularSeries N*N/log (N : ℝ)^2) ≤ ((jurkatRichertSourceCandidates N).card : ℝ))
    (hmedium : jurkatRichertSourceMediumPrimeAggregate N ≤
      (jurkatRichertQ1MainCoefficient jurkatRichertK+b.mediumLoss)*(liuSingularSeries N*N/log (N : ℝ)^2))
    (hboundary : jurkatRichertSourceWeightedCount N ≤ jurkatRichertWeightedCount N+
      b.endpointLoss*(liuSingularSeries N*N/log (N : ℝ)^2)) :
    b.weighted*(liuSingularSeries N*N/log (N : ℝ)^2) ≤ jurkatRichertWeightedCount N := by
  have hMain := jurkatRichert_mainCoefficient_ge_twoPoint6408
    jurkatRichertJ jurkatRichertK jurkatRichert_integralEstimate
  have hM : 0 ≤ liuSingularSeries N*N/log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hMain hM
  have hs := jurkatRichertSourceWeightedCount_eq N
  unfold ChenBudget.weighted
  nlinarith only [hbase,hmedium,hboundary,hh,hs]

theorem chen_budget_count (b : ChenBudget) {N : ℕ} (hN : 9 ≤ N)
    (hlower : b.weighted*(liuSingularSeries N*N/log (N : ℝ)^2) ≤ jurkatRichertWeightedCount N)
    (htriple : correctedChenTriplePenalty N ≤
      (b.tripleMain+b.tripleRemainder)*(liuSingularSeries N*N/log (N : ℝ)^2)) :
    b.margin*(liuSingularSeries N*N/log (N : ℝ)^2) ≤ ((chenGoodRepresentations N).card : ℝ) := by
  have hb := corrected_counting_bridge_public_of_nine_le hN
  rw [correctedChenKeyCount_eq_jurkatRichertWeightedCount_sub_triple] at hb
  unfold ChenBudget.margin
  nlinarith only [hlower,htriple,hb]

theorem chen_budget_existence (b : ChenBudget) {N : ℕ} (hN : 9 ≤ N)
    (hmargin : 0 < b.margin)
    (hlower : b.weighted*(liuSingularSeries N*N/log (N : ℝ)^2) ≤ jurkatRichertWeightedCount N)
    (htriple : correctedChenTriplePenalty N ≤
      (b.tripleMain+b.tripleRemainder)*(liuSingularSeries N*N/log (N : ℝ)^2)) :
    ∃ p q : ℕ, p.Prime ∧ (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  have hc := chen_budget_count b hN hlower htriple
  have hM : 0 < liuSingularSeries N*N/log (N : ℝ)^2 := by
    exact div_pos (mul_pos (liuSingularSeries_pos N) (by exact_mod_cast (show 0 < N by omega)))
      (pow_pos (log_pos (by exact_mod_cast (show 1 < N by omega))) 2)
  have hcard : 0 < (chenGoodRepresentations N).card := by
    exact_mod_cast (mul_pos hmargin hM).trans_le hc
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations,Finset.mem_filter,Finset.mem_range] at hp
  exact ⟨p,N-p,hp.2.1,MathlibNt.ChensTheorem.semiprime_iff.mp ⟨hp.2.2.1,hp.2.2.2⟩,by omega⟩

/-- Jointly feasible allocation for the larger product-error tolerance. -/
def optimizedChenBudget : ChenBudget :=
  ⟨1/25,123/100,1/20000,3.94033,1/100⟩

theorem optimized_chen_budget_positive : 0 < optimizedChenBudget.margin := by
  norm_num [optimizedChenBudget,ChenBudget.margin,ChenBudget.weighted]

#print axioms chen_budget_existence
end ChenEffective
