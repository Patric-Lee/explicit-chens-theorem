import BJSH30ConditionalAggregate
import BJSH30FifthTriple
import NumericalLowerEndpoint
import Goldbach.Statement

noncomputable section
namespace ChenEffective.H30Conditional
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 512

def chenCutoff : ℕ := H30.distributionThreshold

theorem chenCutoff_eq : chenCutoff = 3^(10^13) := bjsStudyGeometryThreshold_eq

theorem square_cutoff_le : H30.squareClosedThreshold ≤ chenCutoff := by
  unfold H30.squareClosedThreshold chenCutoff H30.distributionThreshold
  apply Nat.pow_le_pow_right (by norm_num)
  rw [H30.primePairPowerExponent_eq, H30.distributionExponent_eq]
  norm_num

theorem endpoint_cutoff_le : lowerEndpointThreshold ≤ chenCutoff := by
  unfold lowerEndpointThreshold
  apply max_le
  · apply le_trans (by norm_num : (2:ℕ)^110+1 ≤ 3^100)
    unfold chenCutoff H30.distributionThreshold
    exact Nat.pow_le_pow_right (by norm_num)
      (by rw [H30.distributionExponent_eq]; norm_num)
  · apply max_le
    · exact H30.distribution_log_cutoff (by norm_num)
    · unfold chenCutoff H30.distributionThreshold
      apply Nat.pow_le_pow_right (n:=3) (by decide)
      rw [H30.distributionExponent_eq]
      norm_num

/-- The lower count is assembled from the actual pre-sieved finite counts,
the proved distribution estimates, and the temporary reciprocal-prefix input. -/
theorem weighted_lower {N : ℕ} (hN : chenCutoff ≤ N) (hEven : Even N) :
    (2.02575:ℝ)*(SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) ≤
      jurkatRichertWeightedCount N := by
  have hBase := bjsStudy_base_candidates hN
    ((H30.source_mass_caps (r:=baseCandidateBudget) (by norm_num [baseCandidateBudget])).1.trans
      (square_cutoff_le.trans hN)) hN hEven
  have hUpper := bjsStudy_medium_prime_aggregate hN hN
    ((H30.source_mass_caps (r:=mediumPrimeBudget) (by norm_num [mediumPrimeBudget])).2.trans
      (square_cutoff_le.trans hN)) hN hEven
  let M := SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2
  have hEnd := endpoint_cutoff_le.trans hN
  have hbig : 2^110 < N := by unfold lowerEndpointThreshold at hEnd; omega
  have hb := jurkatRichertSourceWeightedCount_sub_boundary_le_distinct N hbig hEven
  have hp := jurkatRichertDistinctWeightedCount_sub_proper_le N hbig hEven
  have he := numerical_lower_endpoint_loss hEnd
  have he' : 60*(N:ℝ)^(9/10:ℝ) ≤ (1/20000:ℝ)*M := by
    convert he using 1
    dsimp [M]
    ring
  have hn : 0 ≤ (N:ℝ)^(9/10:ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hboundary : jurkatRichertSourceWeightedCount N ≤ jurkatRichertWeightedCount N+
      bjsStudyBudget.endpointLoss*M := by
    norm_num only [bjsStudyBudget] at *
    nlinarith only [hb,hp,he',hn]
  have hh := chen_budget_weighted bjsStudyBudget hBase hUpper hboundary
  convert hh using 1
  norm_num [bjsStudyBudget, ChenBudget.weighted]

/-- Conditional numerical Chen theorem at H=30.027654..., with the exact
cutoff 3^(10^13). The only additional assumption is the explicitly named
temporary reciprocal-prefix window in BJSH30ConditionalProducts. -/
theorem chen {N : ℕ} (hN : chenCutoff ≤ N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q :=
  H30.chen_of_lower (square_cutoff_le.trans hN) hEven (weighted_lower hN hEven)

/-- Literal recovery of the original repository's implicit existence statement. -/
theorem original_chen : Goldbach.ChenTheorem :=
  ⟨chenCutoff, fun _ hN he => chen hN he⟩

#print axioms weighted_lower
#print axioms chen
#print axioms original_chen
end ChenEffective.H30Conditional
