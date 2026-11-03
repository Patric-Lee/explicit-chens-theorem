import NumericalC1Order
import NumericalReverseRatio

namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

@[irreducible] def caseIEndpointC1 : ℕ := caseIOrderC1 (1 + 300 * reverseRatioCap)

theorem reverseRatioCap_one : (1 : ℝ) ≤ reverseRatioCap := by
  norm_num [reverseRatioCap]

theorem caseIEndpointC1_eq : caseIEndpointC1 = 3 ^ (1200 * reverseRatioCap + 5) := by
  unfold caseIEndpointC1
  exact caseIOrderC1_finite_amplitude _

/-- No qualitative reverse-ratio or endpoint-amplitude constant remains here. -/
theorem numerical_caseI_endpoint_gap_closed {C C1 K D : ℝ}
    (hC : 3 ≤ C) (hC1 : (caseIEndpointC1 : ℝ) ≤ C1)
    (hK : 2 ≤ K) (hD : 2 ≤ D)
    (hlarge : C1 * K ^ (7 : ℝ) < Real.log D) :
    ∃ q : Lemma144StrictFactor,
      q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma D 16) (1 / 2)) / 2 ∧
      caseISourceOrderCoefficient
        (1 / C + 864 * (reverseRatioCap : ℝ) / (C * Real.exp (Real.sqrt K)) +
          12 * (reverseRatioCap : ℝ)) D 16 ≤ 1 - q.ρ := by
  unfold caseIEndpointC1 at hC1
  exact numerical_caseI_endpoint_gap (r := reverseRatioCap) (R := (reverseRatioCap : ℝ))
    (by exact_mod_cast (Nat.zero_le reverseRatioCap)) le_rfl hC hC1 hK hD hlarge

#print axioms numerical_caseI_endpoint_gap_closed
end ChenEffective
