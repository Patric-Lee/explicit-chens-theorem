import NumericalClaim146Tail

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

noncomputable def claim146FullCutoff : ℝ := max claim146MonotoneCutoff claim146TailCutoff

theorem claim146FullCutoff_gt_one : 1 < claim146FullCutoff :=
  derivativeCutoff_gt_one.trans_le ((le_max_left _ _).trans (le_max_left _ _))

/-- All three moving Claim-14.6 clauses, with a displayed numerical cutoff. -/
theorem numerical_claim146 {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) {D : ℝ} (hD : claim146FullCutoff ≤ D) :
    Claim14_6_MonotoneLambdaPremise H D 16 (sourceSigma D 16) ∧
    Claim14_6_MonotoneQPremise H D 16 (1/2) (sourceSigma D 16) ∧
    (∀ (sign : ErrorSign) (s : ℝ), 2+sign.epsilon ≤ s → s ≤ sourceSigma D 16 →
      (∫ t in s..sourceSigma D 16, qD H sign.opposite D 16 (1/2) t) <
        (1-1/sourceSigma D 16)^(1-(1/2 : ℝ)) * lambda H sign D 16 0 s) := by
  have hm := numerical_claim146_monotone hH D ((le_max_left _ _).trans hD)
  exact ⟨hm.1, hm.2, numerical_claim146_tail hH D ((le_max_right _ _).trans hD)⟩

#print axioms numerical_claim146
end ChenEffective
