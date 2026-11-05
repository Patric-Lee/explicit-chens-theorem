import NumericalExplicitTower
import QualitativeChen
import Goldbach.Statement
import MathlibNt.ChensTheorem

/-!
The numerical theorem implies the original public specification and its
internal almost-prime formulation. Only the independent statement/vocabulary
modules are imported here; no original implicit Chen proof is used.
-/
noncomputable section
namespace ChenEffective
open Filter

/-- Recover the exact original public existential specification. -/
theorem numerical_implies_original_chen : Goldbach.ChenTheorem :=
  ⟨qualitativeN0, fun _ hN hEven => qualitative_chen hN hEven⟩

/-- Recover the original internal statement, using its existing Semiprime predicate. -/
theorem numerical_implies_original_internal_chen :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ MathlibNt.ChensTheorem.Semiprime q ∧ N=p+q := by
  refine ⟨qualitativeN0, ?_⟩
  intro N hN hEven
  obtain ⟨p,q,hp,hq,hsum⟩ := qualitative_chen hN hEven
  exact ⟨p,q,hp,MathlibNt.ChensTheorem.semiprime_iff.mpr hq,hsum⟩

/-- Recover the original eventual quantitative lower bound for the same count. -/
theorem numerical_implies_original_representation_bound :
    ∀ᶠ N : ℕ in atTop, Even N →
      (0.67 : ℝ)*MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N*(N : ℝ)/
        Real.log N^(2 : ℕ) ≤
      ((MathlibNt.SieveTheory.SwitchingPrinciple.chenGoodRepresentations N).card : ℝ) := by
  filter_upwards [eventually_ge_atTop numericalN0] with N hN
  exact fun hEven => numerical_count_above_tower hN hEven

#print axioms numerical_implies_original_chen
#print axioms numerical_implies_original_internal_chen
#print axioms numerical_implies_original_representation_bound
end ChenEffective
