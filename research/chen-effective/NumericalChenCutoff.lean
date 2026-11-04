import NumericalMediumAggregate
import NumericalNSquare

noncomputable section
namespace ChenEffective
open MathlibNt.SieveTheory SwitchingPrinciple SingularSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A closed numerical Chen cutoff under the sole local Dirichlet axiom. -/
def N0 : ℕ := chenCutoff nLower nSquare numericalTripleErrorCap

theorem N0_formula : N0 = max 9 (max nLower (max (3^(3^4000000000000)) (3^(20000*10^40+1)))) := by
  unfold N0 chenCutoff errorCutoff numericalTripleErrorCap
  rw [nSquare_eq]

/-- Every even integer above the displayed cutoff is prime plus a prime or
the product of two primes. No analytic estimate remains as a hypothesis. -/
theorem numerical_chen {N : ℕ} (hN : N0 ≤ N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧ (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q :=
  numerical_chen_from_lower nLower (fun M hM hMeven => numerical_weighted_lower (N := M) hM hMeven) hN hEven

theorem numerical_chen_representation_count {N : ℕ} (hN : N0 ≤ N) (hEven : Even N) :
    (0.67 : ℝ)*liuSingularSeries N*N/Real.log (N : ℝ)^2 ≤ ((chenGoodRepresentations N).card : ℝ) :=
  explicit_representation_count nLower nSquare numericalTripleErrorCap (numericalTripleErrorCap : ℝ) le_rfl
    (fun M hM hMeven => numerical_weighted_lower (N := M) hM hMeven)
    (fun M hM hMeven => numerical_triple_bound (N := M) hM hMeven) hN hEven

#print axioms numerical_chen
#print axioms numerical_chen_representation_count
end ChenEffective
