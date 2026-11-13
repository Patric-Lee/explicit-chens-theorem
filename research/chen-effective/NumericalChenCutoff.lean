import NumericalMediumAggregate
import NumericalNSquare

noncomputable section
namespace ChenEffective
open MathlibNt.SieveTheory SwitchingPrinciple SingularSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 512

private theorem chen_three_power_mono (a b : ℕ) (h : a ≤ b) : (3 : ℕ)^a ≤ 3^b :=
  Nat.pow_le_pow_right (by norm_num) h

private theorem chen_double_three_power_mono (a b : ℕ) (h : a ≤ b) :
    (3 : ℕ)^(3^a) ≤ 3^(3^b) :=
  chen_three_power_mono _ _ (chen_three_power_mono _ _ h)

theorem nLower_le_nSquare : nLower ≤ nSquare :=
  (le_of_eq nLower_eq).trans
    ((chen_double_three_power_mono 20000 4000000000000 (by norm_num)).trans_eq nSquare_eq.symm)

#print axioms nLower_le_nSquare

/-- A closed numerical Chen cutoff under the sole local Dirichlet axiom. -/
def N0 : ℕ := chenCutoff nLower nSquare numericalTripleErrorCap

private theorem chen_cutoff_formula_symbolic {a b b' c : ℕ} (hb : b=b') :
    chenCutoff a b c = max 9 (max a (max b' (3^(20000*c+1)))) := by
  exact congrArg (fun k : ℕ => max 9 (max a (max k (3^(20000*c+1))))) hb

private theorem chen_cutoff_eq_symbolic {a b c : ℕ}
    (h9 : 9 ≤ b) (ha : a ≤ b) (hc : 3^(20000*c+1) ≤ b) :
    chenCutoff a b c = b := by
  unfold chenCutoff errorCutoff
  exact le_antisymm (max_le h9 (max_le ha (max_le le_rfl hc)))
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem N0_formula : N0 = max 9 (max nLower (max (3^(3^4000000000000)) (3^(20000*10^40+1)))) := by
  exact chen_cutoff_formula_symbolic (a:=nLower) (c:=10^40) nSquare_eq

theorem N0_eq_nSquare : N0=nSquare := by
  have h9 : 9 ≤ nSquare :=
    (by norm_num : 9 ≤ (3 : ℕ)^(3^1)).trans
      ((chen_double_three_power_mono 1 4000000000000 (by norm_num)).trans_eq nSquare_eq.symm)
  have herr : 3^(20000*10^40+1) ≤ nSquare :=
    (chen_three_power_mono (20000*10^40+1) (3^200) (by norm_num)).trans
      ((chen_double_three_power_mono 200 4000000000000 (by norm_num)).trans_eq nSquare_eq.symm)
  exact chen_cutoff_eq_symbolic (c:=10^40) h9 nLower_le_nSquare herr

theorem N0_closed : N0=3^(3^4000000000000) := N0_eq_nSquare.trans nSquare_eq

#print axioms N0_closed

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
