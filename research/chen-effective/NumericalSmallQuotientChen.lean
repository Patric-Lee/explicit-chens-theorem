import NumericalSmallQuotient
import NumericalC1SingleExponential

/-!
# Chen specialization of the absolute terminal error

These bounds concern the actual source family with the already certified
separator and local-product constant. They introduce no analytic assumption.
They are local terminal estimates, not an all-depth Suzuki theorem with an
improved coefficient; that requires controlling the propagated terminal mass.
-/

open scoped Classical BigOperators
namespace ChenEffective
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

noncomputable def chenSmallQuotientLogBoundary : ℝ :=
  numericalSuzukiC1 * numericalLocalProductK ^ (7 : ℝ)

noncomputable def chenSmallQuotientCoefficient : ℝ :=
  logarithmicR chenSmallQuotientLogBoundary numericalLocalProductK

noncomputable def chenSmallQuotientTerminalCoefficient : ℝ :=
  chenSmallQuotientCoefficient *
    Real.log (logarithmicR (chenSmallQuotientLogBoundary + 1) numericalLocalProductK)

theorem chenSmallQuotientLogBoundary_nonneg : 0 ≤ chenSmallQuotientLogBoundary := by
  unfold chenSmallQuotientLogBoundary numericalSuzukiC1
  exact mul_nonneg (zero_le_one.trans (le_max_left _ _)) (Real.rpow_nonneg
    (by linarith only [numerical_local_product_two]) _)

theorem chenSmallQuotientCoefficient_cap :
    chenSmallQuotientCoefficient ≤ Real.exp (10 ^ 42 : ℝ) :=
  smallQuotient_single_exp_cap numericalSuzukiC1_single_exp_cap
    (by linarith only [numerical_local_product_two]) numericalLocalProductK_lt.le

theorem chenSmallQuotientTerminalCoefficient_cap :
    chenSmallQuotientTerminalCoefficient ≤ Real.exp (10 ^ 43 : ℝ) :=
  smallQuotient_terminal_single_exp_cap
    (zero_le_one.trans (le_max_left _ _)) numericalSuzukiC1_single_exp_cap
    (by linarith only [numerical_local_product_two]) numericalLocalProductK_lt.le

/-- Absolute small-quotient control for the literal Chen source at every
depth, including recursive coordinates outside the final interval [4,5]. -/
theorem numerical_chen_small_quotient (N n q p : ℕ)
    (hq : 2 ≤ q) (hp : 2 ≤ p) (hpq : p ≤ q)
    (hsmall : Real.log (q : ℝ) ≤ chenSmallQuotientLogBoundary) :
    suzukiActualT (jurkatRichertSourceBoundingSieve N) n q p ≤
      chenSmallQuotientCoefficient :=
  numerical_actualT_absolute_log_bound _
    (by linarith only [numerical_local_product_two]) (numerical_source_local_product N)
    n q p hq hp hpq hsmall

/-- A complete immediate terminal sum, independent of the parent level and
depth. The next task is propagation of this additive error across all depths. -/
theorem numerical_chen_small_quotient_sum (N n D : ℕ) (F : Finset ℕ)
    (hsupport : F ⊆ (jurkatRichertSourceBoundingSieve N).prodPrimes.primeFactors)
    (hpoints : ∀ p ∈ F, 2 ≤ D ⌈/⌉ p ∧ 2 ≤ p ∧ p ≤ D ⌈/⌉ p) :
    (∑ p ∈ F.filter (fun p =>
      Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ≤ chenSmallQuotientLogBoundary),
      (jurkatRichertSourceBoundingSieve N).nu p *
        suzukiActualT (jurkatRichertSourceBoundingSieve N) n (D ⌈/⌉ p) p) ≤
      Real.exp (10 ^ 43 : ℝ) :=
  (numerical_small_quotient_sum_bound _
    (by linarith only [numerical_local_product_two]) chenSmallQuotientLogBoundary_nonneg
    (numerical_source_local_product N) F n D hsupport hpoints).trans
      chenSmallQuotientTerminalCoefficient_cap

#print axioms numerical_chen_small_quotient
#print axioms numerical_chen_small_quotient_sum
end ChenEffective
