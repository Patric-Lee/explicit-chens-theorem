import NumericalPolynomialSmall
import NumericalPolynomialGate
import NumericalSuzukiC1

namespace ChenEffective
variable [profile : CorrectionProfile]
open Real
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable def polynomialClaimConstant (A K : ℝ) : ℝ :=
  polynomialTerminalConstant A K / polynomialCorrectionWeight

noncomputable def mixedClaimScale (S : BoundingSieve) (H : Section13HatLayers)
    (n D : ℕ) (K s : ℝ) : ℝ :=
  claim14_5Scale S H n (D : ℝ) 16 (1 / 2) (sourceSigma (D : ℝ) 16) K s +
    polynomialCorrectionWeight * polynomialTerminalScale S D K s

theorem polynomialClaimConstant_single_exp_cap {C1 K : ℝ}
    (hC1cap : C1 ≤ Real.exp (10 ^ 40 : ℝ)) (hK : 0 ≤ K) (hKcap : K ≤ (10 ^ 90 : ℝ))
    (hweight : Real.exp (-1000 : ℝ) ≤ polynomialCorrectionWeight) :
    polynomialClaimConstant (C1 * K ^ (7 : ℝ)) K ≤ Real.exp (10 ^ 45 : ℝ) := by
  have hcap := polynomialTerminalConstant_single_exp_cap hC1cap hK hKcap
  unfold polynomialClaimConstant
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp (10 ^ 44 : ℝ) * Real.exp 1000 :=
      mul_le_mul hcap (polynomialCorrectionWeight_inverse hweight) (inv_nonneg.mpr polynomialCorrectionWeight_pos.le) (Real.exp_pos _).le
    _ = Real.exp ((10 ^ 44 : ℝ) + 1000) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)

/-- No compact hat minimum is used in this bounded-level base case. -/
theorem numerical_mixed_bounded_level (S : BoundingSieve) (H : Section13HatLayers)
    (hH : Section13HatSourceContract H) {K A x : ℝ}
    (hK : 0 < K) (hlocal : HasDimensionOneLocalProductBound S K)
    (n q p : ℕ) (hq : 2 ≤ q) (hp : p = ⌈(q : ℝ) ^ (1 / x)⌉₊)
    (hx : 2 ≤ x) (hA : Real.log (q : ℝ) ≤ A) :
    suzukiActualT S n q p ≤ polynomialClaimConstant A K * mixedClaimScale S H n q K x := by
  have hb := numerical_polynomial_terminal_bound S hK hlocal n q p hq hp hx hA
  have hOld : 0 ≤ claim14_5Scale S H n (q : ℝ) 16 (1 / 2)
      (sourceSigma (q : ℝ) 16) K x :=
    claim14_5Scale_nonneg_on_source_domain S H hH hq hx
  have hc : 0 ≤ polynomialClaimConstant A K := by
    unfold polynomialClaimConstant polynomialTerminalConstant
    exact div_nonneg (by positivity) polynomialCorrectionWeight_pos.le
  calc
    _ ≤ polynomialTerminalConstant A K * polynomialTerminalScale S q K x := hb
    _ = polynomialClaimConstant A K *
        (polynomialCorrectionWeight * polynomialTerminalScale S q K x) := by
      unfold polynomialClaimConstant
      field_simp [polynomialCorrectionWeight_pos.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hOld) hc


#print axioms numerical_mixed_bounded_level
end ChenEffective
