import NumericalPolynomialSmall
import NumericalPolynomialGate
import NumericalSmallQuotientChen

/-! The bounded-level branch for the mixed error, with a numerical
single-exponential coefficient for the actual Chen source. This does not yet
assert closure of the mixed invariant through every Case-I/II producer. -/

namespace ChenEffective
open Real
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiLemma144KappaOne JurkatRichert1965ChenGammaOneQOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

noncomputable def polynomialClaimConstant (A K : ℝ) : ℝ :=
  polynomialTerminalConstant A K / polynomialCorrectionWeight

noncomputable def mixedClaimScale (S : BoundingSieve) (H : Section13HatLayers)
    (n D : ℕ) (K s : ℝ) : ℝ :=
  claim14_5Scale S H n (D : ℝ) 16 (1 / 2) (sourceSigma (D : ℝ) 16) K s +
    polynomialCorrectionWeight * polynomialTerminalScale S D K s

theorem polynomialClaimConstant_single_exp_cap {C1 K : ℝ}
    (hC1cap : C1 ≤ Real.exp (10 ^ 40 : ℝ)) (hK : 0 ≤ K) (hKcap : K ≤ (10 ^ 90 : ℝ)) :
    polynomialClaimConstant (C1 * K ^ (7 : ℝ)) K ≤ Real.exp (10 ^ 45 : ℝ) := by
  have hcap := polynomialTerminalConstant_single_exp_cap hC1cap hK hKcap
  unfold polynomialClaimConstant polynomialCorrectionWeight
  rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg]
  calc
    _ ≤ Real.exp (10 ^ 44 : ℝ) * Real.exp 20000 :=
      mul_le_mul_of_nonneg_right hcap (Real.exp_pos _).le
    _ = Real.exp ((10 ^ 44 : ℝ) + 20000) := (Real.exp_add _ _).symm
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

/-- The new bounded branch for Chen has a single-exponential coefficient.
Its mixed scale must still be propagated by a new all-depth induction. -/
theorem numerical_chen_mixed_bounded (N n q : ℕ) {x : ℝ} (hq : 2 ≤ q)
    (hx : 2 ≤ x) (hsmall : Real.log (q : ℝ) ≤ chenSmallQuotientLogBoundary) :
    suzukiActualT (jurkatRichertSourceBoundingSieve N) n q ⌈(q : ℝ) ^ (1 / x)⌉₊ ≤
      Real.exp (10 ^ 45 : ℝ) *
        mixedClaimScale (jurkatRichertSourceBoundingSieve N) jr1965Section13HatLayers n q numericalLocalProductK x := by
  have hK : 0 < numericalLocalProductK := by linarith only [numerical_local_product_two]
  have hb := numerical_mixed_bounded_level (jurkatRichertSourceBoundingSieve N)
    jr1965Section13HatLayers jr1965Section13HatSourceContract hK (numerical_source_local_product N)
    n q ⌈(q : ℝ) ^ (1 / x)⌉₊ hq rfl hx hsmall
  have hc := polynomialClaimConstant_single_exp_cap numericalSuzukiC1_single_exp_cap
    hK.le numericalLocalProductK_lt.le
  have hscale : 0 ≤ mixedClaimScale (jurkatRichertSourceBoundingSieve N) jr1965Section13HatLayers n q numericalLocalProductK x := by
    have hL : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    have hsigma := sourceSigma_pos_of_nat_two_le (d := (16 : ℝ)) hq
    have hv : 0 ≤ claim14_5VProduct (jurkatRichertSourceBoundingSieve N) (q : ℝ) := by
      simpa only [claim14_5VProduct, suzukiVProduct] using
        (suzukiVProduct_pos (jurkatRichertSourceBoundingSieve N) (q : ℝ)).le
    have hOld := claim14_5Scale_nonneg_on_source_domain (jurkatRichertSourceBoundingSieve N)
      jr1965Section13HatLayers jr1965Section13HatSourceContract (N := n) (d := (16 : ℝ))
      (Δ := (1 / 2 : ℝ)) (K := numericalLocalProductK) hq hx
    unfold mixedClaimScale polynomialTerminalScale polynomialCorrection
    have hb0 := polynomialCorrectionWeight_pos.le
    positivity
  exact hb.trans (mul_le_mul_of_nonneg_right hc hscale)

#print axioms numerical_chen_mixed_bounded
end ChenEffective
