import NumericalPolynomialMixedCore
import NumericalSmallQuotientChen

namespace ChenEffective
open Real
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiLemma144KappaOne JurkatRichert1965ChenGammaOneQOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-- Chen's bounded branch has a single-exponential coefficient.
`NumericalMixedInduction` propagates its mixed scale through all depths. -/
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
