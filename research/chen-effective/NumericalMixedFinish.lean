import NumericalMixedGap

open scoped Classical BigOperators Interval
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiFiniteContinuousLayers SuzukiLemma144KappaOne SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem mixed_caseI_correction (S : BoundingSieve) (H : Section13HatLayers)
    (hH : Section13HatSourceContract H) {C K s : ℝ} {M D z : ℕ}
    (hC : 0 ≤ C) (hD : 1 < (D : ℝ)) (hs : 2 ≤ s)
    (hsσ : s ≤ sourceSigma D 16)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hz2 : 2 ≤ (D : ℝ) ^ (1 / s))
    (hw2 : 2 ≤ (D : ℝ) ^ (1 / sourceSigma D 16))
    (hwz : (D : ℝ) ^ (1 / sourceSigma D 16) ≤ (D : ℝ) ^ (1 / s))
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : (logPowerCutoff 32 : ℝ) ≤ Real.log D)
    (hKlevel : K ^ (7 : ℝ) ≤ Real.log D) :
    (16 ≤ sourceSigma D 16 ∧
      C * Real.exp (Real.sqrt K) * suzukiVProduct S z * polynomialCorrectionWeight *
          polynomialInheritedSum S D z (sourceSigma D 16) s ≤
        (11 / 12 : ℝ) * (C * Real.exp (Real.sqrt K) * suzukiVProduct S z *
          polynomialCorrectionWeight * polynomialCorrection D s)) ∨
      C * Real.exp (Real.sqrt K) * suzukiVProduct S z * polynomialCorrectionWeight *
          polynomialInheritedSum S D z (sourceSigma D 16) s ≤
        sigma12InheritedBudget S H M D z C K 16 (1 / 2) s / (100 * sourceSigma D 16) := by
  let W := C * Real.exp (Real.sqrt K) * suzukiVProduct S z
  have hV0 := (suzukiVProduct_pos S (z : ℝ)).le
  have hW : 0 ≤ W := by unfold W; positivity
  have hb := polynomialCorrectionWeight_pos.le
  have hL : 0 < Real.log (D : ℝ) := Real.log_pos hD
  have hlevel := polynomial_transport_level_gate hD hcut hK hKlevel
  by_cases hhigh : 16 ≤ s
  · refine Or.inl ⟨hhigh.trans hsσ, ?_⟩
    have hh := mul_le_mul_of_nonneg_left
      (polynomialInheritedSum_high hD hz2 hw2 hwz hz rfl hhigh hsσ hK hlocal hlevel)
      (mul_nonneg hW hb)
    simpa only [W, mul_assoc, mul_comm, mul_left_comm] using hh
  · apply Or.inr
    have hσ0 : 0 < sourceSigma (D : ℝ) 16 := (by norm_num : (0 : ℝ) < 2).trans_le (hs.trans hsσ)
    have hp := polynomial_compact_correction_payment hL hσ0
      (polynomial_sourceSigma_gate hD hcut)
      (polynomial_compact_hat_floor hH.toSection13HatContract hD M hs (le_of_not_ge hhigh))
    have hi := mixed_polynomial_coarse hD hz2 hw2 hwz hz rfl hs hsσ hK hlocal hlevel
    have hbi : polynomialCorrectionWeight * polynomialInheritedSum S D z (sourceSigma D 16) s ≤
        polynomialCorrectionWeight * (Real.log (D : ℝ)) ^ (-(5 / 8 : ℝ)) := by
      have hh := mul_le_mul_of_nonneg_left hi hb
      have hh' : (3 / 8 : ℝ) * (Real.log (D : ℝ)) ^ (-(5 / 8 : ℝ)) ≤
          (Real.log (D : ℝ)) ^ (-(5 / 8 : ℝ)) := by
        nlinarith only [Real.rpow_nonneg hL.le (-(5 / 8 : ℝ))]
      exact hh.trans (mul_le_mul_of_nonneg_left hh' hb)
    have hh := mul_le_mul_of_nonneg_left (hbi.trans hp) hW
    simpa only [W, sigma12InheritedBudget, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh

theorem mixed_caseI_close (S : BoundingSieve) (H : Section13HatLayers)
    (hH : Section13HatSourceContract H) {C K s ρ side : ℝ} {M D z : ℕ}
    (hC : 0 ≤ C) (hD : 1 < (D : ℝ)) (hs : 2 ≤ s)
    (hsσ : s ≤ sourceSigma D 16)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) (hz2 : 2 ≤ (D : ℝ) ^ (1 / s))
    (hw2 : 2 ≤ (D : ℝ) ^ (1 / sourceSigma D 16))
    (hwz : (D : ℝ) ^ (1 / sourceSigma D 16) ≤ (D : ℝ) ^ (1 / s))
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : (logPowerCutoff 32 : ℝ) ≤ Real.log D) (hKlevel : K ^ (7 : ℝ) ≤ Real.log D)
    (hρ : ρ = (1 + sigma12ContractionMultiplier (sourceSigma D 16) (1 / 2)) / 2)
    (hside : side ≤ ((1 - ρ) / 2) * sigma12InheritedBudget S H M D z C K 16 (1 / 2) s)
    (hactual : suzukiActualT S M D z ≤ suzukiVProduct S z * finiteSourceLayer 1 2 M s +
      ρ * sigma12InheritedBudget S H M D z C K 16 (1 / 2) s + side +
      C * Real.exp (Real.sqrt K) * suzukiVProduct S z * polynomialCorrectionWeight *
        polynomialInheritedSum S D z (sourceSigma D 16) s) :
    suzukiActualT S M D z ≤ suzukiVProduct S z * finiteSourceLayer 1 2 M s +
      (1 - 1 / (10 * sourceSigma D 16)) * mixedBudget S H M D z C K 16 (1 / 2) s := by
  have hσ : 2 ≤ sourceSigma (D : ℝ) 16 := hs.trans hsσ
  have hV0 := (suzukiVProduct_pos S (z : ℝ)).le
  have hB : 0 ≤ sigma12InheritedBudget S H M D z C K 16 (1 / 2) s := by
    unfold sigma12InheritedBudget
    have he := errorEnvelope_nonneg H M (d := (16 : ℝ)) hD (by linarith only [hs])
      (hH.positive _ _ (by linarith only [hs])).le
    have hL := Real.log_pos hD
    positivity
  have hP : 0 ≤ C * Real.exp (Real.sqrt K) * suzukiVProduct S z *
      polynomialCorrectionWeight * polynomialCorrection D s := by
    have hb := polynomialCorrectionWeight_pos.le
    unfold polynomialCorrection
    positivity
  have hh := mixed_gap_arithmetic hB hP hσ
    (mixed_caseI_gap_lower (by linarith only [hσ]) hρ) hside
    (mixed_caseI_correction S H hH hC hD hs hsσ hz hz2 hw2 hwz hK hlocal hcut hKlevel)
  have heq : sigma12InheritedBudget S H M D z C K 16 (1 / 2) s +
      C * Real.exp (Real.sqrt K) * suzukiVProduct S z * polynomialCorrectionWeight * polynomialCorrection D s =
        mixedBudget S H M D z C K 16 (1 / 2) s := by
    unfold sigma12InheritedBudget mixedBudget mixedError
    ring
  rw [heq] at hh
  linarith only [hactual, hh]

#print axioms mixed_caseI_close
end ChenEffective
