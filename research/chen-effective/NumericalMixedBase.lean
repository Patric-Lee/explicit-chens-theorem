import NumericalMixedCaseIITransfer

open scoped Classical BigOperators Interval
namespace ChenEffective
variable [profile : CorrectionProfile]
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiFiniteContinuousLayers SuzukiLemma144KappaOne SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def mixedClaimCoefficient (C1 K : ℝ) : ℝ :=
  max 1 (polynomialClaimConstant (C1 * K ^ (7 : ℝ)) K)
noncomputable def mixedSuzukiCoefficient (C1 K : ℝ) : ℝ :=
  suzukiCoefficient (mixedClaimCoefficient C1 K) C1

theorem mixed_point_of_old (S : BoundingSieve) (H : Section13HatLayers)
    {N D z : ℕ} {C K d Δ s : ℝ} (hC : 0 ≤ C)
    (h : suzukiActualT S N D z ≤ suzukiVProduct S z *
      (finiteSourceLayer 1 2 N s + C * Real.exp (Real.sqrt K) *
        errorEnvelope H N D d s * (Real.log D) ^ (-Δ))) :
    suzukiActualT S N D z ≤ suzukiVProduct S z *
      (finiteSourceLayer 1 2 N s + C * Real.exp (Real.sqrt K) * mixedError H N D d Δ s) := by
  have hv := (suzukiVProduct_pos S (z : ℝ)).le
  have hb := polynomialCorrectionWeight_pos.le
  have hp : 0 ≤ polynomialCorrection D s := by unfold polynomialCorrection; positivity
  unfold mixedError
  have hh := mul_nonneg (mul_nonneg (mul_nonneg hv hC) (Real.exp_pos (Real.sqrt K)).le) (mul_nonneg hb hp)
  nlinarith only [h, hh]

theorem mixed_claim_to_point (S : BoundingSieve) (H : Section13HatLayers)
    (hH : Section13HatSourceContract H) {N D : ℕ} {C C145 K s : ℝ}
    (hC145 : 0 ≤ C145) (hD : 2 ≤ D) (hs : s ∈ KappaOneModel.parityDomain 2 N)
    (hscalar : C145 / (Real.log (D : ℝ) * sourceSigma D 16) ≤ C)
    (hclaim : suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤ C145 * mixedClaimScale S H N D K s) :
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 N s + C * Real.exp (Real.sqrt K) * mixedError H N D 16 (1 / 2) s) := by
  have hs1 : 1 < s := by
    by_cases ho : N % 2 = 1
    · have hh : (2 : ℝ) - 1 < s := by simpa [KappaOneModel.parityDomain, ho] using hs
      linarith only [hh]
    · have hh : 2 ≤ s := by simpa [KappaOneModel.parityDomain, ho] using hs
      linarith only [hh]
  have hD1 : (1 : ℝ) < D := by exact_mod_cast (show 1 < D by omega)
  have hL := Real.log_pos hD1
  have hsig := sourceSigma_pos_of_nat_two_le (d := (16 : ℝ)) hD
  have hzD : (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) ≤ D := by
    exact_mod_cast natCeil_rpow_le_self_on_parityDomain hD hs
  have hv := claim14_5VProduct_le_suzukiVProduct S hzD
  have hvz0 := (suzukiVProduct_pos S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ)).le
  have hv0 : 0 ≤ claim14_5VProduct S (D : ℝ) := by
    simpa only [claim14_5VProduct, suzukiVProduct] using (suzukiVProduct_pos S (D : ℝ)).le
  have he := mixedError_nonneg hH.toSection13HatContract (d := (16 : ℝ)) (Δ := (1 / 2 : ℝ)) hD1
    (zero_lt_one.trans hs1) N
  have hr : 0 ≤ C145 / (Real.log (D : ℝ) * sourceSigma D 16) := by positivity
  have hm := finiteSourceLayer_nonneg_on_parityDomain (by norm_num : (1 : ℝ) < 2) N hs
  apply hclaim.trans
  calc
    _ = claim14_5VProduct S (D : ℝ) *
        (C145 / (Real.log (D : ℝ) * sourceSigma D 16) * Real.exp (Real.sqrt K) *
          mixedError H N D 16 (1 / 2) s) := by
      unfold mixedClaimScale claim14_5Scale polynomialTerminalScale mixedError
      ring
    _ ≤ suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
        (C * Real.exp (Real.sqrt K) * mixedError H N D 16 (1 / 2) s) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hm)
      (suzukiVProduct_pos S _).le

theorem mixed_claim_regime (S : BoundingSieve) (H : Section13HatLayers)
    (hH : Section13HatSourceContract H) {C1 K s : ℝ} {N D : ℕ}
    (hC1 : caseBSourceC1 ≤ C1) (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K) (hD : 2 ≤ D) (hs : 2 ≤ s)
    (hregime : Real.log (D : ℝ) ≤ C1 * K ^ (7 : ℝ) ∨ sourceSigma D 16 ≤ s) :
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      mixedClaimCoefficient C1 K * mixedClaimScale S H N D K s := by
  have hD1 : (1 : ℝ) < D := by exact_mod_cast (show 1 < D by omega)
  have hs0 : 0 < s := by linarith only [hs]
  have hL := Real.log_pos hD1
  have hsig := sourceSigma_pos_of_nat_two_le (d := (16 : ℝ)) hD
  have hv0 : 0 ≤ claim14_5VProduct S (D : ℝ) := by
    simpa only [claim14_5VProduct, suzukiVProduct] using (suzukiVProduct_pos S (D : ℝ)).le
  have hscale : 0 ≤ mixedClaimScale S H N D K s := by
    have ho := claim14_5Scale_nonneg_on_source_domain S H (N := N) (d := (16 : ℝ))
      (Δ := (1 / 2 : ℝ)) (K := K) hH hD hs
    have hb := polynomialCorrectionWeight_pos.le
    unfold mixedClaimScale polynomialTerminalScale polynomialCorrection
    positivity
  by_cases hsmall : Real.log (D : ℝ) ≤ C1 * K ^ (7 : ℝ)
  · exact (numerical_mixed_bounded_level S H hH (by linarith only [hK]) hlocal N D _ hD rfl hs hsmall).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hscale)
  · have hb := numerical_caseB_cutoff H hH S C1 K N D s hC1 hK hlocal hD hs
      (lt_of_not_ge hsmall) (hregime.resolve_left hsmall)
    change suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      1 * claim14_5Scale S H N D 16 (1 / 2) (sourceSigma D 16) K s at hb
    have hextra : 0 ≤ polynomialCorrectionWeight * polynomialTerminalScale S D K s := by
      have hp := polynomialCorrectionWeight_pos.le
      unfold polynomialTerminalScale polynomialCorrection
      positivity
    apply hb.trans
    have hh : claim14_5Scale S H N D 16 (1 / 2) (sourceSigma D 16) K s ≤ mixedClaimScale S H N D K s :=
      le_add_of_nonneg_right hextra
    have hstep : 1 * claim14_5Scale S H N D 16 (1 / 2) (sourceSigma D 16) K s ≤
        mixedClaimScale S H N D K s := by simpa only [one_mul] using hh
    have hfinal : mixedClaimScale S H N D K s ≤ mixedClaimCoefficient C1 K * mixedClaimScale S H N D K s := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show 1 ≤ mixedClaimCoefficient C1 K from le_max_left _ _) hscale
    exact hstep.trans hfinal

#print axioms mixed_claim_regime
end ChenEffective
