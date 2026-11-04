import NumericalClaim146Monotone

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open BridgeAssembly CutoffCorrectedRatio
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def hatShiftCoefficient : ℝ := (51200 : ℝ)^2 * 2
noncomputable def hatTailCoefficient : ℝ := 3 * hatShiftCoefficient^2

theorem numerical_hat_two_step {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) (sign : ErrorSign) {M : ℝ}
    (hM : 4 ≤ M) (hcut : Real.exp 2309 ≤ M+1) :
    weightedHat H sign (M+2) ≤
      (hatTailCoefficient / (M * Real.log (Real.exp 1 * M))^2) * weightedHat H sign M := by
  let E := hatShiftCoefficient
  let A := hatShiftCoefficient
  let Ctail := hatTailCoefficient
  have hEA : E ≤ A := le_rfl
  have hE0 : 0 ≤ E := by unfold E hatShiftCoefficient; positivity
  have hM0 : 0 < M := by linarith only [hM]
  have hL : 0 < Real.log (Real.exp 1 * M) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) hM0.ne', Real.log_exp]
    have h := Real.log_nonneg (show 1 ≤ M by linarith only [hM])
    linarith only [h]
  have hd0 : 0 < M * Real.log (Real.exp 1 * M) := mul_pos hM0 hL
  have hTM0 := hH.positive sign M hM0
  have htwo := section13Hat_twoStep_after_cutoff sign
    (numericalHatBridge hH sign) (numericalForwardMajorant hH) hcut
  change H.T sign (M+2) ≤
    E^2 / (((M+1)*Real.log (Real.exp 1 * (M+1))) *
      ((M+2)*Real.log (Real.exp 1 * (M+2)))) * H.T sign M at htwo
  have hlog1 : Real.log (Real.exp 1 * M) ≤ Real.log (Real.exp 1 * (M + 1)) :=
    Real.log_le_log (by positivity) (by gcongr; linarith)
  have hlog2 : Real.log (Real.exp 1 * M) ≤ Real.log (Real.exp 1 * (M + 2)) :=
    Real.log_le_log (by positivity) (by gcongr; linarith)
  have hd1 : M * Real.log (Real.exp 1 * M) ≤
      (M + 1) * Real.log (Real.exp 1 * (M + 1)) :=
    mul_le_mul (by linarith) hlog1 hL.le (by linarith)
  have hd2 : M * Real.log (Real.exp 1 * M) ≤
      (M + 2) * Real.log (Real.exp 1 * (M + 2)) :=
    mul_le_mul (by linarith) hlog2 hL.le (by linarith)
  have hden : (M * Real.log (Real.exp 1 * M)) ^ 2 ≤
      ((M + 1) * Real.log (Real.exp 1 * (M + 1))) *
        ((M + 2) * Real.log (Real.exp 1 * (M + 2))) := by
    simpa only [pow_two] using
      mul_le_mul hd1 hd2 hd0.le (hd0.le.trans hd1)
  have hsq : E ^ 2 ≤ A ^ 2 := by
    simpa only [pow_two] using mul_le_mul hEA hEA hE0 (hE0.trans hEA)
  have hcoeff : E ^ 2 /
      (((M + 1) * Real.log (Real.exp 1 * (M + 1))) *
        ((M + 2) * Real.log (Real.exp 1 * (M + 2)))) ≤
      (A / (M * Real.log (Real.exp 1 * M))) ^ 2 := by
    calc
      _ ≤ E ^ 2 / (M * Real.log (Real.exp 1 * M)) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg E) (sq_pos_of_pos hd0) hden
      _ ≤ A ^ 2 / (M * Real.log (Real.exp 1 * M)) ^ 2 :=
        div_le_div_of_nonneg_right hsq (sq_nonneg _)
      _ = _ := (div_pow _ _ 2).symm
  have hchain : H.T sign (M + 2) ≤
      (A / (M * Real.log (Real.exp 1 * M))) ^ 2 * H.T sign M :=
    htwo.trans (mul_le_mul_of_nonneg_right hcoeff hTM0.le)
  have hratio : (M + 2) ^ 2 ≤ 3 * M ^ 2 := by nlinarith
  have hweighted := mul_le_mul_of_nonneg_left hchain (sq_nonneg (M + 2))
  have htailfinal : weightedHat H sign (M + 2) ≤
      (Ctail / (M * Real.log (Real.exp 1 * M)) ^ 2) * weightedHat H sign M := by
    calc
      weightedHat H sign (M + 2) ≤ (M + 2) ^ 2 *
          ((A / (M * Real.log (Real.exp 1 * M))) ^ 2 * H.T sign M) := by
        simpa only [weightedHat] using hweighted
      _ ≤ (3 * M ^ 2) * ((A / (M * Real.log (Real.exp 1 * M))) ^ 2 * H.T sign M) :=
        mul_le_mul_of_nonneg_right hratio (mul_nonneg (sq_nonneg _) hTM0.le)
      _ = (Ctail / (M * Real.log (Real.exp 1 * M)) ^ 2) * weightedHat H sign M := by
        dsimp [Ctail, hatTailCoefficient, A, weightedHat]
        field_simp [ne_of_gt hM0, ne_of_gt hL]

  exact htailfinal

#print axioms numerical_hat_two_step
theorem numerical_hat_tail_decay {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) (sign : ErrorSign) {M s : ℝ}
    (hM : 4 ≤ M) (hcut : Real.exp 2309 ≤ M+1)
    (hs : 2+sign.epsilon ≤ s) (hsM : s ≤ M) :
    weightedHat H sign (M+2) ≤ (hatTailCoefficient / M^2) * weightedHat H sign s := by
  have hm0 : 0 < M := by linarith only [hM]
  have hlog : 1 ≤ Real.log (Real.exp 1 * M) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) hm0.ne', Real.log_exp]
    linarith only [Real.log_nonneg (show 1 ≤ M by linarith only [hM])]
  have hprod : M ≤ M * Real.log (Real.exp 1 * M) := by nlinarith only [hlog, hm0]
  have hsq : M^2 ≤ (M * Real.log (Real.exp 1 * M))^2 :=
    pow_le_pow_left₀ hm0.le hprod 2
  have hC0 : 0 ≤ hatTailCoefficient := by unfold hatTailCoefficient; positivity
  have hcoef := div_le_div_of_nonneg_left hC0 (sq_pos_of_pos hm0) hsq
  have hmono : weightedHat H sign M ≤ weightedHat H sign s :=
    weightedHat_antitoneOn_Icc_closed hH.toSection13HatContract sign hs
      ⟨le_rfl, hsM⟩ ⟨hsM, le_rfl⟩ hsM
  have hs0 : 0 < s := by
    have heps : 0 ≤ sign.epsilon := by cases sign <;> norm_num [ErrorSign.epsilon]
    linarith only [hs, heps]
  have hWs : 0 ≤ weightedHat H sign s :=
    mul_nonneg (sq_nonneg s) (hH.positive sign s hs0).le
  exact ((numerical_hat_two_step hH sign hM hcut).trans
    (mul_le_mul_of_nonneg_left hmono (div_nonneg hC0 (sq_nonneg _)))).trans
    (mul_le_mul_of_nonneg_right hcoef hWs)

end ChenEffective
