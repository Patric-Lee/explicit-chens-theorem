import NumericalMovingTail

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open BridgeAssembly CutoffCorrectedRatio SourceClaim146AssemblyNext
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def claim146TailHead : ℝ :=
  max (claim146iiiFixedM hatTailCoefficient (1/2)) (max sourceRatioHead (Real.exp 2309))
noncomputable def claim146TailCutoff : ℝ :=
  let M := claim146TailHead
  max (perturbationCutoff 16 (M+2) 2)
    (max (weightedHeadCutoff M) (max (movingTailCutoff M)
      (max (movingTailCutoff M) (sourceLowerCutoff (M+2)))))
private lemma qD_split_at_fixed_source_point
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {D d Δ M s : ℝ} (hD : 1 < D)
    (hs : 2 + sign.epsilon ≤ s) (hsM : s ≤ M)
    (hMσ : M + 2 ≤ sourceSigma D d) :
    (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) =
      (∫ t in s..M + 2, qD H sign.opposite D d Δ t) +
      (∫ t in M + 2..sourceSigma D d, qD H sign.opposite D d Δ t) := by
  have hs1 : 1 < s := by
    cases sign <;> simp [ErrorSign.epsilon] at hs ⊢ <;> linarith
  have hcont : ContinuousOn (qD H sign.opposite D d Δ)
      (Icc s (sourceSigma D d)) :=
    continuousOn_qD_Icc_of_contract hH sign.opposite hD hs1
  have hintLeft :
      IntervalIntegrable (qD H sign.opposite D d Δ) volume s (M + 2) :=
    (hcont.mono (Icc_subset_Icc_right hMσ)).intervalIntegrable_of_Icc (by linarith)
  have hintRight :
      IntervalIntegrable (qD H sign.opposite D d Δ) volume (M + 2) (sourceSigma D d) :=
    (hcont.mono (Icc_subset_Icc_left (by linarith : s ≤ M + 2))).intervalIntegrable_of_Icc hMσ
  exact (intervalIntegral.integral_add_adjacent_intervals hintLeft hintRight).symm

private lemma claim146iii_margin_of_le
    {C gap M : ℝ} (hC : 0 ≤ C) (hgap : 0 < gap)
    (hM : claim146iiiFixedM C gap ≤ M) :
    4 ≤ M ∧ 2 * C / M ^ 2 < gap / (4 * M) := by
  have hM4 : 4 ≤ M := (le_max_left 4 (16 * C / gap + 1)).trans hM
  have hMpos : 0 < M := by linarith
  have hMlower : 16 * C / gap + 1 ≤ M := (le_max_right 4 (16 * C / gap + 1)).trans hM
  have hcross : 16 * C < gap * M := by
    have hscaled := mul_le_mul_of_nonneg_left hMlower hgap.le
    have hident : gap * (16 * C / gap + 1) = 16 * C + gap := by
      field_simp [ne_of_gt hgap]
    rw [hident] at hscaled
    linarith
  refine ⟨hM4, ?_⟩
  rw [div_lt_div_iff₀ (sq_pos_of_pos hMpos) (mul_pos (by norm_num) hMpos)]
  nlinarith [sq_nonneg M]

theorem numerical_claim146_tail {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) :
    ∀ D : ℝ, claim146TailCutoff ≤ D →
      ∀ (sign : ErrorSign) (s : ℝ),
        2+sign.epsilon ≤ s → s ≤ sourceSigma D 16 →
        (∫ t in s..sourceSigma D 16, qD H sign.opposite D 16 (1/2) t) <
          (1-1/sourceSigma D 16)^(1-(1/2 : ℝ)) * lambda H sign D 16 0 s := by
  let d : ℝ := 16
  let Δ : ℝ := 1/2
  let C := hatTailCoefficient
  have hd : 0 < d := by norm_num [d]
  have hΔ0 : 0 < Δ := by norm_num [Δ]
  have hΔ1 : Δ < 1 := by norm_num [Δ]
  have hC : 0 ≤ C := by dsimp [C, hatTailCoefficient]; positivity
  let gap : ℝ := 1-Δ
  have hgap : 0 < gap := by norm_num [gap, Δ]
  let M := claim146TailHead
  have hMMcore : claim146iiiFixedM C gap ≤ M := by
    rw [show gap = (1/2 : ℝ) by norm_num [gap, Δ] ]
    exact le_max_left _ _
  have hM4 : 4 ≤ M := (claim146iii_margin_of_le hC hgap hMMcore).1
  have hcoef : 2*C/M^2 < gap/(4*M) := (claim146iii_margin_of_le hC hgap hMMcore).2
  have hMhead : sourceRatioHead ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hMcut : Real.exp 2309 ≤ M+1 := by
    have hh : Real.exp 2309 ≤ M :=
      (le_max_right sourceRatioHead (Real.exp 2309)).trans
        (le_max_right (claim146iiiFixedM hatTailCoefficient (1/2)) _)
    linarith only [hh]
  let Dp := perturbationCutoff d (M+2) 2
  have hDp : 1 < Dp := Real.one_lt_exp_iff.mpr (zero_lt_one.trans_le (le_max_left _ _))
  have hpert : ∀ D : ℝ, Dp ≤ D → ∀ (sign : ErrorSign) (s : ℝ), 2+sign.epsilon ≤ s → s ≤ M →
      perturbation D d 0 (M+2) ≤ 2 * perturbation D d 0 s := by
    intro D hD sign s hs _
    have hp := numerical_fixed_perturbation (d := d) (p := M+2) (q := 2)
      (by linarith only [hM4]) (by norm_num) hD
    have hs0 : 0 ≤ s := by
      cases sign <;> norm_num [ErrorSign.epsilon] at hs <;> linarith only [hs]
    have hD1 := hDp.trans_le hD
    have hbase : 1 ≤ 1 + (s+0)^d/Real.log D := by
      exact le_add_of_nonneg_right (div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_pos hD1).le)
    have hPs : 1 ≤ perturbation D d 0 s := Real.one_le_rpow hbase hs0
    linarith only [hp, hPs]
  let Dh := weightedHeadCutoff M
  have hhead := numerical_weighted_head hH.toSection13HatContract hM4
  let DtPlus := movingTailCutoff M
  let DtMinus := movingTailCutoff M
  have htailPlus := numerical_moving_tail hH ErrorSign.plus hM4 hMhead
  have htailMinus := numerical_moving_tail hH ErrorSign.minus hM4 hMhead
  let Dσ := sourceLowerCutoff (M+2)
  have hsourceσ := numerical_sourceSigma_lower d (M+2) hd.le


  let D₀ : ℝ := max Dp (max Dh (max DtPlus (max DtMinus Dσ)))
  change ∀ D : ℝ, D₀ ≤ D → _
  intro D hD sign s hs hsσ
  have hDpD : Dp ≤ D := (le_max_left Dp _).trans hD
  have hDhD : Dh ≤ D :=
    (le_max_left Dh _).trans ((le_max_right Dp _).trans hD)
  have hDtPlusD : DtPlus ≤ D :=
    (le_max_left DtPlus _).trans ((le_max_right Dh _).trans ((le_max_right Dp _).trans hD))
  have hDtMinusD : DtMinus ≤ D := by
    exact (le_max_left DtMinus Dσ).trans
      ((le_max_right DtPlus (max DtMinus Dσ)).trans
        ((le_max_right Dh _).trans ((le_max_right Dp _).trans hD)))
  have hDσD : Dσ ≤ D := by
    exact (le_max_right DtMinus Dσ).trans
      ((le_max_right DtPlus (max DtMinus Dσ)).trans
        ((le_max_right Dh _).trans ((le_max_right Dp _).trans hD)))
  have hD1 : 1 < D := hDp.trans_le hDpD
  have hM2σ : M + 2 ≤ sourceSigma D d := hsourceσ D hDσD
  have hlarge :
      ∀ sign : ErrorSign, ∀ s : ℝ, M ≤ s → s ≤ sourceSigma D d →
        (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) <
          (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
            lambda H sign D d 0 s := by
    intro sign s hsM hsσ'
    cases sign with
    | plus =>
        exact htailPlus D hDtPlusD |>.2 s hsM hsσ'
    | minus =>
        exact htailMinus D hDtMinusD |>.2 s hsM hsσ'
  by_cases hMs : M ≤ s
  · exact hlarge sign s hMs hsσ
  · have hsM : s ≤ M := (lt_of_not_ge hMs).le
    have hheadD := hhead D hDhD sign s hs hsM
    have hpertD := hpert D hDpD sign s hs hsM
    have hlambdaDecay :
        lambda H sign D d 0 (M + 2) ≤
          (2 * C / M ^ 2) * lambda H sign D d 0 s :=
      lambda_fixed_endpoint_decay sign hM4 hD1 hs
        (numerical_hat_tail_decay hH sign hM4 hMcut hs hsM) hpertD hH.toSection13HatContract.positive
    have htailD := hlarge sign (M + 2) (by linarith) hM2σ
    have hsplitD :
        (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) =
          (∫ t in s..M + 2, qD H sign.opposite D d Δ t) +
          (∫ t in M + 2..sourceSigma D d, qD H sign.opposite D d Δ t) :=
      qD_split_at_fixed_source_point (Δ := Δ) hH.toSection13HatContract
        sign hD1 hs hsM hM2σ
    let K : ℝ := (1 - 1 / sourceSigma D d) ^ (1 - Δ)
    let L : ℝ := lambda H sign D d 0 s
    have hKpos : 0 < K := by
      dsimp [K]
      apply Real.rpow_pos_of_pos
      have hσ1 : 1 < sourceSigma D d := by linarith [hM4, hM2σ]
      have hσ0 : 0 < sourceSigma D d := zero_lt_one.trans hσ1
      exact sub_pos.mpr ((div_lt_one hσ0).mpr hσ1)
    have hL : 0 < L := by
      dsimp [L]
      exact lambda_pos_of_source_range hH.toSection13HatContract sign hD1 hs
    have htailBound :
        (∫ t in M + 2..sourceSigma D d,
            qD H sign.opposite D d Δ t) <
          K * ((2 * C / M ^ 2) * L) := by
      exact htailD.trans_le (mul_le_mul_of_nonneg_left hlambdaDecay hKpos.le)
    rw [hsplitD]
    have hsum :
        K * (1 - gap / (4 * M)) * L +
            K * ((2 * C / M ^ 2) * L) < K * L := by
      have hcoefsum : 1 - gap / (4 * M) + 2 * C / M ^ 2 < 1 := by
        linarith
      calc
        K * (1 - gap / (4 * M)) * L + K * ((2 * C / M ^ 2) * L) =
            (K * L) * (1 - gap / (4 * M) + 2 * C / M ^ 2) := by ring
        _ < (K * L) * 1 := by
          exact mul_lt_mul_of_pos_left hcoefsum (mul_pos hKpos hL)
        _ = K * L := by ring
    change (∫ t in s..M + 2, qD H sign.opposite D d Δ t) +
        (∫ t in M + 2..sourceSigma D d, qD H sign.opposite D d Δ t) < K * L
    exact (add_lt_add_of_le_of_lt (by simpa [K, L, gap, d, Δ, mul_assoc] using hheadD)
      htailBound).trans hsum
#print axioms numerical_claim146_tail
end ChenEffective
