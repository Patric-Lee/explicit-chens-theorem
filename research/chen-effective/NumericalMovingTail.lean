import NumericalWeightedHead

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open BridgeAssembly CutoffCorrectedRatio SourceClaim146AssemblyNext
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def movingTailCutoff (M : ℝ) : ℝ :=
  max (max sourceRatioCutoff (sourceLowerCutoff M)) (Real.exp (M^(16 : ℝ)))

theorem movingTailCutoff_gt_one (M : ℝ) : 1 < movingTailCutoff M :=
  (sourceLowerCutoff_gt_one M).trans_le
    ((le_max_right _ _).trans (le_max_left _ _))
private lemma slope_le_log
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 ≤ d) (ht : 0 < t) :
    perturbationSlope D d 0 t ≤
      (d + 1) * Real.log (1 + t ^ d / Real.log D) := by
  exact moving_perturbationSlope_le_log hlog hd ht

private lemma below_cutoff_z_le_one
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 < d) (ht : 0 < t)
    (hcut : t ≤ (Real.log D) ^ (1 / d)) :
    t ^ d / Real.log D ≤ 1 := by
  exact moving_below_cutoff_z_le_one hlog hd ht hcut

private lemma above_cutoff_one_lt_z
    {D d t : ℝ} (hlog : 0 < Real.log D) (hd : 0 < d)
    (hcut : (Real.log D) ^ (1 / d) < t) :
    1 < t ^ d / Real.log D := by
  exact moving_above_cutoff_one_lt_z hlog hd hcut

theorem numerical_asymptotic_certificate {H : Section13HatLayers}
    (hSource : Section13HatSourceContract H) (sign : ErrorSign) {M : ℝ}
    (hM : 4 ≤ M) (hHead : sourceRatioHead ≤ M) :
    ∀ D : ℝ, movingTailCutoff M ≤ D →
      M ≤ sourceSigma D 16 ∧
      (∀ t, M ≤ t → t ≤ (Real.log D)^(1/(16 : ℝ)) → t ≤ sourceSigma D 16 →
        weightedHat H sign t * perturbationSlope D 16 0 t ≤
          t * H.T sign.opposite (t-1) *
            ((t^(16 : ℝ)/Real.log D)/(1+t^(16 : ℝ)/Real.log D))) ∧
      (∀ t, (Real.log D)^(1/(16 : ℝ)) < t → t ≤ sourceSigma D 16 →
        weightedHat H sign t * perturbationSlope D 16 0 t ≤
          t * H.T sign.opposite (t-1) *
            ((t^(16 : ℝ)/Real.log D)/(1+t^(16 : ℝ)/Real.log D))) := by
  let d : ℝ := 16
  have hd : 0 < d := by norm_num [d]
  have hH := hSource.toSection13HatContract
  let D₀ := max sourceRatioCutoff (sourceLowerCutoff M)
  have hD₀ : 1 < D₀ :=
    (sourceLowerCutoff_gt_one M).trans_le (le_max_right _ _)
  have hratio : ∀ D : ℝ, D₀ ≤ D → M ≤ sourceSigma D d ∧
      ∀ t, M ≤ t → t ≤ sourceSigma D d →
        2*(d+1)*max 1 (Real.log (1+t^d/Real.log D))*weightedHat H sign t ≤
          t * H.T sign.opposite (t-1) := by
    intro D hD
    refine ⟨numerical_sourceSigma_lower d M hd.le D ((le_max_right _ _).trans hD), ?_⟩
    intro t ht htσ
    exact (numerical_source_ratio hSource ((le_max_left _ _).trans hD)).2
      sign t (hHead.trans ht) htσ
  have hM' : 1 < M := by linarith only [hM]
  let Dm : ℝ := Real.exp (M ^ d)
  have hDm : 1 < Dm := by
    dsimp [Dm]
    exact Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos (by linarith) _)
  let D₁ : ℝ := max D₀ Dm
  change ∀ D : ℝ, D₁ ≤ D → _
  intro D hD
  have hD₀D : D₀ ≤ D := (le_max_left D₀ Dm).trans hD
  have hDmD : Dm ≤ D := (le_max_right D₀ Dm).trans hD
  have hD1 : 1 < D := hD₀.trans_le hD₀D
  have hlog : 0 < Real.log D := Real.log_pos hD1
  have hMdlog : M ^ d ≤ Real.log D := by
    have hm := Real.strictMonoOn_log.monotoneOn (Real.exp_pos (M ^ d))
      (zero_lt_one.trans hD1) hDmD
    simpa [Dm] using hm
  have hMcut : M ≤ (Real.log D) ^ (1 / d) := by
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith : 0 ≤ M) d)
      hMdlog (by positivity : 0 ≤ 1 / d)
    have hc : (M ^ d) ^ (1 / d) = M := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ M)]
      have : d * (1 / d) = 1 := by field_simp
      rw [this, Real.rpow_one]
    rwa [hc] at hp
  rcases hratio D hD₀D with ⟨hMσ, hratioD⟩
  refine ⟨hMσ, ?_, ?_⟩
  · intro t hMt hcut htσ
    have ht : 0 < t := by linarith
    let z : ℝ := t ^ d / Real.log D
    let W : ℝ := weightedHat H sign t
    let A : ℝ := t * H.T sign.opposite (t - 1)
    have hz0 : 0 ≤ z := div_nonneg (Real.rpow_nonneg ht.le _) hlog.le
    have hz1 : z ≤ 1 := below_cutoff_z_le_one hlog hd ht hcut
    have hb : 0 < 1 + z := by linarith
    have hW0 : 0 ≤ W := by
      dsimp [W, weightedHat]
      exact mul_nonneg (sq_nonneg t) (hH.positive sign t ht).le
    have hratioRaw := hratioD t hMt htσ
    have hratioOne : 2 * ((d + 1) * W) ≤ A := by
      dsimp [z, W, A] at hratioRaw ⊢
      calc
        2 * ((d + 1) * weightedHat H sign t) =
            2 * (d + 1) * 1 * weightedHat H sign t := by ring
        _ ≤ 2 * (d + 1) * max 1
            (Real.log (1 + t ^ d / Real.log D)) * weightedHat H sign t := by
              gcongr
              exact le_max_left _ _
        _ ≤ t * H.T sign.opposite (t - 1) := hratioRaw
    have hden : (d + 1) * W * (1 + z) ≤ A := by
      have hx0 : 0 ≤ (d + 1) * W := mul_nonneg (by linarith) hW0
      nlinarith
    have hs := slope_le_log hlog hd.le ht
    have hlogz : Real.log (1 + z) ≤ z := by
      linarith [Real.log_le_sub_one_of_pos hb]
    have hsW : W * perturbationSlope D d 0 t ≤ (d + 1) * W * z := by
      calc
        W * perturbationSlope D d 0 t ≤
            W * ((d + 1) * Real.log (1 + z)) := by
              apply mul_le_mul_of_nonneg_left _ hW0
              simpa [z] using hs
        _ ≤ W * ((d + 1) * z) := by gcongr
        _ = (d + 1) * W * z := by ring
    calc
      weightedHat H sign t * perturbationSlope D d 0 t ≤
          (d + 1) * weightedHat H sign t * (t ^ d / Real.log D) := hsW
      _ ≤ t * H.T sign.opposite (t - 1) *
          ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D)) := by
            change (d + 1) * W * z ≤ A * (z / (1 + z))
            rw [show A * (z / (1 + z)) = (A * z) / (1 + z) by ring]
            apply (le_div_iff₀ hb).2
            have hm := mul_le_mul_of_nonneg_right hden hz0
            nlinarith
  · intro t hcut htσ
    have ht : 0 < t := (Real.rpow_pos_of_pos hlog _).trans hcut
    have hMt : M ≤ t := hMcut.trans hcut.le
    let z : ℝ := t ^ d / Real.log D
    let W : ℝ := weightedHat H sign t
    let A : ℝ := t * H.T sign.opposite (t - 1)
    have hz1 : 1 < z := by dsimp [z]; exact above_cutoff_one_lt_z hlog hd hcut
    have hb : 0 < 1 + z := by linarith
    have hW0 : 0 ≤ W := by
      dsimp [W, weightedHat]
      exact mul_nonneg (sq_nonneg t) (hH.positive sign t ht).le
    have hA0 : 0 ≤ A := by
      dsimp [A]
      exact (mul_pos ht (hH.positive sign.opposite (t - 1) (by linarith))).le
    have hratioRaw := hratioD t hMt htσ
    have hratioLog : 2 * ((d + 1) * Real.log (1 + z) * W) ≤ A := by
      dsimp [z, W, A] at hratioRaw ⊢
      calc
        2 * ((d + 1) * Real.log (1 + t ^ d / Real.log D) * weightedHat H sign t) =
            2 * (d + 1) * Real.log (1 + t ^ d / Real.log D) * weightedHat H sign t := by ring
        _ ≤ 2 * (d + 1) * max 1
            (Real.log (1 + t ^ d / Real.log D)) * weightedHat H sign t := by
              gcongr
              exact le_max_right _ _
        _ ≤ t * H.T sign.opposite (t - 1) := hratioRaw
    have hhalf : (1 / 2 : ℝ) ≤ z / (1 + z) := by
      apply (le_div_iff₀ hb).2
      linarith
    have hs := slope_le_log hlog hd.le ht
    have hsW : W * perturbationSlope D d 0 t ≤
        (d + 1) * Real.log (1 + z) * W := by
      calc
        W * perturbationSlope D d 0 t ≤
            W * ((d + 1) * Real.log (1 + z)) := by
              apply mul_le_mul_of_nonneg_left _ hW0
              simpa [z] using hs
        _ = (d + 1) * Real.log (1 + z) * W := by ring
    dsimp [z, W, A] at hsW hratioLog hhalf ⊢
    calc
      weightedHat H sign t * perturbationSlope D d 0 t ≤
          (d + 1) * Real.log (1 + t ^ d / Real.log D) * weightedHat H sign t := hsW
      _ ≤ (1 / 2) * (t * H.T sign.opposite (t - 1)) := by linarith
      _ ≤ t * H.T sign.opposite (t - 1) *
          ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D)) := by
            nlinarith
private noncomputable def lambdaNegDerivStrict
    (H : Section13HatLayers) (sign : ErrorSign) (D d t : ℝ) : ℝ :=
  perturbation D d 0 t *
    (t * H.T sign.opposite (t - 1) -
      weightedHat H sign t * perturbationSlope D d 0 t)

private lemma hasDerivAt_lambdaNegStrict
    {H : Section13HatLayers} {β D d t : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hlog : 0 < Real.log D) (ht0 : 0 < t)
    (ht : β + sign.epsilon < t) :
    HasDerivAt (-lambda H sign D d 0)
      (lambdaNegDerivStrict H sign D d t) t := by
  have h := (hasDerivAt_lambda_of_contract (d := d) hH sign hlog
    (show 0 < t + 0 by linarith) ht).neg
  have heq : lambdaNegDerivStrict H sign D d t =
      -(perturbation D d 0 t *
        (weightedHat H sign t * perturbationSlope D d 0 t -
          t * H.T sign.opposite (t - 1))) := by
    unfold lambdaNegDerivStrict
    ring
  rw [heq]
  simpa only [Pi.neg_apply, perturbationSlope] using h

private lemma qD_eq_dde_mainStrict
    {H : Section13HatLayers} {D d Δ t : ℝ} (sign : ErrorSign)
    (hlog : 0 < Real.log D) (ht : 1 < t) :
    qD H sign.opposite D d Δ t =
      (perturbation D d 0 t * (t * H.T sign.opposite (t - 1)) /
          (1 + t ^ d / Real.log D)) *
        ((t - 1) / t) ^ (1 - Δ) := by
  exact qD_eq_dde_main sign hlog ht

private lemma qD_le_lambdaNegDeriv_mul_weightStrict
    {H : Section13HatLayers} {β D d Δ t : ℝ}
    (_hH : Section13HatContract H β) (sign : ErrorSign)
    (hlog : 0 < Real.log D) (ht : 1 < t)
    (hasymp : weightedHat H sign t * perturbationSlope D d 0 t ≤
      t * H.T sign.opposite (t - 1) *
        ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D))) :
    qD H sign.opposite D d Δ t ≤
      lambdaNegDerivStrict H sign D d t * ((t - 1) / t) ^ (1 - Δ) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  let z : ℝ := t ^ d / Real.log D
  have hz0 : 0 ≤ z := div_nonneg (Real.rpow_nonneg ht0.le _) hlog.le
  have hb : 0 < 1 + z := by linarith
  have hmain : t * H.T sign.opposite (t - 1) / (1 + z) ≤
      t * H.T sign.opposite (t - 1) -
        weightedHat H sign t * perturbationSlope D d 0 t := by
    dsimp [z] at hasymp ⊢
    calc
      t * H.T sign.opposite (t - 1) / (1 + t ^ d / Real.log D) =
          t * H.T sign.opposite (t - 1) -
            t * H.T sign.opposite (t - 1) *
              ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D)) := by
            field_simp [hb.ne']
            ring
      _ ≤ t * H.T sign.opposite (t - 1) -
            weightedHat H sign t * perturbationSlope D d 0 t := by
              exact sub_le_sub_left hasymp _
  have hp0 : 0 ≤ perturbation D d 0 t := by
    rw [perturbation]
    simpa [z] using Real.rpow_nonneg hb.le t
  have hw0 : 0 ≤ ((t - 1) / t) ^ (1 - Δ) :=
    Real.rpow_nonneg (div_pos (sub_pos.mpr ht) ht0).le _
  rw [qD_eq_dde_mainStrict sign hlog ht]
  dsimp [lambdaNegDerivStrict]
  apply mul_le_mul_of_nonneg_right _ hw0
  convert mul_le_mul_of_nonneg_left hmain hp0 using 1; ring

private lemma continuousOn_lambdaNegDerivStrict
    {H : Section13HatLayers} {β D d a b : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hlog : 0 < Real.log D) (ha : β + sign.epsilon < a) :
    ContinuousOn (lambdaNegDerivStrict H sign D d) (Icc a b) := by
  have heps : 0 ≤ sign.epsilon := by
    cases sign <;> simp [ErrorSign.epsilon]
  have ha0 : 0 < a := by linarith [hH.beta_gt_one]
  have hp : ContinuousOn (perturbation D d 0) (Icc a b) := by
    intro t ht
    exact (hasDerivAt_perturbation (d := d) hlog
      (by simpa using ha0.trans_le ht.1)).continuousAt.continuousWithinAt
  have hT : ContinuousOn (fun t => t * H.T sign.opposite (t - 1)) (Icc a b) :=
    continuousOn_id.mul ((hH.continuous sign.opposite).comp
      (continuousOn_id.sub continuousOn_const) (by
        intro t ht
        have : 1 < t := by linarith [hH.beta_gt_one, heps, ha, ht.1]
        exact sub_pos.mpr this))
  have hw : ContinuousOn (weightedHat H sign) (Icc a b) :=
    (continuousOn_id.pow 2).mul ((hH.continuous sign).mono (by
      intro t ht
      exact ha0.trans_le ht.1))
  have hs : ContinuousOn (perturbationSlope D d 0) (Icc a b) := by
    intro t ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    have hden : 0 < 1 + (t + 0) ^ d / Real.log D := by
      have : 0 ≤ (t + 0) ^ d / Real.log D :=
        div_nonneg (by simpa [add_zero] using Real.rpow_nonneg (ha0.trans_le ht.1).le d) hlog.le
      linarith
    unfold perturbationSlope
    fun_prop (disch := aesop)
  exact hp.mul (hT.sub (hw.mul hs))

private lemma continuousOn_qD_tailStrict
    {H : Section13HatLayers} {β D d Δ s σ : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hD : 1 < D) (hs : 1 < s) :
    ContinuousOn (qD H sign D d Δ) (Icc s σ) := by
  exact continuousOn_qD_Icc_of_contract hH sign hD hs

theorem numerical_moving_tail {H : Section13HatLayers}
    (hSource : Section13HatSourceContract H) (sign : ErrorSign) {M : ℝ}
    (hM : 4 ≤ M) (hHead : sourceRatioHead ≤ M) :
    ∀ D : ℝ, movingTailCutoff M ≤ D →
      M ≤ sourceSigma D 16 ∧
      ∀ s : ℝ, M ≤ s → s ≤ sourceSigma D 16 →
        (∫ t in s..sourceSigma D 16, qD H sign.opposite D 16 (1/2) t) <
          (1-1/sourceSigma D 16)^(1-(1/2 : ℝ)) * lambda H sign D 16 0 s := by
  let d : ℝ := 16
  let Δ : ℝ := 1/2
  have hΔ : Δ < 1 := by norm_num [Δ]
  have hH := hSource.toSection13HatContract
  let D₀ := movingTailCutoff M
  have hD₀ : 1 < D₀ := movingTailCutoff_gt_one M
  have hcert := numerical_asymptotic_certificate hSource sign hM hHead
  intro D hD
  rcases hcert D hD with ⟨hMσ, hlo, hhi⟩
  refine ⟨hMσ, ?_⟩
  intro s hs hssigma
  let σ := sourceSigma D d
  have hD1 : 1 < D := hD₀.trans_le hD
  have hlog : 0 < Real.log D := Real.log_pos hD1
  have hs2 : 2 < s := by linarith
  have hs0 : 0 < s := by linarith
  have hσ2 : 2 < σ := hs2.trans_le hssigma
  have hσ0 : 0 < σ := by linarith
  let c : ℝ := (1 - 1 / σ) ^ (1 - Δ)
  have hc0 : 0 < c := by
    apply Real.rpow_pos_of_pos
    exact sub_pos.mpr ((div_lt_one hσ0).mpr (by linarith : 1 < σ))
  have hp : 0 < 1 - Δ := sub_pos.mpr hΔ
  have hweight : ∀ t ∈ Icc s σ,
      ((t - 1) / t) ^ (1 - Δ) ≤ c := by
    intro t ht
    have ht0 : 0 < t := hs0.trans_le ht.1
    have ht1 : 1 < t := by linarith [hs2, ht.1]
    have hb0 : 0 ≤ (t - 1) / t := (div_pos (sub_pos.mpr ht1) ht0).le
    have hinv : 1 / σ ≤ 1 / t := one_div_le_one_div_of_le ht0 ht.2
    have hbase : (t - 1) / t ≤ 1 - 1 / σ := by
      calc
        (t - 1) / t = 1 - 1 / t := by field_simp [ne_of_gt ht0]
        _ ≤ 1 - 1 / σ := sub_le_sub_left hinv 1
    dsimp [c]
    exact Real.rpow_le_rpow hb0 hbase hp.le
  have hasymp : ∀ t ∈ Icc s σ,
      weightedHat H sign t * perturbationSlope D d 0 t ≤
        t * H.T sign.opposite (t - 1) *
          ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D)) := by
    intro t ht
    by_cases hr : t ≤ (Real.log D) ^ (1 / d)
    · exact hlo t (hs.trans ht.1) hr ht.2
    · exact hhi t (lt_of_not_ge hr) ht.2
  have hpoint : ∀ t ∈ Icc s σ,
      qD H sign.opposite D d Δ t ≤
        c * lambdaNegDerivStrict H sign D d t := by
    intro t ht
    have ht1 : 1 < t := by linarith [hs2, ht.1]
    have hd0 :=
      qD_le_lambdaNegDeriv_mul_weightStrict (Δ := Δ) hH sign hlog ht1 (hasymp t ht)
    have hneg0 : 0 ≤ lambdaNegDerivStrict H sign D d t := by
      have hp0 : 0 ≤ perturbation D d 0 t := by
        rw [perturbation]
        apply Real.rpow_nonneg
        have : 0 ≤ t ^ d / Real.log D :=
          div_nonneg (Real.rpow_nonneg (by linarith) _) hlog.le
        have : 0 ≤ (t + 0) ^ d / Real.log D := by simpa using this
        linarith
      unfold lambdaNegDerivStrict
      apply mul_nonneg hp0
      have hzfrac : (t ^ d / Real.log D) / (1 + t ^ d / Real.log D) ≤ 1 := by
        apply (div_le_one (by
          have : 0 ≤ t ^ d / Real.log D :=
            div_nonneg (Real.rpow_nonneg (by linarith) _) hlog.le
          linarith)).2
        linarith
      have hmain0 : 0 ≤ t * H.T sign.opposite (t - 1) :=
        (mul_pos (by linarith)
          (hH.positive sign.opposite (t - 1) (by linarith))).le
      rw [sub_nonneg]
      calc
        weightedHat H sign t * perturbationSlope D d 0 t ≤
            t * H.T sign.opposite (t - 1) *
              ((t ^ d / Real.log D) / (1 + t ^ d / Real.log D)) := hasymp t ht
        _ ≤ t * H.T sign.opposite (t - 1) := by
          exact mul_le_of_le_one_right hmain0 hzfrac
    exact hd0.trans (by
      rw [mul_comm c]
      exact mul_le_mul_of_nonneg_left (hweight t ht) hneg0)
  have hqcont : ContinuousOn (qD H sign.opposite D d Δ) (Icc s σ) :=
    continuousOn_qD_tailStrict hH sign.opposite hD1 (by linarith)
  have hdcont : ContinuousOn (lambdaNegDerivStrict H sign D d) (Icc s σ) :=
    continuousOn_lambdaNegDerivStrict (a := s) (b := σ) hH sign hlog (by
      cases sign <;> simp [ErrorSign.epsilon] <;> linarith [hs2])
  have hmono : (∫ t in s..σ, qD H sign.opposite D d Δ t) ≤
      ∫ t in s..σ, c * lambdaNegDerivStrict H sign D d t := by
    exact intervalIntegral.integral_mono_on hssigma
      (hqcont.intervalIntegrable_of_Icc hssigma)
      ((continuousOn_const.mul hdcont).intervalIntegrable_of_Icc hssigma) hpoint
  have hFTC : (∫ t in s..σ, lambdaNegDerivStrict H sign D d t) =
      lambda H sign D d 0 s - lambda H sign D d 0 σ := by
    have hderiv : ∀ t ∈ Ioo s σ,
        HasDerivAt (-lambda H sign D d 0)
          (lambdaNegDerivStrict H sign D d t) t := by
      intro t ht
      apply hasDerivAt_lambdaNegStrict hH sign hlog (by linarith [hs0, ht.1])
      cases sign <;> simp [ErrorSign.epsilon] <;> linarith [hs2, ht.1]
    have hfcont : ContinuousOn (-lambda H sign D d 0) (Icc s σ) := by
      intro t ht
      exact (hasDerivAt_lambdaNegStrict hH sign hlog (by linarith [hs0, ht.1]) (by
        cases sign <;> simp [ErrorSign.epsilon] <;> linarith [hs2, ht.1])).continuousAt.continuousWithinAt
    have hraw := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hssigma
      hfcont hderiv (hdcont.intervalIntegrable_of_Icc hssigma)
    simpa [σ, lambda_eq_perturb_mul_weightedHat, perturbation, sub_eq_add_neg,
      add_comm] using hraw
  have hlamσ : 0 < lambda H sign D d 0 σ := by
    exact lambda_pos H sign hD1 (by norm_num) hσ0 (hH.positive sign σ hσ0)
  calc
    (∫ t in s..σ, qD H sign.opposite D d Δ t) ≤
        ∫ t in s..σ, c * lambdaNegDerivStrict H sign D d t := hmono
    _ = c * (lambda H sign D d 0 s - lambda H sign D d 0 σ) := by
      rw [intervalIntegral.integral_const_mul, hFTC]
    _ < c * lambda H sign D d 0 s := by
      nlinarith [hc0, hlamσ]
    _ = (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
          lambda H sign D d 0 s := by
            rfl
#print axioms numerical_moving_tail
end ChenEffective
