import NumericalHatCompact
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma132SlackFinal

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology Real
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem numerical_hat_tail_slack {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    (1 / 72 : ℝ) ≤ lemma132HatTailSlack H := by
  let f := fun t : ℝ => H.T .minus (t - 1)
  have hi : IntegrableOn f (Ioi (3 : ℝ)) := integrableOn_lemma132HatTailSlack hH
  have hsub : Ioc (3 : ℝ) 4 ⊆ Ioi (3 : ℝ) := fun _ ht => ht.1
  have hint : IntervalIntegrable f volume 3 4 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (3 : ℝ) ≤ 4)).mpr
      (hi.mono_set hsub)
  have hpoint (t : ℝ) (ht : t ∈ Icc (3 : ℝ) 4) : (1 / 72 : ℝ) ≤ f t := by
    have hu2 : 2 ≤ t - 1 := by linarith only [ht.1]
    have hu3 : t - 1 ≤ 3 := by linarith only [ht.2]
    have hw := numerical_weighted_hat_initial hH.toSection13HatContract .minus hu2 hu3
    have hT : 0 ≤ H.T .minus (t - 1) := (hH.positive .minus _ (by linarith only [hu2])).le
    have hs := pow_le_pow_left₀ (show 0 ≤ t - 1 by linarith only [hu2]) hu3 2
    have hh := mul_le_mul_of_nonneg_right hs hT
    dsimp [weightedHat] at hw
    dsimp [f]
    nlinarith only [hw, hh]
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (3 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht3 : 3 < t := ht
    exact (hH.positive .minus _ (by linarith only [ht3])).le
  have htail := setIntegral_mono_set (s := Ioc (3 : ℝ) 4) (t := Ioi (3 : ℝ)) hi hn
    (Filter.Eventually.of_forall (fun _ ht => hsub ht))
  rw [← intervalIntegral.integral_of_le (by norm_num : (3 : ℝ) ≤ 4)] at htail
  calc
    _ = ∫ _t in (3 : ℝ)..4, (1 / 72 : ℝ) := by norm_num
    _ ≤ ∫ t in (3 : ℝ)..4, f t :=
      intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const hint hpoint
    _ ≤ _ := htail

private lemma pred_parityDomain_of_exact_threshold
    (N : ℕ) {x t : ℝ}
    (hN : 2 ≤ N) (hx : 2 + ((N % 2 : ℕ) : ℝ) ≤ x) (ht : t ∈ Ioi x) :
    t - 1 ∈ KappaOneModel.parityDomain 2 (N - 1) := by
  change x < t at ht
  have hflip : (N - 1) % 2 = 1 - N % 2 := by omega
  have hmod : N % 2 = 0 ∨ N % 2 = 1 := by omega
  rcases hmod with hmod | hmod
  · rw [hmod] at hx
    norm_num at hx
    unfold KappaOneModel.parityDomain
    rw [hflip, hmod]
    norm_num
    linarith
  · rw [hmod] at hx
    norm_num at hx
    unfold KappaOneModel.parityDomain
    rw [hflip, hmod]
    norm_num
    linarith

/-- The ordinary hat-tail identity at the closed even threshold. -/
private lemma integral_Ioi_hatTailIntegrand_minus_two
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    IntegrableOn (hatTailIntegrand H .minus) (Ioi (2 : ℝ)) ∧
      (∫ t in Ioi (2 : ℝ), hatTailIntegrand H .minus t) =
        weightedHat H .minus 2 := by
  let f : ℝ → ℝ := weightedHat H .minus
  let f' : ℝ → ℝ := fun t => -hatTailIntegrand H .minus t
  have hTcont : ContinuousAt (H.T .minus) 2 :=
    (hH.continuous .minus).continuousAt (isOpen_Ioi.mem_nhds (by norm_num))
  have hcont : ContinuousWithinAt f (Ici (2 : ℝ)) 2 := by
    exact ((continuousAt_id.pow 2).mul hTcont).continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (2 : ℝ), HasDerivAt f (f' x) x := by
    intro x hx
    simpa [f, f', hatTailIntegrand, neg_mul] using
      hH.dde .minus x (by
        have hx' : 2 < x := hx
        norm_num [ErrorSign.epsilon]
        exact hx')
  have hnonpos : ∀ x ∈ Ioi (2 : ℝ), f' x ≤ 0 := by
    intro x hx
    have hx' : 2 < x := hx
    dsimp only [f', hatTailIntegrand]
    exact neg_nonpos.mpr (mul_nonneg (by linarith [hx'] : 0 ≤ x)
      (hH.positive .plus (x - 1) (by linarith [hx'])).le)
  have hi : IntegrableOn f' (Ioi (2 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonpos hcont hderiv hnonpos
      (by simpa only [f] using hH.weighted_tendsto_zero .minus)
  have htail : IntegrableOn (hatTailIntegrand H .minus) (Ioi (2 : ℝ)) := by
    have hineg := hi.neg
    change IntegrableOn (fun t => -f' t) (Ioi (2 : ℝ)) at hineg
    exact hineg.congr (ae_of_all _ fun t => by simp [f', hatTailIntegrand])
  refine ⟨htail, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv hnonpos
    (by simpa only [f] using hH.weighted_tendsto_zero .minus)
  simpa only [f', MeasureTheory.integral_neg, zero_sub, neg_inj] using h

/-- Keeping the factor `t - 1` after cancellation only improves the ordinary
hat-tail bound.  At closed thresholds the endpoint identities are used. -/
private lemma shiftedHatTail_le_weightedHat
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (N : ℕ) (x : ℝ) (_hN : 2 ≤ N)
    (hx : 2 + ((N % 2 : ℕ) : ℝ) ≤ x) :
    IntegrableOn
        (fun t => (t - 1) * H.T (ErrorSign.ofDepth N).opposite (t - 1))
        (Ioi x) ∧
      (∫ t in Ioi x,
          (t - 1) * H.T (ErrorSign.ofDepth N).opposite (t - 1)) ≤
        weightedHat H (ErrorSign.ofDepth N) x := by
  have hx2 : 2 ≤ x := by
    have hmod0 : (0 : ℝ) ≤ ((N % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hshift_meas : AEStronglyMeasurable
      (fun t => (t - 1) * H.T (ErrorSign.ofDepth N).opposite (t - 1))
      (volume.restrict (Ioi x)) := by
    apply ContinuousOn.aestronglyMeasurable
    · apply (continuousOn_id.sub continuousOn_const).mul
      apply (hH.continuous (ErrorSign.ofDepth N).opposite).comp
        (continuousOn_id.sub continuousOn_const)
      intro t ht
      change x < t at ht
      change 0 < t - 1
      linarith
    · exact measurableSet_Ioi
  have norm_bound : ∀ᵐ t ∂(volume.restrict (Ioi x)),
      ‖(t - 1) * H.T (ErrorSign.ofDepth N).opposite (t - 1)‖ ≤
        hatTailIntegrand H (ErrorSign.ofDepth N) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hxt : x < t := ht
    have hT0 : 0 ≤ H.T (ErrorSign.ofDepth N).opposite (t - 1) :=
      (hH.positive _ _ (by linarith)).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) hT0)]
    dsimp only [hatTailIntegrand]
    exact mul_le_mul_of_nonneg_right (by linarith) hT0
  have point_bound : ∀ᵐ t ∂(volume.restrict (Ioi x)),
      (t - 1) * H.T (ErrorSign.ofDepth N).opposite (t - 1) ≤
        hatTailIntegrand H (ErrorSign.ofDepth N) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hxt : x < t := ht
    have hT0 : 0 ≤ H.T (ErrorSign.ofDepth N).opposite (t - 1) :=
      (hH.positive _ _ (by linarith)).le
    dsimp only [hatTailIntegrand]
    exact mul_le_mul_of_nonneg_right (by linarith) hT0
  rcases Nat.even_or_odd N with hEven | hOdd
  · have hsign : ErrorSign.ofDepth N = .minus := ErrorSign.ofDepth_of_even hEven
    by_cases hxeq : x = 2
    · subst x
      rw [hsign]
      rcases integral_Ioi_hatTailIntegrand_minus_two hH with ⟨hHatInt, hHatEq⟩
      have hShiftInt : IntegrableOn
          (fun t => (t - 1) * H.T .plus (t - 1)) (Ioi (2 : ℝ)) := by
        apply hHatInt.mono'
        · simpa [hsign, ErrorSign.opposite] using hshift_meas
        · simpa [hsign, ErrorSign.opposite] using norm_bound
      refine ⟨hShiftInt, ?_⟩
      calc
        (∫ t in Ioi (2 : ℝ), (t - 1) * H.T .plus (t - 1)) ≤
            ∫ t in Ioi (2 : ℝ), hatTailIntegrand H .minus t :=
          MeasureTheory.integral_mono_ae hShiftInt hHatInt (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            have hT0 : 0 ≤ H.T .plus (t - 1) :=
              (hH.positive _ _ (by linarith [show (2 : ℝ) < t from ht])).le
            dsimp only [hatTailIntegrand, ErrorSign.opposite]
            exact mul_le_mul_of_nonneg_right
              (by linarith [show (2 : ℝ) < t from ht]) hT0)
        _ = weightedHat H .minus 2 := hHatEq
    · have hxgt : 2 < x := lt_of_le_of_ne hx2 (Ne.symm hxeq)
      have htailCond : 2 + (ErrorSign.ofDepth N).epsilon < x := by
        rw [hsign]
        norm_num [ErrorSign.epsilon]
        exact hxgt
      have hHatInt := integrableOn_hatTailIntegrand_Ioi
        hH.toSection13HatContract (ErrorSign.ofDepth N) htailCond
      have hShiftInt := hHatInt.mono' hshift_meas norm_bound
      refine ⟨hShiftInt, ?_⟩
      calc
        (∫ t in Ioi x,
            (t - 1) * H.T (ErrorSign.ofDepth N).opposite (t - 1)) ≤
            ∫ t in Ioi x, hatTailIntegrand H (ErrorSign.ofDepth N) t :=
          MeasureTheory.integral_mono_ae hShiftInt hHatInt point_bound
        _ = weightedHat H (ErrorSign.ofDepth N) x :=
          integral_Ioi_hatTailIntegrand hH.toSection13HatContract _ htailCond
  · have hmod : N % 2 = 1 := Nat.odd_iff.mp hOdd
    have hsign : ErrorSign.ofDepth N = .plus := ErrorSign.ofDepth_of_odd hOdd
    rw [hmod] at hx
    norm_num at hx
    by_cases hx3 : x = 3
    · subst x
      rw [hsign]
      rcases lemma132_weightedHat_plus_three_endpoint_slack hH with ⟨hInt, hEq, _⟩
      refine ⟨by simpa only [ErrorSign.opposite] using hInt, ?_⟩
      change (∫ t in Ioi (3 : ℝ), (t - 1) * H.T .minus (t - 1)) ≤
        weightedHat H .plus 3
      rw [hEq]
      exact sub_le_self _ (lemma132HatTailSlack_pos hH).le
    · have hxgt : 3 < x := lt_of_le_of_ne hx (Ne.symm hx3)
      have htailCond : 2 + (ErrorSign.ofDepth N).epsilon < x := by
        rw [hsign]
        norm_num [ErrorSign.epsilon]
        exact hxgt
      have hHatInt := integrableOn_hatTailIntegrand_Ioi
        hH.toSection13HatContract (ErrorSign.ofDepth N) htailCond
      have hShiftInt := hHatInt.mono' hshift_meas norm_bound
      refine ⟨hShiftInt, ?_⟩
      calc
        (∫ t in Ioi x,
            (t - 1) * H.T (ErrorSign.ofDepth N).opposite (t - 1)) ≤
            ∫ t in Ioi x, hatTailIntegrand H (ErrorSign.ofDepth N) t :=
          MeasureTheory.integral_mono_ae hShiftInt hHatInt point_bound
        _ = weightedHat H (ErrorSign.ofDepth N) x :=
          integral_Ioi_hatTailIntegrand hH.toSection13HatContract _ htailCond

/-- Literal finite-layer coefficient L=144, uniform in depth and coordinate. -/
theorem numerical_finite_layer_hat
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∀ (N : ℕ) (x : ℝ), 1 ≤ N → x ∈ KappaOneModel.parityDomain 2 N →
      x * finiteSourceLayer 1 2 N x ≤ 144 * x ^ 2 * H.T (ErrorSign.ofDepth N) x := by
  let δ := lemma132HatTailSlack H
  let C : ℝ := 144
  have hδ : 0 < δ := lemma132HatTailSlack_pos hH
  have hδbound : (1 / 72 : ℝ) ≤ δ := numerical_hat_tail_slack hH
  have hC2 : 2 ≤ C := by norm_num [C]
  have hC0 : 0 ≤ C := by norm_num [C]
  have hCδ : 2 ≤ C * δ := by dsimp [C]; linarith only [hδbound]
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro x hN hxdom
      by_cases hN1 : N = 1
      · subst N
        have hbase := lemma132_base_one_direct_two hH x hxdom
        have hx1 : 1 < x := by
          change 2 - 1 < x at hxdom
          norm_num at hxdom
          exact hxdom
        have hweight0 : 0 ≤ x ^ 2 * H.T (ErrorSign.ofDepth 1) x :=
          mul_nonneg (sq_nonneg x) (hH.positive _ x (by linarith)).le
        calc
          x * finiteSourceLayer 1 2 1 x ≤
              2 * (x ^ 2 * H.T (ErrorSign.ofDepth 1) x) := by
                simpa only [mul_assoc] using hbase
          _ ≤ C * (x ^ 2 * H.T (ErrorSign.ofDepth 1) x) :=
            mul_le_mul_of_nonneg_right hC2 hweight0
          _ = C * x ^ 2 * H.T (ErrorSign.ofDepth 1) x := by ring
      · have hN2 : 2 ≤ N := by omega
        have hpred : 1 ≤ N - 1 := by omega
        have hsignPred : ErrorSign.ofDepth (N - 1) =
            (ErrorSign.ofDepth N).opposite :=
          ErrorSign.ofDepth_pred_eq_opposite (by omega)
        have predecessor_bound (y : ℝ)
            (hy : 2 + ((N % 2 : ℕ) : ℝ) ≤ y) :
            ∀ t ∈ Ioi y,
              finiteSourceLayer 1 2 (N - 1) (t - 1) ≤
                C * ((t - 1) *
                  H.T (ErrorSign.ofDepth N).opposite (t - 1)) := by
          intro t ht
          have htdom := pred_parityDomain_of_exact_threshold N hN2 hy ht
          have hIH := ih (N - 1) (by omega) (t - 1) hpred htdom
          rw [hsignPred] at hIH
          have ht1 : 0 < t - 1 := by
            have hmod0 : (0 : ℝ) ≤ ((N % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
            change y < t at ht
            linarith
          apply le_of_mul_le_mul_left _ ht1
          calc
            (t - 1) * finiteSourceLayer 1 2 (N - 1) (t - 1) ≤
                C * (t - 1) ^ 2 *
                  H.T (ErrorSign.ofDepth N).opposite (t - 1) := hIH
            _ = (t - 1) *
                (C * ((t - 1) *
                  H.T (ErrorSign.ofDepth N).opposite (t - 1))) := by ring
        have high_bound : ∀ y : ℝ,
            2 + ((N % 2 : ℕ) : ℝ) ≤ y →
            y * finiteSourceLayer 1 2 N y ≤
              C * y ^ 2 * H.T (ErrorSign.ofDepth N) y := by
          intro y hy
          rcases Lemma132FiniteTailIdentity_exactRecursionThreshold N y hN2 hy with
            ⟨hFinInt, hFinTail⟩
          rcases shiftedHatTail_le_weightedHat hH N y hN2 hy with
            ⟨hShiftInt, hShiftTail⟩
          have hpoint := predecessor_bound y hy
          have hIntegral :
              (∫ t in Ioi y, finiteSourceLayer 1 2 (N - 1) (t - 1)) ≤
                ∫ t in Ioi y,
                  C * ((t - 1) *
                    H.T (ErrorSign.ofDepth N).opposite (t - 1)) := by
            apply MeasureTheory.integral_mono_ae hFinInt (hShiftInt.const_mul C)
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact hpoint t ht
          rw [MeasureTheory.integral_const_mul] at hIntegral
          calc
            y * finiteSourceLayer 1 2 N y =
                ∫ t in Ioi y, finiteSourceLayer 1 2 (N - 1) (t - 1) := hFinTail
            _ ≤ C * (∫ t in Ioi y,
                  (t - 1) * H.T (ErrorSign.ofDepth N).opposite (t - 1)) := hIntegral
            _ ≤ C * weightedHat H (ErrorSign.ofDepth N) y := by
              exact mul_le_mul_of_nonneg_left hShiftTail hC0
            _ = C * y ^ 2 * H.T (ErrorSign.ofDepth N) y := by
              rw [weightedHat]
              ring
        rcases Nat.even_or_odd N with hEven | hOdd
        · have hmod : N % 2 = 0 := Nat.even_iff.mp hEven
          apply high_bound x
          unfold KappaOneModel.parityDomain at hxdom
          rw [hmod] at hxdom ⊢
          norm_num at hxdom ⊢
          exact hxdom
        · have hmod : N % 2 = 1 := Nat.odd_iff.mp hOdd
          by_cases hx3 : x ≤ 3
          · have hx1 : 1 < x := by
              unfold KappaOneModel.parityDomain at hxdom
              rw [hmod] at hxdom
              norm_num at hxdom
              exact hxdom
            have hsource := finiteSourceLayer_odd_lowStrip_exact
              N x (by omega) hmod hx1 hx3
            rcases Lemma132FiniteTailIdentity_exactRecursionThreshold N 3 hN2
                (by rw [hmod]; norm_num) with ⟨hFinInt3, hFinTail3⟩
            rcases lemma132_weightedHat_plus_three_endpoint_slack hH with
              ⟨hShiftInt3, hShiftEq3, hWeightEq3⟩
            have hpoint3 := predecessor_bound 3 (by rw [hmod]; norm_num)
            have hIntegral3 :
                (∫ t in Ioi (3 : ℝ), finiteSourceLayer 1 2 (N - 1) (t - 1)) ≤
                  ∫ t in Ioi (3 : ℝ),
                    C * ((t - 1) * H.T .minus (t - 1)) := by
              apply MeasureTheory.integral_mono_ae hFinInt3
                (hShiftInt3.const_mul C)
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              simpa [ErrorSign.ofDepth_of_odd hOdd, ErrorSign.opposite] using hpoint3 t ht
            rw [MeasureTheory.integral_const_mul, hShiftEq3, hWeightEq3] at hIntegral3
            have hAtThreeSlack :
                3 * finiteSourceLayer 1 2 N 3 ≤ C * (1 - δ) := by
              rw [hFinTail3]
              simpa [δ] using hIntegral3
            have hsign : ErrorSign.ofDepth N = .plus :=
              ErrorSign.ofDepth_of_odd hOdd
            have hhatx := hH.initial_plus x (by linarith) (by norm_num; exact hx3)
            have hweightedx : x ^ 2 * H.T .plus x = 1 := by
              norm_num [weightedHat] at hhatx ⊢
              exact hhatx
            calc
              x * finiteSourceLayer 1 2 N x =
                  (3 - x) + 3 * finiteSourceLayer 1 2 N 3 := hsource
              _ ≤ (3 - x) + C * (1 - δ) := add_le_add (le_refl _) hAtThreeSlack
              _ ≤ 2 + C * (1 - δ) := by linarith
              _ ≤ C := by nlinarith
              _ = C * (x ^ 2 * H.T .plus x) := by rw [hweightedx, mul_one]
              _ = C * x ^ 2 * H.T (ErrorSign.ofDepth N) x := by rw [hsign]; ring
          · apply high_bound x
            rw [hmod]
            norm_num
            exact le_of_not_ge hx3



theorem numerical_finite_predecessor {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) {N : ℕ} {s : ℝ} (hN : 2 ≤ N) (hs : 2 ≤ s)
    (hsdom : s - 1 ∈ KappaOneModel.parityDomain 2 (N - 1)) :
    finiteSourceLayer 1 2 (N - 1) (s - 1) ≤
      144 * ((s - 1) * H.T (ErrorSign.ofDepth N).opposite (s - 1)) := by
  have hh := numerical_finite_layer_hat hH (N - 1) (s - 1) (by omega) hsdom
  rw [ErrorSign.ofDepth_pred_eq_opposite (by omega : 1 ≤ N)] at hh
  apply le_of_mul_le_mul_left _ (show 0 < s - 1 by linarith only [hs])
  calc
    _ ≤ _ := hh
    _ = (s - 1) * (144 * ((s - 1) * H.T (ErrorSign.ofDepth N).opposite (s - 1))) := by ring

/-- The same literal L=144 holds at the closed even endpoint. -/
theorem numerical_finite_even_endpoint
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∀ M : ℕ, Even M → 2 ≤ M → finiteSourceLayer 1 2 (M - 1) 1 ≤
      144 * H.T (ErrorSign.ofDepth M).opposite 1 := by
  let L : ℝ := 144
  have hmajor := numerical_finite_layer_hat hH
  intro M hM hM2
  have hpred : (M - 1) % 2 = 1 := by
    have hm0 : M % 2 = 0 := Nat.even_iff.mp hM
    omega
  have hMpred : 1 ≤ M - 1 := by omega
  let F : ℝ → ℝ := fun x => x * finiteSourceLayer 1 2 (M - 1) x
  let G : ℝ → ℝ := fun x => L * x ^ 2 * H.T (ErrorSign.ofDepth (M - 1)) x
  have hclosed : (1 : ℝ) ∈ KappaOneModel.closedDomain 2 (M - 1) := by
    simp [KappaOneModel.closedDomain, KappaOneModel.eps, hpred]
    norm_num
  have hFC : ContinuousWithinAt F (KappaOneModel.closedDomain 2 (M - 1)) 1 := by
    apply continuousWithinAt_id.mul
    exact (MathlibNt.SieveTheory.finiteSourceLayer_continuousOn_closedDomain (by norm_num) (M - 1))
      1 hclosed
  have hGC : ContinuousAt G 1 := by
    dsimp [G]
    have hTcont := (hH.continuous (ErrorSign.ofDepth (M - 1))).continuousAt
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
    exact (continuousAt_const.mul (continuousAt_id.pow 2)).mul hTcont
  have hsub : Set.Ioi (1 : ℝ) ⊆ KappaOneModel.closedDomain 2 (M - 1) := by
    intro x hx
    change (1 : ℝ) < x at hx
    simp [KappaOneModel.closedDomain, KappaOneModel.eps, hpred]
    linarith
  have hFt : Tendsto F (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 (F 1)) :=
    hFC.mono_left (nhdsWithin_mono 1 hsub)
  have hGt : Tendsto G (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 (G 1)) :=
    hGC.tendsto.mono_left inf_le_left
  have hEventually : ∀ᶠ x in 𝓝[Set.Ioi (1 : ℝ)] 1, F x ≤ G x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxdom : x ∈ KappaOneModel.parityDomain 2 (M - 1) := by
      simp [KappaOneModel.parityDomain, hpred]
      norm_num
      exact hx
    exact hmajor (M - 1) x hMpred hxdom
  have hlim : F 1 ≤ G 1 := le_of_tendsto_of_tendsto hFt hGt hEventually
  dsimp [F, G] at hlim
  rw [ErrorSign.ofDepth_pred_eq_opposite (by omega : 1 ≤ M)] at hlim
  simpa using hlim



#print axioms numerical_hat_tail_slack
#print axioms numerical_finite_layer_hat
#print axioms numerical_finite_predecessor
#print axioms numerical_finite_even_endpoint
end ChenEffective
