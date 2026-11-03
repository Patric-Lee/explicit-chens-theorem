import NumericalReverseRatio
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1027ExplicitAdjoint
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection10CutoffCorrectedRatio

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open Section10CanonicalXi Section10Lemma1028FirstCrossing
open Section10Equation1056UniformStationary Section10MinusFirstCrossingProducer
open CutoffCorrectedRatio BridgeAssembly Section13QhatMajorantClosure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem numerical_xi_compact {s : ℝ} (hs : 3 ≤ s) (hs30 : s ≤ 30) : xi s ≤ 30 := by
  have hseries := Real.pow_div_factorial_le_exp (30 : ℝ) (by norm_num) 3
  norm_num [Nat.factorial] at hseries
  have heta : (30 : ℝ) ≤ eta 30 := by
    rw [eta_eq_div (by norm_num : (30 : ℝ) ≠ 0)]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 30)).mpr
    linarith only [hseries]
  by_contra hn
  have hh := eta_strictMonoOn (by norm_num : (0 : ℝ) ≤ 30)
    (xi_pos (show 1 < s by linarith only [hs])).le (lt_of_not_ge hn)
  rw [eta_xi, max_eq_left (show 1 ≤ s by linarith only [hs])] at hh
  exact (not_lt_of_ge (hs30.trans heta)) hh

/-- A numerical forward majorant: cMinus=1152, A=2, cutoff=exp(2309).
The compact seed uses xi≤30, rather than a compactness-selected bound. -/
noncomputable def numericalForwardMajorant {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) : CutoffMajorant (section13Qhat H) := by
  let h := section13QhatFirstCrossingData hH
  let h27 := section13Qhat_lemma1027AdjointRComparison hH
  let S := stationaryCutoff h27
  have hS30 : S ≤ 30 := by
    change max (5 : ℝ) (max (2 * 2 + 2) (Real.exp 2 + 21)) ≤ 30
    have := numerical_exp_two_le_nine
    exact max_le (by norm_num) (max_le (by norm_num) (by linarith))
  have hSnum : Real.exp 2 + 21 ≤ S := stationaryCutoff_ge_numeric h27
  have hβS : (3 : ℝ) < S := by linarith [Real.exp_pos 2]
  have hβoneS : (3 : ℝ) + 1 ≤ S := by linarith [Real.exp_pos 2]
  have hinitial : ∀ u ∈ Icc (3 : ℝ) S,
      normalizedMinusBase (section13Qhat H) xi u < 1152 := by
    intro u hu
    have hu0 : 0 < u := by linarith only [hu.1]
    have hQ := section13Qhat_pos hH.toSection13HatContract hu0
    have hQm := section13Qhat_pos hH.toSection13HatContract
      (show 0 < u-1 by linarith only [hu.1])
    have hxi := numerical_xi_compact hu.1 (hu.2.trans hS30)
    have hn : -(section13Qhat H (u-1)) / (u * section13Qhat H u) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hQm.le) (mul_pos hu0 hQ).le
    have hd : 0 ≤ 2/u := by positivity
    unfold normalizedMinusBase
    linarith only [hn, hd, hxi]
  have hglobal : ∀ s, 4 ≤ s →
      normalizedMinusBase (section13Qhat H) xi s - 1152 ≤ 0 := by
    intro v hv4
    by_cases hvS : v ≤ S
    · have hv3 : 3 ≤ v := by linarith only [hv4]
      linarith only [hinitial v ⟨hv3, hvS⟩]
    · by_contra hn
      have hvreach : (1152 : ℝ) ≤ normalizedMinusBase (section13Qhat H) xi v := by
        linarith only [hn]
      obtain ⟨w, hSw⟩ := minusFirstCrossing_of_reaches h hβS hβoneS hinitial
        (lt_of_not_ge hvS).le hvreach
      exact no_uniform_minusFirstCrossing h rfl h27 (by norm_num) (by norm_num) w hSw
  have hT4 : (4 : ℝ) ≤ Real.exp 2309 := by
    linarith only [Real.add_one_le_exp (2309 : ℝ)]
  refine { xi := xi
           cMinus := 1152
           cutoff := Real.exp 2309
           A := 2
           four_le_cutoff := hT4
           one_le_A := by norm_num
           majorizes_log := ?_
           envelope_slope_nonpos := ?_ }
  · intro s hs
    have hs4 := hT4.trans hs
    have hs0 : 0 < s := by linarith only [hs4]
    have hlog : 2309 ≤ Real.log s := (Real.le_log_iff_exp_le hs0).mpr hs
    have hse : Real.exp 1 ≤ s :=
      (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2309)).trans hs
    have hxi := log_lt_xi hse
    have ht : 2/s ≤ 2 := (div_le_iff₀ hs0).mpr (by linarith only [hs4])
    rw [Real.log_mul (Real.exp_ne_zero 1) hs0.ne', Real.log_exp]
    norm_num only [one_div]
    linarith only [hxi, hlog, ht]
  · intro s hs
    have hs4 := hT4.trans hs
    have hs0 : 0 < s := by linarith only [hs4]
    have hRs := section13Qhat_pos hH.toSection13HatContract hs0
    have hn := hglobal s hs4
    have heq : -(section13Qhat H (s-1)) +
        s * (xi s - 1152 - 2/s) * section13Qhat H s =
        (s * section13Qhat H s) *
          (normalizedMinusBase (section13Qhat H) xi s - 1152) := by
      unfold normalizedMinusBase
      field_simp [hs0.ne', hRs.ne']
      ring
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_pos hs0 hRs).le hn

theorem numerical_Qhat_forward_shift {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) {s : ℝ} (hs : Real.exp 2309 ≤ s) :
    section13Qhat H s ≤ 2 / (s * Real.log (Real.exp 1 * s)) * section13Qhat H (s-1) := by
  exact section10_unitShift_after_cutoff (section13_bridgeAtThree hH .plus).dde
    (numericalForwardMajorant hH) hs

#print axioms numericalForwardMajorant
noncomputable def numericalHatBridge {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) (sign : ErrorSign) :
    Section13HatSection10BridgeAtThree H sign where
  Qhat := section13Qhat H
  dde := (section13_bridgeAtThree hH sign).dde
  K := 51200000000
  one_le_K := by norm_num
  hat_le := by
    intro s hs
    have hs0 : 0 < s := by linarith only [hs]
    have hQ := (section13Qhat_pos hH.toSection13HatContract hs0).le
    have hp := (hH.positive .plus s hs0).le
    have hm := (hH.positive .minus s hs0).le
    have hsmall : H.T sign s ≤ section13Qhat H s := by
      cases sign <;> dsimp [section13Qhat] <;> linarith only [hp, hm]
    exact hsmall.trans (by nlinarith only [hQ])
  Q_le := fun s hs => numerical_Qhat_le_hat hH sign hs

#print axioms numerical_Qhat_forward_shift
end ChenEffective
