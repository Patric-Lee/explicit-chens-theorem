import NumericalReverseEnvelope

open scoped Classical BigOperators Interval
open Set Filter MeasureTheory Topology Real
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open Section10CanonicalXi
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private lemma xi_sub_two_log_antitone_exp_two :
    AntitoneOn (fun s : ℝ => xi s - 2 * Real.log s) (Ici (Real.exp 2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (Real.exp 2))
  · apply xi_continuous.continuousOn.sub
    intro s hs
    exact (Real.continuousAt_log (ne_of_gt ((Real.exp_pos 2).trans_le hs))).const_mul 2
      |>.continuousWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    have hspos : 0 < s := (Real.exp_pos 2).trans hs
    have hs1 : 1 < s :=
      (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans hs
    exact ((xi_hasDerivAt hs1).differentiableAt.sub
      ((Real.hasDerivAt_log (ne_of_gt hspos)).const_mul 2).differentiableAt).differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    have hs' : Real.exp 2 ≤ s := hs.le
    have hspos : 0 < s := (Real.exp_pos 2).trans_le hs'
    have hs1 : 1 < s :=
      (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le hs'
    have hderiv : deriv (fun u : ℝ => xi u - 2 * Real.log u) s =
        deriv xi s - 2 / s := by
      simpa only [Pi.sub_def, xi_deriv hs1, div_eq_mul_inv] using
        ((xi_hasDerivAt hs1).sub
          ((Real.hasDerivAt_log (ne_of_gt hspos)).const_mul 2)).deriv
    rw [hderiv]
    exact sub_nonpos.mpr (xi_deriv_le_two_div hs')

private lemma xi_le_two_log_add_exp_two {s : ℝ} (hs : Real.exp 2 ≤ s) :
    xi s ≤ xi (Real.exp 2) + 2 * Real.log s := by
  have h := xi_sub_two_log_antitone_exp_two
    (show Real.exp 2 ∈ Ici (Real.exp 2) by simp)
    (show s ∈ Ici (Real.exp 2) from hs) hs
  dsimp at h
  rw [Real.log_exp] at h
  linarith


theorem numerical_xi_exp_two : xi (Real.exp 2) ≤ (8 : ℝ) := by
  have hs1 : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hseries := Real.pow_div_factorial_le_exp (8 : ℝ) (by norm_num) 3
  norm_num [Nat.factorial] at hseries
  have heta : Real.exp 2 ≤ eta 8 := by
    rw [eta_eq_div (by norm_num : (8 : ℝ) ≠ 0)]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    linarith only [hseries, numerical_exp_two_le_nine]
  by_contra hn
  have hh := eta_strictMonoOn (by norm_num : (0 : ℝ) ≤ 8) (xi_pos hs1).le (lt_of_not_ge hn)
  rw [eta_xi, max_eq_left hs1.le] at hh
  exact (not_lt_of_ge heta) hh

theorem numerical_xi_phase {s : ℝ} (hs : 10 ≤ s) :
    xi s + numericalReverseSlope - 2 / s ≤ (numericalReverseSlope + 10) * Real.log (Real.exp 1 * s) := by
  have hs0 : 0 < s := by linarith only [hs]
  have hse : Real.exp 2 ≤ s := numerical_exp_two_le_nine.trans (by linarith only [hs])
  have hxi := (xi_le_two_log_add_exp_two hse).trans
    (add_le_add numerical_xi_exp_two (le_refl (2 * Real.log s)))
  have hl : 0 ≤ Real.log s := Real.log_nonneg (by linarith only [hs])
  have he := compactHatLower_pos (m := 10) (by norm_num)
  have hc : 0 ≤ numericalReverseSlope := by unfold numericalReverseSlope; positivity
  have hd : 0 ≤ 2 / s := by positivity
  rw [Real.log_mul (Real.exp_ne_zero 1) hs0.ne', Real.log_exp]
  have hh := mul_nonneg hc hl
  nlinarith only [hxi, hl, hh, hd]

theorem numerical_Qhat_unit_shift {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 10 ≤ s) :
    section13Qhat H (s - 1) ≤ (numericalReverseSlope + 10) *
      (s * Real.log (Real.exp 1 * s)) * section13Qhat H s := by
  have henv := numerical_reverse_envelope hH s hs
  have hphase := numerical_xi_phase hs
  have hs0 : 0 < s := by linarith only [hs]
  have hQ0 := (section13Qhat_pos hH.toSection13HatContract hs0).le
  have hm := mul_le_mul_of_nonneg_right hphase (mul_nonneg hs0.le hQ0)
  nlinarith only [henv, hm]

private opaque reverseRatioCapCertificate : {r : ℕ // r = 51200 * 10075} :=
  ⟨51200 * 10075, rfl⟩

def reverseRatioCap : ℕ := reverseRatioCapCertificate.1

theorem reverseRatioCap_nat_eq : reverseRatioCap = 51200 * 10075 :=
  reverseRatioCapCertificate.2

theorem reverseRatioCap_eq : (reverseRatioCap : ℝ) = 51200 * (numericalReverseSlope + 10) := by
  norm_num [reverseRatioCap_nat_eq, numericalReverseSlope, compactHatLower]

theorem numerical_reverse_ratio {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (sign : ErrorSign) {s σ : ℝ} (hs : 2 ≤ s) (hsσ : s ≤ σ) :
    proposition131iiiReverseRatio H sign s ≤ (reverseRatioCap : ℝ) *
      (σ * Real.log (Real.exp 1 * σ)) := by
  have hs0 : 0 < s := by linarith only [hs]
  have hσ0 : 0 < σ := hs0.trans_le hsσ
  have hlogs : 1 ≤ Real.log (Real.exp 1 * s) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) hs0.ne', Real.log_exp]
    have hh := Real.log_nonneg (show 1 ≤ s by linarith only [hs])
    linarith only [hh]
  have hlogσ : Real.log (Real.exp 1 * s) ≤ Real.log (Real.exp 1 * σ) :=
    Real.log_le_log (mul_pos (Real.exp_pos 1) hs0) (mul_le_mul_of_nonneg_left hsσ (Real.exp_pos 1).le)
  have hprod := mul_le_mul hsσ hlogσ (by linarith only [hlogs]) hσ0.le
  have hr0 : (0 : ℝ) ≤ reverseRatioCap := Nat.cast_nonneg _
  have hT0 : 0 < H.T sign s := hH.positive sign s hs0
  by_cases hlarge : 10 ≤ s
  · have hn : H.T sign.opposite (s - 1) ≤ section13Qhat H (s - 1) := by
      have hp := (hH.positive .plus (s - 1) (by linarith only [hs])).le
      have hm := (hH.positive .minus (s - 1) (by linarith only [hs])).le
      cases sign <;> dsimp [section13Qhat, ErrorSign.opposite] <;> linarith only [hp, hm]
    have hshift := numerical_Qhat_unit_shift hH hlarge
    have hcomp := numerical_Qhat_le_hat hH sign (by linarith only [hlarge])
    have he := compactHatLower_pos (m := 10) (by norm_num)
    have hA0 : 0 ≤ numericalReverseSlope + 10 := by unfold numericalReverseSlope; positivity
    have hh := mul_le_mul_of_nonneg_left hcomp
      (mul_nonneg hA0 (mul_nonneg hs0.le (by linarith only [hlogs])))
    unfold proposition131iiiReverseRatio
    apply (div_le_iff₀ hT0).mpr
    have hmono := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hr0) hT0.le
    rw [reverseRatioCap_eq] at hmono ⊢
    nlinarith only [hn, hshift, hh, hmono]
  · have hraw : proposition131iiiReverseRatio H sign s ≤ reverseRatioCap := by
      by_cases hs4 : 4 ≤ s
      · have hn : H.T sign.opposite (s - 1) ≤ section13Qhat H (s - 1) := by
          have hp := (hH.positive .plus (s - 1) (by linarith only [hs])).le
          have hm := (hH.positive .minus (s - 1) (by linarith only [hs])).le
          cases sign <;> dsimp [section13Qhat, ErrorSign.opposite] <;> linarith only [hp, hm]
        have hshift := relative_Qhat_unit_step hH.toSection13HatContract hs4 (le_of_not_ge hlarge)
        have hcomp := numerical_Qhat_le_hat hH sign (by linarith only [hs4])
        have hh := mul_le_mul_of_nonneg_left hcomp (by norm_num : (0 : ℝ) ≤ 968)
        have hc : (968 : ℝ) * 51200 ≤ reverseRatioCap := by norm_num [reverseRatioCap_nat_eq]
        have hh' := mul_le_mul_of_nonneg_right hc hT0.le
        unfold proposition131iiiReverseRatio
        apply (div_le_iff₀ hT0).mpr
        nlinarith only [hn, hshift, hh, hh']
      · have hbound := numerical_hat_compact_four hH.toSection13HatContract sign hs (le_of_not_ge hs4)
        have hn := numerical_hat_upper_two hH.toSection13HatContract sign.opposite
          (show 1 ≤ s - 1 by linarith only [hs])
        have hh : proposition131iiiReverseRatio H sign s ≤ 25600 := by
          unfold proposition131iiiReverseRatio
          apply (div_le_iff₀ hT0).mpr
          linarith only [hbound, hn]
        exact hh.trans (by norm_num [reverseRatioCap_nat_eq])
    have hfactor : 1 ≤ σ * Real.log (Real.exp 1 * σ) := by
      have hh := mul_le_mul (show (1 : ℝ) ≤ σ by linarith only [hs, hsσ]) (hlogs.trans hlogσ)
        (by norm_num : (0 : ℝ) ≤ 1) hσ0.le
      norm_num only [one_mul] at hh
      exact hh
    exact hraw.trans (le_mul_of_one_le_right hr0 hfactor)

#print axioms numerical_reverse_ratio
end ChenEffective
