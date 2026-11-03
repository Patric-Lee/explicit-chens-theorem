import NumericalHatComparison
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1028ReverseEnvelope

open scoped Classical BigOperators Interval
open Set Filter MeasureTheory Topology Real
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open BridgeAssembly Section10Lemma1028 Section10Lemma1028FirstCrossing Section10CanonicalXi
open Section10Lemma1028PlusAssembly Section10Equation1053NonCircular Section10Equation1055SourceExpansion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem numerical_exp_two_le_nine : Real.exp 2 ≤ (9 : ℝ) := by
  have he : Real.exp 2 = (Real.exp 1) ^ (2 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ = (Real.exp 1) ^ (2 : ℕ) := he
    _ ≤ (3 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ (Real.exp_pos 1).le
      (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 3)) 2
    _ = 9 := by norm_num

noncomputable def numericalReverseSlope : ℝ := 1 / compactHatLower 10 + 65

theorem numerical_Qhat_initial_slope {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {u : ℝ} (hu : u ∈ Icc (3 : ℝ) 10) :
    -normalizedMinusBase (section13Qhat H) xi u ≤ 1 / compactHatLower 10 + 1 := by
  have he := compactHatLower_pos (m := 10) (by norm_num)
  have hQu : 0 < section13Qhat H u := section13Qhat_pos hH.toSection13HatContract (by linarith only [hu.1])
  have hqp := numerical_hat_upper_two hH.toSection13HatContract .plus
    (show 1 ≤ u - 1 by linarith only [hu.1])
  have hqm := numerical_hat_upper_two hH.toSection13HatContract .minus
    (show 1 ≤ u - 1 by linarith only [hu.1])
  have hlp := numerical_hat_compact hH.toSection13HatContract (m := 10) (by norm_num) .plus
    (by linarith only [hu.1]) hu.2
  have hlm := numerical_hat_compact hH.toSection13HatContract (m := 10) (by norm_num) .minus
    (by linarith only [hu.1]) hu.2
  have hQlow : 2 * compactHatLower 10 ≤ section13Qhat H u := by
    unfold section13Qhat
    linarith only [hlp, hlm]
  have hQhigh : section13Qhat H (u - 1) ≤ 4 := by
    unfold section13Qhat
    linarith only [hqp, hqm]
  have hden : 0 < u * section13Qhat H u := mul_pos (by linarith only [hu.1]) hQu
  have hratio : section13Qhat H (u - 1) / (u * section13Qhat H u) ≤ 1 / compactHatLower 10 := by
    apply (div_le_div_iff₀ hden he).mpr
    have hh := mul_le_mul_of_nonneg_left hQlow (show 0 ≤ u by linarith only [hu.1])
    have hh' := mul_le_mul_of_nonneg_right hu.1 he.le
    have hn := mul_le_mul_of_nonneg_right hQhigh he.le
    nlinarith only [hh, hh', hn, he.le]
  have hxi : 0 ≤ xi u := (xi_pos (by linarith only [hu.1])).le
  have htwo : 2 / u ≤ (1 : ℝ) := (div_le_one (by linarith only [hu.1])).mpr (by linarith only [hu.1])
  unfold normalizedMinusBase
  rw [neg_div]
  linarith only [hratio, hxi, htwo]

theorem numerical_reverse_envelope {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∀ s : ℝ, 10 ≤ s →
      0 ≤ -section13Qhat H (s - 1) +
        s * (xi s + numericalReverseSlope - 2 / s) * section13Qhat H s := by
  let h : FirstCrossingDDEApparatus (section13Qhat H) 3 :=
    { adjoint := section13AdjointPlus
      beta_ge_one := by norm_num
      continuous := (section13Qhat_continuousOn hH.toSection13HatContract).mono (by
        intro s hs
        norm_num at hs ⊢
        linarith)
      positive := by
        intro s hs
        exact section13Qhat_pos hH.toSection13HatContract (by linarith)
      original_dde := by
        intro s hs
        exact section13Qhat_dde hH.toSection13HatContract hs
      adjoint_positive := by
        intro s hs
        dsimp [section13AdjointPlus]
        nlinarith [sq_nonneg (s - 1)]
      adjoint_dde := by
        intro s _hs
        exact section13AdjointPlus_dde s
      pairing_zero := by
        intro s hs
        have hz := section13Qhat_pairing_zero hH hs
        have heq := sub_eq_zero.mp hz
        simpa [section10SignedPairing, section13AdjointPlus] using heq }
  have hadj : h.adjoint = explicitKappaOneAdjointPlus := by funext s; rfl
  have he := compactHatLower_pos (m := 10) (by norm_num)
  have hc64 : (64 : ℝ) ≤ numericalReverseSlope := by
    have hh : 0 ≤ 1 / compactHatLower 10 := by positivity
    unfold numericalReverseSlope
    linarith only [hh]
  have hinitial : ∀ u ∈ Icc (3 : ℝ) 10,
      0 < normalizedMinusBase (section13Qhat H) xi u + numericalReverseSlope := by
    intro u hu
    have hh := numerical_Qhat_initial_slope hH hu
    unfold numericalReverseSlope
    linarith only [hh]
  have hproducer := producesPlusFirstCrossing h (by norm_num : (3 : ℝ) < 10)
    (by norm_num : (3 : ℝ) + 1 ≤ 10) hinitial
  have hslope : ∀ s : ℝ, 10 ≤ s →
      0 ≤ normalizedMinusBase (section13Qhat H) xi s + numericalReverseSlope := by
    intro s hs
    by_contra hv
    have hv' : normalizedMinusBase (section13Qhat H) xi s + numericalReverseSlope < 0 := lt_of_not_ge hv
    obtain ⟨w, hSw⟩ := hproducer s hs hv'.le
    have hstrict := equation1055_internal_strict hc64
      ((show Real.exp 2 + 1 ≤ (10 : ℝ) by linarith only [numerical_exp_two_le_nine]).trans hSw)
    have hupper := plusFirstCrossing_scalarRatio_le_one h hadj w
    exact (not_lt_of_ge hupper) hstrict
  intro s hs
  have hs0 : 0 < s := by linarith only [hs]
  have hRs : 0 < section13Qhat H s := section13Qhat_pos hH.toSection13HatContract hs0
  have hn := hslope s hs
  have heq : -section13Qhat H (s - 1) + s * (xi s + numericalReverseSlope - 2 / s) * section13Qhat H s =
      (s * section13Qhat H s) * (normalizedMinusBase (section13Qhat H) xi s + numericalReverseSlope) := by
    unfold normalizedMinusBase
    field_simp [hs0.ne', hRs.ne']
    ring
  rw [heq]
  exact mul_nonneg (mul_pos hs0 hRs).le hn

#print axioms numerical_reverse_envelope
end ChenEffective
