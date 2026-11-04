import NumericalMixedInduction

namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiFiniteContinuousLayers SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem mixed_window_error_le {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {D : ℕ} (hD : 2 ≤ D) {s : ℝ} (hs : 3 / 2 ≤ s) (hs5 : s ≤ 5)
    (N : ℕ) (hsdom : s ∈ KappaOneModel.parityDomain 2 N) :
    mixedError H N D 16 (1 / 2) s ≤
      2 * (errorEnvelope H N D 16 s * (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  have hD1 : (1 : ℝ) < D := by exact_mod_cast (show 1 < D by omega)
  have hL : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have hs0 : 0 < s := by linarith only [hs]
  have hE : Real.exp (-12288 : ℝ) ≤ errorEnvelope H N D 16 s := by
    by_cases hs2 : 2 ≤ s
    · exact polynomial_compact_hat_floor hH.toSection13HatContract hD1 N hs2 (by linarith only [hs5])
    · have ho : Odd N := by
        by_contra hn
        have he := Nat.not_odd_iff_even.mp hn
        have hh : 2 ≤ s := by simpa [KappaOneModel.parityDomain, Nat.even_iff.mp he] using hsdom
        exact hs2 hh
      have hf : Real.exp (-12288 : ℝ) ≤ 1 / 3 := by
        rw [Real.exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3)
          (show (3 : ℝ) ≤ Real.exp 12288 by linarith only [Real.add_one_le_exp (12288 : ℝ)])
      exact hf.trans (one_third_le_errorEnvelope_caseII hH.toSection13HatContract ho hD1
        (by linarith only [hs]) (by linarith only [hs5, hs2]))
  have hhalf : (1 / 2 : ℝ) ≤ Real.log (D : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ D by exact_mod_cast hD)
    linarith only [hh, Real.log_two_gt_d9]
  have hroot : (1 / 2 : ℝ) ≤ (Real.log (D : ℝ)) ^ (1 / 8 : ℝ) := by
    exact (Real.self_le_rpow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num) (by norm_num : (1 / 8 : ℝ) ≤ 1)).trans
      (Real.rpow_le_rpow (by norm_num) hhalf (by norm_num))
  have hInv : (Real.log (D : ℝ)) ^ (-(1 / 8 : ℝ)) ≤ 2 := by
    rw [Real.rpow_neg hL.le]
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hroot
    norm_num only [one_div_div, div_one] at hh
    simpa only [one_div] using hh
  have hb := polynomialCorrectionWeight_pos.le
  have hbE : polynomialCorrectionWeight * (Real.log (D : ℝ)) ^ (-(1 / 8 : ℝ)) ≤
      errorEnvelope H N D 16 s := by
    have hh := mul_le_mul_of_nonneg_left hInv hb
    have hp := polynomialCorrectionWeight_small.trans hE
    nlinarith only [hh, hp, hb]
  have hs4 : 1 ≤ s ^ 4 := one_le_pow₀ (by linarith only [hs] : (1 : ℝ) ≤ s)
  have hpc : polynomialCorrectionWeight * polynomialCorrection D s ≤
      errorEnvelope H N D 16 s * (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    unfold polynomialCorrection
    have heq : (Real.log (D : ℝ)) ^ (-(5 / 8 : ℝ)) =
        (Real.log (D : ℝ)) ^ (-(1 / 8 : ℝ)) * (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hL]
      norm_num
    rw [heq]
    have hh := mul_le_mul_of_nonneg_right hbE (Real.rpow_nonneg hL.le (-(1 / 2 : ℝ)))
    have hp : polynomialCorrectionWeight * ((Real.log (D : ℝ)) ^ (-(1 / 8 : ℝ)) *
        (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) / s ^ 4 ≤
        polynomialCorrectionWeight * ((Real.log (D : ℝ)) ^ (-(1 / 8 : ℝ)) *
          (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) :=
      div_le_self (by positivity) hs4
    ring_nf at hh hp ⊢
    nlinarith only [hh, hp]
  unfold mixedError
  linarith only [hpc]

theorem numerical_mixed_suzuki_window (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    {K C1 : ℝ} (hK : 2 ≤ K) (hC1 : mixedSuzukiSeparator ≤ C1)
    (S : BoundingSieve) (hlocal : HasDimensionOneLocalProductBound S K)
    (N D : ℕ) (hN : 1 ≤ N) (hD : 2 ≤ D) (s : ℝ)
    (hsdom : s ∈ KappaOneModel.parityDomain 2 N) (hslo : 3 / 2 ≤ s) (hshi : s ≤ 5)
    (hsSigma : s ≤ sourceSigma D 16) (hz : 2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 N s + (2 * mixedSuzukiCoefficient C1 K) * Real.exp (Real.sqrt K) *
          errorEnvelope H N D 16 s * (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  have hh := numerical_mixed_suzuki H hH K hK C1 hC1 S hlocal N hN D hD hD s hsdom hsSigma hz
  have he := mixed_window_error_le hH hD hslo hshi N hsdom
  have hc : 0 ≤ mixedSuzukiCoefficient C1 K :=
    (by norm_num : (0 : ℝ) ≤ 36).trans (le_max_left _ _)
  have hv := (suzukiVProduct_pos S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ)).le
  have hp := mul_le_mul_of_nonneg_left he (mul_nonneg hc (Real.exp_pos (Real.sqrt K)).le)
  have hscaled := mul_le_mul_of_nonneg_left hp hv
  nlinarith only [hh, hscaled]

noncomputable def numericalEffectiveSuzukiCoefficient : ℝ :=
  2 * mixedSuzukiCoefficient mixedSuzukiSeparator numericalLocalProductK

#print axioms numerical_mixed_suzuki_window
end ChenEffective
