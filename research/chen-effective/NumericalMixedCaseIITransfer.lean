import NumericalMixedCaseIIScalar

open scoped Classical BigOperators Interval
namespace ChenEffective
variable [profile : CorrectionProfile]
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiFiniteContinuousLayers SuzukiLemma144KappaOne SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem mixedError_nonneg {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {D s d Δ : ℝ} (hD : 1 < D) (hs : 0 < s) (n : ℕ) :
    0 ≤ mixedError H n D d Δ s := by
  have he := errorEnvelope_nonneg H n (d := d) hD hs.le (hH.positive _ _ hs).le
  have hb := polynomialCorrectionWeight_pos.le
  have hL := Real.log_pos hD
  unfold mixedError polynomialCorrection
  positivity

omit profile in
theorem mixed_V_ratio (S : BoundingSieve) {w z : ℝ} (hwz : w ≤ z) :
    suzukiVProduct S w / suzukiVProduct S z = suzukiLocalRatio S w z := by
  classical
  let B := S.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < z)
  let A := S.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < w)
  let E := S.prodPrimes.primeFactors.filter (fun q : ℕ => w ≤ (q : ℝ) ∧ (q : ℝ) < z)
  have hA : B.filter (fun q : ℕ => (q : ℝ) < w) = A := by
    ext q
    simp only [B, A, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2.trans_le hwz⟩, h.2⟩
  have hE : B.filter (fun q : ℕ => ¬ (q : ℝ) < w) = E := by
    ext q
    simp only [B, E, Finset.mem_filter, not_lt]
    tauto
  have hpartition : (∏ q ∈ B, (1 - S.nu q)) =
      (∏ q ∈ A, (1 - S.nu q)) * (∏ q ∈ E, (1 - S.nu q)) := by
    rw [← hA, ← hE]
    exact (Finset.prod_filter_mul_prod_filter_not B (fun q : ℕ => (q : ℝ) < w)
      (fun q => 1 - S.nu q)).symm
  have hAne := (suzukiVProduct_pos S w).ne'
  unfold suzukiVProduct suzukiLocalRatio at *
  change (∏ q ∈ A, (1 - S.nu q)) / (∏ q ∈ B, (1 - S.nu q)) =
    ∏ q ∈ E, (1 - S.nu q)⁻¹
  rw [Finset.prod_inv_distrib, hpartition, div_mul_eq_div_div, div_self hAne, one_div]

theorem mixed_cubic_error_transfer {H : Section13HatLayers}
    (hH : Section13HatContract H 2) {n : ℕ} (hn : Odd n) {D s : ℝ}
    (hD : 1 < D) (hs : 0 < s) (hs3 : s ≤ 3)
    (h3 : (3 : ℝ) ^ (16 : ℝ) ≤ Real.log D) :
    (3 / s) * mixedError H n D 16 (1 / 2) 3 ≤
      (1 + mixedCubicPerturbation / Real.log D) * mixedError H n D 16 (1 / 2) s := by
  have hL := Real.log_pos hD
  have hE0 := errorEnvelope_nonneg H n (d := (16 : ℝ)) hD hs.le (hH.positive _ _ hs).le
  have hLambda := lambda_three_le_perturb_three_mul_lambda_caseII hH hD
    (by norm_num : (0 : ℝ) ≤ 16) hs hs3
  have hEc : (3 / s) * errorEnvelope H n D 16 3 ≤
      perturbation D 16 0 3 * errorEnvelope H n D 16 s := by
    rw [errorEnvelope_eq_lambda_div H (by norm_num : (0 : ℝ) < 3),
      errorEnvelope_eq_lambda_div H hs, ErrorSign.ofDepth_of_odd hn]
    have hh := div_le_div_of_nonneg_right hLambda hs.le
    calc
      _ = lambda H .plus D 16 0 3 / s := by ring
      _ ≤ _ := hh
      _ = _ := by ring
  have hpert := perturbation_three_le_one_add_seven_ratio hL (by norm_num : (0 : ℝ) ≤ 16) h3
  norm_num only [show (16 : ℝ) = (16 : ℕ) by norm_num, Real.rpow_natCast] at hpert
  have hpert' : perturbation D 16 0 3 ≤ 1 + mixedCubicPerturbation / Real.log D := by
    norm_num [mixedCubicPerturbation] at hpert ⊢
    ring_nf at hpert ⊢
    linarith only [hpert]
  have hhat := (mul_le_mul_of_nonneg_right hEc (Real.rpow_nonneg hL.le (-(1 / 2 : ℝ)))).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpert' hE0)
      (Real.rpow_nonneg hL.le (-(1 / 2 : ℝ))))
  have hspow : s ^ 3 ≤ (27 : ℝ) := by
    have hh := pow_le_pow_left₀ hs.le hs3 3
    norm_num at hh
    exact hh
  have hpoly : (3 / s) * polynomialCorrection D 3 ≤ polynomialCorrection D s := by
    have hh : (3 / s) * (1 / (3 : ℝ) ^ 4) ≤ 1 / s ^ 4 := by
      calc
        _ = 1 / (27 * s) := by ring
        _ ≤ _ := by
          apply (div_le_div_iff₀ (by positivity : 0 < 27 * s) (pow_pos hs 4)).mpr
          have hp := mul_le_mul_of_nonneg_left hspow hs.le
          nlinarith only [hp]
    have hp := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hL.le (-(5 / 8 : ℝ)))
    simpa only [polynomialCorrection, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, mul_one, one_mul] using hp
  have hQ : 0 ≤ mixedCubicPerturbation / Real.log D := by unfold mixedCubicPerturbation; positivity
  have hb := polynomialCorrectionWeight_pos.le
  have hp0 : 0 ≤ polynomialCorrection D s := by unfold polynomialCorrection; positivity
  have hp := mul_le_mul_of_nonneg_left hpoly hb
  have hextra := mul_nonneg hQ (mul_nonneg hb hp0)
  unfold mixedError
  ring_nf at hhat hp hextra ⊢
  nlinarith only [hhat, hp, hextra]

#print axioms mixed_cubic_error_transfer
end ChenEffective
