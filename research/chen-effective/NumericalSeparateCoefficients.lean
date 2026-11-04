import NumericalMixedInduction

namespace ChenEffective
open Real Set
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiFiniteContinuousLayers SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

/-- Separate hat and polynomial coefficients, with explicit compatibility
conditions. No fixed small correction weight enters either coefficient. -/
theorem numerical_separate_suzuki (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (K : ℝ) (hK : 2 ≤ K) (C1 : ℝ) (hC1 : mixedSuzukiSeparator ≤ C1)
    (C P : ℝ) (h36 : 36 ≤ C) (hlow : 4 * lowStripNumericalConstant C1 ≤ C)
    (hpoly : 4 * max 1 (polynomialTerminalConstant (C1 * K ^ (7 : ℝ)) K) ≤ P)
    (hPC : P ≤ C)
    (S : BoundingSieve) (hlocal : HasDimensionOneLocalProductBound S K)
    (N D : ℕ) (hN : 1 ≤ N) (hD : 2 ≤ D) (s : ℝ)
    (hs : s ∈ KappaOneModel.parityDomain 2 N) (hsig : s ≤ sourceSigma D 16)
    (hz : 2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 N s + exp (sqrt K) *
          (C * errorEnvelope H N D 16 s * (log (D : ℝ)) ^ (-(1 / 2 : ℝ)) +
            P * polynomialCorrection D s)) := by
  have hC0 : 0 < C := by linarith only [h36]
  have hP0 : 0 < P := by
    have hh : (4 : ℝ) ≤ 4 * max 1 (polynomialTerminalConstant (C1 * K ^ (7 : ℝ)) K) := by
      nlinarith only [le_max_left (1 : ℝ) (polynomialTerminalConstant (C1 * K ^ (7 : ℝ)) K)]
    linarith only [hpoly, hh]
  let w := P / C
  have hw : 0 < w := div_pos hP0 hC0
  let p : CorrectionProfile := {
    weight := w
    positive := hw
    le_one := (div_le_one hC0).mpr hPC }
  have hc : mixedSuzukiCoefficient (profile := p) C1 K ≤ C := by
    change max 36 (max (4 * max 1 (polynomialTerminalConstant (C1 * K ^ (7 : ℝ)) K / w))
      (4 * lowStripNumericalConstant C1)) ≤ C
    apply max_le h36 (max_le _ hlow)
    rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
    apply max_le (by linarith only [h36])
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hw).mpr
    have hcw : C * w = P := by dsimp [w]; field_simp
    rw [hcw]
    exact (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num : (0 : ℝ) ≤ 4)).trans hpoly
  have hh := numerical_mixed_suzuki (profile := p) H hH K hK C1 hC1 S hlocal N hN D hD hD s hs hsig hz
  have hs0 : 0 < s := by
    by_cases ho : N % 2 = 1
    · have ht : (2 : ℝ) - 1 < s := by simpa [KappaOneModel.parityDomain, ho] using hs
      linarith only [ht]
    · have ht : 2 ≤ s := by simpa [KappaOneModel.parityDomain, ho] using hs
      linarith only [ht]
  have hD1 : 1 < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have he := mixedError_nonneg (profile := p) hH.toSection13HatContract
    (d := (16 : ℝ)) (Δ := (1 / 2 : ℝ)) hD1 hs0 N
  have hv := (suzukiVProduct_pos S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ)).le
  have hscaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (exp_pos (sqrt K)).le) he) hv
  calc
    _ ≤ suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 N s + C * exp (sqrt K) * mixedError (profile := p) H N D 16 (1 / 2) s) := by
      nlinarith only [hh, hscaled]
    _ = _ := by
      have hweight : polynomialCorrectionWeight (profile := p) = P / C := rfl
      unfold mixedError
      rw [hweight]
      field_simp [hC0.ne']

/-- The active profile is unweighted: its terminal coefficient is not divided
by exp(-1000). This equality is independent of all analytic hypotheses. -/
theorem unweighted_mixed_claim_coefficient (C1 K : ℝ) :
    mixedClaimCoefficient (profile := defaultCorrectionProfile) C1 K =
      max 1 (polynomialTerminalConstant (C1 * K ^ (7 : ℝ)) K) := by
  change max 1 (polynomialTerminalConstant (C1 * K ^ (7 : ℝ)) K / (1 : ℝ)) = _
  rw [div_one]

/-- One concrete unequal allocation, with every compatibility condition
discharged. The generic theorem also permits other allocations. -/
theorem numerical_separate_suzuki_explicit (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (K : ℝ) (hK : 2 ≤ K) (C1 : ℝ) (hC1 : mixedSuzukiSeparator ≤ C1)
    (S : BoundingSieve) (hlocal : HasDimensionOneLocalProductBound S K)
    (N D : ℕ) (hN : 1 ≤ N) (hD : 2 ≤ D) (s : ℝ)
    (hs : s ∈ KappaOneModel.parityDomain 2 N) (hsig : s ≤ sourceSigma D 16)
    (hz : 2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    let A := mixedSuzukiCoefficient (profile := defaultCorrectionProfile) C1 K
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 N s + exp (sqrt K) *
          ((2 * A) * errorEnvelope H N D 16 s * (log (D : ℝ)) ^ (-(1 / 2 : ℝ)) +
            A * polynomialCorrection D s)) := by
  let A := mixedSuzukiCoefficient (profile := defaultCorrectionProfile) C1 K
  have ha36 : (36 : ℝ) ≤ A := le_max_left _ _
  have ha0 : 0 ≤ A := by linarith only [ha36]
  have hlow : 4 * lowStripNumericalConstant C1 ≤ A :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hpoly : 4 * max 1 (polynomialTerminalConstant (C1 * K ^ (7 : ℝ)) K) ≤ A := by
    have hh : 4 * mixedClaimCoefficient (profile := defaultCorrectionProfile) C1 K ≤ A :=
      (le_max_left _ _).trans (le_max_right _ _)
    rwa [unweighted_mixed_claim_coefficient] at hh
  exact numerical_separate_suzuki H hH K hK C1 hC1 (2 * A) A
    (by linarith only [ha36]) (by linarith only [hlow, ha0]) hpoly (by linarith only [ha0])
    S hlocal N D hN hD s hs hsig hz

#print axioms numerical_separate_suzuki
#print axioms unweighted_mixed_claim_coefficient
#print axioms numerical_separate_suzuki_explicit
end ChenEffective
