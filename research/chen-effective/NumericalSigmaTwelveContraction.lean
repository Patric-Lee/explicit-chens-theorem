import NumericalClaim146
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISourceLargeCoefficientUniform

open scoped Classical BigOperators Interval
open Set Filter Finset Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
theorem numerical_sigmaTwelve_contraction
    {H : Section13HatLayers}
    {d Δ : ℝ}
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd16 : d = 16) (hΔhalf : Δ = 1/2) :
    ∃ D₀ : ℝ, D₀ = claim146FullCutoff ∧ 1 < D₀ ∧
      ∀ S : BoundingSieve,
      ∀ (C K : ℝ), 2 ≤ K → HasDimensionOneLocalProductBound S K → 0 ≤ C →
      ∀ (D N : ℕ) (s : ℝ) (z : ℕ), D₀ ≤ (D : ℝ) →
      0 < s →
      2 + (ErrorSign.ofDepth N).epsilon ≤ s →
      1 < sourceSigma (D : ℝ) d →
      s ≤ sourceSigma (D : ℝ) d →
      1 < (D : ℝ) →
      2 ≤ (D : ℝ) ^ (1 / s) →
      2 ≤ (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) →
      (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (D : ℝ) ^ (1 / s) →
      z = ⌈(D : ℝ) ^ (1 / s)⌉₊ →
      H.betaHat + (ErrorSign.ofDepth N).epsilon ≤ s →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) → 2 ≤ p ∧ 2 * p ≤ D) →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) →
        0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p)) →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) →
        Claim14_13PointwisePremise H N (D : ℝ) d Δ
          (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) →
      ∃ q : Lemma144StrictFactor,
        q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma (D : ℝ) d) Δ) / 2 ∧
        sigmaTwelve S.prodPrimes.primeFactors S.nu
            (fun p => suzukiVProduct S (p : ℝ))
            (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
            (suzukiVProduct S (z : ℝ)) C K Δ N D
            (sourceSigma (D : ℝ) d) s ≤
          sigma12ContractionMultiplier (sourceSigma (D : ℝ) d) Δ *
              sigma12InheritedBudget S H N D z C K d Δ s +
            sigma12EndpointRemainder S H N D z C K d Δ s
              (sourceSigma (D : ℝ) d) ∧
        sigmaTwelve S.prodPrimes.primeFactors S.nu
            (fun p => suzukiVProduct S (p : ℝ))
            (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
            (suzukiVProduct S (z : ℝ)) C K Δ N D
            (sourceSigma (D : ℝ) d) s ≤
          q.ρ * sigma12InheritedBudget S H N D z C K d Δ s +
            sigma12EndpointRemainder S H N D z C K d Δ s
              (sourceSigma (D : ℝ) d) := by
  subst d Δ
  let d : ℝ := 16
  let Δ : ℝ := 1/2
  let D₀ := claim146FullCutoff
  have hD₀ := claim146FullCutoff_gt_one
  have h146 := fun (D : ℝ) (hD : claim146FullCutoff ≤ D) => numerical_claim146 hH hD
  refine ⟨D₀, rfl, hD₀, ?_⟩
  intro S C K hK hlocal hC D N s z hDlarge hs0 hsLower hσ1 hsσ hD hv2 hw2 hwv hz
    hthreshold hCeil hT h1413
  obtain ⟨_hi, hii, hiii⟩ := h146 (D : ℝ) hDlarge
  let σ : ℝ := sourceSigma (D : ℝ) d
  let a : ℝ := sigma12ContractionMultiplier σ Δ
  let A : ℝ := C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
    (Real.log (D : ℝ)) ^ (-Δ)
  let B : ℝ := errorEnvelope H N (D : ℝ) d s
  let R : ℝ := (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite
      (D : ℝ) d Δ s / Real.log ((D : ℝ) ^ (1 / σ))) * (s / s)
  have h12 := sigmaTwelve_suzukiVProduct_le_qD_lemma8_7_natCeil_closed
    (S := S) (H := H) (β := (2 : ℝ)) (C := C) (K := K) (d := d) (Δ := Δ)
    (w := (D : ℝ) ^ (1 / σ)) (v := (D : ℝ) ^ (1 / s))
    (s := s) (τ := s) (σ := σ) (N := N) (D := D) (znat := z)
    hH.toSection13HatContract hD hv2 hw2 hwv le_rfl hz rfl rfl
    hthreshold hsσ hK hlocal (by simpa [d, Δ, σ] using hii) hC hΔ0.le
    (by simpa [d, Δ, σ] using hCeil) (by simpa [d, Δ, σ] using hT) (by simpa [d, Δ, σ] using h1413)
  have hint := hiii (ErrorSign.ofDepth N) s hsLower hsσ
  have hintScaled :
      (1 / s) * (∫ t in s..σ,
        qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) ≤ a * B := by
    have hmul := mul_le_mul_of_nonneg_left hint.le (one_div_nonneg.mpr hs0.le)
    calc
      (1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) ≤
          (1 / s) * (a * lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 s) := by
            simpa [d, Δ, σ, a, sigma12ContractionMultiplier] using hmul
      _ = a * ((1 / s) * lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 s) := by ring
      _ = a * B := by rw [one_div_mul_lambda_eq_errorEnvelope H hs0]
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.exp_nonneg _)) (suzukiVProduct_pos S (z : ℝ)).le)
      (Real.rpow_nonneg (Real.log_nonneg hD.le) _)
  have hraw :
      sigmaTwelve S.prodPrimes.primeFactors S.nu
          (fun p => suzukiVProduct S (p : ℝ))
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S (z : ℝ)) C K Δ N D σ s ≤
        a * (A * B) + A * R := by
    apply h12.trans
    rw [show C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
        ((Real.log (D : ℝ)) ^ (-Δ) *
          ((1 / s) * (∫ t in s..σ,
            qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
            (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite
              (D : ℝ) d Δ s / Real.log ((D : ℝ) ^ (1 / σ))) * (s / s))) =
        A * ((1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) + R) by
            dsimp [A, R]; ring]
    have hinside :
        (1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) + R ≤
          a * B + R := add_le_add hintScaled (le_refl R)
    calc
      A * ((1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) + R) ≤
          A * (a * B + R) := mul_le_mul_of_nonneg_left hinside hA
      _ = a * (A * B) + A * R := by ring
  obtain ⟨q, hq, haq⟩ := exists_sigma12_sameC_strictFactor hσ1 hΔ1
  have hB : 0 ≤ B := by
    apply errorEnvelope_nonneg H N hD hs0.le
    exact (hH.positive (ErrorSign.ofDepth N) s hs0).le
  have hbudget : 0 ≤ A * B := mul_nonneg hA hB
  refine ⟨q, by simpa [d, Δ, σ] using hq, ?_, ?_⟩
  · simpa [d, Δ, σ, a, A, B, R, sigma12InheritedBudget,
      sigma12EndpointRemainder, mul_assoc] using hraw
  · have hρ : a ≤ q.ρ := haq.le
    have hslack : a * (A * B) + A * R ≤ q.ρ * (A * B) + A * R := by
      exact add_le_add (mul_le_mul_of_nonneg_right hρ hbudget) le_rfl
    have hfinal := hraw.trans hslack
    simpa [d, Δ, σ, a, A, B, R, sigma12InheritedBudget,
      sigma12EndpointRemainder, mul_assoc] using hfinal



#print axioms numerical_sigmaTwelve_contraction
end ChenEffective
