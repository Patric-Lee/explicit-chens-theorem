import NumericalPolynomialMixedCore

open scoped Classical BigOperators Interval
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiFiniteContinuousLayers SuzukiLemma144KappaOne SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def mixedError (H : Section13HatLayers) (n : ℕ) (D d Δ s : ℝ) : ℝ :=
  errorEnvelope H n D d s * (Real.log D) ^ (-Δ) +
    polynomialCorrectionWeight * polynomialCorrection D s

noncomputable def mixedBudget (S : BoundingSieve) (H : Section13HatLayers)
    (n D z : ℕ) (C K d Δ s : ℝ) : ℝ :=
  C * Real.exp (Real.sqrt K) * suzukiVProduct S z * mixedError H n D d Δ s

def MixedMovingDomainGlobalDepthAt (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (n Dmin : ℕ) : Prop :=
  ∀ D z : ℕ, Dmin ≤ D → 2 ≤ D → 2 ≤ z →
    ∀ s : ℝ, s ∈ KappaOneModel.parityDomain 2 n → s ≤ sourceSigma D d →
      (D : ℝ) ^ (1 / s) = z →
      suzukiActualT S n D z ≤ suzukiVProduct S z *
        (finiteSourceLayer 1 2 n s + C * Real.exp (Real.sqrt K) * mixedError H n D d Δ s)

def MixedMovingDomainNatCeilAt (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (n Dmin : ℕ) : Prop :=
  ∀ D : ℕ, Dmin ≤ D → 2 ≤ D →
    ∀ s : ℝ, s ∈ KappaOneModel.parityDomain 2 n → s ≤ sourceSigma D d →
      2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
      suzukiActualT S n D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
        suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
          (finiteSourceLayer 1 2 n s + C * Real.exp (Real.sqrt K) * mixedError H n D d Δ s)

theorem mixed_global_of_natCeil (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (n Dmin : ℕ)
    (h : MixedMovingDomainNatCeilAt S H C K d Δ n Dmin) :
    MixedMovingDomainGlobalDepthAt S H C K d Δ n Dmin := by
  intro D z hmin hD hz s hs hsig hpow
  have hc : ⌈(D : ℝ) ^ (1 / s)⌉₊ = z := by rw [hpow, Nat.ceil_natCast]
  have hh := h D hmin hD s hs hsig
  rw [hc] at hh
  exact hh hz

/-- Subtract only the additional correction before using the existing
linear finite-sum assembly. No bound for the subtracted tail is assumed. -/
noncomputable def mixedSubtractedTail (S : BoundingSieve) (C K : ℝ) (n D z : ℕ) : ℝ :=
  suzukiActualT S n D z - C * Real.exp (Real.sqrt K) * suzukiVProduct S z *
    polynomialCorrectionWeight * polynomialCorrection D (Real.log (D : ℝ) / Real.log (z : ℝ))

theorem mixed_pointwise_of_globalIH
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N D Dmin : ℕ) (σ τ : ℝ)
    (hDmin : 2 ≤ Dmin)
    (hprime : ∀ p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊, p.Prime)
    (hscale : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D Dmin σ τ)
    (hinherited : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D σ τ,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1))
    (hV : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D σ τ, 0 ≤ suzukiVProduct S p)
    (hC : 0 ≤ C)
    (hSource : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D σ τ,
      finiteSourceLayer 1 2 (N - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 2 (N - 1) (inheritedCoordinate D p))
    (hError : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D σ τ,
      errorEnvelope H (N - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
        errorEnvelope H (N - 1) (D ⌈/⌉ p : ℕ) d (inheritedCoordinate D p))
    (hrecursiveSigma : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D σ τ,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d)
    (hIH : MixedMovingDomainGlobalDepthAt S H C K d Δ (N - 1) Dmin) :
    PointwiseInductionContract
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) (mixedSubtractedTail S C K)
      (fun p => suzukiVProduct S p) (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ N D σ τ := by
  have hnatural : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) (mixedSubtractedTail S C K)
      (fun p => suzukiVProduct S p) (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ N D σ τ := by
    intro p hp
    have hpPrime := hprime p (Finset.mem_filter.mp hp).1
    have hqmin := ceilDiv_ge_threshold_of_scale hpPrime.pos (hscale p hp)
    have hq2 := hDmin.trans hqmin
    have h2p : 2 * p ≤ D := (Nat.mul_le_mul_right p hDmin).trans (hscale p hp)
    have hdom := parityDomain_mono (hinherited p hp) (coordinate_bounds hpPrime.two_le h2p).1
    have hh := hIH (D ⌈/⌉ p) p hqmin hq2 hpPrime.two_le (recursiveCoordinate D p)
      hdom (hrecursiveSigma p hp) (recursiveCoordinate_power_identity hpPrime.two_le hq2)
    unfold mixedSubtractedTail
    dsimp only [mixedError] at hh
    change suzukiActualT S (N - 1) (D ⌈/⌉ p) p -
      C * Real.exp (Real.sqrt K) * suzukiVProduct S p * polynomialCorrectionWeight *
        polynomialCorrection (D ⌈/⌉ p : ℕ) (recursiveCoordinate D p) ≤ _
    nlinarith only [hh]
  have hlog : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / τ)⌉₊) D σ τ,
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ) := by
    intro p hp
    have hq := hDmin.trans (ceilDiv_ge_threshold_of_scale
      (hprime p (Finset.mem_filter.mp hp).1).pos (hscale p hp))
    exact (Real.log_pos (by exact_mod_cast (show 1 < D ⌈/⌉ p by omega))).le
  exact naturalCeilContract_to_sourceCoordinate _ _ _ _ 2 C K Δ N D σ τ
    hV hC hlog hSource hError hnatural

theorem mixed_sigmaOne_reassemble (S : BoundingSieve) (C K : ℝ)
    (support : Finset ℕ) (N D z : ℕ) (σ τ : ℝ)
    (hc : sigmaOneCarrier support D σ τ = sigmaOneCarrier S.prodPrimes.primeFactors D σ τ) :
    sigmaOne support S.nu (suzukiActualT S) N D σ τ =
      sigmaOne support S.nu (mixedSubtractedTail S C K) N D σ τ +
        C * Real.exp (Real.sqrt K) * suzukiVProduct S z * polynomialCorrectionWeight *
          polynomialInheritedSum S D z σ τ := by
  classical
  have hVz : suzukiVProduct S (z : ℝ) ≠ 0 := (suzukiVProduct_pos S _).ne'
  unfold sigmaOne mixedSubtractedTail polynomialInheritedSum
  rw [hc]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  unfold recursiveCoordinate
  field_simp
  ring

#print axioms mixed_pointwise_of_globalIH
#print axioms mixed_sigmaOne_reassemble
end ChenEffective
