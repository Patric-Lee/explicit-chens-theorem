import NumericalErrorTransport
import NumericalSourceGeometry
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIFinalProducer

open scoped Classical BigOperators Interval
open Set Filter Finset Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def recursiveNatCutoff : ℕ := ⌈recursiveCoordinateCutoff⌉₊
noncomputable def preThresholdCutoff : ℝ := max sourceGeometryCutoff 4

theorem numerical_recursive_coordinate_uniform (D : ℕ) (hD : recursiveNatCutoff ≤ D)
    (S : BoundingSieve) (s : ℝ) (hs : 2 ≤ s) :
    ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D (sourceSigma (D : ℝ) 16) s,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) 16 := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  apply numerical_recursive_coordinate
  · exact (Nat.le_ceil recursiveCoordinateCutoff).trans (by exact_mod_cast hD)
  · exact Nat.prime_of_mem_primeFactors hp'.1
  · exact hs
  · exact hp'.2.1
  · exact hp'.2.2

theorem numerical_preThreshold_geometry (D _N : ℕ) (hD : preThresholdCutoff ≤ (D : ℝ))
    (s : ℝ) (hs : 2 ≤ s) (hsσ : s ≤ sourceSigma (D : ℝ) 16) :
    CaseIPreThresholdGeometryPacket D 16 s := by
  have hD4 : 4 ≤ D := by exact_mod_cast ((le_max_right _ _).trans hD)
  have hg := numerical_source_geometry ((le_max_left _ _).trans hD)
  have hord := rpow_one_div_mono_of_le
    (show (1 : ℝ) ≤ D by exact_mod_cast (show 1 ≤ D by omega))
    (show 0 < s by linarith only [hs]) hsσ
  exact ⟨hD4, by linarith only [hg.1], hg.2.2, hg.2.2.trans hord, hord⟩
theorem numerical_caseI_pointwise_packet
    (H : Section13HatLayers)
    {Dmin : ℕ} {d Δ : ℝ}
    (hH : Section13HatSourceContract H) (hd1 : 1 < d) (hΔ0 : 0 < Δ)
    (hDmin : 2 ≤ Dmin) :
    ∀ D : ℕ, Dmin^2 ≤ D → ∀ (S : BoundingSieve) (N : ℕ) (s : ℝ),
      2 ≤ N → s - 1 ∈ KappaOneModel.parityDomain 2 (N - 1) → 2 ≤ s →
      let σ := sourceSigma (D : ℝ) d
      CaseIErrorEnvelopeTransport S H N D d σ s →
      (∀ p ∈ S.prodPrimes.primeFactors, p.Prime) ∧
      CarrierQuotientThresholdGeometry S.prodPrimes.primeFactors D Dmin σ s ∧
      (∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ s,
        inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1)) ∧
      (∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ s,
        finiteSourceLayer 1 2 (N - 1) (recursiveCoordinate D p) ≤
          finiteSourceLayer 1 2 (N - 1) (inheritedCoordinate D p)) ∧
      CaseIErrorEnvelopeTransport S H N D d σ s ∧
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) → (p : ℝ) < (D : ℝ) ^ (1 / s) →
        2 ≤ p ∧ 2 * p ≤ D) ∧
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) → (p : ℝ) < (D : ℝ) ^ (1 / s) →
        0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p)) ∧
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) → (p : ℝ) < (D : ℝ) ^ (1 / s) →
        Claim14_13PointwisePremise H N (D : ℝ) d Δ
          (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) := by
  intro D hDsq S N s hN hspred hs
  dsimp only
  intro herror
  have hscale := caseI_carrier_quotient_scale S (σ := sourceSigma (D : ℝ) d)
    hDmin hDsq hs
  have hD1 : 1 < D := by
    have : 4 ≤ Dmin ^ 2 := by nlinarith
    omega
  have hprime : ∀ p ∈ S.prodPrimes.primeFactors, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  have hceil : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / s) → 2 ≤ p ∧ 2 * p ≤ D := by
    intro p hp hpl hpu
    have hpCarrier : p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
        (sourceSigma (D : ℝ) d) s := by
      simp only [sigmaOneCarrier, Finset.mem_filter]
      exact ⟨hp, hpl, hpu⟩
    exact ⟨(hprime p hp).two_le,
      (Nat.mul_le_mul_right p hDmin).trans (hscale p hpCarrier)⟩
  have hinherited : ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
      (sourceSigma (D : ℝ) d) s,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1) := by
    intro p hp
    have hp' := hp
    simp only [sigmaOneCarrier, Finset.mem_filter] at hp'
    apply parityDomain_mono hspred
    exact (caseI_inheritedCoordinate_gt (hprime p hp'.1).two_le hD1
      (lt_of_lt_of_le (by norm_num) hs) hp'.2.2).le
  have hsource : ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
      (sourceSigma (D : ℝ) d) s,
      finiteSourceLayer 1 2 (N - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 2 (N - 1) (inheritedCoordinate D p) := by
    intro p hp
    have hp' := hp
    simp only [sigmaOneCarrier, Finset.mem_filter] at hp'
    obtain ⟨hp2, h2p⟩ := hceil p hp'.1 hp'.2.1 hp'.2.2
    have hrec := parityDomain_mono (hinherited p hp) (coordinate_bounds hp2 h2p).1
    exact finiteSourceLayer_recursive_le_inherited (by norm_num) (N - 1) D p
      hp2 h2p (hinherited p hp) hrec
  have hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / s) →
      0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p) := by
    intro p hp _hpl hpu
    have hx0 : 0 < inheritedCoordinate D p :=
      lt_trans (by linarith : 0 < s - 1)
        (caseI_inheritedCoordinate_gt (hprime p hp).two_le hD1 (by linarith) hpu)
    exact (hH.positive _ _ hx0).le
  have h1413 : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / s) →
      Claim14_13PointwisePremise H N (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ)) := by
    intro p hp hpl hpu
    obtain ⟨hp2, h2p⟩ := hceil p hp hpl hpu
    exact claim14_13_pointwise_carrier H (by omega) hp2 h2p hd1 hΔ0
      (by simpa [inheritedCoordinate] using hT p hp hpl hpu)
  exact ⟨hprime, hscale, hinherited, hsource, herror, hceil, hT, h1413⟩
#print axioms numerical_caseI_pointwise_packet
end ChenEffective
