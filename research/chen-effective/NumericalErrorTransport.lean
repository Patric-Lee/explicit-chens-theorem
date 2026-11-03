import NumericalClaim146
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIErrorTransportUniform

open scoped Classical BigOperators Interval
open Set Filter Finset Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve MathlibNt.SieveTheory.SwitchingPrinciple MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def transportQuotientCutoff : ℕ :=
  ⌈max claim146FullCutoff (Real.exp (3*((1+3*(16 : ℝ))*4^(16 : ℝ))))⌉₊ + 1

theorem numerical_error_transport_quotient (H : Section13HatLayers)
    (hH : Section13HatSourceContract H) :    ∃ Dmin : ℕ, Dmin = transportQuotientCutoff ∧ 2 ≤ Dmin ∧
      ∀ (S : BoundingSieve) (D N : ℕ) (s : ℝ),
        CarrierQuotientThresholdGeometry S.prodPrimes.primeFactors D Dmin
          (sourceSigma (D : ℝ) 16) s →
        (∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
            (sourceSigma (D : ℝ) 16) s,
          inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1)) →
        (∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
            (sourceSigma (D : ℝ) 16) s,
          recursiveCoordinate D p ≤
            sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) 16) →
        CaseIErrorEnvelopeTransport S H N D 16 (sourceSigma (D : ℝ) 16) s := by
  let d : ℝ := 16
  have hd1 : 1 < d := by norm_num [d]
  let D146 := claim146FullCutoff
  have hD146 := claim146FullCutoff_gt_one
  have h146 := fun (D : ℝ) (hD : claim146FullCutoff ≤ D) => numerical_claim146 hH hD
  let C : ℝ := (1 + 3 * d) * (4 : ℝ) ^ d
  let A : ℝ := max D146 (Real.exp (3 * C))
  let Dmin := ⌈A⌉₊ + 1
  have hDminA : A < (Dmin : ℝ) := by
    have hh := Nat.le_ceil A
    dsimp [Dmin]
    push_cast
    linarith only [hh]
  have hA1 : 1 < A := hD146.trans_le (le_max_left _ _)
  have hDmin2 : 2 ≤ Dmin := by
    have : (1 : ℝ) < (Dmin : ℝ) := hA1.trans hDminA
    exact_mod_cast this
  refine ⟨Dmin, rfl, hDmin2, ?_⟩
  intro S D N s hscale hinherited hrecursiveUpper p hpCarrier
  have hpSupport : p ∈ S.prodPrimes.primeFactors :=
    (Finset.mem_filter.mp hpCarrier).1
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpSupport
  have hp2 : 2 ≤ p := hpPrime.two_le
  have hp0 : 0 < p := hpPrime.pos
  have hqThreshold : Dmin ≤ D ⌈/⌉ p :=
    ceilDiv_ge_threshold_of_scale hp0 (hscale p hpCarrier)
  have hq2 : 2 ≤ D ⌈/⌉ p := hDmin2.trans hqThreshold
  have h2pD : 2 * p ≤ D :=
    (Nat.mul_le_mul_right p hDmin2).trans (hscale p hpCarrier)
  have hD146A : D146 ≤ A := le_max_left _ _
  have hD146min : D146 ≤ (Dmin : ℝ) :=
    hD146A.trans (le_of_lt hDminA)
  have hD146q : D146 ≤ ((D ⌈/⌉ p : ℕ) : ℝ) := by
    exact hD146min.trans (by exact_mod_cast hqThreshold)
  have hi : Claim14_6_MonotoneLambdaPremise H
      ((D ⌈/⌉ p : ℕ) : ℝ) d
      (sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d) :=
    (h146 ((D ⌈/⌉ p : ℕ) : ℝ) hD146q).1
  have hq1 : 1 < ((D ⌈/⌉ p : ℕ) : ℝ) := by exact_mod_cast (show 1 < D ⌈/⌉ p by omega)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by nlinarith) (Real.rpow_nonneg (by norm_num) _)
  have hExpA : Real.exp (3 * C) ≤ A := le_max_right _ _
  have hExpq : Real.exp (3 * C) ≤ ((D ⌈/⌉ p : ℕ) : ℝ) :=
    hExpA.trans ((le_of_lt hDminA).trans (by exact_mod_cast hqThreshold))
  have hlogLarge : 3 * C ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ) :=
    (Real.le_log_iff_exp_le (by positivity)).2 hExpq
  have hlarge : (1 + 3 * d) * (4 : ℝ) ^ d ≤
      (1 / 3 : ℝ) * Real.log ((D ⌈/⌉ p : ℕ) : ℝ) := by
    change C ≤ _
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
      (by simpa only [mul_comm] using hlogLarge)
  exact errorEnvelope_coordinate_transport_full hH.toSection13HatContract
    (zero_le_one.trans hd1.le) hq1 hlarge hi
    (hinherited p hpCarrier) (coordinate_bounds hp2 h2pD).1
    (hrecursiveUpper p hpCarrier)
#print axioms numerical_error_transport_quotient
theorem numerical_caseI_error_transport (H : Section13HatLayers)
    (hH : Section13HatSourceContract H) (S : BoundingSieve) (D N : ℕ) (s : ℝ)
    (hD : transportQuotientCutoff^2 ≤ D) (hs : 2 ≤ s)
    (hinherited : ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D (sourceSigma (D : ℝ) 16) s,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N-1))
    (hrecursive : ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D (sourceSigma (D : ℝ) 16) s,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) 16) :
    CaseIErrorEnvelopeTransport S H N D 16 (sourceSigma (D : ℝ) 16) s := by
  obtain ⟨_, rfl, hmin, htransport⟩ := numerical_error_transport_quotient H hH
  exact htransport S D N s (caseI_carrier_quotient_scale S hmin hD hs) hinherited hrecursive
end ChenEffective
