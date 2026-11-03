import NumericalC1Geometry

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

noncomputable def transportCaseIICutoff : ℕ := max (transportQuotientCutoff^2) recursiveNatCutoff
theorem numerical_caseII_error_transport
    (H : Section13HatLayers) {d : ℝ}
    (hH : Section13HatSourceContract H) (hd1 : 1 < d) (hd16 : d=16) :
    ∀ D : ℕ, transportCaseIICutoff ≤ D → ∀ (S : BoundingSieve) (N : ℕ) (s : ℝ),
      Odd N → 1 < s → s ≤ 3 →
      (∀ p ∈ sigmaOneCarrier
          (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊)
          D (sourceSigma (D : ℝ) d) 3,
        inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1) ∧
        recursiveCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1)) →
      CaseIIErrorEnvelopeTransport S H N D d := by
  subst d
  let d : ℝ := 16
  let D146 := claim146FullCutoff
  have hD146 := claim146FullCutoff_gt_one
  have h146 := fun (D : ℝ) (hD : D146 ≤ D) => numerical_claim146 hH hD
  let C : ℝ := (1 + 3 * d) * (4 : ℝ) ^ d
  let A : ℝ := max D146 (Real.exp (3 * C))
  let Dmin := transportQuotientCutoff
  have hDminA : A < (Dmin : ℝ) := by
    have hh := Nat.le_ceil A
    change A < ((⌈A⌉₊ + 1 : ℕ) : ℝ)
    push_cast
    linarith only [hh]
  have hA1 : 1 < A := hD146.trans_le (le_max_left _ _)
  have hDmin2 : 2 ≤ Dmin := by
    have : (1 : ℝ) < (Dmin : ℝ) := hA1.trans hDminA
    exact_mod_cast this
  intro D hDcut
  have hD : Dmin^2 ≤ D := (le_max_left _ _).trans hDcut
  have hrecursiveUpper := numerical_recursive_coordinate_uniform D ((le_max_right _ _).trans hDcut)
  intro S N s _hN _hs1 _hs3 hdomains p hpCarrier
  have hpFull : p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
      (sourceSigma (D : ℝ) d) 3 := by
    have hp := hpCarrier
    simp only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1.1, hp.2.1, hp.2.2⟩
  have hpSupport : p ∈ S.prodPrimes.primeFactors :=
    (Finset.mem_filter.mp hpFull).1
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpSupport
  have hp2 : 2 ≤ p := hpPrime.two_le
  have hp0 : 0 < p := hpPrime.pos
  have hscale := caseII_cubic_carrier_quotient_scale (d := d) S hDmin2 hD
  have hqThreshold : Dmin ≤ D ⌈/⌉ p :=
    ceilDiv_ge_threshold_of_scale hp0 (hscale p hpCarrier)
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
  have hq1 : 1 < ((D ⌈/⌉ p : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < D ⌈/⌉ p by omega)
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
    (hdomains p hpCarrier).1 (coordinate_bounds hp2 h2pD).1
    (hrecursiveUpper S 3 (by norm_num) p hpFull)
#print axioms numerical_caseII_error_transport
end ChenEffective
