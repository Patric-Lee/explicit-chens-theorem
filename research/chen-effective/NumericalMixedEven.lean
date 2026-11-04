import NumericalMixedFinish

open scoped Classical BigOperators Interval
open Set Filter Finset Topology MeasureTheory intervalIntegral
namespace ChenEffective
variable [profile : CorrectionProfile]
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
theorem numerical_mixed_even_cutoff
    (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ)
    (hd16 : d=16) (hΔhalf : Δ=1/2) (hΘ7 : Θ=7) :
    ∃ C1min : ℝ, C1min = mixedEvenC1 ∧ 1 ≤ C1min ∧
      ∀ (S : BoundingSieve) (C1 C K : ℝ) (M D : ℕ),
        C1min ≤ C1 → max 3 (1 : ℝ) ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K →
        Even M → 2 ≤ M →
        C1 * K ^ Θ < Real.log (D : ℝ) →
        MixedMovingDomainGlobalDepthAt S H C K d Δ (M - 1) 2 →
        suzukiActualT S M D ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ ≤
          suzukiVProduct S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ *
            finiteSourceLayer 1 2 M 2 +
          (1 - 1 / (10 * sourceSigma (D : ℝ) d)) * mixedBudget S H M D
            ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ C K d Δ 2 := by
  subst d Δ Θ
  let d : ℝ := 16
  let Δ : ℝ := 1/2
  let Θ : ℝ := 7
  have hd1 : 1 < d := by norm_num [d]
  let L : ℝ := 144
  have hL : 1 ≤ L := by norm_num [L]
  have hfinite := numerical_finite_even_endpoint hH
  let R : ℝ := reverseRatioCap
  have hR : 1 ≤ R := reverseRatioCap_one
  have _hratio := fun (sign : ErrorSign) (s σ : ℝ) => numerical_reverse_ratio hH sign (s := s) (σ := σ)
  let Amax : ℝ := 1+2*L*R+12*R
  let C1coef : ℝ := mixedEndpointC1
  have hC1coef : 1 ≤ C1coef := mixedEndpointC1_one
  have hcoef := mixed_endpoint_order_uniform
  let C1scalar : ℝ := caseIScalarC1
  have hC1scalar : 1 ≤ C1scalar := caseIScalarC1_one
  have hscalar := numerical_caseI1423_scalar
  obtain ⟨_, rfl, hC1B, hcaseB⟩ := numerical_sigma_zero_even_cutoff H
    hsrc.hDelta_pos hsrc.hDelta_lt hsrc.h14_1 hsrc.one_le_theta hH rfl rfl rfl
  let C1B := sigmaZeroC1
  let CB : ℝ := 1
  have hCB : 0 < CB := zero_lt_one
  obtain ⟨_, rfl, hD12pos, h12⟩ := numerical_sigmaTwelve_contraction
    hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt rfl rfl
  let D12 := claim146FullCutoff
  let D146 := claim146FullCutoff
  have h146 := fun (D : ℝ) (hD : D146 ≤ D) => numerical_claim146 hH hD
  let Dg := preThresholdCutoff
  have hg := numerical_preThreshold_geometry
  let Drec := recursiveNatCutoff
  have hrec := numerical_recursive_coordinate_uniform
  let Derr := transportQuotientCutoff^2
  have herr := fun (D : ℕ) (hD : Derr ≤ D) (S : BoundingSieve) (N : ℕ) (s : ℝ)
    (hs : 2 ≤ s) => numerical_caseI_error_transport H hH S D N s hD hs
  let Dσ : ℝ := Real.exp (Real.exp 3)
  have hσlarge := numerical_sourceSigma_three d (by norm_num [d])
  let Dcut : ℝ := max 4 (max D12 (max D146
    (max Dg (max Dσ (max (Drec : ℝ) (Derr : ℝ))))))
  have hDcut : 0 < Dcut := (by norm_num : (0 : ℝ) < 4).trans_le (le_max_left _ _)
  let C1cut := max 1 (Real.log Dcut)
  have hC1cut : 1 ≤ C1cut := le_max_left _ _
  have hcut := numerical_fixed_threshold hsrc.hTheta_pos hDcut
  let C1min : ℝ := max 1 (max C1coef (max C1scalar (max C1B C1cut)))
  have hC1min : 1 ≤ C1min := le_max_left _ _
  refine ⟨C1min, rfl, hC1min, ?_⟩
  intro S C1 C K M D hC1 hCcommon hK hlocal hM hM2 hlarge hglobal
  have hCBC : CB ≤ C := (le_max_right 3 CB).trans hCcommon
  have hC3 : (3 : ℝ) ≤ C := (le_max_left 3 CB).trans hCcommon
  have hCpos : 0 < C := by linarith
  obtain ⟨hC1one, hcoefC1, hscalarC1, hcaseBC1, hcutC1⟩ :
      1 ≤ C1 ∧ C1coef ≤ C1 ∧ C1scalar ≤ C1 ∧ C1B ≤ C1 ∧ C1cut ≤ C1 := by
    simpa only [C1min, max_le_iff] using hC1
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast (show 0 < D by
      by_contra hn
      have hD0 : D = 0 := by omega
      subst D
      norm_num at hlarge
      have hC10 : 0 ≤ C1 :=
        (show (0 : ℝ) ≤ 1 by norm_num).trans (hC1min.trans hC1)
      have hKpow : 0 ≤ K ^ (7 : ℕ) := pow_nonneg (by linarith only [hK]) 7
      nlinarith [mul_nonneg hC10 hKpow])
  have hDcutD : Dcut < (D : ℝ) := hcut C1 K (D : ℝ) hcutC1 hK hDpos hlarge
  obtain ⟨hD4real, hD12, hD146, hDg, hDσ, hDrecReal, hDerrReal⟩ :
      (4 : ℝ) ≤ D ∧ D12 ≤ D ∧ D146 ≤ D ∧ Dg ≤ D ∧ Dσ ≤ D ∧
        (Drec : ℝ) ≤ D ∧ (Derr : ℝ) ≤ D := by
    simpa only [Dcut, max_le_iff] using hDcutD.le
  have hD4 : 4 ≤ D := by exact_mod_cast hD4real
  have hD3 : 3 ≤ D := by omega
  have hD2 : 2 ≤ D := by omega
  have hDrec : Drec ≤ D := by exact_mod_cast hDrecReal
  have hDerr : Derr ≤ D := by exact_mod_cast hDerrReal
  have hσ3 : (3 : ℝ) ≤ sourceSigma (D : ℝ) d := hσlarge _ hDσ
  have h2σ : (2 : ℝ) ≤ sourceSigma (D : ℝ) d := by linarith
  have g := hg D M hDg 2 (by norm_num) h2σ
  let σ : ℝ := sourceSigma (D : ℝ) d
  let z : ℕ := ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊
  have hz : z = ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ := rfl
  have hDreal : 1 < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hprime : ∀ p ∈ suzukiSupportedBelow S z, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have toFull : ∀ p, p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ 2 →
      p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2 := by
    intro p hp
    simpa only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter] using
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1,
        (Finset.mem_filter.mp hp).2⟩
  have hscale : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S z) D 2 σ 2 := by
    intro p hp
    exact evenEndpoint_carrier_scale S (by norm_num) (by norm_num [show 4 ≤ D from hD4])
      p (toFull p hp)
  have hrecursiveD := hrec D hDrec S
  have hrecursiveSigma : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ 2,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d := by
    intro p hp
    exact hrecursiveD 2 (by norm_num) p (toFull p hp)
  have hinheritedFull : ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (M - 1) := by
    intro p hp
    apply lemma144_caseI_even_endpoint_inherited_domain S hM hM2 hD4 hz p
    apply Finset.mem_filter.mpr
    exact ⟨(Finset.mem_filter.mp hp).1,
      (nat_lt_natCeil_iff_lt_real (natCast_rpow_one_div_pos (by omega) (2 : ℝ)) hz).2
        (Finset.mem_filter.mp hp).2.2⟩
  have herrorD := herr D hDerr S
  have herror : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ 2,
      errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
        errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (inheritedCoordinate D p) := by
    intro p hp
    exact herrorD M 2 (by norm_num) hinheritedFull
      (hrecursiveD 2 (by norm_num)) p (toFull p hp)
  have hpkt := lemma144_caseI_even_endpoint_source_packet S hM hM2 hD4 hz
  have hpoint := mixed_pointwise_of_globalIH S H C K d Δ M D 2 σ 2
    (by norm_num) hprime hscale
    (by intro p hp; exact (hpkt p (Finset.mem_filter.mp hp).1).1)
    (by intro p _; exact (suzukiVProduct_pos S p).le) hCpos.le
    (by intro p hp; exact (hpkt p (Finset.mem_filter.mp hp).1).2.2)
    herror hrecursiveSigma hglobal
  have h10 := equation14_10_finset_assembly
    (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
    (mixedSubtractedTail S C K) (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    (suzukiVProduct S z) 2 C K Δ M D σ 2
    (ne_of_gt (suzukiVProduct_pos S z))
    (by intro p hp; have hpS := (Finset.mem_filter.mp hp).1
        exact (S.nu_pos_of_prime p (hprime p hpS)
          ((Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpS).1).2.1)).le) hpoint
  have h149 : suzukiActualT S M D z =
      suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ)) ((D : ℝ) ^ (1 / (2 : ℝ))) +
          suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / (2 : ℝ))) := by
    simpa [d, Δ, Θ, L, σ] using suzuki_equation14_9_strict (D := D) (z := z) S hM2
      (fun hOdd => (Nat.not_even_iff_odd.mpr hOdd hM).elim) g.hpowerOrder
  have h11 := caseI_evenEndpointSigma11Edge S hM hM2 h2σ hDreal
    g.hpowerS g.hpowerSigma g.hpowerOrder hK hlocal
  have hceil : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ)) → 2 ≤ p ∧ 2 * p ≤ D := by
    intro p hp hpw hpv
    have hpc : p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2 := by
      simp only [sigmaOneCarrier, Finset.mem_filter]
      exact ⟨hp, hpw, hpv⟩
    exact ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
      evenEndpoint_carrier_scale S (by norm_num)
        (by norm_num [show 4 ≤ D from hD4]) p hpc⟩
  have hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ)) →
      0 ≤ H.T (ErrorSign.ofDepth (M - 1)) (inheritedCoordinate D p) := by
    intro p hp hpw hpv
    have hpc : p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2 := by
      simp only [sigmaOneCarrier, Finset.mem_filter]
      exact ⟨hp, hpw, hpv⟩
    have hcoord := hinheritedFull p hpc
    have hpred : (M - 1) % 2 = 1 := by
      have hm0 : M % 2 = 0 := Nat.even_iff.mp hM
      omega
    have hcoord0 : 0 < inheritedCoordinate D p := by
      simp only [KappaOneModel.parityDomain, hpred, if_pos, Set.mem_Ioi] at hcoord
      norm_num at hcoord
      linarith
    exact (hH.positive _ _ hcoord0).le
  have hEvenLower : 2 + (ErrorSign.ofDepth M).epsilon ≤ (2 : ℝ) := by
    have hnotOdd : ¬ Odd M := fun ho => (Nat.not_even_iff_odd.mpr ho) hM
    simp [ErrorSign.ofDepth, hnotOdd, ErrorSign.epsilon]
  have hthreshold : H.betaHat + (ErrorSign.ofDepth M).epsilon ≤ (2 : ℝ) := by
    rw [hH.betaHat_eq]
    exact hEvenLower
  obtain ⟨q12, hq12, _h12raw, h12q⟩ :=
    h12 S C K hK hlocal (by linarith [hCcommon]) D M 2 z hD12
      (by norm_num) hEvenLower (by linarith [hσ3]) h2σ hDreal
      g.hpowerS g.hpowerSigma g.hpowerOrder hz hthreshold hceil hT
      (by
        intro p hp hpw hpv
        have hcp := hceil p hp hpw hpv
        exact claim14_13_pointwise_carrier H (by omega) hcp.1 hcp.2 hd1
          hsrc.hDelta_pos (hT p hp hpw hpv))
  have h12qSupported :
      sigmaTwelve (suzukiSupportedBelow S z) S.nu
          (fun p => suzukiVProduct S (p : ℝ))
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S (z : ℝ)) C K Δ M D σ 2 ≤
        q12.ρ * sigma12InheritedBudget S H M D z C K d Δ 2 +
          caseI1423Sigma12Endpoint S H M D z C K d Δ 2 σ := by
    rw [show suzukiSupportedBelow S z =
      S.prodPrimes.primeFactors.filter (fun p => p < z) from rfl]
    rw [sigmaTwelve_supportedBelow_eq_full S
      (fun p => suzukiVProduct S (p : ℝ))
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      (suzukiVProduct S (z : ℝ)) C K Δ M D z σ 2
      (by dsimp [z]; exact Nat.le_ceil _)]
    simpa [d, Δ, Θ, L, sigma12EndpointRemainder, caseI1423Sigma12Endpoint] using h12q
  have hscalarD := hscalar C1 K (D : ℝ) hscalarC1 hK
    (by exact_mod_cast hD2) hlarge
  have hend := caseI1423EndpointSourceBounds_evenEndpoint_explicit
    S H C K d Δ L R hH hCpos hsrc.hDelta_pos
      hsrc.hDelta_lt hsrc.h14_1 hL hfinite hR _hratio
      D M hD3 (by simpa only [d, Δ, show (1 : ℝ)-1/2=1/2 by norm_num] using hscalarD) hM hM2 h2σ
  have hzσ : (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) := by
    simpa [d, Δ, Θ, L, z, σ] using g.hpowerOrder.trans (Nat.le_ceil _)
  have hzeroRaw := hcaseB S C1 C K M D z hcaseBC1 hCBC hK hlocal hD2
    hlarge hM hM2 hzσ
  have hi := (h146 (D : ℝ) hD146).1
  have hEtransport : errorEnvelope H M (D : ℝ) d σ ≤
      errorEnvelope H M (D : ℝ) d 2 := by
    apply errorEnvelope_endpoint_le_of_claim14_6 hH.toSection13HatContract hDreal hi
    rw [hH.betaHat_eq]
    exact ⟨hEvenLower, by simpa [d, Δ, Θ, L, σ] using h2σ⟩
  have hzeroUnit : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) ≤
      (CB / C) * caseI1423RemainderUnit
        (sigma12InheritedBudget S H M D z C K d Δ 2) (D : ℝ) σ := by
    apply hzeroRaw.trans
    have hscale := caseI_claim145Scale_le_transported_remainderUnit S H
      (K := K) (Δ := Δ)
      hH hD3 hCpos hCB.le (by norm_num : (1 : ℝ) ≤ 2) h2σ hEtransport
    simpa only [← mul_assoc, div_mul_cancel₀ _ hCpos.ne'] using hscale
  have hAactual : 0 ≤ CB / C + 6 * L * R /
      (C * Real.exp (Real.sqrt K)) + 12 * R := by
    positivity
  have hAupper : CB / C + 6 * L * R /
      (C * Real.exp (Real.sqrt K)) + 12 * R ≤ Amax := by
    have hb := caseI_endpointCoefficient_le_commonScale
      (A := (1 : ℝ)) (C := C) (C145 := CB) (K := K) (L := L) (R := R)
      (by norm_num) hC3 (by simpa using hCBC) (by linarith [hL]) (by linarith [hR])
    norm_num at hb
    norm_num only [L, CB, Amax] at hb ⊢
    simpa only [one_div, add_comm] using add_le_add_right hb (12*R)
  obtain ⟨qgap, hqgap, hcoefGap⟩ := hcoef C1 K (D : ℝ)
    (CB / C + 6 * L * R / (C * Real.exp (Real.sqrt K)) + 12 * R)
    hcoefC1 hK (by exact_mod_cast hD2) hAactual hAupper hlarge
  have hqrho : q12.ρ = qgap.ρ := by rw [hq12, hqgap]
  have hbudget : 0 ≤ sigma12InheritedBudget S H M D z C K d Δ 2 := by
    unfold sigma12InheritedBudget
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hCpos.le (Real.exp_pos _).le)
          (suzukiVProduct_pos S (z : ℝ)).le)
        (Real.rpow_nonneg (Real.log_nonneg hDreal.le) _))
      (errorEnvelope_nonneg H M hDreal (by norm_num)
        (hH.positive _ _ (by norm_num)).le)
  have hside : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        suzukiVProduct S z * (6 * K ^ 2 * finiteSourceLayer 1 2 (M - 1) 1 /
          Real.log ((D : ℝ) ^ (1 / σ))) +
        caseI1423Sigma12Endpoint S H M D z C K d Δ 2 σ ≤
      ((1 - q12.ρ) / 2) * sigma12InheritedBudget S H M D z C K d Δ 2 := by
    rw [hqrho]
    exact mixed_three_remainders_half_gap hbudget hzeroUnit hend.1 hend.2 hcoefGap
  have h2raw := lemma144_sigmaTwo_eq_zero_of_kappaOne_caseI
    (N := M) S hD4 (by norm_num : (2 : ℝ) ≤ 2) hz
  have h2 : suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / (2 : ℝ))) = 0 := by
    simpa [d, Δ, Θ, L, lemma144_realTau_eq_s_of_caseI hD4 (by norm_num : (2 : ℝ) ≤ 2)] using h2raw
  have hcarrier : sigmaOneCarrier (suzukiSupportedBelow S z) D σ 2 =
      sigmaOneCarrier S.prodPrimes.primeFactors D σ 2 := by
    ext p
    simp only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpS, _⟩, hpw, hpv⟩; exact ⟨hpS, hpw, hpv⟩
    · rintro ⟨hpS, hpw, hpv⟩
      exact ⟨⟨hpS, (nat_lt_natCeil_iff_lt_real
        (natCast_rpow_one_div_pos (by omega) (2 : ℝ)) hz).2 hpv⟩, hpw, hpv⟩
  have hmiddle : suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ))
      ((D : ℝ) ^ (1 / (2 : ℝ))) ≤
      sigmaEleven (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (suzukiVProduct S z) 2 M D σ 2 +
        sigmaTwelve (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S z) C K Δ M D σ 2 +
        C * Real.exp (Real.sqrt K) * suzukiVProduct S z * polynomialCorrectionWeight *
          polynomialInheritedSum S D z σ 2 := by
    change sigmaOne (suzukiSupportedBelow S z) S.nu (suzukiActualT S) M D σ 2 ≤ _
    rw [mixed_sigmaOne_reassemble S C K (suzukiSupportedBelow S z) M D z σ 2 hcarrier]
    exact add_le_add h10 le_rfl
  have hKpow : 1 ≤ K ^ (7 : ℝ) := Real.one_le_rpow (by linarith only [hK]) (by norm_num)
  have hC1log : C1 ≤ Real.log (D : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hKpow (show 0 ≤ C1 by linarith only [hC1one])
    nlinarith only [hh, hlarge]
  have hLcut : (logPowerCutoff 32 : ℝ) ≤ Real.log (D : ℝ) := by
    have hh : (logPowerCutoff 32 : ℝ) ≤ C1coef := Nat.cast_le.mpr mixedEndpointC1_gate
    exact hh.trans (hcoefC1.trans hC1log)
  have hKlevel : K ^ (7 : ℝ) ≤ Real.log (D : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hC1one (Real.rpow_nonneg (by linarith only [hK]) (7 : ℝ))
    nlinarith only [hh, hlarge]
  dsimp [CaseIEvenEndpointSigma11Edge] at h11
  have hactual : suzukiActualT S M D z ≤ suzukiVProduct S z * finiteSourceLayer 1 2 M 2 +
      q12.ρ * sigma12InheritedBudget S H M D z C K 16 (1 / 2) 2 +
      (suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        suzukiVProduct S z * (6 * K ^ 2 * finiteSourceLayer 1 2 (M - 1) 1 /
          Real.log ((D : ℝ) ^ (1 / σ))) +
        caseI1423Sigma12Endpoint S H M D z C K d Δ 2 σ) +
      C * Real.exp (Real.sqrt K) * suzukiVProduct S z * polynomialCorrectionWeight *
        polynomialInheritedSum S D z σ 2 := by
    rw [h149, h2]
    linarith only [hmiddle, h11, h12qSupported]
  exact mixed_caseI_close S H hH hCpos.le hDreal (by norm_num) h2σ hz g.hpowerS g.hpowerSigma
    g.hpowerOrder hK hlocal hLcut hKlevel hq12 hside hactual

#print axioms numerical_mixed_even_cutoff
end ChenEffective