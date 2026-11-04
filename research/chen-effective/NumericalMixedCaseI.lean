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
theorem numerical_mixed_caseI_cutoff
    (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ)
    (hd16 : d=16) (hΔhalf : Δ=1/2) (hΘ7 : Θ=7) :
    ∃ C1min : ℝ, C1min = mixedStrictC1 ∧ 1 ≤ C1min ∧
      ∀ (S : BoundingSieve) (C1 C K : ℝ) (M D : ℕ) (s : ℝ),
        C1min ≤ C1 → max 3 (1 : ℝ) ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K →
        2 ≤ M →
        s ∈ KappaOneModel.parityDomain 2 M →
        s - 1 ∈ KappaOneModel.parityDomain 2 (M - 1) →
        2 ≤ s → 2 + (ErrorSign.ofDepth M).epsilon ≤ s →
        C1 * K ^ Θ < Real.log (D : ℝ) →
        s ≤ sourceSigma (D : ℝ) d →
        H.betaHat + (ErrorSign.ofDepth M).epsilon ≤ s →
        MixedMovingDomainGlobalDepthAt S H C K d Δ (M - 1) 2 →
        suzukiActualT S M D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
          suzukiVProduct S ⌈(D : ℝ) ^ (1 / s)⌉₊ *
            finiteSourceLayer 1 2 M s +
          (1 - 1 / (10 * sourceSigma (D : ℝ) d)) * mixedBudget S H M D
            ⌈(D : ℝ) ^ (1 / s)⌉₊ C K d Δ s := by
  subst d Δ Θ
  let d : ℝ := 16
  let Δ : ℝ := 1/2
  let Θ : ℝ := 7
  have hd1 : 1 < d := by norm_num [d]
  let L : ℝ := 144
  have hL : 1 ≤ L := by norm_num [L]
  have hfinite := fun (N : ℕ) (s : ℝ) => numerical_finite_predecessor hH (N := N) (s := s)
  let R : ℝ := reverseRatioCap
  have hR : 1 ≤ R := reverseRatioCap_one
  have hratio := fun (sign : ErrorSign) (s σ : ℝ) => numerical_reverse_ratio hH sign (s := s) (σ := σ)
  let Amax : ℝ := 1+2*L*R+12*R
  let C1coef : ℝ := mixedEndpointC1
  have hC1coef : 1 ≤ C1coef := mixedEndpointC1_one
  have hcoef := mixed_endpoint_order_uniform
  let C1scalar : ℝ := caseIScalarC1
  have hC1scalar : 1 ≤ C1scalar := caseIScalarC1_one
  have hscalar := numerical_caseI1423_scalar
  obtain ⟨_, rfl, hC1B, hcaseB⟩ := numerical_sigma_zero_cutoff H
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
  let Dpkt : ℕ := 4
  have hpkt := numerical_caseI_pointwise_packet H hH hd1 hsrc.hDelta_pos
    (show 2 ≤ (2 : ℕ) by norm_num)
  let Dcut : ℝ := max 4 (max D12 (max D146 (max Dg
    (max (Drec : ℝ) (max (Derr : ℝ) (Dpkt : ℝ))))))
  have hDcut : 0 < Dcut := (by norm_num : (0 : ℝ) < 4).trans_le (le_max_left _ _)
  let C1cut := max 1 (Real.log Dcut)
  have hC1cut : 1 ≤ C1cut := le_max_left _ _
  have hcut := numerical_fixed_threshold hsrc.hTheta_pos hDcut
  let C1min : ℝ := max 1 (max C1coef (max C1scalar (max C1B C1cut)))
  have hC1min : 1 ≤ C1min := le_max_left _ _
  refine ⟨C1min, rfl, hC1min, ?_⟩
  intro S C1 C K M D s hC1 hCcommon hK hlocal hM hsdom hspred hs hsLower
    hlarge hsσ hthreshold hglobal
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
  obtain ⟨hD4real, hD12, hD146, hDg, hDrecReal, hDerrReal, hDpktReal⟩ :
      (4 : ℝ) ≤ D ∧ D12 ≤ D ∧ D146 ≤ D ∧ Dg ≤ D ∧
        (Drec : ℝ) ≤ D ∧ (Derr : ℝ) ≤ D ∧ (Dpkt : ℝ) ≤ D := by
    simpa only [Dcut, max_le_iff] using hDcutD.le
  have hD4 : 4 ≤ D := by exact_mod_cast hD4real
  have hD3 : 3 ≤ D := by omega
  have hD2 : 2 ≤ D := by omega
  have hDrec : Drec ≤ D := by exact_mod_cast hDrecReal
  have hDerr : Derr ≤ D := by exact_mod_cast hDerrReal
  have hDpkt : Dpkt ≤ D := by exact_mod_cast hDpktReal
  have g := hg D M hDg s hs hsσ
  have hrecursiveD := hrec D hDrec S
  have hinheritedForError : ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
      (sourceSigma (D : ℝ) d) s,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (M - 1) := by
    intro p hp
    have hp' := hp
    simp only [sigmaOneCarrier, Finset.mem_filter] at hp'
    apply parityDomain_mono hspred
    exact (MathlibNt.SieveTheory.caseI_inheritedCoordinate_gt
      (Nat.prime_of_mem_primeFactors hp'.1).two_le (by omega)
      (by linarith) hp'.2.2).le
  have herrorD := herr D hDerr S
  have herror := herrorD M s hs hinheritedForError (hrecursiveD s hs)
  obtain ⟨hprime, hscale, hinherited, hsource, herror', hceil, hT, h1413⟩ :=
    hpkt D hDpkt S M s hM hspred hs herror
  let σ : ℝ := sourceSigma (D : ℝ) d
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  have hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊ := rfl
  have hDreal : 1 < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hprimeZ : ∀ p ∈ suzukiSupportedBelow S z, p.Prime := by
    intro p hp; exact hprime p (Finset.mem_filter.mp hp).1
  have toFull : ∀ p, p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s →
      p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ s := by
    intro p hp
    simpa only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter] using
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1,
        (Finset.mem_filter.mp hp).2⟩
  have hscaleZ : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S z) D 2 σ s := by
    intro p hp; exact hscale p (toFull p hp)
  have hinheritedZ : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (M - 1) := by
    intro p hp; exact hinherited p (toFull p hp)
  have hsourceZ : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      finiteSourceLayer 1 2 (M - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 2 (M - 1) (inheritedCoordinate D p) := by
    intro p hp; exact hsource p (toFull p hp)
  have herrorZ : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
        errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (inheritedCoordinate D p) := by
    intro p hp; exact herror' p (toFull p hp)
  have hrecursiveZ : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d := by
    intro p hp; exact hrecursiveD s hs p (toFull p hp)
  have hpoint : PointwiseInductionContract
      (suzukiSupportedBelow S z) (mixedSubtractedTail S C K)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ M D σ s :=
    mixed_pointwise_of_globalIH S H C K d Δ M D 2 σ s
      (by norm_num) hprimeZ hscaleZ hinheritedZ
      (by intro p _; exact (suzukiVProduct_pos S p).le) hCpos.le hsourceZ herrorZ
      hrecursiveZ hglobal
  have h10 := equation14_10_finset_assembly
    (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
    (mixedSubtractedTail S C K) (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    (suzukiVProduct S z) 2 C K Δ M D σ s
    (ne_of_gt (suzukiVProduct_pos S z))
    (by intro p hp; have hpS := (Finset.mem_filter.mp hp).1
        exact (S.nu_pos_of_prime p (hprimeZ p hpS)
          ((Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpS).1).2.1)).le) hpoint
  have h149 : suzukiActualT S M D z =
      suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ)) ((D : ℝ) ^ (1 / s)) +
          suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / s)) := by
    by_cases hOddM : Odd M
    · have hs3 : 3 ≤ s := by
        norm_num [ErrorSign.ofDepth, hOddM, ErrorSign.epsilon] at hsLower
        exact hsLower
      exact suzuki_equation14_9_natCeil S hM (by omega) hs3 hz g.hpowerOrder
    · exact suzuki_equation14_9_strict S hM
        (by intro hodd; exact (hOddM hodd).elim) g.hpowerOrder
  have h11raw := caseI_sigmaEleven_le_finiteSourceLayer_add_endpoint
    (S := S) (β := (2 : ℝ)) (s := s) (τ := s) (σ := σ)
    (K := K) (N := M) (D := D) (z := z)
    (by norm_num) hsdom hspred le_rfl hsσ hDreal g.hpowerS g.hpowerS
      g.hpowerSigma g.hpowerOrder le_rfl hz hK hlocal
  have h11 : sigmaEleven (suzukiSupportedBelow S z) S.nu
      (fun p => suzukiVProduct S p) (suzukiVProduct S z) 2 M D σ s ≤
      suzukiVProduct S z * finiteSourceLayer 1 2 M s +
        caseI1423Sigma11Endpoint S M D z K s σ := by
    simpa [d, Δ, Θ, L, caseI1423Sigma11Endpoint, div_self (ne_of_gt (by linarith : 0 < s))] using h11raw
  obtain ⟨q12, hq12, _h12raw, h12q⟩ :=
    h12 S C K hK hlocal hCpos.le D M s z hD12 (by linarith) hsLower
      g.hsigma hsσ hDreal g.hpowerS g.hpowerSigma g.hpowerOrder hz
      hthreshold hceil hT h1413
  have hcarrier : sigmaOneCarrier (suzukiSupportedBelow S z) D σ s =
      sigmaOneCarrier S.prodPrimes.primeFactors D σ s := by
    ext p
    simp only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpS, _⟩, hpw, hpv⟩; exact ⟨hpS, hpw, hpv⟩
    · rintro ⟨hpS, hpw, hpv⟩
      exact ⟨⟨hpS, (nat_lt_natCeil_iff_lt_real
        (natCast_rpow_one_div_pos (by omega) s) hz).2 hpv⟩, hpw, hpv⟩
  have h12qSupported :
      sigmaTwelve (suzukiSupportedBelow S z) S.nu
          (fun p => suzukiVProduct S (p : ℝ))
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S (z : ℝ)) C K Δ M D σ s ≤
        q12.ρ * sigma12InheritedBudget S H M D z C K d Δ s +
          caseI1423Sigma12Endpoint S H M D z C K d Δ s σ := by
    rw [show suzukiSupportedBelow S z =
      S.prodPrimes.primeFactors.filter (fun p => p < z) from rfl]
    rw [sigmaTwelve_supportedBelow_eq_full S
      (fun p => suzukiVProduct S (p : ℝ))
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      (suzukiVProduct S (z : ℝ)) C K Δ M D z σ s (Nat.le_ceil _)]
    simpa [d, Δ, Θ, L, σ, caseI1423Sigma12Endpoint, sigma12EndpointRemainder,
      div_self (ne_of_gt (by linarith : 0 < s))] using h12q
  have hscalarD := hscalar C1 K (D : ℝ) hscalarC1 hK
    (by exact_mod_cast hD2) hlarge
  have hend := caseI1423EndpointSourceBounds_sharp_of_source
    S H C K d Δ L R hH hCpos hsrc.hDelta_pos hsrc.hDelta_lt hsrc.h14_1
      hL hfinite hR hratio D M s hD3 (by simpa only [d, Δ, show (1 : ℝ)-1/2=1/2 by norm_num] using hscalarD) hM hs hspred hsσ
  have hzσ : (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) :=
    g.hpowerOrder.trans (Nat.le_ceil _)
  have hzeroRaw := hcaseB S C1 C K M D z hcaseBC1 hCBC hK hlocal hD2
    hlarge hM hzσ
  have hi := (h146 (D : ℝ) hD146).1
  have hEtransport : errorEnvelope H M (D : ℝ) d σ ≤
      errorEnvelope H M (D : ℝ) d s := by
    apply errorEnvelope_endpoint_le_of_claim14_6 hH.toSection13HatContract hDreal hi
    rw [hH.betaHat_eq]
    exact ⟨hsLower, by simpa [d, Δ, Θ, L, σ] using hsσ⟩
  have hzeroUnit : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) ≤
      (CB / C) * caseI1423RemainderUnit
        (sigma12InheritedBudget S H M D z C K d Δ s) (D : ℝ) σ := by
    apply hzeroRaw.trans
    have hscale := caseI_claim145Scale_le_transported_remainderUnit S H
      (K := K) (Δ := Δ)
      hH hD3 hCpos hCB.le (by linarith : 1 ≤ s) hsσ hEtransport
    simpa only [← mul_assoc, div_mul_cancel₀ _ hCpos.ne'] using hscale
  have hAactual : 0 ≤ CB / C + 6 * L * R /
      (C * Real.exp (Real.sqrt K)) + 12 * R := by positivity
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
  have hbudget : 0 ≤ sigma12InheritedBudget S H M D z C K d Δ s := by
    unfold sigma12InheritedBudget
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hCpos.le (Real.exp_pos _).le)
          (suzukiVProduct_pos S (z : ℝ)).le)
        (Real.rpow_nonneg (Real.log_nonneg hDreal.le) _))
      (errorEnvelope_nonneg H M hDreal (by linarith)
        (hH.positive _ _ (by linarith)).le)
  have hside : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        caseI1423Sigma11Endpoint S M D z K s σ +
        caseI1423Sigma12Endpoint S H M D z C K d Δ s σ ≤
      ((1 - q12.ρ) / 2) * sigma12InheritedBudget S H M D z C K d Δ s := by
    rw [hqrho]
    exact mixed_three_remainders_half_gap hbudget hzeroUnit hend.1 hend.2 hcoefGap
  have h2raw := lemma144_sigmaTwo_eq_zero_of_kappaOne_caseI
    (N := M) S hD4 hs hz
  have h2 : suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / s)) = 0 := by
    simpa [d, Δ, Θ, L, lemma144_realTau_eq_s_of_caseI hD4 hs] using h2raw
  have hmiddle : suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ))
      ((D : ℝ) ^ (1 / s)) ≤
      sigmaEleven (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (suzukiVProduct S z) 2 M D σ s +
        sigmaTwelve (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S z) C K Δ M D σ s +
        C * Real.exp (Real.sqrt K) * suzukiVProduct S z * polynomialCorrectionWeight *
          polynomialInheritedSum S D z σ s := by
    change sigmaOne (suzukiSupportedBelow S z) S.nu (suzukiActualT S) M D σ s ≤ _
    rw [mixed_sigmaOne_reassemble S C K (suzukiSupportedBelow S z) M D z σ s hcarrier]
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
  have hactual : suzukiActualT S M D z ≤ suzukiVProduct S z * finiteSourceLayer 1 2 M s +
      q12.ρ * sigma12InheritedBudget S H M D z C K 16 (1 / 2) s +
      (suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        caseI1423Sigma11Endpoint S M D z K s σ +
        caseI1423Sigma12Endpoint S H M D z C K d Δ s σ) +
      C * Real.exp (Real.sqrt K) * suzukiVProduct S z * polynomialCorrectionWeight *
        polynomialInheritedSum S D z σ s := by
    rw [h149, h2]
    linarith only [hmiddle, h11, h12qSupported]
  exact mixed_caseI_close S H hH hCpos.le hDreal hs hsσ hz g.hpowerS g.hpowerSigma
    g.hpowerOrder hK hlocal hLcut hKlevel hq12 hside hactual

#print axioms numerical_mixed_caseI_cutoff
end ChenEffective