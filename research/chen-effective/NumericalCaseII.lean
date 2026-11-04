import NumericalCaseIIGap
import NumericalCaseIITransport

open scoped Classical BigOperators Interval
open Set Filter Finset Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

/-- A threshold for D must enter a bound on log D in logarithmic coordinates. -/
noncomputable def c1LogBudget (x : ℝ) : ℝ := max 0 (Real.log x)

theorem le_of_c1LogBudget {x D : ℝ} (hD : 0 < D)
    (h : c1LogBudget x ≤ Real.log D) : x ≤ D := by
  by_cases hx : 0 < x
  · have hl : Real.log x ≤ Real.log D := (le_max_right _ _).trans h
    have he := Real.exp_le_exp.mpr hl
    simpa only [Real.exp_log hx,Real.exp_log hD] using he
  · exact (le_of_not_gt hx).trans hD.le

theorem c1LogBudget_le {x B : ℝ} (hx : 0 ≤ x) (hB : 1 ≤ B) (hxB : x ≤ B) :
    c1LogBudget x ≤ B := by
  apply max_le (zero_le_one.trans hB)
  by_cases hx0 : x=0
  · simpa only [hx0,Real.log_zero] using zero_le_one.trans hB
  · exact (Real.log_le_sub_one_of_pos (lt_of_le_of_ne hx (Ne.symm hx0))).trans (by linarith only [hxB])
noncomputable def caseIIC1 : ℝ :=
  3 + max 0 caseIIGapC1 + max 0 caseBSourceC1 + c1LogBudget sourceRoundedCutoff +
    c1LogBudget (transportCaseIICutoff : ℝ) + c1LogBudget (recursiveNatCutoff : ℝ) + c1LogBudget claim146FullCutoff +
    c1LogBudget (Real.exp 1) + c1LogBudget (Real.exp (max 1 (3*((1+3*(16 : ℝ))*4^(16 : ℝ))))) +
    c1LogBudget ((2 : ℕ)^2 : ℝ)
theorem numerical_caseII_cutoff
    (H : Section13HatLayers)
    {Dmin : ℕ} {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ)
    (hDmin : 2 ≤ Dmin)
    (hd16 : d=16) (hΔhalf : Δ=1/2) (hΘ7 : Θ=7) (hDmin2 : Dmin=2) :
    ∃ C1min : ℝ, C1min = caseIIC1 ∧ 1 ≤ C1min ∧
      ∀ (S : BoundingSieve) (C1 C K : ℝ) (N D : ℕ) (s : ℝ),
        C1min ≤ C1 → 3 ≤ C → 2 ≤ K → 2 ≤ D →
        HasDimensionOneLocalProductBound S K →
        C1 * K ^ Θ < Real.log (D : ℝ) →
        Odd N → 3 ≤ N → 1 < s → s ≤ 3 →
        Lemma144MovingDomainGlobalDepthAt S H C K d Δ (N - 1) Dmin →
        Lemma144CaseIISameCAt S H N D d Δ C K s := by
  subst d Δ Θ Dmin
  let d : ℝ := 16
  let Δ : ℝ := 1/2
  let Θ : ℝ := 7
  let Dmin : ℕ := 2
  have hd1 : 1 < d := by norm_num [d]
  have hDeltaPos : 0 < Δ := by norm_num [Δ]
  have hDeltaLt : Δ < 1 := by norm_num [Δ]
  let Dg := sourceRoundedCutoff
  have hg := numerical_source_rounded_geometry
  let Derr := transportCaseIICutoff
  have herrorAt := numerical_caseII_error_transport H hH hd1 rfl
  let Dcoord := recursiveNatCutoff
  have hcoordinateAt := numerical_recursive_coordinate_uniform
  let D146 := claim146FullCutoff
  have h146 := fun (D : ℝ) (hD : D146 ≤ D) => numerical_claim146 hH hD
  obtain ⟨_, rfl, hCgap1, hgap⟩ := numerical_caseII_bracket_gap hH hsrc rfl rfl rfl
  let Cgap := caseIIGapC1
  let Ccase := caseBSourceC1
  let CB : ℝ := 1
  have hCcase0 : 0 < Ccase := by unfold Ccase caseBSourceC1; positivity
  have hCB0 : 0 < CB := zero_lt_one
  have hCaseBAll := numerical_caseB_cutoff H hH
  let Dconst := Real.exp 1
  have hconst3 : ∀ D : ℝ, Dconst ≤ D → CB ≤ 27*3*(1-Δ)*Real.log D/32 := by
    intro D hD
    have hDpos : 0 < D := (Real.exp_pos 1).trans_le hD
    have hlog : 1 ≤ Real.log D := (Real.le_log_iff_exp_le hDpos).mpr hD
    dsimp [CB, Δ]
    nlinarith only [hlog]
  let A : ℝ := (1 + 3 * d) * (4 : ℝ) ^ d
  let Dlarge : ℝ := Real.exp (max 1 (3 * A))
  let C1min : ℝ :=
    3 + max 0 Cgap + max 0 Ccase + c1LogBudget Dg +
      c1LogBudget (Derr : ℝ) + c1LogBudget (Dcoord : ℝ) + c1LogBudget D146 + c1LogBudget Dconst +
      c1LogBudget Dlarge + c1LogBudget (Dmin ^ 2 : ℝ)
  have hmGap : 0 ≤ max (0 : ℝ) Cgap := le_max_left _ _
  have hmCase : 0 ≤ max (0 : ℝ) Ccase := le_max_left _ _
  have hmDg : 0 ≤ c1LogBudget Dg := le_max_left _ _
  have hmErr : 0 ≤ c1LogBudget (Derr : ℝ) := le_max_left _ _
  have hmCoord : 0 ≤ c1LogBudget (Dcoord : ℝ) := le_max_left _ _
  have hm146 : 0 ≤ c1LogBudget D146 := le_max_left _ _
  have hmConst : 0 ≤ c1LogBudget Dconst := le_max_left _ _
  have hmLarge : 0 ≤ c1LogBudget Dlarge := le_max_left _ _
  have hmSq : 0 ≤ c1LogBudget (Dmin^2 : ℝ) := le_max_left _ _
  have hCmin1 : 1 ≤ C1min := by
    dsimp only [C1min]
    linarith only [hmGap,hmCase,hmDg,hmErr,hmCoord,hm146,hmConst,hmLarge,hmSq]
  refine ⟨C1min, rfl, hCmin1, ?_⟩
  intro S C1 C K N D s hCmin hC3 hK hD2 hlocal hlarge hN hN3 hs1 hs3 hglobal
  have hCaseB := hCaseBAll S
  have hC10 : 0 ≤ C1 := hCmin1.trans hCmin |>.trans' zero_le_one
  have hK1 : 1 ≤ K := by linarith
  have hKpow : 1 ≤ K ^ Θ := Real.one_le_rpow hK1 hsrc.hTheta_pos.le
  have hC1log : C1 < Real.log (D : ℝ) := by
    calc
      C1 = C1*1 := by ring
      _ ≤ C1*K^Θ := mul_le_mul_of_nonneg_left hKpow hC10
      _ < _ := hlarge
  have hCminlog : C1min < Real.log (D : ℝ) := hCmin.trans_lt hC1log
  have hDnat1 : 1 < D := by omega
  have hDreal1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast hDnat1
  have hD0 : (0 : ℝ) < (D : ℝ) := zero_lt_one.trans hDreal1
  have hcuts : Cgap ≤ C1min ∧ Ccase ≤ C1min ∧ c1LogBudget Dg ≤ C1min ∧
      c1LogBudget (Derr : ℝ) ≤ C1min ∧ c1LogBudget (Dcoord : ℝ) ≤ C1min ∧ c1LogBudget D146 ≤ C1min ∧
      c1LogBudget Dconst ≤ C1min ∧ c1LogBudget Dlarge ≤ C1min ∧ c1LogBudget (Dmin^2 : ℝ) ≤ C1min := by
    dsimp only [C1min]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      linarith only [hmGap,hmCase,hmDg,hmErr,hmCoord,hm146,hmConst,hmLarge,hmSq,
        le_max_right (0 : ℝ) Cgap,le_max_right (0 : ℝ) Ccase]
  obtain ⟨hCgap,hCcase,hDg,hDerrR,hDcoordR,hD146,hDconst,hDlarge,hDsqR⟩ := hcuts
  have hDg := le_of_c1LogBudget hD0 (hDg.trans hCminlog.le)
  have hDerrR := le_of_c1LogBudget hD0 (hDerrR.trans hCminlog.le)
  have hDcoordR := le_of_c1LogBudget hD0 (hDcoordR.trans hCminlog.le)
  have hD146 := le_of_c1LogBudget hD0 (hD146.trans hCminlog.le)
  have hDconst := le_of_c1LogBudget hD0 (hDconst.trans hCminlog.le)
  have hDlarge := le_of_c1LogBudget hD0 (hDlarge.trans hCminlog.le)
  have hDsq : Dmin^2 ≤ D := by exact_mod_cast le_of_c1LogBudget hD0 (hDsqR.trans hCminlog.le)
  have herrorD := herrorAt D (by exact_mod_cast hDerrR) S
  have hcoordinateD := hcoordinateAt D (by exact_mod_cast hDcoordR) S
  have hCgap := hCgap.trans hCmin
  have hCcase := hCcase.trans hCmin
  have hD4 : 4 ≤ D := by
    have : 4 ≤ Dmin ^ 2 := by norm_num [Dmin]
    exact this.trans hDsq
  have hDnat1 : 1 < D := by omega
  have hDreal1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast hDnat1
  let y : ℕ := ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let σ : ℝ := sourceSigma (D : ℝ) d
  have g := hg S D hDg s hs1 hs3
  have hscale : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S y) D Dmin σ 3 := by
    simpa [d, Δ, Θ, Dmin, y, σ] using caseII_cubic_carrier_quotient_scale (d := d) S hDmin hDsq
  have hceil : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) → 2 ≤ p ∧ 2 * p ≤ D := by
    intro p hp _hpl hpu
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have hrootle : (D : ℝ) ^ (1 / (3 : ℝ)) ≤ (y : ℝ) := by
      simpa [d, Δ, Θ, Dmin, y] using Nat.le_ceil ((D : ℝ) ^ (1 / (3 : ℝ)))
    have hpD : (2 : ℝ) * p ≤ (D : ℝ) := by
      have hpyle : (p : ℝ) ≤ (y : ℝ) := hpu.le.trans hrootle
      linarith [g.hyDhalf]
    exact ⟨hp2, by exact_mod_cast hpD⟩
  have hdomains : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ 3,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1) ∧
      recursiveCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1) := by
    intro p hpCarrier
    have hp' := hpCarrier
    simp only [sigmaOneCarrier, Finset.mem_filter] at hp'
    have hpFull : p ∈ S.prodPrimes.primeFactors :=
      (Finset.mem_filter.mp hp'.1).1
    obtain ⟨hp2, h2p⟩ := hceil p hpFull hp'.2.1 (by simpa [d, Δ, Θ, Dmin, y] using hp'.2.2)
    have hinherited2 : 2 ≤ inheritedCoordinate D p :=
      (caseII_raw_inherited_gt_two hp2 (by omega) (by simpa [d, Δ, Θ, Dmin, y] using hp'.2.2)).le
    have hrec2 : 2 ≤ recursiveCoordinate D p :=
      hinherited2.trans (coordinate_bounds hp2 h2p).1
    have hNm : (N - 1) % 2 = 0 := by
      have hmod : N % 2 = 1 := Nat.odd_iff.mp hN
      omega
    constructor <;> simp [KappaOneModel.parityDomain, *]
  have herror : CaseIIErrorEnvelopeTransport S H N D d :=
    herrorD N s hN hs1 hs3 (by simpa [d, Δ, Θ, Dmin, y, σ] using hdomains)
  have hsource : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ 3,
      finiteSourceLayer 1 2 (N - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 2 (N - 1) (inheritedCoordinate D p) := by
    intro p hpCarrier
    have hp' := hpCarrier
    simp only [sigmaOneCarrier, Finset.mem_filter] at hp'
    have hpFull : p ∈ S.prodPrimes.primeFactors :=
      (Finset.mem_filter.mp hp'.1).1
    obtain ⟨hp2, h2p⟩ := hceil p hpFull hp'.2.1 (by simpa [d, Δ, Θ, Dmin, y] using hp'.2.2)
    exact finiteSourceLayer_recursive_le_inherited (by norm_num) (N - 1) D p
      hp2 h2p (hdomains p hpCarrier).1 (hdomains p hpCarrier).2
  have hIH : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S y)
      (fun n D' p => ∑ m ∈ sourceParityIndices n, suzukiSourceV S m D' p)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ N D σ 3 := by
    intro p hpCarrier
    have hpSupport : p ∈ suzukiSupportedBelow S y :=
      (Finset.mem_filter.mp hpCarrier).1
    have hpPrime : p.Prime :=
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hpSupport).1
    have hqmin := ceilDiv_ge_threshold_of_scale hpPrime.pos (hscale p hpCarrier)
    have hq2 : 2 ≤ D ⌈/⌉ p := hDmin.trans hqmin
    change (∑ m ∈ sourceParityIndices (N - 1),
      suzukiSourceV S m (D ⌈/⌉ p) p) ≤ _
    rw [sourceParityIndices_eq_actualParityCarrier,
      ← suzukiActualT_eq_parity_sum]
    have hpCarrierFull : p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 3 := by
      exact Finset.mem_filter.mpr ⟨
        (Finset.mem_filter.mp hpSupport).1, (Finset.mem_filter.mp hpCarrier).2⟩
    exact hglobal (D ⌈/⌉ p) p hqmin hq2 hpPrime.two_le
      (recursiveCoordinate D p) (hdomains p hpCarrier).2
      (by simpa [d, Δ, Θ, Dmin, σ] using hcoordinateD 3 (by norm_num) p hpCarrierFull)
      (recursiveCoordinate_power_identity hpPrime.two_le hq2)
  have hEndpoint : Claim14_5Regime 2 (D : ℝ) σ C K σ σ →
      (∑ p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / σ)⌉₊,
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) ≤
        caseIIOddClaim145Endpoint S d N D := by
    intro _
    have hrec := suzukiActualT_caseI_recurrence_natCeil
      (S := S) (N := N) (D := D) (s := σ)
      (by omega) (by omega) (by simpa [d, Δ, Θ, Dmin, σ] using g.h3σ) rfl
    rw [caseIIOddClaim145Endpoint]
    simp_rw [sourceParityIndices_eq_actualParityCarrier,
      ← suzukiActualT_eq_parity_sum]
    simpa [d, Δ, Θ, Dmin, σ] using le_of_eq hrec.symm
  have hnu : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ 3,
      0 ≤ S.nu p := by
    intro p hp
    have hpf : p ∈ S.prodPrimes.primeFactors :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    exact (S.nu_pos_of_prime p (Nat.mem_primeFactors.mp hpf).1
      (Nat.mem_primeFactors.mp hpf).2.1).le
  have hlog : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ 3,
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ) := by
    intro p hp
    have hps : p ∈ suzukiSupportedBelow S y := (Finset.mem_filter.mp hp).1
    have hpPrime : p.Prime :=
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hps).1
    have hqmin := ceilDiv_ge_threshold_of_scale hpPrime.pos (hscale p hp)
    have hq2 : 2 ≤ D ⌈/⌉ p := hDmin.trans hqmin
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ D ⌈/⌉ p by omega))
  have hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) →
      0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p) := by
    intro p hp _hpl hpu
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    exact (hH.positive _ _ (by
      have := caseII_raw_inherited_gt_two hp2 hDnat1 hpu
      linarith)).le
  have h1413 : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) →
      Claim14_13PointwisePremise H N (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ)) := by
    intro p hp hpl hpu
    obtain ⟨hp2, h2p⟩ := hceil p hp (by simpa [d, Δ, Θ, Dmin, σ] using hpl) hpu
    exact claim14_13_pointwise_carrier H (by omega) hp2 h2p hd1 hDeltaPos
      (by simpa [d, Δ, Θ, Dmin, inheritedCoordinate] using hT p hp hpl hpu)
  obtain ⟨hi, hii, hiiiAll⟩ := h146 (D : ℝ) hD146
  have hsign3 : 2 + (ErrorSign.ofDepth N).epsilon ≤ (3 : ℝ) := by
    rw [ErrorSign.ofDepth_of_odd hN]
    norm_num [ErrorSign.epsilon]
  have hiii := (hiiiAll (ErrorSign.ofDepth N) 3 hsign3 g.h3σ).le
  have hcut : 0 ≤ (1 - 1 / σ) ^ (1 - Δ) := by
    apply Real.rpow_nonneg
    have hσ0 : 0 < σ := by dsimp [σ]; linarith [g.h3σ]
    have : 1 / σ ≤ 1 := (div_le_one hσ0).2 (by linarith [g.h3σ])
    linarith
  have hLambda := lambda_three_le_perturb_three_mul_lambda_caseII
    hH.toSection13HatContract hDreal1 (by linarith : 0 ≤ d)
    (zero_lt_one.trans hs1) hs3
  have hE := one_third_le_errorEnvelope_caseII
    (d := d) hH.toSection13HatContract hN hDreal1 hs1 hs3
  have hP : 3 ≤ C * Real.exp (Real.sqrt K) := by
    have hexp : 1 ≤ Real.exp (Real.sqrt K) := Real.one_le_exp (Real.sqrt_nonneg K)
    calc
      3 ≤ C := hC3
      _ = C * 1 := by ring
      _ ≤ C * Real.exp (Real.sqrt K) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
  have hPE : 1 ≤ C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s := by
    nlinarith [mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by positivity : 0 ≤ C * Real.exp (Real.sqrt K))]


  have hrelative :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
        caseIIOddClaim145Endpoint S d N D + suzukiVProduct S (z : ℝ) *
          (finiteSourceLayer 1 2 N s +
            (C * Real.exp (Real.sqrt K)) * errorEnvelope H N (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ) *
              caseIIConcreteRoundedRelativeBracketSourceLarge N (D : ℝ) d Δ
                (sourceSigma (D : ℝ) d) K) := by
    exact caseII_total_le_doubleRounded_direct_sourceLarge_relative_natCeil_of_errorTransport
      (S := S) (H := H) (N := N) (D := D) (y := y) (z := z)
      (σ := σ) (C := C) (C1 := C) (K := K) (ΘK := σ)
      (Δ := Δ) (d := d) (B0 := caseIIOddClaim145Endpoint S d N D) (s := s)
      hH.toSection13HatContract hN (by omega) g.hycube g.hyceil g.hyDhalf
      g.h3σ g.hD g.hDlarge g.hwy g.hy2 g.hyr2 g.hw2 hEndpoint hnu
      (by linarith) hlog hdomains herror hIH
      (by
        rw [hH.toSection13HatContract.betaHat_eq, ErrorSign.ofDepth_of_odd hN]
        norm_num [ErrorSign.epsilon])
      hK hlocal (by simpa [d, Δ, Θ, Dmin, σ] using hii) hDeltaPos hDeltaLt
      (by simpa [d, Δ, Θ, Dmin, σ] using hceil) hT h1413 hs1 hs3 g.hyrzr g.hyz
      g.hyLower g.hyUpper g.hzceil g.hzr2 g.h3dlog hE hcut hiii
      (by rw [ErrorSign.ofDepth_of_odd hN]; exact hLambda) hP hPE
  have hB := hCaseB C1 K N D (sourceSigma (D : ℝ) d)
    hCcase hK hlocal hD2 (by linarith [g.h3σ]) hlarge le_rfl
  have hendpointClaim : caseIIOddClaim145Endpoint S d N D ≤
      CB * claim14_5Scale S H N (D : ℝ) d Δ
        (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) := by
    simpa [d, Δ, Θ, Dmin, CB, ActualClaim145BoundAt, caseIIOddClaim145Endpoint] using hB
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hlogLarge : 3 * A ≤ Real.log (D : ℝ) := by
    have hmax : max 1 (3 * A) ≤ Real.log (D : ℝ) := by
      apply (Real.le_log_iff_exp_le hD0).2
      exact hDlarge
    exact (le_max_right 1 (3 * A)).trans hmax
  have hcoordLarge : A ≤ (1 / 3 : ℝ) * Real.log (D : ℝ) := by
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
      (by simpa only [mul_comm] using hlogLarge)
  have hs0 : 0 < s := zero_lt_one.trans hs1
  have hrootD : (D : ℝ) ^ (1 / s) ≤ (D : ℝ) := by
    have hexp : 1 / s ≤ (1 : ℝ) := by rw [div_le_one hs0]; exact hs1.le
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hDreal1.le hexp
  have hzDnat : z ≤ D := by dsimp [z]; exact Nat.ceil_le.mpr hrootD
  have hzD : (z : ℝ) ≤ (D : ℝ) := by exact_mod_cast hzDnat
  have hV := suzukiVProduct_mono_antitone S hzD
  have hsdomain : s ∈ KappaOneModel.parityDomain 2 N := by
    rw [KappaOneModel.parityDomain, Nat.odd_iff.mp hN]
    norm_num
    exact hs1
  have hEtransport := errorEnvelope_coordinate_transport_full
    hH.toSection13HatContract
    (N := N) (D := (D : ℝ)) (d := d) (σ := sourceSigma (D : ℝ) d)
    (x := s) (y := sourceSigma (D : ℝ) d)
    (by linarith) hDreal1 (by simpa [d, Δ, Θ, Dmin, A] using hcoordLarge) hi hsdomain
    (hs3.trans g.h3σ) le_rfl
  have hEσ0 : 0 ≤ errorEnvelope H N (D : ℝ) d (sourceSigma (D : ℝ) d) :=
    errorEnvelope_nonneg H N hDreal1 (by linarith [g.h3σ])
      (hH.positive (ErrorSign.ofDepth N) _ (by linarith [g.h3σ])).le
  have hL : 0 ≤ (Real.log (D : ℝ)) ^ (-Δ) :=
    Real.rpow_nonneg (Real.log_pos hDreal1).le _
  have hVD : 0 ≤ claim14_5VProduct S (D : ℝ) := by
    simpa [d, Δ, Θ, Dmin, claim14_5VProduct, suzukiVProduct] using
      (suzukiVProduct_pos S (D : ℝ)).le
  have hVz : claim14_5VProduct S (D : ℝ) ≤ suzukiVProduct S (z : ℝ) := by
    simpa [d, Δ, Θ, Dmin, claim14_5VProduct, suzukiVProduct] using hV
  have hconstBase := hconst3 (D : ℝ) hDconst
  have hconstant : CB ≤ 27 * C * (1 - Δ) * Real.log (D : ℝ) / 32 := by
    calc
      CB ≤ 27 * 3 * (1 - Δ) * Real.log (D : ℝ) / 32 := hconstBase
      _ ≤ 27 * C * (1 - Δ) * Real.log (D : ℝ) / 32 := by
        gcongr
  have hgapD := hgap C1 K N D hCgap hK hD2 hlarge hN hN3
  have hscale :
      CB * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) ≤
        suzukiVProduct S (z : ℝ) *
          ((C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ)) *
            (1 - caseIIConcreteRoundedRelativeBracketSourceLarge N (D : ℝ)
              d Δ (sourceSigma (D : ℝ) d) K)) := by
    unfold claim14_5Scale
    simpa [d, Δ, Θ, Dmin, z, mul_assoc] using claim145_endpoint_absorbed_by_caseII_gap
      hVD hVz (Real.exp_pos (Real.sqrt K)).le hEσ0 hEtransport hL
      (Real.log_pos hDreal1) (by linarith [g.h3σ]) hDeltaLt.le
      hCB0.le (by linarith : 0 ≤ C) hgapD hconstant
  have hendpoint : caseIIOddClaim145Endpoint S d N D ≤
      suzukiVProduct S (z : ℝ) *
        ((C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ)) *
          (1 - caseIIConcreteRoundedRelativeBracketSourceLarge N (D : ℝ)
            d Δ (sourceSigma (D : ℝ) d) K)) := hendpointClaim.trans hscale
  dsimp [Lemma144CaseIISameCAt]
  simpa [d, Δ, Θ, Dmin, sourceParityIndices, z] using
    (caseII_sameC_of_relative_and_endpoint_gap
      (scale := C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
        (Real.log (D : ℝ)) ^ (-Δ))
      (bracket := caseIIConcreteRoundedRelativeBracketSourceLarge N (D : ℝ)
        d Δ (sourceSigma (D : ℝ) d) K)
      hendpoint hrelative)
#print axioms numerical_caseII_cutoff
end ChenEffective
