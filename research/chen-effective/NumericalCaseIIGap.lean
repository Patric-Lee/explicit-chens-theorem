import NumericalCaseIICoreDecay
import NumericalFiniteHat
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIISourceLargeLogUniform

open scoped Classical BigOperators Interval
open Set Filter Finset Topology MeasureTheory intervalIntegral
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

noncomputable def caseIIGapAmplitude : ℝ :=
  9*864+72*576+864*((3 : ℝ)/2)^(1/2 : ℝ)+27+(3+28*(3 : ℝ)^(16 : ℝ))
noncomputable def caseIIGapC1 : ℝ :=
  max (coreDecayCutoff caseIIGapAmplitude) (max (Real.exp 1) ((3 : ℝ)^(16 : ℝ)))

theorem numerical_caseII_endpoint_layers {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) :
    ∀ N : ℕ, Odd N → 3 ≤ N →
      finiteSourceLayer 1 2 N 3 ≤ 864 ∧ finiteSourceLayer 1 2 (N-1) 2 ≤ 576 := by
  intro N hN hN3
  have hn := Nat.odd_iff.mp hN
  have hnm : (N-1)%2 = 0 := by omega
  have h3dom : (3 : ℝ) ∈ KappaOneModel.parityDomain 2 N := by
    simp [KappaOneModel.parityDomain, hn]
    norm_num
  have h2dom : (2 : ℝ) ∈ KappaOneModel.parityDomain 2 (N-1) := by
    simp [KappaOneModel.parityDomain, hnm]
  have h3 := numerical_finite_layer_hat hH N 3 (by omega) h3dom
  have h2 := numerical_finite_layer_hat hH (N-1) 2 (by omega) h2dom
  have hu3 := numerical_hat_upper_two hH.toSection13HatContract (ErrorSign.ofDepth N) (by norm_num : (1 : ℝ) ≤ 3)
  have hu2 := numerical_hat_upper_two hH.toSection13HatContract (ErrorSign.ofDepth (N-1)) (by norm_num : (1 : ℝ) ≤ 2)

  constructor <;> nlinarith only [h3, h2, hu3, hu2]
theorem numerical_caseII_bracket_gap
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {d Δ Θ : ℝ} (hsrc : SuzukiClaim145SourceParameters d Δ Θ)
    (hd16 : d=16) (hΔhalf : Δ=1/2) (hΘ7 : Θ=7) :
    ∃ C1min : ℝ, C1min = caseIIGapC1 ∧ 1 ≤ C1min ∧
      ∀ (C1 K : ℝ) (N D : ℕ),
        C1min ≤ C1 → 2 ≤ K → 2 ≤ D →
        C1 * K ^ Θ < Real.log (D : ℝ) → Odd N → 3 ≤ N →
        27 * (1 - Δ) / (32 * sourceSigma (D : ℝ) d) ≤
          1 - caseIIConcreteRoundedRelativeBracketSourceLarge
            N (D : ℝ) d Δ (sourceSigma (D : ℝ) d) K := by
  subst d Δ Θ
  let d : ℝ := 16
  let Δ : ℝ := 1/2
  let Θ : ℝ := 7
  have hDeltaPos : 0 < Δ := by norm_num [Δ]
  have hDeltaLt : Δ < 1 := by norm_num [Δ]
  let L3 : ℝ := 864
  let L2 : ℝ := 576
  have hL3 : 0 ≤ L3 := by norm_num [L3]
  have hL2 : 0 ≤ L2 := by norm_num [L2]
  have hLayers := numerical_caseII_endpoint_layers hH
  let rΔ : ℝ := ((3 : ℝ) / 2) ^ Δ
  let p : ℝ := 3 ^ d
  let J : ℝ := 3 + 28 * p
  let M : ℝ := 9 * L3 + 72 * L2 + 864 * rΔ + 27 + J
  have hr0 : 0 ≤ rΔ := by dsimp [rΔ]; positivity
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hJ0 : 0 ≤ J := by dsimp [J]; positivity
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨Cdec, hCeq, hCdec, hdec⟩ := numerical_caseII_core_decay M hM0
  let C1min : ℝ := max Cdec (max (Real.exp 1) p)
  have hCmin : 1 ≤ C1min := hCdec.trans (le_max_left _ _)
  refine ⟨C1min, by dsimp [C1min]; rw [hCeq]; rfl, hCmin, ?_⟩
  intro C1 K N D hC1 hK hD hlarge hN hN3
  let x : ℝ := Real.log (D : ℝ)
  let σ : ℝ := sourceSigma (D : ℝ) d
  let c : ℝ := (1 - 1 / σ) ^ (1 - Δ)
  have hDreal : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hD1 : (1 : ℝ) < D := by exact_mod_cast (show 1 < D by omega)
  have hDreal1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast hD1
  have hx0 : 0 < x := by simpa [d, Δ, Θ, x] using Real.log_pos hDreal1
  have hCdecC : Cdec ≤ C1 := (le_max_left _ _).trans hC1
  have hxC : C1 < x := by
    have hK0 : 0 < K := by linarith
    have hKΘ1 : 1 ≤ K ^ Θ := Real.one_le_rpow (by linarith) hsrc.hTheta_pos.le
    calc
      C1 ≤ C1 * K ^ Θ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hKΘ1
          (zero_le_one.trans (hCmin.trans hC1))
      _ < x := by simpa [d, Δ, Θ, x] using hlarge
  have hxExp : Real.exp 1 < x :=
    ((le_max_left (Real.exp 1) p).trans (le_max_right Cdec _)).trans_lt
      (hC1.trans_lt hxC)
  have hxp : p < x :=
    ((le_max_right (Real.exp 1) p).trans (le_max_right Cdec _)).trans_lt
      (hC1.trans_lt hxC)
  have hx1 : 1 ≤ x := (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hxExp.le
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hKΘ : K ^ Θ < x := by
    calc
      K ^ Θ ≤ C1 * K ^ Θ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (hCmin.trans hC1) (Real.rpow_nonneg hK0.le _)
      _ < x := by simpa [d, Δ, Θ, x] using hlarge
  have hTheta1 : 1 ≤ Θ := hsrc.one_le_theta
  have hKlePow : K ≤ K ^ Θ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hK1 hTheta1
  have hKx : K ≤ x := hKlePow.trans hKΘ.le
  have hfac : 1 + 3 * K / x ≤ 4 := by
    have hratio : K / x ≤ 1 := (div_le_one hx0).2 hKx
    calc
      1 + 3 * K / x = 1 + 3 * (K / x) := by ring
      _ ≤ 1 + 3 * 1 := by gcongr
      _ = 4 := by norm_num
  have hfac0 : 0 ≤ 1 + 3 * K / x := by positivity
  have hDexp : Real.exp (Real.exp 1) ≤ (D : ℝ) := by
    apply (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < (D : ℝ))).mp
    simpa [d, Δ, Θ, x] using hxExp.le
  have hσ1 : 1 < σ := by
    simpa [d, Δ, Θ, σ, sourceSigma, SwitchingPrinciple.SuzukiLemma144KappaOne.sourceSigma] using
      SwitchingPrinciple.SuzukiLemma144KappaOne.sourceSigma_gt_one_of_large hsrc.d_pos hDexp
  have hσ0 : 0 < σ := zero_lt_one.trans hσ1
  have hc0 : 0 ≤ c := by
    dsimp [c]
    apply Real.rpow_nonneg
    rw [sub_nonneg, div_le_one hσ0]
    exact hσ1.le
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply Real.rpow_le_one
    · rw [sub_nonneg, div_le_one hσ0]
      exact hσ1.le
    · linarith [one_div_pos.mpr hσ0]
    · linarith [hDeltaLt]
  have hpow0 : 0 ≤ x ^ (Δ - 1) := Real.rpow_nonneg hx0.le _
  have hinvpow : x⁻¹ ≤ x ^ (Δ - 1) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hDeltaPos])
  obtain ⟨hLayer3, hLayer2⟩ := hLayers N hN hN3
  have hNm : (N - 1) % 2 = 0 := by
    have := Nat.odd_iff.mp hN
    omega
  have hLayer2nonneg : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2 := by
    apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) (N - 1)
    simp [KappaOneModel.parityDomain, hNm]
  have hA0 :
      caseIIAlgebraicEndpointCoeffSourceLarge N (D : ℝ) σ K ≤
        9 * K * L3 + 72 * K ^ 2 * σ * L2 := by
    unfold caseIIAlgebraicEndpointCoeffSourceLarge
    change 9 * K * finiteSourceLayer 1 2 N 3 +
      18 * K ^ 2 * σ * (1 + 3 * K / x) * finiteSourceLayer 1 2 (N - 1) 2 ≤ _
    have hfirst : 9 * K * finiteSourceLayer 1 2 N 3 ≤ 9 * K * L3 := by
      exact mul_le_mul_of_nonneg_left hLayer3 (by positivity)
    have hsecond :
        18 * K ^ 2 * σ * (1 + 3 * K / x) * finiteSourceLayer 1 2 (N - 1) 2 ≤
          72 * K ^ 2 * σ * L2 := by
      calc
        _ ≤ 18 * K ^ 2 * σ * 4 * L2 := by
          have hpos : 0 ≤ 18 * K ^ 2 * σ := by positivity
          have hterm2 : (1 + 3 * K / x) * finiteSourceLayer 1 2 (N - 1) 2 ≤ 4 * L2 :=
            mul_le_mul hfac hLayer2 hLayer2nonneg (by norm_num : (0 : ℝ) ≤ 4)
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hterm2 hpos
        _ = 72 * K ^ 2 * σ * L2 := by ring
    exact add_le_add hfirst hsecond
  have hQ :
      caseIIQDRelativeEndpointCoeffSourceLarge (D : ℝ) Δ K ≤
        864 * K ^ 2 * rΔ := by
    unfold caseIIQDRelativeEndpointCoeffSourceLarge
    change 216 * K ^ 2 * (1 + 3 * K / x) * ((3 : ℝ) / 2) ^ Δ ≤ _
    calc
      _ ≤ 216 * K ^ 2 * 4 * rΔ := by gcongr
      _ = 864 * K ^ 2 * rΔ := by ring
  have hbaseUnit : 1 ≤ K * σ := by
    calc
      1 ≤ σ := hσ1.le
      _ ≤ K * σ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hK1 hσ0.le
  have hKsigma : K * σ ≤ K ^ 2 * σ ^ 2 := by
    calc
      K * σ = (K * σ) * 1 := by ring
      _ ≤ (K * σ) * (K * σ) :=
        mul_le_mul_of_nonneg_left hbaseUnit (mul_nonneg hK0.le hσ0.le)
      _ = K ^ 2 * σ ^ 2 := by ring
  let T : ℝ := K ^ 2 * σ ^ 2 * x ^ (Δ - 1)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hEndScaled :
      caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K * σ ≤
        (9 * L3 + 72 * L2 + 864 * rΔ + 27) * T := by
    unfold caseIIEndpointRelativeCoeffSourceLarge
    change (caseIIAlgebraicEndpointCoeffSourceLarge N (D : ℝ) σ K * x ^ (Δ - 1) +
      σ * caseIIQDRelativeEndpointCoeffSourceLarge (D : ℝ) Δ K / x +
      27 * K * x ^ (Δ - 1)) * σ ≤ _
    have h0 : 9 * K * L3 * x ^ (Δ - 1) * σ ≤ 9 * L3 * T := by
      dsimp [T]
      have hL3pos : 0 ≤ 9 * L3 * x ^ (Δ - 1) := by positivity
      calc
        9 * K * L3 * x ^ (Δ - 1) * σ = (9 * L3 * x ^ (Δ - 1)) * (K * σ) := by ring
        _ ≤ (9 * L3 * x ^ (Δ - 1)) * (K ^ 2 * σ ^ 2) := mul_le_mul_of_nonneg_left hKsigma hL3pos
        _ = 9 * L3 * (K ^ 2 * σ ^ 2 * x ^ (Δ - 1)) := by ring
    have h1 : 72 * K ^ 2 * σ * L2 * x ^ (Δ - 1) * σ = 72 * L2 * T := by
      dsimp [T]
      ring
    have hqinv :
        σ * (864 * K ^ 2 * rΔ) / x * σ ≤ 864 * rΔ * T := by
      rw [div_eq_mul_inv]
      dsimp [T]
      have h864pos : 0 ≤ 864 * rΔ * K ^ 2 * σ ^ 2 := by positivity
      calc
        σ * (864 * K ^ 2 * rΔ) * x⁻¹ * σ =
            864 * rΔ * K ^ 2 * σ ^ 2 * x⁻¹ := by ring
        _ ≤ 864 * rΔ * K ^ 2 * σ ^ 2 * x ^ (Δ - 1) := mul_le_mul_of_nonneg_left hinvpow h864pos
        _ = 864 * rΔ * (K ^ 2 * σ ^ 2 * x ^ (Δ - 1)) := by ring
    have h2 : 27 * K * x ^ (Δ - 1) * σ ≤ 27 * T := by
      dsimp [T]
      have h27pos : 0 ≤ 27 * x ^ (Δ - 1) := by positivity
      calc
        27 * K * x ^ (Δ - 1) * σ = (27 * x ^ (Δ - 1)) * (K * σ) := by ring
        _ ≤ (27 * x ^ (Δ - 1)) * (K ^ 2 * σ ^ 2) := mul_le_mul_of_nonneg_left hKsigma h27pos
        _ = 27 * (K ^ 2 * σ ^ 2 * x ^ (Δ - 1)) := by ring
    calc
      (caseIIAlgebraicEndpointCoeffSourceLarge N (D : ℝ) σ K * x ^ (Δ - 1) +
          σ * caseIIQDRelativeEndpointCoeffSourceLarge (D : ℝ) Δ K / x +
          27 * K * x ^ (Δ - 1)) * σ =
        caseIIAlgebraicEndpointCoeffSourceLarge N (D : ℝ) σ K * x ^ (Δ - 1) * σ +
          σ * caseIIQDRelativeEndpointCoeffSourceLarge (D : ℝ) Δ K / x * σ +
          27 * K * x ^ (Δ - 1) * σ := by ring
      _ ≤ (9 * K * L3 + 72 * K ^ 2 * σ * L2) * x ^ (Δ - 1) * σ +
          σ * (864 * K ^ 2 * rΔ) / x * σ +
          27 * K * x ^ (Δ - 1) * σ := by
        gcongr
      _ = 9 * K * L3 * x ^ (Δ - 1) * σ +
          72 * K ^ 2 * σ * L2 * x ^ (Δ - 1) * σ +
          σ * (864 * K ^ 2 * rΔ) / x * σ +
          27 * K * x ^ (Δ - 1) * σ := by ring
      _ ≤ 9 * L3 * T + 72 * L2 * T + 864 * rΔ * T + 27 * T := by
        exact add_le_add (add_le_add (add_le_add h0 h1.le) hqinv) h2
      _ = (9 * L3 + 72 * L2 + 864 * rΔ + 27) * T := by ring
  have hpLog : 3 ^ d ≤ Real.log (D : ℝ) := by simpa [d, Δ, Θ, p, x] using hxp.le
  have hpert := perturbation_three_le_one_add_seven_ratio
    (D := (D : ℝ)) (d := d) (by simpa [d, Δ, Θ, x] using hx0) hsrc.d_pos.le hpLog
  let fac : ℝ := 1 + 3 * K / x
  have hmainPert : fac * c * perturbation (D : ℝ) d 0 3 ≤
      fac * c * (1 + 7 * (p / x)) := by
    exact mul_le_mul_of_nonneg_left hpert (mul_nonneg hfac0 hc0)
  have hexcess : fac * (1 + 7 * (p / x)) - 1 ≤ J * K / x := by
    have hxinv0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
    have hxinv1 : x⁻¹ ≤ 1 := (inv_le_one₀ hx0).2 hx1
    have hcross : x⁻¹ * x⁻¹ ≤ x⁻¹ := mul_le_of_le_one_left hxinv0 hxinv1
    dsimp [fac, J]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    have hcros := mul_le_mul_of_nonneg_left hcross
      (show 0 ≤ 21 * K * p by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hK1 (show 0 ≤ 7 * p by positivity)]
  have hIntegral :
      ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c) * σ ≤
        J * T := by
    have hraw :
        (1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c ≤ J * K / x := by
      calc
        _ ≤ fac * c * (1 + 7 * (p / x)) - c := by
          simpa [d, Δ, Θ, fac] using sub_le_sub_right hmainPert c
        _ = c * (fac * (1 + 7 * (p / x)) - 1) := by ring
        _ ≤ fac * (1 + 7 * (p / x)) - 1 := by
          apply mul_le_of_le_one_left _ hc1
          have hfac1 : 1 ≤ fac := by
            have : 0 ≤ 3 * K / x := by positivity
            dsimp [fac]; linarith
          have hsecond1 : 1 ≤ 1 + 7 * (p / x) := by
            have : 0 ≤ 7 * (p / x) := by positivity
            linarith
          have := mul_le_mul hfac1 hsecond1 (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
          nlinarith
        _ ≤ J * K / x := hexcess
    have hs := mul_le_mul_of_nonneg_right hraw hσ0.le
    dsimp [T]
    calc
      ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c) * σ ≤
          (J * K / x) * σ := hs
      _ = J * (K * σ) * x⁻¹ := by rw [div_eq_mul_inv]; ring
      _ ≤ J * (K ^ 2 * σ ^ 2) * x⁻¹ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKsigma (by positivity)) (by positivity)
      _ ≤ J * (K ^ 2 * σ ^ 2) * x ^ (Δ - 1) := mul_le_mul_of_nonneg_left hinvpow (by positivity)
      _ = J * (K ^ 2 * σ ^ 2 * x ^ (Δ - 1)) := by ring
  have hTotalScaled :
      (caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K +
        ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c)) * σ ≤
          M * T := by
    have hEnd2 : caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K * σ ≤
        (9 * L3 + 72 * L2 + 864 * rΔ + 27) * T := hEndScaled
    have hInt2 : ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c) * σ ≤ J * T := hIntegral
    calc
      (caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K +
        ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c)) * σ =
        caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K * σ +
          ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c) * σ := by ring
      _ ≤ (9 * L3 + 72 * L2 + 864 * rΔ + 27) * T + J * T := add_le_add hEnd2 hInt2
      _ = (9 * L3 + 72 * L2 + 864 * rΔ + 27 + J) * T := by ring
      _ = M * T := by rfl
  have hCore := hdec C1 K (D : ℝ) hCdecC hK hDreal hlarge
  have hCore' : M * T ≤ 5 * (1 - Δ) / 32 := by
    have hTotal : M * T = M * (K ^ 2 * σ ^ 2) * x ^ (Δ - 1) := by
      dsimp [T]
      ring
    have hCoreRe : M * (K ^ 2 * σ ^ 2) * x ^ (Δ - 1) ≤ 5 * (1 - Δ) / 32 := by
      have hd1 : M * (K ^ 2 * σ ^ 2) * x ^ (Δ - 1) = M * K ^ 2 * σ ^ 2 * x ^ (Δ - 1) := by ring
      rw [hd1]
      exact hCore
    rw [hTotal]
    exact hCoreRe
  have hExcess :
      caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K +
          ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c) ≤
        5 * (1 - Δ) / (32 * σ) := by
    apply (le_div_iff₀ (show 0 < 32 * σ by positivity)).2
    nlinarith [hTotalScaled.trans hCore']
  have hGap : (1 - Δ) / σ ≤ 1 - c := by
    simpa [d, Δ, Θ, c] using rpow_contraction_gap
      hDeltaPos hDeltaLt hσ1
  change 27 * (1 - Δ) / (32 * σ) ≤
    1 - ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 +
      caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K)
  have ht : caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K +
          ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c) ≤
        5 * (1 - Δ) / (32 * σ) := hExcess
  calc
    27 * (1 - Δ) / (32 * σ) = (1 - Δ) / σ - 5 * (1 - Δ) / (32 * σ) := by ring
    _ ≤ 1 - c - 5 * (1 - Δ) / (32 * σ) := by linarith [hGap]
    _ ≤ 1 - c - (caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K + ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c)) := by linarith [ht]
    _ = 1 - ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 + caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K) := by ring
#print axioms numerical_caseII_bracket_gap
end ChenEffective
