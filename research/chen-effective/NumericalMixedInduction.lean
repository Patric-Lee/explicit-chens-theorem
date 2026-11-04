import NumericalMixedBase
import NumericalMixedCaseI
import NumericalMixedEven
import NumericalMixedCaseII

open scoped Classical BigOperators Interval
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open SuzukiFiniteContinuousLayers SuzukiLemma144KappaOne SuzukiLemma144Equation1410
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem mixed_sourceSigma_three {D : ℝ} (hD : 1 < D)
    (hcut : (logPowerCutoff 32 : ℝ) ≤ Real.log D) : 3 ≤ sourceSigma D 16 := by
  have hL9 := real_log_power_cutoff_nine hcut
  have hL : 0 < Real.log D := Real.log_pos hD
  have hl := real_log_power_cutoff_log hcut
  norm_num only [Nat.cast_ofNat] at hl
  have hinner : Real.log D ≤ Real.log (27 * D) := by
    rw [Real.log_mul (by norm_num) (by linarith only [hD] : D ≠ 0)]
    have hh := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 27)
    linarith only [hh]
  have hell := Real.log_le_log hL hinner
  have hp : 1 ≤ (Real.log D) ^ (1 / 16 : ℝ) :=
    Real.one_le_rpow (by linarith only [hL9]) (by norm_num)
  unfold sourceSigma
  have he0 : 0 ≤ Real.log (Real.log (27 * D)) := by nlinarith only [hl, hell]
  nlinarith only [hl, hell, mul_le_mul_of_nonneg_right hp he0]

theorem mixed_drop_contraction (S : BoundingSieve) (H : Section13HatLayers)
    (hH : Section13HatSourceContract H) {M D z : ℕ} {C K s : ℝ}
    (hC : 0 ≤ C) (hD : 1 < (D : ℝ)) (hs : 0 < s)
    (h : suzukiActualT S M D z ≤ suzukiVProduct S z * finiteSourceLayer 1 2 M s +
      (1 - 1 / (10 * sourceSigma D 16)) * mixedBudget S H M D z C K 16 (1 / 2) s) :
    suzukiActualT S M D z ≤ suzukiVProduct S z *
      (finiteSourceLayer 1 2 M s + C * Real.exp (Real.sqrt K) * mixedError H M D 16 (1 / 2) s) := by
  have he := mixedError_nonneg hH.toSection13HatContract (d := (16 : ℝ))
    (Δ := (1 / 2 : ℝ)) hD hs M
  have hv := (suzukiVProduct_pos S (z : ℝ)).le
  have hB : 0 ≤ mixedBudget S H M D z C K 16 (1 / 2) s := by unfold mixedBudget; positivity
  have hσ : 0 < sourceSigma (D : ℝ) 16 := by
    have hD2 : 2 ≤ D := by
      have hh : 1 < D := by exact_mod_cast hD
      omega
    exact sourceSigma_pos_of_nat_two_le hD2
  have hh := mul_nonneg (show 0 ≤ 1 / (10 * sourceSigma D 16) by positivity) hB
  unfold mixedBudget at h hh
  nlinarith only [h, hh]

/-- The mixed error is preserved at every depth and every natural level.
Small logarithmic levels use the polynomial base coefficient. The compact
Case-I and even endpoint retain a strict gap, and the odd low strip is closed
from the same-depth cubic endpoint. -/
theorem numerical_mixed_suzuki (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (K : ℝ) (hK : 2 ≤ K) :
    ∀ C1 : ℝ, mixedSuzukiSeparator ≤ C1 →
      ∀ S : BoundingSieve, HasDimensionOneLocalProductBound S K →
        ∀ N : ℕ, 1 ≤ N →
          MixedMovingDomainNatCeilAt S H (mixedSuzukiCoefficient C1 K) K 16 (1 / 2) N 2 := by
  intro C1 hC1 S hlocal
  have hnum : numericalSuzukiC1 ≤ C1 := (le_max_left _ _).trans hC1
  have hnew : (mixedEndpointC1 : ℝ) ≤ C1 := (le_max_right _ _).trans hC1
  have hparts : 1 ≤ C1 ∧ caseBSourceC1 ≤ C1 ∧ caseIStrictC1 ≤ C1 ∧ caseIEvenC1 ≤ C1 ∧ caseIIC1 ≤ C1 := by
    simpa only [numericalSuzukiC1, max_le_iff] using hnum
  have hstrict : mixedStrictC1 ≤ C1 := by
    rcases (show 1 ≤ C1 ∧ (caseIEndpointC1 : ℝ) ≤ C1 ∧ (caseIScalarC1 : ℝ) ≤ C1 ∧
        sigmaZeroC1 ≤ C1 ∧ 1 ≤ C1 ∧ Real.log caseIStrictDcut ≤ C1 by
      simpa only [caseIStrictC1, max_le_iff] using hparts.2.2.1) with ⟨h1, _, hsc, hz, h1', hl⟩
    simpa only [mixedStrictC1, max_le_iff] using (show 1 ≤ C1 ∧ (mixedEndpointC1 : ℝ) ≤ C1 ∧
      (caseIScalarC1 : ℝ) ≤ C1 ∧ sigmaZeroC1 ≤ C1 ∧ 1 ≤ C1 ∧ Real.log caseIStrictDcut ≤ C1 from
      ⟨h1, hnew, hsc, hz, h1', hl⟩)
  have heven : mixedEvenC1 ≤ C1 := by
    rcases (show 1 ≤ C1 ∧ (caseIEndpointC1 : ℝ) ≤ C1 ∧ (caseIScalarC1 : ℝ) ≤ C1 ∧
        sigmaZeroC1 ≤ C1 ∧ 1 ≤ C1 ∧ Real.log caseIEvenDcut ≤ C1 by
      simpa only [caseIEvenC1, max_le_iff] using hparts.2.2.2.1) with ⟨h1, _, hsc, hz, h1', hl⟩
    simpa only [mixedEvenC1, max_le_iff] using (show 1 ≤ C1 ∧ (mixedEndpointC1 : ℝ) ≤ C1 ∧
      (caseIScalarC1 : ℝ) ≤ C1 ∧ sigmaZeroC1 ≤ C1 ∧ 1 ≤ C1 ∧ Real.log caseIEvenDcut ≤ C1 from
      ⟨h1, hnew, hsc, hz, h1', hl⟩)
  have hC10 : 0 ≤ C1 := zero_le_one.trans hparts.1
  have hsrc : SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2) 7 := by constructor <;> norm_num
  obtain ⟨_, rfl, _, hI⟩ := numerical_mixed_caseI_cutoff H hH hsrc rfl rfl rfl
  obtain ⟨_, rfl, _, hEven⟩ := numerical_mixed_even_cutoff H hH hsrc rfl rfl rfl
  let C145 := mixedClaimCoefficient C1 K
  let C := mixedSuzukiCoefficient C1 K
  have hC145 : 0 ≤ C145 := zero_le_one.trans (le_max_left _ _)
  have h36 : (36 : ℝ) ≤ C := le_max_left _ _
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 36).trans h36
  have hC3 : max 3 (1 : ℝ) ≤ C := by norm_num; linarith only [h36]
  have hC1C : 1 ≤ C := (by norm_num : (1 : ℝ) ≤ 36).trans h36
  have hnorm : claim145UniformNormalizationConstant C145 16 ≤ C :=
    (numerical_claim_normalization hC145).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hscalar (D : ℕ) (hD : 2 ≤ D) : C145 / (Real.log (D : ℝ) * sourceSigma D 16) ≤ C :=
    ((claim145_uniform_scalar_normalization C145 16 hC145 (by norm_num)).2 D hD).trans hnorm
  let Clow := lowStripNumericalConstant C1
  have hClow : 0 ≤ Clow := by unfold Clow lowStripNumericalConstant; positivity
  have hlowNorm : claim145UniformNormalizationConstant Clow 16 ≤ C :=
    (numerical_claim_normalization hClow).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbase := lemma14_4_base_one_full_global_allD (d := (16 : ℝ)) (Δ := (1 / 2 : ℝ))
    (C := C) (K := K) hH.toSection13HatContract
    (by norm_num : (1 / 2 : ℝ) < 1) (numerical_suzuki_base_constant.trans h36) hK hlocal
  change ∀ N : ℕ, 1 ≤ N → MixedMovingDomainNatCeilAt S H C K 16 (1 / 2) N 2
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    intro D hmin hD s hs hsig hz
    exact mixed_point_of_old S H hC (hbase D hmin hD s hs hsig hz)
  | succ N hN ih =>
    have hglobal := mixed_global_of_natCeil S H C K 16 (1 / 2) N 2 ih
    intro D _hmin hD s hs hsig hz
    have hM2 : 2 ≤ N + 1 := by omega
    have hD1 : (1 : ℝ) < D := by exact_mod_cast (show 1 < D by omega)
    have hs1 : 1 < s := by
      by_cases ho : (N + 1) % 2 = 1
      · have hh : (2 : ℝ) - 1 < s := by simpa [KappaOneModel.parityDomain, ho] using hs
        linarith only [hh]
      · have hh : 2 ≤ s := by simpa [KappaOneModel.parityDomain, ho] using hs
        linarith only [hh]
    have hstop (hs2 : 2 ≤ s)
        (hregime : Real.log (D : ℝ) ≤ C1 * K ^ (7 : ℝ) ∨ sourceSigma D 16 ≤ s) :=
      mixed_claim_to_point S H hH hC145 hD hs (hscalar D hD)
        (mixed_claim_regime S H hH hparts.2.1 hK hlocal hD hs2 hregime)
    by_cases hsmall : Real.log (D : ℝ) ≤ C1 * K ^ (7 : ℝ)
    · by_cases hs2 : 2 ≤ s
      · exact hstop hs2 (Or.inl hsmall)
      · have hodd : Odd (N + 1) := by
          by_contra hn
          have he := Nat.not_odd_iff_even.mp hn
          have hh : 2 ≤ s := by simpa [KappaOneModel.parityDomain, Nat.even_iff.mp he] using hs
          exact hs2 hh
        have hb := numerical_low_strip_actual S H hH.toSection13HatContract hC10 hK hD hodd hlocal
          hs1 (le_of_not_ge hs2) hsmall
        exact mixed_point_of_old S H hC
          (actualClaim145_to_moving_at_common_constant S H hClow (by norm_num) hlowNorm hH hD hs hb)
    · have hlarge : C1 * K ^ (7 : ℝ) < Real.log (D : ℝ) := lt_of_not_ge hsmall
      have hKpow : 1 ≤ K ^ (7 : ℝ) := Real.one_le_rpow (by linarith only [hK]) (by norm_num)
      have hC1log : C1 ≤ Real.log (D : ℝ) := by
        have hh := mul_le_mul_of_nonneg_left hKpow hC10
        nlinarith only [hh, hlarge]
      have hcut : (logPowerCutoff 32 : ℝ) ≤ Real.log (D : ℝ) :=
        (Nat.cast_le.mpr mixedEndpointC1_gate).trans (hnew.trans hC1log)
      have hKlevel : K ^ (7 : ℝ) ≤ Real.log (D : ℝ) := by
        have hh := mul_le_mul_of_nonneg_right hparts.1 (Real.rpow_nonneg (by linarith only [hK]) (7 : ℝ))
        nlinarith only [hh, hlarge]
      have hσ3 := mixed_sourceSigma_three hD1 hcut
      by_cases hfar : sourceSigma (D : ℝ) 16 ≤ s
      · exact hstop (by linarith only [hσ3, hfar]) (Or.inr hfar)
      · have hIpoint (t : ℝ) (htdom : t ∈ KappaOneModel.parityDomain 2 (N + 1))
            (htpred : t - 1 ∈ KappaOneModel.parityDomain 2 N) (ht : 2 ≤ t)
            (htlower : 2 + (ErrorSign.ofDepth (N + 1)).epsilon ≤ t) (htσ : t ≤ sourceSigma D 16) :=
          hI S C1 C K (N + 1) D t hstrict hC3 hK hlocal hM2 htdom
            (by simpa using htpred) ht htlower hlarge htσ (by rw [hH.betaHat_eq]; exact htlower)
            (by simpa using hglobal)
        rcases Nat.even_or_odd (N + 1) with hEvenM | hOddM
        · have hs2 : 2 ≤ s := by simpa [KappaOneModel.parityDomain, Nat.even_iff.mp hEvenM] using hs
          by_cases hseq : s = 2
          · subst s
            exact mixed_drop_contraction S H hH hC hD1 (by norm_num)
              (hEven S C1 C K (N + 1) D heven hC3 hK hlocal hEvenM hM2 hlarge (by simpa using hglobal))
          · have hs2lt : 2 < s := lt_of_le_of_ne hs2 (Ne.symm hseq)
            have hpredOdd : N % 2 = 1 := by have hh := Nat.even_iff.mp hEvenM; omega
            have hpredDom : s - 1 ∈ KappaOneModel.parityDomain 2 N := by
              simp [KappaOneModel.parityDomain, hpredOdd]
              linarith only [hs2lt]
            have hlower : 2 + (ErrorSign.ofDepth (N + 1)).epsilon ≤ s := by
              simpa [ErrorSign.ofDepth_of_even hEvenM, ErrorSign.epsilon] using hs2
            exact mixed_drop_contraction S H hH hC hD1 (zero_lt_one.trans hs1)
              (hIpoint s hs hpredDom hs2 hlower hsig)
        · have hpredEven : N % 2 = 0 := by have hh := Nat.odd_iff.mp hOddM; omega
          by_cases hs3 : 3 ≤ s
          · have hpredDom : s - 1 ∈ KappaOneModel.parityDomain 2 N := by
              simp [KappaOneModel.parityDomain, hpredEven]
              linarith only [hs3]
            have hlower : 2 + (ErrorSign.ofDepth (N + 1)).epsilon ≤ s := by
              simpa only [ErrorSign.ofDepth_of_odd hOddM, ErrorSign.epsilon,
                show (2 : ℝ) + 1 = 3 by norm_num] using hs3
            exact mixed_drop_contraction S H hH hC hD1 (zero_lt_one.trans hs1)
              (hIpoint s hs hpredDom (by linarith only [hs3]) hlower hsig)
          · have hdom3 : (3 : ℝ) ∈ KappaOneModel.parityDomain 2 (N + 1) := by
              norm_num [KappaOneModel.parityDomain, Nat.odd_iff.mp hOddM]
            have hpred2 : (3 : ℝ) - 1 ∈ KappaOneModel.parityDomain 2 N := by
              norm_num [KappaOneModel.parityDomain, hpredEven]
            have hlower : 2 + (ErrorSign.ofDepth (N + 1)).epsilon ≤ (3 : ℝ) := by
              norm_num [ErrorSign.ofDepth_of_odd hOddM, ErrorSign.epsilon]
            exact mixed_caseII_from_cube S H hH hC1C hK hlocal hOddM
              (by have hh := Nat.odd_iff.mp hOddM; omega) hD hs1 (le_of_not_ge hs3) hσ3 hcut hKlevel
              (hIpoint 3 hdom3 hpred2 (by norm_num) hlower hσ3)

#print axioms numerical_mixed_suzuki
end ChenEffective
