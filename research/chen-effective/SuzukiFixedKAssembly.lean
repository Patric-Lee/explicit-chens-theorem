import NumericalCaseABounded
import SuzukiCoefficientAssembly
import NumericalLocalProduct

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology Real
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144Equation1410
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable def fixedClaimCoefficient (C1 K : ℝ) : ℝ := max 1 (boundedCaseAConstant C1 K)
noncomputable def fixedSuzukiCoefficient (C1 K : ℝ) : ℝ :=
  suzukiCoefficient (fixedClaimCoefficient C1 K) C1

/-- Fixing the local-product parameter bypasses the qualitative large-K Case-A thresholds. -/
theorem fixedK_claim145 (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    {K C1 C1B : ℝ} (hK : 2 ≤ K) (hC1 : 0 ≤ C1) (hC1B : C1B ≤ C1)
    (hB : ∀ S : BoundingSieve, Claim145CaseBClosed S H 16 (1 / 2) 7 C1B 1) :
    ∀ (S : BoundingSieve) (N D : ℕ) (s : ℝ),
      HasDimensionOneLocalProductBound S K → 2 ≤ D → 2 ≤ s →
      (Real.log (D : ℝ) ≤ C1 * K ^ (7 : ℝ) ∨ sourceSigma (D : ℝ) 16 ≤ s) →
      ActualClaim145BoundAt S H N D 16 (1 / 2) K s (fixedClaimCoefficient C1 K) := by
  have hbounded := (numerical_caseA_boundedK H hH hC1 (show 1 ≤ K by linarith only [hK])).2
  intro S N D s hlocal hD hs hregime
  by_cases hsmall : Real.log (D : ℝ) ≤ C1 * K ^ (7 : ℝ)
  · have hb := hbounded S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ K s
      (by linarith only [hK]) le_rfl hlocal hD rfl hs hsmall
    have hb' : ActualClaim145BoundAt S H N D 16 (1 / 2) K s (boundedCaseAConstant C1 K) := by
      simpa only [ActualClaim145BoundAt, Claim14_5Bound, Nat.ceil_natCast] using hb
    exact hb'.mono_constant S H hH hD hs (le_max_right _ _)
  · have hsigma : sourceSigma (D : ℝ) 16 ≤ s := hregime.resolve_left hsmall
    have hb := hB S C1 K N D s hC1B hK hlocal hD hs (lt_of_not_ge hsmall) hsigma
    exact hb.mono_constant S H hH hD hs (le_max_left _ _)

/-- The coefficient is a displayed arithmetic function; only C1 admissibility remains qualitative. -/
theorem fixedK_suzuki_assembly
    (H : Section13HatLayers) (hH : Section13HatSourceContract H) (K : ℝ) (hK : 2 ≤ K) :
    ∃ C1min : ℝ, 0 < C1min ∧ ∀ C1 : ℝ, C1min ≤ C1 →
      ∀ (S : BoundingSieve), HasDimensionOneLocalProductBound S K →
        ∀ N : ℕ, 1 ≤ N →
          Lemma144MovingDomainNatCeilAt S H (fixedSuzukiCoefficient C1 K) K 16 (1 / 2) N 2 := by
  have hsrc : SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2) 7 := by
    constructor <;> norm_num
  obtain ⟨C1claim, hC1claim, hCaseB⟩ := numerical_caseB_coefficient_one H
    hsrc.hDelta_pos hsrc.hDelta_lt hsrc.h14_1 hsrc.one_le_theta hH
  obtain ⟨C1strict, hC1strict, hstrictAll⟩ := numerical_caseI_coefficient_one H hH hsrc
  obtain ⟨C1even, hC1even, hevenAll⟩ := numerical_caseI_even_coefficient_one H hH hsrc
  obtain ⟨C1caseII, hC1caseII, hcaseIIAll⟩ :=
    exists_lemma144_caseII_odd_sameC_sourceLargeLog_uniform_moving_uniform_in_S
      H hH hsrc (show 2 ≤ (2 : ℕ) by omega)
  let C1min : ℝ := max 1 (max C1claim (max C1strict (max C1even C1caseII)))
  have hC1min : 0 < C1min := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 hC1
  have hparts : C1claim ≤ C1 ∧ C1strict ≤ C1 ∧ C1even ≤ C1 ∧ C1caseII ≤ C1 := by
    have hm := (le_max_right 1 _).trans (show C1min ≤ C1 from hC1)
    simpa only [max_le_iff] using hm
  have hC10 : 0 ≤ C1 := hC1min.le.trans hC1
  let C145 := fixedClaimCoefficient C1 K
  have hC145 : 0 < C145 := zero_lt_one.trans_le (le_max_left _ _)
  have hclaim := fixedK_claim145 H hH hK hC10 hparts.1 hCaseB
  let Clow := lowStripNumericalConstant C1
  have hClow : 0 ≤ Clow := by dsimp [Clow, lowStripNumericalConstant]; positivity
  have hlow (S : BoundingSieve) (K : ℝ) (N D : ℕ) (s : ℝ)
      (hK : 2 ≤ K) (hN : Odd N) (hlocal : HasDimensionOneLocalProductBound S K)
      (hD : 2 ≤ D) (hs1 : 1 < s) (hs2 : s ≤ 2)
      (hsmall : Real.log (D : ℝ) ≤ C1 * K ^ (7 : ℝ)) :
      ActualClaim145BoundAt S H N D 16 (1 / 2) K s Clow :=
    numerical_low_strip_actual S H hH.toSection13HatContract hC10 hK hD hN hlocal hs1 hs2 hsmall
  let C := suzukiCoefficient C145 C1
  have h36 : (36 : ℝ) ≤ C := le_max_left _ _
  have hC3 : 3 ≤ C := (by norm_num : (3 : ℝ) ≤ 36).trans h36
  have hCstrict : max 3 (1 : ℝ) ≤ C := by norm_num; exact hC3
  have hCeven := hCstrict
  have hCbase : lemma144BaseOneGlobalConstant (1 / 2 : ℝ) ≤ C :=
    numerical_suzuki_base_constant.trans h36
  have hCnorm : claim145UniformNormalizationConstant C145 16 ≤ C :=
    (numerical_claim_normalization hC145.le).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  have hClowNorm : claim145UniformNormalizationConstant Clow 16 ≤ C :=
    (numerical_claim_normalization hClow).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  intro S hlocal
  apply lemma14_4_noDmin_allDepth_of_sourceLarge_strict_even S H
    hC145.le hsrc.d_pos hCnorm hH hsrc.hDelta_lt hCbase hK hlocal
  · intro N D s hN hD hs hregime
    exact hclaim S N D s hlocal hD hs hregime
  · intro M D s hM hsdom hspred hs hsLower hlarge hsSigma hthreshold hglobal
    exact hstrictAll S C1 C K M D s hparts.2.1 hCstrict hK hlocal hM
      hsdom hspred hs hsLower hlarge hsSigma hthreshold hglobal
  · intro M D hMeven hM hsSigma hlarge hglobal
    exact hevenAll S C1 C K M D hparts.2.2.1 hCeven hK hlocal hMeven hM hlarge hglobal
  · intro N D s hN hD hsdom hsSigma hz hside hglobal
    have hodd : Odd (N + 1) := hside.1
    have hM3 : 3 ≤ N + 1 := by
      have hmod : (N + 1) % 2 = 1 := Nat.odd_iff.mp hodd
      omega
    have hs1 : 1 < s := by
      have hs1' : (2 : ℝ) - 1 < s := by
        simpa [KappaOneModel.parityDomain, Nat.odd_iff.mp hodd] using hsdom
      norm_num at hs1' ⊢
      exact hs1'
    by_cases hlarge : C1 * K ^ (7 : ℝ) < Real.log (D : ℝ)
    · apply caseII_sameCAt_to_literal_moving S H
      exact hcaseIIAll S C1 C K (N + 1) D s hparts.2.2.2 hC3 hK hD
        hlocal hlarge hodd hM3 hs1 hside.2 (by simpa using hglobal)
    · have hsmall := le_of_not_gt hlarge
      by_cases hs2 : 2 ≤ s
      · exact actualClaim145_to_moving_at_common_constant S H hC145.le
          hsrc.d_pos hCnorm hH hD hsdom
          (hclaim S (N + 1) D s hlocal hD hs2 (Or.inl hsmall))
      · exact actualClaim145_to_moving_at_common_constant S H hClow
          hsrc.d_pos hClowNorm hH hD hsdom
          (hlow S K (N + 1) D s hK hodd hlocal hD hs1 (le_of_not_ge hs2) hsmall)


noncomputable def chenSuzukiCoefficient (C1 : ℝ) : ℝ :=
  fixedSuzukiCoefficient C1 numericalLocalProductK

/-- Literal source-family specialization: only an admissible numerical C1 is still needed. -/
theorem source_suzuki_coefficient_formula :
    ∃ C1min : ℝ, 0 < C1min ∧ ∀ C1 : ℝ, C1min ≤ C1 →
      ∀ N : ℕ, 1 ≤ N →
        Lemma144MovingDomainNatCeilAt (jurkatRichertSourceBoundingSieve N)
          jr1965Section13HatLayers (chenSuzukiCoefficient C1) numericalLocalProductK 16 (1 / 2) N 2 := by
  obtain ⟨C1min, hC1min, hall⟩ := fixedK_suzuki_assembly
    jr1965Section13HatLayers jr1965Section13HatSourceContract numericalLocalProductK numerical_local_product_two
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 hC1 N hN
  exact hall C1 hC1 (jurkatRichertSourceBoundingSieve N) (numerical_source_local_product N) N hN

#print axioms fixedK_claim145
#print axioms fixedK_suzuki_assembly
#print axioms source_suzuki_coefficient_formula
end ChenEffective
