import OpenAIGrouped.Unit022
import OpenAIGrouped.Unit047
import OpenAIGrouped.Unit020
import OpenAIGrouped.Unit014
import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit049
import OpenAIGrouped.Unit046
import OpenAIGrouped.Unit048
import OpenAIGrouped.Unit016
import OpenAIGrouped.Unit021
import OpenAIGrouped.Unit025
import OpenAIGrouped.Unit015

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondRetainedRatioScalar.lean; sha256: 0a0907e9e530def29db3497b18f76bf639acfd3d4f8d21931211cc5441b93789 -/
section Source2000
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedRatioScalar
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRadicalBudget CenteredMomentSourceBlockWindows
open CenteredMomentSourceDyadicShell CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O

open CenteredMomentSecondNonexceptionalScalar

theorem ratio_penalty_le (r a:ℝ) (hr:0<r) (_ha:0≤a) (ha1:a≤1) :
    r/(1+r)*(max 1 (1/r))^a≤1 := by
  by_cases h:r≤1
  · have hi:1≤1/r:=(le_div_iff₀ hr).mpr (by linarith)
    rw [max_eq_right hi]
    have hp: (1/r)^a≤1/r:=Real.rpow_le_self_of_one_le hi ha1
    calc
      _≤r/(1+r)*(1/r):=mul_le_mul_of_nonneg_left hp (by positivity)
      _=1/(1+r):=by field_simp
      _≤1:=(div_le_one (by positivity)).mpr (by linarith)
  · have hi:1/r≤1:=(div_le_one hr).mpr (by linarith)
    rw [max_eq_left hi,Real.one_rpow,mul_one]
    exact (div_le_one (by positivity)).mpr (by linarith)

def retainedRatio (n:Fin 4→ℤ):ℝ :=
  dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))

theorem retainedRatio_pos (n:Fin 4→ℤ):0<retainedRatio n := by
  unfold retainedRatio
  exact div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))

theorem actual_envelope_scalar_ratio (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(_hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (a:ℝ)(ha:0≤a)(ha1:a≤1) :
    (outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))*
      (max 1 (1/retainedRatio n))^a≤
    (fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) := by
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hu:0<((∏P∈U,P.val).absNorm:ℝ):=by
    rw [map_prod,Nat.cast_prod]
    apply Finset.prod_pos
    intro P hP
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by rw [←commonPrime_span C D hC P]; exact (commonPrime_supported C D hC P).1))
  have hn (i:Fin 4):0<dyadicScale (n i):=dyadicScale_pos _
  let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hr:0<r:=div_pos (mul_pos (hn 0) (hn 1)) (mul_pos (hn 2) (hn 3))
  have hscale := (physical_effective_scale η t S β C D hC hD U R rows W K n hne).le
  have he : secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.span {commonFrequencyGenerator C D}).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm/((C.absNorm:ℝ)*D.absNorm) := by
    rw [secondEffectiveScale,←normValue_eq_embedding,normValue_mul]
    dsimp only [normValue]
    ring
  have hrat : secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
      dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))≤r := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hscale (dyadicScale_pos _).le) (mul_pos (hn 2) (hn 3)).le
  have hfrac : (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
      dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))/(1+r)*
        (max 1 (1/r))^a≤1 := by
    apply le_trans _ (ratio_penalty_le r a hr ha ha1)
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hrat (by positivity)) (Real.rpow_nonneg (by positivity) _)
  rw [outerScalar,normalizer,actual_partitionNormalizer C D hC]
  change _≤(fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))
  rw [childEnvelope,scalar_cancel _ _ _ _ _ _ _ _ _ r _ hc hd
    (dyadicScale_pos _) (dyadicScale_pos _) hu hr.le]
  rw [←he]
  calc
    _=((fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
      ((secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
        dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))/(1+r)*(max 1 (1/r))^a):=by
      dsimp only [retainedRatio,r];ring
    _≤_:=by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac
        (show 0≤(fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) by positivity)

theorem actual_source_envelope_scalar_ratio (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (Hsource:ℝ)(hsource:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (a:ℝ)(ha:0≤a)(ha1:a≤1) :
    (outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))*
      (max 1 (1/retainedRatio n))^a≤
    4*(fixedFactor:ℝ)*η.modulus.absNorm*Hsource/Real.sqrt ((C.absNorm:ℝ)*D.absNorm) := by
  apply (actual_envelope_scalar_ratio η t S β C D hC hD U R rows W K hK n hne a ha ha1).trans
  have hh:=mul_le_mul_of_nonneg_left
    (actual_residual_sqrt_cap η t S β C D hC hD U R rows W K n Hsource hsource hne)
    (show 0≤(fixedFactor:ℝ)*η.modulus.absNorm by positivity)
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentSecondRetainedRatioScalar

end

end OAI

end Source2000

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondRetainedRatioCost.lean; sha256: 6156b29c8c347e20cdf4fe484a32a709a213f9510196dfee9d7e83623e74d1ab -/
section Source2001
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondRetainedRatioCost
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedRatioScalar

theorem actual_canonical_child_ratio_cost (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃Ck:ℝ,0<Ck ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Kphys:ℝ,0<Kphys → ∀n:Fin 4→ℤ,
      let _r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
      ∀(s:Input ι) (τ:RayCharacter→Character),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let _A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      Family s.η C D hC hD U τ →
      s.W₁ 0=0 → s.W₂ 0=0 → 0≤sourceRadius s → sourceRadius s≤Z^B →
      ∀R:ℝ,
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₁*childEnvelope s.η C D U n*(max 1 (1/retainedRatio n))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₂*childEnvelope s.η C D U n*(max 1 (1/retainedRatio n))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock s.η s.t S β C D hC hD U R
        (partRows false s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        Ck*Z^(2*δ)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂ :=by
  obtain ⟨C0,Ce,hC0,hCe,hbound⟩:=actual_canonical_children lo hi W 1 J₁ J₂ B δ hB hδ
  have hfixed:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  refine ⟨4*(fixedFactor:ℝ)*(C0*Ce),by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n s τ hlo hhi R0 seed S β C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH0 hH R Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂ hleft hright
  let rows:=partRows false s.η χ₀ Q m C D U R
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hp:=profileCost_nonneg s
  have hhgt:=heightEnvelope_pos s.t
  have hpm1:=profileMoment_nonneg J₁
  have hpm2:=profileMoment_nonneg J₂
  by_cases hzero:physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n=0
  · rw [hzero,norm_zero,zero_div]
    positivity
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤sourceRadius s:=
    fun I hi=>(original_column_norm s R0 seed I hz1 hz2 hi).2
  let E:=childEnvelope s.η C D U n*(max 1 (1/retainedRatio n))^((1:ℝ)/6)
  have hdyad:0<dyadicScale (n 1):=dyadicScale_pos _
  have hE:0≤E:=by unfold E childEnvelope;positivity
  have hl:∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
      ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) C R0 b) (canonicalRadial (τ χ) Q n) L a≤
        (E₁*E)*(1+‖v‖)^(2*J₁):=by
    intro L hL hLN hsf χ v b a ha
    simpa only [E,mul_assoc] using hleft L hL hLN hsf χ v b a ha
  have hr:∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
      ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) D R0 b) (canonicalRadial (τ χ) Q n) L a≤
        (E₂*E)*(1+‖v‖)^(2*J₂):=by
    intro L hL hLN hsf χ v b a ha
    simpa only [E,mul_assoc] using hright L hL hLN hsf χ v b a ha
  have hh:=hZ.2 Kphys hKphys n s τ hlo hhi R0 seed C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH R Q m χ₀ hQ hm hml hm2 (E₁*E) (E₂*E) (mul_nonneg hE₁ hE) (mul_nonneg hE₂ hE) hl hr
  have hsqrt:Real.sqrt ((E₁*E)*(E₂*E))=E*Real.sqrt (E₁*E₂):=by
    rw [show (E₁*E)*(E₂*E)=E^2*(E₁*E₂) by ring,
      Real.sqrt_mul (sq_nonneg E),Real.sqrt_sq hE]
  simp only [pow_one,hsqrt] at hh
  have hscalar:=actual_source_envelope_scalar_ratio s.η s.t S β C D hC hD U R rows W Kphys hKphys n
    (sourceRadius s) hβ hzero ((1:ℝ)/6) (by norm_num) (by norm_num)
  let F:ℝ:=(C0*Ce)*Z^(2*δ)*profileCost s*Real.sqrt (E₁*E₂)*
    heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂
  have hF:0≤F:=by dsimp only [F];positivity
  have hsc:=mul_le_mul_of_nonneg_left hscalar hF
  apply hh.trans
  convert hsc using 1 <;> dsimp only [F,E] <;> ring

end SevenEighths.CenteredMomentSecondRetainedRatioCost

end

end OAI

end Source2001

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondFrozenRatioCost.lean; sha256: c998ec5d7e163cbcabd9104ef2d63f86a6a9b869f9ba97fb55166848a8f16711 -/
section Source2002
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondFrozenRatioCost
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
open CenteredMomentSecondRetainedRatioCost CenteredMomentSourceLiveColumn
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedRatioScalar

theorem actual_canonical_child_ratio_cost (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃Ck:ℝ,0<Ck ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Kphys:ℝ,0<Kphys → ∀n:Fin 4→ℤ,
      let _r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
      ∀(s:Input ι) (τ:RayCharacter→Character),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let _A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      Family s.η C D hC hD U τ →
      s.W₁ 0=0 → s.W₂ 0=0 → 0≤sourceRadius s → sourceRadius s≤Z^B →
      ∀R:ℝ,
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        frozenCoefficient b.val C R0 s.ν s.W s.P≠0 →
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₁*childEnvelope s.η C D U n*(max 1 (1/retainedRatio n))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        frozenCoefficient b.val D R0 s.ν s.W s.P≠0 →
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₂*childEnvelope s.η C D U n*(max 1 (1/retainedRatio n))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock s.η s.t S β C D hC hD U R
        (partRows false s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        Ck*Z^(2*δ)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂ :=by
  obtain ⟨C0,Ce,hC0,hCe,hbound⟩:=CenteredMomentSecondFrozenChosen.actual_canonical_children lo hi W 1 J₁ J₂ B δ hB hδ
  have hfixed:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  refine ⟨4*(fixedFactor:ℝ)*(C0*Ce),by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n s τ hlo hhi R0 seed S β C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH0 hH R Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂ hleft hright
  let rows:=partRows false s.η χ₀ Q m C D U R
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hp:=profileCost_nonneg s
  have hhgt:=heightEnvelope_pos s.t
  have hpm1:=profileMoment_nonneg J₁
  have hpm2:=profileMoment_nonneg J₂
  by_cases hzero:physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n=0
  · rw [hzero,norm_zero,zero_div]
    positivity
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤sourceRadius s:=
    fun I hi=>(original_column_norm s R0 seed I hz1 hz2 hi).2
  let E:=childEnvelope s.η C D U n*(max 1 (1/retainedRatio n))^((1:ℝ)/6)
  have hdyad:0<dyadicScale (n 1):=dyadicScale_pos _
  have hE:0≤E:=by unfold E childEnvelope;positivity
  have hl:∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        frozenCoefficient b.val C R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) C R0 b) (canonicalRadial (τ χ) Q n) L a≤
        (E₁*E)*(1+‖v‖)^(2*J₁):=by
    intro L hL hLN hsf χ v b hlive a ha
    simpa only [E,mul_assoc] using hleft L hL hLN hsf χ v b hlive a ha
  have hr:∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        frozenCoefficient b.val D R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) D R0 b) (canonicalRadial (τ χ) Q n) L a≤
        (E₂*E)*(1+‖v‖)^(2*J₂):=by
    intro L hL hLN hsf χ v b hlive a ha
    simpa only [E,mul_assoc] using hright L hL hLN hsf χ v b hlive a ha
  have hh:=hZ.2 Kphys hKphys n s τ hlo hhi R0 seed C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH R Q m χ₀ hQ hm hml hm2 (E₁*E) (E₂*E) (mul_nonneg hE₁ hE) (mul_nonneg hE₂ hE) hl hr
  have hsqrt:Real.sqrt ((E₁*E)*(E₂*E))=E*Real.sqrt (E₁*E₂):=by
    rw [show (E₁*E)*(E₂*E)=E^2*(E₁*E₂) by ring,
      Real.sqrt_mul (sq_nonneg E),Real.sqrt_sq hE]
  simp only [pow_one,hsqrt] at hh
  have hscalar:=actual_source_envelope_scalar_ratio s.η s.t S β C D hC hD U R rows W Kphys hKphys n
    (sourceRadius s) hβ hzero ((1:ℝ)/6) (by norm_num) (by norm_num)
  let F:ℝ:=(C0*Ce)*Z^(2*δ)*profileCost s*Real.sqrt (E₁*E₂)*
    heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂
  have hF:0≤F:=by dsimp only [F];positivity
  have hsc:=mul_le_mul_of_nonneg_left hscalar hF
  apply hh.trans
  convert hsc using 1 <;> dsimp only [F,E] <;> ring

end SevenEighths.CenteredMomentSecondFrozenRatioCost

end

end OAI

end Source2002

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondFrozenLiveSource.lean; sha256: 77bac9aa1f7d638d8611d812f83b88397d39a2fa8698abcf5b2ba218bbcc40d2 -/
section Source2003
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
open SevenEighths.CenteredMomentSecondNonexceptionalScalar

namespace SevenEighths.CenteredMomentSecondFrozenLiveSource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondFrozenRatioCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem original_nonexceptional_energy (lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (B L Cr δ ε:ℝ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr)(hδ:0<δ)(hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀s:Input ι,(∀i,s.lo i=lo i)→(∀i,s.hi i=hi i)→
      s.W₁ 0=0→s.W₂ 0=0→0≤sourceRadius s→sourceRadius s≤Z^B→
    ∀R0 seed:Ideal O,Squarefree seed→seed≠0→
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀(χ₀:RayCharacter)(Q:Ideal O)(m:O),Q≤Ideal.span {(72:O)}→
      m≠0→goodLambda∣m→(2:O)∣m→
    ∀Kphys Tsec ξ:ℝ,0<Kphys→frequencyRadius Tsec Z ξ≤Cr*Z^L→
    ∀E₁ E₂:ℝ,0≤E₁→0≤E₂→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ‖partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
      C*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ) := by
  obtain ⟨Ck,hCk,hblock⟩:=actual_canonical_child_ratio_cost lo hi W J₁ J₂ B δ hB hδ
  obtain ⟨Cm,hCm,hmass⟩:=source_part_harmonic_bound B L Cr ε hB hL hCr hε
  refine ⟨Ck*Cm,mul_pos hCk hCm,?_⟩
  filter_upwards [hblock,hmass] with Z hZ hmassZ
  refine ⟨hZ.1,?_⟩
  intro s hlo hhi hz1 hz2 hH0 hH R0 seed hseed hseed0 S β
  have hg (q:ActiveLabel S β):=actual_common_gates s R0 seed hseed hz1 hz2 q.val.1 q.val.2 q.property
  have hs (q:ActiveLabel S β):=commonLabels_supported (activeSource S β) _ _ q.property
  choose τ hf using fun (q:ActiveLabel S β) (U:Finset (CommonIndex q.val.1 q.val.2))=>
    exists_exceptional_family s.η q.val.1 q.val.2 (hs q).1 (hs q).2 (hg q).2.2.1 U
  refine ⟨τ,hf,?_⟩
  intro χ₀ Q m hQ hm hml hm2 Kphys Tsec ξ hKphys hR E₁ E₂ hE₁ hE₂ hleft hright
  let F:=Ck*Z^(2*δ)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
    Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂
  have hF:0≤F:=by
    have hp:=profileCost_nonneg s
    have ht:=heightEnvelope_pos s.t
    have hm1:=profileMoment_nonneg J₁
    have hm2:=profileMoment_nonneg J₂
    have hz:0<Z:=zero_lt_one.trans hZ.1
    dsimp only [F]
    positivity
  have hsum:=hmassZ seed hseed hseed0 S β
    (fun I _ hI=>original_column_mask s R0 seed I hI)
    (fun I _ hI=>(original_column_norm s R0 seed I hz1 hz2 hI).2.trans hH)
    false s.η χ₀ Q m s.t W Kphys Tsec ξ (sourceRadius s) (volume s.toData) F
    hKphys hR hH (volume_pos s.toData) hF
  have hlocal:∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      ‖physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))‖/volume s.toData≤F*pairWeight q.val.1 q.val.2:=by
    intro q hq U n
    by_cases hzero:physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))=0
    · rw [hzero,norm_zero,zero_div]
      exact mul_nonneg hF (pairWeight_nonneg _ _)
    · have hh:=hZ.2 Kphys hKphys (fun i=>(n i:ℤ)) s (τ q U) hlo hhi R0 seed
        q.val.1 q.val.2 (hs q).1 (hs q).2 (hg q).2.2.2.1 (hg q).2.2.2.2.1
        ((hg q).2.2.2.2.2.1.trans hH) ((hg q).2.2.2.2.2.2.trans hH) (hg q).2.2.1 U (hf q U)
        hz1 hz2 hH0 hH (frequencyRadius Tsec Z ξ) Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂
        (hleft q hq U n hzero) (hright q hq U n hzero)
      rw [←physicalBlock_active]
      exact hh.trans_eq (by dsimp only [F,pairWeight];ring)
  have hh:=hsum hlocal
  apply hh.trans_eq
  have hp:Z^(2*δ)*Z^ε=Z^(2*δ+ε):=by rw [Real.rpow_add (zero_lt_one.trans hZ.1)]
  dsimp only [F]
  calc
    _=(Ck*Cm)*(Z^(2*δ)*Z^ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(seed.absNorm:ℝ):=by ring
    _=_:=by rw [hp]
end SevenEighths.CenteredMomentSecondFrozenLiveSource

end

end OAI

end Source2003

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondFrozenLiveDescent.lean; sha256: 969ab0a909d7a4b5deece76ea6c94d5f43c7ca7563f790e3036ee5ac914de2d7 -/
section Source2004
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
open SevenEighths.CenteredMomentSecondNonexceptionalScalar

namespace SevenEighths.CenteredMomentSecondFrozenLiveDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondFrozenRatioCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

theorem original_source_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      Cmain*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ)+
      Cdiag*Kphys*‖paperRadialFourier W 0‖*
        (2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*(∏i,s.M i))^2*
        (1+(∏i,hi i)*whi*whi)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ)+
      Cexc*profileFactor Sprofile s p J Q Kc*
        Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)+
      Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys*Z^(-saving) :=by
  obtain ⟨Cmain,hCmain,hmain⟩:=
    CenteredMomentSecondFrozenLiveSource.original_nonexceptional_energy lo hi W J₁ J₂
      B B 1 δ ε hB hB zero_lt_one hδ hε
  obtain ⟨J,Sprofile,SΦ,hSp,Cexc,Cdiag,Ctail,hCexc,hCdiag,hCtail,hrem⟩:=
    CenteredMomentSecondSourceRemainder.original_source_remainder wlo whi hwlo hwhi
      lo hi hhi W ε δ θ B ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sprofile,SΦ,hSp,Cmain,Cexc,Cdiag,Ctail,hCmain,hCexc,hCdiag,hCtail,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hrem⟩:=hrem Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hmain,hrem] with Z hmZ hrZ
  refine ⟨hmZ.1,?_⟩
  intro s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  have hz (i:Fin 2):p.profile i 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (p.support i hn).1
  have hz1:s.W₁ 0=0:=by rw [hw1];exact hz 0
  have hz2:s.W₂ 0=0:=by rw [hw2];exact hz 1
  obtain ⟨τ,hfamily,hchild⟩:=hmZ.2 s hlo hhis hz1 hz2 hH0 hH R0 seed hseed hseed0
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂
    hleft hright r hX1 hX2 hY1 hY2
  have hn:=hchild χ₀ Q m hQ72 hm hml hm2 Kphys Tsec ξ hKphys
    (by simpa only [one_mul] using hRcap) E₁ E₂ hE₁ hE₂ hleft hright
  have he:=hrZ.2 s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
    χ₀ m hm hml hm2 Tsec Kphys hKphys hVcap hTcap hnom hR hRcap r hX1 hX2 hY1 hY2
  have ht:‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      ‖partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData+
      ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys-
        partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData:=by
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ (volume_pos s.toData).le
    have h:=norm_add_le
      (partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s))
      (sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys-
        partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s))
    simpa only [←add_sub_assoc, add_sub_cancel_left] using h
  exact ht.trans ((add_le_add hn he).trans_eq (by ring))

end SevenEighths.CenteredMomentSecondFrozenLiveDescent

end

end OAI

end Source2004

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondFrozenUniformSubset.lean; sha256: d40f70e3c819376e33bf8d60d208730b3f0a3048e182b77beefa936c9b225b22 -/
section Source2005
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
open SevenEighths.CenteredMomentSecondUniformSubsetSource
open SevenEighths.CenteredMomentSecondNonexceptionalScalar

namespace SevenEighths.CenteredMomentSecondFrozenUniformSubset
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondFrozenRatioCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

theorem original_subsets_source_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      Cmain*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ)+
      Cdiag*Kphys*‖paperRadialFourier W 0‖*
        (2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*(∏i,s.M i))^2*
        (1+(∏i:T,hi i.val)*whi*whi)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ)+
      Cexc*profileFactor Sprofile s p J Q Kc*
        Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)+
      Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys*Z^(-saving)  := by
  have hall (T : Finset ι) := CenteredMomentSecondFrozenLiveDescent.original_source_descent
    wlo whi hwlo hwhi (fun i:T=>lo i.val) (fun i:T=>hi i.val) (fun i=>hhi i.val)
    W J₁ J₂ ε δ θ B ξ saving hε hδ hθ hB hξ
  choose J Sp Sf hSp Cm Ce Cd Ct hCm hCe hCd hCt hbound using hall
  let J0 : ℕ := ∑T:Finset ι,J T
  let Sp0 := Finset.univ.biUnion Sp
  let Sf0 := Finset.univ.biUnion Sf
  let Cm0 : ℝ := 1+∑T:Finset ι,Cm T
  let Ce0 : ℝ := 1+∑T:Finset ι,Ce T
  let Cd0 : ℝ := 1+∑T:Finset ι,Cd T
  let Ct0 : ℝ := 1+∑T:Finset ι,Ct T
  have sum_pos (f : Finset ι→ℝ) (hf : ∀T,0≤f T) : 0<1+∑T:Finset ι,f T := by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset ι)))=>hf T)
    linarith
  have sum_le (f : Finset ι→ℝ) (hf : ∀T,0≤f T) (T : Finset ι) : f T≤1+∑U:Finset ι,f U := by
    have hh:=Finset.single_le_sum (fun U (_:U∈(Finset.univ:Finset (Finset ι)))=>hf U) (Finset.mem_univ T)
    linarith
  refine ⟨J0,Sp0,Sf0,Finset.mem_biUnion.mpr ⟨∅,Finset.mem_univ _,hSp ∅⟩,
    Cm0,Ce0,Cd0,Ct0,sum_pos Cm (fun T=>(hCm T).le),(sum_pos Ce hCe).le,
    sum_pos Cd (fun T=>(hCd T).le),sum_pos Ct (fun T=>(hCt T).le),?_⟩
  intro Q hQ hQt hQ72
  choose K hK hev using fun T=>hbound T Q hQ hQt hQ72
  let K0 : ℝ := 1+∑T:Finset ι,K T
  refine ⟨K0,sum_pos K (fun T=>(hK T).le),?_⟩
  have heall : ∀ᶠ Z : ℝ in atTop, ∀T:Finset ι,_ := Filter.eventually_all.mpr hev
  filter_upwards [heall] with Z hZ
  refine ⟨(hZ ∅).1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=(hZ T).2 s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hsp : Sp T⊆Sp0 := fun x hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hsf : Sf T⊆Sf0 := fun x hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hj : J T≤J0 := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hcm:=sum_le Cm (fun T=>(hCm T).le) T
  have hce:=sum_le Ce hCe T
  have hcd:=sum_le Cd (fun T=>(hCd T).le) T
  have hct:=sum_le Ct (fun T=>(hCt T).le) T
  have hfactor:=factor_mono hsp s p hj Q (hK T).le (sum_le K (fun T=>(hK T).le) T)
  have hfn:=profileFactor_nonneg (Sp T) s p (J T) Q (K T) (hK T).le
  have hphi : (Sf T).sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤Sf0.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := Seminorm.le_def.mp (Finset.sup_mono hsf) W
  have hz : 0≤Z := (hZ T).1.le.trans' zero_le_one
  have hp:=profileCost_nonneg s
  have hm1:=profileMoment_nonneg J₁
  have hm2:=profileMoment_nonneg J₂
  have he:=heightEnvelope_pos s.t
  have hsn : 0≤(seed.absNorm:ℝ) := by positivity
  have hvol:=CenteredMomentSourceInputTailUniform.volume_pos s
  have hc : 0≤(Sf T).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := apply_nonneg _ _
  have hCm0 : 0≤Cm0 := (sum_pos Cm (fun T=>(hCm T).le)).le
  have hCe0 : 0≤Ce0 := (sum_pos Ce hCe).le
  have hCd0 : 0≤Cd0 := (sum_pos Cd (fun T=>(hCd T).le)).le
  have hCt0 : 0≤Ct0 := (sum_pos Ct (fun T=>(hCt T).le)).le
  have hprodhi : 0≤∏i:T,hi i.val := Finset.prod_nonneg (fun i _=>hhi i.val)
  have hprodlo : 0≤∏i:T,s.lo i := Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentSecondFrozenUniformSubset

end

end OAI

end Source2005

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondFrozenSeededPowerDescent.lean; sha256: a712b750771173239a767ee806587c1e52f3977d84b4299018acfe3a2a2dda98 -/
section Source2006
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenSeededPowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar

theorem original_subsets_seeded_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤s.b₁ → 0≤s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩ :=
    CenteredMomentSecondFrozenUniformSubset.original_subsets_source_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ ε δ θ B ξ (saving+Bseed) hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  let a:=seededFactors Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ Sf W
  have hapos:=physicalFactors_nonneg Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ Sf W
    hCm.le hCe hCd.le hCt.le (zero_le_one.trans hZ.1.le) hKphys.le (by positivity)
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le))
  have hseedpos : 0<(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed0)
  have ha : ∀j,0≤a j := by
    intro j
    fin_cases j
    · exact hapos 0
    · exact hapos 1
    · exact hapos 2
    · exact div_nonneg (hapos 3) hseedpos.le
  have hh': ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      sourceCost s Sp p J Q Kc ε (seed.absNorm:ℝ) a := by
    apply hh.trans
    have htail:=paid_seed_term Z Bseed saving (seed.absNorm:ℝ)
      (Ct*plainControl s (p.profile 0) (p.profile 1)^2*
        Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys)
      (zero_lt_one.trans hZ.1) hseedpos hseedcap (by positivity)
    dsimp [sourceCost,a,seededFactors,physicalFactors]
    simp_rw [hhis]
    dsimp [mass, CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume]
    ring_nf at htail ⊢
    linarith only [htail]
  exact hh'.trans (source_rhs s N b b₁ b₂ A hb hb₁ hb₂ hu hc
    (fun i=>by rw [hhis]; exact hhi i.val) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha)

end SevenEighths.CenteredMomentSecondFrozenSeededPowerDescent

end

end OAI

end Source2006

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondReferenceNormalization.lean; sha256: 2bcffc1e042ee3754474edeca17f39eae75db20ea1b90557ff47532618031e96 -/
section Source2007
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondReferenceNormalization
open HeckeFamily CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondNonexceptionalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentSectorLocalization CenteredMomentSecondSourcePowerDescent
open CenteredMomentSecondSourceSeededPowerDescent
local notation "O"=>HeckeFamily.O

def referenceEnvelope (qref:ℝ)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  (fixedFactor:ℝ)*qref*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)

lemma envelope_rescale (η:Character)(qref E:ℝ)(C D:Ideal O)
    (U:Finset (CommonIndex C D))(n:Fin 4→ℤ):
    (qref/(η.modulus.absNorm:ℝ)*E)*childEnvelope η C D U n=
      E*referenceEnvelope qref C D U n:=by
  have hq:(η.modulus.absNorm:ℝ)≠0:=by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot
  unfold childEnvelope referenceEnvelope
  field_simp

lemma paired_rescale (q qref E₁ E₂:ℝ)(hq:0<q)(hr:0≤qref):
    q*Real.sqrt ((qref/q*E₁)*(qref/q*E₂))=qref*Real.sqrt (E₁*E₂):=by
  rw [show (qref/q*E₁)*(qref/q*E₂)=(qref/q)^2*(E₁*E₂) by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (div_nonneg hr hq.le)]
  field_simp

lemma physicalFactors_rescale (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q qref E₁ E₂ r
    loProduct wlo:ℝ)(J₁ J₂:ℕ)(SΦ:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hq:0<q)(hr:0≤qref):
    physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q
      (qref/q*E₁) (qref/q*E₂) r loProduct wlo J₁ J₂ SΦ W=
    physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t qref
      E₁ E₂ r loProduct wlo J₁ J₂ SΦ W:=by
  funext j
  fin_cases j
  · dsimp [physicalFactors]
    have hh:=paired_rescale q qref E₁ E₂ hq hr
    calc
      _=Cmain*Z^(2*δ+ε)*(q*Real.sqrt ((qref/q*E₁)*(qref/q*E₂)))*
        CenteredMomentSecondWindowBudget.heightEnvelope t^(J₁+J₂)*
        CenteredMomentSecondWindowBudget.profileMoment J₁*CenteredMomentSecondWindowBudget.profileMoment J₂:=by ring
      _=_:=by rw [hh];ring
  all_goals rfl

lemma seededFactors_rescale (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q qref E₁ E₂ r
    loProduct wlo seed:ℝ)(J₁ J₂:ℕ)(SΦ:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hq:0<q)(hr:0≤qref):
    seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q
      (qref/q*E₁) (qref/q*E₂) r loProduct wlo seed J₁ J₂ SΦ W=
    seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t qref
      E₁ E₂ r loProduct wlo seed J₁ J₂ SΦ W:=by
  unfold seededFactors
  rw [physicalFactors_rescale Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q qref E₁ E₂ r
    loProduct wlo J₁ J₂ SΦ W hq hr]

end SevenEighths.CenteredMomentSecondReferenceNormalization

end

end OAI

end Source2007

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondFrozenReferenceSeededPowerDescent.lean; sha256: 0772230291e45d91f2ae664dba5421faafe88cf99359edfe659fbbc53d65191d -/
section Source2008
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenReferenceSeededPowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondReferenceNormalization

theorem original_subsets_seeded_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤s.b₁ → 0≤s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀qref:ℝ,0<qref→∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩:=
    CenteredMomentSecondFrozenSeededPowerDescent.original_subsets_seeded_power_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ N b b₁ b₂ hb hb₁ hb₂
        ε δ θ B Bseed ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
    E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hq:0<(s.η.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ s.η.modulus_ne_bot
  have hr:0≤qref/(s.η.modulus.absNorm:ℝ):=div_nonneg hqref.le hq.le
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap
    (qref/(s.η.modulus.absNorm:ℝ)*E₁) (qref/(s.η.modulus.absNorm:ℝ)*E₂)
    (mul_nonneg hr hE₁) (mul_nonneg hr hE₂)
  have hbound:=hh
    (by
      intro q hq U n hn D0 hD hcap hs χ v b hb a ha
      simpa only [envelope_rescale] using hleft q hq U n hn D0 hD hcap hs χ v b hb a ha)
    (by
      intro q hq U n hn D0 hD hcap hs χ v b hb a ha
      simpa only [envelope_rescale] using hright q hq U n hn D0 hD hcap hs χ v b hb a ha)
    r hX1 hX2 hY1 hY2
  rw [seededFactors_rescale Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ)
      J₁ J₂ Sf W hq hqref.le] at hbound
  exact hbound

end SevenEighths.CenteredMomentSecondFrozenReferenceSeededPowerDescent

end

end OAI

end Source2008

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSeededGaussianPower.lean; sha256: 0f6629683e029b14da4ab639b86b8d31b3d78972c1e4dae6928abfbe31e22ad0 -/
section Source2009
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSeededGaussianPower
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondReferenceNormalization

open CenteredMomentAmplificationChildInput
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

omit [DecidableEq ι] in
lemma normalized_source_le_norm (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource s R seed W K≤
      ‖sourceGaussEnergy (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) (heightCoeff s.η s.t) W K‖/
          CenteredMomentAmplificationChildInput.volume s := by
  exact div_le_div_of_nonneg_right (Complex.re_le_norm _)
    (CenteredMomentAmplificationChildInput.volume_pos s).le

omit [DecidableEq ι] in
lemma allocated_source_le_norm (s : Input ι) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    childNormalizedGaussSource s C R seed B τ t W K≤
      ‖sourceGaussEnergy
        (finiteColumns (Fintype.piFinset (child s C R B τ t).pools))
        (coefficient (child s C R B τ t) (R*C) seed)
        (heightCoeff τ t) W K‖/CenteredMomentAmplificationChildInput.volume (child s C R B τ t) :=
  normalized_source_le_norm (child s C R B τ t) (R*C) seed W K

omit [DecidableEq ι] in
lemma active_error_source_le_norm (s : Input ι) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    childNormalizedGaussSource (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp υ v W K≤
      ‖sourceGaussEnergy
        (finiteColumns (Fintype.piFinset (errorInput s C R B τ t Q k Bp υ v).pools))
        (coefficient (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed)
        (heightCoeff υ v) W K‖/
          CenteredMomentAmplificationChildInput.volume (errorInput s C R B τ t Q k Bp υ v) :=
  normalized_source_le_norm (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed W K

theorem actual_subsets_seeded_gaussian_power (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤s.b₁ → 0≤s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀qref:ℝ,0<qref→∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    normalizedGaussSource s R0 seed W Kphys≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩:=
    CenteredMomentSecondFrozenReferenceSeededPowerDescent.original_subsets_seeded_power_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ N b b₁ b₂ hb hb₁ hb₂
        ε δ θ B Bseed ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
    E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  exact (normalized_source_le_norm s R0 seed W Kphys).trans
    (hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
      E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2)

end SevenEighths.CenteredMomentFirstSeededGaussianPower

end

end OAI

end Source2009

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalMainGaussian.lean; sha256: 9ba0374f9f6d3cc88c99429b67e42e19377d1330815dde2b921fac6c1770fc4c -/
section Source2010
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainGaussian
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_main_gaussian_from_bands
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0<Cm ∧ 0≤Ce ∧ 0<Cd ∧ 0<Ct ∧
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Kc:ℝ,0<Kc ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤sigma → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input (R0*C) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    (∀q∈liveLabels input.η Scols β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀dyad:SourceBlocks q.val.1 q.val.2 U Kmain (frequencyRadius (nominal input Kmain) Z ξ)
        (sourceRadius input),
      physicalBlock input.η input.t (activeSource Scols β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U
        (frequencyRadius (nominal input Kmain) Z ξ)
        (partRows false input.η χ₀ (internalQ Q η₀) m q.val.1 q.val.2 U
          (frequencyRadius (nominal input Kmain) Z ξ))
        CenteredMomentFirstAmplificationChoice.ballProfile Kmain (fun i=>(dyad i:ℤ))≠0 →
      ∀χ:RayCharacter,Real.logb Z (dyadicScale (dyad 1))+
        Real.logb Z ((family q U χ).modulus.absNorm:ℝ)≤Mcap) →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let Echild:=CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+
        (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3)+κ*mesh))
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc t
        εsrc (seed.absNorm:ℝ)
        (seededFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Kmain t
          (cost*(τ.modulus.absNorm:ℝ)) Echild Echild r (∏i,input.lo i) a (seed.absNorm:ℝ)
          (dc+degree+4*n) (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,hmain⟩:=
    CenteredMomentEnergyCanonicalMainUniform.actual_main_uniform_child (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL
      degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
      N lower upper a0 Bcap Bcap θsource hlower ha0 hθsource
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hgauss⟩:=
    actual_subsets_seeded_gaussian_power a b haPlain hbPlain lows highs hhighs
      CenteredMomentFirstAmplificationChoice.ballProfile (dc+degree+4*n) (dc+degree+4*n)
      N upper (max 1 b) (max 1 b) hupper (le_max_left _ _) (le_max_left _ _)
      εsrc δsrc θsrc Bcap Bseed ξ saving hεsrc hδsrc hθsrc hBcap hξ
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Zm,hZm,hm⟩:=hmain η₀
  obtain ⟨Kc,hKc,hevent⟩:=hgauss (internalQ Q η₀) hQ0 hQt hQ72
  obtain ⟨Zg,hZg⟩:=Filter.eventually_atTop.1 hevent
  refine ⟨Kc,hKc,max Zm Zg,lt_of_lt_of_le hZm (le_max_left _ _),?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip
    hcap hMdecl hclip hsourceLower Scols β hScols hβ
  let input:=child src C R0 B τ t
  let Km:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
  have hZmZ:Zm≤Z:=(le_max_left _ _).trans hZ
  have hgZ:=hZg Z ((le_max_right _ _).trans hZ)
  have hz:1<Z:=hgZ.1
  have hP:∀i,1≤ input.P i:=by
    intro i
    change 1≤src.P i.val
    rw [hmatch.scale]
    exact Real.one_le_rpow hz.le (hw i.val)
  have hcardInput:Fintype.card (CenteredMomentCommonProfile.liveIndices B.val)≤N:=
    (child_card B.val).trans hcard
  have hlowerBeta (I:Ideal O)(hne:coefficient input (R0*C) seed I≠0):
      asource*volume input≤(I.absNorm:ℝ):=by
    apply (mul_le_mul_of_nonneg_right hsourceLower (volume_pos input).le).trans
    apply CenteredMomentSecondInputCapacitySource.actual_lower_support N lower a hlower haPlain
      input hcardInput hlowerSrc ?_ ?_ (R0*C) seed I hne
    · intro x hx
      change src.W₁ x≠0 at hx
      rw [←hp₁] at hx
      exact (p.support 0 hx).1
    · intro x hx
      change src.W₂ x≠0 at hx
      rw [←hp₂] at hx
      exact (p.support 1 hx).1
  have hsource:=hgZ.2 (CenteredMomentCommonProfile.liveIndices B.val) input p
    (fun i=>hloSrc i.val) (fun i=>hhiSrc i.val) hP hp₁.symm hp₂.symm (mass src)
    hupperSrc hcardInput hb1 hb2 hb1max hb2max (child_mass src C R0 B τ t)
    (R0*C) seed hready.puncture_ne hseed hseed0 hseedcap hready.source_nonneg hready.source_cap
    hready.conductor_cap hready.puncture_cap
  change Scols=finiteColumns (Fintype.piFinset input.pools) at hScols
  change β=coefficient input (R0*C) seed at hβ
  dsimp only at hsource
  subst Scols β
  obtain ⟨family,hfamily,hbound⟩:=hsource
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm0 hml hm2 hwidth r hr1 hr2 hr3 hr4
  let Ec:=CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+
        (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3)+κ*mesh))
  have hEc:0≤Ec:=CenteredMomentEnergyChildEnvelopeFitting.coefficient_nonneg
    Cc C₀ C₁ p T height (dc+degree+4*n) Z _ hCc.le hC₀ hC₁ hheight (zero_le_one.trans hz.le)
  have hpzero (j:Fin 2):p.profile j 0=0:=by
    by_contra hn
    exact (not_le_of_gt haPlain) ((p.support j hn).1)
  have hz1:input.W₁ 0=0:=by change src.W₁ 0=0;rw [←hp₁];exact hpzero 0
  have hz2:input.W₂ 0=0:=by change src.W₂ 0=0;rw [←hp₂];exact hpzero 1
  apply hbound χ₀ m hm0 hml hm2 Km (nominal input Km) hready.scale_pos hready.volume_cap
    hready.nominal_cap (le_refl _) hready.frequency_pos hready.frequency_cap
    (cost*(τ.modulus.absNorm:ℝ))
    (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
    Ec Ec hEc hEc ?_ ?_ r hr1 hr2 hr3 hr4
  all_goals
    intro q hq U dyad hphysical D0 hD0 hD0cap hD0sq χ v B₂ hB₂ alloc halloc
    have hg:=actual_common_gates input (R0*C) seed hseed hz1 hz2 q.val.1 q.val.2 q.property
    have hs:=commonLabels_supported (activeSource _ _) _ _ q.property
  · exact hm θ Z hZmZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
      K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
      _ _ q.val.1 q.val.2 hs.1 hs.2 hg.2.2.1 U _ _ _ (fun i=>(dyad i:ℤ))
      hlowerBeta hphysical (family q U) (hfamily q U) χ (hwidth q hq U dyad hphysical χ)
      q.val.1 (R0*C) (Or.inl rfl) hready.puncture_ne hready.puncture_cap
      (hg.2.2.2.2.2.1.trans hready.source_cap) B₂ hB₂ D0 alloc p hp₁ hp₂
      hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  · exact hm θ Z hZmZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
      K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
      _ _ q.val.1 q.val.2 hs.1 hs.2 hg.2.2.1 U _ _ _ (fun i=>(dyad i:ℤ))
      hlowerBeta hphysical (family q U) (hfamily q U) χ (hwidth q hq U dyad hphysical χ)
      q.val.2 (R0*C) (Or.inr rfl) hready.puncture_ne hready.puncture_cap
      (hg.2.2.2.2.2.2.trans hready.source_cap) B₂ hB₂ D0 alloc p hp₁ hp₂
      hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip

end SevenEighths.CenteredMomentEnergyCanonicalMainGaussian

end

end OAI

end Source2010

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalMainSeparated.lean; sha256: 5954b8b3d2e01d181307744f45b3a0ac36ba84ffc1b7ddf443d703f32c6d1392 -/
section Source2011
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainSeparated
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_main_separated_gaussian
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0<Cm ∧ 0≤Ce ∧ 0<Cd ∧ 0<Ct ∧
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Kc:ℝ,0<Kc ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve cost asource:ℝ,0<K → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input (R0*C) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀_χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let Echild:=CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+
        (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3)+κ*mesh))
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc t
        εsrc (seed.absNorm:ℝ)
        (seededFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Kmain t
          (cost*(τ.modulus.absNorm:ℝ)) Echild Echild r (∏i,input.lo i) a (seed.absNorm:ℝ)
          (dc+degree+4*n) (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    CenteredMomentEnergyCanonicalMainGaussian.actual_main_gaussian_from_bands (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  let Zw:=CenteredMomentEnergyAmplifiedChildWidth.threshold N upper sigma hupper hsigma
  refine ⟨Kc,hKc,max Zi Zw,lt_of_lt_of_le hZi (le_max_left _ _),?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  have hZiZ:Zi≤Z:=(le_max_left _ _).trans hZ
  have hZw:Zw≤Z:=(le_max_right _ _).trans hZ
  have hz:1<Z:=hZi.trans_le hZiZ
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZiZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma.le hcost hasource hdelta hreserve haSource
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip
    hcap hMdecl hclip hsourceLower Scols β hScols hβ
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  apply hbound χ₀ m hm hml hm2 ?_ r hr1 hr2 hr3 hr4
  intro q hq U dyad hphysical χ
  have hs:=commonLabels_supported (activeSource Scols β) _ _ q.property
  have hη:(src.η.modulus.absNorm:ℝ)≤Z^(Real.logb Z (src.η.modulus.absNorm:ℝ)):=by
    rw [Real.rpow_logb (zero_lt_one.trans hz) (ne_of_gt hz)
      (norm_pos src.η.modulus src.η.modulus_ne_bot)]
  have hh:=CenteredMomentEnergyAmplifiedChildWidth.main_child_width N upper sigma hupper hsigma
    Z hZw src hcard hupperSrc C D R0 hC hD hCD E B τ t hB hmod K delta reserve ξ
    (Real.logb Z (src.η.modulus.absNorm:ℝ)) Mwidth hK hdelta hreserve hξsmall hη hMwidth
    (activeSource Scols β) β q.val.1 q.val.2 hs.1 hs.2 U (family q U) (hfamily q U)
    _ CenteredMomentFirstAmplificationChoice.ballProfile (fun i=>(dyad i:ℤ)) hphysical χ
  exact hh.le.trans hdrop

end SevenEighths.CenteredMomentEnergyCanonicalMainSeparated

end

end OAI

end Source2011

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstErrorAllocationPower.lean; sha256: b7e0359a14458f71eb4d0ca6983caa60b796f796927324fe881054aa17ff43a3 -/
section Source2012
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstErrorAllocationPower
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentFirstChildProfileControl
open CenteredMomentAmplificationAllocationCost CenteredMomentCommonProfile
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma child_mass_eq (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    mass (child s (Q^k) R B τ t)=mass s := by
  change (∏i:liveIndices B.val,s.M i.val)=∏i,s.M i
  rw [Finset.prod_coe_sort,prime_slots_live s Q hQ k hslot B]

lemma allocations_card (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) :
    Fintype.card (actualAllocations s.pools (Q^k))≤k+1 := by
  simpa only [Fintype.card_coe] using actual_amplification_allocations_card s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩)

theorem power_sum_eq (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ) (α : ℝ) :
    (∑B:actualAllocations s.pools (Q^k),
      volume (child s (Q^k) R B (τ B) (t B))^α*mass (child s (Q^k) R B (τ B) (t B))^2)=
    Fintype.card (actualAllocations s.pools (Q^k))*
      (volume s/(Q.absNorm:ℝ)^k)^α*mass s^2 := by
  simp_rw [child_volume s Q hQ k hslot,child_mass_eq s Q hQ k hslot]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

theorem power_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ) (α : ℝ) :
    (∑B:actualAllocations s.pools (Q^k),
      volume (child s (Q^k) R B (τ B) (t B))^α*mass (child s (Q^k) R B (τ B) (t B))^2)≤
    ((k+1:ℕ):ℝ)*(volume s/(Q.absNorm:ℝ)^k)^α*mass s^2 := by
  rw [power_sum_eq s Q hQ.ne_zero k hslot R τ t α]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _
    (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) α)
  exact_mod_cast allocations_card s Q hQ k hslot

theorem budget_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ)
    (n : ℕ) (a α : Fin n→ℝ) (ha : ∀j,0≤a j) :
    (∑B:actualAllocations s.pools (Q^k),
      (∑j,a j*volume (child s (Q^k) R B (τ B) (t B))^(α j))*
        mass (child s (Q^k) R B (τ B) (t B))^2)≤
    ((k+1:ℕ):ℝ)*(∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2 := by
  simp_rw [child_volume s Q hQ.ne_zero k hslot,child_mass_eq s Q hQ.ne_zero k hslot]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hs : 0≤∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j) :=
    Finset.sum_nonneg (fun j _=>mul_nonneg (ha j)
      (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) _))
  have hc : (Fintype.card (actualAllocations s.pools (Q^k)):ℝ)≤k+1 := by
    exact_mod_cast allocations_card s Q hQ k hslot
  calc
    _≤((k:ℝ)+1)*((∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hs (sq_nonneg _))
    _=_ := by push_cast;ring

theorem error_budget_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ)
    (n : ℕ) (a α : Fin n→ℝ) (ha : ∀j,0≤a j) :
    (∑B:actualAllocations s.pools (Q^k),
      (∑j,a j*volume (child s (Q^k) R B (τ B) (t B))^(α j))*
        mass (child s (Q^k) R B (τ B) (t B))^2)≤
    8*(∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2 := by
  apply (budget_sum_le s Q hQ k hslot R τ t n a α ha).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _
    (Finset.sum_nonneg (fun j _=>mul_nonneg (ha j)
      (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) _)))
  rcases hk with rfl|rfl|rfl <;> norm_num

end SevenEighths.CenteredMomentFirstErrorAllocationPower

end

end OAI

end Source2012

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAnnularInputAmplification.lean; sha256: 9bf65d46e104703b3cc13d35f1d615f5eae73f1a1581803a84ca93bc57430ed4 -/
section Source2013
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily

theorem eventually_input_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ s : Input ι,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                normalizedGaussSource s R seed ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve)+
                ∑p : elementPool P,∑i : Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
                    ∑χ:RayCharacter,∑B:actualAllocations (activeInput s).pools
                        ((Ideal.span {p.val})^(errorIndex i+1)),
                      childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                        R seed B (τ p i χ) s.t ballProfile
                        (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                          (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))) := by
  filter_upwards [CenteredMomentFirstAnnularAmplification.eventually_annular_amplification_common
    (ι:=ι) M H hH Sbad hbad sigma loss BR Bs Mmax b eta Csec xi reserve
    hsigma hloss hM hb hgap hC hxi hreserve,
    eventually_dyadic_amplification.{0} M H hH Sbad hbad sigma loss BR Bs Mmax b eta
      hsigma hloss hM hgap] with Z hz hpz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hpz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η
  obtain ⟨τ,hN,henergy⟩:=hfam η fixedBadMask fixedBadMask_ne_zero
    (dvd_mul_right _ _) (dvd_mul_left _ _)
  refine ⟨τ,hN,?_⟩
  intro s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  have he:=henergy (original s R seed) s.pools_ne s.prime hsupp z hz hlen hR0 hs0 hR hs
    s.t (volume s) d cLog (volume_pos s) I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  rw [←hsη,normalized_input_coefficient,normalized_input_coefficient] at he
  convert he using 1
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
    (fun Q hQ=>(hdata Q hQ).2.1) p.val p.property
  have hcop:∀i,∀Q∈(activeInput s).slots i,IsCoprime (Ideal.span {p.val}) Q:=by
    exact original_slot_coprime (original s R seed).active Z sigma b eta hZ.le hb hsep z hz hlen
      hsupp (original s R seed).active_slot
      (fun i Q hQ=>s.prime i Q ((original s R seed).active_subset _ hQ))
      (Ideal.span {p.val}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  apply Finset.sum_congr rfl
  intro i _
  rw [←original_active]
  exact (original_childEnergy_eq_inputs (activeInput s) R seed (τ p i) p.val hd.1.ne_zero hcop
    (errorIndex i) s.t _).symm

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI

end Source2013

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAmplifiedPowerBudget.lean; sha256: 18455527d4dc63cf31ee1c73ae66c7705d2281d84d187e5adb8a3db0bf19f1af -/
section Source2014
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAmplifiedPowerBudget
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily

open CenteredMomentFirstAnnularInput CenteredMomentFirstErrorAllocationPower
theorem eventually_input_power_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ s : Input ι,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          ∀ (amain:Fin 4→ℝ) (aerror:elementPool P→Fin 3→RayCharacter→Fin 4→ℝ)
            (α:Fin 4→ℝ), (∀p i χ j,0≤aerror p i χ j)→
          (normalizedGaussSource s R seed ballProfile
            (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
              (frequencyLoss Z (32*Csec) xi) reserve)≤
                (∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)→
          (∀p:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
            ∀B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                R seed B (τ p i χ) s.t ballProfile
                (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                  (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))≤
                (∑j,aerror p i χ j*(volume (child (activeInput s)
                  ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ p i χ) s.t))^(α j))*
                  CenteredMomentFirstChildProfileControl.mass (child (activeInput s)
                    ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ p i χ) s.t)^2)→
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*CenteredMomentFirstChildProfileControl.mass s^2*
              (((Mmax+2*sigma)/(sigma/6))*(∑j,amain j*(volume s)^(α j))+
                ∑p:elementPool P,∑i:Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*(errorIndex i+2:ℝ)*
                    ∑χ:RayCharacter,∑j,aerror p i χ j*
                      (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j)) := by
  filter_upwards [eventually_input_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta Csec xi reserve hsigma hloss hM hb hgap hC hxi hreserve,
    eventually_dyadic_amplification.{0} M H hH Sbad hbad sigma loss BR Bs Mmax b eta
      hsigma hloss hM hgap] with Z hz hpz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hpz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η
  obtain ⟨τ,hN,henergy⟩:=hfam η
  refine ⟨τ,hN,?_⟩
  intro s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec hK hX hsec
    H0 hH0 houter hcap amain aerror α haerr hmain herr
  have he:=henergy s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec
    hK hX hsec H0 hH0 houter hcap
  apply he.trans
  have hpweight:0≤56/((primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card:ℝ):=by positivity
  have hmweight:0≤(Mmax+2*sigma)/(sigma/6):=by positivity
  have herror: ∀p:elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))),∀i:Fin 3,
      (∑χ:RayCharacter,∑B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
          R seed B (τ p i χ) s.t ballProfile
          (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
            (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1)))≤
      (errorIndex i+2:ℝ)*(∑χ:RayCharacter,∑j,aerror p i χ j*
        (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
          CenteredMomentFirstChildProfileControl.mass s^2:=by
    intro p i
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) p.val p.property
    have hcop:∀j,∀Q∈(activeInput s).slots j,IsCoprime (Ideal.span {p.val}) Q:=by
      exact original_slot_coprime (original s R seed).active Z sigma b eta hZ.le hb hsep z hz hlen
        hsupp (original s R seed).active_slot
        (fun j Q hQ=>s.prime j Q ((original s R seed).active_subset _ hQ))
        (Ideal.span {p.val}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hq:Prime (Ideal.span {p.val}):=(hdata _ hd.2.1).1
    calc
      _≤∑χ:RayCharacter,((errorIndex i+1+1:ℕ):ℝ)*
          (∑j,aerror p i χ j*(volume (activeInput s)/
            ((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
              CenteredMomentFirstChildProfileControl.mass (activeInput s)^2:=by
        apply Finset.sum_le_sum
        intro χ hχ
        apply le_trans (Finset.sum_le_sum (fun B _=>herr p i χ B))
        exact budget_sum_le (activeInput s) (Ideal.span {p.val}) hq (errorIndex i+1) hcop R
          (fun _=>τ p i χ) (fun _=>s.t) 4 (aerror p i χ) α (haerr p i χ)
      _=_:=by
        simp only [CenteredMomentFirstChildProfileControl.mass,activeInput]
        push_cast
        rw [←Finset.sum_mul,←Finset.mul_sum]
        congr 2
        ring
  calc
    _≤(56/((primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*
          ((∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)+
          ∑p:elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))),∑i:Fin 3,(16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
            ((errorIndex i+2:ℝ)*(∑χ:RayCharacter,∑j,aerror p i χ j*
              (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
                CenteredMomentFirstChildProfileControl.mass s^2)):=by
      apply mul_le_mul_of_nonneg_left _ hpweight
      apply add_le_add (mul_le_mul_of_nonneg_left hmain hmweight)
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (herror p i)
        (mul_nonneg (by positivity) (localErrorCost_nonneg p (errorIndex i)))
    _=_:=by
      simp only [←mul_assoc,←Finset.sum_mul]
      ring

theorem eventually_original_subsets_power_amplification {Ω : Type*} [Fintype Ω]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (A:Finset Ω) → (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (A:Finset Ω) (p : elementPool P) i χ,(τ A p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ A:Finset Ω,∀ s : Input A,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : A→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          ∀ (amain:Fin 4→ℝ) (aerror:elementPool P→Fin 3→RayCharacter→Fin 4→ℝ)
            (α:Fin 4→ℝ), (∀p i χ j,0≤aerror p i χ j)→
          (normalizedGaussSource s R seed ballProfile
            (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
              (frequencyLoss Z (32*Csec) xi) reserve)≤
                (∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)→
          (∀p:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
            ∀B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                R seed B (τ A p i χ) s.t ballProfile
                (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                  (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))≤
                (∑j,aerror p i χ j*(volume (child (activeInput s)
                  ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t))^(α j))*
                  CenteredMomentFirstChildProfileControl.mass (child (activeInput s)
                    ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t)^2)→
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*CenteredMomentFirstChildProfileControl.mass s^2*
              (((Mmax+2*sigma)/(sigma/6))*(∑j,amain j*(volume s)^(α j))+
                ∑p:elementPool P,∑i:Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*(errorIndex i+2:ℝ)*
                    ∑χ:RayCharacter,∑j,aerror p i χ j*
                      (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j)) := by
  have hall:=Filter.eventually_all.mpr (fun A:Finset Ω=>
    eventually_input_power_amplification (ι:=A) M H hH Sbad hbad sigma loss BR Bs Mmax b eta Csec xi reserve
      hsigma hloss hM hb hgap hC hxi hreserve)
  filter_upwards [hall] with Z hz
  have hbase:=hz (∅:Finset Ω)
  refine ⟨hbase.1,hbase.2.1,hbase.2.2.1,?_⟩
  intro η
  have hf (A:Finset Ω):=(hz A).2.2.2 η
  choose τ hN he using hf
  exact ⟨τ,hN,he⟩

end SevenEighths.CenteredMomentFirstAmplifiedPowerBudget

end

end OAI

end Source2014

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalSourceDyadicWindowEnergy.lean; sha256: 15c3e17d888f548602b6f5cc229727f075846fdb4c649a124f420dd7e622fb5c -/
section Source2015
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentLogDyadic CenteredMomentSecondWindowSource CenteredMomentSecondWindowBudget
open IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]

theorem column_dyadic_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase logAnnulus
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) U K).re≤
      (windowBudget J t E*(1+‖θ‖)^J)^2:=by
  exact (column_window_energy s Q C hQ hC hQC τ t θ X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth L a ha U K hK hU J E hE henergy).trans
      (shifted_window_budget J t θ E hE)

theorem column_star_dyadic_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*star (columnPhase logAnnulus
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ)) U K).re≤
      (windowBudget J t E*(1+‖θ‖)^J)^2:=by
  simpa only [star_logAnnulus_column,norm_neg] using
    column_dyadic_window_energy s Q C hQ hC hQC τ t (-θ) X hX L a ha U K hK hU J E hE henergy

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI

end Source2015

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalSourceFixedEnergy.lean; sha256: 58f61a07cc1a0c681cf0693b8c3fc9061f11a04f441ccde9688baed84fd73b03 -/
section Source2016
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
variable {η:Character}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem FixedPair.left_common_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)
    (t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    (∑'z:O,((‖leftChild s η (fixedBadMask*idealGenerator s.R) t C D hC E ξ₁ L z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K))=commonEnergy s C hC F.left t L U K:=by
  change gaussEnergy Finset.univ (element C C hC.1 s.columns)
    (element_supported C C hC.1 s.columns) _ U K=_
  rw [funext (F.left_column s t L)]
  exact column_unwindowed_energy s C C hC.1 hC rfl F.left t L U K

theorem FixedPair.right_common_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    (∑'z:O,((‖rightChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K))=commonEnergy s D hD F.right t L U K:=by
  change gaussEnergy Finset.univ (element C D hD.1 s.columns)
    (element_supported C D hD.1 s.columns) _ U K=_
  rw [funext (F.right_column hD s t L)]
  exact column_unwindowed_energy s C D hC.1 hD hCD F.right t L U K

theorem FixedPair.right_reflected_common_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    (∑'z:O,((‖rightChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L (-z)‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K))=commonEnergy s D hD F.right t L U K:=by
  rw [←F.right_common_energy hD hCD s t L U K]
  simpa only [Equiv.neg_apply,map_neg,norm_neg] using (Equiv.neg O).tsum_eq
    (fun z:O=>((‖rightChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K))

theorem FixedPair.left_window_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)
    (t θ X:ℝ)(hX:0<X)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)
    (hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)(J:ℕ)(B:ℝ)(hB:0≤B)
    (hsource:∀v:ℝ,(commonEnergy s C hC F.left v L U K).re≤B*(1+‖v‖)^(2*J)):
    (∑'z:O,((‖leftWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC E ξ₁ L θ X logAnnulus z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K)).re≤(windowBudget J t B*(1+‖θ‖)^J)^2:=by
  exact column_dyadic_window_energy s C C hC.1 hC rfl F.left t θ X hX L _
    (F.left_column s t L) U K hK hU J B hB hsource

theorem FixedPair.right_window_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(B:ℝ)(hB:0≤B)
    (hsource:∀v:ℝ,(commonEnergy s D hD F.right v L U K).re≤B*(1+‖v‖)^(2*J)):
    (∑'z:O,((‖rightWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L θ X logAnnulus z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K)).re≤(windowBudget J t B*(1+‖θ‖)^J)^2:=by
  exact column_star_dyadic_window_energy s C D hC.1 hD hCD F.right t θ X hX L _
    (F.right_column hD s t L) U K hK hU J B hB hsource

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI

end Source2016

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAllocationGaussEnergy.lean; sha256: 2576d7d093bc613f2913be7fe0bfa7a9e6e09d713576656f1b9a80318a57e613 -/
section Source2017
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAllocationGaussEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentCommonRawScale CenteredMomentAddedZeroUniform
open CenteredMomentGaussEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def commonEnergy (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, ‖commonGauss D C hC τ t L z‖^2 *
    (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re

def allocatedEnergy (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (sourceGaussEnergy (allocatedData D C L B).columns
    (allocatedData D C L B).beta (heightCoeff τ t) W K).re

lemma common_summable (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ‖commonGauss D C hC τ t L z‖^2 *
      (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
  exact (gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator (CenteredMomentFirstSectors.residualPool C hC.1 D.columns))
    (sourceGenerator_supported _) _ W K hK).summable

lemma allocated_hasSum (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O =>
      ‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
        (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
      (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
      (allocatedEnergy D C L B τ t W K) :=
  gaussEnergy_hasSum_re _ _ _ _ W K hK

lemma allocated_nonneg (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O, 0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤allocatedEnergy D C L B τ t W K := by
  rw [← (allocated_hasSum D C L B τ t W K hK).tsum_eq]
  exact tsum_nonneg (fun z => mul_nonneg (sq_nonneg _) (hW z))

theorem common_energy_allocation (D : OriginalData ι)
    (hS : ∀ i, ∀ I∈D.S i, I≠0) (hp : ∀ i, ∀ I∈D.S (Sum.inl i), Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O, 0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    commonEnergy D C hC τ t L W K ≤
      ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 * allocatedEnergy D C L B τ t W K := by
  unfold commonEnergy
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hW z))
  intro rows
  calc
    _ ≤ ∑ z∈rows, ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
          (‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
          (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [common_gauss_allocation D hS hp C hC hseed τ t L z]
      have hc := mul_le_mul_of_nonneg_right
        (CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B : actualAllocations D.S C =>
            frozenCoefficient B.val C D.R D.nu D.slot D.lengths *
              gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
                (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z))
        (hW z)
      simpa only [Finset.card_univ,Fintype.card_coe,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using hc
    _ = ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
          ∑ z∈rows, ‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
            (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z))
        (allocated_hasSum D C L B τ t W K hK)

def rawVolume (D : OriginalData ι) : ℝ :=
  (D.X₁*D.X₂/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂)) * ∏ i,D.lengths i

lemma rawVolume_pos (D : OriginalData ι) (hX₁ : 0<D.X₁) (hX₂ : 0<D.X₂)
    (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0) (hP : ∀ i,0<D.lengths i) : 0<rawVolume D := by
  apply mul_pos (div_pos (mul_pos hX₁ hX₂) _)
    (Finset.prod_pos (fun i _ => hP i))
  exact mul_pos (CenteredMomentFirstScale.norm_pos _ hB₁) (CenteredMomentFirstScale.norm_pos _ hB₂)

lemma allocated_rawVolume_mul (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0) :
    rawVolume (allocatedData D C L B) * rawReduction B.val D.lengths = rawVolume D := by
  have hB := (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1
  have hv := remainingRaw_source B.val hB D.B₁ D.B₂ hB₁ hB₂ (D.X₁*D.X₂) D.lengths
  change _ = rawVolume (allocatedData D C L B) at hv
  rw [← hv]
  exact raw_scale_identity B.val hB _ D.lengths

lemma allocated_rawVolume (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0<D.lengths i) :
    rawVolume (allocatedData D C L B) = rawVolume D / rawReduction B.val D.lengths := by
  have hr := rawReduction_pos B.val
    (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP
  exact (eq_div_iff hr.ne').mpr (allocated_rawVolume_mul D C L B hB₁ hB₂)

lemma rawVolume_both (D : OriginalData ι) (T : ℝ)
    (hX : D.X₁*D.X₂=T) (hY : D.Y₁*D.Y₂=T) :
    rawVolume D=(T/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂))*∏ i,D.lengths i ∧
    rawVolume D=(D.Y₁*D.Y₂/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂))*∏ i,D.lengths i := by
  simp only [rawVolume,hX,hY,and_self]

def frozenControl (B : Tuple ι) (M : ι → ℝ) : ℝ :=
  ∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),M i

lemma frozenControl_nonneg (B : Tuple ι) (M : ι → ℝ)
    (hM : ∀ i,0≤M i) : 0≤frozenControl B M :=
  Finset.prod_nonneg (fun i _ => hM i)

lemma frozen_norm_bound (D : OriginalData ι) (C : Ideal O)
    (B : actualAllocations D.S C) (M : ι → ℝ) (_hM : ∀ i,0≤M i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hW : ∀ i x,‖D.slot i x‖≤M i) :
    ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖≤frozenControl B.val M := by
  unfold frozenCoefficient frozenControl
  rw [norm_mul]
  have hc : ‖(if IsCoprime C D.R then (1:ℂ) else 0)‖≤1 := by split_ifs <;> simp
  apply (mul_le_of_le_one_right (norm_nonneg _) hc).trans
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
  intro i hi
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hν i _)).trans (hW i _)

theorem frozen_normalized_bound (N : ℕ) (a b : ℝ) (ha : 0<a)
    (D : OriginalData ι) (hcard : Fintype.card ι≤N)
    (C : Ideal O) (hC : C≠0) (B : actualAllocations D.S C)
    (M : ι → ℝ) (hM : ∀ i,0≤M i) (hP : ∀ i,0<D.lengths i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hWnorm : ∀ i x,‖D.slot i x‖≤M i)
    (hW : ∀ i,Function.support (D.slot i)⊆Set.Icc a b) :
    ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2/rawReduction B.val D.lengths ≤
      (max 1 b)^N/(Ideal.absNorm C:ℝ)*(frozenControl B.val M)^2 := by
  have hB := (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1
  have hR := rawReduction_pos B.val hB D.lengths hP
  have hN := CenteredMomentFirstScale.norm_pos C hC
  by_cases hz : frozenCoefficient B.val C D.R D.nu D.slot D.lengths=0
  · rw [hz,norm_zero,zero_pow (by decide : 2≠0),zero_div]
    positivity
  · have hm := frozen_norm_bound D C B M hM hν hWnorm
    have hh := (actual_reduction_norm B.val hB C D.R
      (Finset.mem_filter.mp B.property).2 D.nu D.slot D.lengths hP a b ha hW hz).2
    have he : (max 1 b)^Fintype.card ι≤(max 1 b)^N :=
      pow_le_pow_right₀ (le_max_left _ _) hcard
    have hi : (1:ℝ)/rawReduction B.val D.lengths ≤ (max 1 b)^N/(Ideal.absNorm C:ℝ) := by
      apply (div_le_div_iff₀ hR hN).mpr
      simpa only [one_mul] using hh.trans (mul_le_mul_of_nonneg_right he hR.le)
    calc
      _ ≤ (frozenControl B.val M)^2/rawReduction B.val D.lengths :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hm _) hR.le
      _ = (frozenControl B.val M)^2*(1/rawReduction B.val D.lengths) := by ring
      _ ≤ (frozenControl B.val M)^2*((max 1 b)^N/(Ideal.absNorm C:ℝ)) :=
        mul_le_mul_of_nonneg_left hi (sq_nonneg _)
      _ = _ := by ring

theorem normalized_common_energy_allocation (D : OriginalData ι)
    (hS : ∀ i,∀ I∈D.S i,I≠0) (hp : ∀ i,∀ I∈D.S (Sum.inl i),Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hX₁ : 0<D.X₁) (hX₂ : 0<D.X₂) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0<D.lengths i) :
    commonEnergy D C hC τ t L W K / rawVolume D ≤
      ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        (‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2/rawReduction B.val D.lengths) *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  have hV := rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP
  have he := div_le_div_of_nonneg_right
    (common_energy_allocation D hS hp C hC hseed τ t L W K hK hW) hV.le
  apply he.trans_eq
  rw [mul_div_assoc,Finset.sum_div]
  apply congrArg (fun x : ℝ => ((actualAllocations D.S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  have hR := rawReduction_pos B.val
    (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP
  rw [allocated_rawVolume D C L B hB₁ hB₂ hP]
  field_simp

theorem normalized_common_energy_bound (N : ℕ) (a b : ℝ) (ha : 0<a)
    (D : OriginalData ι) (hcard : Fintype.card ι≤N)
    (hS : ∀ i,∀ I∈D.S i,I≠0) (hp : ∀ i,∀ I∈D.S (Sum.inl i),Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hX₁ : 0<D.X₁) (hX₂ : 0<D.X₂) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0<D.lengths i) (M : ι → ℝ) (hM : ∀ i,0≤M i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hWnorm : ∀ i x,‖D.slot i x‖≤M i)
    (hslot : ∀ i,Function.support (D.slot i)⊆Set.Icc a b) :
    commonEnergy D C hC τ t L W K / rawVolume D ≤
      (max 1 b)^N * ((actualAllocations D.S C).card:ℝ)/(Ideal.absNorm C:ℝ) *
        ∑ B : actualAllocations D.S C, (frozenControl B.val M)^2 *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  apply (normalized_common_energy_allocation D hS hp C hC hseed τ t L W K hK hW
    hX₁ hX₂ hB₁ hB₂ hP).trans
  calc
    _ ≤ ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ((max 1 b)^N/(Ideal.absNorm C:ℝ)*(frozenControl B.val M)^2) *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      have hVa : 0<rawVolume (allocatedData D C L B) := by
        rw [allocated_rawVolume D C L B hB₁ hB₂ hP]
        exact div_pos (rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP)
          (rawReduction_pos B.val (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP)
      exact mul_le_mul_of_nonneg_right
        (frozen_normalized_bound N a b ha D hcard C hC.1 B M hM hP hν hWnorm hslot)
        (div_nonneg (allocated_nonneg D C L B τ t W K hK hW) hVa.le)
    _ = _ := by
      simp only [mul_assoc,← Finset.mul_sum]
      ring

theorem normalized_common_as_tsum (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hV : 0<rawVolume D) :
    (∑' z : O, ‖(Real.sqrt (rawVolume D):ℂ)⁻¹ * commonGauss D C hC τ t L z‖^2 *
      (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) =
      commonEnergy D C hC τ t L W K/rawVolume D := by
  have hn (z : O) : ‖(Real.sqrt (rawVolume D):ℂ)⁻¹ * commonGauss D C hC τ t L z‖^2 =
      ‖commonGauss D C hC τ t L z‖^2/rawVolume D := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow,inv_pow,Real.sq_sqrt hV.le]
    ring
  simp_rw [hn,div_mul_eq_mul_div]
  exact tsum_div_const

theorem allocated_sum_hasSum (D : OriginalData ι) (C L : Ideal O)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ∑ B : actualAllocations D.S C,
      ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
        (‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
        (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re))
      (∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 * allocatedEnergy D C L B τ t W K) := by
  exact hasSum_sum (fun B _ => (allocated_hasSum D C L B τ t W K hK).mul_left _)

theorem original_radial_bound (N : ℕ) (a b : ℝ) (ha : 0<a) :
    ∃ F : ℝ,0<F ∧ ∀ {κ : Type*} [Fintype κ],∀ D : OriginalData κ,
      Fintype.card κ≤N →
      (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
      ∀ (C : Ideal O) (hC : Supported C), D.s∣C →
      ∀ (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K T : ℝ),
      0<K → (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      0<D.X₁ → 0<D.X₂ → D.B₁≠0 → D.B₂≠0 →
      (∀ i,0<D.lengths i) → D.X₁*D.X₂=T → D.Y₁*D.Y₂=T →
      ∀ M : κ → ℝ,(∀ i,0≤M i) → (∀ i I,‖D.nu i I‖≤1) →
      (∀ i x,‖D.slot i x‖≤M i) →
      (∀ i,Function.support (D.slot i)⊆Set.Icc a b) →
      (∑' z : O,
        ‖(Real.sqrt ((T/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂))*∏ i,D.lengths i):ℂ)⁻¹ *
          commonGauss D C hC τ t L z‖^2 * (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) ≤
        F*((actualAllocations D.S C).card:ℝ)/(Ideal.absNorm C:ℝ) *
          ∑ B : actualAllocations D.S C,(frozenControl B.val M)^2 *
            (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  refine ⟨(max 1 b)^N,pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _,?_⟩
  intro κ _ D hcard hS hp C hC hseed τ t L W K T hK hW hX₁ hX₂ hB₁ hB₂ hP hX hY M hM hν hWnorm hslot
  rw [← (rawVolume_both D T hX hY).1,
    normalized_common_as_tsum D C hC τ t L W K (rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP)]
  exact normalized_common_energy_bound N a b ha D hcard hS hp C hC hseed τ t L W K hK hW
    hX₁ hX₂ hB₁ hB₂ hP M hM hν hWnorm hslot

end SevenEighths.CenteredMomentFirstAllocationGaussEnergy

end

end OAI

end Source2017

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstMaskedInput.lean; sha256: 6ab20ce52e05c5917935dbc4bdded2b86930fb86392c8e2324cc6ea1ad36fbcb -/
section Source2018
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMaskedInput
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentFirstMaskedFamily CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRemainingBox
open CenteredMomentSourceLiveColumn CenteredMomentSecondHeightFamily
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

lemma profile_combined_mask (R T seed : Ideal O) (ν : ι→Ideal O→ℂ)
    (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v *
      idealMask (idealGenerator T) (finiteTupleProduct v) =
    profileCoefficient (R*T) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v := by
  rw [idealMask_generator]
  simp only [profileCoefficient, IsCoprime.mul_right_iff]
  split_ifs <;> simp_all

lemma column_combined_mask (S : Finset (Tuple ι)) (R T seed : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    maskedSource (idealGenerator T)
      (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed)) =
    finiteColumnCoefficient S (profileCoefficient (R*T) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed) := by
  funext I
  unfold maskedSource finiteColumnCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [←(Finset.mem_filter.mp hv).2]
  exact profile_combined_mask R T seed ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v

lemma input_combined_mask (s : Input ι) (R T seed : Ideal O) :
    maskedSource (idealGenerator T) (original s R seed).beta =
      (original s (R*T) seed).beta := by
  simpa only [OriginalData.beta, OriginalData.profile, original] using
    column_combined_mask (Fintype.piFinset s.pools) R T seed s.ν s.W s.P
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1

lemma extracted_input (s : Input ι) (η : Character) (R T seed C : Ideal O)
    (hC : Supported C) (t : ℝ) (I : Ideal O) :
    extractedSource η (idealGenerator T) C (original s R seed).beta t I =
      (original s (R*T) seed).beta (C*I) * rowWeight η fixedBadMask 1 1 t C := by
  rw [extractedSource_whole_mask η (idealGenerator T) C hC, input_combined_mask]
  rfl

theorem extracted_input_allocations (s : Input ι) (η τ : Character)
    (R T seed C I : Ideal O) (hC : Supported C) (hI : I≠0)
    (hseed : IsCoprime seed C) (t : ℝ) :
    (if IsCoprime C I then
      extractedSource η (idealGenerator T) C (original s R seed).beta t I else 0) =
    rowWeight η fixedBadMask 1 1 t C *
      ∑ B : actualAllocations s.pools C,
        frozenCoefficient B C (R*T) s.ν s.W s.P *
          (original (child s C (R*T) B τ t) ((R*T)*C) seed).beta I := by
  have hh := original_masked_live_column s.pools s.pools_ne
    (fun i J hJ => s.prime i J hJ) C (R*T) seed I hC.1 hI hseed
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
  rw [extracted_input s η R T seed C hC t I]
  calc
    _ = rowWeight η fixedBadMask 1 1 t C *
        (if IsCoprime C I then (original s (R*T) seed).beta (C*I) else 0) := by
      split_ifs <;> ring
    _ = rowWeight η fixedBadMask 1 1 t C *
        ∑ B : actualAllocations s.pools C, frozenCoefficient B C (R*T) s.ν s.W s.P *
          finiteColumnCoefficient
            (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
            (maskedLiveProfile B C (R*T) seed s.ν s.W s.P s.W₁ s.W₂
              s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I := by
      exact congrArg (fun z : ℂ => rowWeight η fixedBadMask 1 1 t C * z) hh
    _ = _ := by
      apply congrArg (fun z : ℂ => rowWeight η fixedBadMask 1 1 t C * z)
      apply Finset.sum_congr rfl
      intro B _
      exact congrArg (fun z : ℂ => frozenCoefficient B C (R*T) s.ν s.W s.P * z)
        (congrFun (child_columns s C (R*T) seed B τ t).2 I)

lemma normalized_input_mask (s : Input ι) (R T seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy (original s R seed).columns
      (maskedSource (idealGenerator T) (original s R seed).beta)
      (heightCoeff s.η s.t) W K).re / volume s =
      normalizedGaussSource s (R*T) seed W K := by
  rw [input_combined_mask]
  rfl

lemma child_input_combined_mask (s : Input ι) (C R T seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    maskedSource (idealGenerator T)
      (original (child s C R B τ t) (R*C) seed).beta =
      (original (child s C (R*T) B τ t) ((R*T)*C) seed).beta := by
  rw [input_combined_mask]
  simp only [OriginalData.beta, OriginalData.profile, original, child, commonData, Input.pools,
    mul_assoc, mul_comm C T]

lemma normalized_child_mask (s : Input ι) (C R T seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (maskedSource (idealGenerator T)
        (original (child s C R B τ t) (R*C) seed).beta)
      (heightCoeff τ t) W K).re / volume (child s C R B τ t) =
      childNormalizedGaussSource s C (R*T) seed B τ t W K := by
  have hcolumns :
      (original (child s C R B τ t) (R*C) seed).columns =
        (original (child s C (R*T) B τ t) ((R*T)*C) seed).columns :=
    (child_columns s C R seed B τ t).1.symm.trans (child_columns s C (R*T) seed B τ t).1
  have hvolume : volume (child s C R B τ t) = volume (child s C (R*T) B τ t) := by
    simp only [volume, child, commonData]
  unfold childNormalizedGaussSource normalizedGaussSource
  rw [child_input_combined_mask, hcolumns, hvolume, child_character, child_height]

end SevenEighths.CenteredMomentFirstMaskedInput

end

end OAI

end Source2018

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalSourceAllocatedInput.lean; sha256: 13243e36df80a67295f1e8a43c4ce3e747e0ea0168d329cae2c885d2ca67d520 -/
section Source2019
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow ConcretePrimeRowBridge
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentOriginalChildEnergy
open CenteredMomentSmoothedWindowEnergy CenteredMomentGaussEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance firstAllocatedInputDecidableEq {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma commonEnergy_real (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (commonEnergy D C hC τ t L W K).re =
      CenteredMomentFirstAllocationGaussEnergy.commonEnergy D C hC τ t L W K := by
  exact (gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator (CenteredMomentFirstSectors.residualPool C hC.1 D.columns))
    (sourceGenerator_supported _) _ W K hK).tsum_eq.symm

lemma original_rawVolume (s : Input ι) (R seed : Ideal O) :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (original s R seed)=volume s := by
  simp [CenteredMomentFirstAllocationGaussEnergy.rawVolume,original,volume]

lemma allocated_input_columns (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    (allocatedData (original s R seed) C L B).columns=
      (original (child s C R B τ t) (R*C) L).columns ∧
    (allocatedData (original s R seed) C L B).beta=
      (original (child s C R B τ t) (R*C) L).beta := by
  have hh := child_columns s C R L B τ t
  simpa only [OriginalData.columns,OriginalData.beta,allocated_pools,allocated_profile,original] using hh

lemma allocated_input_volume (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      volume (child s C R B τ t) := by
  simp only [CenteredMomentFirstAllocationGaussEnergy.rawVolume,allocatedData,original,
    volume,child,commonData,one_mul,div_mul_div_comm]

lemma allocated_input_energy (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s R seed) C L B τ t W K /
      CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      childNormalizedGaussSource s C R L B τ t W K := by
  obtain ⟨hc,hb⟩ := allocated_input_columns s C R seed L B τ t
  unfold CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy
  rw [hc,hb,allocated_input_volume s C R seed L B τ t]
  rfl

theorem common_energy_allocated_inputs (N : ℕ) (a b : ℝ) (ha : 0<a)
    (s : Input ι) (hcard : Fintype.card ι≤N) (haS : a≤s.lower) (hbS : s.upper≤b)
    (C R seed : Ideal O) (hC : Supported C) (hseed : seed∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (commonEnergy (original s R seed) C hC τ t L W K).re / volume s ≤
      (max 1 b)^N * ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
        ∑B : actualAllocations s.pools C,
          (CenteredMomentFirstAllocationGaussEnergy.frozenControl B.val s.M)^2 *
            childNormalizedGaussSource s C R L B τ t W K := by
  have hh := CenteredMomentFirstAllocationGaussEnergy.normalized_common_energy_bound N a b ha
    (original s R seed) hcard s.pools_ne s.prime C hC hseed τ t L W K hK hW
    s.X₁_pos s.X₂_pos one_ne_zero one_ne_zero s.P_pos s.M
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.ν_bound s.W_bound
    (fun i x hx=>⟨haS.trans (s.slot_support i hx).1,(s.slot_support i hx).2.trans hbS⟩)
  rw [← commonEnergy_real _ _ _ _ _ _ _ _ hK,original_rawVolume] at hh
  change (commonEnergy (original s R seed) C hC τ t L W K).re / volume s ≤
    (max 1 b)^N * ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
      ∑B : actualAllocations s.pools C,
        (CenteredMomentFirstAllocationGaussEnergy.frozenControl B.val s.M)^2 *
          (CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s R seed) C L B τ t W K /
            CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)) at hh
  simpa only [allocated_input_energy] using hh

lemma allocated_input_masked_energy (s : Input ι) (C R T seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s (R*T) seed) C L B τ t W K /
      CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s (R*T) seed) C L B)=
    (sourceGaussEnergy (original (child s C R B τ t) (R*C) L).columns
      (CenteredMomentFirstMaskedFamily.maskedSource (idealGenerator T)
        (original (child s C R B τ t) (R*C) L).beta)
      (heightCoeff τ t) W K).re / volume (child s C R B τ t) := by
  rw [allocated_input_energy,CenteredMomentFirstMaskedInput.normalized_child_mask]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI

end Source2019

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalSourceAllocationControl.lean; sha256: 4edef3cf37908d762c93dac08124cc435ec1df9b870dba093e2d6bf50f4552bd -/
section Source2020
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance firstAllocationControlDecidableEq {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma frozen_live_control (B : Tuple ι) (M : ι→ℝ) :
    frozenControl B M * (∏i : liveIndices B,M i.val) = ∏i,M i := by
  rw [Finset.prod_coe_sort (liveIndices B) M]
  unfold frozenControl liveIndices
  rw [mul_comm]
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i=>B (Sum.inl i)=1) M

lemma frozen_child_control (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : HeckeFamily.Character) (t : ℝ) :
    (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2 = (∏i,s.M i)^2 := by
  rw [←mul_pow]
  exact congrArg (fun x:ℝ=>x^2) (frozen_live_control B.val s.M)

lemma allocated_control_sum (s : Input ι) (C R : Ideal O)
    (τ : HeckeFamily.Character) (t : ℝ) :
    (∑B : actualAllocations s.pools C,
      (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2) =
      ((actualAllocations s.pools C).card:ℝ) * (∏i,s.M i)^2 := by
  simp only [frozen_child_control,Finset.sum_const,Finset.card_univ,Fintype.card_coe,
    nsmul_eq_mul]

theorem allocated_control_mass (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀{κ : Type*}[Fintype κ],Fintype.card κ≤N →
      ∀(s : Input κ)(C R : Ideal O),C≠0 →
      ∀(τ : HeckeFamily.Character)(t : ℝ),
        ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
          (∑B : actualAllocations s.pools C,
            (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2) ≤
          D*(Ideal.absNorm C:ℝ)^(ε-1)*(∏i,s.M i)^2 := by
  obtain ⟨D,hD,hcard⟩ := CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (N+2) (ε/2) (half_pos hε)
  refine ⟨D^2,sq_pos_of_pos hD,?_⟩
  intro κ _ hn s C R hC τ t
  have hN : (0:ℝ)<Ideal.absNorm C := CenteredMomentFirstScale.norm_pos C hC
  have hh := hcard (ι:=κ⊕Fin 2) (by simp only [Fintype.card_sum,Fintype.card_fin];omega)
    s.pools C hC
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (actualAllocations s.pools C).card) hh 2
  rw [mul_pow,←Real.rpow_mul_natCast hN.le,show ε/2*(2:ℕ)=ε by norm_num] at hs
  rw [allocated_control_sum]
  calc
    _ = (((actualAllocations s.pools C).card:ℝ)^2/(Ideal.absNorm C:ℝ)) * (∏i,s.M i)^2 := by ring
    _ ≤ (D^2*(Ideal.absNorm C:ℝ)^ε/(Ideal.absNorm C:ℝ)) * (∏i,s.M i)^2 :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs hN.le) (sq_nonneg _)
    _ = _ := by rw [Real.rpow_sub hN,Real.rpow_one];ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI

end Source2020

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstCommonSourceBudget.lean; sha256: 918971dc0018b2ee621314d645e72860bfeb5d8735caf644344132915ee2df45 -/
section Source2021
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonSourceBudget
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn CenteredMomentFirstAllocationGaussEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

lemma child_nonneg (s:Input ι)(C R seed:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)
    (hW:∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re):
    0≤childNormalizedGaussSource s C R seed B τ t W K:=by
  rw [←allocated_input_energy s C R seed seed B τ t W K]
  apply div_nonneg
  · exact allocated_nonneg (original s R seed) C seed B τ t W K hK hW
  · rw [allocated_input_volume s C R seed seed B τ t]
    exact (CenteredMomentAmplificationChildInput.volume_pos _).le

theorem common_energy_live_allocations (N:ℕ)(a b:ℝ)(ha:0<a)
    (s:Input ι)(hcard:Fintype.card ι≤N)(haS:a≤s.lower)(hbS:s.upper≤b)
    (C R seed:Ideal O)(hC:Supported C)(hseed:seed∣C)
    (τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)
    (hW:∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re):
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
    (max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ)*
      ∑B:actualAllocations s.pools C,
        if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
          (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K
        else 0:=by
  have hh:=normalized_common_energy_allocation (original s R seed) s.pools_ne s.prime C hC hseed
    τ t L W K hK hW s.X₁_pos s.X₂_pos one_ne_zero one_ne_zero s.P_pos
  rw [←commonEnergy_real _ _ _ _ _ _ _ _ hK,original_rawVolume] at hh
  change _ ≤ ((actualAllocations s.pools C).card:ℝ)*
    ∑B:actualAllocations s.pools C,
      (‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*
        (allocatedEnergy (original s R seed) C L B τ t W K/
          rawVolume (allocatedData (original s R seed) C L B)) at hh
  simp_rw [allocated_input_energy s C R seed L _ τ t W K] at hh
  apply hh.trans
  calc
    _≤((actualAllocations s.pools C).card:ℝ)*
      ∑B:actualAllocations s.pools C,
        ((max 1 b)^N/(C.absNorm:ℝ))*
          (if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
            (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K
          else 0):=by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      by_cases hz:frozenCoefficient B.val C R s.ν s.W s.P=0
      · simp only [hz,ne_eq,not_true_eq_false,ite_false,norm_zero,zero_pow (by decide:2≠0),zero_div,zero_mul,mul_zero]
        exact le_rfl
      · rw [ite_eq_left hz]
        have hf:=frozen_normalized_bound N a b ha (original s R seed) hcard C hC.1 B s.M
          (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.ν_bound s.W_bound
          (fun i x hx=>⟨haS.trans (s.slot_support i hx).1,(s.slot_support i hx).2.trans hbS⟩)
        have hn:=child_nonneg s C R L B τ t W K hK hW
        change ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P≤
          (max 1 b)^N/(C.absNorm:ℝ)*(frozenControl B.val s.M)^2 at hf
        convert mul_le_mul_of_nonneg_right hf hn using 1 ; ring
    _=_:=by rw [←Finset.mul_sum];ring

theorem common_energy_from_live_children (N:ℕ)(a b ε:ℝ)(ha:0<a)(hε:0<ε):
    ∃Cbound:ℝ,0<Cbound ∧ ∀{κ:Type*}[Fintype κ],∀s:Input κ,
    Fintype.card κ≤N → a≤s.lower → s.upper≤b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K E:ℝ),0<K → 0≤E →
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤E*(∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-1)*E*(∏i,s.M i)^2:=by
  obtain ⟨D,hD,hmass⟩:=allocated_control_mass N ε hε
  refine ⟨(max 1 b)^N*D,mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _) hD,?_⟩
  intro κ _ s hcard haS hbS C R seed hC hseed τ t L W K E hK hE hW hchild
  have hh:=common_energy_live_allocations N a b ha s hcard haS hbS C R seed hC hseed τ t L W K hK hW
  apply hh.trans
  have hc:0≤(max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ):=by positivity
  have hs:(∑B:actualAllocations s.pools C,
      if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
        (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K else 0)≤
      E*∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2:=by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro B hB
    split_ifs with hb
    · convert mul_le_mul_of_nonneg_left (hchild B hb) (sq_nonneg (frozenControl B.val s.M)) using 1 ; ring
    · positivity
  have hm:=hmass hcard s C R hC.1 τ t
  calc
    _≤((max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ))*
        (E*∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2):=
      mul_le_mul_of_nonneg_left hs hc
    _=((max 1 b)^N*E)*(((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ)*
        ∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2):=by ring
    _≤((max 1 b)^N*E)*(D*(C.absNorm:ℝ)^(ε-1)*(∏i,s.M i)^2):=
      mul_le_mul_of_nonneg_left hm (mul_nonneg (by positivity) hE)
    _=_:=by ring

end SevenEighths.CenteredMomentFirstCommonSourceBudget

end

end OAI

end Source2021

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstCommonSourcePowerBudget.lean; sha256: 70f57bc1b23cf733130caca630d46749a6ad6ef5a0deb1b8b359b94948b71e0f -/
section Source2022
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonSourcePowerBudget
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentFirstCommonSourceBudget
local notation "O"=>ActualEisensteinCubic.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem common_energy_power_budget (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cbound:ℝ,0<Cbound ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → a≤s.lower → s.upper≤b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ),0<K →
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    ∀(n:ℕ)(E α:Fin n→ℝ),(∀j,0≤E j)→(∀j,0≤α j)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤
        (∑j,E j*(CenteredMomentAmplificationChildInput.volume (child s C R B τ t))^(α j))*
          (∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-1)*
          (∑j,E j*(b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ))^(α j))*
            (∏i,s.M i)^2:=by
  obtain ⟨Cbound,hCbound,hbound⟩:=common_energy_from_live_children N a b ε ha hε
  refine ⟨Cbound,hCbound,?_⟩
  intro ι _ s hcard haS hbS C R seed hC hseed τ t L W K hK hW n E α hE hα hchild
  have hv:=CenteredMomentAmplificationChildInput.volume_pos s
  have hn:=CenteredMomentFirstScale.norm_pos C hC.1
  apply hbound s hcard haS hbS C R seed hC hseed τ t L W K _ hK
    (Finset.sum_nonneg (fun j _=>mul_nonneg (hE j) (Real.rpow_nonneg (by positivity) _))) hW
  intro B hB
  apply (hchild B hB).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hE j)
  exact Real.rpow_le_rpow (CenteredMomentAmplificationChildInput.volume_pos _).le
    (CenteredMomentAmplificationChildSourceCaps.common_volume_le N b hb s hcard hbS C R B τ t hB) (hα j)

theorem common_energy_linear_volume (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cbound:ℝ,0<Cbound ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → a≤s.lower → s.upper≤b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K E:ℝ),0<K → 0≤E →
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤
        E*CenteredMomentAmplificationChildInput.volume (child s C R B τ t)*
          (∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-2)*CenteredMomentAmplificationChildInput.volume s*E*(∏i,s.M i)^2:=by
  obtain ⟨Cbound,hCbound,hbound⟩:=common_energy_from_live_children N a b ε ha hε
  refine ⟨Cbound*b^N,mul_pos hCbound (pow_pos (zero_lt_one.trans_le hb) _),?_⟩
  intro ι _ s hcard haS hbS C R seed hC hseed τ t L W K E hK hE hW hchild
  have hv:=CenteredMomentAmplificationChildInput.volume_pos s
  have hn:=CenteredMomentFirstScale.norm_pos C hC.1
  have hh:=hbound s hcard haS hbS C R seed hC hseed τ t L W K
    (E*(b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ))) hK
    (mul_nonneg hE (by positivity)) hW (fun B hB=>by
      apply (hchild B hB).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (CenteredMomentAmplificationChildSourceCaps.common_volume_le N b hb s hcard hbS C R B τ t hB) hE)
        (sq_nonneg _))
  apply hh.trans_eq
  have hp:(C.absNorm:ℝ)^(ε-2)=(C.absNorm:ℝ)^(ε-1)/(C.absNorm:ℝ):=by
    rw [show ε-2=(ε-1)-1 by ring,Real.rpow_sub hn,Real.rpow_one]
  rw [hp]
  ring

end SevenEighths.CenteredMomentFirstCommonSourcePowerBudget

end

end OAI

end Source2022

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstCommonReferencePower.lean; sha256: 6e4df380f9fce104640b0a4ae257beed0dfab7c143a3bb14dda8958271e07caf -/
section Source2023
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonReferencePower
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentFirstCommonSourceBudget
open CenteredMomentFirstCommonSourcePowerBudget
local notation "O"=>HeckeFamily.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def normalizedPower (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ):ℝ:=
  C^ε*(b^N)^α*E/q*(V/C)^(α-1)*Z^(-allowance)

lemma normalizedPower_nonneg (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ)
    (hb:0≤b)(hV:0≤V)(hC:0≤C)(hq:0≤q)(hZ:0≤Z)(hE:0≤E):
    0≤normalizedPower b V C q Z allowance ε E N α:=by
  unfold normalizedPower
  positivity

lemma reference_power_identity (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ)
    (hb:0<b)(hV:0<V)(hC:0<C)(hq:0<q)(hZ:0<Z):
    (q*(V/C)^2*Z^allowance)*normalizedPower b V C q Z allowance ε E N α=
      C^(ε-1)*V*E*(b^N*V/C)^α:=by
  have hx:0<V/C:=div_pos hV hC
  have hbN:0<b^N:=pow_pos hb N
  have hprod:Z^allowance*Z^(-allowance)=1:=by
    rw [←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero]
  unfold normalizedPower
  rw [Real.rpow_sub hx,Real.rpow_one,Real.rpow_sub hC,Real.rpow_one,
    show b^N*V/C=b^N*(V/C) by ring,Real.mul_rpow hbN.le hx.le]
  field_simp
  calc
    _ = E*(Z^allowance*Z^(-allowance)):=by ring
    _ = E:=by rw [hprod,mul_one]

theorem common_energy_reference_powers (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N→a≤s.lower→s.upper≤b→
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C→
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K Z allowance:ℝ),0<K→0<Z→
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    ∀(n:ℕ)(E α:Fin n→ℝ),(∀j,0≤E j)→(∀j,0≤α j)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0→
      childNormalizedGaussSource s C R L B τ t W K≤
        (∑j,E j*(volume (child s C R B τ t))^(α j))*(∏i,(child s C R B τ t).M i)^2)→
    (commonEnergy (original s R seed) C hC τ t L W K).re≤
      ((τ.modulus.absNorm:ℝ)*(volume s/(C.absNorm:ℝ))^2*Z^allowance)*
        (Cb*(∏i,s.M i)^2*∑j,normalizedPower b (volume s) (C.absNorm:ℝ)
          (τ.modulus.absNorm:ℝ) Z allowance ε (E j) N (α j)):=by
  obtain ⟨Cb,hCb,hbound⟩:=common_energy_power_budget N a b ε ha hb hε
  refine ⟨Cb,hCb,?_⟩
  intro ι _ s hc hlo hhi C R seed hC hseed τ t L W K Z allowance hK hZ hW n E α hE hα hchild
  have hV:=volume_pos s
  have hNC:=CenteredMomentFirstScale.norm_pos C hC.1
  have hq:=CenteredMomentFirstScale.norm_pos τ.modulus τ.modulus_ne_bot
  have hh:=hbound s hc hlo hhi C R seed hC hseed τ t L W K hK hW n E α hE hα hchild
  have hh':=(div_le_iff₀ hV).mp hh
  apply hh'.trans_eq
  calc
    _ = Cb*(∏i,s.M i)^2*∑j,(C.absNorm:ℝ)^(ε-1)*volume s*E j*
        (b^N*volume s/(C.absNorm:ℝ))^(α j):=by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = Cb*(∏i,s.M i)^2*∑j,
        ((τ.modulus.absNorm:ℝ)*(volume s/(C.absNorm:ℝ))^2*Z^allowance)*
          normalizedPower b (volume s) (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ)
            Z allowance ε (E j) N (α j):=by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact (reference_power_identity b (volume s) (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ)
        Z allowance ε (E j) N (α j) (zero_lt_one.trans_le hb) hV hNC hq hZ).symm
    _ = _:=by rw [←Finset.mul_sum];ring

end SevenEighths.CenteredMomentFirstCommonReferencePower

end

end OAI

end Source2023

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstExceptionalChildPaid.lean; sha256: 301e5d9ba5bcb15e3e1eb5f1e24b10dd4c77f84d49c4c1fc03e0dad6549d1e28 -/
section Source2024
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstExceptionalChildPaid
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentFirstChildLower
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstExceptionalPaidScales CenteredMomentCompleteCommon
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def inputCap (Z:ℝ)(s:Input ι):ℝ:=
  min (min (Real.logb Z s.X₁) (Real.logb Z s.X₂))
    (min (Real.logb Z s.Y₁) (Real.logb Z s.Y₂))

lemma input_cap_lower (Z r:ℝ)(hZ:1<Z)(s:Input ι)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    r ≤ inputCap Z s:=by
  have h (x:ℝ)(hx:Z^r≤x):r≤Real.logb Z x:=by
    have hh:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) r) hx
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  exact le_min (le_min (h _ hX₁) (h _ hX₂)) (le_min (h _ hY₁) (h _ hY₂))

lemma input_cap_scales (Z:ℝ)(hZ:1<Z)(s:Input ι):
    Z^(inputCap Z s)≤s.X₁ ∧ Z^(inputCap Z s)≤s.X₂ ∧
      Z^(inputCap Z s)≤s.Y₁ ∧ Z^(inputCap Z s)≤s.Y₂:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have h (x:ℝ)(hx:0<x)(hl:inputCap Z s≤Real.logb Z x):Z^(inputCap Z s)≤x:=by
    calc
      _≤Z^(Real.logb Z x):=Real.rpow_le_rpow_of_exponent_le hZ.le hl
      _=x:=Real.rpow_logb hz hZ.ne' hx
  refine ⟨h _ s.X₁_pos ?_,h _ s.X₂_pos ?_,h _ s.Y₁_pos ?_,h _ s.Y₂_pos ?_⟩
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem main_child_stage (Z A M:ℝ)(hZ:1<Z)(b:Branch Z)(hb:b.w=0)
    (s:Input ι)(R:Ideal O)
    (B:actualAllocations s.pools (commonPart b.I b.J))(τ:Character)(t:ℝ)
    (hX₁:Z^(M/4)≤s.X₁)(hX₂:Z^(M/4)≤s.X₂)
    (hY₁:Z^(M/4)≤s.Y₁)(hY₂:Z^(M/4)≤s.Y₂):
    let d:=child s (commonPart b.I b.J) R B τ t
    A-5*M/6-saving b-2*max (inputCap Z d) 0/3≤A-M+loss b:=by
  have hh:=child_lower s (commonPart b.I b.J) R (commonPart_ne_zero b.I b.J)
    B τ t Z (M/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hs:=actual_saving hZ b
  have hm:=le_max_left (inputCap Z (child s (commonPart b.I b.J) R B τ t)) (0:ℝ)
  dsimp only [removedWidth] at hs
  rw [hb] at hs
  dsimp only
  linarith

theorem error_child_stage (Z A M:ℝ)(hZ:1<Z)(b:Branch Z)
    (s:Input ι)(R:Ideal O)
    (B:actualAllocations s.pools (commonPart b.I b.J))(τ:Character)(t:ℝ)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (Bp:actualAllocations (child s (commonPart b.I b.J) R B τ t).pools (Q^k))
    (υ:Character)(v:ℝ)(hw:b.w=(k:ℝ)*Real.logb Z (Q.absNorm:ℝ))
    (hX₁:Z^(M/4)≤s.X₁)(hX₂:Z^(M/4)≤s.X₂)
    (hY₁:Z^(M/4)≤s.Y₁)(hY₂:Z^(M/4)≤s.Y₂):
    let d:=twiceChild s (commonPart b.I b.J) R B τ t Q k Bp υ v
    A-5*M/6-saving b-2*max (inputCap Z d) 0/3≤A-M+loss b:=by
  have hh:=twice_lower s (commonPart b.I b.J) R (commonPart_ne_zero b.I b.J)
    B τ t Q hQ k Bp υ v Z (M/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hs:=actual_saving hZ b
  have hm:=le_max_left (inputCap Z (twiceChild s (commonPart b.I b.J) R B τ t Q k Bp υ v)) (0:ℝ)
  dsimp only [removedWidth] at hs
  rw [hw] at hs
  dsimp only at hr ⊢
  linarith

theorem actual_error_pair (Z A M:ℝ)(hZ:1<Z)(b:Fin 2→Branch Z)
    (s:Input ι)(R:Ideal O)
    (B:∀j,actualAllocations s.pools (commonPart (b j).I (b j).J))
    (τ:Fin 2→Character)(t:Fin 2→ℝ)(Q:Fin 2→Ideal O)(hQ:∀j,Q j≠0)(k:Fin 2→ℕ)
    (Bp:∀j,actualAllocations
      (child s (commonPart (b j).I (b j).J) R (B j) (τ j) (t j)).pools ((Q j)^(k j)))
    (υ:Fin 2→Character)(v:Fin 2→ℝ)
    (hw:∀j,(b j).w=(k j:ℝ)*Real.logb Z ((Q j).absNorm:ℝ))
    (hX₁:Z^(M/4)≤s.X₁)(hX₂:Z^(M/4)≤s.X₂)
    (hY₁:Z^(M/4)≤s.Y₁)(hY₂:Z^(M/4)≤s.Y₂):
    let d:=fun j=>twiceChild s (commonPart (b j).I (b j).J) R
      (B j) (τ j) (t j) (Q j) (k j) (Bp j) (υ j) (v j)
    A-5*M/6-(saving (b 0)+saving (b 1))/2-
      (max (inputCap Z (d 0)) 0+max (inputCap Z (d 1)) 0)/3≤
      max (A-M) 0+(loss (b 0)+loss (b 1))/2:=by
  have h₀:=error_child_stage Z A M hZ (b 0) s R (B 0) (τ 0) (t 0) (Q 0) (hQ 0)
    (k 0) (Bp 0) (υ 0) (v 0) (hw 0) hX₁ hX₂ hY₁ hY₂
  have h₁:=error_child_stage Z A M hZ (b 1) s R (B 1) (τ 1) (t 1) (Q 1) (hQ 1)
    (k 1) (Bp 1) (υ 1) (v 1) (hw 1) hX₁ hX₂ hY₁ hY₂
  have hm:=le_max_left (A-M) (0:ℝ)
  dsimp only at h₀ h₁ ⊢
  linarith

end SevenEighths.CenteredMomentFirstExceptionalChildPaid

end

end OAI

end Source2024

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstMixedChild.lean; sha256: 61e85836ef0acf01d3ffe10f0ac08c012a4cf0b27523a9626741025e21179829 -/
section Source2025
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedChild
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstChildLower CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedCommonRadius
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool ConcreteTraceCRT
open CenteredMomentRankinRadical ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem actual_main_child_stage (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t parentA parentM:ℝ)
    (hX₁:Z^(parentM/4)≤s.X₁)(hX₂:Z^(parentM/4)≤s.X₂)
    (hY₁:Z^(parentM/4)≤s.Y₁)(hY₂:Z^(parentM/4)≤s.Y₂) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    parentA-5*parentM/6-(
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (extractedAllowance I J Z)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3))-2*max (inputCap Z (child s (commonPart I J) Rmask B τ t)) 0/3≤
      parentA-parentM+4*sigma/3+5*(delta+reserve)/6 := by
  have hs:=actual_main_column_saving η τ m I J E hI hJ A K X Z j sigma delta reserve hZ hmod
  have hh:=child_lower s (commonPart I J) Rmask (commonPart_ne_zero I J)
    B τ t Z (parentM/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hm:=le_max_left (inputCap Z (child s (commonPart I J) Rmask B τ t)) (0:ℝ)
  dsimp only at hs hr ⊢
  linarith

theorem actual_error_child_stage (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t parentA parentM:ℝ)
    (Bp:actualAllocations (child s (commonPart I J) Rmask B τ t).pools ((Ideal.span {p0})^k))
    (υ:Character)(v:ℝ)
    (hX₁:Z^(parentM/4)≤s.X₁)(hX₂:Z^(parentM/4)≤s.X₂)
    (hY₁:Z^(parentM/4)≤s.Y₁)(hY₂:Z^(parentM/4)≤s.Y₂) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    parentA-5*parentM/6-(
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (extractedAllowance I J Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0)-2*max (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) 0/3≤
      parentA-parentM+3*sigma/2+5*(delta+reserve)/6 := by
  have hs:=actual_error_column_saving η τ m I J E hI hJ A K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have hQ:Ideal.span {p0}≠0:=Ideal.span_singleton_eq_bot.not.mpr hd.1.ne_zero
  have hh:=twice_lower s (commonPart I J) Rmask (commonPart_ne_zero I J)
    B τ t (Ideal.span {p0}) hQ k Bp υ v Z (parentM/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hm:=le_max_left (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) (0:ℝ)
  dsimp only at hs hr ⊢
  unfold errorRemoval normValue at hs ⊢
  linarith

end SevenEighths.CenteredMomentFirstMixedChild

end

end OAI

end Source2025

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstMixedExceptionalCap.lean; sha256: a1b901062818d310d81792ad776617ba7ca8963055748707dc2186e3609c89b7 -/
section Source2026
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedExceptionalCap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

lemma fixed_presentation_log_nonneg (Z:ℝ)(hZ:1<Z):0≤Real.logb Z fixedPresentationCost:=by
  have h₁:(1:ℝ)≤((Ideal.span {fixedBadMask}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  have h₂:(1:ℝ)≤((Ideal.span {(72:O)}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
  apply Real.logb_nonneg hZ
  unfold fixedPresentationCost
  nlinarith

lemma extracted_allowance_eq (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D)(Z:ℝ):extractedAllowance C D Z=allowance C D Z:=by
  simp only [extractedAllowance,allowance,commonPart_of_equal_support C D hC hCD,
    commonPart_of_equal_support D C hD hCD.symm]

theorem actual_main_exceptional_cap (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t:ℝ)(hK:0<K)(hX:0<X)(_hvolume:X=volume s)
    (hX₁:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.X₁)(hX₂:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.X₂)
    (hY₁:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.Y₁)(hY₂:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.Y₂) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max (inputCap Z (child s (commonPart I J) Rmask B τ t)) 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+4*sigma/3+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_main_child_stage η τ fixedBadMask I J E hI hJ A K X Z j sigma delta reserve hZ hmod s Rmask B t (Real.logb Z X) (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)) hX₁ hX₂ hY₁ hY₂
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have he:=(actual_exceptional_reference η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j) 0 0 (sigma/3) hK hX hZ hmod).le
  rw [←hE] at he
  have hrad:0<mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  rw [show j+(Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j)=Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  simp only [neg_zero,Real.rpow_zero,mul_one,div_one] at he
  have hexp:-sigma/3=-(sigma/3):=by ring
  rw [hexp]
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max (inputCap Z (child s (commonPart I J) Rmask B τ t)) 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

theorem actual_error_exceptional_cap (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t:ℝ)(hK:0<K)(hX:0<X)(_hvolume:X=volume s)
    (Bp:actualAllocations (child s (commonPart I J) Rmask B τ t).pools ((Ideal.span {p0})^k))
    (υ:Character)(v:ℝ)
    (hX₁:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.X₁)(hX₂:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.X₂)
    (hY₁:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.Y₁)(hY₂:Z^((Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/4)≤s.Y₂) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+3*sigma/2+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_error_child_stage η τ fixedBadMask I J E hI hJ A K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk s Rmask B t (Real.logb Z X) (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)) Bp υ v hX₁ hX₂ hY₁ hY₂
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have hp:=elementPool_data _
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have he:=actual_error_reference_le η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j) hK hX hZ hmod p0 hp.1.ne_zero k hk
  rw [←hE] at he
  have hrad:0<errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k:=by unfold errorCommonRadius;positivity
  rw [show j+(Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j)=Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

end SevenEighths.CenteredMomentFirstMixedExceptionalCap

end

end OAI

end Source2026

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstMixedExceptionalLow.lean; sha256: d03293d9714f49143b6f572d4282894481d7a3ccfc6419948d77076546943d5f -/
section Source2027
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedExceptionalLow
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstMixedExceptionalCap CenteredMomentFirstMixedCommonRadius

theorem actual_main_exceptional_reference (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0<K)(hX:0<X) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(Real.logb Z X-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+4*sigma/3+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max r 0 := le_max_right _ _
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_main_column_saving η τ fixedBadMask I J E hI hJ A
    K X Z j sigma delta reserve hZ hmod
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have he:=(actual_exceptional_reference η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j) 0 0 (sigma/3) hK hX hZ hmod).le
  rw [←hE] at he
  have hrad:0<mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  rw [show j+(Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)-j)=Real.logb Z (mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  simp only [neg_zero,Real.rpow_zero,mul_one,div_one] at he
  have hexp:-sigma/3=-(sigma/3):=by ring
  rw [hexp]
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max r 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

theorem actual_error_exceptional_reference (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0<K)(hX:0<X) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(Real.logb Z X-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+3*sigma/2+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max r 0 := le_max_right _ _
  have hi : 0 ≤ Real.logb Z (I.absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hc:=commonPart_of_equal_support I J hI.1 hIJ
  have hd:=commonPart_of_equal_support J I hJ.1 hIJ.symm
  have hs:=actual_error_column_saving η τ fixedBadMask I J E hI hJ A
    K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk
  dsimp only at hs
  simp only [hc,hd,extracted_allowance_eq I J hI.1 hJ.1 hIJ Z] at hs
  have hp:=elementPool_data _
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have hl : 0 ≤ Real.logb Z (normValue p0) :=
    Real.logb_nonneg hZ (normValue_ge_one p0 hp.1.ne_zero)
  have hw : 0 ≤ errorRemoval p0 Z k := by unfold errorRemoval; positivity
  have he:=actual_error_reference_le η τ I J hI hJ hIJ A K X Z j
    (Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j) hK hX hZ hmod p0 hp.1.ne_zero k hk
  rw [←hE] at he
  have hrad:0<errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k:=by unfold errorCommonRadius;positivity
  rw [show j+(Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)-j)=Real.logb Z (errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k) by ring,
    Real.rpow_logb hz hZ.ne' hrad] at he
  have hmul:=mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hz.le (-2*max r 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

theorem actual_main_exceptional_low (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0<K)(hX:0<X)
    (hLow : Real.logb Z X ≤ 5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(4*sigma/3+5*(delta+reserve)/6) := by
  apply (actual_main_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod hK hX).trans
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem actual_error_exceptional_low (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0<K)(hX:0<X)
    (hLow : Real.logb Z X ≤ 5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3)≤
      Z^(3*sigma/2+5*(delta+reserve)/6) := by
  apply (actual_error_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod M H Sbad hbad p0 hp0 k hk hK hX).trans
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

end SevenEighths.CenteredMomentFirstMixedExceptionalLow

end

end OAI

end Source2027

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstMixedExceptionalDeclared.lean; sha256: a7853dd0c5962258178ce8f28982430b72d96a70f6769a75008580761a424282 -/
section Source2028
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedExceptionalDeclared
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedChild
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentRankinRadical
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstMixedExceptionalCap CenteredMomentFirstMixedCommonRadius

open CenteredMomentFirstMixedExceptionalLow

theorem actual_main_exceptional_declared (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0<K)(hX:0<X)
    (Mdecl : ℝ) (hactual : Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ) ≤ Mdecl)
    (hLow : Real.logb Z X ≤ 5*Mdecl/6) :
    (K*(η.modulus.absNorm:ℝ))*(((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3))≤
      Z^(Mdecl+4*sigma/3+5*(delta+reserve)/6) := by
  have hh:=actual_main_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod hK hX
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:0<(η.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hpow:K*(η.modulus.absNorm:ℝ)=Z^(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)):=by
    rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hn]
  apply (mul_le_mul_of_nonneg_left hh (mul_pos hK hn).le).trans
  rw [hpow,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

theorem actual_error_exceptional_declared (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve r : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0<K)(hX:0<X)
    (Mdecl : ℝ) (hactual : Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ) ≤ Mdecl)
    (hLow : Real.logb Z X ≤ 5*Mdecl/6) :
    (K*(η.modulus.absNorm:ℝ))*(((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max r 0/3))≤
      Z^(Mdecl+3*sigma/2+5*(delta+reserve)/6) := by
  have hh:=actual_error_exceptional_reference η τ I J E hI hJ hIJ A hE K X Z j sigma delta reserve r hZ hmod M H Sbad hbad p0 hp0 k hk hK hX
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:0<(η.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hpow:K*(η.modulus.absNorm:ℝ)=Z^(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)):=by
    rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hn]
  apply (mul_le_mul_of_nonneg_left hh (mul_pos hK hn).le).trans
  rw [hpow,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

end SevenEighths.CenteredMomentFirstMixedExceptionalDeclared

end

end OAI

end Source2028

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstMixedDiagonal.lean; sha256: fa9cccf093fa2b95cce0312b24265a3e6f333660d8241ba29bbc973592325a67 -/
section Source2029
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedDiagonal
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedExceptionalCap
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstExceptionalPrefactor CenteredMomentDescentLedger
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCanonicalFirst CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationErrorEnergy
local notation "O"=>HeckeFamily.O

theorem actual_common_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z w wo branch sigma delta reserve eps:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)
    (hw:0≤w)(hwo:0≤wo)(heps:0≤eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=nominalLog C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    (V/(C.absNorm:ℝ))*Z^(-wo)*
      Z^(K0+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve)*
      (V/(C.absNorm:ℝ)/Z^w)^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        branch*sigma+delta+reserve+eps*Real.logb Z V):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hnc:=norm_pos C hC.1
  have hnd:=norm_pos D hD.1
  have hne:=norm_pos _ (subsetGenerator_supported C D hC E).1
  have hnr:=active_norm_pos C D
  have hnq:=norm_pos _ τ.modulus_ne_bot
  have hη:=norm_pos _ η.modulus_ne_bot
  have hf:=fixedPresentationCost_pos
  have hc:0≤Real.logb Z (C.absNorm:ℝ):=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1))
  have hd:0≤Real.logb Z (D.absNorm:ℝ):=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1))
  have hallow:=allowance_nonneg C D Z
  have hfix:=fixed_presentation_log_nonneg Z hZ
  have hm:max (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)-2*w+wo) 0≤
      Real.logb Z (D.absNorm:ℝ)+wo:=max_le (by linarith) (by linarith)
  have he:eps*(Real.logb Z (C.absNorm:ℝ)+w)≥0:=mul_nonneg heps (add_nonneg hc hw)
  have hq:=actual_reference_width η τ C D hC E K Z hK hZ hmod
  have hnom:nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z=
      Real.logb Z ((Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)+2*Real.logb Z V-
      Real.logb Z K-Real.logb Z (C.absNorm:ℝ)-Real.logb Z (D.absNorm:ℝ):=by
    rw [nominalLog,nominal_equal_support C D _ hC.1 hD.1 hCD K V]
    simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow]
    ring
  dsimp only
  apply (Real.logb_le_iff_le_rpow hZ (by positivity)).mp
  simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_rpow hz hZ.ne',Real.logb_rpow_eq_mul_logb_of_pos,Real.logb_pow]
  rw [hnom]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hq,hm,he,hfix,hallow]

theorem actual_main_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve eps:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)(heps:0≤eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    (V/(C.absNorm:ℝ))*mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve*(V/(C.absNorm:ℝ))^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        2*sigma+delta+reserve+eps*Real.logb Z V):=by
  simpa only [mainCommonRadius,zero_mul,mul_zero,sub_zero,add_zero,neg_zero,
    Real.rpow_zero,mul_one,div_one] using
    actual_common_diagonal η τ C D hC hD hCD E K V Z 0 0 2 sigma delta reserve eps
      hK hV hZ (le_refl _) (le_refl _) heps hmod

theorem actual_error_diagonal (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve eps:ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z)(heps:0≤eps)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    (V/(C.absNorm:ℝ))*localErrorCost p (k-1)*errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k*(V/(C.absNorm:ℝ)/(normValue p)^k)^eps/
      ((τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z))≤
      Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        sigma+delta+reserve+eps*Real.logb Z V):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hpv:=normValue_pos p hp
  have hcpos:=norm_pos C hC.1
  have hqpos:=norm_pos _ τ.modulus_ne_bot
  have hl:0≤Real.logb Z (normValue p):=Real.logb_nonneg hZ (normValue_ge_one p hp)
  have hw:0≤errorRemoval p Z k:=by unfold errorRemoval;positivity
  have hwo:0≤errorMoving p Z k:=by unfold errorMoving;split_ifs <;> positivity
  have hh:=actual_common_diagonal η τ C D hC hD hCD E K V Z
    (errorRemoval p Z k) (errorMoving p Z k) 1 sigma delta reserve eps hK hV hZ hw hwo heps hmod
  dsimp only at hh
  rw [one_mul,errorRemoval_power p hp Z hZ k] at hh
  apply le_trans ?_ hh
  unfold errorCommonRadius
  gcongr
  exact actual_error_weight p hp Z hZ k hk

end SevenEighths.CenteredMomentFirstMixedDiagonal

end

end OAI

end Source2029

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstMixedMainError.lean; sha256: 6994139a70973718f33a9a7e86ffbda4d5ce013517390b012ab004b0b3a6e740 -/
section Source2030
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedMainError
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstMixedNormalization CenteredMomentFirstSourceConductorCaps
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem actual_error_conductor_weight (ρ υ:Character)(χ:RayFourExpansion.RayCharacter)
    (p:O)(hp:p≠0)(n:ℕ)(hn:n=0 ∨ n=5 ∨ n=6)(Z:ℝ)(hZ:1<Z)
    (hυ:υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p (errorMovingExponent n)):
    localErrorCost p n*(υ.modulus.absNorm:ℝ)≤rayCost*(ρ.modulus.absNorm:ℝ):=by
  have hray:=CenteredMomentSecondRadicalBudget.child_modulus_bound ρ χ
  have hN:(υ.modulus.absNorm:ℝ)≤
      ((childCharacter ρ χ).modulus.absNorm:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*Z^(errorMoving p Z (n+1)):=by
    rw [←radicalBound_error_power (childCharacter ρ χ) fixedBadMask p hp Z hZ n hn]
    exact_mod_cast hυ
  have hcap:(υ.modulus.absNorm:ℝ)≤
      rayCost*(ρ.modulus.absNorm:ℝ)*Z^(errorMoving p Z (n+1)):=by
    apply hN.trans
    have hr:((childCharacter ρ χ).modulus.absNorm:ℝ)≤
        (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm:=by exact_mod_cast hray
    calc
      _≤((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          Z^(errorMoving p Z (n+1)):=by gcongr
      _=_:=by unfold rayCost fixedPresentationCost;ring
  have hk:n+1=1 ∨ n+1=6 ∨ n+1=7:=by omega
  have hc:=actual_error_weight p hp Z hZ (n+1) hk
  simp only [Nat.add_sub_cancel] at hc
  have hh:=mul_le_mul hc hcap (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  apply hh.trans_eq
  calc
    _=(rayCost*(ρ.modulus.absNorm:ℝ))*(Z^(-errorMoving p Z (n+1))*Z^(errorMoving p Z (n+1))):=by ring
    _=_:=by rw [←Real.rpow_add (zero_lt_one.trans hZ),neg_add_cancel,Real.rpow_zero,mul_one]

theorem actual_main_error_reference (ρ υ:Character)(χ:RayFourExpansion.RayCharacter)
    (p:O)(hp:p≠0)(n:ℕ)(hn:n=0 ∨ n=5 ∨ n=6)(Z V C B E:ℝ)
    (hZ:1<Z)(hV:0<V)(hC:0<C)(hE:0≤E)
    (hυ:υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p (errorMovingExponent n)):
    (V/C)*localErrorCost p n*(υ.modulus.absNorm:ℝ)*(V/C/(normValue p)^(n+1))*E/
      ((ρ.modulus.absNorm:ℝ)*(V/C)^2*Z^B)≤
      rayCost*Z^(-errorRemoval p Z (n+1)-B)*E:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hpv:=normValue_pos p hp
  have hq:0<(ρ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ρ.modulus_ne_bot)
  have hh:=actual_error_conductor_weight ρ υ χ p hp n hn Z hZ hυ
  calc
    _=((V/C)*(localErrorCost p n*(υ.modulus.absNorm:ℝ))*(V/C/(normValue p)^(n+1))*E)/
        ((ρ.modulus.absNorm:ℝ)*(V/C)^2*Z^B):=by ring
    _≤((V/C)*(rayCost*(ρ.modulus.absNorm:ℝ))*(V/C/(normValue p)^(n+1))*E)/
        ((ρ.modulus.absNorm:ℝ)*(V/C)^2*Z^B):=by gcongr
    _=rayCost*Z^(-errorRemoval p Z (n+1)-B)*E:=by
      rw [Real.rpow_sub hz,Real.rpow_neg hz.le,errorRemoval_power p hp Z hZ (n+1)]
      field_simp

end SevenEighths.CenteredMomentFirstMixedMainError

end

end OAI

end Source2030

/- Original source: OAI/NumberTheory/DirichletL/Moments/SuccessorPaidParameters.lean; sha256: 7e9636ba66ca1690d479d54926359afd6f913f7c4039b1ae421d82267d611e70 -/
section Source2031
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentSuccessorPaidParameters
open CenteredMomentFirstSecondLossParameters

def edge (epsChild epsRemove delta epsilon delta1 delta2 theta kappa mesh : ℝ) : ℝ :=
  epsChild+epsRemove+2*delta+epsilon+delta2+delta1/6+kappa*mesh+7*theta/3

def exceptional (sigma deltafr epsilon delta B theta : ℝ) : ℝ :=
  3*sigma+5*deltafr/6+2*epsilon+2*delta+2*(5*B+1)*theta

def diagonal (sigma delta reserve epsilon A : ℝ) : ℝ :=
  2*sigma+delta+reserve+epsilon*A

lemma paid_normalization (Z shortening allowance paid : ℝ) (hZ : 0<Z) :
    Z^(-shortening-allowance)*Z^(shortening+paid)=Z^(paid-allowance) := by
  rw [←Real.rpow_add hZ]
  congr 1
  ring

lemma paid_normalization_with_ratio (Z shortening allowance paid ratio : ℝ)
    (hZ : 0<Z) :
    Z^(-shortening-allowance)*(Z^(shortening+paid)*ratio^((1:ℝ)/6))=
      Z^(paid-allowance)*ratio^((1:ℝ)/6) := by
  rw [←mul_assoc,paid_normalization Z shortening allowance paid hZ]

theorem actual_paid_error_reference
    (ρ υ : HeckeFamily.Character) (χ : RayFourExpansion.RayCharacter)
    (p : HeckeFamily.O) (hp : p≠0) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (Z V C allowance paid : ℝ) (hZ : 1<Z) (hV : 0<V) (hC : 0<C)
    (hυ : υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter ρ χ)
      CenteredMomentSecondHeightFamily.fixedBadMask p
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent n)) :
    (V/C)*CenteredMomentAmplificationErrorEnergy.localErrorCost p n*
      (υ.modulus.absNorm:ℝ)*(V/C/(CenteredMomentSectorLocalization.normValue p)^(n+1))*
      Z^(CenteredMomentFirstAmplificationChoice.errorRemoval p Z (n+1)+paid)/
      ((ρ.modulus.absNorm:ℝ)*(V/C)^2*Z^allowance)≤
      CenteredMomentFirstSourceConductorCaps.rayCost*Z^(paid-allowance) := by
  have hh:=CenteredMomentFirstMixedMainError.actual_main_error_reference
    ρ υ χ p hp n hn Z V C allowance
    (Z^(CenteredMomentFirstAmplificationChoice.errorRemoval p Z (n+1)+paid))
    hZ hV hC (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hυ
  apply hh.trans_eq
  rw [mul_assoc,paid_normalization Z _ allowance paid (zero_lt_one.trans hZ)]

lemma declared_parent_deficit (actual declared loss : ℝ) (h : actual≤declared) :
    actual+(declared-actual)/6+loss≤declared+loss := by linarith

lemma paired_declared_parent (actual declared left right loss : ℝ)
    (h : actual≤declared)
    (hl : left≤(declared-actual)/6+loss)
    (hr : right≤(declared-actual)/6+loss) :
    actual+(left+right)/2≤declared+loss := by linarith

lemma mesh_cost (kappa reserve : ℝ) (hk : 0≤kappa) (hr : 0≤reserve) :
    kappa*(reserve/(kappa+1))≤reserve := by
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0<kappa+1)).mpr
  nlinarith

theorem simultaneous_parameters (Mcap B kappa epsilonTarget : ℝ)
    (hM : 0≤Mcap) (hB : 0≤B) (hk : 0≤kappa) (he : 0<epsilonTarget) :
    ∃ sigma reserve mesh : ℝ,
      0<sigma ∧ sigma≤1 ∧ sigma≤epsilonTarget/1000 ∧
      0<reserve ∧ 0<mesh ∧ mesh≤reserve ∧ kappa*mesh≤reserve ∧
      20*reserve≤sigma/2 ∧
      Mcap<(depth Mcap sigma:ℝ)*sigma/2 ∧
      (∀ epsChild epsRemove delta epsilon delta1 delta2 theta,
        epsChild≤reserve → epsRemove≤reserve → delta≤reserve → epsilon≤reserve →
        delta1≤reserve → delta2≤reserve → theta≤reserve →
        (depth Mcap sigma:ℝ)*edge epsChild epsRemove delta epsilon delta1 delta2 theta kappa mesh
          ≤epsilonTarget/16) ∧
      (∀ deltafr epsilon delta theta,
        deltafr≤reserve → epsilon≤reserve → delta≤reserve → theta≤reserve →
        exceptional sigma deltafr epsilon delta B theta≤epsilonTarget/16) ∧
      (∀ delta other epsilon A,
        delta≤reserve → other≤reserve → 0≤epsilon → epsilon≤reserve → A≤Mcap →
        diagonal sigma delta other epsilon A≤epsilonTarget/16) := by
  let sigma : ℝ := min 1 (epsilonTarget/1000)
  have hs : 0<sigma := lt_min (by norm_num) (by positivity)
  have hs1 : sigma≤1 := min_le_left _ _
  have hse : sigma≤epsilonTarget/1000 := min_le_right _ _
  let n := depth Mcap sigma
  let L : ℝ := (n:ℝ)+Mcap+10*B+30
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hL : 0<L := by dsimp [L]; positivity
  let reserve : ℝ := min (sigma/100) (epsilonTarget/(1000*L))
  have hr : 0<reserve := lt_min (by positivity) (by positivity)
  have hrs : reserve≤sigma/100 := min_le_left _ _
  have hre : reserve≤epsilonTarget/(1000*L) := min_le_right _ _
  have hbudget : reserve*(1000*L)≤epsilonTarget := (le_div_iff₀ (by positivity)).mp hre
  have hnres : (n:ℝ)*reserve≤epsilonTarget/1000 := by
    have hx : (n:ℝ)*reserve≤L*reserve := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr.le
    nlinarith
  have hbRes : (10*B+20)*reserve≤epsilonTarget/1000 := by
    have hx : (10*B+20)*reserve≤L*reserve := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr.le
    nlinarith
  have hmRes : (Mcap+2)*reserve≤epsilonTarget/1000 := by
    have hx : (Mcap+2)*reserve≤L*reserve := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr.le
    nlinarith
  let mesh : ℝ := reserve/(kappa+1)
  have hm : 0<mesh := by dsimp [mesh]; positivity
  have hmr : mesh≤reserve := by
    dsimp [mesh]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hkm : kappa*mesh≤reserve := mesh_cost kappa reserve hk hr.le
  refine ⟨sigma,reserve,mesh,hs,hs1,hse,hr,hm,hmr,hkm,by linarith,
    depth_covers Mcap sigma hs,?_,?_,?_⟩
  · intro ec er d e d1 d2 t hec her hd he hd1 hd2 ht
    have hedge : edge ec er d e d1 d2 t kappa mesh≤10*reserve := by
      unfold edge
      linarith
    have hp := mul_le_mul_of_nonneg_left hedge hn
    change (n:ℝ)*edge ec er d e d1 d2 t kappa mesh≤epsilonTarget/16
    nlinarith
  · intro df e d t hdf he hd ht
    have htheta : 2*(5*B+1)*t≤2*(5*B+1)*reserve :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    unfold exceptional
    nlinarith
  · intro d other e A hd ho he0 he hA
    have hmul : e*A≤reserve*Mcap := (mul_le_mul_of_nonneg_left hA he0).trans
      (mul_le_mul_of_nonneg_right he hM)
    unfold diagonal
    nlinarith

end SevenEighths.CenteredMomentSuccessorPaidParameters

end

end OAI

end Source2031

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAmplifiedFourCoefficients.lean; sha256: 8fe44972dc64f7ba3edc5a3cc6ee91e9047a62449009fe742aa485da99c617ee -/
section Source2032
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedAllowance
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstMixedExceptionalLow CenteredMomentFirstMixedDiagonal
open CenteredMomentSuccessorPaidParameters
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

def reference (q V C Z allowance:ℝ):ℝ:=q*(V/C)^2*Z^allowance

def mainCores (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ):Fin 4→ℝ:=
  ![(V/C)*q*(V/C)*Z^(ell+deficit/6+paid)/reference q V C Z allowance,
    (V/C)*(V/C)^((1:ℝ)/3)*Kmain^((5:ℝ)/6)*Z^(-2*max r 0/3)/reference q V C Z allowance,
    (V/C)*Kmain*(V/C)^eps/reference q V C Z allowance,
    (V/C)*Kmain*Z^(-saving)/reference q V C Z allowance]

def errorCores (p:O)(k:ℕ)(q V C Z allowance Kerror deficit paid eps saving r:ℝ):Fin 4→ℝ:=
  ![(V/C)*localErrorCost p (k-1)*q*Z^(errorMoving p Z k)*
      (V/C/(normValue p)^k)*Z^(errorRemoval p Z k+deficit/6+paid)/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*(V/C/(normValue p)^k)^((1:ℝ)/3)*
      Kerror^((5:ℝ)/6)*Z^(-2*max r 0/3)/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*Kerror*(V/C/(normValue p)^k)^eps/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*Kerror*Z^(-saving)/reference q V C Z allowance]

def lossVector (sigma delta reserve paid eps Mcap saving:ℝ):Fin 4→ℝ:=
  ![paid,3*sigma/2+5*(delta+reserve)/6,
    2*sigma+delta+reserve+eps*Mcap,2*sigma+delta+reserve-saving]

def averagedCoefficients (P:Finset (Ideal O))(mainFactor:ℝ)(H main:Fin 4→ℝ)
    (error:elementPool P→Fin 3→Ray→Fin 4→ℝ):Fin 4→ℝ:=fun j=>
  (56/(P.card:ℝ))*(mainFactor*H j*main j+
    ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)

lemma actual_valuation_mass : (∑i:Fin 3,16*(errorIndex i+2:ℝ)^2)=1872 := by
  norm_num [Fin.sum_univ_succ,errorIndex]

theorem actual_error_average (P:Finset (Ideal O))(hne:P.Nonempty)
    (hp:∀Q∈P,Prime Q)(hbad:∀Q∈P,Q∉fixedBadPrimes)
    (f:elementPool P→Fin 3→Ray→ℝ)(E:ℝ)(_hE:0≤E)
    (hf:∀p i χ,f p i χ≤E):
    (1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
      16*(errorIndex i+2:ℝ)^2*∑χ:Ray,f p i χ)≤
        1872*(Fintype.card Ray:ℝ)*E := by
  have hn:(0:ℝ)<P.card:=by exact_mod_cast hne.card_pos
  have hc:Fintype.card (elementPool P)=P.card:=by
    rw [Fintype.card_coe,elementPool_card P hp hbad]
  have hh:(∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,f p i χ)≤
      ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,E:=by
    apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _=>hf p i χ)) (by positivity)
  apply (mul_le_mul_of_nonneg_left hh (by positivity:0≤1/(P.card:ℝ))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←Finset.sum_mul,actual_valuation_mass,hc]
  field_simp

lemma main_paid_core (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ)
    (hq:0<q)(hV:0<V)(hC:0<C)(hZ:1<Z)(hB:0≤allowance)(hdef:0≤deficit):
    Z^(-ell)*mainCores q V C Z allowance Kmain ell deficit paid eps saving r 0≤
      Z^(deficit+paid) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hx:0<V/C:=div_pos hV hC
  have he:mainCores q V C Z allowance Kmain ell deficit paid eps saving r 0=
      Z^(ell+deficit/6+paid-allowance):=by
    dsimp [mainCores,reference]
    rw [Real.rpow_sub hz]
    field_simp
  rw [he,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

lemma error_paid_core (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)
    (q V C Z allowance Kerror deficit paid eps saving r:ℝ)
    (hq:0<q)(hV:0<V)(hC:0<C)(hZ:1<Z)(hB:0≤allowance)(hdef:0≤deficit):
    errorCores p k q V C Z allowance Kerror deficit paid eps saving r 0≤Z^(deficit+paid) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hx:0<V/C:=div_pos hV hC
  have hpv:=normValue_pos p hp
  have hw:=actual_error_weight p hp Z hZ k hk
  have hs:localErrorCost p (k-1)*Z^(errorMoving p Z k)≤1:=by
    have hh:=mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hz.le (errorMoving p Z k))
    rw [←Real.rpow_add hz,neg_add_cancel,Real.rpow_zero] at hh
    exact hh
  have he:errorCores p k q V C Z allowance Kerror deficit paid eps saving r 0=
      (localErrorCost p (k-1)*Z^(errorMoving p Z k))*Z^(deficit/6+paid-allowance):=by
    dsimp [errorCores,reference]
    rw [Real.rpow_sub hz,show errorRemoval p Z k+deficit/6+paid=
      errorRemoval p Z k+(deficit/6+paid) by ring,Real.rpow_add hz,errorRemoval_power p hp Z hZ k]
    field_simp
  rw [he]
  calc
    _≤1*Z^(deficit/6+paid-allowance):=mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hz.le _)
    _≤Z^(deficit+paid):=by rw [one_mul];apply Real.rpow_le_rpow_of_exponent_le hZ.le;linarith

theorem actual_main_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving r Mdecl Mcap:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0≤sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    ∀j:Fin 4,Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kmain (sigma/3) (Mdecl-M0) paid eps saving r j≤
      Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hr:0<mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  have havg:Z^(-sigma/3)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hZ.le (by linarith)
  have hA:Real.logb Z V≤Mdecl:=by linarith
  have hAcap:Real.logb Z V≤Mcap:=hA.trans hcap
  intro j
  fin_cases j
  · have hh:=main_paid_core (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector,neg_div] using hh
  · have hh:=actual_main_exceptional_reference η τ C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve r hZ hmod hK hV
    have ht:Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 1≤
        Z^(Real.logb Z V-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+
          4*sigma/3+5*(delta+reserve)/6):=by
      convert hh using 1 ; dsimp [mainCores,reference] ; ring
    apply ht.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith
  · have hh:=actual_main_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve eps hK hV hZ heps hmod
    have hc0:0≤mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 2:=by
      dsimp [mainCores,reference];positivity
    apply (mul_le_mul_of_nonneg_right havg hc0).trans
    rw [one_mul]
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    have he:=mul_le_mul_of_nonneg_left hAcap heps
    linarith
  · have hh:=actual_main_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve 0 hK hV hZ (by norm_num) hmod
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    have hcore:mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          2*sigma+delta+reserve)*Z^(-saving):=by
      convert ht using 1 ; dsimp [mainCores,reference] ; ring
    have ht':=mul_le_mul_of_nonneg_left hcore (Real.rpow_nonneg hz.le (-sigma/3))
    apply ht'.trans
    calc
      _≤1*(Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          2*sigma+delta+reserve)*Z^(-saving)):=mul_le_mul_of_nonneg_right havg (by positivity)
      _≤_:=by
        rw [one_mul,←Real.rpow_add hz]
        apply Real.rpow_le_rpow_of_exponent_le hZ.le
        dsimp [lossVector]
        linarith

theorem actual_error_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving r Mdecl Mcap:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0≤sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))(hbad:fixedBadPrimes⊆Sbad)
    (p:O)(hp:p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k;
    ∀j:Fin 4,errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kerror (Mdecl-M0) paid eps saving r j≤
      Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hpdata:=elementPool_data _ (fun Q hQ=>(primePool_data M H Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad _ _ _ Q hQ).2) p hp
  have hp0:p≠0:=hpdata.1.ne_zero
  have hr:0<errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by unfold errorCommonRadius;positivity
  have hA:Real.logb Z V≤Mdecl:=by linarith
  have hAcap:Real.logb Z V≤Mcap:=hA.trans hcap
  intro j
  fin_cases j
  · have hh:=error_paid_core p hp0 k hk (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
      (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector] using hh
  · have hh:=actual_error_exceptional_reference η τ C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve r hZ hmod M H Sbad hbad p hp k hk hK hV
    have ht:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 1≤
        Z^(Real.logb Z V-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+
          3*sigma/2+5*(delta+reserve)/6):=by
      convert hh using 1 ; dsimp [errorCores,reference] ; ring
    apply ht.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith
  · have hh:=actual_error_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve eps hK hV hZ heps hmod p hp0 k hk
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    have he:=mul_le_mul_of_nonneg_left hAcap heps
    linarith
  · have hh:=actual_error_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve 0 hK hV hZ (by norm_num) hmod p hp0 k hk
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    have hcore:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          sigma+delta+reserve)*Z^(-saving):=by
      convert ht using 1 ; dsimp [errorCores,reference] ; ring
    apply hcore.trans
    rw [←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith

def sourceCoefficients (P:Finset (Ideal O))(mainFactor:ℝ)(amain:Fin 4→ℝ)
    (aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ):Fin 4→ℝ:=fun j=>
  (56/(P.card:ℝ))*(mainFactor*amain j+
    ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*localErrorCost p (errorIndex i)*
      ∑χ:Ray,aerror p i χ j*((normValue p)^(errorIndex i+1))^(-alpha j))

lemma shortened_power (V q:ℝ)(k:ℕ)(alpha:ℝ)(hV:0≤V)(hq:0≤q):
    (V/q^k)^alpha=V^alpha*(q^k)^(-alpha):=by
  rw [Real.div_rpow hV (pow_nonneg hq k),Real.rpow_neg (pow_nonneg hq k),div_eq_mul_inv]

theorem source_coefficients_identity (P:Finset (Ideal O))(mainFactor V:ℝ)(hV:0≤V)
    (amain:Fin 4→ℝ)(aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ):
    (∑j:Fin 4,sourceCoefficients P mainFactor amain aerror alpha j*V^(alpha j))=
    (56/(P.card:ℝ))*(mainFactor*(∑j:Fin 4,amain j*V^(alpha j))+
      ∑p:elementPool P,∑i:Fin 3,(16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
        (errorIndex i+2:ℝ)*∑χ:Ray,∑j:Fin 4,aerror p i χ j*
          (V/(normValue p)^(errorIndex i+1))^(alpha j)) := by
  have hnorm:∀p:O,0≤normValue p:=by intro p;unfold normValue;positivity
  let f:=fun (j:Fin 4) (p:elementPool P) (i:Fin 3) (χ:Ray)=>
    16*(errorIndex i+2:ℝ)^2*localErrorCost p (errorIndex i)*
      (aerror p i χ j*((normValue p)^(errorIndex i+1))^(-alpha j))*V^(alpha j)
  have hswap:(∑j:Fin 4,∑p:elementPool P,∑i:Fin 3,∑χ:Ray,f j p i χ)=
      ∑p:elementPool P,∑i:Fin 3,∑χ:Ray,∑j:Fin 4,f j p i χ:=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  calc
    _=(56/(P.card:ℝ))*∑j:Fin 4,
        (mainFactor*amain j*V^(alpha j)+
          (∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*localErrorCost p (errorIndex i)*
            ∑χ:Ray,aerror p i χ j*((normValue p)^(errorIndex i+1))^(-alpha j))*V^(alpha j)):=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      unfold sourceCoefficients
      ring
    _=(56/(P.card:ℝ))*(mainFactor*(∑j:Fin 4,amain j*V^(alpha j))+
        ∑j:Fin 4,∑p:elementPool P,∑i:Fin 3,∑χ:Ray,f j p i χ):=by
      congr 1
      rw [Finset.sum_add_distrib]
      congr 1
      · simp only [Finset.mul_sum,mul_assoc]
      · simp only [f,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    _=(56/(P.card:ℝ))*(mainFactor*(∑j:Fin 4,amain j*V^(alpha j))+
        ∑p:elementPool P,∑i:Fin 3,∑χ:Ray,∑j:Fin 4,f j p i χ):=by rw [hswap]
    _=_:=by
      congr 2
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [shortened_power V (normValue p) _ _ hV (hnorm _)]
      dsimp [f]
      ring

theorem averaged_coefficients_bound (P:Finset (Ideal O))(hne:P.Nonempty)
    (hp:∀Q∈P,Prime Q)(hbad:∀Q∈P,Q∉fixedBadPrimes)
    (Z ell primeLoss mainFactor:ℝ)(hZ:1<Z)(hloss:0≤primeLoss)
    (hfactor:0≤mainFactor)(hcard:Z^(ell-primeLoss)≤(P.card:ℝ))
    (H main loss:Fin 4→ℝ)(error:elementPool P→Fin 3→Ray→Fin 4→ℝ)
    (hH:∀j,0≤H j)(hm:∀j,Z^(-ell)*main j≤Z^(loss j))
    (he:∀p i χ j,error p i χ j≤Z^(loss j)):
    ∀j,averagedCoefficients P mainFactor H main error j≤
      56*(mainFactor+1872*(Fintype.card Ray:ℝ))*H j*Z^(loss j+primeLoss) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:(0:ℝ)<P.card:=by exact_mod_cast hne.card_pos
  have hinv:(1/(P.card:ℝ))≤Z^(-ell+primeLoss):=by
    have hh:=one_div_le_one_div_of_le (Real.rpow_pos_of_pos hz _) hcard
    simpa [one_div,←Real.rpow_neg hz.le,neg_sub,sub_eq_add_neg,add_comm] using hh
  intro j
  have hm':main j≤Z^(ell+loss j):=by
    have hh:=mul_le_mul_of_nonneg_left (hm j) (Real.rpow_nonneg hz.le ell)
    rw [←mul_assoc,←Real.rpow_add hz,add_neg_cancel,Real.rpow_zero,one_mul,
      ←Real.rpow_add hz] at hh
    exact hh
  have hmain:(1/(P.card:ℝ))*main j≤Z^(loss j+primeLoss):=by
    calc
      _≤(1/(P.card:ℝ))*Z^(ell+loss j):=mul_le_mul_of_nonneg_left hm' (by positivity)
      _≤Z^(-ell+primeLoss)*Z^(ell+loss j):=mul_le_mul_of_nonneg_right hinv (by positivity)
      _=Z^(loss j+primeLoss):=by rw [←Real.rpow_add hz];congr 1;ring
  have herr:=actual_error_average P hne hp hbad (fun p i χ=>H j*error p i χ j)
    (H j*Z^(loss j)) (mul_nonneg (hH j) (Real.rpow_nonneg hz.le _)) (fun p i χ=>mul_le_mul_of_nonneg_left (he p i χ j) (hH j))
  have hl:Z^(loss j)≤Z^(loss j+primeLoss):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have herr':(1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
      16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)≤
      1872*(Fintype.card Ray:ℝ)*(H j*Z^(loss j+primeLoss)):=
    herr.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl (hH j)) (by positivity))
  calc
    _=56*(mainFactor*H j*((1/(P.card:ℝ))*main j)+
      (1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
        16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)):=by
      unfold averagedCoefficients;ring
    _≤56*(mainFactor*H j*Z^(loss j+primeLoss)+
      1872*(Fintype.card Ray:ℝ)*(H j*Z^(loss j+primeLoss))):=by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hmain (mul_nonneg hfactor (hH j))) herr') (by norm_num)
    _=_:=by ring

theorem actual_low_four_coefficients
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)(rmain:ℝ)
    (rerror:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3)))→Fin 3→Ray→ℝ):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let main:=mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-M0) paid eps saving rmain;
    let error:=fun (p:elementPool P) (i:Fin 3) (χ:Ray)=>
      errorCores p (errorIndex i+1) (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
        (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ))
          sigma delta reserve p (errorIndex i+1)) (Mdecl-M0) paid eps saving (rerror p i χ);
    ∀j,averagedCoefficients P ((Mamp+2*sigma)/(sigma/6)) H main error j≤
      56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
        Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hne:(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).Nonempty:=by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.rpow_pos_of_pos hz (sigma/3-primeLoss)).trans_le hcard
  have hmain:=actual_main_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
    rmain Mdecl Mcap hK hV hZ hs.le heps hM hcap hactual hlow hmod
  have herror:=fun (p:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))))
      (i:Fin 3) (χ:Ray)=>
    actual_error_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
      (rerror p i χ) Mdecl Mcap hK hV hZ hs.le heps hM hcap hactual hlow hmod
      M Hray Sbad hbad p p.property (errorIndex i+1)
      (by fin_cases i <;> norm_num [errorIndex])
  exact averaged_coefficients_bound _ hne
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).2)
    Z (sigma/3) primeLoss ((Mamp+2*sigma)/(sigma/6)) hZ hloss
    (div_nonneg (by linarith) (by positivity)) hcard H _ _ _ hH
    (by simpa only [neg_div] using hmain) herror

theorem source_normalized_identity (P:Finset (Ideal O))(mainFactor b V C q Z allowance eps:ℝ)
    (N:ℕ)(alpha:Fin 4→ℝ)(amain:Fin 4→ℝ)
    (aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)
    (hV:0<V)(hC:0<C)(hq:0<q)(hZ:0<Z):
    ∀j,CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
        (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C^eps*(b^N)^(alpha j)*averagedCoefficients P mainFactor (fun _=>1)
        (fun j=>(V/C)*amain j*(V/C)^(alpha j)/reference q V C Z allowance)
        (fun p i χ j=>(V/C)*localErrorCost p (errorIndex i)*aerror p i χ j*
          (V/C/(normValue p)^(errorIndex i+1))^(alpha j)/reference q V C Z allowance) j := by
  have hx:0<V/C:=div_pos hV hC
  have hnorm:∀p:O,0≤normValue p:=by intro p;unfold normValue;positivity
  intro j
  have hden:reference q V C Z allowance≠0:=by unfold reference;positivity
  have he:CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
      (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C^eps*(b^N)^(alpha j)*((V/C)*sourceCoefficients P mainFactor amain aerror alpha j*
        (V/C)^(alpha j)/reference q V C Z allowance):=by
    unfold CenteredMomentFirstCommonReferencePower.normalizedPower reference
    rw [Real.rpow_sub hx,Real.rpow_one,Real.rpow_neg hZ.le]
    field_simp
  rw [he]
  congr 1
  unfold sourceCoefficients averagedCoefficients
  simp only [one_mul]
  simp only [shortened_power (V/C) _ _ _ hx.le (hnorm _)]
  simp only [div_eq_mul_inv,mul_add,add_mul,Finset.mul_sum,Finset.sum_mul]
  ring_nf

theorem eventually_prime_average_gates
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
    (Sbad:Finset (Ideal O))(sigma primeLoss:ℝ)(hs:0<sigma)(hloss:0<primeLoss):
    ∀ᶠ Z:ℝ in Filter.atTop,1<Z ∧
      (primePool M H Sbad (1/2) 1 (Z^(sigma/3))).Nonempty ∧
      Z^(sigma/3-primeLoss)≤(primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card := by
  filter_upwards [eventually_actual_pool_card M H hH Sbad (sigma/3) primeLoss (by positivity) hloss,
    Filter.eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_,hc⟩
  apply Finset.card_pos.mp
  exact_mod_cast (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/3-primeLoss)).trans_le hc

lemma source_coefficients_nonneg (P:Finset (Ideal O))(mainFactor:ℝ)(hmain:0≤mainFactor)
    (amain:Fin 4→ℝ)(aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ)
    (ha:∀j,0≤amain j)(he:∀p i χ j,0≤aerror p i χ j):
    ∀j,0≤sourceCoefficients P mainFactor amain aerror alpha j := by
  intro j
  have hc:∀p:O,∀n:ℕ,0≤localErrorCost p n:=by
    intro p n
    have hn:0≤normValue p:=by unfold normValue;positivity
    unfold localErrorCost
    split <;> positivity
  unfold sourceCoefficients
  apply mul_nonneg (by positivity)
  apply add_nonneg (mul_nonneg hmain (ha j))
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (mul_nonneg (by positivity) (hc p (errorIndex i)))
  apply Finset.sum_nonneg
  intro χ _
  exact mul_nonneg (he p i χ j) (Real.rpow_nonneg (by unfold normValue;positivity) _)

def mainPowers (q Z Kmain ell deficit paid saving r:ℝ):Fin 4→ℝ:=
  ![q*Z^(ell+deficit/6+paid),Kmain^((5:ℝ)/6)*Z^(-2*max r 0/3),Kmain,Kmain*Z^(-saving)]

def errorPowers (p:O)(k:ℕ)(q Z Kerror deficit paid saving r:ℝ):Fin 4→ℝ:=
  ![q*Z^(errorMoving p Z k)*Z^(errorRemoval p Z k+deficit/6+paid),
    Kerror^((5:ℝ)/6)*Z^(-2*max r 0/3),Kerror,Kerror*Z^(-saving)]

lemma main_core_power (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ):
    ∀j,mainCores q V C Z allowance Kmain ell deficit paid eps saving r j=
      (V/C)*mainPowers q Z Kmain ell deficit paid saving r j*
        (V/C)^(CenteredMomentSecondChildPowerBudget.powers eps j)/reference q V C Z allowance := by
  intro j
  fin_cases j <;> simp [mainCores,mainPowers,CenteredMomentSecondChildPowerBudget.powers] <;> ring

lemma error_core_power (p:O)(k:ℕ)(q V C Z allowance Kerror deficit paid eps saving r:ℝ):
    ∀j,errorCores p k q V C Z allowance Kerror deficit paid eps saving r j=
      (V/C)*localErrorCost p (k-1)*errorPowers p k q Z Kerror deficit paid saving r j*
        (V/C/(normValue p)^k)^(CenteredMomentSecondChildPowerBudget.powers eps j)/reference q V C Z allowance := by
  intro j
  fin_cases j <;> simp [errorCores,errorPowers,CenteredMomentSecondChildPowerBudget.powers] <;> ring

theorem actual_power_reference_identity (P:Finset (Ideal O))(mainFactor b V C q Z allowance eps:ℝ)
    (N:ℕ)(H:Fin 4→ℝ)(Kmain ell deficit paid saving rmain:ℝ)
    (Kerror rerror:elementPool P→Fin 3→Ray→ℝ)
    (hV:0<V)(hC:0<C)(hq:0<q)(hZ:0<Z):
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers q Z Kmain ell deficit paid saving rmain j;
    let aerror:=fun (p:elementPool P) (i:Fin 3) (χ:Ray) (j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) q Z (Kerror p i χ) deficit paid saving (rerror p i χ) j;
    ∀j,CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
      (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C^eps*(b^N)^(alpha j)*averagedCoefficients P mainFactor H
        (mainCores q V C Z allowance Kmain ell deficit paid eps saving rmain)
        (fun p i χ=>errorCores p (errorIndex i+1) q V C Z allowance (Kerror p i χ)
          deficit paid eps saving (rerror p i χ)) j := by
  dsimp only
  intro j
  rw [source_normalized_identity P mainFactor b V C q Z allowance eps N _ _ _ hV hC hq hZ j]
  congr 1
  unfold averagedCoefficients
  simp only [one_mul]
  rw [main_core_power]
  congr 2
  · ring
  · apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro χ _
    rw [error_core_power]
    simp only [Nat.add_sub_cancel]
    ring

end SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

end

end OAI

end Source2032

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstGaussianCoefficients.lean; sha256: b4b71609031c3ad461dd728122142d3476091f198ffe1ba061a813d38eec80c8 -/
section Source2033
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondChildPowerBudget CenteredMomentSecondSourceSeededPowerDescent
open CenteredMomentSecondSourcePowerDescent CenteredMomentSecondWindowBudget
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentSourceInputTailUniform
local notation "O"=>HeckeFamily.O

def fixedFactors (Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed:ℝ)
    (J:ℕ)(Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ)):Fin 4→ℝ:=
  ![Cm*Z^(2*delta+epsilon)*cost*Ebase*heightEnvelope t^(J+J)*profileMoment J*profileMoment J,
    Ce*Z^(2*epsilon+2*delta+2*(5*B+1)*theta)*loFloor^(-2/3:ℝ),
    Cd*‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖,
    Ct*Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W/seed]

lemma coefficients_mul {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (p:Profiles a b)(J:ℕ)(Q:Ideal O)(K t epsilon seed:ℝ)(f g:Fin 4→ℝ):
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed (fun j=>f j*g j) j=
      CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed f j*g j:=by
  intro j
  fin_cases j <;> simp [CenteredMomentSecondChildPowerBudget.coefficients] <;> ring

lemma coefficients_mono {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (p:Profiles a b)(J:ℕ)(Q:Ideal O)(K t epsilon seed:ℝ)(f g:Fin 4→ℝ)
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(hK:0≤K)(hseed:0≤seed)
    (hfg:∀j,f j≤g j):
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed f j≤
      CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed g j:=by
  have h0:=hfg 0
  have h1:=hfg 1
  have h2:=hfg 2
  have h3:=hfg 3
  intro j
  fin_cases j <;> simp only [CenteredMomentSecondChildPowerBudget.coefficients, Fin.isValue, Matrix.cons_val,  Fin.reduceFinMk]
  · gcongr
  · have he:0≤CenteredMomentFirstChildProfileControl.exceptionalConstant N upper J Q K:=by
      unfold CenteredMomentFirstChildProfileControl.exceptionalConstant
      positivity
    gcongr
  · gcongr
  · gcongr

theorem seeded_factors_main (Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
    ell deficit paid r loProduct wlo loFloor seed:ℝ)(J:ℕ)
    (Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (_hCm:0≤Cm)(hCe:0≤Ce)(hZ:0<Z)(hE:0≤Ebase)(hradius:0≤radius)
    (hlo:0<loFloor)(hloProduct:loFloor≤loProduct*wlo*wlo):
    let E:=Ebase*Z^(ell+deficit/6+paid);
    ∀j,seededFactors Cm Ce Cd Ct Z epsilon delta theta B saving radius t (cost*q)
        E E r loProduct wlo seed J J Sf W j≤
      fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W j*
        mainPowers q Z radius ell deficit paid saving r j:=by
  dsimp only
  have hEp:0≤Ebase*Z^(ell+deficit/6+paid):=mul_nonneg hE (Real.rpow_nonneg hZ.le _)
  have hsqrt:Real.sqrt ((Ebase*Z^(ell+deficit/6+paid))*(Ebase*Z^(ell+deficit/6+paid)))=
      Ebase*Z^(ell+deficit/6+paid):=by rw [←pow_two,Real.sqrt_sq hEp]
  have hneg:(loProduct*wlo*wlo)^(-2/3:ℝ)≤loFloor^(-2/3:ℝ):=
    Real.rpow_le_rpow_of_nonpos hlo hloProduct (by norm_num)
  intro j
  fin_cases j
  · simp only [seededFactors,physicalFactors,fixedFactors,mainPowers,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk,hsqrt]
    exact le_of_eq (by ring)
  · simp only [seededFactors,physicalFactors,fixedFactors,mainPowers,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    rw [Real.rpow_sub hZ]
    have hbase:0≤Ce*Z^(2*epsilon+2*delta+2*(5*B+1)*theta)/Z^(2*max r 0/3)*radius^(5/6:ℝ):=by positivity
    have hh:=mul_le_mul_of_nonneg_left hneg hbase
    have hpow:Z^(-2*max r 0/3)=(Z^(2*max r 0/3))⁻¹:=by
      rw [show -2*max r 0/3=-(2*max r 0/3) by ring,Real.rpow_neg hZ.le]
    convert hh using 1 <;> (try rw [hpow]) <;> ring
  · simp [seededFactors,physicalFactors,fixedFactors,mainPowers,mul_comm,mul_left_comm,mul_assoc]
  · simp only [seededFactors,physicalFactors,fixedFactors,mainPowers,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    exact le_of_eq (by ring)

lemma fixedFactors_nonneg (Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed:ℝ)
    (J:ℕ)(Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hCm:0≤Cm)(hCe:0≤Ce)(hCd:0≤Cd)(hCt:0≤Ct)(hZ:0≤Z)
    (hcost:0≤cost)(hE:0≤Ebase)(hlo:0≤loFloor)(hseed:0≤seed):
    ∀j,0≤fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W j:=by
  have hh:0≤heightEnvelope t:=(heightEnvelope_pos t).le
  have hp:=profileMoment_nonneg J
  have hc:0≤Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=apply_nonneg _ _
  intro j
  fin_cases j <;> simp only [fixedFactors,Matrix.cons_val,Fin.reduceFinMk] <;> positivity

theorem main_coefficients {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (p:Profiles a b)(Jprofile:ℕ)(Q:Ideal O)(Kfix:ℝ)
    (Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
      ell deficit paid r loProduct wlo loFloor seed:ℝ)(J:ℕ)
    (Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(hK:0≤Kfix)(hseed:0≤seed)
    (hCm:0≤Cm)(hCe:0≤Ce)(hZ:0<Z)(hE:0≤Ebase)(hradius:0≤radius)
    (hlo:0<loFloor)(hloProduct:loFloor≤loProduct*wlo*wlo):
    let E:=Ebase*Z^(ell+deficit/6+paid);
    let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
      (fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W);
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
      (seededFactors Cm Ce Cd Ct Z epsilon delta theta B saving radius t (cost*q)
        E E r loProduct wlo seed J J Sf W) j≤
      H j*mainPowers q Z radius ell deficit paid saving r j:=by
  dsimp only
  have hh:=coefficients_mono N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed _ _
    hu hb1 hb2 hK hseed
    (seeded_factors_main Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
      ell deficit paid r loProduct wlo loFloor seed J Sf W hCm hCe hZ hE hradius hlo hloProduct)
  intro j
  exact (hh j).trans_eq (coefficients_mul N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed _ _ j)

theorem error_coefficients {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (profiles:Profiles a b)(Jprofile:ℕ)(Q:Ideal O)(Kfix:ℝ)(prime:O)(k:ℕ)
    (Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
      deficit paid r loProduct wlo loFloor seed:ℝ)(J:ℕ)
    (Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(hK:0≤Kfix)(hseed:0≤seed)
    (hCm:0≤Cm)(hCe:0≤Ce)(hZ:0<Z)(hE:0≤Ebase)(hradius:0≤radius)
    (hlo:0<loFloor)(hloProduct:loFloor≤loProduct*wlo*wlo):
    let E:=Ebase*Z^(CenteredMomentFirstAmplificationChoice.errorRemoval prime Z k+deficit/6+paid);
    let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp profiles Jprofile Q Kfix t epsilon seed
      (fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W);
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp profiles Jprofile Q Kfix t epsilon seed
      (seededFactors Cm Ce Cd Ct Z epsilon delta theta B saving radius t
        (cost*q*Z^(CenteredMomentFirstAmplificationChoice.errorMoving prime Z k))
        E E r loProduct wlo seed J J Sf W) j≤
      H j*errorPowers prime k q Z radius deficit paid saving r j:=by
  dsimp only
  have hh:=main_coefficients N upper b1 b2 A Sp profiles Jprofile Q Kfix
    Cm Ce Cd Ct Z epsilon delta theta B saving radius t
    (q*Z^(CenteredMomentFirstAmplificationChoice.errorMoving prime Z k)) cost Ebase
    (CenteredMomentFirstAmplificationChoice.errorRemoval prime Z k) deficit paid r
    loProduct wlo loFloor seed J Sf W hu hb1 hb2 hK hseed hCm hCe hZ hE hradius hlo hloProduct
  intro j
  have hid:mainPowers (q*Z^(CenteredMomentFirstAmplificationChoice.errorMoving prime Z k)) Z radius
      (CenteredMomentFirstAmplificationChoice.errorRemoval prime Z k) deficit paid saving r j=
      errorPowers prime k q Z radius deficit paid saving r j:=by
    fin_cases j <;> rfl
  have hhj:=hh j
  rw [hid] at hhj
  simpa only [mul_assoc] using hhj

end SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

end

end OAI

end Source2033

/- Original source: OAI/NumberTheory/DirichletL/Energy/NaturalInputMatches.lean; sha256: cfd5e4d5686458f461149cae45783c954f0f9e1b96206a7f9d3db1ce1d87726c -/
section Source2034
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyNaturalInputMatches
open HeckeFamily HeckePrimeAnnular CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
local notation "O" => HeckeFamily.O

def profile (W : ℝ → ℂ) (σ freq y : ℝ) : ℂ :=
  W y * (y : ℂ)^(-HeckeDyadic.shift σ freq)

lemma profile_support (W : ℝ → ℂ) (a b : ℝ)
    (hWs : Function.support W ⊆ Set.Icc a b) (σ freq : ℝ) :
    Function.support (profile W σ freq) ⊆ Set.Icc a b := by
  intro y hy
  apply hWs
  intro hz
  exact hy (by simp only [profile, hz, zero_mul])

lemma profile_zero (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (σ freq : ℝ) :
    profile W σ freq 0 = 0 := by
  by_contra hn
  exact (not_le_of_gt ha) ((profile_support W a b hWs σ freq hn).1)

lemma profile_norm (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (σ freq y : ℝ) :
    ‖profile W σ freq y‖ = ‖W y‖ * y^(-σ) := by
  by_cases hz : W y = 0
  · simp only [profile, hz, zero_mul, norm_zero]
  · have hy : 0 < y := ha.trans_le (hWs hz).1
    simp only [profile, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      Complex.neg_re, HeckeDyadic.shift_re]

theorem exists_profile_bound (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ σ ∈ Set.Icc lo hi, ∀ freq y : ℝ,
      ‖profile W σ freq y‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro σ hσ freq y
  by_cases hz : W y = 0
  · simpa only [profile, hz, zero_mul, norm_zero] using
      (zero_le_one.trans (le_max_left 1 C))
  · rw [profile_norm W a b ha hWs]
    exact (hb σ hσ y (hWs hz)).trans (le_max_right _ _)

def profileBound (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) : ℝ :=
  (exists_profile_bound W hW a b lo hi ha hWs).choose

lemma profileBound_ge_one (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) :
    1 ≤ profileBound W hW a b lo hi ha hWs :=
  (exists_profile_bound W hW a b lo hi ha hWs).choose_spec.1

lemma norm_profile_le (W : ℝ → ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b)
    (σ : ℝ) (hσ : σ ∈ Set.Icc lo hi) (freq y : ℝ) :
    ‖profile W σ freq y‖ ≤ profileBound W hW a b lo hi ha hWs :=
  (exists_profile_bound W hW a b lo hi ha hWs).choose_spec.2 σ hσ freq y

section Input
variable {ι : Type*} [Fintype ι]
variable (Q : Ideal O) [NeZero Q]
local instance : Finite (O ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne Q)
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters Q H)
variable (W : ℝ → ℂ) (hW : Continuous W)
variable (aslot bslot lo hi : ℝ) (haslot : 0 < aslot)
variable (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z Bmask bΦ a b : ℝ}
variable (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0 < a)
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hsame : Y₁ * Y₂ = X₁ * X₂)

def input : Input ι :=
  CenteredMomentEnergyOriginalSource.naturalInput state p ha
    (fun i => primePool Q H bslot (Z^(w i)))
    (fun _ _ hI => (Finset.mem_filter.mp hI).2.1)
    (fun i => relativeCharacter Q H hH η₀ (θ i))
    (fun i => profile W (σ i) (freq i)) (fun i => Z^(w i))
    (fun _ => profileBound W hW aslot bslot lo hi haslot hWs)
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans_le state.base_ge_one) _)
    (fun _ => profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
    aslot bslot haslot (fun i => profile_support W aslot bslot hWs (σ i) (freq i))
    (fun i => norm_profile_le W hW aslot bslot lo hi haslot hWs (σ i) (hσ i) (freq i))
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame

local notation "inp" => input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame

theorem input_matches :
    CenteredMomentAllocatedRayDictionary.Matches Q H hH inp η₀ θ w σ freq W bslot Z := by
  constructor <;> intros <;> rfl

lemma lower_eq : (inp).lower = aslot := rfl
lemma upper_eq : (inp).upper = bslot := rfl
lemma slot_control_eq (i : ι) :
    (inp).M i = profileBound W hW aslot bslot lo hi haslot hWs := rfl
lemma character_eq : (inp).η = state.character := rfl
lemma mask_eq : (inp).m = state.mask := rfl
lemma height_eq : (inp).t = t := rfl
lemma first_rectangle_eq : (inp).X₁ = X₁ ∧ (inp).X₂ = X₂ := ⟨rfl, rfl⟩
lemma second_rectangle_eq : (inp).Y₁ = Y₁ ∧ (inp).Y₂ = Y₂ := ⟨rfl, rfl⟩

theorem coefficient_eq (i : ι) (I : Ideal O) :
    (inp).toData.coefficient i I =
      idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I := rfl

theorem positive_row_eq (z : O) :
    positiveSlotRow (inp).η state.mask 1 z (inp).W₁ (inp).W₂ (inp).slots
      (inp).toData.coefficient (inp).P (inp).t (inp).X₁ (inp).X₂ =
    positiveSlotRow state.character state.mask 1 z (p.profile 0) (p.profile 1)
      (fun i => primePool Q H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) t X₁ X₂ := rfl

theorem energy_eq :
    energy (inp).η state.mask 1 (inp).t (inp).W₁ (inp).W₂ (inp).slots
      (inp).toData.coefficient (inp).P (inp).X₁ (inp).X₂
      state.radial.keep state.radial.profile state.radial.scale =
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool Q H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) X₁ X₂
      state.radial.keep state.radial.profile state.radial.scale := rfl

theorem reference_energy_eq :
    energy (inp).η state.mask 1 (inp).t (inp).W₁ (inp).W₂ (inp).slots
      (inp).toData.coefficient (inp).P (inp).Y₁ (inp).Y₂
      state.radial.keep state.radial.profile state.radial.scale =
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool Q H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) Y₁ Y₂
      state.radial.keep state.radial.profile state.radial.scale := rfl

end Input
end SevenEighths.CenteredMomentEnergyNaturalInputMatches

end

end OAI

end Source2034

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroComparison.lean; sha256: ec3c7562c4af189e67a674ee496677c8c1acd4518ec658f64995186e29e1a997 -/
section Source2035
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroComparison
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource
open CenteredMomentRadialEligibleEnergy CenteredMomentInductionEnergy
open CenteredMomentRetainedProfile CenteredMomentRetainedEnergy
open CenteredMomentHeckeExpansion CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentSourceRow
open CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceProfileMass CenteredMomentHeckeHeight CenteredMomentSourceMass
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

def smallScale (b:ℝ):ℝ:=1/(2*max 1 b)

lemma smallScale_pos (b:ℝ):0<smallScale b:=by unfold smallScale;positivity

lemma smallScale_le_one (b:ℝ):smallScale b≤1:=by
  unfold smallScale
  apply (div_le_iff₀ (by positivity:0<(2:ℝ)*max 1 b)).mpr
  linarith [le_max_left (1:ℝ) b]

lemma smallScale_strict (b:ℝ):smallScale b*b<1:=by
  have hm:0<max 1 b:=zero_lt_one.trans_le (le_max_left _ _)
  unfold smallScale
  have hb:=le_max_right (1:ℝ) b
  rw [div_mul_eq_mul_div,one_mul]
  exact (div_lt_iff₀ (mul_pos (by norm_num) hm)).mpr (by linarith)

def zeroData (s:Input ι):CenteredMomentEligibleEnergy.Data ι := { s.toData with
  Y₁ := smallScale s.b₁
  Y₂ := s.X₁*s.X₂/smallScale s.b₁
  Y₁_pos := smallScale_pos _
  Y₂_pos := div_pos (mul_pos s.X₁_pos s.X₂_pos) (smallScale_pos _)
  same_product := by field_simp [ne_of_gt (smallScale_pos s.b₁)] }

def zeroInput (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0):Input ι :=
  completeInput (zeroData s) hz₁ hz₂ s.ν_bound s.W_bound s.lower s.upper
    s.lower_pos s.lower_le s.upper_ge

omit [DecidableEq ι] in
@[simp] lemma zeroInput_volume (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0):
    volume (zeroInput s hz₁ hz₂)=volume s:=rfl

omit [DecidableEq ι] in
lemma comparison_row_zero (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (R:Ideal O)(z:O):
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂=0:=by
  unfold positiveSlotRow
  change _*(rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t (smallScale s.b₁)*_*_)=0
  rw [strict_subunit_rowTwistedSum_zero s.η (fixedBadMask*idealGenerator R) 1 z
    s.W₁ s.b₁ s.t (smallScale s.b₁) (smallScale_pos _) s.support₁ (smallScale_strict _)]
  simp only [zero_mul,mul_zero]

omit [DecidableEq ι] in
lemma comparison_energy_zero (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (R:Ideal O)(r:Radial):
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
      r.keep r.profile r.scale=0:=by
  unfold CenteredMomentInductionEnergy.energy
  simp only [comparison_row_zero s hz₁ hz₂ R, norm_zero, zero_pow (by decide : (2:ℕ)≠0),
    zero_mul, ite_self, tsum_zero]

theorem actual_zero_comparison_entry (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (R:Ideal O)(r:Radial):
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale≤
    2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset (zeroInput s hz₁ hz₂).pools))
      (coefficient (zeroInput s hz₁ hz₂) R 1) r.profile r.scale‖/volume s:=by
  have hh:=positive_energy_comparison (zeroInput s hz₁ hz₂) R r
  change _≤_+2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots
    s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
    r.keep r.profile r.scale at hh
  rw [comparison_energy_zero s hz₁ hz₂ R r,mul_zero,add_zero] at hh
  exact hh

omit [DecidableEq ι] in
theorem zero_comparison_scale_caps (b L ε:ℝ)(hL:0≤L)(hε:0<ε):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧ ∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      s.b₁≤b → s.X₁≤Z^L → s.X₂≤Z^L →
      (zeroInput s hz₁ hz₂).Y₁≤Z^(2*L+ε) ∧
      (zeroInput s hz₁ hz₂).Y₂≤Z^(2*L+ε):=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro s hz₁ hz₂ hb hX₁ hX₂
  have hZ0:0<Z:=zero_lt_one.trans hZ
  refine ⟨(smallScale_le_one _).trans (Real.one_le_rpow hZ.le (by positivity)),?_⟩
  change s.X₁*s.X₂/smallScale s.b₁≤_
  have hp:s.X₁*s.X₂≤Z^(2*L):=by
    have hh:=mul_le_mul hX₁ hX₂ s.X₂_pos.le (Real.rpow_pos_of_pos hZ0 L).le
    rw [←Real.rpow_add hZ0] at hh
    simpa only [two_mul] using hh
  have hconst:2*max 1 s.b₁≤Z^ε:=(mul_le_mul_of_nonneg_left (max_le_max_left 1 hb) (by norm_num)).trans hc
  unfold smallScale
  rw [div_div_eq_mul_div,div_one]
  calc
    s.X₁*s.X₂*(2*max 1 s.b₁)≤Z^(2*L)*Z^ε:=
      mul_le_mul hp hconst (by positivity) (Real.rpow_pos_of_pos hZ0 _).le
    _=Z^(2*L+ε):=(Real.rpow_add hZ0 _ _).symm

end SevenEighths.CenteredMomentEnergyZeroComparison

end

end OAI

end Source2035

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstDivisorSupport.lean; sha256: 114f5e2afeda8018df072f4af0e4564189ea015c1459b08336b34749195563b8 -/
section Source2036
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstDivisorSupport
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentSecondDivisorSupport CenteredMomentChildAssembly
open CenteredMomentHeckeColumnWindow
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

lemma common_coefficient_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (I : supportedColumns (residualPool D hD.1 s.columns)) :
    (if IsCoprime D (I:Ideal O) ∧ L∣(I:Ideal O) then s.beta (D*I) else 0)*heightCoeff τ t I=0 := by
  split_ifs with hi
  · have hz : s.beta (D*I)=0 := by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (Finset.mem_filter.mp I.property).2.1 s.beta H hβ hn hi.2)
    rw [hz,zero_mul]
  · rw [zero_mul]

theorem commonEnergy_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    commonEnergy s D hD τ t L W K=0 := by
  unfold commonEnergy gaussEnergy gaussPolynomial
  simp only [common_coefficient_zero s D hD H hβ L hL τ t,zero_mul,
    Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0),Complex.ofReal_zero,tsum_zero]

lemma right_coefficient_zero (s : OriginalData ι) (C D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (a : columns C D hD.1 s.columns→ℂ) (I : columns C D hD.1 s.columns) :
    divisorCoefficient L (element C D hD.1 s.columns)
      (fun I=>coefficient η m 1 t s.beta D I*a I) χ I=0 := by
  unfold divisorCoefficient
  rw [element_span]
  split_ifs with hd
  · have hz : s.beta (D*I)=0 := by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (column_supported C D hD.1 s.columns I).1 s.beta H hβ hn hd)
    simp only [coefficient,hz,zero_mul]
  · rfl

theorem rightWindowChild_zero (s : OriginalData ι) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (z : O) :
    rightWindowChild s η m t C D hC hD E χ L θ X V z=0 := by
  unfold rightWindowChild gaussPolynomial
  dsimp only
  simp only [right_coefficient_zero s C D hD H hβ L hL η m t χ,
    zero_mul,Finset.sum_const_zero]

theorem signed_right_window_filter (s : OriginalData ι) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (Ds : Finset (Ideal O)) (rows : Finset O)
    (F : Ideal O→O→ℂ) :
    (∑L∈Ds,∑z∈rows,F L z*star (rightWindowChild s η m t C D hC hD E χ L θ X V (-z)))=
      ∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)),
        ∑z∈rows,F L z*star (rightWindowChild s η m t C D hC hD E χ L θ X V (-z)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hLD
  by_cases hl : (L.absNorm:ℝ)≤H/(D.absNorm:ℝ)
  · rw [ite_eq_left hl]
  · rw [ite_eq_right hl]
    simp only [rightWindowChild_zero s C D hC hD E H hβ L (lt_of_not_ge hl),star_zero,
      mul_zero,Finset.sum_const_zero]

theorem supported_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(Ds : Finset (Ideal O))(D : Ideal O)(H : ℝ),H/(D.absNorm:ℝ)≤Z^B →
      (∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)),
        ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=CenteredMomentMobiusHarmonicMass.full_mass_subpower B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Ds D H hcap
  exact hz.2 _ (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hcap)

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

theorem input_commonEnergy_zero (s : Input ι) (R seed D : Ideal O) (hD : Supported D)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (L : Ideal O)
    (hL : CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    commonEnergy (original s R seed) D hD τ t L W K=0 :=
  commonEnergy_zero (original s R seed) D hD _
    (fun I hi=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s R seed I hz₁ hz₂ hi).2)
    L hL τ t W K

theorem input_rightWindowChild_zero (s : Input ι) (R seed C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (L : Ideal O)
    (hL : CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)<L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (z : O) :
    rightWindowChild (original s R seed) η m t C D hC hD E χ L θ X V z=0 :=
  rightWindowChild_zero (original s R seed) C D hC hD E _
    (fun I hi=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s R seed I hz₁ hz₂ hi).2)
    L hL η m t χ θ X V z

end SevenEighths.CenteredMomentFirstDivisorSupport

end

end OAI

end Source2036

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalSourceCommonBound.lean; sha256: b8fad867982e95680592c8c7de066297a5bc1868f36a831d6c6648e853d13ab9 -/
section Source2037
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSecondIdealBlockBound
local notation "O"=>ActualEisensteinCubic.O
universe u

theorem fixed_log_block_from_common_energy (W:𝓢(ℝ,ℂ))(decay J₁ J₂:ℕ):
    ∃Cbound:ℝ,0≤Cbound ∧ ∀{ι:Type u}[Fintype ι],∀η:Character,∀s:OriginalData ι,
    ∀t:ℝ,∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(E:Finset (CommonIndex C D))(rows:Finset O),(∀h∈rows,h≠0)→
    ∀K K₀ H₀ A₀ B₀:ℝ,0<K→0<K₀→0<H₀→0<A₀→0<B₀→
    ∀(U:𝓢(ℝ,ℂ))(H:ℝ),0<H→
    (∀h:O,0≤(U (‖eisEmbedding h‖^2/H)).re)→
    (∀h∈rows,1≤(U (‖eisEmbedding h‖^2/H)).re)→
    ∀E₁ E₂:Ideal O→ℝ,
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}),0≤E₁ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}),0≤E₂ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}),∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L U H).re≤E₁ L*(1+‖v‖)^(2*J₁))→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}),∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L U H).re≤E₂ L*(1+‖v‖)^(2*J₂))→
    (1+K₀*H₀/(A₀*B₀))^decay*
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K K₀ H₀ A₀ B₀‖≤
      ‖scalar C D hC E K A₀ B₀‖*Cbound*
        ∑L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (windowBudget J₁ t (E₁ L)*windowBudget J₂ t (E₂ L)):=by
  obtain ⟨Cb,hCb,hbound⟩:=physical_block_child_bound W (fun _=>logAnnulus) (fun _=>Real.log 4)
    (fun _=>Real.log_nonneg (by norm_num)) (fun _ _ hn=>logAnnulus_enclosure _ hn) decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows hrows K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
    U H hH hU hmajor E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound η (fixedBadMask*idealGenerator s.R) t s.columns s.beta C D hC hD hCD E rows hrows
    K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
    (fun _ _=>logAnnulus_norm _) (fun _ _=>logAnnulus_norm _) U H hH hU hmajor
    (fun L=>windowBudget J₁ t (E₁ L)) (fun L=>windowBudget J₂ t (E₂ L))
    (fun L _=>windowBudget_nonneg _ _ _) (fun L _=>windowBudget_nonneg _ _ _)
  · intro L hL χ θ
    exact (fixedPair η C D hC E χ χ).left_window_energy s t θ A₀ hA₀ L U H hH hU J₁ (E₁ L)
      (hE₁ L hL) (hleft L hL χ)
  · intro L hL χ θ
    exact (fixedPair η C D hC E χ χ).right_window_energy hD hCD s t θ B₀ hB₀ L U H hH hU J₂ (E₂ L)
      (hE₂ L hL) (hright L hL χ)

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI

end Source2037

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalAnnularCommonBound.lean; sha256: 77e400002f3cbe68b558f7ed3db9ec13b984241953e8bc415393b082ddbc8bd7 -/
section Source2038
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalAnnularCommonBound
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
universe u

theorem actual_annular_block_from_common_energy (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ E₁ E₂ : Ideal O→ℝ,
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), 0≤E₁ L) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), 0≤E₂ L) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ E₁ L*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ E₂ L*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        ∑ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (windowBudget J₁ t (E₁ L)*windowBudget J₂ t (E₂ L)) := by
  obtain ⟨Cb,hCb,hbound⟩:=fixed_log_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n E₁ E₂ hE₁ hE₂ hleft hright
  rw [block_activeRows η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta
    C D hC hD E rows W K n]
  exact hbound η s t C D hC hD hCD E (activeRows rows n)
    (activeRows_nonzero rows n) K (dyadicScale (n 0)) (dyadicScale (n 1))
    (dyadicScale (n 2)) (dyadicScale (n 3)) hK
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
    CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _=>CenteredMomentFirstAnnularMajorant.profile_nonneg _)
    (fun h hh=>by
      have hn:=activeRows_norm rows n h hh
      have hm:=CenteredMomentFirstAnnularMajorant.scaled_majorant
        (dyadicScale (n 1)) (normValue h) (dyadicScale_pos _) hn.2.1.le hn.2.2.le
      simpa only [normValue_eq_embedding] using hm.ge)
    E₁ E₂ hE₁ hE₂ hleft hright

end SevenEighths.CenteredMomentFirstPhysicalAnnularCommonBound

end

end OAI

end Source2038

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstDivisorCommonBound.lean; sha256: 7dc383f4560c277dddf55b775670364327057c8e90d800852f6945cbe65c1f16 -/
section Source2039
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstDivisorCommonBound
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentFirstDivisorSupport CenteredMomentChildAssembly
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSecondWindowBudget
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentMobiusRegroup
open CenteredMomentSecondHeightFamily CenteredMomentFirstPhysicalAnnularCommonBound
local notation "O"=>ActualEisensteinCubic.O

def pairMajorant {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : α→ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑i∈S,∑j∈S,b i*b j*‖∑'z:O,(gaussRow (a i) (ha i) z*star (gaussRow (a j) (ha j) z))*
    W (‖eisEmbedding z‖^2/K)‖

lemma pairMajorant_nonneg {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : α→ℝ) (hb : ∀i∈S,0≤b i)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : 0≤pairMajorant S a ha b W K :=
  Finset.sum_nonneg (fun i hi=>Finset.sum_nonneg (fun j hj=>
    mul_nonneg (mul_nonneg (hb i hi) (hb j hj)) (norm_nonneg _)))

lemma gaussEnergy_pair_bound {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ) (b : α→ℝ)
    (hc : ∀i∈S,‖c i‖≤b i) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (gaussEnergy S a ha c W K).re≤pairMajorant S a ha b W K := by
  apply (Complex.re_le_norm _).trans
  rw [gaussEnergy_expand S a ha c W K hK]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  simp only [norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (hc i hi) (hc j hj) (norm_nonneg _) ((norm_nonneg _).trans (hc i hi)))
    (norm_nonneg _)

variable {ι : Type*} [Fintype ι]

def coarse (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  pairMajorant Finset.univ (sourceGenerator (residualPool C hC.1 s.columns))
    (sourceGenerator_supported _) (fun I:supportedColumns (residualPool C hC.1 s.columns)=>
      ‖if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then s.beta (C*I) else 0‖) W K

lemma coarse_nonneg (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : 0≤coarse s C hC L W K :=
  pairMajorant_nonneg _ _ _ _ (fun _ _=>norm_nonneg _) _ _

lemma commonEnergy_coarse (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (τ : Character) (v : ℝ) :
    (commonEnergy s C hC τ v L W K).re≤coarse s C hC L W K := by
  apply gaussEnergy_pair_bound _ _ _ _ _ _ W K hK
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one τ v I
      (Finset.mem_filter.mp I.property).2.1)

universe u

theorem actual_supported_annular_block (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ Hsource : ℝ,(∀I,s.beta I≠0→(I.absNorm:ℝ)≤Hsource) →
    ∀ E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₁/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₂/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        (∑ L∈(divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b})).filter
            (fun L=>(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
            (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨Cb,hCb,hbound⟩:=actual_annular_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n Hsource hβ E₁ E₂ hE₁ hE₂ hleft hright
  let live (L : Ideal O) : Prop := (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)
  let U := CenteredMomentFirstAnnularMajorant.profile
  let H := dyadicScale (n 1)
  let active (L : Ideal O) : Prop := live L ∧ (UniqueFactorizationMonoid.moebius L:ℂ)≠0
  let F₁ (L : Ideal O) := if active L then E₁/(L.absNorm:ℝ) else coarse s C hC L U H
  let F₂ (L : Ideal O) := if active L then E₂/(L.absNorm:ℝ) else if live L then coarse s D hD L U H else 0
  have hF₁ (L : Ideal O) : 0≤F₁ L := by
    dsimp only [F₁]; split_ifs
    · exact div_nonneg hE₁ (Nat.cast_nonneg _)
    · exact coarse_nonneg _ _ _ _ _ _
  have hF₂ (L : Ideal O) : 0≤F₂ L := by
    dsimp only [F₂]; split_ifs
    · exact div_nonneg hE₂ (Nat.cast_nonneg _)
    · exact coarse_nonneg _ _ _ _ _ _
    · exact le_rfl
  have hh:=hbound η s t C D hC hD hCD E rows K hK n F₁ F₂
    (fun L _=>hF₁ L) (fun L _=>hF₂ L)
    (by
      intro L hL χ v
      by_cases hl:active L
      · simpa only [F₁,ite_eq_left hl] using hleft L hL hl.1 (CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hl.2) χ v
      · apply (commonEnergy_coarse s C hC L U H (dyadicScale_pos _) _ v).trans
        rw [show F₁ L=coarse s C hC L U H from ite_eq_right hl]
        exact le_mul_of_one_le_right (coarse_nonneg _ _ _ _ _ _)
          (one_le_pow₀ (by linarith [norm_nonneg v])))
    (by
      intro L hL χ v
      by_cases hl:active L
      · simpa only [F₂,ite_eq_left hl] using hright L hL hl.1 (CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hl.2) χ v
      · by_cases hc:live L
        · apply (commonEnergy_coarse s D hD L U H (dyadicScale_pos _) _ v).trans
          simp only [F₂,ite_eq_right hl,ite_eq_left hc]
          exact le_mul_of_one_le_right (coarse_nonneg _ _ _ _ _ _) (one_le_pow₀ (by linarith [norm_nonneg v]))
        · rw [commonEnergy_zero s D hD Hsource hβ L (lt_of_not_ge hc)]
          simp only [F₂,ite_eq_right hl,ite_eq_right hc,Complex.zero_re,zero_mul,le_refl])
  let Ds:=divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
    (fun b=>Ideal.span {element C D hD.1 s.columns b})
  have he : (∑L∈Ds,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
      (windowBudget J₁ t (F₁ L)*windowBudget J₂ t (F₂ L))) =
      (∑L∈Ds.filter live,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
    rw [Finset.sum_mul,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L hL
    by_cases hμ:(UniqueFactorizationMonoid.moebius L:ℂ)=0
    · simp only [hμ,norm_zero,zero_mul,zero_div,ite_self]
    · by_cases hl:live L
      · have ha:active L:=⟨hl,hμ⟩
        simp only [F₁,F₂,ite_eq_left ha,live,ite_eq_left hl]
        rw [CenteredMomentSecondHarmonicBudget.paired_divisor J₁ J₂ t E₁ E₂ _ (Nat.cast_nonneg _)]
        ring
      · have ha:¬active L:=fun hh=>hl hh.1
        simp only [F₂,ite_eq_right ha,live,ite_eq_right hl,windowBudget,Real.sqrt_zero,zero_mul,mul_zero]
  exact hh.trans_eq (by rw [he]; ring)

theorem actual_supported_annular_harmonic (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ)
    (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃ Cbound : ℝ, 0<Cbound ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ Hsource : ℝ,(∀I,s.beta I≠0→(I.absNorm:ℝ)≤Hsource) →
    Hsource/(D.absNorm:ℝ)≤Z^B → ∀ E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₁/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₂/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*Z^δ*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨Cb,hCb,hbound⟩:=actual_supported_annular_block W decay J₁ J₂
  obtain ⟨Cm,hCm,hmass⟩:=supported_harmonic_mass B δ hB hδ
  refine ⟨(Cb+1)*Cm,mul_pos (by linarith) hCm,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n Hsource hβ hcap E₁ E₂ hE₁ hE₂ hleft hright
  have hh:=hbound η s t C D hC hD hCD E rows K hK n Hsource hβ E₁ E₂ hE₁ hE₂ hleft hright
  have hm:=hZ.2 (divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
    (fun b=>Ideal.span {element C D hD.1 s.columns b})) D Hsource hcap
  have hW : 0≤windowBudget J₁ t E₁*windowBudget J₂ t E₂ :=
    mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)
  have hz : 0≤Z^δ := Real.rpow_nonneg ((zero_lt_one.trans hZ.1).le) _
  calc
    _ ≤ _ := hh
    _ ≤ ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cb*(Cm*Z^δ)*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
      gcongr
    _ ≤ _ := by
      have hc : Cb≤Cb+1 := by linarith
      calc
        _ = ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cb*Cm*Z^δ*
          (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by ring
        _ ≤ ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*(Cb+1)*Cm*Z^δ*
          (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by gcongr
        _ = _ := by ring

end SevenEighths.CenteredMomentFirstDivisorCommonBound

end

end OAI

end Source2039
