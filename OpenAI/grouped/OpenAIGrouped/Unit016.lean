import OpenAIGrouped.Unit015
import OpenAIGrouped.Unit014
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit009
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import OpenAIGrouped.Unit013
import OpenAIGrouped.Unit010
import OpenAIGrouped.Unit008
import OpenAIGrouped.Unit007

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondMaskedWindow.lean; sha256: abe3cab8f5e28e8f3da9fea1258a0098f0186a783d6e9c1ecceaadd6be5c23fd -/
section Source640
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondMaskedWindow
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedSource
open CenteredMomentChildAssembly CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentRowNorm CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

theorem masked_divisor_coefficient (η τ : Character) (χ : RayCharacter) (A : O)
    (C : Ideal O) (hC : Supported C)
    (hτ : ∀I:Ideal O,Supported I → IsCoprime C I → ∀t:ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (t : ℝ)
    (I : sectorPool C hC.1 S) :
    divisorCoefficient L (sectorElement C hC.1 S)
      (movingCoefficient A (sectorElement C hC.1 S)
        (fun J:sectorPool C hC.1 S=>β (C*J)*heightCoeff η t J)) χ I=
      (if L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I := by
  have hi : IsCoprime C (I:Ideal O) := (Finset.mem_filter.mp I.property).2
  rw [divisorCoefficient,movingCoefficient,sectorElement_span,
    hτ I (sectorPool_supported C hC.1 S I) hi t]
  dsimp only [sectorElement]
  split_ifs <;> ring

theorem masked_child_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (C : Ideal O) (hC : Supported C)
    (hτ : ∀I:Ideal O,Supported I → IsCoprime C I → ∀t:ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (t : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J:sectorPool C hC.1 S=>β (C*J)*heightCoeff η t J)) χ) Φ H=
    sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τ t) Φ H := by
  have he := funext (masked_divisor_coefficient η τ χ A C hC hτ S β L t)
  rw [he]
  unfold restrictedEnergy sourceRestrictedEnergy
  apply tsum_congr
  intro z
  rw [sector_rowPolynomial S (fun I=>(if L∣I then β (C*I) else 0)*heightCoeff τ t I) C hC z]
  have hc : (fun I : supportedColumns (residualPool C hC.1 S)=>
      if IsCoprime C (I:Ideal O) then (if L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I else 0)=
      (fun I : supportedColumns (residualPool C hC.1 S)=>
        (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I) := by
    funext I
    split_ifs <;> simp_all
  rw [hc]

theorem original_window_from_masked_source (η τ : Character) (χ : RayCharacter) (A : O)
    (C : Ideal O) (hC : Supported C)
    (hτ : ∀I:Ideal O,Supported I → IsCoprime C I → ∀t:ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (keep : O→Prop)
    (t θ X : ℝ) (hX : 0<X) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀v:ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S) (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) Φ H≤
      (E*heightCost t θ^(2*J))*(∫w:ℝ,(1+‖w‖)^J*
        ‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖)^2 := by
  have hc := funext (masked_divisor_coefficient η τ χ A C hC hτ S β L t)
  change restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
    (fun I=>(divisorCoefficient L (sectorElement C hC.1 S)
      (movingCoefficient A (sectorElement C hC.1 S) (fun I=>β (C*I)*heightCoeff η t I)) χ) I*_) Φ H≤_
  rw [hc]
  have hh := restricted_window_energy_from_height keep logAnnulus logAnnulus_compact logAnnulus_smooth J
    Finset.univ (sectorElement C hC.1 S) (sectorElement_supported C hC.1 S)
    (fun I:sectorPool C hC.1 S=>if L∣(I:Ideal O) then β (C*I) else 0)
    τ t θ X hX Φ H hH hΦ E hE ?_
  · simpa only [sectorElement_span] using hh
  intro v
  have hs := hsource v
  rw [←masked_child_energy η τ χ A C hC hτ S β L v keep Φ H] at hs
  rw [funext (masked_divisor_coefficient η τ χ A C hC hτ S β L v)] at hs
  simpa only [sectorElement_span] using hs

end SevenEighths.CenteredMomentSecondMaskedWindow

end

end OAI

end Source640

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondRadicalFamily.lean; sha256: 47ffceab874ea2b5dd09ac209cd11b5d749ea930cc0282e035b7ef8292dfee20 -/
section Source641
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst (CommonIndex)
open CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource
open CenteredMomentRadicalFamily CenteredMomentSecondHeightFamily CenteredMomentSecondChildProfile
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentCommonSupport RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem active_radical_product (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) :
    (∏ P : ActiveIndex C D U,Ideal.span {activePrime C D U P})=
      ∏ P∈fixedActiveSet C D U,P.val := by
  simp only [activePrime,commonPrime_span C D hC]
  exact Finset.prod_coe_sort _ (fun P : CommonIndex C D=>P.val)

theorem exists_second_radical_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      τ.modulus.absNorm≤(childCharacter η χ).modulus.absNorm*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (∏P∈fixedActiveSet C D U,P.val).absNorm ∧
      (∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
        fixedBadMask 1 (reducedNumerator C D U) n) ∧
      ∀I:Ideal O,Supported I → ∀t:ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hM,hN,hτ⟩ := exists_radical_row_presentation (childCharacter η χ) fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    (activePrime C D U) (fun P=>commonPrime_supported C D hC P.val)
    (activeExponent C D U) (activeExponent_pos C D U)
  have he (n:O) : elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n := by
    rw [reducedNumerator_active_product]
    exact hτ n
  refine ⟨τ,?_,he,?_⟩
  · rw [←map_prod,active_radical_product C D hC U] at hN
    exact hN
  · intro I hI t
    have ht := idealCoeff_eq_row (childCharacter η χ) τ fixedBadMask 1
      (reducedNumerator C D U) he I
    change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
    rw [ht,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
    simp only [one_pow,mul_one]
    rw [heightCoeff_eq_fixed_rowWeight η t I hI]
    simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk]
    ring_nf

end SevenEighths.CenteredMomentSecondRadicalFamily

end

end OAI

end Source641

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondRadicalColumns.lean; sha256: db6a7682289f2f19215e9dbd0806c1db79d7fb51ae223defae129eaa695c37a9 -/
section Source642
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondRadicalColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction
open CenteredMomentSecondSixthSource CenteredMomentSecondRadicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

theorem sixthFactor_span_dvd_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    Ideal.span {sixthFactor C D U}∣D := by
  conv_rhs => rw [←right_ideal_product C D hC hD hCD]
  simp only [sixthFactor,span_finset_product,←Ideal.span_singleton_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  have hd := rightExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤rightExponent C D P := min_le_right _ _
  unfold fixedExponent
  split_ifs <;> omega

theorem residual_sixth_coefficient_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime D I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,ite_eq_left
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd_right C D hC hD hCD U)),mul_one]

theorem exists_actual_masked_radical_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      τ.modulus.absNorm≤(childCharacter η χ).modulus.absNorm*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (∏P∈fixedActiveSet C D U,P.val).absNorm ∧
      ∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀t:ℝ,
        heightCoeff τ t I=heightCoeff η t I*
          idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
          rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hN,he,hτ⟩ := exists_second_radical_family η χ C D hC U
  refine ⟨τ,hN,?_⟩
  intro I hI hi t
  rw [hτ I hI t]
  rcases hi with hi|hi
  · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
  · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]

end SevenEighths.CenteredMomentSecondRadicalColumns

end

end OAI

end Source642

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondWindowBudget.lean; sha256: d0034e50bccefa53da9bb738e4c354225797938d227733a9e729947acdcde111 -/
section Source643
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowBudget
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open CenteredMomentSecondWindowSource

def profileMoment (J : ℕ) : ℝ :=
  ∫ w : ℝ,(1+‖w‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖

theorem profileMoment_nonneg (J : ℕ) : 0≤profileMoment J :=
  integral_nonneg (fun w=>by positivity)

def heightEnvelope (t : ℝ) : ℝ := (1+‖t‖+2*Real.pi)*(1+2*Real.pi)

theorem heightEnvelope_pos (t : ℝ) : 0<heightEnvelope t := by unfold heightEnvelope;positivity

theorem heightCost_le_envelope (t θ : ℝ) : heightCost t θ≤heightEnvelope t*(1+‖θ‖) := by
  have hh : 1+‖t‖+2*Real.pi*‖θ‖≤(1+‖t‖+2*Real.pi)*(1+‖θ‖) := by
    nlinarith [norm_nonneg t,norm_nonneg θ,Real.pi_pos]
  have he := mul_le_mul_of_nonneg_right hh (show 0≤1+2*Real.pi by positivity)
  convert he using 1 <;> simp only [heightCost,heightEnvelope] ; ring

def windowBudget (J : ℕ) (t E : ℝ) : ℝ := Real.sqrt E*heightEnvelope t^J*profileMoment J

theorem windowBudget_nonneg (J : ℕ) (t E : ℝ) : 0≤windowBudget J t E :=
  mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (heightEnvelope_pos _).le _))
    (profileMoment_nonneg _)

theorem shifted_window_budget (J : ℕ) (t θ E : ℝ) (hE : 0≤E) :
    (E*heightCost t θ^(2*J))*profileMoment J^2≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  calc
    _ ≤ E*(heightEnvelope t*(1+‖θ‖))^(2*J)*profileMoment J^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (heightCost_pos _ _).le (heightCost_le_envelope t θ) _) hE)
        (sq_nonneg _)
    _ = _ := by
      rw [show 2*J=J*2 by omega,pow_mul]
      simp only [windowBudget,mul_pow,Real.sq_sqrt hE]
      ring

theorem conjugate_shifted_window_budget (J : ℕ) (t θ E : ℝ) (hE : 0≤E) :
    (E*heightCost t (-θ)^(2*J))*profileMoment J^2≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  simpa only [norm_neg] using shifted_window_budget J t (-θ) E hE

end SevenEighths.CenteredMomentSecondWindowBudget

end

end OAI

end Source643

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondRadicalBlock.lean; sha256: 3a60783b42e69313f3ac3772845d021bd2f8bd0026c391830527fc0efe904731 -/
section Source644
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondRadicalBlock
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

theorem actual_block_from_masked_source (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃B:ℝ,0≤B ∧ ∀r:ℝ,0<r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
        (C D:Ideal O) (hC:Supported C) (hD:Supported D),
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0<X → 0<Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),0<H →
      (∀z:O,0≤(Φ (normValue z/H)).re) → (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:Ideal O→ℝ,
      (∀L,0≤E₁ L) → (∀L,0≤E₂ L) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool C hC.1 S)
          (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤E₁ L*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool D hD.1 S)
          (fun I=>if IsCoprime D I ∧ L∣I then β (D*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤E₂ L*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        B*∑L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (windowBudget J₁ t (E₁ L)*windowBudget J₂ t (E₂ L)) := by
  obtain ⟨B,hB,hbound⟩:=actual_nonexceptional_block_bound W decay J₁ J₂
  refine ⟨B,hB,?_⟩
  intro r hr η τ t S β C D hC hD hCD U A hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound r hr η t S β C D hC hD hCD U R rows ρ x
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
    (fun J=>Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y)) Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor
    (fun L=>windowBudget J₁ t (E₁ L)) (fun L=>windowBudget J₂ t (E₂ L))
    (fun L _=>windowBudget_nonneg _ _ _) (fun L _=>windowBudget_nonneg _ _ _)
  · intro L hL χ w
    exact (original_window_from_masked_source η (τ χ) χ A C hC
      (fun I hi hc v=>hτ χ I hi (Or.inl hc) v) S β L _ t w X hX J₁ Φ H hH
      (by simpa only [normValue_eq_embedding] using hΦ) (E₁ L) (hE₁ L) (hleft L hL χ)).trans
        (shifted_window_budget J₁ t w (E₁ L) (hE₁ L))
  · intro L hL χ w
    simp only [star_logAnnulus_column]
    exact (original_window_from_masked_source η (τ χ) χ A D hD
      (fun I hi hc v=>hτ χ I hi (Or.inr hc) v) S β L _ t (-w) Y hY J₂ Φ H hH
      (by simpa only [normValue_eq_embedding] using hΦ) (E₂ L) (hE₂ L) (hright L hL χ)).trans
        (conjugate_shifted_window_budget J₂ t w (E₂ L) (hE₂ L))

end SevenEighths.CenteredMomentSecondRadicalBlock

end

end OAI

end Source644

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondPhysicalBlock.lean; sha256: 5035d144a8ac5eb20369e47c3fa647fed42f57dca4cdfa86e541266d5a3abc93 -/
section Source645
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondSectorRetained CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSectorLocalization
open CenteredMomentSecondRadicalBlock CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

def outerScalar (C D : Ideal O) (K : ℝ) (n : Fin 4→ℤ) : ℝ :=
  K/(Real.sqrt (Ideal.absNorm C:ℝ)*Real.sqrt (Ideal.absNorm D:ℝ)*
    Real.sqrt (dyadicScale (n 2))*Real.sqrt (dyadicScale (n 3)))

def physicalBlock (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) : ℂ :=
  let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  ∑z∈rows,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*z) then
    ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        idealCorrelation (C*I) (D*J)
          ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
          ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
      ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
      (physicalKernel C D W K R (A*z) I J*
        ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue z)*
          dyadicWeight (n 2) (Ideal.absNorm (I:Ideal O):ℝ)*
          dyadicWeight (n 3) (Ideal.absNorm (J:Ideal O):ℝ):ℝ):ℂ)) else 0

def normalizedBlock (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) : ℂ :=
  let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  ∑z∈rows,retainedScalar C D U R z*
    ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        idealCorrelation (C*I) (D*J)
          ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
          ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
      ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
      wholeKernel W (fun _=>logAnnulus)
        (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
        (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
        (Real.log (normValue z/dyadicScale (n 1)))
        (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/dyadicScale (n 2)))
        (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/dyadicScale (n 3)))

private lemma physicalBlock_scalar (a b c d e f : ℂ) (hb : b ≠ 0) :
    c * d * (a * e * f) = a * b * (b⁻¹ * e * (c * d * f)) := by
  calc
    _ = a * e * (c * d * f) := by ring
    _ = a * (b * b⁻¹) * e * (c * d * f) := by rw [mul_inv_cancel₀ hb, mul_one]
    _ = _ := by ring

theorem physicalBlock_eq (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ) :
    physicalBlock η t S β C D hC hD U R rows W K n=
      (outerScalar C D K n:ℂ)*(normalizer C D U:ℂ)*
        normalizedBlock η t S β C D hC hD U R rows W K n := by
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC) (nonunitFrequencyGenerator_ne_zero C D hC U)
  unfold physicalBlock normalizedBlock
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp_rw [physical_kernel_dyadic C D _ _ hC hD
    (sectorPool_supported C hC.1 S _) (sectorPool_supported D hD.1 S _)
    _ z hA (hrows z hz) W K R hK n]
  have hn : (normalizer C D U:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (normalizer_pos C D hC U).ne'
  simp only [outerScalar,Complex.ofReal_div,Complex.ofReal_mul,retainedScalar,canonicalPartitionScalar]
  simp only [normalizer] at hn ⊢
  by_cases hp : canonicalPartition C D U (nonunitFrequencyGenerator C D U*z)
  · simp only [hp,ite_true]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    exact physicalBlock_scalar _ _ _ _ _ _ hn
  · simp only [hp,ite_false,mul_zero,zero_mul,Finset.sum_const_zero]

end SevenEighths.CenteredMomentSecondPhysicalBlock

end

end OAI

end Source645

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondBlockAggregate.lean; sha256: f788c1c915dcfed59fad24f04dd4dea44f0a822b1d41e7861c273d2760eda1be -/
section Source646
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondBlockAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondLocalization CenteredMomentSecondSectorFrequency
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorColumns
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentHeckeColumnWindow
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondRetainedRows
open CenteredMomentSecondActiveDyadic CenteredMomentSecondDyadicPartition
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondPhysicalBlock CenteredMomentSecondWholeKernel
local notation "O" => ActualEisensteinCubic.O

abbrev ActiveLabel (S : Finset (Ideal O)) (β : Ideal O→ℂ) :=
  ↥(commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β)))

abbrev SourceBlocks (C D : Ideal O) (U : Finset (CommonIndex C D)) (K R H : ℝ) :=
  Blocks (sourceLower C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K)
    (sourceUpper C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K R H)

lemma retainedRows_ne_zero (R : ℝ) (A z : O) (hz : z∈retainedRows R A) : z≠0 := by
  have hp := (mem_rowNormDisk.mp hz).1
  intro h
  simp [h] at hp

theorem active_kernel_windows (η : Character)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (I : sectorPool C hC.1 (activeSource S β)) (J : sectorPool D hD.1 (activeSource S β))
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks (sourceLower C D A K) (sourceUpper C D A K R H),
        physicalKernel C D W K R (A*h) I J*
          ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue h)*
            dyadicWeight (n 2) (Ideal.absNorm (I:Ideal O):ℝ)*
            dyadicWeight (n 3) (Ideal.absNorm (J:Ideal O):ℝ):ℝ):ℂ) := by
  refine (active_physical_kernel_partition η S β H hH C D hC hD I J A h hA W K R hK).trans ?_
  apply Finset.sum_congr rfl
  intro n hn
  exact (physical_kernel_dyadic C D I J hC hD
    (sectorPool_supported C hC.1 _ I) (sectorPool_supported D hD.1 _ J)
    A h hA hh W K R hK (fun i=>n i)).symm

theorem sector_finite_blocks (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
    (∑h∈retainedRows R A,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      sectorFrequency η t (activeSource S β) β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑n : SourceBlocks C D U K R H,
        physicalBlock η t (activeSource S β) β C D hC hD U R (retainedRows R A) W K
          (fun i=>(n i:ℤ)) := by
  dsimp only
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)
  unfold physicalBlock
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hp : canonicalPartition C D U (nonunitFrequencyGenerator C D U*h)
  · simp only [hp,ite_true]
    unfold sectorFrequency
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I hI
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J hJ
    conv_lhs => rw [active_kernel_windows η S β H hH C D hC hD I J _ h hA
      (retainedRows_ne_zero R _ h hh) W K R hK,Finset.mul_sum]
  · simp only [hp,ite_false,Finset.sum_const_zero]

theorem original_secondRetainedEnergy_blocks (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ H : ℝ) (hK : 0<K)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑p : ActiveLabel S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
        ∑U : Finset (CommonIndex p.val.1 p.val.2),
          ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock η t (activeSource S β) β p.val.1 p.val.2
              (commonLabels_supported (activeSource S β) _ _ p.property).1
              (commonLabels_supported (activeSource S β) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (retainedRows (frequencyRadius Tsec Z ξ)
                (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
              W K (fun i=>(n i:ℤ)) := by
  rw [←secondRetainedEnergy_active η t S β W K Tsec Z ξ,
    original_retained_energy_GV η t (activeSource S β) β W K Tsec Z ξ hK]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [actual_GV_finite_rows]
  exact sector_finite_blocks η t S β H hH _ _ _ _ U W K _ hK

lemma common_height_norm_le_one (η : Character) (t : ℝ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) :
    ‖heightCoeff η t C*star (heightCoeff η t D)‖≤1 := by
  rw [norm_mul,norm_star]
  have hc := CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one η t C hC
  have hd := CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one η t D hD
  nlinarith [norm_nonneg (heightCoeff η t C),norm_nonneg (heightCoeff η t D)]

theorem original_secondRetainedEnergy_norm_le (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ H : ℝ) (hK : 0<K)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H) :
    ‖secondRetainedEnergy η t S β W K Tsec Z ξ‖≤
      ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
            (commonLabels_supported (activeSource S β) _ _ p.property).1
            (commonLabels_supported (activeSource S β) _ _ p.property).2 U
            (frequencyRadius Tsec Z ξ)
            (retainedRows (frequencyRadius Tsec Z ξ)
              (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
            W K (fun i=>(n i:ℤ))‖ := by
  rw [original_secondRetainedEnergy_blocks η t S β W K Tsec Z ξ H hK hH]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    (common_height_norm_le_one η t _ _
      (commonLabels_supported (activeSource S β) _ _ p.property).1.1
      (commonLabels_supported (activeSource S β) _ _ p.property).2.1)).trans
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro U hU
  exact norm_sum_le _ _

end SevenEighths.CenteredMomentSecondBlockAggregate

end

end OAI

end Source646

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondRadicalBudget.lean; sha256: 94dd796ed54ab752af4934ebeb61f4b3f5ac9d96bc8ecf63f4b3b7cadc6193f1 -/
section Source647
namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
namespace SevenEighths.CenteredMomentSecondRadicalBudget
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondRadicalFamily CenteredMomentSecondMovingSupport
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst CenteredMomentChildRows CenteredMomentPartitionNorm
open CenteredMomentHeckeColumnWindow RayFourExpansion CenteredMomentCommonSupport CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

def fixedFactor : ℕ := (Ideal.span {(12:O)}).absNorm*
  (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

theorem fixedFactor_pos : 0<fixedFactor := by
  unfold fixedFactor
  apply Nat.mul_pos
  · apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))

theorem child_modulus_bound (η : Character) (χ : RayCharacter) :
    (childCharacter η χ).modulus.absNorm≤η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm := by
  have hn : η.modulus*Ideal.span {(12:O)}≠0 := mul_ne_zero η.modulus_ne_bot
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  have hd : (childCharacter η χ).modulus∣η.modulus*Ideal.span {(12:O)} := by
    apply Ideal.dvd_iff_le.mpr
    exact le_inf Ideal.mul_le_left Ideal.mul_le_right
  simpa only [map_mul] using Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)) (map_dvd Ideal.absNorm hd)

theorem active_radical_dvd (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*w)≠0) :
    (∏P∈fixedActiveSet C D U,P.val)∣
      (∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U} := by
  have hd := Finset.prod_dvd_prod_of_subset (fixedActiveSet C D U)
    (U∪nonunitPartitionSet C D U) (fun P:CommonIndex C D=>P.val)
    (fixedActiveSet_subset C D hC hD hCD U w hne)
  have hdis : Disjoint U (nonunitPartitionSet C D U) := by
    apply Finset.disjoint_left.mpr
    intro P hP hV
    exact (Finset.mem_sdiff.mp hV).2 hP
  rw [Finset.prod_union hdis] at hd
  rw [nonunitFrequencyGenerator_span]
  simpa only [unitIdeal,commonPrime_span C D hC] using hd

theorem active_radical_norm_bound (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*w)≠0) :
    (∏P∈fixedActiveSet C D U,P.val).absNorm≤
      (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm := by
  have hp (S : Finset (CommonIndex C D)) : (∏P∈S,P.val)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun P _=>(commonPrime_supported_ideal C D hC P).1)
  have hv : Ideal.span {nonunitFrequencyGenerator C D U}≠0 := by
    rw [nonunitFrequencyGenerator_span]
    simpa only [unitIdeal,commonPrime_span C D hC] using hp (nonunitPartitionSet C D U)
  simpa only [map_mul] using Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero (hp U) hv)))
    (map_dvd Ideal.absNorm (active_radical_dvd C D hC hD hCD U w hne))

theorem exists_second_budgeted_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD : Supported D),CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD
        (commonFrequencyGenerator C D*w)≠0 →
      τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*
        (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm := by
  obtain ⟨τ,hN,he,ht⟩ := exists_second_radical_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hne
  have h1 := child_modulus_bound η χ
  have h2 := active_radical_norm_bound C D hC hD hCD U w hne
  apply hN.trans
  calc
    _≤(η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
      ((∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)) h2
    _=_ := by unfold fixedFactor;ring

theorem conductor_log_bound (η τ : Character) (A B : Ideal O) (hA : A≠0) (hB : B≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*A.absNorm*B.absNorm)
    (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z (fixedFactor:ℝ)+Real.logb Z (A.absNorm:ℝ)+Real.logb Z (B.absNorm:ℝ) := by
  have hτ : (0:ℝ)<τ.modulus.absNorm := by
    exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))
  have hη : (η.modulus.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hK : (fixedFactor:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt fixedFactor_pos)
  have ha : (A.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hA)
  have hb : (B.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hh := Real.logb_le_logb_of_le hZ hτ (show (τ.modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*fixedFactor*A.absNorm*B.absNorm by exact_mod_cast hN)
  rwa [Real.logb_mul (mul_ne_zero (mul_ne_zero hη hK) ha) hb,
    Real.logb_mul (mul_ne_zero hη hK) ha,Real.logb_mul hη hK] at hh

theorem exists_second_log_budgeted_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD : Supported D),CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      ∀Z:ℝ,1<Z → Real.logb Z (τ.modulus.absNorm:ℝ)≤
        Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z (fixedFactor:ℝ)+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ) := by
  obtain ⟨τ,he,ht,hN⟩ := exists_second_budgeted_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hne Z hZ
  have hp (S : Finset (CommonIndex C D)) : (∏P∈S,P.val)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun P _=>(commonPrime_supported_ideal C D hC P).1)
  have hv : Ideal.span {nonunitFrequencyGenerator C D U}≠0 := by
    rw [nonunitFrequencyGenerator_span]
    simpa only [unitIdeal,commonPrime_span C D hC] using hp (nonunitPartitionSet C D U)
  exact conductor_log_bound η τ _ _ (hp U) hv (hN hD hCD w hne) Z hZ

theorem fixed_log_cost_eventually (ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ:ℝ in Filter.atTop,1<Z ∧ Real.logb Z (fixedFactor:ℝ)≤ε := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (fixedFactor:ℝ)
  filter_upwards [he,Filter.eventually_gt_atTop (1:ℝ)] with Z hK hZ
  refine ⟨hZ,?_⟩
  have hp : (0:ℝ)<fixedFactor := by exact_mod_cast fixedFactor_pos
  have hh := Real.logb_le_logb_of_le hZ hp hK
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hh

end SevenEighths.CenteredMomentSecondRadicalBudget

end

end OAI

end Source647

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondRetainedWidth.lean; sha256: 57e91a58c3473cf5d6ddd93b39318d03c25cd3694ec76d615313ede86a765f42 -/
section Source648
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology

namespace SevenEighths.CenteredMomentSecondRetainedWidth
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondRadicalBudget CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentCanonicalFirst
open CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem retained_geometry (R : ℝ) (G V z : O)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    0<R ∧ G≠0 ∧ V≠0 ∧ z≠0 ∧ 1≤normValue z ∧
      normValue z≤4*R/(normValue G*normValue V) ∧
      1≤4*R/(normValue G*normValue V) := by
  obtain ⟨hGV,hz⟩:=retained_product_ne_zero R (G*V) z hne
  have hg:=left_ne_zero_of_mul hGV
  have hv:=right_ne_zero_of_mul hGV
  have hrow:=retained_norm_enclosure R (G*V) z hGV hne
  rw [normValue_mul] at hrow
  have hn:=normValue_ge_one z hz
  have hr:=retainedWeight_enclosure R _ hne
  refine ⟨by linarith,hg,hv,hz,hn,hrow,hn.trans hrow⟩

theorem retained_log_budget (η τ : Character) (G V z : O) (U : Ideal O)
    (hU : U≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*U.absNorm*
      (Ideal.span {V}).absNorm)
    (R Z : ℝ) (hZ : 1<Z)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    Real.logb Z (max 1 (4*R/(normValue G*normValue V)))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue G)+
        Real.logb Z (U.absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨hR,hG,hV,_,_,_,hmax⟩:=retained_geometry R G V z hne
  have hg:=normValue_pos G hG
  have hv:=normValue_pos V hV
  have hF : (fixedFactor:ℝ)≠0:=by exact_mod_cast fixedFactor_pos.ne'
  have hc:=conductor_log_bound η τ U (Ideal.span {V}) hU
    (Ideal.span_singleton_eq_bot.not.mpr hV) hN Z hZ
  change Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
    Real.logb Z (fixedFactor:ℝ)+Real.logb Z (U.absNorm:ℝ)+Real.logb Z (normValue V) at hc
  rw [max_eq_right hmax,Real.logb_div (mul_ne_zero (by norm_num) hR.ne')
    (mul_ne_zero hg.ne' hv.ne'),Real.logb_mul (by norm_num : (4:ℝ)≠0) hR.ne',
    Real.logb_mul hg.ne' hv.ne',Real.logb_mul (by norm_num : (4:ℝ)≠0) hF]
  linarith

theorem retained_row_log_budget (η τ : Character) (G V z : O) (U : Ideal O)
    (hU : U≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*U.absNorm*
      (Ideal.span {V}).absNorm)
    (R Z : ℝ) (hZ : 1<Z)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    Real.logb Z (normValue z)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue G)+
        Real.logb Z (U.absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨_,_,_,hz,_,hn,_⟩:=retained_geometry R G V z hne
  have hh:=Real.logb_le_logb_of_le hZ (normValue_pos z hz) (hn.trans (le_max_right 1 _))
  have hb:=retained_log_budget η τ G V z U hU hN R Z hZ hne
  linarith

theorem exists_retained_width_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀hD : Supported D,CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
      ∀Z R:ℝ,1<Z → ∀z:O,
        retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0 →
        0<R ∧ z≠0 ∧ 1≤normValue z ∧
        normValue z≤4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)) ∧
        Real.logb Z (max 1 (4*R/(normValue (commonFrequencyGenerator C D)*
          normValue (nonunitFrequencyGenerator C D U))))+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) ∧
        Real.logb Z (normValue z)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨τ,he,ht,hN⟩:=exists_second_budgeted_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hw
  have hb:=hN hD hCD w hw
  refine ⟨hb,?_⟩
  intro Z R hZ z hz
  have hU : (∏P∈U,P.val)≠0:=Finset.prod_ne_zero_iff.mpr
    (fun P _=>(commonPrime_supported_ideal C D hC P).1)
  obtain ⟨hR,_,_,hne,h1,hrow,_⟩:=retained_geometry R _ _ z hz
  exact ⟨hR,hne,h1,hrow,retained_log_budget η τ _ _ z _ hU hb R Z hZ hz,
    retained_row_log_budget η τ _ _ z _ hU hb R Z hZ hz⟩

theorem fixed_width_cost_eventually (ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ:ℝ in Filter.atTop,1<Z ∧ Real.logb Z (4*(fixedFactor:ℝ))≤ε := by
  have he:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (4*(fixedFactor:ℝ))
  filter_upwards [he,Filter.eventually_gt_atTop (1:ℝ)] with Z hF hZ
  refine ⟨hZ,?_⟩
  have hp : (0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hh:=Real.logb_le_logb_of_le hZ (by positivity : 0<4*(fixedFactor:ℝ)) hF
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hh

theorem exists_uniform_retained_width_family (ε : ℝ) (hε : 0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀(η:Character)(χ:RayCharacter)(C D:Ideal O)
      (hC:Supported C)(U:Finset (CommonIndex C D)),
    ∃τ:Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀hD : Supported D,CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
      ∀Z R:ℝ,Z₀≤Z → ∀z:O,
        retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0 →
        0<R ∧ z≠0 ∧ 1≤normValue z ∧
        normValue z≤4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)) ∧
        Real.logb Z (max 1 (4*R/(normValue (commonFrequencyGenerator C D)*
          normValue (nonunitFrequencyGenerator C D U))))+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε ∧
        Real.logb Z (normValue z)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε := by
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.mp (fixed_width_cost_eventually ε hε)
  refine ⟨Z₀,(hZ₀ Z₀ le_rfl).1,?_⟩
  intro η χ C D hC U
  obtain ⟨τ,he,ht,hb⟩:=exists_retained_width_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hw
  obtain ⟨hN,hrow⟩:=hb hD hCD w hw
  refine ⟨hN,?_⟩
  intro Z R hZ z hz
  obtain ⟨hZ1,hcost⟩:=hZ₀ Z hZ
  obtain ⟨hR,hn,h1,hup,hmax,hlog⟩:=hrow Z R hZ1 z hz
  exact ⟨hR,hn,h1,hup,by linarith,by linarith⟩

end SevenEighths.CenteredMomentSecondRetainedWidth

end

end OAI

end Source648

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondLiveBlock.lean; sha256: a10f0699e68b01e68a32a8b55b9bf1d7fab7bc5fb9cd8233efd1e5a20438706c -/
section Source649
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorRetained
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
local notation "O" => HeckeFamily.O

def liveLabels (η:Character) (S:Finset (Ideal O)) (β:Ideal O→ℂ):Finset (ActiveLabel S β):=
  Finset.univ.filter (fun p=>idealCoeff η p.val.1≠0 ∧ idealCoeff η p.val.2≠0)

lemma mem_liveLabels (η:Character) (S:Finset (Ideal O)) (β:Ideal O→ℂ) (p:ActiveLabel S β):
    p∈liveLabels η S β ↔ idealCoeff η p.val.1≠0 ∧ idealCoeff η p.val.2≠0:=by
  simp only [liveLabels,Finset.mem_filter,Finset.mem_univ,true_and]

lemma common_height_zero_of_not_live (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (p:ActiveLabel S β)
    (hp:p∉liveLabels η S β):heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)=0:=by
  rw [mem_liveLabels] at hp
  push Not at hp
  by_cases hc:idealCoeff η p.val.1=0
  · simp only [heightCoeff,hc,zero_mul]
  · simp only [heightCoeff,hp hc,zero_mul,star_zero,mul_zero]

def liveRows (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O):Finset O:=
  rows.filter (fun z=>retainedWeight R
    (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0)

lemma liveRows_weight (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O)
    (z:O) (hz:z∈liveRows C D U R rows):
    retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0:=
  (Finset.mem_filter.mp hz).2

lemma liveRows_geometry (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O)
    (z:O) (hz:z∈liveRows C D U R rows):
    0<R ∧ z≠0 ∧ 1≤normValue z ∧ normValue z≤
      4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)):=by
  obtain ⟨hr,hg,hv,hz0,h1,hbound,hmax⟩:=CenteredMomentSecondRetainedWidth.retained_geometry R
    (commonFrequencyGenerator C D) (nonunitFrequencyGenerator C D U) z
    (liveRows_weight C D U R rows z hz)
  exact ⟨hr,hz0,h1,hbound⟩

lemma physicalBlock_live_rows (η:Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n:=by
  unfold physicalBlock liveRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hr:retainedWeight R
      (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))=0
  · simp only [hr,ne_eq,not_true_eq_false,physicalKernel,Complex.ofReal_zero,
      mul_zero,zero_mul,Finset.sum_const_zero,ite_self]
  · simp only [hr,ne_eq,not_false_eq_true,ite_true]

lemma physicalBlock_row_split (η:Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ) (p:O→Prop):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter p) W K n+
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter (fun z=>¬p z)) W K n:=by
  rw [physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
  unfold physicalBlock
  exact (Finset.sum_filter_add_sum_filter_not _ p _).symm

theorem original_live_blocks (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H:ℝ) (hK:0<K)
    (hH:∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H):
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
        ∑U:Finset (CommonIndex p.val.1 p.val.2),
          ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock η t (activeSource S β) β p.val.1 p.val.2
              (commonLabels_supported (activeSource S β) _ _ p.property).1
              (commonLabels_supported (activeSource S β) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (liveRows p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ)
                (retainedRows (frequencyRadius Tsec Z ξ)
                  (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)))
              W K (fun i=>(n i:ℤ)):=by
  rw [original_secondRetainedEnergy_blocks η t S β W K Tsec Z ξ H hK hH]
  trans ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (retainedRows (frequencyRadius Tsec Z ξ)
            (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
          W K (fun i=>(n i:ℤ))
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p hp hn
    rw [common_height_zero_of_not_live η t S β p hn,zero_mul]
  · apply Finset.sum_congr rfl
    intro p hp
    apply congrArg (fun x : ℂ => heightCoeff η t p.val.1 * star (heightCoeff η t p.val.2) * x)
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro n hn
    exact physicalBlock_live_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _

end SevenEighths.CenteredMomentSecondLiveBlock

end

end OAI

end Source649

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondBlockSupport.lean; sha256: ad720aefea747de0bb984de05615cd816bbd2b0a0f1e1ee727f92015276acd5f -/
section Source650
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondBlockSupport
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorFrequency CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

theorem normalizedBlock_zero_of_common (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hz:∀z∈rows,idealCorrelation C D hC hD
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z)=0) :
    normalizedBlock η t S β C D hC hD U R rows W K n=0 := by
  unfold normalizedBlock
  apply Finset.sum_eq_zero
  intro z hzr
  let F:O→Ideal O→Ideal O→ℂ:=fun _ I J=>
    wholeKernel W (fun _=>logAnnulus)
      (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
      (Real.log (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/
        dyadicScale (n 0))) (Real.log (normValue z/dyadicScale (n 1)))
      (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
      (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))
  have he:=sectorFrequency_zero_of_common η t S β C D hC hD hCD F
    ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z) (hz z hzr)
  simpa only [sectorFrequency,F,mul_zero] using congrArg (fun x:ℂ=>retainedScalar C D U R z*x) he

theorem normalizedBlock_nonzero_common (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hne:normalizedBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  by_contra hn
  push Not at hn
  apply hne
  exact normalizedBlock_zero_of_common η t S β C D hC hD hCD U R rows W K n
    (fun z hz=>by simpa only [mul_assoc] using hn z hz)

theorem physicalBlock_nonzero_common (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (hrows:∀z∈rows,z≠0)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  rw [physicalBlock_eq η t S β C D hC hD U R rows hrows W K hK n] at hne
  exact normalizedBlock_nonzero_common η t S β C D hC hD hCD U R rows W K n
    (right_ne_zero_of_mul hne)

end SevenEighths.CenteredMomentSecondBlockSupport

end

end OAI

end Source650

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondReducedPredicate.lean; sha256: d18d0f084f723a34d24de0a39db7ffe667397f48653732581643f6d524c1a360 -/
section Source651
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondReducedPredicate
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredExceptionalProfile CenteredMomentFixedRowMask CenteredMomentRestrictedEnergy
open CenteredMomentSecondFamilyTransport CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSixthReduction CenteredMomentCanonicalFirst RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem fixed_mask_change (η : Character) (Q : Ideal O) (m n A z : O)
    (hm:m≠0) (hn:n≠0) (hA:A≠0) (hz:z≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m)
    (hnLam:ConcretePrimeRowBridge.goodLambda∣n) (hn2:(2:O)∣n) :
    FixedInducingRow η Q m A z ↔ FixedInducingRow η Q n A z := by
  have h1:=fixedInducingRow_mul_mask_iff η Q m n A z hm hn hA hz hmLam hm2
  have h2:=fixedInducingRow_mul_mask_iff η Q n m A z hn hm hA hz hnLam hn2
  rw [mul_comm n m] at h2
  exact h1.symm.trans h2

theorem actual_reduced_inducing_iff (η τ : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hz:z≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [fixed_sixth_inducing_iff _ Q m z hm hz hmLam hm2 C D hC U]
  exact (fixed_mask_change (childCharacter η χ) Q m fixedBadMask (reducedNumerator C D U) z
    hm fixedBadMask_ne_zero (reducedNumerator_ne_zero C D hC U) hz hmLam hm2
    (dvd_mul_right _ _) (dvd_mul_left _ _)).trans
      (fixedInducingRow_transport η τ χ _ hτ Q z).symm

theorem actual_nonexceptional_iff (η τ : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal O) (m z:O) (hm:m≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  unfold nonexceptional
  by_cases hz:z=0
  · simp only [hz,ne_eq,not_true_eq_false,false_and]
  · rw [actual_reduced_inducing_iff η τ χ C D hC U hτ Q m z hm hz hmLam hm2]

end SevenEighths.CenteredMomentSecondReducedPredicate

end

end OAI

end Source651

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondLiveFamily.lean; sha256: f1ae1ed2b9b205b4ed43e89c4cebf5688b76acfed8ce55f67ffa692c5a2980f1 -/
section Source652
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedWidth
open CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource CenteredMomentSecondRadicalColumns
open CenteredMomentSecondReducedPredicate CenteredMomentSecondLiveBlock CenteredMomentSecondBlockSupport
open CenteredMomentSecondPhysicalBlock CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentRestrictedEnergy CenteredMomentSectorLocalization RayFourExpansion
local notation "O" => HeckeFamily.O

theorem exists_live_source_family (η:Character) (C D:Ideal O)
    (hC:Supported C) (hD:Supported D) (hCD:primeSupport C=primeSupport D)
    (U:Finset (CommonIndex C D)):
    ∃τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀t:ℝ,
        heightCoeff (τ χ) t I=heightCoeff η t I*
          idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
          rayCharacter χ (primaryGenerator I)) ∧
      (∀χ:RayCharacter,∀Q:Ideal O,∀m z:O,m≠0 →
        ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
        (nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
          z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z)) ∧
      ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
        (W:𝓢(ℝ,ℂ))(K:ℝ),0<K → ∀n:Fin 4→ℤ,
      physicalBlock η t S β C D hC hD U R rows W K n≠0 →
      ∀χ:RayCharacter,
        (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
          (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
      ∀Z:ℝ,1<Z → ∀z∈liveRows C D U R rows,
        Real.logb Z (normValue z)+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)):=by
  choose τ he ht hrest using fun χ:RayCharacter=>exists_retained_width_family η χ C D hC U
  refine ⟨τ,?_,?_,?_⟩
  · intro χ I hI hi t
    rw [ht χ I hI t]
    rcases hi with hi|hi
    · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
    · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]
  · intro χ Q m z hm hml hm2
    exact actual_nonexceptional_iff η (τ χ) χ C D hC U (he χ) Q m z hm hml hm2
  · intro t S β R rows W K hK n hne
    have hne':physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n≠0:=by
      rwa [←physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
    obtain ⟨w,hw,hwc⟩:=physicalBlock_nonzero_common η t S β C D hC hD hCD U R
      (liveRows C D U R rows) (fun z hz=>(liveRows_geometry C D U R rows z hz).2.1)
      W K hK n hne'
    intro χ
    obtain ⟨hN,hwidth⟩:=hrest χ hD hCD (nonunitFrequencyGenerator C D U*w) hwc
    refine ⟨hN,?_⟩
    intro Z hZ z hz
    exact (hwidth Z R hZ z (liveRows_weight C D U R rows z hz)).2.2.2.2.2

end SevenEighths.CenteredMomentSecondLiveFamily

end

end OAI

end Source652

/- Original source: OAI/NumberTheory/DirichletL/Moments/RetainedProfile.lean; sha256: da6726e7032ec19f14a58902119d9e219b7d1a7e0f1687b63b0fc43543fb6ebd -/
section Source653
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentRetainedProfile
open CenteredMomentLattice CenteredMomentTwist CenteredMomentHeckeTwist
open CenteredMomentHeckeHeight CenteredMomentHeckeVolume CenteredMomentHeckeCancellation HeckeFamily
open EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

def dilated (W : ℝ → ℂ) (c : ℝ) : ℝ → ℂ := fun x => W (c * x)

theorem dilated_contDiff (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (c : ℝ) :
    ContDiff ℝ ∞ (dilated W c) :=
  hW.comp (contDiff_const.mul contDiff_id)

theorem dilated_support (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) :
    Function.support (dilated W c) ⊆ Set.Icc (a / B) b := by
  intro x hx
  have hv := hs hx
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hx0 : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha hv.1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  constructor
  · apply (div_le_iff₀ hB0).mpr
    exact hv.1.trans (by nlinarith)
  · exact (show x ≤ c * x by nlinarith).trans hv.2

theorem seminorm_dilation_le (f g : 𝓢(ℝ, ℂ)) (ζ : ℂ) (c B : ℝ)
    (hζ : ‖ζ‖ = 1) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hg : ∀ x, g x = ζ * f (c * x)) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n g ≤ B ^ n * SchwartzMap.seminorm ℝ k n f := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hB0 : 0 ≤ B := hc0.trans hcB
  have he : (g : ℝ → ℂ) = fun x => ζ * f (c * x) := funext hg
  apply SchwartzMap.seminorm_le_bound' ℝ k n g (by positivity)
  intro x
  rw [he, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_smul (f.smooth n), norm_mul, hζ,
    one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0 n)]
  have hx : |x| ^ k ≤ |c * x| ^ k := by
    apply pow_le_pow_left₀ (abs_nonneg x)
    rw [abs_mul, abs_of_nonneg hc0]
    nlinarith [abs_nonneg x]
  calc
    _ = c ^ n * (|x| ^ k * ‖iteratedDeriv n f (c * x)‖) := by ring
    _ ≤ c ^ n * (|c * x| ^ k * ‖iteratedDeriv n f (c * x)‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) (pow_nonneg hc0 n)
    _ ≤ c ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm' ℝ k n f (c * x))
        (pow_nonneg hc0 n)
    _ ≤ B ^ n * SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hcB _) (apply_nonneg _ _)

theorem normPowerProfile_dilated (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    normPowerProfile (dilated W c) (a / B) b
      (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
      (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t x =
      ((c : ℂ) ^ (Complex.I * t))⁻¹ *
        normPowerProfile W a b ha hs hW t (c * x) := by
  rw [normPowerProfile_apply, normPowerProfile_apply]
  by_cases hz : W (c * x) = 0
  · simp [dilated, hz]
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hx : 0 < x := (mul_pos_iff.mp (lt_of_lt_of_le ha (hs hz).1)).resolve_right
    (by intro h; linarith [h.1]) |>.2
  have hp := Complex.mul_cpow_ofReal_nonneg hc0.le hx.le (Complex.I * t)
  rw [← Complex.ofReal_mul] at hp
  rw [hp]
  have hn : (c : ℂ) ^ (Complex.I * t) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_real_imaginary_power c t hc0]; norm_num)
  dsimp only [dilated]
  simp only [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem normPowerProfile_dilated_seminorm (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ n * SchwartzMap.seminorm ℝ k n (normPowerProfile W a b ha hs hW t) := by
  apply seminorm_dilation_le _ _ ((c : ℂ) ^ (Complex.I * t))⁻¹ c B
    (by rw [norm_inv, norm_real_imaginary_power c t (lt_of_lt_of_le zero_lt_one hc), inv_one])
    hc hcB
  intro x
  exact normPowerProfile_dilated W a b B c ha hB hc hcB hs hW t x

theorem normPowerProfile_dilated_finite (W : ℝ → ℂ) (a b B c : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (hc : 1 ≤ c) (hcB : c ≤ B)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) (F : Finset (ℕ × ℕ)) :
    F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile (dilated W c) (a / B) b
        (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
        (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
      B ^ (F.sup Prod.snd) *
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) := by
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  apply (normPowerProfile_dilated_seminorm W a b B c ha hB hc hcB hs hW t z.1 z.2).trans
  exact mul_le_mul (pow_le_pow_right₀ hB (Finset.le_sup hz))
    (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) hz) (apply_nonneg _ _) (by positivity)

theorem dilated_normPowerProfile_uniform_degree (a b B : ℝ) (ha : 0 < a)
    (hB : 1 ≤ B) (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, ∀ hc : 1 ≤ c, ∀ hcB : c ≤ B, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (normPowerProfile (dilated W c) (a / B) b
          (div_pos ha (lt_of_lt_of_le zero_lt_one hB))
          (dilated_support W a b B c ha hB hc hcB hs) (dilated_contDiff W hW c) t) ≤
        C * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := normPowerProfile_uniform_degree a b ha F
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  refine ⟨B ^ (F.sup Prod.snd) * C, mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hB) _) hC, ?_⟩
  intro c hc hcB t
  have ht : (1 + ‖t / (2 * Real.pi)‖) ^ J ≤ (1 + ‖t‖) ^ J := by
    gcongr
    exact CenteredMomentHeight.normalized_height_le t
  calc
    _ ≤ B ^ (F.sup Prod.snd) *
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) :=
      normPowerProfile_dilated_finite W a b B c ha hB hc hcB hs hW t F
    _ ≤ B ^ (F.sup Prod.snd) * (C * (1 + ‖t‖) ^ J) :=
      mul_le_mul_of_nonneg_left
        ((hbound t).trans (mul_le_mul_of_nonneg_left ht hC.le)) (by positivity)
    _ = _ := by ring

def clippedScale (S : ℝ) : ℝ := max 1 S

def clipDilation (S : ℝ) : ℝ := clippedScale S / S

theorem clippedScale_ge_one (S : ℝ) : 1 ≤ clippedScale S := le_max_left _ _

theorem clipDilation_ge_one (S : ℝ) (hS : 0 < S) : 1 ≤ clipDilation S := by
  rw [clipDilation, le_div_iff₀ hS, one_mul]
  exact le_max_right _ _

theorem clipDilation_le (b S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) :
    clipDilation S ≤ max 1 b := by
  rw [clipDilation, div_le_iff₀ hS]
  apply max_le
  · exact hret.trans (by nlinarith [le_max_right (1 : ℝ) b])
  · nlinarith [le_max_left (1 : ℝ) b]

theorem clipDilation_eq_one (S : ℝ) (hS : 1 ≤ S) : clipDilation S = 1 := by
  simp [clipDilation, clippedScale, max_eq_right hS, ne_of_gt (lt_of_lt_of_le zero_lt_one hS)]

theorem clipDilation_subunit (S : ℝ) (hS : S ≤ 1) :
    clipDilation S = 1 / S := by simp [clipDilation, clippedScale, max_eq_left hS]

theorem clipped_source (W : ℝ → ℂ) (S x : ℝ) (hS : 0 < S) :
    dilated W (clipDilation S) (x / clippedScale S) = W (x / S) := by
  have hclip : clippedScale S ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (clippedScale_ge_one S))
  unfold dilated clipDilation
  congr 1
  field_simp

theorem strict_subunit_ideal_zero (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1)
    (I : Ideal O) (hI : I ≠ 0) : W ((Ideal.absNorm I : ℝ) / S) = 0 := by
  by_contra h
  have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hu := (div_le_iff₀ hS).mp (hs h)
  nlinarith

theorem strict_subunit_sum_zero (A : Ideal O → ℂ) (hA : A 0 = 0)
    (W : ℝ → ℂ) (b S : ℝ) (hS : 0 < S)
    (hs : Function.support W ⊆ Set.Iic b) (hstrict : S * b < 1) :
    (∑' I : Ideal O, A I * W ((Ideal.absNorm I : ℝ) / S)) = 0 := by
  calc
    _ = ∑' _I : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro I
      by_cases hI : I = 0
      · rw [hI, hA, zero_mul]
      · rw [strict_subunit_ideal_zero W b S hS hs hstrict I hI, mul_zero]
    _ = 0 := tsum_zero

theorem clipped_ideal_sum (A : Ideal O → ℂ) (W : ℝ → ℂ) (S : ℝ) (hS : 0 < S) :
    (∑' I : Ideal O, A I * W ((Ideal.absNorm I : ℝ) / S)) =
      ∑' I : Ideal O, A I * dilated W (clipDilation S)
        ((Ideal.absNorm I : ℝ) / clippedScale S) := by
  apply tsum_congr
  intro I
  rw [clipped_source W S _ hS]

theorem clipped_twistedIdealSum (χ : Character) (W : ℝ → ℂ) (t S : ℝ) (hS : 0 < S) :
    twistedIdealSum χ W t S =
      twistedIdealSum χ (dilated W (clipDilation S)) t (clippedScale S) :=
  clipped_ideal_sum _ W S hS

theorem strict_subunit_twistedIdealSum_zero (χ : Character) (W : ℝ → ℂ)
    (b t S : ℝ) (hS : 0 < S) (hs : Function.support W ⊆ Set.Iic b)
    (hstrict : S * b < 1) : twistedIdealSum χ W t S = 0 := by
  apply strict_subunit_sum_zero _ _ W b S hS hs hstrict
  simp only [map_zero, zero_mul]

theorem clipped_rowTwistedSum (η : Character) (m A₀ z : O)
    (W : ℝ → ℂ) (t S : ℝ) (hS : 0 < S) :
    rowTwistedSum η m A₀ z W t S =
      rowTwistedSum η m A₀ z (dilated W (clipDilation S)) t (clippedScale S) :=
  clipped_ideal_sum _ W S hS

theorem strict_subunit_rowTwistedSum_zero (η : Character) (m A₀ z : O)
    (W : ℝ → ℂ) (b t S : ℝ) (hS : 0 < S) (hs : Function.support W ⊆ Set.Iic b)
    (hstrict : S * b < 1) : rowTwistedSum η m A₀ z W t S = 0 := by
  apply strict_subunit_sum_zero _ _ W b S hS hs hstrict
  simp only [map_zero, zero_mul]

def retainedProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  normPowerProfile (dilated W (clipDilation S)) (a / max 1 b) b
    (div_pos ha (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (dilated_support W a b (max 1 b) (clipDilation S) ha (le_max_left _ _)
      (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs)
    (dilated_contDiff W hW (clipDilation S)) t

theorem retainedProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t x : ℝ) :
    retainedProfile W a b ha hs hW S hS hret t x =
      (x : ℂ) ^ (Complex.I * t) * W (clipDilation S * x) :=
  normPowerProfile_apply _ _ _ _ _ _ _ _

theorem retainedProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) :
    Function.support (retainedProfile W a b ha hs hW S hS hret t : ℝ → ℂ) ⊆
      Set.Icc (a / max 1 b) b := by
  apply (normPowerProfile_support _ _ _ _ _ _ _).trans
  exact dilated_support W a b (max 1 b) (clipDilation S) ha (le_max_left _ _)
    (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs

theorem retainedProfile_uniform_degree (a b : ℝ) (ha : 0 < a)
    (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ S : ℝ, ∀ hS : 0 < S, ∀ hret : 1 ≤ S * b, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W a b ha hs hW S hS hret t) ≤ C * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := dilated_normPowerProfile_uniform_degree a b (max 1 b) ha (le_max_left _ _) F
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  exact ⟨C, hC, fun S hS hret t =>
    hbound (clipDilation S) (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) t⟩

theorem two_retainedProfile_uniform_degree (a₁ b₁ a₂ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (F : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ hW₁ : ContDiff ℝ ∞ W₁, ∀ hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ S₁ S₂ : ℝ, ∀ hS₁ : 0 < S₁, ∀ hS₂ : 0 < S₂,
      ∀ hret₁ : 1 ≤ S₁ * b₁, ∀ hret₂ : 1 ≤ S₂ * b₂, ∀ t : ℝ,
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ S₁ hS₁ hret₁ t) +
      F.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (retainedProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ S₂ hS₂ hret₂ t) ≤ C * (1 + ‖t‖) ^ J := by
  obtain ⟨J₁, hJ₁⟩ := retainedProfile_uniform_degree a₁ b₁ ha₁ F
  obtain ⟨J₂, hJ₂⟩ := retainedProfile_uniform_degree a₂ b₂ ha₂ F
  refine ⟨max J₁ J₂, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C₁, hC₁, hb₁⟩ := hJ₁ W₁ hs₁ hW₁
  obtain ⟨C₂, hC₂, hb₂⟩ := hJ₂ W₂ hs₂ hW₂
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro S₁ S₂ hS₁ hS₂ hret₁ hret₂ t
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have h₁ := (hb₁ S₁ hS₁ hret₁ t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_left J₁ J₂)) hC₁.le)
  have h₂ := (hb₂ S₂ hS₂ hret₂ t).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_right J₁ J₂)) hC₂.le)
  nlinarith

theorem retained_row_rectangle (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ : ℝ) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (A : ℂ) :
    A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂) =
      A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂)) := by
  rw [clipped_rowTwistedSum η m A₀ z W₁ t S₁ hS₁,
    clipped_rowTwistedSum η m A₀ z W₂ t S₂ hS₂]

theorem strict_subunit_row_rectangle_zero (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ t S₁ S₂ : ℝ) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hstrict : S₁ * b₁ < 1 ∨ S₂ * b₂ < 1) (A : ℂ) :
    A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂) = 0 := by
  rcases hstrict with h₁ | h₂
  · rw [strict_subunit_rowTwistedSum_zero η m A₀ z W₁ b₁ t S₁ hS₁ hs₁ h₁, zero_mul, mul_zero]
  · rw [strict_subunit_rowTwistedSum_zero η m A₀ z W₂ b₂ t S₂ hS₂ hs₂ h₂, mul_zero, mul_zero]

theorem two_retained_row_rectangles (η : Character) (m A₀ z : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ T₁ T₂ : ℝ)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (A : ℂ) :
    ‖A * (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
      rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ≤
      ‖A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ +
      ‖A * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
        rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ := by
  rw [mul_sub, retained_row_rectangle η m A₀ z W₁ W₂ t S₁ S₂ hS₁ hS₂ A,
    retained_row_rectangle η m A₀ z W₁ W₂ t T₁ T₂ hT₁ hT₂ A]
  exact norm_sub_le _ _

theorem two_retained_row_energies (η : Character) (m A₀ : O)
    (W₁ W₂ : ℝ → ℂ) (t S₁ S₂ T₁ T₂ : ℝ)
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (rows : Finset O) (A : O → ℂ) (w : O → ℝ) (hw : ∀ z ∈ rows, 0 ≤ w z) :
    (∑ z ∈ rows, w z * ‖A z *
      (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
        rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ^ 2) ≤
      2 * (∑ z ∈ rows, w z * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ ^ 2) +
      2 * (∑ z ∈ rows, w z * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z hz
  have hb := two_retained_row_rectangles η m A₀ z W₁ W₂ t S₁ S₂ T₁ T₂ hS₁ hS₂ hT₁ hT₂ (A z)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hnorm : ‖A z *
      (rowTwistedSum η m A₀ z W₁ t S₁ * rowTwistedSum η m A₀ z W₂ t S₂ -
        rowTwistedSum η m A₀ z W₁ t T₁ * rowTwistedSum η m A₀ z W₂ t T₂)‖ ^ 2 ≤
      2 * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ ^ 2 +
      2 * ‖A z *
        (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖ ^ 2 := by
    nlinarith [sq_nonneg
      (‖A z * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation S₁)) t (clippedScale S₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation S₂)) t (clippedScale S₂))‖ -
       ‖A z * (rowTwistedSum η m A₀ z (dilated W₁ (clipDilation T₁)) t (clippedScale T₁) *
          rowTwistedSum η m A₀ z (dilated W₂ (clipDilation T₂)) t (clippedScale T₂))‖)]
  convert mul_le_mul_of_nonneg_left hnorm (hw z hz) using 1; ring

theorem retained_volumeControl_le (Q : Ideal O) (χ : Character)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (S : ℝ) (hS : 0 < S) (hret : 1 ≤ S * b) (t : ℝ) :
    volumeControl Q χ (retainedProfile W a b ha hs hW S hS hret t) ≤
      (max 1 b) ^ (pvSeminorms.sup Prod.snd) *
        volumeControl Q χ (normPowerProfile W a b ha hs hW t) := by
  have h := normPowerProfile_dilated_finite W a b (max 1 b) (clipDilation S)
    ha (le_max_left _ _) (clipDilation_ge_one S hS) (clipDilation_le b S hS hret) hs hW t pvSeminorms
  change pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ)
    (retainedProfile W a b ha hs hW S hS hret t) ≤ _ at h
  unfold volumeControl pvControl
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ ((IdealMobiusDivisorSum.idealDivisors χ.modulus).card : ℝ) *
      (Nat.card (O ⧸ Ideal.span {fixedPeriod Q}) : ℝ) * pvConstant from
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) pvConstant_pos.le)
  convert hh using 1 <;> ring

theorem retained_volumeControl_uniform_degree (Q : Ideal O) (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      ∀ S : ℝ, ∀ hS : 0 < S, ∀ hret : 1 ≤ S * b, ∀ t : ℝ,
      volumeControl Q χ (retainedProfile W a b ha hs hW S hS hret t) ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J := by
  obtain ⟨J, hJ⟩ := volumeControl_polynomial_height Q a b ε B ha hε hB
  refine ⟨J, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hJ W hs hW
  let D := (max 1 b) ^ (pvSeminorms.sup Prod.snd)
  have hD : 0 < D := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro Z hZ χ hχ S hS hret t
  calc
    _ ≤ D * volumeControl Q χ (normPowerProfile W a b ha hs hW t) :=
      retained_volumeControl_le Q χ W a b ha hs hW S hS hret t
    _ ≤ D * (C * Z ^ ε * (1 + ‖t‖) ^ J) :=
      mul_le_mul_of_nonneg_left (hbound Z hZ χ hχ t) hD.le
    _ = _ := by ring

end SevenEighths.CenteredMomentRetainedProfile

end

end OAI

end Source653

/- Original source: OAI/NumberTheory/DirichletL/Moments/RetainedEnergy.lean; sha256: eeb0dd6dafd5fac1b7aeb570bda344613d65c2208b172828212837a4beb89fe1 -/
section Source654
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRetainedEnergy
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredMomentRetainedProfile
open CenteredMomentDivisorRawEnergy HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveSlotRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) : ℂ :=
  (Real.sqrt (X₁*X₂*∏ i,P i):ℂ)⁻¹ *
    ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
      ∏ i,rowSlot η m A z (S i) (β i) t)

def retainedPositiveRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) : ℂ :=
  positiveSlotRow η m A z (dilated W₁ (clipDilation X₁)) (dilated W₂ (clipDilation X₂))
    S β P t (clippedScale X₁) (clippedScale X₂)

omit [DecidableEq ι] in
theorem retained_rectangle_raw_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (t X₁ X₂ T : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hT : 0 < T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
      ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
        ∏ i,rowSlot η m A z (S i) (β i) t)‖^2 =
      (clippedScale X₁*clippedScale X₂/T)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  have hp : 0 < ∏ i,P i := Finset.prod_pos (fun i _ => hP i)
  have hc₁ : 0 < clippedScale X₁ := zero_lt_one.trans_le (clippedScale_ge_one _)
  have hc₂ : 0 < clippedScale X₂ := zero_lt_one.trans_le (clippedScale_ge_one _)
  unfold retainedPositiveRow positiveSlotRow
  rw [normalized_norm_sq _ (mul_pos hT hp),normalized_norm_sq _ (mul_pos (mul_pos hc₁ hc₂) hp),
    clipped_rowTwistedSum η m A z W₁ t X₁ hX₁,clipped_rowTwistedSum η m A z W₂ t X₂ hX₂]
  field_simp [hp.ne',hT.ne',hc₁.ne',hc₂.ne']

omit [DecidableEq ι] in
theorem centered_to_retained_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hT : 0 < T) :
    ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2 ≤
      2*(clippedScale X₁*clippedScale X₂/T)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2+
      2*(clippedScale Y₁*clippedScale Y₂/T)*‖retainedPositiveRow η m A z W₁ W₂ S β P t Y₁ Y₂‖^2 := by
  let F (U V : ℝ) : ℂ := (Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
    ((rowTwistedSum η m A z W₁ t U*rowTwistedSum η m A z W₂ t V)*
      ∏ i,rowSlot η m A z (S i) (β i) t)
  have he : centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T=F X₁ X₂-F Y₁ Y₂ := by
    unfold centeredSlotRow F
    ring
  rw [he]
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (F X₁ X₂) (F Y₁ Y₂)) 2
  have hn : ‖F X₁ X₂-F Y₁ Y₂‖^2 ≤ 2*‖F X₁ X₂‖^2+2*‖F Y₁ Y₂‖^2 := by
    nlinarith [sq_nonneg (‖F X₁ X₂‖-‖F Y₁ Y₂‖)]
  have hx := retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t X₁ X₂ T hX₁ hX₂ hT
  have hy := retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t Y₁ Y₂ T hY₁ hY₂ hT
  change ‖F X₁ X₂‖^2=_ at hx
  change ‖F Y₁ Y₂‖^2=_ at hy
  rw [hx,hy] at hn
  convert hn using 1 ; ring

omit [DecidableEq ι] in
theorem centered_to_retained_weighted_energy (η : Character) (m A : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hT : 0 < T)
    (rows : Finset O) (ω : O → ℝ) (hω : ∀ z∈rows,0 ≤ ω z) :
    (∑ z∈rows,ω z*‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2) ≤
      2*(clippedScale X₁*clippedScale X₂/T)*
        (∑ z∈rows,ω z*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2)+
      2*(clippedScale Y₁*clippedScale Y₂/T)*
        (∑ z∈rows,ω z*‖retainedPositiveRow η m A z W₁ W₂ S β P t Y₁ Y₂‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z hz
  have hh := mul_le_mul_of_nonneg_left
    (centered_to_retained_energy η m A z W₁ W₂ S β P hP t X₁ X₂ Y₁ Y₂ T
      hX₁ hX₂ hY₁ hY₂ hT) (hω z hz)
  convert hh using 1 ; ring

omit [DecidableEq ι] in
theorem retained_rectangle_uniform_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (b₁ b₂ t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 ≤
      (max 1 b₁*max 1 b₂)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  have hB : 0 ≤ max 1 b₁*max 1 b₂ := mul_nonneg
    (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_left _ _))
  by_cases h₁ : X₁*b₁ < 1
  · unfold positiveSlotRow
    rw [strict_subunit_rowTwistedSum_zero η m A z W₁ b₁ t X₁ hX₁ hs₁ h₁,zero_mul,zero_mul,mul_zero,norm_zero,zero_pow (by decide)]
    exact mul_nonneg hB (sq_nonneg _)
  by_cases h₂ : X₂*b₂ < 1
  · unfold positiveSlotRow
    rw [strict_subunit_rowTwistedSum_zero η m A z W₂ b₂ t X₂ hX₂ hs₂ h₂,mul_zero,zero_mul,mul_zero,norm_zero,zero_pow (by decide)]
    exact mul_nonneg hB (sq_nonneg _)
  have hr : clippedScale X₁*clippedScale X₂/(X₁*X₂) ≤ max 1 b₁*max 1 b₂ := by
    have h := mul_le_mul (clipDilation_le b₁ X₁ hX₁ (le_of_not_gt h₁))
      (clipDilation_le b₂ X₂ hX₂ (le_of_not_gt h₂))
      (zero_le_one.trans (clipDilation_ge_one _ hX₂)) (zero_le_one.trans (le_max_left _ _))
    simpa only [clipDilation,div_mul_div_comm] using h
  unfold positiveSlotRow
  rw [retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t X₁ X₂ (X₁*X₂) hX₁ hX₂ (mul_pos hX₁ hX₂)]
  exact mul_le_mul_of_nonneg_right hr (sq_nonneg _)

omit [DecidableEq ι] in
theorem centered_to_retained_uniform_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (b₁ b₂ t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2 ≤
      2*(max 1 b₁*max 1 b₂)*
        (‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2+
         ‖retainedPositiveRow η m A z W₁ W₂ S β P t Y₁ Y₂‖^2) := by
  have he : centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T =
      positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂-
      positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂ := by
    unfold centeredSlotRow positiveSlotRow
    rw [hX,hY]
    ring
  rw [he]
  have hx := retained_rectangle_uniform_energy η m A z W₁ W₂ S β P hP b₁ b₂ t X₁ X₂ hX₁ hX₂ hs₁ hs₂
  have hy := retained_rectangle_uniform_energy η m A z W₁ W₂ S β P hP b₁ b₂ t Y₁ Y₂ hY₁ hY₂ hs₁ hs₂
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le
    (positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂)
    (positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂)) 2
  nlinarith [sq_nonneg (‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖-
    ‖positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂‖)]

end SevenEighths.CenteredMomentRetainedEnergy

end

end OAI

end Source654

/- Original source: OAI/NumberTheory/DirichletL/Moments/DivisorFullMask.lean; sha256: 977bf1ecf0010e105e7fe032d956358ced5f0b34ef6165681464daf3477d40ce -/
section Source655
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorFullMask
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O

 theorem annular_hasFiniteSupport (W : ℝ → ℂ) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b) :
    (fun I : Ideal O => W ((Ideal.absNorm I:ℝ)/X)).HasFiniteSupport := by
  apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil (b*X))).subset
  intro I hI
  have hn := (div_le_iff₀ hX).mp (hs hI)
  exact_mod_cast hn.trans (Nat.le_ceil (b*X))

theorem rectangle_hasFiniteSupport (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (fun v : Ideal O × Ideal O => idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ v.1 v.2).HasFiniteSupport := by
  have h₁ := (annular_hasFiniteSupport W₁ b₁ X₁ hX₁ hW₁).union
    (annular_hasFiniteSupport W₁ b₁ Y₁ hY₁ hW₁)
  have h₂ := (annular_hasFiniteSupport W₂ b₂ X₂ hX₂ hW₂).union
    (annular_hasFiniteSupport W₂ b₂ Y₂ hY₂ hW₂)
  apply (h₁.prod h₂).subset
  intro v hv
  constructor
  · by_contra hn
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
    exact hv (by simp only [idealRectangle,hn.1,hn.2,zero_mul,sub_self])
  · by_contra hn
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
    exact hv (by simp only [idealRectangle,hn.1,hn.2,mul_zero,sub_self])

theorem rectangle_tsum_sum {α : Type*} [Fintype α]
    (f : α → Ideal O → Ideal O → ℂ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O,∑' J : Ideal O,
      ∑ a, f a I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      ∑ a,∑' I : Ideal O,∑' J : Ideal O,f a I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J := by
  have hs (a : α) : Summable (fun v : Ideal O × Ideal O =>
      f a v.1 v.2*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ v.1 v.2) :=
    summable_of_hasFiniteSupport ((rectangle_hasFiniteSupport W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
      hW₁ hW₂ hX₁ hX₂ hY₁ hY₂).mul_right _)
  have hi (I : Ideal O) := Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) => (hs a).prod_factor I)
  simp_rw [hi]
  exact Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) => (hs a).prod)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem factorTuple_product (v : ι → Ideal O) (I J : Ideal O) :
    (∏ i,factorTuple v I J i)=(∏ i,v i)*I*J := by
  rw [Fintype.prod_sum_type,Fin.prod_univ_two]
  simp only [factorTuple,Sum.elim_inl,Sum.elim_inr,ite_true,
    show (1:Fin 2) ≠ 0 by decide,ite_false,mul_assoc]

theorem full_mask_eq_allocated_rectangles (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (D : Ideal O) (hD : Squarefree D)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑ v : (i : ι) → S i,(∏ i,β i (v i))*
      ∑' I : Ideal O,∑' J : Ideal O,
        (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ := by
  have he (v : (i : ι) → S i) (I J : Ideal O) :
      (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0) =
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a := by
    rw [← factorTuple_product]
    exact squarefree_mask_allocation D hD Finset.univ _
  simp_rw [he,Finset.sum_mul]
  simp_rw [rectangle_tsum_sum _ W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

end SevenEighths.CenteredMomentDivisorFullMask

end

end OAI

end Source655

/- Original source: OAI/NumberTheory/DirichletL/Moments/DivisorRowEnergy.lean; sha256: 9b06f4c2c421df0e354aab78e610cf4a1cd84c465525ae8c693512f141954c59 -/
section Source656
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorRowEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRows CenteredMomentDivisorFullMask
open CenteredMomentDivisorEnergy CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def maskedRectangle (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (D : Ideal O)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑ v : (i : ι) → S i,(∏ i,β i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J

theorem actual_allocated_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
      (D : Ideal O),Squarefree D → ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z ∈ rows,0 ≤ ω z) →
      (∑ z ∈ rows,ω z*‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
            ∑ z ∈ rows,ω z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
  obtain ⟨C,hC,hcard⟩ := allocation_card_small_power (ι := ι ⊕ Fin 2) (N+2) (by omega) ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows ω hω
  have hc : (Finset.univ : Finset (ι ⊕ Fin 2)).card ≤ N+2 := by
    simpa only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hslots 2
  have hrow (z : O) :
      ‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
        (Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
          ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
            ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
    unfold maskedRectangle
    rw [full_mask_eq_allocated_rectangles η m A z t S β D hD W₁ W₂ b₁ b₂
      _ _ _ _ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂]
    calc
      _ ≤ (∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun _a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)) => (1:ℝ))
          (fun a => ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖))
  calc
    _ ≤ ∑ z ∈ rows,ω z*((Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) :=
      Finset.sum_le_sum (fun z hz => mul_le_mul_of_nonneg_left (hrow z) (hω z hz))
    _ = (Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))):ℝ)*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ∑ z ∈ rows,ω z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
      simp_rw [mul_left_comm (ω _) _,Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD.ne_zero Finset.univ hc)
      (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun z hz => mul_nonneg (hω z hz) (sq_nonneg _))))

end SevenEighths.CenteredMomentDivisorRowEnergy

end

end OAI

end Source656

/- Original source: OAI/NumberTheory/DirichletL/Moments/DivisorRetained.lean; sha256: 9024fe3c9be0db0fe98c02b5781abbceae4de8e8c02a946feab11c98d711b7b1 -/
section Source657
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentRetainedEnergy CenteredMomentDivisorRowEnergy HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def allocatedPositiveRow (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) : ℂ :=
  retainedPositiveRow η m A z W₁ W₂ (fun i : liveIndices D a => S i)
    (fun i : liveIndices D a => β i) (fun i : liveIndices D a => P i) t
    (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))

theorem allocated_to_retained_energy (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M P : ι → ℝ) (hM : ∀ i,0 ≤ M i) (hP : ∀ i,0 < P i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
      (2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P *
        (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
         ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have hN (j : Fin 2) : (0:ℝ) < Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  have hx : (X₁/Ideal.absNorm (selectedPlain D a 0))*(X₂/Ideal.absNorm (selectedPlain D a 1))=
      T/selectedNorm D a := by rw [div_mul_div_comm,hX]; rfl
  have hy : (Y₁/Ideal.absNorm (selectedPlain D a 0))*(Y₂/Ideal.absNorm (selectedPlain D a 1))=
      T/selectedNorm D a := by rw [div_mul_div_comm,hY]; rfl
  have hr := allocated_raw_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hT
  have hc := centered_to_retained_uniform_energy η m A z W₁ W₂
    (fun i : liveIndices D a => S i) (fun i : liveIndices D a => β i)
    (fun i : liveIndices D a => P i) (fun i => hP i) b₁ b₂ t _ _ _ _ _
    (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1)) (div_pos hY₁ (hN 0)) (div_pos hY₂ (hN 1))
    hx hy hW₁ hW₂
  have hF : 0 < formalReductionFactor D a P := mul_pos (selectedNorm_pos D a)
    (Finset.prod_pos (fun i _ => hP i))
  have hh := mul_le_mul_of_nonneg_left hc (div_nonneg (sq_nonneg (∏ i∈frozenIndices D a,M i)) hF.le)
  apply hr.trans
  convert hh using 1 <;> simp only [residualCenteredRow,allocatedPositiveRow] ; ring

theorem masked_raw_to_retained_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)),(∀ i,∀ I∈S i,Prime I) →
      ∀ (β : ι → Ideal O → ℂ) (M P : ι → ℝ),(∀ i,0 ≤ M i) → (∀ i,0 < P i) →
      (∀ i,∀ I∈S i,‖β i I‖ ≤ M i) → ∀ (D : Ideal O),Squarefree D →
      ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z∈rows,0 ≤ ω z) →
      (∑ z∈rows,ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
      C*(Ideal.absNorm D:ℝ)^ε*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P)*
          ∑ z∈rows,ω z*
            (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
             ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  obtain ⟨C,hC,hbase⟩ := actual_allocated_energy (ι := ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S hS β M P hM hP hβ D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY rows ω hω
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hh := hbase η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows (fun z => ω z/(T*∏ i,P i))
    (fun z hz => div_nonneg (hω z hz) htotal.le)
  have he (z : O) (x : ℂ) : (ω z/(T*∏ i,P i))*‖x‖^2 =
      ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*x‖^2 := by
    rw [normalized_norm_sq _ htotal]
    ring
  simp_rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hb := mul_le_mul_of_nonneg_left
    (allocated_to_retained_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
      b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY) (hω z hz)
  convert hb using 1 ; ring

end SevenEighths.CenteredMomentDivisorRetained

end

end OAI

end Source657

/- Original source: OAI/NumberTheory/DirichletL/Moments/DivisorBoundary.lean; sha256: 0553b106a29103eb034ffb9a9252a981f4f4a84aa1189d14ed259bbb34945294 -/
section Source658
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorBoundary
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def frozenSlots (D : Ideal O) (s slots : Finset ι) (a : Allocation D s) : Finset ι :=
  slots.filter (fun i => (selectedPrimes D s a i).Nonempty)

def extractedProduct (D : Ideal O) (s plain slots : Finset ι) (a : Allocation D s)
    (v : ι → Ideal O) : Ideal O :=
  (∏ i ∈ plain,selectedDivisor D s a i)*(∏ i ∈ frozenSlots D s slots a,v i)

theorem divisor_dvd_extractedProduct (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0) :
    D∣extractedProduct D s plain slots a v := by
  apply (squarefree_dvd_iff _ _ hD).mpr
  intro P hP
  let PP : primeSupport D := ⟨P,hP⟩
  have hne : (a PP).val.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (Finset.mem_erase.mp (a PP).property).1
  obtain ⟨i,hi⟩ := hne
  have his : i ∈ s := (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (a PP).property)) hi
  have hip : PP ∈ selectedPrimes D s a i := Finset.mem_filter.mpr ⟨Finset.mem_univ PP,hi⟩
  rcases Finset.mem_union.mp (hs his) with hp | hslot
  · apply dvd_mul_of_dvd_left
    exact (Finset.dvd_prod_of_mem (fun Q : primeSupport D => (Q:Ideal O)) hip).trans
      (Finset.dvd_prod_of_mem (fun i => selectedDivisor D s a i) hp)
  · apply dvd_mul_of_dvd_right
    exact (selected_divides_factor D s v a hn PP i hi).trans
      (Finset.dvd_prod_of_mem v (Finset.mem_filter.mpr ⟨hslot,⟨PP,hip⟩⟩))

theorem extractedProduct_ne_zero (D : Ideal O) (s plain slots : Finset ι)
    (a : Allocation D s) (v : ι → Ideal O) (hv : ∀ i ∈ slots,v i ≠ 0) :
    extractedProduct D s plain slots a v ≠ 0 :=
  mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => selectedDivisor_ne_zero D s a i))
    (Finset.prod_ne_zero_iff.mpr (fun i hi => hv i (Finset.mem_filter.mp hi).1))

theorem actual_divisor_norm_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) :
    Ideal.absNorm D ≤ (∏ i ∈ plain,Ideal.absNorm (selectedDivisor D s a i))*
      (∏ i ∈ frozenSlots D s slots a,Ideal.absNorm (v i)) := by
  have hd := divisor_dvd_extractedProduct D hD s plain slots hs a v hn
  have hnorm := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (extractedProduct_ne_zero D s plain slots a v hv))) (map_dvd Ideal.absNorm hd)
  simpa only [extractedProduct,map_mul,map_prod] using hnorm

theorem actual_divisor_log_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤
      (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
      (∑ i ∈ frozenSlots D s slots a,Real.logb Z (Ideal.absNorm (v i):ℝ)) := by
  have hnorm : (Ideal.absNorm D:ℝ) ≤
      (∏ i ∈ plain,(Ideal.absNorm (selectedDivisor D s a i):ℝ))*
      (∏ i ∈ frozenSlots D s slots a,(Ideal.absNorm (v i):ℝ)) := by
    exact_mod_cast actual_divisor_norm_boundary D hD s plain slots hs a v hn hv
  have hp (i : ι) : (Ideal.absNorm (selectedDivisor D s a i):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (selectedDivisor_ne_zero D s a i))
  have hq (i : ι) (hi : i ∈ frozenSlots D s slots a) : (Ideal.absNorm (v i):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i (Finset.mem_filter.mp hi).1))
  have hh := Real.logb_le_logb_of_le hZ (show (0:ℝ)<Ideal.absNorm D by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)) hnorm
  rw [Real.logb_mul (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
    (Finset.prod_ne_zero_iff.mpr hq), Real.logb_prod _ _ (fun i _ => hp i),
    Real.logb_prod _ _ hq] at hh
  exact hh

def formalReduction (D : Ideal O) (s plain slots : Finset ι) (a : Allocation D s)
    (P : ι → ℝ) (Z : ℝ) : ℝ :=
  (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
    ∑ i ∈ frozenSlots D s slots a,Real.logb Z (P i)

def frozenRatio (D : Ideal O) (s slots : Finset ι) (a : Allocation D s)
    (v : ι → Ideal O) (P : ι → ℝ) (Z : ℝ) : ℝ :=
  ∑ i ∈ frozenSlots D s slots a,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)

theorem formal_reduction_add_ratio (D : Ideal O) (s plain slots : Finset ι)
    (a : Allocation D s) (v : ι → Ideal O) (hv : ∀ i ∈ slots,v i ≠ 0)
    (P : ι → ℝ) (hP : ∀ i ∈ slots,0 < P i) (Z : ℝ) :
    formalReduction D s plain slots a P Z+frozenRatio D s slots a v P Z =
      (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
      (∑ i ∈ frozenSlots D s slots a,Real.logb Z (Ideal.absNorm (v i):ℝ)) := by
  unfold formalReduction frozenRatio
  rw [add_assoc,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have his := (Finset.mem_filter.mp hi).1
  rw [Real.logb_div (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i his))) (hP i his).ne']
  ring

theorem actual_formal_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) (P : ι → ℝ) (hP : ∀ i ∈ slots,0 < P i)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤
      formalReduction D s plain slots a P Z+frozenRatio D s slots a v P Z := by
  rw [formal_reduction_add_ratio D s plain slots a v hv P hP Z]
  exact actual_divisor_log_boundary D hD s plain slots hs a v hn hv Z hZ

theorem divisor_dyad_card (Ds : Finset (Ideal O)) (T : ℝ) (hT : 1 ≤ T)
    (hD : ∀ D ∈ Ds,D ≠ 0) (hN : ∀ D ∈ Ds,(Ideal.absNorm D:ℝ) < 2*T) :
    (Ds.card:ℝ) ≤ 256*T := by
  have h := DescentFiberCost.finite_ideal_count_real Ds (2*T) (by linarith) hD
    (fun D hD => (hN D hD).le)
  linarith

theorem paired_raw_divisor_bound (Ds : Finset (Ideal O)) (T Z θ : ℝ)
    (hT : 1 ≤ T) (hZ : 1 < Z) (r₁ r₂ w₁ w₂ : Ideal O → ℝ)
    (hD : ∀ D ∈ Ds,D ≠ 0)
    (hlo : ∀ D ∈ Ds,T ≤ (Ideal.absNorm D:ℝ))
    (hhi : ∀ D ∈ Ds,(Ideal.absNorm D:ℝ) < 2*T)
    (hleft : ∀ D ∈ Ds,Real.logb Z (Ideal.absNorm D:ℝ) ≤ r₁ D+w₁ D)
    (hright : ∀ D ∈ Ds,Real.logb Z (Ideal.absNorm D:ℝ) ≤ r₂ D+w₂ D)
    (hw : ∀ D ∈ Ds,w₁ D+w₂ D ≤ 2*θ) :
    (∑ D ∈ Ds,Z^(-(r₁ D+r₂ D)/2)) ≤ 256*Z^θ := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have he (D : Ideal O) (hmem : D ∈ Ds) : Z^(-(r₁ D+r₂ D)/2) ≤ Z^θ/T := by
    have hn := Real.logb_le_logb_of_le hZ hT0 (hlo D hmem)
    have h₁ := hleft D hmem
    have h₂ := hright D hmem
    have hω := hw D hmem
    have hh : -(r₁ D+r₂ D)/2 ≤ θ-Real.logb Z T := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hh
    rw [Real.rpow_sub hZ0,Real.rpow_logb hZ0 hZ.ne' hT0] at hpow
    exact hpow
  calc
    _ ≤ ∑ _D ∈ Ds,Z^θ/T := Finset.sum_le_sum (fun D hD => he D hD)
    _ = (Ds.card:ℝ)*(Z^θ/T) := by simp
    _ ≤ (256*T)*(Z^θ/T) := mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT hD hhi) (by positivity)
    _ = _ := by field_simp

end SevenEighths.CenteredMomentDivisorBoundary

end

end OAI

end Source658

/- Original source: OAI/NumberTheory/DirichletL/Moments/SlotRatios.lean; sha256: 4f815851713cffccfa3a3369fe221d610272780b9766c349763a7e2f88925fa4 -/
section Source659
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def logWindow (a b : ℝ) : ℝ := max |Real.log a| |Real.log b|

theorem logWindow_nonneg (a b : ℝ) : 0 ≤ logWindow a b :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem slot_log_ratio_bound (W : ℝ → ℂ) (a b P Z : ℝ) (I : Ideal O)
    (ha : 0 < a) (hZ : 1 < Z)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hW : W ((Ideal.absNorm I:ℝ)/P) ≠ 0) :
    |Real.logb Z ((Ideal.absNorm I:ℝ)/P)| ≤ logWindow a b/Real.log Z := by
  have hw := hs hW
  have hr : 0 < (Ideal.absNorm I:ℝ)/P := ha.trans_le hw.1
  have hlow := Real.log_le_log ha hw.1
  have hhigh := Real.log_le_log hr hw.2
  have habs : |Real.log ((Ideal.absNorm I:ℝ)/P)| ≤ logWindow a b := by
    apply abs_le.mpr
    constructor
    · have h := neg_abs_le (Real.log a)
      have hm := le_max_left |Real.log a| |Real.log b|
      dsimp only [logWindow]
      linarith
    · exact hhigh.trans ((le_abs_self _).trans (le_max_right _ _))
  rw [Real.logb,abs_div,abs_of_pos (Real.log_pos hZ)]
  exact div_le_div_of_nonneg_right habs (Real.log_pos hZ).le

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem frozen_subset_ratio_bound (entrance frozen : Finset ι) (hsub : frozen ⊆ entrance)
    (W : ι → ℝ → ℂ) (a b P : ι → ℝ) (v : ι → Ideal O) (Z : ℝ) (hZ : 1 < Z)
    (ha : ∀ i ∈ entrance,0 < a i)
    (hs : ∀ i ∈ entrance,Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hW : ∀ i ∈ frozen,W i ((Ideal.absNorm (v i):ℝ)/P i) ≠ 0) :
    |∑ i ∈ frozen,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)| ≤
      (∑ i ∈ entrance,logWindow (a i) (b i))/Real.log Z := by
  calc
    _ ≤ ∑ i ∈ frozen,|Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ frozen,logWindow (a i) (b i)/Real.log Z :=
      Finset.sum_le_sum (fun i hi => slot_log_ratio_bound (W i) (a i) (b i) (P i) Z (v i)
        (ha i (hsub hi)) hZ (hs i (hsub hi)) (hW i hi))
    _ = (∑ i ∈ frozen,logWindow (a i) (b i))/Real.log Z := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => logWindow_nonneg (a i) (b i))) (Real.log_pos hZ).le

theorem disjoint_frozen_ratio_bound (entrance old fresh : Finset ι)
    (hold : old ⊆ entrance) (hfresh : fresh ⊆ entrance) (hdis : Disjoint old fresh)
    (W : ι → ℝ → ℂ) (a b P : ι → ℝ) (v : ι → Ideal O) (Z : ℝ) (hZ : 1 < Z)
    (ha : ∀ i ∈ entrance,0 < a i)
    (hs : ∀ i ∈ entrance,Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hW : ∀ i ∈ old ∪ fresh,W i ((Ideal.absNorm (v i):ℝ)/P i) ≠ 0) :
    |(∑ i ∈ old,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i))+
      (∑ i ∈ fresh,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i))| ≤
      (∑ i ∈ entrance,logWindow (a i) (b i))/Real.log Z := by
  rw [← Finset.sum_union hdis]
  exact frozen_subset_ratio_bound entrance (old ∪ fresh) (Finset.union_subset hold hfresh)
    W a b P v Z hZ ha hs hW

end SevenEighths.CenteredMomentSlotRatios

end

end OAI

end Source659

/- Original source: OAI/NumberTheory/DirichletL/Moments/DivisorWitness.lean; sha256: 4b8ee71779cc145a32d7e21c5567cae4c1777cf6bfc101e9e045c417901dec56 -/
section Source660
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorWitness
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentHeckeExpansion
open CenteredMomentRectangle HeckeFamily IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_tsum_term {α : Type*} (f : α → ℂ) (h : (∑' x,f x) ≠ 0) :
    ∃ x,f x ≠ 0 := by
  by_contra hn
  push Not at hn
  exact h (by simp only [hn,tsum_zero])

theorem allocated_nonzero_witness (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ)
    (hne : allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    ∃ (v : (i : ι) → S i) (I J : Ideal O),
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a ≠ 0 ∧
      (∀ i,β i (v i) ≠ 0) ∧ idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J ≠ 0 := by
  obtain ⟨v,_,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hβ,ht⟩ := mul_ne_zero_iff.mp hv
  obtain ⟨I,hI⟩ := exists_tsum_term _ ht
  obtain ⟨J,hJ⟩ := exists_tsum_term _ hI
  have hh := mul_ne_zero_iff.mp hJ
  exact ⟨v,I,J,(mul_ne_zero_iff.mp hh.1).1,
    fun i => Finset.prod_ne_zero_iff.mp hβ i (Finset.mem_univ i),hh.2⟩

def actualExtracted (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) : Ideal O :=
  (selectedPlain D a 0*selectedPlain D a 1)*∏ i∈frozenIndices D a,v i

private theorem prime_dvd_selectedPlain (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (j : Fin 2) (P : primeSupport D)
    (hP : P ∈ selectedPrimes D Finset.univ a (Sum.inr j)) :
    (P : Ideal O) ∣ selectedPlain D a j := by
  exact Finset.dvd_prod_of_mem (fun q : primeSupport D => (q : Ideal O))
    (a := P) (s := selectedPrimes D Finset.univ a (Sum.inr j)) hP

theorem divisor_dvd_actualExtracted (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (I J : Ideal O)
    (hn : allocationTerm D Finset.univ (factorTuple v I J) a ≠ 0) :
    D ∣ actualExtracted D a v := by
  apply (squarefree_dvd_iff D _ hD).mpr
  intro P hP
  let PP : primeSupport D := ⟨P,hP⟩
  obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp (a PP).property).1
  have hmem : PP ∈ selectedPrimes D Finset.univ a i :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ PP,hi⟩
  cases i with
  | inl i =>
      have hfr : i ∈ frozenIndices D a := Finset.mem_filter.mpr ⟨Finset.mem_univ i,⟨PP,hmem⟩⟩
      have hd : P∣v i := selected_divides_factor D Finset.univ (factorTuple v I J) a hn PP (Sum.inl i) hi
      exact dvd_mul_of_dvd_right (hd.trans (Finset.dvd_prod_of_mem v (a := i) (s := frozenIndices D a) hfr)) _
  | inr j =>
      have hd : P∣selectedPlain D a j := prime_dvd_selectedPlain D a j PP hmem
      fin_cases j
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _

theorem actualExtracted_ne_zero (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) : actualExtracted D a v ≠ 0 :=
  mul_ne_zero (mul_ne_zero (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hv i))

theorem actualExtracted_norm_boundary (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) (I J : Ideal O)
    (hn : allocationTerm D Finset.univ (factorTuple v I J) a ≠ 0) :
    (Ideal.absNorm D:ℝ) ≤ selectedNorm D a*∏ i∈frozenIndices D a,(Ideal.absNorm (v i):ℝ) := by
  have h := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (actualExtracted_ne_zero D a v hv))) (map_dvd Ideal.absNorm (divisor_dvd_actualExtracted D hD a v I J hn))
  simpa only [actualExtracted,map_mul,map_prod,Nat.cast_mul,Nat.cast_prod,selectedNorm] using
    (show (Ideal.absNorm D:ℝ) ≤ Ideal.absNorm (actualExtracted D a v) by exact_mod_cast h)

end SevenEighths.CenteredMomentDivisorWitness

end

end OAI

end Source660

/- Original source: OAI/NumberTheory/DirichletL/Moments/DivisorActualBoundary.lean; sha256: 97bc26355960afce8f27b7bd3b6e185900f07695b4c0daf5cc75e6bff38c5cf8 -/
section Source661
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorActualBoundary
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentDivisorRaw CenteredMomentDivisorWitness CenteredMomentSlotRatios HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem selected_log_identity (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) (P : ι → ℝ) (hP : ∀ i,0 < P i) (Z : ℝ) :
    Real.logb Z (selectedNorm D a*∏ i∈frozenIndices D a,(Ideal.absNorm (v i:Ideal O):ℝ)) =
      Real.logb Z (formalReductionFactor D a P)+
        ∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i) := by
  have hn (i : ι) : (Ideal.absNorm (v i:Ideal O):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i))
  unfold formalReductionFactor
  rw [Real.logb_mul (selectedNorm_pos D a).ne' (Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)),
    Real.logb_mul (selectedNorm_pos D a).ne' (Finset.prod_ne_zero_iff.mpr (fun i _ => (hP i).ne')),
    Real.logb_prod _ _ (fun i _ => hn i),Real.logb_prod _ _ (fun i _ => (hP i).ne')]
  simp_rw [Real.logb_div (hn _) (hP _).ne']
  rw [Finset.sum_sub_distrib]
  ring

theorem nonzero_row_formal_boundary (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (hβW : ∀ i I,β i I ≠ 0 → W i ((Ideal.absNorm I:ℝ)/P i) ≠ 0)
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hne : allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
  obtain ⟨v,I,J,ha,hβ,hrect⟩ := allocated_nonzero_witness η m A z t S β D a
    W₁ W₂ X₁ X₂ Y₁ Y₂ hne
  have hv (i : ι) : (v i:Ideal O) ≠ 0 := (hS i (v i) (v i).property).ne_zero
  have hb := actualExtracted_norm_boundary D hD a (fun i => v i) hv I J ha
  have hND : (0:ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hl := Real.logb_le_logb_of_le hZ hND hb
  rw [selected_log_identity D a (fun i => v i) hv P hP Z] at hl
  have hr : |∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i)| ≤
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
    apply frozen_subset_ratio_bound (ι := ι) Finset.univ (frozenIndices D a) (Finset.subset_univ _)
      W lo hi P (fun i => (v i:Ideal O)) Z hZ
    · intro i _
      exact hlo i
    · intro i _
      exact hW i
    · intro i _
      exact hβW i (v i) (hβ i)
  have hh := (le_abs_self (∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i))).trans hr
  linarith

theorem original_nonzero_row_formal_boundary (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (ν : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hne : allocatedRectangle η m A z t S
      (fun i I => ν i I*W i ((Ideal.absNorm I:ℝ)/P i)) D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z :=
  nonzero_row_formal_boundary η m A z t S hS _ W lo hi P hlo hP hW
    (fun _i _I h => (mul_ne_zero_iff.mp h).2) D hD a W₁ W₂ X₁ X₂ Y₁ Y₂ Z hZ hne

end SevenEighths.CenteredMomentDivisorActualBoundary

end

end OAI

end Source661

/- Original source: OAI/NumberTheory/DirichletL/Moments/ActiveAllocation.lean; sha256: 017a5415a78dbedfe7a0d66731dd1a0900cb3e8534077892af92922fd3cd5956 -/
section Source662
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentActiveAllocation
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentRetainedEnergy CenteredMomentDivisorRowEnergy CenteredMomentDivisorRetained
open CenteredMomentSlotRatios CenteredMomentDivisorActualBoundary CenteredMomentDivisorRectangle
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def activeAllocations (η:Character) (m A:O) (t:ℝ) (S:ι→Finset (Ideal O))
    (β:ι→Ideal O→ℂ) (D:Ideal O) (W₁ W₂:ℝ→ℂ) (X₁ X₂ Y₁ Y₂:ℝ) :
    Finset (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :=
  Finset.univ.filter (fun a=>∃z:O,allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂≠0)

theorem inactive_zero (η:Character) (m A:O) (t:ℝ) (S:ι→Finset (Ideal O))
    (β:ι→Ideal O→ℂ) (D:Ideal O) (W₁ W₂:ℝ→ℂ) (X₁ X₂ Y₁ Y₂:ℝ)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (ha:a∉activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂) (z:O) :
    allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂=0 := by
  by_contra hn
  exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,z,hn⟩)

theorem masked_eq_active_allocations (η:Character) (m A z:O) (t:ℝ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (D:Ideal O) (hD:Squarefree D)
    (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂) :
    maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂=
      ∑a∈activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂,
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ := by
  unfold maskedRectangle
  rw [CenteredMomentDivisorFullMask.full_mask_eq_allocated_rectangles η m A z t S β D hD
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂]
  symm
  exact Finset.sum_subset (Finset.subset_univ _) (fun a _ ha=>inactive_zero η m A t S β D
    W₁ W₂ X₁ X₂ Y₁ Y₂ a ha z)

theorem active_allocated_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
      (D : Ideal O),Squarefree D → ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z ∈ rows,0 ≤ ω z) →
      (∑ z ∈ rows,ω z*‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a ∈ activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂,
            ∑ z ∈ rows,ω z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
  obtain ⟨C,hC,hbase⟩:=actual_allocated_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ rows ω hω
  apply (hbase η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ rows ω hω).trans_eq
  congr 1
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a ha hn
  simp only [inactive_zero η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂ a hn,norm_zero,zero_pow (by norm_num:2≠0),mul_zero,Finset.sum_const_zero]

theorem active_raw_to_retained_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)),(∀ i,∀ I∈S i,Prime I) →
      ∀ (β : ι → Ideal O → ℂ) (M P : ι → ℝ),(∀ i,0 ≤ M i) → (∀ i,0 < P i) →
      (∀ i,∀ I∈S i,‖β i I‖ ≤ M i) → ∀ (D : Ideal O),Squarefree D →
      ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z∈rows,0 ≤ ω z) →
      (∑ z∈rows,ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
      C*(Ideal.absNorm D:ℝ)^ε*
        ∑ a ∈ activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂,
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P)*
          ∑ z∈rows,ω z*
            (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
             ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  obtain ⟨C,hC,hbase⟩ := active_allocated_energy (ι := ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S hS β M P hM hP hβ D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY rows ω hω
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hh := hbase η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows (fun z => ω z/(T*∏ i,P i))
    (fun z hz => div_nonneg (hω z hz) htotal.le)
  have he (z : O) (x : ℂ) : (ω z/(T*∏ i,P i))*‖x‖^2 =
      ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*x‖^2 := by
    rw [normalized_norm_sq _ htotal]
    ring
  simp_rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hb := mul_le_mul_of_nonneg_left
    (allocated_to_retained_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
      b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY) (hω z hz)
  convert hb using 1 ; ring

theorem active_formal_boundary (η : Character) (m A : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (ν : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hactive : a∈activeAllocations η m A t S
      (fun i I => ν i I*W i ((Ideal.absNorm I:ℝ)/P i)) D W₁ W₂ X₁ X₂ Y₁ Y₂) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
  obtain ⟨z,hz⟩:=(Finset.mem_filter.mp hactive).2
  exact original_nonzero_row_formal_boundary η m A z t S hS ν W lo hi P hlo hP hW
    D hD a W₁ W₂ X₁ X₂ Y₁ Y₂ Z hZ hz

end SevenEighths.CenteredMomentActiveAllocation

end

end OAI

end Source662

/- Original source: OAI/NumberTheory/DirichletL/Moments/ActiveDivisorShell.lean; sha256: 585491404d857a603ec977f901d20c225cb2670b95990cfe702565eadcbbf0f9 -/
section Source663
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentActiveDivisorShell
open HeckeFamily CenteredMomentActiveAllocation CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentDivisorBoundary CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

structure Source (ι:Type*) [Fintype ι] where
  η : Character
  m : O
  A : O
  t : ℝ
  slots : ι→Finset (Ideal O)
  prime : ∀i,∀I∈slots i,Prime I
  ν : ι→Ideal O→ℂ
  W : ι→ℝ→ℂ
  lo : ι→ℝ
  hi : ι→ℝ
  P : ι→ℝ
  lo_pos : ∀i,0<lo i
  P_pos : ∀i,0<P i
  support : ∀i,Function.support (W i)⊆Set.Icc (lo i) (hi i)
  W₁ : ℝ→ℂ
  W₂ : ℝ→ℂ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Source.active (s:Source ι) (D:Ideal O) : Finset (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :=
  activeAllocations s.η s.m s.A s.t s.slots
    (fun i I=>s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)) D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

def Source.allowance (s:Source ι) (Z:ℝ) : ℝ :=
  (∑i,logWindow (s.lo i) (s.hi i))/Real.log Z

theorem Source.active_boundary (s:Source ι) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (ha:a∈s.active D) (Z:ℝ) (hZ:1<Z) :
    Real.logb Z (Ideal.absNorm D:ℝ)≤Real.logb Z (formalReductionFactor D a s.P)+s.allowance Z :=
  active_formal_boundary s.η s.m s.A s.t s.slots s.prime s.ν s.W s.lo s.hi s.P s.lo_pos s.P_pos
    s.support D hD a s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ Z hZ ha

theorem reciprocal_sqrt_log (Z x y:ℝ) (hZ:1<Z) (hx:0<x) (hy:0<y) :
    1/Real.sqrt (x*y)=Z^(-(Real.logb Z x+Real.logb Z y)/2) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  calc
    _=(x*y)^(-(1/2:ℝ)):=by rw [Real.sqrt_eq_rpow,one_div,Real.rpow_neg (mul_nonneg hx.le hy.le)]
    _=(Z^(Real.logb Z x+Real.logb Z y))^(-(1/2:ℝ)):=by
      rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hx,Real.rpow_logb hz hZ.ne' hy]
    _=_:=by rw [←Real.rpow_mul hz.le]; congr 1; ring

theorem Source.active_pair_weight {κ:Type*} [Fintype κ] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (ha:a∈s.active D) (hb:b∈v.active D) (Z:ℝ) (hZ:1<Z) :
    1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P)≤
      Z^((s.allowance Z+v.allowance Z)/2)/(Ideal.absNorm D:ℝ) := by
  have hs:0<formalReductionFactor D a s.P:=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))
  have hv:0<formalReductionFactor D b v.P:=
    mul_pos (selectedNorm_pos D b) (Finset.prod_pos (fun i _=>v.P_pos i))
  have hn:0<(Ideal.absNorm D:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  rw [reciprocal_sqrt_log Z _ _ hZ hs hv]
  have hl:=s.active_boundary D hD a ha Z hZ
  have hr:=v.active_boundary D hD b hb Z hZ
  have he:-(Real.logb Z (formalReductionFactor D a s.P)+Real.logb Z (formalReductionFactor D b v.P))/2≤
      (s.allowance Z+v.allowance Z)/2-Real.logb Z (Ideal.absNorm D:ℝ):=by linarith
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le he
  rwa [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn] at hp

theorem paired_active_divisor_shell {κ:Type*} [Fintype κ] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (Ds:Finset (Ideal O))
    (a:∀D:Ideal O,Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:∀D:Ideal O,Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (hD:∀D∈Ds,Squarefree D) (ha:∀D∈Ds,a D∈s.active D) (hb:∀D∈Ds,b D∈v.active D)
    (T Z:ℝ) (hT:1≤T) (hZ:1<Z)
    (hlo:∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) (hhi:∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) :
    (∑D∈Ds,1/Real.sqrt (formalReductionFactor D (a D) s.P*formalReductionFactor D (b D) v.P))≤
      256*Z^((s.allowance Z+v.allowance Z)/2) := by
  have hs (D:Ideal O):0<formalReductionFactor D (a D) s.P:=
    mul_pos (selectedNorm_pos D (a D)) (Finset.prod_pos (fun i _=>s.P_pos i))
  have hv (D:Ideal O):0<formalReductionFactor D (b D) v.P:=
    mul_pos (selectedNorm_pos D (b D)) (Finset.prod_pos (fun i _=>v.P_pos i))
  simp_rw [reciprocal_sqrt_log Z _ _ hZ (hs _) (hv _)]
  apply paired_raw_divisor_bound Ds T Z ((s.allowance Z+v.allowance Z)/2) hT hZ
    (fun D=>Real.logb Z (formalReductionFactor D (a D) s.P))
    (fun D=>Real.logb Z (formalReductionFactor D (b D) v.P))
    (fun _=>s.allowance Z) (fun _=>v.allowance Z)
    (fun D hd=>(hD D hd).ne_zero) hlo hhi
    (fun D hd=>s.active_boundary D (hD D hd) (a D) (ha D hd) Z hZ)
    (fun D hd=>v.active_boundary D (hD D hd) (b D) (hb D hd) Z hZ)
  intro D hd
  linarith

theorem paired_all_active_shell {κ:Type*} [Fintype κ] [DecidableEq κ]
    (N:ℕ) (hι:Fintype.card ι≤N) (hκ:Fintype.card κ≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Source ι) (v:Source κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((s.allowance Z+v.allowance Z)/2) := by
  obtain ⟨C₁,hC₁,hcard₁⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  obtain ⟨C₂,hC₂,hcard₂⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=κ⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨256*C₁*C₂,by positivity,?_⟩
  intro s v Ds hD T Z hT hZ hlo hhi
  have ht:0<T:=zero_lt_one.trans_le hT
  have hz:0<Z:=zero_lt_one.trans hZ
  let θ:ℝ:=(s.allowance Z+v.allowance Z)/2
  have hc₁ (D:Ideal O) (hd:D∈Ds):( (s.active D).card:ℝ)≤C₁*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((s.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₁ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hc₂ (D:Ideal O) (hd:D∈Ds):( (v.active D).card:ℝ)≤C₂*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((v.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (κ⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₂ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hp (D:Ideal O) (hd:D∈Ds):
      (∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
      (C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T):=by
    have hn:0<(Ideal.absNorm D:ℝ):=ht.trans_le (hlo D hd)
    have he:((Ideal.absNorm D:ℝ)^ε)*((Ideal.absNorm D:ℝ)^ε)=(Ideal.absNorm D:ℝ)^(2*ε):=by
      rw [←Real.rpow_add hn]; congr 1; ring
    have hpow:(Ideal.absNorm D:ℝ)^(2*ε)≤(2*T)^(2*ε):=
      Real.rpow_le_rpow hn.le (hhi D hd).le (by positivity)
    calc
      _≤∑_a∈s.active D,∑_b∈v.active D,Z^θ/(Ideal.absNorm D:ℝ):=
        Finset.sum_le_sum (fun a ha=>Finset.sum_le_sum (fun b hb=>s.active_pair_weight v D (hD D hd) a b ha hb Z hZ))
      _=((s.active D).card:ℝ)*((v.active D).card:ℝ)*(Z^θ/(Ideal.absNorm D:ℝ)):=by simp;ring
      _≤(C₁*(Ideal.absNorm D:ℝ)^ε)*(C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^θ/(Ideal.absNorm D:ℝ)):=
        mul_le_mul_of_nonneg_right (mul_le_mul (hc₁ D hd) (hc₂ D hd) (by positivity) (by positivity)) (by positivity)
      _=(C₁*C₂)*(Ideal.absNorm D:ℝ)^(2*ε)*(Z^θ/(Ideal.absNorm D:ℝ)):=by rw [←he];ring
      _≤(C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T):=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity))
          (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) ht (hlo D hd)) (by positivity) (by positivity)
  calc
    _≤∑_D∈Ds,(C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T):=Finset.sum_le_sum hp
    _=(Ds.card:ℝ)*((C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T)):=by simp
    _≤(256*T)*((C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T)):=
      mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT (fun D hd=>(hD D hd).ne_zero) hhi) (by positivity)
    _=(256*C₁*C₂)*(2*T)^(2*ε)*Z^θ:=by field_simp

end SevenEighths.CenteredMomentActiveDivisorShell

end

end OAI

end Source663

/- Original source: OAI/NumberTheory/DirichletL/Moments/UniformDivisorShell.lean; sha256: e1cca22cd758f6cec24f72cef3be7aea8d82aa97ddc8166b10a5e77421e4643b -/
section Source664
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentUniformDivisorShell
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def ShellBound (ι κ:Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C ε:ℝ) : Prop := ∀(s:Source ι) (v:Source κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((s.allowance Z+v.allowance Z)/2)

theorem uniform_subset_shell {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀J L:Finset ι,ShellBound J L C ε := by
  have he (p:Finset ι×Finset ι):∃C:ℝ,0<C ∧ ShellBound p.1 p.2 C ε:=
    paired_all_active_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B:ℝ:=1+∑p:Finset ι×Finset ι,C p
  have hs:0≤∑p:Finset ι×Finset ι,C p:=Finset.sum_nonneg (fun p _=>(hC p).le)
  have hB:0<B:=by dsimp [B];linarith
  refine ⟨B,hB,?_⟩
  intro J L s v Ds hD T Z hT hZ hlo hhi
  have hc:C (J,L)≤B:=by
    have hp:=Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]
    linarith
  exact (hbound (J,L) s v Ds hD T Z hT hZ hlo hhi).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _))

theorem subset_allowance {ι:Type*} [Fintype ι] [DecidableEq ι]
    (J:Finset ι) (s:Source J) (lo hi:ι→ℝ) (hlo:∀i:J,s.lo i=lo i) (hhi:∀i:J,s.hi i=hi i)
    (Z:ℝ) (hZ:1<Z) : s.allowance Z≤(∑i,logWindow (lo i) (hi i))/Real.log Z := by
  unfold Source.allowance
  simp_rw [hlo,hhi]
  rw [Finset.sum_coe_sort J (fun i:ι=>logWindow (lo i) (hi i))]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hZ).le
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>logWindow_nonneg _ _)

theorem paired_entrance_allowance {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀(J L:Finset ι) (s:Source J) (v:Source L)
      (lo hi:ι→ℝ), (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((∑i,logWindow (lo i) (hi i))/Real.log Z) := by
  obtain ⟨C,hC,hbound⟩:=uniform_subset_shell (ι:=ι) ε hε
  refine ⟨C,hC,?_⟩
  intro J L s v lo hi hslo hshi hvlo hvhi Ds hD T Z hT hZ hlo hhi
  apply (hbound J L s v Ds hD T Z hT hZ hlo hhi).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hs:=subset_allowance J s lo hi hslo hshi Z hZ
  have hv:=subset_allowance L v lo hi hvlo hvhi Z hZ
  linarith

theorem numerical_allowance (Z H:ℝ) (hZ:1<Z) : Z^(H/Real.log Z)=Real.exp H := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
  congr 1
  field_simp [(Real.log_pos hZ).ne']

theorem paired_shell_subpower {ι:Type*} [Fintype ι] [DecidableEq ι]
    (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀(J L:Finset ι) (s:Source J) (v:Source L),
      (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z → T≤Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤C*Z^δ := by
  let ε:ℝ:=δ/(2*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  have he:2*B*ε≤δ:=by
    have hh:ε*(2*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩:=paired_entrance_allowance (ι:=ι) ε hε
  let E:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(2*ε)*E,by dsimp [E];positivity,?_⟩
  intro J L s v hslo hshi hvlo hvhi Ds hD T Z hT hZ hTZ hlo hhi
  have ht:0<T:=zero_lt_one.trans_le hT
  have hz:0<Z:=zero_lt_one.trans hZ
  have hh:=hbound J L s v lo hi hslo hshi hvlo hvhi Ds hD T Z hT hZ hlo hhi
  rw [numerical_allowance Z _ hZ,Real.mul_rpow (by norm_num:0≤(2:ℝ)) ht.le] at hh
  have hpow:T^(2*ε)≤Z^δ:=by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith [he]
  apply hh.trans
  calc
    C*(2^(2*ε)*T^(2*ε))*E=(C*2^(2*ε)*E)*T^(2*ε):=by ring
    _≤(C*2^(2*ε)*E)*Z^δ:=mul_le_mul_of_nonneg_left hpow (by dsimp [E];positivity)

end SevenEighths.CenteredMomentUniformDivisorShell

end

end OAI

end Source664

/- Original source: OAI/NumberTheory/DirichletL/Moments/EligibleEnergy.lean; sha256: a7d6b9ec985e26a4f8918d4a4fa48f3145540cacbc400350fc3b39dd8dacbb45 -/
section Source665
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEligibleEnergy
open HeckeFamily CenteredMomentActiveDivisorShell CenteredMomentActiveAllocation
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorRowEnergy
local notation "O" => ActualEisensteinCubic.O

structure Data (ι:Type*) [Fintype ι] extends Source ι where
  M : ι→ℝ
  M_ge_one : ∀i,1≤M i
  coefficient_bound : ∀i,∀I∈slots i,‖ν i I*W i ((Ideal.absNorm I:ℝ)/P i)‖≤M i
  b₁ : ℝ
  b₂ : ℝ
  support₁ : Function.support W₁⊆Set.Iic b₁
  support₂ : Function.support W₂⊆Set.Iic b₂
  X₁_pos : 0<X₁
  X₂_pos : 0<X₂
  Y₁_pos : 0<Y₁
  Y₂_pos : 0<Y₂
  same_product : Y₁*Y₂=X₁*X₂
  rows : Finset O
  weight : O→ℝ
  weight_nonneg : ∀z∈rows,0≤weight z

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Data.coefficient (s:Data ι) (i:ι) (I:Ideal O) : ℂ :=
  s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)

def Data.energy (s:Data ι) (D:Ideal O) : ℝ :=
  ∑z∈s.rows,s.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂‖^2

def Data.childEnergy (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : ℝ :=
  ∑z∈s.rows,s.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)

def Data.profileFactor (s:Data ι) : ℝ :=
  (2*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2

lemma Data.energy_nonneg (s:Data ι) (D:Ideal O) : 0≤s.energy D :=
  Finset.sum_nonneg (fun z hz=>mul_nonneg (s.weight_nonneg z hz) (sq_nonneg _))

lemma Data.child_nonneg (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0≤s.childEnergy D a :=
  Finset.sum_nonneg (fun z hz=>mul_nonneg (s.weight_nonneg z hz) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

omit [DecidableEq ι] in
lemma Data.profile_nonneg (s:Data ι) : 0≤s.profileFactor :=by
  unfold Data.profileFactor
  exact mul_nonneg (by positivity) (sq_nonneg _)

lemma Data.reduction_pos (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0<formalReductionFactor D a s.P :=
  mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))

theorem actual_source_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀s:Data ι,∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,s.childEnergy D a≤E) →
      s.energy D≤C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P := by
  obtain ⟨C,hC,hbound⟩:=active_raw_to_retained_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s D hD E hE hchild
  have hh:=hbound s.η s.m s.A s.t s.slots s.prime s.coefficient s.M s.P
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound D hD s.W₁ s.W₂
    s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos rfl s.same_product s.rows s.weight s.weight_nonneg
  change s.energy D≤_ at hh
  apply hh.trans
  calc
    _≤C*(Ideal.absNorm D:ℝ)^ε*∑a∈s.toSource.active D,
        (s.profileFactor/formalReductionFactor D a s.P)*E:=by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      apply Finset.sum_le_sum
      intro a ha
      have hp:(∏i∈frozenIndices D a,s.M i)≤∏i,s.M i:=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
      apply mul_le_mul _ (hchild a ha) (s.child_nonneg D a) _
      · apply div_le_div_of_nonneg_right _ (s.reduction_pos D a).le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))) hp 2
      · exact div_nonneg s.profile_nonneg (s.reduction_pos D a).le
    _=_:=by
      simp only [div_eq_mul_inv,one_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

lemma sqrt_sum_le {α:Type*} (S:Finset α) (f:α→ℝ) (hf:∀a∈S,0≤f a) :
    Real.sqrt (∑a∈S,f a)≤∑a∈S,Real.sqrt (f a) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun a _=>Real.sqrt_nonneg _),?_⟩
  have hh:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=S) (f:=fun a=>Real.sqrt (f a))
    (fun a _=>Real.sqrt_nonneg _)
  have he:(∑a∈S,Real.sqrt (f a)^2)=∑a∈S,f a:=Finset.sum_congr rfl (fun a ha=>Real.sq_sqrt (hf a ha))
  rwa [he] at hh

lemma sqrt_reciprocal (x:ℝ) (_hx:0<x) : Real.sqrt (1/x)=1/Real.sqrt x := by
  rw [Real.sqrt_div (by norm_num:0≤(1:ℝ)),Real.sqrt_one]

theorem actual_source_root_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀s:Data ι,∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,s.childEnergy D a≤E) →
      Real.sqrt (s.energy D)≤C*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)*Real.sqrt (s.profileFactor*E)*
        ∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P) := by
  obtain ⟨C,hC,hbase⟩:=actual_source_from_children (ι:=ι) N hslots ε hε
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  intro s D hD E hE hc
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he:0≤s.profileFactor*E:=mul_nonneg s.profile_nonneg hE
  have hs:=sqrt_sum_le (s.toSource.active D) (fun a=>1/formalReductionFactor D a s.P)
    (fun a _=>div_nonneg zero_le_one (s.reduction_pos D a).le)
  simp_rw [sqrt_reciprocal _ (s.reduction_pos D _)] at hs
  have hh:=Real.sqrt_le_sqrt (hbase s D hD E hE hc)
  have hrew:C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)=
      (C*(Ideal.absNorm D:ℝ)^ε*(s.profileFactor*E))*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P):=by ring
  rw [hrew,Real.sqrt_mul (mul_nonneg (mul_nonneg hC.le hp) he),
    Real.sqrt_mul (mul_nonneg hC.le hp),Real.sqrt_mul hC.le] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hs (by positivity))

end SevenEighths.CenteredMomentEligibleEnergy

end

end OAI

end Source665

/- Original source: OAI/NumberTheory/DirichletL/Moments/PairedEligibleEnergy.lean; sha256: 75edeeada2bb71f4a97cdf51ac7560e34f15cf3e90f2cc91b3bad47e4e944056 -/
section Source666
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPairedEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => ActualEisensteinCubic.O

lemma reciprocal_sums {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (D:Ideal O) :
    (∑a∈s.active D,1/Real.sqrt (formalReductionFactor D a s.P))*
      (∑b∈v.active D,1/Real.sqrt (formalReductionFactor D b v.P))=
    ∑a∈s.active D,∑b∈v.active D,
      1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hf:0≤formalReductionFactor D a s.P:=
    (mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))).le
  rw [Real.sqrt_mul hf]
  ring

theorem actual_paired_source_shell {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (N:ℕ) (hι:Fintype.card ι≤N) (hκ:Fintype.card κ≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (v:Data κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀(E₁ E₂ T Z:ℝ),0≤E₁ → 0≤E₂ → 1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*(2*T)^(3*ε)*Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)*
          (Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)) := by
  obtain ⟨C₁,hC₁,hl⟩:=actual_source_root_from_children (ι:=ι) N hι ε hε
  obtain ⟨C₂,hC₂,hr⟩:=actual_source_root_from_children (ι:=κ) N hκ ε hε
  obtain ⟨C₃,hC₃,hshell⟩:=paired_all_active_shell (ι:=ι) (κ:=κ) N hι hκ ε hε
  refine ⟨C₁*C₂*C₃,by positivity,?_⟩
  intro s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  let W:ℝ:=Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)
  let θ:ℝ:=(s.toSource.allowance Z+v.toSource.allowance Z)/2
  let F:Ideal O→ℝ:=fun D=>∑a∈s.toSource.active D,∑b∈v.toSource.active D,
    1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P)
  have hW:0≤W:=mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hF (D:Ideal O):0≤F D:=Finset.sum_nonneg (fun a _=>Finset.sum_nonneg
    (fun b _=>div_nonneg zero_le_one (Real.sqrt_nonneg _)))
  have ht:0<T:=zero_lt_one.trans_le hT
  have hp (D:Ideal O) (hd:D∈Ds):Real.sqrt (s.energy D)*Real.sqrt (v.energy D)≤
      (C₁*C₂)*(2*T)^ε*W*F D:=by
    have hn:0<(Ideal.absNorm D:ℝ):=ht.trans_le (hlo D hd)
    have hpow:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg hn.le _
    have hmul:=mul_le_mul (hl s D (hD D hd) E₁ hE₁ (hleft D hd))
      (hr v D (hD D hd) E₂ hE₂ (hright D hd)) (Real.sqrt_nonneg _) (by positivity)
    apply hmul.trans
    calc
      _=(C₁*C₂)*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)^2*W*
          ((∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P))*
           (∑b∈v.toSource.active D,1/Real.sqrt (formalReductionFactor D b v.P))):=by dsimp [W];ring
      _=(C₁*C₂)*(Ideal.absNorm D:ℝ)^ε*W*F D:=by
        rw [Real.sq_sqrt hpow,reciprocal_sums]
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn.le (hhi D hd).le hε.le) (by positivity)) hW) (hF D)
  calc
    _≤∑D∈Ds,(C₁*C₂)*(2*T)^ε*W*F D:=Finset.sum_le_sum hp
    _=((C₁*C₂)*(2*T)^ε*W)*(∑D∈Ds,F D):=(Finset.mul_sum ..).symm
    _≤((C₁*C₂)*(2*T)^ε*W)*(C₃*(2*T)^(2*ε)*Z^θ):=
      mul_le_mul_of_nonneg_left (hshell s.toSource v.toSource Ds hD T Z hT hZ hlo hhi) (by positivity)
    _=(C₁*C₂*C₃)*(2*T)^(3*ε)*Z^θ*W:=by
      have hpow:(2*T)^ε*(2*T)^(2*ε)=(2*T)^(3*ε):=by
        rw [←Real.rpow_add (by positivity:0<2*T)];congr 1;ring
      calc
        _=(C₁*C₂*C₃)*((2*T)^ε*(2*T)^(2*ε))*Z^θ*W:=by ring
        _=_:=by rw [hpow]

end SevenEighths.CenteredMomentPairedEligibleEnergy

end

end OAI

end Source666

/- Original source: OAI/NumberTheory/DirichletL/Moments/UniformEligibleEnergy.lean; sha256: 4bfb83de41452b76739a16871a135e221ac874bddb2d993bf430fb75d52e22f5 -/
section Source667
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentUniformEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentPairedEligibleEnergy
open CenteredMomentUniformDivisorShell CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def Bound (ι κ:Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (C ε:ℝ) : Prop :=
  ∀(s:Data ι) (v:Data κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀(E₁ E₂ T Z:ℝ),0≤E₁ → 0≤E₂ → 1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*(2*T)^(3*ε)*Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)*
          (Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂))

theorem uniform_subset_energy {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀J L:Finset ι,Bound J L C ε := by
  have he (p:Finset ι×Finset ι):∃C:ℝ,0<C ∧ Bound p.1 p.2 C ε:=
    actual_paired_source_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B:ℝ:=1+∑p:Finset ι×Finset ι,C p
  have hs:0≤∑p:Finset ι×Finset ι,C p:=Finset.sum_nonneg (fun p _=>(hC p).le)
  have hB:0<B:=by dsimp [B];linarith
  refine ⟨B,hB,?_⟩
  intro J L s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  have hc:C (J,L)≤B:=by
    have hp:=Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]
    linarith
  exact (hbound (J,L) s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg (by linarith) _)) (by positivity))

theorem actual_source_shell_subpower {ι:Type*} [Fintype ι] [DecidableEq ι]
    (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀(J L:Finset ι) (s:Data J) (v:Data L),
      (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀E₁ E₂ T Z:ℝ,
      0≤E₁ → 0≤E₂ → 1≤T → 1<Z → T≤Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*Z^δ*(Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)) := by
  let ε:ℝ:=δ/(3*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  have he:3*B*ε≤δ:=by
    have hh:ε*(3*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩:=uniform_subset_energy (ι:=ι) ε hε
  let E:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(3*ε)*E,by dsimp [E];positivity,?_⟩
  intro J L s v hslo hshi hvlo hvhi Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hTZ hlo hhi hleft hright
  have ht:0<T:=zero_lt_one.trans_le hT
  have hz:0<Z:=zero_lt_one.trans hZ
  have hs:=subset_allowance J s.toSource lo hi hslo hshi Z hZ
  have hv:=subset_allowance L v.toSource lo hi hvlo hvhi Z hZ
  have hnum:Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)≤E:=by
    dsimp [E]
    rw [←numerical_allowance Z _ hZ]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  have hh:=hbound J L s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply (mul_le_mul_of_nonneg_left hnum (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))).trans
  rw [Real.mul_rpow (by norm_num:0≤(2:ℝ)) ht.le]
  have hp:T^(3*ε)≤Z^δ:=by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith [he]
  calc
    C*(2^(3*ε)*T^(3*ε))*E=(C*2^(3*ε)*E)*T^(3*ε):=by ring
    _≤(C*2^(3*ε)*E)*Z^δ:=mul_le_mul_of_nonneg_left hp (by dsimp [E];positivity)

end SevenEighths.CenteredMomentUniformEligibleEnergy

end

end OAI

end Source667

/- Original source: OAI/NumberTheory/DirichletL/Moments/AbsoluteEnergy.lean; sha256: 36cfa538becc649184d1f4b312b01c23008d7c84c5aa1540c9212a40f32de49a -/
section Source668
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentAbsoluteEnergy
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open ConcreteTraceCRT EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_norm_le_one_all (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) : ‖rowWeight η m A z t I‖ ≤ 1 := by
  by_cases hI : I=0
  · subst I
    rw [map_zero,norm_zero]
    norm_num
  · exact CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A z t I hI

theorem radial_norm_summable (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ‖Φ (‖eisEmbedding z‖^2/K)‖) := by
  simpa only [scaledRadialTest_apply] using
    actual_eisenstein_summable_norm (scaledRadialTest Φ K hK)

theorem radial_weight_lattice_bound_all (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O, ‖Φ (‖eisEmbedding z‖^2/K)‖) ≤ diagonalControl Φ*max 1 K := by
  by_cases hlarge : 1≤K
  · simpa only [max_eq_right hlarge] using radial_weight_lattice_bound Φ K hlarge
  have hsmall : K≤1 := (not_le.mp hlarge).le
  let B := 4*(Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have hB : 0≤B := by dsimp [B]; positivity
  have hp (z : O) : ‖Φ (‖eisEmbedding z‖^2/K)‖ ≤
      B*((1+1*‖eisEmbedding z‖^2)^2)⁻¹ := by
    have hq : 0≤‖eisEmbedding z‖^2/K := div_nonneg (sq_nonneg _) hK.le
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2,0)) (k := 2) (n := 0) le_rfl le_rfl Φ (‖eisEmbedding z‖^2/K)
    simp only [norm_iteratedFDeriv_zero,Real.norm_of_nonneg hq] at hh
    norm_num only [show (2:ℝ)^2=4 by norm_num] at hh
    change (1+‖eisEmbedding z‖^2/K)^2*‖Φ (‖eisEmbedding z‖^2/K)‖≤B at hh
    have hq' : ‖eisEmbedding z‖^2≤‖eisEmbedding z‖^2/K := by
      apply (le_div_iff₀ hK).mpr
      exact mul_le_of_le_one_right (sq_nonneg _) hsmall
    have hden : (1+1*‖eisEmbedding z‖^2)^2≤(1+‖eisEmbedding z‖^2/K)^2 := by
      simp only [one_mul]
      gcongr
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hden (norm_nonneg _)).trans hh
  have hb := (radial_norm_summable Φ K hK).tsum_le_tsum hp
    ((scaled_eisenstein_cauchy_summable 1 (by norm_num)).mul_left B)
  rw [tsum_mul_left] at hb
  have hc := scaled_eisenstein_cauchy_small 1 (by norm_num) (by norm_num)
  simp only [one_mul] at hc hb
  have ht := hb.trans (mul_le_mul_of_nonneg_left hc hB)
  rw [max_eq_left hsmall,mul_one]
  dsimp only [B] at ht
  unfold diagonalControl
  nlinarith

theorem finite_hecke_polynomial_norm (η : Character) (m A z : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) :
    ‖∑ I∈S,c I*rowWeight η m A z t I‖ ≤ ∑ I∈S,‖c I‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t I)

theorem finite_hecke_energy_summable (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
      Φ (‖eisEmbedding z‖^2/K)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun z : O => (∑ I∈S,‖c I‖)^2*‖Φ (‖eisEmbedding z‖^2/K)‖)
  · intro z
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (finite_hecke_polynomial_norm η m A z t S c) 2)
      (norm_nonneg _)
  · exact (radial_norm_summable Φ K hK).mul_left _

theorem finite_hecke_energy_absolute (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    ‖finiteHeckeEnergy η m A t S c Φ K‖ ≤
      diagonalControl Φ*max 1 K*(∑ I∈S,‖c I‖)^2 := by
  have hs := (finite_hecke_energy_summable η m A t S c Φ K hK).norm
  calc
    _ ≤ ∑' z : O, ‖((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
        Φ (‖eisEmbedding z‖^2/K)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' z : O,(∑ I∈S,‖c I‖)^2*‖Φ (‖eisEmbedding z‖^2/K)‖ := by
      apply hs.tsum_le_tsum _ ((radial_norm_summable Φ K hK).mul_left _)
      intro z
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (finite_hecke_polynomial_norm η m A z t S c) 2)
        (norm_nonneg _)
    _ = (∑ I∈S,‖c I‖)^2*(∑' z : O,‖Φ (‖eisEmbedding z‖^2/K)‖) := tsum_mul_left
    _ ≤ (∑ I∈S,‖c I‖)^2*(diagonalControl Φ*max 1 K) :=
      mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) (sq_nonneg _)
    _ = _ := by ring

theorem smooth_subset_source_absolute_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple J)) (K : ℝ),0<K →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let E := finiteHeckeEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K
      ‖E‖≤C*max 1 K*H^2 ∧ ‖E‖/H≤C*max 1 K*H := by
  obtain ⟨D,hD,hm⟩ := smooth_subset_source_mass_uniform F Wslot W₁ W₂ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  let C := (diagonalControl Φ+1)*D^2
  have hd := diagonalControl_nonneg Φ
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S K hK H E
  have hmass := (hm J hJ 1 one_ne_zero 1 R 0 ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S).2
  have hmass' : (∑ I∈finiteColumns S,‖finiteColumnCoefficient S
      (profileCoefficient R (fun j : J => ν j.val) (fun j : J => Wslot j.val)
        (fun j : J => P j.val) W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I‖)≤D*H := by
    simpa only [finiteColumnCoefficient,profileCoefficient_eq_original,H,mul_assoc] using hmass
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hNB₁ : 0<(Ideal.absNorm B₁:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hNB₂ : 0<(Ideal.absNorm B₂:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  have hprod : 0<∏ j∈J,P j := Finset.prod_pos hP
  have hH : 0<H := by dsimp only [H]; positivity
  have hmax : 0≤max 1 K := le_trans zero_le_one (le_max_left _ _)
  have he : ‖E‖≤C*max 1 K*H^2 := by
    apply (finite_hecke_energy_absolute η m A t (finiteColumns S) _ Φ K hK).trans
    calc
      _ ≤ diagonalControl Φ*max 1 K*(D*H)^2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hmass' 2)
          (mul_nonneg hd hmax)
      _ ≤ (diagonalControl Φ+1)*max 1 K*(D*H)^2 := by gcongr; linarith
      _ = C*max 1 K*H^2 := by dsimp only [C]; ring
  refine ⟨he,?_⟩
  apply (div_le_iff₀ hH).mpr
  convert he using 1; ring

end SevenEighths.CenteredMomentAbsoluteEnergy

end

end OAI

end Source668

/- Original source: OAI/NumberTheory/DirichletL/Moments/PositiveSummability.lean; sha256: 5e9c587aa2b23ffa17600f0c50cd207d058dfb80d39175900ba835778d9d43e5 -/
section Source669
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentPositiveSummability
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentSourceMass
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile CenteredMomentDivisorRetained
open CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction CenteredMomentDivisorAllocation
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O

lemma plain_finite_norm (η:Character) (m A z:O) (t:ℝ) (W:ℝ→ℂ) (b X:ℝ)
    (hs:Function.support W⊆Set.Iic b) (hX:0<X) :
    ‖rowTwistedSum η m A z W t X‖≤∑I∈idealBall (b*X),‖W ((Ideal.absNorm I:ℝ)/X)‖ := by
  rw [rowTwistedSum_eq_weight,tsum_eq_sum (s:=idealBall (b*X)) ?_]
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t I)
  · intro I hI
    by_cases h0:I=0
    · subst I
      simp only [map_zero,zero_mul]
    · have hw:W ((Ideal.absNorm I:ℝ)/X)=0 := by
        by_contra hn
        have hh:=hs hn
        have hbound:(Ideal.absNorm I:ℝ)≤b*X:=(div_le_iff₀ hX).mp hh
        exact hI ((mem_idealBall _ _).mpr ⟨h0,hbound⟩)
      rw [hw,mul_zero]

lemma slot_finite_norm (η:Character) (m A z:O) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) :
    ‖rowSlot η m A z S β t‖≤∑I∈S,‖β I‖ := by
  rw [rowSlot_eq_weight]
  exact finite_hecke_polynomial_norm η m A z t S β

lemma bounded_radial_summable (F:O→ℂ) (B:ℝ) (hF:∀z,‖F z‖≤B)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    Summable (fun z:O=>if keep z then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (f:=fun z:O=>B^2*‖Φ (‖eisEmbedding z‖^2/K)‖)
  · intro z
    split_ifs
    · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hF z) 2)
        (Complex.abs_re_le_norm _) (abs_nonneg _) (sq_nonneg _)
    · simp only [norm_zero]
      positivity
  · exact (radial_norm_summable Φ K hK).mul_left _

lemma product_bounded {ι:Type*} [Fintype ι]
    (η:Character) (m A:O) (t:ℝ) (c:ℂ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) :
    ∃B:ℝ,∀z:O,‖c*((rowTwistedSum η m A z W₁ t X₁*
      rowTwistedSum η m A z W₂ t X₂)*∏i,rowSlot η m A z (S i) (β i) t)‖≤B := by
  refine ⟨‖c‖*((∑I∈idealBall (b₁*X₁),‖W₁ ((Ideal.absNorm I:ℝ)/X₁)‖)*
    (∑I∈idealBall (b₂*X₂),‖W₂ ((Ideal.absNorm I:ℝ)/X₂)‖)*
    ∏i,∑I∈S i,‖β i I‖),?_⟩
  intro z
  rw [norm_mul,norm_mul,norm_mul,norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul
  · exact mul_le_mul (plain_finite_norm η m A z t W₁ b₁ X₁ hs₁ hX₁)
      (plain_finite_norm η m A z t W₂ b₂ X₂ hs₂ hX₂) (norm_nonneg _) (by positivity)
  · exact Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun i _=>slot_finite_norm η m A z t (S i) (β i))
  · positivity
  · positivity

 theorem retained_positive_summable {ι:Type*} [Fintype ι]
    (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    Summable (fun z:O=>if keep z then ‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  unfold retainedPositiveRow positiveSlotRow
  simp_rw [←clipped_rowTwistedSum η m A _ W₁ t X₁ hX₁,
    ←clipped_rowTwistedSum η m A _ W₂ t X₂ hX₂]
  obtain ⟨B,hB⟩:=product_bounded η m A t
    (Real.sqrt (clippedScale X₁*clippedScale X₂*∏i,P i):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  exact bounded_radial_summable _ B hB keep Φ K hK

theorem allocated_positive_summable {ι:Type*} [Fintype ι] [DecidableEq ι]
    (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (D:Ideal O) (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    Summable (fun z:O=>if keep z then ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  have hN (j:Fin 2):(0:ℝ)<Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  unfold allocatedPositiveRow
  exact retained_positive_summable η m A t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1)) _ _ _ keep Φ K hK

end SevenEighths.CenteredMomentPositiveSummability

end

end OAI

end Source669

/- Original source: OAI/NumberTheory/DirichletL/Moments/RadialEligibleEnergy.lean; sha256: 97229b52aab2de72235465a510f4990bb864f2e4af88961fc7811809827476e9 -/
section Source670
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentRadialEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRetained CenteredMomentPositiveSummability
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

structure Radial where
  keep : O→Prop
  profile : 𝓢(ℝ,ℂ)
  scale : ℝ
  scale_pos : 0<scale
  nonneg : ∀z:O,0≤(profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/scale)).re

def Radial.weight (r:Radial) (z:O) : ℝ :=
  if r.keep z then (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0

lemma Radial.weight_nonneg (r:Radial) (z:O) : 0≤r.weight z := by
  unfold Radial.weight
  split_ifs
  · exact r.nonneg z
  · rfl

def finiteData (s:Data ι) (r:Radial) (S:Finset O) : Data ι :=
  {s with rows:=S,weight:=r.weight,weight_nonneg:=fun z _=>r.weight_nonneg z}

def energy (s:Data ι) (r:Radial) (D:Ideal O) : ℝ :=
  ∑'z:O,r.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    CenteredMomentDivisorRowEnergy.maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂‖^2

def childEnergy (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : ℝ :=
  ∑'z:O,r.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)

lemma child_summable (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :
    Summable (fun z:O=>r.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)) := by
  have hX:=allocated_positive_summable s.η s.m s.A s.t s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂
    s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.slots s.coefficient s.P D a
    r.keep r.profile r.scale r.scale_pos
  have hY:=allocated_positive_summable s.η s.m s.A s.t s.W₁ s.W₂ s.b₁ s.b₂ s.Y₁ s.Y₂
    s.support₁ s.support₂ s.Y₁_pos s.Y₂_pos s.slots s.coefficient s.P D a
    r.keep r.profile r.scale r.scale_pos
  convert hX.add hY using 1
  funext z
  unfold Radial.weight
  split_ifs <;> ring

lemma finite_child_le (s:Data ι) (r:Radial) (S:Finset O) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :
    (finiteData s r S).childEnergy D a≤childEnergy s r D a := by
  exact sum_le_hasSum S (fun z _=>mul_nonneg (r.weight_nonneg z)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))) (child_summable s r D a).hasSum

lemma energy_nonneg (s:Data ι) (r:Radial) (D:Ideal O) : 0≤energy s r D :=
  tsum_nonneg (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))

lemma child_nonneg (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0≤childEnergy s r D a :=
  tsum_nonneg (fun z=>mul_nonneg (r.weight_nonneg z) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem actual_source_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial),∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P := by
  obtain ⟨C,hC,hbound⟩:=CenteredMomentEligibleEnergy.actual_source_from_children N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s r D hD E hE hchild
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))
  intro S
  exact hbound (finiteData s r S) D hD E hE
    (fun a ha=>(finite_child_le s r S D a).trans (hchild a ha))

 theorem actual_source_root_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial),∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      Real.sqrt (energy s r D)≤C*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)*Real.sqrt (s.profileFactor*E)*
        ∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P) := by
  obtain ⟨C,hC,hbase⟩:=actual_source_from_children (ι:=ι) N hslots ε hε
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  intro s r D hD E hE hc
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he:0≤s.profileFactor*E:=mul_nonneg s.profile_nonneg hE
  have hs:=sqrt_sum_le (s.toSource.active D) (fun a=>1/formalReductionFactor D a s.P)
    (fun a _=>div_nonneg zero_le_one (s.reduction_pos D a).le)
  simp_rw [sqrt_reciprocal _ (s.reduction_pos D _)] at hs
  have hh:=Real.sqrt_le_sqrt (hbase s r D hD E hE hc)
  have hrew:C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)=
      (C*(Ideal.absNorm D:ℝ)^ε*(s.profileFactor*E))*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P):=by ring
  rw [hrew,Real.sqrt_mul (mul_nonneg (mul_nonneg hC.le hp) he),
    Real.sqrt_mul (mul_nonneg hC.le hp),Real.sqrt_mul hC.le] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hs (by positivity))

end SevenEighths.CenteredMomentRadialEligibleEnergy

end

end OAI

end Source670

/- Original source: OAI/NumberTheory/DirichletL/Moments/RadialCenteredEnergy.lean; sha256: 575c11deacbab31e6460e0b1dadd1af099c8350731a0bdd41f9abbc1cc18ce86 -/
section Source671
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentRadialCenteredEnergy
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorExtraction CenteredMomentDivisorRowEnergy CenteredMomentDivisorRectangle
open CenteredMomentHeckeSlots CenteredMomentPositiveSummability CenteredMomentActiveAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def centeredChildEnergy (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):ℝ:=
  ∑'z:O,r.weight z*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
    s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2

lemma centered_child_summable (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):
    Summable (fun z:O=>r.weight z*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2):=by
  have hN (j:Fin 2):(0:ℝ)<Ideal.absNorm (selectedPlain D a j):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  let c:ℂ:=(Real.sqrt ((s.X₁*s.X₂/selectedNorm D a)*∏i:liveIndices D a,s.P i):ℂ)⁻¹
  obtain ⟨BX,hBX⟩:=product_bounded s.η s.m s.A s.t c s.W₁ s.W₂ s.b₁ s.b₂
    (s.X₁/Ideal.absNorm (selectedPlain D a 0)) (s.X₂/Ideal.absNorm (selectedPlain D a 1))
    s.support₁ s.support₂ (div_pos s.X₁_pos (hN 0)) (div_pos s.X₂_pos (hN 1))
    (fun i:liveIndices D a=>s.slots i) (fun i:liveIndices D a=>s.coefficient i)
  obtain ⟨BY,hBY⟩:=product_bounded s.η s.m s.A s.t c s.W₁ s.W₂ s.b₁ s.b₂
    (s.Y₁/Ideal.absNorm (selectedPlain D a 0)) (s.Y₂/Ideal.absNorm (selectedPlain D a 1))
    s.support₁ s.support₂ (div_pos s.Y₁_pos (hN 0)) (div_pos s.Y₂_pos (hN 1))
    (fun i:liveIndices D a=>s.slots i) (fun i:liveIndices D a=>s.coefficient i)
  have hF (z:O):‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖≤BX+BY:=by
    unfold residualCenteredRow centeredSlotRow
    change ‖c*((_ - _)*_)‖≤_
    rw [sub_mul,mul_sub]
    exact (norm_sub_le _ _).trans (add_le_add (hBX z) (hBY z))
  have hs:=bounded_radial_summable _ (BX+BY) hF r.keep r.profile r.scale r.scale_pos
  convert hs using 1
  funext z
  unfold Radial.weight
  split_ifs <;> ring

lemma centered_child_nonneg (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):0≤centeredChildEnergy s r D a:=
  tsum_nonneg (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))

def restrict (r:Radial) (p:O→Prop):Radial:={r with keep:=fun z=>r.keep z ∧ p z}

 theorem centered_child_split (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (p:O→Prop):
    centeredChildEnergy s r D a=centeredChildEnergy s (restrict r p) D a+
      centeredChildEnergy s (restrict r (fun z=>¬p z)) D a:=by
  unfold centeredChildEnergy
  rw [←Summable.tsum_add (centered_child_summable s (restrict r p) D a)
    (centered_child_summable s (restrict r (fun z=>¬p z)) D a)]
  apply tsum_congr
  intro z
  by_cases hk:r.keep z <;> by_cases hp:p z <;> simp [Radial.weight,restrict,hk,hp]

 theorem actual_source_centered (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^ε*
        ∑a∈s.toSource.active D,((∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P)*
          centeredChildEnergy s r D a:=by
  obtain ⟨C,hC,hbase⟩:=active_allocated_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s r D hD
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))
  intro rows
  have hb:=hbase s.η s.m s.A s.t s.slots s.coefficient D hD s.W₁ s.W₂ s.b₁ s.b₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    rows (fun z=>r.weight z/(s.X₁*s.X₂*∏i,s.P i)) (fun z _=>div_nonneg (r.weight_nonneg z) hraw.le)
  have he (z:O) (x:ℂ):(r.weight z/(s.X₁*s.X₂*∏i,s.P i))*‖x‖^2=
      r.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*x‖^2:=by
    rw [normalized_norm_sq _ hraw];ring
  simp_rw [he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  have hf:0≤(∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P:=
    div_nonneg (sq_nonneg _) (mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))).le
  calc
    _≤∑z∈rows,r.weight z*((∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P)*
      ‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=by
      apply Finset.sum_le_sum
      intro z hz
      have hh:=mul_le_mul_of_nonneg_left
        (allocated_raw_energy s.η s.m s.A z s.t s.slots s.prime s.coefficient s.M s.P
          (fun i=>(zero_le_one.trans (s.M_ge_one i))) s.P_pos s.coefficient_bound D a s.W₁ s.W₂
          s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
          s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos (mul_pos s.X₁_pos s.X₂_pos)) (r.weight_nonneg z)
      convert hh using 1 ; ring
    _=((∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P)*
      ∑z∈rows,r.weight z*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intros;ring
    _≤_:=mul_le_mul_of_nonneg_left (sum_le_hasSum rows
      (fun z _=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _)) (centered_child_summable s r D a).hasSum) hf

 theorem actual_source_from_centered_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,centeredChildEnergy s r D a≤E) →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P:=by
  obtain ⟨C,hC,hbound⟩:=actual_source_centered N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s r D hD E hE hchild
  apply (hbound s r D hD).trans
  calc
    _≤C*(Ideal.absNorm D:ℝ)^ε*∑a∈s.toSource.active D,
        (s.profileFactor/formalReductionFactor D a s.P)*E:=by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      apply Finset.sum_le_sum
      intro a ha
      have hp:(∏i∈frozenIndices D a,s.M i)≤∏i,s.M i:=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
      have hsq:(∏i∈frozenIndices D a,s.M i)^2≤s.profileFactor:=by
        have hh:=pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))) hp 2
        have hf:1≤2*(max 1 s.b₁*max 1 s.b₂):=by
          have ht:=one_le_mul_of_one_le_of_one_le (le_max_left 1 s.b₁) (le_max_left 1 s.b₂)
          linarith
        exact hh.trans (le_mul_of_one_le_left (sq_nonneg _) hf)
      exact mul_le_mul (div_le_div_of_nonneg_right hsq (s.reduction_pos D a).le)
        (hchild a ha) (centered_child_nonneg s r D a) (div_nonneg s.profile_nonneg (s.reduction_pos D a).le)
    _=_:=by
      simp only [div_eq_mul_inv,one_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

end SevenEighths.CenteredMomentRadialCenteredEnergy

end

end OAI

end Source671

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceDegree.lean; sha256: 16adee87ae4c181d8190be87eda2b545082f06a5e08d45eb6e529f37edd54ff9 -/
section Source672
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeVolume
open CenteredMomentHeckeCancellation CenteredMomentHeckeTwist CenteredMomentLattice
open CenteredMomentMask CenteredMomentTwist CenteredMomentHeight CenteredMomentHeckeSlots
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem volumeControl_uniform_degree (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∀ Q : Ideal O, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      ∀ t : ℝ, volumeControl Q χ (normPowerProfile W a b ha hs hW t) ≤
        C * Z ^ ε * (1 + ‖t‖) ^ n := by
  obtain ⟨n, hn⟩ := normPowerProfile_uniform_degree a b ha pvSeminorms
  obtain ⟨D, hD, hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  refine ⟨n, ?_⟩
  intro Q W hs hW
  obtain ⟨C, hC, hprofile⟩ := hn W hs hW
  let mass : ℝ := Nat.card (O ⧸ Ideal.span {fixedPeriod Q})
  have hmass : 0 ≤ mass := Nat.cast_nonneg _
  let A := D * mass * pvConstant * C
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg hD.le hmass) pvConstant_pos.le) hC.le
  refine ⟨1 + A, by linarith, ?_⟩
  intro Z hZ χ hnorm t
  have hheight : (1 + ‖t / (2 * Real.pi)‖) ^ n ≤ (1 + ‖t‖) ^ n := by
    gcongr
    exact normalized_height_le t
  have hseminorm := (hprofile t).trans (mul_le_mul_of_nonneg_left hheight hC.le)
  have herr : volumeControl Q χ (normPowerProfile W a b ha hs hW t) ≤
      (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := by
    unfold volumeControl pvControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hnorm)
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hseminorm pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg pvConstant_pos.le (apply_nonneg _ _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := herr
    _ = A * Z ^ ε * (1 + ‖t‖) ^ n := by dsimp only [A]; ring
    _ ≤ (1 + A) * Z ^ ε * (1 + ‖t‖) ^ n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : A ≤ 1 + A)
          (Real.rpow_nonneg (le_trans zero_le_one hZ) ε)) (by positivity)

theorem rectangle_uniform_degree
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ Q : Ideal O, Q≠0 → ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ η χ ψ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      (Q ≤ ψ.modulus) → CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A₀ z : O, (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (twistedIdealSum χ W₁ t X₁ * twistedIdealSum χ W₂ t X₂ -
          twistedIdealSum χ W₁ t Y₁ * twistedIdealSum χ W₂ t Y₂)‖ ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J * (Real.sqrt T / L) := by
  obtain ⟨n₁, hn₁⟩ := volumeControl_uniform_degree a₁ b₁ ε B ha₁ hε hB
  obtain ⟨n₂, hn₂⟩ := volumeControl_uniform_degree a₂ b₂ ε B ha₂ hε hB
  refine ⟨max n₁ n₂, ?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨D₁, hD₁, herr₁⟩ := hn₁ Q W₁ hs₁ hW₁
  obtain ⟨D₂, hD₂, herr₂⟩ := hn₂ Q W₂ hs₂ hW₂
  let M₁ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ 0)
  let M₂ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ 0)
  have hM₁ : 0 ≤ M₁ := apply_nonneg _ _
  have hM₂ : 0 ≤ M₂ := apply_nonneg _ _
  have hbound₁ (y : ℝ) : ‖W₁ y‖ ≤ M₁ := by
    rw [← normPowerProfile_norm W₁ a₁ b₁ ha₁ hs₁ hW₁ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hbound₂ (y : ℝ) : ‖W₂ y‖ ≤ M₂ := by
    rw [← normPowerProfile_norm W₂ a₂ b₂ ha₂ hs₂ hW₂ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  let V := 128 * (b₁ * M₁ + b₂ * M₂)
  have hV : 0 ≤ V := mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  let C := 1 + 4 * (D₁ + D₂) * V
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z hZ η χ ψ hnorm hQψ hind m A₀ z hmLam hm2 hrow t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let E := volumeControl Q χ (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
    volumeControl Q χ (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have hpow₁ := pow_le_pow_right₀ ht (le_max_left n₁ n₂)
  have hpow₂ := pow_le_pow_right₀ ht (le_max_right n₁ n₂)
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (le_trans zero_le_one hZ) ε
  have hE : E ≤ (D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ := by
    have h₁ := (herr₁ Z hZ χ hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₁ (mul_nonneg hD₁.le hz))
    have h₂ := (herr₂ Z hZ χ hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₂ (mul_nonneg hD₂.le hz))
    dsimp only [E]
    nlinarith
  have hraw := actual_twisted_rectangle_saving η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ W₂ a₁ b₁ a₂ b₂ M₁ M₂
    ha₁ ha₂ hb₁ hb₂ hM₁ hM₂ hs₁ hs₂ hW₁ hW₂ hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
  have hnormalized := CenteredMoment.normalized_centered_saving _ T L V E hT hraw
  have hratio : 0 ≤ Real.sqrt T / L := div_nonneg (Real.sqrt_nonneg T) hL.le
  calc
    _ ≤ 4 * E * V * (Real.sqrt T / L) := hnormalized
    _ ≤ 4 * ((D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂) * V *
        (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hV) hratio
    _ = (4 * (D₁ + D₂) * V) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ *
        (Real.sqrt T / L) := by ring
    _ ≤ C * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ * (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hz) (by positivity)) hratio

theorem row_rectangle_uniform_degree
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ Q : Ideal O, Q≠0 → ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (η : Character) (m A₀ z : O),
      m ≠ 0 → A₀ ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A₀*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A₀ z W₁ t X₁*rowTwistedSum η m A₀ z W₂ t X₂-
         rowTwistedSum η m A₀ z W₁ t Y₁*rowTwistedSum η m A₀ z W₂ t Y₂)‖ ≤
        C*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,hJ⟩ := rectangle_uniform_degree a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ η m A₀ z hm hA hz hmLam hm2 hcond hex t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  obtain ⟨χ,ψ,hχ,hprim,hind,hQψ,hrow⟩ := fixedInducingRow_controlled η Q m A₀ z hm hA hz hmLam hm2 hex
  have hχnorm : (Ideal.absNorm χ.modulus:ℝ) ≤ Z^B :=
    (show (Ideal.absNorm χ.modulus:ℝ) ≤ HeckeRowClosure.rowConductorBound η m 1 (A₀*z) by exact_mod_cast hχ).trans hcond
  simp_rw [rowTwistedSum_eq η χ m A₀ z hrow]
  exact hbound Z hZ η χ ψ hχnorm hQψ hind m A₀ z hmLam hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

theorem slots_uniform_degree
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ Q : Ideal O, Q≠0 → ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (η : Character) (m A z : O),
      m ≠ 0 → A ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀ (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (p b M : ι → ℝ),
      (∀ i, 0 < p i) → (∀ i, 0 ≤ b i) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ P ∈ S i, ‖β i P‖ ≤ M i) →
      (∀ i, ∀ P ∈ S i, β i P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ b i*p i) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z W₁ W₂ S β p t X₁ X₂ Y₁ Y₂ T‖ ≤
        C*Z^ε*(1+‖t‖)^J*(∏ i,128*b i*M i)*(Real.sqrt (T*∏ i,p i)/L) := by
  obtain ⟨J,hJ⟩ := row_rectangle_uniform_degree a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ η m A z hm hA hz hmLam hm2 hcond hex S β p b M hp hb hM hβ hN
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) t‖ ≤ (128*b i*M i)*p i := by
    convert rowSlot_bound η m A z (S i) (β i) t (b i*p i) (M i)
      (mul_nonneg (hb i) (hp i).le) (hM i) (hβ i) (hN i) using 1 ; ring
  exact whole_product_normalization _ (fun i => rowSlot η m A z (S i) (β i) t)
    (fun i => 128*b i*M i) p (C*Z^ε*(1+‖t‖)^J) T L
    (by positivity) hT hL (fun i => mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hp hslots
    (hbound Z hZ η m A z hm hA hz hmLam hm2 hcond hex
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source672

/- Original source: OAI/NumberTheory/DirichletL/Moments/HeckeExceptionalEnergy.lean; sha256: cedc30729530b22fcb396deae37405de3baae62aa968604bf2285387764b2265 -/
section Source673
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeExceptionalEnergy
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentForcing CenteredMomentChildRows UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem forcing_finite_energy (p : ι → O)
    (hp : ∀ i, Prime (Ideal.span {p i})) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (c d : ι → ℕ) (V : Finset ι) (η : Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (m e : O) (hm : m ≠ 0) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (he : elementCoeff η e ≠ 0) (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow
      (childCharacter η χ) Q m (movingElement p c d V) z)
    (hgood : ∀ i ∈ forcingSet c d V,
      ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i} ∧ (2:O) ∉ Ideal.span {p i} ∧
      IsCoprime Q (Ideal.span {p i}) ∧ Ideal.span {p i} ∣ Ideal.span {e})
    (Z C M D : ℝ) (hZ : 1 < Z) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}):ℝ) ≤ C*Z^M)
    (f : O → ℂ) (hf : ∀ z ∈ rows, ‖f z‖ ≤ D) :
    (∑ z ∈ rows, ‖f z‖^2) ≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*C^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V)))/6))*D^2 := by
  have hc := actual_forcing_exceptional_count p hp hinj c d V η χ Q hQ0 hQ hQ72
    m e hm hmLam hm2 he rows hrows hex hgood Z C M hZ hC hN
  calc
    _ ≤ ∑ _z ∈ rows, D^2 := Finset.sum_le_sum (fun z hz =>
      pow_le_pow_left₀ (norm_nonneg _) (hf z hz) 2)
    _ = (rows.card:ℝ)*D^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg D)

theorem exceptional_slots_energy (Q : Ideal O) (hQ0 : Q ≠ 0)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 < Z →
      ∀ (p : ι → O), (∀ i, Prime (Ideal.span {p i})) →
      Function.Injective (fun i => Ideal.span {p i}) →
      ∀ (c d : ι → ℕ) (V : Finset ι) (η : Character) (χ : RayFourExpansion.RayCharacter),
      ∀ m e : O, m ≠ 0 → (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      elementCoeff η e ≠ 0 → ∀ rows : Finset O,
      (∀ z ∈ rows, z ≠ 0) →
      (∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow
        (childCharacter η χ) Q m (movingElement p c d V) z) →
      (∀ z ∈ rows, (HeckeRowClosure.rowConductorBound (childCharacter η χ) m 1
        (movingElement p c d V*z):ℝ) ≤ Z^B) →
      (∀ i ∈ forcingSet c d V,
        ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i} ∧ (2:O) ∉ Ideal.span {p i} ∧
        IsCoprime Q (Ideal.span {p i}) ∧ Ideal.span {p i} ∣ Ideal.span {e}) →
      ∀ Cr Mrow : ℝ, 0 ≤ Cr →
      (∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Cr*Z^Mrow) →
      ∀ (S : κ → Finset (Ideal O)) (β : κ → Ideal O → ℂ) (P b Ms : κ → ℝ),
      (∀ i, 0 < P i) → (∀ i, 0 ≤ b i) → (∀ i, 0 ≤ Ms i) →
      (∀ i, ∀ I ∈ S i, ‖β i I‖ ≤ Ms i) →
      (∀ i, ∀ I ∈ S i, β i I ≠ 0 → (Ideal.absNorm I:ℝ) ≤ b i*P i) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      (∑ z ∈ rows, ‖centeredSlotRow (childCharacter η χ) m (movingElement p c d V) z
        W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2) ≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((Mrow-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V)))/6))*
        (C*Z^ε*(1+‖t‖)^J*(∏ i,128*b i*Ms i)*(Real.sqrt (T*∏ i,P i)/L))^2 := by
  obtain ⟨J,hJ⟩ := exceptional_slots_estimate (ι := κ) Q hQ0 a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ p hp hinj c d V η χ m e hm hmLam hm2 he rows hrows hex hcond hgood
    Cr Mrow hCr hN S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hA : movingElement p c d V ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [movingElement_span]
    exact movingIdeal_ne_zero _ hp c d V
  refine forcing_finite_energy p hp hinj c d V η χ Q hQ0 hQ hQ72
    m e hm hmLam hm2 he rows hrows hex hgood Z Cr Mrow _ hZ hCr ?_ hN _ ?_
  · have hprod : 0 ≤ ∏ i,128*b i*Ms i :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hMs i))
    positivity
  · intro z hz
    exact hbound Z hZ.le (childCharacter η χ) m (movingElement p c d V) z hm hA (hrows z hz)
      hmLam hm2 (hcond z hz) (hex z hz) S β P b Ms hP hb hMs hβ hNs
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

end SevenEighths.CenteredMomentHeckeExceptionalEnergy

end

end OAI

end Source673

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalCount.lean; sha256: 48566258b8b5941f09abd42573aa8d30ebe4c167cd5a577cf8a7f438c2cd04c8 -/
section Source674
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondExceptionalCount
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondHeightFamily CenteredMomentSupport UniqueFactorizationMonoid
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

lemma supported_coprime_72 (C:Ideal O) (hC:Supported C) :
    IsCoprime (Ideal.span {(72:O)}) C := by
  let n:=primaryGenerator C
  have hn:Supported (Ideal.span {n}):=by rw [primary_span_supported C hC]; exact hC
  have h2:IsCoprime n (2:O):=(fixedBadMask_coprime n hn).of_mul_left_right.symm
  have h9: IsCoprime n (9:O):=
    (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n ((supported_span_iff n).mp hn).1).symm
  have h72:IsCoprime n (72:O):=by
    convert (h2.pow_right : IsCoprime n ((2:O)^3)).mul_right h9 using 1 ; norm_num
  rw [←primary_span_supported C hC,Ideal.isCoprime_span_singleton_iff]
  exact h72.symm

lemma common_prime_dvd_left (C D:Ideal O) (P:CommonIndex C D) : P.val∣C :=
  dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)

lemma common_prime_prime (C D:Ideal O) (hC:Supported C) (P:CommonIndex C D) :
    Prime (Ideal.span {commonPrime C D P}) := by
  rw [commonPrime_span C D hC P]
  exact prime_of_normalized_factor _ (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)

lemma outer_nonzero_left (η:Character) (t:ℝ) (C D:Ideal O)
    (hne:heightCoeff η t C*star (heightCoeff η t D)≠0) : idealCoeff η C≠0 :=
  left_ne_zero_of_mul (left_ne_zero_of_mul hne)

theorem actual_canonical_exceptional_count (η:Character) (χ:RayFourExpansion.RayCharacter)
    (C D:Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (Q:Ideal O) (hQ0:Q≠0) (hQ:Q≠⊤) (hQ72:Q≤Ideal.span {(72:O)})
    (hQC:IsCoprime Q C) (hη:idealCoeff η C≠0)
    (m:O) (hm:m≠0) (hmLam:goodLambda∣m) (hm2:(2:O)∣m)
    (rows:Finset O) (hrows:∀z∈rows,z≠0)
    (hex:∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z)
    (Z Cr M:ℝ) (hZ:1<Z) (hCr:0≤Cr)
    (hN:∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) :
    (rows.card:ℝ)≤768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
      Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
        (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6) := by
  have he:elementCoeff η (primaryGenerator C)≠0 := by
    rw [←idealCoeff_span η (supported_primaryGenerator_ne_zero C hC),primary_span_supported C hC]
    exact hη
  have hinj:Function.Injective (fun P:CommonIndex C D=>Ideal.span {commonPrime C D P}):=by
    simpa only [commonPrime_span C D hC] using (Subtype.val_injective:Function.Injective (fun P:CommonIndex C D=>P.val))
  have hb:=actual_forcing_exceptional_count (commonPrime C D) (common_prime_prime C D hC) hinj
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U) η χ
    Q hQ0 hQ hQ72 m (primaryGenerator C) hm hmLam hm2 he rows hrows hex (by
      intro P hP
      rw [commonPrime_span C D hC P]
      refine ⟨common_good C D hC P,CanonicalRowCompletion.good_odd_prime_two_not_mem _
        (common_odd C D hC P),hQC.of_isCoprime_of_dvd_right (common_prime_dvd_left C D P),?_⟩
      rw [primary_span_supported C hC]
      exact common_prime_dvd_left C D P) Z Cr M hZ hCr hN
  simpa only [commonPrime_span C D hC] using hb

end SevenEighths.CenteredMomentSecondExceptionalCount

end

end OAI

end Source674

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalEnergy.lean; sha256: 60d582ab53c02bbf3c7aabbdc84f93b17c6bc98f447d1800e26982ae48f5f041 -/
section Source675
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentSecondExceptionalEnergy
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentHeckeSlots CenteredMomentSecondExceptionalCount UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem actual_exceptional_slots_energy {ι:Type*} [Fintype ι]
    (Q:Ideal O) (hQ0:Q≠0) (hQ:Q≠⊤) (hQ72:Q≤Ideal.span {(72:O)})
    (a₁ b₁ a₂ b₂ ε B:ℝ) (ha₁:0<a₁) (ha₂:0<a₂)
    (hb₁:0≤b₁) (hb₂:0≤b₂) (hε:0<ε) (hB:0≤B) :
    ∃J:ℕ,∀W₁ W₂:ℝ→ℂ,Function.support W₁⊆Set.Icc a₁ b₁ →
      Function.support W₂⊆Set.Icc a₂ b₂ → ContDiff ℝ ∞ W₁ → ContDiff ℝ ∞ W₂ →
      ∃C0:ℝ,0<C0 ∧ ∀Z:ℝ,1<Z →
      ∀(η:Character) (χ:RayFourExpansion.RayCharacter) (C D:Ideal O) (_hC:Supported C)
        (U:Finset (CommonIndex C D)),IsCoprime Q C → idealCoeff η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m A z) →
      (∀z∈rows,(HeckeRowClosure.rowConductorBound (childCharacter η χ) m 1 (A*z):ℝ)≤Z^B) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b Ms:ι→ℝ),
      (∀i,0<P i) → (∀i,0≤b i) → (∀i,0≤Ms i) →
      (∀i,∀I∈S i,‖β i I‖≤Ms i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L:ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      (∑z∈rows,‖centeredSlotRow (childCharacter η χ) m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2)≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun p:CommonIndex C D=>p.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6))*
        (C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/L))^2 := by
  obtain ⟨J,hJ⟩:=exceptional_slots_estimate (ι:=ι) Q hQ0 a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C0,hC0,hpoint⟩:=hJ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C0,hC0,?_⟩
  intro Z hZ η χ C D hC U hQC hη m hm hmLam hm2 A rows hrows hex hcond Cr M hCr hN
    S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hA:A≠0:=mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  have hc:=actual_canonical_exceptional_count η χ C D hC U Q hQ0 hQ hQ72 hQC hη m hm hmLam hm2
    rows hrows hex Z Cr M hZ hCr hN
  have hp:∀z∈rows,‖centeredSlotRow (childCharacter η χ) m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
      C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/L):=by
    intro z hz
    exact hpoint Z hZ.le (childCharacter η χ) m A z hm hA (hrows z hz) hmLam hm2
      (hcond z hz) (hex z hz) S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hXT hYT
  calc
    _≤∑z∈rows,(C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/L))^2 :=
      Finset.sum_le_sum (fun z hz=>pow_le_pow_left₀ (norm_nonneg _) (hp z hz) 2)
    _=(rows.card:ℝ)*(C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/L))^2 := by simp
    _≤_:=mul_le_mul_of_nonneg_right hc (sq_nonneg _)

end SevenEighths.CenteredMomentSecondExceptionalEnergy

end

end OAI

end Source675

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalAllocationShell.lean; sha256: 9386a78205c9486092fbaf4b17eba9b3e9186da7a5fdbc891bc303870935041f -/
section Source676
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalAllocationShell
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentDivisorBoundary CenteredMomentSlotRatios
open CenteredMomentUniformDivisorShell
local notation "O" => ActualEisensteinCubic.O

lemma exact_max_cancellation (r r₁ : ℝ) :
    -r₁-max (r-r₁) 0 = -max r r₁ := by
  by_cases h : r ≤ r₁
  · rw [max_eq_right (by linarith : r-r₁≤0),max_eq_right h]
    ring
  · rw [max_eq_left (by linarith : 0≤r-r₁),max_eq_left (le_of_not_ge h)]
    ring

def exceptionalWeight {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (s : Source ι) (v : Source κ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ⊕Fin 2))) (Z r : ℝ) : ℝ :=
  Z^(-Real.logb Z (formalReductionFactor D a s.P)-
    Real.logb Z (formalReductionFactor D b v.P)-
    max (r-Real.logb Z (formalReductionFactor D a s.P)) 0)

theorem active_exceptional_weight {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (s : Source ι) (v : Source κ) (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ⊕Fin 2)))
    (_ha : a∈s.active D) (hb : b∈v.active D) (Z r : ℝ) (hZ : 1<Z) :
    exceptionalWeight s v D a b Z r ≤ Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hn : (0:ℝ)<Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hv := v.active_boundary D hD b hb Z hZ
  have hm := exact_max_cancellation r (Real.logb Z (formalReductionFactor D a s.P))
  have he : -Real.logb Z (formalReductionFactor D a s.P)-
      Real.logb Z (formalReductionFactor D b v.P)-
      max (r-Real.logb Z (formalReductionFactor D a s.P)) 0 ≤
      v.allowance Z-r-Real.logb Z (Ideal.absNorm D:ℝ) := by
    linarith [le_max_left r (Real.logb Z (formalReductionFactor D a s.P))]
  unfold exceptionalWeight
  apply (Real.rpow_le_rpow_of_exponent_le hZ.le he).trans_eq
  rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hn]

theorem actual_exceptional_shell {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (N : ℕ) (hι : Fintype.card ι≤N) (hκ : Fintype.card κ≤N) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(s : Source ι) (v : Source κ) (Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r) ≤
        C*(2*T)^(2*ε)*Z^(v.allowance Z-r) := by
  obtain ⟨C₁,hC₁,hcard₁⟩ := CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  obtain ⟨C₂,hC₂,hcard₂⟩ := CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=κ⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨256*C₁*C₂,by positivity,?_⟩
  intro s v Ds hD T Z r hT hZ hlo hhi
  have ht : 0<T := zero_lt_one.trans_le hT
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc₁ (D : Ideal O) (hd : D∈Ds) : ((s.active D).card:ℝ)≤C₁*(Ideal.absNorm D:ℝ)^ε := by
    apply (show ((s.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₁ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hc₂ (D : Ideal O) (hd : D∈Ds) : ((v.active D).card:ℝ)≤C₂*(Ideal.absNorm D:ℝ)^ε := by
    apply (show ((v.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (κ⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₂ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hp (D : Ideal O) (hd : D∈Ds) :
      (∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤
        (C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T) := by
    have hn : (0:ℝ)<Ideal.absNorm D := ht.trans_le (hlo D hd)
    have he : (Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε=(Ideal.absNorm D:ℝ)^(2*ε) := by
      rw [←Real.rpow_add hn]; congr 1; ring
    have hpow : (Ideal.absNorm D:ℝ)^(2*ε)≤(2*T)^(2*ε) :=
      Real.rpow_le_rpow hn.le (hhi D hd).le (by positivity)
    calc
      _ ≤ ∑_a∈s.active D,∑_b∈v.active D,Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ) :=
        Finset.sum_le_sum (fun a ha=>Finset.sum_le_sum (fun b hb=>
          active_exceptional_weight s v D (hD D hd) a b ha hb Z r hZ))
      _ = ((s.active D).card:ℝ)*((v.active D).card:ℝ)*(Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) := by simp; ring
      _ ≤ (C₁*(Ideal.absNorm D:ℝ)^ε)*(C₂*(Ideal.absNorm D:ℝ)^ε)*
          (Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hc₁ D hd) (hc₂ D hd) (by positivity) (by positivity)) (by positivity)
      _ = (C₁*C₂)*(Ideal.absNorm D:ℝ)^(2*ε)*(Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) := by rw [←he]; ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity))
        (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) ht (hlo D hd)) (by positivity) (by positivity)
  calc
    _ ≤ ∑_D∈Ds,(C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T) := Finset.sum_le_sum hp
    _ = (Ds.card:ℝ)*((C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T)) := by simp
    _ ≤ (256*T)*((C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T)) :=
      mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT (fun D hd=>(hD D hd).ne_zero) hhi) (by positivity)
    _ = (256*C₁*C₂)*(2*T)^(2*ε)*Z^(v.allowance Z-r) := by field_simp

def ShellBound (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C ε : ℝ) : Prop := ∀(s : Source ι) (v : Source κ) (Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r) ≤
        C*(2*T)^(2*ε)*Z^(v.allowance Z-r)

theorem uniform_subset_shell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ℝ) (hε : 0<ε) : ∃C : ℝ,0<C ∧ ∀J L : Finset ι,ShellBound J L C ε := by
  have he (p : Finset ι×Finset ι) : ∃C : ℝ,0<C ∧ ShellBound p.1 p.2 C ε :=
    actual_exceptional_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B : ℝ := 1+∑p : Finset ι×Finset ι,C p
  have hs : 0≤∑p : Finset ι×Finset ι,C p := Finset.sum_nonneg (fun p _=>(hC p).le)
  refine ⟨B,by dsimp [B]; linarith,?_⟩
  intro J L s v Ds hD T Z r hT hZ hlo hhi
  have hc : C (J,L)≤B := by
    have hp := Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]; linarith
  exact (hbound (J,L) s v Ds hD T Z r hT hZ hlo hhi).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _))

theorem exceptional_shell_subpower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : ι→ℝ) (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(J L : Finset ι) (s : Source J) (v : Source L),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds : Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,
      1≤T → 1<Z → T≤Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤C*Z^(δ-r) := by
  let ε : ℝ := δ/(2*(B+1))
  have hε : 0<ε := div_pos hδ (by positivity)
  have he : 2*B*ε≤δ := by
    have hh : ε*(2*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := uniform_subset_shell (ι:=ι) ε hε
  let E : ℝ := Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(2*ε)*E,by dsimp [E]; positivity,?_⟩
  intro J L s v hvlo hvhi Ds hD T Z r hT hZ hTZ hlo hhi
  have ht : 0<T := zero_lt_one.trans_le hT
  have hz : 0<Z := zero_lt_one.trans hZ
  have hh := hbound J L s v Ds hD T Z r hT hZ hlo hhi
  have hv : Z^(v.allowance Z-r)≤E*Z^(-r) := by
    calc
      _≤Z^((∑i,logWindow (lo i) (hi i))/Real.log Z-r) :=
        Real.rpow_le_rpow_of_exponent_le hZ.le
          (sub_le_sub_right (subset_allowance L v lo hi hvlo hvhi Z hZ) r)
      _=E*Z^(-r) := by rw [sub_eq_add_neg,Real.rpow_add hz,numerical_allowance Z _ hZ]
  have hpow : T^(2*ε)≤Z^δ := by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith [he])
  apply hh.trans
  calc
    _≤C*(2*T)^(2*ε)*(E*Z^(-r)) := mul_le_mul_of_nonneg_left hv (by positivity)
    _=(C*2^(2*ε)*E)*T^(2*ε)*Z^(-r) := by
      rw [Real.mul_rpow (by norm_num : 0≤(2:ℝ)) ht.le]; ring
    _≤(C*2^(2*ε)*E)*Z^δ*Z^(-r) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by dsimp [E]; positivity)) (by positivity)
    _=(C*2^(2*ε)*E)*Z^(δ-r) := by rw [mul_assoc,←Real.rpow_add hz]; rfl

end SevenEighths.CenteredMomentExceptionalAllocationShell

end

end OAI

end Source676

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalCappedAmplitude.lean; sha256: c2796331998f0d9384e5f4d071aa813ba94ed10d7dc0d9e8c4e37a756ab663ca -/
section Source677
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentExceptionalCappedAmplitude
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentCounting CenteredMomentHeckeTwist CenteredMomentTwist CenteredMomentHeight CenteredMomentLattice
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondExceptionalCount
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => HeckeFamily.O

theorem rowTwistedSum_absolute (η : Character) (m A z : O) (W : ℝ→ℂ)
    (b M t X : ℝ) (hb : 0≤b) (hM : 0≤M) (hX : 0<X)
    (hs : Function.support W⊆Set.Iic b) (hW : ∀x,‖W x‖≤M) :
    ‖rowTwistedSum η m A z W t X‖≤(128*b*M)*X := by
  have hh := norm_tsum_ideal_ball
    (fun I : Ideal O => (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)*
      (Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)) (b*X) M
    (mul_nonneg hb hX.le) hM (by
      change (idealCoeff η (0:Ideal O)*_)*_*_=0
      rw [map_zero,zero_mul,zero_mul,zero_mul]) (by
      intro I
      by_cases hI : I=0
      · subst I; simpa only [map_zero,zero_mul,mul_zero,norm_zero] using hM
      · rw [norm_mul]
        exact (mul_le_mul (row_twisted_coefficient_norm η m A z t I hI) (hW _)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul M)) (by
      intro I hI
      exact (div_le_iff₀ hX).mp (hs (right_ne_zero_of_mul hI)))
  exact hh.trans_eq (by ring)

theorem normalized_rectangle_absolute (η : Character) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ M₁ M₂ : ℝ)
    (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (hW₁ : ∀x,‖W₁ x‖≤M₁) (hW₂ : ∀x,‖W₂ x‖≤M₂)
    (t X₁ X₂ Y₁ Y₂ T : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T) :
    ‖(Real.sqrt T:ℂ)⁻¹ *
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)‖≤
      (2*(128*b₁*M₁)*(128*b₂*M₂))*Real.sqrt T := by
  have hT : 0<T := hpX ▸ mul_pos hX₁ hX₂
  have hsq : 0<Real.sqrt T := Real.sqrt_pos.2 hT
  have hprod (U V : ℝ) (hU : 0<U) (hV : 0<V) :
      ‖rowTwistedSum η m A z W₁ t U*rowTwistedSum η m A z W₂ t V‖≤
        ((128*b₁*M₁)*(128*b₂*M₂))*(U*V) := by
    rw [norm_mul]
    apply (mul_le_mul (rowTwistedSum_absolute η m A z W₁ b₁ M₁ t U hb₁ hM₁ hU hs₁ hW₁)
      (rowTwistedSum_absolute η m A z W₂ b₂ M₂ t V hb₂ hM₂ hV hs₂ hW₂)
      (norm_nonneg _) (by positivity)).trans_eq
    ring
  have hraw := (norm_sub_le
    (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)
    (rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)).trans
      (add_le_add (hprod X₁ X₂ hX₁ hX₂) (hprod Y₁ Y₂ hY₁ hY₂))
  rw [hpX,hpY] at hraw
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsq.le]
  apply (mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hsq.le)).trans_eq
  have he := Real.sq_sqrt hT.le
  field_simp
  rw [he]
  ring

theorem capped_rectangle_uniform_degree
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∀W₁ W₂ : ℝ→ℂ,
      ∀_hs₁ : Function.support W₁⊆Set.Icc a₁ b₁,
      ∀_hs₂ : Function.support W₂⊆Set.Icc a₂ b₂,
      ∀_hW₁ : ContDiff ℝ ∞ W₁,∀_hW₂ : ContDiff ℝ ∞ W₂,
      ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀(η : Character)(m A z : O),
      m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
         rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)‖≤
        C*Z^ε*(1+‖t‖)^J*(Real.sqrt T/max 1 L) := by
  obtain ⟨J,hJ⟩ := row_rectangle_uniform_degree a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hcancel⟩ := hJ Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  let M₁ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ 0)
  let M₂ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ 0)
  have hM₁ : 0≤M₁ := apply_nonneg _ _
  have hM₂ : 0≤M₂ := apply_nonneg _ _
  have hbound₁ (x : ℝ) : ‖W₁ x‖≤M₁ := by
    rw [←normPowerProfile_norm W₁ a₁ b₁ ha₁ hs₁ hW₁ 0 x]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hbound₂ (x : ℝ) : ‖W₂ x‖≤M₂ := by
    rw [←normPowerProfile_norm W₂ a₂ b₂ ha₂ hs₂ hW₂ 0 x]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  let D : ℝ := 2*(128*b₁*M₁)*(128*b₂*M₂)
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨C+D,by positivity,?_⟩
  intro Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hpow : 0≤Z^ε := Real.rpow_nonneg (zero_le_one.trans hZ) _
  by_cases hlarge : 1≤L
  · rw [max_eq_right hlarge]
    exact (hcancel Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L
      hL hX₁ hX₂ hY₁ hY₂ hpX hpY).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) hpow) (by positivity))
          (div_nonneg (Real.sqrt_nonneg _) hL.le))
  · rw [max_eq_left (le_of_not_ge hlarge),div_one]
    have ha := normalized_rectangle_absolute η m A z W₁ W₂ b₁ b₂ M₁ M₂ hb₁ hb₂ hM₁ hM₂
      (fun _ hx=>(hs₁ hx).2) (fun _ hx=>(hs₂ hx).2) hbound₁ hbound₂
      t X₁ X₂ Y₁ Y₂ T (hL.trans_le hX₁) (hL.trans_le hX₂)
      (hL.trans_le hY₁) (hL.trans_le hY₂) hpX hpY
    apply ha.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg T)
    calc
      D≤C+D := le_add_of_nonneg_left hC.le
      _≤(C+D)*Z^ε := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hε.le)
      _≤(C+D)*Z^ε*(1+‖t‖)^J := le_mul_of_one_le_right (by positivity)
        (one_le_pow₀ (by linarith [norm_nonneg t]))

theorem actual_capped_slots
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∀W₁ W₂ : ℝ→ℂ,
      ∀_hs₁ : Function.support W₁⊆Set.Icc a₁ b₁,
      ∀_hs₂ : Function.support W₂⊆Set.Icc a₂ b₂,
      ∀_hW₁ : ContDiff ℝ ∞ W₁,∀_hW₂ : ContDiff ℝ ∞ W₂,
      ∃C : ℝ,0<C ∧ ∀(ι : Type*) [Fintype ι],∀Z : ℝ,1≤Z →
      ∀(η : Character)(m A z : O),m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S : ι→Finset (Ideal O))(β : ι→Ideal O→ℂ)(P b M : ι→ℝ),
      (∀i,0<P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
        C*Z^ε*(1+‖t‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,P i)/max 1 L) := by
  obtain ⟨J,hJ⟩ := capped_rectangle_uniform_degree a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro ι _ Z hZ η m A z hm hA hz hml hm2 hc he S β P b M hP hb hM hβ hN
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) t‖≤(128*b i*M i)*P i := by
    convert rowSlot_bound η m A z (S i) (β i) t (b i*P i) (M i)
      (mul_nonneg (hb i) (hP i).le) (hM i) (hβ i) (hN i) using 1; ring
  exact whole_product_normalization _ (fun i=>rowSlot η m A z (S i) (β i) t)
    (fun i=>128*b i*M i) P (C*Z^ε*(1+‖t‖)^J) T (max 1 L) (by positivity) hT
    (zero_lt_one.trans_le (le_max_left _ _))
    (fun i=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hP hslots
    (hbound Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

theorem actual_canonical_capped_energy
    (a₁ b₁ a₂ b₂ ε B:ℝ) (ha₁:0<a₁) (ha₂:0<a₂)
    (hb₁:0≤b₁) (hb₂:0≤b₂) (hε:0<ε) (hB:0≤B) :
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∀W₁ W₂:ℝ→ℂ,Function.support W₁⊆Set.Icc a₁ b₁ →
      Function.support W₂⊆Set.Icc a₂ b₂ → ContDiff ℝ ∞ W₁ → ContDiff ℝ ∞ W₂ →
      ∃C0:ℝ,0<C0 ∧ ∀(ι:Type*) [Fintype ι],∀Z:ℝ,1<Z →
      ∀(η:Character) (χ:RayFourExpansion.RayCharacter) (C D:Ideal O) (_hC:Supported C)
        (U:Finset (CommonIndex C D)),IsCoprime Q C → idealCoeff η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m A z) →
      (∀z∈rows,(HeckeRowClosure.rowConductorBound (childCharacter η χ) m 1 (A*z):ℝ)≤Z^B) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b Ms:ι→ℝ),
      (∀i,0<P i) → (∀i,0≤b i) → (∀i,0≤Ms i) →
      (∀i,∀I∈S i,‖β i I‖≤Ms i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L:ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      (∑z∈rows,‖centeredSlotRow (childCharacter η χ) m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2)≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun p:CommonIndex C D=>p.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6))*
        (C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/max 1 L))^2 := by
  obtain ⟨J,hJ⟩:=actual_capped_slots a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ0 hQ hQ72 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C0,hC0,hpoint⟩:=hJ Q hQ0 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C0,hC0,?_⟩
  intro ι _ Z hZ η χ C D hC U hQC hη m hm hmLam hm2 A rows hrows hex hcond Cr M hCr hN
    S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hA:A≠0:=mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  have hc:=actual_canonical_exceptional_count η χ C D hC U Q hQ0 hQ hQ72 hQC hη m hm hmLam hm2
    rows hrows hex Z Cr M hZ hCr hN
  have hp:∀z∈rows,‖centeredSlotRow (childCharacter η χ) m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
      C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/max 1 L):=by
    intro z hz
    exact hpoint ι Z hZ.le (childCharacter η χ) m A z hm hA (hrows z hz) hmLam hm2
      (hcond z hz) (hex z hz) S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hXT hYT
  calc
    _≤∑z∈rows,(C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/max 1 L))^2 :=
      Finset.sum_le_sum (fun z hz=>pow_le_pow_left₀ (norm_nonneg _) (hp z hz) 2)
    _=(rows.card:ℝ)*(C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/max 1 L))^2 := by simp
    _≤_:=mul_le_mul_of_nonneg_right hc (sq_nonneg _)

theorem max_raw_reduction (Z Rred r : ℝ) (hZ : 1<Z) (hR : 0<Rred) :
    max 1 (Z^r/Rred)=Z^(max (r-Real.logb Z Rred) 0) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have he : Z^r/Rred=Z^(r-Real.logb Z Rred) := by
    rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hR]
  rw [he]
  by_cases h : 0≤r-Real.logb Z Rred
  · rw [max_eq_left h,max_eq_right (Real.one_le_rpow hZ.le h)]
  · rw [max_eq_right (le_of_not_ge h),Real.rpow_zero,
      max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ.le (le_of_not_ge h))]

theorem reciprocal_max_raw_reduction (Z Rred r : ℝ) (hZ : 1<Z) (hR : 0<Rred) :
    1/max 1 (Z^r/Rred)=Z^(-max (r-Real.logb Z Rred) 0) := by
  rw [max_raw_reduction Z Rred r hZ hR,Real.rpow_neg (zero_le_one.trans hZ.le),one_div]

theorem allocation_reciprocal_max {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : CenteredMomentActiveDivisorShell.Source ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (Z r : ℝ) (hZ : 1<Z) :
    1/max 1 (Z^r/formalReductionFactor D a s.P)=
      Z^(-max (r-Real.logb Z (formalReductionFactor D a s.P)) 0) := by
  apply reciprocal_max_raw_reduction Z _ r hZ
  exact mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))

end SevenEighths.CenteredMomentExceptionalCappedAmplitude

end

end OAI

end Source677

/- Original source: OAI/NumberTheory/DirichletL/Moments/AllocatedCenteredCapped.lean; sha256: c7b8685be7124aa99d89ef9642f008a21f2cbc1fa43479fd06e69000f28ee7b7 -/
section Source678
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentAllocatedCenteredCapped
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle CenteredMomentExceptionalCappedAmplitude
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma plain_norm_le_reduction (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,1≤P i) (j:Fin 2):
    (Ideal.absNorm (selectedPlain L a j):ℝ)≤formalReductionFactor L a P:=by
  have hN (k:Fin 2):(1:ℝ)≤Ideal.absNorm (selectedPlain L a k):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr k)))
  have hh:(Ideal.absNorm (selectedPlain L a j):ℝ)≤selectedNorm L a:=by
    fin_cases j
    · exact le_mul_of_one_le_right (by positivity) (hN 1)
    · exact le_mul_of_one_le_left (by positivity) (hN 0)
  exact hh.trans (le_mul_of_one_le_right (selectedNorm_pos L a).le
    (Finset.one_le_prod₀ (fun i _=>hP i)))

lemma allocated_lower (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,1≤P i) (Z r X:ℝ) (hZ:0<Z) (hX:Z^r≤X) (j:Fin 2):
    Z^r/formalReductionFactor L a P≤X/(Ideal.absNorm (selectedPlain L a j):ℝ):=by
  have hn:(0:ℝ)<Ideal.absNorm (selectedPlain L a j):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr j)))
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hZ.le _) hn
    (plain_norm_le_reduction L a P hP j)).trans (div_le_div_of_nonneg_right hX hn.le)

lemma remaining_volume (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,0<P i) (T:ℝ):
    (T/selectedNorm L a)*(∏i:liveIndices L a,P i)=
      (T*∏i,P i)/formalReductionFactor L a P:=by
  rw [Finset.prod_coe_sort]
  apply (eq_div_iff (mul_pos (selectedNorm_pos L a) (Finset.prod_pos (fun i _=>hP i))).ne').mpr
  exact raw_scale_identity L a T P

 theorem actual_allocated_capped_energy
    (a₁ b₁ a₂ b₂ ε B:ℝ) (ha₁:0<a₁) (ha₂:0<a₂)
    (hb₁:0≤b₁) (hb₂:0≤b₂) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∀W₁ W₂:ℝ→ℂ,Function.support W₁⊆Set.Icc a₁ b₁ →
      Function.support W₂⊆Set.Icc a₂ b₂ → ContDiff ℝ ∞ W₁ → ContDiff ℝ ∞ W₂ →
      ∃C0:ℝ,0<C0 ∧ ∀(ι:Type*) [Fintype ι] [DecidableEq ι],∀Z:ℝ,1<Z →
      ∀(η:Character) (χ:RayFourExpansion.RayCharacter) (C D:Ideal O) (_hC:Supported C)
        (U:Finset (CommonIndex C D)),IsCoprime Q C → idealCoeff η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m A z) →
      (∀z∈rows,(HeckeRowClosure.rowConductorBound (childCharacter η χ) m 1 (A*z):ℝ)≤Z^B) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b Ms:ι→ℝ),
      (∀i,1≤P i) → (∀i,0≤b i) → (∀i,0≤Ms i) →
      (∀i,∀I∈S i,‖β i I‖≤Ms i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀(L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2))),
      ∀t X₁ X₂ Y₁ Y₂ T r:ℝ,Z^r≤X₁ → Z^r≤X₂ → Z^r≤Y₁ → Z^r≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      (∑z∈rows,‖residualCenteredRow (childCharacter η χ) m A z t S β P L a W₁ W₂ X₁ X₂ Y₁ Y₂ T‖^2)≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun p:CommonIndex C D=>p.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6))*
        (C0*Z^ε*(1+‖t‖)^J*(∏i:liveIndices L a,128*b i*Ms i)*
          (Real.sqrt ((T*∏i,P i)/formalReductionFactor L a P)/
            Z^(max (r-Real.logb Z (formalReductionFactor L a P)) 0)))^2:=by
  obtain ⟨J,hJ⟩:=actual_canonical_capped_energy a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ0 hQ hQ72 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C0,hC0,hbound⟩:=hJ Q hQ0 hQ hQ72 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C0,hC0,?_⟩
  intro ι _ _ Z hZ η χ C D hC U hQC hη m hm hmLam hm2 A rows hrows hex hcond Cr M hCr hN
    S β P b Ms hP hb hMs hβ hNs L a t X₁ X₂ Y₁ Y₂ T r hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hp (i:ι):0<P i:=zero_lt_one.trans_le (hP i)
  have hred:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hp i))
  have hh:=hbound (liveIndices L a) Z hZ η χ C D hC U hQC hη m hm hmLam hm2 rows hrows hex hcond Cr M hCr hN
    (fun i=>S i) (fun i=>β i) (fun i=>P i) (fun i=>b i) (fun i=>Ms i)
    (fun i=>hp i) (fun i=>hb i) (fun i=>hMs i) (fun i=>hβ i) (fun i=>hNs i)
    t (X₁/Ideal.absNorm (selectedPlain L a 0)) (X₂/Ideal.absNorm (selectedPlain L a 1))
    (Y₁/Ideal.absNorm (selectedPlain L a 0)) (Y₂/Ideal.absNorm (selectedPlain L a 1))
    (T/selectedNorm L a) (Z^r/formalReductionFactor L a P)
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hred)
    (allocated_lower L a P hP Z r X₁ (zero_lt_one.trans hZ) hX₁ 0)
    (allocated_lower L a P hP Z r X₂ (zero_lt_one.trans hZ) hX₂ 1)
    (allocated_lower L a P hP Z r Y₁ (zero_lt_one.trans hZ) hY₁ 0)
    (allocated_lower L a P hP Z r Y₂ (zero_lt_one.trans hZ) hY₂ 1)
    (by rw [div_mul_div_comm,hXT];rfl) (by rw [div_mul_div_comm,hYT];rfl)
  rw [remaining_volume L a P hp T,max_raw_reduction Z _ r hZ hred] at hh
  exact hh

end SevenEighths.CenteredMomentAllocatedCenteredCapped

end

end OAI

end Source678

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorProfiles.lean; sha256: d19cb167702eb17958b3eafc3240e81d28d4013382e3197c624f33a7a866bf44 -/
section Source679
namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

def expNeg (x : ℝ) : ℂ := Complex.exp (-(x : ℂ))

lemma expNeg_smooth : ContDiff ℝ ∞ expNeg := by
  exact Complex.ofRealCLM.contDiff.neg.cexp

lemma expNeg_hasDerivAt (x : ℝ) : HasDerivAt expNeg (-expNeg x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).neg).cexp
  convert! h using 1; simp [expNeg]

lemma iteratedDeriv_expNeg (n : ℕ) :
    iteratedDeriv n expNeg = fun x => (-1 : ℂ)^n*expNeg x := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, (expNeg_hasDerivAt x).deriv, pow_succ]
    ring

lemma expNeg_derivative_norm (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n expNeg x‖ = Real.exp (-x) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expNeg]
  simp [expNeg, norm_pow, Complex.norm_exp]

lemma expNeg_derivative_decay (n i : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1+x)^n*‖iteratedFDeriv ℝ i expNeg x‖ ≤ (n.factorial : ℝ)*Real.exp 1 := by
  rw [expNeg_derivative_norm]
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (1+x) (by linarith : 0 ≤ 1+x) n)
  calc
    _ ≤ (Real.exp (1+x)*(n.factorial : ℝ))*Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by
      rw [mul_right_comm, ← Real.exp_add, show (1+x)+(-x) = 1 by ring]
      ring

def productProfile (Ω V T : ℝ → ℂ) (A B C s : ℝ) : ℂ :=
  Ω s*(1-V (A*s))*expNeg (B*s)*T (C*s)

def inverseProfile (W V : ℝ → ℂ) (R x : ℝ) : ℂ := W x*V (R*x)

def logSourceFun (Ω V T : ℝ → ℂ) (A B C y : ℝ) : ℂ :=
  Ω y*(1-V (A*Real.exp y))*expNeg (B*Real.exp y)*T (C*Real.exp y)

lemma logSource_smooth (Ω V T : ℝ → ℂ) (hΩ : ContDiff ℝ ∞ Ω)
    (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T) (A B C : ℝ) :
    ContDiff ℝ ∞ (logSourceFun Ω V T A B C) := by
  unfold logSourceFun
  have hE := expNeg_smooth
  fun_prop

lemma logSource_compact (Ω V T : ℝ → ℂ) (hΩ : HasCompactSupport Ω) (A B C : ℝ) :
    HasCompactSupport (logSourceFun Ω V T A B C) :=
  ((hΩ.mul_right).mul_right).mul_right

def logSource (Ω V T : ℝ → ℂ) (hΩc : HasCompactSupport Ω)
    (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B C : ℝ) : SchwartzMap ℝ ℂ :=
  (logSource_compact Ω V T hΩc A B C).toSchwartzMap (logSource_smooth Ω V T hΩ hV hT A B C)

@[simp] lemma logSource_apply (Ω V T : ℝ → ℂ) (hΩc : HasCompactSupport Ω)
    (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B C y : ℝ) :
    logSource Ω V T hΩc hΩ hV hT A B C y =
      Ω y*(1-V (A*Real.exp y))*expNeg (B*Real.exp y)*T (C*Real.exp y) := rfl

end
end SevenEighths.HeckeDetectorProfiles

end OAI

end Source679
