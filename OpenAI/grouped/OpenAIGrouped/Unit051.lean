import OpenAIGrouped.Unit050
import OpenAIGrouped.Unit022
import OpenAIGrouped.Unit025
import OpenAIGrouped.Unit047
import OpenAIGrouped.Unit024
import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit048
import OpenAIGrouped.Unit046
import OpenAIGrouped.Unit016
import OpenAIGrouped.Unit049
import OpenAIGrouped.Unit021

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstWindowBudgets.lean; sha256: 1e7ee603a0c52c9a86413c7a52c97dfd75ecb1229ecdb8bf9301c825b0664310 -/
section Source2040
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstWindowBudgets
open CenteredMomentSecondWindowBudget

lemma sqrt_sum_le {α:Type*}(s:Finset α)(E:α→ℝ)(hE:∀i∈s,0≤E i):
    Real.sqrt (∑i∈s,E i)≤∑i∈s,Real.sqrt (E i):=by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    have he:0≤E a:=hE a (Finset.mem_insert_self _ _)
    have hs:0≤∑i∈s,E i:=Finset.sum_nonneg (fun i hi=>hE i (Finset.mem_insert_of_mem hi))
    have hadd:Real.sqrt (E a+∑i∈s,E i)≤Real.sqrt (E a)+Real.sqrt (∑i∈s,E i):=by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [Real.sq_sqrt he,Real.sq_sqrt hs,
          mul_nonneg (Real.sqrt_nonneg (E a)) (Real.sqrt_nonneg (∑i∈s,E i))]
    exact hadd.trans (add_le_add le_rfl (ih (fun i hi=>hE i (Finset.mem_insert_of_mem hi))))

lemma windowBudget_sum {α:Type*}(s:Finset α)(E:α→ℝ)(hE:∀i∈s,0≤E i)
    (J:ℕ)(t:ℝ):
    windowBudget J t (∑i∈s,E i)≤∑i∈s,windowBudget J t (E i):=by
  unfold windowBudget
  rw [←Finset.sum_mul,←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (sqrt_sum_le s E hE) (pow_nonneg (heightEnvelope_pos t).le _))
    (profileMoment_nonneg J)

theorem windowBudget_pair_sum {α β:Type*}(s:Finset α)(u:Finset β)
    (E:α→ℝ)(F:β→ℝ)(hE:∀i∈s,0≤E i)(hF:∀j∈u,0≤F j)
    (J₁ J₂:ℕ)(t:ℝ):
    windowBudget J₁ t (∑i∈s,E i)*windowBudget J₂ t (∑j∈u,F j)≤
      ∑i∈s,∑j∈u,windowBudget J₁ t (E i)*windowBudget J₂ t (F j):=by
  have hh:=mul_le_mul (windowBudget_sum s E hE J₁ t) (windowBudget_sum u F hF J₂ t)
    (windowBudget_nonneg J₂ t _) (Finset.sum_nonneg (fun i _=>windowBudget_nonneg J₁ t (E i)))
  apply hh.trans_eq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
universe u

theorem actual_annular_block_from_four_budgets (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ E₁ E₂ : Ideal O→Fin 4→ℝ,
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ i,0≤E₁ L i) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ i,0≤E₂ L i) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (∑i,E₁ L i)*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (∑i,E₂ L i)*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        ∑ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ t (E₁ L i)*windowBudget J₂ t (E₂ L j)) := by
  obtain ⟨Cb,hCb,hbound⟩:=CenteredMomentFirstPhysicalAnnularCommonBound.actual_annular_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n E₁ E₂ hE₁ hE₂ hleft hright
  have hh:=hbound η s t C D hC hD hCD E rows K hK n
    (fun L=>∑i,E₁ L i) (fun L=>∑i,E₂ L i)
    (fun L hL=>Finset.sum_nonneg (fun i _=>hE₁ L hL i))
    (fun L hL=>Finset.sum_nonneg (fun i _=>hE₂ L hL i)) hleft hright
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) hCb)
  apply Finset.sum_le_sum
  intro L hL
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact windowBudget_pair_sum Finset.univ Finset.univ (E₁ L) (E₂ L)
    (fun i _=>hE₁ L hL i) (fun i _=>hE₂ L hL i) J₁ J₂ t

end SevenEighths.CenteredMomentFirstWindowBudgets

end

end OAI

end Source2040

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstMixedWindow.lean; sha256: 349212a0ddb54397437f9aa743dcd4854a1e964e88b479709c2c0a0bb67b6166 -/
section Source2041
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMixedWindow
open CenteredMomentFirstMixedRoot CenteredMomentFirstMixedAllowance CenteredMomentSecondWindowBudget
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentCompleteCommon
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstNonexceptionalPrefactor
local notation "O"=>HeckeFamily.O

theorem original_four_budget_reference {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair s.η C D hC E ξ₁ ξ₂)
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z:ℝ)(EL ER:Fin 4→ℝ)(JL JR:ℕ)(height:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(hZ:1<Z)
    (hEL:∀i,0≤EL i)(hER:∀i,0≤ER i)(hwin:∀i y,U i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=volume s.toData;
    ‖scalar C D hC E K A₀ B₀‖/V*
      (∑i:Fin 4,∑j:Fin 4,
        windowBudget JL height ((F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL i)*
        windowBudget JR height ((F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER j))≤
      (‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*
        (s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm)*
        (∑i:Fin 4,∑j:Fin 4,windowBudget JL height (EL i)*windowBudget JR height (ER j)) :=by
  dsimp only
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hh:=original_fixed_reference_pair s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂
    m A t S C D hC hD hCD E ξ₁ ξ₂ F rows W U K K₀ H₀ A₀ B₀ M Z
    (EL i) (ER j) hK hA hB hZ (hEL i) (hER j) hwin hn
  have hqL:0<(F.left.modulus.absNorm:ℝ):=norm_pos _ F.left.modulus_ne_bot
  have hqR:0<(F.right.modulus.absNorm:ℝ):=norm_pos _ F.right.modulus_ne_bot
  have hCpos:=norm_pos C hC.1
  have hDpos:=norm_pos D hD.1
  have hV:=volume_pos s.toData
  have hz:0<Z:=zero_lt_one.trans hZ
  have hei:=hEL i
  have herj:=hER j
  have hh':=mul_le_mul_of_nonneg_right hh
    (mul_nonneg (mul_nonneg (pow_nonneg (heightEnvelope_pos height).le JL)
      (profileMoment_nonneg JL)) (mul_nonneg (pow_nonneg (heightEnvelope_pos height).le JR)
      (profileMoment_nonneg JR)))
  simp only [Real.sqrt_mul (by positivity : 0≤
    (F.left.modulus.absNorm:ℝ)*(volume s.toData/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL i),
    Real.sqrt_mul (hEL i)] at hh'
  unfold windowBudget
  nlinarith only [hh']

end SevenEighths.CenteredMomentFirstMixedWindow

end

end OAI

end Source2041

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstReferenceBlock.lean; sha256: 5d554551189b5bbc264562201da53ddc96adad2ecc5c5084d13ef98a16ef27a4 -/
section Source2042
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstReferenceBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentFirstDivisorSupport CenteredMomentChildAssembly
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSecondWindowBudget
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentMobiusRegroup
open CenteredMomentSecondHeightFamily CenteredMomentFirstPhysicalAnnularCommonBound
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstMixedAllowance
open CenteredMomentFirstMixedWindow CenteredMomentFirstWindowBudgets
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
local notation "O"=>HeckeFamily.O

theorem actual_reference_block (W:𝓢(ℝ,ℂ)) (decay J₁ J₂:ℕ)
    (B δ:ℝ)(hB:0≤B)(hδ:0<δ):
    ∃Cb:ℝ,0<Cb ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{ι:Type*}[Fintype ι][DecidableEq ι],∀s:Input ι,∀R seed:Ideal O,
    ∀a₁ a₂:ℝ,0<a₁→0<a₂→
    (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀E:Finset (CommonIndex C D),∀ξ₁ ξ₂:RayCharacter,
    ∀F:FixedPair s.η C D hC E ξ₁ ξ₂,∀rows:Finset O,∀K:ℝ,0<K→∀n:Fin 4→ℤ,
    sourceRadius s/(D.absNorm:ℝ)≤Z^B→∀EL ER:Fin 4→ℝ,(∀i,0≤EL i)→(∀i,0≤ER i)→
    let V:=volume s;
    let refL:=(F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z);
    let refR:=(F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z);
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 (original s R seed).columns))
      (fun b=>Ideal.span {element C D hD.1 (original s R seed).columns b}),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) C hC (fixedPair s.η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        ((∑i,refL*EL i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁))→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 (original s R seed).columns))
      (fun b=>Ideal.span {element C D hD.1 (original s R seed).columns b}),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) D hD (fixedPair s.η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        ((∑i,refR*ER i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂))→
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay*
      ‖block s.η (fixedBadMask*idealGenerator R) 1 s.t (original s R seed).columns
        (original s R seed).beta C D hC hD E rows W (fun _=>logAnnulus)
        K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))‖/V≤
      Cb*Z^δ*(‖inactiveWeight C D E‖*(Real.exp (Real.log 4)/((∏i,s.lo i)*a₁*a₂))*
        fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm)*
      (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (EL i)*windowBudget J₂ s.t (ER j)):=by
  obtain ⟨Cb,hCb,hev⟩:=CenteredMomentFirstDivisorCommonBound.actual_supported_annular_harmonic
    W decay J₁ J₂ B δ hB hδ
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ _ s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ C D hC hD hCD E ξ₁ ξ₂ F rows K hK n hcap EL ER hEL hER
    V refL refR hleft hright
  have hz:0≤Z:=zero_le_one.trans hZ.1.le
  have hcb:0≤Cb:=hCb.le
  have hf:0≤fixedPresentationCost:=fixedPresentationCost_pos.le
  have hprodlo:0≤∏i,s.lo i:=Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)
  have hV:0<V:=volume_pos s
  have hRL:0≤refL:=by dsimp [refL]; positivity
  have hRR:0≤refR:=by dsimp [refR]; positivity
  have hLE:∀i:Fin 4,0≤refL*EL i:=fun i=>mul_nonneg hRL (hEL i)
  have hRE:∀i:Fin 4,0≤refR*ER i:=fun i=>mul_nonneg hRR (hER i)
  have hz₁:s.W₁ 0=0:=by by_contra hn;have hh:=hs₁ 0 hn;linarith
  have hz₂:s.W₂ 0=0:=by by_contra hn;have hh:=hs₂ 0 hn;linarith
  have hb:=hZ.2 s.η (original s R seed) s.t C D hC hD hCD E rows K hK n
    (sourceRadius s) (fun I hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2)
    hcap (∑i,refL*EL i) (∑i,refR*ER i)
    (Finset.sum_nonneg (fun i _=>hLE i)) (Finset.sum_nonneg (fun i _=>hRE i)) hleft hright
  have hw:=windowBudget_pair_sum Finset.univ Finset.univ (fun i=>refL*EL i) (fun i=>refR*ER i)
    (fun i _=>hLE i) (fun i _=>hRE i) J₁ J₂ s.t
  have hb':=hb.trans (mul_le_mul_of_nonneg_left hw (by positivity))
  by_cases hn:block s.η (fixedBadMask*idealGenerator R) 1 s.t (original s R seed).columns
      (original s R seed).beta C D hC hD E rows W (fun _=>logAnnulus)
      K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))=0
  · simp only [hn,norm_zero,mul_zero,zero_div]
    have he:0≤∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (EL i)*windowBudget J₂ s.t (ER j):=
      Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>mul_nonneg
        (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))
    positivity
  · have href:=original_four_budget_reference s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂
      (fixedBadMask*idealGenerator R) 1 s.t (original s R seed).columns C D hC hD hCD E
      ξ₁ ξ₂ F rows W (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) (Real.log 4) Z EL ER J₁ J₂ s.t hK
      (dyadicScale_pos _) (dyadicScale_pos _) hZ.1 hEL hER
      (fun _ x hx=>by
        have hh:=logAnnulus_support hx
        exact abs_le.mpr ⟨hh.1,hh.2.trans (Real.log_nonneg (by norm_num))⟩) hn
    have hh:=div_le_div_of_nonneg_right hb' hV.le
    have hscale:0≤Cb*Z^δ:=by positivity
    have hmul:=mul_le_mul_of_nonneg_left href hscale
    calc
      _ ≤ _ := hh
      _ = Cb*Z^δ*(‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖/V*
          (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (refL*EL i)*windowBudget J₂ s.t (refR*ER j))) := by ring
      _ ≤ _ := by convert hmul using 1 <;> (try dsimp [refL,refR,V,volume,CenteredMomentExceptionalAmplitudePair.volume]) ; ring

end SevenEighths.CenteredMomentFirstReferenceBlock

end

end OAI

end Source2042

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalActiveDictionary.lean; sha256: 72cb6c8f4f79024e0737c00b1ba7117c832d2cc425b061fb6ff3fee1b6f8f3fc -/
section Source2043
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalActiveDictionary
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentScale CenteredMomentPrimitive IdealMobiusDivisorSum
open CenteredMomentFirstPhysicalSource CenteredMomentActiveSource
local notation "O" => HeckeFamily.O

theorem columns_active (C D : Ideal O) (hD : D≠0) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) :
    columns C D hD (activeSource S β)=
      (columns C D hD S).filter (fun I=>β (D*I)≠0) := by
  ext I
  simp only [columns,Finset.mem_filter,mem_residualPool,supportedColumns_active]
  tauto

theorem element_value (C D : Ideal O) (hD : D≠0) (S : Finset (Ideal O))
    (I : columns C D hD S) :
    element C D hD S I=CompletedGauss.primaryGenerator (I:Ideal O) := rfl

theorem column_sum_active (C D : Ideal O) (hD : D≠0) (S : Finset (Ideal O))
    (β f : Ideal O→ℂ) (hf : ∀I,β (D*I)=0→f I=0) :
    (∑I∈columns C D hD (activeSource S β),f I)=∑I∈columns C D hD S,f I := by
  rw [columns_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi : β (D*I)=0
  · simp only [hi,ne_eq,not_true_eq_false,ite_false,hf I hi]
  · simp only [hi,ne_eq,not_false_eq_true,ite_true]

theorem column_pair_sum_active (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (f : Ideal O→Ideal O→ℂ)
    (hl : ∀I J,β (C*I)=0→f I J=0) (hr : ∀I J,β (D*J)=0→f I J=0) :
    (∑I∈columns C C hC (activeSource S β),∑J∈columns C D hD (activeSource S β),f I J)=
      ∑I∈columns C C hC S,∑J∈columns C D hD S,f I J := by
  simp_rw [column_sum_active C D hD S β _ (fun J h=>hr _ J h)]
  apply column_sum_active C C hC S β
  intro I hi
  exact Finset.sum_eq_zero (fun J hJ=>hl I J hi)

lemma primary_supported (I : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {CompletedGauss.primaryGenerator I}) := by
  rw [primary_span_supported I hI]
  exact hI

def physicalTerm (η : Character) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) : ℂ :=
  if hI : Supported I then if hJ : Supported J then
    let na:=CompletedGauss.primaryGenerator I
    let nb:=CompletedGauss.primaryGenerator J
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
    let k:=K/‖eisEmbedding e‖^2
    let r:=activeConductor C D
    if IsCoprime I J then
      (tripleRow na nb r (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) e *
      ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
      tripleFourier na nb r
        (supported_element_ne_zero _ (primary_supported I hI))
        (supported_element_ne_zero _ (primary_supported J hJ))
        (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) h)*
      (coefficient η m A t β C I*star (coefficient η m A t β D J))*
      windows V (k/‖eisEmbedding r‖^2) (‖eisEmbedding h‖^2)
        (‖eisEmbedding na‖^2) (‖eisEmbedding nb‖^2) K₀ H₀ A₀ B₀*
      EisensteinSchwartzPoisson.paperRadialFourier W
        (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
    else 0
  else 0 else 0

theorem physicalTerm_zero_left (η : Character) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) (hi : β (C*I)=0) :
    physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J=0 := by
  simp only [physicalTerm,coefficient,hi,zero_mul,mul_zero]
  split_ifs <;> rfl

theorem physicalTerm_zero_right (η : Character) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) (hj : β (D*J)=0) :
    physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J=0 := by
  simp only [physicalTerm,coefficient,hj,zero_mul,star_zero,mul_zero]
  split_ifs <;> rfl

theorem block_eq_ideal_sums (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      inactiveWeight C D E * ∑h∈rows,
        ∑I∈columns C C hC.1 S,∑J∈columns C D hD.1 S,
          physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J := by
  unfold block
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _=∑I:columns C C hC.1 S,∑J:columns C D hD.1 S,
        physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro J hJ
      simp only [physicalTerm,dite_eq_left (column_supported C C hC.1 S I),
        dite_eq_left (column_supported C D hD.1 S J),element]
      rfl
    _=_ := by
      simp_rw [Finset.sum_coe_sort]
      exact Finset.sum_coe_sort (columns C C hC.1 S)
        (fun I=>∑J∈columns C D hD.1 S,
          physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J)

theorem block_active (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t (activeSource S β) β C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀ := by
  rw [block_eq_ideal_sums,block_eq_ideal_sums]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  exact column_pair_sum_active C D hC.1 hD.1 S β
    (physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h)
    (fun I J hi=>physicalTerm_zero_left η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J hi)
    (fun I J hj=>physicalTerm_zero_right η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J hj)

theorem block_active_ne_zero_iff (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t (activeSource S β) β C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0 ↔
      block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0 := by
  rw [block_active]

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
open CenteredMomentCommonRadialData CenteredMomentFirstRetainedNorm
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentLogDyadic

theorem original_dyadic_block_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
    block s.η m A t (activeSource S β) β C D hC hD E rows W
      (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))=
    block s.η m A t S β C D hC hD E rows W
      (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  apply block_active

theorem original_sector_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sector s R seed m A t
        (activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed))
        C D hC hD W K X Z ξ=
      sector s R seed m A t S C D hC hD W K X Z ξ := by
  unfold sector
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  apply Finset.sum_congr rfl
  intro n hn
  apply block_active

theorem original_sectorMass_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sectorMass s R seed m A t
        (activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed))
        C D hC hD W K X Z ξ=
      sectorMass s R seed m A t S C D hC hD W K X Z ξ := by
  unfold sectorMass
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  apply Finset.sum_congr rfl
  intro n hn
  rw [block_active]

theorem original_retained_full_sectorMass [DecidableEq ι] (s : Input ι) (R seed : Ideal O)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) (hK : 0<K) :
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
    let T:=activeSource S β
    ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S β W K X Z ξ‖≤
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ := by
  dsimp only
  apply (original_retained_norm s R seed hz₁ hz₂ m A t S W K X Z ξ hK).trans_eq
  apply Finset.sum_congr rfl
  intro p hp
  exact original_sectorMass_active s R seed m A t S _ _ _ _ W K X Z ξ

theorem active_sectorMass_sum (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (Φ : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    let T:=activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (∑p:commonLabels (supportedColumns T) (supportedColumns T),
      sectorMass s R seed m A t T p.val.1 p.val.2
        (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K X Z ξ)=
    ∑p:commonLabels (supportedColumns T) (supportedColumns T),
      sectorMass s R seed m A t S p.val.1 p.val.2
        (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K X Z ξ := by
  dsimp only
  apply Finset.sum_congr rfl
  intro p hp
  exact original_sectorMass_active s R seed m A t S _ _ _ _ Φ K X Z ξ

theorem physicalMass_full_source [DecidableEq ι] (s : Input ι) (R seed : Ideal O)
    (m A : O) (Φ : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    CenteredMomentFirstSourceReduction.physicalMass s R seed m A Φ K Z ξ=
      let S:=CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)
      let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
      let T:=activeSource S β
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A s.t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
          (CenteredMomentExceptionalAmplitudePair.volume s.toData) Z ξ := by
  exact active_sectorMass_sum s R seed m A s.t
    (CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)) Φ K
    (CenteredMomentExceptionalAmplitudePair.volume s.toData) Z ξ

theorem normalized_physicalMass_full_source [DecidableEq ι] (s : Input ι)
    (R seed : Ideal O) (m A : O) (Φ : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    CenteredMomentFirstSourceReduction.physicalMass s R seed m A Φ K Z ξ /
        CenteredMomentExceptionalAmplitudePair.volume s.toData=
      let S:=CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)
      let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
      let T:=activeSource S β
      (∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A s.t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
          (CenteredMomentExceptionalAmplitudePair.volume s.toData) Z ξ) /
        CenteredMomentExceptionalAmplitudePair.volume s.toData := by
  exact congrArg (fun x:ℝ=>x/CenteredMomentExceptionalAmplitudePair.volume s.toData)
    (physicalMass_full_source s R seed m A Φ K Z ξ)

end SevenEighths.CenteredMomentFirstPhysicalActiveDictionary

end

end OAI

end Source2043

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalDyadicCount.lean; sha256: 35e6a39c8d07271d064c13d5ae47c84d5ef7463fe85e829b3ec3cdc234408c87 -/
section Source2044
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentDyadicCount

lemma indices_mono_upper (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hbc : b≤c) :
    indices a b ⊆ indices a c := by
  intro n hn
  rw [mem_indices_iff_scale a c ha (hb.trans_le hbc)]
  have h := (mem_indices_iff_scale a b ha hb n).mp hn
  exact ⟨h.1,h.2.trans (by linarith)⟩

lemma blocks_card_le (K R H nC nD : ℝ) (hH : 0<H)
    (hC : 1≤nC) (hD : 1≤nD) :
    Fintype.card (Blocks K R (H/nC) (H/nD)) ≤
      Fintype.card (∀i:Fin 4,↥(indices (![K,1,1,1] i)
        (![K,max 1 R,max 1 H,max 1 H] i))) := by
  have hcol (n : ℝ) (hn : 1≤n) : indices 1 (H/n) ⊆ indices 1 (max 1 H) := by
    apply indices_mono_upper _ _ _ (by norm_num) (div_pos hH (zero_lt_one.trans_le hn))
    exact (div_le_self hH.le hn).trans (le_max_right _ _)
  have hs (i : Fin 4) : bands K R (H/nC) (H/nD) i ⊆
      indices (![K,1,1,1] i) (![K,max 1 R,max 1 H,max 1 H] i) := by
    fin_cases i
    · exact Finset.Subset.refl _
    · intro n hn
      obtain ⟨hr,q,hq,hne⟩ := (mem_retainedIndices R n).mp hn
      exact retained_integral_mem R q hq n hr hne
    · exact hcol nC hC
    · exact hcol nD hD
  let f : Blocks K R (H/nC) (H/nD) →
      (∀i:Fin 4,↥(indices (![K,1,1,1] i) (![K,max 1 R,max 1 H,max 1 H] i))) :=
    fun x i => ⟨x i,hs i (x i).property⟩
  apply Fintype.card_le_of_injective f
  intro x y hxy
  funext i
  apply Subtype.ext
  exact congrArg (fun z => (z i).val) hxy

theorem blocks_subpower (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (_hCr : 0<Cr) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀K R H nC nD : ℝ,0<K → 0<H → 1≤nC → 1≤nD →
      R≤Cr*Z^L → H≤Z^B →
      (Fintype.card (Blocks K R (H/nC) (H/nD)):ℝ)≤C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := four_indices_subpower (max 1 Cr) (B+L) ε
    (le_max_left _ _) (add_nonneg hB hL) hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  intro K R H nC nD hK hH hnC hnD hR hHcap
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hp : 1≤Z^(B+L) := Real.one_le_rpow hZ (add_nonneg hB hL)
  have hbound : 1≤max 1 Cr*Z^(B+L) :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) hp
  have hR' : max 1 R≤max 1 Cr*Z^(B+L) := by
    apply max_le hbound
    exact hR.trans (mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
      (Real.rpow_nonneg hz.le _) (by positivity))
  have hH' : max 1 H≤max 1 Cr*Z^(B+L) := by
    apply max_le hbound
    exact hHcap.trans ((Real.rpow_le_rpow_of_exponent_le hZ (by linarith : B≤B+L)).trans
      (le_mul_of_one_le_left (zero_le_one.trans hp) (le_max_left _ _)))
  have hfour := hcount ![K,1,1,1] ![K,max 1 R,max 1 H,max 1 H]
    (by intro i;fin_cases i <;> simp_all)
    (by intro i;fin_cases i <;> simp)
    (by intro i;fin_cases i
        · simpa [div_self hK.ne'] using hbound
        · simpa using hR'
        · simpa using hH'
        · simpa using hH')
  exact (show (Fintype.card (Blocks K R (H/nC) (H/nD)):ℝ)≤
    Fintype.card (∀i:Fin 4,↥(indices (![K,1,1,1] i)
      (![K,max 1 R,max 1 H,max 1 H] i))) by
      exact_mod_cast blocks_card_le K R H nC nD hH hnC hnD).trans hfour

theorem original_blocks_subpower (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D : Ideal ActualEisensteinCubic.O), C≠0 → D≠0 →
      ∀(E : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
        (K R H : ℝ),0<K → 0<H → R≤Cr*Z^L → H≤Z^B →
      (Fintype.card (Blocks (effectiveScale C D E K) R
        (H/Ideal.absNorm C) (H/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩ := blocks_subpower B L Cr ε hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount] with Z hcount
  intro C D hC hD E K R H hK hH hR hHcap
  have norm_one (I : Ideal ActualEisensteinCubic.O) (hI : I≠0) :
      (1:ℝ)≤Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hcount _ _ _ _ _ (effectiveScale_pos C D E K hK) hH
    (norm_one C hC) (norm_one D hD) hR hHcap

end SevenEighths.CenteredMomentFirstPhysicalDyadicCount

end

end OAI

end Source2044

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstNonexceptionalWeightSum.lean; sha256: 2f80e52f9690763995f2ee57a316d63b7bec6f39605e38359198a1d305c8a21a -/
section Source2045
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalWeightSum
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentActiveSource CenteredMomentSupportedCorrelation CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentRankinRadical
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Labels (s:Input ι)(R seed:Ideal O):=
  ActiveLabel (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)

def weight (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K r:ℝ)(p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (τ₁ τ₂:Character)
    (n:Blocks (effectiveScale p.val.1 p.val.2 E K) r
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)):ℝ:=
  let h:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
  if block s.η m A t (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) p.val.1 p.val.2 h.1 h.2 E
      (CenteredMomentSecondRetainedRows.retainedRows r 1) W V K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))=0 then 0
  else ‖scalar p.val.1 p.val.2 h.1 E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*
    volume s.toData/((p.val.1.absNorm:ℝ)*p.val.2.absNorm)*
      Real.sqrt ((τ₁.modulus.absNorm:ℝ)*τ₂.modulus.absNorm)

theorem weight_le (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K r a₁ a₂ M F:ℝ)(hK:0<K)(ha₁:0<a₁)(ha₂:0<a₂)(hF:0≤F)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (hwin:∀i y,V i y≠0→|y|≤M)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(τ₁ τ₂:Character)
    (hc₁:(τ₁.modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor p.val.1 p.val.2)‖^2)
    (hc₂:(τ₂.modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor p.val.1 p.val.2)‖^2)
    (n:Blocks (effectiveScale p.val.1 p.val.2 E K) r
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)):
    weight s R seed m A t W V K r p E τ₁ τ₂ n≤
      ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ))*
        (CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
          (commonRadical p.val.1 p.val.2).absNorm):=by
  have hp:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  unfold weight
  dsimp only
  split_ifs with hn
  · exact mul_nonneg (by positivity)
      (div_nonneg (CenteredMomentFirstInactiveRadicalMass.inactiveWeight_nonneg _ _ _ _)
        (Nat.cast_nonneg _))
  · have hh:=original_scalar_conductors s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ m A t _
      p.val.1 p.val.2 hp.1 hp.2 E _ W V K (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) M F τ₁ τ₂ hK
      (dyadicScale_pos _) (dyadicScale_pos _) hF hwin hn hc₁ hc₂
    convert hh using 1 ;
      simp only [CenteredMomentFirstInactiveRadicalMass.inactiveWeight,Real.rpow_zero,
        div_one,CenteredMomentFirstPhysicalSource.inactiveWeight] ; ring

def sectorWeight (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K r:ℝ)(p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (τ₁ τ₂:Character):ℝ:=
  ∑n:Blocks (effectiveScale p.val.1 p.val.2 E K) r
    (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm),
    weight s R seed m A t W V K r p E τ₁ τ₂ n

def sumWeight (s:Input ι)(R seed:Ideal O)(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K:ℝ)(radius:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ)
    (τ₁ τ₂:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→Character):ℝ:=
  ∑p:Labels s R seed,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
    sectorWeight s R seed m A t W V K (radius p E) p E (τ₁ p E) (τ₂ p E)

theorem original_weight_sum (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,
    ∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι)(R seed:Ideal O),
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→0<sourceRadius s→sourceRadius s≤Z^B→
    ∀(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K a₁ a₂ M F:ℝ),
      0<K→0<a₁→0<a₂→0≤F→
      (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
      (∀i y,V i y≠0→|y|≤M)→
    ∀(radius:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ)
      (τ₁ τ₂:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→Character),
      (∀p E,radius p E≤Cr*Z^L)→
      (∀p E,((τ₁ p E).modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
        ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)‖^2*
        ‖eisEmbedding (activeConductor p.val.1 p.val.2)‖^2)→
      (∀p E,((τ₂ p E).modulus.absNorm:ℝ)≤F*(s.η.modulus.absNorm:ℝ)*
        ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)‖^2*
        ‖eisEmbedding (activeConductor p.val.1 p.val.2)‖^2)→
      sumWeight s R seed m A t W V K radius τ₁ τ₂≤
        ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ))*
          (C₀*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨Cd,hCd,hd⟩:=original_blocks_subpower B L Cr (ε/2) hB hL hCr (by linarith)
  obtain ⟨Cm,hCm,hm⟩:=CenteredMomentFirstInactiveRadicalMass.actual_inactive_radical_mass
    B (ε/2) hB (by linarith)
  refine ⟨Cd*Cm,mul_pos hCd hCm,?_⟩
  filter_upwards [hd,eventually_ge_atTop (2:ℝ)] with Z hd hZ
  intro ι _ _ s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M F
    hK ha₁ ha₂ hF hs₁ hs₂ hwin radius τ₁ τ₂ hr hc₁ hc₂
  let P:ℝ:=(Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ)
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  have hP:0≤P:=by dsimp [P];positivity
  let f:=fun (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))=>
    CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
      (commonRadical p.val.1 p.val.2).absNorm
  have hf:∀p E,0≤f p E:=by
    intro p E
    exact div_nonneg (CenteredMomentFirstInactiveRadicalMass.inactiveWeight_nonneg _ _ _ _) (Nat.cast_nonneg _)
  have hb (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
      sectorWeight s R seed m A t W V K (radius p E) p E (τ₁ p E) (τ₂ p E)≤
        (Cd*Z^(ε/2)*P)*f p E:=by
    unfold sectorWeight
    have hp:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
    have hcard:=hd p.val.1 p.val.2 hp.1.1 hp.2.1 E K (radius p E) (sourceRadius s)
      hK hH (hr p E) hHcap
    calc
      _≤∑_n:Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
          (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm),P*f p E:=by
        apply Finset.sum_le_sum
        intro n hn
        exact weight_le s R seed m A t W V K (radius p E) a₁ a₂ M F hK ha₁ ha₂ hF
          hs₁ hs₂ hwin p E (τ₁ p E) (τ₂ p E) (hc₁ p E) (hc₂ p E) n
      _≤_:=by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        convert mul_le_mul_of_nonneg_right hcard (mul_nonneg hP (hf p E)) using 1 ; ring
  have hmass:=hm Z hZ seed hs hs0
    (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (fun I _ hI=>original_column_mask s R seed I hI)
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2.trans hHcap) 0 le_rfl
  calc
    _≤∑p:Labels s R seed,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        (Cd*Z^(ε/2)*P)*f p E:=by
      unfold sumWeight
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro E hE
      exact hb p E
    _=(Cd*Z^(ε/2)*P)*
        (∑p:Labels s R seed,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,f p E):=by
      simp only [Finset.mul_sum]
    _≤(Cd*Z^(ε/2)*P)*(Cm*Z^(ε/2)/(seed.absNorm:ℝ)):=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _=P*((Cd*Cm)*Z^ε/(seed.absNorm:ℝ)):=by
      have hz:0<Z:=by linarith
      have he:Z^(ε/2)*Z^(ε/2)=Z^ε:=by rw [←Real.rpow_add hz];congr 1;ring
      calc
        _=P*(Cd*Cm)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm:ℝ):=by ring
        _=_:=by rw [he];ring

end SevenEighths.CenteredMomentFirstNonexceptionalWeightSum

end

end OAI

end Source2045

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstNonexceptionalFixedWeightSum.lean; sha256: 2841ad2a1ffbae515168569b645e24c648be2a963953daf3fce9335e70f2dd57 -/
section Source2046
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalFixedWeightSum
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalSource
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Families (s:Input ι)(R seed:Ideal O)(ξ₁ ξ₂:RayCharacter):=
  (p:Labels s R seed)→(E:Finset (CommonIndex p.val.1 p.val.2))→
    FixedPair s.η p.val.1 p.val.2
      (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
        (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).1 E ξ₁ ξ₂

theorem original_fixed_weight_sum (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,
    ∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι)(R seed:Ideal O),
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→0<sourceRadius s→sourceRadius s≤Z^B→
    ∀(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K a₁ a₂ M:ℝ),
      0<K→0<a₁→0<a₂→
      (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
      (∀i y,V i y≠0→|y|≤M)→
    ∀(radius:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ),
      (∀p E,radius p E≤Cr*Z^L)→∀ξ₁ ξ₂:RayCharacter,∀F:Families s R seed ξ₁ ξ₂,
      sumWeight s R seed m A t W V K radius (fun p E=>(F p E).left) (fun p E=>(F p E).right)≤
        ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ))*
          (C₀*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C₀,hC₀,hbound⟩:=original_weight_sum B L Cr ε hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hbound] with Z hbound
  intro ι _ _ s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M
    hK ha₁ ha₂ hs₁ hs₂ hwin radius hr ξ₁ ξ₂ F
  exact hbound ι s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M
    fixedPresentationCost hK ha₁ ha₂ fixedPresentationCost_pos.le hs₁ hs₂ hwin radius
    (fun p E=>(F p E).left) (fun p E=>(F p E).right) hr
    (fun p E=>(F p E).conductor_caps.1) (fun p E=>(F p E).conductor_caps.2)

end SevenEighths.CenteredMomentFirstNonexceptionalFixedWeightSum

end

end OAI

end Source2046

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalDyadicCountSource.lean; sha256: 0929669644247a0b5dd291acbc2cfc7efec9d35298a6d506fd701fd031b232dc -/
section Source2047
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=>ActualEisensteinCubic.O

lemma local_frequency_radius_cap (I J:Ideal O)(E:Finset (CommonIndex I J))
    (K V Z B ξ:ℝ)(hK:0<K)(hV:0≤V)(hZ:1≤Z)
    (hVcap:V≤Z^B)(hKcap:K⁻¹≤Z^B):
    frequencyRadius (firstNominalScale I J (∏P∈E,P.val) K V) Z ξ≤Z^(3*B+ξ/2) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hT:V^2/K≤Z^(3*B):=by
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hV hVcap 2) hKcap
      (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num
    ring
  unfold frequencyRadius
  calc
    _≤Z^(3*B)*Z^(ξ/2):=mul_le_mul_of_nonneg_right
      ((first_nominal_scale_le I J E K V hK).trans hT) (Real.rpow_nonneg hz.le _)
    _=_:=by rw [←Real.rpow_add hz]

theorem original_local_blocks_subpower (B Hcap ξ ε:ℝ)
    (hB:0≤B)(hHcap:0≤Hcap)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D:Ideal O),C≠0→D≠0→∀(E:Finset (CommonIndex C D))(K V H:ℝ),
      0<K→0≤V→0<H→V≤Z^B→K⁻¹≤Z^B→H≤Z^Hcap→
      (Fintype.card (Blocks (effectiveScale C D E K)
        (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K V) Z ξ)
        (H/Ideal.absNorm C) (H/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=original_blocks_subpower Hcap (3*B+ξ/2) 1 ε
    hHcap (by positivity) (by norm_num) hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  intro C D hC hD E K V H hK hV hH hVcap hKcap hHbound
  exact hcount C D hC hD E K _ H hK hH
    (by simpa only [one_mul] using (local_frequency_radius_cap C D E K V Z B ξ
      hK hV hZ hVcap hKcap)) hHbound

open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair

lemma input_radius_cap {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B Z:ℝ)(s:Input ι)
    (hhi:∀i,|s.hi i|≤hi i)(hb₁:|s.b₁|≤b₁)(hb₂:|s.b₂|≤b₂)
    (hZ:1≤Z)(hfixed:(∏i,hi i)*b₁*b₂≤Z)
    (hV:volume s.toData≤Z^B):sourceRadius s≤Z^(B+1) := by
  have hVol:0<volume s.toData:=volume_pos s.toData
  have he:sourceRadius s=(∏i,s.hi i)*s.b₁*s.b₂*volume s.toData:=by
    unfold sourceRadius volume;ring
  rw [he]
  have hprod:|∏i,s.hi i|≤∏i,hi i:=by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun i _=>abs_nonneg _) (fun i _=>hhi i)
  have hb₁0:0≤b₁:=(abs_nonneg _).trans hb₁
  have hp0:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>(abs_nonneg _).trans (hhi i))
  have hbound:|(∏i,s.hi i)*s.b₁*s.b₂|≤(∏i,hi i)*b₁*b₂:=by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul hprod hb₁ (abs_nonneg _) hp0) hb₂
      (abs_nonneg _) (mul_nonneg hp0 hb₁0)
  have hcoeff:(∏i,s.hi i)*s.b₁*s.b₂≤Z:=
    (le_abs_self _).trans (hbound.trans hfixed)
  calc
    _≤Z*Z^B:=mul_le_mul hcoeff hV hVol.le (zero_le_one.trans hZ)
    _=Z^(B+1):=by rw [Real.rpow_add_one (ne_of_gt (zero_lt_one.trans_le hZ))];ring

theorem original_input_local_blocks_subpower {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)(hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀s:Input ι,(∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
      ∀(C D:Ideal O),C≠0→D≠0→∀(E:Finset (CommonIndex C D))(K:ℝ),
      0<K→volume s.toData≤Z^B→K⁻¹≤Z^B→
      (Fintype.card (Blocks (effectiveScale C D E K)
        (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K (volume s.toData)) Z ξ)
        (sourceRadius s/Ideal.absNorm C) (sourceRadius s/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=original_local_blocks_subpower B (B+1) ξ ε
    hB (by positivity) hξ hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ),
    Filter.eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hcount hZ hfixed
  intro s hhi hb₁ hb₂ hH C D hC hD E K hK hV hKi
  exact hcount C D hC hD E K _ _ hK (volume_pos s.toData).le hH hV hKi
    (input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ hfixed hV)

lemma input_radius_pos_of_live {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed I:Ideal O)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (hlive:coefficient s R seed I≠0):0<sourceRadius s := by
  obtain ⟨hI,hcap⟩:=original_column_norm s R seed I hz₁ hz₂ hlive
  exact (CenteredMomentFirstScale.norm_pos I hI).trans_le hcap

end SevenEighths.CenteredMomentFirstPhysicalDyadicCount

end

end OAI

end Source2047

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstNonexceptionalLocalWeightSum.lean; sha256: 6e1d95d84278ab9109e85331433bd2eef936b1ac4a78e3bc956de9d8146683de -/
section Source2048
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalFixedWeightSum
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentExceptionalAmplitudePair
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def localRadius (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  frequencyRadius (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)) Z ξ

theorem original_local_fixed_weight_sum (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,
    ∀(s:Input ι)(R seed:Ideal O),Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→
      (∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
    ∀(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K a₁ a₂ M:ℝ),
      0<K→0<a₁→0<a₂→volume s.toData≤Z^B→K⁻¹≤Z^B→
      (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
      (∀i y,V i y≠0→|y|≤M)→
    ∀ξ₁ ξ₂:RayCharacter,∀F:Families s R seed ξ₁ ξ₂,
      sumWeight s R seed m A t W V K (localRadius s R seed K Z ξ)
        (fun p E=>(F p E).left) (fun p E=>(F p E).right)≤
      ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ))*
        (C₀*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C₀,hC₀,hbound⟩:=original_fixed_weight_sum (B+1) (3*B+ξ/2) 1 ε
    (by positivity) (by positivity) (by norm_num) hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hbound hZ hfixed
  intro s R seed hs hs0 hz₁ hz₂ hhi hb₁ hb₂ hH m A t W V K a₁ a₂ M
    hK ha₁ ha₂ hV hKi hs₁ hs₂ hwin ξ₁ ξ₂ F
  apply hbound ι s R seed hs hs0 hz₁ hz₂ hH
    (input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ hfixed hV)
    m A t W V K a₁ a₂ M hK ha₁ ha₂ hs₁ hs₂ hwin
    (localRadius s R seed K Z ξ) _ ξ₁ ξ₂ F
  intro p E
  simpa only [localRadius,one_mul] using
    local_frequency_radius_cap p.val.1 p.val.2 E K (volume s.toData) Z B ξ
      hK (volume_pos s.toData).le hZ hV hKi

end SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum

end

end OAI

end Source2048

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstReferenceSource.lean; sha256: 7379aef9fa13d15f0c280c60e7e64c64fc3f20a0269bef61c0959551a958562d -/
section Source2049
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstReferenceSource
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstRetainedNorm
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstPhysicalActiveDictionary CenteredMomentFirstSourceReduction
open CenteredMomentFirstInactiveRadicalMass CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentExceptionalAmplitudePair CenteredMomentRankinRadical
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev SourceBlocks (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):=
  Blocks (effectiveScale p.val.1 p.val.2 E K) (localRadius s R seed K Z ξ p E)
    (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)

def originalBlock (s:Input ι)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):ℂ:=
  block s.η (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    p.val.1 p.val.2
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).1
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).2 E
    (retainedRows (localRadius s R seed K Z ξ p E) 1) W (fun _=>logAnnulus)
    K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))

def radicalWeight (s:Input ι)(R seed:Ideal O)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
    ((commonRadical p.val.1 p.val.2).absNorm:ℝ)

omit [DecidableEq ι] in
lemma radicalWeight_nonneg (s:Input ι)(R seed:Ideal O)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):0≤radicalWeight s R seed p E:=
  div_nonneg (inactiveWeight_nonneg _ _ _ _) (Nat.cast_nonneg _)

lemma physicalMass_eq_sum (s:Input ι)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K Z ξ:ℝ):
    physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ=
      ∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑n:SourceBlocks s R seed K Z ξ p E,‖originalBlock s R seed W K Z ξ p E n‖:=by
  rw [physicalMass_full_source]
  rfl

theorem original_block_sum (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,∀s:Input ι,∀R seed:Ideal O,
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→
      (∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
    ∀W:𝓢(ℝ,ℂ),∀K A:ℝ,0<K→0≤A→volume s.toData≤Z^B→K⁻¹≤Z^B→
    (∀p:Labels s R seed,∀E∈inactiveSubsets p.val.1 p.val.2,
      ∀n:SourceBlocks s R seed K Z ξ p E,
      ‖originalBlock s R seed W K Z ξ p E n‖/volume s.toData≤A*radicalWeight s R seed p E)→
    physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ/
      volume s.toData≤A*(C₀*Z^ε/(seed.absNorm:ℝ)) := by
  obtain ⟨Cd,hCd,hd⟩:=original_input_local_blocks_subpower hi b₁ b₂ B ξ (ε/2) hB hξ (by linarith)
  obtain ⟨Cm,hCm,hm⟩:=actual_inactive_radical_mass (B+1) (ε/2) (by linarith) (by linarith)
  refine ⟨Cd*Cm,mul_pos hCd hCm,?_⟩
  filter_upwards [hd,eventually_ge_atTop (2:ℝ),eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hd hZ hfixed
  intro s R seed hs hs0 hz₁ hz₂ hhi hb₁ hb₂ hH W K A hK hA hV hKi hblock
  have hZ1:1≤Z:=by linarith
  have hcap:=input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ1 hfixed hV
  have hmass:=hm Z hZ seed hs hs0
    (finiteColumns (Fintype.piFinset s.pools)) (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (fun I _ hI=>original_column_mask s R seed I hI)
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2.trans hcap) 0 (le_refl _)
  have hf:∀p E,0≤radicalWeight s R seed p E:=radicalWeight_nonneg s R seed
  have hsector (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
      (hE:E∈inactiveSubsets p.val.1 p.val.2):
      (∑n:SourceBlocks s R seed K Z ξ p E,‖originalBlock s R seed W K Z ξ p E n‖/volume s.toData)≤
        (Cd*Z^(ε/2)*A)*radicalWeight s R seed p E := by
    have hp:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
    have hcard:=hd s hhi hb₁ hb₂ hH p.val.1 p.val.2 hp.1.1 hp.2.1 E K hK hV hKi
    change (Fintype.card (SourceBlocks s R seed K Z ξ p E):ℝ)≤Cd*Z^(ε/2) at hcard
    calc
      _≤∑_n:SourceBlocks s R seed K Z ξ p E,A*radicalWeight s R seed p E:=
        Finset.sum_le_sum (fun n _=>hblock p E hE n)
      _ = (Fintype.card (SourceBlocks s R seed K Z ξ p E):ℝ)*(A*radicalWeight s R seed p E) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ ≤ (Cd*Z^(ε/2))*(A*radicalWeight s R seed p E) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hA (hf p E))
      _ = _ := (mul_assoc _ _ _).symm
  rw [physicalMass_eq_sum]
  simp only [Finset.sum_div]
  calc
    _≤∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        (Cd*Z^(ε/2)*A)*radicalWeight s R seed p E:=by
      apply Finset.sum_le_sum;intro p _
      exact Finset.sum_le_sum (fun E hE=>hsector p E hE)
    _=(Cd*Z^(ε/2)*A)*(∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        radicalWeight s R seed p E):=by simp_rw [←Finset.mul_sum]
    _≤(Cd*Z^(ε/2)*A)*(Cm*Z^(ε/2)/(seed.absNorm:ℝ)):=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _=_ := by
      rw [show Z^ε=Z^(ε/2)*Z^(ε/2) by rw [←Real.rpow_add (by linarith : 0<Z)];congr 1;ring]
      ring

end SevenEighths.CenteredMomentFirstReferenceSource

end

end OAI

end Source2049

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalOriginalMask.lean; sha256: b63d868d4d81887c15417b4e6b7bb2f82e15f509d9d18d4a4bb3e999f1f409c3 -/
section Source2050
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalOriginalMask
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstMaskedFamily CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonSupport
open CenteredMomentFirstRetainedNorm CenteredMomentFirstSourceReduction
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
lemma original_coefficient (s : Input ι) (R seed C I : Ideal O)
    (hI : Supported I) (t : ℝ) :
    CenteredMomentFirstPhysicalSource.coefficient s.η (fixedBadMask*idealGenerator R) 1 t
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C I =
    CenteredMomentFirstPhysicalSource.coefficient s.η fixedBadMask 1 t
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C I := by
  unfold CenteredMomentFirstPhysicalSource.coefficient
  by_cases h : CenteredMomentOriginalCommonHarmonic.coefficient s R seed (C*I)=0
  · simp [h]
  · have hc : IsCoprime I R :=
      (beta_coprime (original s R seed) (C*I) h).of_mul_left_right
    have hw := rowWeight_mask_factor s.η (idealGenerator R) I hI t
    change CenteredMomentHeckeExpansion.rowWeight s.η (fixedBadMask*idealGenerator R) 1 1 t I =
      idealMask (idealGenerator R) I * CenteredMomentHeckeExpansion.rowWeight s.η fixedBadMask 1 1 t I at hw
    rw [hw]
    simp only [idealMask, span_idealGenerator, hc, ite_true, one_mul]

omit [DecidableEq ι] in
theorem original_block (s : Input ι) (R seed : Ideal O) (t : ℝ)
    (S : Finset (Ideal O)) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (rows : Finset O) (W : 𝓢(ℝ,ℂ))
    (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block s.η (fixedBadMask*idealGenerator R) 1 t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀ =
    block s.η fixedBadMask 1 t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀ := by
  unfold block
  apply congrArg (fun z : ℂ => inactiveWeight C D E * z)
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  dsimp only
  rw [original_coefficient s R seed C a (column_supported C C hC.1 S a) t,
    original_coefficient s R seed D b (column_supported C D hD.1 S b) t]

omit [DecidableEq ι] in
lemma original_sector (s : Input ι) (R seed : Ideal O) (t : ℝ)
    (S : Finset (Ideal O)) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sector s R seed (fixedBadMask*idealGenerator R) 1 t S C D hC hD W K X Z ξ =
    sector s R seed fixedBadMask 1 t S C D hC hD W K X Z ξ := by
  unfold sector
  simp_rw [original_block]

omit [DecidableEq ι] in
lemma original_sectorMass (s : Input ι) (R seed : Ideal O) (t : ℝ)
    (S : Finset (Ideal O)) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sectorMass s R seed (fixedBadMask*idealGenerator R) 1 t S C D hC hD W K X Z ξ =
    sectorMass s R seed fixedBadMask 1 t S C D hC hD W K X Z ξ := by
  unfold sectorMass
  simp_rw [original_block]

omit [DecidableEq ι] in
theorem original_physicalMass (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s R seed (fixedBadMask*idealGenerator R) 1 W K Z ξ =
    physicalMass s R seed fixedBadMask 1 W K Z ξ := by
  unfold physicalMass
  simp_rw [original_sectorMass]

end SevenEighths.CenteredMomentFirstPhysicalOriginalMask

end

end OAI

end Source2050

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalZeroRadius.lean; sha256: 145e4162965d455367a0362643254ec5871456669c41c1b754ee5cc39ebe47ca -/
section Source2051
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalZeroRadius
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstRetainedNorm
open CenteredMomentFirstSourceReduction CenteredMomentCommonSupport
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
lemma coefficient_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0) (I : Ideal O) :
    CenteredMomentOriginalCommonHarmonic.coefficient s R seed I=0 := by
  by_contra h
  obtain ⟨hI,hN⟩ := original_column_norm s R seed I h₁ h₂ h
  have hn : 1≤(I.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  linarith

omit [DecidableEq ι] in
lemma block_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀=0 := by
  simp [block,CenteredMomentFirstPhysicalSource.coefficient,coefficient_zero s R seed h₁ h₂ hH]

omit [DecidableEq ι] in
lemma sectorMass_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sectorMass s R seed m A t S C D hC hD W K X Z ξ=0 := by
  unfold sectorMass
  simp only [block_zero s R seed h₁ h₂ hH,norm_zero,Finset.sum_const_zero]

omit [DecidableEq ι] in
theorem physicalMass_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (m A : O) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s R seed m A W K Z ξ=0 := by
  unfold physicalMass
  simp only [sectorMass_zero s R seed h₁ h₂ hH,Finset.sum_const_zero]

omit [DecidableEq ι] in
theorem sourceGaussEnergy_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (S : Finset (Ideal O)) (f : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) f W K=0 := by
  simp [sourceGaussEnergy,gaussEnergy,gaussPolynomial,coefficient_zero s R seed h₁ h₂ hH]

end SevenEighths.CenteredMomentFirstPhysicalZeroRadius

end

end OAI

end Source2051

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstReferenceEnergy.lean; sha256: a7831816f5c995a2ceb489a28bd38861e45771b3aabc823fc7088eebe56fa1ab -/
section Source2052
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstReferenceEnergy
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstReferenceBlock
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstSourceReduction CenteredMomentFirstInactiveRadicalMass
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentExceptionalAmplitudePair CenteredMomentRankinRadical
open CenteredMomentAmplificationChildInput CenteredMomentGaussEnergy CenteredMomentChildAssembly
open CenteredMomentCommonSupport CenteredMomentMobiusRegroup CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstMixedAllowance CenteredMomentSecondWindowBudget CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev supported (s:Input ι)(R seed:Ideal O)(p:Labels s R seed):=
  commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property

def ColumnBounds (s:Input ι)(R seed:Ideal O)(Z:ℝ)(J₁ J₂:ℕ)(EL ER:Fin 4→ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(n:Fin 4→ℤ):Prop:=
  let C:=p.val.1; let D:=p.val.2; let h:=supported s R seed p
  let F:=fixedPair s.η C D h.1 E 1 1
  let V:=volume s.toData
  let refL:=(F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)
  let refR:=(F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)
  (∀L∈divisorPool (Finset.univ:Finset (columns C D h.2.1 (original s R seed).columns))
    (fun b=>Ideal.span {element C D h.2.1 (original s R seed).columns b}),
    (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
    (commonEnergy (original s R seed) C h.1 (fixedPair s.η C D h.1 E χ χ).left v L
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      ((∑i,refL*EL i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) ∧
  (∀L∈divisorPool (Finset.univ:Finset (columns C D h.2.1 (original s R seed).columns))
    (fun b=>Ideal.span {element C D h.2.1 (original s R seed).columns b}),
    (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
    (commonEnergy (original s R seed) D h.2 (fixedPair s.η C D h.1 E χ χ).right v L
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      ((∑i,refR*ER i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂))

def pairedBudget (J₁ J₂:ℕ)(t:ℝ)(EL ER:Fin 4→ℝ):ℝ:=
  ∑i:Fin 4,∑j:Fin 4,windowBudget J₁ t (EL i)*windowBudget J₂ t (ER j)
lemma pairedBudget_nonneg (J₁ J₂:ℕ)(t:ℝ)(EL ER:Fin 4→ℝ):0≤pairedBudget J₁ J₂ t EL ER:=
  Finset.sum_nonneg (fun _i _=>Finset.sum_nonneg (fun _j _=>mul_nonneg
    (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))

def sourceFactor (s:Input ι)(a₁ a₂ K:ℝ):ℝ:=
  (Real.exp (Real.log 4)/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ)
omit [DecidableEq ι] in
lemma sourceFactor_nonneg (s:Input ι)(a₁ a₂ K:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)(hK:0<K):
    0≤sourceFactor s a₁ a₂ K:=by
  have hlo:0<∏i,s.lo i:=Finset.prod_pos (fun i _=>s.lo_pos i)
  have hf:=fixedPresentationCost_pos
  unfold sourceFactor
  positivity

theorem actual_physical_mass (W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)(hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,∀s:Input ι,∀R seed:Ideal O,
      Squarefree seed→seed≠0→(∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→
      ∀a₁ a₂ K:ℝ,0<a₁→0<a₂→0<K→
      (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
      volume s.toData≤Z^B→K⁻¹≤Z^B→∀EL ER:Fin 4→ℝ,(∀i,0≤EL i)→(∀i,0≤ER i)→
      (∀p:Labels s R seed,∀E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        ∀n:SourceBlocks s R seed K Z ξ p E,
        CenteredMomentFirstReferenceSource.originalBlock s R seed W K Z ξ p E n≠0→ColumnBounds s R seed Z J₁ J₂ EL ER p E (fun i => (n i).val))→
      physicalMass s R seed fixedBadMask 1 W K Z ξ/volume s.toData≤
        C*Z^ε/(seed.absNorm:ℝ)*sourceFactor s a₁ a₂ K*pairedBudget J₁ J₂ s.t EL ER:=by
  obtain ⟨Cs,hCs,hsum⟩:=original_block_sum hi b₁ b₂ B ξ (ε/2) hB hξ (by linarith)
  obtain ⟨Cb,hCb,hblock⟩:=actual_reference_block W 0 J₁ J₂ (B+1) (ε/2) (by linarith) (by linarith)
  refine ⟨Cs*Cb,mul_pos hCs hCb,?_⟩
  filter_upwards [hsum,hblock,eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hsum hblock hfixed
  intro s R seed hseed hseed0 hhi hb₁ hb₂ a₁ a₂ K ha₁ ha₂ hK hs₁ hs₂ hV hKi EL ER hEL hER hcol
  have hz₁:s.W₁ 0=0:=by by_contra hn;have hh:=hs₁ 0 hn;linarith
  have hz₂:s.W₂ 0=0:=by by_contra hn;have hh:=hs₂ 0 hn;linarith
  by_cases hH:0<sourceRadius s
  case neg =>
    rw [CenteredMomentFirstPhysicalZeroRadius.physicalMass_zero s R seed hz₁ hz₂ (le_of_not_gt hH)]
    simp only [zero_div]
    have hsF:=sourceFactor_nonneg s a₁ a₂ K ha₁ ha₂ hK
    have hsP:=pairedBudget_nonneg J₁ J₂ s.t EL ER
    have hZpos:0<Z:=zero_lt_one.trans hblock.1
    positivity
  let A:=Cb*Z^(ε/2)*sourceFactor s a₁ a₂ K*pairedBudget J₁ J₂ s.t EL ER
  have hA:0≤A:=mul_nonneg (mul_nonneg (mul_nonneg hCb.le (Real.rpow_nonneg (by linarith [hblock.1]) _))
    (sourceFactor_nonneg s a₁ a₂ K ha₁ ha₂ hK)) (pairedBudget_nonneg _ _ _ _ _)
  have hcap:=CenteredMomentFirstPhysicalDyadicCount.input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hblock.1.le hfixed hV
  have hpblock (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
      (hE:E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2)
      (n:SourceBlocks s R seed K Z ξ p E):
      ‖CenteredMomentFirstReferenceSource.originalBlock s R seed W K Z ξ p E n‖/volume s.toData≤A*radicalWeight s R seed p E:=by
    by_cases hne:CenteredMomentFirstReferenceSource.originalBlock s R seed W K Z ξ p E n=0
    · rw [hne,norm_zero,zero_div]
      exact mul_nonneg hA (radicalWeight_nonneg s R seed p E)
    have hp:=supported s R seed p
    have hg:=actual_common_gates s R seed hseed hz₁ hz₂ p.val.1 p.val.2 p.property
    have hND:1≤(p.val.2.absNorm:ℝ):=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1)
    have hcapD:sourceRadius s/(p.val.2.absNorm:ℝ)≤Z^(B+1):=
      (div_le_self hH.le hND).trans hcap
    have hh:=hblock.2 s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ p.val.1 p.val.2 hp.1 hp.2 hg.2.2.1 E 1 1
      (fixedPair s.η p.val.1 p.val.2 hp.1 E 1 1) (retainedRows (localRadius s R seed K Z ξ p E) 1)
      K hK (fun i => (n i).val) hcapD EL ER hEL hER (hcol p E hE n hne).1 (hcol p E hE n hne).2
    simp only [pow_zero,one_mul] at hh
    convert hh using 1 <;>
      simp only [CenteredMomentFirstReferenceSource.originalBlock,A,sourceFactor,pairedBudget,radicalWeight,
        CenteredMomentFirstInactiveRadicalMass.inactiveWeight,Real.rpow_zero,div_one,
        CenteredMomentFirstPhysicalSource.inactiveWeight, CenteredMomentAmplificationChildInput.original,
        CenteredMomentFirstAmplificationChoice.OriginalData.columns,
        CenteredMomentFirstAmplificationChoice.OriginalData.beta,
        CenteredMomentFirstAmplificationChoice.OriginalData.profile,
        CenteredMomentOriginalCommonHarmonic.coefficient,
        CenteredMomentAmplificationChildInput.volume,
        CenteredMomentExceptionalAmplitudePair.volume] ; ring
  have hh:=hsum s R seed hseed hseed0 hz₁ hz₂ hhi hb₁ hb₂ hH W K A hK hA hV hKi hpblock
  rw [CenteredMomentFirstPhysicalOriginalMask.original_physicalMass] at hh
  calc
    _≤_:=hh
    _=_:=by
      rw [show Z^ε=Z^(ε/2)*Z^(ε/2) by rw [←Real.rpow_add (by linarith [hblock.1]:0<Z)];congr 1;ring]
      dsimp [A]
      ring

end SevenEighths.CenteredMomentFirstReferenceEnergy

end

end OAI

end Source2052

/- Original source: OAI/NumberTheory/DirichletL/Energy/OriginalProfileControl.lean; sha256: 9a1026f36c39af9f01ea069d12ddd5203a40a93018c66874644647db11e06fc4 -/
section Source2053
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyOriginalProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceInputTailUniform CenteredMomentFirstReferenceEnergy
open CenteredMomentEnergyZeroComparison CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyState CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
lemma slot_product_le (s:Input ι)(N:ℕ)(C:ℝ)(hC:1≤C)
    (hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C): (∏i,s.M i)≤C^N := by
  calc
    _≤∏_i:ι,C:=Finset.prod_le_prod₀ (fun i _=>(s.M_ge_one i).trans' zero_le_one) (fun i _=>hM i)
    _=C^(Fintype.card ι):=by simp
    _≤C^N:=pow_le_pow_right₀ hC hN

omit [DecidableEq ι] in
lemma plain_control_le {a b:ℝ}(s:Input ι)(p:Profiles a b)(S:Finset (ℕ×ℕ))
    (N:ℕ)(C:ℝ)(hC:1≤C)(hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C):
    plainControl s (p.profile 0) (p.profile 1)≤C^N*p.control (insert (0,0) S) := by
  have h0 (i:Fin 2):SchwartzMap.seminorm ℝ 0 0 (p.profile i)≤
      sourceControl (insert (0,0) S) (p.profile i):=
    Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ)
      (s:=insert (0,0) S) (i:=(0,0)) (x:=p.profile i) (Finset.mem_insert_self _ _)
  have hpair:=mul_le_mul (h0 0) (h0 1) (apply_nonneg _ _) (sourceControl_nonneg _ _)
  have hh:=mul_le_mul (slot_product_le s N C hC hN hM) hpair
    (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (pow_nonneg (by linarith) _)
  simpa only [plainControl,Profiles.control,mul_assoc] using hh

omit [DecidableEq ι] in
lemma plain_control_sq_le {a b:ℝ}(s:Input ι)(p:Profiles a b)(S:Finset (ℕ×ℕ))
    (N:ℕ)(C:ℝ)(hC:1≤C)(hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C):
    (plainControl s (p.profile 0) (p.profile 1))^2≤C^(2*N)*(p.control (insert (0,0) S))^2 := by
  have hh:=pow_le_pow_left₀ (plainControl_nonneg _ _ _) (plain_control_le s p S N C hC hN hM) 2
  simpa only [mul_pow,←pow_mul,Nat.mul_comm N 2] using hh

omit [DecidableEq ι] in
lemma zero_plain_control (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(W₁ W₂:𝓢(ℝ,ℂ)):
    plainControl (zeroInput s hz₁ hz₂) W₁ W₂=plainControl s W₁ W₂:=rfl

omit [DecidableEq ι] in
lemma lower_product (s:Input ι)(N:ℕ)(a:ℝ)(ha:0<a)
    (hN:Fintype.card ι≤N)(hlo:∀i,a≤s.lo i):
    (min 1 a)^N≤∏i,s.lo i := by
  have hm:0≤min 1 a:=le_min zero_le_one ha.le
  calc
    _≤(min 1 a)^(Fintype.card ι):=pow_le_pow_of_le_one hm (min_le_left _ _) hN
    _=∏_i:ι,min 1 a:=by simp
    _≤∏i,s.lo i:=Finset.prod_le_prod₀ (fun _ _=>hm) (fun i _=>(min_le_right _ _).trans (hlo i))

omit [DecidableEq ι] in
lemma source_factor_le (s:Input ι)(N:ℕ)(aslot a K:ℝ)(hs:0<aslot)(ha:0<a)(hK:0<K)
    (hN:Fintype.card ι≤N)(hlo:∀i,aslot≤s.lo i):
    sourceFactor s a a K≤
      (Real.exp (Real.log 4)*fixedPresentationCost/((min 1 aslot)^N*a*a))*K*(s.η.modulus.absNorm:ℝ) := by
  have hd:0<(min 1 aslot)^N*a*a:=by positivity
  have hprod:=lower_product s N aslot hs hN hlo
  have hden:(min 1 aslot)^N*a*a≤(∏i,s.lo i)*a*a:=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod ha.le) ha.le
  have hdiv:=div_le_div_of_nonneg_left (Real.exp_pos (Real.log 4)).le hd hden
  have hc:=fixedPresentationCost_pos
  have hn:0≤(s.η.modulus.absNorm:ℝ):=Nat.cast_nonneg _
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdiv hc.le) hK.le) hn
  unfold sourceFactor
  convert hh using 1 ; ring

local notation "O"=>HeckeFamily.O
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

local notation "inp" => CenteredMomentEnergyNaturalInputMatches.input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame

theorem natural_plain_control (N:ℕ)(hN:Fintype.card ι≤N)(S:Finset (ℕ×ℕ)):
    (plainControl inp (p.profile 0) (p.profile 1))^2≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 :=
  plain_control_sq_le inp p S N _
    (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) hN (fun _=>le_refl _)

theorem natural_zero_plain_control (N:ℕ)(hN:Fintype.card ι≤N)(S:Finset (ℕ×ℕ))
    (hz₁:(inp).W₁ 0=0)(hz₂:(inp).W₂ 0=0):
    (plainControl (zeroInput inp hz₁ hz₂) (p.profile 0) (p.profile 1))^2≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 :=
  plain_control_sq_le (zeroInput inp hz₁ hz₂) p S N _
    (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) hN (fun _=>le_refl _)

theorem natural_source_factor (N:ℕ)(hN:Fintype.card ι≤N)(K:ℝ)(hK:0<K):
    sourceFactor inp a a K≤
      (Real.exp (Real.log 4)*fixedPresentationCost/((min 1 aslot)^N*a*a))*K*
        (state.character.modulus.absNorm:ℝ) :=
  source_factor_le inp N aslot a K haslot ha hK hN (fun _=>le_refl _)

theorem natural_zero_source_factor (N:ℕ)(hN:Fintype.card ι≤N)(K:ℝ)(hK:0<K)
    (hz₁:(inp).W₁ 0=0)(hz₂:(inp).W₂ 0=0):
    sourceFactor (zeroInput inp hz₁ hz₂) a a K≤
      (Real.exp (Real.log 4)*fixedPresentationCost/((min 1 aslot)^N*a*a))*K*
        (state.character.modulus.absNorm:ℝ) :=
  source_factor_le (zeroInput inp hz₁ hz₂) N aslot a K haslot ha hK hN (fun _=>le_refl _)

end Input
end SevenEighths.CenteredMomentEnergyOriginalProfileControl

end

end OAI

end Source2053

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalMainSeparatedPower.lean; sha256: 404bea3490b414e538e4ef8a6029e7f4670f6d1c94476bdb15742b8d2dfe3fb6 -/
section Source2054
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower
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

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients
theorem actual_main_separated_power
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
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+degree+4*n);
    let Hweights:=coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J
      (internalQ Q η₀) Kc t εsrc (seed.absNorm:ℝ)
      (fixedFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap cost Ebase t
        (CenteredMomentSecondInputCapacitySource.lowerFactor N lower a) (seed.absNorm:ℝ)
        (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile);
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,Hweights j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    CenteredMomentEnergyCanonicalMainSeparated.actual_main_separated_gaussian (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Kc,hKc,Zi,hZi,?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  have hg:=hbound χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+degree+4*n)
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  have hz:0<Z:=zero_lt_one.trans (hZi.trans_le hZ)
  have hE:0≤Ebase:=by dsimp [Ebase];have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile;positivity
  have hloProd:=CenteredMomentEnergyOriginalProfileControl.lower_product
    (child src C R0 B τ t) N lower hlower ((live_card_le B.val).trans hcard)
    (fun i=>hlowerSrc.trans (src.lower_le i.val))
  have hlo:CenteredMomentSecondInputCapacitySource.lowerFactor N lower a≤
      (∏i,(child src C R0 B τ t).lo i)*a*a:=by
    unfold CenteredMomentSecondInputCapacitySource.lowerFactor
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right hloProd (sq_nonneg a)
  have hcoef:=CenteredMomentEnergyFirstGaussianCoefficients.main_coefficients
    N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc
    Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving
    (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
    t (τ.modulus.absNorm:ℝ) cost Ebase (sigma/3)
    (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid r
    (∏i,(child src C R0 B τ t).lo i) a
    (CenteredMomentSecondInputCapacitySource.lowerFactor N lower a) (seed.absNorm:ℝ)
    (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile
    (zero_le_one.trans hupper) (le_trans zero_le_one (le_max_left _ _))
    (le_trans zero_le_one (le_max_left _ _)) hKc.le (Nat.cast_nonneg _) hCm.le hCe hz hE
    (by unfold mainCommonRadius;positivity)
    (CenteredMomentSecondInputCapacitySource.lowerFactor_pos N lower a hlower haPlain) hlo
  have hexp:
      (Bcap+Bcap)*εmask+(εchild+εremove+
        (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3)+κ*mesh)=
      sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))/6+paid :=by
    dsimp [paid];ring
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  have hh:=mul_le_mul_of_nonneg_right (hcoef j)
    (Real.rpow_nonneg (volume_pos (child src C R0 B τ t)).le (powers εsrc j))
  simpa only [CenteredMomentEnergyChildEnvelopeFitting.coefficient,hexp,Ebase,paid] using hh

end SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower

end

end OAI

end Source2054

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstGaussianProfileWeights.lean; sha256: 29af46cda8fc53fd70b16a6ad845bea2117ef018a4c18ab5a0e0dcfd10972927 -/
section Source2055
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentSecondWindowBudget
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O

def losses (epsilon delta theta B:ℝ):Fin 4→ℝ:=
  ![2*delta+epsilon,2*epsilon+2*delta+2*(5*B+1)*theta,0,0]

private lemma control_mono {a b:ℝ}(p:Profiles a b){S T:Finset (ℕ×ℕ)}(h:S⊆T):
    p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono h) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono h) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

private lemma zero_control_le {a b:ℝ}(p:Profiles a b)(U:Finset (ℕ×ℕ))(h:(0,0)∈U):
    SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1)≤p.control U:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) h) (p.profile 0))
    (Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) h) (p.profile 1)) (apply_nonneg _ _) (sourceControl_nonneg _ _)

theorem actual_weights {a b:ℝ}(N:ℕ)(upper b1 b2 Amax loFloor:ℝ)
    (Cm Ce Cd Ct Cc cost epsilon delta theta B:ℝ)
    (Jprofile Jchild degree:ℕ)(Sp Tchild Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(_hAmax:0≤Amax)(hlo:0<loFloor)
    (hCm:0≤Cm)(hCe:0≤Ce)(hCd:0≤Cd)(hCt:0≤Ct)(hCc:0≤Cc)(hcost:0≤cost):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀Q:Ideal O,∀Kfix:ℝ,0≤Kfix→∃C:ℝ,0<C ∧
    ∀p:Profiles a b,∀Z t height A seed C0 C1:ℝ,
      0<Z→0≤height→0≤A→A≤Amax→1≤seed→0≤C0→0≤C1→
    let Ebase:=Cc*(C0+C1)*diagonalControl W*(p.control Tchild)^2*(1+height)^degree;
    ∀j:Fin 4,
      coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
        (fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed Jchild Sf W) j≤
      C*(C0+C1+1)*(p.control U)^2*(1+|t|+height)^J*Z^(losses epsilon delta theta B j)/seed:=by
  let U:=insert (0,0) (Sp∪Tchild)
  let J:=degree+(Jchild+Jchild)+2*Jprofile
  refine ⟨U,J,?_⟩
  intro Q Kfix hK
  let Hconst:ℝ:=(1+2*Real.pi)^2
  let D0:=Cm*cost*Cc*diagonalControl W*(profileMoment Jchild)^2*
    Hconst^(Jchild+Jchild)*(2*(b1*b2)*upper^N*Amax^2)*(upper^N*b1*b2)
  let D1:=Ce*loFloor^(-2/3:ℝ)*exceptionalConstant N upper Jprofile Q Kfix*Amax^4
  let D2:=Cd*‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖*4*(1+upper^N*b^2)^(1+epsilon)
  let D3:=Ct*Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hd:=diagonalControl_nonneg W
  have hmoment:=profileMoment_nonneg Jchild
  have hSf:0≤Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=apply_nonneg _ _
  have hExc:0≤exceptionalConstant N upper Jprofile Q Kfix:=by
    unfold exceptionalConstant
    positivity
  have hD0:0≤D0:=by dsimp [D0,Hconst];positivity
  have hD1:0≤D1:=by dsimp [D1];positivity
  have hD2:0≤D2:=by dsimp [D2];positivity
  have hD3:0≤D3:=mul_nonneg hCt hSf
  let C:=1+D0+D1+D2+D3
  have hC:0<C:=by dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro p Z t height A seed C0 C1 hZ hheight hA hAA hseed hC0 hC1
  dsimp only
  let H:=1+|t|+height
  have hH:1≤H:=by dsimp [H];linarith [abs_nonneg t]
  have hH0:0≤H:=zero_le_one.trans hH
  have hseed0:0≤seed:=zero_le_one.trans hseed
  have hS:Sp⊆U:=by intro x hx;simp [U,hx]
  have hT:Tchild⊆U:=by intro x hx;simp [U,hx]
  have h00:(0,0)∈U:=by simp [U]
  have hp:=p.control_nonneg U
  have hpS:=p.control_nonneg Sp
  have hpT:=p.control_nonneg Tchild
  have hSpc: (p.control Sp)^2≤(p.control U)^2:=
    (sq_le_sq₀ hpS hp).mpr (control_mono p hS)
  have hTpc: (p.control Tchild)^2≤(p.control U)^2:=
    (sq_le_sq₀ hpT hp).mpr (control_mono p hT)
  have h00c:(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2≤(p.control U)^2:=
    (sq_le_sq₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) hp).mpr (zero_control_le p U h00)
  have hAp: A^2≤Amax^2:=pow_le_pow_left₀ hA hAA 2
  have hA4: A^4≤Amax^4:=pow_le_pow_left₀ hA hAA 4
  have hh:1+height≤H:=by dsimp [H];linarith [abs_nonneg t]
  have ht:1+‖t‖≤H:=by dsimp [H];linarith
  have henv0:0≤heightEnvelope t:=(heightEnvelope_pos t).le
  have henv:heightEnvelope t≤Hconst*H:=by
    have hx:1+|t|+2*Real.pi≤(1+2*Real.pi)*H:=by
      dsimp [H]
      nlinarith [Real.pi_pos,abs_nonneg t,
        mul_nonneg (le_of_lt Real.pi_pos) (abs_nonneg t)]
    have hy:=mul_le_mul_of_nonneg_right hx (show 0≤1+2*Real.pi by positivity)
    convert hy using 1 <;> dsimp [heightEnvelope,Hconst] ; ring
  have henvp:heightEnvelope t^(Jchild+Jchild)≤Hconst^(Jchild+Jchild)*H^(Jchild+Jchild):=by
    simpa only [mul_pow] using pow_le_pow_left₀ (heightEnvelope_pos t).le henv (Jchild+Jchild)
  have hheightp:(1+height)^degree≤H^degree:=pow_le_pow_left₀ (by positivity) hh degree
  have htp:(1+‖t‖)^(2*Jprofile)≤H^J:=
    (pow_le_pow_left₀ (by positivity) ht (2*Jprofile)).trans
      (pow_le_pow_right₀ hH (by dsimp [J];omega))
  have hjoin:H^degree*H^(Jchild+Jchild)≤H^J:=by
    rw [←pow_add]
    exact pow_le_pow_right₀ hH (by dsimp [J];omega)
  have hHone:1≤H^J:=one_le_pow₀ hH
  have hC01:0≤C0+C1:=add_nonneg hC0 hC1
  have hCplus:0≤C0+C1+1:=by positivity
  have hD (j:Fin 4): (![D0,D1,D2,D3] j)≤C:=by
    fin_cases j <;> simp only [Matrix.cons_val,Fin.reduceFinMk] <;> dsimp [C] <;> linarith
  have hbase (d:ℝ)(hd0:0≤d)(hdC:d≤C)(ell:ℝ):
      d*(C0+C1+1)*(p.control U)^2*H^J*Z^ell/seed≤
      C*(C0+C1+1)*(p.control U)^2*H^J*Z^ell/seed:=by
    apply div_le_div_of_nonneg_right _ hseed0
    gcongr
  intro j
  fin_cases j
  · apply le_trans _ (hbase D0 hD0 (hD 0) (2*delta+epsilon))
    dsimp only [CenteredMomentSecondChildPowerBudget.coefficients,fixedFactors,losses,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    apply div_le_div_of_nonneg_right _ hseed0
    calc
      _≤Cm*Z^(2*delta+epsilon)*cost*
          (Cc*(C0+C1)*diagonalControl W*(p.control U)^2*H^degree)*
          (Hconst^(Jchild+Jchild)*H^(Jchild+Jchild))*profileMoment Jchild*profileMoment Jchild*
          (2*(b1*b2)*upper^N*Amax^2)*(upper^N*b1*b2):=by gcongr
      _=D0*(C0+C1)*(p.control U)^2*(H^degree*H^(Jchild+Jchild))*Z^(2*delta+epsilon):=by dsimp [D0];ring
      _≤D0*(C0+C1)*(p.control U)^2*H^J*Z^(2*delta+epsilon):=by gcongr
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hD0)
            (sq_nonneg (p.control U))) (pow_nonneg hH0 J))
        (Real.rpow_nonneg hZ.le _)
  · apply le_trans _ (hbase D1 hD1 (hD 1) (2*epsilon+2*delta+2*(5*B+1)*theta))
    dsimp only [CenteredMomentSecondChildPowerBudget.coefficients,fixedFactors,losses,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    apply div_le_div_of_nonneg_right _ hseed0
    calc
      _≤Ce*Z^(2*epsilon+2*delta+2*(5*B+1)*theta)*loFloor^(-2/3:ℝ)*
          exceptionalConstant N upper Jprofile Q Kfix*(p.control U)^2*H^J*Amax^4:=by gcongr
      _=D1*(p.control U)^2*H^J*Z^(2*epsilon+2*delta+2*(5*B+1)*theta):=by dsimp [D1];ring
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right hD1 (le_add_of_nonneg_left hC01))
            (sq_nonneg (p.control U))) (pow_nonneg hH0 J))
        (Real.rpow_nonneg hZ.le _)
  · apply le_trans _ (hbase D2 hD2 (hD 2) 0)
    dsimp only [CenteredMomentSecondChildPowerBudget.coefficients,fixedFactors,losses,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    rw [Real.rpow_zero,mul_one]
    apply div_le_div_of_nonneg_right _ hseed0
    calc
      _≤D2*(p.control U)^2:=by
        convert mul_le_mul_of_nonneg_left h00c hD2 using 1 ; dsimp only [D2] ; ring
      _≤D2*(C0+C1+1)*(p.control U)^2*H^J:=by
        calc
          _≤D2*(C0+C1+1)*(p.control U)^2:=mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right hD2 (le_add_of_nonneg_left hC01)) (sq_nonneg _)
          _≤_:=le_mul_of_one_le_right (by positivity) hHone
  · apply le_trans _ (hbase D3 hD3 (hD 3) 0)
    dsimp only [CenteredMomentSecondChildPowerBudget.coefficients,fixedFactors,losses,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    rw [Real.rpow_zero,mul_one]
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hseed0
    calc
      _≤D3*(p.control U)^2:=mul_le_mul_of_nonneg_left h00c hD3
      _≤D3*(C0+C1+1)*(p.control U)^2*H^J:=by
        calc
          _≤D3*(C0+C1+1)*(p.control U)^2:=mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right hD3 (le_add_of_nonneg_left hC01)) (sq_nonneg _)
          _≤_:=le_mul_of_one_le_right (by positivity) hHone

end SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights

end

end OAI

end Source2055

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalMainHomogeneous.lean; sha256: 9c7d3b7d27444e0e8fdb6a69189fd42abbf9d6225e407c601b90fa4b13c9909c -/
section Source2056
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous
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

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients
theorem actual_main_homogeneous
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
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(hcost:1≤cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
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
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
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
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    CenteredMomentEnergyCanonicalMainSeparatedPower.actual_main_separated_power (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  have hlo:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N lower a hlower haPlain
  obtain ⟨Uprofile,Jheight,hweights⟩:=
    CenteredMomentEnergyFirstGaussianProfileWeights.actual_weights (a:=a) (b:=b)
      N upper (max 1 b) (max 1 b) ((max 1 Mslot)^N)
      (CenteredMomentSecondInputCapacitySource.lowerFactor N lower a)
      Cm Ce Cd Ct Cc cost εsrc δsrc θsrc Bcap J (dc+degree+4*n) (dc+degree+4*n)
      Sp T Sf CenteredMomentFirstAmplificationChoice.ballProfile
      (zero_le_one.trans hupper) (le_trans zero_le_one (le_max_left _ _))
      (le_trans zero_le_one (le_max_left _ _)) (by positivity) hlo
      hCm.le hCe hCd.le hCt.le hCc.le (zero_le_one.trans hcost)
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hwbound⟩:=hweights (internalQ Q η₀) Kc hKc.le
  refine ⟨Cbound,hCbound,Zi,hZi,?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  let input:=child src C R0 B τ t
  let Scols:=finiteColumns (Fintype.piFinset input.pools)
  let β:=coefficient input (R0*C) seed
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β rfl rfl
  have hg:=hbound 1 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  have hz:0<Z:=zero_lt_one.trans (hZi.trans_le hZ)
  have hmass:mass src≤(max 1 Mslot)^N:=
    CenteredMomentEnergyOriginalProfileControl.slot_product_le src N (max 1 Mslot)
      (le_max_left _ _) hcard (fun i=>(hMs i).trans (le_max_right _ _))
  have hnseed:1≤(seed.absNorm:ℝ):=norm_ge_one seed hseed0
  have hh:=hwbound p Z t height (mass src) (seed.absNorm:ℝ) C₀ C₁
    hz hheight (mass_nonneg src) hmass hnseed hC₀ hC₁
  dsimp only at hh
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos input).le _)
  apply mul_le_mul_of_nonneg_right (hh j)
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
    try unfold mainCommonRadius
  all_goals positivity

end SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous

end

end OAI

end Source2056

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalMainSubsets.lean; sha256: e5dfb8c5a934e078a10ac72db32d1e895c98dbdf7f54ed8380944f1d7b0fb5aa -/
section Source2057
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainSubsets
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

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients
theorem actual_original_subsets_main_power
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
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(hcost:1≤cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
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
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  have hmain (Aorig:Finset α):=
    CenteredMomentEnergyCanonicalMainHomogeneous.actual_main_homogeneous (α:=Aorig) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource (fun i=>lows i.val) (fun i=>highs i.val)
      (fun i=>hhighs i.val) εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  choose Uj Jj hj using hmain
  let Uprofile:Finset (ℕ×ℕ):=Finset.univ.biUnion Uj
  let Jheight:ℕ:=∑Aorig:Finset α,Jj Aorig
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  choose Cj hCj Zj hZj hconsume using fun Aorig=>hj Aorig η₀ Q hQM hQ0 hQt hQ72
  let Cbound:ℝ:=1+∑Aorig:Finset α,Cj Aorig
  let Z₀:ℝ:=2+∑Aorig:Finset α,|Zj Aorig|
  have hCbound:0<Cbound:=by
    have hh:=Finset.sum_nonneg (fun Aorig (_:Aorig∈(Finset.univ:Finset (Finset α)))=>(hCj Aorig).le)
    dsimp [Cbound];linarith
  have hZ₀:1<Z₀:=by
    have hh:=Finset.sum_nonneg (fun Aorig (_:Aorig∈(Finset.univ:Finset (Finset α)))=>abs_nonneg (Zj Aorig))
    dsimp [Z₀];linarith
  have hCC (Aorig:Finset α):Cj Aorig≤Cbound:=by
    have hh:=Finset.single_le_sum (fun A (_:A∈(Finset.univ:Finset (Finset α)))=>(hCj A).le)
      (Finset.mem_univ Aorig)
    dsimp [Cbound];linarith
  have hZZ (Aorig:Finset α):Zj Aorig≤Z₀:=by
    have hh:=Finset.single_le_sum (fun A (_:A∈(Finset.univ:Finset (Finset α)))=>abs_nonneg (Zj A))
      (Finset.mem_univ Aorig)
    dsimp [Z₀];linarith [le_abs_self (Zj Aorig)]
  refine ⟨Cbound,hCbound,Z₀,hZ₀,?_⟩
  intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  have hposA:=positiveAt_subtype M H hH Aorig Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hg:=hconsume Aorig θ Z ((hZZ Aorig).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hposA
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  have hsub:Uj Aorig⊆Uprofile:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨Aorig,Finset.mem_univ _,hx⟩
  have hp:p.control (Uj Aorig)≤p.control Uprofile:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hJ:Jj Aorig≤Jheight:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ Aorig)
  have hz:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hp0:=p.control_nonneg (Uj Aorig)
  have hp1:=p.control_nonneg Uprofile
  have hh:(1+|t|+height)^(Jj Aorig)≤(1+|t|+height)^Jheight:=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hfront:Cj Aorig*(C₀+C₁+1)*(p.control (Uj Aorig))^2*(1+|t|+height)^(Jj Aorig)≤
      Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight:=by
    have hc:=hCC Aorig
    have hc0:0≤Cj Aorig:=(hCj Aorig).le
    gcongr
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos _).le _)
  apply mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _))
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
    try unfold mainCommonRadius
  all_goals positivity

end SevenEighths.CenteredMomentEnergyCanonicalMainSubsets

end

end OAI

end Source2057

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalNestedReference.lean; sha256: 014825de985bcbe9d567d396bfea684f5cd77060e7d76c371c49b6cad854c118 -/
section Source2058
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalNestedReference
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

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

theorem nested_original_subsets_reference_paid (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀Jparent:Finset α,∀Jorig:Finset Jparent,∀θ:Jorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Jorig→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Jorig,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤Z^L → d.X₂≤Z^L → d.Y₁≤Z^L → d.Y₂≤Z^L →
    ∀A Mparent reference u ell δ₁ δ₂ θclip:ℝ,0<reference →
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Real.logb Z reference≤
      A-Mparent+6*(u+ell)+δ₁+Real.logb Z (ratioPenalty dyad) →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z reference≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  let Pairs:=ΣJparent:Finset α,Finset Jparent
  have hex (J:Pairs):=actual_reference_paid_source (α:=J.2) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  choose n T dc Cc hCc hbound using hex
  let n₀:=∑J:Pairs,n J
  let dc₀:=∑J:Pairs,dc J
  let T₀:Finset (ℕ×ℕ):=Finset.univ.biUnion T
  let Ctot:ℝ:=1+∑J:Pairs,Cc J
  have hCt:0<Ctot:=by
    have hh:=Finset.sum_nonneg (fun J (_:J∈(Finset.univ:Finset Pairs))=>(hCc J).le)
    dsimp [Ctot];linarith
  refine ⟨n₀,T₀,dc₀,Ctot,hCt,?_⟩
  intro η₀
  let Choices:=ΣJ:Pairs,J.2→RayQuotient.Characters M H
  let:Fintype (RayQuotient.Characters M H):=Fintype.ofFinite _
  let:Fintype Choices:=inferInstance
  have hchoices (c:Choices):∃Z₀:ℝ,1<Z₀ ∧ _:=hbound c.1 η₀ c.2
  choose Zchoice hZchoice hb using hchoices
  let Z₀:ℝ:=1+∑c:Choices,Zchoice c
  have hZ₀:1<Z₀:=by
    have hn:Nonempty Choices:=⟨⟨⟨∅,∅⟩,fun i=>False.elim (Finset.notMem_empty _ i.property)⟩⟩
    let:Nonempty Choices:=hn
    have hh:=Finset.sum_pos (s:=Finset.univ) (fun c _=>(zero_lt_one.trans (hZchoice c)))
      Finset.univ_nonempty
    dsimp [Z₀];linarith
  refine ⟨Z₀,hZ₀,?_⟩
  intro Jparent Jorig θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hZi:Zchoice ⟨⟨Jparent,Jorig⟩,θ⟩≤Z:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ)
      (fun c _=>(zero_lt_one.trans (hZchoice c)).le) (Finset.mem_univ (⟨⟨Jparent,Jorig⟩,θ⟩:Choices))
    dsimp [Z₀] at hZ
    linarith
  have hp₀:=positiveAt_subtype M H hH Jparent W bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hp:=positiveAt_subtype M H hH Jorig W bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hp₀
  have hh:=hb ⟨⟨Jparent,Jorig⟩,θ⟩ Z hZi εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hp
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hc:Cc ⟨Jparent,Jorig⟩≤Ctot:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ) (fun J _=>(hCc J).le) (Finset.mem_univ (⟨Jparent,Jorig⟩:Pairs))
    dsimp [Ctot];linarith
  have ht:T ⟨Jparent,Jorig⟩⊆T₀:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨⟨Jparent,Jorig⟩,Finset.mem_univ _,hx⟩
  have hctrl:p.control (T ⟨Jparent,Jorig⟩)≤p.control T₀:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hn₀:n ⟨Jparent,Jorig⟩≤n₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ (⟨Jparent,Jorig⟩:Pairs))
  have hdc₀:dc ⟨Jparent,Jorig⟩≤dc₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ (⟨Jparent,Jorig⟩:Pairs))
  have hdeg:dc ⟨Jparent,Jorig⟩+degree+4*n ⟨Jparent,Jorig⟩≤dc₀+degree+4*n₀:=by omega
  have hpow:(1+(|v|+height))^(dc ⟨Jparent,Jorig⟩+degree+4*n ⟨Jparent,Jorig⟩)≤
      (1+(|v|+height))^(dc₀+degree+4*n₀):=
    pow_le_pow_right₀ (by linarith [abs_nonneg v]) hdeg
  have hcontrol:=p.control_nonneg (T ⟨Jparent,Jorig⟩)
  have hd:0≤diagonalControl (canonicalRadial τ (internalQ Q η₀) dyad).profile:=by
    unfold diagonalControl;positivity
  have hz0:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hr:0<ratioPenalty dyad:=zero_lt_one.trans_le (le_max_left _ _)
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyCanonicalNestedReference

end

end OAI

end Source2058

/- Original source: OAI/NumberTheory/DirichletL/Energy/ActiveChildRestoration.lean; sha256: ce4a798fdd67dea471ebf8e6868f4dfac393507d0540c9de332fe5d9a35db066 -/
section Source2059
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyActiveChildRestoration
open ConcretePrimeRowBridge
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonHeightEnvelope
open CenteredMomentFirstAnnularInput CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α]
local instance {β:Type*}:DecidableEq β:=Classical.decEq _

theorem allocated_row_active (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:Character)(v:ℝ)
    (D:Ideal O)(a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (z:O)(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ):
    let d : CenteredMomentEligibleEnergy.Data (CenteredMomentCommonProfile.liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    let e : CenteredMomentEligibleEnergy.Data (CenteredMomentCommonProfile.liveIndices B.val) :=
      commonData (withHeight s τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools, restoreAllocation_val]
          using (restoreAllocation s C B).property⟩
    allocatedPositiveRow d.η d.m d.A z d.t d.slots d.coefficient d.P D a W₁ W₂ X₁ X₂=
      allocatedPositiveRow e.η e.m e.A z e.t e.slots e.coefficient e.P D a W₁ W₂ X₁ X₂ := by
  change positiveSlotRow τ
      (CenteredMomentSecondHeightFamily.fixedBadMask * idealGenerator (R * C)) 1 z
      (dilated W₁ (clipDilation (X₁ / Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a 0))))
      (dilated W₂ (clipDilation (X₂ / Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a 1))))
      (fun i : CenteredMomentDivisorRaw.liveIndices D a => (activeInput s).slots i.val.val)
      (fun i => (activeInput s).toData.coefficient i.val.val)
      (fun i => (activeInput s).P i.val.val) v _ _ =
    positiveSlotRow τ
      (CenteredMomentSecondHeightFamily.fixedBadMask * idealGenerator (R * C)) 1 z
      (dilated W₁ (clipDilation (X₁ / Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a 0))))
      (dilated W₂ (clipDilation (X₂ / Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a 1))))
      (fun i : CenteredMomentDivisorRaw.liveIndices D a => s.slots i.val.val)
      (fun i => s.toData.coefficient i.val.val)
      (fun i => s.P i.val.val) v _ _
  unfold positiveSlotRow
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  have hz (f : Ideal O → ℂ) : heightCoefficient f 0 = f := by
    funext I
    simp [heightCoefficient]
  simpa only [hz] using rowSlot_active s i.val.val τ
    (CenteredMomentSecondHeightFamily.fixedBadMask * idealGenerator (R * C)) 1 z v 0

theorem child_energy_active (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:Character)(v:ℝ)
    (D:Ideal O)(a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (rad:Radial):
    let d : CenteredMomentEligibleEnergy.Data (CenteredMomentCommonProfile.liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    let e : CenteredMomentEligibleEnergy.Data (CenteredMomentCommonProfile.liveIndices B.val) :=
      commonData (withHeight s τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools, restoreAllocation_val]
          using (restoreAllocation s C B).property⟩
    childEnergy d rad D a = childEnergy e rad D a := by
  dsimp only
  unfold childEnergy
  apply tsum_congr
  intro z
  exact congrArg₂ (fun x y : ℂ => rad.weight z * (‖x‖ ^ 2 + ‖y‖ ^ 2))
    (allocated_row_active s C R B τ v D a z s.W₁ s.W₂
      (s.X₁ / Ideal.absNorm (B.val (Sum.inr 0)))
      (s.X₂ / Ideal.absNorm (B.val (Sum.inr 1))))
    (allocated_row_active s C R B τ v D a z s.W₁ s.W₂
      (s.Y₁ / Ideal.absNorm (B.val (Sum.inr 0)))
      (s.Y₂ / Ideal.absNorm (B.val (Sum.inr 1))))

end SevenEighths.CenteredMomentEnergyActiveChildRestoration

end

end OAI

end Source2059

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalErrorPaid.lean; sha256: 2156106603dde3f017a37fbe44d7bc17757205a6442d677920c5b770357edf8e -/
section Source2060
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorPaid
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][instα:DecidableEq α]

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

open CenteredMomentEnergyCanonicalMainPaid CenteredMomentEnergyCanonicalNestedReference
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open CenteredMomentEnergyActiveChildRestoration

def castAllocation (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C):actualAllocations t.pools C:=
  ⟨B.val,by rw [←h];exact B.property⟩

def castDivisorAllocation (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))):
    Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices (castAllocation s t h C B).val⊕Fin 2)):=alloc

def restoreDivisorAllocation (s:Input α)(C:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))):
    Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices (restoreAllocation s C B).val⊕Fin 2)):=alloc

lemma cast_child_energy (s t:Input α)(h:s=t)(C R:Ideal O)
    (B:actualAllocations s.pools C)(τ:Character)(v:ℝ)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (rad:Radial):
    childEnergy (commonData (withHeight s τ v) C R B) rad D alloc=
      childEnergy (commonData (withHeight t τ v) C R (castAllocation s t h C B)) rad D
        (castDivisorAllocation s t h C B D alloc):=by
  subst t
  rfl

lemma restored_child_energy (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:Character)(v:ℝ)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (rad:Radial):
    childEnergy (commonData (withHeight (activeInput s) τ v) C R B) rad D alloc=
      childEnergy (commonData (withHeight s τ v) C R (restoreAllocation s C B)) rad D
        (restoreDivisorAllocation s C B D alloc):=by
  cases Subsingleton.elim instα (Classical.decEq α)
  exact child_energy_active s C R B τ v D alloc rad

omit instα in
lemma cast_preVolume (s t:Input α)(h:s=t)(C R:Ideal O)
    (B:actualAllocations s.pools C)(τ:Character)(v:ℝ):
    CenteredMomentAllocatedChildCapacity.preVolume (commonData (withHeight t τ v) C R (castAllocation s t h C B))=
      CenteredMomentAllocatedChildCapacity.preVolume (commonData (withHeight s τ v) C R B):=by
  subst t
  rfl

omit instα in
lemma cast_slot_sum (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C)(f:α→ℝ):
    (∑i:CenteredMomentCommonProfile.liveIndices (castAllocation s t h C B).val,f i.val)=
      ∑i:CenteredMomentCommonProfile.liveIndices B.val,f i.val:=rfl

omit instα in
lemma restored_preVolume (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:Character)(v:ℝ):
    CenteredMomentAllocatedChildCapacity.preVolume (commonData (withHeight s τ v) C R (restoreAllocation s C B))=
      CenteredMomentAllocatedChildCapacity.preVolume (commonData (withHeight (activeInput s) τ v) C R B):=rfl

omit instα in
lemma restored_slot_sum (s:Input α)(C:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(f:α→ℝ):
    (∑i:CenteredMomentCommonProfile.liveIndices (restoreAllocation s C B).val,f i.val)=
      ∑i:CenteredMomentCommonProfile.liveIndices B.val,f i.val:=rfl

theorem actual_error_child_from_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤M → ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤sigma → 1≤cost → 0<asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=1 ∨ k=6 ∨ k=7) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^k),
    ∀(υ:Character)(v0:ℝ),
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock υ v0 Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kerror dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family υ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    let δpaid:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
      sourceReserve src input C D Z delta reserve cost asource
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      Cc*(Ideal.absNorm (Rpick*Cpick).radical:ℝ)^εmask*(C₀+C₁)*
        diagonalControl (canonicalRadial (family χ) (internalQ Q η₀) dyad).profile*
        (p.control T)^2*(1+(|v|+height))^(dc+degree+4*n)*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(errorRemoval prime Z k+δpaid/6+θclip/3)+κ*mesh):=by
  cases Subsingleton.elim instα (Classical.decEq α)
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=nested_original_subsets_reference_paid (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀
  refine ⟨Z₀,hZ₀,?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource hK hsigma hcost hasource
    prime hprime k hk hprimeScale hslot Bp υ v0 hυ input hinput
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  subst input
  have hz:1<Z:=hZ₀.trans_le hZ
  have hcost0:0<cost:=zero_lt_one.trans_le hcost
  let input:=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  let restored:=restoredError src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  have heInput:input=activeInput restored:=by
    exact error_source_active src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  let B₂a:=castAllocation input (activeInput restored) heInput Cpick B₂
  let B₂r:=restoreAllocation restored Cpick B₂a
  let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
  have hKerror:0<Kerror:=by dsimp [Kerror];unfold errorCommonRadius;positivity
  have hP:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hz.le (hw i)
  have hcap':length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤Mdecl:=by
    simpa only [hmatch.scale,Real.logb_rpow (zero_lt_one.trans hz) hz.ne'] using hcap
  obtain ⟨hδ,hpar,hshift⟩:=actual_active_error_admission src τ υ C D R0 hC hD hCD E B t hB
    K Z sigma delta reserve cost asource hK hz hcost0 hasource prime hprime k hk hsigma hprimeScale
    hslot Bp v0 hmod Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical
    Cpick Rpick hside B₂ hB₂ κ Mdecl hκsmall hP hcap' hMdecl
  have hm:=restoredError_matches M H hH hmatch C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  have caps₁:=common_raw_caps src C R0 B τ t (Z^L) hX₁ hX₂ hY₁ hY₂
  have caps₂:=common_raw_caps (child src C R0 B τ t) ((Ideal.span {prime})^k) (R0*C)
    (restoreAllocation (child src C R0 B τ t) ((Ideal.span {prime})^k) Bp) υ v0 (Z^L)
    caps₁.1 caps₁.2.1 caps₁.2.2.1 caps₁.2.2.2
  have caps₃:=common_raw_caps restored Cpick Rpick B₂r (family χ) v (Z^L)
    caps₂.1 caps₂.2.1 caps₂.2.2.1 caps₂.2.2.2
  have hτnorm:0<(τ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hqpos:0<cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k):=by positivity
  have hdef:=actual_width_le_reference hfamily v0 Scols βsource Rwindow rows Wkernel Kerror hKerror dyad
    hphysical (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) Z hυ hz χ
  have hn:=actual_dyad_ge_one v0 Scols βsource Rwindow rows Wkernel Kerror dyad hphysical
  have hrem:0≤errorRemoval prime Z k:=by
    have hn:0≤Real.logb Z (normValue prime):=by linarith
    unfold errorRemoval
    positivity
  have hsum:(∑i:CenteredMomentCommonProfile.liveIndices B₂.val,Real.logb Z (input.P i.val))=
      ∑i:CenteredMomentCommonProfile.liveIndices B₂.val,w i.val.val.val:=by
    apply Finset.sum_congr rfl
    intro i hi
    change Real.logb Z (src.P i.val.val.val)=w i.val.val.val
    rw [hmatch.scale,Real.logb_rpow (zero_lt_one.trans hz) hz.ne']
  have hparw:Real.logb Z (volume src)+(6*κ-1)*
      (∑i:CenteredMomentCommonProfile.liveIndices B₂r.val,w i.val.val.val)≤Mdecl:=by
    rw [hsum] at hpar
    have heSum := (restored_slot_sum restored Cpick B₂a (fun i=>w i.val.val)).trans
      (cast_slot_sum input (activeInput restored) heInput Cpick B₂ (fun i=>w i.val.val))
    exact (congrArg (fun x=>Real.logb Z (volume src)+(6*κ-1)*x) heSum).trans_le hpar
  have hshiftw:
      Real.logb Z ((commonData (withHeight restored (family χ) v) Cpick Rpick B₂r).X₁*
        (commonData (withHeight restored (family χ) v) Cpick Rpick B₂r).X₂*
        ∏i:CenteredMomentCommonProfile.liveIndices B₂r.val,restored.P i.val)-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)≤
      Real.logb Z (volume src)-Mdecl+6*(errorRemoval prime Z k+0)+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          sourceReserve src input C D Z delta reserve cost asource)+Real.logb Z (ratioPenalty dyad):=by
    change Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume
      (commonData (withHeight restored (family χ) v) Cpick Rpick B₂r))-_≤_
    have hpv:= (restored_preVolume restored Cpick Rpick B₂a (family χ) v).trans
      ((cast_preVolume input (activeInput restored) heInput Cpick Rpick B₂ (family χ) v).trans
        (common_preVolume_height input Cpick Rpick B₂ (family χ) υ v v0))
    calc
      _ = Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume
          (commonData (withHeight input υ v0) Cpick Rpick B₂)) -
          Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad) :=
        congrArg (fun x=>Real.logb Z x - Real.logb Z
          (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)) hpv
      _ ≤ _ := by
        dsimp only [input]
        simpa only [add_zero] using hshift
  have hh:=hbound (CenteredMomentCommonProfile.liveIndices B.val)
    (CenteredMomentCommonProfile.liveIndices Bp.val) (fun i=>θ i.val.val)
    Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    (fun i=>w i.val.val) (fun i=>σ i.val.val) (fun i=>freq i.val.val) v height mesh hmesh
    (fun i=>hw i.val.val) (fun i=>hwm i.val.val) (fun i=>hwL i.val.val) (fun i=>hσlo i.val.val)
    (fun i=>hσhi i.val.val) hheight (fun i=>hfreq i.val.val)
  have hh := hh restored hm (fun i=>hhi i.val.val) (fun i=>hMs i.val.val)
  have hh := hh Cpick Rpick B₂r
  let allocA:=castDivisorAllocation input (activeInput restored) heInput Cpick B₂ Dalloc alloc
  let allocR:=restoreDivisorAllocation restored Cpick B₂a Dalloc allocA
  have hh := hh Dalloc allocR hRpick
  have hh := hh (family χ) dyad hn hwidth
  have hh := hh p hp₁ hp₂
  have hh := hh caps₃.1 caps₃.2.1 caps₃.2.2.1 caps₃.2.2.2
  have hh := hh (Real.logb Z (volume src)) Mdecl
    (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)
    (errorRemoval prime Z k) 0
    (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
      sourceReserve src input C D Z delta reserve cost asource)
    0 θclip (envelope_pos _ hqpos _ _ hC₂ _ _)
    hrem le_rfl hδ le_rfl hθclip
  have hh := hh hparw
  have hh := hh hshiftw
  have hh := hh (by linarith only [hdef]) hclip
  have he := (cast_child_energy input (activeInput restored) heInput Cpick Rpick B₂ (family χ) v Dalloc alloc
    (canonicalRadial (family χ) (internalQ Q η₀) dyad)).trans
      (restored_child_energy restored Cpick Rpick B₂a (family χ) v Dalloc allocA
        (canonicalRadial (family χ) (internalQ Q η₀) dyad))
  apply he.trans_le
  simpa only [zero_add,add_zero] using hh

end SevenEighths.CenteredMomentEnergyCanonicalErrorPaid

end

end OAI

end Source2060

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalErrorUniform.lean; sha256: 516270768ed47866665040ff65bb591856226789d91dc700b63956a065f9aec7 -/
section Source2061
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorUniform
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

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

open CenteredMomentEnergyCanonicalMainPaid CenteredMomentEnergyCanonicalNestedReference
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open CenteredMomentEnergyActiveChildRestoration

theorem actual_error_uniform_child (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 BR BC θsource:ℝ)
    (hlower:0<lower)(ha0:0<a0)(hθsource:0<θsource):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤M → ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤sigma → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=1 ∨ k=6 ∨ k=7) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^k),
    ∀(υ:Character)(v0:ℝ),
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock υ v0 Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kerror dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family υ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    (Rpick.absNorm:ℝ)≤Z^BR → (Cpick.absNorm:ℝ)≤Z^BC →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
        ((BR+BC)*εmask+(εchild+εremove+errorRemoval prime Z k+
          (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
            delta+reserve+θsource)/6+θclip/3+κ*mesh))*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad*
        (ratioPenalty dyad)^((1:ℝ)/6)*(1+‖v‖)^(2*(dc+degree+4*n))  :=by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=
    CenteredMomentEnergyCanonicalErrorPaid.actual_error_child_from_bands (α:=α) M H hH
      W aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL
      degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
  obtain ⟨Zr,hZr,hr⟩:=CenteredMomentFirstAmplifiedPaidReserve.eventually_source_reserve
    N lower upper 1 a0 θsource hlower (by norm_num) ha0 hθsource
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Zi,hZi,hi⟩:=hbound η₀
  refine ⟨max Zi Zr,lt_of_lt_of_le hZi (le_max_left _ _),?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ v0 hυ input hinput
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlowerBeta hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick hRN hCN B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hZiZ:Zi≤Z:=(le_max_left _ _).trans hZ
  have hZrZ:Zr≤Z:=(le_max_right _ _).trans hZ
  have hz:1<Z:=hZi.trans_le hZiZ
  have hh:=hi θ Z hZiZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource
    hK hsigma hcost hasource prime hprime k hk hprimeScale hslot Bp υ v0 hυ
    input hinput
    Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad
    hlowerBeta hphysical family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hupperInput:input.upper≤upper:=by rw [hinput];exact hupperSrc
  have hchild:Fintype.card (CenteredMomentCommonProfile.liveIndices B.val)≤N:=
    (CenteredMomentAmplificationChildSourceCaps.live_card_le B.val).trans hcard
  have herr:Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤N:=
    (CenteredMomentAmplificationChildSourceCaps.live_card_le Bp.val).trans hchild
  have hsmall:sourceReserve src input C D Z delta reserve cost asource≤delta+reserve+θsource:=
    hr Z hZrZ src input hcard herr hlowerSrc hupperInput C D hC.1 hD.1
      delta reserve cost asource hdelta hreserve hcost haSource
  have hCp:Cpick≠0:=by rcases hside with rfl|rfl;exact hC₂.1;exact hD₂.1
  have hqpos:0<cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k):=
    mul_pos (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _)
  have href:0<envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad:=
    envelope_pos _ hqpos C₂ D₂ hC₂ U dyad
  apply hh.trans
  apply CenteredMomentEnergyChildEnvelopeFitting.paid_rhs_fit Cc C₀ C₁ p T Rpick Cpick hRpick hCp
    (family χ) (internalQ Q η₀) dyad v height (dc+degree+4*n) Z BR BC εmask
    _ _ _ _ hCc.le hC₀ hC₁ hheight hz.le hεmask.le hRN hCN
  · linarith
  · exact href.le
  · exact zero_le_one.trans (le_max_left _ _)

end SevenEighths.CenteredMomentEnergyCanonicalErrorUniform

end

end OAI

end Source2061

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondFrozenPowerDescent.lean; sha256: ee5c21f970f4058c343aa80dfb10bfcc5300bd4c50540bfce9773d987926029c -/
section Source2062
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenPowerDescent
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
open CenteredMomentSecondSourcePowerDescent CenteredMomentSecondNonexceptionalScalar

theorem original_subsets_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤s.b₁ → 0≤s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
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
        (physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩ :=
    CenteredMomentSecondFrozenUniformSubset.original_subsets_source_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ ε δ θ B ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  let a:=physicalFactors Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ Sf W
  have ha : ∀j,0≤a j := physicalFactors_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hCm.le hCe hCd.le hCt.le (zero_le_one.trans hZ.1.le) hKphys.le (by positivity)
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le))
  have hh': ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      sourceCost s Sp p J Q Kc ε (seed.absNorm:ℝ) a := by
    convert hh using 1
    dsimp [sourceCost,a,physicalFactors]
    simp_rw [hhis]
    dsimp [mass, CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume]
    ring
  exact hh'.trans (source_rhs s N b b₁ b₂ A hb hb₁ hb₂ hu hc
    (fun i=>by rw [hhis]; exact hhi i.val) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha)

end SevenEighths.CenteredMomentSecondFrozenPowerDescent

end

end OAI

end Source2062

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstNestedSeededGaussianPower.lean; sha256: 9def1d5e3813686a356230528ffcae821dedb03d49e72b2705957e6656a84464 -/
section Source2063
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNestedSeededGaussianPower
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

open CenteredMomentFirstSeededGaussianPower CenteredMomentSecondFrozenRatioCost
open CenteredMomentSecondUniformSubsetSource

abbrev NestedIndex (α:Type*) := ΣT:Finset α,Finset T

def emptyIndex : NestedIndex ι := ⟨∅,∅⟩

theorem nested_source_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : NestedIndex ι, ∀(s:Input T.2)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val.val) → (∀i,s.hi i=hi i.val.val) →
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
        (1+(∏i:T.2,hi i.val.val)*whi*whi)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ)+
      Cexc*profileFactor Sprofile s p J Q Kc*
        Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)+
      Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys*Z^(-saving)  := by
  have hall (T : NestedIndex ι) := CenteredMomentSecondFrozenLiveDescent.original_source_descent
    wlo whi hwlo hwhi (fun i:T.2=>lo i.val.val) (fun i:T.2=>hi i.val.val) (fun i=>hhi i.val.val)
    W J₁ J₂ ε δ θ B ξ saving hε hδ hθ hB hξ
  choose J Sp Sf hSp Cm Ce Cd Ct hCm hCe hCd hCt hbound using hall
  let J0 : ℕ := ∑T:NestedIndex ι,J T
  let Sp0 := Finset.univ.biUnion Sp
  let Sf0 := Finset.univ.biUnion Sf
  let Cm0 : ℝ := 1+∑T:NestedIndex ι,Cm T
  let Ce0 : ℝ := 1+∑T:NestedIndex ι,Ce T
  let Cd0 : ℝ := 1+∑T:NestedIndex ι,Cd T
  let Ct0 : ℝ := 1+∑T:NestedIndex ι,Ct T
  have sum_pos (f : NestedIndex ι→ℝ) (hf : ∀T,0≤f T) : 0<1+∑T:NestedIndex ι,f T := by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (NestedIndex ι)))=>hf T)
    linarith
  have sum_le (f : NestedIndex ι→ℝ) (hf : ∀T,0≤f T) (T : NestedIndex ι) : f T≤1+∑U:NestedIndex ι,f U := by
    have hh:=Finset.single_le_sum (fun U (_:U∈(Finset.univ:Finset (NestedIndex ι)))=>hf U) (Finset.mem_univ T)
    linarith
  refine ⟨J0,Sp0,Sf0,Finset.mem_biUnion.mpr ⟨emptyIndex,Finset.mem_univ _,hSp emptyIndex⟩,
    Cm0,Ce0,Cd0,Ct0,sum_pos Cm (fun T=>(hCm T).le),(sum_pos Ce hCe).le,
    sum_pos Cd (fun T=>(hCd T).le),sum_pos Ct (fun T=>(hCt T).le),?_⟩
  intro Q hQ hQt hQ72
  choose K hK hev using fun T=>hbound T Q hQ hQt hQ72
  let K0 : ℝ := 1+∑T:NestedIndex ι,K T
  refine ⟨K0,sum_pos K (fun T=>(hK T).le),?_⟩
  have heall : ∀ᶠ Z : ℝ in atTop, ∀T:NestedIndex ι,_ := Filter.eventually_all.mpr hev
  filter_upwards [heall] with Z hZ
  refine ⟨(hZ emptyIndex).1,?_⟩
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
  have hprodhi : 0≤∏i:T.2,hi i.val.val := Finset.prod_nonneg (fun i _=>hhi i.val.val)
  have hprodlo : 0≤∏i:T.2,s.lo i := Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)
  apply hh.trans
  gcongr

theorem nested_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : NestedIndex ι, ∀(s:Input T.2)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val.val) → (∀i,s.hi i=hi i.val.val) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T.2≤N → 0≤s.b₁ → 0≤s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
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
        (physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩ :=
    nested_source_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ ε δ θ B ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  let a:=physicalFactors Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ Sf W
  have ha : ∀j,0≤a j := physicalFactors_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hCm.le hCe hCd.le hCt.le (zero_le_one.trans hZ.1.le) hKphys.le (by positivity)
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le))
  have hh': ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      sourceCost s Sp p J Q Kc ε (seed.absNorm:ℝ) a := by
    convert hh using 1
    dsimp [sourceCost,a,physicalFactors]
    simp_rw [hhis]
    dsimp [mass, CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume]
    ring
  exact hh'.trans (source_rhs s N b b₁ b₂ A hb hb₁ hb₂ hu hc
    (fun i=>by rw [hhis]; exact hhi i.val.val) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha)

theorem nested_seeded_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : NestedIndex ι, ∀(s:Input T.2)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val.val) → (∀i,s.hi i=hi i.val.val) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T.2≤N → 0≤s.b₁ → 0≤s.b₂ →
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
    nested_source_descent
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
    (fun i=>by rw [hhis]; exact hhi i.val.val) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha)

theorem nested_reference_seeded_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : NestedIndex ι, ∀(s:Input T.2)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val.val) → (∀i,s.hi i=hi i.val.val) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T.2≤N → 0≤s.b₁ → 0≤s.b₂ →
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
    nested_seeded_power_descent
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

theorem actual_nested_subsets_seeded_gaussian_power (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : NestedIndex ι, ∀(s:Input T.2)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val.val) → (∀i,s.hi i=hi i.val.val) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T.2≤N → 0≤s.b₁ → 0≤s.b₂ →
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
    nested_reference_seeded_power_descent
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

end SevenEighths.CenteredMomentFirstNestedSeededGaussianPower

end

end OAI

end Source2063

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalErrorGaussian.lean; sha256: 59bee2e42a23ec15dda1d1a856bd70110f9dc6a5b2bd298c070d745b9fb141d7 -/
section Source2064
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorGaussian
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

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

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_error_gaussian_from_bands
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
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=1 ∨ k=6 ∨ k=7) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^k),
    ∀(υ:Character)(v0:ℝ),
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
    Ready input ((R0*C)*(Ideal.span {prime})^k) Kerror Z ξ Bcap →
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
    β=coefficient input ((R0*C)*(Ideal.span {prime})^k) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    (∀q∈liveLabels input.η Scols β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀dyad:SourceBlocks q.val.1 q.val.2 U Kerror (frequencyRadius (nominal input Kerror) Z ξ)
        (sourceRadius input),
      physicalBlock input.η input.t (activeSource Scols β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U
        (frequencyRadius (nominal input Kerror) Z ξ)
        (partRows false input.η χ₀ (internalQ Q η₀) m q.val.1 q.val.2 U
          (frequencyRadius (nominal input Kerror) Z ξ))
        CenteredMomentFirstAmplificationChoice.ballProfile Kerror (fun i=>(dyad i:ℤ))≠0 →
      ∀χ:RayCharacter,Real.logb Z (dyadicScale (dyad 1))+
        Real.logb Z ((family q U χ).modulus.absNorm:ℝ)≤Mcap) →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let Echild:=CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+errorRemoval prime Z k+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3+κ*mesh))
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^k) seed CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc v0
        εsrc (seed.absNorm:ℝ)
        (seededFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Kerror v0
          (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) Echild Echild r (∏i,input.lo i) a (seed.absNorm:ℝ)
          (dc+degree+4*n) (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,hmain⟩:=
    CenteredMomentEnergyCanonicalErrorUniform.actual_error_uniform_child (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL
      degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
      N lower upper a0 Bcap Bcap θsource hlower ha0 hθsource
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hgauss⟩:=
    actual_nested_subsets_seeded_gaussian_power a b haPlain hbPlain lows highs hhighs
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
    prime hprime k hk hprimeScale hslot Bp υ v0 hυ input hinput
  subst input
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip
    hcap hMdecl hclip hasourceFactor Scols β hScols hβ
  let input:=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  let Km:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
  have hZmZ:Zm≤Z:=(le_max_left _ _).trans hZ
  have hgZ:=hZg Z ((le_max_right _ _).trans hZ)
  have hz:1<Z:=hgZ.1
  have hP:∀i,1≤ input.P i:=by
    intro i
    change 1≤src.P i.val.val
    rw [hmatch.scale]
    exact Real.one_le_rpow hz.le (hw i.val.val)
  have hcardInput:Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤N:=
    (child_card Bp.val).trans ((child_card B.val).trans hcard)
  have hmass:mass input≤mass src:=
    (child_mass (activeInput (child src C R0 B τ t)) ((Ideal.span {prime})^k) (R0*C) Bp υ v0).trans
      (child_mass src C R0 B τ t)
  have hsource:=hgZ.2 ⟨CenteredMomentCommonProfile.liveIndices B.val,CenteredMomentCommonProfile.liveIndices Bp.val⟩ input p
    (fun i=>hloSrc i.val.val) (fun i=>hhiSrc i.val.val) hP hp₁.symm hp₂.symm (mass src)
    hupperSrc hcardInput hb1 hb2 hb1max hb2max hmass
    ((R0*C)*(Ideal.span {prime})^k) seed hready.puncture_ne hseed hseed0 hseedcap hready.source_nonneg hready.source_cap
    hready.conductor_cap hready.puncture_cap
  change Scols=finiteColumns (Fintype.piFinset input.pools) at hScols
  change β=coefficient input ((R0*C)*(Ideal.span {prime})^k) seed at hβ
  dsimp only at hsource
  subst Scols β
  obtain ⟨family,hfamily,hbound⟩:=hsource
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm0 hml hm2 hwidth r hr1 hr2 hr3 hr4
  let Ec:=CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+errorRemoval prime Z k+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3+κ*mesh))
  have hEc:0≤Ec:=CenteredMomentEnergyChildEnvelopeFitting.coefficient_nonneg
    Cc C₀ C₁ p T height (dc+degree+4*n) Z _ hCc.le hC₀ hC₁ hheight (zero_le_one.trans hz.le)
  have hpzero (j:Fin 2):p.profile j 0=0:=by
    by_contra hn
    exact (not_le_of_gt haPlain) ((p.support j hn).1)
  have hz1:input.W₁ 0=0:=by change src.W₁ 0=0;rw [←hp₁];exact hpzero 0
  have hz2:input.W₂ 0=0:=by change src.W₂ 0=0;rw [←hp₂];exact hpzero 1
  have hlowerInput:lower ≤ input.lower:=hlowerSrc
  have hplain₁:∀x,input.W₁ x≠0→a≤x:=by
    intro x hx
    change src.W₁ x≠0 at hx
    rw [←hp₁] at hx
    exact (p.support 0 hx).1
  have hplain₂:∀x,input.W₂ x≠0→a≤x:=by
    intro x hx
    change src.W₂ x≠0 at hx
    rw [←hp₂] at hx
    exact (p.support 1 hx).1
  have hlowerBeta (I:Ideal O)
      (hI:coefficient input ((R0*C)*(Ideal.span {prime})^k) seed I≠0):
      asource*volume input≤(I.absNorm:ℝ):=by
    exact (mul_le_mul_of_nonneg_right hasourceFactor (volume_pos input).le).trans
      (CenteredMomentSecondInputCapacitySource.actual_lower_support N lower a hlower haPlain
        input hcardInput hlowerInput hplain₁ hplain₂ _ seed I hI)
  apply hbound χ₀ m hm0 hml hm2 Km (nominal input Km) hready.scale_pos hready.volume_cap
    hready.nominal_cap (le_refl _) hready.frequency_pos hready.frequency_cap
    (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k))
    (mul_pos (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _))
    Ec Ec hEc hEc ?_ ?_ r hr1 hr2 hr3 hr4
  all_goals
    intro q hq U dyad hphysical D0 hD0 hD0cap hD0sq χ v B₂ hB₂ alloc halloc
    have hqp:=q.property
    have hg:=actual_common_gates input ((R0*C)*(Ideal.span {prime})^k) seed hseed hz1 hz2 q.val.1 q.val.2 hqp
    have hs:=commonLabels_supported (activeSource _ _) _ _ q.property
  · exact hm θ Z hZmZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
      K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ v0 hυ input rfl
      _ _ q.val.1 q.val.2 hs.1 hs.2 hg.2.2.1 U _ _ _ (fun i=>(dyad i:ℤ))
      hlowerBeta hphysical (family q U) (hfamily q U) χ (hwidth q hq U dyad hphysical χ)
      q.val.1 ((R0*C)*(Ideal.span {prime})^k) (Or.inl rfl) hready.puncture_ne hready.puncture_cap
      (hg.2.2.2.2.2.1.trans hready.source_cap) B₂ hB₂ D0 alloc p hp₁ hp₂
      hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  · exact hm θ Z hZmZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
      K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ v0 hυ input rfl
      _ _ q.val.1 q.val.2 hs.1 hs.2 hg.2.2.1 U _ _ _ (fun i=>(dyad i:ℤ))
      hlowerBeta hphysical (family q U) (hfamily q U) χ (hwidth q hq U dyad hphysical χ)
      q.val.2 ((R0*C)*(Ideal.span {prime})^k) (Or.inr rfl) hready.puncture_ne hready.puncture_cap
      (hg.2.2.2.2.2.2.trans hready.source_cap) B₂ hB₂ D0 alloc p hp₁ hp₂
      hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip

end SevenEighths.CenteredMomentEnergyCanonicalErrorGaussian

end

end OAI

end Source2064

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalErrorAdmitted.lean; sha256: 287ade302737a270a571999a2faa2395f445629b9a20cf9206d00f347b2bb333 -/
section Source2065
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorAdmitted
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

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

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_error_smaller_gaussian
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
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
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
    β=coefficient input ((R0*C)*(Ideal.span {prime})^(k+1)) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀_χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let Echild:=CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+errorRemoval prime Z (k+1)+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3+κ*mesh))
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc v0
        εsrc (seed.absNorm:ℝ)
        (seededFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Kerror v0
          (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1))) Echild Echild r (∏i,input.lo i) a (seed.absNorm:ℝ)
          (dc+degree+4*n) (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    CenteredMomentEnergyCanonicalErrorGaussian.actual_error_gaussian_from_bands (α:=α) M H hH
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
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
  subst input
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  have hZiZ:Zi≤Z:=(le_max_left _ _).trans hZ
  have hZw:Zw≤Z:=(le_max_right _ _).trans hZ
  have hz:1<Z:=hZi.trans_le hZiZ
  have hk':k+1=1 ∨ k+1=6 ∨ k+1=7:=by omega
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZiZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma.le hcost hasource hdelta hreserve haSource
    prime hprime (k+1) hk' hprimeScale hslot Bp υ v0 hυ _ rfl
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
  have hh:=CenteredMomentEnergyAmplifiedChildWidth.error_child_width N upper sigma hupper hsigma
    Z hZw src hcard hupperSrc C D R0 hC hD hCD E B τ t hB hmod
    prime hprime k hk hslot Bp υ χerr v0 hN K delta reserve ξ
    (Real.logb Z (src.η.modulus.absNorm:ℝ)) Mwidth hK hdelta hreserve hξsmall hη hMwidth
    (activeSource Scols β) β q.val.1 q.val.2 hs.1 hs.2 U (family q U) (hfamily q U)
    _ CenteredMomentFirstAmplificationChoice.ballProfile (fun i=>(dyad i:ℤ)) hphysical χ
  exact hh.le.trans hdrop

end SevenEighths.CenteredMomentEnergyCanonicalErrorAdmitted

end

end OAI

end Source2065

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalErrorPower.lean; sha256: bbe79621817f0f718ac2a9ef18188157f0fc4bc835bf34dcdb4ad77d8d4b6c00 -/
section Source2066
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorPower
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

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

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_error_power_from_bands
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
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
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
    β=coefficient input ((R0*C)*(Ideal.span {prime})^(k+1)) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀_χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+degree+4*n);
    let Hweights:=coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J
      (internalQ Q η₀) Kc v0 εsrc (seed.absNorm:ℝ)
      (CenteredMomentEnergyFirstGaussianCoefficients.fixedFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap cost Ebase v0
        (CenteredMomentSecondInputCapacitySource.lowerFactor N lower a) (seed.absNorm:ℝ)
        (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile);
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,Hweights j*CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    CenteredMomentEnergyCanonicalErrorAdmitted.actual_error_smaller_gaussian (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Kc,hKc,Zi,hZi,?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
  subst input
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  let input:=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0
  let Km:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input rfl
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  have hg:=hbound χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+degree+4*n)
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  have hz:0<Z:=zero_lt_one.trans (hZi.trans_le hZ)
  have hE:0≤Ebase:=by dsimp [Ebase];have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile;positivity
  have hcardInput:Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤N:=
    (live_card_le Bp.val).trans ((live_card_le B.val).trans hcard)
  have hloProd:=CenteredMomentEnergyOriginalProfileControl.lower_product input N lower hlower hcardInput
    (fun i=>hlowerSrc.trans (src.lower_le i.val.val))
  have hlo:CenteredMomentSecondInputCapacitySource.lowerFactor N lower a≤(∏i,input.lo i)*a*a:=by
    unfold CenteredMomentSecondInputCapacitySource.lowerFactor
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right hloProd (sq_nonneg a)
  have hcoef:=CenteredMomentEnergyFirstGaussianCoefficients.error_coefficients
    N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc prime (k+1)
    Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Km v0 (τ.modulus.absNorm:ℝ) cost Ebase
    (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid r
    (∏i,input.lo i) a (CenteredMomentSecondInputCapacitySource.lowerFactor N lower a) (seed.absNorm:ℝ)
    (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile
    (zero_le_one.trans hupper) (le_trans zero_le_one (le_max_left _ _))
    (le_trans zero_le_one (le_max_left _ _)) hKc.le (Nat.cast_nonneg _) hCm.le hCe hz hE
    (by unfold Km errorCommonRadius;positivity)
    (CenteredMomentSecondInputCapacitySource.lowerFactor_pos N lower a hlower haPlain) hlo
  have hexp:
      (Bcap+Bcap)*εmask+(εchild+εremove+errorRemoval prime Z (k+1)+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3+κ*mesh)=
      errorRemoval prime Z (k+1)+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))/6+paid :=by
    dsimp [paid];ring
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  have hh:=mul_le_mul_of_nonneg_right (hcoef j)
    (Real.rpow_nonneg (volume_pos input).le (powers εsrc j))
  simpa only [CenteredMomentEnergyChildEnvelopeFitting.coefficient,hexp,Ebase,paid] using hh

end SevenEighths.CenteredMomentEnergyCanonicalErrorPower

end

end OAI

end Source2066

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalErrorHomogeneous.lean; sha256: ec553406ca6a93433d9b8cf5b733012247ddb4e18bc5dadf589f162904978507 -/
section Source2067
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorHomogeneous
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

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

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_error_homogeneous
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
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(hcost:1≤cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
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
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
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
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|v0|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    CenteredMomentEnergyCanonicalErrorPower.actual_error_power_from_bands (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  have hlo:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N lower a hlower haPlain
  obtain ⟨Uprofile,Jheight,hweights⟩:=
    CenteredMomentEnergyFirstGaussianProfileWeights.actual_weights (a:=a) (b:=b)
      N upper (max 1 b) (max 1 b) ((max 1 Mslot)^N)
      (CenteredMomentSecondInputCapacitySource.lowerFactor N lower a)
      Cm Ce Cd Ct Cc cost εsrc δsrc θsrc Bcap J (dc+degree+4*n) (dc+degree+4*n)
      Sp T Sf CenteredMomentFirstAmplificationChoice.ballProfile
      (zero_le_one.trans hupper) (le_trans zero_le_one (le_max_left _ _))
      (le_trans zero_le_one (le_max_left _ _)) (by positivity) hlo
      hCm.le hCe hCd.le hCt.le hCc.le (zero_le_one.trans hcost)
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hwbound⟩:=hweights (internalQ Q η₀) Kc hKc.le
  refine ⟨Cbound,hCbound,Zi,hZi,?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  let Scols:=finiteColumns (Fintype.piFinset input.pools)
  let β:=coefficient input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β rfl rfl
  have hg:=hbound 1 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  have hz:0<Z:=zero_lt_one.trans (hZi.trans_le hZ)
  have hmass:mass src≤(max 1 Mslot)^N:=
    CenteredMomentEnergyOriginalProfileControl.slot_product_le src N (max 1 Mslot)
      (le_max_left _ _) hcard (fun i=>(hMs i).trans (le_max_right _ _))
  have hnseed:1≤(seed.absNorm:ℝ):=norm_ge_one seed hseed0
  have hh:=hwbound p Z v0 height (mass src) (seed.absNorm:ℝ) C₀ C₁
    hz hheight (mass_nonneg src) hmass hnseed hC₀ hC₁
  dsimp only at hh
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos input).le _)
  apply mul_le_mul_of_nonneg_right (hh j)
  fin_cases j <;> simp only [CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
    try unfold errorCommonRadius
  all_goals positivity

end SevenEighths.CenteredMomentEnergyCanonicalErrorHomogeneous

end

end OAI

end Source2067

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalErrorSubsets.lean; sha256: dbf4c767b78758ed4cdf73df208f4fcc414cde78aa77013e8793df3f07780270 -/
section Source2068
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorSubsets
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

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

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_original_subsets_error_power
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
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(hcost:1≤cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
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
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|v0|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  have hmain (Aorig:Finset α):=
    CenteredMomentEnergyCanonicalErrorHomogeneous.actual_error_homogeneous (α:=Aorig) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource (fun i=>lows i.val) (fun i=>highs i.val)
      (fun i=>hhighs i.val) εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  choose Uj Jj hj using hmain
  let Uprofile:Finset (ℕ×ℕ):=Finset.univ.biUnion Uj
  let Jheight:ℕ:=∑Aorig:Finset α,Jj Aorig
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  choose Cj hCj Zj hZj hconsume using fun Aorig=>hj Aorig η₀ Q hQM hQ0 hQt hQ72
  let Cbound:ℝ:=1+∑Aorig:Finset α,Cj Aorig
  let Z₀:ℝ:=2+∑Aorig:Finset α,|Zj Aorig|
  have hCbound:0<Cbound:=by
    have hh:=Finset.sum_nonneg (fun Aorig (_:Aorig∈(Finset.univ:Finset (Finset α)))=>(hCj Aorig).le)
    dsimp [Cbound];linarith
  have hZ₀:1<Z₀:=by
    have hh:=Finset.sum_nonneg (fun Aorig (_:Aorig∈(Finset.univ:Finset (Finset α)))=>abs_nonneg (Zj Aorig))
    dsimp [Z₀];linarith
  have hCC (Aorig:Finset α):Cj Aorig≤Cbound:=by
    have hh:=Finset.single_le_sum (fun A (_:A∈(Finset.univ:Finset (Finset α)))=>(hCj A).le)
      (Finset.mem_univ Aorig)
    dsimp [Cbound];linarith
  have hZZ (Aorig:Finset α):Zj Aorig≤Z₀:=by
    have hh:=Finset.single_le_sum (fun A (_:A∈(Finset.univ:Finset (Finset α)))=>abs_nonneg (Zj A))
      (Finset.mem_univ Aorig)
    dsimp [Z₀];linarith [le_abs_self (Zj Aorig)]
  refine ⟨Cbound,hCbound,Z₀,hZ₀,?_⟩
  intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  have hposA:=positiveAt_subtype M H hH Aorig Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hg:=hconsume Aorig θ Z ((hZZ Aorig).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hposA
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  have hsub:Uj Aorig⊆Uprofile:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨Aorig,Finset.mem_univ _,hx⟩
  have hp:p.control (Uj Aorig)≤p.control Uprofile:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hJ:Jj Aorig≤Jheight:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ Aorig)
  have hz:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hp0:=p.control_nonneg (Uj Aorig)
  have hp1:=p.control_nonneg Uprofile
  have hh:(1+|v0|+height)^(Jj Aorig)≤(1+|v0|+height)^Jheight:=
    pow_le_pow_right₀ (by linarith [abs_nonneg v0]) hJ
  have hfront:Cj Aorig*(C₀+C₁+1)*(p.control (Uj Aorig))^2*(1+|v0|+height)^(Jj Aorig)≤
      Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|v0|+height)^Jheight:=by
    have hc:=hCC Aorig
    have hc0:0≤Cj Aorig:=(hCj Aorig).le
    gcongr
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos _).le _)
  apply mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _))
  fin_cases j <;> simp only [CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
    try unfold errorCommonRadius
  all_goals positivity

end SevenEighths.CenteredMomentEnergyCanonicalErrorSubsets

end

end OAI

end Source2068

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalAmplifiedUniform.lean; sha256: d15d634e1f87b9698f46b4d77f3aec20a201f8ab805291002130d63da5f08769 -/
section Source2069
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform
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

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

lemma front_mono {a b:ℝ}(p:Profiles a b)(U V:Finset (ℕ×ℕ))(hUV:U⊆V)
    (J K:ℕ)(hJK:J≤K)(c d C₀ C₁ t height:ℝ)
    (hc:0≤c)(hcd:c≤d)(hC₀:0≤C₀)(hC₁:0≤C₁)(hh:0≤height):
    c*(C₀+C₁+1)*(p.control U)^2*(1+|t|+height)^J≤
      d*(C₀+C₁+1)*(p.control V)^2*(1+|t|+height)^K:=by
  have hp:p.control U≤p.control V:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hUV) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hUV) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hp0:=p.control_nonneg U
  have hp1:=p.control_nonneg V
  have ht:(1+|t|+height)^J≤(1+|t|+height)^K:=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJK
  have hd:0≤d:=hc.trans hcd
  gcongr

theorem actual_original_subsets_amplified_power
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
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(hcost:1≤cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
    (∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
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
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2) ∧
    (∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter),
    υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ t →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
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
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2) :=by
  obtain ⟨Um,Jm,hm⟩:=
    CenteredMomentEnergyCanonicalMainSubsets.actual_original_subsets_main_power (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  obtain ⟨Ue,Je,he⟩:=
    CenteredMomentEnergyCanonicalErrorSubsets.actual_original_subsets_error_power (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  refine ⟨Um∪Ue,max Jm Je,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cm,hCm,Zm,hZm,hmain⟩:=hm η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ce,hCe,Ze,hZe,herror⟩:=he η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cm+Ce,add_pos hCm hCe,max Zm Ze,lt_of_lt_of_le hZm (le_max_left _ _),?_,?_⟩
  ·
    intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
      hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
      hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
    dsimp only
    intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hg:=hmain Aorig θ Z ((le_max_left _ _).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
      hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hfront:=front_mono p Um (Um∪Ue) Finset.subset_union_left Jm (max Jm Je) (le_max_left _ _)
      Cm (Cm+Ce) C₀ C₁ t height hCm.le (le_add_of_nonneg_right hCe.le) hC₀ hC₁ hheight
    dsimp only at hg ⊢
    have hz:0<Z:=zero_lt_one.trans ((lt_of_lt_of_le hZm (le_max_left Zm Ze)).trans_le hZ)
    apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos _).le _)
    apply mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _))
    fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
      try unfold mainCommonRadius
    all_goals positivity
  ·
    intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
      hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
      hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ χerr hN hυ input hinput
    dsimp only
    intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hg:=herror Aorig θ Z ((le_max_right _ _).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ χerr t hN hυ input hinput
      hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hfront:=front_mono p Ue (Um∪Ue) Finset.subset_union_right Je (max Jm Je) (le_max_right _ _)
      Ce (Cm+Ce) C₀ C₁ t height hCe.le (le_add_of_nonneg_left hCm.le) hC₀ hC₁ hheight
    dsimp only at hg ⊢
    have hz:0<Z:=zero_lt_one.trans ((lt_of_lt_of_le hZm (le_max_left Zm Ze)).trans_le hZ)
    apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos _).le _)
    apply mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _))
    fin_cases j <;> simp only [CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
      try unfold errorCommonRadius
    all_goals positivity

end SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform

end

end OAI

end Source2069

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstAnnularAdmission.lean; sha256: d3fe2185d0cb1af186ce293f043274bb29f2f137d25b76c7403d8a2373025b6c -/
section Source2070
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

universe u
namespace SevenEighths.CenteredMomentEnergyFirstAnnularAdmission
open HeckeFamily ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstPhysicalLedger CenteredMomentFirstExtractedLedger
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
lemma source_dyad_retained (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    Retained (localRadius s R seed K Z ξ p E) (n 1):=by
  have hn: (n 1:ℤ)∈retainedIndices (localRadius s R seed K Z ξ p E):=(n 1).property
  exact ((mem_retainedIndices _ _).mp hn).1

omit [DecidableEq ι] in
lemma source_dyad_gt_one (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):1<dyadicScale (n 1):=by
  have hn: (n 1:ℤ)∈retainedIndices (localRadius s R seed K Z ξ p E):=(n 1).property
  obtain ⟨q,hq,hweight⟩:=((mem_retainedIndices _ _).mp hn).2
  exact hq.trans_lt ((dyadicWeight_support (n 1)) hweight).2

omit [DecidableEq ι] in
lemma source_nominal_positive (s:Input ι)(R seed:Ideal O)(K:ℝ)(hK:0<K)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
    0<firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData):=by
  have he:=Ideal.span_singleton_eq_bot.not.mpr
    (primeSubsetGenerator_ne_zero (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)
  have hE:(∏P∈E,P.val)≠(0:Ideal O):=by
    simpa only [primeSubsetGenerator,span_idealGenerator,Ideal.zero_eq_bot] using he
  exact firstNominalScale_pos _ _ _ hE K _ hK (volume_pos s.toData)

omit [DecidableEq ι] in
lemma source_nominal_span (s:Input ι)(R seed:Ideal O)(K:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
    firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)=
      firstNominalScale p.val.1 p.val.2
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E})
        K (volume s.toData):=by rw [primeSubsetGenerator,span_idealGenerator]

def amplifierCap (A D ξcap:ℝ):ℝ:=3*max A D+ξcap/2+1

omit [DecidableEq ι] in
theorem source_amplifier_packet (A D ξcap Z:ℝ)(hZ:32≤Z)
    (s:Input ι)(R seed:Ideal O)(K ξ:ℝ)(hK:0<K)(hξ:ξ≤ξcap)
    (hV:volume s.toData≤Z^A)(hKi:K⁻¹≤Z^D)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    let Tsec:=firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData);
    0<Tsec ∧ 0<dyadicScale (n 1) ∧
      dyadicScale (n 1)≤4*frequencyRadius Tsec Z ξ ∧
      8*dyadicScale (n 1)≤Z^(amplifierCap A D ξcap) ∧
      Tsec≤1*firstNominalScale p.val.1 p.val.2
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E})
        K (volume s.toData):=by
  have hz:1≤Z:=by linarith
  have hzpos:0<Z:=by linarith
  have hfreq:=retained_scale_le _ (n 1) (source_dyad_retained s R seed K Z ξ p E n)
  have hV':volume s.toData≤Z^(max A D):=hV.trans
    (Real.rpow_le_rpow_of_exponent_le hz (le_max_left _ _))
  have hKi':K⁻¹≤Z^(max A D):=hKi.trans
    (Real.rpow_le_rpow_of_exponent_le hz (le_max_right _ _))
  have hrad:=local_frequency_radius_cap p.val.1 p.val.2 E K (volume s.toData) Z
    (max A D) ξ hK (volume_pos s.toData).le hz hV' hKi'
  have hrad':localRadius s R seed K Z ξ p E≤Z^(3*max A D+ξcap/2):=by
    apply hrad.trans
    exact Real.rpow_le_rpow_of_exponent_le hz (by linarith)
  refine ⟨source_nominal_positive s R seed K hK p E,dyadicScale_pos _,hfreq,?_,?_⟩
  · calc
      _≤32*Z^(3*max A D+ξcap/2):=by linarith
      _≤Z*Z^(3*max A D+ξcap/2):=
        mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hzpos.le _)
      _=Z^(amplifierCap A D ξcap):=by
        unfold amplifierCap
        rw [Real.rpow_add_one hzpos.ne']
        ring
  · rw [one_mul]
    exact (source_nominal_span s R seed K p E).le

omit [DecidableEq ι] in
lemma source_frequency_ledger (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)(hK:0<K)(hZ:1<Z)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    Real.logb Z (dyadicScale (n 1))≤
      Real.logb Z (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData))+
        frequencyLoss Z 1 ξ:=by
  apply retained_first_dyad_enclosure _ Z 1 _ ξ hZ (by norm_num) _ (n 1)
    (source_dyad_retained s R seed K Z ξ p E n)
  rw [one_mul,Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (source_nominal_positive s R seed K hK p E)]

theorem fixed_endpoint_radius (N:ℕ)(upper b₁ b₂ A Z:ℝ)
    (hu:1≤upper)(hb₁:0≤b₁)(hb₂:0≤b₂)(hZ:32≤Z)
    (hfixed:upper^N*b₁*b₂≤Z)
    (s:Input ι)(hN:Fintype.card ι≤N)
    (hhi:∀i,|s.hi i|≤upper)(hs₁:|s.b₁|≤b₁)(hs₂:|s.b₂|≤b₂)
    (hV:volume s.toData≤Z^A):sourceRadius s≤Z^(A+1):=by
  apply input_radius_cap (fun _:ι=>upper) b₁ b₂ A Z s hhi hs₁ hs₂ (by linarith) _ hV
  have hpow:upper^(Fintype.card ι)≤upper^N:=pow_le_pow_right₀ hu hN
  simpa only [Finset.prod_const,Finset.card_univ] using
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hb₁) hb₂).trans hfixed

theorem eventually_source_admission (N:ℕ)(upper b₁ b₂ A D ξcap:ℝ)
    (hu:1≤upper)(hb₁:0≤b₁)(hb₂:0≤b₂):
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(α:Type u)[Fintype α][DecidableEq α],∀s:Input α,Fintype.card α≤N →
      (∀i,|s.hi i|≤upper) → |s.b₁|≤b₁ → |s.b₂|≤b₂ →
      ∀(R seed:Ideal O)(K ξ:ℝ),0<K → ξ≤ξcap →
      volume s.toData≤Z^A → K⁻¹≤Z^D →
      sourceRadius s≤Z^(A+1) ∧
      ∀(p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
        (n:SourceBlocks s R seed K Z ξ p E),
      let Tsec:=firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData);
      0<Tsec ∧ 1<dyadicScale (n 1) ∧
        dyadicScale (n 1)≤4*frequencyRadius Tsec Z ξ ∧
        8*dyadicScale (n 1)≤Z^(amplifierCap A D ξcap) ∧
        Tsec≤1*firstNominalScale p.val.1 p.val.2
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E})
          K (volume s.toData):=by
  filter_upwards [eventually_ge_atTop (32:ℝ),eventually_ge_atTop (upper^N*b₁*b₂)] with Z hZ hf
  refine ⟨by linarith,?_⟩
  intro α _ _ s hN hhi hs₁ hs₂ R seed K ξ hK hξ hV hKi
  refine ⟨fixed_endpoint_radius N upper b₁ b₂ A Z hu hb₁ hb₂ hZ hf s hN hhi hs₁ hs₂ hV,?_⟩
  intro p E n
  have hh:=source_amplifier_packet A D ξcap Z hZ s R seed K ξ hK hξ hV hKi p E n
  exact ⟨hh.1,source_dyad_gt_one s R seed K Z ξ p E n,hh.2.2⟩

end SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

end

end OAI

end Source2070

/- Original source: OAI/NumberTheory/DirichletL/Energy/AmplifierFamilyAdmission.lean; sha256: 72cf1a31d21fbf2a6852cf0938843e6779a0f53e0fd736fc7095a68fc5d6c408 -/
section Source2071
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ActualEisensteinCubic
open CenteredMomentFirstSourceConductorCaps CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSectorLocalization CenteredMomentFirstAmplifiedFourCoefficients
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

def referenceCost : ℝ := max 1 rayCost

lemma referenceCost_ge_one : 1≤referenceCost := le_max_left _ _

theorem actual_error_reference_cap (ρ υ:Character)(χ:RayFourExpansion.RayCharacter)
    (p:O)(hp:p≠0)(n:ℕ)(hn:n=0 ∨ n=5 ∨ n=6)(Z:ℝ)(hZ:1<Z)
    (hυ:υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p
      (errorMovingExponent n)):
    (υ.modulus.absNorm:ℝ)≤referenceCost*(ρ.modulus.absNorm:ℝ)*
      Z^(errorMoving p Z (n+1)):=by
  have hray:=CenteredMomentSecondRadicalBudget.child_modulus_bound ρ χ
  have hN:(υ.modulus.absNorm:ℝ)≤
      ((childCharacter ρ χ).modulus.absNorm:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*Z^(errorMoving p Z (n+1)):=by
    rw [←radicalBound_error_power (childCharacter ρ χ) fixedBadMask p hp Z hZ n hn]
    exact_mod_cast hυ
  have hr:((childCharacter ρ χ).modulus.absNorm:ℝ)≤
      (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm:=by exact_mod_cast hray
  calc
    _≤((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
        Z^(errorMoving p Z (n+1)):=by apply hN.trans;gcongr
    _=rayCost*(ρ.modulus.absNorm:ℝ)*Z^(errorMoving p Z (n+1)):=by
      unfold rayCost fixedPresentationCost;ring
    _≤_:=by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      exact mul_le_mul_of_nonneg_right (le_max_right 1 rayCost) (Nat.cast_nonneg _)

end SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

end

end OAI

end Source2071

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstRawScaleAdmission.lean; sha256: ce750ee0a5d87968fca4bdc9ec52a4fd73de905ccc28c29cb686c5a7a20dc5e1 -/
section Source2072
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentEnergyAmplifiedRayDictionary CenteredMomentFirstAnnularInput
open CenteredMomentFirstChildLower CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α]
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

def parentLower (s:Input α)(Z:ℝ):ℝ:=
  min (min (Real.logb Z s.X₁) (Real.logb Z s.X₂))
    (min (Real.logb Z s.Y₁) (Real.logb Z s.Y₂))

theorem parent_lower_scales (s:Input α)(Z:ℝ)(hZ:1<Z):
    Z^(parentLower s Z)≤s.X₁ ∧ Z^(parentLower s Z)≤s.X₂ ∧
    Z^(parentLower s Z)≤s.Y₁ ∧ Z^(parentLower s Z)≤s.Y₂:=by
  have h (X:ℝ)(hX:0<X)(hx:parentLower s Z≤Real.logb Z X):Z^(parentLower s Z)≤X:=by
    calc
      _≤Z^(Real.logb Z X):=Real.rpow_le_rpow_of_exponent_le hZ.le hx
      _=X:=Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX
  exact ⟨h _ s.X₁_pos ((min_le_left _ _).trans (min_le_left _ _)),
    h _ s.X₂_pos ((min_le_left _ _).trans (min_le_right _ _)),
    h _ s.Y₁_pos ((min_le_right _ _).trans (min_le_left _ _)),
    h _ s.Y₂_pos ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem main_minimum_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t Z:ℝ)(hZ:1<Z):
    let d:=child s C R B τ t
    let r:=parentLower s Z-Real.logb Z (C.absNorm:ℝ)
    Z^r≤d.X₁ ∧ Z^r≤d.X₂ ∧ Z^r≤d.Y₁ ∧ Z^r≤d.Y₂:=by
  have h:=parent_lower_scales s Z hZ
  exact child_lower s C R hC B τ t Z (parentLower s Z) hZ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem active_error_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:Character)(v Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=child (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C) Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  have hc:=child_lower s C R hC B τ t Z r hZ hX₁ hX₂ hY₁ hY₂
  have hpn:(Ideal.span {p}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr hp
  have hh:=child_lower (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C)
    (pow_ne_zero k hpn) Bp υ v Z (r-Real.logb Z (C.absNorm:ℝ)) hZ
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have he:Real.logb Z (((Ideal.span {p}:Ideal O)^k).absNorm:ℝ)=errorRemoval p Z k:=by
    rw [map_pow,Nat.cast_pow,Real.logb_pow]
    rfl
  simpa only [he] using hh

theorem restored_error_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:Character)(v Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=restoredError s C R B τ t (Ideal.span {p}) k Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  exact active_error_lower s C R hC B τ t p hp k Bp υ v Z r hZ hX₁ hX₂ hY₁ hY₂

theorem error_minimum_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:Character)(v Z:ℝ)(hZ:1<Z):
    let d:=child (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C) Bp υ v
    let r':=parentLower s Z-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  have h:=parent_lower_scales s Z hZ
  exact active_error_lower s C R hC B τ t p hp k Bp υ v Z (parentLower s Z) hZ
    h.1 h.2.1 h.2.2.1 h.2.2.2

end SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission

end

end OAI

end Source2072

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalAnnularPower.lean; sha256: df7f331776464f7f29a2cd3c267344230259925663be4f471887ac6a319bf5e5 -/
section Source2073
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalAnnularPower
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

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentEnergyCanonicalAmplifiedUniform CenteredMomentEnergyAmplifierFamilyAdmission
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission
open CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

theorem actual_original_subsets_annular_power
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
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(_hξ1:ξ≤1)(hreserve:0<reserve):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3));
    P.Nonempty ∧ Z^(sigma/3-primeLoss)≤(P.card:ℝ) ∧
    ∀τ:Character,∃υ:(Aorig:Finset α)→(Ac:Finset Aorig)→elementPool P→Fin 3→RayCharacter→Character,
    (∀Aorig Ac prime i χ,(υ Aorig Ac prime i χ).modulus.absNorm≤
      radicalBound (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime.val
        (errorMovingExponent (errorIndex i))) ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → (C.absNorm:ℝ)≤Z^(A+1) →
    ∀E:Finset (CommonIndex C D),
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K H0:ℝ,0<K → 0<H0 →
    H0≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)) Z ξ →
    8*H0≤Z^(amplifierCap A 0 ξ) →
    ∀(B:actualAllocations src.pools C)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Ready (child src C R0 B τ t) (R0*C)
      (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve) Z ξ (readyBudget A Pcap) →
    (∀prime:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      let d:=errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t;
      (∀I:Ideal O,coefficient d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1)) seed I=0) ∨
      Ready d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
        (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve prime (errorIndex i+1))
        Z ξ (readyBudget A Pcap)) →
    let input:=child src C R0 B τ t;
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let rmain:=parentLower src Z-Real.logb Z (C.absNorm:ℝ);
    let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve;
    let Hcoef:=fun j=>Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
      Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ);
    let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j;
    let aerror:=fun (prime:elementPool P)(i:Fin 3)(_χ:RayCharacter)(j:Fin 4)=>
      Hcoef j*errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
        (errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1))
        deficit paid saving (rmain-errorRemoval prime Z (errorIndex i+1)) j;
    childNormalizedGaussSource src C R0 seed B τ t CenteredMomentFirstAnnularMajorant.profile
      H0≤
      (∑j,sourceCoefficients P ((amplifierCap A 0 ξ+2*sigma)/(sigma/6)) amain aerror (powers εsrc) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  let Bcap:=readyBudget A Pcap
  have hBcap:0≤Bcap:=readyBudget_nonneg A Pcap hA hPcap
  have hAmp:0≤amplifierCap A 0 ξ:=by unfold amplifierCap;positivity
  obtain ⟨U,J,huniform⟩:=actual_original_subsets_amplified_power (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ sigma referenceCost hsigma hξsmall referenceCost_ge_one
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,Zbase,hZbase,hm,he⟩:=huniform η₀ Q hQM hQ0 hQt hQ72
  have hall:=Filter.eventually_all.mpr (fun Aorig:Finset α=>
    eventually_original_subsets_power_amplification (Ω:=Aorig) M H hH fixedBadPrimes (Finset.Subset.refl _)
      sigma primeLoss (Pcap+A+1) Bseed (amplifierCap A 0 ξ) (max 1 bslot) eta 1 ξ reserve
      hsigma hPrimeLoss hAmp (by positivity) heta (by norm_num) hξ.le hreserve)
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss hAmp heta
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.mp
    (hall.and (hsepEvent.and (eventually_ge_atTop Zbase)))
  refine ⟨Cbound,hCbound,max Z₀ Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Z hZthreshold
  obtain ⟨hamp,hsepdata,hZZbase⟩:=
    hZ₀ Z ((le_max_left _ _).trans hZthreshold)
  have hZ:1<Z:=hZbase.trans_le hZZbase
  dsimp only
  have hbase:=hamp (∅:Finset α)
  refine ⟨hbase.2.1,hbase.2.2.1,?_⟩
  intro τ
  have hf (Aorig:Finset α):=(hamp Aorig).2.2.2 τ
  choose υ hυN henergy using hf
  refine ⟨υ,hυN,?_⟩
  intro Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC
    E hmod K H0 hK hH0 houter hHcap B t hB seed hseed hseedne hseedcap
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth
    hdrop hclip hsourceLower hreadym herrorPacket
  let input:=child src C R0 B τ t
  let delta:=frequencyLoss Z 32 ξ
  have hdelta:0≤delta:=frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ.le
  have hRC:(R0*C).absNorm=R0.absNorm*C.absNorm:=map_mul _ _ _
  have hRcommon:( (R0*C).absNorm:ℝ)≤Z^(Pcap+A+1):=by
    rw [hRC,Nat.cast_mul]
    calc
      _≤Z^Pcap*Z^(A+1):=mul_le_mul hRcap hNC (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _)
      _=Z^(Pcap+A+1):=by rw [←Real.rpow_add (by linarith:0<Z)];congr 1;ring
  have hmainlower:=main_minimum_lower src C R0 hC.1 B τ t Z hZ
  have hmain:=hm Aorig θ Z hZZbase εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve a0 hK ha0 hdelta hreserve.le le_rfl
    hreadym seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower _
    hmainlower.1 hmainlower.2.1 hmainlower.2.2.1 hmainlower.2.2.2
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let rmain:=parentLower src Z-Real.logb Z (C.absNorm:ℝ)
  let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve
  let Hcoef:=fun j=>Cbound*(C₀+C₁+1)*(p.control U)^2*(1+|t|+height)^J*
    Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ)
  let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j
  let aerror:=fun (prime:elementPool (primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))))
    (i:Fin 3)(χ:RayCharacter)(j:Fin 4)=>Hcoef j*
      errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1))
      deficit paid saving (rmain-errorRemoval prime Z (errorIndex i+1)) j
  have hHcoef:∀j,0≤Hcoef j:=by intro j;dsimp [Hcoef];positivity
  have haerror:∀prime i χ j,0≤aerror prime i χ j:=by
    intro prime i χ j
    apply mul_nonneg (hHcoef j)
    fin_cases j <;> simp only [errorPowers,Matrix.cons_val,Fin.reduceFinMk]
    all_goals try unfold errorRadius errorCommonRadius
    all_goals positivity
  have hsupp:∀i,Function.support (input.W i)⊆Set.Iic (max 1 bslot):=by
    intro i x hx
    exact ((src.support i.val hx).2.trans (hhi i.val)).trans (le_max_right _ _)
  let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun i=>w i.val
  have hz:∀i,z i≤eta:=fun i=>hweta i.val
  have hlen:∀i,input.P i=Z^(z i):=fun i=>hmatch.scale i.val
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hsepdata
  have herror:∀prime:elementPool (primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))),
      ∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput input).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      childNormalizedGaussSource (activeInput input) ((Ideal.span {prime.val})^(errorIndex i+1))
        (R0*C) seed Bp (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t
        CenteredMomentFirstAmplificationChoice.ballProfile
        (errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1))≤
      (∑j,aerror prime i χ j*(volume (child (activeInput input)
        ((Ideal.span {prime.val})^(errorIndex i+1)) (R0*C) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t))^(powers εsrc j))*
        mass (child (activeInput input) ((Ideal.span {prime.val})^(errorIndex i+1)) (R0*C) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t)^2:=by
    intro prime i χ Bp
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) prime.val prime.property
    have hprime:prime.val≠0:=hd.1.ne_zero
    have hcop:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact CenteredMomentFirstAmplificationChoice.original_slot_coprime (original input (R0*C) seed).active
        Z sigma (max 1 bslot) eta hZ.le (by positivity) hsep z hz hlen hsupp
        (original input (R0*C) seed).active_slot
        (fun j Q hQ=>input.prime j Q ((original input (R0*C) seed).active_subset _ hQ))
        _ (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hk:=CenteredMomentFirstAmplificationChoice.errorIndex_cases i
    have hk':errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by omega
    have hN:=hυN Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have hvcap:=actual_error_reference_cap τ _ χ prime.val hprime (errorIndex i) hk Z hZ hN
    have hre:=herrorPacket prime i χ Bp
    rcases hre with hdead|hlive
    · change normalizedGaussSource _ _ _ _ _≤_
      apply (CenteredMomentFirstSecondInputGates.normalized_zero _ _ _ hdead _ _).le.trans
      exact mul_nonneg (Finset.sum_nonneg (fun j _=>mul_nonneg (haerror prime i χ j)
        (Real.rpow_nonneg (volume_pos _).le _))) (sq_nonneg _)
    · have hlower:=error_minimum_lower src C R0 hC.1 B τ t prime.val hprime
        (errorIndex i+1) Bp (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t Z hZ
      have hprimeScale: sigma/6≤Real.logb Z (normValue prime.val):=by
        have hh:=Real.logb_le_logb_of_le hZ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/6)) (hdata _ hd.2.1).2.2.1
        simpa only [normValue,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
      have hh:=he Aorig θ Z hZZbase εchild C₀ C₁ hC₀ hC₁ hzero hpos
        w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
        hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
        K delta reserve a0 hK ha0 hdelta hreserve.le le_rfl
        prime.val hprime (errorIndex i) hk hprimeScale hcop Bp _ χ hN hvcap _ rfl
        hlive seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
        hcap hMdecl hMwidth hdrop hclip hsourceLower _
        hlower.1 hlower.2.1 hlower.2.2.1 hlower.2.2.2
      exact hh
  have hE:Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}≠0:=
    Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
  have hann:=henergy Aorig (CenteredMomentCommonProfile.liveIndices B.val) input rfl hsupp z hz hlen
    (R0*C) seed (mul_ne_zero hR0 hC.1) hseedne hRcommon hseedcap
    (Real.logb Z (D.absNorm:ℝ)) (Real.logb Z (C.absNorm:ℝ)) C D
    (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hE K (volume src) _
    hK (volume_pos src) (by simp only [one_mul];exact le_rfl) H0 hH0 houter hHcap
    amain aerror (powers εsrc) haerror (by simpa only [mul_one,nominalLog,input,amain,Hcoef,Kmain,mainRadius,paid,deficit,rmain,delta] using hmain)
    (by simpa only [mul_one,nominalLog,errorRadius,delta] using herror)
  apply hann.trans_eq
  rw [source_coefficients_identity _ _ _ (volume_pos input).le]
  dsimp only [normValue]
  ring

end SevenEighths.CenteredMomentEnergyCanonicalAnnularPower

end

end OAI

end Source2073

/- Original source: OAI/NumberTheory/DirichletL/Energy/CanonicalAmplifiedColumn.lean; sha256: 4c9fa0fb1570441418dc5222eaa0c89b0bf6120b9fabcbe6525e3bbf6320e1e1 -/
section Source2074
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentFirstPhysicalSource CenteredMomentCommonAllocationSum
open CenteredMomentFirstCommonReferencePower CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentPrimeElements CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentSecondChildPowerBudget
open CenteredMomentSourceLiveColumn
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma main_coefficients_nonneg (q Z K ell deficit paid saving r:ℝ)
    (hq:0≤q)(hZ:0≤Z)(hK:0≤K):∀j,0≤mainPowers q Z K ell deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;> positivity

lemma error_coefficients_nonneg (p:O)(k:ℕ)(q Z K deficit paid saving r:ℝ)
    (hq:0≤q)(hZ:0≤Z)(hK:0≤K):∀j,0≤errorPowers p k q Z K deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;> positivity

theorem common_annular_reference_powers (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N→a≤s.lower→s.upper≤b→
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C→
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(H0 Z allowance:ℝ),0<H0→0<Z→
    ∀(P:Finset (Ideal O))(mainFactor:ℝ)(H:Fin 4→ℝ),0≤mainFactor→(∀j,0≤H j)→
    ∀(Kmain ell deficit paid saving rmain:ℝ),0≤Kmain→
    ∀(Kerror rerror:elementPool P→Fin 3→Ray→ℝ),(∀p i χ,0≤Kerror p i χ)→
    let q:ℝ:=τ.modulus.absNorm;
    let amain:=fun j=>H j*mainPowers q Z Kmain ell deficit paid saving rmain j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) q Z (Kerror p i χ) deficit paid saving (rerror p i χ) j;
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0→
      childNormalizedGaussSource s C R L B τ t CenteredMomentFirstAnnularMajorant.profile H0≤
        (∑j,sourceCoefficients P mainFactor amain aerror (powers ε) j*
          (volume (child s C R B τ t))^(powers ε j))*
          CenteredMomentFirstChildProfileControl.mass (child s C R B τ t)^2)→
    (commonEnergy (original s R seed) C hC τ t L CenteredMomentFirstAnnularMajorant.profile H0).re≤
      reference q (volume s) (C.absNorm:ℝ) Z allowance*
        (Cb*CenteredMomentFirstChildProfileControl.mass s^2*
          ∑j,(C.absNorm:ℝ)^ε*(b^N)^(powers ε j)*
            averagedCoefficients P mainFactor H
              (mainCores q (volume s) (C.absNorm:ℝ) Z allowance Kmain ell deficit paid ε saving rmain)
              (fun p i χ=>errorCores p (errorIndex i+1) q (volume s) (C.absNorm:ℝ)
                Z allowance (Kerror p i χ) deficit paid ε saving (rerror p i χ)) j):=by
  obtain ⟨Cb,hCb,hbound⟩:=common_energy_reference_powers N a b ε ha hb hε
  refine ⟨Cb,hCb,?_⟩
  intro ι _ s hc hlo hhi C R seed hC hseed τ t L H0 Z allowance hH0 hZ
    P mainFactor H hmain hH Kmain ell deficit paid saving rmain hKmain Kerror rerror hKerror
  dsimp only
  intro hchildren
  have hq:0<(τ.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
  have hNC:0<(C.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ hC.1
  have hcoeff:=source_coefficients_nonneg P mainFactor hmain
    (fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain ell deficit paid saving rmain j)
    (fun p i χ j=>H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (Kerror p i χ) deficit paid saving (rerror p i χ) j) (powers ε)
    (fun j=>mul_nonneg (hH j) (main_coefficients_nonneg _ _ _ _ _ _ _ _ hq.le hZ.le hKmain j))
    (fun p i χ j=>mul_nonneg (hH j) (error_coefficients_nonneg _ _ _ _ _ _ _ _ _
      hq.le hZ.le (hKerror p i χ) j))
  have hh:=hbound s hc hlo hhi C R seed hC hseed τ t L
    CenteredMomentFirstAnnularMajorant.profile H0 Z allowance hH0 hZ
    (fun z=>CenteredMomentFirstAnnularMajorant.profile_nonneg _) 4 _ (powers ε)
    hcoeff (powers_nonneg ε hε.le) hchildren
  apply hh.trans_eq
  unfold reference
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  exact actual_power_reference_identity P mainFactor b (volume s) (C.absNorm:ℝ)
    (τ.modulus.absNorm:ℝ) Z allowance ε N H Kmain ell deficit paid saving rmain Kerror rerror
    (volume_pos s) hNC hq hZ j

end SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

end

end OAI

end Source2074

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstHighExceptionalPowers.lean; sha256: 5df9067a2160c6b1ed5072998c0df2c8dedc83410d6ad41526cff9315d943a79 -/
section Source2075
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstHighExceptionalPowers
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

theorem actual_main_exceptional_uniform_cap (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve Mdecl : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hK:0<K)(hX:0<X)
    (hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl) :
    ((X/(I.absNorm:ℝ))*(X/(I.absNorm:ℝ))^((1:ℝ)/3)*(mainCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve)^((5:ℝ)/6)*Z^(-sigma/3)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)) 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+4*sigma/3+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)) 0 := le_max_right _ _
  have hrLower:=le_max_left (Mdecl/4-Real.logb Z (I.absNorm:ℝ)) (0:ℝ)
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
    (Real.rpow_nonneg hz.le (-2*max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)) 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

theorem actual_error_exceptional_uniform_cap (η τ : Character)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hIJ:primeSupport I=primeSupport J)
    (A : Finset (CommonIndex I J)) (hE:E=Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A})
    (K X Z j sigma delta reserve Mdecl : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hK:0<K)(hX:0<X)
    (hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl) :
    ((X/(I.absNorm:ℝ))*localErrorCost p0 (k-1)*(X/(I.absNorm:ℝ)/(normValue p0)^k)^((1:ℝ)/3)*(errorCommonRadius Z (Real.logb Z (J.absNorm:ℝ)) (nominalLog I J E K X Z) (Real.logb Z (I.absNorm:ℝ)) sigma delta reserve p0 k)^((5:ℝ)/6)/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*Z^(allowance I J Z)))*Z^(-2*max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k) 0/3)≤
      Z^(Real.logb Z X-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+3*sigma/2+5*(delta+reserve)/6):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hf:=fixed_presentation_log_nonneg Z hZ
  have hr : 0 ≤ max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k) 0 := le_max_right _ _
  have hrLower:=le_max_left (Mdecl/4-Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k) (0:ℝ)
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
    (Real.rpow_nonneg hz.le (-2*max (Mdecl/4-Real.logb Z (I.absNorm:ℝ)-errorRemoval p0 Z k) 0/3))
  apply hmul.trans
  rw [←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  simp only [nominalLog] at hs ⊢
  linarith

end SevenEighths.CenteredMomentEnergyFirstHighExceptionalPowers

end

end OAI

end Source2075

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstHighFourCoefficients.lean; sha256: 950d2cd9cfdaa03b9a1309ffb3712aec787d32233d15becc777214c7da765872 -/
section Source2076
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstHighFourCoefficients
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

open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentEnergyFirstHighExceptionalPowers

theorem actual_main_high_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0≤sigma)(heps:0≤eps)(_hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth)(hwidth:Mwidth≤Mdecl)
    (hlow:Real.logb Z V≤Mdecl)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    ∀j:Fin 4,Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kmain (sigma/3) (Mdecl-M0) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j≤
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
      (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ))
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector,neg_div] using hh
  · have hh:=actual_main_exceptional_uniform_cap η τ C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve Mwidth hZ hmod hK hV hactual
    have ht:Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) 1≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
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
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) 2:=by
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
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) 3≤
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

theorem actual_error_high_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0≤sigma)(heps:0≤eps)(_hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth)(hwidth:Mwidth≤Mdecl)
    (hlow:Real.logb Z V≤Mdecl)
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
      (allowance C D Z) Kerror (Mdecl-M0) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k) j≤
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
      (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k)
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector] using hh
  · have hh:=actual_error_exceptional_uniform_cap η τ C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve Mwidth hZ hmod M H Sbad hbad p hp k hk hK hV hactual
    have ht:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k) 1≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
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
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k) 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          sigma+delta+reserve)*Z^(-saving):=by
      convert ht using 1 ; dsimp [errorCores,reference] ; ring
    apply hcore.trans
    rw [←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith

theorem actual_high_four_coefficients
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth)(hwidth:Mwidth≤Mdecl)
    (hlow:Real.logb Z V≤Mdecl)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (H:Fin 4→ℝ)(hH:∀j,0≤H j):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let main:=mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-M0) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ));
    let error:=fun (p:elementPool P) (i:Fin 3) (_χ:Ray)=>
      errorCores p (errorIndex i+1) (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
        (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ))
          sigma delta reserve p (errorIndex i+1)) (Mdecl-M0) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1));
    ∀j,averagedCoefficients P ((Mamp+2*sigma)/(sigma/6)) H main error j≤
      56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
        Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hne:(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).Nonempty:=by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.rpow_pos_of_pos hz (sigma/3-primeLoss)).trans_le hcard
  have hmain:=actual_main_high_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
    Mdecl Mwidth Mcap hK hV hZ hs.le heps hM hcap hactual hwidth hlow hmod
  have herror:=fun (p:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))))
      (i:Fin 3) (χ:Ray)=>
    actual_error_high_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
      Mdecl Mwidth Mcap hK hV hZ hs.le heps hM hcap hactual hwidth hlow hmod
      M Hray Sbad hbad p p.property (errorIndex i+1)
      (by fin_cases i <;> norm_num [errorIndex])
  exact averaged_coefficients_bound _ hne
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).2)
    Z (sigma/3) primeLoss ((Mamp+2*sigma)/(sigma/6)) hZ hloss
    (div_nonneg (by linarith) (by positivity)) hcard H _ _ _ hH
    (by simpa only [neg_div] using hmain) herror

end SevenEighths.CenteredMomentEnergyFirstHighFourCoefficients

end

end OAI

end Source2076

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstHighNormalizedGaussianPowers.lean; sha256: 7a3a57c4d6f0c261710db17bbaffbf8e64e9036cb0c4ca3a58d9c45263488804 -/
section Source2077
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstHighNormalizedGaussianPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

open CenteredMomentEnergyFirstHighFourCoefficients

theorem actual_high_normalized_four_powers
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth)(hwidth:Mwidth≤Mdecl)
    (hlow:Real.logb Z V≤Mdecl)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:0≤upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤H j):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1)) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (C.absNorm:ℝ)^eps*∑j:Fin 4,(upper^N)^(alpha j)*
        (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
          Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss)) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hz:=zero_lt_one.trans hZ
  have hn:=actual_power_reference_identity
    (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))) ((Mamp+2*sigma)/(sigma/6))
    upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z (allowance C D Z) eps N H
    (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
    (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ))
    (fun p i χ=>errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1))
    (fun p i χ=>Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1)) hV hc hq hz
  have hav:=actual_high_four_coefficients M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hwidth hlow hloss hMamp hcard hmod H hH
  dsimp only at hn hav
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [hn j]
  have hpos:0≤(C.absNorm:ℝ)^eps*(upper^N)^(CenteredMomentSecondChildPowerBudget.powers eps j):=by positivity
  exact (mul_le_mul_of_nonneg_left (hav j) hpos).trans_eq (by ring)

end SevenEighths.CenteredMomentEnergyFirstHighNormalizedGaussianPowers

end

end OAI

end Source2077

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstHighGaussianUniformPowers.lean; sha256: 281b08c35cf507151f70003c414b3cfcdf0ccf145cc0f24e125fad23c7e03d2c -/
section Source2078
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentSecondChildPowerBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

lemma finite_power_budget (upper nc Z eps Bcommon deficit primeLoss G F seed:ℝ)
    (N:ℕ)(hupper:1≤upper)(hnc:0≤nc)(hZ:1<Z)(heps:0≤eps)(heps1:eps≤1)
    (hncap:nc≤Z^Bcommon)(hG:0≤G)(_hF:0≤F)(_hseed:0<seed)
    (H srcLoss actualLoss:Fin 4→ℝ)(hH:∀j,0≤H j)
    (hbound:∀j,H j≤F*Z^(srcLoss j)/seed):
    nc^eps*(∑j:Fin 4,(upper^N)^(powers eps j)*
      (G*H j*Z^(deficit+actualLoss j+primeLoss)))≤
      (upper^N*G*F/seed)*Z^(deficit+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+actualLoss j):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hncPow:nc^eps≤Z^(eps*Bcommon):=by
    have hh:=Real.rpow_le_rpow hnc hncap heps
    simpa only [←Real.rpow_mul hz.le,mul_comm Bcommon eps] using hh
  have hu:1≤upper^N:=one_le_pow₀ hupper
  have hup (j:Fin 4):(upper^N)^(powers eps j)≤upper^N:=by
    have hp:powers eps j≤1:=by fin_cases j <;> simp [powers] <;> linarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hu hp
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj0:=hH j
  have hu0:0≤upper:=zero_le_one.trans hupper
  calc
    _≤Z^(eps*Bcommon)*(upper^N*(G*(F*Z^(srcLoss j)/seed)*Z^(deficit+actualLoss j+primeLoss))):=by
      apply mul_le_mul hncPow _ (by positivity) (by positivity)
      apply mul_le_mul (hup j) _ (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left (hbound j) hG
    _=(upper^N*G*F/seed)*Z^(deficit+eps*Bcommon+primeLoss)*Z^(srcLoss j+actualLoss j):=by
      calc
        _=(upper^N*G*F/seed)*(Z^(eps*Bcommon)*Z^(srcLoss j)*Z^(deficit+actualLoss j+primeLoss)):=by ring
        _=_:=by
          rw [←Real.rpow_add hz, ←Real.rpow_add hz]
          rw [show eps*Bcommon + srcLoss j + (deficit+actualLoss j+primeLoss) =
            (deficit+eps*Bcommon+primeLoss)+(srcLoss j+actualLoss j) by ring,
            Real.rpow_add hz]
          ring

theorem actual_high_uniform_four_powers {a b:ℝ}
    (N:ℕ)(upper b1 b2 Amax loFloor:ℝ)
    (Cm Ce Cd Ct Cc cost epsilon deltaSource thetaSource Bcap:ℝ)
    (Jprofile Jchild degree:ℕ)(Sp Tchild Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:1≤upper)(hb1:0≤b1)(hb2:0≤b2)(hAmax:0≤Amax)(hlo:0<loFloor)
    (hCm:0≤Cm)(hCe:0≤Ce)(hCd:0≤Cd)(hCt:0≤Ct)(hCc:0≤Cc)(hcost:0≤cost)
    (sigma delta reserve paid saving Mcap Mamp primeLoss Bcommon:ℝ)
    (hs:0<sigma)(heps:0≤epsilon)(heps1:epsilon≤1)(hloss:0≤primeLoss)(hMamp:0≤Mamp):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀Q:Ideal O,∀Kfix:ℝ,0≤Kfix→∃Cbound:ℝ,0<Cbound ∧
    ∀p:Profiles a b,∀Z t height A seed C0 C1:ℝ,
      1<Z→0≤height→0≤A→A≤Amax→1≤seed→0≤C0→0≤C1→
    ∀(M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O)),
    fixedBadPrimes⊆Sbad→
    ∀(η τ:Character)(C D:Ideal O)(_hC:Supported C)(_hD:Supported D),
    primeSupport C=primeSupport D→∀E:Finset (CommonIndex C D),
    ∀K V Mdecl Mwidth:ℝ,0<K→0<V→0≤Mdecl→Mdecl≤Mcap→
    Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth→Mwidth≤Mdecl→
    Real.logb Z V≤Mdecl→
    Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card→
    τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}→
    (C.absNorm:ℝ)≤Z^Bcommon→
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (q:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve q (errorIndex i+1);
    let alpha:=powers epsilon;
    let Ebase:=Cc*(C0+C1)*diagonalControl W*(p.control Tchild)^2*(1+height)^degree;
    let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
      (fixedFactors Cm Ce Cd Ct Z epsilon deltaSource thetaSource Bcap cost Ebase t loFloor seed Jchild Sf W);
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j;
    let aerror:=fun (q:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers q (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror q i χ)
        (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval q Z (errorIndex i+1)) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) epsilon
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (Cbound*(C0+C1+1)*(p.control U)^2*(1+|t|+height)^J/seed)*
        Z^(Mdecl-M0+epsilon*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(losses epsilon deltaSource thetaSource Bcap j+
          lossVector sigma delta reserve paid epsilon Mcap saving j):=by
  obtain ⟨U,J,hweights⟩:=actual_weights N upper b1 b2 Amax loFloor
    Cm Ce Cd Ct Cc cost epsilon deltaSource thetaSource Bcap Jprofile Jchild degree Sp Tchild Sf W
    (zero_le_one.trans hu) hb1 hb2 hAmax hlo hCm hCe hCd hCt hCc hcost
  refine ⟨U,J,?_⟩
  intro Q Kfix hKfix
  obtain ⟨Cweights,hCweights,hw⟩:=hweights Q Kfix hKfix
  let G:=56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))
  have hG:0<G:=by dsimp [G];positivity
  refine ⟨upper^N*G*Cweights,by positivity,?_⟩
  intro p Z t height A seed C0 C1 hZ hheight hA hAA hseed hC0 hC1
    M _ Hray Sbad hbad η τ C D hC hD hCD E K V Mdecl Mwidth hK hV hM hcap hactual hwidth hlow hcard hmod hncap
  dsimp only
  let Ebase:=Cc*(C0+C1)*diagonalControl W*(p.control Tchild)^2*(1+height)^degree
  let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
    (fixedFactors Cm Ce Cd Ct Z epsilon deltaSource thetaSource Bcap cost Ebase t loFloor seed Jchild Sf W)
  have hEbase:0≤Ebase:=by
    have hd:=diagonalControl_nonneg W
    dsimp [Ebase]
    positivity
  have hH:∀j,0≤H j:=coefficients_nonneg N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed _
    (zero_le_one.trans hu) hb1 hb2 hKfix (zero_le_one.trans hseed)
    (fixedFactors_nonneg Cm Ce Cd Ct Z epsilon deltaSource thetaSource Bcap cost Ebase t loFloor seed Jchild Sf W
      hCm hCe hCd hCt (zero_le_one.trans hZ.le) hcost hEbase hlo.le (zero_le_one.trans hseed))
  have ha:=CenteredMomentEnergyFirstHighNormalizedGaussianPowers.actual_high_normalized_four_powers
    M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid epsilon saving Mdecl Mwidth Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hwidth hlow hloss hMamp hcard hmod upper N (zero_le_one.trans hu)
    H hH
  dsimp only at ha
  apply ha.trans
  have hb:=finite_power_budget upper (C.absNorm:ℝ) Z epsilon Bcommon
    (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) primeLoss G
    (Cweights*(C0+C1+1)*(p.control U)^2*(1+|t|+height)^J) seed N hu (Nat.cast_nonneg _)
    hZ heps heps1 hncap hG.le (by positivity) (zero_lt_one.trans_le hseed) H
    (losses epsilon deltaSource thetaSource Bcap)
    (lossVector sigma delta reserve paid epsilon Mcap saving) hH
    (hw p Z t height A seed C0 C1 (zero_lt_one.trans hZ) hheight hA hAA hseed hC0 hC1)
  convert hb using 1 ; dsimp only [G] ; ring

theorem actual_high_homogeneous_four_powers
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth)(hwidth:Mwidth≤Mdecl)
    (hlow:Real.logb Z V≤Mdecl)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:1≤upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)
    (F seed Bcommon:ℝ)(srcLoss:Fin 4→ℝ)(hF:0≤F)(hseed:0<seed)(heps1:eps≤1)
    (hncap:(C.absNorm:ℝ)≤Z^Bcommon)
    (hbound:∀j,H j≤F*Z^(srcLoss j)/seed):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1)) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (upper^N*(56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ)))*F/seed)*
        Z^(Mdecl-M0+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+lossVector sigma delta reserve paid eps Mcap saving j) := by
  have ha:=CenteredMomentEnergyFirstHighNormalizedGaussianPowers.actual_high_normalized_four_powers
    M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hwidth hlow hloss hMamp hcard hmod
    upper N (zero_le_one.trans hupper) H hH
  dsimp only at ha ⊢
  apply ha.trans
  exact finite_power_budget upper (C.absNorm:ℝ) Z eps Bcommon
    (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) primeLoss
    (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))) F seed N
    hupper (Nat.cast_nonneg _) hZ heps heps1 hncap (by positivity) hF hseed H
    srcLoss (lossVector sigma delta reserve paid eps Mcap saving) hH hbound

end SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers

end

end OAI

end Source2078

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstNormalizedGaussianPowers.lean; sha256: 45fbbb659ac3da50abea69fe1042b4b26a269ec3899b4da4916c5f7493189c40 -/
section Source2079
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstNormalizedGaussianPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

theorem actual_normalized_four_powers
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
    (upper:ℝ)(N:ℕ)(hupper:0≤upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)(rmain:ℝ)
    (rerror:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3)))→Fin 3→Ray→ℝ):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving rmain j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (rerror p i χ) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (C.absNorm:ℝ)^eps*∑j:Fin 4,(upper^N)^(alpha j)*
        (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
          Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss)) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hz:=zero_lt_one.trans hZ
  have hn:=actual_power_reference_identity
    (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))) ((Mamp+2*sigma)/(sigma/6))
    upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z (allowance C D Z) eps N H
    (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
    (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid saving rmain
    (fun p i χ=>errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1))
    rerror hV hc hq hz
  have hav:=actual_low_four_coefficients M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hlow hloss hMamp hcard hmod H hH rmain rerror
  dsimp only at hn hav
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [hn j]
  have hpos:0≤(C.absNorm:ℝ)^eps*(upper^N)^(CenteredMomentSecondChildPowerBudget.powers eps j):=by positivity
  exact (mul_le_mul_of_nonneg_left (hav j) hpos).trans_eq (by ring)

end SevenEighths.CenteredMomentEnergyFirstNormalizedGaussianPowers

end

end OAI

end Source2079
