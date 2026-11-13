import OpenAIGrouped.Unit054
import OpenAIGrouped.Unit053
import OpenAIGrouped.Unit052
import OpenAIGrouped.Unit051
import OpenAIGrouped.Unit023
import OpenAIGrouped.Unit024
import OpenAIGrouped.Unit032
import OpenAIGrouped.Unit045
import OpenAIGrouped.Unit033
import OpenAIGrouped.Unit029

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroUnbalancedOriginal.lean; sha256: d212a815247b8fc3d2c5587f6c34cf12bbe1700c33e7dbee98c7f81f7330f5b7 -/
section Source2200
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroUnbalancedOriginalPower
open CenteredMomentEnergyZeroUnbalancedOriginalGates
local notation "O"=>HeckeFamily.O

theorem original_unbalanced_from_zero_low
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →
      min (length Z X₁) (length Z X₂)≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂ →
      s.plainEnergy p t X₁ X₂ ≤
        C*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=original_from_zero_low
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hshort hlarge
  have hordered (p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
      (hshort:length Z X₁≤s.width/4)
      (hlarge:5*s.width/6≤length Z X₁+length Z X₂):
      s.plainEnergy p t X₁ X₂≤
        C*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
    have hlong:=original_long_positive Z s.width X₁ X₂ hZ.1
      (hrho.trans_le hslo) hX₁ hX₂ hshort hlarge
    exact hZ.2 e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂
      (raw_short_bound Z s.width X₁ hZ.1 hX₁ hshort) hlong.2.2
  rcases min_le_iff.mp hshort with hshort|hshort
  · exact hordered p X₁ X₂ hX₁ hX₂ hshort hlarge
  · let p':Profiles a b:={
      profile:=![p.profile 1,p.profile 0]
      support:=by
        intro i
        fin_cases i
        · simpa using p.support 1
        · simpa using p.support 0 }
    have hpcontrol:p'.control U=p.control U:=by
      simp [p',Profiles.control,mul_comm]
    have hswap:s.plainEnergy p' t X₂ X₁=s.plainEnergy p t X₁ X₂:=by
      unfold NaturalState.plainEnergy CenteredMomentInductionEnergy.energy
      apply tsum_congr
      intro z
      have hh:CenteredMomentRetainedEnergy.positiveSlotRow s.character s.mask 1 z
          (p'.profile 0) (p'.profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0)
          (fun _:Fin 0=>1) t X₂ X₁=
          CenteredMomentRetainedEnergy.positiveSlotRow s.character s.mask 1 z
          (p.profile 0) (p.profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0)
          (fun _:Fin 0=>1) t X₁ X₂:=by
        simp only [p',Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
        unfold CenteredMomentRetainedEnergy.positiveSlotRow
        rw [mul_comm X₂ X₁]
        ring
      rw [hh]
    have hh:=hordered p' X₂ X₁ hX₂ hX₁ hshort (by linarith)
    simpa only [hswap,hpcontrol] using hh

end SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginal

end

end OAI

end Source2200

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroReferenceBounded.lean; sha256: 884ba60e07c53f3483fa806d33c6b0fed16183dfe4fa7d7396d7379b42789c95 -/
section Source2201
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget CenteredMomentNaturalRowSource
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem balanced_reference_from_zero_low
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →s.width/4≤Real.logb Z (X₁*X₂) →
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hLupper,hscalar⟩:=
    exists_bounded_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_from_low d hd a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi
      hBmask hL 2 (by norm_num) S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong 0 n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  have hxiM:xi≤s.width/6:=by linarith only [hxirho, hslo, hrho]
  have hh:=hZ.2 e Q degree K hK hlow s hQ hs hxiM p t X₁ X₂ hX₁ hX₂ hlarge
  have hledger:=hscalar e he Z hZ.1.le s hs (Fin 0) (fun _=>0) (by simpa using hM)
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one] at hledger
  have hp:=hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hp
  let A:=Cprofile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*(1+|t|)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤A:=by dsimp only [A];positivity
  have hE:0≤E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    exact ht
  have hmain:Cref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*
        (1+|t|)^(2*n))≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hdiag hA]
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl s.radial.profile≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤E:=by
      dsimp only [E]
      nlinarith only [mul_nonneg hK (mul_nonneg hdiag hA)]
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤L:=by linarith only [hM, hBmask, hxi, hL]
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)
  have hP:0≤P:=by dsimp only [P];positivity
  have hQmain:0≤Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyZeroReferenceBounded

end

end OAI

end Source2201

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroReferenceLiveBounded.lean; sha256: 28e602824bbe3fe98041ed86c1c686ee4d31b24904263a7e31a015af311053ef -/
section Source2202
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceLiveBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceBounded CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem balanced_reference_live (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧0<xi ∧xi≤rho/100 ∧Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →
      5*s.width/6≤length Z X₁+length Z X₂ →
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
        C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=balanced_reference_from_zero_low
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=CenteredMomentEnergyLiveClippingDefect.endpoint_threshold
    b (rho/100) (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge
  rcases CenteredMomentEnergyLiveClippingDefect.energy_zero_or_defect s.character s.mask 1 t p
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) X₁ X₂ Z
    s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · refine Or.inr (hZ.2 e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ ?_)
    have hh:=hdft.2.trans (hendpoint Z hZZ)
    linarith

end SevenEighths.CenteredMomentEnergyZeroReferenceLiveBounded

end

end OAI

end Source2202

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroReferencePhysicalBounded.lean; sha256: 2682777f51dbda4bbe6b810a870fca09af8215236e256c7abcb9f449eca98d19 -/
section Source2203
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferencePhysicalBounded
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferenceLiveBounded CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
local notation "O"=>HeckeFamily.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

open CenteredMomentEnergyZeroReferencePhysical

theorem actual_positive_source_entry (a b bΦ rho ε Mcap Bmask B εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0<d ∧0<xi ∧xi≤rho/100 ∧Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),X₁*X₂≤Z^B →
      5*s.width/6≤length Z X₁+length Z X₂ →
      let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
      s.plainEnergy p t X₁ X₂=0 ∨
      s.plainEnergy p t X₁ X₂≤
        2*diagonalControl s.radial.profile*(
          physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)+
          Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
          Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
            Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
        2*C*(K+1)*diagonalControl s.radial.profile*
          (sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=balanced_reference_live
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=Fin 0) bΦ hbΦ (fun _=>1) a b B εdiag ξ saving (by simp) ha (by linarith) hB hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hV hlarge
  rcases hz.2 e Q degree K he hK hlow s hQ hslo hs p t X₁ X₂ hX₁ hX₂ hlarge with hzero|hreference
  · exact Or.inl hzero
  · right
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (by simp) s.puncture s.radial s.radial_support
      (by rw [balanced_volume];exact hV) (natural_inverse_scale s B hB)
    change s.plainEnergy p t X₁ X₂≤_+2*s.plainEnergy p t
      (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) at hphysical
    rw [balanced_volume] at hphysical
    dsimp only [inp] at hphysical
    linarith only [hphysical,hreference]

end SevenEighths.CenteredMomentEnergyZeroReferencePhysicalBounded

end

end OAI

end Source2203

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthHighBound.lean; sha256: 09eb74be3fdb4b88d07720c1e08af8b13f6622d768d88bdaead64e0d0fb41bd7 -/
section Source2204
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthHighBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyOriginalProfileControl
local notation "O"=>HeckeFamily.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

lemma low_restrict (Q:Ideal O)(a b bΦ Bmask L L' Mcap e Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(K:ℝ)(hZ:1≤Z)(hL:L'≤L)
    (h:ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K):
    ZeroLowAt Q a b bΦ Bmask L' Mcap e Z degree S K:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hl
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ hL
  exact h s hQ hs p t X₁ X₂ hX₁ hX₂ (hc₁.trans hp) (hc₂.trans hp) hl

theorem actual_high_from_physical
    (a b bΦ rho ε Mcap Bmask B εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(e emass efinal:ℝ)(Q:Ideal O)(K Cmass:ℝ),
      0≤e→0≤K→0≤Cmass→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      ZeroLowAt Q a b bΦ Bmask (Mcap+Bmask+rho/100) Mcap e Z degree S K→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q→ rho≤s.width→s.width≤Mcap→
      ∀(p:Profiles a b)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),X₁*X₂≤Z^B→
      5*s.width/6≤length Z X₁+length Z X₂→
      let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
      ((Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂)→
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)≤
          Cmass*(p.control Smass)^2*(1+|t|)^Jmass*
            Z^(max s.width (length Z X₁+length Z X₂)+emass))→
      s.plainEnergy p t X₁ X₂≤
        Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|)^Jout*Z^(max s.width (length Z X₁+length Z X₂)+efinal):=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuCap,hLu,hLuCap,huStage⟩:=
    CenteredMomentEnergyZeroUnbalancedOriginal.original_unbalanced_from_zero_low
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirCap,hLr,hLrCap,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hrStage⟩:=
    CenteredMomentEnergyZeroReferencePhysicalBounded.actual_positive_source_entry
      a b bΦ rho ε Mcap Bmask B εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hB hεdiag hξ
  refine ⟨Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Ju,Uu,Cu,hCu,huBound⟩:=huStage S
  obtain ⟨Jr,Ur,Cr,hCr,hrBound⟩:=hrStage S
  let U:Finset (ℕ×ℕ):=insert (0,0) (Smass∪Uu∪Ur)
  let Jout:ℕ:=Jmass+Ju+Jr
  let P:ℝ:=1
  let D:ℝ:=Cdiag*P*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ctail*P*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤P:=by norm_num [P]
  have hD:0≤D:=by dsimp [D];positivity
  have hT:0≤T:=by dsimp [T];positivity
  let Cfixed:ℝ:=Cu+2*Cr+2*D+2*T+2
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];positivity
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [huBound,hrBound] with Z hZu hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Q K Cmass he hK hCmass hefinal hmassFinal hdiagFinal htailFinal
    hlow s hQ hwidthLo hwidth p t X₁ X₂ hX₁ hX₂ hvolume hlarge
  dsimp only
  intro hphysical
  let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂
  have hlowU:=low_restrict Q a b bΦ Bmask _ Lu Mcap e Z degree S K hZ.1.le hLuCap hlow
  have hlowR:=low_restrict Q a b bΦ Bmask _ Lr Mcap e Z degree S K hZ.1.le hLrCap hlow
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hscale:0≤s.radial.scale:=s.radial.scale_pos.le
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hbase:1≤1+|t|:=by exact le_add_of_nonneg_right (abs_nonneg t)
  let Mout:ℝ:=max s.width (length Z X₁+length Z X₂)
  have hwm:s.width≤Mout:=le_max_left _ _
  let F:ℝ:=(p.control U)^2*(1+|t|)^Jout*Z^(Mout+efinal)
  have hF:0≤F:=by dsimp [F];positivity
  have henv (Sj:Finset (ℕ×ℕ))(jj:ℕ)(ej:ℝ)(hSj:Sj⊆U)(hjj:jj≤Jout)(hej:ej≤efinal):
      (p.control Sj)^2*(1+|t|)^jj*Z^(s.width+ej)≤F:=by
    have hp:=profile_control_mono p hSj
    have hp0:=p.control_nonneg Sj
    have hj:=pow_le_pow_right₀ hbase hjj
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (add_le_add hwm hej)
    dsimp [F]
    gcongr
  have hu:Uu⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hr:Ur⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hm:Smass⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hju:Ju≤Jout:=by dsimp [Jout];omega
  have hjr:Jr≤Jout:=by dsimp [Jout];omega
  have hjm:Jmass≤Jout:=by dsimp [Jout];omega
  have huni:Cu*(K+1)≤Cfixed*(K+Cmass+1):=by
    have hCuC : Cu ≤ Cfixed := by
      dsimp only [Cfixed]
      linarith only [hCr, hD, hT]
    exact mul_le_mul hCuC (by linarith only [hCmass])
      (by linarith only [hK]) hCfixed.le
  by_cases hshort:min (length Z X₁) (length Z X₂)≤s.width/4
  · have hunbalanced:=hZu.2 e Q degree K he hK hlowU s hQ hwidthLo hwidth
      p t X₁ X₂ hX₁ hX₂ hshort hlarge
    have heq:=henv Uu Ju (e+ε) hu hju hefinal
    have hh':=mul_le_mul_of_nonneg_left heq (show 0≤Cu*(K+1)*diagonalControl s.radial.profile by positivity)
    have hc:=mul_le_mul_of_nonneg_right huni (mul_nonneg hdg hF)
    apply hunbalanced.trans
    dsimp [F] at hh' hc ⊢
    rw [show s.width+e+ε=s.width+(e+ε) by ring]
    nlinarith only [hh',hc]
  · have hfour':=balanced_four_scale_gates Z s.width X₁ X₂ hZ.1 (hrho.trans_le hwidthLo)
      hX₁ hX₂ (le_of_not_ge hshort)
    have hfour:Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂:=
      ⟨hfour'.1,hfour'.2.1,hfour'.2.2.1,hfour'.2.2.2.1⟩
    rcases hZ.2 e Q degree K he hK hlowR s hQ hwidthLo hwidth p t X₁ X₂ hX₁ hX₂
      hvolume hlarge with hzero|hsource
    · rw [hzero]
      positivity
    have hmass:=hphysical hfour
    have hmEnv:(p.control Smass)^2*(1+|t|)^Jmass*Z^(Mout+emass)≤F:=by
      have hp:=profile_control_mono p hm
      have hp0:=p.control_nonneg Smass
      have hj:=pow_le_pow_right₀ hbase hjm
      have hx:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (show Mout+emass≤Mout+efinal by linarith only [hmassFinal])
      dsimp [F]
      gcongr
    have hmass':physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
        (X₁*X₂)≤Cmass*F:=by
      apply hmass.trans
      convert mul_le_mul_of_nonneg_left hmEnv hCmass using 1 ; ring
    have hplain:(plainControl inp (p.profile 0) (p.profile 1))^2≤P*(p.control U)^2:=by
      have hc:=plain_control_sq_le inp p U 0 1 (by norm_num) (by simp) (by intro i;exact Fin.elim0 i)
      have h00:(0,0)∈U:=Finset.mem_insert_self _ _
      simpa only [P,Finset.insert_eq_of_mem h00,one_pow,one_mul] using hc
    have hheight1:1≤(1+|t|)^Jout:=one_le_pow₀ hbase
    have hscalePower (x:ℝ)(hx:x≤efinal):s.radial.scale*Z^x≤Z^(Mout+efinal):=by
      rw [s.scale_eq,←Real.rpow_add hz]
      exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by have hh:=hwm;unfold NaturalState.width at hh;linarith only [hh, hx, s.character_nonneg])
    have hterm (c A x:ℝ)(hc:0≤c)(hA:0≤A)(hx:x≤efinal):
        c*(plainControl inp (p.profile 0) (p.profile 1))^2*A*s.radial.scale*Z^x≤c*P*A*F:=by
      calc
        _≤c*(P*(p.control U)^2)*A*(s.radial.scale*Z^x):=by rw [←mul_assoc];gcongr
        _≤c*(P*(p.control U)^2)*A*Z^(Mout+efinal):=by gcongr;exact hscalePower x hx
        _≤c*P*A*F:=by
          dsimp [F]
          nlinarith only [mul_nonneg (show 0≤c*P*A*(p.control U)^2*Z^(Mout+efinal) by positivity)
            (sub_nonneg.mpr hheight1)]
    have hdterm:=hterm Cdiag (Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) hdiagFinal
    have htterm:=hterm Ctail (Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) htailFinal
    have hrEnv:=henv Ur Jr (e+ε) hr hjr hefinal
    have href:=mul_le_mul_of_nonneg_left hrEnv (show 0≤2*Cr*(K+1)*diagonalControl s.radial.profile by positivity)
    have hsum:=mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmass' hdterm) htterm)
      (show 0≤2*diagonalControl s.radial.profile by positivity)
    have hcoeff:2*Cmass+2*D+2*T+2*Cr*(K+1)≤Cfixed*(K+Cmass+1):=by
      dsimp [Cfixed]
      nlinarith only [hCu, hCr, hD, hT, hK, hCmass, mul_nonneg hCu.le hK,mul_nonneg hCu.le hCmass,mul_nonneg hCr.le hCmass,
        mul_nonneg hD hK,mul_nonneg hD hCmass,mul_nonneg hT hK,mul_nonneg hT hCmass]
    have hfinish:=mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hdg hF)
    apply hsource.trans
    change _≤Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
      (1+|t|)^Jout*Z^(Mout+efinal)
    dsimp [D,T,F] at hsum href hfinish
    change _≤_ at hsum
    change 2*Cr*(K+1)*diagonalControl s.radial.profile*((p.control Ur)^2*
      (1+|t|)^Jr*Z^(s.width+(e+ε)))≤_ at href
    change 2*diagonalControl s.radial.profile*(_+_+_)+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(p.control Ur)^2*
      (1+|t|)^Jr*Z^(s.width+e+ε)≤_
    have hex:s.width+e+ε=s.width+(e+ε):=by ring
    rw [hex]
    nlinarith only [hsum,href,hfinish]

end SevenEighths.CenteredMomentEnergyZeroGrowthHighBound

end

end OAI

end Source2204

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthSource.lean; sha256: 3d7dab36a6386b055984d67b36ed13cd687d7318773a89de538e5c691141edb4 -/
section Source2205
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthSource
open HeckeFamily QuadraticInitialBound CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroGrowthHighBound
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentFirstSourceReduction CenteredMomentEnergyBandMonotonicity
open CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

def PhysicalGrowthAt (Q:Ideal O)(a b bΦ Bmask L rho Mcap ξ e Z:ℝ)(ha:0<a)
    (Ψ:𝓢(ℝ,ℂ))(S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→ rho≤s.width→s.width≤Mcap→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→5*s.width/6≤length Z X₁+length Z X₂→
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
    (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
      Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂)→
    physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)≤
      C*(p.control S)^2*(1+|t|)^J*Z^(max s.width (length Z X₁+length Z X₂)+e)

theorem actual_growth_from_physical
    (a b bΦ rho ε Mcap Bmask B L εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hLB:2*L≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(e emass efinal:ℝ)(Q:Ideal O)(K Cmass:ℝ),
      0≤e→0≤K→0≤Cmass→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      ZeroAt Q a b bΦ Bmask L rho efinal Z Jout U (Cfixed*(K+Cmass+1))→
      ZeroLowAt Q a b bΦ Bmask (max L (Mcap+Bmask+rho/100)) Mcap e Z degree S K→
      PhysicalGrowthAt Q a b bΦ Bmask L rho Mcap ξ emass Z ha Ψ Smass Jmass Cmass→
      ZeroGrowthAt Q a b bΦ Bmask L Mcap efinal Z Jout U (Cfixed*(K+Cmass+1)):=by
  obtain ⟨Ψ,hsΨ,hnΨ,hstage⟩:=actual_high_from_physical a b bΦ rho ε Mcap Bmask B εdiag ξ saving
    ha hlo hhi hbΦ hrho hε hM hBmask hB hεdiag hξ
  refine ⟨Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Jh,Uh,Ch,hCh,hbound⟩:=hstage degree S Jmass Smass
  let Jout:=degree+Jh
  let U:=S∪Uh
  let Cfixed:=Ch+1
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];linarith
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Q K Cmass he hK hCm hef hmf hdf htf hold hlow hmass
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hCout:0≤Cfixed*(K+Cmass+1):=by positivity
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  by_cases hsmall:s.width≤ rho
  · exact zeroGrowth_of_zeroAt Q a b bΦ Bmask L rho efinal Z Jout U
      (Cfixed*(K+Cmass+1)) hCout hold s hQ hsmall p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hbase:1≤1+|t|:=by linarith [abs_nonneg t]
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hS:S⊆U:=Finset.subset_union_left
  have hUh:Uh⊆U:=Finset.subset_union_right
  have hlowL:=low_restrict Q a b bΦ Bmask _ L Mcap e Z degree S K hZ.1.le (le_max_left _ _) hlow
  by_cases hl:length Z X₁+length Z X₂≤5*s.width/6
  · have hh:=hlowL s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hl
    have hp:=profile_control_mono p hS
    have hp0:=p.control_nonneg S
    have hj:degree≤Jout:=Nat.le_add_right _ _
    have hpow:=pow_le_pow_right₀ hbase hj
    have hloss:s.width+e≤max s.width (length Z X₁+length Z X₂)+efinal:=by
      linarith [le_max_left s.width (length Z X₁+length Z X₂)]
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hloss
    have hcoeff:K≤Cfixed*(K+Cmass+1):=by dsimp [Cfixed];nlinarith [mul_nonneg hCh.le hK,mul_nonneg hCh.le hCm]
    apply hh.trans
    rw [Real.norm_eq_abs]
    gcongr
  have hlowR:=low_restrict Q a b bΦ Bmask _ (Mcap+Bmask+rho/100) Mcap e Z degree S K
    hZ.1.le (le_max_right _ _) hlow
  have hvolume:X₁*X₂≤Z^B:=by
    calc
      _≤Z^L*Z^L:=mul_le_mul hc₁ hc₂ hX₂.le (Real.rpow_nonneg hz.le _)
      _=Z^(2*L):=by rw [←Real.rpow_add hz];congr 1;ring
      _≤Z^B:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLB
  have hp:=hmass s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ (le_of_not_ge hl)
  have hh:=hZ.2 e emass efinal Q K Cmass he hK hCm hef hmf hdf htf hlowR
    s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hvolume (le_of_not_ge hl) hp
  have hcontrol:=profile_control_mono p hUh
  have hp0:=p.control_nonneg Uh
  have hj:Jh≤Jout:=Nat.le_add_left _ _
  have hpow:=pow_le_pow_right₀ hbase hj
  have hcoeff:Ch≤Cfixed:=by dsimp [Cfixed];linarith
  apply hh.trans
  rw [Real.norm_eq_abs]
  gcongr

end SevenEighths.CenteredMomentEnergyZeroGrowthSource

end

end OAI

end Source2205

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthPhysical.lean; sha256: 5cecb6430db18c1cccab84f81d4f81b9fbc988c9261c2fa8b71e44ee8d5706c6 -/
section Source2206
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthPhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentSecondHeightFamily
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentEnergyZeroGrowthPhysicalReindex CenteredMomentSourceInputReindex
open CenteredMomentEnergyZeroBalancedAdmission CenteredMomentEnergyZeroBalancedDictionary
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstSourceParameters CenteredMomentEnergyFirstLiveAdmission
open CenteredMomentEnergyCanonicalHighPhysical CenteredMomentEnergyZeroGrowthSource
open CenteredMomentEnergyStageMargins CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceReduction
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_growth_physical
    (Wslot:ℝ→ℂ)(aslot bslot Lslot lo hi κ a b bΦ Bmask Lgoal Lchild Mparent Mchild
      Mschedule Bschedule ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hLs:0≤Lslot)(hκ:(3/4:ℝ)≤κ)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκbeta:2*HeckeZeroSupremum.beta-1≤κ)
    (ha:0<a)(hb:0≤b)(hBmask:0≤Bmask)(hLgoal:0≤Lgoal)(hLchild:0≤Lchild)
    (hMparent:0≤Mparent)(hMchild:0≤Mchild)(hMschedule:0≤Mschedule)(hBschedule:0≤Bschedule)
    (hε:0<ε)(hcap: max Mparent (2*Lgoal)≤Lchild)
    (hready:readyBudget (max Mparent (2*Lgoal)) Bmask≤Bschedule)
    (hdrop:Mparent-amplification ε/2≤Mchild)
    (Ψ:𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→
    ∀(k:ℕ)(εchild C₀ C₁ rho:ℝ),εchild≤stageLoss Mschedule Bschedule ε k→
      0≤C₀→0≤C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 Lchild Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 Lchild Lslot lo hi
        Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalGrowthAt (internalQ Q η₀) a b bΦ Bmask Lgoal rho Mparent
        (reserve Mschedule Bschedule ε/4) (physicalLoss Mschedule Bschedule ε k)
        Z ha Ψ Uprofile Jheight (C*(C₀+C₁+1)):=by
  let A:=max Mparent (2*Lgoal)
  let r:=reserve Mschedule Bschedule ε
  have hA:0≤A:=hMparent.trans (le_max_left _ _)
  obtain ⟨hsigma,hsigma1,hr,hxiSigma,hxi1,hes,hes1,hem,hmesh,hmeshEta,heta0,heta,hSaving,hSeed⟩:=
    parameter_gates Mschedule A Bschedule κ ε hMschedule hA hBschedule hκ hε
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have ha2:0<a^2:=sq_pos_of_pos ha
  obtain ⟨U,J,hphysical⟩:=actual_high_physical (α:=α) M H hH
    Wslot aslot bslot Mchild Lslot (r/4) lo hi κ a b 1
    (maskEpsilon Mschedule Bschedule ε) (by norm_num) hem ha hb
    Lchild hLchild degree S haslot hWs hW hMchild hLs hr hκsmall hbeta hκbeta
    0 1 1 (a^2) (r/4) (by norm_num) (by norm_num) ha2 hr
    (fun _=>1) (fun _=>1) (fun _=>by norm_num)
    (sourceEpsilon Mschedule A Bschedule ε) (r/4) (r/4) (A+1) (r/4)
    (2*amplification ε+1) hes hr hr hr
    (amplification ε) hsigma hxiSigma A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBmask heta hr hsigma1 hxi1 hr hes1 le_rfl (fun _=>Ψ) (r/4) (a*a)
    hr (mul_pos ha ha)
  have hfit:=eventually_actual_four_fit Mschedule A Bmask Bschedule κ ε
    hMschedule hA hBmask hBschedule hready hκ hε
  have hclip:∀ᶠZ:ℝ in atTop,1<Z ∧ Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    filter_upwards [eventually_gt_atTop (1:ℝ),
      (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<2*(r/4) by linarith)))
        (max 1 b*max 1 b)] with Z hZ hz
    exact ⟨hZ,(Real.logb_le_iff_le_rpow hZ (mul_pos
      (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _)))).mpr hz⟩
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Zbase,hZbase,hphysical⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Znum,hZnum⟩:=Filter.eventually_atTop.mp (hfit.and hclip)
  refine ⟨C,hC,max Zbase Znum,hZbase.trans_le (le_max_left _ _),?_⟩
  intro Z hZZ k εchild C₀ C₁ rho hchild hC₀ hC₁ hzero hpos
  have hZbaseLe:Zbase≤Z:=(le_max_left _ _).trans hZZ
  have hn:=hZnum Z ((le_max_right _ _).trans hZZ)
  have hZ:1<Z:=hn.1.1
  intro s hQ hsLower hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hlarge
  dsimp only
  intro hfour
  let src:=emptyBalanced s p ha t X₁ X₂ hX₁ hX₂ α
  let θ:(∅:Finset α)→RayQuotient.Characters M H:=fun i=>isEmptyElim i
  have hmatch:CenteredMomentAllocatedRayDictionary.Matches M H hH src η₀ θ
      (fun _=>0) (fun _=>0) (fun _=>0) Wslot bslot Z:=by
    constructor <;> intro i <;> exact isEmptyElim i
  have hupper:=four_upper_scales s p ha t X₁ X₂ hX₁ hX₂ Mparent Lgoal hZ hLgoal hs hc₁ hc₂
  have hu:Z^A≤Z^Lchild:=Real.rpow_le_rpow_of_exponent_le hZ.le hcap
  have hgate:=declared_capacity s p ha t X₁ X₂ hX₁ hX₂ hZ
  have hdecl:=declared_capacity_upper s X₁ X₂ Mparent Lgoal hZ hLgoal hs hc₁ hc₂
  have hK:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  have hbound:=hphysical ∅ θ Z hZbaseLe εchild C₀ C₁ hC₀ hC₁ hzero hpos
    (fun _=>0) (fun _=>0) (fun _=>0) 0 (mesh Mschedule Bschedule κ ε) hmesh.le
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i) (by norm_num)
    (fun i=>isEmptyElim i) src hmatch
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i) (by simp) le_rfl le_rfl
    hb hb (le_max_right _ _) (le_max_right _ _) (by simp)
    s.puncture 1 s.puncture_ne_zero s.puncture_bound squarefree_one one_ne_zero
    s.radial.scale hK.1 p rfl rfl
    (hupper.1.trans hu) (hupper.2.1.trans hu) (hupper.2.2.1.trans hu) (hupper.2.2.2.trans hu)
    (max s.width (length Z X₁+length Z X₂)) s.width (r/4)
    (columnLoss Mschedule Bschedule ε k) hr.le hdecl
    (by
      change length Z X₁+length Z X₂+6*κ*(∑i:(∅:Finset α),(0:ℝ))≤_
      simpa only [Finset.sum_const_zero,mul_zero,add_zero] using
        le_max_right s.width (length Z X₁+length Z X₂))
    (hgate.2.1.trans (le_max_left _ _)) hgate.2.1 (by linarith)
    hn.2.2 (by simp [lowerFactor]) (le_max_left _ _)
    hfour.1 hfour.2.1 hfour.2.2.1 hfour.2.2.2 (hn.1.2 k εchild hchild)
  rw [show physicalMass src s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z (r/4)=
      physicalMass (CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂)
        s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z (r/4) from
        empty_balanced_mass s p ha t X₁ X₂ hX₁ hX₂ _ _ _ _ _ _ _ _] at hbound
  rw [show volume src=X₁*X₂ from empty_balanced_volume s p ha t X₁ X₂ hX₁ hX₂] at hbound
  have heq:max s.width (length Z X₁+length Z X₂)+columnLoss Mschedule Bschedule ε k+r/4=
      max s.width (length Z X₁+length Z X₂)+physicalLoss Mschedule Bschedule ε k:=by
    dsimp only [r]
    rw [add_assoc,columnLoss_physical]
  simpa only [map_one,Nat.cast_one,div_one,add_zero,
    show (src).t=t from rfl,heq] using hbound

end SevenEighths.CenteredMomentEnergyZeroGrowthPhysical

end

end OAI

end Source2206

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthSourceControlled.lean; sha256: e9f2da58bfc4baa59cde685497097a5ac3a25791e3761ae58701827bbc88c390 -/
section Source2207
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthSourceControlled
open HeckeFamily QuadraticInitialBound CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroGrowthHighBound
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentFirstSourceReduction CenteredMomentEnergyBandMonotonicity
open CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

open CenteredMomentEnergyZeroGrowthSource (PhysicalGrowthAt)

theorem actual_growth_from_physical
    (a b bΦ rho ε Mcap Bmask B L εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hLB:2*L≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(e emass efinal:ℝ)(Q:Ideal O)(K Cmass Cprevious:ℝ),
      0≤e→0≤K→0≤Cmass→0≤Cprevious→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      ZeroAt Q a b bΦ Bmask L rho efinal Z degree S Cprevious→
      ZeroLowAt Q a b bΦ Bmask (max L (Mcap+Bmask+rho/100)) Mcap e Z degree S K→
      PhysicalGrowthAt Q a b bΦ Bmask L rho Mcap ξ emass Z ha Ψ Smass Jmass Cmass→
      ZeroGrowthAt Q a b bΦ Bmask L Mcap efinal Z Jout U (Cfixed*(K+Cmass+Cprevious+1)):=by
  obtain ⟨Ψ,hsΨ,hnΨ,hstage⟩:=actual_high_from_physical a b bΦ rho ε Mcap Bmask B εdiag ξ saving
    ha hlo hhi hbΦ hrho hε hM hBmask hB hεdiag hξ
  refine ⟨Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Jh,Uh,Ch,hCh,hbound⟩:=hstage degree S Jmass Smass
  let Jout:=degree+Jh
  let U:=S∪Uh
  let Cfixed:=Ch+1
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];linarith
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Q K Cmass Cprevious he hK hCm hCp hef hmf hdf htf hold hlow hmass
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hCout:0≤Cfixed*(K+Cmass+Cprevious+1):=by positivity
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hbase:1≤1+|t|:=by linarith [abs_nonneg t]
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hS:S⊆U:=Finset.subset_union_left
  have hUh:Uh⊆U:=Finset.subset_union_right
  by_cases hsmall:s.width≤ rho
  · have hh:=zeroGrowth_of_zeroAt Q a b bΦ Bmask L rho efinal Z degree S
      Cprevious hCp hold s hQ hsmall p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
    have hp:=profile_control_mono p hS
    have hp0:=p.control_nonneg S
    have hj:degree≤Jout:=Nat.le_add_right _ _
    have hpow:=pow_le_pow_right₀ (show 1≤1+‖t‖ by linarith [norm_nonneg t]) hj
    have hcoeff:Cprevious≤Cfixed*(K+Cmass+Cprevious+1):=by
      dsimp [Cfixed]
      nlinarith [mul_nonneg hCh.le hK,mul_nonneg hCh.le hCm,mul_nonneg hCh.le hCp]
    apply hh.trans
    gcongr
  have hlowL:=low_restrict Q a b bΦ Bmask _ L Mcap e Z degree S K hZ.1.le (le_max_left _ _) hlow
  by_cases hl:length Z X₁+length Z X₂≤5*s.width/6
  · have hh:=hlowL s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hl
    have hp:=profile_control_mono p hS
    have hp0:=p.control_nonneg S
    have hj:degree≤Jout:=Nat.le_add_right _ _
    have hpow:=pow_le_pow_right₀ hbase hj
    have hloss:s.width+e≤max s.width (length Z X₁+length Z X₂)+efinal:=by
      linarith [le_max_left s.width (length Z X₁+length Z X₂)]
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hloss
    have hcoeff:K≤Cfixed*(K+Cmass+Cprevious+1):=by dsimp [Cfixed];nlinarith [mul_nonneg hCh.le hK,mul_nonneg hCh.le hCm,mul_nonneg hCh.le hCp]
    apply hh.trans
    rw [Real.norm_eq_abs]
    gcongr
  have hlowR:=low_restrict Q a b bΦ Bmask _ (Mcap+Bmask+rho/100) Mcap e Z degree S K
    hZ.1.le (le_max_right _ _) hlow
  have hvolume:X₁*X₂≤Z^B:=by
    calc
      _≤Z^L*Z^L:=mul_le_mul hc₁ hc₂ hX₂.le (Real.rpow_nonneg hz.le _)
      _=Z^(2*L):=by rw [←Real.rpow_add hz];congr 1;ring
      _≤Z^B:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLB
  have hp:=hmass s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ (le_of_not_ge hl)
  have hh:=hZ.2 e emass efinal Q K Cmass he hK hCm hef hmf hdf htf hlowR
    s hQ (le_of_not_ge hsmall) hs p t X₁ X₂ hX₁ hX₂ hvolume (le_of_not_ge hl) hp
  have hcontrol:=profile_control_mono p hUh
  have hp0:=p.control_nonneg Uh
  have hj:Jh≤Jout:=Nat.le_add_left _ _
  have hpow:=pow_le_pow_right₀ hbase hj
  have hcoeff:Ch≤Cfixed:=by dsimp [Cfixed];linarith
  have hcoefFull:Ch*(K+Cmass+1)≤Cfixed*(K+Cmass+Cprevious+1):=
    mul_le_mul hcoeff (by linarith) (by positivity) hCfixed.le
  have hfront:=mul_le_mul_of_nonneg_right hcoefFull
    (show 0≤diagonalControl s.radial.profile*(p.control Uh)^2*(1+|t|)^Jh*
      Z^(max s.width (length Z X₁+length Z X₂)+efinal) by positivity)
  have hmid:s.plainEnergy p t X₁ X₂≤
      Cfixed*(K+Cmass+Cprevious+1)*diagonalControl s.radial.profile*(p.control Uh)^2*
        (1+|t|)^Jh*Z^(max s.width (length Z X₁+length Z X₂)+efinal):=by
    apply hh.trans
    convert hfront using 1 <;> ring
  apply hmid.trans
  rw [Real.norm_eq_abs]
  gcongr

end SevenEighths.CenteredMomentEnergyZeroGrowthSourceControlled

end

end OAI

end Source2207

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthReserve.lean; sha256: 623319508bc0b2e78de20fdb9eb0b9cf3be5768c192f36f109f5382260ef20ff -/
section Source2208
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyZeroGrowthReserve
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyReferenceScalarBounds

theorem ledger_bound (Mcap Bmask bΦ L d loss defect xi saving ε:ℝ)
    (_hM:0≤Mcap)(_hB:0≤Bmask)(hL:0≤L)(hd:0<d)
    (hmain:d*(Bmask+Mcap+1)+loss+defect+xi≤ε)
    (herror:Bmask*d+Mcap*(2*d)-2*saving+L≤ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z→∀s:NaturalState Z Bmask bΦ,s.width≤Mcap→
      (s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤C*Z^(s.width+ε):=by
  let A:ℝ:=max 1 ((fixedConductorFactor:ℝ)*bΦ)
  let B:ℝ:=1+2*L/d
  have hA:0<A:=zero_lt_one.trans_le (le_max_left _ _)
  have hBp:0<B:=by dsimp [B];positivity
  refine ⟨A^d*B+A^(2*d),by positivity,?_⟩
  intro Z hZ s hs
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hr:=radical_power s d hd.le
  have hc:=conductor_power s Mcap d hs hd.le
  have hc₂:=conductor_power s Mcap (2*d) hs (by positivity)
  have hl:=log_interval Z L d hZ hL hd
  have hm:max 1 s.radial.scale≤Z^s.width:=by
    apply max_le (Real.one_le_rpow hZ s.width_nonneg)
    rw [s.scale_eq]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    exact le_add_of_nonneg_right s.character_nonneg
  have hreflect:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
        (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi))≤A^d*B*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^d*Z^(Mcap*d)*(B*Z^d)*Z^(s.width+loss+defect+xi)):=by gcongr
      _=A^d*B*Z^(s.width+(d*(Bmask+Mcap+1)+loss+defect+xi)):=by
        calc
          _=A^d*B*(Z^(Bmask*d)*Z^(Mcap*d)*Z^d*Z^(s.width+loss+defect+xi)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 2;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  have herr:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
        Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤A^(2*d)*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^(2*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^s.width*Z^L):=by gcongr
      _=A^(2*d)*Z^(s.width+(Bmask*d+Mcap*(2*d)-2*saving+L)):=by
        calc
          _=A^(2*d)*(Z^(Bmask*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^s.width*Z^L):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 1;congr 1;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  calc
    _≤A^d*B*Z^(s.width+ε)+A^(2*d)*Z^(s.width+ε):=by
      simpa only [mul_add] using add_le_add hreflect herr
    _=_:=by ring

theorem exists_growth_reserve (ε Mcap Bmask bΦ Loriginal:ℝ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L saving C:ℝ,0<d ∧ 0<L ∧ 0<saving ∧ 0<C ∧
      Loriginal≤L ∧ Mcap+Bmask+d+d≤L ∧
      ∀Z:ℝ,1≤Z→∀s:NaturalState Z Bmask bΦ,s.width≤Mcap→
      (s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+d+d+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤C*Z^(s.width+ε):=by
  let d:=ε/(8*(Bmask+Mcap+4))
  let L:=max Loriginal (Mcap+Bmask+d+d)+1
  let saving:=L+Bmask*d+2*Mcap*d+1
  have hd:0<d:=by dsimp [d];positivity
  have hL:0<L:=by dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+d+d)]
  have hsave:0<saving:=by dsimp only [saving];positivity
  have hmain:d*(Bmask+Mcap+1)+d+d+d≤ε:=by
    have heq:d*(Bmask+Mcap+4)=ε/8:=by
      dsimp only [d]
      field_simp
    nlinarith
  have herr:Bmask*d+Mcap*(2*d)-2*saving+L≤ε:=by
    dsimp only [saving]
    nlinarith [mul_nonneg hB hd.le,mul_nonneg hM hd.le]
  obtain ⟨C,hC,hbound⟩:=ledger_bound Mcap Bmask bΦ L d d d d saving ε hM hB hL.le hd hmain herr
  exact ⟨d,L,saving,C,hd,hL,hsave,hC,by dsimp only [L];linarith [le_max_left Loriginal (Mcap+Bmask+d+d)],
    by dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+d+d)],hbound⟩

end SevenEighths.CenteredMomentEnergyZeroGrowthReserve

end

end OAI

end Source2208

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthChild.lean; sha256: 6c15f6ce702a46828557c0397d93ecafd789c935168e45de6409c77d0536b16a -/
section Source2209
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthChild
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyProfiles CenteredMomentLattice
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroReferenceChild
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceLowChild
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceChild
open CenteredMomentEnergyReferenceChildProfiles CenteredMomentInductionEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization CenteredMomentRetainedProfile
local notation "O"=>HeckeFamily.O

theorem independent_from_growth
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroGrowthAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤Bmask)(ha:0<a)(s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)
    (hs:s.width≤Mcap)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    :
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S)^2*Z^(max s.width (length Z X₁+length Z X₂)+ε):=by
  rw [independent_energy s hB ha W₁ W₂ hs₁ hs₂ t₁ t₂ X₁ X₂ hX₁ hX₂]
  have hh:=hlow (unitBudgetState s hB) hQ hs
    (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂) 0 X₁ X₂ hX₁ hX₂ hc₁ hc₂
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    norm_zero,add_zero,one_pow,mul_one,effectiveState,effectiveRadial] using hh

theorem reflected_from_growth
    (a b bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:ZeroGrowthAt Q a b bΦ Bmask L Mcap ε Z degree S C)
    (hB:0≤Bmask)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)(hs:s.width≤Mcap)
    (Wshort:𝓢(ℝ,ℂ))(hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    :
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((reflectionProfiles ha hlo hhi Wshort hsW j k v t).control S)^2*Z^(max s.width (length Z X₁+length Z X₂)+ε):=by
  have hh:=independent_from_growth a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha s hQ hs
    (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice Wshort k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hsW k) (-2*Real.pi*v) t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have he:((annulusSeed a b hlo hhi).profile:ℝ→ℂ)=(fun y:ℝ=>(annulus y:ℂ)):=
    funext annulusTemplate_apply
  simpa only [derivativeChoice_apply,he,reflectionProfiles] using hh

end SevenEighths.CenteredMomentEnergyZeroGrowthChild

end

end OAI

end Source2209

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroReflectionSupport.lean; sha256: 43a8597d29fdc12f89d446fc5762f02a6dfbb0b4afaa3b09294491d87b2c91e6 -/
section Source2210
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReflectionSupport
open HeckeFamily Filter CenteredMomentNaturalPrimitive EisensteinSchwartzPoisson
open CenteredMomentReflectionMass CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentReflectionDeletion CenteredMomentReflectionWeightedEnergy
open CenteredMomentReflectedChoiceEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyReferenceLowWindow
open CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O" => HeckeFamily.O

def naturalDualScale (χ ψ : Character) (X : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) : ℝ :=
  (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)

lemma naturalDualScale_pos (χ ψ : Character) (X : ℝ) (hX : 0<X)
    (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
    (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) :
    0<naturalDualScale χ ψ X D H := by
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hN := subset_product_norm_pos D (fun P hP=>redundantSet_prime _ _ P
    (Finset.mem_powerset.mp hD hP))
  have hH := norm_pos H.val
  unfold naturalDualScale
  positivity

theorem eventually_natural_choice_range (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M →
      ∀(D : Finset (Ideal O))(_hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
        (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Z^a) D H)(n : ℤ),
      n∈retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY → 0≤M-a+xi := by
  filter_upwards [eventually_natural_choice_geometry C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod D hD H hY n hn
  have h := hZ.2 χ ψ M a hcap hmod ((⟨D,hD⟩,H),n) hY hn
  have hz := Real.log_pos hZ.1
  have hm : 0≤(M-a+xi)*Real.log Z := h.2.1.trans h.2.2
  nlinarith

theorem eventually_natural_source_zero (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M → M+xi<a →
      (∀(D : Finset (Ideal O))(_hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
        (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Z^a) D H),
        retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY=∅) ∧
      (∀(D : Finset (Ideal O)),D∈(redundantSet χ.modulus ψ.modulus).powerset →
        ∀(H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))(η : Character)(F : ℝ→ℂ),
        finiteAnnularColumn η F (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H)=0) ∧
      (∀(W : ℝ→ℂ)(t : ℝ),retainedOriginal χ ψ W (Z^a) (Z^(xi/4)) t=0) ∧
      (∀G : 𝓢(ℝ,ℂ),retainedSchwartz χ ψ G (Z^a) (Z^(xi/4))=0) := by
  filter_upwards [eventually_natural_choice_range C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod hfar
  have hempty (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
      (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
      (hY : 0<naturalDualScale χ ψ (Z^a) D H) :
      retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have h := hZ.2 χ ψ M a hcap hmod D hD H hY n hn
    linarith
  have hcol (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
      (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) (η : Character)(F : ℝ→ℂ) :
      finiteAnnularColumn η F (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H)=0 := by
    have hy := naturalDualScale_pos χ ψ (Z^a) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) D hD H
    rw [finiteAnnularColumn,dite_eq_left hy,hempty D hD H hy]
    simp
  refine ⟨hempty,hcol,?_,?_⟩
  · intro W t
    unfold retainedOriginal
    apply Finset.sum_eq_zero
    intro D hD
    have hz : (fun H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)=>
        coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
        finiteAnnularColumn χ.inverse
          (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Z^(xi/4))
          (naturalDualScale χ ψ (Z^a) D H))=fun _=>0 := by
      funext H
      rw [hcol D hD H]
      simp
    change (∑'H : SmoothIdeal (redundantSet χ.modulus ψ.modulus),
      coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
      finiteAnnularColumn χ.inverse
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Z^(xi/4))
        (naturalDualScale χ ψ (Z^a) D H))=0
    rw [hz,tsum_zero]
  · intro G
    unfold retainedSchwartz
    apply Finset.sum_eq_zero
    intro D hD
    have hz : (fun H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)=>
        coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
        finiteAnnularColumn χ.inverse (paperRadialFourier G) (Z^(xi/4))
          (naturalDualScale χ ψ (Z^a) D H))=fun _=>0 := by
      funext H
      rw [hcol D hD H]
      simp
    change (∑'H : SmoothIdeal (redundantSet χ.modulus ψ.modulus),
      coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
      finiteAnnularColumn χ.inverse (paperRadialFourier G) (Z^(xi/4))
        (naturalDualScale χ ψ (Z^a) D H))=0
    rw [hz,tsum_zero]

lemma deleted_short_length (Z b Xshort Xlong Nshort : ℝ)
    (hZ : 1<Z)(_hb : 0<b)(hshort : 0<Xshort)(hlong : Xshort≤Xlong)
    (hN : 1≤Nshort)(hsupport : 1≤b*Xlong) :
    length Z (Xshort/Nshort)≤Real.logb Z Xlong+Real.logb Z (max 1 b) := by
  have hx : 0<Xlong := hshort.trans_le hlong
  have hn : 0<Nshort := zero_lt_one.trans_le hN
  have hd : Xshort/Nshort≤Xlong := (div_le_self hshort.le hN).trans hlong
  have hlog := Real.logb_le_logb_of_le hZ (div_pos hshort hn) hd
  have hprod : 1≤max 1 b*Xlong := hsupport.trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hx.le)
  have hzero := Real.logb_nonneg hZ hprod
  rw [Real.logb_mul (ne_of_gt (zero_lt_one.trans_le (le_max_left 1 b))) hx.ne'] at hzero
  rw [length_eq_max_log Z _ hZ (div_pos hshort hn)]
  apply max_le
  · linarith
  · exact hlog.trans (le_add_of_nonneg_right (Real.logb_nonneg hZ (le_max_left _ _)))

theorem live_deleted_growth (Z b M xi Xshort Xlong Nshort Nlong : ℝ)
    (hZ : 1<Z)(hb : 0<b)(_hM : 0≤M)(hshort : 0<Xshort)(hlong : Xshort≤Xlong)
    (hNs : 1≤Nshort)(hNl : 1≤Nlong)(hsupport : 1≤b*Xlong)
    (hlive : 0≤M-Real.logb Z (Xlong/Nlong)+xi)
    (x : ℝ)(hx : x∈Set.Icc 0 (max 0 (M-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)) :
    length Z (Real.exp x)+length Z (Xshort/Nshort)≤
      M+Real.logb Z Nlong+Real.logb Z (max 1 b)+xi := by
  have hxlong : 0<Xlong := hshort.trans_le hlong
  have hnlong : 0<Nlong := zero_lt_one.trans_le hNl
  have hwindow := (reflection_window_length Z _ x hZ (le_max_left _ _) hx).1
  rw [max_eq_right hlive,Real.logb_div hxlong.ne' hnlong.ne'] at hwindow
  have hshortbound := deleted_short_length Z b Xshort Xlong Nshort hZ hb hshort hlong hNs hsupport
  linarith

theorem eventually_endpoint_defect (b epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ Real.logb Z (max 1 b)≤epsilon := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (max 1 b)/epsilon))] with Z hZ hz
  refine ⟨hZ,?_⟩
  rw [Real.logb]
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  have hh := (div_le_iff₀ hepsilon).mp hz
  nlinarith

theorem actual_deleted_growth {Z Bmask bΦ : ℝ}(s : NaturalState Z Bmask bΦ)
    (b xi Xshort Xlong : ℝ)(hZ : 1<Z)(hb : 0<b)
    (hshort : 0<Xshort)(hlong : Xshort≤Xlong)(hsupport : 1≤b*Xlong)
    (Dshort Dlong : Finset (Ideal O))
    (hDs : Dshort∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hDl : Dlong∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hlive : 0≤s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)
    (x : ℝ)(hx : x∈Set.Icc 0
      (max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z)) :
    length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
      s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+Real.logb Z (max 1 b)+xi := by
  exact live_deleted_growth Z b s.width xi Xshort Xlong _ _ hZ hb s.width_nonneg
    hshort hlong (divisor_norm s Dshort hDs).1 (divisor_norm s Dlong hDl).1 hsupport hlive x hx

theorem eventually_actual_source_zero (bΦ xi : ℝ)(hbΦ : 0<bΦ)(hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(Bmask : ℝ)(s : NaturalState Z Bmask bΦ)
      (z : O),(effectiveState s).radial.keep z →
      let χ := naturalCharacter s.character z
      ∀ψ : Character,
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      ∀a : ℝ,s.width+xi<a →
      (∀(W : ℝ→ℂ)(t : ℝ),retainedOriginal χ ψ W (Z^a) (Z^(xi/4)) t=0) ∧
      (∀G : 𝓢(ℝ,ℂ),retainedSchwartz χ ψ G (Z^a) (Z^(xi/4))=0) := by
  let C : ℝ := ((fixedConductorFactor:ℝ)+1)*bΦ
  have hC : 0<C := mul_pos (by positivity) hbΦ
  filter_upwards [eventually_natural_source_zero C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask s z hz
  dsimp only
  intro ψ hcap a hfar
  have hm : ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤C*Z^s.width := by
    apply (effective_character_cap s hbΦ.le z hz).trans
    dsimp only [C]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hbΦ.le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  exact (hZ.2 (naturalCharacter s.character z) ψ s.width a hcap hm hfar).2.2

theorem eventually_actual_deleted_growth (b epsilon : ℝ)(hb : 0<b)(hepsilon : 0<epsilon) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(Bmask bΦ : ℝ)(s : NaturalState Z Bmask bΦ)
      (xi Xshort Xlong : ℝ),0<Xshort → Xshort≤Xlong → 1≤b*Xlong →
      ∀(Dshort Dlong : Finset (Ideal O)),
      Dshort∈(CompletedGauss.primeSupport s.puncture).powerset →
      Dlong∈(CompletedGauss.primeSupport s.puncture).powerset →
      0≤s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi →
      ∀x∈Set.Icc 0 (max 0 (s.width-Real.logb Z
        (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z),
      length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
        s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+epsilon+xi := by
  filter_upwards [eventually_endpoint_defect b epsilon hepsilon] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask bΦ s xi Xshort Xlong hshort hlong hsupport Dshort Dlong hDs hDl hlive x hx
  have h := actual_deleted_growth s b xi Xshort Xlong hZ.1 hb hshort hlong hsupport
    Dshort Dlong hDs hDl hlive x hx
  linarith [hZ.2]

theorem eventually_actual_retained_deleted_growth (b bΦ xi epsilon : ℝ)
    (hb : 0<b)(hbΦ : 0<bΦ)(hxi : 0<xi)(hepsilon : 0<epsilon) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(Bmask : ℝ)(s : NaturalState Z Bmask bΦ)
      (z : O),(effectiveState s).radial.keep z →
      let χ := naturalCharacter s.character z
      ∀ψ : Character,
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      ∀(Xshort Xlong : ℝ),0<Xshort → Xshort≤Xlong → 1≤b*Xlong →
      ∀(Dshort Dlong : Finset (Ideal O)),
      Dshort∈(CompletedGauss.primeSupport s.puncture).powerset →
      Dlong∈(CompletedGauss.primeSupport s.puncture).powerset →
      ∀(E : Finset (Ideal O)),E∈(redundantSet χ.modulus ψ.modulus).powerset →
      ∀(H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Xlong/((∏P∈Dlong,P).absNorm:ℝ)) E H)(n : ℤ),
      n∈retainedAnnuli (Z^(xi/4))
        (naturalDualScale χ ψ (Xlong/((∏P∈Dlong,P).absNorm:ℝ)) E H) hY →
      ∀x∈Set.Icc 0 (max 0 (s.width-Real.logb Z
        (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z),
      length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
        s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+epsilon+xi := by
  let C : ℝ := ((fixedConductorFactor:ℝ)+1)*bΦ
  have hC : 0<C := mul_pos (by positivity) hbΦ
  filter_upwards [eventually_natural_choice_range C xi hC hxi,
    eventually_actual_deleted_growth b epsilon hb hepsilon] with Z hZ hgrowth
  refine ⟨hZ.1,?_⟩
  intro Bmask s z hz
  dsimp only
  intro ψ hcap Xshort Xlong hshort hlong hsupport Dshort Dlong hDs hDl E hE H hY n hn x hx
  have hm : ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤C*Z^s.width := by
    apply (effective_character_cap s hbΦ.le z hz).trans
    dsimp only [C]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hbΦ.le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  have hL : 0<Xlong/((∏P∈Dlong,P).absNorm:ℝ) :=
    div_pos (hshort.trans_le hlong) (zero_lt_one.trans_le (divisor_norm s Dlong hDl).1)
  have hexp : Z^(Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ)))=
      Xlong/((∏P∈Dlong,P).absNorm:ℝ) :=
    Real.rpow_logb (zero_lt_one.trans hZ.1) hZ.1.ne' hL
  have hrange := hZ.2 (naturalCharacter s.character z) ψ s.width
    (Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))) hcap hm E hE H
  rw [hexp] at hrange
  have hlive := hrange hY n hn
  exact hgrowth.2 Bmask bΦ s xi Xshort Xlong hshort hlong hsupport
    Dshort Dlong hDs hDl hlive x hx

end SevenEighths.CenteredMomentEnergyZeroReflectionSupport

end

end OAI

end Source2210

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthMoments.lean; sha256: 4f5db79000f1b3568605d7cbd45024604c946f54280fa1c6c31835f22ee49515 -/
section Source2211
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthMoments
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentEnergyZeroGrowthChild CenteredMomentEnergyReferenceLowControl
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem reflected_uniform (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
    ∀(bΦ Bmask L Mcap ε Z:ℝ)(Q:Ideal O)(degree:ℕ)(C:ℝ),0≤C →
    ZeroGrowthAt Q a b bΦ Bmask L Mcap ε Z degree S C → 0≤Bmask →
    ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → s.width≤Mcap →
    ∀(Wshort:𝓢(ℝ,ℂ))(_hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
      (j k:Fin 2)(v t X₁ X₂:ℝ),0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(max s.width (length Z X₁+length Z X₂)+ε))*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_child_control a b ha hlo hhi S 0
  refine ⟨n,T,D,hD,?_⟩
  intro bΦ Bmask L Mcap ε Z Q degree C hC hlow hB s hQ hs
    Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hh:=reflected_from_growth a b bΦ Bmask L Mcap ε Z Q degree S C hlow hB ha hlo hhi
    s hQ hs Wshort hsW j k v t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hb:=hd Wshort hsW j k v t 0 (le_refl 0)
  simp only [add_zero,zero_add,pow_zero,mul_one] at hb
  have hp:0≤C*diagonalControl s.radial.profile:=mul_nonneg hC (by
    unfold diagonalControl
    positivity)
  have hz:0≤Z^(max s.width (length Z X₁+length Z X₂)+ε):=(Real.rpow_pos_of_pos (zero_lt_one.trans_le s.base_ge_one) _).le
  have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hz
  apply hh.trans
  convert hmul using 1 ; ring

lemma actual_growth_power (Z b M xi epsilon loss Xshort Xlong Nshort Nlong x:ℝ)
    (hZ:1<Z)(hb:0<b)(hM:0≤M)(he:0≤epsilon)(hxi:0≤xi)
    (hshort:0<Xshort)(hlong:Xshort≤Xlong)(hNs:1≤Nshort)(hNl:1≤Nlong)
    (hsupport:1≤b*Xlong)(hdef:Real.logb Z (max 1 b)≤epsilon)
    (hlive:0≤M-Real.logb Z (Xlong/Nlong)+xi)
    (hx:x∈Set.Icc 0 (max 0 (M-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)):
    Z^(max M (length Z (Real.exp x)+length Z (Xshort/Nshort))+loss)≤
      Nlong*Z^(M+loss+epsilon+xi):=by
  have hg:=live_deleted_growth Z b M xi Xshort Xlong Nshort Nlong
    hZ hb hM hshort hlong hNs hNl hsupport hlive x hx
  have hN:=Real.logb_nonneg hZ hNl
  have hemax:max M (length Z (Real.exp x)+length Z (Xshort/Nshort))≤
      M+Real.logb Z Nlong+epsilon+xi:=max_le (by linarith) (by linarith)
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le (show max M (length Z (Real.exp x)+length Z (Xshort/Nshort))+loss≤M+Real.logb Z Nlong+epsilon+xi+loss by linarith)
  apply hp.trans_eq
  rw [show M+Real.logb Z Nlong+epsilon+xi+loss=
    Real.logb Z Nlong+(M+loss+epsilon+xi) by ring,
    Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (zero_lt_one.trans_le hNl)]

end SevenEighths.CenteredMomentEnergyZeroGrowthMoments

end

end OAI

end Source2211

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthWindow.lean; sha256: 540ee099abfbf2550247d7fa1eafe8df4b05c9fba18e2ef412380910f3a21cc3 -/
section Source2212
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroGrowthWindow
open CenteredMomentFiniteProfileExceptional
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthMoments CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceLowWindow CenteredMomentEnergyReferenceLowBranchGeometry
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

theorem actual_reflected_window (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
    ∀(bΦ Bmask L Mcap loss Z:ℝ)(Q:Ideal O)(degree:ℕ)(C:ℝ),0≤C→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S C→0≤Bmask→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
    ∀(Wshort:𝓢(ℝ,ℂ)),Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀xi epsilon Xshort Xlong:ℝ,0≤xi→0≤epsilon→1<Z→
    Real.logb Z (max 1 b)≤epsilon→Mcap+Bmask+epsilon+xi≤L→
    0<Xshort→Xshort≤Xlong→Xshort≤Z^L→1≤b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CompletedGauss.primeSupport s.puncture).powerset→
    Dlong∈(CompletedGauss.primeSupport s.puncture).powerset→
    let Nshort:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nlong:ℝ:=(∏P∈Dlong,P).absNorm;
    0≤s.width-Real.logb Z (Xlong/Nlong)+xi→
    ∀(j k:Fin 2)(v t x:ℝ),
    x∈Set.Icc 0 (max 0 (s.width-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)→
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) (Xshort/Nshort) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|)^(2*n)*Z^(s.width+loss+epsilon+xi)*Nlong)*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hu⟩:=reflected_uniform a b ha hlo hhi S
  refine ⟨n,T,D,hD,?_⟩
  intro bΦ Bmask L Mcap loss Z Q degree C hC hgrowth hB s hQ hs Wshort hsW
    xi epsilon Xshort Xlong hxi he hZ hdef hL hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive j k v t x hx
  obtain ⟨hNs,hNscap⟩:=divisor_norm s Dshort hDs
  obtain ⟨hNl,hNlcap⟩:=divisor_norm s Dlong hDl
  have hpS:0<((∏P∈Dshort,P).absNorm:ℝ):=zero_lt_one.trans_le hNs
  have hpL:0<((∏P∈Dlong,P).absNorm:ℝ):=zero_lt_one.trans_le hNl
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ hpL).mpr hNlcap
  have hlen:=live_deleted_growth Z b s.width xi Xshort Xlong _ _ hZ (by linarith)
    s.width_nonneg hshort hlong hNs hNl hsupport hlive x hx
  have hn:=length_nonneg Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ)) hZ
  have hlenx:length Z (Real.exp x)≤L:=by linarith
  have hlogx:Real.logb Z (Real.exp x)≤length Z (Real.exp x):=by
    rw [length_eq_max_log Z _ hZ (Real.exp_pos _)]
    exact le_max_right _ _
  have hxc:Real.exp x≤Z^L:=(Real.logb_le_iff_le_rpow hZ (Real.exp_pos _)).mp (hlogx.trans hlenx)
  have hsc:Xshort/((∏P∈Dshort,P).absNorm:ℝ)≤Z^L:=
    (div_le_self hshort.le hNs).trans hshortcap
  have hh:=hu bΦ Bmask L Mcap loss Z Q degree C hC hgrowth hB s hQ hs Wshort hsW
    j k v t (Real.exp x) (Xshort/((∏P∈Dshort,P).absNorm:ℝ))
    (Real.exp_pos _) (div_pos hshort hpS) hxc hsc
  have hp:=actual_growth_power Z b s.width xi epsilon loss Xshort Xlong _ _ x
    hZ (by linarith) s.width_nonneg he hxi hshort hlong hNs hNl hsupport hdef hlive hx
  have hcoef:0≤C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*(1+|t|)^(2*n):=by
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  apply hh.trans
  have hbnd:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hcoef)
    (show 0≤(1+‖v‖)^(2*n) by positivity)
  convert hbnd using 1 ; ring
end SevenEighths.CenteredMomentEnergyZeroGrowthWindow

end

end OAI

end Source2212

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthReflection.lean; sha256: 3eee5420a6e48fcd6d2aa3771986d6985af0b75b37dc707983adf1cb683bc0d2 -/
section Source2213
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthReflection
open CenteredMomentNaturalRowSource
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthWindow CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

theorem live_deleted_reflection (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hepsilon:0<epsilon)(hxi:0<xi)(hdefect:0<defect)
    (B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤Bmask→
    Mcap+Bmask+defect+xi≤L→Mcap+Bmask+defect≤Lreflect→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
    ∀Wlong Wshort:𝓢(ℝ,ℂ),Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b→
    Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀t Xshort Xlong:ℝ,0<Xshort→Xshort≤Xlong→Xshort≤Z^L→1≤b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CompletedGauss.primeSupport s.puncture).powerset→
    Dlong∈(CompletedGauss.primeSupport s.puncture).powerset→
    let Ns:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nl:ℝ:=(∏P∈Dlong,P).absNorm;
    let along:=Real.logb Z (Xlong/Nl);
    0≤s.width-along+xi→
    let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*Nl;
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Xlong/Nl) 0 t*
      polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
        (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E+
      D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
          (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨n,T,Dchild,hDc,hchild⟩:=actual_reflected_window a b ha hlo hhi S
  obtain ⟨nlong,Slong,C,D,hC,hD,href⟩:=natural_reference_reflection_homogeneous
    a b bΦ epsilon xi saving Lreflect ha (by linarith) hbΦ hepsilon hxi B n hB
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href,eventually_endpoint_defect b defect hdefect] with Z hZ hendpoint
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive
  have hz:=zero_lt_one.trans hZ.1
  obtain ⟨hNs,hNscap⟩:=divisor_norm s Dshort hDs
  obtain ⟨hNl,hNlcap⟩:=divisor_norm s Dlong hDl
  have hpS:=zero_lt_one.trans_le hNs
  have hpL:=zero_lt_one.trans_le hNl
  have hxl:=hshort.trans_le hlong
  have hlogs:=deleted_short_length Z b Xlong Xlong 1 hZ.1 (by linarith) hxl le_rfl le_rfl hsupport
  simp only [div_one] at hlogs
  have hn:=length_nonneg Z Xlong hZ.1
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ.1 hpL).mpr hNlcap
  have hlength:s.width≤Lreflect+Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ)):=by
    rw [Real.logb_div hxl.ne' hpL.ne']
    linarith [hendpoint.2]
  have hpowL:=Real.rpow_logb hz hZ.1.ne' (div_pos hxl hpL)
  have hpowS:=Real.rpow_logb hz hZ.1.ne' (div_pos hshort hpS)
  let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*((∏P∈Dlong,P).absNorm:ℝ)
  have hh:=hZ.2 Bmask s Wlong Wshort hsLong hsShort (Fin 0) ∅
    (fun _=>∅) (fun _ _=>0) (fun _=>1) t
    (Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ)))
    (Real.logb Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))) E hlength
  simp only [Finset.prod_empty,mul_one,hpowL,hpowS] at hh
  apply hh
  · dsimp [E]
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  · intro v j k x hx
    exact hchild bΦ Bmask L Mcap loss Z Q degree K hK hgrowth hBmask s hQ hs Wshort hsShort
      xi defect Xshort Xlong hxi.le hdefect.le hZ.1 hendpoint.2 hL
      hshort hlong hshortcap hsupport Dshort Dlong hDs hDl hlive j k v t x hx
end SevenEighths.CenteredMomentEnergyZeroGrowthReflection

end

end OAI

end Source2213

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthBounds.lean; sha256: a6e0553b2bdf0b4bf2f95936151da48b18f2fd4f0fe6b7f61adf921dd74aa769 -/
section Source2214
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthBounds
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyZeroReferenceError CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource
open CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

lemma actual_window_cap (Z b Bmask bΦ Mcap defect xi L Xlong:ℝ)
    (hZ:1<Z)(hb:0<b)(hx:0<Xlong)(hsupport:1≤b*Xlong)
    (hdefect:Real.logb Z (max 1 b)≤defect)
    (hL:Mcap+Bmask+defect+xi≤L)(hL0:0≤L)
    (s:NaturalState Z Bmask bΦ)(hs:s.width≤Mcap)
    (Dlong:Finset (Ideal O))(hDl:Dlong∈(CompletedGauss.primeSupport s.puncture).powerset):
    max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)≤L:=by
  obtain ⟨hn,hncap⟩:=divisor_norm s Dlong hDl
  have hnp:0<((∏P∈Dlong,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hlogN:Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ hnp).mpr hncap
  have hlow:=deleted_short_length Z b Xlong Xlong 1 hZ hb hx le_rfl le_rfl hsupport
  simp only [div_one] at hlow
  have hnon:=CenteredMomentEnergyBands.length_nonneg Z Xlong hZ
  apply max_le hL0
  rw [Real.logb_div hx.ne' hnp.ne']
  linarith

theorem actual_deleted_short_mass (b:ℝ):
    ∃C:ℝ,0<C ∧ ∀(Z Bmask bΦ L:ℝ)(s:NaturalState Z Bmask bΦ)
      (W:𝓢(ℝ,ℂ)),Function.support (W:ℝ→ℂ)⊆Set.Iic b→
      ∀t X:ℝ,0<X→X≤Z^L→
      ∀D:Finset (Ideal O),D∈(CompletedGauss.primeSupport s.puncture).powerset→
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W
        (X/((∏P∈D,P).absNorm:ℝ)) 0 t)
        (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl s.radial.profile*max 1 s.radial.scale*Z^L:=by
  obtain ⟨C,hC,hbound⟩:=short_energy_bound b
  refine ⟨C,hC,?_⟩
  intro Z Bmask bΦ L s W hW t X hX hcap D hD
  obtain ⟨hn,_⟩:=divisor_norm s D hD
  have hnp:0<((∏P∈D,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hh:=hbound W hW (naturalCharacter s.character) t
    (X/((∏P∈D,P).absNorm:ℝ)) s.radial.scale s.radial.profile
    (effectiveState s).radial.keep (div_pos hX hnp) s.radial.scale_pos s.radial.nonneg
  apply hh.trans
  apply mul_le_mul_of_nonneg_left ((div_le_self hX.le hn).trans hcap)
  exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _))
    (diagonalControl_nonneg _)) (le_max_of_le_left zero_le_one)

end SevenEighths.CenteredMomentEnergyZeroGrowthBounds

end

end OAI

end Source2214

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthBounded.lean; sha256: 05b36f928d8da81147df0a0b1f8f92f2c48982079db240dc6458148246fdefb4 -/
section Source2215
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthBounded
open CenteredMomentNaturalRowSource
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthWindow CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyZeroGrowthReflection CenteredMomentEnergyZeroGrowthBounds

theorem live_deleted_bounded (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hepsilon:0<epsilon)(hxi:0<xi)(hdefect:0<defect)
    (B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤Bmask→
    Mcap+Bmask+defect+xi≤L→Mcap+Bmask+defect≤Lreflect→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
    ∀Wlong Wshort:𝓢(ℝ,ℂ),Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b→
    Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀t Xshort Xlong:ℝ,0<Xshort→Xshort≤Xlong→Xshort≤Z^L→1≤b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CompletedGauss.primeSupport s.puncture).powerset→
    Dlong∈(CompletedGauss.primeSupport s.puncture).powerset→
    let Ns:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nl:ℝ:=(∏P∈Dlong,P).absNorm;
    let along:=Real.logb Z (Xlong/Nl);
    0≤s.width-along+xi→
    let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*Nl;
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Xlong/Nl) 0 t*
      polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
        (1+2*(L*Real.log Z))*E+
      D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*
          diagonalControl s.radial.profile*max 1 s.radial.scale*Z^L :=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=live_deleted_reflection
    a b bΦ epsilon xi defect saving Lreflect ha hlo hhi hbΦ hepsilon hxi hdefect B hB S
  obtain ⟨Cshort,hCs,hshortmass⟩:=actual_deleted_short_mass b
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Cshort,hC,mul_pos hD hCs,?_⟩
  filter_upwards [href,eventually_endpoint_defect b defect hdefect] with Z hZ hendpoint
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl
  dsimp only
  intro hlive
  have hh:=hZ.2 Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
    s hQ hs Wlong Wshort hsLong hsShort t Xshort Xlong hshort hlong hshortcap hsupport Dshort Dlong hDs hDl hlive
  have hL0:0≤L:=by linarith [s.width_nonneg]
  have hw:=actual_window_cap Z b Bmask bΦ Mcap defect xi L Xlong hZ.1 (by linarith)
    (hshort.trans_le hlong) hsupport hendpoint.2 hL hL0 s hs Dlong hDl
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hwindow:1+2*(max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z)
      ≤1+2*(L*Real.log Z):=by nlinarith
  have hmass:=hshortmass Z Bmask bΦ L s Wshort (fun x hx=>(hsShort hx).2)
    t Xshort hshort hshortcap Dshort hDs
  have hd:=diagonalControl_nonneg s.radial.profile
  have hN:0≤((∏P∈Dlong,P).absNorm:ℝ):=Nat.cast_nonneg _
  have hZ0:0<Z:=zero_lt_one.trans hZ.1
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hwindow (by positivity)
    · positivity
  · have he:=mul_le_mul_of_nonneg_left hmass
      (show 0≤D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving) by positivity)
    convert he using 1 ; ring

end SevenEighths.CenteredMomentEnergyZeroGrowthBounded

end

end OAI

end Source2215

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroRetainedError.lean; sha256: e8072035aa11a39c3bd35424c14a6ec8efc0751a9f5e1b3b2bf1e688e3a1c3ae -/
section Source2216
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroRetainedError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentNaturalPrimitive CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyZeroReflectionSupport CenteredMomentOriginalRadialComparison
open CenteredMomentRadialPolynomialEnergy CenteredMomentEnergyState
open CenteredMomentEnergyReferenceState CenteredMomentAllocatedNaturalRadial
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentEnergyReferenceReflection
local notation "O" => HeckeFamily.O

theorem finite_original_error (xi saving Cscale epsilon : ℝ)
    (hxi : 0<xi)(hscale : 0<Cscale)(hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
      ∀{ι : Type}[Fintype ι],∀χ : ι→Character,(∀i,(χ i).residue≠1) →
      ∃ψ : ι→Character,
        (∀i,FiniteFourier.IsPrimitiveOnIdeals (ψ i).residue ∧ (ψ i).residue≠1 ∧
          (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) ∧
      ∀(G : ι→𝓢(ℝ,ℂ))(P : ι→ℂ)(Z M along Src Rcap : ℝ),Z₀≤Z →
        M+xi<along → 0<Src → 1≤Rcap →
        (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤Src) →
        (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
        (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
        (∀i,retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))=0) ∧
        (∑i,‖polynomial (χ i) false (G i) (Z^along) 0 0*P i‖^2)≤
          C*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨H,C,hC,happrox⟩:=CenteredMomentUniformOriginalEnergy.actual_original_energy_to_retained
    (xi/2) saving 0 Cscale epsilon (by positivity) hscale hepsilon
  obtain ⟨Z₁,hZ₁⟩:=eventually_atTop.mp (eventually_natural_source_zero Cscale xi hscale hxi)
  refine ⟨H,C,max 2 Z₁,hC,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro ι _ χ hχ
  obtain ⟨ψ,hψ,henergy⟩:=happrox χ hχ
  refine ⟨ψ,hψ,?_⟩
  intro G P Z M along Src Rcap hZ₀ hfar hSrc hR hGS hmod hcap
  have hZ:=hZ₁ Z ((le_max_right _ _).trans hZ₀)
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hzero(i:ι):retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))=0:=
    (hZ.2 (χ i) (ψ i) M along (hψ i).2.2 (hmod i) hfar).2.2.2 (G i)
  have hsource(i:ι):((χ i).modulus.absNorm:ℝ)≤Cscale*Z^(0:ℝ)*Z^along:=by
    simp only [Real.rpow_zero,mul_one]
    exact (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith)) hscale.le)
  have hh:=henergy G (fun _=>Z^along) P Src Z Rcap hSrc hZ.1.le hR
    (fun _=>Real.rpow_pos_of_pos hz _) hGS hcap hsource
  rw [show (xi/2)/2=xi/4 by ring] at hh
  simp only [hzero,zero_mul,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,
    mul_zero,zero_add] at hh
  exact ⟨hzero,hh⟩

theorem radial_original_error (xi saving Cscale epsilon : ℝ)
    (hxi : 0<xi)(hscale : 0<Cscale)(hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
      ∀(G:O→𝓢(ℝ,ℂ))(χ:O→Character)(P:O→ℂ)(omega:O→ℝ)
        (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K Pbound:ℝ)(Wshort:ℝ→ℂ)
        (c d Z M along Xshort Src Rcap:ℝ),
      Z₀≤Z → 0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀z,‖P z‖≤Pbound) → (∀z,keep z → (χ z).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → 0<Xshort →
      M+xi<along → 0<Src → 1≤Rcap →
      (∀z,keep z → H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G z)≤Src) →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Rcap) →
      radialEnergy (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) keep Φ K≤
        C*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) keep Φ K := by
  obtain ⟨H,C,Z₀,hC,hZ₀,hfinite⟩:=finite_original_error xi saving Cscale epsilon hxi hscale hepsilon
  refine ⟨H,C,Z₀,hC,hZ₀,?_⟩
  intro G χ P omega keep Φ K Pbound Wshort c d Z M along Xshort Src Rcap
    hZ hK hΦ hP hχ hd hshort hXshort hfar hSrc hR hGS hmod hcap
  have hz:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hshortsum:=single_radial_summable χ P omega Wshort c d Xshort Pbound hd hXshort
    hshort hP keep Φ K hK
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  have hmem(z:↥S):keep (z:O):=(Finset.mem_filter.mp z.property).2
  obtain ⟨ψ,hψ,hf⟩:=hfinite (fun z:↥S=>χ z) (fun z=>hχ z (hmem z))
  let Q(z:↥S):ℂ:=
    (polynomial (χ z) false Wshort Xshort 0 (omega z)*P z)*
      (Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hh:=(hf (fun z:↥S=>G z) Q Z M along Src Rcap hZ hfar hSrc hR
    (fun z=>hGS z (hmem z)) (fun z=>hmod z (hmem z)) (fun z=>hcap z (hmem z))).2
  simp only [Q,←mul_assoc] at hh
  rw [finite_weighted rows keep
      (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) Φ K hΦ,
    finite_weighted rows keep
      (fun z=>polynomial (χ z) false Wshort Xshort 0 (omega z)*P z) Φ K hΦ] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (hshortsum.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl))
    (by positivity))

theorem natural_polynomials_summable {Z Bmask bΦ:ℝ}(state:NaturalState Z Bmask bΦ)
    (Wlong Wshort:𝓢(ℝ,ℂ))(a b Xlong Xshort t omega:ℝ)
    (hb:0≤b)(hXlong:0<Xlong)(hXshort:0<Xshort)
    (hsLong:Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b)
    (hsShort:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b):
    Summable (fun z:O=>if (effectiveState state).radial.keep z then
      ‖polynomial (naturalCharacter state.character z) false Wlong Xlong 0 t*
        polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega‖^2*
        (state.radial.profile (‖eisEmbedding z‖^2/state.radial.scale)).re else 0) ∧
    Summable (fun z:O=>if (effectiveState state).radial.keep z then
      ‖polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega‖^2*
        (state.radial.profile (‖eisEmbedding z‖^2/state.radial.scale)).re else 0):=by
  constructor
  · simpa only [mul_one] using pair_radial_summable (naturalCharacter state.character)
      (fun _=>1) (fun _=>t) (fun _=>omega) Wlong Wshort a b a b Xlong Xshort 1
      hb hb hXlong hXshort hsLong hsShort (fun _=>by simp)
      (effectiveState state).radial.keep state.radial.profile state.radial.scale state.radial.scale_pos
  · simpa only [mul_one] using single_radial_summable (naturalCharacter state.character)
      (fun _=>1) (fun _=>omega) Wshort a b Xshort 1 hb hXshort hsShort (fun _=>by simp)
      (effectiveState state).radial.keep state.radial.profile state.radial.scale state.radial.scale_pos

theorem natural_original_error (a b bΦ epsilon xi saving:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask:ℝ)(state:NaturalState Z Bmask bΦ)(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(t omega along Xshort:ℝ),0<Xshort → state.width+xi<along →
      radialEnergy (fun z=>polynomial (naturalCharacter state.character z) false Wlong
          (Z^along) 0 t*polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega)
        (effectiveState state).radial.keep state.radial.profile state.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^state.width))^(2*epsilon)*
        (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
        radialEnergy (fun z=>polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega)
          (effectiveState state).radial.keep state.radial.profile state.radial.scale:=by
  obtain ⟨H,C,Z₀,hC,hZ₀,hr⟩:=radial_original_error xi saving
    ((fixedConductorFactor:ℝ)*bΦ) epsilon hxi (mul_pos conductorFactor_pos hbΦ) hepsilon
  obtain ⟨n,T,Ct,hCt,hprofile⟩:=normPowerProfile_source_control a b ha H
  let S:=T∪{(0,0)}
  have hS:(0,0)∈S:=by simp [S]
  refine ⟨n,S,C*Ct^2,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop Z₀] with Z hZ
  have hz:1<Z:=hZ₀.trans_le hZ
  refine ⟨hz,?_⟩
  intro Bmask state Wlong Wshort hsLong hsShort t omega along Xshort hXshort hfar
  by_cases hzero:sourceControl S Wlong=0
  · have hw:=sourceControl_zero S hS Wlong hzero
    subst Wlong
    simp [polynomial,summand,radialEnergy]
  have hpos:0<sourceControl S Wlong:=lt_of_le_of_ne (sourceControl_nonneg S Wlong) (Ne.symm hzero)
  let G:=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t
  let Src:=Ct*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)*(1+‖t‖)^n
  have hSrc:0<Src:=mul_pos (mul_pos hCt hpos) (by positivity)
  have hcontrol:sourceControl T Wlong≤sourceControl S Wlong:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left:T⊆T∪{(0,0)})) Wlong
  have hnorm:H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤Src:=
    (hprofile Wlong hsLong t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcontrol hCt.le) (by positivity))
  have hh:=hr (fun _=>G) (naturalCharacter state.character) (fun _=>1) (fun _=>omega)
    (effectiveState state).radial.keep state.radial.profile state.radial.scale 1
    Wshort a b Z state.width along Xshort Src
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^state.width)) hZ state.radial.scale_pos
    state.radial.nonneg (fun _=>by simp) (effective_character_nonprincipal state)
    hb hsShort hXshort hfar hSrc (le_max_left _ _) (fun _ _=>hnorm)
    (effective_character_cap state hbΦ.le)
    (fun z hz=>(effective_character_cap state hbΦ.le z hz).trans (le_max_right _ _))
  have hG:(G:ℝ→ℂ)=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t:=rfl
  simp only [hG,CenteredMomentNaturalMaskedFloor.twist_polynomial _ Wlong a b ha hsLong t,mul_one] at hh
  apply hh.trans_eq
  dsimp only [Src]
  rw [show (1+‖t‖)^(2*n)=((1+‖t‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

theorem short_radial_mass (χ:O→Character)(W:𝓢(ℝ,ℂ))(a b X:ℝ)
    (hb:0≤b)(hX:0<X)(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (omega:O→ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K):
    radialEnergy (fun z=>polynomial (χ z) false W X 0 (omega z)) keep Φ K≤
      (128*max 1 b)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
        QuadraticInitialBound.diagonalControl Φ*max 1 K*X:=by
  let A:=((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)
  let V:=(128*max 1 b*A)^2*X
  have hV:0≤V:=by dsimp [V];positivity
  have hp(z:O):‖polynomial (χ z) false W X 0 (omega z)‖^2≤V:=by
    have hh:=pow_le_pow_left₀ (norm_nonneg _)
      (CenteredMomentOriginalReflectionErrorMass.plain_polynomial_bound (χ z) W b A X (omega z)
        (apply_nonneg _ _) hX (SchwartzMap.norm_le_seminorm ℝ W) (fun y hy=>(hs hy).2)) 2
    simpa only [mul_pow,Real.sq_sqrt hX.le,V] using hh
  have hsum:=single_radial_summable χ (fun _=>1) omega W a b X 1 hb hX hs
    (fun _=>by simp) keep Φ K hK
  simp only [mul_one] at hsum
  have hweight:=CenteredMomentAbsoluteEnergy.radial_norm_summable Φ K hK
  have hh:radialEnergy (fun z=>polynomial (χ z) false W X 0 (omega z)) keep Φ K≤
      (∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖)*V:=by
    rw [←tsum_mul_right]
    apply hsum.tsum_le_tsum _ (hweight.mul_right V)
    intro z
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right (hp z) (norm_nonneg _)).trans_eq (mul_comm _ _))
    · exact mul_nonneg (norm_nonneg _) hV
  apply (hh.trans (mul_le_mul_of_nonneg_right
    (CenteredMomentAbsoluteEnergy.radial_weight_lattice_bound_all Φ K hK) hV)).trans_eq
  dsimp [V,A]
  ring

theorem natural_original_error_mass (a b bΦ epsilon xi saving:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask:ℝ)(state:NaturalState Z Bmask bΦ)(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(t omega along Xshort:ℝ),0<Xshort → state.width+xi<along →
      radialEnergy (fun z=>polynomial (naturalCharacter state.character z) false Wlong
          (Z^along) 0 t*polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega)
        state.radial.keep state.radial.profile state.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^state.width))^(2*epsilon)*
        (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
        QuadraticInitialBound.diagonalControl state.radial.profile*max 1 state.radial.scale*Xshort:=by
  obtain ⟨n,S,C,hC,h⟩:=natural_original_error a b bΦ epsilon xi saving ha hb hbΦ hepsilon hxi
  refine ⟨n,S,C*(128*max 1 b)^2,by positivity,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask state Wlong Wshort hsLong hsShort t omega along Xshort hXshort hfar
  have hh:=hZ.2 Bmask state Wlong Wshort hsLong hsShort t omega along Xshort hXshort hfar
  have he(f:O→ℂ):radialEnergy f (effectiveState state).radial.keep
      state.radial.profile state.radial.scale=
      radialEnergy f state.radial.keep state.radial.profile state.radial.scale:=
    radialEnergy_effective state.radial f
  rw [he,he] at hh
  have hm:=short_radial_mass (naturalCharacter state.character) Wshort a b Xshort
    hb hXshort hsShort (fun _=>omega) state.radial.keep state.radial.profile
    state.radial.scale state.radial.scale_pos
  have hz:0<Z:=zero_lt_one.trans hZ.1
  apply (hh.trans (mul_le_mul_of_nonneg_left hm (by positivity))).trans_eq
  ring

end SevenEighths.CenteredMomentEnergyZeroRetainedError

end

end OAI

end Source2216

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthOriginal.lean; sha256: 1fea2597f9544591eb9c41eb088ed380efec3d32027cf911b97f3a2c55f4e11a -/
section Source2217
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthOriginal
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroGrowthBounded CenteredMomentEnergyZeroRetainedError
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceDeletionEnergy CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentInductionEnergy CenteredMomentEnergyLiveClippingDefect CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O

def swapProfiles {a b:ℝ}(p:Profiles a b):Profiles a b where
  profile := ![p.profile 1,p.profile 0]
  support := by
    intro i
    fin_cases i
    · simpa using p.support 1
    · simpa using p.support 0

lemma swapProfiles_control {a b:ℝ}(p:Profiles a b)(U:Finset (ℕ×ℕ)):
    (swapProfiles p).control U=p.control U:=by
  simp [swapProfiles,Profiles.control,mul_comm]

lemma plainEnergy_swap {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (p:Profiles a b)(t X₁ X₂:ℝ):
    s.plainEnergy (swapProfiles p) t X₂ X₁=s.plainEnergy p t X₁ X₂:=by
  unfold NaturalState.plainEnergy energy
  apply tsum_congr
  intro z
  have hh:positiveSlotRow s.character s.mask 1 z ((swapProfiles p).profile 0)
      ((swapProfiles p).profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      t X₂ X₁=positiveSlotRow s.character s.mask 1 z (p.profile 0) (p.profile 1)
      (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) t X₁ X₂:=by
    simp only [swapProfiles,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    unfold positiveSlotRow
    rw [mul_comm X₂ X₁]
    ring
  rw [hh]

theorem original_from_growth (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hepsilon:0<epsilon)(hxi:0<xi)(hdefect:0<defect)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
      ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤Bmask→
      Mcap+Bmask+defect+xi≤L→Mcap+Bmask+defect≤Lreflect→
      ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
      s.plainEnergy p t X₁ X₂≤
        C*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
          (s.puncture.radical.absNorm:ℝ)^epsilon*
          ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
            (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi)+
           (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
            Z^(-2*saving)*max 1 s.radial.scale*Z^L):=by
  obtain ⟨n,T,Dchild,hDc,nlive,Slive,Clive,Dlive,hCl,hDl,hlive⟩:=
    live_deleted_bounded a b bΦ epsilon xi defect saving Lreflect
      ha hlo hhi hbΦ hepsilon hxi hdefect 2 (by norm_num) S
  obtain ⟨ndead,Sdead,Cdead,hCd,hdead⟩:=natural_original_error_mass
    a b bΦ epsilon xi saving ha (by linarith only [hlo, hhi]) hbΦ hepsilon hxi
  obtain ⟨Cweight,hCw,hweight⟩:=original_energy_weighted_deletion (α:=Fin 0)
    (fun _=>0) (fun _=>0) (fun _=>le_refl 0) epsilon hepsilon
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T (Slive∪Sdead)
    0 n (nlive+ndead) Clive Dchild (Dlive+Cdead) hCl hDc (by positivity)
  refine ⟨J,U,Cweight*Cprofile,by positivity,?_⟩
  filter_upwards [hlive,hdead] with Z hZ hZd
  refine ⟨hZ.1,?_⟩
  intro Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect s hQ hs
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hL0:0≤L:=by linarith only [s.width_nonneg, hs, hBmask, hdefect, hxi, hL]
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hd:=diagonalControl_nonneg s.radial.profile
  let Rcap:=max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)
  let Pmain:=Rcap^epsilon*(1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi)
  let Perror:=Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*Z^L
  have hPm:0≤Pmain:=by dsimp only [Pmain,Rcap];positivity
  have hPe:0≤Perror:=by dsimp only [Perror,Rcap];positivity
  have hordered (p:Profiles a b)(t Xshort Xlong:ℝ)(hXs:0<Xshort)(horder:Xshort≤Xlong)
      (hcap:Xshort≤Z^L)(hsupport:1≤b*Xlong):
      s.plainEnergy p t Xshort Xlong≤
        Cweight*Cprofile*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
          (s.puncture.radical.absNorm:ℝ)^epsilon*(Pmain+Perror):=by
    have hXl:0<Xlong:=hXs.trans_le horder
    have hp:=hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t 0 (le_refl 0)
    simp only [add_zero,zero_add,pow_zero,mul_one] at hp
    let A:=Cprofile*(p.control U)^2*(1+|t|)^J
    let E:=(K+1)*diagonalControl s.radial.profile*A
    have hA:0≤A:=by dsimp only [A];positivity
    have hE:0≤E:=by dsimp only [E];positivity
    have hSl:sourceControl Slive (p.profile 1)≤sourceControl (Slive∪Sdead) (p.profile 1):=
      control_mono Finset.subset_union_left _
    have hSd:sourceControl Sdead (p.profile 1)≤sourceControl (Slive∪Sdead) (p.profile 1):=
      control_mono Finset.subset_union_right _
    have hSl0:=sourceControl_nonneg Slive (p.profile 1)
    have hSd0:=sourceControl_nonneg Sdead (p.profile 1)
    have hheight:1≤1+‖t‖:=le_add_of_nonneg_right (norm_nonneg _)
    have hnL:(1+‖t‖)^(2*nlive)≤(1+‖t‖)^(2*(nlive+ndead)):=
      pow_le_pow_right₀ hheight (by omega)
    have hnD:(1+‖t‖)^(2*ndead)≤(1+‖t‖)^(2*(nlive+ndead)):=
      pow_le_pow_right₀ hheight (by omega)
    have hmain:Clive*(sourceControl Slive (p.profile 1))^2*(1+‖t‖)^(2*nlive)*
        (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*(1+|t|)^(2*n))≤E:=by
      have hh:Clive*Dchild*(sourceControl Slive (p.profile 1))^2*(sourceControl T (p.profile 0))^2*
          (1+‖t‖)^(2*nlive)*(1+|t|)^(2*n)≤A:=by
        apply le_trans _ hp.2.1
        gcongr
      have hh':=mul_le_mul_of_nonneg_left hh (mul_nonneg hK hd)
      have he:K*diagonalControl s.radial.profile*A≤E:=by
        dsimp only [E]
        nlinarith only [mul_nonneg hd hA]
      apply le_trans _ he
      convert hh' using 1; ring
    have herrLive:Dlive*(sourceControl Slive (p.profile 1))^2*(1+‖t‖)^(2*nlive)*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl s.radial.profile≤E:=by
      have hh:Dlive*(sourceControl Slive (p.profile 1))^2*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖t‖)^(2*nlive)≤A:=by
        apply le_trans _ hp.2.2
        gcongr
        exact le_add_of_nonneg_right hCd.le
      have hh':=mul_le_mul_of_nonneg_left hh hd
      have he:diagonalControl s.radial.profile*A≤E:=by
        dsimp only [E]
        nlinarith only [mul_nonneg hK (mul_nonneg hd hA)]
      apply le_trans _ he
      convert hh' using 1; ring
    have herrDead:Cdead*(sourceControl Sdead (p.profile 1))^2*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖t‖)^(2*ndead)*
        diagonalControl s.radial.profile≤E:=by
      have hh:Cdead*(sourceControl Sdead (p.profile 1))^2*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖t‖)^(2*ndead)≤A:=by
        apply le_trans _ hp.2.2
        gcongr
        exact le_add_of_nonneg_left hDl.le
      have hh':=mul_le_mul_of_nonneg_left hh hd
      have he:diagonalControl s.radial.profile*A≤E:=by
        dsimp only [E]
        nlinarith only [mul_nonneg hK (mul_nonneg hd hA)]
      apply le_trans _ he
      convert hh' using 1; ring
    have hw:=hweight Z Bmask bΦ a b s (p.profile 0) (p.profile 1) ha (by linarith only [hlo, hhi])
      (p.support 0) (p.support 1) (fun _=>∅) (fun _ _=>0) (fun _=>1)
      t Xshort Xlong (E*(Pmain+Perror)) 1
    have hresult:s.plainEnergy p t Xshort Xlong≤
        Cweight*(s.puncture.radical.absNorm:ℝ)^epsilon*(E*(Pmain+Perror)):=by
      apply hw
      · simp
      · simp
      · simp
      · simp
      · exact hXs
      · exact hXl
      · exact mul_nonneg hE (add_nonneg hPm hPe)
      · norm_num
      · intro Ds hDs Dl hDl' I hI
        obtain ⟨hNs,_⟩:=divisor_norm s Ds hDs
        obtain ⟨hNl,_⟩:=divisor_norm s Dl hDl'
        have hpS:0<((∏P∈Ds,P).absNorm:ℝ):=zero_lt_one.trans_le hNs
        have hpL:0<((∏P∈Dl,P).absNorm:ℝ):=zero_lt_one.trans_le hNl
        have heffective (f:O→ℂ):radialEnergy f (effectiveState s).radial.keep
            s.radial.profile s.radial.scale=radialEnergy f s.radial.keep s.radial.profile s.radial.scale:=
          radialEnergy_effective s.radial f
        simp only [Finset.univ_eq_empty,Finset.empty_sdiff,Finset.prod_empty,mul_one,Real.rpow_one]
        rw [show (fun z:O=>polynomial (naturalCharacter s.character z) false (p.profile 0)
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)) 0 t*
            polynomial (naturalCharacter s.character z) false (p.profile 1)
              (Xlong/((∏P∈Dl,P).absNorm:ℝ)) 0 t)=
            (fun z:O=>polynomial (naturalCharacter s.character z) false (p.profile 1)
              (Xlong/((∏P∈Dl,P).absNorm:ℝ)) 0 t*
            polynomial (naturalCharacter s.character z) false (p.profile 0)
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)) 0 t) by funext z;exact mul_comm _ _]
        by_cases hl:0≤s.width-Real.logb Z (Xlong/((∏P∈Dl,P).absNorm:ℝ))+xi
        · have hh:=hZ.2 Bmask L Mcap loss Q degree K hK hgrowth hBmask hL hLreflect
            s hQ hs (p.profile 1) (p.profile 0) (p.support 1) (p.support 0)
            t Xshort Xlong hXs horder hcap hsupport Ds Dl hDs hDl' hl
          have hb:=add_le_add
            (mul_le_mul_of_nonneg_right hmain (mul_nonneg hPm hpL.le))
            (mul_le_mul_of_nonneg_right herrLive hPe)
          have hc:E*Pmain*((∏P∈Dl,P).absNorm:ℝ)+E*Perror≤
              E*(Pmain+Perror)*((∏P∈Dl,P).absNorm:ℝ):=by
            calc
              _ ≤ E*Pmain*((∏P∈Dl,P).absNorm:ℝ)+(E*Perror)*((∏P∈Dl,P).absNorm:ℝ) :=
                add_le_add le_rfl (le_mul_of_one_le_right (mul_nonneg hE hPe) hNl)
              _ = _ := by ring
          apply hh.trans
          calc
            _ ≤ E*Pmain*((∏P∈Dl,P).absNorm:ℝ)+E*Perror := by
              convert hb using 1 <;> dsimp only [Pmain,Perror,Rcap] <;> ring
            _ ≤ _ := hc
        · have hfar:s.width+xi<Real.logb Z (Xlong/((∏P∈Dl,P).absNorm:ℝ)):=by linarith only [hl]
          have hh:=hZd.2 Bmask s (p.profile 1) (p.profile 0) (p.support 1) (p.support 0)
            t t (Real.logb Z (Xlong/((∏P∈Dl,P).absNorm:ℝ)))
            (Xshort/((∏P∈Ds,P).absNorm:ℝ)) (div_pos hXs hpS) hfar
          rw [Real.rpow_logb hz hZ.1.ne' (div_pos hXl hpL)] at hh
          rw [heffective]
          have hshortcap:Xshort/((∏P∈Ds,P).absNorm:ℝ)≤Z^L:=
            (div_le_self hXs.le hNs).trans hcap
          have hb:=mul_le_mul_of_nonneg_right herrDead
            (show 0≤Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)) by positivity)
          have hc:E*(Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*
              (Xshort/((∏P∈Ds,P).absNorm:ℝ)))≤E*Perror:=by
            dsimp only [Perror]
            gcongr
          have hf:E*Perror≤E*(Pmain+Perror)*((∏P∈Dl,P).absNorm:ℝ):=by
            exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hPm) hE).trans
              (le_mul_of_one_le_right (mul_nonneg hE (add_nonneg hPm hPe)) hNl)
          apply hh.trans
          calc
            _ ≤ E*(Rcap^(2*epsilon)*Z^(-2*saving)*max 1 s.radial.scale*
                (Xshort/((∏P∈Ds,P).absNorm:ℝ))) := by
              convert hb using 1; dsimp only [Rcap,sourceControl]; ring
            _ ≤ E*Perror := hc
            _ ≤ _ := hf
    apply hresult.trans_eq
    dsimp only [E,A]
    ring
  intro p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  by_cases hzero:s.plainEnergy p t X₁ X₂=0
  · rw [hzero]
    positivity
  · obtain ⟨z,hz,hrow⟩:=energy_support_witness s.character s.mask 1 t
      (p.profile 0) (p.profile 1) (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      X₁ X₂ s.radial.keep s.radial.profile s.radial.scale hzero
    obtain ⟨hs₁,hs₂⟩:=positiveSlotRow_profiles_scales s.character s.mask 1 z p
      (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) t X₁ X₂ hX₁ hX₂ hrow
    by_cases horder:X₁≤X₂
    · exact hordered p t X₁ X₂ hX₁ horder hc₁ hs₂
    · have hh:=hordered (swapProfiles p) t X₂ X₁ hX₂ (le_of_not_ge horder) hc₂ hs₁
      simpa only [plainEnergy_swap,swapProfiles_control] using hh

end SevenEighths.CenteredMomentEnergyZeroGrowthOriginal

end

end OAI

end Source2217

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthConclusion.lean; sha256: 3064fea1e3b937590a97064b50d09341309052641cd96c460bae140ddc70d2b5 -/
section Source2218
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthConclusion
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O" => HeckeFamily.O

lemma profile_control_mono {a b:ℝ}(p:Profiles a b)
    {S T:Finset (ℕ×ℕ)}(hST:S⊆T):p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul
    (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

lemma zeroGrowth_mono (Q:Ideal O)(a b bΦ Bmask L L' M M' ε ε' Z:ℝ)
    (degree degree':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hL:L'≤L)(hM:M'≤M)(hε:ε≤ε')(hdegree:degree≤degree')
    (hST:S⊆T)(hC:0≤C)(hCC:C≤C')
    (h:ZeroGrowthAt Q a b bΦ Bmask L M ε Z degree S C):
    ZeroGrowthAt Q a b bΦ Bmask L' M' ε' Z degree' T C':=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hscale:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le s.base_ge_one hL
  have hh:=h s hQ (hs.trans hM) p t X₁ X₂ hX₁ hX₂
    (hc₁.trans hscale) (hc₂.trans hscale)
  have hC' : 0≤C' := hC.trans hCC
  have hp:=profile_control_mono p hST
  have hpn:=p.control_nonneg S
  have hpt:=p.control_nonneg T
  have hd:=diagonalControl_nonneg s.radial.profile
  have hheight:(1+‖t‖)^degree≤(1+‖t‖)^degree':=
    pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree
  have hpower:Z^(max s.width (length Z X₁+length Z X₂)+ε)≤
      Z^(max s.width (length Z X₁+length Z X₂)+ε'):=
    Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith)
  have hZ : 0≤Z := zero_le_one.trans s.base_ge_one
  have hfront:C*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree≤
      C'*diagonalControl s.radial.profile*(p.control T)^2*(1+‖t‖)^degree':=by
    apply mul_le_mul _ hheight (by positivity) (by positivity)
    apply mul_le_mul _ ((sq_le_sq₀ hpn hpt).mpr hp) (sq_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right hCC hd
  exact hh.trans (mul_le_mul hfront hpower (Real.rpow_nonneg hZ _) (by positivity))

lemma zeroAt_mono (Q:Ideal O)(a b bΦ Bmask L L' M M' ε ε' Z:ℝ)
    (degree degree':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hL:L'≤L)(hM:M'≤M)(hε:ε≤ε')(hdegree:degree≤degree')
    (hST:S⊆T)(hC:0≤C)(hCC:C≤C')
    (h:ZeroAt Q a b bΦ Bmask L M ε Z degree S C):
    ZeroAt Q a b bΦ Bmask L' M' ε' Z degree' T C':=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hscale:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le s.base_ge_one hL
  have hh:=h s hQ (hs.trans hM) p t X₁ X₂ hX₁ hX₂
    (hc₁.trans hscale) (hc₂.trans hscale)
  have hC' : 0≤C' := hC.trans hCC
  have hp:=profile_control_mono p hST
  have hpn:=p.control_nonneg S
  have hpt:=p.control_nonneg T
  have hd:=diagonalControl_nonneg s.radial.profile
  have hheight:(1+‖t‖)^degree≤(1+‖t‖)^degree':=
    pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree
  have hpower:Z^(s.width+ε)≤Z^(s.width+ε'):=
    Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith)
  have hZ : 0≤Z := zero_le_one.trans s.base_ge_one
  have hfront:C*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree≤
      C'*diagonalControl s.radial.profile*(p.control T)^2*(1+‖t‖)^degree':=by
    apply mul_le_mul _ hheight (by positivity) (by positivity)
    apply mul_le_mul _ ((sq_le_sq₀ hpn hpt).mpr hp) (sq_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right hCC hd
  exact hh.trans (mul_le_mul hfront hpower (Real.rpow_nonneg hZ _) (by positivity))

theorem zero_from_same_width_growth (a b bΦ ε Mcap Bmask Loriginal:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L:ℝ,0<d ∧ 0<L ∧ Loriginal≤L ∧
      ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
        ZeroGrowthAt Q a b bΦ Bmask L Mcap d Z degree S K→
        ZeroAt Q a b bΦ Bmask Loriginal Mcap ε Z J U (C*(K+1)):=by
  obtain ⟨d,L,saving,Cledger,hd,hL,hsaving,hCledger,hLoriginal,hroom,hledger⟩:=
    CenteredMomentEnergyZeroGrowthReserve.exists_growth_reserve
      ε Mcap Bmask bΦ Loriginal hε hM hB
  refine ⟨d,L,hd,hL,hLoriginal,?_⟩
  intro S
  obtain ⟨J,U,Csource,hCsource,hsource⟩:=
    CenteredMomentEnergyZeroGrowthOriginal.original_from_growth
      a b bΦ d d d saving L ha hlo hhi hbΦ hd hd hd S
  refine ⟨J,U,Csource*Cledger,mul_pos hCsource hCledger,?_⟩
  filter_upwards [hsource] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Q degree K hK hgrowth s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hscale:Z^Loriginal≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLoriginal
  have hh:=hZ.2 Bmask L Mcap d Q degree K hK hgrowth hB hroom
    (by linarith) s hQ hs p t X₁ X₂ hX₁ hX₂ (hc₁.trans hscale) (hc₂.trans hscale)
  have hl:=hledger Z hZ.1.le s hs
  have hfront:0≤Csource*(K+1)*diagonalControl s.radial.profile*
      (p.control U)^2*(1+|t|)^J:=by
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  calc
    _≤Csource*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
        (Cledger*Z^(s.width+ε)):=by
      apply hh.trans
      convert mul_le_mul_of_nonneg_left hl hfront using 1 ; ring
    _=_:=by rw [Real.norm_eq_abs];ring

end SevenEighths.CenteredMomentEnergyZeroGrowthConclusion

end

end OAI

end Source2218

/- Original source: OAI/NumberTheory/DirichletL/Energy/BackwardSourceRanges.lean; sha256: f0ce11cd963df6bfcea297294fcbb1bbe4857ee7055c7f438ad408af5e690c18 -/
section Source2219
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBackwardSourceRanges
open CenteredMomentEnergyWidthRanges CenteredMomentEnergyProfiles
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyState
open CenteredMomentNaturalRowSource CenteredMomentEnergyStageReserveBounded

def lengthAt (M B L:ℝ)(depth k:ℕ):ℝ:=range M B L (depth-k)
def lowerAt (a b:ℝ)(depth k:ℕ):ℝ:=lower a b (depth-k)

lemma previous_length (M B L:ℝ)(depth k:ℕ)(hk:k<depth):
    lengthAt M B L depth k=CenteredMomentEnergyWidthRanges.step M B
      (lengthAt M B L depth (k+1)):=by
  have hn:depth-k=(depth-(k+1))+1:=by omega
  simp only [lengthAt,hn,range]

lemma previous_lower (a b:ℝ)(depth k:ℕ)(hk:k<depth):
    lowerAt a b depth k=lowerAt a b depth (k+1)/max 1 b:=by
  have hn:depth-k=(depth-(k+1))+1:=by omega
  simp only [lowerAt,hn,lower]

lemma length_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(depth k:ℕ):
    0≤lengthAt M B L depth k:=range_nonneg M B L hM hB _

lemma original_length (M B L:ℝ)(hM:0≤M)(hB:0≤B)(depth k:ℕ):
    L≤lengthAt M B L depth k:=range_original M B L hM hB _

lemma lower_positive (a b:ℝ)(ha:0<a)(depth k:ℕ):0<lowerAt a b depth k:=
  lower_pos a b ha _

theorem profile_step_support (a b:ℝ)(ha:0<a)(depth k:ℕ)(hk:k<depth)
    (W:Test (lowerAt a b depth (k+1)) b)(U:ℝ)(hU:0<U)(t:ℝ)(j:Fin 2):
    Function.support
      ((CenteredMomentEnergyProfiles.step _ b (lower_positive a b ha depth (k+1)) W U hU t j).profile:ℝ→ℂ)
      ⊆Set.Icc (lowerAt a b depth k) b:=by
  rw [previous_lower a b depth k hk]
  exact (CenteredMomentEnergyProfiles.step _ b (lower_positive a b ha depth (k+1)) W U hU t j).support

theorem previous_admits (M B L stageCap rho d e Lref:ℝ)
    (hM:0≤M)(hB:0≤B)(hstage:stageCap≤M)(hrho:rho≤1)(hd:d≤1)(he:e≤1)
    (depth k:ℕ)(hk:k<depth)(hLref:Lref≤stageCap+B+rho/100):
    lengthAt M B L depth (k+1)≤lengthAt M B L depth k ∧
    Lref≤lengthAt M B L depth k ∧
    max (lengthAt M B L depth (k+1)) (stageCap+B+2*d)+1≤lengthAt M B L depth k ∧
    2*lengthAt M B L depth (k+1)+e≤lengthAt M B L depth k ∧
    2*(max (lengthAt M B L depth (k+1)) (stageCap+B+2*d)+1)+e≤lengthAt M B L depth k:=by
  have h:=step_admits M B (lengthAt M B L depth (k+1)) rho d e hM hB
    (length_nonneg M B L hM hB depth (k+1)) hrho hd he
  rw [previous_length M B L depth k hk]
  refine ⟨h.1,?_,?_,h.2.2.2.1,?_⟩
  · exact (show Lref≤M+B+rho/100+1 by linarith).trans h.2.1
  · have hm:max (lengthAt M B L depth (k+1)) (stageCap+B+2*d)≤
        max (lengthAt M B L depth (k+1)) (M+B+2*d):=max_le_max_left _ (by linarith)
    linarith only [hm,h.2.2.1]
  · apply le_trans _ h.2.2.2.2
    gcongr

lemma paired_contours (M B L stageCap rho L₁ L₂:ℝ)
    (hM:0≤M)(hB:0≤B)(hstage:stageCap≤M)(hrho:rho≤1)
    (depth k:ℕ)(hk:k<depth)
    (h₁:L₁≤stageCap+B+rho/100)(h₂:L₂≤stageCap+B+rho/100):
    max L₁ L₂≤lengthAt M B L depth k:=
  (previous_admits M B L stageCap rho 0 0 (max L₁ L₂) hM hB hstage hrho
    (by norm_num) (by norm_num) depth k hk (max_le h₁ h₂)).2.1

lemma source_cap_uniform (M B L:ℝ)(hM:0≤M)(hB:0≤B)(depth k:ℕ):
    sourceCap M B L (depth-k)≤sourceCap M B L depth:=by
  have h:=range_mono M B L hM hB (Nat.sub_le depth k)
  unfold sourceCap
  linarith

lemma scheduled_source_cap (M B L ε:ℝ)(hM:0≤M)(hB:0≤B)(k:ℕ):
    sourceCap M B L (count M ε-k)≤finalSourceCap M B L ε:=
  source_cap_uniform M B L hM hB _ _

theorem actual_reference_reserve_previous
    (M B L stageCap rho ε bΦ:ℝ)(hM:0≤M)(hB:0≤B)(hstage0:0≤stageCap)
    (hstage:stageCap≤M)(hrho:0<rho)(hrho1:rho≤1)(hε:0<ε)
    (depth k:ℕ)(hk:k<depth):
    ∃d xi saving Lref C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ stageCap+B+xi≤Lref ∧ Lref≤stageCap+B+rho/100 ∧
      Lref≤lengthAt M B L depth k ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState Z B bΦ,s.width≤stageCap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤stageCap →
      (s.puncture.radical.absNorm:ℝ)^d*(Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(Lref*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤C*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,Lref,C,hd,hxi,hs,hC,hxr,hL,hLu,hledger⟩:=
    exists_bounded_separated_reference_reserve rho ε stageCap B bΦ hrho hε hstage0 hB
  refine ⟨d,xi,saving,Lref,C,hd,hxi,hs,hC,hxr,hL,hLu,?_,hledger⟩
  exact (previous_admits M B L stageCap rho 0 0 Lref hM hB hstage hrho1
    (by norm_num) (by norm_num) depth k hk hLu).2.1

end SevenEighths.CenteredMomentEnergyBackwardSourceRanges

end

end OAI

end Source2219

/- Original source: OAI/NumberTheory/DirichletL/Energy/ZeroGrowthContourBounded.lean; sha256: 0465cdc54fd85344a6217c263404faf3a2fe9eb1d55ebe7099b2d3905e073cbd -/
section Source2220
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalRowSource QuadraticInitialBound
local notation "O"=>HeckeFamily.O

private lemma ledger_loss_mono (Z d ell A B P w:ℝ)(hZ:1≤Z)(hd:0≤d)(hell:0≤ell)
    (hA:0≤A)(hB:0≤B)(hP:0≤P):
    P*(A*Z^(w+ell+d+d)+B)≤Z^ell*(P*(A*Z^(w+d+d+d)+B)):=by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hp:1≤Z^ell:=Real.one_le_rpow hZ hell
  have hm:Z^(w+ell+d+d)≤Z^ell*Z^(w+d+d+d):=by
    rw [←Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _≤P*(A*(Z^ell*Z^(w+d+d+d))+Z^ell*B):=by
      apply mul_le_mul_of_nonneg_left _ hP
      exact add_le_add (mul_le_mul_of_nonneg_left hm hA)
        (le_mul_of_one_le_left hB hp)
    _=_:=by ring

theorem bounded_growth_reserve (ε Mcap Bmask bΦ Loriginal:ℝ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L saving C:ℝ,0<d ∧ d≤1 ∧ 0<L ∧ 0<saving ∧ 0<C ∧
      L=max Loriginal (Mcap+Bmask+2*d)+1 ∧ Loriginal≤L ∧
      Mcap+Bmask+d+d≤L ∧
      ∀Z:ℝ,1≤Z→∀s:NaturalState Z Bmask bΦ,s.width≤Mcap→
      (s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+d+d+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤C*Z^(s.width+ε):=by
  let d:=min 1 (ε/(8*(Bmask+Mcap+4)))
  let L:=max Loriginal (Mcap+Bmask+2*d)+1
  let saving:=L+Bmask*d+2*Mcap*d+1
  have hd:0<d:=lt_min (by norm_num) (by positivity)
  have hd1:d≤1:=min_le_left _ _
  have hdε:d*(Bmask+Mcap+4)≤ε/8:=by
    have hh: d≤ε/(8*(Bmask+Mcap+4)):=min_le_right _ _
    have he: d*(8*(Bmask+Mcap+4))≤ε:=
      (le_div_iff₀ (by positivity)).mp hh
    linarith
  have hL:0<L:=by dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+2*d)]
  have hs:0<saving:=by dsimp [saving];positivity
  have hmain:d*(Bmask+Mcap+1)+d+d+d≤ε:=by linarith
  have herr:Bmask*d+Mcap*(2*d)-2*saving+L≤ε:=by
    dsimp only [saving]
    nlinarith [mul_nonneg hB hd.le,mul_nonneg hM hd.le]
  obtain ⟨C,hC,hbound⟩:=CenteredMomentEnergyZeroGrowthReserve.ledger_bound
    Mcap Bmask bΦ L d d d d saving ε hM hB hL.le hd hmain herr
  refine ⟨d,L,saving,C,hd,hd1,hL,hs,hC,rfl,?_,?_,hbound⟩
  · dsimp only [L];linarith [le_max_left Loriginal (Mcap+Bmask+2*d)]
  · dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+2*d)]

theorem zero_from_growth_additional_loss_bounded (a b bΦ ε Mcap Bmask Loriginal:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L:ℝ,0<d ∧ d≤1 ∧ 0<L ∧ Loriginal≤L ∧
      L=max Loriginal (Mcap+Bmask+2*d)+1 ∧
      L≤max Loriginal (Mcap+Bmask+2)+1 ∧
      ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(ell:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤ell→0≤K→
        ZeroGrowthAt Q a b bΦ Bmask L Mcap ell Z degree S K→
        ZeroAt Q a b bΦ Bmask Loriginal Mcap (ell+ε) Z J U (C*(K+1)):=by
  obtain ⟨d,L,saving,Cledger,hd,hd1,hL,hsaving,hCledger,hLexact,hLoriginal,hroom,hledger⟩:=
    bounded_growth_reserve
      ε Mcap Bmask bΦ Loriginal hε hM hB
  refine ⟨d,L,hd,hd1,hL,hLoriginal,hLexact,?_,?_⟩
  · rw [hLexact]
    gcongr
    linarith only [hd1]
  intro S
  obtain ⟨J,U,Csource,hCsource,hsource⟩:=
    CenteredMomentEnergyZeroGrowthOriginal.original_from_growth
      a b bΦ d d d saving L ha hlo hhi hbΦ hd hd hd S
  refine ⟨J,U,Csource*Cledger,mul_pos hCsource hCledger,?_⟩
  filter_upwards [hsource] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ell Q degree K hell hK hgrowth s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hscale:Z^Loriginal≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLoriginal
  have hh:=hZ.2 Bmask L Mcap ell Q degree K hK hgrowth hB hroom
    (by linarith) s hQ hs p t X₁ X₂ hX₁ hX₂ (hc₁.trans hscale) (hc₂.trans hscale)
  let Rcap:=max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)
  let A:=Rcap^d*(1+2*(L*Real.log Z))
  let B:=Rcap^(2*d)*Z^(-2*saving)*max 1 s.radial.scale*Z^L
  let P:=(s.puncture.radical.absNorm:ℝ)^d
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hA:0≤A:=by dsimp [A,Rcap];positivity
  have hBb:0≤B:=by dsimp [B,Rcap];positivity
  have hP:0≤P:=by dsimp [P];positivity
  have hb:=ledger_loss_mono Z d ell A B P s.width hZ.1.le hd.le hell hA hBb hP
  have hl:=mul_le_mul_of_nonneg_left (hledger Z hZ.1.le s hs) (Real.rpow_nonneg hz.le ell)
  have htotal:P*(A*Z^(s.width+ell+d+d)+B)≤Cledger*Z^(s.width+(ell+ε)):=by
    apply hb.trans
    calc
      _≤Z^ell*(Cledger*Z^(s.width+ε)):=hl
      _=Cledger*(Z^ell*Z^(s.width+ε)):=by ring
      _=Cledger*Z^(s.width+(ell+ε)):=by rw [←Real.rpow_add hz];congr 2;ring
  have hfront:0≤Csource*(K+1)*diagonalControl s.radial.profile*
      (p.control U)^2*(1+|t|)^J:=by
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  calc
    _≤Csource*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
        (Cledger*Z^(s.width+(ell+ε))):=by
      apply hh.trans
      convert mul_le_mul_of_nonneg_left htotal hfront using 1 ; dsimp only [P,A,B,Rcap] ; ring
    _=_:=by rw [Real.norm_eq_abs];ring

end SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded

end

end OAI

end Source2220

/- Original source: OAI/NumberTheory/DirichletL/Energy/NaturalZeroStage.lean; sha256: f32ebf15c8e9faa8133cde1cdc7b7d849584cbe0847ee7127ef57a3fda1736c2 -/
section Source2221
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalZeroStage
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyStageMonotonicity CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_zero_stage
    (W:ℝ→ℂ)(aslot bslot Lslot lo hi κ a b bΦ Bmask Lgoal Mparent Mchild
      Mschedule Bschedule ε rho:ℝ)(k:ℕ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hLs:0≤Lslot)(hκ:(3/4:ℝ)≤κ)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκbeta:2*HeckeZeroSupremum.beta-1≤κ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:2≤bΦ)(hBmask:0≤Bmask)(_hLgoal:0≤Lgoal)
    (hMparent:0≤Mparent)(hMchild:0≤Mchild)(hMschedule:0≤Mschedule)(hBschedule:0≤Bschedule)
    (hε:0<ε)(hrho:0<rho)(hrhoChild:rho≤Mchild)
    (hdrop:Mparent-amplification ε/2≤Mchild):
    ∃d Lgrow Llow:ℝ,0<d ∧ d≤1 ∧ 0<Lgrow ∧ Lgoal≤Lgrow ∧
      Lgrow=max Lgoal (Mparent+Bmask+2*d)+1 ∧
      Llow=max Lgrow (Mparent+Bmask+rho/100) ∧
      Llow≤max Lgoal (Mparent+Bmask+rho/100+2)+1 ∧
    ∀Lchild:ℝ,0≤Lchild→max Mparent (2*Lgrow)≤Lchild→
      readyBudget (max Mparent (2*Lgrow)) Bmask≤Bschedule→
    ∀degree degreeLow:ℕ,∀S Slow:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀εchild C₀ C₁ Clow:ℝ,εchild≤stageLoss Mschedule Bschedule ε k→
      0≤C₀→0≤C₁→0≤Clow→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask Lchild Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask Lchild Lslot lo hi
        Mchild εchild κ Z η₀ Q degree S C₁→
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask Llow Mparent
        (physicalLoss Mschedule Bschedule ε k) Z degreeLow Slow Clow→
      ZeroAt (internalQ Q η₀) a b bΦ Bmask Lgoal Mparent
        (stageLoss Mschedule Bschedule ε (k+1)) Z J U (C*(Clow+C₀+C₁+1)):=by
  let r:=reserve Mschedule Bschedule ε
  have hκ0:0≤κ:=by linarith
  have hr:0<r:=(bounds Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε).2.2.2.1
  have hb:0≤b:=by linarith
  have hrad:0<bΦ:=by linarith
  obtain ⟨d,Lgrow,hd,hd1,hLg,hgoal,hLexact,hLupper,hsharp⟩:=
    CenteredMomentEnergyZeroGrowthContourBounded.zero_from_growth_additional_loss_bounded
      a b bΦ r Mparent Bmask Lgoal ha hlo hhi hrad hr hMparent hBmask
  let Llow:=max Lgrow (Mparent+Bmask+rho/100)
  refine ⟨d,Lgrow,Llow,hd,hd1,hLg,hgoal,hLexact,rfl,?_,?_⟩
  · apply max_le
    · apply hLupper.trans
      exact add_le_add (max_le_max (le_refl Lgoal)
        (show Mparent+Bmask+2≤Mparent+Bmask+rho/100+2 by linarith only [hrho])) (le_refl (1:ℝ))
    · have hh:=le_max_right Lgoal (Mparent+Bmask+rho/100+2)
      linarith
  intro Lchild hLc hcap hready degree degreeLow S Slow
  obtain ⟨Ψ,hsΨ,hnΨ,hgrowth⟩:=
    CenteredMomentEnergyZeroGrowthSourceControlled.actual_growth_from_physical
      a b bΦ rho r Mparent Bmask (2*Lgrow) Lgrow (r/4) (r/4) (2*amplification ε+1)
      ha hlo hhi hrad hrho hr hMparent hBmask (by positivity) le_rfl (by positivity) (by positivity)
  obtain ⟨Smass,Jmass,hphysical⟩:=
    CenteredMomentEnergyZeroGrowthPhysical.actual_growth_physical (α:=α) M H hH
      W aslot bslot Lslot lo hi κ a b bΦ Bmask Lgrow Lchild Mparent Mchild Mschedule Bschedule ε
      haslot hWs hW hLs hκ hbeta hκbeta ha hb hBmask hLg.le hLc hMparent hMchild
      hMschedule hBschedule hε hcap hready hdrop Ψ degree S
  obtain ⟨Jgrowth,Ugrowth,Cgrowth,hCg,hgrowth⟩:=hgrowth (degree+degreeLow) (S∪Slow) Jmass Smass
  obtain ⟨J,U,Csharp,hCs,hsharp⟩:=hsharp Ugrowth
  refine ⟨J,U,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cmass,hCm,Zmass,hZm,hmass⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  let C:=Csharp*(Cgrowth*(Cmass+2)+1)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_ge_atTop Zmass,hgrowth,hsharp] with Z hZmZ hg hs
  have hZ:1<Z:=hZm.trans_le hZmZ
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ Clow hchild hC₀ hC₁ hClow hz hp hl
  have hmarg:=margins Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε k
  have hpLoss:0≤physicalLoss Mschedule Bschedule ε k:=hmarg.1.le
  have hrLoss:0≤reflectedLoss Mschedule Bschedule ε k:=hpLoss.trans hmarg.2.2.2.1
  have hlength:Lgrow≤Lchild:=by linarith [le_max_right Mparent (2*Lgrow)]
  have hap:a/max 1 b≤a:=div_le_self ha.le (le_max_left _ _)
  have hzero:=zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ 2 0 _ _ _
    degree degree S S C₀ C₀ hZ.le le_rfl le_rfl hbΦ hBmask le_rfl le_rfl le_rfl
    le_rfl (Finset.Subset.refl _) hC₀ le_rfl hz
  have hpositive:=positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
    _ _ 2 0 _ _ _ η₀ Q degree degree S S C₁ C₁ hZ.le
    le_rfl le_rfl hbΦ hBmask le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₁ le_rfl hp
  have hmassNow:=hmass Z hZmZ k εchild C₀ C₁ rho hchild hC₀ hC₁ hzero hpositive
  have hprevious:=zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z a b bΦ Bmask Lgrow rho
    (reflectedLoss Mschedule Bschedule ε k) degree (degree+degreeLow) S (S∪Slow) C₀ C₀
    hZ.le hap le_rfl le_rfl le_rfl hlength hrhoChild
    (hchild.trans (hmarg.2.1.trans hmarg.2.2.2.1)) (Nat.le_add_right _ _)
    Finset.subset_union_left hC₀ le_rfl hz
  have hlow:=zeroLowAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
    degreeLow (degree+degreeLow) Slow (S∪Slow) Clow Clow hZ.le
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_add_left _ _)
    Finset.subset_union_right hClow le_rfl hl
  have hgrowthNow:=hg.2 (physicalLoss Mschedule Bschedule ε k)
    (physicalLoss Mschedule Bschedule ε k) (reflectedLoss Mschedule Bschedule ε k)
    (internalQ Q η₀) Clow (Cmass*(C₀+C₁+1)) C₀ hpLoss hClow (by positivity) hC₀
    (by unfold reflectedLoss;exact le_rfl) hmarg.2.2.2.1
    (hmarg.2.2.1.trans hmarg.2.2.2.1)
    (by have hh:= (bounds Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε).1
        linarith only [hrLoss,hh]) hprevious hlow hmassNow
  have hfinal:=hs.2 (reflectedLoss Mschedule Bschedule ε k) (internalQ Q η₀) Jgrowth
    (Cgrowth*(Clow+Cmass*(C₀+C₁+1)+C₀+1)) hrLoss (by positivity) hgrowthNow
  rw [reflected_then_zero] at hfinal
  have hfront:Csharp*(Cgrowth*(Clow+Cmass*(C₀+C₁+1)+C₀+1)+1)≤C*(Clow+C₀+C₁+1):=by
    have hinner:Clow+Cmass*(C₀+C₁+1)+C₀+1≤(Cmass+2)*(Clow+C₀+C₁+1):=by
      nlinarith [mul_nonneg hCm.le hClow]
    calc
      _≤Csharp*(Cgrowth*((Cmass+2)*(Clow+C₀+C₁+1))+(Clow+C₀+C₁+1)):=by
        gcongr
        linarith
      _=_:=by dsimp [C];ring
  exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
    J J U U _ _ hZ.le le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    le_rfl (Finset.Subset.refl _) (by positivity) hfront hfinal

end SevenEighths.CenteredMomentEnergyNaturalZeroStage

end

end OAI

end Source2221

/- Original source: OAI/NumberTheory/DirichletL/Energy/CappedSuccessorPacking.lean; sha256: 2724a7a6d99bec483ed730299e2288a6a1c6c281dae46929a53c8037f03bf43d -/
section Source2222
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedSuccessorPacking
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyStageMonotonicity CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSourceBound CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem certified_from_stages
    (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (ha:0<a)(hmask:0≤Bmask)(hMcap:0≤Mcap)(hκ:0≤κ)(hε:0<ε)(k:ℕ)
    (ez el eh:ℝ)
    (hez:ez≤stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
    (hel:el≤stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
    (heh:eh≤stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
    (hold:CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH
      W bslot a b radial Bmask L lo hi Mcap κ ε k)
    (hzero:∃J:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
        ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (lengthAt Mcap Bmask L ε (k+1))
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1)) ez Z J S C)
    (hlow:∃J:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
        PositiveLowAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (lengthAt Mcap Bmask L ε (k+1)) (fineMesh Mcap Bmask L κ ε) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1)) el κ Z η₀ Q J S C)
    (hhigh:∃J:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
        PositiveHighAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (lengthAt Mcap Bmask L ε (k+1)) (fineMesh Mcap Bmask L κ ε) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1)) eh κ Z η₀ Q J S C):
    CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH
      W bslot a b radial Bmask L lo hi Mcap κ ε (k+1):=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hr:0<reserve Mcap Bs ε:=(bounds Mcap Bs κ ε hMcap hBs hκ hε).2.2.2.1
  have hlower:lowerAt a b Mcap ε k≤lowerAt a b Mcap ε (k+1):=
    CenteredMomentEnergyProfiles.lower_antitone a b ha (by unfold remaining;omega)
  have hlength:lengthAt Mcap Bmask L ε (k+1)≤lengthAt Mcap Bmask L ε k:=
    range_mono Mcap Bmask L hMcap hmask (by unfold remaining;omega)
  have hloss:stageLoss Mcap Bs ε k≤stageLoss Mcap Bs ε (k+1):=by
    unfold stageLoss
    rw [loss_succ]
    linarith
  obtain ⟨Jold,Sold,hold⟩:=hold
  obtain ⟨Jz,Sz,hzero⟩:=hzero
  obtain ⟨Jl,Sl,hlow⟩:=hlow
  obtain ⟨Jh,Sh,hhigh⟩:=hhigh
  let J:=Jold+Jz+Jl+Jh
  let S:=Sold∪Sz∪Sl∪Sh
  have hJo:Jold≤J:=by dsimp [J];omega
  have hJz:Jz≤J:=by dsimp [J];omega
  have hJl:Jl≤J:=by dsimp [J];omega
  have hJh:Jh≤J:=by dsimp [J];omega
  have hSo:Sold⊆S:=by intro x hx;simp [S,hx]
  have hSz:Sz⊆S:=by intro x hx;simp [S,hx]
  have hSl:Sl⊆S:=by intro x hx;simp [S,hx]
  have hSh:Sh⊆S:=by intro x hx;simp [S,hx]
  refine ⟨J,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Coz,Cop,hCoz,hCop,hold⟩:=hold η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cz,hCz,hzero⟩:=hzero η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cl,hCl,hlow⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ch,hCh,hhigh⟩:=hhigh η₀ Q hQM hQ0 hQt hQ72
  let Cp:=Cop+Cl+Ch
  have hCp:0<Cp:=by dsimp [Cp];linarith
  have hCop':Cop≤Cp:=by dsimp [Cp];linarith
  have hCl':Cl≤Cp:=by dsimp [Cp];linarith
  have hCh':Ch≤Cp:=by dsimp [Cp];linarith
  refine ⟨Cz,Cp,hCz,hCp,?_⟩
  filter_upwards [hold,hzero,hlow,hhigh] with Z hold hz hl hh
  refine ⟨hold.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      Jz J Sz S Cz Cz hold.1.le le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
      hez hJz hSz hCz.le le_rfl hz
  · apply positive_from_stages (α:=α) M H hH W bslot _ _ _ _ _ _ _ _
      (bandWidth Mcap Bs ε k) _ _ κ Z η₀ Q J S Cp
    · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
        _ _ _ _ _ _ _ η₀ Q Jold J Sold S Cop Cp hold.1.le
        hlower le_rfl le_rfl le_rfl hlength le_rfl hloss hJo hSo hCop.le hCop' hold.2.2
    · exact positiveLowAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
        _ _ _ _ _ _ _ η₀ Q Jl J Sl S Cl Cp hold.1.le
        le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl hel hJl hSl hCl.le hCl' hl
    · exact positiveHighAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ _ κ Z
        _ _ _ _ _ _ _ _ η₀ Q Jh J Sh S Ch Cp hold.1.le
        le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl heh hJh hSh hCh.le hCh' hh

end SevenEighths.CenteredMomentEnergyCappedSuccessorPacking

end

end OAI

end Source2222

/- Original source: OAI/NumberTheory/DirichletL/Energy/CappedBandTransport.lean; sha256: b4985987719271c32dea8d31a11940810019d25bb6fa0d645f71603b99534657 -/
section Source2223
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedBandTransport
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

lemma saturated_successor (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (ha:0<a)(hmask:0≤Bmask)(hMcap:0≤Mcap)(hκ:0≤κ)(hε:0<ε)(k:ℕ)
    (hsaturated:bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k=Mcap)
    (h:CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH W bslot
      a b radial Bmask L lo hi Mcap κ ε k):
    CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH W bslot
      a b radial Bmask L lo hi Mcap κ ε (k+1):=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hr:0<reserve Mcap Bs ε:=(bounds Mcap Bs κ ε hMcap hBs hκ hε).2.2.2.1
  have hlower:lowerAt a b Mcap ε k≤lowerAt a b Mcap ε (k+1):=
    CenteredMomentEnergyProfiles.lower_antitone a b ha (by unfold remaining;omega)
  have hlength:lengthAt Mcap Bmask L ε (k+1)≤lengthAt Mcap Bmask L ε k:=
    range_mono Mcap Bmask L hMcap hmask (by unfold remaining;omega)
  have hwidth:bandWidth Mcap Bs ε (k+1)≤bandWidth Mcap Bs ε k:=by
    rw [hsaturated]
    exact bandWidth_le _ _ _ _
  have hloss:stageLoss Mcap Bs ε k≤stageLoss Mcap Bs ε (k+1):=by
    unfold stageLoss
    rw [loss_succ]
    linarith
  obtain ⟨degree,S,hcert⟩:=h
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero,Cpositive,hCz,hCp,hbound⟩:=hcert η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Czero,Cpositive,hCz,hCp,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le hlower le_rfl le_rfl le_rfl
      hlength hwidth hloss le_rfl (Finset.Subset.refl _) hCz.le le_rfl hZ.2.1
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      hlower le_rfl le_rfl le_rfl hlength hwidth hloss le_rfl (Finset.Subset.refl _)
      hCp.le le_rfl hZ.2.2

end SevenEighths.CenteredMomentEnergyCappedBandTransport

end

end OAI

end Source2223

/- Original source: OAI/NumberTheory/DirichletL/Energy/CappedAnalyticSuccessor.lean; sha256: d31d07bfa0645d729342c381158bceb84c48f37117f36ee2b47417cab3f62184 -/
section Source2224
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedAnalyticSuccessor
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyPositiveHighBound
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt lowerAt_pos child_support child_length)
open CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyStageMonotonicity
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyCappedRequests
open CenteredMomentEnergySourceCapSchedule CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_successor
    (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤bslot)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hrad:2≤radial)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hκ:(3/4:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκbeta:2*HeckeZeroSupremum.beta-1≤κ)
    (k:ℕ)(hk:k<count Mcap ε)
    (hold:CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (k+1):=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  let Mp:=bandWidth Mcap Bs ε (k+1)
  let Mc:=bandWidth Mcap Bs ε k
  let ac:=lowerAt a b Mcap ε (k+1)
  let Lc:=lengthAt Mcap Bmask L ε (k+1)
  let Lp:=lengthAt Mcap Bmask L ε k
  let Lreq:=requestLength Mcap Bmask Lc
  let A:=2*range Mcap Bmask L (count Mcap ε)+Mcap+1
  let r:=reserve Mcap Bs ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap.le hmask _
  have hκ0:0≤κ:=by linarith
  have hb:0≤b:=zero_le_one.trans hhi
  have hr:0<r:=(bounds Mcap Bs κ ε hMcap.le hBs hκ0 hε).2.2.2.1
  have hr1:r/4≤1:=by
    have hh:=bounds Mcap Bs κ ε hMcap.le hBs hκ0 hε
    have hrs:r≤amplification ε/100:=min_le_left _ _
    linarith [hh.2.1]
  have hMp:0≤Mp:=bandWidth_nonneg Mcap Bs ε hMcap.le hBs hε _
  have hMc:0<Mc:=band_positive Mcap Bs ε hMcap hBs hε k
  have hMpM:Mp≤Mcap:=bandWidth_le _ _ _ _
  have hMcM:Mc≤Mcap:=bandWidth_le _ _ _ _
  have hac:0<ac:=lowerAt_pos a b Mcap ε ha _
  have haca:ac≤a:=CenteredMomentEnergyProfiles.lower_antitone a b ha (Nat.zero_le _)
  have haclo:ac≤1/4:=haca.trans hlo
  have hLc:0≤Lc:=range_nonneg Mcap Bmask L hMcap.le hmask _
  have hLp:0≤Lp:=range_nonneg Mcap Bmask L hMcap.le hmask _
  have hreq:=request_bounds Mcap Bmask Lc hMcap.le hmask hLc
  have hreqFinal:Lreq≤range Mcap Bmask L (count Mcap ε):=
    request_le_final Mcap Bmask L ε hMcap.le hmask k hk
  have hRange:=range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap ε)
  have hA:0≤A:=by dsimp [A];positivity
  have hMA:Mp≤A:=by dsimp [A];linarith [range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap ε)]
  have hready:readyBudget A Bmask≤Bs:=
    readyBudget_le_schedule Mcap Bmask L ε A Bmask hMcap.le hmask le_rfl le_rfl
  have hdrop:Mp-amplification ε/2≤Mc:=parent_drop Mcap Bs ε hε k
  have hmesh:0≤fineMesh Mcap Bmask L κ ε:=
    (fineMesh_pos Mcap Bmask L κ ε hMcap.le hmask hκ0 hε).le
  have hsupport:lowerAt a b Mcap ε k=ac/max 1 b:=child_support a b Mcap ε k hk
  have hrequest:2*max Lreq Mp+r/4≤Lp:=previous_admits Mcap Bmask L ε Mp (r/4)
    hMcap.le hmask hMpM hr1 k hk
  have hhighL:max Lc Mp≤Lp:=by
    have hh:max Lc Mp≤Lreq:=max_le hreq.2.1 (hMpM.trans hreq.2.2)
    have hg:0≤max Lreq Mp:=hreq.1.trans (le_max_left _ _)
    have hx:=le_max_left Lreq Mp
    linarith
  have href:Mp+Bmask+Mc/100≤Lreq:=by
    have hh:=actual_contours Mcap Bmask Lc Mp Mc 0 hMcap.le hmask hMpM hMcM (by norm_num)
    exact (le_max_right _ _).trans hh
  obtain ⟨Jold,Sold,hprev⟩:=hold
  obtain ⟨Slow,Jlow,hlow⟩:=CenteredMomentEnergyCappedLowStage.actual_capped_low (α:=α) M H hH
    W aslot bslot a b radial Bmask L lo hi Mcap κ ε hW haslot hWs hbslot ha hb hrad
    hmask hMcap.le hκ hε hbeta hκbeta k hk ⟨Jold,Sold,hprev⟩
  obtain ⟨Uhigh,Jhigh,hhigh⟩:=CenteredMomentEnergyNaturalHighStage.actual_high_stage (α:=α) M H hH
    W hW aslot bslot lo hi ac b radial haslot hWs hbslot hac haclo hhi (by linarith)
    Mcap A Bs Bmask Mp Mc Lc (fineMesh Mcap Bmask L κ ε) Mc κ ε k hMc hMcap.le hA hBs hmask
    hMp hMc.le hLc hmesh hMA hready hκ hbeta hκbeta hε le_rfl hdrop Jold Sold Jlow Slow
  obtain ⟨d,Lgrow,Llow,hd,hd1,hLg,hgoal,hLexact,hLlow,hLupper,hzeroStage⟩:=
    CenteredMomentEnergyNaturalZeroStage.actual_zero_stage (α:=α) M H hH
      W aslot bslot (fineMesh Mcap Bmask L κ ε) lo hi κ ac b radial Bmask Lc Mp Mc Mcap Bs ε Mc k
      haslot hWs hW hmesh hκ hbeta hκbeta hac haclo hhi hrad hmask hLc hMp hMc.le hMcap.le hBs
      hε hMc le_rfl hdrop
  have hLlowReq:Llow≤Lreq:=by
    rw [hLlow,hLexact]
    exact actual_contours Mcap Bmask Lc Mp Mc d hMcap.le hmask hMpM hMcM hd1
  have hLgrowLow:Lgrow≤Llow:=by rw [hLlow];exact le_max_left _ _
  have hLgrowReq:Lgrow≤Lreq:=hLgrowLow.trans hLlowReq
  have hzeroCap:max Mp (2*Lgrow)≤Lp:=by
    have hm:Mp≤Lreq:=hMpM.trans hreq.2.2
    have hh:=le_max_left Lreq Mp
    apply max_le <;> linarith
  have hzeroReady:readyBudget (max Mp (2*Lgrow)) Bmask≤Bs:=by
    have hc:max Mp (2*Lgrow)≤A:=by
      apply max_le
      · exact hMA
      · dsimp [A];linarith
    apply le_trans _ hready
    unfold readyBudget
    linarith
  obtain ⟨Jzero,Uzero,hzero⟩:=hzeroStage Lp hLp hzeroCap hzeroReady Jold Jlow Sold Slow
  have hmarg:=margins Mcap Bs κ ε hMcap.le hBs hκ0 hε k
  apply CenteredMomentEnergyCappedSuccessorPacking.certified_from_stages (α:=α) M H hH
    W bslot a b radial Bmask L lo hi Mcap κ ε ha hmask hMcap.le hκ0 hε k
    (stageLoss Mcap Bs ε (k+1)) (physicalLoss Mcap Bs ε k) (reflectedLoss Mcap Bs ε k)
    le_rfl (hmarg.2.2.2.1.trans hmarg.2.2.2.2) hmarg.2.2.2.2 ⟨Jold,Sold,hprev⟩
  · refine ⟨Jzero,Uzero,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨C₀,C₁,hC₀,hC₁,hprevZ⟩:=hprev η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Cz,hCz,hzeroZ⟩:=hzero η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Cz*(Clow+C₀+C₁+1),by positivity,?_⟩
    filter_upwards [hprevZ,hlowZ,hzeroZ] with Z hp hl hz
    have hzz:=hp.2.1
    have hpp:=hp.2.2
    rw [hsupport] at hzz hpp
    have hlowRestricted:=zeroLowAt_transport (internalQ Q η₀)
      ac b radial Bmask Lreq Mp (physicalLoss Mcap Bs ε k) Z
      ac b radial Bmask Llow Mp (physicalLoss Mcap Bs ε k) Jlow Jlow Slow Slow Clow Clow
      hp.1.le le_rfl le_rfl le_rfl le_rfl hLlowReq le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.2
    exact hz.2 _ C₀ C₁ Clow le_rfl hC₀.le hC₁.le hClow.le hzz hpp hlowRestricted
  · refine ⟨Jlow,Slow,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Clow,hClow,?_⟩
    filter_upwards [hlowZ] with Z hl
    exact positiveLowAt_transport (α:=α) M H hH W bslot
      ac b radial Bmask Lreq (fineMesh Mcap Bmask L κ ε) lo hi Mp (physicalLoss Mcap Bs ε k) κ Z
      ac b radial Bmask Lc Mp (physicalLoss Mcap Bs ε k) η₀ Q Jlow Jlow Slow Slow Clow Clow
      hl.1.le le_rfl le_rfl le_rfl le_rfl hreq.2.1 le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
  · refine ⟨Jhigh,Uhigh,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨C₀,C₁,hC₀,hC₁,hprevZ⟩:=hprev η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Ch,hCh,hhighZ⟩:=hhigh η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Ch*(C₀+C₁+Clow+1),by positivity,?_⟩
    filter_upwards [hprevZ,hlowZ,hhighZ] with Z hp hl hh
    have hzz:=hp.2.1
    have hpp:=hp.2.2
    rw [hsupport] at hzz hpp
    have hzSmall:=zeroAt_transport (internalQ Q η₀)
      (ac/max 1 b) b radial Bmask Lp Mc (stageLoss Mcap Bs ε k) Z
      (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs ε k)
      Jold Jold Sold Sold C₀ C₀ hp.1.le le_rfl le_rfl hrad hmask hhighL le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hC₀.le le_rfl hzz
    have hpSmall:=positiveAt_transport (α:=α) M H hH W bslot
      (ac/max 1 b) b radial Bmask Lp (fineMesh Mcap Bmask L κ ε) lo hi Mc (stageLoss Mcap Bs ε k) κ Z
      (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs ε k) η₀ Q
      Jold Jold Sold Sold C₁ C₁ hp.1.le le_rfl le_rfl hrad hmask hhighL le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hC₁.le le_rfl hpp
    have hlRestricted:=positiveLowAt_transport (α:=α) M H hH W bslot
      ac b radial Bmask Lreq (fineMesh Mcap Bmask L κ ε) lo hi Mp (physicalLoss Mcap Bs ε k) κ Z
      ac b radial Bmask (Mp+Bmask+Mc/100) Mp (physicalLoss Mcap Bs ε k) η₀ Q
      Jlow Jlow Slow Slow Clow Clow hp.1.le le_rfl le_rfl le_rfl le_rfl href le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
    exact hh.2 _ C₀ C₁ Clow le_rfl hC₀.le hC₁.le hClow.le hzSmall hpSmall hlRestricted

end SevenEighths.CenteredMomentEnergyCappedAnalyticSuccessor

end

end OAI

end Source2224

/- Original source: OAI/NumberTheory/DirichletL/Energy/CappedRadialTransport.lean; sha256: 5e61fd581589a817d306fa8b14fe53d8a236d8a8d5d60aacdbae64d39b2547fe -/
section Source2225
namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedRadialTransport
open HeckeFamily CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyBandMonotonicity
local notation "O" => HeckeFamily.O
variable {α : Type*}
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem certified_radial_mono (W : ℝ → ℂ)
    (bslot a b radialOld radialNew Bmask L lo hi Mcap κ ε : ℝ) (k : ℕ)
    (hrad : radialNew ≤ radialOld)
    (h : CertifiedBand (α := α) M H hH W bslot a b radialOld Bmask L lo hi Mcap κ ε k) :
    CertifiedBand (α := α) M H hH W bslot a b radialNew Bmask L lo hi Mcap κ ε k := by
  obtain ⟨degree, S, hbound⟩ := h
  refine ⟨degree, S, ?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero, Cpositive, hCzero, hCpositive, hcert⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Czero, Cpositive, hCzero, hCpositive, ?_⟩
  filter_upwards [hcert] with Z hZ
  refine ⟨hZ.1, ?_, ?_⟩
  · exact zeroAt_transport _ _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl hrad le_rfl
      le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hZ.2.1
  · exact positiveAt_transport (α := α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl hrad le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hZ.2.2

theorem certified_from_max_two (W : ℝ → ℂ)
    (bslot a b radial Bmask L lo hi Mcap κ ε : ℝ) (k : ℕ)
    (h : CertifiedBand (α := α) M H hH W bslot a b (max 2 radial)
      Bmask L lo hi Mcap κ ε k) :
    CertifiedBand (α := α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k :=
  certified_radial_mono (α := α) M H hH W bslot a b (max 2 radial) radial
    Bmask L lo hi Mcap κ ε k (le_max_right _ _) h

end SevenEighths.CenteredMomentEnergyCappedRadialTransport

end

end OAI

end Source2225

/- Original source: OAI/NumberTheory/DirichletL/Energy/CertifiedExistence.lean; sha256: 2d48b75fdd14ba8eabb428f79f98e0a6e532c28083075bacf16e1d57f020d7a9 -/
section Source2226
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCertifiedExistence
open HeckeFamily CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyCappedAnalyticSuccessor CenteredMomentEnergyCappedRadialTransport
open CenteredMomentEnergyWidthSchedule
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem certified_bands (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤bslot)(ha:0<a)(haUpper:a≤1/4)(hb:1≤b)(hrad:2≤radial)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hκ0:(3/4:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∀k:ℕ,k≤count Mcap ε→
      CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k:=by
  intro k
  induction k with
  | zero =>
    intro _
    exact certified_floor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW ha (by linarith) (by linarith) hmask hMcap.le (by linarith) hε hbeta hκ
  | succ k ih =>
    intro hk
    have hprevious:=ih (Nat.le_of_succ_le hk)
    have hstep:k<count Mcap ε:=by omega
    exact actual_successor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε hbeta hκ
      k hstep hprevious

theorem terminal_certificate (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤bslot)(ha:0<a)(haUpper:a≤1/4)(hb:1≤b)(_hrad:0<radial)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hκ0:(3/4:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε):=by
  apply certified_from_max_two (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε
  exact certified_bands (α:=α) M H hH W aslot bslot a b (max 2 radial) Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb (le_max_left _ _) hmask hMcap hκ0 hε hbeta hκ _ le_rfl

end SevenEighths.CenteredMomentEnergyCertifiedExistence

end

end OAI

end Source2226

/- Original source: OAI/NumberTheory/DirichletL/Detector/DetectorBatch.lean; sha256: 1b10930a0dba429879c4ee3e48b94f502ca1cc6a28d3bd3ef89a896982366d45 -/
section Source2227
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorSupportedWitness ProbePhysical
local notation "O" => HeckeFamily.O

def retainedProjection (R : Finset FreeRow) (u0 : FreeRow) (u : FreeRow) : FreeRow :=
  if u∈R then u else u0

@[simp] theorem retainedProjection_of_mem (R : Finset FreeRow) (u0 u : FreeRow) (hu : u∈R) :
    retainedProjection R u0 u=u := by simp [retainedProjection,hu]

theorem retainedProjection_mem (R : Finset FreeRow) (u0 : FreeRow) (h0 : u0∈R) (u : FreeRow) :
    retainedProjection R u0 u∈R := by
  unfold retainedProjection
  split_ifs with hu
  · exact hu
  · exact h0

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def retainedSourceBatch {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character)
    (R : Finset FreeRow) (u0 : FreeRow) (h0 : u0∈R)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (hw : ∀u∈R,SupportedWitness
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) U a ε tstar T allowance i)
    (hrow : ∀u∈R,rowNorm u≤U)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hm : 0≤mesh) (hb : 0<binWidth)
    (hwpos : ∀s∈slots,0<widths s) (hwmesh : ∀s∈slots,widths s≤mesh)
    (hsupply : 7/37≤∑s∈slots,widths s) :
    Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i where
  rows := R
  family := fun u=>sourceDetectorFamily S hS.prime η (retainedProjection R u0 u)
    (rayCubeFamily M H hH (retainedProjection R u0 u))
  witness := fun u=>hw (retainedProjection R u0 u) (retainedProjection_mem R u0 h0 u)
  row_norm := hrow
  data := sourceMomentData M H hH S hS.prime η
  reverse := sourceMomentReverse M H
  row_coeff := by
    intro u hu j I
    rw [retainedProjection_of_mem R u0 u hu]
    exact source_family_moment_coeff M H hH S hS.prime hS.bad η u j I
  slots := slots
  profile := profile
  upper := upper
  widths := widths
  external := external
  mesh := mesh
  binWidth := binWidth
  mesh_nonneg := hm
  binWidth_pos := hb
  widths_pos := hwpos
  widths_mesh := hwmesh
  supply := hsupply

lemma physical_slot_widths {N : ℕ} (ell : Fin N→ℝ) (d dmin mesh : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤d) (hdtop : d≤37/42)
    (hell : ∀j,0<ell j) (hsmall : ∀j,ell j≤dmin*mesh)
    (hsum : ∑j,ell j=1/6) :
    (∀j,0<ell j/d) ∧ (∀j,ell j/d≤mesh) ∧ 7/37≤∑j,ell j/d := by
  have hd0 : 0<d := hdmin.trans_le hd
  have hm : 0≤mesh := by
    by_contra hn
    have hm : mesh<0 := lt_of_not_ge hn
    have hn : (∑j,ell j)≤0 := Finset.sum_nonpos fun j _=>
      (hsmall j).trans (mul_nonpos_of_nonneg_of_nonpos hdmin.le hm.le)
    rw [hsum] at hn
    norm_num at hn
  refine ⟨fun j=>div_pos (hell j) hd0,fun j=>?_,?_⟩
  · apply (div_le_iff₀ hd0).mpr
    exact (hsmall j).trans (by nlinarith)
  · rw [←Finset.sum_div,hsum]
    apply (le_div_iff₀ hd0).mpr
    nlinarith

lemma physical_slot_scale {N : ℕ} (ell : Fin N→ℝ) (Z d : ℝ) (hZ : 0<Z) (hd : d≠0) (j : Fin N) :
    (Z^d)^(ell j/d)=Z^(ell j) := by
  rw [←Real.rpow_mul hZ.le]
  congr 1
  field_simp
end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2227

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/TargetPrincipal.lean; sha256: f1a27c6555c3b0b9562b26ee1de00cc8e1f200dad3007b5daa7934827bc3ff27 -/
section Source2228
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter UniqueFactorizationMonoid
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def targetPrincipalSupport (η : Character) : Finset (Ideal O) :=
  (normalizedFactors (η.modulus*Ideal.span {rowMaskElement}*Ideal.span {(72:O)})).toFinset

lemma targetPrincipalSupport_prime (η : Character) : ∀P∈targetPrincipalSupport η,Prime P := by
  intro P hP
  exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma inverse_target_elementCoeff (η : Character) (u : FreeRow) (n : O) :
    elementCoeff (targetRow η u).inverse n=
      rowTwist (HeckeRowClosure.elementHom ((fixedSourcePrincipal ∅ (by simp)).product η.inverse))
        rowMaskElement 1 u.val n := by
  rw [elementCoeff_inverse]
  unfold targetRow
  rw [elementCoeff_product,elementCoeff_inverse,mul_inv_rev,inv_inv,rawRow_elementCoeff]
  change (elementCoeff (fixedSourcePrincipal ∅ (by simp)) n *
    idealRowHom (rowMaskElement^6*1^4*u.val) (Ideal.span {n})) * (elementCoeff η n)⁻¹=
    elementCoeff ((fixedSourcePrincipal ∅ (by simp)).product η.inverse) n *
      idealRowHom (rowMaskElement^6*1^4*u.val) (Ideal.span {n})
  rw [elementCoeff_product,elementCoeff_inverse]
  ring

theorem principal_target_row_norm_bound (η : Character) (u : FreeRow)
    (hs : Supported (Ideal.span {u.val})) (hp : (targetRow η u).residue=1) :
    rowNorm u≤(HeckeExceptionalRows.bound (targetPrincipalSupport η):ℝ) := by
  obtain ⟨v,hv⟩ := exists_supported_primary_unit u.val hs
  let r : O := (v:O)*u.val
  have hspan : (Ideal.span {r}:Ideal O)=Ideal.span {u.val} :=
    Ideal.span_singleton_mul_left_unit v.isUnit u.val
  have hr : Supported (Ideal.span {r}) := hspan.symm ▸ hs
  have hx : (1:O)^4*u.val=(v⁻¹:Oˣ).val*λ₀^0*(2:O)^0*r := by simp [r]
  let η0 := (fixedSourcePrincipal ∅ (by simp)).product η.inverse
  have hmod : η0.modulus=η.modulus := by
    change (1:Ideal O)⊓η.modulus=η.modulus
    simp
  have hinv : (targetRow η u).inverse.residue=1 := by
    change (targetRow η u).residue⁻¹=1
    rw [hp,inv_one]
  have hfixed := HeckeRowNonprincipal.principal_row_fixed_support η0 (targetRow η u).inverse
    rowMaskElement 1 u.val rowMaskElement_ne_zero (dvd_mul_left _ _) (dvd_mul_right _ _)
    v⁻¹ 0 0 r hr hv hx (inverse_target_elementCoeff η u) hinv (fun P _=>hspan.symm ▸ u.property.2 P)
  rw [hmod] at hfixed
  have hn := HeckeExceptionalRows.row_norm_bound (targetPrincipalSupport η) (targetPrincipalSupport_prime η) hfixed
  rw [hspan] at hn
  unfold rowNorm
  exact_mod_cast hn

theorem excluded_target_nonprincipal_eventually (η : Character) (d : ℝ) (hd : 0<d) :
    ∀ᶠ Z : ℝ in atTop,∀u : FreeRow,Z^d≤rowNorm u →
      Supported (Ideal.span {u.val}) → ∀S : Finset (Ideal O),∀hS : ∀P∈S,Prime P,
      ((targetRow η u).excludePrimes S hS).residue≠1 := by
  filter_upwards [(tendsto_rpow_atTop hd).eventually
    (eventually_gt_atTop (HeckeExceptionalRows.bound (targetPrincipalSupport η):ℝ))]
    with Z hZ u hu hs S hS
  intro hp
  have hp' := (HeckeFiniteDeletion.principal_iff_of_mask _ _ (excludePrimes_mask (targetRow η u) S hS)).mp hp
  exact not_lt_of_ge (principal_target_row_norm_bound η u hs hp') (hZ.trans_le hu)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2228

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/DetectorReady.lean; sha256: 5609221f1f947d7cc23f18dfb933fec07bd3f30b2ccf744eaeb60c570be4c5a2 -/
section Source2229
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceConductorConstant (S : Finset (Ideal O)) (η : Character) : ℕ :=
  conductorConstant*(∏P∈S,P).absNorm*(η.modulus.absNorm+1)+conductorConstant*M.absNorm

theorem source_ray_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) :
    (sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).modulus.absNorm≤
      sourceConductorConstant M S η*(Ideal.span {u.val}:Ideal O).absNorm := by
  cases j with
  | inl b =>
    cases b with
    | false =>
      apply (targetRow_excluded_conductor S hS η u).trans
      unfold sourceConductorConstant
      ring_nf
      omega
    | true =>
      apply (rowCharacter_conductor S hS u).trans
      unfold sourceConductorConstant
      ring_nf
      omega
  | inr θ =>
    apply (ProbeRayCharacterFamily.raw_twisted_conductor M H hH u θ).trans
    unfold sourceConductorConstant
    ring_nf
    omega

theorem source_ray_nonprincipal_eventually (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (d : ℝ) (hd : 0<d) :
    ∀ᶠ Z : ℝ in atTop,∀U : ℝ,∀u∈rowBand (Z^d) U,
      (calibrationForSet S hmax).residueMonoid u.val≠0 →
      ∀j,(sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue≠1 := by
  filter_upwards [excluded_target_nonprincipal_eventually η d hd,
    ProbeRayCharacterFamily.large_supported_twists_eventually M d hd] with Z htarget hray
  intro U u hu hc j
  have hs := calibration_nonzero_supported S hmax hS.bad u.val hc
  have hnorm := (mem_rowBand.mp hu).2.1
  cases j with
  | inl b =>
    cases b with
    | false => exact htarget u hnorm hs S hS.prime
    | true => exact calibrated_row_nonprincipal S hS.prime hmax hS.bad u (mem_rowBand.mp hu).1 hc
  | inr θ => exact hray u hnorm hs H hH θ

theorem source_ray_maximum_eventually (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (d : ℝ) (hd : 0<d) :
    ∀ᶠ Z : ℝ in atTop,∀U : ℝ,∀u∈rowBand (Z^d) U,
      (calibrationForSet S hmax).residueMonoid u.val≠0 →
      ∃hnp : ∀j,(sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue≠1,
      ∀T : ℝ,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) T=
        HeckeDetectorZeros.zeroMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) hnp T := by
  filter_upwards [source_ray_nonprincipal_eventually M H hH S hS hmax η d hd] with Z hZ
  intro U u hu hc
  exact ⟨hZ U u hu hc,fun T=>detectorMaximum_eq_nonprincipal _ _ T⟩

theorem source_ray_conductor_eventually (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (ν : ℝ) (hν : 0<ν) :
    ∀ᶠ Z : ℝ in atTop,∀(u : FreeRow) (d : ℝ),rowNorm u≤Z^(d-ν) →
      ∀j,((sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).modulus.absNorm:ℝ)≤Z^d := by
  have hh := HeckeDyadic.constant_absorbed_eventually (sourceConductorConstant M S η:ℝ) ν hν
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hC hZ
  intro u d hu j
  have hq : ((sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).modulus.absNorm:ℝ)≤
      (sourceConductorConstant M S η:ℝ)*rowNorm u := by
    unfold rowNorm
    exact_mod_cast source_ray_conductor M H hH S hS η u j
  apply hq.trans
  calc
    _ ≤ Z^ν*Z^(d-ν) := mul_le_mul hC hu (by unfold rowNorm;positivity) (Real.rpow_nonneg hZ.le _)
    _ = Z^d := by rw [←Real.rpow_add hZ];congr 1;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2229

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CubeSupportedWitness.lean; sha256: e0745ae7b7c7d38c8f35cea95a919a5361d5a6193c07a978e4c6f0441addc478 -/
section Source2230
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
open HeckeDetectorSupportedWitness
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) (η : Character)

theorem supported_witnesses_from_source_cube (dmin dmax τ ε e κ heightCost margin : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0<margin)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠ Z : ℝ in atTop,∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ (U : ℝ) (rows : Finset FreeRow),rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
      let χ := fun u : rows => sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
      ∀(a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀u : rows,detectorMaximum (χ u) (3*(i+1 : ℕ)*(Z^τ))<a+2*e) →
        (∀u : rows,a≤detectorMaximum (χ u) ((3*i : ℕ)*Z^τ)) →
        ∀ tstar : ℝ,1≤tstar → tstar≤3/2 →
          Nonempty (∀u : rows,SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ)
            ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z0,hdet⟩ := actual_supported_witness_family dmin dmax τ ε e κ heightCost I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hbudget
  filter_upwards [eventually_ge_atTop Z0,
    source_ray_nonprincipal_eventually M H hH S hS hmax η (1/100) (by norm_num),
    source_ray_conductor_eventually M H hH S hS.prime η margin hmargin] with Z hZ hnp hcond
  intro d hd hd' U rows hrows hcal hrow
  dsimp only
  intro a i hi ha ha' hnext hcurrent tstar ht ht'
  let χ := fun u : rows => sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
  have hχ : ∀u j,(χ u j).residue≠1 := fun u=>hnp U u.val (hrows u.property) (hcal u.val u.property)
  have heq (u : rows) := detectorMaximum_eq_nonprincipal (χ u) (hχ u)
  exact hdet Z hZ d hd hd' χ hχ a i hi ha ha'
    (fun u=>by rw [←heq u];exact hnext u)
    (fun u=>by rw [←heq u];exact hcurrent u)
    (fun u=>hcond u.val d (hrow u.val u.property)) tstar ht ht'

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2230

/- Original source: OAI/NumberTheory/DirichletL/Detector/SourceBatch.lean; sha256: 39c56d463054b01be89d79179a73e6efc74c4ffcc41aacf2cbd33565e04b0b84 -/
section Source2231
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_source_batch (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hdtop : dmax≤37/42) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0<margin) (hm : 0≤mesh) (hb : 0<binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀tstar : ℝ,1≤tstar → tstar≤3/2 →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0<ell j) → (∀j,ell j≤dmin*mesh) → (∑j,ell j)=1/6 →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=>ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) := by
  have hw := supported_witnesses_from_source_cube M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin I hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hmargin hbudget
  filter_upwards [hw,eventually_ge_atTop (1:ℝ)] with Z hw hZ
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent tstar ht ht' N ell hell hsmall hsum W upper z
  obtain ⟨w⟩ := hw d hd hd' U rows hrows hcal hrow a i hi ha ha'
    (fun u=>hnext u.val u.property) (fun u=>hcurrent u.val u.property) tstar ht ht'
  obtain ⟨u0,h0⟩ := hne
  have hnorm (u : FreeRow) (hu : u∈rows) : rowNorm u≤Z^d :=
    (hrow u hu).trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  obtain ⟨hwp,hwm,hsp⟩ := physical_slot_widths ell d dmin mesh hdmin hd (hd'.trans hdtop) hell hsmall hsum
  let B := retainedSourceBatch M H hH S hS η rows u0 h0 (Z^d) a ε tstar (Z^τ)
    ((Z^d)^(τ/(2*dmax))) i (fun u hu=>w ⟨u,hu⟩) hnorm
    Finset.univ W upper (fun j=>ell j/d) z mesh binWidth hm hb (fun j _=>hwp j) (fun j _=>hwm j) hsp
  refine ⟨B,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro u hu j
  dsimp [B,retainedSourceBatch]
  rw [retainedProjection_of_mem rows u0 u hu]
end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2231

/- Original source: OAI/NumberTheory/DirichletL/Detector/SourceAmplitudeClasses.lean; sha256: f5ac6fcdf19de4d801affcfb69e5102f40e624c56dca678eda6a16e45c447291 -/
section Source2232
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_source_amplitude_batches (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hdtop : dmax≤37/42) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0<margin) (hm : 0≤mesh) (hb : 0<binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0<ell j) → (∀j,ell j≤dmin*mesh) → (∑j,ell j)=1/6 →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=>u.val)
      W upper (fun j=>ell j/d) z (Z^d)
    ∀bin : HeckeDetectorFiberPartition.BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) binWidth,
    let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
      (Z^d) ((2*a-1)/2) binWidth hb (fun j=>ell j/d) Q bin
    rows'.Nonempty →
    let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=>ell j/d) bin
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows' ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=>ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows',∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) ∧
      (∀u∈B.rows,HeckeDetectorAmplitudeFirst.rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=>u.val)
          B.profile B.upper B.widths B.external (Z^d)) u=q) := by
  have hbatches := actual_source_batch M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin mesh binWidth I hdmin hdmax hdtop hτ hτzero hτheight
    hε he he' hκ hκ' hheightCost hmargin hm hb hbudget
  filter_upwards [hbatches] with Z hbatch
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent N ell hell hsmall hsum W upper z
  dsimp only
  intro bin hne'
  let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=>u.val)
    W upper (fun j=>ell j/d) z (Z^d)
  let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
    (Z^d) ((2*a-1)/2) binWidth hb (fun j=>ell j/d) Q bin
  let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=>ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hcut := HeckeDetectorAdaptiveCutoff.cutoff_bounds (2*a-1) q (by linarith)
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu=>hcal u (hsub hu)) (fun u hu=>hrow u (hsub hu)) a i hi ha ha'
      (fun u hu=>hnext u (hsub hu)) (fun u hu=>hcurrent u (hsub hu))
      (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,?_⟩
  intro u hu
  have hu' : u∈rows' := hBr ▸ hu
  rw [hSlots,hWidths,hW,hUpper,hZ,hBin]
  exact HeckeDetectorAmplitudeFirst.rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2)
    binWidth hb (fun j=>ell j/d) Q bin u hu'
end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2232

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/RestoreCorrection.lean; sha256: a032269770291db813352ac13113f6d1c5e74e1a78698c3a01b4b191cd220a05 -/
section Source2233
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def supportedCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  if hs : Supported P.val then
    if P.val∣Ideal.span {u.val} then ramifiedCorrection η u P hs x w z
    else idealUnramifiedCorrection η u P x w z
  else 1

def excludedCorrection (S : Finset (Ideal O)) (η : Character) (u : FreeRow)
    (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  if P.val∈S then 1 else supportedCorrection η u P x w z

theorem continuedCorrection_first_hasProd (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (htail : FirstTail eps S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    HasProd (fun P : PrimeIdeal=>excludedCorrection S η u P x w z)
      (continuedCorrection S hS η u x w z) := by
  have hp := (ramifiedFactor_hasProd S hS η u x w z).mul
    (unramifiedProduct_first_multipliable eps S htail η u x w z hx hz hw hxw).hasProd
  have hsub : HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      excludedCorrection S η u P.val x w z) (continuedCorrection S hS η u x w z) := by
    convert hp using 1
    · funext P
      have hs := outside_prime_supported S hS.bad P.val P.property
      simp only [excludedCorrection,ite_eq_right P.property,supportedCorrection,dite_eq_left hs,
        ramifiedFactor,unramifiedFactor]
      split_ifs <;> simp
    · rfl
  exact (Subtype.val_injective.hasProd_iff (fun P hP=>by
    have hm : P.val∈S := by
      by_contra hn
      exact hP ⟨⟨P,hn⟩,rfl⟩
    simp [excludedCorrection,hm])).mp hsub

theorem continuedCorrection_restore (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (htail : FirstTail eps S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    continuedCorrection S hS η u x w z=
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
        ∏P∈T,supportedCorrection η u P x w z := by
  have hlarge := continuedCorrection_first_hasProd eps S hS htail η u x w z hx hz hw hxw
  have hsmall := continuedCorrection_first_hasProd eps (markExclusions S T)
    (markedSourceExclusions S hS T) (marked_firstTail eps S htail T)
    η u x w z hx hz hw hxw
  have hfinite : HasProd (fun P : PrimeIdeal=>if P∈T then supportedCorrection η u P x w z else 1)
      (∏P∈T,supportedCorrection η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T)
      (f:=fun P : PrimeIdeal=>if P∈T then supportedCorrection η u P x w z else 1)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [Finset.prod_ite_mem,Finset.inter_self] using hh
  apply hlarge.unique
  convert hsmall.mul hfinite using 1
  funext P
  simp only [excludedCorrection,mem_markExclusions]
  by_cases hp : P∈T
  · simp [hp,hT P hp]
  · simp [hp]

theorem continuedCorrection_restore_quotients (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (htail : FirstTail eps S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re)
    (G : PrimeIdeal→ℂ) (hne : ∀P∈T,supportedCorrection η u P x w z≠0) :
    continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T,G P=continuedCorrection S hS η u x w z*
      ∏P∈T,G P/supportedCorrection η u P x w z := by
  rw [continuedCorrection_restore eps S hS htail T hT η u x w z hx hz hw hxw,
    Finset.prod_div_distrib]
  have hn : (∏P∈T,supportedCorrection η u P x w z)≠0 := Finset.prod_ne_zero_iff.mpr hne
  field_simp
end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source2233

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsCentralCancellation.lean; sha256: 7725f7dbef619a609bd867acc993b377b67b19d9e35ef312dcadbf5c97e21ee8 -/
section Source2234
namespace OAI

noncomputable section
namespace SevenEighths.ProbeLocal

theorem central_phase_error_bound (V W D P B q vInv : ℂ) (A T : ℝ)
    (hA : 1≤A) (hV : ‖V‖≤1/2) (hD : ‖D‖≤1/2)
    (hW : ‖W‖≤A) (hq : ‖q‖≤A) (hv : ‖vInv‖≤1)
    (hVT : A^2*‖V‖≤T) (hDT : A^2*‖D‖≤T)
    (hET : A^2*‖P+D‖≤28*T) (hBET : A*‖B‖*‖P+D‖≤28*T)
    (hBD : B*D=vInv) (hWq : vInv*W=q) :
    ‖compensatedReplacement V W D P B q+continuedCorrection V W D P*vInv‖≤720*T := by
  have hA0 : 0≤A := by linarith
  have hT : 0≤T := (mul_nonneg (sq_nonneg A) (norm_nonneg V)).trans hVT
  have h1V : ‖1-V‖≤2 := by
    have hh := norm_sub_le (1:ℂ) V
    rw [norm_one] at hh
    linarith
  have h1W : ‖1-W‖≤2*A := by
    have hh := norm_sub_le (1:ℂ) W
    rw [norm_one] at hh
    linarith
  have hdiff : ‖vInv-q‖≤2*A := (norm_sub_le vInv q).trans (by linarith)
  have hfac : ‖(1-V)*(1-W)/(1-D)‖≤8*A := by
    rw [div_eq_mul_inv,norm_mul,norm_mul]
    have hi := inv_one_sub_norm_le_two D hD
    calc
      _ ≤ 2*(2*A)*2 := by gcongr
      _ = _ := by ring
  have hleft : ‖(vInv-q)*(V/(1-V)-D)‖≤2*A*(2*‖V‖+‖D‖) := by
    rw [norm_mul]
    apply mul_le_mul hdiff _ (norm_nonneg _) (by positivity)
    calc
      _ ≤ ‖V/(1-V)‖+‖D‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [div_eq_mul_inv,norm_mul]
        have hi := inv_one_sub_norm_le_two V hV
        nlinarith [mul_le_mul_of_nonneg_left hi (norm_nonneg V)]
  have hright : ‖(B+vInv-q)*(P+D)‖≤(‖B‖+2*A)*‖P+D‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ = ‖B+(vInv-q)‖ := by congr 1;ring
      _ ≤ ‖B‖+‖vInv-q‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  rw [continued_normalized_cancellation V W D P B q vInv
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD) hBD hWq,norm_mul]
  calc
    _ ≤ (8*A)*(2*A*(2*‖V‖+‖D‖)+(‖B‖+2*A)*‖P+D‖) := by
      apply mul_le_mul hfac _ (norm_nonneg _) (by positivity)
      exact (norm_add_le _ _).trans (add_le_add hleft hright)
    _ = 32*(A^2*‖V‖)+16*(A^2*‖D‖)+8*(A*‖B‖*‖P+D‖)+16*(A^2*‖P+D‖) := by ring
    _ ≤ 720*T := by linarith

end SevenEighths.ProbeLocal
end

end OAI

end Source2234

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsCentralError.lean; sha256: 3142ea14e8cc02190934f9dc25ad7bf09554aca99c845fb5f5dce9fcd53a66d1 -/
section Source2235
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

lemma central_unramified_error_weights (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    let L := Q^(6*e)
    let E := unramifiedMarked Q A eta v x w z+coordD Q eta v x
    L^2*‖coordV Q z‖≤Q^(-(51/100:ℝ)) ∧
    L^2*‖coordD Q eta v x‖≤Q^(-(51/100:ℝ)) ∧
    L^2*‖E‖≤28*Q^(-(51/100:ℝ)) ∧
    L*‖star eta*(Q:ℂ)^x‖*‖E‖≤28*Q^(-(51/100:ℝ)) := by
  dsimp only
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  let R := coordR Q A x z
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let B := star eta*(Q:ℂ)^x
  let L : ℝ := Q^(6*e)
  have hL : 1≤L := Real.one_le_rpow hQ1 (by positivity)
  have hL0 : 0≤L := by positivity
  have hR := coordR_norm_le Q hQ0 A x z hA
  have hV := coordV_norm Q hQ0 z
  have hD := coordD_norm_le Q hQ0 eta v x heta hv
  have hK := coordK_norm_le Q hQ1 eta x w heta
  have hW : ‖W‖≤L := (coordW_norm_le Q hQ0 v w hv).trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith))
  have hB : ‖B‖≤Q^x.re := by
    dsimp only [B]
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by rw [hx,hz];linarith))
  have hVh : ‖V‖≤1/2 := hV.le.trans (rpow_le_half Q _ hQ (by rw [hz];norm_num))
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by rw [hx];linarith))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hE : ‖unramifiedMarked Q A eta v x w z+D‖≤24*L*‖R‖+4*‖K‖*‖V‖ := by
    have hh := unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    apply hh.trans
    nlinarith [mul_le_mul_of_nonneg_left (show 1+‖W‖≤2*L by linarith) (norm_nonneg R)]
  have weighted (k r : ℝ) (N : ℝ) (hN : N≤Q^r) (hexp : k+r≤-(51/100:ℝ)) :
      Q^k*N≤Q^(-(51/100:ℝ)) := by
    calc
      _ ≤ Q^k*Q^r := mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg hQ0.le _)
      _ = Q^(k+r) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hQ1 hexp
  have hLR : L^3*‖R‖≤Q^(-(51/100:ℝ)) := by
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hR (by rw [hx,hz];linarith)
  have hLKV : L^2*(‖K‖*‖V‖)≤Q^(-(51/100:ℝ)) := by
    have hkv : ‖K‖*‖V‖≤Q^(1-x.re-w.re-6*z.re) := by
      calc
        _ ≤ Q^(1-x.re-w.re)*Q^(-6*z.re) := mul_le_mul hK hV.le (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
        _ = _ := by rw [←Real.rpow_add hQ0];congr 1;ring
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hkv (by rw [hx,hw,hz];linarith)
  have hLBR : L^2*(‖B‖*‖R‖)≤Q^(-(51/100:ℝ)) := by
    have hbr : ‖B‖*‖R‖≤Q^(4-5*x.re-6*z.re) := by
      calc
        _ ≤ Q^x.re*Q^(4-6*x.re-6*z.re) := mul_le_mul hB hR (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
        _ = _ := by rw [←Real.rpow_add hQ0];congr 1;ring
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hbr (by rw [hx,hz];linarith)
  have hLBKV : L*(‖B‖*‖K‖*‖V‖)≤Q^(-(51/100:ℝ)) := by
    have hbkv : ‖B‖*‖K‖*‖V‖≤Q^(1-w.re-6*z.re) := by
      calc
        _ ≤ Q^x.re*Q^(1-x.re-w.re)*Q^(-6*z.re) := by
          gcongr
          exact hV.le
        _ = _ := by rw [←Real.rpow_add hQ0,←Real.rpow_add hQ0];congr 1;ring
    exact weighted _ _ _ hbkv (by rw [hw,hz];linarith)
  refine ⟨?_,?_,?_,?_⟩
  · change L^2*‖V‖≤_
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hV.le (by rw [hz];linarith)
  · change L^2*‖D‖≤_
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hD (by rw [hx];linarith)
  · have hh := mul_le_mul_of_nonneg_left hE (sq_nonneg L)
    change L^2*‖unramifiedMarked Q A eta v x w z+D‖≤_
    nlinarith [hLR,hLKV]
  · have hh := mul_le_mul_of_nonneg_left hE (mul_nonneg hL0 (norm_nonneg B))
    change L*‖B‖*‖unramifiedMarked Q A eta v x w z+D‖≤_
    nlinarith [hLBR,hLBKV]

end SevenEighths.ProbeEuler
end

end OAI

end Source2235

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsCentralSelected.lean; sha256: 5fefd31772b8d30c7e46f1cb4f1038bb2142f514390e5e8437189551bde642b4 -/
section Source2236
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

lemma unramifiedSelected_central_error (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v‖≤
      720*Q^(-(51/100:ℝ)) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hL : 1≤Q^(6*e) := Real.one_le_rpow hQ1 (by positivity)
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by rw [hz];norm_num)
  have hD : ‖coordD Q eta v x‖≤1/2 :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans
      (rpow_le_half Q _ hQ (by rw [hx];linarith))
  have hW : ‖coordW Q v w‖≤Q^(6*e) := (coordW_norm_le Q hQ0 v w hv.le).trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith))
  have hq : ‖(Q:ℂ)^(-w)‖≤Q^(6*e) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
  obtain ⟨hVT,hDT,hET,hBET⟩ := central_unramified_error_weights Q a e A eta v x w z
    hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  have hi := selected_phase_identities Q eta v x w hQ0 heta hv
  have hh := central_phase_error_bound (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w)) (star v)
    (Q^(6*e)) (Q^(-(51/100:ℝ))) hL hV hD hW hq (by rw [norm_star,hv])
    hVT hDT hET hBET hi.1 hi.2
  simpa only [unramifiedSelected,unramifiedClosed,unramifiedMarked] using hh

end SevenEighths.ProbeEuler
end

end OAI

end Source2236

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CentralSlots.lean; sha256: 18d547251edc7de4f56eaa64fac728d85f15be12ae1e8fc14b0b2b193f60aa61 -/
section Source2237
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeLocal
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma row_phase_norm_one_of_not_dvd (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) :
    ‖idealRowHom u.val P.val‖=1 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg := supported_prime_data p hp (hspan.symm ▸ hs)
  have hnot : ¬p∣u.val := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hu : IsCoprime u.val p := (hp.irreducible.coprime_iff_not_dvd.mpr hnot).symm
  have he : idealRowHom u.val P.val=actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    rw [←hspan,idealRowHom_prime u.val (Ideal.span {p}) hg.1]
  rw [he]
  exact Complex.norm_eq_one_of_pow_eq_one (actualSextic_unit_six p u.val hg.1 hg.2 hu) (by decide)

theorem actual_central_unramified_error (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (4:ℝ)≤P.val.absNorm)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖continuedCompensatedLocal η u P hs x w z
        (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))+
      idealUnramifiedCorrection η u P x w z*star (idealRowHom u.val P.val)‖≤
        720*(P.val.absNorm:ℝ)^(-(51/100:ℝ)) := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hV : ‖coordV P.val.absNorm z‖<1 := by
    rw [coordV_norm _ hQ0]
    exact (rpow_le_half _ _ hQ (by rw [hz];norm_num)).trans_lt (by norm_num)
  have hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1 :=
    (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η _)).trans_lt
      ((rpow_le_half _ _ hQ (by rw [hx,hz];linarith)).trans_lt (by norm_num))
  rw [continuedCompensatedLocal_unramified η u P hs hn x w z hV hR]
  exact unramifiedSelected_central_error _ a e _ _ _ x w z hQ ha ha1 he he1
    (actualAPhase_norm_le_one η _)
    (PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero hη)
    (row_phase_norm_one_of_not_dvd u P hs hn) hx hw hz

end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source2237

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsCentralQuotient.lean; sha256: 74e747c8a4410722b01e663dc4d9a31ca12447f522a6ff688051af6e8e05e3f5 -/
section Source2238
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma unramifiedClosed_central_lower (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 480≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖unramifiedClosed Q A eta v x w z‖ := by
  have hQ0 : 0<Q := by linarith
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (10*e)
    (by linarith) hA heta hv (by positivity) (by rw [hx];linarith)
    (by rw [hz]) (by rw [hw];linarith) (by rw [hx,hw];linarith)
  have hp : Q^(-1-min (10*e) (1/50:ℝ))≤Q^(-1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by
      have hm : 0≤min (10*e) (1/50:ℝ) := by positivity
      linarith)
  have hi : Q^(-1:ℝ)≤1/480 := by
    rw [Real.rpow_neg_one,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) hQ
  have ht := norm_sub_le (1:ℂ) (unramifiedClosed Q A eta v x w z)
  have ht' := norm_add_le (1-unramifiedClosed Q A eta v x w z)
    (unramifiedClosed Q A eta v x w z)
  rw [sub_add_cancel,norm_one,norm_sub_rev] at ht'
  nlinarith

lemma unramifiedSelected_central_quotient (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 480≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖unramifiedSelected Q A eta v x w z/unramifiedClosed Q A eta v x w z+star v‖≤
      1440*Q^(-(51/100:ℝ)) := by
  have hh := unramifiedClosed_central_lower Q a e A eta v x w z hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  have hn : unramifiedClosed Q A eta v x w z≠0 := by
    intro hz;rw [hz,norm_zero] at hh;norm_num at hh
  have hp : 0<‖unramifiedClosed Q A eta v x w z‖ := by linarith
  have hb := unramifiedSelected_central_error Q a e A eta v x w z
    (by linarith) ha ha1 he he1 hA heta hv hx hw hz
  have hid : unramifiedSelected Q A eta v x w z/unramifiedClosed Q A eta v x w z+star v=
      (unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v)/
      unramifiedClosed Q A eta v x w z := by field_simp
  rw [hid,norm_div]
  apply (div_le_iff₀ hp).mpr
  have ht : 0≤Q^(-(51/100:ℝ)) := Real.rpow_nonneg (by linarith) _
  nlinarith
end SevenEighths.ProbeEuler
end

end OAI

end Source2238

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CentralNormalized.lean; sha256: 0a8731c99e036e8d654681925166f7178f1ae1ffe5a772dcee41080388ec41ac -/
section Source2239
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeLocal
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge

theorem actual_central_unramified_normalized (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (480:ℝ)≤P.val.absNorm)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖idealUnramifiedCorrection η u P x w z‖ ∧
    ‖continuedCompensatedLocal η u P hs x w z
        (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
      idealUnramifiedCorrection η u P x w z+star (idealRowHom u.val P.val)‖≤
        1440*(P.val.absNorm:ℝ)^(-(51/100:ℝ)) := by
  have heta := PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero hη
  have hv := row_phase_norm_one_of_not_dvd u P hs hn
  have hA := actualAPhase_norm_le_one η (primaryGenerator P.val)
  constructor
  · exact unramifiedClosed_central_lower _ a e _ _ _ x w z hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  · have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
    have hV : ‖coordV P.val.absNorm z‖<1 := by
      rw [coordV_norm _ hQ0]
      exact (rpow_le_half _ _ (by linarith) (by rw [hz];norm_num)).trans_lt (by norm_num)
    have hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1 :=
      (coordR_norm_le _ hQ0 _ x z hA).trans_lt
        ((rpow_le_half _ _ (by linarith) (by rw [hx,hz];linarith)).trans_lt (by norm_num))
    rw [continuedCompensatedLocal_unramified η u P hs hn x w z hV hR]
    exact unramifiedSelected_central_quotient _ a e _ _ _ x w z hQ ha ha1 he he1 hA heta hv hx hw hz
end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source2239
