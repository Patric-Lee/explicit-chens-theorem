import OpenAIGrouped.Unit052
import OpenAIGrouped.Unit025
import OpenAIGrouped.Unit050
import OpenAIGrouped.Unit051
import OpenAIGrouped.Unit046
import OpenAIGrouped.Unit021
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit047

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Energy/ReferenceDeletionEnergy.lean; sha256: 59099173356976dd46dbe2da258e91064989c602748d3b2660281a6d5d168dcd -/
section Source2120
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceDeletionEnergy
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceSource CenteredMomentEnergyReferenceWeightedEnergy
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentRadialPolynomialEnergy
open CenteredMomentCommonMaskRadialEnergy CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

theorem original_energy_weighted_deletion (bslot M:α→ℝ)(hM:∀i,0≤M i)
    (ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(Z Bmask bΦ a b:ℝ)(s:NaturalState Z Bmask bΦ)
      (W₁ W₂:𝓢(ℝ,ℂ)),0<a → 0≤b →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
        (t X₁ X₂ E p:ℝ),
      (∀i,∀I∈pool i,Prime I) → (∀i,0<P i) →
      (∀i,∀I∈pool i,‖β i I‖≤M i) →
      (∀i,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤bslot i*P i) →
      0<X₁ → 0<X₂ → 0≤E → p≤1 →
      (∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
       ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
       ∀J∈(Finset.univ:Finset α).powerset,
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
          polynomial (naturalCharacter s.character z) false W₂
          (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
          ∏i∈Finset.univ\J,naturalSlot (naturalCharacter s.character z) (pool i)
            (heightCoefficient (β i) t) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale
            ≤E*((∏I∈D₂,I).absNorm:ℝ)^p) →
      energy s.character s.mask 1 t W₁ W₂ pool β P X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤C*(s.puncture.radical.absNorm:ℝ)^ε*E:=by
  obtain ⟨C,hC,hmass⟩:=CenteredMomentEnergyReferenceDeletionBudget.weighted_uniform_mass_subpower
    (Finset.univ:Finset α) bslot M (fun i _=>hM i) (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro Z Bmask bΦ a b s W₁ W₂ ha hb hs₁ hs₂ pool β P t X₁ X₂ E p hp hP hβ hs hX₁ hX₂ hE hple hchildren
  let R:=CompletedGauss.primeSupport s.puncture
  have hR:∀I∈R,Prime I:=support_prime s.puncture
  let κ:={D:Finset (Ideal O)//D∈R.powerset}×
    {D:Finset (Ideal O)//D∈R.powerset}×{J:Finset α//J∈(Finset.univ:Finset α).powerset}
  let cf(z:O)(j:κ):=signedCoefficient (naturalCharacter s.character z) R j.1.val j.2.1.val j.2.2.val
    pool (fun i=>heightCoefficient (β i) t) P
  let f(z:O)(j:κ):=polynomial (naturalCharacter s.character z) false W₁
    (X₁/((∏I∈j.1.val,I).absNorm:ℝ)) 0 t *
    polynomial (naturalCharacter s.character z) false W₂
    (X₂/((∏I∈j.2.1.val,I).absNorm:ℝ)) 0 t *
    ∏i∈Finset.univ\j.2.2.val,naturalSlot (naturalCharacter s.character z) (pool i)
      (heightCoefficient (β i) t) (P i)
  let ρ(j:κ):=uniformMajorant R j.1.val j.2.1.val j.2.2.val bslot M
  let q(j:κ):=((∏I∈j.2.1.val,I).absNorm:ℝ)^(p/2)
  have hρ(j:κ):0≤ρ j:=uniformMajorant_nonneg _ _ _ _ _ _ (fun i _=>hM i)
  have hq(j:κ):0≤q j:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hn(D:Finset (Ideal O))(hD:D∈R.powerset):0<((∏I∈D,I).absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun I hi=>(hR I (Finset.mem_powerset.mp hD hi)).ne_zero)))
  have hcf(z:O)(j:κ):‖cf z j‖≤ρ j:=by
    apply signedCoefficient_uniform _ R hR _ _ (Finset.mem_powerset.mp j.1.property)
      (Finset.mem_powerset.mp j.2.1.property) _ pool (fun i=>heightCoefficient (β i) t) P bslot M
      (fun i _=>hp i) (fun i _=>hP i) (fun i _=>hM i)
    · intro i _ I hI
      rw [heightCoefficient_norm _ _ _ (hp i I hI).ne_zero]
      exact hβ i I hI
    · intro i _ I hI hnz
      exact hs i I hI (left_ne_zero_of_mul hnz)
  have hsum(j:κ):Summable (fun z:O=>if (effectiveState s).radial.keep z then
      ‖f z j‖^2*(s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)).re else 0):=by
    obtain ⟨B,hB,hbound⟩:=slots_bounded (Finset.univ\j.2.2.val) pool (fun i=>heightCoefficient (β i) t) P
    exact pair_radial_summable (naturalCharacter s.character)
      (fun z=>∏i∈Finset.univ\j.2.2.val,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (β i) t) (P i)) (fun _=>t) (fun _=>t) W₁ W₂ a b a b
      (X₁/((∏I∈j.1.val,I).absNorm:ℝ)) (X₂/((∏I∈j.2.1.val,I).absNorm:ℝ)) B hb hb
      (div_pos hX₁ (hn _ j.1.property)) (div_pos hX₂ (hn _ j.2.1.property)) hs₁ hs₂
      (fun z=>hbound _) (effectiveState s).radial.keep s.radial.profile s.radial.scale s.radial.scale_pos
  have hchild(j:κ):radialEnergy (fun z=>f z j) (effectiveState s).radial.keep
      s.radial.profile s.radial.scale≤E*(q j)^2:=by
    have hh:=hchildren j.1.val j.1.property j.2.1.val j.2.1.property j.2.2.val j.2.2.property
    have hpow:(q j)^2=((∏I∈j.2.1.val,I).absNorm:ℝ)^p:=by
      dsimp only [q]
      rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      norm_num
    rw [hpow]
    exact hh
  have he:=radial_weighted_energy cf f ρ q hρ hq (effectiveState s).radial.keep s.radial.profile
    s.radial.scale E s.radial.nonneg (fun z _=>hcf z) hE hsum hchild
  have hid(z:O):(∑j:κ,cf z j*f z j)=signedCommonSource s W₁ W₂ pool β P t X₁ X₂ z:=
    triple_sum R.powerset R.powerset (Finset.univ:Finset α).powerset
      (fun D₁ D₂ J=>signedCoefficient (naturalCharacter s.character z) R D₁ D₂ J
        pool (fun i=>heightCoefficient (β i) t) P *
        (polynomial (naturalCharacter s.character z) false W₁ (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
         polynomial (naturalCharacter s.character z) false W₂ (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
         ∏i∈Finset.univ\J,naturalSlot (naturalCharacter s.character z) (pool i) (heightCoefficient (β i) t) (P i)))
  simp_rw [hid] at he
  rw [←original_energy_eq_signed s W₁ W₂ ha hs₁ hs₂ pool hp β P hP t X₁ X₂ hX₁ hX₂] at he
  have hm:(∑j:κ,ρ j*q j)≤C*((∏I∈R,I).absNorm:ℝ)^(ε/2):=by
    exact (triple_sum R.powerset R.powerset (Finset.univ:Finset α).powerset
      (fun D₁ D₂ J=>uniformMajorant R D₁ D₂ J bslot M*((∏I∈D₂,I).absNorm:ℝ)^(p/2))).trans_le
      (hmass R hR (p/2) (by linarith))
  have hr:(((∏I∈R,I).absNorm:ℝ)^(ε/2))^2=(s.puncture.radical.absNorm:ℝ)^ε:=by
    rw [CenteredMomentAllocatedNaturalSource.primeSupport_product_radical s.puncture s.puncture_ne_zero]
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  exact he.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _=>mul_nonneg (hρ j) (hq j))) hm 2) hE).trans_eq
    (by rw [mul_pow,hr]))

end SevenEighths.CenteredMomentEnergyReferenceDeletionEnergy

end

end OAI

end Source2120

/- Original source: OAI/NumberTheory/DirichletL/Energy/OriginalHighReflectionOriginal.lean; sha256: e1db9eb81af6631eca0ac3546f58a29cbe876fff64e06a70b68ea7164147778c -/
section Source2121
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionGeometry CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyOriginalHighReflectionDeleted CenteredMomentEnergyReferenceDeletionEnergy
open CenteredMomentInductionEnergy
theorem original_high_from_low
    (epsilonDelete:ℝ)(hepsilonDelete:0<epsilonDelete)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0<C ∧ 0<D ∧ 0<Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap → xi≤s.width/14 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      length Z X₁≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i))) :=by
  obtain ⟨Bslot,hBslot,hslot⟩:=CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=α)
    (fun _=>bslot) (fun _=>Bslot) (fun _=>hBslot.le) epsilonDelete hepsilonDelete
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=deleted_original_from_low (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving Mcap Bmask L ha hlo hhi hbΦ hepsilon hxi hBmask hL B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,Cweight,hC,hD,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  apply hweight Z Bmask bΦ a b s W₁ W₂ ha (by linarith) hs₁ hs₂
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) t X₁ X₂ _ 0
  · intro i I hI
    exact (Finset.mem_filter.mp hI).2.1
  · intro i
    exact Real.rpow_pos_of_pos hZpos _
  · intro i I hI
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh
  · intro i I hI hn
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).2
    apply hh
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hX₁
  · exact hX₂
  · have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤L:=by linarith [s.width_nonneg]
    have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simpa only [Real.rpow_zero,mul_one] using hZ.2 Lslot ε κ η₀ Q K hK hlow
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hs hxiM
      W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap D₁ hD₁ D₂ hD₂ (Finset.univ\J)

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionOriginal

end

end OAI

end Source2121

/- Original source: OAI/NumberTheory/DirichletL/Energy/ReferenceScalarBounds.lean; sha256: de02784a2f1354d7134882c01b9a2b1071def5af974e1bd0141fa19d62762d1e -/
section Source2122
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceScalarBounds
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource

lemma radical_power {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(d:ℝ)(hd:0≤d):
    (s.puncture.radical.absNorm:ℝ)^d≤Z^(Bmask*d):=by
  have hh:=Real.rpow_le_rpow (Nat.cast_nonneg _) s.radical_bound hd
  simpa only [←Real.rpow_mul (zero_lt_one.trans_le s.base_ge_one).le] using hh

lemma conductor_power {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (Mcap d:ℝ)(hs:s.width≤Mcap)(hd:0≤d):
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))^d*Z^(Mcap*d):=by
  have hZ:0<Z:=zero_lt_one.trans_le s.base_ge_one
  have hM:0≤Mcap:=s.width_nonneg.trans hs
  have hz:1≤Z^Mcap:=Real.one_le_rpow s.base_ge_one hM
  have hc:1≤max 1 ((fixedConductorFactor:ℝ)*bΦ):=le_max_left _ _
  have hbase:max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))*Z^Mcap:=by
    apply max_le
    · nlinarith
    · apply le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hZ.le _))
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le s.base_ge_one hs)
        (zero_le_one.trans hc)
  have hh:=Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) hbase hd
  rw [Real.mul_rpow (zero_le_one.trans hc) (Real.rpow_nonneg hZ.le _),←Real.rpow_mul hZ.le] at hh
  exact hh

lemma radial_scale {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):
    max 1 s.radial.scale≤Z^s.width:=by
  rw [s.scale_eq]
  apply max_le (Real.one_le_rpow s.base_ge_one s.width_nonneg)
  apply Real.rpow_le_rpow_of_exponent_le s.base_ge_one
  exact le_add_of_nonneg_right s.character_nonneg

lemma physical_slot_product {α:Type*}[Fintype α](Z:ℝ)(hZ:1≤Z)(w:α→ℝ)(Mcap:ℝ)
    (hwidth:(∑i,w i)≤Mcap): (∏i,Z^(w i))≤Z^Mcap:=by
  rw [←Real.rpow_sum_of_pos (zero_lt_one.trans_le hZ)]
  exact Real.rpow_le_rpow_of_exponent_le hZ hwidth

lemma short_slot_mass {α:Type*}[Fintype α]{Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (Mcap:ℝ)(hs:s.width≤Mcap)(w:α→ℝ)(hwidth:(∑i,w i)≤Mcap):
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))≤Z^(s.width+5*Mcap/4):=by
  have hz:0<Z:=zero_lt_one.trans_le s.base_ge_one
  calc
    _≤Z^s.width*Z^(Mcap/4)*Z^Mcap:=by
      apply mul_le_mul (mul_le_mul (radial_scale s)
        (Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith))
        (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
        (physical_slot_product Z s.base_ge_one w Mcap hwidth)
        (Finset.prod_nonneg (fun i _=>Real.rpow_nonneg hz.le _)) (by positivity)
    _=Z^(s.width+5*Mcap/4):=by rw [←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring

lemma log_interval (Z L d:ℝ)(hZ:1≤Z)(hL:0≤L)(hd:0<d):
    1+2*(L*Real.log Z)≤(1+2*L/d)*Z^d:=by
  have hlog:=Real.log_le_rpow_div (zero_le_one.trans hZ) hd
  have hone:=Real.one_le_rpow hZ hd.le
  have hh:=mul_le_mul_of_nonneg_left hlog (show 0≤2*L by positivity)
  calc
    _≤Z^d+2*L*(Z^d/d):=by nlinarith
    _=(1+2*L/d)*Z^d:=by ring

end SevenEighths.CenteredMomentEnergyReferenceScalarBounds

end

end OAI

end Source2122

/- Original source: OAI/NumberTheory/DirichletL/Energy/ReferenceScalarReserve.lean; sha256: 6030ffd0e471ca53c2278286c0b5a9d82bc4f10c4cfeae5da84d96d0b3b0be92 -/
section Source2123
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceScalarReserve
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyReferenceScalarBounds

theorem ledger_bound (Mcap Bmask bΦ L d saving ε:ℝ)
    (hM:0≤Mcap)(_hB:0≤Bmask)(hL:0≤L)(hd:0<d)
    (hmain:d*(Bmask+Mcap+2)≤ε)
    (herror:Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*
        (Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
           (1+2*(L*Real.log Z))*Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
           max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))) ≤C*Z^(s.width+ε):=by
  let A:ℝ:=max 1 ((fixedConductorFactor:ℝ)*bΦ)
  let B:ℝ:=1+2*L/d
  have hA:0<A:=zero_lt_one.trans_le (le_max_left _ _)
  have hBpos:0<B:=by dsimp only [B];positivity
  refine ⟨1+A^d*B+A^(2*d),by positivity,?_⟩
  intro Z hZ s hs α inst w hw
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hr:=radical_power s d hd.le
  have hc:=conductor_power s Mcap d hs hd.le
  have hc₂:=conductor_power s Mcap (2*d) hs (by positivity)
  have hl:=log_interval Z L d hZ hL hd
  have hm:=short_slot_mass s Mcap hs w hw
  have hdirect:(s.puncture.radical.absNorm:ℝ)^d*Z^(s.width+d)≤Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*Z^(s.width+d):=mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hz.le _)
      _=Z^(s.width+d*(Bmask+1)):=by rw [←Real.rpow_add hz];congr 1;ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)
  have hreflect:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
        (1+2*(L*Real.log Z))*Z^(s.width+d))≤A^d*B*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^d*Z^(Mcap*d)*(B*Z^d)*Z^(s.width+d)):=by
        gcongr
      _=A^d*B*Z^(s.width+d*(Bmask+Mcap+2)):=by
        calc
          _=A^d*B*(Z^(Bmask*d)*Z^(Mcap*d)*Z^d*Z^(s.width+d)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 2;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  have herrorTerm:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
        max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤A^(2*d)*Z^(s.width+ε):=by
    calc
      _=(s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          (max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))):=by ring
      _≤Z^(Bmask*d)*(A^(2*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^(s.width+5*Mcap/4)):=by
        gcongr
      _=A^(2*d)*Z^(s.width+(Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4)):=by
        calc
          _=A^(2*d)*(Z^(Bmask*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^(s.width+5*Mcap/4)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 1;congr 1;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  calc
    _≤Z^(s.width+ε)+A^d*B*Z^(s.width+ε)+A^(2*d)*Z^(s.width+ε):=by
      simpa only [mul_add] using add_le_add (add_le_add hdirect hreflect) herrorTerm
    _=_:=by ring

theorem exists_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0<rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
      ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*
        (Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
           (1+2*(L*Real.log Z))*Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
           max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))) ≤C*Z^(s.width+ε):=by
  let d:=ε/(4*(Bmask+Mcap+2))
  let xi:=rho/100
  let saving:=2*Mcap+Bmask*d+2*Mcap*d+1
  let L:=Mcap+Bmask+xi+1
  have hd:0<d:=by dsimp only [d];positivity
  have hxi:0<xi:=by dsimp only [xi];positivity
  have hsave:0<saving:=by dsimp only [saving];positivity
  have hL:0≤L:=by dsimp only [L];positivity
  have hmain:d*(Bmask+Mcap+2)≤ε:=by
    dsimp only [d]
    have hp:0<Bmask+Mcap+2:=by positivity
    field_simp
    nlinarith
  have herror:Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε:=by
    dsimp only [saving]
    nlinarith [mul_nonneg hB hd.le,mul_nonneg hM hd.le]
  obtain ⟨C,hC,hledger⟩:=ledger_bound Mcap Bmask bΦ L d saving ε hM hB hL hd hmain herror
  exact ⟨d,xi,saving,L,C,hd,hxi,hsave,hC,le_rfl,by dsimp only [L];linarith,hledger⟩

end SevenEighths.CenteredMomentEnergyReferenceScalarReserve

end

end OAI

end Source2123

/- Original source: OAI/NumberTheory/DirichletL/Energy/ReferenceProfileBudget.lean; sha256: 3f18bae0e325a27898553735564f63b4b382d4de6546bff5d5afd26f24781d77 -/
section Source2124
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional

lemma control_mono {S T:Finset (ℕ×ℕ)}(h:S⊆T)(W:𝓢(ℝ,ℂ)):
    sourceControl S W≤sourceControl T W:=Seminorm.le_def.mp (Finset.sup_mono h) W

theorem reference_envelopes (a b:ℝ)(ha:0<a)
    (S T Slong:Finset (ℕ×ℕ))(degree n nlong:ℕ)(Cref Dchild Dref:ℝ)
    (hCr:0<Cref)(hDc:0<Dchild)(hDr:0<Dref):
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W₁ W₂:𝓢(ℝ,ℂ),∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,∀t height:ℝ,0≤height →
      let E:=C*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J;
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*(1+|t|+height)^degree≤E ∧
      Cref*Dchild*(sourceControl Slong W₂)^2*(sourceControl T W₁)^2*
        (1+‖t‖)^(2*nlong)*(1+|t|+height)^(degree+2*n)≤E ∧
      Dref*(sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
        (1+‖t‖)^(2*nlong)≤E:=by
  obtain ⟨na,Ta,Ca,hCa,hprof⟩:=independent_profile_control a b ha S
  let U:=((Ta∪T)∪Slong)∪{(0,0)}
  let J:=degree+4*na+2*n+2*nlong
  let C:=1+Ca^2*2^(4*na)+Cref*Dchild+Dref
  have hC:0<C:=by dsimp only [C];positivity
  refine ⟨J,U,C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only
  let H:=1+|t|+height
  let A:=sourceControl U W₁*sourceControl U W₂
  have hH:1≤H:=by dsimp only [H];linarith [abs_nonneg t]
  have hH0:0≤H:=zero_le_one.trans hH
  have hA:0≤A:=mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have haU:Ta⊆U:=by intro x hx;simp [U,hx]
  have hTU:T⊆U:=by intro x hx;simp [U,hx]
  have hlU:Slong⊆U:=by intro x hx;simp [U,hx]
  have hzU:(0,0)∈U:=by simp [U]
  have hz:(schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁≤sourceControl U W₁:=
    Seminorm.le_def.mp (Finset.le_sup hzU) W₁
  have hp:(independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S≤Ca*A*(2*H)^(2*na):=by
    apply (hprof W₁ W₂ hs₁ hs₂ t t).trans
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left _ hCa.le
      exact mul_le_mul (control_mono haU W₁) (control_mono haU W₂)
        (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
    · apply pow_le_pow_left₀ (by positivity)
      dsimp only [H]
      simp only [Real.norm_eq_abs]
      linarith [abs_nonneg t]
    · positivity
    · positivity
  have hd:(independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S^2*H^degree≤
      (Ca^2*2^(4*na))*A^2*H^J:=by
    have hsq:=pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2
    have hmul:=mul_le_mul_of_nonneg_right hsq (pow_nonneg hH0 degree)
    have hid:(Ca*A*(2*H)^(2*na))^2*H^degree=
        (Ca^2*2^(4*na))*A^2*H^(degree+4*na):=by
      rw [mul_pow,mul_pow,←pow_mul,show (2*na)*2=4*na by omega,mul_pow,pow_add]
      ring_nf
    rw [hid] at hmul
    exact hmul.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hH (by dsimp only [J];omega)) (by positivity))
  have hm:(sourceControl Slong W₂)^2*(sourceControl T W₁)^2≤A^2:=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
    dsimp only [A]
    simpa only [mul_comm] using mul_le_mul (control_mono hTU W₁) (control_mono hlU W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have he:(sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2≤A^2:=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (apply_nonneg _ _))
    dsimp only [A]
    simpa only [mul_comm] using mul_le_mul hz (control_mono hlU W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hheightpow:(1+‖t‖)^(2*nlong)≤H^(2*nlong):=by
    apply pow_le_pow_left₀ (by positivity)
    dsimp only [H]
    simp only [Real.norm_eq_abs]
    linarith
  have hcm: Cref*Dchild≤C:=by dsimp only [C];nlinarith [sq_nonneg Ca,pow_nonneg (show (0:ℝ)≤2 by norm_num) (4*na)]
  have hce:Dref≤C:=by dsimp only [C];nlinarith [sq_nonneg Ca,pow_nonneg (show (0:ℝ)≤2 by norm_num) (4*na)]
  have hcd:Ca^2*2^(4*na)≤C:=by dsimp only [C];nlinarith
  refine ⟨hd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcd (sq_nonneg A)) (pow_nonneg hH0 J)),?_,?_⟩
  · calc
      _=(Cref*Dchild)*((sourceControl Slong W₂)^2*(sourceControl T W₁)^2)*
          ((1+‖t‖)^(2*nlong)*H^(degree+2*n)):=by ring
      _≤C*A^2*(H^(2*nlong)*H^(degree+2*n)):=by gcongr
      _≤C*A^2*H^J:=by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (sq_nonneg A))
        rw [←pow_add]
        exact pow_le_pow_right₀ hH (by dsimp only [J];omega)
  · calc
      _=Dref*((sourceControl Slong W₂)^2*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2)*(1+‖t‖)^(2*nlong):=by ring
      _≤C*A^2*H^(2*nlong):=by gcongr
      _≤C*A^2*H^J:=mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hH (by dsimp only [J];omega)) (mul_nonneg hC.le (sq_nonneg A))

end SevenEighths.CenteredMomentEnergyReferenceProfileBudget

end

end OAI

end Source2124

/- Original source: OAI/NumberTheory/DirichletL/Energy/OriginalHighReflectionPower.lean; sha256: 205516f6343f3e600ac9734a52547915804a43b3355d3f27c1d78066af85b68c -/
section Source2125
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionPower
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_high_power
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      length Z X₁≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hscalar⟩:=
    exists_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_high_from_low (α:=α) M H hH d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi hBmask hL 2 (by norm_num) degree S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong degree n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hxiM:xi≤s.width/14:=by linarith
  have hh:=hZ.2 Lslot d κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hsumcap:(∑i,w i)≤Mcap:=by
    have hlen₁:=length_nonneg Z X₁ hZ.1
    have hlen₂:=length_nonneg Z X₂ hZ.1
    have hk:=mul_le_mul_of_nonneg_right (show (1:ℝ)≤6*κ by linarith) hsum
    nlinarith
  have hledger:=hscalar Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤A:=by dsimp only [A];positivity
  have hE:0≤E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left hdiag (le_add_of_nonneg_left hK)) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤L:=by linarith
  let P:=Z^(s.width+d)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+d)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
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

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionPower

end

end OAI

end Source2125

/- Original source: OAI/NumberTheory/DirichletL/Energy/OriginalHighReflectionSymmetric.lean; sha256: 119005d30ab4de4c2dd2cac2cba4662c7606ed27ac28ae3aad3ff73cddbcce69 -/
section Source2126
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetric
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionPower
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

omit [DecidableEq α] in
lemma energy_swap (η:Character)(m A:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K=
      energy η m A t W₂ W₁ pool β P X₂ X₁ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  have hh:positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂=
      positiveSlotRow η m A z W₂ W₁ pool β P t X₂ X₁:=by
    unfold positiveSlotRow
    rw [mul_comm X₁ X₂]
    ring
  rw [hh]

theorem balanced_four_scale_gates (Z width X₁ X₂:ℝ)(hZ:1<Z)(hwidth:0<width)
    (hX₁:0<X₁)(hX₂:0<X₂)
    (hshort:width/4≤min (length Z X₁) (length Z X₂)):
    Z^(width/4)≤X₁ ∧ Z^(width/4)≤X₂ ∧
    Z^(width/4)≤comparisonFirst Z width ∧
    Z^(width/4)≤comparisonSecond Z width X₁ X₂ ∧
    length Z X₁+length Z X₂=Real.logb Z (X₁*X₂):=by
  have h₁:width/4≤length Z X₁:=hshort.trans (min_le_left _ _)
  have h₂:width/4≤length Z X₂:=hshort.trans (min_le_right _ _)
  have hraw (X:ℝ)(hX:0<X)(h:width/4≤length Z X):
      length Z X=Real.logb Z X ∧ width/4≤Real.logb Z X:=by
    have he:=CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z X hZ hX
    have hp:0<Real.logb Z X:=by
      by_contra hn
      rw [he,max_eq_left (le_of_not_gt hn)] at h
      linarith
    refine ⟨he.trans (max_eq_right hp.le),?_⟩
    rwa [he,max_eq_right hp.le] at h
  obtain ⟨he₁,hr₁⟩:=hraw X₁ hX₁ h₁
  obtain ⟨he₂,hr₂⟩:=hraw X₂ hX₂ h₂
  refine ⟨?_,?_,le_refl _,?_,?_⟩
  · simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX₁] using
      Real.rpow_le_rpow_of_exponent_le hZ.le hr₁
  · simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX₂] using
      Real.rpow_le_rpow_of_exponent_le hZ.le hr₂
  · rw [comparison_second_power Z width X₁ X₂ hZ hX₁ hX₂,
      Real.logb_mul hX₁.ne' hX₂.ne']
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · rw [he₁,he₂,Real.logb_mul hX₁.ne' hX₂.ne']

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_unbalanced_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      min (length Z X₁) (length Z X₂)≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=original_high_power (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  rcases min_le_iff.mp hshort with hshort|hshort
  · exact hZ.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · rw [energy_swap]
    have hh:=hZ.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₂ W₁ hs₂ hs₁ X₂ X₁ hX₂ hX₁ hshort (by linarith) (by linarith)
    simpa only [mul_comm (sourceControl U W₂) (sourceControl U W₁)] using hh

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetric

end

end OAI

end Source2126

/- Original source: OAI/NumberTheory/DirichletL/Energy/LiveClippingDefect.lean; sha256: 2976bdb1d6a1497f4e3f72a09cb53792dde3bcf5e96c79b8ed72263978e8a5da -/
section Source2127
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyLiveClippingDefect
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentRetainedEnergy
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

theorem rowTwistedSum_support_witness (η : Character) (m A z : O)
    (W : ℝ → ℂ) (t X : ℝ) (h : rowTwistedSum η m A z W t X ≠ 0) :
    ∃ I : Ideal O, I ≠ 0 ∧ W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold rowTwistedSum
  calc
    _ = ∑' _I : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro I
      by_cases hI : I = 0
      · subst I
        rw [idealCoeff_zero, zero_mul, zero_mul, zero_mul]
      · rw [hn I hI, mul_zero]
    _ = 0 := tsum_zero

theorem rowTwistedSum_support_scale (η : Character) (m A z : O)
    (W : ℝ → ℂ) (t X b : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b)
    (h : rowTwistedSum η m A z W t X ≠ 0) : 1 ≤ b * X := by
  obtain ⟨I, hI, hW⟩ := rowTwistedSum_support_witness η m A z W t X h
  have hn : (1 : ℝ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hn.trans ((div_le_iff₀ hX).mp (hs hW))

variable {ι : Type*} [Fintype ι]

theorem positiveSlotRow_support_scales (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ b : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (h : positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ ≠ 0) :
    1 ≤ b * X₁ ∧ 1 ≤ b * X₂ := by
  have hp := left_ne_zero_of_mul (right_ne_zero_of_mul h)
  exact ⟨rowTwistedSum_support_scale η m A z W₁ t X₁ b hX₁ hs₁
      (left_ne_zero_of_mul hp),
    rowTwistedSum_support_scale η m A z W₂ t X₂ b hX₂ hs₂
      (right_ne_zero_of_mul hp)⟩

theorem positiveSlotRow_profiles_scales (η : Character) (m A z : O)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (h : positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ ≠ 0) :
    1 ≤ b * X₁ ∧ 1 ≤ b * X₂ := by
  exact positiveSlotRow_support_scales η m A z _ _ S β P t X₁ X₂ b hX₁ hX₂
    (fun _ hx => (p.support 0 hx).2) (fun _ hx => (p.support 1 hx).2) h

theorem length_le_raw_add_endpoint (Z X b : ℝ) (hZ : 1 < Z) (hX : 0 < X)
    (hs : 1 ≤ b * X) : length Z X ≤ Real.logb Z X + Real.logb Z (max 1 b) := by
  have hB : 0 < max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  have hc : max 1 X ≤ max 1 b * X := by
    apply max_le
    · exact hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hX.le)
    · simpa using mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) b) hX.le
  have hh := Real.logb_le_logb_of_le hZ
    (zero_lt_one.trans_le (le_max_left (1 : ℝ) X)) hc
  rw [Real.logb_mul hB.ne' hX.ne'] at hh
  simpa [length, add_comm] using hh

theorem total_clipping_defect (Z X₁ X₂ b : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hs₁ : 1 ≤ b * X₁) (hs₂ : 1 ≤ b * X₂) :
    length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
      2 * Real.logb Z (max 1 b) := by
  have h1 := length_le_raw_add_endpoint Z X₁ b hZ hX₁ hs₁
  have h2 := length_le_raw_add_endpoint Z X₂ b hZ hX₂ hs₂
  rw [Real.logb_mul hX₁.ne' hX₂.ne']
  linarith

theorem endpoint_threshold (b δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      2 * Real.logb Z (max 1 b) ≤ δ := by
  let Z₀ := Real.exp (1 + 2 * Real.log (max 1 b) / δ)
  have hb : 0 ≤ Real.log (max 1 b) := Real.log_nonneg (le_max_left _ _)
  have he : 0 < 1 + 2 * Real.log (max 1 b) / δ := by positivity
  have hZ₀ : 1 < Z₀ := Real.one_lt_exp_iff.mpr he
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZZ
  have hZ : 1 < Z := hZ₀.trans_le hZZ
  have hlog := Real.log_le_log (Real.exp_pos _) hZZ
  rw [Real.log_exp] at hlog
  have hbound : 2 * Real.log (max 1 b) ≤ δ * Real.log Z := by
    have hh : 2 * Real.log (max 1 b) / δ ≤ Real.log Z := by linarith
    exact (div_le_iff₀ hδ).mp hh |>.trans_eq (mul_comm _ _)
  rw [Real.logb, ← mul_div_assoc]
  exact (div_le_iff₀ (Real.log_pos hZ)).mpr hbound

theorem profiles_uniform_defect (a b δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ (η : Character) (m A z : O) (p : Profiles a b)
        (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
        (t X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
        positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ ≠ 0 →
        length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤ δ := by
  obtain ⟨Z₀, hZ₀, hh⟩ := endpoint_threshold b δ hδ
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZZ η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
  obtain ⟨h1, h2⟩ := positiveSlotRow_profiles_scales η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
  exact (total_clipping_defect Z X₁ X₂ b (hZ₀.trans_le hZZ) hX₁ hX₂ h1 h2).trans (hh Z hZZ)

theorem total_clipping_defect_nonneg (Z X₁ X₂ : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) := by
  have h1 := Real.logb_le_logb_of_le hZ hX₁ (le_max_right (1 : ℝ) X₁)
  have h2 := Real.logb_le_logb_of_le hZ hX₂ (le_max_right (1 : ℝ) X₂)
  rw [Real.logb_mul hX₁.ne' hX₂.ne']
  dsimp only [length]
  linarith

theorem positiveSlotRow_zero_or_defect (η : Character) (m A z : O)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ Z : ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0 ∨
    (0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ∧
      length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
        2 * Real.logb Z (max 1 b)) := by
  by_cases hrow : positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0
  · exact Or.inl hrow
  · obtain ⟨h1, h2⟩ := positiveSlotRow_profiles_scales η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
    exact Or.inr ⟨total_clipping_defect_nonneg Z X₁ X₂ hZ hX₁ hX₂,
      total_clipping_defect Z X₁ X₂ b hZ hX₁ hX₂ h1 h2⟩

theorem energy_support_witness (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (h : CenteredMomentInductionEnergy.energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K ≠ 0) :
    ∃ z : O, keep z ∧ positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold CenteredMomentInductionEnergy.energy
  calc
    _ = ∑' _z : O, (0 : ℝ) := by
      apply tsum_congr
      intro z
      by_cases hk : keep z
      · simp only [ite_eq_left hk, hn z hk, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
      · simp only [ite_eq_right hk]
    _ = 0 := tsum_zero

theorem energy_zero_or_defect (η : Character) (m A : O) (t : ℝ)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ Z : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    CenteredMomentInductionEnergy.energy η m A t (p.profile 0) (p.profile 1)
        S β P X₁ X₂ keep Φ K = 0 ∨
    (0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ∧
      length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
        2 * Real.logb Z (max 1 b)) := by
  by_cases h : CenteredMomentInductionEnergy.energy η m A t (p.profile 0) (p.profile 1)
      S β P X₁ X₂ keep Φ K = 0
  · exact Or.inl h
  · obtain ⟨z, _, hz⟩ := energy_support_witness η m A t _ _ S β P X₁ X₂ keep Φ K h
    exact Or.inr ((positiveSlotRow_zero_or_defect η m A z p S β P t X₁ X₂ Z hZ hX₁ hX₂).resolve_left hz)

theorem raw_gates_of_defect (Z M X₁ X₂ ell κ e : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hdefect : length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤ e)
    (hlarge : 5*M/6 ≤ length Z X₁ + length Z X₂ + ell)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*ell ≤ M) :
    5*M/6-e ≤ Real.logb Z (X₁ * X₂)+ell ∧
      Real.logb Z (X₁ * X₂)+ell+(6*κ-1)*ell ≤ M := by
  have hnonneg := total_clipping_defect_nonneg Z X₁ X₂ hZ hX₁ hX₂
  constructor <;> nlinarith

theorem robust_slot_budgets (M total ell kappa defect : ℝ)
    (hell : 0 ≤ ell) (hk : 3/4 ≤ kappa)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M) :
    ell ≤ M/21+2*defect/7 ∧ (6*kappa-1)*ell ≤ M/6+defect := by
  have hkell : 7/2*ell ≤ (6*kappa-1)*ell :=
    mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem robust_defect_le_width (M xi defect : ℝ) (hM : 0 ≤ M) (hxi : 0 ≤ xi)
    (hreserve : xi+11*defect/7 ≤ M/14) : defect ≤ M := by
  linarith

theorem robust_balanced_long_nonneg (M total ell kappa xi defect : ℝ)
    (hM : 0 ≤ M) (hell : 0 ≤ ell) (hk : 3/4 ≤ kappa) (hxi : 0 ≤ xi)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M)
    (hreserve : xi+11*defect/7 ≤ M/14) :
    15*M/28-9*defect/7 ≤ total-M/4 ∧ 0 ≤ total-M/4 := by
  obtain ⟨he, hb⟩ := robust_slot_budgets M total ell kappa defect hell hk hlarge hcap
  constructor <;> linarith

theorem robust_reflected_low (M short along ell z kappa xi defect reflected : ℝ)
    (hM : 0 ≤ M) (_hs : 0 ≤ short) (hsM : short ≤ M/4)
    (_hell : 0 ≤ ell) (_hz : 0 ≤ z) (hze : z ≤ ell) (hk : 3/4 ≤ kappa)
    (he : ell ≤ M/21+2*defect/7)
    (hbudget : (6*kappa-1)*ell ≤ M/6+defect)
    (hxi : 0 ≤ xi) (hdefect : 0 ≤ defect) (hdefectM : defect ≤ M)
    (hhigh : 5*M/6 < short+max 0 along+z)
    (href : reflected ≤ max 0 (M-along+xi)) :
    0 < along ∧ reflected+short+z ≤ 16*M/21+xi+4*defect/7 ∧
      reflected+short+6*kappa*z ≤ 13*M/14+xi+11*defect/7 := by
  have haz : 0 < along := by
    by_contra hn
    have ha : along ≤ 0 := le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget : (6*kappa-1)*z ≤ M/6+defect :=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap : z ≤ M/21+2*defect/7 := hze.trans he
  refine ⟨haz, ?_⟩
  by_cases hr : 0 ≤ M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem robust_reflected_low_admissible (M xi defect short reflected z kappa : ℝ)
    (hd : 0 ≤ defect) (hreserve : xi+11*defect/7 ≤ M/14)
    (ht : reflected+short+z ≤ 16*M/21+xi+4*defect/7)
    (hc : reflected+short+6*kappa*z ≤ 13*M/14+xi+11*defect/7) :
    reflected+short+z ≤ 5*M/6 ∧ reflected+short+6*kappa*z ≤ M := by
  constructor <;> linarith

theorem robust_deleted_cases (M total short along ell z kappa xi defect reflected : ℝ)
    (hM : 0 ≤ M) (hs : 0 ≤ short) (hsM : short ≤ M/4)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hk : 3/4 ≤ kappa)
    (hxi : 0 ≤ xi) (hd : 0 ≤ defect)
    (hreserve : xi+11*defect/7 ≤ M/14)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M)
    (halong : max 0 along ≤ total-M/4)
    (href : reflected ≤ max 0 (M-along+xi)) :
    (short+max 0 along+z ≤ 5*M/6 ∧ short+max 0 along+6*kappa*z ≤ M) ∨
    (0 < along ∧ reflected+short+z ≤ 5*M/6 ∧
      reflected+short+6*kappa*z ≤ M) := by
  obtain ⟨he,hbudget⟩ := robust_slot_budgets M total ell kappa defect hell hk hlarge hcap
  by_cases hlo : short+max 0 along+z ≤ 5*M/6
  · refine Or.inl ⟨hlo, ?_⟩
    have hzcap := mul_le_mul_of_nonneg_left hze (by linarith : 0 ≤ 6*kappa)
    nlinarith
  · obtain ⟨hapos, ht, hc⟩ := robust_reflected_low M short along ell z kappa xi defect reflected
      hM hs hsM hell hz hze hk he hbudget hxi hd
      (robust_defect_le_width M xi defect hM hxi hreserve) (lt_of_not_ge hlo) href
    exact Or.inr ⟨hapos, robust_reflected_low_admissible M xi defect short reflected z kappa hd hreserve ht hc⟩

theorem robust_fixed_slack (M₀ : ℝ) (hM₀ : 0 < M₀) :
    0 < M₀/56 ∧ ∀M : ℝ, M₀ ≤ M →
      M₀/56+11*(M₀/56)/7 ≤ M/14 := by
  constructor
  · positivity
  · intro M hM
    linarith

open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDeletionBudget
open CenteredMomentEnergyReferenceDeletionCapacity

theorem robust_deleted_reference_cases (Z M X₁ X₂ ell z κ ξ e reflected : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hκ : 3/4 ≤ κ)
    (hξ : 0 ≤ ξ) (he : 0 ≤ e) (hreserve : ξ+11*e/7 ≤ M/14)
    (hlarge : 5*M/6-e ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell ≤ M)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : ∀ I ∈ D₁, Prime I) (hD₂ : ∀ I ∈ D₂, Prime I)
    (href : reflected ≤ max 0 (M-Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+ξ)) :
    let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
    let long := length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
    (short+long+z ≤ 5*M/6 ∧ short+long+6*κ*z ≤ M) ∨
    (0 < Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ)) ∧
      reflected+short+z ≤ 16*M/21+ξ+4*e/7 ∧
      reflected+short+6*κ*z ≤ 13*M/14+ξ+11*e/7) := by
  dsimp only
  have hb := robust_balanced_long_nonneg M (Real.logb Z (X₁*X₂)) ell κ ξ e
    hM hell hκ hξ hlarge hcap hreserve
  have hpos := comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂
  have hlog : Real.logb Z (comparisonSecond Z M X₁ X₂) = Real.logb Z (X₁*X₂)-M/4 := by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂,
      Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  have hY : 1 ≤ comparisonSecond Z M X₁ X₂ := by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂]
    exact Real.one_le_rpow hZ.le hb.2
  have hn₂ := product_norm_ge_one D₂ hD₂
  have hlongpos := div_pos hpos.2 (zero_lt_one.trans_le hn₂)
  have hshort := deleted_short_length Z M hZ hM D₁ hD₁
  have hshort0 := length_nonneg Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ)) hZ
  have hlong : length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ)) ≤
      Real.logb Z (X₁*X₂)-M/4 := by
    rw [← hlog]
    exact Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (le_max_left 1 _)) (max_le hY (div_le_self hpos.2.le hn₂))
  by_cases hlo : length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ))+
      length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6
  · refine Or.inl ⟨hlo, ?_⟩
    have hkc := mul_le_mul_of_nonneg_left hze (by linarith : 0 ≤ 6*κ)
    nlinarith
  · apply Or.inr
    obtain ⟨hellbound, hslot⟩ := robust_slot_budgets M (Real.logb Z (X₁*X₂)) ell κ e
      hell hκ hlarge hcap
    apply robust_reflected_low M _ _ ell z κ ξ e reflected hM hshort0 hshort hell hz hze hκ
      hellbound hslot hξ he (robust_defect_le_width M ξ e hM hξ hreserve) _ href
    rw [← CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z _ hZ hlongpos]
    exact lt_of_not_ge hlo

theorem robust_deleted_reference_window (Z M X₁ X₂ ell z κ ξ e : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hκ : 3/4 ≤ κ)
    (hξ : 0 ≤ ξ) (he : 0 ≤ e) (hreserve : ξ+11*e/7 ≤ M/14)
    (hlarge : 5*M/6-e ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell ≤ M)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : ∀ I ∈ D₁, Prime I) (hD₂ : ∀ I ∈ D₂, Prime I) :
    let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
    let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
    (short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6 ∧
      short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+6*κ*z ≤ M) ∨
    (0 < along ∧ ∀ x ∈ Set.Icc 0 (max 0 (M-along+ξ)*Real.log Z),
      length Z (Real.exp x)+short+z ≤ 5*M/6 ∧
      length Z (Real.exp x)+short+6*κ*z ≤ M) := by
  dsimp only
  let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))
  rcases robust_deleted_reference_cases Z M X₁ X₂ ell z κ ξ e (max 0 (M-along+ξ))
    hZ hM hX₁ hX₂ hell hz hze hκ hξ he hreserve hlarge hcap D₁ D₂ hD₁ hD₂ le_rfl with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h.1, ?_⟩
    intro x hx
    have hh := CenteredMomentEnergyReferenceLowWindow.reflection_window_length Z
      (max 0 (M-along+ξ)) x hZ (le_max_left _ _) hx
    have hb := robust_reflected_low_admissible M ξ e _ (max 0 (M-along+ξ)) z κ
      he hreserve h.2.1 h.2.2
    constructor <;> linarith [hh.1]

theorem live_profiles_reference_window (a b M₀ : ℝ) (hM₀ : 0 < M₀) :
    ∃ e ξ Z₀ : ℝ, 0 < e ∧ 0 < ξ ∧ 1 < Z₀ ∧
      ∀ (Z M : ℝ), Z₀ ≤ Z → M₀ ≤ M →
      ∀ (η : Character) (m A u : O) (p : Profiles a b)
        (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
        (t X₁ X₂ ell z κ : ℝ), 0 < X₁ → 0 < X₂ → 0 ≤ ell →
        0 ≤ z → z ≤ ell → 3/4 ≤ κ →
        5*M/6 ≤ length Z X₁+length Z X₂+ell →
        length Z X₁+length Z X₂+6*κ*ell ≤ M →
      ∀ (D₁ D₂ : Finset (Ideal O)), (∀ I ∈ D₁, Prime I) → (∀ I ∈ D₂, Prime I) →
      positiveSlotRow η m A u (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0 ∨
      (let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
       let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
       (short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6 ∧
        short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+6*κ*z ≤ M) ∨
       (0 < along ∧ ∀ x ∈ Set.Icc 0 (max 0 (M-along+ξ)*Real.log Z),
         length Z (Real.exp x)+short+z ≤ 5*M/6 ∧
         length Z (Real.exp x)+short+6*κ*z ≤ M)) := by
  have he : 0 < M₀/56 := by positivity
  obtain ⟨Z₀, hZ₀, hdefect⟩ := profiles_uniform_defect (ι := ι) a b (M₀/56) he
  refine ⟨M₀/56, M₀/56, Z₀, he, he, hZ₀, ?_⟩
  intro Z M hZZ hMM η m A u p S β P t X₁ X₂ ell z κ hX₁ hX₂ hell hz hze hκ hlarge hcap D₁ D₂ hD₁ hD₂
  by_cases hrow : positiveSlotRow η m A u (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0
  · exact Or.inl hrow
  · apply Or.inr
    have hZ := hZ₀.trans_le hZZ
    obtain ⟨hl, hc⟩ := raw_gates_of_defect Z M X₁ X₂ ell κ (M₀/56) hZ hX₁ hX₂
      (hdefect Z hZZ η m A u p S β P t X₁ X₂ hX₁ hX₂ hrow) hlarge hcap
    exact robust_deleted_reference_window Z M X₁ X₂ ell z κ (M₀/56) (M₀/56)
      hZ (hM₀.le.trans hMM) hX₁ hX₂ hell hz hze hκ he.le he.le
      ((robust_fixed_slack M₀ hM₀).2 M hMM) hl hc D₁ D₂ hD₁ hD₂

end SevenEighths.CenteredMomentEnergyLiveClippingDefect

end

end OAI

end Source2127

/- Original source: OAI/NumberTheory/DirichletL/Energy/DeletedRobustGeometry.lean; sha256: 2037b3c8eb49c9fdc5c8a4d805efd7ce64237ae6ca70ac4d50e1ef9dd265636d -/
section Source2128
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyDeletedRobustGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyLiveClippingDefect
local notation "O" => HeckeFamily.O

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(hB:0≤Bmask)(Mcap L X₁ X₂ ell z κ xi e:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hκ:3/4≤κ)(hxi:0≤xi)(he:0≤e)(hreserve:xi+11*e/7≤s.width/14)
    (hlarge:5*s.width/6-e≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ);
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤s.width/4 ∧ short≤L ∧ along≤L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤s.width)):= by
  have hbase : 0 < Z := zero_lt_one.trans hZ
  have hb := robust_balanced_long_nonneg s.width (Real.logb Z (X₁*X₂)) ell κ xi e
    s.width_nonneg hell hκ hxi hlarge hcap hreserve
  have hy₁ : 1 ≤ comparisonFirst Z s.width :=
    Real.one_le_rpow hZ.le (by linarith [s.width_nonneg])
  have hy₂ : 1 ≤ comparisonSecond Z s.width X₁ X₂ := by
    rw [comparison_second_power Z s.width X₁ X₂ hZ hX₁ hX₂]
    exact Real.one_le_rpow hZ.le hb.2
  have hf : Real.logb Z (comparisonFirst Z s.width) = s.width/4 :=
    Real.logb_rpow hbase hZ.ne'
  have hl : Real.logb Z (comparisonSecond Z s.width X₁ X₂) = Real.logb Z (X₁*X₂)-s.width/4 := by
    rw [comparison_second_power Z s.width X₁ X₂ hZ hX₁ hX₂, Real.logb_rpow hbase hZ.ne']
  have hd₁ := divisor_reflection_range s hZ Mcap _ hwidth hy₁ D₁ hD₁
  have hd₂ := divisor_reflection_range s hZ Mcap _ hwidth hy₂ D₂ hD₂
  dsimp only at hd₁ hd₂
  rw [hf] at hd₁
  rw [hl] at hd₂
  have hn₁ := (divisor_norm s D₁ hD₁).1
  have hn₂ := (divisor_norm s D₂ hD₂).1
  have hlog₁ := Real.logb_nonneg hZ hn₁
  have hlog₂ := Real.logb_nonneg hZ hn₂
  have hMcap : 0 ≤ Mcap := s.width_nonneg.trans hwidth
  have hLc : 0 ≤ L := by linarith
  have hslot : 0 ≤ (6*κ-1)*ell := mul_nonneg (by linarith) hell
  dsimp only
  refine ⟨hd₁.2.2, hd₂.2.2, by linarith, by linarith [s.width_nonneg],
    by linarith, hd₂.2.1, max_le hLc (by linarith [hd₂.1]), ?_⟩
  have hp₁ : ∀ I ∈ D₁, Prime I := fun I hi =>
    CenteredMomentNaturalRowSource.support_prime s.puncture I (Finset.mem_powerset.mp hD₁ hi)
  have hp₂ : ∀ I ∈ D₂, Prime I := fun I hi =>
    CenteredMomentNaturalRowSource.support_prime s.puncture I (Finset.mem_powerset.mp hD₂ hi)
  let along := Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ)
  have halong : Real.logb Z (comparisonSecond Z s.width X₁ X₂/((∏ P ∈ D₂, P).absNorm : ℝ)) = along := by
    rw [← hd₂.2.2]
    exact Real.logb_rpow hbase hZ.ne'
  rcases robust_deleted_reference_cases Z s.width X₁ X₂ ell z κ xi e (max 0 (s.width-along+xi))
    hZ s.width_nonneg hX₁ hX₂ hell hz hze hκ hxi he hreserve hlarge hcap D₁ D₂ hp₁ hp₂
    (by rw [halong]) with hc | hc
  · exact Or.inl (by simpa only [hd₁.2.2, hd₂.2.2] using hc)
  · apply Or.inr
    have hh := robust_reflected_low_admissible s.width xi e _ (max 0 (s.width-along+xi)) z κ
      he hreserve hc.2.1 hc.2.2
    simpa only [hd₁.2.2] using hh

end SevenEighths.CenteredMomentEnergyDeletedRobustGeometry

end

end OAI

end Source2128

/- Original source: OAI/NumberTheory/DirichletL/Energy/ReferenceRobustDeletedEnergy.lean; sha256: b5e385d3e4e294539bf46139cbc8d4e94ffe9711d0e2517ff1d0c1111d449aa4 -/
section Source2129
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustDeletedEnergy
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyDeletedRobustGeometry CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem deleted_energy_from_low_robust
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi defect saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hdefect:0≤defect)(hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap → xi+11*defect/7≤s.width/14 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      5*s.width/6-defect≤Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤s.width →
      ∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀F:Finset α,
      let β:=fun i I=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (comparisonFirst Z s.width/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
        polynomial (naturalCharacter s.character z) false W₂
          (comparisonSecond Z s.width X₁ X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i)):=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low_with_error (α:=α) M H hH
    Finset.univ Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap D₁ hD₁ D₂ hD₂ F
  dsimp only
  let short:=s.width/4-Real.logb Z ((∏I∈D₁,I).absNorm:ℝ)
  let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)
  have hsum:0≤∑i∈F,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hsumle:(∑i∈F,w i)≤∑i,w i:=Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ F) (fun i _ _=>hw i)
  have hg:=actual_deleted_gates s hZ.1 hBmask Mcap L X₁ X₂ (∑i,w i) (∑i∈F,w i) κ xi defect hs hL
    hX₁ hX₂ (Finset.sum_nonneg (fun i _=>hw i)) hsum hsumle hκ hxi.le hdefect hxiM hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hg
  rw [←hg.1,←hg.2.1]
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hLpos:0≤L:=by linarith [s.width_nonneg]
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hprod: (∏i∈F,Z^(w i))≤∏i,Z^(w i):=Finset.prod_le_prod_of_subset_of_one_le₀
    (Finset.subset_univ F) (fun i _=> (Real.rpow_pos_of_pos hZpos _).le)
    (fun i _ _=>Real.one_le_rpow hZ.1.le (hw i))
  rcases hg.2.2.2.2.2.2.2 with hd|hr
  · have hdirect:=direct_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S K hlow hBmask ha F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      s hQ hs W₁ W₂ hs₁ hs₂ (Z^short) (Z^along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.2.1) hd.2 hd.1
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=hZ.2 Bmask L Lslot Mcap ε κ η₀ Q K hK hlow hBmask F (Finset.subset_univ F)
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs W₂ W₁ hs₂ hs₁ along short
      hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2 hr.1
    dsimp only at hh
    have hswap: (fun z=>polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))) =
      (fun z=>polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))):=by funext z;ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    · gcongr
      exact hg.2.2.2.2.2.2.1
    · gcongr
      · exact hZ.1.le
      · exact hg.2.2.1

end SevenEighths.CenteredMomentEnergyReferenceRobustDeletedEnergy

end

end OAI

end Source2129

/- Original source: OAI/NumberTheory/DirichletL/Energy/ReferenceRobustOriginal.lean; sha256: 88a8fce7fa21f4516b649cd44b075a37ce12d8d8eb2e221296147d742b9345f5 -/
section Source2130
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyDeletedRobustGeometry CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyReferenceRobustDeletedEnergy CenteredMomentEnergyReferenceDeletionEnergy
open CenteredMomentInductionEnergy
theorem original_reference_from_low_robust
    (epsilonDelete:ℝ)(hepsilonDelete:0<epsilonDelete)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi defect saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hdefect:0≤defect)(hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0<C ∧ 0<D ∧ 0<Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap → xi+11*defect/7≤s.width/14 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      5*s.width/6-defect≤Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i))) :=by
  obtain ⟨Bslot,hBslot,hslot⟩:=CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=α)
    (fun _=>bslot) (fun _=>Bslot) (fun _=>hBslot.le) epsilonDelete hepsilonDelete
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=deleted_energy_from_low_robust (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi defect saving Mcap Bmask L ha hlo hhi hbΦ hepsilon hxi hdefect hBmask hL B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,Cweight,hC,hD,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hp:=comparison_positive Z s.width X₁ X₂ hZpos hX₁ hX₂
  apply hweight Z Bmask bΦ a b s W₁ W₂ ha (by linarith) hs₁ hs₂
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) _ 0
  · intro i I hI
    exact (Finset.mem_filter.mp hI).2.1
  · intro i
    exact Real.rpow_pos_of_pos hZpos _
  · intro i I hI
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh
  · intro i I hI hn
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).2
    apply hh
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hp.1
  · exact hp.2
  · have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤L:=by linarith [s.width_nonneg]
    have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simpa only [Real.rpow_zero,mul_one] using hZ.2 Lslot ε κ η₀ Q K hK hlow
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hs hxiM
      W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap D₁ hD₁ D₂ hD₂ (Finset.univ\J)

end SevenEighths.CenteredMomentEnergyReferenceRobustOriginal

end

end OAI

end Source2130

/- Original source: OAI/NumberTheory/DirichletL/Energy/ReferenceRobustPower.lean; sha256: dfab782560e99e50261982732ef0bfa91a66da08fbd50536192b20a89ea9088c -/
section Source2131
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustPower
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceRobustOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_reference_power_robust
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      5*s.width/6-rho/100≤Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hscalar⟩:=
    exists_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_reference_from_low_robust (α:=α) M H hH d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ d xi (rho/100) saving Mcap Bmask L ha hlo hhi hbΦ hd hxi (by positivity) hBmask hL 2 (by norm_num) degree S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong degree n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hxiM:xi+11*(rho/100)/7≤s.width/14:=by linarith
  have hh:=hZ.2 Lslot d κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hg:=CenteredMomentEnergyLiveClippingDefect.robust_slot_budgets s.width
    (Real.logb Z (X₁*X₂)) (∑i,w i) κ (rho/100) hsum hκ hlarge hcap
  have hsumcap:(∑i,w i)≤Mcap:=by linarith [s.width_nonneg]
  have hledger:=hscalar Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤A:=by dsimp only [A];positivity
  have hE:0≤E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤E:=by
      calc
        _ = (1:ℝ)*diagonalControl s.radial.profile*A := by ring
        _ ≤ (K+1)*diagonalControl s.radial.profile*A :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤L:=by linarith
  let P:=Z^(s.width+d)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+d)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
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

end SevenEighths.CenteredMomentEnergyReferenceRobustPower

end

end OAI

end Source2131

/- Original source: OAI/NumberTheory/DirichletL/Energy/ReferenceLivePower.lean; sha256: 22bc9abd7a8eb9e14a61c98b9f39961d3e18d797d2b0fa6e35cd53a9859e8741 -/
section Source2132
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLivePower
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceRobustOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_reference_power_live
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀p:Profiles a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale = 0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=
    CenteredMomentEnergyReferenceRobustPower.original_reference_power_robust
      (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=CenteredMomentEnergyLiveClippingDefect.endpoint_threshold b (rho/100)
    (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  rcases CenteredMomentEnergyLiveClippingDefect.energy_zero_or_defect s.character s.mask 1 t p
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) X₁ X₂ Z s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · apply Or.inr
    have hg:=CenteredMomentEnergyLiveClippingDefect.raw_gates_of_defect
      Z s.width X₁ X₂ (∑i,w i) κ (rho/100) hZ.1 hX₁ hX₂
      (hdft.2.trans (hendpoint Z hZZ)) hlarge hcap
    exact hZ.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hg.1 hg.2

end SevenEighths.CenteredMomentEnergyReferenceLivePower

end

end OAI

end Source2132

/- Original source: OAI/NumberTheory/DirichletL/Energy/FixedRadialSource.lean; sha256: cdee7d41ffb34fa441de7f6eb1e8eb655b9073f1b9c43da283c3a66a540a29be -/
section Source2133
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyFixedRadialSource
open HeckeFamily CenteredMomentSourceRow CenteredMomentAbsoluteEnergy CenteredMomentHeckeExpansion
open QuadraticInitialBound ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

lemma norm_le_diagonalControl (Φ:𝓢(ℝ,ℂ))(x:ℝ):‖Φ x‖≤diagonalControl Φ:=by
  have hs:SchwartzMap.seminorm ℝ 0 0 Φ≤
      (Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ:=by
    exact Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ)
      (by simp : (0,0)∈Finset.Iic (2,0))) Φ
  apply (SchwartzMap.norm_le_seminorm ℝ Φ x).trans
  apply hs.trans
  unfold diagonalControl
  exact le_mul_of_one_le_left (by positivity) (by nlinarith [Real.pi_nonneg])

theorem exists_fixed_bump (b:ℝ)(_hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ (∀x,(Ψ x).im=0) ∧
      (∀x∈Set.Icc (0:ℝ) b,Ψ x=1):=by
  have hsub:Set.Icc (0:ℝ) b⊆Set.Ioo (-1) (b+1):=by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v:ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv:ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf:ContDiff ℝ ∞ f).pow 2)
  have hsupp:Function.support v⊆Set.Icc (-1) (b+1):=by
    intro x hx
    have hn:x∈Function.support f:=by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  let Ψ:𝓢(ℝ,ℂ):=(HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp).toSchwartzMap hv
  refine ⟨Ψ,hsupp,?_,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x
    exact Complex.ofReal_im _
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

theorem finite_energy_domination (b:ℝ)(Ψ:𝓢(ℝ,ℂ))
    (hΨ:∀x,0≤(Ψ x).re)(hone:∀x∈Set.Icc (0:ℝ) b,Ψ x=1)
    (Φ:𝓢(ℝ,ℂ))(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic b)
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (K:ℝ)(hK:0<K):
    ‖finiteHeckeEnergy η m A t S c Φ K‖≤
      diagonalControl Φ*‖finiteHeckeEnergy η m A t S c Ψ K‖:=by
  have hΦ:∀x:ℝ,0≤x→‖Φ x‖≤diagonalControl Φ*(Ψ x).re:=by
    intro x hx
    by_cases h:Φ x=0
    · rw [h,norm_zero]
      exact mul_nonneg (diagonalControl_nonneg Φ) (hΨ x)
    · rw [hone x ⟨hx,hs h⟩,Complex.one_re,mul_one]
      exact norm_le_diagonalControl Φ x
  have hsumΦ:=finite_hecke_energy_summable η m A t S c Φ K hK
  have hsumΨ:=finite_hecke_energy_summable η m A t S c Ψ K hK
  have hre:HasSum (fun z:O=>‖∑I∈S,c I*rowWeight η m A z t I‖^2*
      (Ψ (‖eisEmbedding z‖^2/K)).re)
      (finiteHeckeEnergy η m A t S c Ψ K).re:=by
    have hh:=Complex.hasSum_re hsumΨ.hasSum
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      finiteHeckeEnergy] using hh
  calc
    _≤∑'z:O,‖((‖∑I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
      Φ (‖eisEmbedding z‖^2/K)‖:=norm_tsum_le_tsum_norm hsumΦ.norm
    _≤∑'z:O,diagonalControl Φ*(‖∑I∈S,c I*rowWeight η m A z t I‖^2*
      (Ψ (‖eisEmbedding z‖^2/K)).re):=by
      apply hsumΦ.norm.tsum_le_tsum _ (hre.summable.mul_left _)
      intro z
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact (mul_le_mul_of_nonneg_left (hΦ _ (by positivity)) (sq_nonneg _)).trans_eq (by ring)
    _=diagonalControl Φ*(finiteHeckeEnergy η m A t S c Ψ K).re:=by
      rw [tsum_mul_left,hre.tsum_eq]
    _≤_:=mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (diagonalControl_nonneg Φ)

theorem fixed_source (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀Φ:𝓢(ℝ,ℂ),Function.support (Φ:ℝ→ℂ)⊆Set.Iic b→
      ∀(η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)(K:ℝ),0<K→
      ‖finiteHeckeEnergy η m A t S c Φ K‖≤
        diagonalControl Φ*‖finiteHeckeEnergy η m A t S c Ψ K‖:=by
  obtain ⟨Ψ,hs,hn,_,hone⟩:=exists_fixed_bump b hb
  exact ⟨Ψ,hs,hn,fun Φ hΦ η m A t S c K hK=>finite_energy_domination b Ψ hn hone Φ hΦ η m A t S c K hK⟩

end SevenEighths.CenteredMomentEnergyFixedRadialSource

end

end OAI

end Source2133

/- Original source: OAI/NumberTheory/DirichletL/Energy/FixedRadialEntry.lean; sha256: 08ddc83b2e4305f83348fcd574baba45ad8b6402a62c2013c070bed981ae73cd -/
section Source2134
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFixedRadialEntry
open ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentSourceMass CenteredMomentSourceRectangleMask
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialSource CenteredMomentSourceRow
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentRadialEligibleEnergy
open CenteredMomentEnergyZeroComparison CanonicalQuadraticSieve
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

theorem original_comparison (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀s:Input ι,∀R:Ideal O,∀r:Radial,
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic b→
      CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
      2*QuadraticInitialBound.diagonalControl r.profile*
        ‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) Ψ r.scale‖/volume s+
      2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale :=by
  obtain ⟨Ψ,hs,hn,hh⟩:=fixed_source b hb
  refine ⟨Ψ,hs,hn,?_⟩
  intro s R r hr
  apply (positive_energy_comparison s R r).trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (volume_pos s).le
  have h:=mul_le_mul_of_nonneg_left
    (hh r.profile hr s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.scale r.scale_pos)
    (by norm_num : (0:ℝ)≤2)
  simpa only [mul_assoc] using h

theorem original_zero_comparison (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      ∀R:Ideal O,∀r:Radial,Function.support (r.profile:ℝ→ℂ)⊆Set.Iic b→
      CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
      2*QuadraticInitialBound.diagonalControl r.profile*
        ‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
          (finiteColumns (Fintype.piFinset (zeroInput s hz₁ hz₂).pools))
          (coefficient (zeroInput s hz₁ hz₂) R 1) Ψ r.scale‖/volume s :=by
  obtain ⟨Ψ,hs,hn,hh⟩:=original_comparison (ι:=ι) b hb
  refine ⟨Ψ,hs,hn,?_⟩
  intro s hz₁ hz₂ R r hr
  have h:=hh (zeroInput s hz₁ hz₂) R r hr
  change _≤_+2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
    s.W₁ s.W₂ s.slots s.toData.coefficient s.P
    (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂ r.keep r.profile r.scale at h
  rw [comparison_energy_zero s hz₁ hz₂ R r,mul_zero,add_zero] at h
  exact h
end SevenEighths.CenteredMomentEnergyFixedRadialEntry

end

end OAI

end Source2134

/- Original source: OAI/NumberTheory/DirichletL/Energy/FixedRadialReduction.lean; sha256: aec168f5276f728078233b396e1a469e9618570ab8514488bea4aacc3e4f6d46 -/
section Source2135
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyFixedRadialReduction
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildInput
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyFixedRadialEntry
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputFirstRemainder
open CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

theorem actual_original_reduction (bΦ:ℝ)(hbΦ:0<bΦ)
    (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,
      0<Cdiag ∧ 0<Ctail ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(R:Ideal O)(r:Radial),Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ→
      volume s≤Z^B→(r.scale)⁻¹≤Z^B→
      CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale≤
      2*diagonalControl r.profile*(
        physicalMass s R 1 fixedBadMask 1 Ψ r.scale Z ξ/volume s+
        Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^ε+
        Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^(-saving))+
      2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale:=by
  obtain ⟨Ψ,hs,hn,hentry⟩:=original_comparison (ι:=ι) bΦ hbΦ
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=
    original_first_physical_reduction hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Ψ,hs,hn,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [hred] with Z hz
  refine ⟨hz.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  have hsource:=hz.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hsi fixedBadMask 1
    (dvd_mul_right _ _) (dvd_mul_left _ _) R 1 Ψ r.scale r.scale_pos hV hK
  have hpos:=hentry s R r hr
  have hdom:=mul_le_mul_of_nonneg_left hsource
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (diagonalControl_nonneg r.profile))
  apply hpos.trans
  apply add_le_add _ le_rfl
  simpa only [mul_div_assoc, CenteredMomentAmplificationChildInput.volume,
    CenteredMomentExceptionalAmplitudePair.volume] using hdom
end SevenEighths.CenteredMomentEnergyFixedRadialReduction

end

end OAI

end Source2135

/- Original source: OAI/NumberTheory/DirichletL/Energy/PositiveHighSource.lean; sha256: 370cd3a1dc2e3c4647c4e9d5c8d7df570f19e2e7b30e416296fecf64cc67bb36 -/
section Source2136
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSource
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

def balancedInput:Input α:=
  CenteredMomentEnergyNaturalInputMatches.input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
    hX₁ hX₂
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

local notation "balancedSource"=>balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

omit [DecidableEq α] in
lemma balanced_matches:
    CenteredMomentAllocatedRayDictionary.Matches M H hH balancedSource η₀ θ w σ freq W bslot Z:=by
  constructor <;> intros <;> rfl

omit [DecidableEq α] in
lemma balanced_volume:
    CenteredMomentAmplificationChildInput.volume balancedSource=X₁*X₂*∏i,Z^(w i):=rfl

omit [DecidableEq α] in
lemma balanced_volume_bound (κ Mcap:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width)(hs:s.width≤Mcap):
    CenteredMomentAmplificationChildInput.volume balancedSource≤Z^Mcap:=by
  rw [balanced_volume]
  have hz:=zero_lt_one.trans hZ
  have hw0:0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hx (X:ℝ):X≤Z^(length Z X):=by
    rw [length,Real.rpow_logb hz hZ.ne' (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
    exact le_max_right _ _
  calc
    _≤(Z^(length Z X₁)*Z^(length Z X₂))*(∏i,Z^(w i)):=by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun _ _=>Real.rpow_nonneg hz.le _))
      exact mul_le_mul (hx X₁) (hx X₂) hX₂.le (Real.rpow_nonneg hz.le _)
    _=Z^(length Z X₁+length Z X₂+∑i,w i):=by
      rw [←Real.rpow_add hz,←Real.rpow_sum_of_pos hz,←Real.rpow_add hz]
    _≤Z^Mcap:=Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith)

theorem actual_positive_source_entry
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hbslot:0≤bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤w i)→ (∀i,w i≤Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤hi),
      0≤height→ (∀i,|freq i|≤height)→ 3/4≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤s.width→ s.width≤Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=original_reference_power_live (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=α) bΦ hbΦ (fun _=>bslot) a b Mcap εdiag ξ saving (fun _=>hbslot) ha (by linarith) hM hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  rcases hz.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hreference
  · exact Or.inl hzero
  · right
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (fun _=>le_rfl) s.puncture s.radial s.radial_support
      (balanced_volume_bound M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂ κ Mcap hz.1 hw hκ hcap hs)
      (natural_inverse_scale s Mcap hM)
    have href':energy inp.η (fixedBadMask*idealGenerator s.puncture) 1 inp.t
        inp.W₁ inp.W₂ inp.slots inp.toData.coefficient inp.P inp.Y₁ inp.Y₂
        s.radial.keep s.radial.profile s.radial.scale≤
        C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|+height)^J*Z^(s.width+ε):=hreference
    apply hphysical.trans
    have hh:=add_le_add_left (mul_le_mul_of_nonneg_left href' (by norm_num : (0:ℝ)≤2))
      (2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving)))
    convert hh using 1 <;> ring
end SevenEighths.CenteredMomentEnergyPositiveHighSource

end

end OAI

end Source2136

/- Original source: OAI/NumberTheory/DirichletL/Energy/PositiveHighParameters.lean; sha256: e3e0f7f1e4f0d3bd963d6962f70f9026ba26d274767896c711ce4574b483ad62 -/
section Source2137
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveHighParameters
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

lemma actual_width_le (hZ:1<Z):
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤s.width:=by
  have hn:0<(s.character.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.character.modulus_ne_bot)
  have hc:Real.logb Z (s.character.modulus.absNorm:ℝ)≤s.characterWidth:=
    (Real.logb_le_iff_le_rpow hZ hn).mpr s.modulus_bound
  rw [s.scale_eq,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  exact add_le_add_right hc _

lemma actual_conductor_scale (hZ:1<Z):
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width:=by
  rw [s.scale_eq,NaturalState.width,Real.rpow_add (zero_lt_one.trans hZ)]
  exact mul_le_mul_of_nonneg_left s.modulus_bound (Real.rpow_nonneg (by linarith) _)

omit [DecidableEq α] in
lemma balanced_log_volume (κ:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width):
    Real.logb Z (CenteredMomentAmplificationChildInput.volume balancedSource)≤s.width:=by
  have hv:0<CenteredMomentAmplificationChildInput.volume balancedSource:=by
    rw [balanced_volume]
    exact mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos (by linarith) _))
  exact (Real.logb_le_iff_le_rpow hZ hv).mpr
    (balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl)

omit [DecidableEq α] in
lemma balanced_actual_four_scales (hZ:1<Z)(hwidth:0<s.width)
    (hshort:s.width/4≤min (length Z X₁) (length Z X₂)):
    let M0:=Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ);
    Z^(M0/4)≤(balancedSource).X₁ ∧ Z^(M0/4)≤(balancedSource).X₂ ∧
    Z^(M0/4)≤(balancedSource).Y₁ ∧ Z^(M0/4)≤(balancedSource).Y₂:=by
  have hf:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  have hm:=actual_width_le s hZ
  have hp:Z^((Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ))/4)≤
      Z^(s.width/4):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  exact ⟨hp.trans hf.1,hp.trans hf.2.1,hp.trans hf.2.2.1,hp.trans hf.2.2.2.1⟩

omit [DecidableEq α] in
lemma balanced_control (N:ℕ)(hN:Fintype.card α≤N)(S:Finset (ℕ×ℕ)):
    (plainControl balancedSource (p.profile 0) (p.profile 1))^2≤
      (CenteredMomentEnergyNaturalInputMatches.profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2:=by
  apply plain_control_sq_le balancedSource p S N _
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
    hN (fun _=>le_rfl)

omit [DecidableEq α] in
lemma balanced_source_cost (N:ℕ)(hN:Fintype.card α≤N)(hZ:1<Z):
    CenteredMomentFirstReferenceEnergy.sourceFactor balancedSource a a s.radial.scale≤
      (Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a))*Z^s.width:=by
  have hK:0<s.radial.scale:=by rw [s.scale_eq]; positivity
  have hc:=source_factor_le balancedSource N aslot a s.radial.scale haslot ha hK hN (fun _=>le_rfl)
  have hconst:0≤Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a):=by
    have hp:=CenteredMomentFirstPhysicalSource.fixedPresentationCost_pos
    positivity
  have he:(balancedSource).η=s.character:=rfl
  rw [he] at hc
  apply hc.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (actual_conductor_scale s hZ) hconst

end SevenEighths.CenteredMomentEnergyPositiveHighParameters

end

end OAI

end Source2137

/- Original source: OAI/NumberTheory/DirichletL/Energy/LowFixedRadialEntry.lean; sha256: 15fb5c8e9cd03a9a652c86ccfde99c1a39b5b1bbcba3445f49cacae56bafff1d -/
section Source2138
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyLowFixedRadialEntry
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentEnergyZeroComparison
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyOriginalSource
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentEnergyState CenteredMomentEnergyPhysicalEntry
open CenteredMomentRadialEligibleEnergy CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

omit [DecidableEq ι] in
lemma zero_control (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(W₁ W₂:𝓢(ℝ,ℂ)):
    plainControl (zeroInput s hz₁ hz₂) W₁ W₂=plainControl s W₁ W₂:=rfl

theorem original_low_reduction (bΦ:ℝ)(hbΦ:0<bΦ)
    (hi:ι→ℝ)(a b B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(ha:0<a)(hb:0≤b)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,
      0<Cdiag ∧0<Ctail ∧∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),∀he₁:s.W₁=W₁,∀he₂:s.W₂=W₂,
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      (∀i,s.hi i≤hi i) →∀(R:Ideal O)(r:Radial),
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
      CenteredMomentAmplificationChildInput.volume s≤Z^B → r.scale⁻¹≤Z^B →
      let hz₁:s.W₁ 0=0:=by rw [he₁];exact CenteredMomentDetectorPlainSource.support_zero W₁ a b ha hs₁;
      let hz₂:s.W₂ 0=0:=by rw [he₂];exact CenteredMomentDetectorPlainSource.support_zero W₂ a b ha hs₂;
      energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots s.toData.coefficient
        s.P s.X₁ s.X₂ r.keep r.profile r.scale≤
      2*diagonalControl r.profile*(
        physicalMass (zeroInput s hz₁ hz₂) R 1 fixedBadMask 1 Ψ r.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume s+
        Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^ε+
        Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^(-saving)):=by
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    bΦ hbΦ hi a b B ε ξ saving hhi ha hb hB hε hξ
  refine ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [hred] with Z hz
  refine ⟨hz.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  dsimp only
  let hz₁:s.W₁ 0=0:=by rw [he₁];exact CenteredMomentDetectorPlainSource.support_zero W₁ a b ha hs₁
  let hz₂:s.W₂ 0=0:=by rw [he₂];exact CenteredMomentDetectorPlainSource.support_zero W₂ a b ha hs₂
  have hh:=hz.2 (zeroInput s hz₁ hz₂) W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  change energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots s.toData.coefficient
    s.P s.X₁ s.X₂ r.keep r.profile r.scale≤_+2*energy s.η (fixedBadMask*idealGenerator R) 1 s.t
    s.W₁ s.W₂ s.slots s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
    r.keep r.profile r.scale at hh
  rw [comparison_energy_zero s hz₁ hz₂ R r,mul_zero,add_zero,zeroInput_volume,zero_control] at hh
  exact hh

omit [DecidableEq ι] in
theorem zero_comparison_product_cap (b B ε:ℝ)(_hB:0≤B)(hε:0<ε):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      s.b₁≤b →s.X₁*s.X₂≤Z^B →
      (zeroInput s hz₁ hz₂).Y₁≤1 ∧
      (zeroInput s hz₁ hz₂).Y₂≤Z^(B+ε):=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro s hz₁ hz₂ hb hprod
  refine ⟨smallScale_le_one _,?_⟩
  change s.X₁*s.X₂/smallScale s.b₁≤_
  have hconst:2*max 1 s.b₁≤Z^ε:=
    (mul_le_mul_of_nonneg_left (max_le_max_left 1 hb) (by norm_num)).trans hc
  unfold smallScale
  rw [div_div_eq_mul_div,div_one]
  calc
    _≤Z^B*Z^ε:=mul_le_mul hprod hconst (by positivity)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le
    _=Z^(B+ε):=(Real.rpow_add (zero_lt_one.trans hZ) _ _).symm

omit [DecidableEq ι] in
theorem zero_comparison_first_log (b ε:ℝ)(hε:0<ε):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      s.b₁≤b → -ε≤Real.logb Z (zeroInput s hz₁ hz₂).Y₁ ∧
        Real.logb Z (zeroInput s hz₁ hz₂).Y₁≤0:=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro s hz₁ hz₂ hb
  change -ε≤Real.logb Z (smallScale s.b₁) ∧ Real.logb Z (smallScale s.b₁)≤0
  have hconst:2*max 1 s.b₁≤Z^ε:=
    (mul_le_mul_of_nonneg_left (max_le_max_left 1 hb) (by norm_num)).trans hc
  have hlower:Z^(-ε)≤smallScale s.b₁:=by
    rw [Real.rpow_neg (zero_lt_one.trans hZ).le]
    simpa only [smallScale,one_div] using one_div_le_one_div_of_le (by positivity) hconst
  refine ⟨?_,?_⟩
  · have hh:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hlower
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  · have hh:=Real.logb_le_logb_of_le hZ (smallScale_pos s.b₁) (smallScale_le_one s.b₁)
    simpa only [Real.logb_one] using hh

end SevenEighths.CenteredMomentEnergyLowFixedRadialEntry

end

end OAI

end Source2138

/- Original source: OAI/NumberTheory/DirichletL/Energy/NaturalLowSourceBound.lean; sha256: 38c22046b05e8f8d25d8169ba8afd2f5dcc784ebee61945f25d317cbc112c263 -/
section Source2139
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalLowSourceBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyZeroComparison CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyLowFixedRadialEntry CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentAmplificationChildInput CenteredMomentInductionEnergy
open CenteredMomentEnergyBands CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource HeckeDyadic HeckePrimeAnnular
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=
  CenteredMomentEnergyOriginalSource.energyOriginalSourceDecidableSum

section Source
variable (Q:Ideal O)[NeZero Q]
variable (H:Subgroup (O⧸Q)ˣ)(hH:RayOrthogonality.globalUnits Q≤H)
variable (η₀:Character)(θ:ι→RayQuotient.Characters Q H)
variable (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:ι→ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(state:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

def sourceInput : Input ι :=
  input Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
    state p ha t X₁ X₂ X₁ X₂ hX₁ hX₂ hX₁ hX₂ rfl

def zeroSourceInput : Input ι :=
  zeroInput (sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂)
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 1))
end Source

private lemma control_mono {a b:ℝ}(p:Profiles a b)(S:Finset (ℕ×ℕ)):
    p.control S≤p.control (insert (0,0) S):=by
  unfold Profiles.control
  exact mul_le_mul
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem natural_low_source_bound
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hMcap:0≤Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∃Cfixed:ℝ,0<Cfixed ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Q:Ideal O)[NeZero Q](H:Subgroup (O⧸Q)ˣ)(hH:RayOrthogonality.globalUnits Q≤H),
    ∀(η₀:Character)(θ:ι→RayQuotient.Characters Q H),
    ∀(w σ freq:ι→ℝ), (∀i,0≤w i) → ∀hσ:∀i,σ i∈Set.Icc lo hi,
    ∀(Bmask:ℝ)(state:NaturalState Z Bmask bΦ)(p:Profiles a b)(t X₁ X₂:ℝ),
    ∀hX₁:0<X₁,∀hX₂:0<X₂,∀κ:ℝ,1/6≤κ →
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤Mcap →
    ∀(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical height e:ℝ),0≤Cphysical →0≤height →
    εdiag≤e → -saving≤e →
    physicalMass (zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂) state.puncture 1 fixedBadMask 1
      Ψ state.radial.scale Z ξ /
      volume (sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
        w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂) ≤
      Cphysical*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e) →
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool Q H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I*
        annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i=>Z^(w i)) X₁ X₂ state.radial.keep state.radial.profile state.radial.scale ≤
      Cfixed*(Cphysical+1)*diagonalControl state.radial.profile*
        (p.control (insert (0,0) S))^2*(1+|t|+height)^J*Z^(state.width+e):=by
  obtain ⟨Ψ,hΨs,hΨn,Sd,St,Cd,Ct,hCd,hCt,hred⟩:=
    original_low_reduction (ι:=ι) bΦ hbΦ (fun _=>bslot) a b Mcap εdiag ξ saving
      (fun _=>hbslot) ha hb hMcap hεdiag hξ
  let P:ℝ:=(profileBound W hW aslot bslot lo hi haslot hWs)^(2*Fintype.card ι)
  let D:ℝ:=Cd*P*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ct*P*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤P:=pow_nonneg (zero_le_one.trans (profileBound_ge_one W hW aslot bslot lo hi haslot hWs)) _
  have hD:0≤D:=by dsimp [D];positivity
  have hT:0≤T:=by dsimp [T];positivity
  refine ⟨Ψ,hΨs,hΨn,2*(1+D+T),by positivity,?_⟩
  filter_upwards [hred] with Z hz
  refine ⟨hz.1,?_⟩
  intro Q _ H hH η₀ θ w σ freq hw hσ Bmask state p t X₁ X₂ hX₁ hX₂ κ hκ hcap
    S J Cphysical height e hCphysical hheight he hsave hphysical
  let s:=sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
  have hZ:0<Z:=zero_lt_one.trans hz.1
  have hPi:∀i,1≤s.P i:=fun i=>Real.one_le_rpow hz.1.le (hw i)
  have hv:volume s≤Z^Mcap:=original_volume_cap s Z κ Mcap hz.1 hκ hPi (by
    change length Z X₁+length Z X₂+6*κ*(∑i,Real.logb Z (Z^(w i)))≤Mcap
    simpa only [Real.logb_rpow hZ hz.1.ne'] using hcap)
  have hscale:1≤state.radial.scale:=by rw [state.scale_eq];exact Real.one_le_rpow hz.1.le state.row_nonneg
  have hKi:state.radial.scale⁻¹≤Z^Mcap:=
    (inv_le_one_of_one_le₀ hscale).trans (Real.one_le_rpow hz.1.le hMcap)
  have hbound:=hz.2 s (p.profile 0) (p.profile 1) rfl rfl (p.support 0) (p.support 1)
    (fun _=>le_rfl) state.puncture state.radial state.radial_support hv hKi
  have hplain:(plainControl s (p.profile 0) (p.profile 1))^2≤P*(p.control (insert (0,0) S))^2:=
    plain_control_sq_le s p S (Fintype.card ι) _
      (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) le_rfl (fun _=>le_rfl)
  have hsquare:(p.control S)^2≤(p.control (insert (0,0) S))^2:=
    pow_le_pow_left₀ (p.control_nonneg S) (control_mono p S) 2
  let F:ℝ:=(p.control (insert (0,0) S))^2*(1+|t|+height)^J*Z^(state.width+e)
  have hF:0≤F:=by dsimp [F];positivity
  have hheight1:1≤(1+|t|+height)^J:=one_le_pow₀ (by linarith [abs_nonneg t])
  have hscalePower (x:ℝ)(hx:x≤e):state.radial.scale*Z^x≤Z^(state.width+e):=by
    rw [state.scale_eq,←Real.rpow_add hZ]
    exact Real.rpow_le_rpow_of_exponent_le hz.1.le (by unfold NaturalState.width;linarith [state.character_nonneg])
  have hphysical':physicalMass (zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂) state.puncture 1 fixedBadMask 1
      Ψ state.radial.scale Z ξ/volume s≤Cphysical*F:=by
    apply hphysical.trans
    calc
      _≤Cphysical*(p.control (insert (0,0) S))^2*(1+|t|+height)^J*Z^(state.width+e):=by gcongr
      _=Cphysical*F:=by dsimp [F];ring
  have hterm (c A x:ℝ)(hc:0≤c)(hA:0≤A)(hx:x≤e):
      c*(plainControl s (p.profile 0) (p.profile 1))^2*A*state.radial.scale*Z^x≤c*P*A*F:=by
    calc
      _≤c*(P*(p.control (insert (0,0) S))^2)*A*(state.radial.scale*Z^x):=by
        rw [←mul_assoc];gcongr
      _≤c*(P*(p.control (insert (0,0) S))^2)*A*Z^(state.width+e):=by
        gcongr;exact hscalePower x hx
      _≤c*P*A*F:=by
        have hh:=le_mul_of_one_le_right
          (show 0≤c*P*A*(p.control (insert (0,0) S))^2*Z^(state.width+e) by positivity) hheight1
        dsimp [F]
        convert hh using 1 <;> ring
  have hd:=hterm Cd (Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) he
  have ht:=hterm Ct (St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) hsave
  change energy state.character state.mask 1 t (p.profile 0) (p.profile 1) _ _ _ _ _ _ _ _≤_ at hbound
  apply hbound.trans
  change 2*diagonalControl state.radial.profile*(_+_+_)≤_
  have hsum:=add_le_add (add_le_add hphysical' hd) ht
  have hmul:=mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (diagonalControl_nonneg state.radial.profile))
  apply hmul.trans
  dsimp only [D,T] at *
  have hcoeff:Cphysical+Cd*P*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ+
      Ct*P*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ≤
      (1+Cd*P*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ+
        Ct*P*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ)*(Cphysical+1):=by
    nlinarith [mul_nonneg hCphysical hD,mul_nonneg hCphysical hT]
  have hh:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoeff hF)
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (diagonalControl_nonneg state.radial.profile))
  dsimp [F] at hh ⊢
  nlinarith only [hh]

end SevenEighths.CenteredMomentEnergyNaturalLowSourceBound

end

end OAI

end Source2139

/- Original source: OAI/NumberTheory/DirichletL/Energy/NaturalSourceAdmission.lean; sha256: b6007a32438984a06477d2716db23d9395778cb75d90caf117b048494e09b7c8 -/
section Source2140
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalSourceAdmission
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyZeroComparison
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyInputParentCapacity CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource HeckeDyadic HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentSourceRow CenteredMomentRetainedEnergy
open CenteredMomentSourceInputTailUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := energyOriginalSourceDecidableSum

def lowerProduct (N : ℕ) (aslot a : ℝ) : ℝ := (min 1 aslot)^N*a*a

lemma lowerProduct_pos (N : ℕ) {aslot a : ℝ} (hs : 0 < aslot) (ha : 0 < a) :
    0 < lowerProduct N aslot a := by unfold lowerProduct; positivity

section Source
variable (Q : Ideal O) [NeZero Q]
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters Q H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z Bmask bΦ a b : ℝ} (state : NaturalState Z Bmask bΦ)
variable (p : Profiles a b) (ha : 0 < a) (t X₁ X₂ : ℝ)
variable (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "s" => sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
local notation "s₀" => zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂

theorem both_matches :
    CenteredMomentAllocatedRayDictionary.Matches Q H hH s η₀ θ w σ freq W bslot Z ∧
    CenteredMomentAllocatedRayDictionary.Matches Q H hH s₀ η₀ θ w σ freq W bslot Z := by
  constructor <;> constructor <;> intros <;> rfl

lemma source_fields :
    (s).η = state.character ∧ (s₀).η = state.character ∧
    (s).m = state.mask ∧ (s₀).m = state.mask ∧ (s).A = 1 ∧ (s₀).A = 1 ∧
    (s).t = t ∧ (s₀).t = t ∧
    (s).W₁ = p.profile 0 ∧ (s₀).W₁ = p.profile 0 ∧
    (s).W₂ = p.profile 1 ∧ (s₀).W₂ = p.profile 1 ∧
    (s).lower = aslot ∧ (s₀).lower = aslot ∧ (s).upper = bslot ∧ (s₀).upper = bslot := by
  repeat' constructor

lemma slot_fields (i : ι) :
    (s).P i = Z^(w i) ∧ (s₀).P i = Z^(w i) ∧
    (s).lo i = aslot ∧ (s₀).lo i = aslot ∧ (s).hi i = bslot ∧ (s₀).hi i = bslot ∧
    (s).M i = profileBound W hW aslot bslot lo hi haslot hWs ∧
    (s₀).M i = profileBound W hW aslot bslot lo hi haslot hWs ∧
    (s).slots i = primePool Q H bslot (Z^(w i)) ∧
    (s₀).slots i = primePool Q H bslot (Z^(w i)) := by repeat' constructor

lemma slot_coefficient (i : ι) (I : Ideal O) :
    (s).toData.coefficient i I = idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
      annularWeight W (Z^(w i)) (σ i) (freq i) I ∧
    (s₀).toData.coefficient i I = (s).toData.coefficient i I := ⟨rfl, rfl⟩

lemma rectangles :
    (s).X₁ = X₁ ∧ (s).X₂ = X₂ ∧ (s).Y₁ = X₁ ∧ (s).Y₂ = X₂ ∧
    (s₀).X₁ = X₁ ∧ (s₀).X₂ = X₂ ∧
    (s₀).Y₁ = smallScale b ∧ (s₀).Y₂ = X₁*X₂/smallScale b ∧
    (s₀).Y₁*(s₀).Y₂ = X₁*X₂ := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  exact (s₀).same_product

lemma raw_volume : volume s = X₁*X₂*∏ i, Z^(w i) ∧ volume s₀ = volume s := ⟨rfl,rfl⟩

lemma volume_log (hZ : 1 < Z) :
    Real.logb Z (volume s) = Real.logb Z X₁ + Real.logb Z X₂ + ∑ i, w i ∧
    Real.logb Z (volume s₀) = Real.logb Z X₁ + Real.logb Z X₂ + ∑ i, w i := by
  have hh := input_volume_log s Z
  change Real.logb Z (volume s) = Real.logb Z X₁ + Real.logb Z X₂ +
    ∑ i, Real.logb Z (Z^(w i)) at hh
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  exact ⟨hh,hh⟩

theorem capacity_admission (hZ : 1 < Z) (hw : ∀ i, 0 ≤ w i) (κ : ℝ)
    (hκ : 1/6 ≤ κ)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ state.width) :
    (∀ i, 1 ≤ (s).P i ∧ 1 ≤ (s₀).P i) ∧
    volume s ≤ Z^state.width ∧ volume s₀ ≤ Z^state.width := by
  have hPi : ∀ i, 1 ≤ (s).P i := fun i => Real.one_le_rpow hZ.le (hw i)
  have hv := original_volume_cap s Z κ state.width hZ hκ hPi (by
    change length Z X₁ + length Z X₂ + 6*κ*(∑ i, Real.logb Z (Z^(w i))) ≤ _
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hcap)
  exact ⟨fun i => ⟨hPi i,hPi i⟩,hv,hv⟩

theorem low_admission (hZ : 1 < Z)
    (hlow : length Z X₁ + length Z X₂ + ∑ i, w i ≤ 5*state.width/6) :
    Real.logb Z (volume s) ≤ 5*state.width/6 ∧
    Real.logb Z (volume s₀) ≤ 5*state.width/6 := by
  have hv := volume_log Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂ hZ
  have h1 := raw_log_le_length Z X₁ hZ hX₁
  have h2 := raw_log_le_length Z X₂ hZ hX₂
  constructor <;> linarith [hv.1,hv.2]

theorem lower_product_admission (N : ℕ) (hN : Fintype.card ι ≤ N) :
    0 < lowerProduct N aslot a ∧
    lowerProduct N aslot a ≤ (∏ i, (s).lo i)*a*a ∧
    lowerProduct N aslot a ≤ (∏ i, (s₀).lo i)*a*a := by
  have hh := lower_product s N aslot haslot hN (fun _ => le_rfl)
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le
  exact ⟨lowerProduct_pos N haslot ha,hb,hb⟩

theorem profile_control_admission (N : ℕ) (hN : Fintype.card ι ≤ N)
    (S : Finset (ℕ×ℕ)) :
    (plainControl s (p.profile 0) (p.profile 1))^2 ≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 ∧
    (plainControl s₀ (p.profile 0) (p.profile 1))^2 ≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 := by
  have hh := plain_control_sq_le s p S N _
    (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) hN (fun _ => le_rfl)
  exact ⟨hh,hh⟩

theorem normalized_zero_source (R : Ideal O) (z : O) :
    positiveSlotRow state.character (fixedBadMask*idealGenerator R) 1 z
      (p.profile 0) (p.profile 1) (s).slots (s).toData.coefficient (s).P t X₁ X₂ =
    (Real.sqrt (volume s) : ℂ)⁻¹ *
      ∑ I ∈ finiteColumns (Fintype.piFinset (s₀).pools),
        CenteredMomentOriginalCommonHarmonic.coefficient s₀ R 1 I * rowWeight state.character fixedBadMask 1 z t I := by
  have hh := normalized_input_difference s₀ R z
  have hz := comparison_row_zero s
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 1)) R z
  change positiveSlotRow state.character (fixedBadMask*idealGenerator R) 1 z
      (p.profile 0) (p.profile 1) (s).slots (s).toData.coefficient (s).P t X₁ X₂ -
    positiveSlotRow (s).η (fixedBadMask*idealGenerator R) 1 z (s).W₁ (s).W₂ (s).slots
      (s).toData.coefficient (s).P (s).t (s₀).Y₁ (s₀).Y₂ = _ at hh
  change positiveSlotRow (s).η (fixedBadMask*idealGenerator R) 1 z (s).W₁ (s).W₂ (s).slots
    (s).toData.coefficient (s).P (s).t (s₀).Y₁ (s₀).Y₂ = 0 at hz
  rw [hz,sub_zero] at hh
  exact hh

end Source

theorem radial_admission {Z Bmask bΦ : ℝ} (state : NaturalState Z Bmask bΦ) :
    1 ≤ state.radial.scale ∧ state.radial.scale⁻¹ ≤ 1 ∧
    state.radial.scale⁻¹ ≤ Z^state.width := by
  have hs : 1 ≤ state.radial.scale := by
    rw [state.scale_eq]
    exact Real.one_le_rpow state.base_ge_one state.row_nonneg
  have hi := inv_le_one_of_one_le₀ hs
  exact ⟨hs,hi,hi.trans (Real.one_le_rpow state.base_ge_one state.width_nonneg)⟩

theorem original_scale_caps {Z X₁ X₂ M L κ : ℝ} (w : ι → ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hw : ∀ i, 0 ≤ w i) (hκ : 1/6 ≤ κ)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ M)
    (hM : M ≤ L) : X₁ ≤ Z^L ∧ X₂ ≤ Z^L := by
  have hn : 0 ≤ 6*κ*(∑ i, w i) :=
    mul_nonneg (by linarith) (Finset.sum_nonneg (fun i _ => hw i))
  have h1 := raw_log_le_length Z X₁ hZ hX₁
  have h2 := raw_log_le_length Z X₂ hZ hX₂
  constructor
  · apply (Real.logb_le_iff_le_rpow hZ hX₁).mp
    linarith [length_nonneg Z X₂ hZ]
  · apply (Real.logb_le_iff_le_rpow hZ hX₂).mp
    linarith [length_nonneg Z X₁ hZ]

theorem eventually_scale_admission (b L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
    ∀ (Q : Ideal O) [NeZero Q] (H : Subgroup (O ⧸ Q)ˣ)
      (hH : RayOrthogonality.globalUnits Q ≤ H) (η₀ : Character)
      (θ : ι → RayQuotient.Characters Q H),
    ∀ (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
      (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot),
    ∀ (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi),
    ∀ (Bmask bΦ a : ℝ) (state : NaturalState Z Bmask bΦ) (p : Profiles a b)
      (ha : 0 < a) (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (κ : ℝ),
    (∀ i, 0 ≤ w i) → 1/6 ≤ κ → state.width ≤ L →
    length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ state.width →
    let s := sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
    let s₀ := zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
    (s).X₁ ≤ Z^L ∧ (s).X₂ ≤ Z^L ∧ (s).Y₁ ≤ Z^L ∧ (s).Y₂ ≤ Z^L ∧
    (s₀).X₁ ≤ Z^L ∧ (s₀).X₂ ≤ Z^L ∧
    (s₀).Y₁ ≤ Z^(2*L+ε) ∧ (s₀).Y₂ ≤ Z^(2*L+ε) := by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1 : ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro ι _ _ Q _ H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ Bmask bΦ a state p ha t X₁ X₂ hX₁ hX₂ κ hw hκ hM hcap
  dsimp only
  have hx := original_scale_caps w hZ hX₁ hX₂ hw hκ hcap hM
  refine ⟨hx.1,hx.2,hx.1,hx.2,hx.1,hx.2,?_,?_⟩
  · exact (smallScale_le_one b).trans (Real.one_le_rpow hZ.le (by positivity))
  · change X₁*X₂/smallScale b ≤ _
    have hp : X₁*X₂ ≤ Z^(2*L) := by
      have hh := mul_le_mul hx.1 hx.2 hX₂.le (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) L).le
      rw [←Real.rpow_add (zero_lt_one.trans hZ)] at hh
      simpa only [two_mul] using hh
    unfold smallScale
    rw [div_div_eq_mul_div,div_one]
    exact (mul_le_mul hp hc (by positivity)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le).trans_eq
        (Real.rpow_add (zero_lt_one.trans hZ) _ _).symm

end SevenEighths.CenteredMomentEnergyNaturalSourceAdmission

end

end OAI

end Source2140

/- Original source: OAI/NumberTheory/DirichletL/Energy/PositiveBalancedAdmission.lean; sha256: b970e995a4a232f42316d372f8f21f00b91d48509c04ee236da8e0d9fb5dd2e4 -/
section Source2141
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

open CenteredMomentEnergyPositiveHighParameters
open CenteredMomentEnergyNaturalInputMatches CenteredMomentAmplificationChildInput

theorem fixed_fields :
    (balancedSource).lower=aslot ∧ (balancedSource).upper=bslot ∧
    (balancedSource).b₁=b ∧ (balancedSource).b₂=b ∧
    (balancedSource).W₁=p.profile 0 ∧ (balancedSource).W₂=p.profile 1 ∧
    (balancedSource).η=s.character ∧ (balancedSource).m=s.mask ∧ (balancedSource).t=t ∧
    (∀i,(balancedSource).lo i=aslot) ∧ (∀i,(balancedSource).hi i=bslot) ∧
    (∀i,(balancedSource).M i=profileBound W hW aslot bslot lo hi haslot hWs) ∧
    (∀i,(balancedSource).P i=Z^(w i)) := by
  repeat' constructor
  all_goals intro i;rfl

theorem fixed_lower_product (N:ℕ)(hN:Fintype.card α≤N) :
    0<(min 1 aslot)^N*a*a ∧
    (min 1 aslot)^N*a*a≤(∏i,(balancedSource).lo i)*a*a := by
  have hh:=CenteredMomentEnergyOriginalProfileControl.lower_product balancedSource N aslot haslot hN
    (fun _=>le_rfl)
  exact ⟨by positivity,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le⟩

lemma exact_log_volume (hZ:1<Z) :
    Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+∑i,w i := by
  have hh:=CenteredMomentEnergyInputParentCapacity.input_volume_log balancedSource Z
  change Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+
    ∑i,Real.logb Z (Z^(w i)) at hh
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

theorem four_upper_scales (κ L:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width)(hs:s.width≤L) :
    (balancedSource).X₁≤Z^L ∧ (balancedSource).X₂≤Z^L ∧
    (balancedSource).Y₁≤Z^L ∧ (balancedSource).Y₂≤Z^L := by
  have hp:0<Z:=zero_lt_one.trans hZ
  have hx:=CenteredMomentEnergyNaturalSourceAdmission.original_scale_caps w hZ hX₁ hX₂ hw
    (by linarith : (1/6:ℝ)≤κ) hcap hs
  have hv:=balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs
  have hprod:1≤∏i,Z^(w i):=by
    rw [←Real.rpow_sum_of_pos hp]
    exact Real.one_le_rpow hZ.le (Finset.sum_nonneg (fun i _=>hw i))
  have hxy:X₁*X₂≤volume balancedSource:=by
    change X₁*X₂≤X₁*X₂*(∏i,Z^(w i))
    exact le_mul_of_one_le_right (mul_pos hX₁ hX₂).le hprod
  have hY:1≤comparisonFirst Z s.width:=Real.one_le_rpow hZ.le (div_nonneg s.width_nonneg (by norm_num))
  refine ⟨hx.1,hx.2,?_,?_⟩
  · change Z^(s.width/4)≤Z^L
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [s.width_nonneg])
  · change X₁*X₂/comparisonFirst Z s.width≤Z^L
    exact (div_le_self (mul_pos hX₁ hX₂).le hY).trans (hxy.trans hv)

theorem four_lower_scales (hZ:1<Z)(hwidth:0<s.width)
    (hshort:s.width/4≤min (length Z X₁) (length Z X₂)) :
    Z^(s.width/4)≤(balancedSource).X₁ ∧ Z^(s.width/4)≤(balancedSource).X₂ ∧
    Z^(s.width/4)≤(balancedSource).Y₁ ∧ Z^(s.width/4)≤(balancedSource).Y₂ := by
  have hh:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

theorem state_capacity_packet (κ L:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width)(hs:s.width≤L) :
    1≤s.radial.scale ∧ s.radial.scale⁻¹≤1 ∧
    (balancedSource).η=s.character ∧ (balancedSource).m=s.mask ∧
    length Z (balancedSource).X₁+length Z (balancedSource).X₂+6*κ*(∑i,w i)≤s.width ∧
    Real.logb Z s.radial.scale+Real.logb Z ((balancedSource).η.modulus.absNorm:ℝ)≤s.width ∧
    volume balancedSource≤Z^s.width ∧ Real.logb Z (volume balancedSource)≤s.width ∧
    volume balancedSource≤Z^L ∧
    (s.puncture.absNorm:ℝ)≤Z^Bmask := by
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  exact ⟨hr.1,hr.2.1,rfl,rfl,hcap,actual_width_le s hZ,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl,
    balanced_log_volume M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ hZ hw hκ hcap,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs,s.puncture_bound⟩

end SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

end

end OAI

end Source2141

/- Original source: OAI/NumberTheory/DirichletL/Energy/ReferenceLowEmpty.lean; sha256: 43f216d3c5e39eceec0479cb8975aeebf9f157f8cdb28b237ba00750f8a9ecb9 -/
section Source2142
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowEmpty
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α][IsEmpty α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem zero_low_positive_empty
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)(hC:0≤C)
    (h:ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C):
    PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C:=by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hsmall
  have hh:=h s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ (by simpa using hsmall)
  have hid:energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=
      s.plainEnergy p t X₁ X₂:=by
    simp only [energy,positiveSlotRow,NaturalState.plainEnergy,Finset.univ_eq_empty,
      Finset.prod_empty,mul_one]
  rw [hid]
  apply hh.trans
  have hp:(1+‖t‖)^degree≤(1+|t|+height)^degree:=by
    apply pow_le_pow_left₀ (by positivity)
    rw [Real.norm_eq_abs]
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by unfold diagonalControl;positivity))
    (Real.rpow_nonneg (zero_le_one.trans s.base_ge_one) _)

end SevenEighths.CenteredMomentEnergyReferenceLowEmpty

end

end OAI

end Source2142

/- Original source: OAI/NumberTheory/DirichletL/Energy/LowBandEmpty.lean; sha256: 8896d452b4b3b0652931286d139b8ec5867defb6e3153accea92a7e4b3c8360d -/
section Source2143
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyLowBandEmpty
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem positive_low_zero
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (h:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C):
    ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  let T:Finset α:=∅
  let θ:T→RayQuotient.Characters M H:=fun i=>False.elim (Finset.notMem_empty _ i.property)
  let w:T→ℝ:=fun _=>0
  have hcap:length Z X₁+length Z X₂+6*κ*(∑i:T,w i)≤s.width:=by
    simp only [T,w,Finset.sum_const_zero,mul_zero,add_zero]
    linarith [s.width_nonneg]
  have hl:length Z X₁+length Z X₂+(∑i:T,w i)≤5*s.width/6:=by
    simpa only [w,Finset.sum_const_zero,add_zero] using hsmall
  have hh:=h T θ w w w t 0 (fun _=>le_rfl)
    (fun i=>False.elim (Finset.notMem_empty _ i.property))
    (fun i=>False.elim (Finset.notMem_empty _ i.property))
    (fun i=>False.elim (Finset.notMem_empty _ i.property)) le_rfl
    (fun _=>by simp [w]) s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hl
  have hid:energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (w i) (w i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=
      s.plainEnergy p t X₁ X₂:=by
    simp only [T,energy,positiveSlotRow,NaturalState.plainEnergy,Finset.univ_eq_empty,
      Finset.prod_empty,mul_one]
  rw [hid] at hh
  simpa only [add_zero,Real.norm_eq_abs] using hh

end SevenEighths.CenteredMomentEnergyLowBandEmpty

end

end OAI

end Source2143

/- Original source: OAI/NumberTheory/DirichletL/Energy/PositiveLowBandSource.lean; sha256: 7c92ce7de0f562b727b4f00895600d2a94509793a84781db5ffdb0a708bf9aaa -/
section Source2144
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveLowBandSource
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def PhysicalLowAt (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (a b bΦ Bmask L Lslot rho Mcap κ ξ e Z:ℝ)(ha:0<a)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(η₀:Character)(Q:Ideal O)
    (S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ freq:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→∀hσlo:∀i,lo≤σ i,∀hσhi:∀i,σ i≤hi,
    0≤height→(∀i,|freq i|≤height)→
  ∀state:NaturalState Z Bmask bΦ,state.fixedModulus=internalQ Q η₀→ rho≤state.width→state.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤state.width→
    length Z X₁+length Z X₂+(∑i,w i)≤5*state.width/6→
    physicalMass (zeroSourceInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂)
      state.puncture 1 fixedBadMask 1 (Ψ T) state.radial.scale Z ξ /
      volume (sourceInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂)≤
      C*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e)

theorem actual_low_stages_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hMcap:0≤Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧∃Cfixed:ℝ,0<Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Lslot rho κ e:ℝ)(η₀:Character)(Q:Ideal O)(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical:ℝ),
      1/6≤κ→0≤Cphysical→εdiag≤e→-saving≤e→
      PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1))→
      PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cphysical→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1)) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap e Z J (insert (0,0) S)
        (Cfixed*(Cphysical+1)):=by
  have hfixed (T:Finset α):=natural_low_source_bound (ι:=T) W hW aslot bslot lo hi
    a b bΦ Mcap εdiag ξ saving haslot hWs hbslot ha hb hbΦ hMcap hεdiag hξ
  choose Ψ hΨs hΨn Cj hCj hbound using hfixed
  let Cfixed:ℝ:=1+∑T:Finset α,Cj T
  have hCfixed:0<Cfixed:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
    dsimp [Cfixed];linarith
  have hCC (T:Finset α):Cj T≤Cfixed:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
      (Finset.mem_univ T)
    dsimp [Cfixed];linarith
  refine ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,?_⟩
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hall,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro Bmask L Lslot rho κ e η₀ Q S J Cphysical hκ hCphysical he hsave hold hmass
  have hpositive:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
      J (insert (0,0) S) (Cfixed*(Cphysical+1)):=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidth
      p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
    by_cases hsmall:state.width≤ rho
    · exact hold T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
        state hQ hsmall p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
    have hp:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      state hQ (le_of_not_ge hsmall) hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
    have hh:=(hZ T).2 M H hH η₀ θ w σ freq hw (fun i=>⟨hσlo i,hσhi i⟩)
      Bmask state p t X₁ X₂ hX₁ hX₂ κ hκ (hcapacity.trans hwidth)
      S J Cphysical height e hCphysical hheight he hsave hp
    have hc:=hCC T
    have hd:=diagonalControl_nonneg state.radial.profile
    have hz:0≤Z:=zero_le_one.trans hZ1.le
    apply hh.trans
    gcongr
  exact ⟨hpositive,CenteredMomentEnergyLowBandEmpty.positive_low_zero (α:=α) M H hH
    W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J (insert (0,0) S)
    (Cfixed*(Cphysical+1)) hpositive⟩

end SevenEighths.CenteredMomentEnergyPositiveLowBandSource

end

end OAI

end Source2144

/- Original source: OAI/NumberTheory/DirichletL/Energy/StageReserve.lean; sha256: e173967b9f82d94b8d40dcf2457a517952121d9e753e654650d3879993f6df73 -/
section Source2145
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyStageReserve
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyReferenceScalarReserve

theorem exists_separated_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0<rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*(
        Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤
        C*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,hledger⟩:=
    exists_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hB
  refine ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,?_⟩
  intro e he Z hZ s hwidth α _ w hw
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hze:1≤Z^e:=Real.one_le_rpow hZ he
  have hp:Z^(s.width+e)≤Z^e*Z^(s.width+d):=by
    rw [←Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  let A:ℝ:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))
  let B:ℝ:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hLp:0≤L:=by linarith
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hA:0≤A:=by dsimp [A];positivity
  have hB0:0≤B:=by dsimp [B];positivity
  have hb:B≤Z^e*B:=by nlinarith
  have hh:=add_le_add (add_le_add hp (mul_le_mul_of_nonneg_left hp hA)) hb
  have hrad:0≤(s.puncture.radical.absNorm:ℝ)^d:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hh':=(mul_le_mul_of_nonneg_left hh hrad)
  have hend:=mul_le_mul_of_nonneg_left (hledger Z hZ s hwidth α w hw)
    (Real.rpow_nonneg hz.le e)
  calc
    _≤Z^e*((s.puncture.radical.absNorm:ℝ)^d*(Z^(s.width+d)+A*Z^(s.width+d)+B)):=by
      convert hh' using 1 ; dsimp [A,B] ; ring
    _≤Z^e*(C*Z^(s.width+ε)):=by
      exact hend
    _=C*Z^(s.width+e+ε):=by
      rw [mul_left_comm,←Real.rpow_add hz]
      congr 2
      ring

lemma inherited_loss_budget (incoming overhead final:ℝ)
    (hin:incoming≤final/2)(hover:overhead≤final/2):incoming+overhead≤final:=by
  linarith

end SevenEighths.CenteredMomentEnergyStageReserve

end

end OAI

end Source2145

/- Original source: OAI/NumberTheory/DirichletL/Energy/WidthSchedule.lean; sha256: 2b55ce3ad606f637c8c2d656cfb1f435b5ca6f4359dee6b96d96f5c542092836 -/
section Source2146
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyWidthSchedule
open CenteredMomentSuccessorPaidParameters CenteredMomentFirstSecondLossParameters

def amplification (ε:ℝ):ℝ := min 1 (ε/16000)
def count (M ε:ℝ):ℕ := depth M (amplification ε)
def scale (M B ε:ℝ):ℝ := (count M ε:ℝ)+M+10*B+30
def reserve (M B ε:ℝ):ℝ :=
  min (amplification ε/100) (ε/(1000000*scale M B ε))
def mesh (M B κ ε:ℝ):ℝ := reserve M B ε/(κ+1)
def width (M B ε:ℝ)(k:ℕ):ℝ := reserve M B ε/16+(k:ℝ)*amplification ε/2
def loss (M B ε:ℝ)(k:ℕ):ℝ := reserve M B ε+64*(k:ℝ)*reserve M B ε

theorem bounds (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε):
    0<amplification ε ∧ amplification ε≤1 ∧ amplification ε≤ε/16000 ∧
    0<reserve M B ε ∧ 0<mesh M B κ ε ∧ mesh M B κ ε≤reserve M B ε ∧
    κ*mesh M B κ ε≤reserve M B ε ∧
    20*reserve M B ε≤amplification ε/2 ∧
    M<width M B ε (count M ε) ∧
    loss M B ε (count M ε)≤ε/1000 :=by
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  have hs1:amplification ε≤1:=min_le_left _ _
  have hse:amplification ε≤ε/16000:=min_le_right _ _
  have hn:0≤(count M ε:ℝ):=Nat.cast_nonneg _
  have hL:0<scale M B ε:=by unfold scale;positivity
  have hr:0<reserve M B ε:=lt_min (by positivity) (by positivity)
  have hrs:reserve M B ε≤amplification ε/100:=min_le_left _ _
  have hre:reserve M B ε≤ε/(1000000*scale M B ε):=min_le_right _ _
  have hp:reserve M B ε*(1000000*scale M B ε)≤ε:=
    (le_div_iff₀ (by positivity)).mp hre
  have hnL:(count M ε:ℝ)≤scale M B ε:=by unfold scale;linarith
  have h1L:1≤scale M B ε:=by unfold scale;linarith
  have hnR:(count M ε:ℝ)*reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right hnL hr.le
    nlinarith
  have hR:reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right h1L hr.le
    nlinarith
  have hm:0<mesh M B κ ε:=by unfold mesh;positivity
  have hmr:mesh M B κ ε≤reserve M B ε:=by
    unfold mesh
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hkm:κ*mesh M B κ ε≤reserve M B ε:=mesh_cost κ _ hκ hr.le
  have hw:M<width M B ε (count M ε):=by
    have hd:=depth_covers M (amplification ε) hs
    change M<(count M ε:ℝ)*amplification ε/2 at hd
    unfold width
    linarith
  refine ⟨hs,hs1,hse,hr,hm,hmr,hkm,by linarith,hw,?_⟩
  unfold loss
  linarith

lemma reserve_cost (M B ε c:ℝ)(hM:0≤M)(hB:0≤B)(hε:0<ε)
    (hc:c≤scale M B ε):c*reserve M B ε≤ε/1000000:=by
  have hL:0<scale M B ε:=by unfold scale;positivity
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  have hr:0<reserve M B ε:=lt_min (by positivity) (by positivity)
  have hre:reserve M B ε≤ε/(1000000*scale M B ε):=min_le_right _ _
  have hp:reserve M B ε*(1000000*scale M B ε)≤ε:=
    (le_div_iff₀ (by positivity)).mp hre
  have hh:=mul_le_mul_of_nonneg_right hc hr.le
  nlinarith

theorem one_time_losses (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (df es d theta other A:ℝ)(hdf:df≤reserve M B ε)(hes:es≤reserve M B ε)
    (hd:d≤reserve M B ε)(ht:theta≤reserve M B ε)(ho:other≤reserve M B ε)
    (he0:0≤es)(hA:A≤M):
    exceptional (amplification ε) df es d B theta≤ε/1000 ∧
      diagonal (amplification ε) d other es A≤ε/1000:=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hs:=hb.2.2.1
  have hr:=hb.2.2.2.1
  have hx:=reserve_cost M B ε (10*B+7) hM hB hε (by unfold scale;linarith [Nat.cast_nonneg (α:=ℝ) (count M ε)])
  have hy:=reserve_cost M B ε (M+2) hM hB hε (by unfold scale;linarith [Nat.cast_nonneg (α:=ℝ) (count M ε)])
  have htheta:=mul_le_mul_of_nonneg_left ht (show 0≤2*(5*B+1) by positivity)
  have hmul:es*A≤reserve M B ε*M:=
    (mul_le_mul_of_nonneg_left hA he0).trans (mul_le_mul_of_nonneg_right hes hM)
  constructor
  · unfold exceptional
    nlinarith
  · unfold diagonal
    nlinarith

lemma mesh_lt_prime_width (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε):
    mesh M B κ ε<amplification ε/6:=by
  have h:=bounds M B κ ε hM hB hκ hε
  have hp:=h.1
  have hm:=h.2.2.2.2.2.1
  have hr:=h.2.2.2.2.2.2.2.1
  linarith

lemma width_zero (M B ε:ℝ):width M B ε 0=reserve M B ε/16:=by simp [width]
lemma loss_zero (M B ε:ℝ):loss M B ε 0=reserve M B ε:=by simp [loss]
lemma width_succ (M B ε:ℝ)(k:ℕ):
    width M B ε (k+1)-amplification ε/2=width M B ε k:=by
  simp only [width,Nat.cast_add,Nat.cast_one]
  ring
lemma loss_succ (M B ε:ℝ)(k:ℕ):
    loss M B ε (k+1)=loss M B ε k+64*reserve M B ε:=by
  simp only [loss,Nat.cast_add,Nat.cast_one]
  ring

lemma child_band (M B ε parent child:ℝ)(k:ℕ)
    (hp:parent≤width M B ε (k+1))(hc:child≤parent-amplification ε/2):
    child≤width M B ε k:=by
  rw [←width_succ M B ε k]
  linarith

lemma loss_le_final (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(hk:k≤count M ε):loss M B ε k≤ε/1000:=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hr:=hb.2.2.2.1
  have hk':(k:ℝ)≤(count M ε:ℝ):=by exact_mod_cast hk
  apply le_trans _ hb.2.2.2.2.2.2.2.2.2
  unfold loss
  gcongr

lemma next_paid_loss (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(er d e d1 d2 theta other:ℝ)
    (her:er≤reserve M B ε)(hd:d≤reserve M B ε)(he:e≤reserve M B ε)
    (hd1:d1≤reserve M B ε)(hd2:d2≤reserve M B ε)(ht:theta≤reserve M B ε)
    (ho:other≤50*reserve M B ε):
    loss M B ε k+edge 0 er d e d1 d2 theta κ (mesh M B κ ε)+other≤
      loss M B ε (k+1):=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hr:=hb.2.2.2.1
  have hm:=hb.2.2.2.2.2.2.1
  rw [loss_succ]
  unfold edge
  linarith

theorem actual_removal_path {ι:Type*}[DecidableEq ι]
    (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0<κ)(hε:0<ε)
    (n:ℕ)(J:Fin n→Finset ι)(w:Fin n→ι→ℝ)(x y state:Fin n→ℝ)
    (hw:∀k,∀i∈J k,0≤w k i)(hm:∀k,∀i∈J k,w k i≤mesh M B κ ε):
    ∃R:Fin n→Finset ι,(∀k,R k⊆J k) ∧
      (∀k,R k=J k ∨ x k+y k+6*κ*(∑i∈J k\R k,w k i)≤state k) ∧
      (∑k,κ*(∑i∈R k,w k i))≤
        (∑k,CenteredMomentLiveCapacity.excess (J k) (w k) (x k) (y k) (state k) κ/6)+
          (n:ℝ)*reserve M B ε:=by
  have hb:=bounds M B κ ε hM hB hκ.le hε
  have hmesh:=hb.2.2.2.2.1
  have hcost:=hb.2.2.2.2.2.2.1
  choose R hR hcap hpay using fun k=>CenteredMomentLiveCapacity.removal_excess_cost
    (J k) (w k) (x k) (y k) (state k) κ (mesh M B κ ε) hκ hmesh.le (hw k) (hm k)
  refine ⟨R,hR,hcap,?_⟩
  calc
    _≤∑k,(CenteredMomentLiveCapacity.excess (J k) (w k) (x k) (y k) (state k) κ/6+
        reserve M B ε):=Finset.sum_le_sum (fun k _=>(hpay k).trans (by linarith))
    _=_:=by rw [Finset.sum_add_distrib];simp

end SevenEighths.CenteredMomentEnergyWidthSchedule

end

end OAI

end Source2146

/- Original source: OAI/NumberTheory/DirichletL/Energy/StageReserveSchedule.lean; sha256: 412602f7f94d069ed7a65edd720f252deabdafccea322e8cdc589ba22cc45d9c -/
section Source2147
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyWidthSchedule CenteredMomentSuccessorPaidParameters

def stageLoss (M B ε:ℝ)(k:ℕ):ℝ:=ε/1000+loss M B ε k

lemma stageLoss_pos (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)(k:ℕ):
    0<stageLoss M B ε k:=by
  have hr:0<reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  unfold stageLoss loss
  positivity

lemma stageLoss_final (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(hk:k≤count M ε):stageLoss M B ε k≤ε/500:=by
  have hh:=loss_le_final M B κ ε hM hB hκ hε k hk
  unfold stageLoss
  linarith

lemma successor_with_references (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(er d e d1 d2 theta other highReflection zeroReflection:ℝ)
    (her:er≤reserve M B ε)(hd:d≤reserve M B ε)(he:e≤reserve M B ε)
    (hd1:d1≤reserve M B ε)(hd2:d2≤reserve M B ε)(ht:theta≤reserve M B ε)
    (ho:other≤48*reserve M B ε)
    (hhigh:highReflection≤reserve M B ε)(hzero:zeroReflection≤reserve M B ε):
    stageLoss M B ε k+edge 0 er d e d1 d2 theta κ (mesh M B κ ε)+
      other+highReflection+zeroReflection≤stageLoss M B ε (k+1):=by
  have hh:=next_paid_loss M B κ ε hM hB hκ hε k er d e d1 d2 theta
    (other+highReflection+zeroReflection) her hd he hd1 hd2 ht (by linarith)
  unfold stageLoss
  linarith

lemma one_time_with_new_cost (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(sourceLoss extra:ℝ)(hsource:sourceLoss≤ε/1000)
    (hextra:extra≤50*reserve M B ε):
    sourceLoss+extra≤stageLoss M B ε (k+1):=by
  have hr:0<reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  have hk:0≤(k:ℝ):=Nat.cast_nonneg _
  simp only [stageLoss,loss,Nat.cast_add,Nat.cast_one]
  nlinarith

lemma actual_one_time_with_new_cost (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(df es d theta other A extra:ℝ)
    (hdf:df≤reserve M B ε)(hes:es≤reserve M B ε)(hd:d≤reserve M B ε)
    (ht:theta≤reserve M B ε)(ho:other≤reserve M B ε)(he0:0≤es)(hA:A≤M)
    (hextra:extra≤50*reserve M B ε):
    CenteredMomentSuccessorPaidParameters.exceptional (amplification ε) df es d B theta+extra≤
      stageLoss M B ε (k+1) ∧
    CenteredMomentSuccessorPaidParameters.diagonal (amplification ε) d other es A+extra≤
      stageLoss M B ε (k+1):=by
  have hh:=one_time_losses M B κ ε hM hB hκ hε df es d theta other A hdf hes hd ht ho he0 hA
  exact ⟨one_time_with_new_cost M B κ ε hM hB hκ hε k _ extra hh.1 hextra,
    one_time_with_new_cost M B κ ε hM hB hκ hε k _ extra hh.2 hextra⟩

end SevenEighths.CenteredMomentEnergyStageReserveSchedule

end

end OAI

end Source2147

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstStageLossBudget.lean; sha256: c042eb1b3bb2f4ddb73078995e815c0471173ebf3e01260ba61abb6a177cb8ae -/
section Source2148
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstStageLossBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentSuccessorPaidParameters
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients

def sourcePaid (Bcap emask ell er delta reserveAmp thetaSource thetaClip κ mesh:ℝ):ℝ:=
  (Bcap+Bcap)*emask+ell+er+(delta+reserveAmp+thetaSource)/6+thetaClip/3+κ*mesh

theorem literal_four_budget (M Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hB:0≤Bcap)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(ell epsSrc epsMask deltaSrc thetaSrc deltaAmp reserveAmp thetaSource thetaClip
      er primeLoss physicalLoss highReflection zeroReflection saving:ℝ)
    (hell:ell≤stageLoss M Bcap ε k)
    (he0:0≤epsSrc)(he:epsSrc≤reserve M Bcap ε)
    (hemask:(Bcap+Bcap)*epsMask≤reserve M Bcap ε)
    (hdsrc:deltaSrc≤reserve M Bcap ε)(htsrc:thetaSrc≤reserve M Bcap ε)
    (hda:0≤deltaAmp)(hra:0≤reserveAmp)(hts:0≤thetaSource)(htc:0≤thetaClip)
    (hsmall:deltaAmp+reserveAmp+thetaSource≤reserve M Bcap ε)
    (hclip:thetaClip≤reserve M Bcap ε)(her:er≤reserve M Bcap ε)
    (hcommon:epsSrc*Bcommon≤reserve M Bcap ε)
    (hprime:primeLoss≤reserve M Bcap ε)(hphysical:physicalLoss≤reserve M Bcap ε)
    (hhigh:highReflection≤reserve M Bcap ε)(hzero:zeroReflection≤reserve M Bcap ε)
    (hsaving:2*amplification ε+deltaAmp+reserveAmp≤saving):
    ∀j:Fin 4,
      losses epsSrc deltaSrc thetaSrc Bcap j+
        lossVector (amplification ε) deltaAmp reserveAmp
          (sourcePaid Bcap epsMask ell er deltaAmp reserveAmp thetaSource thetaClip κ (mesh M Bcap κ ε))
          epsSrc M saving j+
        epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection≤
      stageLoss M Bcap ε (k+1):=by
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0<reserve M Bcap ε:=hb.2.2.2.1
  have hs:0≤amplification ε:=hb.1.le
  have hother:epsSrc*Bcommon+primeLoss+physicalLoss≤48*reserve M Bcap ε:=by linarith
  have hextra:epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection≤
      50*reserve M Bcap ε:=by linarith
  have hdf:deltaAmp+reserveAmp≤reserve M Bcap ε:=by linarith
  have hdelta:deltaAmp≤reserve M Bcap ε:=by linarith
  have hres:reserveAmp≤reserve M Bcap ε:=by linarith
  have hmain:=successor_with_references M Bcap κ ε hM hB hκ hε k
    er deltaSrc epsSrc (deltaAmp+reserveAmp+thetaSource) ((Bcap+Bcap)*epsMask) thetaClip
    (epsSrc*Bcommon+primeLoss+physicalLoss) highReflection zeroReflection
    her hdsrc he hsmall hemask hclip hother hhigh hzero
  have hone:=actual_one_time_with_new_cost M Bcap κ ε hM hB hκ hε k
    (deltaAmp+reserveAmp) epsSrc deltaSrc thetaSrc reserveAmp M
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection)
    hdf he hdsrc htsrc hres he0 le_rfl hextra
  have hdiag:=actual_one_time_with_new_cost M Bcap κ ε hM hB hκ hε k
    (deltaAmp+reserveAmp) epsSrc deltaAmp thetaSrc reserveAmp M
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection)
    hdf he hdelta htsrc hres he0 le_rfl hextra
  have htail:=one_time_with_new_cost M Bcap κ ε hM hB hκ hε k 0
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection) (by positivity) hextra
  intro j
  fin_cases j <;> simp only [losses,lossVector,Matrix.cons_val,Fin.reduceFinMk]
  · dsimp [sourcePaid,edge] at hmain ⊢
    linarith
  · dsimp [exceptional] at hone
    linarith [hone.1]
  · dsimp [diagonal] at hdiag
    linarith [hdiag.2]
  · linarith

theorem chosen_four_budget (M Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hB:0≤Bcap)(hBc:0≤Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε;
    let es:=r/(Bcommon+1);
    let em:=r/(Bcap+Bcap+1);
    0<es ∧ es≤1 ∧ 0<em ∧ 0<r/4 ∧ 0<2*amplification ε+1 ∧
    ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤stageLoss M Bcap ε k→
      highReflection≤r→zeroReflection≤r→∀j:Fin 4,
      losses es (r/4) (r/4) Bcap j+
        lossVector (amplification ε) (r/4) (r/4)
          (sourcePaid Bcap em ell (r/4) (r/4) (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
          es M (2*amplification ε+1) j+
        es*Bcommon+r/4+r/4+highReflection+zeroReflection≤stageLoss M Bcap ε (k+1):=by
  dsimp only
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0<reserve M Bcap ε:=hb.2.2.2.1
  have hs:0<amplification ε:=hb.1
  have hrsmall:reserve M Bcap ε≤amplification ε/100:=min_le_left _ _
  have hr1:reserve M Bcap ε≤1:=by linarith [hb.2.1]
  have hes:0<reserve M Bcap ε/(Bcommon+1):=by positivity
  have hem:0<reserve M Bcap ε/(Bcap+Bcap+1):=by positivity
  have hesle:reserve M Bcap ε/(Bcommon+1)≤reserve M Bcap ε:=by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hemscale:(Bcap+Bcap)*(reserve M Bcap ε/(Bcap+Bcap+1))≤reserve M Bcap ε:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hescale:(reserve M Bcap ε/(Bcommon+1))*Bcommon≤reserve M Bcap ε:=by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  refine ⟨hes,hesle.trans hr1,hem,by positivity,by positivity,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero
  apply literal_four_budget M Bcap Bcommon κ ε hM hB hκ hε k ell
    (reserve M Bcap ε/(Bcommon+1)) (reserve M Bcap ε/(Bcap+Bcap+1))
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    highReflection zeroReflection (2*amplification ε+1)
    hell hes.le hesle hemscale
  all_goals first | exact hescale | exact hhigh | exact hzero | positivity | linarith

end SevenEighths.CenteredMomentEnergyFirstStageLossBudget

end

end OAI

end Source2148

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstDeclaredCapacityLossBudget.lean; sha256: ce5d19aaaeef4f8b92580be6f2f40f2741783fd1c30e6efab03624771168f95e -/
section Source2149
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstDeclaredCapacityLossBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients

lemma lossVector_cap (sigma delta reserveAmp paid es M A saving:ℝ)
    (he:0≤es)(hM:0≤M)(hA:0≤A)(j:Fin 4):
    lossVector sigma delta reserveAmp paid es A saving j≤
      lossVector sigma delta reserveAmp paid es M saving j+es*A:=by
  fin_cases j <;> simp only [lossVector,Matrix.cons_val,Fin.reduceFinMk] <;>
    nlinarith [mul_nonneg he hM,mul_nonneg he hA]

theorem chosen_declared_four_budget (M A Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hA:0≤A)(hB:0≤Bcap)(hBc:0≤Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε
    let es:=r/(4*(Bcommon+A+1))
    let em:=r/(Bcap+Bcap+1)
    0<es ∧ es≤1 ∧ 0<em ∧ es*A≤r/4 ∧ es*Bcommon≤r/4 ∧
    ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤stageLoss M Bcap ε k→
      highReflection≤r→zeroReflection≤r→∀j:Fin 4,
      losses es (r/4) (r/4) Bcap j+
        lossVector (amplification ε) (r/4) (r/4)
          (sourcePaid Bcap em ell (r/4) (r/4) (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
          es A (2*amplification ε+1) j+
        es*Bcommon+r/4+r/4+highReflection+zeroReflection≤stageLoss M Bcap ε (k+1):=by
  dsimp only
  let r:=reserve M Bcap ε
  let es:=r/(4*(Bcommon+A+1))
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0<r:=hb.2.2.2.1
  have hs:0<amplification ε:=hb.1
  have hrsmall:r≤amplification ε/100:=min_le_left _ _
  have hr1:r≤1:=by linarith [hb.2.1]
  have hden:0<4*(Bcommon+A+1):=by positivity
  have hes:0<es:=by dsimp [es];positivity
  have hesle:es≤r/4:=by
    dsimp [es]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hBc,mul_nonneg hr.le hA]
  have hescap:es*A≤r/4:=by
    dsimp [es]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hBc]
  have hescommon:es*Bcommon≤r/4:=by
    dsimp [es]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hA]
  have hemscale:(Bcap+Bcap)*(r/(Bcap+Bcap+1))≤r:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  refine ⟨hes,by linarith,by positivity,hescap,hescommon,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero j
  have hh:=literal_four_budget M Bcap Bcommon κ ε hM hB hκ hε k ell
    es (r/(Bcap+Bcap+1)) (r/4) (r/4) (r/4) (r/4) (r/4) (r/4)
    (r/4) (r/4) (r/4+es*A) highReflection zeroReflection (2*amplification ε+1)
    hell hes.le (by dsimp [r] at *;linarith) hemscale
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    hhigh hzero (by linarith)
  have hc:=lossVector_cap (amplification ε) (r/4) (r/4)
    (sourcePaid Bcap (r/(Bcap+Bcap+1)) ell (r/4) (r/4) (r/4) (r/4) (r/4)
      κ (mesh M Bcap κ ε)) es M A (2*amplification ε+1) hes.le hM hA j
  have hj:=hh j
  change losses es (r/4) (r/4) Bcap j+_+es*Bcommon+r/4+r/4+highReflection+zeroReflection≤_
  linarith only [hj,hc]

end SevenEighths.CenteredMomentEnergyFirstDeclaredCapacityLossBudget

end

end OAI

end Source2149

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstActualFrequencyBudget.lean; sha256: 96bd0011304aa7fdf771255697d9a02a32da573040a85bd0ecff91a81e2c200e -/
section Source2150
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstDeclaredCapacityLossBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentSectorLocalization

theorem eventually_frequency_loss (r:ℝ)(hr:0<r):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      0≤frequencyLoss Z 32 (r/4) ∧ frequencyLoss Z 32 (r/4)≤r/4:=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by positivity:0<r/8))) 128,
    eventually_gt_atTop (1:ℝ)] with Z hpow hZ
  have hlog:=Real.logb_le_logb_of_le hZ (by norm_num:(0:ℝ)<128) hpow
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hlog
  refine ⟨hZ,frequencyLoss_nonneg Z 32 (r/4) hZ (by norm_num) (by positivity),?_⟩
  unfold frequencyLoss
  norm_num only [show (4:ℝ)*32=128 by norm_num]
  linarith only [hlog]

lemma paid_frequency_mono
    (sigma delta delta' reserveAmp Bcap emask ell er thetaSource thetaClip κ mesh
      es A saving:ℝ)(hd:delta≤delta')(j:Fin 4):
    lossVector sigma delta reserveAmp
      (sourcePaid Bcap emask ell er delta reserveAmp thetaSource thetaClip κ mesh)
      es A saving j≤
    lossVector sigma delta' reserveAmp
      (sourcePaid Bcap emask ell er delta' reserveAmp thetaSource thetaClip κ mesh)
      es A saving j:=by
  fin_cases j <;>
    simp only [lossVector,sourcePaid,Matrix.cons_val,Fin.reduceFinMk] <;>
    linarith only [hd]

theorem actual_frequency_four_budget (M A Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hA:0≤A)(hB:0≤Bcap)(hBc:0≤Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε
    let es:=r/(4*(Bcommon+A+1))
    let em:=r/(Bcap+Bcap+1)
    0<es ∧ es≤1 ∧ 0<em ∧ 0<r/4 ∧ r/4≤amplification ε/4 ∧
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      0≤frequencyLoss Z 32 (r/4) ∧ frequencyLoss Z 32 (r/4)≤r/4 ∧
      ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤stageLoss M Bcap ε k→
        highReflection≤r→zeroReflection≤r→∀j:Fin 4,
        losses es (r/4) (r/4) Bcap j+
          lossVector (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
            (sourcePaid Bcap em ell (r/4) (frequencyLoss Z 32 (r/4))
              (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
            es A (2*amplification ε+1) j+
          es*Bcommon+r/4+r/4+highReflection+zeroReflection≤stageLoss M Bcap ε (k+1):=by
  dsimp only
  let r:=reserve M Bcap ε
  let es:=r/(4*(Bcommon+A+1))
  let em:=r/(Bcap+Bcap+1)
  obtain ⟨hes,hes1,hem,_,_,hbudget⟩:=chosen_declared_four_budget M A Bcap Bcommon κ ε
    hM hA hB hBc hκ hε
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0<r:=hb.2.2.2.1
  have hrs:r≤amplification ε/100:=min_le_left _ _
  refine ⟨hes,hes1,hem,by positivity,by linarith [hb.1],?_⟩
  filter_upwards [eventually_frequency_loss r hr] with Z hZ
  refine ⟨hZ.1,hZ.2.1,hZ.2.2,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero j
  have hfixed:=hbudget k ell highReflection zeroReflection hell hhigh hzero j
  have hmono:=paid_frequency_mono (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
    (r/4) Bcap em ell (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε) es A
    (2*amplification ε+1) hZ.2.2 j
  change losses es (r/4) (r/4) Bcap j+_+es*Bcommon+r/4+r/4+highReflection+zeroReflection≤_ at hfixed ⊢
  linarith only [hfixed,hmono]

end SevenEighths.CenteredMomentEnergyFirstActualFrequencyBudget

end

end OAI

end Source2150

/- Original source: OAI/NumberTheory/DirichletL/Energy/WidthRanges.lean; sha256: 4fd022dd8ef39d5e89a0eac27ccb8ebfbf02e55143d52a89f3e39666c73b9f5a -/
section Source2151
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyProfiles CenteredMomentEnergyWidthSchedule

def step (M B L:ℝ):ℝ:=4*(L+M+B+4)
def range (M B L:ℝ):ℕ→ℝ
  | 0=>max 1 L
  | n+1=>step M B (range M B L n)
def sourceCap (M B L:ℝ)(n:ℕ):ℝ:=10*(range M B L n+M+B+1)
def finalSourceCap (M B L ε:ℝ):ℝ:=sourceCap M B L (count M ε)
def fineMesh (M B L κ ε:ℝ):ℝ:=mesh M (finalSourceCap M B L ε) κ ε

lemma range_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):0≤range M B L n:=by
  induction n with
  | zero=>exact zero_le_one.trans (le_max_left _ _)
  | succ n ih=>simp only [range,step];positivity

lemma range_mono (M B L:ℝ)(hM:0≤M)(hB:0≤B):Monotone (range M B L):=by
  apply monotone_nat_of_le_succ
  intro n
  have hh:=range_nonneg M B L hM hB n
  simp only [range,step]
  linarith

lemma range_original (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):L≤range M B L n:=by
  exact (le_max_right (1:ℝ) L).trans (range_mono M B L hM hB (Nat.zero_le n))

lemma step_admits (M B L rho d e:ℝ)(hM:0≤M)(hB:0≤B)(hL:0≤L)
    (hrho:rho≤1)(hd:d≤1)(he:e≤1):
    L≤step M B L ∧ M+B+rho/100+1≤step M B L ∧
    max L (M+B+2*d)+1≤step M B L ∧
    2*L+e≤step M B L ∧
    2*(max L (M+B+2*d)+1)+e≤step M B L:=by
  have hmax:max L (M+B+2*d)≤L+M+B+2:=by
    apply max_le <;> linarith
  unfold step
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma range_envelope (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):
    range M B L n≤(8:ℝ)^n*(max 1 L+M+B+4):=by
  induction n with
  | zero=>simp only [range,pow_zero,one_mul];linarith
  | succ n ih=>
    have hp:1≤(8:ℝ)^n:=one_le_pow₀ (by norm_num)
    have ha:0≤max 1 L:=zero_le_one.trans (le_max_left _ _)
    have hm:M+B+4≤(8:ℝ)^n*(max 1 L+M+B+4):=by
      have hh:=mul_le_mul_of_nonneg_right hp (show 0≤max 1 L+M+B+4 by positivity)
      simp only [one_mul] at hh
      linarith
    simp only [range,step,pow_succ]
    nlinarith

lemma ready_exponent_le (M B L A D P q e xi:ℝ)(n:ℕ)
    (hM:0≤M)(hB:0≤B)
    (hA:A≤2*range M B L n+M+1)(hD:D≤1)(hP:P≤B)
    (hq:q≤4*range M B L n+3*M+4)(he:e≤1)(hxi:xi≤1):
    CenteredMomentFirstSecondInputGates.exponent A D P q e xi≤sourceCap M B L n:=by
  have hr:=range_nonneg M B L hM hB n
  unfold CenteredMomentFirstSecondInputGates.exponent sourceCap
  apply max_le
  · linarith
  apply max_le
  · linarith
  apply max_le <;> linarith

lemma sourceCap_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):0≤sourceCap M B L n:=by
  have hr:=range_nonneg M B L hM hB n
  unfold sourceCap
  positivity

lemma fineMesh_pos (M B L κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε):
    0<fineMesh M B L κ ε:=by
  exact (bounds M (finalSourceCap M B L ε) κ ε hM
    (sourceCap_nonneg M B L hM hB _) hκ hε).2.2.2.2.1

lemma support_step (a b:ℝ)(ha:0<a)(n:ℕ):
    0<lower a b (n+1) ∧ lower a b (n+1)=lower a b n/max 1 b:=
  ⟨lower_pos a b ha _,rfl⟩

end SevenEighths.CenteredMomentEnergyWidthRanges

end

end OAI

end Source2151

/- Original source: OAI/NumberTheory/DirichletL/Energy/StageMargins.lean; sha256: c1ea4cc1264ad298f734639488564ffbdf27791b6d7249d949b39db9f774527d -/
section Source2152
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyStageMargins
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule

def physicalLoss (M B ε:ℝ)(k:ℕ):ℝ:=stageLoss M B ε (k+1)-2*reserve M B ε
def reflectedLoss (M B ε:ℝ)(k:ℕ):ℝ:=physicalLoss M B ε k+reserve M B ε

lemma physicalLoss_eq (M B ε:ℝ)(k:ℕ):
    physicalLoss M B ε k=stageLoss M B ε k+62*reserve M B ε:=by
  unfold physicalLoss stageLoss
  rw [loss_succ]
  ring
lemma reflected_then_zero (M B ε:ℝ)(k:ℕ):
    reflectedLoss M B ε k+reserve M B ε=stageLoss M B ε (k+1):=by
  unfold reflectedLoss physicalLoss
  ring
lemma margins (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)(k:ℕ):
    0<physicalLoss M B ε k ∧
    stageLoss M B ε k≤physicalLoss M B ε k ∧
    reserve M B ε/4≤physicalLoss M B ε k ∧
    physicalLoss M B ε k≤reflectedLoss M B ε k ∧
    reflectedLoss M B ε k≤stageLoss M B ε (k+1):=by
  have hr:0<reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  have he:=stageLoss_pos M B κ ε hM hB hκ hε k
  have hp:=physicalLoss_eq M B ε k
  have hf:=reflected_then_zero M B ε k
  unfold reflectedLoss at *
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end SevenEighths.CenteredMomentEnergyStageMargins

end

end OAI

end Source2152

/- Original source: OAI/NumberTheory/DirichletL/Energy/FirstSourceParameters.lean; sha256: 6e61abb66638c297a7df789be01a3d8986824c886256351ea98d0e69b12d96b6 -/
section Source2153
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentSectorLocalization

def sourceEpsilon (M A B ε:ℝ):ℝ:=reserve M B ε/(4*((A+1)+A+1))
def maskEpsilon (M B ε:ℝ):ℝ:=reserve M B ε/(B+B+1)
def columnLoss (M B ε:ℝ)(k:ℕ):ℝ:=
  stageLoss M B ε (k+1)-2*reserve M B ε-reserve M B ε/4

lemma source_cap_mono (es ds ts Bactual Bschedule sigma delta amp em child er θs θc κ mesh A saving:ℝ)
    (hB:Bactual≤Bschedule)(ht:0≤ts)(hem:0≤em)(j:Fin 4):
    losses es ds ts Bactual j+
      lossVector sigma delta amp (sourcePaid Bactual em child er delta amp θs θc κ mesh) es A saving j≤
    losses es ds ts Bschedule j+
      lossVector sigma delta amp (sourcePaid Bschedule em child er delta amp θs θc κ mesh) es A saving j:=by
  fin_cases j <;>
    simp only [losses,lossVector,sourcePaid,Matrix.cons_val,Fin.reduceFinMk] <;>
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hB),mul_nonneg hem (sub_nonneg.mpr hB)]

theorem parameter_gates (M A B κ ε:ℝ)(hM:0≤M)(hA:0≤A)(hB:0≤B)
    (hκ:(3/4:ℝ)≤κ)(hε:0<ε):
    let sigma:=amplification ε
    let r:=reserve M B ε
    0<sigma ∧ sigma≤1 ∧ 0<r/4 ∧ r/4≤sigma/4 ∧ r/4≤1 ∧
      0<sourceEpsilon M A B ε ∧ sourceEpsilon M A B ε≤1 ∧
      0<maskEpsilon M B ε ∧ 0<mesh M B κ ε ∧
      mesh M B κ ε≤sigma/12 ∧ 0≤sigma/12 ∧ sigma/12<sigma/6 ∧
      0<2*sigma+1 ∧ 0≤A+1:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have hb:=bounds M B κ ε hM hB hκ0 hε
  have hr:=hb.2.2.2.1
  have hrs:reserve M B ε≤amplification ε/100:=min_le_left _ _
  have hm:=hb.2.2.2.2.2.1
  have hes:0<sourceEpsilon M A B ε:=by unfold sourceEpsilon;positivity
  have hesr:sourceEpsilon M A B ε≤reserve M B ε:=by
    unfold sourceEpsilon
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hr.le hA]
  exact ⟨hb.1,hb.2.1,by positivity,by linarith,by linarith,
    hes,by linarith,by unfold maskEpsilon;positivity,hb.2.2.2.2.1,
    by linarith,by linarith [hb.1],by linarith [hb.1],by linarith [hb.1],by linarith⟩

lemma columnLoss_physical (M B ε:ℝ)(k:ℕ):
    columnLoss M B ε k+reserve M B ε/4=
      CenteredMomentEnergyStageMargins.physicalLoss M B ε k:=by
  unfold columnLoss CenteredMomentEnergyStageMargins.physicalLoss
  ring

theorem eventually_actual_four_fit (M A P B κ ε:ℝ)
    (hM:0≤M)(hA:0≤A)(_hP:0≤P)(hB:0≤B)(hready:readyBudget A P≤B)
    (hκ:(3/4:ℝ)≤κ)(hε:0<ε):
    let r:=reserve M B ε
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(k:ℕ)(εchild:ℝ),εchild≤stageLoss M B ε k→∀j:Fin 4,
        losses (sourceEpsilon M A B ε) (r/4) (r/4) (readyBudget A P) j+
          lossVector (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
            ((readyBudget A P+readyBudget A P)*maskEpsilon M B ε+εchild+r/4+
              (frequencyLoss Z 32 (r/4)+r/4+r/4)/6+(r/4)/3+κ*mesh M B κ ε)
            (sourceEpsilon M A B ε) A (2*amplification ε+1) j+
          sourceEpsilon M A B ε*(A+1)+r/4≤columnLoss M B ε k:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have h:=actual_frequency_four_budget M A B (A+1) κ ε hM hA hB (by linarith) hκ0 hε
  obtain ⟨_,_,hem,_,_,hevent⟩:=h
  have hr:0<reserve M B ε:=(bounds M B κ ε hM hB hκ0 hε).2.2.2.1
  filter_upwards [hevent] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro k εchild hchild j
  have hfit:=hZ.2.2.2 k εchild (reserve M B ε) (reserve M B ε) hchild le_rfl le_rfl j
  have hmono:=source_cap_mono (sourceEpsilon M A B ε) (reserve M B ε/4) (reserve M B ε/4)
    (readyBudget A P) B (amplification ε) (frequencyLoss Z 32 (reserve M B ε/4))
    (reserve M B ε/4) (maskEpsilon M B ε) εchild (reserve M B ε/4)
    (reserve M B ε/4) (reserve M B ε/4) κ (mesh M B κ ε) A (2*amplification ε+1)
    hready (by positivity) hem.le j
  change losses (sourceEpsilon M A B ε) _ _ B j+
    lossVector _ _ _ (sourcePaid B (maskEpsilon M B ε) εchild _ _ _ _ _ _ _) _ _ _ j+
    sourceEpsilon M A B ε*(A+1)+_+_+_+_≤_ at hfit
  dsimp only [sourcePaid] at hmono hfit
  unfold columnLoss
  dsimp only [sourceEpsilon,maskEpsilon] at hmono hfit ⊢
  linarith only [hmono,hfit]

theorem ready_budget_final (M Bmask L ε A P:ℝ)(hM:0≤M)(hB:0≤Bmask)
    (hA:A≤2*CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε)+M+1)
    (hP:P≤Bmask):
    readyBudget A P≤CenteredMomentEnergyWidthRanges.finalSourceCap M Bmask L ε:=by
  have hn:1≤count M ε:=by
    unfold count CenteredMomentFirstSecondLossParameters.depth
    omega
  have hm:=CenteredMomentEnergyWidthRanges.range_mono M Bmask L hM hB hn
  have hr:20≤CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε):=by
    simp only [CenteredMomentEnergyWidthRanges.range,CenteredMomentEnergyWidthRanges.step] at hm
    linarith [le_max_left (1:ℝ) L]
  unfold readyBudget CenteredMomentEnergyWidthRanges.finalSourceCap CenteredMomentEnergyWidthRanges.sourceCap
  linarith

end SevenEighths.CenteredMomentEnergyFirstSourceParameters

end

end OAI

end Source2153

/- Original source: OAI/NumberTheory/DirichletL/Energy/NaturalLowPhysical.lean; sha256: cb1ea4e3b4b00293b23463f4c70e168abcecb1729d170e8a4a4e83621ee3bf4c -/
section Source2154
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalLowPhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyPositiveLowBandSource
open CenteredMomentEnergyNaturalSourceAdmission
open CenteredMomentEnergyPositiveHighParameters CenteredMomentEnergyPositiveBalancedAdmission
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_natural_low_physical
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hMg:0≤Mglobal)(hA:0≤A)(hB:0≤B)(hBm:0≤Bmask)
    (_hMp:0≤Mparent)(hMc:0≤Mchild)(hL:0≤Lgoal)(hLs:0≤Lslot)
    (hMA:Mparent≤A)(hready:readyBudget A Bmask≤B)
    (hκ:(3/4:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤Mchild)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤stageLoss Mglobal B ε k→0≤C₀→0≤C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalLowAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
        a b bΦ Bmask Lgoal Lslot rho Mparent κ (reserve Mglobal B ε/4)
        (physicalLoss Mglobal B ε k) Z ha Ψ η₀ Q U J (C*(C₀+C₁+1)) := by
  let r:=reserve Mglobal B ε
  let N:=Fintype.card α
  let Mslot:=profileBound W hW.continuous aslot bslot lo hi haslot hWs
  let a0:=CenteredMomentSecondInputCapacitySource.lowerFactor N aslot a
  let lp:=(min 1 aslot)^N*a*a
  have hMslot:1≤Mslot:=profileBound_ge_one W hW.continuous aslot bslot lo hi haslot hWs
  have ha0:0<a0:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N aslot a haslot ha
  have hlp:0<lp:=by dsimp [lp];positivity
  obtain ⟨hsigma,hsigma1,hr,hxi,hxi1,hes,hes1,hem,hmesh,hmesheta,heta,hetastrict,_,_⟩:=
    parameter_gates Mglobal A B κ ε hMg hA hB hκ hε
  have hrpos:0<r/4:=hr
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hLbase:0≤max Lgoal Mparent:=hL.trans (le_max_left _ _)
  have hLphys:0≤2*max Lgoal Mparent+r/4:=by positivity
  obtain ⟨U,J,hphysical⟩:=CenteredMomentEnergyCanonicalLowPhysical.actual_low_physical (α:=α)
    M H hH W aslot bslot Mchild Lslot (r/4) lo hi κ a b Mslot (maskEpsilon Mglobal B ε)
    (zero_le_one.trans hMslot) hem ha hb (2*max Lgoal Mparent+r/4) hLphys degree S haslot hWs hW hMc hLs hr
    hκsmall hbeta hκbeta N aslot (max 1 bslot) a0 (r/4) haslot (le_max_left _ _) ha0 hr
    (fun _=>aslot) (fun _=>bslot) (fun _=>hbslot)
    (sourceEpsilon Mglobal A B ε) (r/4) (r/4) (A+1) (r/4) (2*amplification ε+1)
    hes hr hr hr (amplification ε) hsigma hxi A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBm hetastrict hr hsigma1 hxi1 hr hes1 le_rfl Ψ (r/4) lp hr hlp
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Z₀,hZ₀,hbound⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,
    eventually_actual_four_fit Mglobal A Bmask B κ ε hMg hA hBm hB hready hκ hε,
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b),
    eventually_scale_admission b (max Lgoal Mparent) (r/4) hLbase hr]
    with Z hZZ hfit hclipPow hscale
  have hZ:1<Z:=hZ₀.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0<max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hstate
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hlow
  let inp:=zeroSourceInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hN:Fintype.card T≤N:=Fintype.card_le_of_injective (fun i:T=>i.val) Subtype.val_injective
  have hm:=(both_matches M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂).2
  have hu:=hscale.2 T M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) Bmask bΦ a state p ha t X₁ X₂ hX₁ hX₂ κ
    hw hκsmall (hstate.trans (le_max_right _ _)) hcapacity
  have hg:max Lgoal Mparent≤2*max Lgoal Mparent+r/4:=by linarith
  have hu1:inp.X₁≤Z^(2*max Lgoal Mparent+r/4):=
    hu.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hu2:inp.X₂≤Z^(2*max Lgoal Mparent+r/4):=
    hu.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hp:=lower_product_admission M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ N hN
  have hlowV:Real.logb Z (volume inp)≤5*state.width/6:=
    (low_admission M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ hZ hlow).2
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height (mesh Mglobal B κ ε)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hσlo hσhi hheight hfreq
    inp hm (fun _=>le_rfl) (fun _=>le_rfl) (fun _=>rfl) (fun _=>rfl) hN le_rfl (le_max_right _ _)
    hb hb (le_max_right _ _) (le_max_right _ _) hp.2.2 state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p rfl rfl
    hu1 hu2 hu.2.2.2.2.2.2.1 hu.2.2.2.2.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B ε k)
    hrpos.le (hstate.trans hMA) hcapacity hwidth hwidth (by linarith only [hstate,hdrop])
    hclip le_rfl hlowV (hfit.2 k εchild hell)
  have hcost:state.width+columnLoss Mglobal B ε k+r/4=state.width+physicalLoss Mglobal B ε k:=by
    rw [add_assoc]
    exact congrArg (state.width+·) (columnLoss_physical Mglobal B ε k)
  rw [hcost] at hh
  have ht:inp.t=t:=rfl
  have hv0:volume inp = volume (sourceInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂):=rfl
  rw [ht,hv0] at hh
  simpa only [map_one,Nat.cast_one,div_one,mul_assoc] using hh

end SevenEighths.CenteredMomentEnergyNaturalLowPhysical

end

end OAI

end Source2154

/- Original source: OAI/NumberTheory/DirichletL/Energy/BandMonotonicity.lean; sha256: 15102fee699c6a156a62a86e7480d4afdc67153fc0c613964aa7f68e1b793465 -/
section Source2155
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBandMonotonicity
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

def widenState {Z B b B' b':ℝ}(s:NaturalState Z B b)(hB:B≤B')(hb:b≤b'):
    NaturalState Z B' b':=
  {s with
    puncture_bound:=s.puncture_bound.trans (Real.rpow_le_rpow_of_exponent_le s.base_ge_one hB)
    radial_support:=fun _x hx=>le_trans (s.radial_support hx) hb}

def widenProfiles {a b a' b':ℝ}(p:Profiles a b)(ha:a'≤a)(hb:b≤b'):Profiles a' b' where
  profile:=p.profile
  support:=fun i _x hx=>⟨ha.trans (p.support i hx).1,(p.support i hx).2.trans hb⟩

lemma widenState_width {Z B b B' b':ℝ}(s:NaturalState Z B b)(hB:B≤B')(hb:b≤b'):
    (widenState s hB hb).width=s.width:=rfl

lemma widenProfiles_control {a b a' b':ℝ}(p:Profiles a b)(ha:a'≤a)(hb:b≤b')
    (S:Finset (ℕ×ℕ)):(widenProfiles p ha hb).control S=p.control S:=rfl

lemma profile_control_mono {a b:ℝ}(p:Profiles a b){S T:Finset (ℕ×ℕ)}(hst:S⊆T):
    p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem zeroAt_transport (Q:Ideal O)(a b radial mask L Mcap eps Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤radial)(hm:mask'≤mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:ZeroAt Q a b radial mask L Mcap eps Z J S C):
    ZeroAt Q a' b' radial' mask' L' Mcap' eps' Z J' T C':=by
  intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    t X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap)
  change s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+‖t‖)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+‖t‖)^J≤(1+‖t‖)^J':=pow_le_pow_right₀ (by linarith [norm_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem positiveAt_transport (W:ℝ→ℂ)(bslot a b radial mask L Lslot lo hi Mcap eps κ Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (η₀:Character)(Q:Ideal O)(J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤radial)(hm:mask'≤mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:PositiveAt (α:=α) M H hH W bslot a b radial mask L Lslot lo hi Mcap eps κ Z η₀ Q J S C):
    PositiveAt (α:=α) M H hH W bslot a' b' radial' mask' L' Lslot lo hi Mcap' eps' κ Z η₀ Q J' T C':=by
  intro A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hcapacity
  change _≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+|t|+height)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+|t|+height)^J≤(1+|t|+height)^J':=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyBandMonotonicity

end

end OAI

end Source2155

/- Original source: OAI/NumberTheory/DirichletL/Energy/PositiveLowSourceControlled.lean; sha256: bc65de7ba401370cea07bbbe32a70c2770511de7b64d97c7bd2fe97e47ca8ce0 -/
section Source2156
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveLowSourceControlled
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyPositiveLowBandSource (PhysicalLowAt)
open CenteredMomentEnergyBandMonotonicity

theorem actual_low_stages_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hMcap:0≤Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧∃Cfixed:ℝ,0<Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Lslot rho κ e:ℝ)(η₀:Character)(Q:Ideal O)(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical Cprevious:ℝ),
      1/6≤κ→0≤Cphysical→0≤Cprevious→εdiag≤e→-saving≤e→
      PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
        J S Cprevious→
      PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cphysical→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1)+Cprevious) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap e Z J (insert (0,0) S)
        (Cfixed*(Cphysical+1)+Cprevious) :=by
  obtain ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,hbound⟩:=
    CenteredMomentEnergyPositiveLowBandSource.actual_low_stages_from_physical (α:=α) M H hH
      W hW aslot bslot lo hi a b bΦ Mcap εdiag ξ saving haslot hWs hbslot ha hb hbΦ
      hMcap hεdiag hξ
  refine ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask L Lslot rho κ e η₀ Q S J Cphysical Cprevious hκ hCphysical hCprevious he hsave hold hmass
  let Cm:=Cphysical+Cprevious/Cfixed
  have hdiv:0≤Cprevious/Cfixed:=div_nonneg hCprevious hCfixed.le
  have hCm:0≤Cm:=by dsimp [Cm];positivity
  have hcc:Cphysical≤Cm:=by dsimp [Cm];linarith
  have heq:Cfixed*(Cm+1)=Cfixed*(Cphysical+1)+Cprevious:=by
    dsimp [Cm]
    field_simp
    ; ring
  have hprev:Cprevious≤Cfixed*(Cm+1):=by
    rw [heq]
    have hh:0≤Cfixed*(Cphysical+1):=by positivity
    linarith
  have hold':PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
      J (insert (0,0) S) (Cfixed*(Cm+1)):=
    positiveAt_transport (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z
      a b bΦ Bmask L rho e η₀ Q J J S (insert (0,0) S) Cprevious (Cfixed*(Cm+1)) hZ.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.subset_insert _ _)
      hCprevious hprev hold
  have hmass':PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
      a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cm:=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hlo hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hh:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hlo hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hz:0≤Z:=zero_le_one.trans hZ.1.le
    apply hh.trans
    gcongr
  have hh:=hZ.2 Bmask L Lslot rho κ e η₀ Q S J Cm hκ hCm he hsave hold' hmass'
  simpa only [heq] using hh

end SevenEighths.CenteredMomentEnergyPositiveLowSourceControlled

end

end OAI

end Source2156

/- Original source: OAI/NumberTheory/DirichletL/Energy/StageReserveBounded.lean; sha256: b5ad381c8e1db808fc48de34dab0eef968a3eca9426b0ace5fd407ebfa36be95 -/
section Source2157
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyStageReserve

theorem exists_bounded_separated_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0<rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*(
        Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤
        C*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,hledger⟩:=
    exists_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hB
  refine ⟨d,xi,saving,Mcap+Bmask+xi,C,hd,hxi,hs,hC,hxr,le_refl _,by linarith,?_⟩
  intro e he Z hZ s hwidth α _ w hw
  apply le_trans _ (hledger e he Z hZ s hwidth α w hw)
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hLp:0≤Mcap+Bmask+xi:=by linarith
  gcongr

end SevenEighths.CenteredMomentEnergyStageReserveBounded

end

end OAI

end Source2157

/- Original source: OAI/NumberTheory/DirichletL/Energy/OriginalHighReflectionBounded.lean; sha256: e8667278d9355dae0f7f372d86bfd478f04ac0f6d2aca0ab3c27dfd72744f75e -/
section Source2158
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_high_power
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤e → 0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      length Z X₁≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hLupper,hscalar⟩:=
    exists_bounded_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_high_from_low (α:=α) M H hH d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi hBmask hL 2 (by norm_num) degree S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong degree n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hxiM:xi≤s.width/14:=by linarith
  have hh:=hZ.2 Lslot e κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hsumcap:(∑i,w i)≤Mcap:=by
    have hlen₁:=length_nonneg Z X₁ hZ.1
    have hlen₂:=length_nonneg Z X₂ hZ.1
    have hk:=mul_le_mul_of_nonneg_right (show (1:ℝ)≤6*κ by linarith) hsum
    nlinarith
  have hledger:=hscalar e he Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤A:=by dsimp only [A];positivity
  have hE:0≤E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤E:=
      mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left hdiag (le_add_of_nonneg_left hK)) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤L:=by linarith
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
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

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionBounded

end

end OAI

end Source2158

/- Original source: OAI/NumberTheory/DirichletL/Energy/OriginalHighReflectionSymmetricBounded.lean; sha256: 7007d81a940fd698e9405a203c4b855aa25de4ad2d4c4281758d8257ecdc6f93 -/
section Source2159
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionBounded
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyOriginalHighReflectionSymmetric

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_unbalanced_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0<rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤e → 0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤s.width → s.width≤Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      min (length Z X₁) (length Z X₂)≤s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=original_high_power (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  rcases min_le_iff.mp hshort with hshort|hshort
  · exact hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · rw [energy_swap]
    have hh:=hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₂ W₁ hs₂ hs₁ X₂ X₁ hX₂ hX₁ hshort (by linarith) (by linarith)
    simpa only [mul_comm (sourceControl U W₂) (sourceControl U W₁)] using hh

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBounded

end

end OAI

end Source2159
