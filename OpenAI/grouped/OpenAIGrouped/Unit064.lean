import OpenAIGrouped.Unit063
import OpenAIGrouped.Unit062
import OpenAIGrouped.Unit061
import OpenAIGrouped.Unit060
import OpenAIGrouped.Unit059

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Descent/WholePriorityEnergy.lean; sha256: 974798fec22a52890e3e7005e858d913dd2103468b21a6856552c4a3b64167de -/
section Source2560
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem whole_priority_retained_fixed_ray
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (firstCommon firstDivisor:Finset ι)
    (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector:Finset ι→ℂ)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
    (_hcube:cube.Admissible) (_hcommon:Disjoint firstCommon cube.support)
    (_hdivisor:firstDivisor⊆firstCommon∪cube.support)
    (_hold:∀D∈pool.powerset,selector D≠0 → ∀i,(old i).val∣
      sourceIdeal p cube.support*sourceIdeal p firstCommon*sourceIdeal p D)
    (_hextra:extra cube⊆cube.support),
    let source:=unifiedSource p pool
      (activeParents p extra pool cube firstCommon firstDivisor old selector negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀(z:SecondRayIndex)
        (Y R L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀D∈pool.powerset,‖selector D‖≤1) →
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y:ℂ)*secondRayCoefficient z *
        ∑x∈source,sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,Cbin,hC,hCbin,he⟩:=
    actual_priority_retained_bound (ι:=ι) (σ:=σ) om rowMajorant lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,coefficientBound*C,Cbin,mul_nonneg coefficientBound_pos.le hC,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool cube firstCommon firstDivisor old selector
    Ψ m ray core slots assigned lists a cutoff hcube hcommon hdivisor hold hextra source Ψ₀ z
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
    hselector haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hsource:ActualSecondSourceConditions p source:=
    active_conditions p hp extra pool cube firstCommon firstDivisor old selector hcube hcommon hdivisor
      hold hextra negative assigned lists cutoff
  have hd:∀x∈source,∀i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient:=
    active_deleted_support p hinj extra pool cube firstCommon firstDivisor old selector hcube hcommon
      hdivisor hold hextra negative assigned lists cutoff
  have hw:∀x∈source,‖normalizedWeight p hg cube negative Ψ m selector ray core assigned a x‖≤1:=
    fun x hx=>normalizedWeight_norm p hg hinj extra pool cube firstCommon firstDivisor old selector
      negative Ψ m ray core assigned lists a haassigned hselector (fun D hD hD0=>hΨ _) cutoff x hx
  have hΨ₀:∀n,‖Ψ₀ n‖≤1:=fun n=>(firstCoreTwist_norm_le negative (if negative then ray.1 else ray.2)
    Ψ core n).trans (hΨ n)
  have he₀:=he p hp hcop hg hpr hinj hc source hsource pool Ψ₀ m z (slots\assigned) (slots\assigned)
    lists lists a a (InverseMomentWholeRetainedSource.deleted p extra negative)
    (InverseMomentWholeRetainedSource.deleted p extra negative)
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t
    (normalizedWeight p hg cube negative Ψ m selector ray core assigned a) labels A
    hd hd hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ₀ hw
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hrow:∀x:MarkedSecondSource ι (Jo+(assigned.card+assigned.card)) 0,wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
      (principalWindow om lo hi hlo hsupport negative t) X Y z x=
      actualSecondSignedWeight p hp hcop hg Ψ₀ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ₀ m z)
        (slots\assigned) (slots\assigned)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x) a a
        (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t)
        rowMajorant Y X:=fun x=>wholeRow_eq p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a _ X Y z x
  rw [source_sum_normalized p hg cube negative Ψ m selector ray core assigned a source]
  rw [show (Y:ℂ)*secondRayCoefficient z*((coefficientBound:ℂ)*
      ∑x∈source,normalizedWeight p hg cube negative Ψ m selector ray core assigned a x*
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x)=
      (coefficientBound:ℂ)*((Y:ℂ)*secondRayCoefficient z*
        ∑x∈source,normalizedWeight p hg cube negative Ψ m selector ray core assigned a x*
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x) by ring]
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  simp_rw [hrow,←mul_assoc]
  convert mul_le_mul_of_nonneg_left he₀ coefficientBound_pos.le using 1 <;> ring_nf

end SevenEighths.InverseMoment

end

end OAI

end Source2560

/- Original source: OAI/NumberTheory/DirichletL/Descent/WholePriorityRays.lean; sha256: 5019441e1caaa25beeb5e23debc4e30f02a45cac90c0102602b89cfab0e0bb5c -/
section Source2561
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem whole_priority_retained_all_rays
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (firstCommon firstDivisor:Finset ι)
    (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (selector:Finset ι→ℂ)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
    (_hcube:cube.Admissible) (_hcommon:Disjoint firstCommon cube.support)
    (_hdivisor:firstDivisor⊆firstCommon∪cube.support)
    (_hold:∀D∈pool.powerset,selector D≠0 → ∀i,(old i).val∣
      sourceIdeal p cube.support*sourceIdeal p firstCommon*sourceIdeal p D)
    (_hextra:extra cube⊆cube.support),
    let source:=unifiedSource p pool
      (activeParents p extra pool cube firstCommon firstDivisor old selector negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀
        (Y R L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀D∈pool.powerset,‖selector D‖≤1) →
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
        ∑x∈source,sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,Cbin,hC,hCbin,he⟩:=
    whole_priority_retained_fixed_ray (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C*(512*32^2),Cbin,by positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool cube firstCommon firstDivisor old selector
    Ψ m ray core slots assigned lists a cutoff hcube hcommon hdivisor hold hextra source Ψ₀
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
    hselector haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:= (1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*(1+Cbin*Real.log Z)^4*
    Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  let S:SecondRayIndex→ℂ:=fun z=>(Y:ℂ)*secondRayCoefficient z *
      ∑x∈source,sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x
  have hP:0≤P:=by dsimp [P];positivity
  have hH:0≤H:=by dsimp [H];positivity
  have hz (z:SecondRayIndex):P*‖S z‖≤C*A*H*‖secondRayCoefficient z‖:=by
    have h:=he p hp hcop hg hpr hinj hc extra pool cube firstCommon firstDivisor old selector
      Ψ m ray core slots assigned lists a cutoff hcube hcommon hdivisor hold hextra z
      Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
      hselector haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass
      (hleft z) (hright z)
    convert h using 1 ; dsimp only [P,S,H] ; ring
  calc
    _≤P*∑z:SecondRayIndex,‖S z‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) hP
    _=∑z:SecondRayIndex,P*‖S z‖:=Finset.mul_sum _ _ _
    _≤∑z:SecondRayIndex,C*A*H*‖secondRayCoefficient z‖:=Finset.sum_le_sum (fun z _=>hz z)
    _=C*A*H*(∑z:SecondRayIndex,‖secondRayCoefficient z‖):=(Finset.mul_sum _ _ _).symm
    _≤C*A*H*(512*32^2):=mul_le_mul_of_nonneg_left secondRayCoefficient_mass (by positivity)
    _= _:=by dsimp [H];ring

end SevenEighths.InverseMoment

end

end OAI

end Source2561

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondVariablePrincipal.lean; sha256: e92944d9511da28ae4e461bbf274de523f9fa8683123278a1489fb4c9e90ea5c -/
section Source2562
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge
open SecondPassIntegration CompletedHeight InversePrincipalEnergy RayFourExpansion
open InverseSecondPrincipalCaller
local notation "Eis" => ActualEisensteinCubic.O

theorem first_retained_radius_one {ι : Type*} [DecidableEq ι]
    (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (labels : Finset (Ideal Eis)) (b : CubeCoordinates ι) (Y : ℝ)
    (hlabels : ∀ f∈labels,f≠0) (hne : (firstRetainedSource p labels b Y).Nonempty) : 1≤Y := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨hf,hk⟩ := (mem_firstRetainedSource p labels b Y x).mp hx
  have hm : firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1≠0 := by
    unfold firstPhysicalMultiplier
    exact mul_ne_zero (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero _ (hlabels _ hf)))
      (primeProduct_ne_zero p hp _ _)
  by_contra hy
  rw [nonzeroChildFrequencyBall_empty _ hm Y (lt_of_not_ge hy)] at hk
  exact Finset.notMem_empty _ hk

theorem firstCore_variable_principal_energy (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      ∀ (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      (∀ i∈slots,Disjoint (lists i) D) →
      ∀ (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m c d : Eis),d≠0 → ∀ (r : FirstCoreIndex)
      (om W : 𝓢(ℝ,ℂ)) (a b : ℝ) (_ha : 0<a) (_hs : Function.support om⊆Set.Icc a b)
      (M t X Y : ℝ) (R : Finset ι→Finset ι→ℝ),b≤Real.exp M → 0<X → 1≤Y → (∀ G E,0≤R G E) →
      let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p B v ε₁ ε₂
      ‖truncatedSecondZero p hg F Ψ₀ m₀ c₀ d H W Y (fun G E=>secondPhysicalCutoff p d (R G E) G E)‖ +
      ‖principalRestoration p hg hinj hp F Ψ₀ m₀ c₀ d H W Y (fun G E=>secondPhysicalMask p d (R G E) G E)‖ ≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Y*(X*Real.exp M)^(1+ε) := by
  obtain ⟨s,C,hC,hbound⟩ := marked_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists coeff hslots hcoeff F D B v ε₁ ε₂ hD
    negative χ Ψ hΨ m c d hd r om W a b ha hs M t X Y R hb hX hY hR H Ψ₀ m₀ c₀
  let V := principalWindow om a b ha hs negative t
  let H₀ := markedRadial p slots lists coeff ∅ V X
  have he (U : Finset ι) : secondInputCoefficient p hg Ψ₀ m₀ c₀ d H U=
      secondInputCoefficient p hg Ψ₀ m₀ c₀ d H₀ U :=
    firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX Ψ₀
      (m*b0Label p B v ε₁ ε₂) c₀ d
  rw [zero_congr_input p hg F Ψ₀ m₀ c₀ d H H₀ he,
    restoration_congr_input p hp hg hinj F Ψ₀ m₀ c₀ d H H₀ he]
  have hz : ∀ G∈F.powerset,∀ E∈G.powerset,(0:Eis)∈secondPhysicalCutoff p d (R G E) G E := by
    intro G hG E hE
    exact zero_mem_childFrequencyBall _ (mul_ne_zero hd (primeSubsetGenerator_ne_zero _ _)) _ (hR G E)
  have hbnd := hbound p hp hg hinj hcop slots lists coeff hslots hcoeff ∅ F Ψ₀
    (fun z=>(firstCoreTwist_norm_le negative χ Ψ r z).trans (hΨ z)) m₀ c₀ d V W X M Y
    hX hY (principalWindow_upper om a b ha hs M hb negative t)
    (fun G E=>secondPhysicalCutoff p d (R G E) G E) hz
    (fun G E=>secondPhysicalMask p d (R G E) G E)
    (fun G _ E k=>secondPhysicalMask_norm_le_one p d (R G E.val) G E.val k.val)
  simpa only [H₀,V,Finset.card_empty,pow_zero,mul_one,principalWindow_seminorm_zero] using hbnd

end SevenEighths.InverseMoment

end

end OAI

end Source2562

/- Original source: OAI/NumberTheory/DirichletL/Descent/WholePriorityPrincipal.lean; sha256: 985c1cd4d0d9cfb85e7f449f7ff2c712349927dde47ee416ef8f9df8ed3b8aae -/
section Source2563
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrincipalEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def wholePriorityPrincipalEnergy
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (pool:Finset ι) (b:CubeCoordinates ι) (C extra:Finset ι) (negative:Bool)
    (Ψ:O→*ℂ) (m d:O) (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (selector:Finset ι→ℂ) (om W:𝓢(ℝ,ℂ)) (X t Y:ℝ)
    (R:Finset ι→Finset ι→Finset ι→ℝ) : ℝ :=
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖*
      ∑J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2*
        (let H:=firstCoreTest (primeMark (slots\J) (fun i=>lists i\(A∪D)) a)
          (fun u=>om (Real.exp u)) (columnLog p (primeProductNorm p D*X)) negative (-t) D
         let Ψ₀:=firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
         let m₀:=(m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
           b.leftBit b.rightBit)*∏i∈D,p i
         let c₀:=(∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
           b.leftBit b.rightBit
         ‖truncatedSecondZero p hg pool Ψ₀ m₀ c₀ d H W Y
           (fun G E=>secondPhysicalCutoff p d (R D G E) G E)‖+
         ‖principalRestoration p hg hinj hp pool Ψ₀ m₀ c₀ d H W Y
           (fun G E=>secondPhysicalMask p d (R D G E) G E)‖)

theorem whole_priority_principal_bound (ε:ℝ) (hε:0<ε) :
    ∃ (s:Finset (ℕ×ℕ)) (Cp:ℝ),0<Cp ∧
    ∀ {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (pool:Finset ι) (b:CubeCoordinates ι) (C extra:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m d:O) (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (selector:Finset ι→ℂ) (om W:𝓢(ℝ,ℂ)) (lo hi:ℝ)
      (_hlo:0<lo) (_hs:Function.support om⊆Set.Icc lo hi)
      (M t X Y:ℝ) (R:Finset ι→Finset ι→Finset ι→ℝ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → d≠0 → hi≤Real.exp M → 0<X → 1≤Y → (∀D G E,0≤R D G E) →
      wholePriorityPrincipalEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a selector om W X t Y R ≤
        Cp*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
          Y*(X*Real.exp M)^(1+ε)*
          (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p
            ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D))^(2*ε)) := by
  obtain ⟨s,Cp,hCp,hprinc⟩ := firstCore_variable_principal_energy ε hε
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power ε hε
  refine ⟨s,((32*512:ℝ)^2*512)*Cp*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop pool b C extra negative Ψ m d slots lists a selector om W lo hi hlo hs
    M t X Y R hslots ha hΨ hd hhi hX hY hR
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  let P:=Cp*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*Y*(X*Real.exp M)^(1+ε)
  have hP:0≤P:=by dsimp [P];positivity
  have hm (J:Finset σ) (hJ:J∈slots.powerset) (D:Finset ι) :
      ‖primeMark J lists a (A∪D)‖^2≤Cm^2*(primeProductNorm p (A∪D))^(2*ε) := by
    have hj:=Finset.mem_powerset.mp hJ
    have hh:=hmark p hp hcop J lists a (fun i hi j hj' hij=>hslots (hj hi) (hj hj') hij) (fun i hi=>ha i (hj hi)) (A∪D)
    have he:((primeProductNorm p (A∪D))^ε)^2=(primeProductNorm p (A∪D))^(2*ε):=by
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      congr 1;ring
    calc
      _≤(Cm*(primeProductNorm p (A∪D))^ε)^2:=pow_le_pow_left₀ (norm_nonneg _) hh 2
      _= _:=by rw [mul_pow,he]
  have hn (D:Finset ι) : 0≤primeProductNorm p (A∪D):=(primeProductNorm_pos p hp _).le
  unfold wholePriorityPrincipalEnergy
  dsimp only
  have hinner (r:RayCharacter×RayCharacter) (D:Finset ι) (core:FirstCoreIndex) (J:Finset σ)
      (hJ:J∈slots.powerset) := hprinc p hp hg hinj hcop (slots\J) (fun i=>lists i\(A∪D)) a
    (residual_lists_pairwise slots J lists A D hslots) (residual_coeff_bound slots J lists a A D ha)
    pool D b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
    (fun i _=>residual_lists_avoid lists A D i) negative (if negative then r.1 else r.2) Ψ hΨ
    m (∏i∈C,p i) d hd core om W lo hi hlo hs M t X Y (R D) hhi hX hY (hR D)
  change _≤_
  calc
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
        ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative Ψ m D core‖*
        ((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*P)) := by
      gcongr with r hr D hD core hc
      calc
        _≤∑J∈slots.powerset,Cm^2*(primeProductNorm p (A∪D))^(2*ε)*P := by
          apply Finset.sum_le_sum
          intro J hJ
          exact mul_le_mul (hm J hJ D) (hinner r D core J hJ) (by positivity) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _))
        _= _:=by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*
        ((32*512)*((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*P))) := by
      gcongr with r hr D hD
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (firstCoreOuter_mass p hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D (hΨ _)) (mul_nonneg (pow_nonneg (by norm_num) _)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _)) hP))
    _= ((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*P*
      (∑r:RayCharacter×RayCharacter,‖crossCoeff r.1 r.2‖)*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm (s:=pool.powerset)]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring
    _≤ ((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*P*512*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · simpa only [Fintype.sum_prod_type] using crossCoeff_sum_norm_le
        · positivity
      · exact Finset.sum_nonneg (fun D hD=>mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hn D) _))
    _= _ := by
      have he:((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card:=by rw [←pow_mul,pow_mul'];norm_num
      rw [he]
      dsimp only [P,A]
      ring

end SevenEighths.InverseMoment

end

end OAI

end Source2563

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondTailCost.lean; sha256: 68afe817a4d09a212df9f4746c01b7e51e630765a3e547fbed37bf116f709f65 -/
section Source2564
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in
theorem residualPairWeight_bounded_test
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O)
    (Hcol : Finset ι → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (G S T : Finset ι) :
    ‖residualPairWeight p hg Ψ Ψ m c d
      (fun U => Hcol (G ∪ U)) (fun U => Hcol (G ∪ U)) S T‖ ≤ B^2 := by
  simp only [residualPairWeight, norm_mul, norm_star, sourceSupportMobius_norm p hinj, one_mul]
  have hS := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (fun U => Hcol (G ∪ U)) S).trans (hcol _)
  have hT := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (fun U => Hcol (G ∪ U)) T).trans (hcol _)
  simpa only [pow_two] using mul_le_mul hS hT (norm_nonneg _) hB

include hp hinj
theorem residualTailCost_bounded_test
    (F G E : Finset ι) (hEG : E ⊆ G) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (Hcol : Finset ι → ℂ) (B Y H lengthScale P : ℝ) (A : ℕ)
    (hB : 0 ≤ B) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (hsupport : ∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) :
    residualTailCost p hg F G Ψ Ψ m c d
      (fun S => Hcol (G∪S))
      (fun S => Hcol (G∪S))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P ≤
      if primeProductNorm p G ≤ lengthScale then
        (128*lengthScale)^2 * (B^2 *
          (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) else 0 := by
  let C := B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let w := residualPairWeight p hg Ψ Ψ m c d
    (fun S => Hcol (G∪S))
    (fun S => Hcol (G∪S))
  have hsupp (S T : Finset ι) (hw : w S T ≠ 0) :
      primeProductNorm p G ≤ lengthScale ∧ primeProductNorm p E ≤ lengthScale ∧
      primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale := by
    obtain ⟨hS,hT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
    have hGS := hsupport (G ∪ S) hS
    have hGT := hsupport (G ∪ T) hT
    have hG := (primeProductNorm_mono p hp Finset.subset_union_left).trans hGS
    exact ⟨hG, (primeProductNorm_mono p hp hEG).trans hG,
      (primeProductNorm_mono p hp Finset.subset_union_right).trans hGS,
      (primeProductNorm_mono p hp Finset.subset_union_right).trans hGT⟩
  by_cases hG : primeProductNorm p G ≤ lengthScale
  · rw [ite_eq_left hG]
    calc
      _ ≤ ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset,
          if primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale then C else 0 := by
        unfold residualTailCost
        apply Finset.sum_le_sum
        intro S hS
        apply Finset.sum_le_sum
        intro T hT
        by_cases hd : Disjoint S T
        · rw [ite_eq_left hd]
          dsimp only
          by_cases hw : w S T = 0
          · change ‖w S T‖ * _ ≤ _
            rw [hw, norm_zero, zero_mul]
            split_ifs <;> positivity
          · obtain ⟨_,hE,hSn,hTn⟩ := hsupp S T hw
            rw [ite_eq_left ⟨hSn,hTn⟩]
            have hn2 : ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 =
                primeProductNorm p S * primeProductNorm p T := active_norm_sq_disjoint p S T hd
            have hn : 1 ≤ ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖ := by
              have hpS := primeProductNorm_ge_one p hp S
              have hpT := primeProductNorm_ge_one p hp T
              have hpST : 1 ≤ primeProductNorm p S * primeProductNorm p T := one_le_mul_of_one_le_of_one_le hpS hpT
              rw [← hn2] at hpST
              nlinarith [norm_nonneg (eisEmbedding (∏ i : activeSupport T S, p i.val))]
            have hNe : 0 < ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 :=
              SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _)
            have hden : ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
                ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 ≤ lengthScale^3 := by
              rw [primeSubsetGenerator_norm_eq_productNorm, hn2]
              have hST := mul_le_mul hSn hTn (FirstPassCubeLabels.primeProductNorm_pos p hp T).le
                (zero_le_one.trans hL)
              have hEST := mul_le_mul hE hST
                (mul_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
                  (FirstPassCubeLabels.primeProductNorm_pos p hp T).le) (zero_le_one.trans hL)
              nlinarith
            have hscalar := tail_radial_scalar_le Y
              (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2)
              (‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖) lengthScale H P A hY hNe hn hL hden hH hP
            exact mul_le_mul (residualPairWeight_bounded_test p hg hinj Ψ hΨ m c d Hcol B hB hcol G S T)
              hscalar (by positivity) (sq_nonneg _)
        · rw [ite_eq_right hd]
          split_ifs <;> positivity
      _ = ((boundedPrimeSupports p (F\G) lengthScale).card : ℝ)^2 * C :=
        sum_pair_indicator (F\G).powerset (fun S => primeProductNorm p S ≤ lengthScale) C
      _ ≤ (128*lengthScale)^2 * C := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (boundedPrimeSupports_card p hinj (F\G) lengthScale hL) 2) hC
  · rw [ite_eq_right hG]
    have hz : residualTailCost p hg F G Ψ Ψ m c d
        (fun S => Hcol (G∪S))
        (fun S => Hcol (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P = 0 := by
      unfold residualTailCost
      apply Finset.sum_eq_zero
      intro S hS
      apply Finset.sum_eq_zero
      intro T hT
      by_cases hd : Disjoint S T
      · rw [ite_eq_left hd]
        have hw : w S T = 0 := by
          by_contra hw
          exact hG (hsupp S T hw).1
        change ‖w S T‖ * _ = 0
        rw [hw, norm_zero, zero_mul]
      · rw [ite_eq_right hd]
    exact hz.le

theorem secondSourceTailCost_bounded_test
    (F : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (Hcol : Finset ι → ℂ) (B Y H lengthScale P : ℝ) (A : ℕ)
    (hB : 0 ≤ B) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (hsupport : ∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) :
    (∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
      residualTailCost p hg F G Ψ Ψ m c d
        (fun S => Hcol (G∪S))
        (fun S => Hcol (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A P) ≤
      (128*lengthScale)^4 * (B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) := by
  let C := B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have h128 : 0 ≤ 128*lengthScale := by positivity
  calc
    _ ≤ ∑ G ∈ F.powerset, if primeProductNorm p G ≤ lengthScale then (128*lengthScale)^3*C else 0 := by
      apply Finset.sum_le_sum
      intro G hG
      by_cases hGn : primeProductNorm p G ≤ lengthScale
      · rw [ite_eq_left hGn]
        have heq : boundedPrimeSupports p G lengthScale = G.powerset := by
          apply Finset.filter_eq_self.mpr
          intro E hE
          exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hE)).trans hGn
        have hcard : (G.powerset.card : ℝ) ≤ 128*lengthScale := by
          simpa only [heq] using boundedPrimeSupports_card p hinj G lengthScale hL
        calc
          _ ≤ ∑ E : G.powerset, (128*lengthScale)^2*C := by
            apply Finset.sum_le_sum
            intro E hE
            have hr := residualTailCost_bounded_test p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
              Ψ hΨ m c d Hcol B Y H lengthScale P A hB hY hH hP hL hcol hsupport
            rw [ite_eq_left hGn] at hr
            have hc := secondSourceCommonCoefficient_norm_le_one p hp hg hinj Ψ hΨ m c d G E.val
            exact (mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans
              (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg _) hC))
          _ = (G.powerset.card : ℝ)*((128*lengthScale)^2*C) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
          _ ≤ (128*lengthScale)*((128*lengthScale)^2*C) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (sq_nonneg _) hC)
          _ = _ := by ring
      · rw [ite_eq_right hGn]
        apply Finset.sum_nonpos
        intro E hE
        have hr := residualTailCost_bounded_test p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
          Ψ hΨ m c d Hcol B Y H lengthScale P A hB hY hH hP hL hcol hsupport
        rw [ite_eq_right hGn] at hr
        exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hr
    _ = ((boundedPrimeSupports p F lengthScale).card : ℝ)*((128*lengthScale)^3*C) := by
      rw [← Finset.sum_filter]
      simp only [boundedPrimeSupports, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (128*lengthScale)*((128*lengthScale)^3*C) :=
      mul_le_mul_of_nonneg_right (boundedPrimeSupports_card p hinj F lengthScale hL)
        (mul_nonneg (pow_nonneg h128 _) hC)
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI

end Source2564

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondWholeTail.lean; sha256: 23ca2cae2d42ece345eaa6f18d39d4e3ff1192b7508424e93e0a7e15f99206a5 -/
section Source2565
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_second_supported_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H lengthScale : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ lengthScale →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
        (128*lengthScale)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+lengthScale^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_uniform_secondSourceTail_bound order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Hcol W B Y H lengthScale hB hY hH hL hcol hsupp K hK
  exact (htail p hp hg hinj hc F Ψ m c d Hcol W Y H hY hH K hK).trans
    (secondSourceTailCost_bounded_test p hp hg hinj F Ψ hΨ m c d Hcol B Y H lengthScale
      (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) order hB hY hH (by positivity) hL hcol hsupp)

def supportedSecondRadius (d : O) (lengthScale Y H : ℝ) : ℝ :=
  childOuterRadius Y (‖eisEmbedding d‖^2 * lengthScale) lengthScale lengthScale lengthScale H

lemma supportedSecondRadius_eq (d : O) (lengthScale Y H : ℝ) :
    supportedSecondRadius d lengthScale Y H = ‖eisEmbedding d‖^2 * lengthScale^4 * H / Y := by
  unfold supportedSecondRadius childOuterRadius
  ring

theorem full_second_child_supported_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H lengthScale R : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ lengthScale →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) →
      supportedSecondRadius d lengthScale Y H ≤ R →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun _ E => childFrequencyBall
          (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) R)‖ ≤
        (128*lengthScale)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+lengthScale^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_supported_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H lengthScale R hB hY hH hL hcol hsupp hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d Hcol W B Y H lengthScale hB hY hH hL hcol hsupp
  intro G hG E S hS T hT hST hw k hk
  obtain ⟨hGS,hGT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hGS' := hsupp (G ∪ S) hGS
  have hGT' := hsupp (G ∪ T) hGT
  have hGn := (primeProductNorm_mono p hp Finset.subset_union_left).trans hGS'
  have hEn := (primeProductNorm_mono p hp (Finset.mem_powerset.mp E.property)).trans hGn
  have hSn := (primeProductNorm_mono p hp Finset.subset_union_right).trans hGS'
  have hTn := (primeProductNorm_mono p hp Finset.subset_union_right).trans hGT'
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E.val
  have he : e ≠ 0 := primeSubsetGenerator_ne_zero _ _
  have hde : d*e ≠ 0 := mul_ne_zero hd he
  have hdN : 0 < ‖eisEmbedding d‖^2 := SecondPassIntegration.elementNorm_pos d hd
  have hL0 : 0 < lengthScale := lt_of_lt_of_le zero_lt_one hL
  have heN : ‖eisEmbedding e‖^2 ≤ lengthScale := by
    simpa only [e,primeSubsetGenerator_norm_eq_productNorm] using hEn
  have hdeN : ‖eisEmbedding (d*e)‖^2 ≤ ‖eisEmbedding d‖^2 * lengthScale := by
    simp only [map_mul,norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_left heN (sq_nonneg _)
  apply childFrequencyBall_raw_tail p hp Y (‖eisEmbedding d‖^2*lengthScale)
    lengthScale lengthScale lengthScale H hY (mul_pos hdN hL0) hL0 hL0 hL0 hH
    (d*e) e hde he hdeN heN S T hST hSn hTn k
  intro hsmall
  apply hk
  apply (mem_childFrequencyBall (d*e) hde R k).mpr
  exact ((mem_childFrequencyBall (d*e) hde _ k).mp hsmall).trans hR

end
end SevenEighths.InverseMoment

end OAI

end Source2565

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondWholeCutoff.lean; sha256: f8ac8aa6d25d5616afdb40706fbb6a668329f3726423d921ec9ec7241133a02d -/
section Source2566
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_whole_column_denominator {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal] (G E S T : Finset ι)
    (hEG : E ⊆ G) (hGS : Disjoint G S) (hGT : Disjoint G T)
    (L : ℝ) (hL : 0 ≤ L)
    (hS : primeProductNorm p (G ∪ S) ≤ L)
    (hT : primeProductNorm p (G ∪ T) ≤ L) :
    (primeProductNorm p E)^2 * (primeProductNorm p S * primeProductNorm p T) ≤ L^2 := by
  have hE := primeProductNorm_mono p hp hEG
  have hE0 := (primeProductNorm_pos p hp E).le
  have hS0 := (primeProductNorm_pos p hp S).le
  have hT0 := (primeProductNorm_pos p hp T).le
  rw [primeProductNorm_union p G S hGS] at hS
  rw [primeProductNorm_union p G T hGT] at hT
  calc
    _ ≤ (primeProductNorm p G)^2 * (primeProductNorm p S * primeProductNorm p T) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hE0 hE 2) (mul_nonneg hS0 hT0)
    _ = (primeProductNorm p G * primeProductNorm p S) *
      (primeProductNorm p G * primeProductNorm p T) := by ring
    _ ≤ L*L := mul_le_mul hS hT (mul_nonneg (primeProductNorm_pos p hp G).le hT0) hL
    _ = _ := by ring

def wholeSecondRadius (d : O) (L Y H : ℝ) : ℝ := ‖eisEmbedding d‖^2 * L^2 * H / Y

theorem full_second_whole_column_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H L R : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ L →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ L) →
      wholeSecondRadius d L Y H ≤ R →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun _ E => childFrequencyBall
          (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) R)‖ ≤
        (128*L)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+L^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_supported_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H L R hB hY hH hL hcol hsupp hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d Hcol W B Y H L hB hY hH hL hcol hsupp
  intro G hG E S hS T hT hST hw k hk
  obtain ⟨hGS,hGT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hdGS : Disjoint G S := Finset.disjoint_left.mpr (by
    intro i hiG hiS
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hiS)).2 hiG)
  have hdGT : Disjoint G T := Finset.disjoint_left.mpr (by
    intro i hiG hiT
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hT) hiT)).2 hiG)
  have hden := second_whole_column_denominator p hp G E.val S T
    (Finset.mem_powerset.mp E.property) hdGS hdGT L (zero_le_one.trans hL)
    (hsupp _ hGS) (hsupp _ hGT)
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E.val
  have he : e ≠ 0 := primeSubsetGenerator_ne_zero _ _
  have hde := mul_ne_zero hd he
  have hdN : 0 < ‖eisEmbedding d‖^2 := SecondPassIntegration.elementNorm_pos d hd
  have heN : 0 < ‖eisEmbedding e‖^2 := SecondPassIntegration.elementNorm_pos e he
  have henorm : ‖eisEmbedding e‖^2 = primeProductNorm p E.val :=
    primeSubsetGenerator_norm_eq_productNorm p E.val
  have hkR := (outside_childFrequencyBall (d*e) hde R k hk).le
  have hR' : ‖eisEmbedding d‖^2 * L^2 * H ≤
      Y * (‖eisEmbedding d‖^2 * ‖eisEmbedding e‖^2 * ‖eisEmbedding k‖^2) := by
    have hh := (div_le_iff₀ hY).mp hR
    have hh' := mul_le_mul_of_nonneg_right hkR hY.le
    simp only [map_mul,norm_mul,mul_pow] at hh'
    nlinarith
  have hbound : H * (‖eisEmbedding e‖^2 *
      (primeProductNorm p S * primeProductNorm p T)) ≤ Y*‖eisEmbedding k‖^2 := by
    apply (mul_le_mul_iff_right₀ (mul_pos hdN heN)).mp
    have hh := mul_le_mul_of_nonneg_left hden (mul_nonneg hdN.le hH)
    rw [←henorm] at hh
    nlinarith [hh,hR']
  rw [active_norm_sq_disjoint p S T hST,div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos heN (mul_pos (primeProductNorm_pos p hp S)
    (primeProductNorm_pos p hp T)))).mpr
  exact hbound

end
end SevenEighths.InverseMoment

end OAI

end Source2566

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondMarkedTail.lean; sha256: 0d7714df94e0738fe782d42e90131b0219eff84ee9d2fad7a6ad2f4e02424d87 -/
section Source2567
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InversePrincipalEnergy InverseSecondPrincipalCaller
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem marked_radial_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → O) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A : Finset ι) (V : 𝓢(ℝ,ℂ)) (X M : ℝ), 0 < X →
      (∀ u, V u ≠ 0 → u ≤ Real.exp M) →
      ∀ U, ‖markedRadial p slots lists a A V X U‖ ≤
        (2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * SchwartzMap.seminorm ℝ 0 0 V := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_extracted_bound ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A V X M hX hV U
  by_cases hz : V (primeProductNorm p U/X) = 0
  · simp only [markedRadial,hz,mul_zero,norm_zero]
    positivity
  · have hn : primeProductNorm p U ≤ X*Real.exp M := by
      simpa only [mul_comm] using (div_le_iff₀ hX).mp (hV _ hz)
    have hn0 : 0 ≤ primeProductNorm p U := (primeProductNorm_pos p hp U).le
    rw [markedRadial,norm_mul]
    apply (mul_le_mul (hmark p hp hcop slots lists a hslots ha A U)
      (V.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity)).trans
    gcongr

theorem full_marked_second_tail (ε : ℝ) (hε : 0 < ε) (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct Cm : ℝ), 0 < Ct ∧ 0 < Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0)
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A : Finset ι) (V W : 𝓢(ℝ,ℂ)) (X M Y H R : ℝ),
      0 < X → 0 < Y → 0 ≤ H → 1 ≤ X*Real.exp M →
      (∀ u, V u ≠ 0 → u ≤ Real.exp M) →
      wholeSecondRadius d (X*Real.exp M) Y H ≤ R →
      ‖secondSourceTail p hp hg hinj F Ψ m c d (markedRadial p slots lists a A V X) W Y
        (fun _ E => childFrequencyBall (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) R)‖ ≤
        (128*(X*Real.exp M))^4 *
          (((2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * SchwartzMap.seminorm ℝ 0 0 V)^2 *
            (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
              (1+(X*Real.exp M)^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_whole_column_tail order
  obtain ⟨Cm,hCm,hmark⟩ := marked_radial_uniform_bound ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc F Ψ hΨ m c d hd slots lists a hslots ha A V W X M Y H R hX hY hH hL hV hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d hd (markedRadial p slots lists a A V X) W
    _ Y H (X*Real.exp M) R (by positivity) hY hH hL
  · exact hmark p hp hcop slots lists a hslots ha A V X M hX hV
  · exact markedRadial_support p slots lists a A V X M hX hV
  · exact hR

end
end SevenEighths.InverseMoment

end OAI

end Source2567

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondCorrelatedCutoff.lean; sha256: ffd4c0bafb330437708928fa11bd28d4b8a3efd90d9beef57c916f86593c309a -/
section Source2568
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_correlated_column_denominator {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (G E S T : Finset ι) (hGS : Disjoint G S) (hGT : Disjoint G T)
    (L : ℝ) (hL : 0 ≤ L)
    (hS : primeProductNorm p (G ∪ S) ≤ L)
    (hT : primeProductNorm p (G ∪ T) ≤ L) :
    (primeProductNorm p E)^2 * (primeProductNorm p S * primeProductNorm p T) ≤
      (primeProductNorm p E/primeProductNorm p G)^2 * L^2 := by
  have hG0 := (primeProductNorm_pos p hp G).ne'
  have hbound := second_whole_column_denominator p hp G G S T Finset.Subset.rfl hGS hGT L hL hS hT
  calc
    _ = (primeProductNorm p E/primeProductNorm p G)^2 *
      ((primeProductNorm p G)^2 * (primeProductNorm p S*primeProductNorm p T)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (sq_nonneg _)

def correlatedSecondRadius {ι : Type*} [DecidableEq ι] (p : ι → O)
    (d : O) (G E : Finset ι) (L Y H : ℝ) : ℝ :=
  ‖eisEmbedding d‖^2 * (primeProductNorm p E/primeProductNorm p G)^2 * L^2 * H / Y

theorem full_second_correlated_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H L : ℝ) (R : Finset ι → Finset ι → ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ L →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ L) →
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        correlatedSecondRadius p d G E.val L Y H ≤ R G E.val) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun G E => childFrequencyBall
          (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) (R G E))‖ ≤
        (128*L)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+L^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_supported_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H L R hB hY hH hL hcol hsupp hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d Hcol W B Y H L hB hY hH hL hcol hsupp
  intro G hG E S hS T hT hST hw k hk
  obtain ⟨hGS,hGT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hdGS : Disjoint G S := Finset.disjoint_left.mpr (by
    intro i hiG hiS
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hiS)).2 hiG)
  have hdGT : Disjoint G T := Finset.disjoint_left.mpr (by
    intro i hiG hiT
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hT) hiT)).2 hiG)
  have hden := second_correlated_column_denominator p hp G E.val S T hdGS hdGT L (zero_le_one.trans hL)
    (hsupp _ hGS) (hsupp _ hGT)
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E.val
  have he : e ≠ 0 := primeSubsetGenerator_ne_zero _ _
  have hde := mul_ne_zero hd he
  have hdN : 0 < ‖eisEmbedding d‖^2 := SecondPassIntegration.elementNorm_pos d hd
  have heN : 0 < ‖eisEmbedding e‖^2 := SecondPassIntegration.elementNorm_pos e he
  have henorm : ‖eisEmbedding e‖^2 = primeProductNorm p E.val :=
    primeSubsetGenerator_norm_eq_productNorm p E.val
  have hkR := (outside_childFrequencyBall (d*e) hde (R G E.val) k hk).le
  have hR' : ‖eisEmbedding d‖^2 * (primeProductNorm p E.val/primeProductNorm p G)^2 * L^2 * H ≤
      Y * (‖eisEmbedding d‖^2 * ‖eisEmbedding e‖^2 * ‖eisEmbedding k‖^2) := by
    have hh := (div_le_iff₀ hY).mp (hR G hG E)
    have hh' := mul_le_mul_of_nonneg_right hkR hY.le
    simp only [map_mul,norm_mul,mul_pow] at hh'
    nlinarith
  have hbound : H * (‖eisEmbedding e‖^2 *
      (primeProductNorm p S * primeProductNorm p T)) ≤ Y*‖eisEmbedding k‖^2 := by
    apply (mul_le_mul_iff_right₀ (mul_pos hdN heN)).mp
    have hh := mul_le_mul_of_nonneg_left hden (mul_nonneg hdN.le hH)
    rw [←henorm] at hh
    rw [←henorm] at hR'
    nlinarith [hh,hR']
  rw [active_norm_sq_disjoint p S T hST,div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos heN (mul_pos (primeProductNorm_pos p hp S)
    (primeProductNorm_pos p hp T)))).mpr
  exact hbound

end
end SevenEighths.InverseMoment

end OAI

end Source2568

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondCutoffScale.lean; sha256: c12a72a3f038b7ebdd4c23b41e19f5a049e2fba9d0beb16f601f7fc2e082c7db -/
section Source2569
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_correlated_radius_bound {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (d : O) (G E : Finset ι)
    (Z delta theta g s Hc eta tau L : ℝ) (hZ : 0<Z) (hL0 : 0≤L)
    (hd : ‖eisEmbedding d‖^2≤Z^(delta+eta))
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G)
    (hL : L≤Z^(s+4*eta)) :
    correlatedSecondRadius p d G E L (Z^(Hc+12*eta+tau)) (Z^tau) ≤
      Z^(2*(s-g)-Hc+delta+2*theta+eta) := by
  have hratio : primeProductNorm p E/primeProductNorm p G ≤ Z^(theta-g+2*eta) := by
    calc
      _ ≤ Z^(theta+eta)/Z^(g-eta) := div_le_div₀
        (Real.rpow_pos_of_pos hZ _).le hE (Real.rpow_pos_of_pos hZ _) hG
      _ = _ := by rw [←Real.rpow_sub hZ]; congr 1; ring
  have hratio0 : 0≤primeProductNorm p E/primeProductNorm p G :=
    div_nonneg (primeProductNorm_pos p hp E).le (primeProductNorm_pos p hp G).le
  have hsq (x : ℝ) : (Z^x)^2=Z^(2*x) := by
    rw [pow_two,←Real.rpow_add hZ]
    congr 1
    ring
  calc
    _ ≤ Z^(delta+eta)*(Z^(theta-g+2*eta))^2*(Z^(s+4*eta))^2*
        Z^tau/Z^(Hc+12*eta+tau) := by
      unfold correlatedSecondRadius
      gcongr
    _ = _ := by
      rw [hsq,hsq,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
      congr 1
      ring

theorem second_correlated_radius_childM {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (d : O) (G E : Finset ι)
    (Z M r ell V delta A B j t g theta eta tau L : ℝ) (hZ : 0<Z) (hL0 : 0≤L)
    (hd : ‖eisEmbedding d‖^2≤Z^(delta+eta))
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G)
    (hL : L≤Z^(r-A-B-t+4*eta)) :
    correlatedSecondRadius p d G E L
      (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau) ≤
      Z^(childM M ell A t g theta V j eta) := by
  have hb := second_correlated_radius_bound p hp d G E Z delta theta g (r-A-B-t)
    (firstPhysicalHeight M r ell V delta B j) eta tau L hZ hL0 hd hE hG hL
  convert hb using 1; congr 1
  unfold childM decrease firstPhysicalHeight
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2569

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondCanonicalTail.lean; sha256: 6532c1bd09158372402e88823ae0e15279679b2d58c7f7d955ebbf97b06b9dd1 -/
section Source2570
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem first_fresh_canonical_error (ε : ℝ) (hε : 0<ε) (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct Cm : ℝ), 0<Ct ∧ 0<Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
      (F D Bset : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m : Eis)
      (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      (∀ i∈slots,Disjoint (lists i) D) →
      ∀ (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
      (X height Wbound Z M n ell V delta A B j t eta tau : ℝ),
      0<X → 0<Z → 1≤X*Real.exp Wbound → b≤Real.exp Wbound →
      X*Real.exp Wbound≤Z^(n-A-B-t+4*eta) →
      ∀ (c d : Eis), d≠0 → ‖ConcreteTraceCRT.eisEmbedding d‖^2≤Z^(delta+eta) →
      ∀ (r : FirstCoreIndex) (g theta : Finset ι→ℝ),
      (∀ G∈F.powerset,Z^(g G-eta)≤primeProductNorm p G) →
      (∀ G∈F.powerset,∀ E : G.powerset,primeProductNorm p E.val≤Z^(theta E.val+eta)) →
      let Y := Z^(firstPhysicalHeight M n ell V delta B j+12*eta+tau)
      let H := Z^tau
      let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative height) X
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p Bset v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p Bset v ε₁ ε₂
      let K := fun (G E : Finset ι) => childFrequencyBall
        (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        (Z^(childM M ell A t (g G) (theta E) V j eta))
      ‖firstFreshSecondPoisson p hp hg hinj F D Bset v ε₁ ε₂ negative χ Ψ m
          (primeMark slots lists coeff) om X c d r height Y -
        truncatedSecondSource p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K‖ ≤
        (128*(X*Real.exp Wbound))^4 *
          ((Cm*(X*Real.exp Wbound)^ε*SchwartzMap.seminorm ℝ 0 0 om)^2 *
            (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
              (1+(X*Real.exp Wbound)^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_correlated_tail order
  obtain ⟨Cm,hCm,hmark⟩ := marked_radial_uniform_bound ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc F D Bset v ε₁ ε₂ negative χ Ψ hΨ m
    slots lists coeff hslots hcoeff hD om a b ha hs X height Wbound Z M n ell V delta A B j t eta tau
    hX hZ hL hb hLscale c d hd hdN r g theta hgN heN Y H H₀ Ψ₀ m₀ c₀ K
  have hY : 0<Y := Real.rpow_pos_of_pos hZ _
  have hH : 0≤H := (Real.rpow_pos_of_pos hZ _).le
  have hid := first_fresh_radial_truncated p hp hg hinj hc F D Bset v ε₁ ε₂ negative χ Ψ m
    slots lists coeff hD om a b ha hs X height Y hX hY c d r K
  change _ = truncatedSecondSource p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K +
    secondSourceTail p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K at hid
  rw [hid,add_sub_cancel_left]
  have hVsupp := principalWindow_upper om a b ha hs Wbound hb negative height
  have hcoef := hmark p hp hcop slots lists coeff hslots hcoeff ∅
    (principalWindow om a b ha hs negative height) X Wbound hX hVsupp
  simp only [Finset.card_empty,pow_zero,one_mul,principalWindow_seminorm_zero] at hcoef
  apply htail p hp hg hinj hc F Ψ₀
    (fun z=>(firstCoreTwist_norm_le negative χ Ψ r z).trans (hΨ z))
    m₀ c₀ d hd H₀ rowMajorant _ Y H (X*Real.exp Wbound)
    (fun G E=>Z^(childM M ell A t (g G) (theta E) V j eta))
    (by positivity) hY hH hL hcoef
  · exact markedRadial_support p slots lists coeff ∅ _ X Wbound hX hVsupp
  · intro G hG E
    exact second_correlated_radius_childM p hp d G E.val Z M n ell V delta A B j t (g G)
      (theta E.val) eta tau (X*Real.exp Wbound) hZ (zero_le_one.trans hL)
      hdN (heN G hG E) (hgN G hG) hLscale

end
end SevenEighths.InverseMoment

end OAI

end Source2570

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondSourceSize.lean; sha256: 1a741a452fc04c58cb4140233c51086dd7470aebc4613e0e336e3c731f9c61c1 -/
section Source2571
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)

include hp in
theorem first_source_height_bounds (b : CubeCoordinates ι) (C D : Finset ι)
    (hCB : Disjoint C b.support)
    (hD : D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M Mmax Fmax r ell V delta B j eta tau : ℝ) (hZ : 1<Z)
    (hM : 0≤M) (hMm : M≤Mmax) (hell : 0≤ell) (hV : 0≤V)
    (hdelta : 0≤delta) (hB : 0≤B) (hj : 0≤j) (heta : 0≤eta) (htau : 0≤tau)
    (hwhole : r+3*ell+V≤Fmax)
    (h1 : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta))
    (hC : primeProductNorm p C≤Z^(r+eta))
    (hc : Z^(B-eta)≤primeProductNorm p C)
    (hd : Z^(delta-eta)≤primeProductNorm p D)
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2) :
    -Mmax≤firstPhysicalHeight M r ell V delta B j+12*eta+tau ∧
    firstPhysicalHeight M r ell V delta B j+12*eta+tau≤3*Fmax+16*eta+tau := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hd' := first_source_divisor_center p hp b C D hCB hD Z r ell delta eta hZ h1 h2 hC hd
  have hb' := (Real.rpow_le_rpow_left_iff hZ).mp (hc.trans hC)
  have hj' := hJ.trans ((cube_label_norm_bounds p hp b.support b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos (Z^(ell+eta)) (Real.rpow_pos_of_pos hz _).le h1 h2).1)
  rw [←Real.rpow_mul_natCast hz.le] at hj'
  have hj'' := (Real.rpow_le_rpow_left_iff hZ).mp hj'
  norm_num at hj''
  unfold firstPhysicalHeight
  constructor <;> linarith

include hp in

theorem second_source_scalar_caps (b : CubeCoordinates ι) (C D : Finset ι)
    (hCB : Disjoint C b.support)
    (hD : D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M Mmax Fmax r ell V delta B j eta tau A t L : ℝ) (hZ : 1<Z)
    (hM : 0≤M) (hMm : M≤Mmax) (hFm : 0≤Fmax) (hell : 0≤ell) (hV : 0≤V)
    (hdelta : 0≤delta) (hB : 0≤B) (hj : 0≤j) (heta : 0≤eta) (htau : 0≤tau)
    (hA : 0≤A) (ht : 0≤t) (hwhole : r+3*ell+V≤Fmax)
    (h1 : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta))
    (hC : primeProductNorm p C≤Z^(r+eta))
    (hc : Z^(B-eta)≤primeProductNorm p C)
    (hd : Z^(delta-eta)≤primeProductNorm p D)
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2)
    (hL : L≤Z^(r-A-B-t+4*eta)) :
    let Y := Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)
    let cap := Mmax+3*Fmax+16*eta+tau
    Y≤Z^cap ∧ Y⁻¹≤Z^cap ∧ L≤Z^cap := by
  dsimp only
  have hz : 0<Z := zero_lt_one.trans hZ
  obtain ⟨hlo,hhi⟩ := first_source_height_bounds p hp b C D hCB hD
    Z M Mmax Fmax r ell V delta B j eta tau hZ hM hMm hell hV hdelta hB hj heta htau
    hwhole h1 h2 hC hc hd hJ
  refine ⟨Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith),?_,?_⟩
  · rw [←Real.rpow_neg hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · exact hL.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))

end
end SevenEighths.InverseMoment

end OAI

end Source2571

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondTailAbsorption.lean; sha256: cc38b688f2bf6578c989b620406856e4e77d8a97a757e376c2cf9b68379a3075 -/
section Source2572
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section

lemma second_tail_fixed_cap (Y L cap B P H : ℝ) (order : ℕ)
    (hY : 0<Y) (hL : 0≤L) (hc : 1≤cap) (_hB : 0≤B) (hP : 0≤P) (hH : 0≤H)
    (hy : Y≤cap) (hyi : Y⁻¹≤cap) (hl : L≤cap) :
    (128*L)^4*(B^2*(Y*P*(1+L^3/Y)^2/(1+H)^order))≤
      (4*128^4)*B^2*P*cap^13/(1+H)^order := by
  have hc0 : 0≤cap := zero_le_one.trans hc
  have hscale : 1+L^3/Y≤2*cap^4 := by
    calc
      _ ≤ 1+cap^3*cap := by rw [div_eq_mul_inv]; gcongr
      _ ≤ _ := by have hh : 1≤cap^4 := one_le_pow₀ hc; nlinarith
  calc
    _ = (128*L)^4*B^2*Y*P*(1+L^3/Y)^2/(1+H)^order := by ring
    _ ≤ (128*cap)^4*B^2*cap*P*(2*cap^4)^2/(1+H)^order := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      gcongr
    _ = _ := by ring

theorem choose_second_tail_order (Lcap tau saving : ℝ) (hL : 0≤Lcap) (htau : 0<tau) :
    ∃ order : ℕ,∀ Z Y L B P : ℝ,1≤Z → 0<Y → 0≤L → 0≤B → 0≤P →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → L≤Z^Lcap →
      (128*L)^4*(B^2*(Y*P*(1+L^3/Y)^2/(1+Z^tau)^order))≤
        (4*128^4)*B^2*P*Z^(-saving) := by
  obtain ⟨order,ho⟩ := exists_nat_gt ((13*Lcap+saving)/tau)
  refine ⟨order,?_⟩
  intro Z Y L B P hZ hY hL0 hB hP hy hyi hl
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hb := second_tail_fixed_cap Y L (Z^Lcap) B P (Z^tau) order hY hL0
    (Real.one_le_rpow hZ hL) hB hP (Real.rpow_pos_of_pos hz _).le hy hyi hl
  have hdecay : (Z^Lcap)^13/(1+Z^tau)^order≤Z^(-saving) := by
    calc
      _ ≤ (Z^Lcap)^13/(Z^tau)^order := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) order)
      _ = Z^(13*Lcap-tau*(order:ℝ)) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
        congr 1
        norm_num
        ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hZ
        have hh := (div_lt_iff₀ htau).mp ho
        nlinarith
  apply hb.trans
  calc
    _ = ((4*128^4)*B^2*P)*((Z^Lcap)^13/(1+Z^tau)^order) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

end
end SevenEighths.InverseMoment

end OAI

end Source2572

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondRapidTail.lean; sha256: 8766a87f6708cc74a8f59cac45b31d6957db79f352a3925be18e931759be4f18 -/
section Source2573
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_second_rapid_correlated_tail (Lcap tau saving : ℝ)
    (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ), (∀ a,‖Ψ a‖≤1) →
      ∀ (m c d : O),d≠0 → ∀ (Hcol : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (Z B Y L : ℝ) (R : Finset ι→Finset ι→ℝ),
      1≤Z → 0≤B → 0<Y → 1≤L → Y≤Z^Lcap → Y⁻¹≤Z^Lcap → L≤Z^Lcap →
      (∀ U,‖Hcol U‖≤B) → (∀ U,Hcol U≠0 → primeProductNorm p U≤L) →
      (∀ G∈F.powerset,∀ E : G.powerset,correlatedSecondRadius p d G E.val L Y (Z^tau)≤R G E.val) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))‖≤
      C*B^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  obtain ⟨order,horder⟩ := choose_second_tail_order Lcap tau saving hLcap htau
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_correlated_tail order
  refine ⟨s,(4*128^4)*Ct,by positivity,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W Z B Y L R hZ hB hY hL hy hyi hl hcol hsupp hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have he := htail p hp hg hinj hc F Ψ hΨ m c d hd Hcol W B Y (Z^tau) L R
    hB hY (Real.rpow_pos_of_pos hz _).le hL hcol hsupp hR
  apply he.trans
  have hh := horder Z Y L B (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    hZ hY (zero_le_one.trans hL) hB (mul_nonneg hCt.le (apply_nonneg _ _)) hy hyi hl
  convert hh using 1 ; ring

end
end SevenEighths.InverseMoment

end OAI

end Source2573

/- Original source: OAI/NumberTheory/DirichletL/Descent/PrincipalSelectorMass.lean; sha256: 66e76744d7e742bb759caf80733b88cac30556aecaa99655f39487b27bee771b -/
section Source2574
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

theorem first_selector_weighted_mass {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (pool A:Finset ι) (selector:Finset ι→ℂ) (E T S ε:ℝ)
    (hE:0≤E) (hT:0<T) (hS:0≤S) (hε:0≤ε)
    (hA:primeProductNorm p A≤E)
    (hselector:∀D∈pool.powerset,‖selector D‖≤S)
    (hsupport:∀D∈pool.powerset,selector D≠0→primeProductNorm p D≤T) :
    (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^ε)≤
      128*T*S*(E*T)^ε := by
  have hfilter:(∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^ε)=
      ∑D∈boundedPrimeSupports p pool T,‖selector D‖*(primeProductNorm p (A∪D))^ε:=by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro D hD hnot
    have hz:selector D=0:=by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨hD,hsupport D hD h⟩)
    simp [hz]
  rw [hfilter]
  calc
    _≤∑D∈boundedPrimeSupports p pool T,S*(E*T)^ε:=by
      apply Finset.sum_le_sum
      intro D hD
      have hnorm:primeProductNorm p (A∪D)≤E*T:=
        (primeProductNorm_union_le_mul p hp A D).trans
          (mul_le_mul hA (Finset.mem_filter.mp hD).2 (primeProductNorm_pos p hp D).le hE)
      exact mul_le_mul (hselector D (Finset.mem_filter.mp hD).1)
        (Real.rpow_le_rpow (primeProductNorm_pos p hp _).le hnorm hε)
        (Real.rpow_nonneg (primeProductNorm_pos p hp _).le _) hS
    _= ((boundedPrimeSupports p pool T).card:ℝ)*S*(E*T)^ε:=by simp;ring
    _≤_:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (boundedPrimeSupports_card_positive p hp hinj pool T hT) hS)
      (Real.rpow_nonneg (mul_nonneg hE hT.le) _)

theorem first_whole_extracted_norm {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (b:CubeCoordinates ι) (hb:b.Admissible) (C extra:Finset ι) (he:extra⊆b.support)
    (negative:Bool) (B:ℝ) (hB:0≤B)
    (h₁:‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (h₂:‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) :
    primeProductNorm p (extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))≤
      B^2*primeProductNorm p C := by
  have hbits:(if negative then b.rightDivisor else b.leftDivisor)⊆b.support:=by
    cases negative
    · exact hb.1
    · exact hb.2
  have hs:extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)⊆b.support∪C:=by
    exact Finset.union_subset (he.trans Finset.subset_union_left)
      (Finset.union_subset_union hbits (Finset.Subset.refl C))
  apply (primeProductNorm_mono p hp hs).trans
  apply (primeProductNorm_union_le_mul p hp b.support C).trans
  exact mul_le_mul_of_nonneg_right (cubeCoordinates_radical_bound p hp b B hB h₁ h₂)
    (primeProductNorm_pos p hp C).le

end SevenEighths.InverseMoment

end

end OAI

end Source2574

/- Original source: OAI/NumberTheory/DirichletL/Inversion/WholePriorityRapidTail.lean; sha256: eb84141144393fab491600905024ba2daa9aede9f8974dbbd6a2958aa2f1613e -/
section Source2575
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityRapidTail
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseMoment InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O" => ActualEisensteinCubic.O

theorem marked_rapid_tail (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ), (∀u,‖Ψ u‖≤1) →
      ∀ (m c d : O),d≠0 → ∀ (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      ∀ (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (negative : Bool) (height X M Y Z : ℝ)
      (R : Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀G∈F.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (markedRadial p slots lists a ∅ (principalWindow om lo hi hlo hs negative height) X) W Y
        (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))‖≤
      Ct*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_rapid_correlated_tail Lcap tau (saving+Lcap) hLcap htau
  obtain ⟨Cm,hCm,hmark⟩ := marked_radial_uniform_bound (1/2) (by norm_num)
  refine ⟨s,Ct*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc F Ψ hΨ m c d hd slots lists a hslots ha
    om W lo hi hlo hs negative height X M Y Z R hX hhi hZ hY hL hy hyi hl hR
  let L:=X*Real.exp M
  have hLpos : 0<L := mul_pos hX (Real.exp_pos _)
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hv := principalWindow_upper om lo hi hlo hs M hhi negative height
  have hm := hmark p hp hcop slots lists a hslots ha ∅
    (principalWindow om lo hi hlo hs negative height) X M hX hv
  simp only [Finset.card_empty,pow_zero,one_mul,principalWindow_seminorm_zero] at hm
  have ht := htail p hp hg hinj hc F Ψ hΨ m c d hd _ W Z
    (Cm*L^(1/2:ℝ)*SchwartzMap.seminorm ℝ 0 0 om) Y L R hZ (by positivity) hY hL hy hyi hl hm
    (markedRadial_support p slots lists a ∅ _ X M hX hv) hR
  have hp : (L^(1/2:ℝ))^2=L := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hLpos.le]
    norm_num
  have habsorb : L*Z^(-(saving+Lcap))≤Z^(-saving) := by
    calc
      _≤Z^Lcap*Z^(-(saving+Lcap)) := mul_le_mul_of_nonneg_right hl (by positivity)
      _=Z^(-saving) := by rw [←Real.rpow_add hz];congr 1;ring
  apply ht.trans
  calc
    _=(Ct*Cm^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        (L*Z^(-(saving+Lcap))) := by rw [mul_pow,mul_pow,hp];ring
    _≤_ := by
      exact mul_le_mul_of_nonneg_left habsorb (by positivity)

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def wholePriorityTailEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support om⊆Set.Icc lo hi) (X t Y : ℝ)
    (R : Finset ι→Finset ι→Finset ι→ℝ) : ℝ :=
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖*
      ∑J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2*
        ‖secondSourceTail p hp hg hinj pool
          (firstCoreTwist negative (if negative then r.1 else r.2) Ψ core)
          ((m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit)*∏i∈D,p i)
          ((∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit) d
          (markedRadial p (slots\J) (fun i=>lists i\(A∪D)) a ∅
            (principalWindow om lo hi hlo hs negative t) X) W Y
          (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R D G E))‖

theorem whole_priority_tail_weighted (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
      (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (selector : Finset ι→ℂ) (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (M t X Y Z : ℝ)
      (R : Finset ι→Finset ι→Finset ι→ℝ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → d≠0 → hi≤Real.exp M → 0<X → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀D∈pool.powerset,selector D≠0 → ∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R D G E.val) →
      wholePriorityTailEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a
        selector om W lo hi hlo hs X t Y R ≤
      Ct*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Z^(-saving)*(∑D∈pool.powerset,‖selector D‖*primeProductNorm p
          ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := marked_rapid_tail Lcap tau saving hLcap htau
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power (1/2) (by norm_num)
  refine ⟨s,((32*512:ℝ)^2*512)*Ct*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  let P:=Ct*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving)
  have hP : 0≤P := by dsimp [P];positivity
  have hn (D : Finset ι) : 0≤primeProductNorm p (A∪D) := (primeProductNorm_pos p hp _).le
  have hm (J : Finset σ) (hJ : J∈slots.powerset) (D : Finset ι) :
      ‖primeMark J lists a (A∪D)‖^2≤Cm^2*primeProductNorm p (A∪D) := by
    have hj:=Finset.mem_powerset.mp hJ
    have hh:=hmark p hp hcop J lists a (fun i hi j hj' hij=>hslots (hj hi) (hj hj') hij)
      (fun i hi=>ha i (hj hi)) (A∪D)
    have he : ((primeProductNorm p (A∪D))^(1/2:ℝ))^2=primeProductNorm p (A∪D) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (hn D)]
      norm_num
    calc
      _≤(Cm*(primeProductNorm p (A∪D))^(1/2:ℝ))^2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
      _=_ := by rw [mul_pow,he]
  unfold wholePriorityTailEnergy
  dsimp only
  calc
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
        ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative Ψ m D core‖*
        ((2:ℝ)^slots.card*(Cm^2*primeProductNorm p (A∪D)*P)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro D hD
      by_cases hsel : selector D=0
      · simp only [hsel,norm_zero,mul_zero,zero_mul,le_refl]
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro core hcore
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        calc
          _≤∑J∈slots.powerset,Cm^2*primeProductNorm p (A∪D)*P := by
            apply Finset.sum_le_sum
            intro J hJ
            have ht := htail p hp hcop hg hinj hc pool
              (firstCoreTwist negative (if negative then r.1 else r.2) Ψ core)
              (fun z=>(firstCoreTwist_norm_le negative _ Ψ core z).trans (hΨ z))
              ((m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
                b.leftBit b.rightBit)*∏i∈D,p i)
              ((∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
                b.leftBit b.rightBit) d hd (slots\J) (fun i=>lists i\(A∪D)) a
              (residual_lists_pairwise slots J lists A D hslots)
              (residual_coeff_bound slots J lists a A D ha) om W lo hi hlo hs negative t X M Y Z (R D)
              hX hhi hZ hY hL hy hyi hl (hR D hD hsel)
            exact mul_le_mul (hm J hJ D) ht (norm_nonneg _) (mul_nonneg (sq_nonneg _) (hn D))
          _=_ := by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*
        ((32*512)*((2:ℝ)^slots.card*(Cm^2*primeProductNorm p (A∪D)*P))) := by
      gcongr with r hr D hD
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (firstCoreOuter_mass p hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D (hΨ _))
        (mul_nonneg (pow_nonneg (by norm_num) _)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (hn D)) hP))
    _=((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*P*
      (∑r:RayCharacter×RayCharacter,‖crossCoeff r.1 r.2‖)*
      (∑D∈pool.powerset,‖selector D‖*primeProductNorm p (A∪D)) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm (s:=pool.powerset)]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring
    _≤((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*P*512*
      (∑D∈pool.powerset,‖selector D‖*primeProductNorm p (A∪D)) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · simpa only [Fintype.sum_prod_type] using crossCoeff_sum_norm_le
        · positivity
      · exact Finset.sum_nonneg (fun D hD=>mul_nonneg (norm_nonneg _) (hn D))
    _=_ := by
      have he : ((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card := by rw [←pow_mul,pow_mul'];norm_num
      rw [he]
      dsimp only [P,A]
      ring

theorem whole_priority_tail_bound (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
      (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (selector : Finset ι→ℂ) (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (M t X Y Z : ℝ)
      (R : Finset ι→Finset ι→Finset ι→ℝ) (B T S : ℝ),
      b.Admissible → extra⊆b.support → 0≤B → 0<T → 0≤S →
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B →
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B →
      (∀D∈pool.powerset,‖selector D‖≤S) →
      (∀D∈pool.powerset,selector D≠0 → primeProductNorm p D≤T) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → d≠0 → hi≤Real.exp M → 0<X → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀D∈pool.powerset,selector D≠0 → ∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R D G E.val) →
      wholePriorityTailEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a
        selector om W lo hi hlo hs X t Y R ≤
      Ct*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        S*(B^2*primeProductNorm p C)*T^2*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := whole_priority_tail_weighted Lcap tau saving hLcap htau
  refine ⟨s,128*Ct,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R B T S hb he hB hT hS hb₁ hb₂ hsel hsupp
    hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR
  have hn := first_whole_extracted_norm p hp b hb C extra he negative B hB hb₁ hb₂
  have hmass := first_selector_weighted_mass p hp hinj pool
    (extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)) selector
    (B^2*primeProductNorm p C) T S 1 (mul_nonneg (sq_nonneg _) (primeProductNorm_pos p hp C).le)
    hT hS (by norm_num) hn hsel hsupp
  simp only [Real.rpow_one] at hmass
  have ht := htail p hp hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR
  apply ht.trans
  have hh := mul_le_mul_of_nonneg_left hmass
    (show 0≤Ct*(4:ℝ)^slots.card*
      (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*Z^(-saving) by positivity)
  convert hh using 1
  ring

theorem whole_priority_tail_rapid (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
      (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (selector : Finset ι→ℂ) (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (M t X Y Z : ℝ)
      (R : Finset ι→Finset ι→Finset ι→ℝ) (B T S : ℝ),
      b.Admissible → extra⊆b.support → 0≤B → 0<T → 0≤S →
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B →
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B →
      (∀D∈pool.powerset,‖selector D‖≤S) →
      (∀D∈pool.powerset,selector D≠0 → primeProductNorm p D≤T) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → d≠0 → hi≤Real.exp M → 0<X → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀D∈pool.powerset,selector D≠0 → ∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R D G E.val) →
      B^2*primeProductNorm p C≤Z^Lcap → T≤Z^Lcap →
      wholePriorityTailEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a
        selector om W lo hi hlo hs X t Y R ≤
      Ct*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        S*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := whole_priority_tail_bound Lcap tau (saving+3*Lcap) hLcap htau
  refine ⟨s,Ct,hCt,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R B T S hb he hB hT hS hb₁ hb₂ hsel hsupp
    hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR hEcap hTcap
  have ht := htail p hp hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R B T S hb he hB hT hS hb₁ hb₂ hsel hsupp
    hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have habsorb : (B^2*primeProductNorm p C)*T^2*Z^(-(saving+3*Lcap))≤Z^(-saving) := by
    calc
      _≤Z^Lcap*(Z^Lcap)^2*Z^(-(saving+3*Lcap)) := by gcongr
      _=Z^(-saving) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
  apply ht.trans
  have hh := mul_le_mul_of_nonneg_left habsorb
    (show 0≤Ct*(4:ℝ)^slots.card*
      (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*S by positivity)
  convert hh using 1
  ring

def wholeFreshError (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C extra D : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (R : Finset ι→Finset ι→ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) : ℂ :=
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  let H:=markedRadial p (slots\J) (fun i=>lists i\(A∪D)) a ∅
    (principalWindow om lo hi hlo hs negative t) X
  let Ψ₀:=firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
  let m₀:=(m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit)*∏i∈D,p i
  let c₀:=(∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
  firstFreshSecondPoisson p hp hg hinj pool D b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
    (primeMark (slots\J) (fun i=>lists i\(A∪D)) a) om X (∏i∈C,p i) d core t Y -
  truncatedSecondSource p hp hg hinj pool Ψ₀ m₀ c₀ d H rowMajorant Y
    (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))

lemma wholeFreshError_eq_tail (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (b : CubeCoordinates ι) (C extra D : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (R : Finset ι→Finset ι→ℝ)
    (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) :
    wholeFreshError p hp hg hinj pool b C extra D negative Ψ m d slots J lists a
      om lo hi hlo hs X t Y R r core =
    let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
    secondSourceTail p hp hg hinj pool (firstCoreTwist negative (if negative then r.1 else r.2) Ψ core)
      ((m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit)*∏i∈D,p i)
      ((∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) d
      (markedRadial p (slots\J) (fun i=>lists i\(A∪D)) a ∅
        (principalWindow om lo hi hlo hs negative t) X) rowMajorant Y
      (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E)) := by
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  have he := first_fresh_radial_truncated p hp hg hinj hc pool D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m (slots\J) (fun i=>lists i\(A∪D)) a
    (fun i _=>residual_lists_avoid lists A D i) om lo hi hlo hs X t Y hX hY
    (∏i∈C,p i) d core
    (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))
  dsimp only at he
  unfold wholeFreshError
  dsimp only
  rw [he,add_sub_cancel_left]

theorem wholePriorityTailEnergy_eq_original_errors
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support om⊆Set.Icc lo hi) (X t Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (R : Finset ι→Finset ι→Finset ι→ℝ) :
    wholePriorityTailEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a selector
      om rowMajorant lo hi hlo hs X t Y R =
    let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
    (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
        ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative Ψ m D core‖*
        ∑J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2*
          ‖wholeFreshError p hp hg hinj pool b C extra D negative Ψ m d slots J lists a
            om lo hi hlo hs X t Y (R D) r core‖ := by
  simp_rw [wholeFreshError_eq_tail p hp hg hinj hc pool b C extra _ negative Ψ m d slots _
    lists a om lo hi hlo hs X t Y hX hY]
  rfl

end SevenEighths.InverseWholePriorityRapidTail

end

end OAI

end Source2575

/- Original source: OAI/NumberTheory/DirichletL/Descent/WholePriorityCollapse.lean; sha256: 6b1cac27c33fb7f61b239c8d08ff4daf3c49fa57181103d67798edc6be79decd -/
section Source2576
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem whole_assigned_source_original
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (H:SecondParentSource ι Jo→ℂ):
    (∑y∈activeParents p extra pool cube C E old selector negative assigned lists,
      coefficient p assigned a (fun x=>(priorityOuter p hg cube negative Ψ m selector ray core x.quotientSupport:ℂ)) y *
        H (forgetAppended y))=
    ∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      H (parent p (fixedPoint cube C E old D)) := by
  rw [activeParents,←wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj,
    sum_activeFixedSource]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector D≠0
  · rw [ite_eq_left hs]
    simp only [fixedPoint,wholeExtractedSupport,extractedSupport,Finset.union_assoc]
  · rw [ite_eq_right hs,priorityOuter_zero p hg cube negative Ψ m selector ray core D (not_ne_iff.mp hs)]
    simp

theorem whole_assigned_source_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (H:SecondParentSource ι Jo→ℂ):
    ‖∑y∈activeParents p extra pool cube C E old selector negative assigned lists,
      coefficient p assigned a (fun x=>(priorityOuter p hg cube negative Ψ m selector ray core x.quotientSupport:ℂ)) y *
        H (forgetAppended y)‖≤
    ∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
      ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*
      ‖H (parent p (fixedPoint cube C E old D))‖ := by
  rw [whole_assigned_source_original p hg hinj]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro D hD
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (by unfold priorityOuter;positivity),Real.norm_of_nonneg (sq_nonneg _)]

end SevenEighths.InverseMoment

end

end OAI

end Source2576

/- Original source: OAI/NumberTheory/DirichletL/Descent/WholePriorityBranches.lean; sha256: 36b2206f0cf6045a27ba3166ae432f2e760486d276d772b013f62c06cd5164b1 -/
section Source2577
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def priorityZeroParent (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):ℂ:=
  truncatedSecondZero p hg pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)

def priorityTailParent (hp:∀i,p i≠0) (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):ℂ:=
  secondSourceTail p hp hg hinj pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)

theorem whole_priority_signed_branches
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=activeParents p extra pool cube C E old selector negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    (∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      wholePriorityPoisson p hp hg hinj pool cube C E (extra cube) negative Ψ m slots assigned lists a om X t Y ray core D)=
    (∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D)))+
    (∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x)+
    (∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D))) := by
  intro V Ψ₀ parents source
  rw [whole_priority_complex_slice p hp hg hcop hinj hc hpr pool cube C E extra old negative Ψ m
    slots assigned lists a selector om lo hi hlo hs X t Y hX hY ray core R (fun _ _=>())]
  rw [fullPhysical_unified p hg hp hcop hinj extra pool]
  dsimp only
  rw [←whole_assigned_source_original p hg hinj extra pool cube C E old selector negative Ψ m ray core assigned lists a
      (priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R),
    ←whole_assigned_source_original p hg hinj extra pool cube C E old selector negative Ψ m ray core assigned lists a
      (priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R)]
  rfl

theorem whole_priority_slice_bound
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→SmoothMobiusCorrection.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=activeParents p extra pool cube C E old selector negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    ‖∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      wholePriorityPoisson p hp hg hinj pool cube C E (extra cube) negative Ψ m slots assigned lists a om X t Y ray core D‖≤
    (∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
      ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*
      ‖priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D))‖)+
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x‖+
    (∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
      ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D))‖) := by
  intro V Ψ₀ parents source
  rw [whole_priority_signed_branches p hg hp hcop hinj hc hpr extra pool cube C E old selector negative
    Ψ m ray core slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  have hn (H:Finset ι→ℂ):
      ‖∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
        (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*H D‖≤
      ∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
        ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*‖H D‖:=by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro D hD
    rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (by unfold priorityOuter;positivity),Real.norm_of_nonneg (sq_nonneg _)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hn _) (le_refl _))) (hn _))

end SevenEighths.InverseMoment

end

end OAI

end Source2577

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityBranches.lean; sha256: a09be139c40765b235b6b63014e70059e968d19282ffc419698dc4a0b84b82ea -/
section Source2578
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_priority_signed_branches
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (Source ι Jo)) (w:Source ι Jo→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots assigned (fun i=>lists i\extra x.cube) a om X t Y ray core (parent p x))=
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x))+
    (∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x)+
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)) := by
  intro V Ψ₀ parents source
  rw [global_priority_physical_source p hp hcop hg hinj hc hpr extra pool original negative Ψ m ray core w
    slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  rw [wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj original negative assigned lists a
      (globalPriorityOuter p hg negative Ψ m ray core w)
      (priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R),
    wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj original negative assigned lists a
      (globalPriorityOuter p hg negative Ψ m ray core w)
      (priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R)]
  rfl

theorem global_priority_slice_bound
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (Source ι Jo)) (w:Source ι Jo→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots assigned (fun i=>lists i\extra x.cube) a om X t Y ray core (parent p x)‖≤
    (∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖)+
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x‖+
    (∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖) := by
  intro V Ψ₀ parents source
  rw [global_priority_signed_branches p hg hp hcop hinj hc hpr extra pool original w negative
    Ψ m ray core slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  have hn (H:Source ι Jo→ℂ):
      ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
        (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*H x‖≤
      ∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
        ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*‖H x‖:=by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro x hx
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hn _) (le_refl _))) (hn _))

end SevenEighths.InverseMoment

end

end OAI

end Source2578

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPrincipalMass.lean; sha256: 09233b2c0ff0376cb1100afe9eb88928a1b8945cb1a799e824961c50de489430 -/
section Source2579
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

abbrev Core (ι : Type*) := CubeCoordinates ι×Finset ι×Finset ι

def core {ι : Type*} {Jo : ℕ} (x : Source ι Jo) : Core ι :=
  (x.cube,x.firstCommon,x.quotientSupport)

def divisorTarget {ι : Type*} [DecidableEq ι] (p : ι→O) (q : Core ι) : Ideal O :=
  sourceIdeal p q.1.support*sourceIdeal p q.2.1*sourceIdeal p q.2.2

lemma divisorTarget_ne_zero {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (q : Core ι) : divisorTarget p q≠0 :=
  mul_ne_zero (mul_ne_zero (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _))
    (sourceIdeal_ne_zero p hp _)

lemma firstDivisor_dvd_target {ι : Type*} [DecidableEq ι] (p : ι→O)
    [∀i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ} (x : Source ι Jo) (hx : SourceValid p x) :
    sourceIdeal p x.firstDivisor∣divisorTarget p (core x) := by
  have hd := sourceIdeal_dvd p _ _ hx.first_divisor
  rw [sourceIdeal_union p _ _ hx.common_disjoint] at hd
  apply hd.trans
  change sourceIdeal p x.firstCommon*sourceIdeal p x.cube.support∣
    sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*sourceIdeal p x.quotientSupport
  rw [mul_comm (sourceIdeal p x.firstCommon)]
  exact dvd_mul_right _ _

theorem core_fiber_card {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i})) {Jo : ℕ}
    (S : Finset (Source ι Jo)) (q : Core ι)
    (hS : ∀x∈S,SourceValid p x) (hq : ∀x∈S,core x=q) :
    S.card≤(idealDivisors (divisorTarget p q)).card^(Jo+1) := by
  let D := idealDivisors (divisorTarget p q)
  have hD := divisorTarget_ne_zero p hp q
  let encode (x : S) : D×(Fin Jo→D) :=
    (⟨sourceIdeal p x.val.firstDivisor,(mem_idealDivisors hD).mpr (by
      simpa only [hq x.val x.property] using firstDivisor_dvd_target p x.val (hS x.val x.property))⟩,
      fun i=>⟨(x.val.oldAssigned i).val,(mem_idealDivisors hD).mpr (by
        have hh := (hS x.val x.property).old_support i
        change (x.val.oldAssigned i).val∣divisorTarget p (core x.val) at hh
        simpa only [hq x.val x.property] using hh)⟩)
  have hi : Function.Injective encode := by
    intro x y he
    have hk := (hq x.val x.property).trans (hq y.val y.property).symm
    have hd : x.val.firstDivisor=y.val.firstDivisor :=
      sourceIdeal_injective p hinj (congrArg (fun z=>z.1.val) he)
    have ho : x.val.oldAssigned=y.val.oldAssigned := by
      funext i
      apply Subtype.ext
      exact congrArg (fun z=>(z.2 i).val) he
    apply Subtype.ext
    exact Source.ext (congrArg Prod.fst hk) (congrArg (fun q=>q.2.1) hk) hd
      (congrArg (fun q=>q.2.2) hk) ho
  have hh := Fintype.card_le_of_injective encode hi
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,D,pow_succ,mul_comm] using hh

theorem core_fiber_small_power (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(q : Core ι),
    (∀x∈S,SourceValid p x) → (∀x∈S,core x=q) →
    (S.card:ℝ)≤C*(Ideal.absNorm (divisorTarget p q):ℝ)^eps := by
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power
    (eps/(Jmax+1)) (by positivity)
  refine ⟨D^(Jmax+1),by positivity,?_⟩
  intro ι _ p hp _ hinj Jo hJo S q hS hq
  have h0 := divisorTarget_ne_zero p hp q
  have hcard : S.card≤(idealDivisors (divisorTarget p q)).card^(Jmax+1) :=
    (core_fiber_card p hp hinj S q hS hq).trans
      (Nat.pow_le_pow_right (InverseInitialFibers.divisor_card_pos _ h0) (Nat.add_le_add_right hJo 1))
  have hb := pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ h0) (Jmax+1)
  apply (show (S.card:ℝ)≤((idealDivisors (divisorTarget p q)).card:ℝ)^(Jmax+1) by exact_mod_cast hcard).trans
  apply hb.trans_eq
  rw [mul_pow]
  congr 1
  rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  field_simp

lemma divisorTarget_norm_bound {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (q : Core ι) (B V T : ℝ)
    (hB : 0≤B) (hV : 0≤V) (_hT : 0≤T)
    (hb₁ : ‖eisEmbedding (primeProduct p q.1.support q.1.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p q.1.support q.1.rightExponent)‖^2≤B)
    (hC : primeProductNorm p q.2.1≤V) (ht : primeProductNorm p q.2.2≤T) :
    (Ideal.absNorm (divisorTarget p q):ℝ)≤B^2*V*T := by
  unfold divisorTarget
  simp only [map_mul,Nat.cast_mul,sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
  change primeProductNorm p q.1.support*primeProductNorm p q.2.1*primeProductNorm p q.2.2≤_
  exact mul_le_mul (mul_le_mul (cubeCoordinates_radical_bound p hp q.1 B hB hb₁ hb₂)
    hC (primeProductNorm_pos p hp _).le (sq_nonneg _)) ht (primeProductNorm_pos p hp _).le
    (mul_nonneg (sq_nonneg _) hV)

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI

end Source2579

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPrincipalMassCount.lean; sha256: 09eb156ea6787d657a71681fbfa102c95d2ce843fec108b9d4b1a0703d6e262f -/
section Source2580
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma support_family_card {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (S : Finset (Finset ι)) (U : ℝ) (hU : 0<U) (hS : ∀A∈S,primeProductNorm p A≤U) :
    (S.card:ℝ)≤128*U := by
  by_cases h1 : 1≤U
  · have hh := DescentFiberCost.finite_ideal_count_real (S.image (sourceIdeal p)) U h1
      (by intro I hI;obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hI;exact sourceIdeal_ne_zero p hp A)
      (by
        intro I hI
        obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hI
        simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hS A hA)
    simpa only [Finset.card_image_of_injective S (sourceIdeal_injective p hinj)] using hh

  · have he : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      exact h1 ((primeProductNorm_ge_one p hp A).trans (hS A hA))
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem original_source_card (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(B H V T : ℝ),
    1≤B → 0≤H → 0<V → 0<T → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤H) →
    (∀x∈S,primeProductNorm p x.firstCommon≤V) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤T) →
    (S.card:ℝ)≤C*B^(1+eps)*H*V*T*(B^2*V*T)^eps := by
  obtain ⟨Cf,hCf,hfiber⟩ := core_fiber_small_power Jmax eps heps
  obtain ⟨Cb,hCb,hcube⟩ := cube_coordinates_parity_count eps heps
  refine ⟨Cf*Cb*128^2,by positivity,?_⟩
  intro ι _ p hp _ hinj Jo hJo S B H V T hB hH hV hT hS hleft hright hactive hcommon hquot
  let Q := S.image core
  let bs := S.image Source.cube
  let cs := S.image Source.firstCommon
  let ts := S.image Source.quotientSupport
  have hbcount : (bs.card:ℝ)≤Cb*B^(1+eps)*H := hcube p hp hinj bs B H hB hH
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact (hS x hx).admissible)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hleft x hx)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hright x hx)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hactive x hx)
  have hccount : (cs.card:ℝ)≤128*V := support_family_card p hp hinj cs V hV
    (by intro A hA;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA;exact hcommon x hx)
  have htcount : (ts.card:ℝ)≤128*T := support_family_card p hp hinj ts T hT
    (by intro A hA;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA;exact hquot x hx)
  have hsub : Q⊆bs×ˢ(cs×ˢts) := by
    intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,Finset.mem_image_of_mem _ hx⟩⟩
  have hQcard : (Q.card:ℝ)≤(Cb*B^(1+eps)*H)*(128*V)*(128*T) := by
    have hh : (Q.card:ℝ)≤(bs.card:ℝ)*((cs.card:ℝ)*(ts.card:ℝ)) := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (by simp only [Finset.card_product])
    apply hh.trans
    calc
      _ ≤ (Cb*B^(1+eps)*H)*((128*V)*(128*T)) := by gcongr
      _ = _ := by ring
  have hF (q : Core ι) (hq : q∈Q) :
      ((S.filter (fun x=>core x=q)).card:ℝ)≤Cf*(B^2*V*T)^eps := by
    have hf := hfiber p hp hinj Jo hJo (S.filter (fun x=>core x=q)) q
      (fun x hx=>hS x (Finset.mem_filter.mp hx).1) (fun x hx=>(Finset.mem_filter.mp hx).2)
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    apply hf.trans
    apply mul_le_mul_of_nonneg_left _ hCf.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (divisorTarget_norm_bound p hp (core x) B V T (zero_le_one.trans hB) hV.le hT.le
        (hleft x hx) (hright x hx) (hcommon x hx) (hquot x hx)) heps.le
  have he : (S.card:ℝ)=∑q∈Q,((S.filter (fun x=>core x=q)).card:ℝ) := by
    calc
      _ = ∑_x∈S,(1:ℝ) := by simp
      _ = ∑q∈Q,∑_x∈S.filter (fun x=>core x=q),(1:ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx=>Finset.mem_image_of_mem core hx) _).symm
      _ = _ := by simp
  rw [he]
  calc
    _ ≤ ∑_q∈Q,Cf*(B^2*V*T)^eps := Finset.sum_le_sum hF
    _ = (Q.card:ℝ)*(Cf*(B^2*V*T)^eps) := by simp
    _ ≤ ((Cb*B^(1+eps)*H)*(128*V)*(128*T))*(Cf*(B^2*V*T)^eps) :=
      mul_le_mul_of_nonneg_right hQcard (by positivity)
    _ = _ := by ring

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI

end Source2580

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPrincipalMassWeighted.lean; sha256: b87d0591e3a08450c73b3750a83714940675355c48883e2ad0273eace3df174b -/
section Source2581
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def principalSupport {ι : Type*} [DecidableEq ι] {Jo : ℕ}
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool) (x : Source ι Jo) : Finset ι :=
  (extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪x.quotientSupport

lemma principalSupport_norm {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ}
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool) (x : Source ι Jo)
    (hx : SourceValid p x) (hextra : extra x.cube⊆x.cube.support)
    (B V T : ℝ) (hB : 0≤B) (hV : 0≤V)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B)
    (hC : primeProductNorm p x.firstCommon≤V) (ht : primeProductNorm p x.quotientSupport≤T) :
    primeProductNorm p (principalSupport extra negative x)≤B^2*V*T := by
  have hh := first_whole_extracted_norm p hp x.cube hx.admissible x.firstCommon (extra x.cube)
    hextra negative B hB hb₁ hb₂
  unfold principalSupport
  apply (primeProductNorm_union_le_mul p hp _ _).trans
  exact mul_le_mul (hh.trans (mul_le_mul_of_nonneg_left hC (sq_nonneg _))) ht
    (primeProductNorm_pos p hp _).le (mul_nonneg (sq_nonneg _) hV)

theorem original_weighted_mass (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(B H V T a : ℝ),
    1≤B → 0≤H → 0<V → 0<T → 0≤a → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤H) →
    (∀x∈S,primeProductNorm p x.firstCommon≤V) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤T) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^a)≤
      C*B^(1+eps)*H*V*T*(B^2*V*T)^(eps+a) := by
  obtain ⟨C,hC,hcount⟩ := original_source_card Jmax eps heps
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S B H V T a hB hH hV hT ha hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hcard := hcount p hp hinj Jo hJo S B H V T hB hH hV hT hS hb₁ hb₂ hactive hcommon hquot
  have hBp : 0<B := zero_lt_one.trans_le hB
  calc
    _ ≤ ∑_x∈S,(B^2*V*T)^a := Finset.sum_le_sum (fun x hx=>
      Real.rpow_le_rpow (primeProductNorm_pos p hp _).le
        (principalSupport_norm p hp extra negative x (hS x hx) (hextra x hx) B V T hBp.le hV.le
          (hb₁ x hx) (hb₂ x hx) (hcommon x hx) (hquot x hx)) ha)
    _ = (S.card:ℝ)*(B^2*V*T)^a := by simp
    _ ≤ (C*B^(1+eps)*H*V*T*(B^2*V*T)^eps)*(B^2*V*T)^a :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [mul_assoc,←Real.rpow_add (by positivity : 0<B^2*V*T)]

lemma weighted_mass_power (Z ell R Bfirst t eta eps a : ℝ) (hZ : 0<Z) :
    (Z^(ell+eta))^(1+eps)*Z^((R+eta)/2)*Z^(Bfirst+eta)*Z^(t+eta)*
      ((Z^(ell+eta))^2*Z^(Bfirst+eta)*Z^(t+eta))^(eps+a)=
    Z^(ell+R/2+Bfirst+t+7*eta/2+eps*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul_natCast hZ.le]
  repeat rw [←Real.rpow_add hZ]
  rw [←Real.rpow_mul hZ.le,←Real.rpow_add hZ]
  congr 1
  norm_num
  ring

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI

end Source2581

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPrincipalMassSource.lean; sha256: 66ec557f38e5109df6fe53f45b88df5accc85f32ba4c3bf9d11b8c2b513d360a -/
section Source2582
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma active_norm_of_square {ι : Type*} [DecidableEq ι] (p : ι→O)
    (A : Finset ι) (Z R eta : ℝ) (hZ : 0<Z)
    (hA : primeProductNorm p A≤Z^(R+eta)) :
    ‖eisEmbedding (∏i∈A,p i)‖≤Z^((R+eta)/2) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg hZ.le _)).mp
  have hh : (Z^((R+eta)/2))^2=Z^(R+eta) := by
    rw [←Real.rpow_mul_natCast hZ.le]
    congr 1
    norm_num
  rw [hh]
  exact hA

theorem original_weighted_source (Jmax : ℕ) (delta : ℝ) (hdelta : 0<delta) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(Z ell R Bfirst t eta a loss : ℝ),
    1≤Z → 0≤ell+eta → 0≤a →
    7*eta/2+delta*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)≤loss →
    (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(R+eta)) →
    (∀x∈S,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta)) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤Z^(t+eta)) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^a)≤
      C*Z^(ell+R/2+Bfirst+t+loss) := by
  obtain ⟨C,hC,hraw⟩ := original_weighted_mass Jmax delta hdelta
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z ell R Bfirst t eta a loss hZ hell ha hloss hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hh := hraw p hp hinj Jo hJo S (Z^(ell+eta)) (Z^((R+eta)/2))
    (Z^(Bfirst+eta)) (Z^(t+eta)) a (Real.one_le_rpow hZ hell)
    (Real.rpow_nonneg hZp.le _) (Real.rpow_pos_of_pos hZp _)
    (Real.rpow_pos_of_pos hZp _) ha hS hb₁ hb₂
    (fun x hx=>active_norm_of_square p _ Z R eta hZp (hactive x hx))
    hcommon hquot extra negative hextra
  apply hh.trans
  calc
    _ = C*( (Z^(ell+eta))^(1+delta)*Z^((R+eta)/2)*Z^(Bfirst+eta)*Z^(t+eta)*
      ((Z^(ell+eta))^2*Z^(Bfirst+eta)*Z^(t+eta))^(delta+a)) := by ring
    _ = C*Z^(ell+R/2+Bfirst+t+7*eta/2+delta*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)) := by
      rw [weighted_mass_power Z ell R Bfirst t eta delta a hZp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hC.le

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI

end Source2582

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPrincipalMassPrefactor.lean; sha256: 88afd12c6b53c761eb52a05b5c2ec3be84caeebb7a01431df40956b29431d53a -/
section Source2583
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def physicalPrincipalFactor (Z M r ell V delta A B R j t eta tau eps window : ℝ) : ℝ :=
  (Z^(firstKappa M r ell V delta A B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
    Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)*
    (Z^(r-A-B-t)*Real.exp window)^(1+eps)

lemma principal_nominal_identity (M r ell V delta A B R j t : ℝ) :
    firstKappa M r ell V delta A B R+firstPhysicalHeight M r ell V delta B j+
      (r-A-B-t)+(ell+R/2+B+t)=r+3*ell+V-B-j := by
  unfold firstKappa firstPhysicalHeight
  ring

lemma physical_principal_exact (Z M r ell V delta A B R j t eta tau eps window loss : ℝ)
    (hZ : 0<Z) :
    physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      Z^(ell+R/2+B+t+loss)=
    Real.exp (window*(1+eps))*
      Z^(r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss) := by
  have he : Real.exp ((9/2:ℝ)*(eta*Real.log Z))=Z^((9/2:ℝ)*eta) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  have hw : (Real.exp window)^(1+eps)=Real.exp (window*(1+eps)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  unfold physicalPrincipalFactor
  rw [he,Real.mul_rpow (Real.rpow_nonneg hZ.le _) (Real.exp_pos _).le,
    ←Real.rpow_mul hZ.le,hw]
  have hx : r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss=
    firstKappa M r ell V delta A B R+(9/2:ℝ)*eta+
    (firstPhysicalHeight M r ell V delta B j+12*eta+tau)+
    (r-A-B-t)*(1+eps)+(ell+R/2+B+t+loss) := by
    unfold firstKappa firstPhysicalHeight
    ring
  rw [hx]
  simp only [Real.rpow_add hZ]
  ring

theorem original_physical_weighted_source (Jmax : ℕ) (dsmall : ℝ) (hdsmall : 0<dsmall) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))
    (Z M r ell V delta A B R j t eta tau eps window pi : ℝ),
    1≤Z → 0≤ell+eta → 0≤eps → 0≤B → 0≤j →
    eps*(r-A-B-t)+7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*eps*(2*ell+B+t+4*eta)≤pi+eta/2 →
    (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(R+eta)) →
    (∀x∈S,primeProductNorm p x.firstCommon≤Z^(B+eta)) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤Z^(t+eta)) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^(2*eps))≤
      C*Real.exp (window*(1+eps))*Z^(r+3*ell+V+17*eta+tau+pi) := by
  obtain ⟨C,hC,hsource⟩ := original_weighted_source Jmax dsmall hdsmall
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z M r ell V delta A B R j t eta tau eps window pi hZ hell heps hB hj hcost hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  let loss := 7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*eps*(2*ell+B+t+4*eta)
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hh := hsource p hp hinj Jo hJo S Z ell R B t eta (2*eps) loss hZ hell
    (by positivity) (le_refl _) hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hP : 0≤physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window := by
    unfold physicalPrincipalFactor
    positivity
  calc
    _ ≤ physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      (C*Z^(ell+R/2+B+t+loss)) := mul_le_mul_of_nonneg_left hh hP
    _ = C*(physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      Z^(ell+R/2+B+t+loss)) := by ring
    _ = C*(Real.exp (window*(1+eps))*
      Z^(r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss)) := by
      rw [physical_principal_exact Z M r ell V delta A B R j t eta tau eps window loss hZp]
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ _) (by positivity)
      dsimp [loss]
      linarith

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI

end Source2583

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityMass.lean; sha256: b509b4d845c9d48d05f17c80a094bc157abdc6d7034849457b786cf6b1f5e60e -/
section Source2584
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
open InverseSecondPrincipalCaller InversePrincipalEnergy FirstCauchyArithmetic
local notation "O"=>ActualEisensteinCubic.O

theorem global_priority_weighted_branch (ε:ℝ)(hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      {Jo:ℕ}(original:Finset (Source ι Jo))(extra:CubeCoordinates ι→Finset ι)
      (negative:Bool)(Ψ:O→*ℂ)(m:O)(w:Source ι Jo→ℂ)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(B:ℝ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→
      (∀u,‖Ψ u‖≤1)→(∀x∈original,‖w x‖≤1)→0≤B→
      ∀U:(RayCharacter×RayCharacter)→FirstCoreIndex→Finset σ→Source ι Jo→ℝ,
      (∀r core J,J∈slots.powerset→∀x∈original,0≤U r core J x)→
      (∀r core J,J∈slots.powerset→∀x∈original,U r core J x≤B)→
      (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ∑x∈original,‖globalPriorityOuter p hg negative Ψ m r core w x‖*
          ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*U r core J x≤
      Cb*(4:ℝ)^slots.card*B*
        ∑x∈original,(primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε):=by
  obtain ⟨Cm,hCm,hmark⟩:=finite_primeMark_small_power ε hε
  let Cr:ℝ:=Fintype.card (RayCharacter×RayCharacter)
  let Cc:ℝ:=Fintype.card FirstCoreIndex
  refine ⟨(32*512)*Cr*Cc*coefficientBound*Cm^2,by
    have hr:0<Cr:=by dsimp [Cr];exact_mod_cast Fintype.card_pos
    have hc:0<Cc:=by dsimp [Cc];exact_mod_cast Fintype.card_pos
    have:=coefficientBound_pos;positivity,?_⟩
  intro ι σ _ _ p hp _ hg hcop Jo original extra negative Ψ m w slots lists a B hslots ha hΨ hw hB U hU0 hU
  let N:=fun x:Source ι Jo=>(primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε)
  have hn(x:Source ι Jo):0≤N x:=Real.rpow_nonneg (primeProductNorm_pos p hp _).le _
  have hm(J:Finset σ)(hJ:J∈slots.powerset)(x:Source ι Jo):
      ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2≤Cm^2*N x:=by
    have hj:=Finset.mem_powerset.mp hJ
    have hh:=hmark p hp hcop J lists a (fun i hi j hj' hij=>hslots (hj hi) (hj hj') hij)
      (fun i hi=>ha i (hj hi)) (wholeExtractedSupport (fun x=>extra x.cube) negative x)
    have he:((primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^ε)^2=N x:=by
      dsimp [N]
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      congr 1;ring
    exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (by rw [mul_pow,he])
  have hw'(r:RayCharacter×RayCharacter)(core:FirstCoreIndex)(x:Source ι Jo)(hx:x∈original):
      ‖globalPriorityOuter p hg negative Ψ m r core w x‖≤coefficientBound:=by
    rw [globalPriorityOuter,norm_mul]
    have ht:=priorityOuter_norm p hg x.cube negative Ψ m (fun _=>1) r core x.quotientSupport (by simp) (hΨ _)
    exact (mul_le_mul (hw x hx) ht (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  calc
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ∑x∈original,coefficientBound*(Cm^2*N x)*B:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro core hc
      apply Finset.sum_le_sum
      intro J hJ
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul (mul_le_mul (hw' r core x hx) (hm J hJ x) (sq_nonneg _) coefficientBound_pos.le)
        (hU r core J hJ x hx) (hU0 r core J hJ x hx) (mul_nonneg coefficientBound_pos.le (mul_nonneg (sq_nonneg Cm) (hn x)))
    _= _:=by
      have hsum:(∑x∈original,coefficientBound*(Cm^2*N x)*B)=
          coefficientBound*Cm^2*B*∑x∈original,N x:=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros;ring
      rw [hsum]
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      have he:((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card:=by rw [←pow_mul,pow_mul'];norm_num
      rw [←he]
      dsimp only [Cr,Cc,N]
      ring
end SevenEighths.InverseMoment

end

end OAI

end Source2584

/- Original source: OAI/NumberTheory/DirichletL/Descent/WholePriorityMass.lean; sha256: 356787fd31d84edc8c42c2f529f8110392fa0a4d190d5239ea294ae7e86a2b8c -/
section Source2585
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrincipalEnergy
local notation "O"=>ActualEisensteinCubic.O

theorem whole_priority_weighted_branch (ε:ℝ) (hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (pool:Finset ι) (b:CubeCoordinates ι) (C extra:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (selector:Finset ι→ℂ) (B:ℝ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → 0≤B →
      ∀U:(RayCharacter×RayCharacter)→Finset ι→FirstCoreIndex→Finset σ→ℝ,
      (∀r D core J,J∈slots.powerset → 0≤U r D core J) →
      (∀r D core J,J∈slots.powerset → U r D core J≤B) →
      (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
          ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit negative Ψ m D core‖*
          ∑J∈slots.powerset,‖primeMark J lists a
            ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)‖^2*U r D core J ≤
      Cb*(4:ℝ)^slots.card*B*
        (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p
          ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D))^(2*ε)):=by
  obtain ⟨Cm,hCm,hmark⟩:=finite_primeMark_small_power ε hε
  refine ⟨((32*512:ℝ)^2*512)*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hcop pool b C extra negative Ψ m slots lists a selector B hslots ha hΨ hB U hU0 hU
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  have hm (J:Finset σ) (hJ:J∈slots.powerset) (D:Finset ι) :
      ‖primeMark J lists a (A∪D)‖^2≤Cm^2*(primeProductNorm p (A∪D))^(2*ε) := by
    have hj:=Finset.mem_powerset.mp hJ
    have hh:=hmark p hp hcop J lists a (fun i hi j hj' hij=>hslots (hj hi) (hj hj') hij) (fun i hi=>ha i (hj hi)) (A∪D)
    have he:((primeProductNorm p (A∪D))^ε)^2=(primeProductNorm p (A∪D))^(2*ε):=by
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      congr 1;ring
    calc
      _≤(Cm*(primeProductNorm p (A∪D))^ε)^2:=pow_le_pow_left₀ (norm_nonneg _) hh 2
      _= _:=by rw [mul_pow,he]
  have hn (D:Finset ι) : 0≤primeProductNorm p (A∪D):=(primeProductNorm_pos p hp _).le
  calc
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
        ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative Ψ m D core‖*
        ((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*B)) := by
      gcongr with r hr D hD core hc
      calc
        _≤∑J∈slots.powerset,Cm^2*(primeProductNorm p (A∪D))^(2*ε)*B := by
          apply Finset.sum_le_sum
          intro J hJ
          exact mul_le_mul (hm J hJ D) (hU r D core J hJ) (hU0 r D core J hJ) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _))
        _= _:=by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*
        ((32*512)*((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*B))) := by
      gcongr with r hr D hD
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (firstCoreOuter_mass p hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D (hΨ _)) (mul_nonneg (pow_nonneg (by norm_num) _)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _)) hB))
    _= ((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*B*
      (∑r:RayCharacter×RayCharacter,‖crossCoeff r.1 r.2‖)*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm (s:=pool.powerset)]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring
    _≤ ((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*B*512*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · simpa only [Fintype.sum_prod_type] using crossCoeff_sum_norm_le
        · positivity
      · exact Finset.sum_nonneg (fun D hD=>mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hn D) _))
    _= _ := by
      have he:((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card:=by rw [←pow_mul,pow_mul'];norm_num
      rw [he]
      dsimp only [A]
      ring

end SevenEighths.InverseMoment

end

end OAI

end Source2585

/- Original source: OAI/NumberTheory/DirichletL/Descent/WholePriorityParentBounds.lean; sha256: 89c3d464167a7f20b23e886640888f1539860b432653992a49aa18accc871511 -/
section Source2586
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrincipalEnergy InversePrioritySecondSource
local notation "O"=>ActualEisensteinCubic.O

variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq σ] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem parent_residual_lists_subset {Jo:ℕ} (extra:CubeCoordinates ι→Finset ι)
    (negative:Bool) (lists:σ→Finset ι) (y:SecondParentSource ι Jo) (i:σ):
    residualLists p negative (fun i=>lists i\extra y.cube) y i⊆lists i:=
by
  intro k hk
  exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hk).1).1

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem parent_residual_lists_pairwise {Jo:ℕ} (extra:CubeCoordinates ι→Finset ι)
    (negative:Bool) (slots assigned:Finset σ) (lists:σ→Finset ι) (y:SecondParentSource ι Jo)
    (hslots:(slots:Set σ).PairwiseDisjoint lists):
    ((slots\assigned:Finset σ):Set σ).PairwiseDisjoint (residualLists p negative (fun i=>lists i\extra y.cube) y):=by
  intro i hi j hj hij
  exact (hslots (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij).mono
    (parent_residual_lists_subset p extra negative lists y i)
    (parent_residual_lists_subset p extra negative lists y j)

theorem priority_zero_parent_uniform (ε:ℝ) (hε:0<ε):
    ∃(s:Finset (ℕ×ℕ))(C:ℝ),0<C ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) →
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Y → (∀G E,0≤R G E) →
    ∀{Jo:ℕ}(y:SecondParentSource ι Jo),
      ‖priorityZeroParent p hg extra pool negative Ψ m slots assigned lists a
        (principalWindow om lo hi hlo hs negative t) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*
        Y*(X*Real.exp M)^(1+ε):=by
  obtain ⟨s,C,hC,hbound⟩:=marked_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop extra pool negative Ψ m slots assigned lists a hslots ha hΨ
    om lo hi hlo hs X M Y t R hX hhi hY hR Jo y
  have hpair:=parent_residual_lists_pairwise p extra negative slots assigned lists y hslots
  have hcoeff:∀i∈slots\assigned,∀k∈residualLists p negative (fun i=>lists i\extra y.cube) y i,‖a i k‖≤1:=by
    intro i hi k hk
    exact ha i (Finset.mem_sdiff.mp hi).1 k (parent_residual_lists_subset p extra negative lists y i hk)
  have hz:∀G∈pool.powerset,∀E∈G.powerset,(0:O)∈secondVariableCutoff p y R G E:=by
    intro G hG E hE
    exact zero_mem_childFrequencyBall _
      (mul_ne_zero (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _)) _ (hR G E)
  have hb:=hbound p hp hg hinj hcop (slots\assigned)
    (residualLists p negative (fun i=>lists i\extra y.cube) y) a hpair hcoeff ∅ pool Ψ hΨ
    (secondParentPuncture p m y) (secondParentLabel p y) (secondParentDivisor p y)
    (principalWindow om lo hi hlo hs negative t) rowMajorant X M Y hX hY
    (principalWindow_upper om lo hi hlo hs M hhi negative t) (secondVariableCutoff p y R) hz
    (fun _ _ _=>0) (by intros; simp)
  have hb':‖priorityZeroParent p hg extra pool negative Ψ m slots assigned lists a
      (principalWindow om lo hi hlo hs negative t) X Y R y‖≤_:=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hb
  simpa only [Finset.card_empty,pow_zero,mul_one,principalWindow_seminorm_zero,mul_assoc] using hb'

theorem priority_tail_parent_uniform (Lcap tau saving:ℝ)(hLcap:0≤Lcap)(htau:0<tau):
    ∃(s:Finset (ℕ×ℕ))(C:ℝ),0<C ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) →
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y Z t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
    ∀{Jo:ℕ}(y:SecondParentSource ι Jo),
      (∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p y) G E.val (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ m slots assigned lists a
        (principalWindow om lo hi hlo hs negative t) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving):=by
  obtain ⟨s,C,hC,hbound⟩:=InverseWholePriorityRapidTail.marked_rapid_tail Lcap tau saving hLcap htau
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc extra pool negative Ψ m slots assigned lists a hslots ha hΨ
    om lo hi hlo hs X M Y Z t R hX hhi hZ hY hscale hy hyi hx Jo y hR
  have hpair:=parent_residual_lists_pairwise p extra negative slots assigned lists y hslots
  have hcoeff:∀i∈slots\assigned,∀k∈residualLists p negative (fun i=>lists i\extra y.cube) y i,‖a i k‖≤1:=by
    intro i hi k hk
    exact ha i (Finset.mem_sdiff.mp hi).1 k (parent_residual_lists_subset p extra negative lists y i hk)
  exact hbound p hp hcop hg hinj hc pool Ψ hΨ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) (primeSubsetGenerator_ne_zero _ _)
    (slots\assigned) _ a hpair hcoeff om rowMajorant lo hi hlo hs negative t X M Y Z R
    hX hhi hZ hY hscale hy hyi hx hR

end SevenEighths.InverseMoment

end

end OAI

end Source2586

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityZero.lean; sha256: bd51829d4914f99a84a5e41234c342187d5d9da840ccfd1672ac0c7f0f654964 -/
section Source2587
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InversePrioritySecondSource InverseFirstPriorityParents InverseMomentWholePriorityParents
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
def globalPriorityZeroAggregate
    (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal](hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityZeroParent p hg extra pool negative
        (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots J lists a V X Y R (parent p x)‖

theorem global_priority_zero_aggregate (ε:ℝ)(hε:0<ε):
    ∃(s:Finset (ℕ×ℕ))(Czero:ℝ),0<Czero ∧
    ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      {Jo:ℕ}(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
      (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→(∀u,‖Ψ u‖≤1)→
      (∀x∈original,‖w x‖≤1)→
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X→hi≤Real.exp M→1≤Y→(∀G E,0≤R G E)→
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a
        (principalWindow om lo hi hlo hs negative t) X Y R≤
      Czero*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Y*(X*Real.exp M)^(1+ε)*
        ∑x∈original,(primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε):=by
  obtain ⟨s,Cp,hCp,hprincipal⟩:=priority_zero_parent_uniform ε hε
  obtain ⟨Cb,hCb,hmass⟩:=global_priority_weighted_branch ε hε
  refine ⟨s,Cb*Cp,mul_pos hCb hCp,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop Jo extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y t R hX hhi hY hR
  let B:=Cp*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*
    Y*(X*Real.exp M)^(1+ε)
  have hB:0≤B:=by dsimp [B];positivity
  have hh:=hmass p hp hg hcop original extra negative Ψ m w slots lists a B hslots ha hΨ hw hB
    (fun ray core J x=>‖priorityZeroParent p hg extra pool negative
      (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots J lists a
      (principalWindow om lo hi hlo hs negative t) X Y R (parent p x)‖)
    (by intros;positivity)
    (fun ray core J hJ x hx=>hprincipal p hp hg hinj hcop extra pool negative
      (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots J lists a hslots ha
      (fun u=>(firstCoreTwist_norm_le negative _ Ψ core u).trans (hΨ u))
      om lo hi hlo hs X M Y t R hX hhi hY hR (parent p x))
  convert hh using 1 <;> dsimp only [globalPriorityZeroAggregate,B] ; ring
end SevenEighths.InverseMoment

end

end OAI

end Source2587

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityZeroPhysical.lean; sha256: b9775c4627837080fde2500c2c00eeb28333e8613654eae5696458ad085af56d -/
section Source2588
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass
local notation "O"=>ActualEisensteinCubic.O

theorem global_priority_zero_physical (ε:ℝ)(hε:0<ε)(Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall):
    ∃(s:Finset (ℕ×ℕ))(Czero:ℝ),0<Czero ∧
    ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (Jo:ℕ),Jo≤Jmax→∀(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)
      (original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)(negative:Bool)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→(∀u,‖Ψ u‖≤1)→
      (∀x∈original,‖w x‖≤1)→
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (Z M r ell V delta A B Ractive j t eta tau window pi height:ℝ)(R:Finset ι→Finset ι→ℝ),
      1≤Z→0≤ell+eta→0≤B→0≤j→
      ε*(r-A-B-t)+7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*ε*(2*ell+B+t+4*eta)≤pi+eta/2→
      (∀x∈original,SourceValid p x)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(B+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(t+eta))→
      (∀x∈original,extra x.cube⊆x.cube.support)→
      hi≤Real.exp window→1≤Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)→(∀G E,0≤R G E)→
      (Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a
        (principalWindow om lo hi hlo hs negative height) (Z^(r-A-B-t))
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) R≤
      Czero*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+ε))*
        Z^(r+3*ell+V+17*eta+tau+pi):=by
  obtain ⟨s,Cp,hCp,hprincipal⟩:=global_priority_zero_aggregate ε hε
  obtain ⟨Cm,hCm,hmass⟩:=original_physical_weighted_source Jmax dsmall hdsmall
  refine ⟨s,Cp*Cm,mul_pos hCp hCm,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop Jo hJo extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs Z M r ell V delta A B Ractive j t eta tau window pi height R
    hZ hell hB hj hcost hsource hc₁ hc₂ hactive hcommon hquot hextra hhi hY hR
  have hz:0<Z:=zero_lt_one.trans_le hZ
  let P:=Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let Q:=Cp*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
    (SchwartzMap.seminorm ℝ 0 0 om)^2
  have hP:0≤P:=by dsimp [P];positivity
  have hQ:0≤Q:=by dsimp [Q];positivity
  have he:=mul_le_mul_of_nonneg_left (hprincipal p hp hg hinj hcop extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs (Z^(r-A-B-t)) window
    (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) height R (by positivity) hhi hY hR) hP
  have hm:=hmass p hp hinj Jo hJo original Z M r ell V delta A B Ractive j t eta tau ε window pi
    hZ hell hε.le hB hj hcost hsource hc₁ hc₂ hactive hcommon hquot extra negative hextra
  have hsupp(x:Source ι Jo):wholeExtractedSupport (fun x=>extra x.cube) negative x=principalSupport extra negative x:=by
    simp only [wholeExtractedSupport,extractedSupport,principalSupport,Finset.union_assoc]
  simp_rw [hsupp] at he
  apply he.trans
  calc
    _=Q*(physicalPrincipalFactor Z M r ell V delta A B Ractive j t eta tau ε window*
      ∑x∈original,(primeProductNorm p (principalSupport extra negative x))^(2*ε)):=by
      dsimp [Q,P,physicalPrincipalFactor];ring
    _≤Q*(Cm*Real.exp (window*(1+ε))*Z^(r+3*ell+V+17*eta+tau+pi)):=mul_le_mul_of_nonneg_left hm hQ
    _= _:=by dsimp [Q];ring
end SevenEighths.InverseMoment

end

end OAI

end Source2588

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityRays.lean; sha256: b1ce98166a2232d803242503d19b460c90f2f5ab55cc32d00c78bd667d71839f -/
section Source2589
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_retained_all_rays
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
,
    let source:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
        ∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,Cbin,hC,hCbin,he⟩:=
    global_priority_retained_moving_radius (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C*(512*32^2),Cbin,by positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff source Ψ₀
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:= (1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*(1+Cbin*Real.log Z)^4*
    Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  let S:SecondRayIndex→ℂ:=fun z=>(Y:ℂ)*secondRayCoefficient z *
      ∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x
  have hP:0≤P:=by dsimp [P];positivity
  have hH:0≤H:=by dsimp [H];positivity
  have hz (z:SecondRayIndex):P*‖S z‖≤C*A*H*‖secondRayCoefficient z‖:=by
    have h:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a cutoff z
      Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
      haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass
      (hleft z) (hright z)
    convert h using 1 ; dsimp only [P,S,H] ; ring
  calc
    _≤P*∑z:SecondRayIndex,‖S z‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) hP
    _=∑z:SecondRayIndex,P*‖S z‖:=Finset.mul_sum _ _ _
    _≤∑z:SecondRayIndex,C*A*H*‖secondRayCoefficient z‖:=Finset.sum_le_sum (fun z _=>hz z)
    _=C*A*H*(∑z:SecondRayIndex,‖secondRayCoefficient z‖):=(Finset.mul_sum _ _ _).symm
    _≤C*A*H*(512*32^2):=mul_le_mul_of_nonneg_left secondRayCoefficient_mass (by positivity)
    _= _:=by dsimp [H];ring

end SevenEighths.InverseMoment

end

end OAI

end Source2589

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityAggregate.lean; sha256: 3736c72d9064ac21eee309f8a787c60cc675f5de4d6b438042e2b110db3ed965 -/
section Source2590
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
def globalPriorityRetainedAggregate
    (p:ι→Eis)[∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hp:∀i,p i≠0)(hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    {Jo:ℕ}(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))(w:InverseFirstPriorityParents.Source ι Jo→ℂ)
    (negative:Bool)(Ψ:Eis→*ℂ)(m:Eis)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z*
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) (fun _=>R),
        globalPriorityWeight p hg negative Ψ m ray core w J a x*
        wholeRow p hp hcop hg extra pool negative (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a V X Y z x‖

theorem global_priority_retained_aggregate
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff);
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤eta ∧
      2≤Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤Z ∧
      1≤b ∧
      b≤Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2))) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityRetainedAggregate p hg hp hcop extra pool original w
          negative Ψ m slots lists a (principalWindow om lo hi hlo hsupport negative t) X Y cutoff ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,Cbin,hC,hCbin,he⟩:=
    global_priority_retained_all_rays (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ J K εmass hεmass
  let Ctot:=(32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*
    (Fintype.card FirstCoreIndex:ℝ)*C
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,Ctot,Cbin,by dsimp [Ctot];positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hslots hA hdata
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:=C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  have hb (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ)(ha:assigned⊆slots):
    P*‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖≤H:=by
    obtain ⟨haassigned,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hcube₁,hcube₂,hactive,hj,hquot,hΨ,
      ha₁,ha₂,hlabels,ho,hslots₁,hslots₂,hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,hleft,hright⟩:=hdata ray core assigned ha
    exact he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a (fun _=>cutoff)
      Y (R assigned) L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t (labels assigned) A
      haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA' hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hZ:1<Z:=(hdata 1 1 ∅ (Finset.empty_subset _)).2.2.2.1
  have hH:0≤H:=by dsimp [H];positivity
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  let S:(RayCharacter×RayCharacter)→FirstCoreIndex→Finset σ→ℝ:=fun ray core assigned=>‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖
  change ∀ray core assigned, assigned⊆slots → P*S ray core assigned≤H at hb
  change P*((32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,S ray core assigned)≤_
  calc
    _=(32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,P*S ray core assigned:=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hr
      apply Finset.sum_congr rfl
      intro core hc
      apply Finset.sum_congr rfl
      intro assigned ha
      ring
    _≤(32*512)*(2:ℝ)^slots.card*∑_ray:RayCharacter×RayCharacter,∑_core:FirstCoreIndex,∑_assigned∈slots.powerset,H:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun ray _=>Finset.sum_le_sum fun core _=>Finset.sum_le_sum fun assigned ha=>hb ray core assigned (Finset.mem_powerset.mp ha)
    _=(32*512)*(4:ℝ)^slots.card*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)^slots.card=(2:ℝ)^slots.card*(2:ℝ)^slots.card by rw [←mul_pow];norm_num]
      ring
    _≤(32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by gcongr
    _= _:=by dsimp [Ctot,H];ring
end SevenEighths.InverseMoment

end

end OAI

end Source2590

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityTailMass.lean; sha256: 11018780bacb3284224d0b0e0b7a31174883541abc15f70d543663477bcce6c5 -/
section Source2591
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open InverseMomentGlobalPrincipalMass
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem original_tail_mass (Jmax : ℕ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(Z L : ℝ),
    1≤Z → 0≤L → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^L) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^L) →
    (∀x∈S,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^L) →
    (∀x∈S,primeProductNorm p x.firstCommon≤Z^L) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤Z^L) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,primeProductNorm p (principalSupport extra negative x))≤C*Z^(13*L) := by
  obtain ⟨C,hC,hraw⟩ := original_weighted_mass Jmax 1 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z L hZ hL hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hh := hraw p hp hinj Jo hJo S (Z^L) (Z^L) (Z^L) (Z^L) 1
    (Real.one_le_rpow hZ hL) (by positivity) (by positivity) (by positivity)
    (by norm_num) hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  simp only [Real.rpow_one] at hh
  apply hh.trans_eq
  have he : Z^(13*L)=(Z^L)^13 := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    norm_num
    ring
  rw [he]
  norm_num
  ring

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI

end Source2591

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityTailCollapse.lean; sha256: 6c3409b80e5fb8e354c1992290552395e6137283d7828f3798b1b97cd5a0d1d6 -/
section Source2592
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

lemma tail_forget (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι→Finset ι→ℝ)
    (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R
      (forgetAppended (Jo:=Jo) y)=
    priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R y := rfl

theorem original_paired_tail (hp : ∀i,p i≠0)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (source : Finset (Source ι Jo))
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι→Finset ι→ℝ) :
    (∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
      coefficient p J a w y*priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R y)=
    ∑x∈source,w x*(‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R (parent p x) := by
  rw [wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj]
  simp only [tail_forget]

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI

end Source2592

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityTail.lean; sha256: 93a7dd4c3198789fbbcf03c2b6ea5adde906da8f69890d51a12fe7af8fdb3fcc -/
section Source2593
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseWholePriorityRetainedSource FirstCauchyArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem global_parent_tail_rapid (Jmax : ℕ) (Lcap tau saving : ℝ)
    (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃(s : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀{ι σ : Type*}[DecidableEq ι][DecidableEq σ]
      (p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Jo : ℕ),Jo≤Jmax → ∀(extra : CubeCoordinates ι→Finset ι)(pool : Finset ι)
      (source : Finset (Source ι Jo))(negative : Bool)(Ψ : O→*ℂ)(m : O)
      (ray : RayCharacter×RayCharacter)(core : FirstCoreIndex)
      (w : Source ι Jo→ℂ)(slots J : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ),
      J⊆slots → (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) → (∀x∈source,‖w x‖≤1) →
      ∀(om : 𝓢(ℝ,ℂ))(lo hi : ℝ)(hlo : 0<lo)(hs : Function.support om⊆Set.Icc lo hi)
      (X M Y Z height : ℝ)(R : Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀x∈source,SourceValid p x) → (∀x∈source,extra x.cube⊆x.cube.support) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.firstCommon≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.quotientSupport≤Z^Lcap) →
      (∀x∈source,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := priority_tail_parent_uniform Lcap tau (saving+13*Lcap) hLcap htau
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power (1/2) (by norm_num)
  obtain ⟨Cs,hCs,hmass⟩ := original_tail_mass Jmax
  have hCb : 0<coefficientBound := coefficientBound_pos
  refine ⟨s,coefficientBound*Cm^2*Ct*Cs,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc Jo hJo extra pool source negative Ψ m ray core w slots J lists a
    hJ hslots ha hΨ hw om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  let Ψ₀ := firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  let V := principalWindow om lo hi hlo hs negative height
  let Q := (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2
  let T := Ct*Q*Z^(-(saving+13*Lcap))
  have hT : 0≤T := by dsimp [T,Q];positivity
  have hΨ₀ : ∀u,‖Ψ₀ u‖≤1 := fun u=>(firstCoreTwist_norm_le negative _ Ψ core u).trans (hΨ u)
  have hout (x : Source ι Jo) (hx : x∈source) :
      ‖globalPriorityOuter p hg negative Ψ m ray core w x‖≤coefficientBound := by
    rw [globalPriorityOuter,norm_mul]
    exact (mul_le_mul (hw x hx)
      (priorityOuter_norm p hg x.cube negative Ψ m (fun _=>1) ray core x.quotientSupport
        (by simp) (hΨ _)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hm (x : Source ι Jo) :
      ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2≤
        Cm^2*primeProductNorm p (principalSupport extra negative x) := by
    have hh := hmark p hp hcop J lists a
      (fun i hi j hj hij=>hslots (hJ hi) (hJ hj) hij) (fun i hi=>ha i (hJ hi))
      (principalSupport extra negative x)
    have he : ((primeProductNorm p (principalSupport extra negative x))^(1/2:ℝ))^2=
        primeProductNorm p (principalSupport extra negative x) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      norm_num
    have hsupp : wholeExtractedSupport (fun x=>extra x.cube) negative x=principalSupport extra negative x := by
      simp only [wholeExtractedSupport,extractedSupport,principalSupport,Finset.union_assoc]
    rw [hsupp]
    exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (by rw [mul_pow,he])
  have ht (x : Source ι Jo) (hx : x∈source) :
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots J lists a V X Y R (parent p x)‖≤T := by
    simpa only [T,Q,mul_assoc] using htail p hp hg hinj hcop hc extra pool negative Ψ₀ m slots J lists a
      hslots ha hΨ₀ om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
      (parent p x) (hR x hx)
  have hmass₀ := hmass p hp hinj Jo hJo source Z Lcap hZ hLcap hsource hb₁ hb₂ hactive hcommon hquot extra negative hextra
  rw [original_paired_tail p hg hp hinj]
  calc
    _ ≤ ∑x∈source,‖globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots J lists a V X Y R (parent p x)‖ := norm_sum_le _ _
    _ ≤ ∑x∈source,coefficientBound*(Cm^2*primeProductNorm p (principalSupport extra negative x))*T := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (mul_le_mul (hout x hx) (hm x) (sq_nonneg _) coefficientBound_pos.le)
        (ht x hx) (norm_nonneg _)
        (mul_nonneg hCb.le (mul_nonneg (sq_nonneg _) (primeProductNorm_pos p hp _).le))
    _ = coefficientBound*Cm^2*T*(∑x∈source,primeProductNorm p (principalSupport extra negative x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ coefficientBound*Cm^2*T*(Cs*Z^(13*Lcap)) :=
      mul_le_mul_of_nonneg_left hmass₀ (by positivity)
    _ = _ := by
      have he : Z^(-(saving+13*Lcap))*Z^(13*Lcap)=Z^(-saving) := by
        rw [←Real.rpow_add hz]
        congr 1
        ring
      dsimp only [T,Q]
      calc
        _ = coefficientBound*Cm^2*Ct*Cs*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
          (SchwartzMap.seminorm ℝ 0 0 om)^2*(Z^(-(saving+13*Lcap))*Z^(13*Lcap)) := by ring
        _ = _ := by rw [he]

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI

end Source2593

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityTailAggregate.lean; sha256: eae2b18515136aff68911dd7781812b5b550660098b3335090c1e2a002f9b3ff -/
section Source2594
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseWholePriorityRetainedSource FirstCauchyArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem global_parent_tail_aggregate_rapid (Jmax : ℕ) (Lcap tau saving : ℝ)
    (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃(s : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀{ι σ : Type*}[DecidableEq ι][DecidableEq σ]
      (p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Jo : ℕ),Jo≤Jmax → ∀(extra : CubeCoordinates ι→Finset ι)(pool : Finset ι)
      (source : Finset (Source ι Jo))(negative : Bool)(Ψ : O→*ℂ)(m : O)
      (w : Source ι Jo→ℂ)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) → (∀x∈source,‖w x‖≤1) →
      ∀(om : 𝓢(ℝ,ℂ))(lo hi : ℝ)(hlo : 0<lo)(hs : Function.support om⊆Set.Icc lo hi)
      (X M Y Z height : ℝ)(R : Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀x∈source,SourceValid p x) → (∀x∈source,extra x.cube⊆x.cube.support) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.firstCommon≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.quotientSupport≤Z^Lcap) →
      (∀x∈source,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      (32*512)*(2:ℝ)^slots.card*
      (∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖)≤
      C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,C,hC,hbound⟩ := global_parent_tail_rapid Jmax Lcap tau saving hLcap htau
  let N : ℝ := (Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)
  have hN : 0<N := by dsimp [N];positivity
  refine ⟨s,(32*512)*N*C,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  let B := C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
    (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving)
  have hsum : (∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
      ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖)
      ≤N*(2:ℝ)^slots.card*B := by
    calc
      _ ≤ ∑_ray:RayCharacter×RayCharacter,∑_core:FirstCoreIndex,∑_J∈slots.powerset,B := by
        apply Finset.sum_le_sum
        intro ray hr
        apply Finset.sum_le_sum
        intro core hc₀
        apply Finset.sum_le_sum
        intro J hJ
        exact hbound p hp hg hinj hcop hc Jo hJo extra pool source negative Ψ m ray core w slots J lists a
          (Finset.mem_powerset.mp hJ) hslots ha hΨ hw om lo hi hlo hs X M Y Z height R
          hX hhi hZ hY hscale hy hyi hXcap hsource hextra hb₁ hb₂ hactive hcommon hquot hR
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        dsimp [N]
        ring
  apply (mul_le_mul_of_nonneg_left hsum (by positivity : 0≤(32*512)*(2:ℝ)^slots.card)).trans_eq
  have he : ((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card := by
    rw [←pow_mul,pow_mul']
    norm_num
  dsimp [B]
  calc
    _ = (32*512)*N*C*((2:ℝ)^slots.card)^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
      (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by ring
    _ = _ := by rw [he]

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI

end Source2594

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityTailPhysical.lean; sha256: 503672b90464c775e23b4fe655bf92a267d97a6f9b1aea89c730d1ad96e6ee57 -/
section Source2595
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseWholePriorityRetainedSource FirstCauchyArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem global_physical_tail_rapid (Jmax : ℕ) (Lcap tau saving : ℝ)
    (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃(s : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀{ι σ : Type*}[DecidableEq ι][DecidableEq σ]
      (p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Jo : ℕ),Jo≤Jmax → ∀(extra : CubeCoordinates ι→Finset ι)(pool : Finset ι)
      (source : Finset (Source ι Jo))(negative : Bool)(Ψ : O→*ℂ)(m : O)
      (w : Source ι Jo→ℂ)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) → (∀x∈source,‖w x‖≤1) →
      ∀(om : 𝓢(ℝ,ℂ))(lo hi : ℝ)(hlo : 0<lo)(hs : Function.support om⊆Set.Icc lo hi)
      (X M Y Z height kappa eta : ℝ)(R : Finset ι→Finset ι→ℝ),
      kappa+(9/2:ℝ)*eta≤Lcap →
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀x∈source,SourceValid p x) → (∀x∈source,extra x.cube⊆x.cube.support) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.firstCommon≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.quotientSupport≤Z^Lcap) →
      (∀x∈source,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      (Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*((32*512)*(2:ℝ)^slots.card*
      (∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖))≤
      C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,C,hC,hbound⟩ := global_parent_tail_aggregate_rapid Jmax Lcap tau (saving+Lcap) hLcap htau
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height kappa eta R hkappa hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hh := hbound p hp hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have he : Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z))=Z^(kappa+(9/2:ℝ)*eta) := by
    rw [Real.rpow_add hz,Real.rpow_def_of_pos hz ((9/2:ℝ)*eta)]
    congr 2
    ring
  have hP : Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z))≤Z^Lcap := by
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hZ hkappa
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans
  calc
    _ ≤ Z^Lcap*(C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
      (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-(saving+Lcap))) :=
      mul_le_mul_of_nonneg_right hP (by positivity)
    _ = _ := by
      have he₂ : Z^Lcap*Z^(-(saving+Lcap))=Z^(-saving) := by
        rw [←Real.rpow_add hz]
        congr 1
        ring
      calc
        _ = C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
          (SchwartzMap.seminorm ℝ 0 0 om)^2*(Z^Lcap*Z^(-(saving+Lcap))) := by ring
        _ = _ := by rw [he₂]

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI

end Source2595

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityFullBranches.lean; sha256: fe0d3af2cfaa7db311f942d12dcdddca0971b1bd27e2eb7cff9964a8080ef331 -/
section Source2596
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_priority_slice_full_tail
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (Source ι Jo)) (w:Source ι Jo→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots assigned (fun i=>lists i\extra x.cube) a om X t Y ray core (parent p x)‖≤
    (∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖)+
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x‖+
    ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖ := by
  intro V Ψ₀ parents source
  rw [global_priority_signed_branches p hg hp hcop hinj hc hpr extra pool original w negative
    Ψ m ray core slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  have hn (H:Source ι Jo→ℂ):
      ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
        (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*H x‖≤
      ∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
        ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*‖H x‖:=by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro x hx
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hn _) (le_refl _))) (le_refl _))

end SevenEighths.InverseMoment

end

end OAI

end Source2596

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityFullAggregate.lean; sha256: 10b14980260cf99bdcb7de59f18fae315c2fbcac85630526182dcad175d3cee6 -/
section Source2597
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InversePrioritySecondSource InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InverseMomentGlobalPriorityTail
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal](hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
def globalPriorityOriginalEnergy (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
        a om X t Y ray core (parent p x)).re

def globalPriorityTailAggregate (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) original negative J lists,
      coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
      priorityTailParent p hg hp hinj extra pool negative
        (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
        m slots J lists a V X Y R y‖

theorem global_priority_three_branches
    (hp:∀i,p i≠0)(hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ)(hX:0<X)(hY:0<Y)(R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t;
    globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y≤
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a V X Y R+
      globalPriorityRetainedAggregate p hg hp hcop extra pool original w negative Ψ m slots lists a V X Y R+
      globalPriorityTailAggregate p hg hp hinj extra pool original w negative Ψ m slots lists a V X Y R:=by
  dsimp only
  unfold globalPriorityOriginalEnergy globalPriorityZeroAggregate globalPriorityRetainedAggregate globalPriorityTailAggregate
  rw [←mul_add,←mul_add]
  simp only [←Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro ray hray
  apply Finset.sum_le_sum
  intro core hcore
  apply Finset.sum_le_sum
  intro J hJ
  have hb:=global_priority_slice_full_tail p hg hp hcop hinj hc hpr extra pool original w negative Ψ m
    ray core slots J lists a om lo hi hlo hs X t Y hX hY R
  dsimp only at hb
  rw [original_paired_tail p hg hp hinj]
  exact (Complex.re_le_norm _).trans hb
end SevenEighths.InverseMoment

end

end OAI

end Source2597

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalCanonicalEnergy.lean; sha256: 9f1acef0dc3b7a6796e07fe1471c8af755782e264e79f2d8e7bf8bfba8c28a02 -/
section Source2598
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_canonical_to_original_priority
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(extra:CubeCoordinates ι→Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑x∈outer,firstCanonicalSecondEnergy p hp hg hinj pool x.cube x.firstCommon
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
      (fun U=>primeMark slots lists a (extra x.cube∪U)) (selector x) om X t Y) ≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool (globalParentSource outer pool selector)
      (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y := by
  apply le_trans (Finset.sum_le_sum (fun x hx=>
    first_actual_second_whole_cube_priority p hp hg hinj hc pool x.cube x.firstCommon (extra x.cube)
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
      slots lists a (selector x) om X t Y hY))
  exact le_of_eq (global_second_energy_source p hg hp hinj outer pool selector houter extra
    negative Ψ m slots lists a om X t Y)

theorem original_canonical_to_global_priority
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(selector:FirstOriginalOuter ι→Finset ι→ℂ)
    (extra:CubeCoordinates ι→Finset ι)(negative:Bool)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑k∈firstOriginalOuter pool Q,firstCanonicalSecondEnergy p hp hg hinj pool k.1 k.2.1
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2)
      (fun U=>primeMark slots lists a (extra k.1∪U)) (selector k) om X t Y) ≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool
      (InverseFirstGlobalParents.originalParentSource pool Q selector)
      (fun x=>(‖selector (InverseFirstGlobalParents.toOriginal x) x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y := by
  apply le_trans (Finset.sum_le_sum (fun k hk=>
    first_actual_second_whole_cube_priority p hp hg hinj hc pool k.1 k.2.1 (extra k.1)
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2)
      slots lists a (selector k) om X t Y hY))
  exact le_of_eq (InverseFirstGlobalParents.original_second_energy_source p hg hp hinj pool Q
    selector extra negative Ψ m slots lists a om X t Y)

end SevenEighths.InverseMoment

end

end OAI

end Source2598

/- Original source: OAI/NumberTheory/DirichletL/Descent/OriginalCellPriority.lean; sha256: f6fc8a39fe0473e144f5de16797e48cf83b2040fd76eebce1470139f5f6eab63 -/
section Source2599
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
open InverseFirstPriorityParents InverseFirstGlobalParents
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]

def originalSubsetSource (outer:Finset (FirstOriginalOuter ι)):Finset (Source ι 0):=
  outer.image ofOriginal

theorem original_subset_canonical_priority
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (outer:Finset (FirstOriginalOuter ι))(pool:Finset ι)
    (selector:FirstOriginalOuter ι→Finset ι→ℂ)(extra:CubeCoordinates ι→Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj pool k.1 k.2.1
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2)
      (fun U=>primeMark slots lists a (extra k.1∪U)) (selector k) om X t Y) ≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool
      (globalParentSource (originalSubsetSource outer) pool (originalSelector selector))
      (fun x=>(‖selector (toOriginal x) x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y:=by
  have hempty:∀x∈originalSubsetSource outer,x.quotientSupport=∅:=by
    intro x hx
    obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hx
    rfl
  have he:=global_canonical_to_original_priority p hp hg hinj hc
    (originalSubsetSource outer) pool (originalSelector selector) hempty extra
    negative Ψ m slots lists a om X t Y hY
  rw [show originalSubsetSource outer=outer.image ofOriginal from rfl,
    Finset.sum_image (fun _ _ _ _ h=>ofOriginal_injective h)] at he
  have hs (k:FirstOriginalOuter ι): originalSelector selector (ofOriginal k)=selector k :=
    originalSelector_ofOriginal_fun selector k
  simp_rw [hs] at he
  simpa only [originalSubsetSource,ofOriginal,originalSelector,toOriginal,eraseFirstQuotient] using he

theorem original_cell_parent_source
    (p:ι→O)(pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (selector:FirstOriginalOuter ι→Finset ι→ℂ)
    (k:InverseMomentFirstChildWindows.SourceIndex)(l:ℕ):
    globalParentSource (originalSubsetSource (InverseFirstGlobalCaps.outerCell p pool Q k))
      pool (originalSelector (fun x=>InverseMomentFirstChildWindows.commonSelector p (selector x) l))=
      InverseFirstGlobalCaps.parentCell p pool Q selector k l:=by
  ext x
  rw [InverseFirstGlobalCaps.mem_parentCell]
  simp only [globalParentSource,Finset.mem_biUnion,originalSubsetSource,Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨o,ho,rfl⟩,D,⟨hD,hs⟩,he⟩
    exact ⟨o,ho,D,hD,by simpa using hs,he⟩
  · rintro ⟨o,ho,D,hD,hs,he⟩
    exact ⟨ofOriginal o,⟨o,ho,rfl⟩,D,⟨hD,by simpa using hs⟩,he⟩

theorem original_cell_canonical_priority
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(selector:FirstOriginalOuter ι→Finset ι→ℂ)
    (k:InverseMomentFirstChildWindows.SourceIndex)(l:ℕ)
    (extra:CubeCoordinates ι→Finset ι)(negative:Bool)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑o∈InverseFirstGlobalCaps.outerCell p pool Q k,
      firstCanonicalSecondEnergy p hp hg hinj pool o.1 o.2.1 negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) o.2.2)
        (fun U=>primeMark slots lists a (extra o.1∪U))
        (InverseMomentFirstChildWindows.commonSelector p (selector o) l) om X t Y)≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool
      (InverseFirstGlobalCaps.parentCell p pool Q selector k l)
      (fun x=>(‖InverseMomentFirstChildWindows.commonSelector p (selector (toOriginal x)) l x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y:=by
  have he:=original_subset_canonical_priority p hp hg hinj hc
    (InverseFirstGlobalCaps.outerCell p pool Q k) pool
    (fun x=>InverseMomentFirstChildWindows.commonSelector p (selector x) l) extra negative Ψ m slots lists a om X t Y hY
  rwa [original_cell_parent_source] at he

end SevenEighths.InverseMoment

end

end OAI

end Source2599
