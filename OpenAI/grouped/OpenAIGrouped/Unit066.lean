import OpenAIGrouped.Unit065
import OpenAIGrouped.Unit062
import OpenAIGrouped.Unit064
import OpenAIGrouped.Unit033
import OpenAIGrouped.Unit057
import OpenAIGrouped.Unit061
import OpenAIGrouped.Unit042
import OpenAIGrouped.Unit041
import OpenAIGrouped.Unit038
import OpenAIGrouped.Unit040
import OpenAIGrouped.Unit039
import OpenAIGrouped.Unit060

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Descent/PriorityCellEnergyWindowOrderUniform.lean; sha256: d956336744d31f005ccb6c33abe5ab072f331c2e27cab2955d4dde7a27ba4561 -/
section Source2640
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
theorem actual_priority_cell_recursive_window_order_uniform_types
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (Aker K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C : ℝ,0 ≤ C ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source) (d:InverseSecondSourceBlocks.BlockIndex)
    (_hcell:∀x∈source,InverseSecondSourceBlocks.index p x=d),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y R L Z X Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ x∈source,primeProductNorm p x.second.sourceCommon ≤ Z^(gcount+eta)) →
      (∀ x∈source,Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+Vlabel) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+Vlabel) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^Aker)) := by
  let g:=priorityLogWindow om lo hi hlo hsupport negative
  let mg:=|Real.log lo|+|Real.log hi|
  have hm:0≤mg:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hg:Function.support g⊆Set.Icc (-mg) mg:=priorityLogWindow_support om lo hi hlo hsupport negative
  have hcg:Function.support (conjugateProfile g)⊆Set.Icc (-mg) mg:=by
    intro x hx
    apply hg
    simpa only [Function.mem_support,conjugateProfile_apply,star_ne_zero] using hx
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_second_fixed_block_recursive_window_order_uniform_types  (conjugateProfile g) g Φ mg mg 1
      (fun _=>1) (fun _=>2) B₀ hm hm (le_refl 1) (fun _=>zero_lt_one)
      (fun _=>by norm_num) hB₀ hcg hg Aker K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩:=hordered J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg₀ hpr hinj hc Jo source hs d hcell pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X Vlabel εchild ell Ractive j tcount gcount theta eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY hrows hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hblock:=actual_source_block_ratios p hp source d hcell
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx))
  have he:=henergy p hp hcop hg₀ hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    (scales d 0) (scales d 1) (scales d 2) (scales d 3) Y R L Z
    (secondCellColumnExponent Z X d) Vlabel εchild ell Ractive j tcount gcount theta eta ρ
    1 1 (-priorityHeight negative t) (priorityHeight negative t) w labels A
    hd₁ hd₂ hρ (le_refl 1) (le_refl 1) (le_refl 1) (le_refl 1) hL (lt_trans zero_lt_one hZ)
    (dyadScale_pos _) (dyadScale_pos _) (dyadScale_pos _) (dyadScale_pos _)
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one hZ) _) hY hrows hblock
    hcube₁ hcube₂ hactive hj hquot hcommon hdiv hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  rw [second_cell_physical_scale Z X d hZ hX] at he
  refine le_trans (le_of_eq (congrArg (fun v : ℂ => ‖(Y : ℂ) * secondRayCoefficient z * v‖) ?_)) he
  apply Finset.sum_congr rfl
  intro x _hx
  exact congrArg (fun v : ℂ => (w x * actualSecondSignedWeight p hp hcop hg₀ Ψ
    (m * ConcretePrimeRowBridge.idealGenerator x.quotient) z x) * v)
    (actual_priority_profile_common p hp hcop hg₀ pool (secondInheritedProfile p x Ψ m z)
      slots₁ slots₂ _ _ a₁ a₂ om lo hi hlo hsupport negative t Φ Y X hX)

end SevenEighths.InverseMoment

end

end OAI

end Source2640

/- Original source: OAI/NumberTheory/DirichletL/Descent/PriorityMovingRadiusWindowOrderUniform.lean; sha256: 9927a60b88ef0947dcc26ab882864996d9e4ee1a3131242af0d73688624998ff -/
section Source2641
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
theorem actual_priority_source_moving_radius_window_order_uniform_types
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C : ℝ,0 ≤ C ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
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
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      ∑d∈keys p source,(Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+(Vlabel d))+εchild))*
          Z^((ell+Ractive/2-j+tcount+(secondCellExponent Z d 0)-(secondCellExponent Z d 1)+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^0)) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_priority_cell_recursive_window_order_uniform_types  om Φ lo hi hlo hsupport negative B₀ hB₀ 0 K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩:=hordered J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hz:0<Z:=zero_lt_one.trans hZ
  have hk:∀x∈source,x.second.frequency≠0:=fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)
  rw [physical_source_partition p hp hcop hg source pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ w]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  have hin : cell p source d⊆source:=cell_subset p source d
  have hcommon:∀x∈cell p source d,primeProductNorm p x.second.sourceCommon≤Z^(secondCellExponent Z d 0+eta):=by
    intro x hx
    have hr:primeProductNorm p x.second.sourceCommon≤2*scales d 0:=
      (div_le_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).2.le
    apply hr.trans
    rw [Real.rpow_add hz,second_cell_scale_rpow Z d 0 hZ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbin (show 0≤scales d 0 from (dyadScale_pos _).le)
  have hdiv:∀x∈cell p source d,Z^(secondCellExponent Z d 1-eta)≤primeProductNorm p x.second.divisor:=by
    intro x hx
    have hr:scales d 1≤primeProductNorm p x.second.divisor:=by
      simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 1).1
    have hh:Z^(secondCellExponent Z d 1-eta)≤Z^(secondCellExponent Z d 1):=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    rw [second_cell_scale_rpow Z d 1 hZ] at hh
    exact hh.trans hr
  exact henergy p hp hcop hg hpr hinj hc (cell p source d) (cell_conditions p source hs d) d
    (fun x hx=>(mem_cell p source d x).mp hx |>.2) pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y (R d) L Z X (Vlabel d) εchild ell Ractive j tcount
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta ρ t w (labels d) A
    (fun x hx=>hd₁ x (hin hx)) (fun x hx=>hd₂ x (hin hx)) hρ hL hZ hX hY
    (fun x hx=>by simpa only [(mem_cell p source d x).mp hx |>.2] using hrows x (hin hx)) (fun x hx=>hcube₁ x (hin hx)) (fun x hx=>hcube₂ x (hin hx))
    (fun x hx=>hactive x (hin hx)) (fun x hx=>hj x (hin hx)) (fun x hx=>hquot x (hin hx))
    hcommon hdiv hΨ (fun x hx=>hw x (hin hx)) ha₁ ha₂ (hlabels d hd) ho hslots₁ hslots₂ hA
    (hleft d hd) (hright d hd)

end SevenEighths.InverseMoment

end

end OAI

end Source2641

/- Original source: OAI/NumberTheory/DirichletL/Descent/PriorityRetainedMovingRadiusWindowOrderUniform.lean; sha256: cf8081d5c66a68ef0df02dc59932aae7e8a19b64688418acecdcdbd6fa2a0f50 -/
section Source2642
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
theorem actual_priority_retained_moving_radius_window_order_uniform_types
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
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
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_priority_source_moving_radius_window_order_uniform_types  om Φ lo hi hlo hsupport negative B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩:=hordered J
  obtain ⟨Cbin,hCbin,hbudget⟩:=priority_source_scalar_budget caps hcaps
  refine ⟨36*(2:ℝ)^(2*K)*C,Cbin,by positivity,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b
    ρ t w labels A hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have he:=henergy p hp hcop hg hpr hinj hc source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  let H:ℝ:=(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)
  have hheight:(1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
      (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J=H:=by
    cases negative <;> simp [priorityHeight,H,two_mul,pow_add]
  let D:ℝ:=36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*C*H
  have hD:0≤D:=by dsimp [D,H];positivity
  let S:ℝ:=∑d∈keys p source,priorityCellScalar Z Y L X ell Ractive j tcount eta εchild εmass Bfirst (secondRayCoefficient z) d
  have hfactor:
      (∑d∈keys p source,(Real.exp (6*L)*‖(Y:ℂ)*secondRayCoefficient z*
          ((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel d)+εchild))*
          Z^((ell+Ractive/2-j+tcount+secondCellExponent Z d 0-secondCellExponent Z d 1+11*eta/2)*(1+εmass)))*
          (C*((1+‖-priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J*
            (1+‖priorityHeight negative t‖)^InverseClippingProfiles.momentOrder J))))=D*S:=by
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hheight,hVe d]
    dsimp only [D,priorityCellScalar,secondCount]
    ring
  simp only [pow_zero,div_one] at he
  rw [hfactor] at he
  have hbnd:=hbudget p hp source Z M r ell V delta Acol Bfirst Ractive j tcount eta tau pi εchild εmass b D
    (secondRayCoefficient z) hZ2 hD hb hthreshold
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)) hnorm
    (by simpa only [hXe] using hgeom) hmass
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hP:0≤P:=by dsimp [P];positivity
  have hconst:D≤(36*(2:ℝ)^(2*K)*C)*A*H:=by
    have h1:(2:ℝ)^slots₁.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₁
    have h2:(2:ℝ)^slots₂.card≤2^K:=pow_le_pow_right₀ (by norm_num) hslots₂
    calc
      _≤36*(2:ℝ)^K*(2:ℝ)^K*A*C*H:=by dsimp only [D];gcongr
      _= _:=by rw [show 2*K=K+K by omega,pow_add];ring
  calc
    _≤P*(D*S):=mul_le_mul_of_nonneg_left he hP
    _≤D*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by
      convert hbnd using 1 ; dsimp only [P,S] ; rw [hYe,hXe,hLe] ; ring
    _≤((36*(2:ℝ)^(2*K)*C)*A*H)*‖secondRayCoefficient z‖*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+εchild):=by gcongr
    _= _:=by dsimp only [H];ring

end SevenEighths.InverseMoment

end

end OAI

end Source2642

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityFilteredEnergyUniform.lean; sha256: e7c351ed9334b81fd01c1fe72cdbd6df185510d14f0a16440066cc602002c416 -/
section Source2643
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
theorem global_priority_filtered_moving_radius_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
    let originalSource:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀(z:SecondRayIndex)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
    let source:=InverseMomentGlobalRetainedGates.geometrySource p originalSource b X;
      hi≤b →
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
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y:ℂ)*secondRayCoefficient z *
        ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_priority_retained_moving_radius_window_order_uniform_types  om rowMajorant lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  refine ⟨coefficientBound*C,Cbin,mul_nonneg coefficientBound_pos.le hC,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff originalSource Ψ₀ z
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A source hhib
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hsub:source⊆originalSource:=InverseMomentGlobalRetainedGates.geometrySource_subset p originalSource b X
  have hsource:ActualSecondSourceConditions p source:=
    ActualSecondSourceConditions.mono p (unified_conditions p hp extra original hvalid hextra negative assigned lists pool cutoff) hsub
  have hd:∀x∈source,∀i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient:=
    fun x hx=>unified_deleted_support p hinj extra original hvalid hextra negative assigned lists pool cutoff x (hsub hx)
  have hw:∀x∈source,‖normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x‖≤1:=
    fun x hx=>normalizedGlobalPriorityWeight_norm p hg hinj extra original pool negative Ψ m ray core w hwOriginal hΨ
      assigned lists a haassigned cutoff x (hsub hx)
  have hΨ₀:∀n,‖Ψ₀ n‖≤1:=fun n=>(firstCoreTwist_norm_le negative (if negative then ray.1 else ray.2)
    Ψ core n).trans (hΨ n)
  have he₀:=he p hp hcop hg hpr hinj hc source hsource pool Ψ₀ m z (slots\assigned) (slots\assigned)
    lists lists a a (InverseMomentWholeRetainedSource.deleted p extra negative)
    (InverseMomentWholeRetainedSource.deleted p extra negative)
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t
    (normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a) labels A
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
  have hupper:∀y,principalWindow om lo hi hlo hsupport negative t y≠0 → y≤b:=by
    intro y hy
    have hy':y∈Function.support om:=by
      rw [←principalWindow_support om lo hi hlo hsupport negative t]
      exact hy
    exact (hsupport hy').2.trans hhib
  rw [InverseMomentGlobalRetainedGates.original_retained_geometry_sum p hp hcop hg extra pool originalSource
    (globalPriorityWeight p hg negative Ψ m ray core w assigned a) negative Ψ₀ m slots assigned lists a
    (principalWindow om lo hi hlo hsupport negative t) X Y b hX hupper z]
  rw [globalPriority_sum_normalized p hg negative Ψ m ray core w assigned a source]
  rw [show (Y:ℂ)*secondRayCoefficient z*((coefficientBound:ℂ)*
      ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x)=
      (coefficientBound:ℂ)*((Y:ℂ)*secondRayCoefficient z*
        ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x) by ring]
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  simp_rw [hrow,←mul_assoc]
  convert mul_le_mul_of_nonneg_left he₀ coefficientBound_pos.le using 1 <;> ring_nf

end SevenEighths.InverseMoment

end

end OAI

end Source2643

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityFilteredRaysUniform.lean; sha256: 7d2819476f4319f4982fb24bdd3ecbb2b2125cdeb4b10b46172f065046a73dce -/
section Source2644
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
theorem global_priority_filtered_all_rays_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
    let originalSource:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
    let source:=InverseMomentGlobalRetainedGates.geometrySource p originalSource b X;
      hi≤b →
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
        ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_moving_radius_uniform_types  om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  refine ⟨C*(512*32^2),Cbin,by positivity,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff originalSource Ψ₀
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A source hhib
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:= (1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*(1+Cbin*Real.log Z)^4*
    Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  let S:SecondRayIndex→ℂ:=fun z=>(Y:ℂ)*secondRayCoefficient z *
      ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x
  have hP:0≤P:=by dsimp [P];positivity
  have hH:0≤H:=by dsimp [H];positivity
  have hz (z:SecondRayIndex):P*‖S z‖≤C*A*H*‖secondRayCoefficient z‖:=by
    have h:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a cutoff z
      Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
      hhib haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
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

end Source2644

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityFilteredAggregateUniform.lean; sha256: bc3bf81f2f007e702f58598ef0a416cad253e76aebb86d385c5519386e9803a0 -/
section Source2645
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
theorem global_priority_filtered_aggregate_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
      hi≤b → slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
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
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_all_rays_uniform_types  om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  let Ctot:=(32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*
    (Fintype.card FirstCoreIndex:ℝ)*C
  refine ⟨Ctot,Cbin,by dsimp [Ctot];positivity,hCbin,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hhib hslots hA hdata
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
      hhib haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
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

end Source2645

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityFilteredStepUniform.lean; sha256: 1101460cf950ebc0db8de0e275e62524c2d604f6d5baa8a29068dda9470c5bbf -/
section Source2646
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentGlobalPriorityTail
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
theorem global_priority_filtered_physical_step_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤Real.exp window)(hLcap:0≤Lcap)(htau:0<tau)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
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
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤b → (slots:Set σ).PairwiseDisjoint lists→slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
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
      Jo≤Jmax→0≤ell+eta→0≤Bfirst→0≤j→
      εmass*(r-Acol-Bfirst-tcount)+7*eta/2+dsmall*(3*ell+Bfirst+tcount+5*eta)+
        2*εmass*(2*ell+Bfirst+tcount+4*eta)≤pi+eta/2→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(tcount+eta))→
      1≤Y→1≤X*Real.exp window→Y≤Z^Lcap→Y⁻¹≤Z^Lcap→X*Real.exp window≤Z^Lcap→
      firstKappa M r ell V delta Acol Bfirst Ractive+(9/2:ℝ)*eta≤Lcap→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^Lcap)→
      (∀G E,0≤cutoff G E)→
      (∀x∈original,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp window) Y (Z^tau)≤cutoff G E.val)→
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_aggregate_uniform_types  om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  obtain ⟨sz,Cz,hCz,hzero⟩:=global_priority_zero_physical εmass hεmass Jmax dsmall hdsmall
  obtain ⟨st,Ct,hCt,htail⟩:=global_physical_tail_rapid Jmax Lcap tau saving hLcap htau
  let Cz':=Cz*(4:ℝ)^K*(sz.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+εmass))
  let Ct':=Ct*(4:ℝ)^K*(st.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2
  refine ⟨C,Cbin,Cz',Ct',hC,hCbin,by dsimp [Cz'];positivity,by dsimp [Ct'];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels A
    hhib hdisj hslots hA hdata hJo hell hBfirst hj hcost hcube₁ hcube₂ hactive hcommon hquotient
    hYone hscale hy hyi hx hPcap hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hrad hcutoff
  have hh:=hdata 1 1 ∅ (Finset.empty_subset _)
  obtain ⟨_,hρ,hL,hZ,hX,hY,heta,hbin,_,_,_,_,_,_,hΨall,_,_,_,_,_,_,_,hYe,hXe,hLe,_,hZ2,_,_,_,_,_,_,_⟩:=hh
  have hz:0<Z:=zero_lt_one.trans hZ
  have haall:∀i∈slots,∀q∈lists i,‖a i q‖≤1:=by
    have hh':=hdata 1 1 slots (Finset.Subset.refl _)
    exact hh'.1
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  have hzn:=hzero p hp hg hinj hcop Jo hJo extra pool original w negative Ψ m slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport Z M r ell V delta Acol Bfirst Ractive j tcount eta tau window pi t cutoff
    hZ.le hell hBfirst hj hcost hvalid hcube₁ hcube₂ hactive hcommon hquotient hextra hhi (by rwa [←hYe]) hrad
  rw [←hXe,←hYe] at hzn
  have hzbound : _ ≤ Cz'*Z^(r+3*ell+V+17*eta+tau+pi):=hzn.trans (by dsimp [Cz'];gcongr)
  have htn:=htail p hp hg hinj hcop hc Jo hJo extra pool original negative Ψ m w slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport X window Y Z t
    (firstKappa M r ell V delta Acol Bfirst Ractive) eta cutoff hPcap hX hhi hZ.le hY hscale hy hyi hx
    hvalid hextra hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hcutoff
  have htbound : _ ≤ Ct'*Z^(-saving):=htn.trans (by dsimp [Ct'];gcongr)
  have hrbound:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hhib hslots hA hdata
  have hb:=global_priority_three_branches p hg hp hcop hinj hc hpr extra pool original w negative Ψ m slots lists a
    om lo hi hlo hsupport X t Y hX hY cutoff
  have hP:0≤Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)):=by positivity
  have hb':=mul_le_mul_of_nonneg_left hb hP
  simp only [mul_add] at hb'
  exact hb'.trans (add_le_add (add_le_add hzbound hrbound) htbound)
end SevenEighths.InverseMoment

end

end OAI

end Source2646

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityFixedChildStepUniform.lean; sha256: e775f3d67a6de0ccbca51d227b9408dd9d4b00c8c0d49d5d115f5c84e79fd2f0 -/
section Source2647
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentGlobalPriorityTail
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
theorem global_priority_fixed_child_step_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤Real.exp window)(hLcap:0≤Lcap)(htau:0<tau)
    (bcap:ℝ)(hbcap:1≤bcap)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
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
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤b → b≤bcap → (slots:Set σ).PairwiseDisjoint lists→slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
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
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ s:ℝ,∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (childLogTest ω₁ s)
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(1+‖s‖)^(2*J)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ s:ℝ,∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (childLogTest ω₂ s)
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(1+‖s‖)^(2*J))) →
      Jo≤Jmax→0≤ell+eta→0≤Bfirst→0≤j→
      εmass*(r-Acol-Bfirst-tcount)+7*eta/2+dsmall*(3*ell+Bfirst+tcount+5*eta)+
        2*εmass*(2*ell+Bfirst+tcount+4*eta)≤pi+eta/2→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(tcount+eta))→
      1≤Y→1≤X*Real.exp window→Y≤Z^Lcap→Y⁻¹≤Z^Lcap→X*Real.exp window≤Z^Lcap→
      firstKappa M r ell V delta Acol Bfirst Ractive+(9/2:ℝ)*eta≤Lcap→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^Lcap)→
      (∀G E,0≤cutoff G E)→
      (∀x∈original,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp window) Y (Z^tau)≤cutoff G E.val)→
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*J))*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
  obtain ⟨v₁,v₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hstep⟩:=
    global_priority_filtered_physical_step_uniform_types  om lo hi hlo hsupport negative
      window Lcap tau saving hhi hLcap htau Jmax dsmall hdsmall caps hcaps B₀ hB₀ K εmass hεmass
  obtain ⟨w₁,a₁,b₁,ha₁,hab₁,hw₁,hsw₁,hfixed₁⟩:=canonical_actual_child_uniform
    v₁ af bf bcap haf hbcap ((subset_tsupport _).trans hs₁) (v₁.smooth ⊤)
  obtain ⟨w₂,a₂,b₂,ha₂,hab₂,hw₂,hsw₂,hfixed₂⟩:=canonical_actual_child_uniform
    v₂ af bf bcap haf hbcap ((subset_tsupport _).trans hs₂) (v₂.smooth ⊤)
  refine ⟨w₁,w₂,min a₁ a₂,max b₁ b₂,lt_min ha₁ ha₂,
    (min_le_left _ _).trans (hab₁.trans (le_max_left _ _)),hw₁,hw₂,
    hsw₁.trans (Set.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _)),
    hsw₂.trans (Set.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)),?_⟩
  intro J
  obtain ⟨C₁,hC₁,he₁⟩:=hfixed₁ J
  obtain ⟨C₂,hC₂,he₂⟩:=hfixed₂ J
  obtain ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,he⟩:=hstep (2*J)
  let Cmax:=max C₁ C₂
  have hmax:0≤Cmax:=hC₁.le.trans (le_max_left _ _)
  refine ⟨C*Cmax,Cbin,Czero,Ctail,mul_nonneg hC hmax,hCbin,hCzero,hCtail,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels A
    hhib hbcap' hdisj hslots hA hdata hJo hell hBfirst hj hcost hcube₁ hcube₂ hactive hcommon hquotient
    hYone hscale hy hyi hx hPcap hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hrad hcutoff
  have hout:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels (Cmax*A)
    hhib hdisj hslots (mul_nonneg hmax hA)
  have hnew:
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*(Cmax*A)*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*J))*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
    apply hout
    · intro ray core assigned hassigned
      obtain ⟨haa,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hb₁,hb₂,hactive',hj',hq,hΨ,
        hal,har,hlabels,ho,hsl,hsr,hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,hleft,hright⟩:=hdata ray core assigned hassigned
      refine ⟨haa,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hb₁,hb₂,hactive',hj',hq,hΨ,
        hal,har,hlabels,ho,hsl,hsr,mul_nonneg hmax hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,?_,?_⟩
      · intro z d hd u J₁ hJ₁ γ hγ
        have hgeomcell:=source_cell_joint_bound p hp _ (fun x hx=>(Finset.mem_erase.mp (hrows x hx)).1) b X hgeom d hd
        have hh:=he₁ p hp hcop hg hpr pool _ _ ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (fun f hf=>pow_nonneg (Nat.cast_nonneg _) _) Z X _
          (A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild)) d false u hZ hX
          (hgeomcell.trans (mul_le_mul_of_nonneg_right hbcap' hX.le)) (mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
          (fun s=>hleft z d hd s J₁ hJ₁ γ hγ)
        change _≤(Cmax*A)*Z^(_)*_
        apply hh.trans
        have hH:0≤tripleHeight (2*J) u.1*coordinateHeight (2*J) u.2:=by
          unfold tripleHeight coordinateHeight
          positivity
        have hE:0≤A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild):=
          mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hE) hH using 1 ; ring
      · intro z d hd u J₂ hJ₂ γ hγ
        have hgeomcell:=source_cell_joint_bound p hp _ (fun x hx=>(Finset.mem_erase.mp (hrows x hx)).1) b X hgeom d hd
        have hh:=he₂ p hp hcop hg hpr pool _ _ ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (fun f hf=>pow_nonneg (Nat.cast_nonneg _) _) Z X _
          (A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild)) d true u hZ hX
          (hgeomcell.trans (mul_le_mul_of_nonneg_right hbcap' hX.le)) (mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
          (fun s=>hright z d hd s J₂ hJ₂ γ hγ)
        change _≤(Cmax*A)*Z^(_)*_
        apply hh.trans
        have hH:0≤tripleHeight (2*J) u.1*coordinateHeight (2*J) u.2:=by
          unfold tripleHeight coordinateHeight
          positivity
        have hE:0≤A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild):=
          mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hE) hH using 1 ; ring
    all_goals assumption
  convert hnew using 1 ; ring
end SevenEighths.InverseMoment

end

end OAI

end Source2647

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstLabelCellStep.lean; sha256: 4c1bcc504450f19010aa131f90697d4fe3d8ed8ca33d21ceee5bffe5206d32dc -/
section Source2648
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondFibers InverseInitialClippedColumns RayFourExpansion FirstCauchyArithmetic
open InverseWholePriorityRetainedSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def ChildBounds {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (Z M r ell V eta tau window b epschild A : ℝ) (K degree : ℕ) : Prop :=
  ∀(ray : RayCharacter×RayCharacter)(core : FirstCoreIndex)(assigned : Finset σ),assigned⊆slots→
  let S := source p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  let Ψ₀ := firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  (∀z : SecondRayIndex,∀d∈keys p S,∀s : ℝ,∀J₁∈(slots\assigned).powerset,∀γ∈actualSecondTriples p 1 1 (cell p S d),
    normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
      (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
      ((actualCellLabels p S d).filter Squarefree)
      (nonzeroChildFrequencyBall 1 (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d))
      (secondLabelWeight K) (childLogTest ω₁ s)
      (Z^(max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))) Z
      (actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d)≤
      A*Z^(actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d+epschild)*
        (1+‖s‖)^(2*degree)) ∧
  (∀z : SecondRayIndex,∀d∈keys p S,∀s : ℝ,∀J₂∈(slots\assigned).powerset,∀γ∈actualSecondTriples p 1 1 (cell p S d),
    normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
      (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
      ((actualCellLabels p S d).filter Squarefree)
      (nonzeroChildFrequencyBall 1 (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d))
      (secondLabelWeight K) (childLogTest ω₂ s)
      (Z^(max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))) Z
      (actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d)≤
      A*Z^(actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d+epschild)*
        (1+‖s‖)^(2*degree))

theorem actual_label_cell_step (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
    (hsupport : Function.support om⊆Set.Icc lo hi) (negative : Bool)
    (window Ltail Lgate tau saving : ℝ) (hhi : hi≤Real.exp window)
    (hLtail : 0≤Ltail) (hLgate : 0≤Lgate) (htau : 0<tau)
    (bcap : ℝ) (hbcap : 1≤bcap) (dsmall : ℝ) (hdsmall : 0<dsmall)
    (B₀ : Fin 6→ℝ) (hB₀ : ∀i,0≤B₀ i) (K : ℕ) (epsmass : ℝ) (hepsmass : 0<epsmass) :
    ∃(ω₁ ω₂ : 𝓢(ℝ,ℂ))(loFresh hiFresh : ℝ),0<loFresh ∧ loFresh≤hiFresh ∧
      HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
    ∀degree : ℕ,∃C Cbin Czero Ctail : ℝ,0≤C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ : Type}[DecidableEq ι][DecidableEq σ](p : ι→O)(hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι)(Q : Finset (ι→₀ℕ))(k : SourceIndex)(l j : ℕ)
      (Ψ : O→*ℂ)(m : O)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ)
      (Z M r ell V eta pi b Lcol LY epschild A t : ℝ)(ρ : Fin 6→ℝ),
      2≤Z→0≤eta→2≤Z^eta→0≤ell+eta→
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))→
      (slots:Set σ).PairwiseDisjoint lists→slots.card≤K→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      (∀u,‖Ψ u‖≤1)→(∀i,|ρ i|≤B₀ i)→hi≤b→b≤bcap→1≤b→b≤Z^(6*eta)→
      Real.exp window≤Z^(4*eta)→0≤A→
      columnScale Z r k l negative*Real.exp window≤Z^Lcol→
      (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY→
      b*columnScale Z r k l negative≤Z^Lgate→exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lgate→
      epsmass*(ell+exponent Z (k 4)/2+exponent Z l+Lgate+11*eta/2)≤pi→
      epsmass*(r-columnA Z k negative-exponent Z (k 2)-exponent Z l)+7*eta/2+
        dsmall*(3*ell+exponent Z (k 2)+exponent Z l+5*eta)+
        2*epsmass*(2*ell+exponent Z (k 2)+exponent Z l+4*eta)≤pi+eta/2→
      1≤firstCellRadius Z M r ell V eta tau k j→1≤columnScale Z r k l negative*Real.exp window→
      firstCellRadius Z M r ell V eta tau k j≤Z^Ltail→
      (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^Ltail→
      columnScale Z r k l negative*Real.exp window≤Z^Ltail→
      firstKappa M r ell V (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) (exponent Z (k 4))+
        (9/2:ℝ)*eta≤Ltail→
      ell+eta≤Ltail→exponent Z (k 4)+eta≤Ltail→exponent Z (k 2)+eta≤Ltail→exponent Z l+eta≤Ltail→
      ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree→
      (Z^(firstKappa M r ell V (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) (exponent Z (k 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j) (parentWeight p l)
        negative Ψ m slots lists a om (columnScale Z r k l negative) t (firstCellRadius Z M r ell V eta tau k j)≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*degree))*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+epschild)+Ctail*Z^(-saving) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,hstep⟩ := global_priority_fixed_child_step_uniform_types
    om lo hi hlo hsupport negative window Ltail tau saving hhi hLtail htau bcap hbcap
    0 dsmall hdsmall (fun _=>Lgate) (fun _=>hLgate) B₀ hB₀ K epsmass hepsmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro degree
  obtain ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,he⟩ := hstep degree
  refine ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc pool Q k l j Ψ m slots lists a
    Z M r ell V eta pi b Lcol LY epschild A t ρ hZ2 heta hbin hell hQ hdisj hslots ha hΨ hρ hhib hbb hb1 hb6
    hwindow hA hcol hYi hgeom hphysical hbudget hcost hY1 hX1 hYcap hYicap hXcap hPcap hellcap hactivecap hcommoncap hquotcap hchild
  have hZ : 1<Z := by linarith
  have hz : 0<Z := zero_lt_one.trans hZ
  have hX : 0<columnScale Z r k l negative := Real.rpow_pos_of_pos hz _
  have hY : 0<firstCellRadius Z M r ell V eta tau k j := Real.rpow_pos_of_pos hz _
  have hparent := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  have htail := parent_tail_caps p hp pool Q k l j Z ell eta Ltail hZ heta hbin hLtail hQ
    hellcap hactivecap hcommoncap hquotcap
  apply he p hp hcop hg hpr hinj hc (extra negative) pool
    (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
    (label_parent_valid p pool Q k l j) (fun y hy=>extra_subset negative y.cube)
    (parentWeight p l) (fun y hy=>parentWeight_norm p l y) Ψ m slots lists a
    (secondCutoff p Z M r ell V eta tau window k l j negative)
    (firstCellRadius Z M r ell V eta tau k j)
    (fun _ d=>actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
    (eta*Real.log Z) Z (columnScale Z r k l negative) epschild
    (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta)
    ell (exponent Z (k 4)) (exponent Z j) (exponent Z l) eta M r V
    (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) pi b ρ t
    (fun assigned d=>actualCellLabels p (source p pool Q k l j negative assigned lists Z M r ell V eta tau window b) d) A
    hhib hbb hdisj hslots hA
  · intro ray core assigned hassigned
    obtain ⟨_,_,hrows,_,hn,hlabels,_,hcaps,hgeometry,hmass⟩ := source_step_arithmetic p hp pool Q k l j
      negative assigned lists Z M r ell V eta tau window b Lcol LY Lgate epsmass pi
      hZ heta hbin hepsmass.le hwindow hQ hcol hYi hgeom hphysical hbudget
    have hJ : assigned.card≤K := (Finset.card_le_card hassigned).trans hslots
    have hrest : (slots\assigned).card≤K := (Finset.card_le_card Finset.sdiff_subset).trans hslots
    have hbchild := hchild ray core assigned hassigned
    refine ⟨(fun i hi q hq=>ha i (hassigned hi) q hq),hρ,mul_nonneg heta (Real.log_nonneg hZ.le),hZ,hX,hY,heta,hbin,
      hrows,(fun x hx=>(hn x hx).1),(fun x hx=>(hn x hx).2.1),(fun x hx=>(hn x hx).2.2.1),
      (fun x hx=>(hn x hx).2.2.2.2.2.1),(fun x hx=>(hn x hx).2.2.2.2.1),hΨ,
      (fun i hi q hq=>ha i (Finset.mem_sdiff.mp hi).1 q hq),
      (fun i hi q hq=>ha i (Finset.mem_sdiff.mp hi).1 q hq),
      (fun d hd x hx=>hlabels d x hx),by omega,hrest,hrest,hA,rfl,rfl,rfl,(fun _=>rfl),hZ2,hb1,hb6,
      hcaps,hgeometry,hmass,hbchild.1,hbchild.2⟩
  · exact Nat.zero_le _
  · exact hell
  · exact dyadic_exponent_nonneg Z hZ _
  · exact dyadic_exponent_nonneg Z hZ _
  · exact hcost
  · exact fun y hy=>(hparent y hy).1
  · exact fun y hy=>(hparent y hy).2.1
  · exact fun y hy=>(hparent y hy).2.2.1
  · exact fun y hy=>(hparent y hy).2.2.2.1
  · exact fun y hy=>(hparent y hy).2.2.2.2.1
  · exact hY1
  · exact hX1
  · exact hYcap
  · exact hYicap
  · exact hXcap
  · exact hPcap
  · exact fun y hy=>(htail y hy).1
  · exact fun y hy=>(htail y hy).2.1
  · exact fun y hy=>(htail y hy).2.2.1
  · exact fun y hy=>(htail y hy).2.2.2.1
  · exact fun y hy=>(htail y hy).2.2.2.2
  · exact fun G E=>secondCutoff_nonneg p Z M r ell V eta tau window k l j negative hz G E
  · exact fun y hy G hG E=>secondCutoff_dominates p hp pool Q k l j negative Z M r ell V eta tau window hZ hbin y hy G E.val

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI

end Source2648

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalRankMoments.lean; sha256: 2a6c0cca77ab991b09b82d21c678f5038b0b74c00cbd3df1139df38c66c67a47 -/
section Source2649
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialClippedColumns InverseSecondFibers InverseSecondSourceBlocks
open CanonicalCoefficientClass InverseMomentFirstLabelCell InverseMomentFirstChildWindows InverseFirstGlobalCaps
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def CanonicalRankMoments (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ):Prop :=
  ∀(Ψ:O→*ℂ),IsBaseRayTwist base Ψ→∀(m:O),m≠0→∀N V M Qwidth:ℝ,
    0≤N→0≤V→0≤M→0≤Qwidth→M≤Mmax→N+V≤Fcap→
    CanonicalMargins (N+V) M Qwidth z c→
    ‖ConcreteTraceCRT.eisEmbedding m‖^2=Z^Qwidth→
    ∀(subslots:Finset σ),subslots⊆slots→∀labels:Finset (Ideal O),
      (∀I∈labels,Admissible I ∧ (Ideal.absNorm I:ℝ)≤Z^V)→∀s:ℝ,
    normalizedColumnEnergy p hp hcop hg pool Ψ m subslots lists a labels
      (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (childLogTest W s) (Z^N) Z (N+V)≤
      A*Z^(N+V+eps)*(1+‖s‖)^(2*degree)

include hp in
theorem canonical_rank_moments_children
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)(negative:Bool)
    (base Ψ:O→*ℂ)(hΨ:IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:𝓢(ℝ,ℂ))
    (Z M r ell V eta tau window b cutoff Qwidth z c eps A:ℝ)(K degree:ℕ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (_hd:0<cutoff)(hterminal:cutoff≤ell+V)(hsmall:eta≤cutoff/16)
    (hparent:CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ:∀v∈Q,‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (h₁:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₁ Z (M-3*cutoff/2) (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree)
    (h₂:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₂ Z (M-3*cutoff/2) (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree):
    ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
      Z M r ell V eta tau window b eps A K degree :=by
  intro ray core assigned hass
  let S:=source p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  have hbase:IsBaseRayTwist base Ψ₀:=hΨ.firstCore _ _ _
  have hstate:=source_state_bounds p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b cutoff
    hZ heta hbin hell hV hb hbt hwindow hterminal hsmall hQ
  have hmargin:=source_child_margins p hp hpr pool Q k l j negative assigned lists Z M r ell V eta tau window b
    m hm Qwidth z c hZ heta hbin hV hparent hpuncture hQ
  have hlabels:=source_labels p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b hZ heta hbin hQ
  constructor
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₁ (secondRayMinus Ψ₀ zz) (hbase.secondMinus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₂ (secondRayPlus Ψ₀ zz) (hbase.secondPlus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩

end SevenEighths.InverseMoment

end

end OAI

end Source2649

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCanonicalEnergy.lean; sha256: f4a13c5ba7290d9e00abc160eca671b9f390b83de552d610c57590573503e968 -/
section Source2650
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialCanonicalEnergy
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CanonicalQuadraticSieve
open InverseMoment InverseInitialClippedColumns SecondPassArithmetic CanonicalCoefficientClass
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [DecidableEq σ] in
theorem normalization_change (pool:Finset ι)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(w:Ideal O→ℝ)(W:ℝ→ℂ)
    (X Z F G:ℝ)(hZ:0<Z):
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z F=
      Z^(G-F)*normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z G := by
  have he:Z^F*normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z F=
      Z^G*normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z G:=
    (columnEnergy_normalization p hp hcop hg pool Ψ m slots lists a labels rows w W X hZ F).symm.trans
      (columnEnergy_normalization p hp hcop hg pool Ψ m slots lists a labels rows w W X hZ G)
  apply mul_left_cancel₀ (Real.rpow_pos_of_pos hZ F).ne'
  rw [←mul_assoc,←Real.rpow_add hZ,show F+(G-F)=G by ring]
  exact he

omit [DecidableEq σ] in
theorem energy_range_weight_le (pool:Finset ι)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows largeRows:Finset O)(w v:Ideal O→ℝ)(W:ℝ→ℂ)
    (X Z F:ℝ)(hrows:rows⊆largeRows)(hw:∀f∈labels,0≤w f)(hv:∀f∈labels,w f≤v f):
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z F≤
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels largeRows v W X Z F := by
  unfold normalizedColumnEnergy
  apply Finset.sum_le_sum
  intro f hf
  apply mul_le_mul (hv f hf)
    (Finset.sum_le_sum_of_subset_of_nonneg hrows (fun _ _ _=>sq_nonneg _))
    (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
    ((hw f hf).trans (hv f hf))

omit [DecidableEq σ] in
theorem initial_child_from_rank (pool:Finset ι)(base Ψ:O→*ℂ)
    (slots subslots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:𝓢(ℝ,ℂ))
    (Z Mcap Fcap z c eps A N V M Q η:ℝ)(K degree:ℕ)(m:O)
    (hZ:1<Z)(hbase:IsBaseRayTwist base Ψ)(hm:m≠0)
    (hN:0≤N)(hV:0≤V+2*η)(hM:0≤M)(hQ:0≤Q)
    (hMcap:M≤Mcap)(hFcap:N+(V+2*η)≤Fcap)
    (hmargin:CanonicalMargins (N+(V+2*η)) M Q z c)
    (hmnorm:‖eisEmbedding m‖^2=Z^Q)(hsub:subslots⊆slots)
    (labels:Finset (Ideal O))(hlabels:∀f∈labels,Admissible f ∧ (f.absNorm:ℝ)≤Z^(V+2*η))
    (rows:Finset O)(hrows:rows⊆nonzeroChildFrequencyBall 1 (Z^M))
    (weight:Ideal O→ℝ)(hw:∀f∈labels,0≤weight f)
    (hweight:∀f∈labels,weight f≤secondLabelWeight K f)(s:ℝ)
    (hmoment:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z Mcap Fcap z c eps A K degree):
    normalizedColumnEnergy p hp hcop hg pool Ψ m subslots lists a labels rows weight
      (childLogTest W s) (Z^N) Z (N+V)≤A*Z^(N+V+eps+4*η)*(1+‖s‖)^(2*degree) := by
  have hcanon:=hmoment Ψ hbase m hm N (V+2*η) M Q hN hV hM hQ hMcap hFcap hmargin hmnorm
    subslots hsub labels hlabels s
  rw [normalization_change p hp hcop hg pool Ψ m subslots lists a labels rows weight
    (childLogTest W s) (Z^N) Z (N+V) (N+(V+2*η)) (zero_lt_one.trans hZ)]
  apply (mul_le_mul_of_nonneg_left
    ((energy_range_weight_le p hp hcop hg pool Ψ m subslots lists a labels rows
      (nonzeroChildFrequencyBall 1 (Z^M)) weight (secondLabelWeight K) (childLogTest W s)
      (Z^N) Z (N+(V+2*η)) hrows hw hweight).trans hcanon)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans_eq
  rw [show N+(V+2*η)-(N+V)=2*η by ring]
  calc
    _=A*(Z^(2*η)*Z^(N+(V+2*η)+eps))*(1+‖s‖)^(2*degree):=by ring
    _=_:=by
      rw [←Real.rpow_add (zero_lt_one.trans hZ)]
      congr 3
      ring

end SevenEighths.InverseInitialCanonicalEnergy

end

end OAI

end Source2650

/- Original source: OAI/NumberTheory/DirichletL/Descent/CompletionSplit.lean; sha256: e5d627f0b66e0a9ce1e39d2f965f3f30b2ab0794ddcacfdf84f4c7172411542f -/
section Source2651
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem marked_cube_inverse_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) :
    (Function.support (fun H : Ideal O =>
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
        markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H^3*A)))).Finite := by
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  apply (hf.image (fun p => p.2.1)).subset
  intro H hH
  by_contra hn
  have hzero : ∀ I J, markedExpandedTerm Ψ W X d I H J = 0 := by
    intro I J
    by_contra hz
    exact hn ⟨(I, H, J), hz, rfl⟩
  apply hH
  dsimp only
  rw [weighted_markedCompletedT_reopen]
  simp only [hzero, tsum_zero]

theorem marked_large_cube_inner_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) (I : Ideal O) :
    (∑' H : Ideal O,∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0) =
    ∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let f : Ideal O → ℂ := fun B =>
    columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I : ℝ) : ℂ)*
      Vstar W ((Ideal.absNorm I : ℝ)*(Ideal.absNorm B : ℝ)^3/X)*d (I*B^3)
  have heq (H J : Ideal O) :
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ (H*J)*f (H*J)=markedExpandedTerm Ψ W X d I H J := by
    simp only [f,markedExpandedTerm,expandedTerm,map_mul,Nat.cast_mul,mul_pow,mul_assoc]
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  have hp : (Function.support (fun p : Ideal O × Ideal O => markedExpandedTerm Ψ W X d I p.1 p.2)).Finite := by
    change ((fun p : Ideal O × Ideal O => (I,p)) ⁻¹'
      Function.support (fun p : Ideal O × Ideal O × Ideal O => markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hg := large_cube_convolution H₀ (cubeWeight Ψ) (cubeWeight_zero Ψ) f (by simpa only [heq] using hp)
  rw [show (∑' H : Ideal O, ∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0)=
      ∑' B : Ideal O,largeCubeCoefficient H₀ B*cubeWeight Ψ B*f B by simpa only [heq] using hg]
  apply tsum_congr
  intro B
  dsimp [f,summand]
  ring

theorem marked_large_cube_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) :
    (∑' H : Ideal O, if H₀ ≤ (Ideal.absNorm H : ℝ) then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A)) else 0) =
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let F : Ideal O × Ideal O × Ideal O → ℂ := fun p =>
    if H₀ ≤ (Ideal.absNorm p.2.1 : ℝ) then markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2 else 0
  have hF : Summable F := summable_of_hasFiniteSupport
    ((markedExpandedTerm_finite_support Ψ W hW X hX d).subset (by
      intro p hp
      by_contra hn
      have he : markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2=0 := not_ne_iff.mp hn
      exact hp (by simp [F,he])))
  let e : (Ideal O × Ideal O × Ideal O) ≃ (Ideal O × Ideal O × Ideal O) := {
    toFun := fun p => (p.2.1,p.1,p.2.2)
    invFun := fun p => (p.2.1,p.1,p.2.2)
    left_inv := by rintro ⟨I,H,J⟩;rfl
    right_inv := by rintro ⟨I,H,J⟩;rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal O,∑' I : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0 := by
      apply tsum_congr
      intro H
      by_cases h : H₀ ≤ (Ideal.absNorm H : ℝ)
      · simp only [ite_eq_left h,weighted_markedCompletedT_reopen]
      · simp only [ite_eq_right h,tsum_zero]
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F p := e.tsum_eq F
    _ = ∑' I : Ideal O,∑' H : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then markedExpandedTerm Ψ W X d I H J else 0 := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (marked_large_cube_inner_reopen Ψ W hW X H₀ hX d)

theorem marked_completed_cube_inverse_split (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (d : Ideal O → ℂ) :
    (Real.sqrt X : ℂ)⁻¹*(∑' I : Ideal O,columnWeight Ψ I*d I*W ((Ideal.absNorm I : ℝ)/X)) =
    (∑' H : Ideal O, if (Ideal.absNorm H : ℝ)<H₀ then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A)) else 0) +
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let f := fun H : Ideal O => (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
    markedCompletedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) (fun A => d (H^3*A))
  have hf := marked_cube_inverse_finite_support Ψ W hW X hX d
  have hs : Summable (fun H : Ideal O => if (Ideal.absNorm H : ℝ)<H₀ then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  have hl : Summable (fun H : Ideal O => if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  rw [marked_cube_inverse Ψ W hW X hX d,←marked_large_cube_reopen Ψ W hW X H₀ hX d]
  change (∑' H,f H)=(∑' H,if (Ideal.absNorm H : ℝ)<H₀ then f H else 0)+
    ∑' H,if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0
  rw [← hs.tsum_add hl]
  apply tsum_congr
  intro H
  by_cases h : (Ideal.absNorm H : ℝ)<H₀
  · simp [h,not_le.mpr h]
  · simp [h,le_of_not_gt h]

end
end SevenEighths.InverseMoment

end OAI

end Source2651

/- Original source: OAI/NumberTheory/DirichletL/Descent/CompletionSupport.lean; sha256: 8ef313badbdb96c8155ac30dfe1e96d72899a4a1ef27087a29eacd82af4273a0 -/
section Source2652
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem marked_large_cube_sum_comm (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0<X) (d : Ideal O → ℂ) :
    (∑'I:Ideal O,∑'B:Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3)) =
      ∑'B:Ideal O,∑'I:Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B*d (I*B^3) := by
  let a : Ideal O×Ideal O → ℂ := fun p=>largeCubeCoefficient H₀ p.2*summand Ψ W X p.1 p.2*d (p.1*p.2^3)
  have hf : (Function.support a).Finite :=
    (completedT_finite_support Ψ W hW X hX).subset (by
      intro p hp
      exact fun h=>hp (by simp only [a,h,mul_zero,zero_mul]))
  have hs : Summable a := summable_of_hasFiniteSupport hf
  let e := Equiv.prodComm (Ideal O) (Ideal O)
  have ht : Summable (fun p=>a (e p)) := e.summable_iff.mpr hs
  calc
    _ = ∑'p:Ideal O×Ideal O,a p := hs.tsum_prod.symm
    _ = ∑'p:Ideal O×Ideal O,a (e p) := (e.tsum_eq a).symm
    _ = _ := ht.tsum_prod

theorem marked_large_cube_sum_finite (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : O →* ℂ) (m f z : O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) (d : Ideal O → ℂ) :
    (∑'I:Ideal O,∑'B:Ideal O,largeCubeCoefficient H₀ B*summand (rowTwist Ψ m f z) W X I B*d (I*B^3)) =
      ∑B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑'I:Ideal O,summand (rowTwist Ψ m f z) W X I B*d (I*B^3) := by
  rw [marked_large_cube_sum_comm _ W hWc X H₀ hX d]
  simp only [mul_assoc, tsum_mul_left]
  apply tsum_eq_sum
  intro B hB
  have hz : ∀I:Ideal O,summand (rowTwist Ψ m f z) W X I B=0 := by
    intro I
    by_contra hn
    exact hB (summand_cube_support S D hSp Ψ m f z hm W b X hX hW hD I B hn)
  simp only [hz,tsum_zero,mul_zero,zero_mul]

theorem marked_inner_completed_sum (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (hX : 0<X)
    (B : Ideal O) (hB : B≠0) (d : Ideal O → ℂ) :
    (∑'I:Ideal O,summand Ψ W X I B*d (I*B^3)) =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        ∑'I:Ideal O,columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))*d (I*B^3) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := div_pos hX (pow_pos hN _)
  have ht (I:Ideal O) : summand Ψ W X I B =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        (columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
    have harg : (Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X =
        (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3) := by
      rw [div_div_eq_mul_div]
    have hn := vstar_source_normalization Ψ W (X/(Ideal.absNorm B:ℝ)^3) hY I
    calc
      _ = cubeWeight Ψ B * (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ) *
          Vstar W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
        rw [summand,harg]
        ring
      _ = _ := by rw [hn]; ring
  simp_rw [ht]
  simp only [mul_assoc, tsum_mul_left]

end
end SevenEighths.InverseMoment

end OAI

end Source2652

/- Original source: OAI/NumberTheory/DirichletL/Descent/CompletePool.lean; sha256: e4be53e0107ea83d7c75232b2bddb2194640a5ef56178f5e187d454cb6a0695c -/
section Source2653
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

theorem marked_selected_column_sum (F : Finset (Ideal O))
    (hF : ∀I∈F,CanonicalQuadraticSieve.Admissible I)
    (Ψ : O →* ℂ) (m f z : O) (W : ℕ → ℂ) (d : Ideal O → ℂ) :
    let p := CanonicalQuadraticSieve.poolPrimary F
    let hp := CanonicalQuadraticSieve.poolPrimary_ne_zero F hF
    letI : ∀i:ConcretePrimeRowBridge.primePool F,(Ideal.span {p i}).IsMaximal :=
      fun i=>by rw [CanonicalQuadraticSieve.poolPrimary_span F hF i]; infer_instance
    let hcop := CanonicalQuadraticSieve.poolPrimary_coprime F hF
    let hg := CanonicalQuadraticSieve.poolPrimary_good F hF
    (∑I∈F,columnWeight (rowTwist Ψ m f z) I * W (Ideal.absNorm I)*d I) =
      ∑S∈(Finset.univ:Finset (ConcretePrimeRowBridge.primePool F)).powerset,
        canonicalSourceCoefficient p hp hcop hg Ψ m f (fun T=>InitialMeanSquare.selectedIdealTest F W T*d (∏i∈T,i.val)) S *
          finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z := by
  dsimp only
  let : ∀i:ConcretePrimeRowBridge.primePool F,
      (Ideal.span {CanonicalQuadraticSieve.poolPrimary F i}).IsMaximal :=
    fun i=>by rw [CanonicalQuadraticSieve.poolPrimary_span F hF i]; infer_instance
  rw [InitialMeanSquare.sum_selected_ideals F (fun I hI=>(hF I hI).2.1)]
  apply Finset.sum_congr rfl
  intro S hS
  have hspan : (Ideal.span {∏i∈S,CanonicalQuadraticSieve.poolPrimary F i}) = ∏i∈S,i.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact Finset.prod_congr rfl (fun i _=>CanonicalQuadraticSieve.poolPrimary_span F hF i)
  have hpr (i:ConcretePrimeRowBridge.primePool F) :
      ConcretePrimeRowBridge.goodLambda^2∣CanonicalQuadraticSieve.poolPrimary F i-1 :=
    (primaryPrime_spec i.val (CanonicalQuadraticSieve.poolPrimary_ne_zero F hF i)).2.2.2
  have h := columnWeight_finset (CanonicalQuadraticSieve.poolPrimary F)
    (CanonicalQuadraticSieve.poolPrimary_ne_zero F hF)
    (CanonicalQuadraticSieve.poolPrimary_coprime F hF)
    (CanonicalQuadraticSieve.poolPrimary_good F hF) hpr S Ψ m f z
    (fun T=>InitialMeanSquare.selectedIdealTest F W T*d (∏i∈T,i.val))
  rw [hspan] at h
  rw [←h]
  unfold InitialMeanSquare.selectedIdealTest
  split_ifs <;> simp ; ring

theorem marked_weighted_column_tsum_eq (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀ P∈S,Prime P) (Ψ : O →* ℂ) (m f z : O) (hm : ∀ P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0 → t≤b) (hD : b*X≤D) (d : Ideal O → ℂ) :
    (∑' I:Ideal O,columnWeight (rowTwist Ψ m f z) I*W ((Ideal.absNorm I:ℝ)/X)*d I) =
      ∑ I∈InitialMeanSquare.outsideSquarefreeIdeals S D,
        columnWeight (rowTwist Ψ m f z) I*W ((Ideal.absNorm I:ℝ)/X)*d I := by
  apply tsum_eq_sum
  intro I hI
  have hz : columnWeight (rowTwist Ψ m f z) I*W ((Ideal.absNorm I:ℝ)/X)=0 := by
    by_contra hn
    exact hI (weighted_column_support S D hSp Ψ m f z hm W b X hX hW hD hn)
  rw [hz,zero_mul]

theorem marked_complete_pool_eq_global (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0 → t≤b) (hD : b*X≤D) (d : Ideal O → ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    fixedChildRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ Ψ m
      (fun T=>W (primeProductNorm (poolPrimary F) T/X)*d (∏i∈T,i.val)) f z =
    ∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*
      W ((Ideal.absNorm I:ℝ)/X)*d I := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  symm
  rw [marked_weighted_column_tsum_eq S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W b X hX hW hD d]
  have he := marked_selected_column_sum F hF Ψ (m*excludedGenerator S) f z (fun n=>W (n/X)) d
  dsimp only at he
  rw [he]
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro T hT
  rw [canonicalSourceCoefficient_fixed_mask _ _ _ _ Ψ m (excludedGenerator S) f _ T
    (outside_pool_fixed_mask S D hbad hSp T)]
  have ht := InitialMeanSquare.selectedIdealTest_outside S D hbad hSp W b X hX hW hD T
  simp only [canonicalSourceCoefficient,secondChildColumn]
  rw [ht]
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2653

/- Original source: OAI/NumberTheory/DirichletL/Descent/ReopenedMarks.lean; sha256: 0718c8ccb9df1b9bc9a43cd6a752c282a3e8a0c875c5afe2dc2ba6fddcef9912 -/
section Source2654
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))

omit [DecidableEq σ] in
include hinj in
theorem prime_dvd_span_primeProduct (S : Finset ι) (v : ι→ℕ) (i : ι) :
    (Ideal.span {p i}:Ideal O)∣Ideal.span {primeProduct p S v} ↔ i∈S ∧ 0<v i := by
  simp only [primeProduct,FiniteGaussPhase.span_finset_prod,←Ideal.span_singleton_pow]
  rw [←dvd_iff_emultiplicity_pos,primeIdealProduct_emultiplicity (fun i=>Ideal.span {p i}) hinj]
  by_cases hi : i∈S <;> simp [hi]

omit [DecidableEq σ] in
include hinj in
theorem prime_dvd_reopened_index (S : Finset ι) (v : ι→₀ℕ) (i : ι) :
    (Ideal.span {p i}:Ideal O)∣(Ideal.span {∏k∈S,p k})*(Ideal.span {primeProduct p v.support v})^3 ↔
      i∈S∪v.support := by
  have hi : Prime (Ideal.span {p i}:Ideal O) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have hs := prime_dvd_span_primeProduct p hinj S (fun _=>1) i
  simp only [primeProduct,pow_one,Nat.zero_lt_one,and_true] at hs
  rw [hi.dvd_mul,hi.dvd_pow_iff_dvd (by decide : (3:ℕ)≠0),hs,
    prime_dvd_span_primeProduct p hinj v.support v i,Finset.mem_union]
  have hv : i∈v.support ↔ 0<v i := by rw [Finsupp.mem_support_iff]; omega
  tauto

include hinj in

omit [DecidableEq σ] in
theorem reopened_whole_mark_divisibility (slots : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (S : Finset ι) (v : ι→₀ℕ) :
    primeMark slots lists a (S∪v.support) =
    ∏j∈slots,∑i∈lists j,if (Ideal.span {p i}:Ideal O)∣
      (Ideal.span {∏k∈S,p k})*(Ideal.span {primeProduct p v.support v})^3 then a j i else 0 := by
  unfold primeMark primeSlot
  simp_rw [prime_dvd_reopened_index p hinj]

theorem reopened_mark_priority (slots : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (S : Finset ι) (v : ι→₀ℕ) :
    primeMark slots lists a (S∪v.support) =
      ∑J∈slots.powerset,primeMark J lists a v.support *
        primeMark (slots\J) (fun j=>lists j\v.support) a S := by
  rw [Finset.union_comm,primeMark_priority]
  simp only [primeMark_residual_lists]

end
end SevenEighths.InverseMoment

end OAI

end Source2654

/- Original source: OAI/NumberTheory/DirichletL/Descent/CompleteMarkedPool.lean; sha256: bebed519aa36ad338824fc1dd6de627adc519720ac3b77d0b8db6c13de031ab1 -/
section Source2655
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

def indexedIdealMark {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (primes : ι→Ideal O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (I : Ideal O) : ℂ :=
  ∏j∈slots,∑i∈lists j,if primes i∣I then a j i else 0

theorem complete_pool_mark {σ : Type*} [DecidableEq σ]
    (F : Finset (Ideal O)) (hF : ∀ I∈F,Admissible I)
    (slots : Finset σ) (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (T : Finset (primePool F)) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a (∏i∈T,i.val) =
      primeMark slots lists a T := by
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hinj : Function.Injective (fun i:primePool F=>Ideal.span {poolPrimary F i}) := by
    intro i j h
    dsimp only at h
    rw [poolPrimary_span F hF i,poolPrimary_span F hF j] at h
    exact Subtype.ext h
  have he := reopened_whole_mark_divisibility (poolPrimary F) hinj slots lists a T 0
  simp only [Finsupp.support_zero,Finset.union_empty,primeProduct,Finset.prod_empty,
    Ideal.span_singleton_one,←Ideal.one_eq_top,one_pow,mul_one] at he
  have hspan : Ideal.span {∏i∈T,poolPrimary F i}=∏i∈T,i.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact Finset.prod_congr rfl (fun i _=>poolPrimary_span F hF i)
  rw [hspan] at he
  simpa only [indexedIdealMark,poolPrimary_span F hF] using he.symm

theorem finiteCanonicalMarkedRow_complete_global {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m f z slots lists a W X =
    ∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a I*W ((Ideal.absNorm I:ℝ)/X) := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  have he := marked_complete_pool_eq_global S D hbad hSp Ψ m f z W b X hX hW hD
    (indexedIdealMark (fun i:primePool F=>i.val) slots lists a)
  dsimp only at he
  have hmark : (fun T:Finset (primePool F)=>W (primeProductNorm (poolPrimary F) T/X)*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (∏i∈T,i.val)) =
      (fun T=>primeMark slots lists a T*W (primeProductNorm (poolPrimary F) T/X)) := by
    funext T
    rw [complete_pool_mark F hF slots lists a T,mul_comm]
  rw [hmark] at he
  unfold finiteCanonicalMarkedRow
  calc
    _ = _ := he
    _ = _ := tsum_congr (fun I=>by ring)

end
end SevenEighths.InverseMoment

end OAI

end Source2655

/- Original source: OAI/NumberTheory/DirichletL/Descent/CompletedReopening.lean; sha256: 5272ee5555c18fdeed0be37f85137022ea73a3f3e2ea77bc15d542c192590f3f -/
section Source2656
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

def outsideCanonicalMarkedRow {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Ψ : O →* ℂ) (m f z : O) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m f z slots lists a W X

theorem outsideCanonicalMarkedRow_cube_split {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      ∑ B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑' I:Ideal O,summand Ψrow W X I B*mark (I*B^3) := by
  dsimp only
  unfold outsideCanonicalMarkedRow
  rw [finiteCanonicalMarkedRow_complete_global S D hbad hSp Ψ m f z W b X hX hW hD]
  rw [marked_completed_cube_inverse_split _ W hWc X H₀ hX]
  rw [marked_large_cube_sum_finite S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W hWc b X H₀ hX hW hD]

theorem outsideCanonicalMarkedRow_reopened {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      ∑ B∈outsideIdealsUpTo S D,
        (largeCubeCoefficient H₀ B*cubeWeight Ψrow B*
          (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹)*
        ∑' I:Ideal O,columnWeight Ψrow I*W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))*mark (I*B^3) := by
  rw [outsideCanonicalMarkedRow_cube_split S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  rw [marked_inner_completed_sum _ W X hX B (outsideIdealsUpTo_ne_bot S D B hB)]
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2656

/- Original source: OAI/NumberTheory/DirichletL/Descent/ReopenedPriority.lean; sha256: 7c82d1994a91abaa3552a6d4ec4b69b32cc24c8832e2b59c40bd193d03701ab8 -/
section Source2657
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varying_reopened_prime_priority
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : O→*ℂ) (m f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : (ι→₀ℕ)→Finset ι→ℂ) (z : O) :
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f
      (fun v S=>primeMark slots lists a (S∪v.support)*V v S) z =
    ∑J∈slots.powerset,varyingReopenedRow p hp hcop hg pool Q
      (fun v=>β v*primeMark J lists a v.support) Ψ m f
      (fun v S=>primeMark (slots\J) (fun j=>lists j\v.support) a S*V v S) z := by
  unfold varyingReopenedRow
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [canonicalSourceCoefficient]
  rw [reopened_mark_priority]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

omit [DecidableEq σ] in
theorem allocated_cube_coefficient_bound
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hJ : J⊆slots) (hslots : (slots : Set σ).PairwiseDisjoint lists)
    (ha : ∀ j∈slots,∀ i∈lists j,‖a j i‖≤1)
    (β : (ι→₀ℕ)→ℂ) (v : ι→₀ℕ) :
    ‖β v*primeMark J lists a v.support‖≤‖β v‖*(2:ℝ)^v.support.card := by
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact primeMark_norm_le_divisor_count J lists a v.support
    (fun i hi j hj hne=>hslots (hJ hi) (hJ hj) hne) (fun j hj i hi=>ha j (hJ hj) i hi)

end
end SevenEighths.InverseMoment

end OAI

end Source2657

/- Original source: OAI/NumberTheory/DirichletL/Descent/ReopenedIdentification.lean; sha256: 113c6ad8673d89301a160f5e069945777c2c3c6640eedc8f12d35043eb6caa54 -/
section Source2658
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

theorem complete_pool_whole_cube_mark {σ : Type*} [DecidableEq σ]
    (F : Finset (Ideal O)) (hF : ∀ I∈F,Admissible I)
    (slots : Finset σ) (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (T : Finset (primePool F)) (v : primePool F→₀ℕ) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a
      ((∏i∈T,i.val)*cubeIdeal F v^3) = primeMark slots lists a (T∪v.support) := by
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hinj : Function.Injective (fun i:primePool F=>Ideal.span {poolPrimary F i}) := by
    intro i j h
    dsimp only at h
    rw [poolPrimary_span F hF i,poolPrimary_span F hF j] at h
    exact Subtype.ext h
  have he := reopened_whole_mark_divisibility (poolPrimary F) hinj slots lists a T v
  have hspan : Ideal.span {∏i∈T,poolPrimary F i}=∏i∈T,i.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact Finset.prod_congr rfl (fun i _=>poolPrimary_span F hF i)
  rw [hspan,cubeIdeal_eq_primeProduct_span F hF v] at he
  simpa only [indexedIdealMark,poolPrimary_span F hF] using he.symm

theorem reopened_marked_global_column {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X : ℝ) (hb : 0≤b) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let Y := X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3
    (∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*W ((Ideal.absNorm I:ℝ)/Y)*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3)) =
    fixedChildRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ Ψ m
      (fun T=>primeMark slots lists a (T∪v.support)*W (primeProductNorm (poolPrimary F) T/Y)) f z := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let Y := X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3
  have hN := norm_at_least_one (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  have hY : 0<Y := by dsimp [Y];positivity
  have hYD : b*Y≤D := (mul_le_mul_of_nonneg_left
    (div_le_self hX.le (one_le_pow₀ hN)) hb).trans hD
  have he := marked_complete_pool_eq_global S D hbad hSp Ψ m f z W b Y hY hW hYD
    (fun I=>indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3))
  dsimp only at he ⊢
  rw [←he]
  congr 1
  funext T
  rw [complete_pool_whole_cube_mark F hF slots lists a T v,mul_comm]

end
end SevenEighths.InverseMoment

end OAI

end Source2658

/- Original source: OAI/NumberTheory/DirichletL/Descent/ReopenedOriginalRow.lean; sha256: b43ad2724fc2a5cd1e9534ddde8c3caf7477462eaad9bf90514088786f87685b -/
section Source2659
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

def markedReopenedCubeBin {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (X H₀ : ℝ)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
  ∑ v∈Q,(largeCubeCoefficient H₀ (cubeIdeal F v)*cubeWeight Ψrow (cubeIdeal F v)*
    (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹)*
    ∑' I:Ideal O,columnWeight Ψrow I*W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3))*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3)

theorem original_marked_split_to_bins {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool F=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      markedReopenedCubeBin S D ((outsideIdealsUpTo S D).image (cubeIndex F)) Ψ m f z W X H₀ slots lists a := by
  rw [outsideCanonicalMarkedRow_reopened S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  dsimp only
  rw [sum_outside_cubeIndex S D]
  rfl

theorem markedReopenedCubeBin_eq_varying {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X H₀ : ℝ) (hb : 0≤b) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β := fun v=>largeCubeCoefficient H₀ (cubeIdeal F v)*
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)*
      (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists a =
      varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q β Ψ m f
        (fun v T=>primeMark slots lists a (T∪v.support)*
          W (primeProductNorm (poolPrimary F) T/(X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3))) z := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  unfold markedReopenedCubeBin varyingReopenedRow
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [reopened_marked_global_column S D hbad hSp Ψ m f z W b X hb hX hW hD slots lists a v]
  rw [cubeWeight_row_factor,cubeIdeal_row F hF v z]
  unfold fixedChildRow
  simp only [Finset.mul_sum,secondChildColumn,canonicalSourceCoefficient]
  apply Finset.sum_congr rfl
  intro T hT
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2659

/- Original source: OAI/NumberTheory/DirichletL/Descent/ReopenedSeparation.lean; sha256: af0ec010d957c8a7fb0e203ca0ffcea6526443af654e5555f6fab46a6d22243c -/
section Source2660
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open CanonicalCubeSeparation JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varyingReopenedRow_integrand
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (Ψ : O →* ℂ) (m f z : O) (H : (ι→₀ℕ)→Finset ι → ℂ) :
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f H z =
      ∑ v ∈ Q, ∑ T ∈ pool.powerset,
        β v * (multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
          canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z) * H v T := by
  unfold varyingReopenedRow
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro T hT
  simp only [canonicalSourceCoefficient]
  ring

theorem varying_canonical_bin_separation
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Ψ : O →* ℂ) (m f z : O) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀ v ∈ Q, B ≤ n v) (hn' : ∀ v ∈ Q, n v ≤ Real.exp 1*B) :
    (∑ v ∈ Q, (β v * (n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹) *
      multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      fixedChildRow p hp hcop hg pool Ψ m
        (fun T => mark v T*W (primeProductNorm p T/(X/(n v)^3))) f z) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          varyingReopenedRow p hp hcop hg pool Q
            (separatedCubeCoefficient β n B ξ) Ψ m f
            (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z*mark v T
  have hsep := reopening_finite_sum W a b ha hs hW V hV Q pool.powerset β A n
    (primeProductNorm p) B ell X hB hell hX hn hn'
    (fun T _ => primeProductNorm_pos p hp T)
  calc
    _ = ∑ v ∈ Q, ∑ T ∈ pool.powerset, (β v * A v T) *
        ((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ *
          W (primeProductNorm p T/(X/(n v)^3))) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [fixedChildRow_coefficient_expansion p hp hcop hg, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      dsimp only [A]
      ring
    _ = _ := by
      rw [hsep]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [varyingReopenedRow_integrand p hp hcop hg]
      simp only [A, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro T hT
      dsimp only [columnLog]
      ring

end
end SevenEighths.InverseMoment

end OAI

end Source2660

/- Original source: OAI/NumberTheory/DirichletL/Descent/ReopenedCommonMeasure.lean; sha256: 65af77d50a947738e074c94ab3e2818589d33acd5c1466d69b75031ec8274ed2 -/
section Source2661
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

theorem markedReopenedCubeBin_separated {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hb : 0≤b) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u,|u|≤columnWindowRadius a b→V u=1)
    (B ell X H₀ : ℝ) (hB : 0<B) (hell : 0<ell) (hX : X=B^3*ell)
    (hD : b*X≤D)
    (hn : ∀ v∈Q,B≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ))
    (hn' : ∀ v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤Real.exp 1*B)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β := fun v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
    let n := fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists weights =
      ((B*Real.sqrt ell:ℝ):ℂ)⁻¹ * ∫ ξ:ℝ,reopeningCoefficient W a b ha hs hW ξ*
        varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
          (separatedCubeCoefficient β n B ξ) Ψ m f
          (fun v T=>primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let β := fun v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
  let n := fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
  have hXp : 0<X := hX ▸ mul_pos (pow_pos hB _) hell
  have hupper : ∀ t,W t≠0→t≤b := fun t ht=>(hs ht).2
  dsimp only
  rw [←varying_canonical_bin_separation (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) W a b ha hs hW V hV
    Finset.univ Q β n (fun v T=>primeMark slots lists weights (T∪v.support))
    Ψ m f z B ell X hB hell hX hn hn']
  unfold markedReopenedCubeBin
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [reopened_marked_global_column S D hbad hSp Ψ m f z W b X hb hXp hupper hD slots lists weights v]
  rw [cubeWeight_row_factor,cubeIdeal_row F hF v z]
  have hc := cube_coefficient_restore H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
    (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  have hc' : β v*(n v:ℂ)⁻¹=largeCubeCoefficient H₀ (cubeIdeal F v)*
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) := by
    simpa only [β,n,Complex.ofReal_natCast] using hc
  rw [hc']
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2661

/- Original source: OAI/NumberTheory/DirichletL/Descent/ReopenedIntegralEnergy.lean; sha256: b72f0437ca9844899acfc4c793f66104c5fd53facbbf9894a85422be9206b778 -/
section Source2662
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalCubeSeparation JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varying_separated_canonical_integrable
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Ψ : O →* ℂ) (m f z : O)
    (b V : 𝓢(ℝ,ℂ)) (B ell : ℝ) :
    Integrable (fun ξ : ℝ => b ξ *
      varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient β n B ξ)
        Ψ m f (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z*mark v T
  have hi := reopening_finite_sum_integrable Q pool.powerset β A n (primeProductNorm p) B ell b V
  convert hi using 1
  funext ξ
  rw [varyingReopenedRow_integrand p hp hcop hg]
  simp only [A,Finset.mul_sum,columnLog]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro T hT
  ring

theorem varying_separated_canonical_family_energy
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O → (ι →₀ ℕ) → ℂ) (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (Ψ : O →* ℂ) (m : O) (b V : 𝓢(ℝ,ℂ))
    (B ell K E : ℝ) (d : ℕ) (hB : 0 < B) (hell : 0 < ell) (hK : 0 < K) (hE : 0 ≤ E)
    (hbound : ∀ ξ : ℝ,
      rowFamilyEnergy labels (fun I z =>
        varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) K ≤
        E*(1+|ξ|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, b ξ *
        varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) K ≤
      (B^2*ell)⁻¹ * E*(∫ ξ : ℝ, ‖b ξ‖*(1+|ξ|)^d)^2 := by
  have hb : Integrable (fun ξ : ℝ => ‖b ξ‖*(1+|ξ|)^d) := by
    simpa only [Real.norm_eq_abs,mul_comm] using weighted_schwartz_integrable b d
  have hφ (I : Ideal O) (z : O) : Integrable (fun ξ : ℝ => b ξ *
      varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
        Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) :=
    varying_separated_canonical_integrable p hp hcop hg pool Q (β I) n mark Ψ m (idealGenerator I) z b V B ell
  have hm := rowFamilyEnergy_integral_polynomial labels K hK b
    (fun I z ξ => varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
      Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z)
    d E hE hb hφ hbound
  have hn : ‖((B*Real.sqrt ell : ℝ) : ℂ)⁻¹‖^2 = (B^2*ell)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (mul_pos hB (Real.sqrt_pos.mpr hell)),inv_pow,mul_pow,Real.sq_sqrt hell.le]
  rw [rowFamilyEnergy_const_mul labels _ K hK, hn]
  convert mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (B^2*ell)⁻¹) using 1 ; ring

end
end SevenEighths.InverseMoment

end OAI

end Source2662

/- Original source: OAI/NumberTheory/DirichletL/Descent/ReopenedBinEnergy.lean; sha256: bad0207308172495388e4b8c2ebc2fbce7c57b648c5a56eb7f6b20fa227f3b15 -/
section Source2663
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

theorem markedReopenedCubeBin_energy
    {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (labels : Finset (Ideal O)) (Ψ : O →* ℂ) (m : O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hb : 0≤b) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X H₀ K E : ℝ) (d : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell) (hD : b*X≤D) (hK : 0 < K) (hE : 0 ≤ E)
    (hn : ∀ v ∈ Q, B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun I v => reopenedCubeCoefficient H₀
      (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    (∀ ξ : ℝ, rowFamilyEnergy labels (fun I z =>
      varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
        (separatedCubeCoefficient (β I) n B ξ) Ψ m (idealGenerator I)
        (fun v T => primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) K ≤
      E*(1+|ξ|)^(2*d)) →
    rowFamilyEnergy labels (fun I z =>
      markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z W X H₀ slots lists weights) K ≤
      (B^2*ell)⁻¹ * E *
        (∫ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by
  dsimp only
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  let β := fun I v => reopenedCubeCoefficient H₀
    (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
  let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
  intro hbound
  have hrows : (fun I z => markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z W X H₀ slots lists weights) =
      (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ *
          varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
            (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
            (separatedCubeCoefficient (β I) n B ξ) Ψ m (idealGenerator I)
            (fun v T => primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) := by
    funext I z
    exact markedReopenedCubeBin_separated S D hbad hSp Q Ψ m (idealGenerator I) z W a b ha hb hs hW V hV
      B ell X H₀ hB hell hX hD hn hn' slots lists weights
  rw [hrows]
  exact varying_separated_canonical_family_energy (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q labels β n (fun v T=>primeMark slots lists weights (T∪v.support)) Ψ m
    (reopeningCoefficient W a b ha hs hW) V B ell K E d hB hell hK hE hbound

end
end SevenEighths.InverseMoment

end OAI

end Source2663

/- Original source: OAI/NumberTheory/DirichletL/Descent/ReopenedBins.lean; sha256: 2c927a68279170fe73593c185de8857e978f5dbf7cdb9d720854eff7d95f5a20 -/
section Source2664
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

theorem marked_column_zero_of_subunit (Ψ : O→*ℂ) (W : ℝ→ℂ) (b Y : ℝ)
    (hY : 0<Y) (hW : ∀ t,W t≠0→t≤b) (hsub : b*Y<1) (mark : Ideal O→ℂ) :
    (∑' I:Ideal O,columnWeight Ψ I*W ((Ideal.absNorm I:ℝ)/Y)*mark I)=0 := by
  suffices hz : ∀ I:Ideal O,columnWeight Ψ I*W ((Ideal.absNorm I:ℝ)/Y)*mark I=0 by
    simp only [hz,tsum_zero]
  intro I
  by_cases hI : I=0
  · simp only [hI,columnWeight_zero,zero_mul]
  have hw : W ((Ideal.absNorm I:ℝ)/Y)=0 := by
    by_contra hn
    have hh := (div_le_iff₀ hY).mp (hW _ hn)
    have hone := norm_at_least_one I hI
    linarith
  simp only [hw,mul_zero,zero_mul]

variable {σ : Type*} [DecidableEq σ]
  (S : Finset (Ideal O)) (D : ℕ)
  (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X H₀ : ℝ)
  (slots : Finset σ)
  (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
  (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)

theorem markedReopenedCubeBin_eq_active (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) :
    markedReopenedCubeBin S D
      ((outsideIdealsUpTo S D).image (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      Ψ m f z W X H₀ slots lists a =
    markedReopenedCubeBin S D (activeCubeExponents S D b X) Ψ m f z W X H₀ slots lists a := by
  unfold markedReopenedCubeBin activeCubeExponents
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hlarge : b*X<(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3 := by
    exact lt_of_not_ge (fun hh=>hn (Finset.mem_filter.mpr ⟨hv,hh⟩))
  have hN : 0<(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ) :=
    lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  have hsub : b*(X/(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3)<1 := by
    rw [←mul_div_assoc]
    exact (div_lt_one (pow_pos hN _)).mpr hlarge
  rw [marked_column_zero_of_subunit _ W b _ (div_pos hX (pow_pos hN _)) hW hsub,mul_zero]

theorem markedReopenedCubeBin_log_bins :
    markedReopenedCubeBin S D (activeCubeExponents S D b X) Ψ m f z W X H₀ slots lists a =
    ∑ j∈cubeLogRange b X,
      markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a := by
  unfold markedReopenedCubeBin
  dsimp only
  exact sum_activeCubeLogBins S D b X _

def markedShortCompletedSum (Ψrow : O→*ℂ) (W : ℝ→ℂ) (X H₀ : ℝ) (mark : Ideal O→ℂ) : ℂ :=
  ∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
    (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
      markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0

theorem original_marked_reopened_binned (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (hWc : HasCompactSupport W) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D) :
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
    markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a) +
    ∑ j∈cubeLogRange b X,
      markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a := by
  rw [original_marked_split_to_bins S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  rw [markedReopenedCubeBin_eq_active S D Ψ m f z W b X H₀ slots lists a hX hW,
    markedReopenedCubeBin_log_bins]
  rfl

theorem original_marked_binned_energy (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (hWc : HasCompactSupport W) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D) :
    ‖outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 ≤
    2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2 +
    (cubeLogRange b X).card*∑ j∈cubeLogRange b X,
      ‖markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a‖^2) := by
  have hs := norm_add_sum_sq_le (cubeLogRange b X)
    (markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a))
    (fun j=>markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a)
  rw [←original_marked_reopened_binned S D Ψ m f z W b X H₀ slots lists a hbad hSp hWc hX hW hD] at hs
  have hn : ‖outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 =
      X*‖(Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg X),
      mul_pow,inv_pow,Real.sq_sqrt hX.le]
    field_simp
  rw [hn]
  convert mul_le_mul_of_nonneg_left hs hX.le using 1 ; ring

end
end SevenEighths.InverseMoment

end OAI

end Source2664

/- Original source: OAI/NumberTheory/DirichletL/Descent/ShortCompletionEnergy.lean; sha256: 7d876ef4e5731a96bb47bf146004ea212ecb0af6742f34fa5720d7b4f2434ac4 -/
section Source2665
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem markedShortCompletedSum_eq (Ψ : O →* ℂ) (W : ℝ → ℂ) (X H₀ : ℝ) (mark : Ideal O→ℂ) :
    markedShortCompletedSum Ψ W X H₀ mark = ∑H∈shortCubeRange H₀,
      (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) := by
  unfold markedShortCompletedSum
  rw [tsum_eq_sum (s:=shortCubeRange H₀)]
  · exact Finset.sum_congr rfl (fun H hH => ite_eq_left ((mem_shortCubeRange H₀ H).mp hH).2)
  · intro H hH
    by_cases hz : H=0
    · simp [hz]
    · have hn : ¬(Ideal.absNorm H:ℝ)<H₀ := fun hn => hH ((mem_shortCubeRange H₀ H).mpr ⟨hz,hn⟩)
      exact ite_eq_right hn

theorem marked_short_completed_energy {κ : Type*} [Fintype κ]
    (Ψ : κ → O →* ℂ) (hΨ : ∀k z,‖Ψ k z‖≤1)
    (mark : κ→Ideal O→ℂ) (W : ℝ → ℂ) (X H₀ A : ℝ) (hA : 0≤A)
    (hcompleted : ∀H∈shortCubeRange H₀,
      (∑k,‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2)≤A) :
    (∑k,‖markedShortCompletedSum (Ψ k) W X H₀ (mark k)‖^2)≤
      A*(256*(columnDyadicLength H₀+1:ℝ))^2 := by
  let S := shortCubeRange H₀
  let lengthScale : ℝ := ∑H∈S,1/(Ideal.absNorm H:ℝ)
  have hS (H : Ideal O) (hH : H∈S) : H≠0 := ((mem_shortCubeRange H₀ H).mp hH).1
  have hn (H : Ideal O) (hH : H∈S) : 0<(Ideal.absNorm H:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS H hH (Ideal.absNorm_eq_zero_iff.mp hz))
  have hL : 0≤lengthScale := Finset.sum_nonneg (fun H hH => by positivity)
  have hb (k : κ) : ‖markedShortCompletedSum (Ψ k) W X H₀ (mark k)‖^2≤
      lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2 := by
    rw [markedShortCompletedSum_eq]
    apply (ideal_reciprocal_cauchy S hS _).trans
    apply mul_le_mul_of_nonneg_left _ hL
    apply Finset.sum_le_sum
    intro H hH
    rw [norm_mul]
    calc
      _ ≤ (Ideal.absNorm H:ℝ)*((1/(Ideal.absNorm H:ℝ))*‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖)^2 := by
        gcongr
        exact cube_inverse_weight_norm (Ψ k) (hΨ k) H
      _ = _ := by field_simp [(hn H hH).ne']
  have hsum : (∑k,‖markedShortCompletedSum (Ψ k) W X H₀ (mark k)‖^2)≤A*lengthScale^2 := by
    calc
      _ ≤ ∑k,lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2 :=
        Finset.sum_le_sum (fun k _ => hb k)
      _ = lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*∑k,‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro H hH
        rw [←Finset.mul_sum]
      _ ≤ lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*A := by
        gcongr with H hH
        exact hcompleted H hH
      _ = A*lengthScale^2 := by rw [←Finset.sum_mul]; change lengthScale*(lengthScale*A)=A*lengthScale^2; ring
  have hbound : lengthScale≤256*(columnDyadicLength H₀+1:ℝ) :=
    finite_inverse_norm_sum S H₀ hS (fun H hH => ((mem_shortCubeRange H₀ H).mp hH).2.le)
  exact hsum.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hbound 2) hA)

end
end SevenEighths.InverseMoment

end OAI

end Source2665

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CompletedRowsEnergy.lean; sha256: 0549d3c08fdbb81bf419fa734dd8428f6e9931b4f0548b084cc0bc7ebf1b9fbd -/
section Source2666
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem canonical_completed_rows_energy (q : ℕ) (hq : q≠0)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η)
    (hη1 : η≤1) (hηc : η≤cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (F : Ideal Eis) (_hF : Squarefree F)
      (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,∀ P∈lists i,P∉reflectionExcludedPrimes q) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/32) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_completed_fiber_energy q hq lo hi hlo W hWs hW
    L cstar η hL hcstar hη hη1 hηc rmax
  obtain ⟨D,hD,ha⟩ := completed_representative_aggregation (2*L+1) (cstar/32) (by linarith) (by positivity)
  let B : Ideal Eis := Ideal.span {excludedGenerator (reflectionExcludedPrimes q)}
  let Z₁ := max Z₀ (max 2 (Ideal.absNorm B:ℝ))
  refine ⟨degree,D*C,Z₁,mul_pos hD hC,lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hexcluded
    hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  have hZZ : Z₀≤Z := (le_max_left _ _).trans hZ
  have hZ2 : 2≤Z := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hZ
  have hz : 0<Z := by linarith
  have hz1 : 1≤Z := by linarith
  have hBn : (Ideal.absNorm B:ℝ)≤Z := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hZ
  have hmask : ActualFiber.maskIdeal q m F=B*F*Ideal.span {m} := by
    dsimp only [ActualFiber.maskIdeal,ActualFiber.maskElement,B]
    rw [←Ideal.span_singleton_mul_span_singleton]
    ring
  have hmaskn : (Ideal.absNorm (ActualFiber.maskIdeal q m F):ℝ)≤Z^(2*L+1) := by
    rw [hmask]
    exact canonical_mask_norm_cap B F (Ideal.span {m}) Z V L L hz1 hBn hFn hRn hVc le_rfl
  have hparentn : ∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(2*L+1) := by
    intro I hI
    exact ⟨(hparents I hI).1,(hparents I hI).2.trans
      (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))⟩
  have hh := ha Z hZ2 parents (ActualFiber.maskIdeal q m F) hparentn
    (ActualFiber.maskIdeal_ne_zero q m hm F hF.ne_zero) hmaskn
    (C*(1+‖θ‖)^degree*Z^(N+V-cstar/16))
    (fun I => ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
      (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
    (by positivity) (fun J hJ => he (σ:=σ) J F (hparents J hJ).1 hF m hm Z N V M z₀ margin hhat d
      hZZ hN hM hMc hVc hzc hhc (hparents J hJ).2 hFn hRn hinv hmargin hVd hhd hd
      parents hparents hcard lists H hdis hmax hgood hprime hodd hexcluded hH1 hH hprod
      Ψ hΨnorm hΨperiod u θ w hw)
  apply hh.trans_eq
  calc
    _ = (D*C)*(1+‖θ‖)^degree*(Z^(cstar/32)*Z^(N+V-cstar/16)) := by ring
    _ = _ := by rw [←Real.rpow_add hz]; congr 2; ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source2666

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalCompletedEnergy.lean; sha256: 792b42ea2facf31aea6d7970c19d4e9547884f48ef7238c8862d70b6713ac300 -/
section Source2667
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem canonical_original_completed_energy (q : ℕ) (hq : q≠0)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η)
    (hη1 : η≤1) (hηc : η≤cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (F : Ideal Eis) (_hF : Squarefree F)
      (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/32) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_completed_rows_energy q hq lo hi hlo W hWs hW
    L cstar η hL hcstar hη hη1 hηc rmax
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let S := reflectionExcludedPrimes q
  let lists' := punctureLists lists S
  have hsub (i : σ) : lists' i⊆lists i := Finset.filter_subset _ _
  let w' : ∀ i,lists' i→ℂ := fun i P => w i ⟨P.val,hsub i P.property⟩
  have hh := he (σ:=σ) F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists' H
    (fun i j hij => (hdis hij).mono (hsub i) (hsub j))
    (fun i P hP => hmax i P (hsub i hP)) (fun i P hP => hgood i P (hsub i hP))
    (fun i P hP => hprime i P (hsub i hP)) (fun i P hP => hodd i P (hsub i hP))
    (fun i P hP => (Finset.mem_filter.mp hP).2) hH1 (fun i P hP => hH i P (hsub i hP)) hprod
    Ψ hΨnorm hΨperiod u θ w' (fun i P => hw i ⟨P.val,hsub i P.property⟩)
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro I hI
  exact congrArg (fun z : ℂ => ‖z‖^2) (original_completed_puncture_lists lists hprime S Ψ m
    (ConcretePrimeRowBridge.idealGenerator F) (u.val*ConcretePrimeRowBridge.idealGenerator I)
    (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) w)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source2667

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CubeSlots.lean; sha256: eeff4c247ffdf8e554c75d1913cf4573a8579ec1cb714b003eb76c15b72bfffb -/
section Source2668
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma prime_dvd_cube_mul (P H A : Ideal Eis) (hP : Prime P) :
    P∣H^3*A ↔ P∣H ∨ P∣A := by
  constructor
  · intro h
    rcases hP.dvd_mul.mp h with h|h
    · exact Or.inl (hP.dvd_of_dvd_pow h)
    · exact Or.inr h
  · rintro (h|h)
    · exact dvd_mul_of_dvd_left (dvd_pow h (by decide : (3:ℕ)≠0)) A
    · exact dvd_mul_of_dvd_right h _

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def cubeActiveSlots (H : Ideal Eis) (S : PrimeFamily σ) : Finset σ :=
  Finset.univ.filter (fun i => ¬S.ideal i∣H)

omit [DecidableEq σ] in
lemma cube_shifted_mark (H A : Ideal Eis) (S : PrimeFamily σ) :
    (∏ i,if S.ideal i∣H^3*A then (1:ℂ) else 0)=
      ∏ i∈cubeActiveSlots H S,if S.ideal i∣A then (1:ℂ) else 0 := by
  rw [cubeActiveSlots,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  have hp : Prime (S.ideal i) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  rw [prime_dvd_cube_mul _ H A hp]
  by_cases hh : S.ideal i∣H
  · simp only [hh,true_or,ite_true,not_true_eq_false,ite_false]
  · simp only [hh,false_or,not_false_eq_true,ite_true]

omit [DecidableEq σ] in
lemma cube_shifted_mark_restrict (H A : Ideal Eis) (S : PrimeFamily σ) :
    (∏ i,if S.ideal i∣H^3*A then (1:ℂ) else 0)=
      ∏ i : cubeActiveSlots H S,if (S.restrict (cubeActiveSlots H S)).ideal i∣A then (1:ℂ) else 0 := by
  rw [cube_shifted_mark]
  symm
  exact Finset.prod_coe_sort (cubeActiveSlots H S) (fun i => if S.ideal i∣A then (1:ℂ) else 0)

omit [DecidableEq σ] in
theorem markedCompletedT_cube_shift (Ψ : Eis→*ℂ) (W : ℝ→ℂ) (X : ℝ)
    (H : Ideal Eis) (S : PrimeFamily σ) :
    markedCompletedT Ψ W X (fun A => ∏ i,if S.ideal i∣H^3*A then (1:ℂ) else 0)=
      markedCompletedT Ψ W X
        (fun A => ∏ i : cubeActiveSlots H S,if (S.restrict (cubeActiveSlots H S)).ideal i∣A then (1:ℂ) else 0) := by
  congr 1
  funext A
  exact cube_shifted_mark_restrict H A S

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source2668

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CubeSlotChoices.lean; sha256: 0df5cc8a920a428e703ce361442efbc01a27e21618c6c834b9b5f7eb7701c554 -/
section Source2669
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

 def cubeDivList (H : Ideal Eis) (L : Finset (Ideal Eis)) : Finset (Ideal Eis) := L.filter (fun P => P∣H)
 def cubeAwayList (H : Ideal Eis) (L : Finset (Ideal Eis)) : Finset (Ideal Eis) := L.filter (fun P => ¬P∣H)
 def cubeChoiceActive (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) (p : ∀ i,L i) : Finset σ :=
  Finset.univ.filter (fun i => ¬(p i).val∣H)

abbrev CubeSlotChoices (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :=
  Σ T : Finset σ,(∀ i : {i // i∉T},cubeDivList H (L i.val))×(∀ i : T,cubeAwayList H (L i.val))

def cubeChoicesJoin (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) (x : CubeSlotChoices H L) : ∀ i,L i :=
  (slotChoiceSplit L x.1).symm
    (fun i => ⟨(x.2.2 i).val,(Finset.mem_filter.mp (x.2.2 i).property).1⟩,
     fun i => ⟨(x.2.1 i).val,(Finset.mem_filter.mp (x.2.1 i).property).1⟩)

lemma cubeChoicesJoin_label (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) (x : CubeSlotChoices H L) :
    cubeChoiceActive H L (cubeChoicesJoin H L x)=x.1 := by
  rcases x with ⟨T,b,a⟩
  ext i
  simp only [cubeChoiceActive,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hi : i∈T
  · have ha := (Finset.mem_filter.mp (a ⟨i,hi⟩).property).2
    have he := slotChoiceSplit_active L T
      (fun j => ⟨(a j).val,(Finset.mem_filter.mp (a j).property).1⟩)
      (fun j => ⟨(b j).val,(Finset.mem_filter.mp (b j).property).1⟩) ⟨i,hi⟩
    dsimp only [cubeChoicesJoin]
    rw [he]
    exact iff_of_true ha hi
  · have hb := (Finset.mem_filter.mp (b ⟨i,hi⟩).property).2
    have he := slotChoiceSplit_inactive L T
      (fun j => ⟨(a j).val,(Finset.mem_filter.mp (a j).property).1⟩)
      (fun j => ⟨(b j).val,(Finset.mem_filter.mp (b j).property).1⟩) ⟨i,hi⟩
    dsimp only [cubeChoicesJoin]
    rw [he]
    exact iff_of_false (not_not_intro hb) hi

lemma cubeChoicesJoin_injective (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :
    Function.Injective (cubeChoicesJoin H L) := by
  rintro ⟨T,b,a⟩ ⟨U,d,c⟩ he
  have ht := congrArg (cubeChoiceActive H L) he
  rw [cubeChoicesJoin_label,cubeChoicesJoin_label] at ht
  dsimp only at ht
  subst U
  apply congrArg (fun q => (⟨T,q⟩ : CubeSlotChoices H L))
  have hx := congrArg (slotChoiceSplit L T) he
  simp only [cubeChoicesJoin,Equiv.apply_symm_apply] at hx
  apply Prod.ext
  · funext i
    apply Subtype.ext
    exact congrArg (fun q => (q.2 i).val) hx
  · funext i
    apply Subtype.ext
    exact congrArg (fun q => (q.1 i).val) hx

lemma cubeChoicesJoin_surjective (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :
    Function.Surjective (cubeChoicesJoin H L) := by
  intro p
  let T := cubeChoiceActive H L p
  let a : ∀ i : T,cubeAwayList H (L i.val) := fun i =>
    ⟨(p i.val).val,Finset.mem_filter.mpr ⟨(p i.val).property,(Finset.mem_filter.mp i.property).2⟩⟩
  have hd (i : {i // i∉T}) : (p i.val).val∣H := by
    by_contra hi
    exact i.property (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  let b : ∀ i : {i // i∉T},cubeDivList H (L i.val) := fun i =>
    ⟨(p i.val).val,Finset.mem_filter.mpr ⟨(p i.val).property,hd i⟩⟩
  refine ⟨⟨T,b,a⟩,?_⟩
  apply (slotChoiceSplit L T).injective
  simp only [cubeChoicesJoin,Equiv.apply_symm_apply]
  apply Prod.ext <;> funext i <;> apply Subtype.ext <;> rfl

def cubeSlotChoiceEquiv (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :
    CubeSlotChoices H L ≃ (∀ i,L i) :=
  Equiv.ofBijective (cubeChoicesJoin H L) ⟨cubeChoicesJoin_injective H L,cubeChoicesJoin_surjective H L⟩

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source2669

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CubeSlotSource.lean; sha256: 27a444721e40e117289c98705877ee138826a3a68ffbb7861ac2a4165ca10cf5 -/
section Source2670
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (H : Ideal Eis) (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

include hmax hgood in
lemma cubeJoined_mark (x : CubeSlotChoices H L) (A : Ideal Eis) :
    (∏ i,if (cubeChoicesJoin H L x i).val∣H^3*A then (1:ℂ) else 0)=
      ∏ i : x.1,if (x.2.2 i).val∣A then (1:ℂ) else 0 := by
  have hs := cube_shifted_mark H A (slotChoiceFamily L hmax hgood (cubeChoicesJoin H L x))
  have hl : cubeActiveSlots H (slotChoiceFamily L hmax hgood (cubeChoicesJoin H L x))=x.1 :=
    cubeChoicesJoin_label H L x
  rw [hl] at hs
  apply hs.trans
  rw [←Finset.prod_coe_sort x.1]
  apply Finset.prod_congr rfl
  intro i hi
  have he := slotChoiceSplit_active L x.1
    (fun i => ⟨(x.2.2 i).val,(Finset.mem_filter.mp (x.2.2 i).property).1⟩)
    (fun i => ⟨(x.2.1 i).val,(Finset.mem_filter.mp (x.2.1 i).property).1⟩) i
  change (if ((slotChoiceSplit L x.1).symm _ i.val).val∣A then (1:ℂ) else 0)=_
  rw [he]

include hmax hgood in
lemma cubeJoined_completed (x : CubeSlotChoices H L) (Ψ : Eis→*ℂ) (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT Ψ W X
      (fun A => ∏ i,if (cubeChoicesJoin H L x i).val∣H^3*A then (1:ℂ) else 0)=
    markedCompletedT Ψ W X
      (fun A => ∏ i : x.1,if (x.2.2 i).val∣A then (1:ℂ) else 0) := by
  congr 1
  funext A
  exact cubeJoined_mark H L hmax hgood x A

lemma cubeJoined_coefficient (x : CubeSlotChoices H L) (w : ∀ i,L i→ℂ) :
    (∏ i,w i (cubeChoicesJoin H L x i))=
      (∏ i : {i // i∉x.1},w i.val ⟨(x.2.1 i).val,(Finset.mem_filter.mp (x.2.1 i).property).1⟩)*
      (∏ i : x.1,w i.val ⟨(x.2.2 i).val,(Finset.mem_filter.mp (x.2.2 i).property).1⟩) := by
  exact (slot_coefficient_split L x.1 w _ _).trans (mul_comm _ _)

def cubeAbsorbedCoefficient (w : ∀ i,L i→ℂ) (T : Finset σ) : ℂ :=
  ∑ b : ∀ i : {i // i∉T},cubeDivList H (L i.val),
    ∏ i : {i // i∉T},w i.val ⟨(b i).val,(Finset.mem_filter.mp (b i).property).1⟩

lemma cubeAbsorbedCoefficient_product (w : ∀ i,L i→ℂ) (T : Finset σ) :
    cubeAbsorbedCoefficient H L w T=
      ∏ i : {i // i∉T},∑ P : cubeDivList H (L i.val),w i.val ⟨P.val,(Finset.mem_filter.mp P.property).1⟩ :=
  (Fintype.prod_sum (fun (i : {i // i∉T}) (P : cubeDivList H (L i.val)) =>
    w i.val ⟨P.val,(Finset.mem_filter.mp P.property).1⟩)).symm

include hmax hgood

theorem original_cube_shifted_tuple_source (w : ∀ i,L i→ℂ)
    (Ψ : Eis→*ℂ) (W : ℝ→ℂ) (X : ℝ) :
    (∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT Ψ W X
      (fun A => ∏ i,if (p i).val∣H^3*A then (1:ℂ) else 0))=
    ∑ T : Finset σ,cubeAbsorbedCoefficient H L w T*
      ∑ a : ∀ i : T,cubeAwayList H (L i.val),
        (∏ i : T,w i.val ⟨(a i).val,(Finset.mem_filter.mp (a i).property).1⟩)*
          markedCompletedT Ψ W X (fun A => ∏ i : T,if (a i).val∣A then (1:ℂ) else 0) := by
  rw [←(cubeSlotChoiceEquiv H L).sum_comp]
  change (∑ x : CubeSlotChoices H L,(∏ i,w i (cubeChoicesJoin H L x i))*
    markedCompletedT Ψ W X (fun A => ∏ i,if (cubeChoicesJoin H L x i).val∣H^3*A then (1:ℂ) else 0))=_
  simp_rw [cubeJoined_completed H L hmax hgood,cubeJoined_coefficient]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Fintype.sum_prod_type]
  simp only [cubeAbsorbedCoefficient,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source2670

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CubeSlotBounds.lean; sha256: a7b420f75fc4a2fdadd7341e5e997f617802e019c4b112fa8c20e2c1b0e915b7 -/
section Source2671
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
open IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma cubeDivList_card (H : Ideal Eis) (hH : H≠0) (L : Finset (Ideal Eis)) :
    (cubeDivList H L).card≤(idealDivisors H).card := by
  apply Finset.card_le_card
  intro P hP
  exact (mem_idealDivisors hH).mpr (Finset.mem_filter.mp hP).2

lemma cube_divisor_card_one (H : Ideal Eis) (hH : H≠0) :
    (1:ℝ)≤(idealDivisors H).card := by
  exact_mod_cast Finset.card_pos.mpr ⟨1,(mem_idealDivisors hH).mpr (one_dvd H)⟩

lemma cubeAbsorbedCoefficient_norm (H : Ideal Eis) (hH : H≠0)
    (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1) (T : Finset σ) (rmax : ℕ)
    (hr : Fintype.card σ≤rmax) :
    ‖cubeAbsorbedCoefficient H L w T‖≤((idealDivisors H).card:ℝ)^rmax := by
  rw [cubeAbsorbedCoefficient_product,norm_prod]
  calc
    _ ≤ ∏ i : {i // i∉T},((idealDivisors H).card:ℝ) := by
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      intro i hi
      calc
        _ ≤ ∑ P : cubeDivList H (L i.val),‖w i.val ⟨P.val,(Finset.mem_filter.mp P.property).1⟩‖ := norm_sum_le _ _
        _ ≤ ∑ _P : cubeDivList H (L i.val),(1:ℝ) := Finset.sum_le_sum (fun P _ => hw _ _)
        _ = ((cubeDivList H (L i.val)).card:ℝ) := by simp
        _ ≤ _ := Nat.cast_le.mpr (cubeDivList_card H hH _)
    _ = ((idealDivisors H).card:ℝ)^(Fintype.card {i // i∉T}) := by simp
    _ ≤ _ := pow_le_pow_right₀ (cube_divisor_card_one H hH)
      ((Fintype.card_subtype_le _).trans hr)

lemma cubeAbsorbedCoefficient_mass (H : Ideal Eis) (hH : H≠0)
    (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1) (rmax : ℕ) (hr : Fintype.card σ≤rmax) :
    (∑ T : Finset σ,‖cubeAbsorbedCoefficient H L w T‖)≤
      (2:ℝ)^rmax*((idealDivisors H).card:ℝ)^rmax := by
  calc
    _ ≤ ∑ _T : Finset σ,((idealDivisors H).card:ℝ)^rmax :=
      Finset.sum_le_sum (fun T _ => cubeAbsorbedCoefficient_norm H hH L w hw T rmax hr)
    _ = (2:ℝ)^(Fintype.card σ)*((idealDivisors H).card:ℝ)^rmax := by
      simp [Fintype.card_finset]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hr) (by positivity)

theorem cubeAbsorbedCoefficient_small_power (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      (H : Ideal Eis),H≠0 → ∀ (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ),
      (∀ i P,‖w i P‖≤1) → Fintype.card σ≤rmax →
      (∑ T : Finset σ,‖cubeAbsorbedCoefficient H L w T‖)^2≤C*(Ideal.absNorm H:ℝ)^ε := by
  let δ : ℝ := ε/(2*rmax+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨((2:ℝ)^rmax*D^rmax)^2,by positivity,?_⟩
  intro σ _ _ H hH L w hw hr
  have hn : (1:ℝ)≤Ideal.absNorm H := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hH (Ideal.absNorm_eq_zero_iff.mp h))
  have hn0 : 0<(Ideal.absNorm H:ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hde : δ*(rmax:ℝ)*2≤ε := by
    dsimp [δ]
    have hp : (0:ℝ)<2*rmax+1 := by positivity
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  calc
    _ ≤ ((2:ℝ)^rmax*((idealDivisors H).card:ℝ)^rmax)^2 := by
      exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
        (cubeAbsorbedCoefficient_mass H hH L w hw rmax hr) 2
    _ ≤ ((2:ℝ)^rmax*(D*(Ideal.absNorm H:ℝ)^δ)^rmax)^2 := by gcongr; exact hd H hH
    _ = ((2:ℝ)^rmax*D^rmax)^2*(Ideal.absNorm H:ℝ)^(δ*(rmax:ℝ)*2) := by
      have he := Real.rpow_mul_natCast hn0.le (δ*(rmax:ℝ)) 2
      norm_num only [Nat.cast_ofNat] at he
      rw [he,Real.rpow_mul_natCast hn0.le δ rmax]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn hde) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source2671

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CubeSlotEnergy.lean; sha256: 93e2d4789ed6fc3eae430232043f3c327a7550cd9a87d292441194159b3450f4 -/
section Source2672
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem original_cube_shifted_tuple_energy (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ κ : Type*} [Fintype σ] [DecidableEq σ]
      (H : Ideal Eis),H≠0 → ∀ (L : σ→Finset (Ideal Eis))
      (_hmax : ∀ i,∀ P∈L i,P.IsMaximal)
      (_hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
      (w : ∀ i,L i→ℂ), (∀ i P,‖w i P‖≤1) → Fintype.card σ≤rmax →
    ∀ (rows : Finset κ) (Ψ : κ→(Eis→*ℂ)) (W : ℝ→ℂ) (X E : ℝ),0≤E →
      (∀ T : Finset σ,
        (∑ k∈rows,‖∑ a : ∀ i : T,cubeAwayList H (L i.val),
          (∏ i : T,w i.val ⟨(a i).val,(Finset.mem_filter.mp (a i).property).1⟩)*
            markedCompletedT (Ψ k) W X (fun A => ∏ i : T,if (a i).val∣A then (1:ℂ) else 0)‖^2)≤E) →
      (∑ k∈rows,‖∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT (Ψ k) W X
        (fun A => ∏ i,if (p i).val∣H^3*A then (1:ℂ) else 0)‖^2)≤
      C*(Ideal.absNorm H:ℝ)^ε*E := by
  obtain ⟨C,hC,hb⟩ := cubeAbsorbedCoefficient_small_power rmax ε hε
  refine ⟨C,hC,?_⟩
  intro σ κ _ _ H hH L hmax hgood w hw hr rows Ψ W X E hE he
  simp_rw [original_cube_shifted_tuple_source H L hmax hgood w]
  apply (weighted_finite_row_energy_uniform Finset.univ rows (cubeAbsorbedCoefficient H L w)
    (fun T k => ∑ a : ∀ i : T,cubeAwayList H (L i.val),
      (∏ i : T,w i.val ⟨(a i).val,(Finset.mem_filter.mp (a i).property).1⟩)*
        markedCompletedT (Ψ k) W X (fun A => ∏ i : T,if (a i).val∣A then (1:ℂ) else 0)) E
    (fun T _ => he T)).trans
  exact mul_le_mul_of_nonneg_right (hb H hH L w hw hr) hE
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source2672

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CubeCompletedEnergy.lean; sha256: 6cd9403fa9b4a78d86dca6d96497f5fdcbcc8ff450ca4b9a527d44583e536c12 -/
section Source2673
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem canonical_cube_shifted_completed_energy (q : ℕ) (hq : q≠0)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η)
    (hη1 : η≤1) (hηc : η≤cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (F : Ideal Eis) (_hF : Squarefree F)
      (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (Hcube : Ideal Eis),Hcube≠0 → (Ideal.absNorm Hcube:ℝ)≤Z^hhat →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣Hcube^3*A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_original_completed_energy q hq lo hi hlo W hWs hW
    L cstar η hL hcstar hη hη1 hηc rmax
  let ε := cstar/(64*(L+1))
  have hε : 0<ε := by dsimp [ε];positivity
  obtain ⟨D,hD,hcube⟩ := original_cube_shifted_tuple_energy rmax ε hε
  refine ⟨degree,D*C,Z₀,mul_pos hD hC,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨnorm hΨperiod Hcube hcube0 hcuben u θ w hw
  have hz1 : 1≤Z := (lt_of_lt_of_le hZ₀ hZ).le
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hz1
  have hremain (T : Finset σ) :
      (∑ I∈parents,‖∑ a : ∀ i : T,cubeAwayList Hcube (lists i.val),
        (∏ i : T,w i.val ⟨(a i).val,(Finset.mem_filter.mp (a i).property).1⟩)*
          markedCompletedT (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
            (Z^(N-3*hhat)) (fun A => ∏ i : T,if (a i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/32) := by
    have hsub (i : T) : cubeAwayList Hcube (lists i.val)⊆lists i.val := Finset.filter_subset _ _
    have hcardT : Fintype.card T≤rmax := by
      rw [Fintype.card_coe]
      exact (Finset.card_le_univ T).trans hcard
    have hprodT : (∏ i : T,H i.val)≤Z^z₀ := by
      apply le_trans ?_ hprod
      rw [Finset.prod_coe_sort]
      exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ T)
        (fun i hi => (hH1 i).trans' (by norm_num)) (fun i hi hnot => hH1 i)
    exact he (σ:=T) F hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
      hFn hRn hinv hmargin hVd hhd hd parents hparents hcardT
      (fun i : T => cubeAwayList Hcube (lists i.val)) (fun i : T => H i.val)
      (fun i j hij => (hdis (fun he => hij (Subtype.ext he))).mono (hsub i) (hsub j))
      (fun i P hP => hmax i.val P (hsub i hP)) (fun i P hP => hgood i.val P (hsub i hP))
      (fun i P hP => hprime i.val P (hsub i hP)) (fun i P hP => hodd i.val P (hsub i hP))
      (fun i => hH1 i.val) (fun i P hP => hH i.val P (hsub i hP)) hprodT
      Ψ hΨnorm hΨperiod u θ (fun i P => w i.val ⟨P.val,hsub i P.property⟩)
      (fun i P => hw i.val ⟨P.val,hsub i P.property⟩)
  have hh := hcube Hcube hcube0 lists hmax hgood w hw hcard parents
    (fun I => rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
    (Z^(N-3*hhat)) (C*(1+‖θ‖)^degree*Z^(N+V-cstar/32)) (by positivity) hremain
  have hεcap : hhat*ε≤cstar/64 := by
    have hhε : ε*(64*(L+1))=cstar := by dsimp [ε];field_simp
    nlinarith [mul_le_mul_of_nonneg_right hhc hε.le]
  have hn : (Ideal.absNorm Hcube:ℝ)^ε≤Z^(cstar/64) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hcuben hε.le).trans
    rw [←Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hz1 hεcap
  apply hh.trans
  calc
    _ ≤ D*Z^(cstar/64)*(C*(1+‖θ‖)^degree*Z^(N+V-cstar/32)) := by gcongr
    _ = (D*C)*(1+‖θ‖)^degree*(Z^(cstar/64)*Z^(N+V-cstar/32)) := by ring
    _ = _ := by rw [←Real.rpow_add hz];congr 2;ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source2673

/- Original source: OAI/NumberTheory/DirichletL/Descent/ShortReflectedEnergy.lean; sha256: 5cc6cb9b8ac7bc85415147171cf3e11de30b6b7bd63532f39f4ba71005bd0bb2 -/
section Source2674
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open InverseTerminalWidths InverseReflectedPhase CompletedHeight
local notation "Eis"=>ActualEisensteinCubic.O
universe v

def tupleDivisibilityMark {σ:Type v} [Fintype σ] [DecidableEq σ]
    (lists:σ→Finset (Ideal Eis)) (w:∀i,lists i→ℂ) (A:Ideal Eis):ℂ :=
  ∑p:∀i,lists i,(∏i,w i (p i))*∏i,if (p i).val∣A then (1:ℂ) else 0

theorem completed_tuple_mark {σ:Type v} [Fintype σ] [DecidableEq σ]
    (lists:σ→Finset (Ideal Eis)) (w:∀i,lists i→ℂ)
    (Ψ:Eis→*ℂ) (W:ℝ→ℂ) (hW:HasCompactSupport W)
    (X:ℝ) (hX:0<X) (H:Ideal Eis):
    markedCompletedT Ψ W X (fun A=>tupleDivisibilityMark lists w (H^3*A))=
      ∑p:∀i,lists i,(∏i,w i (p i))*markedCompletedT Ψ W X
        (fun A=>∏i,if (p i).val∣H^3*A then (1:ℂ) else 0) := by
  unfold tupleDivisibilityMark
  rw [markedCompletedT_finset_sum Finset.univ Ψ W hW X hX]
  simp only [markedCompletedT_const_mul]

theorem short_cube_exact_scale (Z N:ℝ) (hZ:1<Z) (H:Ideal Eis) (hH:H≠0):
    Z^(N-3*Real.logb Z (Ideal.absNorm H:ℝ))=Z^N/(Ideal.absNorm H:ℝ)^3 := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:0<(Ideal.absNorm H:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (fun hn=>hH (Ideal.absNorm_eq_zero_iff.mp hn))
  rw [Real.rpow_sub hz,show 3*Real.logb Z (Ideal.absNorm H:ℝ)=Real.logb Z (Ideal.absNorm H:ℝ)*3 by ring,
    show Z^(Real.logb Z (Ideal.absNorm H:ℝ)*3)=(Z^(Real.logb Z (Ideal.absNorm H:ℝ)))^3 from
      Real.rpow_mul_natCast hz.le _ 3,Real.rpow_logb hz (ne_of_gt hZ) hn]

theorem canonical_short_completed_energy (q:ℕ) (hq:q≠0)
    (lo hi:ℝ) (hlo:0<lo) (W:ℝ→ℂ)
    (hWs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (L cstar eta:ℝ) (hL:0≤L) (hcstar:0<cstar) (heta:0<eta)
    (heta1:eta≤1) (hetac:eta≤cstar/100000) (rmax:ℕ):
    ∃(degree:ℕ)(C Z₀:ℝ),0<C ∧ 1<Z₀ ∧
    ∀{σ:Type v} [Fintype σ] [DecidableEq σ],∀(F:Ideal Eis)(_hF:Squarefree F)
      (m:Eis)(_hm:m≠0)(Z N V M z₀ margin hcut d:ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hcut≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀(parents:Finset (Ideal Eis)),(∀I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀(lists:σ→Finset (Ideal Eis))(H:σ→ℝ),
      Pairwise (fun i j=>Disjoint (lists i) (lists j)) →
      (∀i,∀P∈lists i,P.IsMaximal) →
      (∀i,∀P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀i,∀P∈lists i,Prime P) → (∀i,∀P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀i,1≤H i) → (∀i,∀P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏i,H i)≤Z^z₀ →
    ∀(Ψ:Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀(u:Eisˣ)(θ:ℝ)(w:∀i,lists i→ℂ),(∀i P,‖w i P‖≤1) →
      (∑I∈parents,‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64)*(256*(columnDyadicLength (Z^hcut)+1:ℝ))^2 := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩:=canonical_cube_shifted_completed_energy q hq lo hi hlo W hWs hW
    L cstar eta hL hcstar heta heta1 hetac rmax
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hcut d hZ hN hM hMc hVc hzc hcutc hFn hRn
    hmargin hreserve hVd hcutd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Ψ hΨ hperiod u θ w hw
  have hZ1:1<Z:=lt_of_lt_of_le hZ₀ hZ
  have hz:0<Z:=zero_lt_one.trans hZ1
  have htw:HasCompactSupport (normTwistedSource W θ):=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((normTwistedSource_support W θ).trans hWs)
  have hcompleted (J:Ideal Eis) (hJ:J∈shortCubeRange (Z^hcut)):
      (∑I∈parents,‖markedCompletedT
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N/(Ideal.absNorm J:ℝ)^3) (fun A=>tupleDivisibilityMark lists w (J^3*A))‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/64):=by
    obtain ⟨hJ0,hJnorm⟩:=(mem_shortCubeRange _ J).mp hJ
    have hn:0<(Ideal.absNorm J:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (fun hn=>hJ0 (Ideal.absNorm_eq_zero_iff.mp hn))
    have hc:Real.logb Z (Ideal.absNorm J:ℝ)≤hcut:=
      (Real.logb_le_iff_le_rpow hZ1 hn).mpr hJnorm.le
    have hjpow:(Ideal.absNorm J:ℝ)≤Z^(Real.logb Z (Ideal.absNorm J:ℝ)):=by
      rw [Real.rpow_logb hz (ne_of_gt hZ1) hn]
    have h:=he F hF m hm Z N V M z₀ margin (Real.logb Z (Ideal.absNorm J:ℝ)) d
      hZ hN hM hMc hVc hzc (hc.trans hcutc) hFn hRn hmargin hreserve hVd (hc.trans hcutd) hd
      parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨ hperiod J hJ0 hjpow u θ w hw
    rw [short_cube_exact_scale Z N hZ1 J hJ0] at h
    simpa only [completed_tuple_mark lists w _ _ htw _ (div_pos (Real.rpow_pos_of_pos hz _) (pow_pos hn _)) J] using h
  have hh:=marked_short_completed_energy
    (fun I:parents=>rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (u.val*ConcretePrimeRowBridge.idealGenerator I.val))
    (fun I n=>rowTwist_norm Ψ hΨ _ _ _ n) (fun _=>tupleDivisibilityMark lists w)
    (normTwistedSource W θ) (Z^N) (Z^hcut) (C*(1+‖θ‖)^degree*Z^(N+V-cstar/64))
    (by positivity) (fun J hJ=>by
      rw [Finset.sum_coe_sort parents (fun I:Ideal Eis=>‖markedCompletedT
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N/(Ideal.absNorm J:ℝ)^3) (fun A=>tupleDivisibilityMark lists w (J^3*A))‖^2)]
      exact hcompleted J hJ)
  rw [Finset.sum_coe_sort parents (fun I:Ideal Eis=>‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)] at hh
  exact hh

end SevenEighths.InverseMoment

end

end OAI

end Source2674

/- Original source: OAI/NumberTheory/DirichletL/Descent/ShortReflectedPower.lean; sha256: 69c1fa0fec169ee34db87f1e9a9da24cd7b3e04e242532293327a3debfea94ee -/
section Source2675
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open InverseTerminalWidths InverseReflectedPhase CompletedHeight
local notation "Eis"=>ActualEisensteinCubic.O
universe v

theorem short_harmonic_small_power (L e:ℝ) (hL:0≤L) (he:0<e):
    ∃C:ℝ,0<C ∧ ∀Z h:ℝ,1≤Z → 0≤h → h≤L →
      (256*(columnDyadicLength (Z^h)+1:ℝ))^2≤C*Z^e := by
  let a:=e/(2*(L+1))
  have ha:0<a:=by dsimp [a]; positivity
  let B:=256*(2+1/(a*Real.log 2))
  have hlog:0<Real.log 2:=Real.log_pos (by norm_num)
  have hB:0<B:=by dsimp [B]; positivity
  refine ⟨B^2,pow_pos hB _,?_⟩
  intro Z h hZ hh hhL
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hZh:1≤Z^h:=Real.one_le_rpow hZ hh
  have hb:=mul_le_mul_of_nonneg_left (columnDyadicLength_small_power a ha (Z^h) hZh)
    (by norm_num:(0:ℝ)≤256)
  have hs:(256*(columnDyadicLength (Z^h)+1:ℝ))^2≤B^2*Z^(h*a*2):=by
    calc
      _≤(B*(Z^h)^a)^2:=pow_le_pow_left₀ (by positivity) (by simpa [B,mul_assoc] using hb) 2
      _=B^2*Z^(h*a*2):=by rw [mul_pow,←Real.rpow_mul hz.le,←Real.rpow_mul_natCast hz.le (h*a) 2]; norm_num
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have heq:a*(2*(L+1))=e:=by dsimp [a]; field_simp
  nlinarith

theorem canonical_short_completed_power_energy (q:ℕ) (hq:q≠0)
    (lo hi:ℝ) (hlo:0<lo) (W:ℝ→ℂ)
    (hWs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (L cstar eta:ℝ) (hL:0≤L) (hcstar:0<cstar) (heta:0<eta)
    (heta1:eta≤1) (hetac:eta≤cstar/100000) (rmax:ℕ):
    ∃(degree:ℕ)(C Z₀:ℝ),0<C ∧ 1<Z₀ ∧
    ∀{σ:Type v} [Fintype σ] [DecidableEq σ],∀(F:Ideal Eis)(_hF:Squarefree F)
      (m:Eis)(_hm:m≠0)(Z N V M z₀ margin hcut d:ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀(parents:Finset (Ideal Eis)),(∀I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀(lists:σ→Finset (Ideal Eis))(H:σ→ℝ),
      Pairwise (fun i j=>Disjoint (lists i) (lists j)) →
      (∀i,∀P∈lists i,P.IsMaximal) →
      (∀i,∀P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀i,∀P∈lists i,Prime P) → (∀i,∀P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀i,1≤H i) → (∀i,∀P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏i,H i)≤Z^z₀ →
    ∀(Ψ:Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀(u:Eisˣ)(θ:ℝ)(w:∀i,lists i→ℂ),(∀i P,‖w i P‖≤1) →
      (∑I∈parents,‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I)) (normTwistedSource W θ)
        (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/128) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩:=canonical_short_completed_energy q hq lo hi hlo W hWs hW
    L cstar eta hL hcstar heta heta1 hetac rmax
  obtain ⟨B,hB,hbound⟩:=short_harmonic_small_power L (cstar/128) hL (by positivity)
  refine ⟨degree,C*B,Z₀,mul_pos hC hB,hZ₀,?_⟩
  intro σ _ _ F hF m hm Z N V M z₀ margin hcut d hZ hN hM hMc hVc hzc hcut0 hcutc hFn hRn
    hmargin hreserve hVd hcutd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Ψ hΨ hperiod u θ w hw
  have hz:0<Z:=zero_lt_one.trans (lt_of_lt_of_le hZ₀ hZ)
  have hh:=he F hF m hm Z N V M z₀ margin hcut d hZ hN hM hMc hVc hzc hcutc hFn hRn
    hmargin hreserve hVd hcutd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Ψ hΨ hperiod u θ w hw
  apply hh.trans
  calc
    _≤C*(1+‖θ‖)^degree*Z^(N+V-cstar/64)*(B*Z^(cstar/128)):=
      mul_le_mul_of_nonneg_left (hbound Z hcut (lt_of_lt_of_le hZ₀ hZ).le hcut0 hcutc) (by positivity)
    _=(C*B)*(1+‖θ‖)^degree*Z^(N+V-cstar/128):=by
      rw [show N+V-cstar/128=(N+V-cstar/64)+cstar/128 by ring,Real.rpow_add hz]
      ring

end SevenEighths.InverseMoment

end

end OAI

end Source2675

/- Original source: OAI/NumberTheory/DirichletL/Inversion/ShortCanonicalNormalization.lean; sha256: e665df2f1c7552a82b645fa89a74984de8a57dc03c131eda15399b34ea51c0cf -/
section Source2676
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseShortCanonicalNormalization
open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalRowCompletion
open InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis" => ActualEisensteinCubic.O
lemma normalization_norm_sq (Z N V : ℝ) (hZ : 0<Z) (x : ℂ) :
    ‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)*x‖^2 =
      Z^(-V)*‖x‖^2 := by
  have hn : 0≤Z^(-(N+V)/2) := Real.rpow_nonneg hZ.le _
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg hn,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,mul_pow,
    Real.sq_sqrt (Real.rpow_nonneg hZ.le _),←Real.rpow_mul_natCast hZ.le _ 2,
    ←Real.rpow_add hZ]
  congr 2
  norm_num

lemma divisor_weight_sum (K : ℕ) (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (Z V : ℝ),1≤Z → 0≤V → V≤L →
      ∀ labels : Finset (Ideal Eis),
      (∀ f∈labels,f≠0 ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
      (∑ f∈labels,((idealDivisors f).card:ℝ)^(9+4*K))≤C*Z^(V+ε) := by
  let n : ℕ := 9+4*K
  have hn : (0:ℝ)<n := by dsimp [n]; positivity
  let δ : ℝ := ε/((L+1)*(n:ℝ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨128*D^n,by positivity,?_⟩
  intro Z V hZ hV hVL labels hf
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hbudget : L*(δ*(n:ℝ))≤ε := by
    have heq : (L+1)*(δ*(n:ℝ))=ε := by dsimp [δ]; field_simp
    nlinarith [mul_pos hδ hn]
  have hb (f : Ideal Eis) (hfl : f∈labels) :
      ((idealDivisors f).card:ℝ)^n≤D^n*Z^ε := by
    have hfN : (Ideal.absNorm f:ℝ)≤Z^L :=
      (hf f hfl).2.trans (Real.rpow_le_rpow_of_exponent_le hZ hVL)
    calc
      _ ≤ (D*(Ideal.absNorm f:ℝ)^δ)^n := by gcongr; exact hd f (hf f hfl).1
      _ = D^n*(Ideal.absNorm f:ℝ)^(δ*(n:ℝ)) := by
        rw [mul_pow,Real.rpow_mul_natCast (Nat.cast_nonneg _)]
      _ ≤ D^n*(Z^L)^(δ*(n:ℝ)) := by gcongr
      _ = D^n*Z^(L*(δ*(n:ℝ))) := by rw [←Real.rpow_mul hz.le]
      _ ≤ _ := by gcongr
  have hc := DescentFiberCost.finite_ideal_count_real labels (Z^V)
    (Real.one_le_rpow hZ hV) (fun f hfl => (hf f hfl).1) (fun f hfl => (hf f hfl).2)
  calc
    _ ≤ ∑ _f∈labels,D^n*Z^ε := Finset.sum_le_sum (fun f hfl => hb f hfl)
    _ = (labels.card:ℝ)*(D^n*Z^ε) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (128*Z^V)*(D^n*Z^ε) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (128*D^n)*Z^(V+ε) := by rw [Real.rpow_add hz]; ring

lemma rowTwist_label_transfer (Ψ : Eis→*ℂ) (m a f k : Eis) :
    CanonicalRowCompletion.rowTwist Ψ m (a*f) k =
      CanonicalRowCompletion.rowTwist Ψ m f (a^4*k) := by
  have he : m^6*(a*f)^4*k=m^6*f^4*(a^4*k) := by ring
  unfold CanonicalRowCompletion.rowTwist
  rw [he]

lemma label_eq_rowUnit_generator (f : Ideal Eis) (hf : f≠0) (g : Eis)
    (hg : Ideal.span {g}=f) :
    g=(CompletedUnitRows.rowUnit g).val*ConcretePrimeRowBridge.idealGenerator f := by
  have hgn : g≠0 := by
    intro he
    apply hf
    rw [←hg,he,Ideal.span_singleton_zero]
    rfl
  have hh := CompletedUnitRows.rowUnit_spec g hgn
  rw [hg] at hh
  exact hh.symm

local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
universe v

theorem canonical_short_normalized_generator_energy (q : ℕ) (hq : q≠0)
    (lo hi : ℝ) (hlo : 0<lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (heta : 0<eta)
    (heta1 : eta≤1) (hetac : eta≤cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],
    ∀ (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤Z → 0≤N → 0≤V → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀ f∈labels,Squarefree f ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
    ∀ (labelGenerator : Ideal Eis→Eis),(∀ f∈labels,Ideal.span {labelGenerator f}=f) →
    ∀ (T : Finset Eis),(∀ k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) → (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ f∈labels,secondLabelWeight K f * ∑ k∈T,
        ‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)*markedShortCompletedSum
          (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_short_completed_power_energy q hq lo hi hlo W hWs hW
    L cstar eta hL hcstar heta heta1 hetac rmax
  obtain ⟨D,hD,hlabels⟩ := divisor_weight_sum K L (cstar/256) hL (by positivity)
  refine ⟨degree,D*(6*C),Z₀,by positivity,hZ₀,?_⟩
  intro σ _ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabelsN labelGenerator hlabelGenerator T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw
  have hz1 : 1≤Z := (lt_of_lt_of_le hZ₀ hZ).le
  have hz : 0<Z := zero_lt_one.trans_le hz1
  let rows := T.image (fun k => Ideal.span {k})
  have hrows := CompletedUnitRows.image_span_nonzero_norm T (Z^M) hT
  let E := C*(1+‖θ‖)^degree*Z^(N+V-cstar/128)
  have hf (f : Ideal Eis) (hfl : f∈labels) :
      (∑ k∈T,‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f) k)
        (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤6*E := by
    let uf := CompletedUnitRows.rowUnit (labelGenerator f)
    have hgf : labelGenerator f=uf.val*ConcretePrimeRowBridge.idealGenerator f :=
      label_eq_rowUnit_generator f (hlabelsN f hfl).1.ne_zero (labelGenerator f) (hlabelGenerator f hfl)
    apply (CompletedUnitRows.sum_nonzero_element_le_units T (fun k hk => (hT k hk).1)
      (fun k => ‖markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f) k)
        (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)
      (fun k => sq_nonneg _)).trans
    have hb (u : Eisˣ) :
        (∑ I∈rows,‖markedShortCompletedSum
          (rowTwist Ψ (ActualFiber.maskElement q m) (labelGenerator f)
            (u.val*ConcretePrimeRowBridge.idealGenerator I))
          (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤E := by
      have hh := he f (hlabelsN f hfl).1 m hm Z N V M z₀ margin hcut d
        hZ hN hM hMc hVc hzc hcut0 hcutc (hlabelsN f hfl).2 hRn hmargin hreserve hVd hcutd hd
        rows hrows hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨ hperiod (uf^4*u) θ w hw
      simpa only [hgf,rowTwist_label_transfer,Units.val_mul,Units.val_pow_eq_pow_val,E,mul_assoc] using hh
    calc
      _ ≤ ∑ _u : Eisˣ,E := Finset.sum_le_sum (fun u _ => hb u)
      _ = 6*E := by simp only [Finset.sum_const,Finset.card_univ,CompletedUnitRows.unit_card,nsmul_eq_mul,Nat.cast_ofNat]
  have hl : (∑ f∈labels,secondLabelWeight K f)≤D*Z^(V+cstar/256) :=
    hlabels Z V hz1 hV hVc labels (fun f hfl => ⟨(hlabelsN f hfl).1.ne_zero,(hlabelsN f hfl).2⟩)
  simp_rw [normalization_norm_sq Z N V hz,←Finset.mul_sum]
  calc
    _ ≤ ∑ f∈labels,secondLabelWeight K f*(Z^(-V)*(6*E)) := by
      apply Finset.sum_le_sum
      intro f hfl
      apply mul_le_mul_of_nonneg_left _ (by unfold secondLabelWeight; positivity)
      exact mul_le_mul_of_nonneg_left (hf f hfl) (Real.rpow_nonneg hz.le _)
    _ = (∑ f∈labels,secondLabelWeight K f)*(Z^(-V)*(6*E)) := by rw [Finset.sum_mul]
    _ ≤ (D*Z^(V+cstar/256))*(Z^(-V)*(6*E)) := mul_le_mul_of_nonneg_right hl (by dsimp [E]; positivity)
    _ = (D*(6*C))*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
      dsimp only [E]
      have hr : Z^(V+cstar/256)*Z^(-V)*Z^(N+V-cstar/128)=Z^(N+V-cstar/256) := by
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
      calc
        _ = (D*(6*C))*(1+‖θ‖)^degree*(Z^(V+cstar/256)*Z^(-V)*Z^(N+V-cstar/128)) := by ring
        _ = _ := by rw [hr]

theorem canonical_short_normalized_energy (q : ℕ) (hq : q≠0)
    (lo hi : ℝ) (hlo : 0<lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (heta : 0<eta)
    (heta1 : eta≤1) (hetac : eta≤cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],
    ∀ (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤Z → 0≤N → 0≤V → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀ f∈labels,Squarefree f ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
    ∀ (T : Finset Eis),(∀ k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) → (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ f∈labels,secondLabelWeight K f * ∑ k∈T,
        ‖((Z^(-(N+V)/2):ℝ):ℂ)*((Real.sqrt (Z^N):ℝ):ℂ)*markedShortCompletedSum
          (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark lists w)‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_short_normalized_generator_energy q hq
    lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax K
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabelsN T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw
  exact he m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc hRn
    hmargin hreserve hVd hcutd hd labels hlabelsN ConcretePrimeRowBridge.idealGenerator
    (fun f _ => ConcretePrimeRowBridge.span_idealGenerator f) T hT hcard lists H hdis hmax hgood hprime hodd
    hH1 hH hprod Ψ hΨ hperiod θ w hw

end SevenEighths.InverseShortCanonicalNormalization

end

end OAI

end Source2676

/- Original source: OAI/NumberTheory/DirichletL/Inversion/CanonicalShortAttachment.lean; sha256: d7a61e8bcfe2f078ac8282b304d45b1d4448b3080091f8148d109de9d2b97d6e -/
section Source2677
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseCanonicalShortAttachment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis" => ActualEisensteinCubic.O
universe u v

def idealLists {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (j : σ) : Finset (Ideal Eis) :=
  (lists j).image Subtype.val

def transportCoeff {σ : Type u} (F : Finset (Ideal Eis))
    (a : σ→primePool F→ℂ) (j : σ) (P : Ideal Eis) : ℂ :=
  if h:P∈primePool F then a j ⟨P,h⟩ else 0

@[simp] theorem transportCoeff_val {σ : Type u} (F : Finset (Ideal Eis))
    (a : σ→primePool F→ℂ) (j : σ) (i : primePool F) :
    transportCoeff F a j i.val=a j i := by simp [transportCoeff]

def idealWeights {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (j : σ) (P : idealLists F lists j) : ℂ := transportCoeff F a j P.val

lemma tuple_mark_product {σ : Type u} [Fintype σ] [DecidableEq σ]
    (lists : σ→Finset (Ideal Eis)) (w : ∀j,lists j→ℂ) (A : Ideal Eis) :
    tupleDivisibilityMark lists w A=
      ∏j,∑P:lists j,if P.val∣A then w j P else 0 := by
  unfold tupleDivisibilityMark
  calc
    _ = ∑p:∀j,lists j,∏j,if (p j).val∣A then w j (p j) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j hj
      split_ifs <;> simp
    _ = _ := (Fintype.prod_sum (fun j (P : lists j)=>if P.val∣A then w j P else 0)).symm

theorem indexed_mark_eq_tuple {σ : Type u} [DecidableEq σ]
    (F : Finset (Ideal Eis)) (slots : Finset σ) (lists : σ→Finset (primePool F))
    (a : σ→primePool F→ℂ) (A : Ideal Eis) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a A=
      tupleDivisibilityMark (fun j:slots=>idealLists F lists j.val)
        (fun j:slots=>idealWeights F lists a j.val) A := by
  rw [tuple_mark_product]
  unfold indexedIdealMark
  rw [←Finset.prod_coe_sort slots]
  apply Finset.prod_congr rfl
  intro j hj
  change _ = ∑P:idealLists F lists j.val,if P.val∣A then transportCoeff F a j.val P.val else 0
  rw [Finset.sum_coe_sort (idealLists F lists j.val) (fun P : Ideal Eis=>if P∣A then transportCoeff F a j.val P else 0)]
  change (∑i∈lists j.val,if i.val∣A then a j.val i else 0)=
    ∑P∈(lists j.val).image Subtype.val,if P∣A then transportCoeff F a j.val P else 0
  rw [Finset.sum_image (fun i hi k hk h=>Subtype.ext h)]
  simp only [transportCoeff_val]

lemma idealLists_disjoint {σ : Type u} [DecidableEq σ]
    (F : Finset (Ideal Eis)) (slots : Finset σ) (lists : σ→Finset (primePool F))
    (h : (slots:Set σ).Pairwise (fun j k=>Disjoint (lists j) (lists k))) :
    Pairwise (fun j k:slots=>Disjoint (idealLists F lists j.val) (idealLists F lists k.val)) := by
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  obtain ⟨i,hi,he⟩:=Finset.mem_image.mp hP
  obtain ⟨i',hi',he'⟩:=Finset.mem_image.mp hQ
  have hii : i=i' := Subtype.ext (he.trans he'.symm)
  have hjk' : j.val≠k.val := fun he=>hjk (Subtype.ext he)
  exact Finset.disjoint_left.mp (h j.property k.property hjk') hi (hii.symm ▸ hi')

lemma idealLists_prime_data {σ : Type u} (F : Finset (Ideal Eis))
    (hF : ∀I∈F,Admissible I) (lists : σ→Finset (primePool F))
    (j : σ) (P : Ideal Eis) (hP : P∈idealLists F lists j) :
    P.IsMaximal ∧ goodLambda∉P ∧ Prime P ∧ ringChar (Eis⧸P)≠2 := by
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
  refine ⟨inferInstance,poolGood F hF i,?_,poolOdd F hF i⟩
  exact Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance

lemma idealLists_capacity {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (H : σ→ℝ)
    (hH : ∀j,∀i∈lists j,(Ideal.absNorm i.val:ℝ)≤H j) :
    ∀j,∀P∈idealLists F lists j,(Ideal.absNorm P:ℝ)≤H j := by
  intro j P hP
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
  exact hH j i hi

lemma idealWeights_norm {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (ha : ∀j,∀i∈lists j,‖a j i‖≤1) :
    ∀j,∀P:idealLists F lists j,‖idealWeights F lists a j P‖≤1 := by
  intro j P
  obtain ⟨i,hi,he⟩:=Finset.mem_image.mp P.property
  change ‖transportCoeff F a j P.val‖≤1
  rw [←he,transportCoeff_val]
  exact ha j i hi

def longReopened (Ψ : Eis→*ℂ) (W : ℝ→ℂ) (X H₀ : ℝ) (mark : Ideal Eis→ℂ) : ℂ :=
  ∑' I:Ideal Eis,∑' B:Ideal Eis,largeCubeCoefficient H₀ B*summand Ψ W X I B*mark (I*B^3)

theorem complete_pool_split {σ : Type u} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (Ψ : Eis→*ℂ) (m f k : Eis) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀x,W x≠0→x≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let mark:=indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    let row:=rowTwist Ψ (m*excludedGenerator S) f k
    outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X=
      (Real.sqrt X:ℂ)*(markedShortCompletedSum row W X H₀ mark+longReopened row W X H₀ mark) := by
  dsimp only
  have hg:=finiteCanonicalMarkedRow_complete_global S D hbad hSp Ψ m f k W b X hX hW hD slots lists a
  change outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X=_ at hg
  have he:=marked_completed_cube_inverse_split (rowTwist Ψ (m*excludedGenerator S) f k)
    W hWc X H₀ hX
    (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)
  rw [←hg] at he
  change (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X=
    markedShortCompletedSum _ W X H₀ _+longReopened _ W X H₀ _ at he
  have hn : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  calc
    _ = (Real.sqrt X:ℂ)*((Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X) := by rw [←mul_assoc,mul_inv_cancel₀ hn,one_mul]
    _ = _ := by rw [he]

lemma complete_pool_sub_long {σ : Type u} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (Ψ : Eis→*ℂ) (m f k : Eis) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀x,W x≠0→x≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let mark:=indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    let row:=rowTwist Ψ (m*excludedGenerator S) f k
    outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X-
      (Real.sqrt X:ℂ)*longReopened row W X H₀ mark=
      (Real.sqrt X:ℂ)*markedShortCompletedSum row W X H₀ mark := by
  dsimp only
  rw [complete_pool_split S D hbad hSp Ψ m f k W hWc b X H₀ hX hW hD slots lists a]
  ring

lemma primary_span (f : Ideal Eis) (hf : Supported f) : Ideal.span {primaryGenerator f}=f :=
  (primaryGenerator_spec f (supported_primaryGenerator_ne_zero f hf)).1

lemma actual_mask (q : ℕ) (m : Eis) :
    m*excludedGenerator (reflectionExcludedPrimes q)=ActualFiber.maskElement q m := rfl

theorem normalized_complete_short_attachment (q : ℕ) (hq : q≠0)
    (lo hi : ℝ) (hlo : 0<lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (heta : 0<eta)
    (heta1 : eta≤1) (hetac : eta≤cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [DecidableEq σ],
    ∀ (m : Eis),m≠0 → ∀ (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤Z → 0≤N → 0≤V → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀f∈labels,Supported f ∧ Squarefree f ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
    ∀ (T : Finset Eis),(∀k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤Z^M) →
    ∀ D : ℕ,hi*Z^N≤D → ∀ slots : Finset σ,slots.card≤rmax →
    ∀ (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H : σ→ℝ),
      (slots:Set σ).Pairwise (fun j k=>Disjoint (lists j) (lists k)) →
      (∀j∈slots,1≤H j) → (∀j∈slots,∀i∈lists j,(Ideal.absNorm i.val:ℝ)≤H j) →
      (∏j∈slots,H j)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ)
      (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (∀j∈slots,∀i∈lists j,‖a j i‖≤1) →
      let S:=reflectionExcludedPrimes q
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
      let mark:=indexedIdealMark (fun i:primePool F=>i.val) slots lists a
      (∑f∈labels,secondLabelWeight K f*∑k∈T,
        ‖((Z^(-(N+V)/2):ℝ):ℂ)*
          (outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (primaryGenerator f) k
            slots lists a (normTwistedSource W θ) (Z^N)-
            (Real.sqrt (Z^N):ℂ)*longReopened
              (rowTwist Ψ (ActualFiber.maskElement q m) (primaryGenerator f) k)
              (normTwistedSource W θ) (Z^N) (Z^hcut) mark)‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩:=InverseShortCanonicalNormalization.canonical_short_normalized_generator_energy
    q hq lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax K
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabels T hT D hD slots hcard lists H hdis hH1 hH hprod
    Ψ hΨ hperiod θ a ha
  dsimp only
  let S:=reflectionExcludedPrimes q
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF : ∀I∈F,Admissible I:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
  let ilists:slots→Finset (Ideal Eis):=fun j=>idealLists F lists j.val
  let iw:∀j,ilists j→ℂ:=fun j=>idealWeights F lists a j.val
  have hp (j:slots) (P:Ideal Eis) (hP:P∈ilists j) := idealLists_prime_data F hF lists j.val P hP
  have hcap : ∀j:slots,∀P∈ilists j,(Ideal.absNorm P:ℝ)≤H j.val := by
    intro j P hP
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
    exact hH j.val j.property i hi
  have hw : ∀j:slots,∀P:ilists j,‖iw j P‖≤1 := by
    intro j P
    obtain ⟨i,hi,hh⟩:=Finset.mem_image.mp P.property
    change ‖transportCoeff F a j.val P.val‖≤1
    rw [←hh,transportCoeff_val]
    exact ha j.val j.property i hi
  have henergy:=he (σ:=slots) m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels (fun f hf=>(hlabels f hf).2) primaryGenerator
    (fun f hf=>primary_span f (hlabels f hf).1) T hT (by simpa using hcard)
    ilists (fun j:slots=>H j.val) (idealLists_disjoint F slots lists hdis)
    (fun j P hP=>(hp j P hP).1) (fun j P hP=>(hp j P hP).2.1)
    (fun j P hP=>(hp j P hP).2.2.1) (fun j P hP=>(hp j P hP).2.2.2)
    (fun j=>hH1 j.val j.property) hcap (by simpa only [Finset.prod_coe_sort] using hprod)
    Ψ hΨ hperiod θ iw hw
  have hz : 0<Z:=zero_lt_one.trans (lt_of_lt_of_le hZ₀ hZ)
  have hX : 0<Z^N:=Real.rpow_pos_of_pos hz _
  have htw : HasCompactSupport (normTwistedSource W θ):=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((normTwistedSource_support W θ).trans hWs)
  have hupper : ∀x,normTwistedSource W θ x≠0→x≤hi := fun x hx=>
    (hWs (normTwistedSource_support W θ hx)).2
  have hmark : indexedIdealMark (fun i:primePool F=>i.val) slots lists a=
      tupleDivisibilityMark ilists iw := funext (indexed_mark_eq_tuple F slots lists a)
  have hsame (f : Ideal Eis) (k : Eis) :
      outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (primaryGenerator f) k
        slots lists a (normTwistedSource W θ) (Z^N)-
        (Real.sqrt (Z^N):ℂ)*longReopened
          (rowTwist Ψ (ActualFiber.maskElement q m) (primaryGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut)
          (indexedIdealMark (fun i:primePool F=>i.val) slots lists a)=
      (Real.sqrt (Z^N):ℂ)*markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (primaryGenerator f) k)
        (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark ilists iw) := by
    have hh:=complete_pool_sub_long S D (reflectionExcludedPrimes_bad q)
      (reflectionExcludedPrimes_prime q) Ψ m (primaryGenerator f) k
      (normTwistedSource W θ) htw hi (Z^N) (Z^hcut) hX hupper hD slots lists a
    dsimp only at hh
    rw [actual_mask] at hh
    exact hh.trans (by rw [hmark])
  dsimp only [S, F] at hsame
  simp_rw [hsame]
  simpa only [mul_assoc] using henergy

end SevenEighths.InverseCanonicalShortAttachment

end

end OAI

end Source2677

/- Original source: OAI/NumberTheory/DirichletL/Inversion/ReflectedArithmeticHeight.lean; sha256: 5dabfc234836d0d6da83defd40236b81a3285122425bf78b114735e401258509 -/
section Source2678
namespace OAI

namespace SevenEighths.InverseReflectedArithmeticHeight
open scoped Classical BigOperators ContDiff SchwartzMap
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
open InverseReflectedPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v w

theorem actual_reflected_finite_source_arithmetic_uniform
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ {κ : Type w} (source : Finset κ) (weight : κ→ℂ)
        (K : κ→Ideal Eis) (hK : ∀ j, Admissible (K j)) (S : κ→PrimeFamily σ) (jF : φ→ℕ)
        (D : ∀ j, ControlledStratumArithmetic (F.reflected (K j) (hK j) (S j)).generator N a c mode)
        (n b : κ→Ideal Eis), (∀ j ∈ source, n j≠0 ∧ b j≠0) →
        (∑ j ∈ source, weight j*actualKernelSourceTerm F (K j) (hK j) (S j) jF (D j) s hc
          unit m (n j) (b j) windows QK QP Qn Qb W θ X) =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            ∑ j ∈ source, (weight j*actualMixedCoefficient F (K j) (hK j) (S j) jF (D j) s hc unit m (n j) (b j))*
              (kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm (K j):ℝ)*
                kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm (∏ i, (S j).ideal i):ℝ)*
                kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm (n j):ℝ) (Ideal.absNorm (b j):ℝ))) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := reflected_finite_source_uniform.{w}
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro N a c mode φ σ _ _ F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  have hr := ramifiedScale_pos 1 completedRamifiedStep (by norm_num)
    (lt_trans zero_lt_one completedRamifiedStep_gt_one) m
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep θ (actualKernelCoefficient F s m X) QK QP Qn Qb
    (ramifiedScale 1 completedRamifiedStep m) (actualKernelCoefficient_pos F s hc m X hX)
    hQK hQP hQn hQb hr
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro κ source weight K hK S jF D n b hn
  have hnorm (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hpos (j : κ) (hj : j ∈ source) : (0:ℝ)<Ideal.absNorm (K j) ∧
      (0:ℝ)<Ideal.absNorm (∏ i, (S j).ideal i) ∧ (0:ℝ)<Ideal.absNorm (n j) ∧ (0:ℝ)<Ideal.absNorm (b j) :=
    ⟨hnorm _ (hK j).1,hnorm _ (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne ((S j).ideal i))),
      hnorm _ (hn j hj).1,hnorm _ (hn j hj).2⟩
  have hh := he source (fun j => weight j*actualMixedCoefficient F (K j) (hK j) (S j) jF (D j) s hc unit m (n j) (b j))
    (fun j => (Ideal.absNorm (K j):ℝ)) (fun j => (Ideal.absNorm (∏ i, (S j).ideal i):ℝ))
    (fun j => (Ideal.absNorm (n j):ℝ)) (fun j => (Ideal.absNorm (b j):ℝ)) hpos
  simpa only [actualKernelSourceTerm_numeric,mul_assoc] using hh

theorem weighted_finite_physical_row_common_measure_arithmetic_uniform
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ)
        (Pset nset bset : Finset (Ideal Eis))
        (D : ∀ P : Pset, IsCoprime K P.val →
          ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode),
        (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) → (∀ n ∈ nset, n≠0) → (∀ b ∈ bset, b≠0) →
        ∀ (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
        weightedFinitePhysicalKernelRow F K hK S jF Pset nset bset D s hc unit m windows QK QP Qn Qb W θ X r₀ aw₀ w₀ =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc
              (fun K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ))
              (fun P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ))
              (fun n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)) unit m) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := actual_reflected_finite_source_arithmetic_uniform
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro N a c mode φ σ _ _ F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep (N:=N) (a:=a) (c:=c) (mode:=mode) (φ:=φ) (σ:=σ) F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀
  let T := CoprimeSourceIndex K Pset nset bset
  have hh := he (Finset.univ : Finset T) (fun x => r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val) (fun _ => K) (fun _ => hK)
    (fun x => S x.1.val.val) jF (fun x => D x.1.val x.1.property)
    (fun x => x.2.1.val) (fun x => x.2.2.val)
    (fun x _ => ⟨hn _ x.2.1.property,hb _ x.2.2.property⟩)
  unfold weightedFinitePhysicalKernelRow
  rw [hh]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [T]
  congr 1
  rw [weightedPhysicalReflectedRow_eq_coprime_source]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hprod x.1.val.val x.1.val.property]
  ring

theorem weighted_finite_physical_row_branch_measure_arithmetic_uniform
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ)
        (Pset nset bset : Finset (Ideal Eis))
        (D : ∀ P : Pset, IsCoprime K P.val →
          ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode),
        (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) → (∀ n ∈ nset, n≠0) → (∀ b ∈ bset, b≠0) →
        ∀ (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
        ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
          (D0 : ControlledStratumArithmetic G0.generator N a c mode),
        (∀ P : Pset, IsCoprime K P.val → Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal)) →
        (∀ P hp, (D P hp).fixedFactor=D0.fixedFactor) →
        (∀ P hp u m n b, actualCuspColumn (D P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
        (∀ b ∈ bset, primaryGenerator b≠0) →
        weightedFinitePhysicalKernelRow F K hK S jF Pset nset bset D s hc unit m windows QK QP Qn Qb W θ X r₀ aw₀ w₀ =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
              (actualCuspColumn D0 s hc unit m)
              (fun K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ))
              (fun P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ))
              (fun n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)) unit m Pset nset bset K)) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := weighted_finite_physical_row_common_measure_arithmetic_uniform
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro N a c mode φ σ _ _ F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep (N:=N) (a:=a) (c:=c) (mode:=mode) (φ:=φ) (σ:=σ) F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀ ι _ G0 D0 hcop hκ hA hbgen
  rw [he K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  exact weightedPhysicalReflectedRow_eq_branches F K hK S jF Pset nset bset hprod D hcop
    G0 D0 s hc hκ hA hbgen _ _ _ unit m

theorem literal_reflected_raw_tail_arithmetic_uniform (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀ {ι : Type u} [Fintype ι], ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (scale T : ℝ), 0<scale → 0<T →
    ∀ cut : RawTailIndex→Prop,
      (∀ x, cut x → T≤scale*(ramifiedScale 1 completedRamifiedStep x.1)^3*
        (Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3) →
      Summable (fun x => ‖if cut x then rawDualKernelTerm V scale 1 completedRamifiedStep
        (literalRawCoefficient G D s hc j S u) x else 0‖) ∧
      ‖∑' x, if cut x then rawDualKernelTerm V scale 1 completedRamifiedStep
        (literalRawCoefficient G D s hc j S u) x else 0‖≤
      C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(scale^2)⁻¹ := by
  obtain ⟨orders,C,hC,hb⟩ := raw_kernel_tail a₀ b₀ completedRamifiedStep ha₀ completedRamifiedStep_gt_one A
  refine ⟨orders,C,hC,?_⟩
  intro N a c mode V hV ι _ G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  have hh := hb V hV scale 1 (Ideal.absNorm (∏ i,G.ideal i):ℝ) T hs (by norm_num) (Nat.cast_nonneg _) hT
    (literalRawCoefficient G D s hc j S u) (literalRawCoefficient_norm G D s hc hN hbase hchar j hj S u) cut hcut
  simpa only [one_pow,mul_one] using hh

theorem literal_reflected_dyadic_tail_arithmetic_uniform (lo hi : ℝ) (hlo : 0<lo) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc lo hi →
    ∀ {ι : Type u} [Fintype ι], ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (scale T : ℝ), 0<scale → 0<T →
    ∀ cut : (ℕ×ℕ×ℕ)→Prop,
      (∀ i, cut i → 16*T≤rawDyadicCenter scale i) →
      ‖∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          rawDualKernelTerm V scale 1 completedRamifiedStep
            (literalRawCoefficient G D s hc j S u)
            (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
              ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0‖≤
        C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(scale^2)⁻¹ := by
  obtain ⟨orders,C,hC,hb⟩ := literal_reflected_raw_tail_arithmetic_uniform lo hi hlo A
  refine ⟨orders,C,hC,?_⟩
  intro N a c mode V hV ι _ G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  obtain ⟨hn,hh⟩ := hb (N:=N) (a:=a) (c:=c) (mode:=mode) V hV G D s hc hN hbase hchar j hj S u scale T hs hT
    (fun x => cut (rawDyadicLabel x)) (fun x hx => by
      have hc' := hcut (rawDyadicLabel x) hx
      have hl := rawDyadicCenter_lower scale hs.le x
      linarith)
  rw [tsum_cut_dyadic _ cut hn.of_norm] at hh
  exact hh

theorem literal_dyadic_tail_height_arithmetic_uniform (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ {ι : Type u} [Fintype ι], ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (θ X T : ℝ), 0<X → 0<T →
    ∀ cut : (ℕ×ℕ×ℕ)→Prop,
      (∀ i, cut i → 16*T≤rawDyadicCenter (literalRawScale G s X) i) →
      ‖∑' i : ℕ×ℕ×ℕ, if cut i then
        literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by
  obtain ⟨orders,C,hC,hbound⟩ := literal_reflected_dyadic_tail_arithmetic_uniform lo hi hlo A
  let V := vstarSchwartz W lo hi hlo hWs hW
  have hV : Function.support (V : ℝ→ℂ)⊆Set.Icc lo hi := Vstar_support W lo hi hWs
  obtain ⟨H,hH,hpoly⟩ := CompletedHeight.normTwistedSource_schwartz V lo hi hlo hV
  obtain ⟨degree,C₁,hC₁,hsemi⟩ := hpoly orders
  have hlink (θ : ℝ) : (H θ : ℝ→ℂ)=Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hH θ x]
    change FourierBridge.logPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x)=
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase θ (Real.log x)*W x)
    ring
  have hHs (θ : ℝ) : Function.support (H θ : ℝ→ℂ)⊆Set.Icc lo hi := by
    intro x hx
    change H θ x≠0 at hx
    rw [hH θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  refine ⟨degree,C*C₁,mul_pos hC hC₁,?_⟩
  intro N a c mode ι _ G D s hc hN hbase hchar j hj S u θ X T hX hT cut hcut
  have hh := hbound (N:=N) (a:=a) (c:=c) (mode:=mode) (H θ) (hHs θ) G D s hc hN hbase hchar j hj S u
    (literalRawScale G s X) T (literalRawScale_pos G s hc X hX) hT cut hcut
  have hleft : (∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          rawDualKernelTerm (H θ) (literalRawScale G s X) 1 completedRamifiedStep
            (literalRawCoefficient G D s hc j S u)
            (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
              ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0)=
      ∑' i : ℕ×ℕ×ℕ, if cut i then
        literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i else 0 := by
    simp only [rawDualKernelTerm,hlink,literalDyadicBlock,literalRawSeries]
  rw [hleft] at hh
  apply hh.trans
  have hsemi' := mul_le_mul_of_nonneg_left (hsemi θ) hC.le
  have hrest : 0≤(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by positivity
  calc
    _ = (C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) (H θ))*
        ((Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹) := by ring
    _ ≤ (C*(C₁*(1+‖θ‖)^degree))*
        ((Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹) :=
      mul_le_mul_of_nonneg_right hsemi' hrest
    _ = _ := by ring

end
end SevenEighths.InverseReflectedArithmeticHeight

end OAI

end Source2678

/- Original source: OAI/NumberTheory/DirichletL/Reflection/UniformPhysicalUniformDegree.lean; sha256: d07ffe90c343b7d8736495c59af7c7f51670cbda67b5a5a62d3de12c81e3a1e7 -/
section Source2679
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v

theorem surviving_physical_source_energy_type_uniform_uniform_degree
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ), ∀ {N a c : Eis} {mode : Bool},
    ∃ (C₀ C : ℝ), 0≤C₀ ∧ 0<C ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c ∣ N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f, jF f<6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (T θ QK QP Qn Qb : ℝ),
      0<T → 0<QK → 0<QP → 0<Qn → 0<Qb →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ)≤X)
      (D : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
        ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property).1 (S P.val)).generator N a c mode)
      (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis⧸(F.sum (S P)).ideal i)≠2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ)≤Y) →
      (∀ b ∈ bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*L) →
      (∀ K P hp, (D K P hp).fixedFactor=D0.fixedFactor) →
      (∀ K P hp u m n b, actualCuspColumn (D K P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
      (∀ K ∈ rows, ‖r₀ K‖≤1) → (∀ P ∈ Pset, ‖aw₀ P‖≤1) → (∀ n b, ‖w₀ n b‖≤1) →
      let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
      let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R
      let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
      (∑ K : rows, ‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀‖^2) ≤
      scalar^2*((branches.card:ℝ)*∑ e∈branches,
        let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
        let Bq := extractedDualScale (frozenExtracted F jF e 2) B
        (frozenBranchScale F jF e)^2*
          (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))))*(C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsource⟩ := InverseReflectedArithmeticHeight.weighted_finite_physical_row_branch_measure_arithmetic_uniform
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW 0
  refine ⟨degree,?_⟩
  intro N a c mode
  obtain ⟨C,hC,henergy⟩ := integrated_filtered_actual_reflected_energy_type_uniform
    (Ω := ℝ) (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C₀,C,hC₀,hC,?_⟩
  intro φ σ _ _ X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
  let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R
  let density := twistedDensity U W θ R
  let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
  let r := fun t K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ)
  let aw := fun t P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ)
  let w := fun t n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)
  obtain ⟨hsource',hdi,_,hl1,_⟩ := hsource (N:=N) (a:=a) (c:=c) (mode:=mode) (φ:=φ) (σ:=σ) F s hc u m θ T QK QP Qn Qb hT hQK hQP hQn hQb
  have hpair (K : rows) (P : Pset) (hKP : IsCoprime K.val P.val) :
      Pairwise (Function.onFun IsCoprime (F.reflected K.val (hrows K.val K.property).1 (S P.val)).ideal) := by
    apply F.reflected_pairwise _ _ _ hF
    · intro i j hij
      change IsCoprime ((F.sum (S P.val)).ideal (Sum.inr i)) ((F.sum (S P.val)).ideal (Sum.inr j))
      exact hScop P.val P.property (Sum.inr_injective.ne hij)
    · rw [hproducts P.val P.property]
      exact hKP
    · exact (hrowcop K.val K.property).1
    · intro f i
      change IsCoprime ((F.sum (S P.val)).ideal (Sum.inl f)) ((F.sum (S P.val)).ideal (Sum.inr i))
      exact hScop P.val P.property (Sum.inl_ne_inr : (Sum.inl f : φ⊕σ)≠Sum.inr i)
  have hn0 : ∀ n ∈ nset, n≠0 := fun n hn' => (hn n hn').1.1.ne_zero
  have hb0 : ∀ b ∈ bset, b≠0 := by
    intro b hb' hbzero
    exact (hb b hb').1 (by rw [hbzero,primaryGenerator_zero])
  have hidentity (K : rows) :
      weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀ =
      (scalar:ℂ)*∫ t : ℝ, density t*∑ e∈branches,
        weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor (actualCuspColumn D0 s hc u m)
          (r t) (aw t) (w t) u m Pset nset bset K.val := by
    simpa only [sum_branches_eq_surviving] using hsource' K.val (hrows K.val K.property).1 S jF Pset nset bset (D K) hproducts hn0 hb0 r₀ aw₀ w₀
      G0 D0 (hpair K) (hκ K) (hA K) (fun b hb' => (hb b hb').1)
  have hh := henergy X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m rows nset bset Pset S branches volume density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdi
    (fun K hK => weightedKernelCoordinate_measurable windows M (r₀ K) 0 (-2) QK _)
    (fun P hP => weightedKernelCoordinate_measurable windows M (aw₀ P) 1 (-2) QP _)
    (fun n hn b hb => weightedKernelDual_measurable windows M (w₀ n b) Qn Qb _ _)
    (fun t K hK => weightedKernelCoordinate_norm windows M hwindowNorm hwindows _ (hr₀ K hK) _ _ _ _ _)
    (fun t P hP => weightedKernelCoordinate_norm windows M hwindowNorm hwindows _ (haw₀ P hP) _ _ _ _ _)
    (fun t n b => weightedKernelDual_norm windows M hwindowNorm hwindows _ (hw₀ n b) _ _ _ _ _)
  have hR : 0<R := by
    have hCC := actualKernelCoefficient_pos F s hc m T hT
    dsimp only [R,kernelCenter]
    positivity
  have hscalar : 0<scalar := by
    have hr := ramifiedScale_pos 1 completedRamifiedStep (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) m
    have hs := smallScalar_pos hR
    dsimp only [scalar]
    positivity
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hscalar] at hh
  have hl1' : (∫ t : ℝ, ‖density t‖)≤C₀*(1+‖θ‖)^degree := by
    simpa only [pow_zero,one_mul] using hl1
  have hsquare : (∫ t : ℝ, ‖density t‖)^2≤(C₀*(1+‖θ‖)^degree)^2 :=
    (sq_le_sq₀ (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)).mpr hl1'
  simp_rw [hidentity]
  rw [Finset.sum_coe_sort rows (fun K : Ideal Eis => ‖(scalar:ℂ)*∫ t : ℝ, density t*∑ e∈branches,
    weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor (actualCuspColumn D0 s hc u m)
      (r t) (aw t) (w t) u m Pset nset bset K‖^2)]
  apply hh.trans
  apply mul_le_mul_of_nonneg_left hsquare
  apply mul_nonneg (sq_nonneg _)
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro e he
  have hYq : 0≤extractedDualScale (frozenExtracted F jF e 1) Y := le_trans zero_le_one (le_max_left _ _)
  have hBq : 0≤extractedDualScale (frozenExtracted F jF e 2) B := le_trans zero_le_one (le_max_left _ _)
  positivity

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source2679
