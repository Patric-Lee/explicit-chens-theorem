import OpenAIGrouped.Unit063
import OpenAIGrouped.Unit064
import OpenAIGrouped.Unit060
import OpenAIGrouped.Unit037
import OpenAIGrouped.Unit062
import OpenAIGrouped.Unit059
import OpenAIGrouped.Unit058

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstOriginalProfileLiveParents.lean; sha256: dd768f07c174c92f41624d8d137971c882f38ed8adf9b7899c1183f70bfea163 -/
section Source2600
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]

lemma refined_parent_source (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ) :
    globalParentSource (originalSubsetSource (refinedOuter p pool Q k (labelGate p j)))
      pool (originalSelector (fun x=>commonSelector p (selector x) l))=
      InverseFirstGlobalCaps.labelParentCell p pool Q selector k l j := by
  ext x
  rw [InverseFirstGlobalCaps.labelParentCell,Finset.mem_filter,InverseFirstGlobalCaps.mem_parentCell]
  simp only [globalParentSource,Finset.mem_biUnion,originalSubsetSource,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨o,ho,rfl⟩,D,⟨hD,hs⟩,rfl⟩
    have ho' := Finset.mem_filter.mp ho
    refine ⟨⟨o,?_,D,hD,by simpa using hs,rfl⟩,?_⟩
    · simpa only [originalOuterCell_eq_caps] using ho'.1
    · simpa [labelGate,fillFirstQuotient,toOriginal,ofOriginal] using ho'.2
  · rintro ⟨⟨o,ho,D,hD,hs,rfl⟩,hj⟩
    refine ⟨ofOriginal o,⟨o,?_,rfl⟩,D,⟨hD,by simpa using hs⟩,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · simpa only [originalOuterCell_eq_caps] using ho
    · simpa [labelGate,fillFirstQuotient,toOriginal,ofOriginal] using hj

theorem refined_child_priority (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    refinedChildEnergy p hp hg hinj pool Q k l (labelGate p j) negative Ψ m
      (fun v U=>primeMark slots lists a (v.support∪U)) om X t Y ≤
    globalPriorityOriginalEnergy p hg hp hinj
      (fun b=>if negative then b.rightExponent.support else b.leftExponent.support) pool
      (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
      (fun x=>(‖commonSelector p (fun _=>1) l x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y := by
  have he := original_subset_canonical_priority p hp hg hinj hc
    (refinedOuter p pool Q k (labelGate p j)) pool (fun _=>commonSelector p (fun _=>1) l)
    (fun b=>if negative then b.rightExponent.support else b.leftExponent.support)
    negative Ψ m slots lists a om X t Y hY
  rw [refined_parent_source] at he
  cases negative <;> simpa [refinedChildEnergy,divisorElement] using he

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI

end Source2600

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstDyadicCell.lean; sha256: b6a0b61b5a97f5f0b019c71b034629066ad99bc81dcbbb8487696833321c62ef -/
section Source2601
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
variable (p:ι→O)

def firstCellRadius (Z M r ell V eta tau:ℝ)(k:SourceIndex)(j:ℕ):ℝ:=
  Z^(firstPhysicalHeight M r ell V (dyadicExponent Z (k 3))
    (dyadicExponent Z (k 2)) (dyadicExponent Z j)+12*eta+tau)

theorem first_dyadic_radius_cell (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (k:SourceIndex)(j:ℕ)(x:FirstOriginalOuter ι)
    (hx:x∈refinedOuter p pool Q k (labelGate p j))
    (Z M r ell V eta tau:ℝ):
    firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau=
      firstCellRadius Z M r ell V eta tau k j:=by
  rw [refinedOuter_label] at hx
  obtain ⟨hx,hj⟩:=Finset.mem_filter.mp hx
  have hg:outerGate p k x:=(Finset.mem_filter.mp hx).2
  have hC:=hg 2
  have hD:=hg 3
  change dyadIndex (primeProductNorm p x.2.1)=k 2 at hC
  change dyadIndex (‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.2.2)‖^2)=k 3 at hD
  rw [primeSubsetGenerator_norm_eq_productNorm] at hD
  unfold firstDyadicRadius firstCellRadius firstDyadicExponent
  rw [hD,hC]
  change dyadIndex (‖eisEmbedding (jLabel p x.1.support
    (fun i=>x.1.leftExponent i+x.1.rightExponent i) x.1.leftBit x.1.rightBit)‖^2)=j at hj
  rw [hj]

theorem first_dyadic_refined_cutoff (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (k:SourceIndex)(j:ℕ)(Z M r ell V eta tau:ℝ):
    ∀x∈refinedOuter p pool Q k (labelGate p j),∀_I:Ideal O,
      firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau≤
        firstCellRadius Z M r ell V eta tau k j:=by
  intro x hx I
  exact (first_dyadic_radius_cell p pool Q k j x hx Z M r ell V eta tau).le

end SevenEighths.InverseMoment

end

end OAI

end Source2601

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondAdmissible.lean; sha256: a15439b2eb1afce2fa638260eabe92009bd272cd8c009fad158c88b76305166f -/
section Source2602
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem actual_second_inherited_puncture_ne_zero
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    actualSecondInheritedPuncture m (actualSecondChild p u v x).1 ≠ 0 := by
  change ((m*ConcretePrimeRowBridge.idealGenerator x.quotient)*
    primaryGenerator (Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}))*
    primaryGenerator (sourceIdeal p (x.second.sourceCommon\x.second.divisor)) ≠ 0
  rw [show primaryGenerator (Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) =
      b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryGenerator_primeProduct p hp hpr _ _,
    sourceIdeal_gen p hp hpr]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hm (ConcretePrimeRowBridge.idealGenerator_ne_zero _ ht))
    (primeProduct_ne_zero p hp _ _)) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))

lemma radicalGenerator_ne_zero (a : Eis) (ha : a ≠ 0) :
    ConcretePrimeRowBridge.idealGenerator (Ideal.span {a}).radical ≠ 0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  intro hz
  apply Ideal.span_singleton_eq_bot.not.mpr ha
  apply le_antisymm _ bot_le
  exact (Ideal.le_radical : (Ideal.span {a} : Ideal Eis) ≤ (Ideal.span {a}).radical).trans (le_of_eq hz)

def actualSecondPunctureWidth (Z : ℝ) (m : Eis) (γ : OuterTriple) : ℝ :=
  Real.logb Z (‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2)

include hp in
theorem actual_second_puncture_width_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 1 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (hB : primeProductNorm p x.cube.support ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    actualSecondPunctureWidth Z m (actualSecondChild p u v x).1 ≤ Q+ell+t+g-theta+4*eta := by
  have hp0 := actual_second_inherited_puncture_ne_zero p hp hpr x ht u v m hm
  have hr0 := radicalGenerator_ne_zero _ hp0
  change actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1 ≠ 0 at hr0
  apply (Real.logb_le_iff_le_rpow hZ (sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hr0)))).mpr
  exact actual_second_puncture_power_budget p hp hpr x hE ht u v m hm
    Z Q ell t g theta eta (zero_lt_one.trans hZ) hQ hB hT hG hD

include hp in

theorem actual_second_child_margins
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht0 : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z F M Q z c ell A t g theta V j delta eta : ℝ) (hZ : 1 < Z)
    (hparent : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (hB : primeProductNorm p x.cube.support ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  apply child_margins hparent hA ht hV hj
    (actual_second_common_center p hp x hE Z g theta eta hZ hG hD) hdelta heta
  have hwidth := actual_second_puncture_width_bound p hp hpr x hE ht0 u v m hm
    Z Q ell t g theta eta hZ hQ hB hT hG hD
  unfold decrease
  linarith

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_second_row_decrease
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (Z M ell A t g theta V j eta d : ℝ) (hZ : 1 < Z)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hterminal : d ≤ ell+V) (heta : eta ≤ d/16)
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hJ : Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    3*d/2 ≤ M-childM M ell A t g theta V j eta :=
  child_row_decrease hA ht (actual_second_common_center p hp x hE Z g theta eta hZ hG hD)
    (actual_second_label_center p hp x Z ell j eta hZ h1 h2 hJ) hterminal heta

end
end SevenEighths.InverseMoment

end OAI

end Source2602

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondSharpPuncture.lean; sha256: 05ec768593faed03f5c3fcb05d5575606eee0f5e6bab2f9f6e9628d1c9b9d346 -/
section Source2603
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_second_radical_puncture_q0_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) *
        (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hspan : Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} =
      (Ideal.span {m} : Ideal Eis) *
      Ideal.span {b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit} * sourceIdeal p (x.second.sourceCommon\x.second.divisor) := by
    rw [←actual_second_puncture_span p hp hpr x hE u v m]
    simp only [←Ideal.span_singleton_mul_span_singleton,secondExpansionQuotient_of_subset p x.second hE,
      secondMaskQuotient_span,sourceIdeal,FiniteGaussPhase.span_finset_prod]
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  simp only [actualSecondRadicalPuncture,ConcretePrimeRowBridge.span_idealGenerator,hspan]
  have hn (S : Finset ι) : (Ideal.absNorm (sourceIdeal p S) : ℝ)=primeProductNorm p S := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏ i ∈ S,p i)).symm
  rw [←hn (x.second.sourceCommon\x.second.divisor)]
  exact radical_product_norm_le _ _ _ _ (Ideal.span_singleton_eq_bot.not.mpr hm)
    (Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _))
    (sourceIdeal_ne_zero p hp _) Ideal.le_radical

include hp in

theorem actual_second_inherited_puncture_q0_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) * Ideal.absNorm x.quotient *
        (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hm' := mul_ne_zero hm (ConcretePrimeRowBridge.idealGenerator_ne_zero x.quotient ht)
  have hb := actual_second_radical_puncture_q0_norm p hp hpr x hE u v
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) hm'
  change ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) (actualSecondChild p u v x).1)‖^2 ≤ _
  apply hb.trans
  have ho : (Ideal.absNorm (Ideal.span {m*ConcretePrimeRowBridge.idealGenerator x.quotient}).radical : ℝ) ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ)*Ideal.absNorm x.quotient := by
    rw [←Ideal.span_singleton_mul_span_singleton,ConcretePrimeRowBridge.span_idealGenerator]
    simpa only [mul_one,map_one,Nat.cast_one] using radical_product_norm_le (Ideal.span {m}) 1 1 x.quotient
      (Ideal.span_singleton_eq_bot.not.mpr hm) one_ne_zero ht Ideal.le_radical
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ho (Nat.cast_nonneg _)) (primeProductNorm_pos p hp _).le

include hp in

theorem actual_second_q0_cube_bound
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (B : ℝ) (hB : 0 ≤ B)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) ≤ B := by
  change (Ideal.absNorm (Ideal.span {b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) : ℝ) ≤ B
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]
  exact (cube_label_norm_bounds p hp _ _ _ _ _ x.cube.support_pos B hB h1 h2).2.1

include hp in
theorem actual_second_puncture_power_from_cubes
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 0 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    ‖eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      Z^(Q+ell+t+g-theta+4*eta) := by
  have hr := second_residual_norm_power_bound p hp _ _ hE Z g theta eta hZ hG hD
  have hb := actual_second_q0_cube_bound p hp x u v _ (Real.rpow_pos_of_pos hZ _).le h1 h2
  apply (actual_second_inherited_puncture_q0_norm p hp hpr x hE ht u v m hm).trans
  calc
    _ ≤ (Z^Q*Z^(t+eta))*Z^(ell+eta)*Z^(g-theta+2*eta) := by
      have hr0 := (primeProductNorm_pos p hp (x.second.sourceCommon\x.second.divisor)).le
      gcongr
    _ = Z^((Q+(t+eta))+(ell+eta)+(g-theta+2*eta)) := by
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by congr 1; ring

include hp in
theorem actual_second_puncture_width_from_cubes
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 1 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    actualSecondPunctureWidth Z m (actualSecondChild p u v x).1 ≤ Q+ell+t+g-theta+4*eta := by
  have hp0 := actual_second_inherited_puncture_ne_zero p hp hpr x ht u v m hm
  have hr0 := radicalGenerator_ne_zero _ hp0
  change actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1 ≠ 0 at hr0
  apply (Real.logb_le_iff_le_rpow hZ (sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hr0)))).mpr
  exact actual_second_puncture_power_from_cubes p hp hpr x hE ht u v m hm
    Z Q ell t g theta eta (zero_lt_one.trans hZ) hQ h1 h2 hT hG hD

include hp in

theorem actual_second_child_margins_from_cubes
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht0 : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z F M Q z c ell A t g theta V j delta eta : ℝ) (hZ : 1 < Z)
    (hparent : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  apply child_margins hparent hA ht hV hj
    (actual_second_common_center p hp x hE Z g theta eta hZ hG hD) hdelta heta
  have hwidth := actual_second_puncture_width_from_cubes p hp hpr x hE ht0 u v m hm
    Z Q ell t g theta eta hZ hQ h1 h2 hT hG hD
  unfold decrease
  linarith

end
end SevenEighths.InverseMoment

end OAI

end Source2603

/- Original source: OAI/NumberTheory/DirichletL/Descent/SourceDepth.lean; sha256: 0783a444f955a496e43c57c5511d8dc6aab875ffe3e58d7492c1cabc74faaaee -/
section Source2604
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)

include hp in

theorem actual_second_childF_upper {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor⊆x.second.sourceCommon)
    (Z F ell A t g theta V j delta eta : ℝ) (hZ : 1<Z)
    (hA : 0≤A) (ht : 0≤t) (hell : 0≤ell) (hV : 0≤V) (hdelta : delta≤6*eta)
    (hG : primeProductNorm p x.second.sourceCommon≤Z^(g+eta))
    (hD : Z^(theta-eta)≤primeProductNorm p x.second.divisor)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    childF F ell A t g theta V j delta≤F+11*eta :=
  childF_upper hA ht hell hV
    (actual_second_common_center p hp x hE Z g theta eta hZ hG hD)
    (actual_second_label_center p hp x Z ell j eta hZ h1 h2 hJ) hdelta

include hp in

theorem actual_source_path_lengths
    (Jo Jn : ℕ→ℕ) (x : (k : ℕ)→MarkedSecondSource ι (Jo k) (Jn k))
    (F M ell A t g theta V j delta : ℕ→ℝ) (Z eta d : ℝ) (hZ : 1<Z)
    (n : ℕ) (heta : eta≤d/16)
    (hsource : ∀ k<n,
      (x k).second.divisor⊆(x k).second.sourceCommon ∧
      0≤A k ∧ 0≤t k ∧ 0≤ell k ∧ 0≤V k ∧ delta k≤6*eta ∧ d≤ell k+V k ∧
      primeProductNorm p (x k).second.sourceCommon≤Z^(g k+eta) ∧
      Z^(theta k-eta)≤primeProductNorm p (x k).second.divisor ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.leftExponent)‖^2≤Z^(ell k+eta) ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.rightExponent)‖^2≤Z^(ell k+eta) ∧
      Z^(j k-eta)≤‖eisEmbedding (jLabel p (x k).cube.support
        (fun i=>(x k).cube.leftExponent i+(x k).cube.rightExponent i)
        (x k).cube.leftBit (x k).cube.rightBit)‖^2)
    (hF : ∀ k<n,F (k+1)=childF (F k) (ell k) (A k) (t k) (g k) (theta k) (V k) (j k) (delta k))
    (hM : ∀ k<n,M (k+1)=childM (M k) (ell k) (A k) (t k) (g k) (theta k) (V k) (j k) eta) :
    F n≤F 0+11*(n:ℝ)*eta ∧ M n+3*(n:ℝ)*d/2≤M 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : n<n+1 := Nat.lt_succ_self n
    obtain ⟨he,ha,ht,hl,hv,hd,hterm,hg,hdiv,h1,h2,hj⟩ := hsource n hlt
    have hi := ih (fun k hk=>hsource k (Nat.lt_trans hk hlt))
      (fun k hk=>hF k (Nat.lt_trans hk hlt)) (fun k hk=>hM k (Nat.lt_trans hk hlt))
    have hf := actual_second_childF_upper p hp (x n) he Z (F n) (ell n) (A n) (t n)
      (g n) (theta n) (V n) (j n) (delta n) eta hZ ha ht hl hv hd hg hdiv h1 h2 hj
    have hm := actual_second_row_decrease p hp (x n) he Z (M n) (ell n) (A n) (t n)
      (g n) (theta n) (V n) (j n) eta d hZ ha ht hterm heta hg hdiv h1 h2 hj
    rw [←hF n hlt] at hf
    rw [←hM n hlt] at hm
    push_cast
    constructor <;> linarith [hi.1,hi.2]

theorem source_depth_caps (F M N V F0 M0 eta : ℝ) (n D : ℕ) (hn : n≤D)
    (heta : 0≤eta) (hF : F≤F0+11*(n:ℝ)*eta) (_hM : 0≤M) (hMm : M≤M0)
    (hN : 0≤N) (hV : 0≤V) (hsum : F=N+V) :
    N≤F0+11*(D:ℝ)*eta ∧ V≤F0+11*(D:ℝ)*eta ∧ M≤M0 := by
  have hn' : (n:ℝ)≤D := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right hn' heta
  constructor
  · linarith
  constructor
  · linarith
  · exact hMm

end
end SevenEighths.InverseMoment

end OAI

end Source2604

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActualChildState.lean; sha256: 67a07562d44da69e8137d98fbbb4ca40270a9b586781b7f423b1bf59b7801ad3 -/
section Source2605
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def actualCellLabelExponent (Z B j eta : ℝ) (d : BlockIndex) : ℝ :=
  secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta

def actualCellTotalExponent (Z X B j eta : ℝ) (d : BlockIndex) : ℝ :=
  max 0 (secondCellColumnExponent Z X d)+actualCellLabelExponent Z B j eta d

def actualCellClipping (Z X : ℝ) (d : BlockIndex) : ℝ :=
  max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d

lemma actual_cell_total_transition (Z r ell V A B t j eta : ℝ) (d : BlockIndex) (hZ : 1<Z) :
    actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d=
      childF (r+3*ell+V) ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j
        (actualCellClipping Z (Z^(r-A-B-t)) d+4*eta) := by
  unfold actualCellTotalExponent actualCellLabelExponent actualCellClipping
  rw [second_cell_formal_column Z r A B t d hZ]
  unfold childF decrease secondFormalColumn secondFormalLabel
  ring

lemma actual_cell_label_nonneg (Z B j eta : ℝ) (d : BlockIndex)
    (hZ : 1<Z) (hB : 0≤B) (hj : 0≤j) (heta : 0≤eta) :
    0≤actualCellLabelExponent Z B j eta d := by
  have h1 := secondCellExponent_nonneg Z d 1 hZ
  have h2 := secondCellExponent_nonneg Z d 2 hZ
  unfold actualCellLabelExponent secondFormalLabel
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

omit [DecidableEq ι] in
theorem actual_cell_norm_centers {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z eta : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (i : Fin 4) :
    Z^(secondCellExponent Z d i-eta)≤outerNorms p x i ∧
      outerNorms p x i≤Z^(secondCellExponent Z d i+eta) := by
  have hr := cell_ratios p hp source hk d x hx i
  have hz : 0<Z := zero_lt_one.trans hZ
  have hlo := (le_div_iff₀ (dyadScale_pos (d i))).mp hr.1
  have hhi := (div_le_iff₀ (dyadScale_pos (d i))).mp hr.2.le
  constructor
  · apply (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith : secondCellExponent Z d i-eta≤secondCellExponent Z d i)).trans
    simpa only [second_cell_scale_rpow Z d i hZ,one_mul,scales] using hlo
  · calc
      _ ≤ 2*scales d i := hhi
      _ ≤ Z^eta*scales d i := mul_le_mul_of_nonneg_right hbin (dyadScale_pos _).le
      _ = _ := by rw [←second_cell_scale_rpow Z d i hZ,←Real.rpow_add hz];congr 1;ring

theorem actual_cell_child_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (u v : Oˣ) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient:ℝ)≤Z^(t+eta)) :
    CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
      (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  have hxs := cell_subset p source d hx
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  rw [actual_cell_total_transition Z r ell V A B t j eta d hZ]
  apply actual_second_child_margins_from_cubes p hp hpr x (hs.second_divisor x hxs)
    (hs.quotient_nonzero x hxs) u v m hm Z (r+3*ell+V) M Q z c ell A t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j _ eta hZ hparent hA ht hV hj
    (by unfold actualCellClipping;have := le_max_right 0 (secondCellColumnExponent Z (Z^(r-A-B-t)) d);linarith)
    heta hQ h1 h2 hT
  · simpa only [outerNorms,Matrix.cons_val_zero] using hG
  · simpa only [outerNorms,Matrix.cons_val_one,Matrix.cons_val_zero] using hD

theorem actual_cell_child_total_upper {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hs : ActualSecondSourceConditions p source)
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z r ell V A B t j eta b : ℝ) (hZ : 1<Z)
    (hA : 0≤A) (ht : 0≤t) (hell : 0≤ell) (hV : 0≤V) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hb : 1≤b) (hthreshold : b≤Z^(6*eta))
    (hgeom : ∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*Z^(r-A-B-t))
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d≤(r+3*ell+V)+15*eta := by
  have hxs := cell_subset p source d hx
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  have hgt := actual_second_common_center p hp x (hs.second_divisor x hxs) Z
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta hZ
    (by simpa [outerNorms] using hG) (by simpa [outerNorms] using hD)
  have hj := actual_second_label_center p hp x Z ell j eta hZ h1 h2 hJ
  have hd : d∈keys p source := (mem_keys_iff p source d).mpr ⟨x,hx⟩
  have hc := second_cell_clipping_width Z (Z^(r-A-B-t)) b eta d hZ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hb
    (source_cell_joint_bound p hp source hk b _ hgeom d hd) hthreshold
  rw [actual_cell_total_transition Z r ell V A B t j eta d hZ]
  unfold childF decrease actualCellClipping
  linarith

end SevenEighths.InverseMoment
end

end OAI

end Source2605

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActualChildStateSupport.lean; sha256: 7abb40fd7255bfd6527ab9d71ec684014e9dee0337d808385ea5e4419f6372ab -/
section Source2606
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem actual_cell_label_support {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (u v : Oˣ)
    (Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ : ‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) :=
  actual_cell_child_label_power p hp source hk d x hx u v Z B j eta hZ hbin hC hJ

theorem actual_cell_correlated_row_support
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (u v : Oˣ)
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hd : ‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)‖^2≤Z^(delta+eta))
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (correlatedSecondRadius p (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
        x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    (actualSecondChild p u v x).2.2∈nonzeroChildFrequencyBall 1
      (Z^(childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)) := by
  have hE := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).2
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).1
  have hr := second_correlated_radius_childM p hp
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor) x.second.sourceCommon x.second.divisor
    Z M r ell V delta A B j t (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta tau L
    (zero_lt_one.trans hZ) hL0 hd (by simpa [outerNorms] using hE) (by simpa [outerNorms] using hG) hL
  apply (actual_second_row_ball p hp hpr x u v _).mp
  have hb := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mp hgate
  exact (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mpr ⟨hb.1,hb.2.trans hr⟩

omit hp in

lemma actual_child_row_length_nonneg (Z M : ℝ) (hZ : 1<Z) (k : O)
    (hk : k∈nonzeroChildFrequencyBall 1 (Z^M)) : 0≤M := by
  have hb := (mem_nonzeroChildFrequencyBall 1 one_ne_zero (Z^M) k).mp hk
  simp only [one_mul] at hb
  have hk0 : k≠0 := (Finset.mem_erase.mp hk).1
  have hn := EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq k hk0
  have hpow : Z^(0:ℝ)≤Z^M := by simpa only [Real.rpow_zero,one_mul] using hn.trans hb.2
  exact (Real.rpow_le_rpow_left_iff hZ).mp hpow

theorem actual_cell_row_decrease {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hs : ActualSecondSourceConditions p source)
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z M ell A t V j eta cutoff : ℝ) (hZ : 1<Z)
    (hA : 0≤A) (ht : 0≤t) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hterminal : cutoff≤ell+V) (hsmall : eta≤cutoff/16)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta+3*cutoff/2≤M := by
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  have hh := actual_second_row_decrease p hp x (hs.second_divisor x (cell_subset p source d hx)) Z M ell A t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta cutoff hZ hA ht hterminal hsmall
    (by simpa [outerNorms] using hG) (by simpa [outerNorms] using hD) h1 h2 hJ
  linarith

theorem actual_cell_triple_puncture_nonzero
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex) (m : O) (hm : m≠0)
    (γ : OuterTriple) (hγ : γ∈actualSecondTriples p 1 1 (cell p source d)) :
    actualSecondInheritedRadicalPuncture m γ≠0 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  exact radicalGenerator_ne_zero _ (actual_second_inherited_puncture_ne_zero p hp hpr x
    (hs.quotient_nonzero x (cell_subset p source d hx)) 1 1 m hm)

end SevenEighths.InverseMoment
end

end OAI

end Source2606

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActualChildStateRadius.lean; sha256: b380f3af17e0f0a280b98cfc05ceea7ee08ed5ed4ea73663b12b47e69bdc95c1 -/
section Source2607
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def actualCellRowExponent (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta

def actualCellRowRadius (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  Z^(actualCellRowExponent Z M ell A t V j eta d)

lemma actual_cell_row_radius_pos (Z M ell A t V j eta : ℝ) (d : BlockIndex) (hZ : 0<Z) :
    0<actualCellRowRadius Z M ell A t V j eta d := Real.rpow_pos_of_pos hZ _

theorem actual_cell_correlated_source_gates {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hd : ∀x∈source,‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)‖^2≤Z^(delta+eta))
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : ∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (correlatedSecondRadius p (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
        x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d) := by
  have hk : ∀x∈source,x.second.frequency≠0 := fun x hx=>(Finset.mem_erase.mp (hgate x hx)).1
  intro d x hx
  have hxs := cell_subset p source d hx
  exact (actual_second_row_ball p hp hpr x 1 1 _).mpr
    (actual_cell_correlated_row_support p hp hpr source hk d x hx 1 1
      Z M r ell V delta A B j t eta tau L hZ heta hbin hL0 (hd x hxs) hL (hgate x hxs))

theorem actual_cell_radius_nonnegative_on_keys {ι : Type*} [DecidableEq ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M ell A t V j eta : ℝ) (hZ : 1<Z)
    (hrows : ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d)) :
    ∀d∈keys p source,0≤actualCellRowExponent Z M ell A t V j eta d := by
  intro d hd
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hr := actual_second_row_radius_one p (cell p source d)
    (actualCellRowRadius Z M ell A t V j eta d) ⟨x,hx⟩ (hrows d)
  exact (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero,actualCellRowRadius] using hr)

end SevenEighths.InverseMoment
end

end OAI

end Source2607

/- Original source: OAI/NumberTheory/DirichletL/Inversion/SecondUniformCutoff.lean; sha256: b21189713b950928c76421771c7eea66e9e7892a10cb73e6bf83f3d900c9af4f -/
section Source2608
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseSecondUniformCutoff
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseSecondSourceBlocks InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def uniformSecondRadius {ι : Type*} [DecidableEq ι] (p : ι→O)
    (Z delta eta : ℝ) (G E : Finset ι) (L Y H : ℝ) : ℝ :=
  Z^(delta+eta)*(primeProductNorm p E/primeProductNorm p G)^2*L^2*H/Y

lemma uniformSecondRadius_nonneg {ι : Type*} [DecidableEq ι] (p : ι→O)
    (Z delta eta : ℝ) (G E : Finset ι) (L Y H : ℝ)
    (hZ : 0≤Z) (hY : 0≤Y) (hH : 0≤H) :
    0≤uniformSecondRadius p Z delta eta G E L Y H := by
  unfold uniformSecondRadius
  positivity

theorem correlated_le_uniform {ι : Type*} [DecidableEq ι] (p : ι→O)
    (Z delta eta : ℝ) (d : O) (G E : Finset ι) (L Y H : ℝ)
    (hY : 0<Y) (hH : 0≤H) (hd : ‖eisEmbedding d‖^2≤Z^(delta+eta)) :
    correlatedSecondRadius p d G E L Y H≤uniformSecondRadius p Z delta eta G E L Y H := by
  unfold correlatedSecondRadius uniformSecondRadius
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (sq_nonneg _)) (sq_nonneg _)) hH) hY.le

theorem uniform_radius_bound {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (G E : Finset ι) (Z delta theta g s Hc eta tau L : ℝ)
    (hZ : 0<Z) (hL0 : 0≤L)
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G) (hL : L≤Z^(s+4*eta)) :
    uniformSecondRadius p Z delta eta G E L (Z^(Hc+12*eta+tau)) (Z^tau)≤
      Z^(2*(s-g)-Hc+delta+2*theta+eta) := by
  have hratio : primeProductNorm p E/primeProductNorm p G≤Z^(theta-g+2*eta) := by
    calc
      _≤Z^(theta+eta)/Z^(g-eta):=div_le_div₀
        (Real.rpow_pos_of_pos hZ _).le hE (Real.rpow_pos_of_pos hZ _) hG
      _= _:=by rw [←Real.rpow_sub hZ];congr 1;ring
  have hratio0 : 0≤primeProductNorm p E/primeProductNorm p G :=
    div_nonneg (primeProductNorm_pos p hp E).le (primeProductNorm_pos p hp G).le
  have hsq (x : ℝ) : (Z^x)^2=Z^(2*x) := by
    rw [pow_two,←Real.rpow_add hZ]
    congr 1
    ring
  calc
    _≤Z^(delta+eta)*(Z^(theta-g+2*eta))^2*(Z^(s+4*eta))^2*Z^tau/Z^(Hc+12*eta+tau):=by
      unfold uniformSecondRadius
      gcongr
    _= _:=by
      rw [hsq,hsq,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
      congr 1
      ring

theorem uniform_radius_childM {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (G E : Finset ι) (Z M r ell V delta A B j t g theta eta tau L : ℝ)
    (hZ : 0<Z) (hL0 : 0≤L)
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G) (hL : L≤Z^(r-A-B-t+4*eta)) :
    uniformSecondRadius p Z delta eta G E L
      (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau)≤
      Z^(childM M ell A t g theta V j eta) := by
  have hb:=uniform_radius_bound p hp G E Z delta theta g (r-A-B-t)
    (firstPhysicalHeight M r ell V delta B j) eta tau L hZ hL0 hE hG hL
  convert hb using 1
  congr 1
  unfold childM decrease firstPhysicalHeight
  ring

theorem actual_cell_uniform_source_gates {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : ∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (uniformSecondRadius p Z delta eta x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d) := by
  have hk : ∀x∈source,x.second.frequency≠0 := fun x hx=>(Finset.mem_erase.mp (hgate x hx)).1
  intro d x hx
  have hxs:=cell_subset p source d hx
  have hE:=(actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).2
  have hG:=(actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).1
  have hr:=uniform_radius_childM p hp x.second.sourceCommon x.second.divisor
    Z M r ell V delta A B j t (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta tau L
    (zero_lt_one.trans hZ) hL0 (by simpa [outerNorms] using hE) (by simpa [outerNorms] using hG) hL
  have hb:=(mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mp (hgate x hxs)
  exact (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mpr ⟨hb.1,hb.2.trans hr⟩

theorem actual_cell_uniform_child_rows {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : ∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (uniformSecondRadius p Z delta eta x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    ∀d,∀x∈cell p source d,∀u v:Oˣ,(actualSecondChild p u v x).2.2∈nonzeroChildFrequencyBall 1
      (actualCellRowRadius Z M ell A t V j eta d) := by
  intro d x hx u v
  exact (actual_second_row_ball p hp hpr x u v _).mp
    (actual_cell_uniform_source_gates p hp source Z M r ell V delta A B j t eta tau L
      hZ heta hbin hL0 hL hgate d x hx)

theorem actual_cell_uniform_radius_nonnegative {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : ∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (uniformSecondRadius p Z delta eta x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    ∀d∈keys p source,0≤actualCellRowExponent Z M ell A t V j eta d :=
  actual_cell_radius_nonnegative_on_keys p source Z M ell A t V j eta hZ
    (actual_cell_uniform_source_gates p hp source Z M r ell V delta A B j t eta tau L
      hZ heta hbin hL0 hL hgate)

theorem full_second_uniform_tail (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀a,‖Ψ a‖≤1)
      (Z delta eta : ℝ) (m c d : O) (_hd : d≠0)
      (_hdyad : ‖eisEmbedding d‖^2≤Z^(delta+eta))
      (Hcol : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (B Y H L : ℝ),
      0≤B → 0<Y → 0≤H → 1≤L →
      (∀U,‖Hcol U‖≤B) → (∀U,Hcol U≠0→primeProductNorm p U≤L) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun G E=>childFrequencyBall
          (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
          (uniformSecondRadius p Z delta eta G E L Y H))‖≤
        (128*L)^4*(B^2*(Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
          (1+L^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,he⟩:=full_second_correlated_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ Z delta eta m c d hd hdyad Hcol W B Y H L hB hY hH hL hcol hsupp
  exact he p hp hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H L
    (fun G E=>uniformSecondRadius p Z delta eta G E L Y H) hB hY hH hL hcol hsupp
    (fun G _ E=>correlated_le_uniform p Z delta eta d G E.val L Y H hY hH hdyad)

end SevenEighths.InverseSecondUniformCutoff
end

end OAI

end Source2608

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActualChildStateLabels.lean; sha256: 759992e4943048668c69cee1bbdf4f18f67771c7e0bd806b49f163fdc0a2a506 -/
section Source2609
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def actualCellLabels {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : Finset (Ideal O) :=
  (cell p source d).image (fun x=>(actualSecondChild p 1 1 x).2.1)

lemma actual_cell_labels_cover {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) :
    (actualSecondChild p 1 1 x).2.1∈actualCellLabels p source d :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem actual_cell_labels_bound (hp : ∀i,p i≠0) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : ∀x∈source,primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ : ∀x∈source,‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    ∀I∈actualCellLabels p source d,(Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) := by
  intro I hI
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hI
  exact actual_cell_child_label_power p hp source hk d x hx 1 1 Z B j eta hZ hbin
    (hC x (cell_subset p source d hx)) (hJ x (cell_subset p source d hx))

theorem actual_cell_squarefree_labels (hp : ∀i,p i≠0) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : ∀x∈source,primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ : ∀x∈source,‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    ∀I∈(actualCellLabels p source d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) := by
  intro I hI
  have hi := Finset.mem_filter.mp hI
  exact ⟨hi.2,hi.2.ne_zero,actual_cell_labels_bound p hp source hk d Z B j eta hZ hbin hC hJ I hi.1⟩

theorem actual_cell_nonzero_weight_label (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex)
    (hw : actualSecondSignedWeight p hp hcop hg Ψ m ray x≠0) :
    (actualSecondChild p 1 1 x).2.1∈(actualCellLabels p source d).filter Squarefree := by
  have hxs := cell_subset p source d hx
  exact Finset.mem_filter.mpr ⟨actual_cell_labels_cover p source d x hx,
    actual_second_nonzero_weight_squarefree p hp hcop hg Ψ m ray x
      (hs.common_disjoint x hxs) (hs.second_divisor x hxs) hw 1 1⟩

end SevenEighths.InverseMoment
end

end OAI

end Source2609

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActualChildStateTriples.lean; sha256: c1288d90a55f3e7d3103e4e635ef7cc792247778e99237d1fefcd4895ecccdeb -/
section Source2610
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem actual_cell_triple_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : ∀x∈source,(Ideal.absNorm x.quotient:ℝ)≤Z^(t+eta))
    (γ : OuterTriple) (hγ : γ∈actualSecondTriples p 1 1 (cell p source d)) :
    actualSecondInheritedRadicalPuncture m γ≠0 ∧
    0≤actualSecondPunctureWidth Z m γ ∧
    ‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
    CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
      (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
      (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  have hn := actual_cell_triple_puncture_nonzero p hp hpr source hs d m hm γ hγ
  refine ⟨hn,?_,?_,?_⟩
  · exact Real.logb_nonneg hZ (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hn)
  · exact (Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hn)))).symm
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    have hxs := cell_subset p source d hx
    exact actual_cell_child_margins p hp hpr source hs hk d x hx 1 1 m hm
      Z r ell V M Q z c A B t j eta hZ hparent hA ht hV hj heta hbin hQ
      (h1 x hxs) (h2 x hxs) (hT x hxs)

omit hp in

theorem actual_child_enlarged_row_bounds (Z M : ℝ) (hZ : 1<Z) (k : O)
    (hk : k∈nonzeroChildFrequencyBall 1 (Z^M)) :
    k≠0 ∧ ‖eisEmbedding k‖^2≤Z^M ∧ 0≤M := by
  have hb := (mem_nonzeroChildFrequencyBall 1 one_ne_zero _ k).mp hk
  simp only [one_mul] at hb
  exact ⟨(Finset.mem_erase.mp hk).1,hb.2,actual_child_row_length_nonneg Z M hZ k hk⟩

omit hp in

theorem actual_child_size_caps (F M Q z c cap : ℝ)
    (hinv : CanonicalMargins F M Q z c) (hM : 0≤M) (hQ : 0≤Q) (hz : 0≤z)
    (hc : 0≤c) (hF : F≤cap) : M≤cap ∧ Q≤cap ∧ z≤cap := by
  obtain ⟨h1,h2⟩ := hinv
  constructor
  · linarith
  constructor <;> linarith

end SevenEighths.InverseMoment
end

end OAI

end Source2610

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalRetainedGates.lean; sha256: 19cae7af2acaf1917ab965da5183d4541c6b6c07a01390144b5bf2a61080f090 -/
section Source2611
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def retainedSource (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) : Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0) :=
  unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) (fun _=>cutoff)

lemma original_parent_witness
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedSource p extra original negative J lists pool cutoff) :
    ∃y∈original,forgetAppended (Jo:=Jo) (secondParentOf x)=parent p y := by
  have hp := ((mem_unifiedSource p pool _ (fun _=>cutoff) x).mp hx).1
  obtain ⟨y,hy,q,hq,he⟩ := (mem_wholeAssignedParents p (fun x=>extra x.cube) original negative J lists _).mp hp
  exact ⟨y,hy,by simpa only [forget_attach] using congrArg (forgetAppended (Jo:=Jo)) he.symm⟩

lemma original_coordinates
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedSource p extra original negative J lists pool cutoff) :
    ∃y∈original,x.cube=y.cube ∧ x.firstCommon=y.firstCommon ∧
      x.firstDivisor=y.firstDivisor ∧ x.quotient=sourceIdeal p y.quotientSupport ∧
      (∀i:Fin Jo,x.oldAssigned (Fin.castAdd (J.card+J.card) i)=y.oldAssigned i) := by
  obtain ⟨y,hy,he⟩ := original_parent_witness p extra original negative J lists pool cutoff x hx
  exact ⟨y,hy,congrArg SecondParentSource.cube he,congrArg SecondParentSource.firstCommon he,
    congrArg SecondParentSource.firstDivisor he,congrArg SecondParentSource.quotient he,
    fun i=>congrArg (fun z=>z.oldAssigned i) he⟩

lemma retained_conditions (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) :
    ActualSecondSourceConditions p (retainedSource p extra original negative J lists pool cutoff) :=
  unified_conditions p hp extra original hvalid hextra negative J lists pool (fun _=>cutoff)

lemma original_numeric_gates (extra : CubeCoordinates ι→Finset ι)
    (original : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ)
    (lists : σ→Finset ι) (pool : Finset ι) (cutoff : Finset ι→Finset ι→ℝ)
    (B A C Q JL JU D : ℝ)
    (hB₁ : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤B)
    (hB₂ : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤B)
    (hA : ∀y∈original,primeProductNorm p (cubeActiveSupport y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)≤A)
    (hC : ∀y∈original,primeProductNorm p y.firstCommon≤C)
    (hQ : ∀y∈original,primeProductNorm p y.quotientSupport≤Q)
    (hJ : ∀y∈original,JL≤‖eisEmbedding (jLabel p y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p y.cube.support (fun i=>y.cube.leftExponent i+y.cube.rightExponent i)
        y.cube.leftBit y.cube.rightBit)‖^2≤JU)
    (hD : ∀y∈original,primeProductNorm p y.firstDivisor≤D) :
    ∀x∈retainedSource p extra original negative J lists pool cutoff,
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B ∧
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B ∧
      primeProductNorm p (cubeActiveSupport x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)≤A ∧ primeProductNorm p x.firstCommon≤C ∧
      (Ideal.absNorm x.quotient:ℝ)≤Q ∧
      JL≤‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤JU ∧
      primeProductNorm p x.firstDivisor≤D := by
  intro x hx
  obtain ⟨y,hy,hb,hc,hd,hq,ho⟩ := original_coordinates p extra original negative J lists pool cutoff x hx
  rw [hb,hc,hd,hq]
  refine ⟨hB₁ y hy,hB₂ y hy,hA y hy,hC y hy,?_,(hJ y hy).1,(hJ y hy).2,hD y hy⟩
  simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hQ y hy

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI

end Source2611

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalRetainedGatesGeometry.lean; sha256: 7c0bf0e853b2efbda2d9e5797feaea69d2264518d91e5c7b104aff8896bd15b2 -/
section Source2612
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

lemma actual_profile_zero_of_geometry
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X b : ℝ) (hX : 0<X)
    (hW : ∀y,W₁ y≠0 → y≤b)
    (hgeom : b*X<primeProductNorm p x.common*primeProductNorm p x.overlap) :
    actualSecondProfileRow p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X=0 := by
  rw [actualSecondProfileRow_eq_whole]
  apply Finset.sum_eq_zero
  intro N hN
  apply Finset.sum_eq_zero
  intro M hM
  have hzero : W₁ (primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p N/X)=0 := by
    by_contra hn
    have hh := (div_le_iff₀ hX).mp (hW _ hn)
    have hlo := le_mul_of_one_le_right
      (mul_nonneg (primeProductNorm_pos p hp x.common).le (primeProductNorm_pos p hp x.overlap).le)
      (primeProductNorm_ge_one p hp N)
    linarith
  simp [secondNormProfile,secondActualNorms,hzero]

lemma wholeRow_zero_of_geometry
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo : ℕ} (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X Y b : ℝ) (hX : 0<X) (hW : ∀y,W y≠0 → y≤b)
    (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0)
    (hgeom : b*X<primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap) :
    wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x=0 := by
  rw [wholeRow_eq]
  have hh := actual_profile_zero_of_geometry p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
    (slots\J) (slots\J) (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
    (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x) a a W W rowMajorant Y X b hX hW hgeom
  rw [hh,mul_zero]

omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
def geometrySource {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    Finset (MarkedSecondSource ι Jo Jn) :=
  source.filter (fun x=>primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X)

omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
omit [DecidableEq ι] in
lemma geometrySource_subset {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    geometrySource p source b X⊆source := Finset.filter_subset _ _

omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
omit [DecidableEq ι] in
lemma geometrySource_gate {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    ∀x∈geometrySource p source b X,
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X :=
  fun _x hx=>(Finset.mem_filter.mp hx).2

lemma original_retained_geometry_sum
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo : ℕ} (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (source : Finset (MarkedSecondSource ι Jo 0)) (w : MarkedSecondSource ι Jo 0→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X Y b : ℝ)
    (hX : 0<X) (hW : ∀y,W y≠0 → y≤b) (ray : SecondRayIndex) :
    (∑x∈source,w x*wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x)=
    ∑x∈geometrySource p source b X,w x*wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x := by
  rw [geometrySource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs with hg₀
  · rfl
  · rw [wholeRow_zero_of_geometry p hp hcop hg extra pool negative Ψ m slots J lists a W X Y b hX hW
      ray x (lt_of_not_ge hg₀),mul_zero]

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI

end Source2612

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalRetainedGatesRadius.lean; sha256: 82e8cccf173029cb97e7a40f506f99e275c1d9a7994d37669ee2f212d5e22be9 -/
section Source2613
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open InverseSecondUniformCutoff
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def supportedRetainedSource (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) : Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0) :=
  geometrySource p (retainedSource p extra original negative J lists pool cutoff) b X

lemma supported_subset (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    supportedRetainedSource p extra original negative J lists pool cutoff b X⊆
      retainedSource p extra original negative J lists pool cutoff := geometrySource_subset p _ b X

lemma supported_conditions (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    ActualSecondSourceConditions p (supportedRetainedSource p extra original negative J lists pool cutoff b X) :=
  ActualSecondSourceConditions.mono p (retained_conditions p hp extra original hvalid hextra negative J lists pool cutoff)
    (supported_subset p extra original negative J lists pool cutoff b X)

lemma supported_frequency_ne_zero
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool cutoff b X,x.second.frequency≠0 := by
  intro x hx
  exact unified_frequency_ne_zero p pool _ (fun _=>cutoff) x
    (supported_subset p extra original negative J lists pool cutoff b X hx)

lemma supported_uniform_frequency_gate
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z delta eta L Y tau b X : ℝ) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool
      (fun G E=>uniformSecondRadius p Z delta eta G E L Y (Z^tau)) b X,
      x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
        (uniformSecondRadius p Z delta eta x.second.sourceCommon x.second.divisor L Y (Z^tau)) := by
  intro x hx
  exact ((mem_unifiedSource p pool _ _ x).mp
    (supported_subset p extra original negative J lists pool _ b X hx)).2.2.2.2

theorem supported_cell_row_gates (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z M r ell V delta A B j t eta tau L b X : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hL : L≤Z^(r-A-B-t+4*eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool
      (fun G E=>uniformSecondRadius p Z delta eta G E L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau)) b X
    (∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta (index p x))) ∧
    (∀d∈keys p source,0≤actualCellRowExponent Z M ell A t V j eta d) := by
  intro source
  have hgates := actual_cell_uniform_source_gates p hp source Z M r ell V delta A B j t eta tau L
    hZ heta hbin hL0 hL (supported_uniform_frequency_gate p extra original negative J lists pool Z delta eta L _ tau b X)
  refine ⟨?_,actual_cell_radius_nonnegative_on_keys p source Z M ell A t V j eta hZ hgates⟩
  intro x hx
  exact hgates (index p x) x (Finset.mem_filter.mpr ⟨hx,rfl⟩)

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI

end Source2613

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalRetainedGatesCaps.lean; sha256: d2a608df23c7a1125582e5aed7638f7a17c49327da17753624433b42033a1f5f -/
section Source2614
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open InverseSecondUniformCutoff
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma uniform_radius_cap (G E : Finset ι) (hEG : E⊆G)
    (Z delta eta L Y tau Lcol LY : ℝ) (hZ : 0<Z) (hL : 0≤L) (hY : 0<Y)
    (hLc : L≤Z^Lcol) (hYi : Y⁻¹≤Z^LY) :
    uniformSecondRadius p Z delta eta G E L Y (Z^tau)≤
      Z^(delta+eta+2*Lcol+tau+LY) := by
  have hr : primeProductNorm p E/primeProductNorm p G≤1 :=
    (div_le_one (primeProductNorm_pos p hp G)).mpr (primeProductNorm_mono p hp hEG)
  have hr0 : 0≤primeProductNorm p E/primeProductNorm p G := by
    exact div_nonneg (primeProductNorm_pos p hp E).le (primeProductNorm_pos p hp G).le
  have hs : (primeProductNorm p E/primeProductNorm p G)^2≤1 := pow_le_one₀ hr0 hr
  unfold uniformSecondRadius
  rw [div_eq_mul_inv]
  calc
    _ ≤ Z^(delta+eta)*1*(Z^Lcol)^2*Z^tau*Z^LY := by gcongr
    _ = _ := by
      rw [mul_one,←Real.rpow_mul_natCast hZ.le]
      repeat rw [←Real.rpow_add hZ]
      congr 1
      norm_num
      ring

lemma bare_frequency_norm_le (a k : O) (ha : a≠0) :
    ‖eisEmbedding k‖^2≤‖eisEmbedding (a*k)‖^2 := by
  have hh := element_norm_ge_one a ha
  rw [map_mul,norm_mul,mul_pow]
  exact le_mul_of_one_le_left (sq_nonneg _) hh

include hp in

theorem supported_outer_caps
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z delta eta L Y tau b X Lcol LY Lcap : ℝ)
    (hZ : 1≤Z) (hL : 0≤L) (hY : 0<Y) (hLc : L≤Z^Lcol) (hYi : Y⁻¹≤Z^LY)
    (hgeom : b*X≤Z^Lcap) (hphysical : delta+eta+2*Lcol+tau+LY≤Lcap) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool
      (fun G E=>uniformSecondRadius p Z delta eta G E L Y (Z^tau)) b X,
      ∀i,outerNorms p x i≤Z^Lcap := by
  intro x hx i
  have hret := supported_subset p extra original negative J lists pool _ b X hx
  have hm := (mem_unifiedSource p pool _ _ x).mp hret
  have hg : primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤Z^Lcap :=
    (geometrySource_gate p _ b X x hx).trans hgeom
  have hG : primeProductNorm p x.second.sourceCommon≤Z^Lcap :=
    (le_mul_of_one_le_right (primeProductNorm_pos p hp _).le (primeProductNorm_ge_one p hp _)).trans hg
  have hV : primeProductNorm p x.second.overlap≤Z^Lcap :=
    (le_mul_of_one_le_left (primeProductNorm_pos p hp _).le (primeProductNorm_ge_one p hp _)).trans hg
  fin_cases i
  · exact hG
  · exact (primeProductNorm_mono p hp hm.2.2.1).trans hG
  · exact hV
  · have hb := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mp hm.2.2.2.2
    exact (bare_frequency_norm_le _ _ (actualSecondMultiplier_ne_zero p x)).trans
      (hb.2.trans ((uniform_radius_cap p hp _ _ hm.2.2.1 Z delta eta L Y tau Lcol LY
        (zero_lt_one.trans_le hZ) hL hY hLc hYi).trans
        (Real.rpow_le_rpow_of_exponent_le hZ hphysical)))

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI

end Source2614

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalRetainedGatesChildren.lean; sha256: 801f5ca16b5df2b74162044c2d563829c79f66d1c3dcb30f4cd1851e62a40fd0 -/
section Source2615
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

lemma supported_original_property
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ)
    (F : CubeCoordinates ι→Finset ι→Finset ι→Ideal O→Prop)
    (hF : ∀y∈original,F y.cube y.firstCommon y.firstDivisor (sourceIdeal p y.quotientSupport)) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool cutoff b X,
      F x.cube x.firstCommon x.firstDivisor x.quotient := by
  intro x hx
  obtain ⟨y,hy,hb,hc,hd,hq,ho⟩ := original_coordinates p extra original negative J lists pool cutoff x
    (supported_subset p extra original negative J lists pool cutoff b X hx)
  rw [hb,hc,hd,hq]
  exact hF y hy

theorem supported_label_gates (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : ∀y∈original,primeProductNorm p y.firstCommon≤Z^(B+eta))
    (hJ : ∀y∈original,‖eisEmbedding (jLabel p y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)‖^2≤Z^(j+eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b X
    (∀d,∀x∈cell p source d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p source d) ∧
    (∀d,∀I∈(actualCellLabels p source d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d)) := by
  intro source
  have hc := supported_original_property p extra original negative J lists pool cutoff b X
    (fun _ C _ _=>primeProductNorm p C≤Z^(B+eta)) hC
  have hj := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>‖eisEmbedding (jLabel p q.support
      (fun i=>q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit)‖^2≤Z^(j+eta)) hJ
  exact ⟨fun d x hx=>actual_cell_labels_cover p source d x hx,
    fun d=>actual_cell_squarefree_labels p hp source
      (supported_frequency_ne_zero p extra original negative J lists pool cutoff b X) d Z B j eta hZ hbin hc hj⟩

theorem supported_child_margins (hp : ∀i,p i≠0)
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b : ℝ) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : ∀y∈original,primeProductNorm p y.quotientSupport≤Z^(t+eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    ∀d,∀γ∈actualSecondTriples p 1 1 (cell p source d),
      actualSecondInheritedRadicalPuncture m γ≠0 ∧ 0≤actualSecondPunctureWidth Z m γ ∧
      ‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
      CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
        (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
        (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  intro source d γ hγ
  have hs := supported_conditions p hp extra original hvalid hextra negative J lists pool cutoff b (Z^(r-A-B-t))
  have hk := supported_frequency_ne_zero p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
  have hb₁ := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.leftExponent)‖^2≤Z^(ell+eta)) h1
  have hb₂ := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.rightExponent)‖^2≤Z^(ell+eta)) h2
  have hq := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun _ _ _ I=>(Ideal.absNorm I:ℝ)≤Z^(t+eta)) (by
      intro y hy
      simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hT y hy)
  exact actual_cell_triple_margins p hp hpr source hs hk d m hm
    Z r ell V M Q z c A B t j eta hZ hparent hA ht hV hj heta hbin hQ hb₁ hb₂ hq γ hγ

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI

end Source2615

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalRetainedGatesBudget.lean; sha256: 9b8331d59ce77b6f345daaeb60746d6204ddcae0f5eeee40c9f9199f1aa85380 -/
section Source2616
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseInitialArithmetic InverseSecondSourceBlocks
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

 theorem source_cell_exponent_cap {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hk : ∀x∈source,x.second.frequency≠0) (Z Lcap : ℝ) (hZ : 1<Z)
    (hnorm : ∀x∈source,∀i,outerNorms p x i≤Z^Lcap)
    (d : BlockIndex) (hd : d∈keys p source) (i : Fin 4) :
    secondCellExponent Z d i≤Lcap := by
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hs : scales d i≤outerNorms p x i := by
    simpa only [one_mul,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx i).1
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [second_cell_scale_rpow Z d i hZ]
  exact hs.trans (hnorm x (cell_subset p source d hx) i)

theorem source_cell_mass_gate {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hk : ∀x∈source,x.second.frequency≠0)
    (Z Lcap ell Ractive j t eta eps pi : ℝ) (hZ : 1<Z) (hj : 0≤j) (heps : 0≤eps)
    (hnorm : ∀x∈source,∀i,outerNorms p x i≤Z^Lcap)
    (hbudget : eps*(ell+Ractive/2+t+Lcap+11*eta/2)≤pi) :
    ∀d∈keys p source,eps*(secondCount ell Ractive j t
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤pi := by
  intro d hd
  have hg := source_cell_exponent_cap p hp source hk Z Lcap hZ hnorm d hd 0
  have htheta := secondCellExponent_nonneg Z d 1 hZ
  apply le_trans (mul_le_mul_of_nonneg_left (show
    secondCount ell Ractive j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2≤
      ell+Ractive/2+t+Lcap+11*eta/2 by unfold secondCount; linarith) heps) hbudget

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI

end Source2616

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalRetainedGatesRank.lean; sha256: 6412c4e54a12cf1b55928e219b10412fb4de033138ed105fc5b58a5d44e9f631 -/
section Source2617
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

theorem supported_row_rank_decrease (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X Z M ell A t V j eta shortCutoff : ℝ)
    (hZ : 1<Z) (hA : 0≤A) (ht : 0≤t) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hterminal : shortCutoff≤ell+V) (hsmall : eta≤shortCutoff/16)
    (h1 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : ∀y∈original,Z^(j-eta)≤‖eisEmbedding (jLabel p y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)‖^2) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b X
    ∀d∈keys p source,actualCellRowExponent Z M ell A t V j eta d+3*shortCutoff/2≤M := by
  intro source d hd
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hxs := cell_subset p source d hx
  have hs := supported_conditions p hp extra original hvalid hextra negative J lists pool cutoff b X
  have hk := supported_frequency_ne_zero p extra original negative J lists pool cutoff b X
  have hb₁ := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.leftExponent)‖^2≤Z^(ell+eta)) h1
  have hb₂ := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.rightExponent)‖^2≤Z^(ell+eta)) h2
  have hj := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>Z^(j-eta)≤‖eisEmbedding (jLabel p q.support
      (fun i=>q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit)‖^2) hJ
  exact actual_cell_row_decrease p hp source hs hk d x hx Z M ell A t V j eta shortCutoff
    hZ hA ht heta hbin hterminal hsmall (hb₁ x hxs) (hb₂ x hxs) (hj x hxs)

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI

end Source2617

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstLabelCellStepGates.lean; sha256: 783da7d8457af02743f11e56f27e0dd93477ca4d1b4881f9a6461be183f17f99 -/
section Source2618
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

def extra (negative : Bool) (c : CubeCoordinates ι) : Finset ι :=
  if negative then c.rightExponent.support else c.leftExponent.support

lemma extra_subset (negative : Bool) (c : CubeCoordinates ι) : extra negative c⊆c.support := by
  cases negative
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

lemma dyadic_exponent_nonneg (Z : ℝ) (hZ : 1<Z) (n : ℕ) :
    0≤InverseFirstGlobalCaps.dyadicExponent Z n :=
  Real.logb_nonneg hZ (by unfold dyadScale;exact one_le_pow₀ (by norm_num : (1:ℝ)≤2))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma label_parent_valid (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,SourceValid p y := by
  intro y hy
  obtain ⟨o,ho,D,hD,hs,rfl⟩ := (InverseFirstGlobalCaps.mem_parentCell p pool Q (fun _ _=>1) k l y).mp
    (Finset.mem_filter.mp hy).1
  exact original_fill_valid p pool Q o (Finset.mem_filter.mp ho).1 D

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem label_parent_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) (Z ell eta : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport y.cube.support
        (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)
        ≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 4)+eta) ∧
      primeProductNorm p y.firstCommon≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 2)+eta) ∧
      primeProductNorm p y.quotientSupport≤Z^(InverseFirstGlobalCaps.dyadicExponent Z l+eta) ∧
      Z^(InverseFirstGlobalCaps.dyadicExponent Z j-eta)≤InverseFirstGlobalCaps.jNorm p (toOriginal y) ∧
      InverseFirstGlobalCaps.jNorm p (toOriginal y)≤Z^(InverseFirstGlobalCaps.dyadicExponent Z j+eta) ∧
      primeProductNorm p y.firstDivisor≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 3)+eta) := by
  intro y hy
  have hparent := (Finset.mem_filter.mp hy).1
  have hc := InverseFirstGlobalCaps.parentCell_cube_bounds p pool Q (fun _ _=>1) k l Z ell eta hQ y hparent
  have hn := InverseFirstGlobalCaps.parentCell_norm_bounds p hp pool Q (fun _ _=>1) k l Z eta hZ hbin y hparent
  have hi := InverseFirstGlobalCaps.parentCell_ideal_bounds p hp pool Q (fun _ _=>1) k l Z eta hZ hbin y hparent
  have hj := InverseFirstGlobalCaps.labelParentCell_bounds p hp pool Q (fun _ _=>1) k l j Z eta hZ hbin y hy
  refine ⟨hc.1,hc.2,?_,hi.1.2,?_,?_,hj.2.2,?_⟩
  · simpa only [InverseFirstGlobalCaps.sourceIdeal_norm] using hi.2.2.2
  · simpa only [hn.2.1] using hn.2.2.2
  · exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)).trans hj.2.1
  · simpa only [InverseFirstGlobalCaps.sourceIdeal_norm] using hi.2.1.2

include hp in

theorem retained_label_numeric (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) (Z ell eta : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    let source := supportedRetainedSource p (extra negative)
      (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j) negative J lists pool cutoff b X
    ∀x∈source,
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
        ≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 4)+eta) ∧
      primeProductNorm p x.firstCommon≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 2)+eta) ∧
      (Ideal.absNorm x.quotient:ℝ)≤Z^(InverseFirstGlobalCaps.dyadicExponent Z l+eta) ∧
      Z^(InverseFirstGlobalCaps.dyadicExponent Z j-eta)≤
        ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤Z^(InverseFirstGlobalCaps.dyadicExponent Z j+eta) ∧
      primeProductNorm p x.firstDivisor≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 3)+eta) := by
  intro source x hx
  have h := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact original_numeric_gates p (extra negative) _ negative J lists pool cutoff _ _ _ _ _ _ _
    (fun y hy=>(h y hy).1) (fun y hy=>(h y hy).2.1) (fun y hy=>(h y hy).2.2.1)
    (fun y hy=>(h y hy).2.2.2.1) (fun y hy=>(h y hy).2.2.2.2.1)
    (fun y hy=>⟨(h y hy).2.2.2.2.2.1,(h y hy).2.2.2.2.2.2.1⟩)
    (fun y hy=>(h y hy).2.2.2.2.2.2.2) x (supported_subset p _ _ negative J lists pool cutoff b X hx)

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI

end Source2618

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstLabelCellStepSource.lean; sha256: c4baf5bd0c7877ff07cb157028ddb47c104e489dabe3965bce21f70e0fead083 -/
section Source2619
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondUniformCutoff
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

abbrev exponent := InverseFirstGlobalCaps.dyadicExponent

def columnA (Z : ℝ) (k : SourceIndex) (negative : Bool) : ℝ :=
  exponent Z (k (if negative then 0 else 1))

def columnScale (Z r : ℝ) (k : SourceIndex) (l : ℕ) (negative : Bool) : ℝ :=
  Z^(r-columnA Z k negative-exponent Z (k 2)-exponent Z l)

def secondCutoff (p : ι→O) (Z M r ell V eta tau window : ℝ) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (G E : Finset ι) : ℝ :=
  uniformSecondRadius p Z (exponent Z (k 3)) eta G E
    (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j) (Z^tau)

def source (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :=
  supportedRetainedSource p (extra negative)
    (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
    negative J lists pool (secondCutoff p Z M r ell V eta tau window k l j negative)
    b (columnScale Z r k l negative)

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_valid (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ActualSecondSourceConditions p (source p pool Q k l j negative J lists Z M r ell V eta tau window b) :=
  supported_conditions p hp _ _ (label_parent_valid p pool Q k l j) (fun y _hy=>extra_subset negative y.cube)
    negative J lists pool _ b _

lemma source_frequency_ne_zero (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,x.second.frequency≠0 :=
  supported_frequency_ne_zero p _ _ negative J lists pool _ b _

lemma source_geometry (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*columnScale Z r k l negative :=
  geometrySource_gate p _ b _

include hp in
theorem source_row_gates (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hwindow : Real.exp window≤Z^(4*eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    (∀x∈S,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta (index p x))) ∧
    (∀d∈keys p S,0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d) := by
  intro S
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc : columnScale Z r k l negative*Real.exp window≤
      Z^(r-columnA Z k negative-exponent Z (k 2)-exponent Z l+4*eta) := by
    unfold columnScale
    rw [Real.rpow_add hz]
    exact mul_le_mul_of_nonneg_left hwindow (Real.rpow_nonneg hz.le _)
  exact supported_cell_row_gates p hp _ _ negative J lists pool Z M r ell V (exponent Z (k 3))
    (columnA Z k negative) (exponent Z (k 2)) (exponent Z j) (exponent Z l) eta tau
    (columnScale Z r k l negative*Real.exp window) b (columnScale Z r k l negative)
    hZ heta hbin (by unfold columnScale;positivity) hc

include hp in
theorem source_outer_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap : ℝ)
    (hZ : 1<Z)
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,
      ∀i,outerNorms p x i≤Z^Lcap := by
  exact supported_outer_caps p hp _ _ negative J lists pool Z (exponent Z (k 3)) eta
    (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j)
    tau b (columnScale Z r k l negative) Lcol LY Lcap hZ.le
    (by unfold columnScale;positivity) (by unfold firstCellRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    hcol hYi hgeom hphysical

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI

end Source2619

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstLabelCellStepChildren.lean; sha256: 9272abd398c306d5dc69dc0774254d0917b4073ee62d0579c51e9b8cfc5ed7be -/
section Source2620
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_labels (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    (∀d,∀x∈cell p S d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p S d) ∧
    (∀d,∀I∈(actualCellLabels p S d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤
        Z^(actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)) := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_label_gates p hp _ _ negative J lists pool _ b (columnScale Z r k l negative)
    Z (exponent Z (k 2)) (exponent Z j) eta hZ hbin
    (fun y hy=>(hb y hy).2.2.2.1) (fun y hy=>(hb y hy).2.2.2.2.2.2.1)

include hp in
theorem source_child_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (m : O) (hm : m≠0) (Qwidth z c : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hV : 0≤V)
    (hparent : CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d,∀γ∈actualSecondTriples p 1 1 (cell p S d),
      actualSecondInheritedRadicalPuncture m γ≠0 ∧ 0≤actualSecondPunctureWidth Z m γ ∧
      ‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
      CanonicalMargins (actualCellTotalExponent Z (columnScale Z r k l negative)
        (exponent Z (k 2)) (exponent Z j) eta d)
        (childM M ell (columnA Z k negative) (exponent Z l) (secondCellExponent Z d 0)
          (secondCellExponent Z d 1) V (exponent Z j) eta)
        (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_child_margins p hp hpr _ _ (label_parent_valid p pool Q k l j)
    (fun y hy=>extra_subset negative y.cube) negative J lists pool _ b m hm
    Z r ell V M Qwidth z c (columnA Z k negative) (exponent Z (k 2)) (exponent Z l) (exponent Z j) eta
    hZ hparent (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) hV
    (dyadic_exponent_nonneg Z hZ _) heta hbin hpuncture
    (fun y hy=>(hb y hy).1) (fun y hy=>(hb y hy).2.1) (fun y hy=>(hb y hy).2.2.2.2.1)

include hp in
theorem source_row_decrease (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b short : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hterminal : short≤ell+V) (hsmall : eta≤short/16)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d∈keys p S,actualCellRowExponent Z M ell (columnA Z k negative)
      (exponent Z l) V (exponent Z j) eta d+3*short/2≤M := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_row_rank_decrease p hp _ _ (label_parent_valid p pool Q k l j)
    (fun y hy=>extra_subset negative y.cube) negative J lists pool _ b (columnScale Z r k l negative)
    Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta short hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) heta hbin hterminal hsmall
    (fun y hy=>(hb y hy).1) (fun y hy=>(hb y hy).2.1) (fun y hy=>(hb y hy).2.2.2.2.2.1)

include hp in
theorem source_mass_gate (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap eps pi : ℝ)
    (hZ : 1<Z) (heps : 0≤eps)
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap)
    (hbudget : eps*(ell+exponent Z (k 4)/2+exponent Z l+Lcap+11*eta/2)≤pi) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d∈keys p S,eps*(secondCount ell (exponent Z (k 4)) (exponent Z j) (exponent Z l)
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤pi := by
  intro S
  exact source_cell_mass_gate p hp S (source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b)
    Z Lcap ell (exponent Z (k 4)) (exponent Z j) (exponent Z l) eta eps pi hZ
    (dyadic_exponent_nonneg Z hZ _) heps
    (source_outer_caps p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap
      hZ hcol hYi hgeom hphysical) hbudget

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI

end Source2620

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActualChildStateDepth.lean; sha256: 7c7e1c44cb12fea788c2f39195a87aff9aa5da790d24509e1e1ad3541ff4db35 -/
section Source2621
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem actual_cell_path_lengths {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (Jo Jn : ℕ→ℕ) (source : (k : ℕ)→Finset (MarkedSecondSource ι (Jo k) (Jn k)))
    (cellIndex : ℕ→BlockIndex) (x : (k : ℕ)→MarkedSecondSource ι (Jo k) (Jn k))
    (F M r ell V A B t j b : ℕ→ℝ) (Z eta cutoff : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hsmall : eta≤cutoff/16) (n : ℕ)
    (hsource : ∀k<n,
      ActualSecondSourceConditions p (source k) ∧
      (∀y∈source k,y.second.frequency≠0) ∧ x k∈cell p (source k) (cellIndex k) ∧
      F k=r k+3*ell k+V k ∧
      0≤A k ∧ 0≤t k ∧ 0≤ell k ∧ 0≤V k ∧ cutoff≤ell k+V k ∧
      1≤b k ∧ b k≤Z^(6*eta) ∧
      (∀y∈source k,primeProductNorm p y.second.sourceCommon*primeProductNorm p y.second.overlap≤
        b k*Z^(r k-A k-B k-t k)) ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.leftExponent)‖^2≤Z^(ell k+eta) ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.rightExponent)‖^2≤Z^(ell k+eta) ∧
      Z^(j k-eta)≤‖eisEmbedding (jLabel p (x k).cube.support
        (fun i=>(x k).cube.leftExponent i+(x k).cube.rightExponent i)
        (x k).cube.leftBit (x k).cube.rightBit)‖^2)
    (hF : ∀k<n,F (k+1)=actualCellTotalExponent Z (Z^(r k-A k-B k-t k)) (B k) (j k) eta (cellIndex k))
    (hM : ∀k<n,M (k+1)=childM (M k) (ell k) (A k) (t k)
      (secondCellExponent Z (cellIndex k) 0) (secondCellExponent Z (cellIndex k) 1) (V k) (j k) eta) :
    F n≤F 0+15*(n:ℝ)*eta ∧ M n+3*(n:ℝ)*cutoff/2≤M 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : n<n+1 := Nat.lt_succ_self n
    obtain ⟨hs,hk,hx,hparent,hA,ht,hell,hV,hterm,hb,hthreshold,hgeom,h1,h2,hj⟩ := hsource n hn
    have hi := ih (fun k hk=>hsource k (Nat.lt_trans hk hn))
      (fun k hk=>hF k (Nat.lt_trans hk hn)) (fun k hk=>hM k (Nat.lt_trans hk hn))
    have hf := actual_cell_child_total_upper p hp (source n) hs hk (cellIndex n) (x n) hx
      Z (r n) (ell n) (V n) (A n) (B n) (t n) (j n) eta (b n) hZ hA ht hell hV heta hbin
      hb hthreshold hgeom h1 h2 hj
    have hm := actual_cell_row_decrease p hp (source n) hs hk (cellIndex n) (x n) hx
      Z (M n) (ell n) (A n) (t n) (V n) (j n) eta cutoff hZ hA ht heta hbin hterm hsmall h1 h2 hj
    rw [←hF n hn,←hparent] at hf
    rw [←hM n hn] at hm
    push_cast
    constructor <;> linarith [hi.1,hi.2]

theorem actual_cell_depth_caps (F M N V F0 M0 eta : ℝ) (n depth : ℕ)
    (hn : n≤depth) (heta : 0≤eta) (hF : F≤F0+15*(n:ℝ)*eta)
    (hM : M≤M0) (hN : 0≤N) (hV : 0≤V) (hsum : F=N+V) :
    N≤F0+15*(depth:ℝ)*eta ∧ V≤F0+15*(depth:ℝ)*eta ∧ M≤M0 := by
  have hn' : (n:ℝ)≤depth := by exact_mod_cast hn
  have he := mul_le_mul_of_nonneg_right hn' heta
  constructor
  · linarith
  constructor
  · linarith
  · exact hM

theorem actual_cell_depth_bound (M M0 cutoff : ℝ) (n : ℕ) (hcutoff : 0<cutoff)
    (hM : 0≤M) (hpath : M+3*(n:ℝ)*cutoff/2≤M0) :
    (n:ℝ)≤2*M0/(3*cutoff) := by
  apply (le_div_iff₀ (by positivity : 0<3*cutoff)).mpr
  nlinarith

end SevenEighths.InverseMoment
end

end OAI

end Source2621

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActualDepthBudget.lean; sha256: 86b66c81fd90749655b835ae3fbd976d5f3a0f2c2e8ca4eb7cdcd7420ad1cf72 -/
section Source2622
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment

def actualDepth (Mmax cutoff : ℝ) : ℕ := ⌈2*Mmax/(3*cutoff)⌉₊+1

lemma actualDepth_pos (Mmax cutoff : ℝ) : 0<actualDepth Mmax cutoff := by
  exact Nat.succ_pos _

lemma actualDepth_strict (Mmax cutoff : ℝ) :
    2*Mmax/(3*cutoff)<(actualDepth Mmax cutoff:ℝ) := by
  have h := Nat.le_ceil (2*Mmax/(3*cutoff))
  unfold actualDepth
  push_cast
  linarith

theorem actual_depth_parameters (depth : ℕ) (cutoff c eps : ℝ)
    (hd : 0<cutoff) (hc : 0<c) (heps : 0<eps) :
    ∃eta tau pi : ℝ,0<eta ∧ 0<tau ∧ 0<pi ∧ eta≤cutoff/16 ∧
      (depth:ℝ)*7*eta≤c/2 ∧ (depth:ℝ)*15*eta≤1 ∧
      (depth:ℝ)*(100*eta+4*tau+4*pi)≤eps/4 := by
  let D : ℝ := (depth:ℝ)+1
  have hD : 0<D := by dsimp [D];positivity
  have hn : 0≤(depth:ℝ) := Nat.cast_nonneg _
  have hnD : (depth:ℝ)≤D := by dsimp [D];linarith
  let eta := min (cutoff/16) (min (c/(28*D)) (min (1/(30*D)) (eps/(1600*D))))
  let tau := eps/(128*D)
  have heta : 0<eta := by dsimp [eta];positivity
  have htau : 0<tau := by dsimp [tau];positivity
  have he1 : eta≤cutoff/16 := min_le_left _ _
  have he2 : eta≤c/(28*D) := (min_le_right _ _).trans (min_le_left _ _)
  have he3 : eta≤1/(30*D) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have he4 : eta≤eps/(1600*D) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hb2 : eta*(28*D)≤c := (le_div_iff₀ (by positivity)).mp he2
  have hb3 : eta*(30*D)≤1 := (le_div_iff₀ (by positivity)).mp he3
  have hb4 : eta*(1600*D)≤eps := (le_div_iff₀ (by positivity)).mp he4
  have ht : tau*(128*D)=eps := by dsimp [tau];field_simp
  have hne : (depth:ℝ)*eta≤D*eta := mul_le_mul_of_nonneg_right hnD heta.le
  have hnt : (depth:ℝ)*tau≤D*tau := mul_le_mul_of_nonneg_right hnD htau.le
  refine ⟨eta,tau,tau,heta,htau,htau,he1,?_,?_,?_⟩ <;> nlinarith

theorem actual_depth_margin_size (depth n : ℕ) (hn : n≤depth)
    (c eta F0 : ℝ) (heta : 0≤eta)
    (hmargin : (depth:ℝ)*7*eta≤c/2) (hsize : (depth:ℝ)*15*eta≤1) :
    c/2≤c-7*(n:ℝ)*eta ∧ F0+15*(n:ℝ)*eta≤F0+1 := by
  have hnn : (n:ℝ)≤depth := by exact_mod_cast hn
  have hh := mul_le_mul_of_nonneg_right hnn heta
  constructor <;> nlinarith

theorem actual_depth_uniform_caps (depth n : ℕ) (hn : n≤depth)
    (F M N V Q z c F0 M0 eta : ℝ) (heta : 0≤eta) (hc : 0<c)
    (hmargin : (depth:ℝ)*7*eta≤c/2) (hsize : (depth:ℝ)*15*eta≤1)
    (hF : F≤F0+15*(n:ℝ)*eta) (hM0 : M≤M0)
    (hN : 0≤N) (hV : 0≤V) (hM : 0≤M) (hQ : 0≤Q) (hz : 0≤z)
    (hsum : F=N+V) (hinv : CanonicalMargins F M Q z (c-7*(n:ℝ)*eta)) :
    N≤F0+1 ∧ V≤F0+1 ∧ M≤min M0 (F0+1) ∧ Q≤F0+1 ∧ z≤F0+1 := by
  have hh := actual_depth_margin_size depth n hn c eta F0 heta hmargin hsize
  have hFcap : F≤F0+1 := hF.trans hh.2
  have hcaps := actual_child_size_caps F M Q z (c-7*(n:ℝ)*eta) (F0+1)
    hinv hM hQ hz (by linarith [hh.1]) hFcap
  refine ⟨?_,?_,le_min hM0 hcaps.1,hcaps.2.1,hcaps.2.2⟩ <;> linarith

theorem actual_depth_retained_loss (depth n : ℕ) (hn : n≤depth)
    (eta tau pi epsChild eps : ℝ) (he : 0≤eta) (ht : 0≤tau) (hp : 0≤pi)
    (hc : 0≤epsChild) (hbudget : (depth:ℝ)*(100*eta+4*tau+4*pi)≤eps/4)
    (hchild : (depth:ℝ)*epsChild≤eps/4) :
    (n:ℝ)*(48*eta+tau+pi+epsChild)≤eps/2 := by
  have hn' : (n:ℝ)≤depth := by exact_mod_cast hn
  have h1 := mul_le_mul_of_nonneg_right hn' (show 0≤48*eta+tau+pi+epsChild by positivity)
  have h2 : (depth:ℝ)*(48*eta+tau+pi)≤(depth:ℝ)*(100*eta+4*tau+4*pi) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    linarith
  nlinarith

theorem actual_depth_row_negative (M Mmax cutoff : ℝ) (n : ℕ) (hd : 0<cutoff)
    (hn : actualDepth Mmax cutoff≤n)
    (hpath : M+3*(n:ℝ)*cutoff/2≤Mmax) : M<0 := by
  have hn' : (actualDepth Mmax cutoff:ℝ)≤n := by exact_mod_cast hn
  have hs := (actualDepth_strict Mmax cutoff).trans_le hn'
  have hs' := (div_lt_iff₀ (by positivity : 0<3*cutoff)).mp hs
  nlinarith

end SevenEighths.InverseMoment
end

end OAI

end Source2622

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstCanonicalChildren.lean; sha256: 14ab506c4d7114d8918f67c057d594c5b390957f84281876ffcc97417302ba51 -/
section Source2623
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstGlobalCaps InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_total_cap (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)
    (negative:Bool)(J:Finset σ)(lists:σ→Finset ι)(Z M r ell V eta tau window b:ℝ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)):
    let S:=source p pool Q k l j negative J lists Z M r ell V eta tau window b;
    ∀d∈keys p S,actualCellTotalExponent Z (columnScale Z r k l negative)
      (exponent Z (k 2)) (exponent Z j) eta d≤r+3*ell+V+15*eta :=by
  intro S d hd
  obtain ⟨x,hx⟩:=(mem_keys_iff p S d).mp hd
  have hn:=retained_label_numeric p hp pool Q k l j Z ell eta hZ heta hbin hQ negative J lists
    (secondCutoff p Z M r ell V eta tau window k l j negative) b (columnScale Z r k l negative)
    x (cell_subset p S d hx)
  have he:=actual_cell_child_total_upper p hp S
    (source_valid p hp pool Q k l j negative J lists Z M r ell V eta tau window b)
    (source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b)
    d x hx Z r ell V (columnA Z k negative) (exponent Z (k 2)) (exponent Z l) (exponent Z j) eta b hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) hell hV heta hbin hb hbt
    (source_geometry p pool Q k l j negative J lists Z M r ell V eta tau window b)
    hn.1 hn.2.1 hn.2.2.2.2.2.1
  exact he

include hp in
theorem source_state_bounds (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)
    (negative:Bool)(J:Finset σ)(lists:σ→Finset ι)(Z M r ell V eta tau window b cutoff:ℝ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hterminal:cutoff≤ell+V)(hsmall:eta≤cutoff/16)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)):
    let S:=source p pool Q k l j negative J lists Z M r ell V eta tau window b;
    ∀d∈keys p S,
      0≤max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d) ∧
      0≤actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d ∧
      actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d≤r+3*ell+V+15*eta ∧
      0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d ∧
      actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d+3*cutoff/2≤M :=by
  intro S d hd
  refine ⟨le_max_left _ _,actual_cell_label_nonneg Z _ _ eta d hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) heta,?_,?_,?_⟩
  · exact source_total_cap p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hell hV hb hbt hQ d hd
  · exact (source_row_gates p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hwindow).2 d hd
  · exact source_row_decrease p hp pool Q k l j negative J lists Z M r ell V eta tau window b cutoff hZ heta hbin hterminal hsmall hQ d hd

end SevenEighths.InverseMomentFirstLabelCell

end

end OAI

end Source2623

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalChildSupport.lean; sha256: 144dc4c2b149a3635dbd857081a98116c28dd3474277598a2629e649be25fb4b -/
section Source2624
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialArithmetic InverseSecondSourceBlocks InverseSecondFibers
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
variable (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_source_prime_supported (i:ι):Supported (Ideal.span {p i}) :=by
  have hn:(Ideal.span {p i}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr (hp i)
  refine ⟨hn,?_⟩
  intro P hP
  obtain ⟨hprime,hle⟩:=(Ideal.mem_normalizedFactors_iff hn).mp hP
  have he:Ideal.span {p i}=P:=(inferInstance:(Ideal.span {p i}:Ideal O).IsMaximal).eq_of_le hprime.ne_top hle
  subst P
  exact ⟨hg i,hc i⟩

lemma canonical_supported_prod {α:Type*}(S:Finset α)(f:α→Ideal O)
    (hf:∀i∈S,Supported (f i)):Supported (∏i∈S,f i) :=by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Supported (1:Ideal O)
    refine ⟨one_ne_zero,?_⟩
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact (Multiset.notMem_zero P hP).elim
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,supported_mul_iff]
    exact ⟨hf i (Finset.mem_insert_self _ _),ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj))⟩

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_source_ideal_supported (S:Finset ι):Supported (sourceIdeal p S) :=by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  exact canonical_supported_prod S (fun i=>Ideal.span {p i}) (fun i _=>canonical_source_prime_supported p hp hg hc i)

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_prime_product_supported (S:Finset ι)(v:ι→ℕ):Supported (Ideal.span {primeProduct p S v}) :=by
  rw [primeProduct,FiniteGaussPhase.span_finset_prod]
  apply canonical_supported_prod
  intro i hi
  rw [←Ideal.span_singleton_pow]
  exact supported_pow (canonical_source_prime_supported p hp hg hc i) _

include hp hg hc in
lemma actual_second_label_supported {Jo Jn:ℕ}(x:MarkedSecondSource ι Jo Jn):
    Supported (actualSecondChild p 1 1 x).2.1 :=by
  change Supported ((Ideal.span {jLabel p x.cube.support
    (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit})*
    sourceIdeal p x.firstCommon*sourceIdeal p x.second.divisor*sourceIdeal p x.second.overlap)
  simp only [supported_mul_iff]
  exact ⟨⟨⟨canonical_prime_product_supported p hp hg hc _ _,canonical_source_ideal_supported p hp hg hc _⟩,
    canonical_source_ideal_supported p hp hg hc _⟩,canonical_source_ideal_supported p hp hg hc _⟩

include hp hg hc in
theorem actual_cell_labels_supported {Jo Jn:ℕ}(S:Finset (MarkedSecondSource ι Jo Jn))(d:BlockIndex):
    ∀I∈actualCellLabels p S d,Supported I :=by
  intro I hI
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hI
  exact actual_second_label_supported p hp hg hc x

include hp hg hc in
theorem actual_cell_labels_admissible {Jo Jn:ℕ}(S:Finset (MarkedSecondSource ι Jo Jn))(d:BlockIndex):
    ∀I∈(actualCellLabels p S d).filter Squarefree,CanonicalQuadraticSieve.Admissible I :=by
  intro I hI
  obtain ⟨hm,hs⟩:=Finset.mem_filter.mp hI
  have hh:=actual_cell_labels_supported p hp hg hc S d I hm
  exact ⟨hh.1,hs,hh.2⟩

end SevenEighths.InverseMoment

end

end OAI

end Source2624

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstLabelCellStepData.lean; sha256: 94421dc998d39866f847c72800afd8d07359baa9a01563837666a390ce40b2a6 -/
section Source2625
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_step_arithmetic (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap eps pi : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (heps : 0≤eps)
    (hwindow : Real.exp window≤Z^(4*eta))
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap)
    (hbudget : eps*(ell+exponent Z (k 4)/2+exponent Z l+Lcap+11*eta/2)≤pi) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ActualSecondSourceConditions p S ∧
    (∀x∈S,x.second.frequency≠0) ∧
    (∀x∈S,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta (index p x))) ∧
    (∀d∈keys p S,0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d) ∧
    (∀x∈S,
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
        ≤Z^(exponent Z (k 4)+eta) ∧
      primeProductNorm p x.firstCommon≤Z^(exponent Z (k 2)+eta) ∧
      (Ideal.absNorm x.quotient:ℝ)≤Z^(exponent Z l+eta) ∧
      Z^(exponent Z j-eta)≤
        ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤Z^(exponent Z j+eta) ∧
      primeProductNorm p x.firstDivisor≤Z^(exponent Z (k 3)+eta)) ∧
    (∀d,∀x∈cell p S d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p S d) ∧
    (∀d,∀I∈(actualCellLabels p S d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)) ∧
    (∀x∈S,∀i,outerNorms p x i≤Z^Lcap) ∧
    (∀x∈S,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*columnScale Z r k l negative) ∧
    (∀d∈keys p S,eps*(secondCount ell (exponent Z (k 4)) (exponent Z j) (exponent Z l)
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤pi) := by
  intro S
  have hr := source_row_gates p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hwindow
  have hl := source_labels p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hQ
  exact ⟨source_valid p hp pool Q k l j negative J lists Z M r ell V eta tau window b,
    source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b,
    hr.1,hr.2,
    retained_label_numeric p hp pool Q k l j Z ell eta hZ heta hbin hQ negative J lists _ b _,
    hl.1,hl.2,
    source_outer_caps p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap
      hZ hcol hYi hgeom hphysical,
    source_geometry p pool Q k l j negative J lists Z M r ell V eta tau window b,
    source_mass_gate p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap eps pi
      hZ heps hcol hYi hgeom hphysical hbudget⟩

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI

end Source2625

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstLabelCellStepPhysicalGates.lean; sha256: 087f8b0ba97eedcc132af88c20e873f0cc1f492681a87af39fe3d5c844e928f1 -/
section Source2626
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondUniformCutoff InversePrioritySecondSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0)

def parentWeight (l : ℕ) (x : Source ι 0) : ℂ :=
  (‖commonSelector p (fun _=>1) l x.quotientSupport‖:ℂ)

lemma parentWeight_norm (l : ℕ) (x : Source ι 0) : ‖parentWeight p l x‖≤1 := by
  simp only [parentWeight,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  simpa using InverseFirstGlobalCaps.commonSelector_norm p (fun _=>1) l x.quotientSupport

lemma secondCutoff_nonneg (Z M r ell V eta tau window : ℝ) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (hZ : 0<Z) (G E : Finset ι) :
    0≤secondCutoff p Z M r ell V eta tau window k l j negative G E := by
  apply uniformSecondRadius_nonneg _ _ _ _ _ _ _ _ _ hZ.le
  · unfold firstCellRadius
    positivity
  · exact Real.rpow_nonneg hZ.le _

include hp in
theorem secondCutoff_dominates (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (Z M r ell V eta tau window : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,∀G E : Finset ι,
      correlatedSecondRadius p (secondParentDivisor p (parent p y)) G E
        (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j) (Z^tau)≤
      secondCutoff p Z M r ell V eta tau window k l j negative G E := by
  intro y hy G E
  have hd := (InverseFirstGlobalCaps.parentCell_ideal_bounds p hp pool Q (fun _ _=>1) k l
    Z eta hZ hbin y (Finset.mem_filter.mp hy).1).2.1.2
  apply correlated_le_uniform p Z (exponent Z (k 3)) eta _ G E _ _ _
    (by unfold firstCellRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  simpa [secondParentDivisor,parent,InverseFirstGlobalCaps.sourceIdeal_norm,
    primeSubsetGenerator_norm_eq_productNorm] using hd

include hp in
theorem parent_tail_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (Z ell eta Lcap : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hcap : 0≤Lcap)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hell : ell+eta≤Lcap) (hactive : exponent Z (k 4)+eta≤Lcap)
    (hcommon : exponent Z (k 2)+eta≤Lcap) (hquot : exponent Z l+eta≤Lcap) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^Lcap ∧
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^Lcap ∧
      ‖eisEmbedding (∏i∈cubeActiveSupport y.cube.support
        (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit,p i)‖≤Z^Lcap ∧
      primeProductNorm p y.firstCommon≤Z^Lcap ∧ primeProductNorm p y.quotientSupport≤Z^Lcap := by
  intro y hy
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ y hy
  have hpw {a : ℝ} (ha : a≤Lcap) : Z^a≤Z^Lcap := Real.rpow_le_rpow_of_exponent_le hZ.le ha
  refine ⟨hb.1.trans (hpw hell),hb.2.1.trans (hpw hell),?_,
    hb.2.2.2.1.trans (hpw hcommon),hb.2.2.2.2.1.trans (hpw hquot)⟩
  have he := hb.2.2.1.trans (hpw hactive)
  have hone := Real.one_le_rpow hZ.le hcap
  change ‖eisEmbedding (∏i∈_,p i)‖^2≤Z^Lcap at he
  have hn := norm_nonneg (eisEmbedding (∏i∈cubeActiveSupport y.cube.support
    (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit,p i))
  nlinarith

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI

end Source2626

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondBlockEnergyWindowOrder.lean; sha256: 7957326034f6597f30eefd965039e44bc2c70e82c3358efd5b42f0e4f0de9703 -/
section Source2627
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff SchwartzMap

namespace SevenEighths.InverseMoment
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory InverseInitialClippedColumns
open InverseSecondProfileUniform InverseAmbientProfileTower
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_second_fixed_block_recursive_window_order
    (g₁ g₂ Φ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 4→ℝ) (B₀ : Fin 6→ℝ)
    (hm₁ : 0≤m₁) (hm₂ : 0≤m₂) (hcap : 1≤bcap)
    (hlo : ∀ i,0<lo i) (hhi : ∀ i,lo i≤hi i) (hB₀ : ∀ i,0≤B₀ i)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂) (Aker K : ℕ) (εmass : ℝ) (hεmass : 0 < εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
        (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,∀ i,InverseSecondChildWindows.actualOuterRatios p x G E V B i∈Set.Icc (lo i) (hi i)) →
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
          (clippedTest ω₁ (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  obtain ⟨ω₁,ω₂,U₀,M₀,af,bf,haf,habf,hωc₁,hωc₂,hωs₁,hωs₂,hM,hUc,hUs,hwindows⟩ :=
    InverseSecondChildWindows.actual_second_child_windows g₁ g₂ m₁ m₂ bcap lo hi B₀
      hm₁ hm₂ hcap hg₁ hg₂ hlo hhi hB₀
  refine ⟨ω₁,ω₂,af,bf,haf,habf,hωc₁,hωc₂,hωs₁,hωs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩ := actual_second_deleted_moving_mass_recursive (ι:=ι) (σ:=σ)
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hUs hg₁ hg₂ Aker J K εmass hεmass
  refine ⟨C,hC,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    G E V B Y R L Z N Vlabel εchild ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hblock hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  obtain ⟨hω₁,hω₂,hcut⟩ := hwindows p hp source pool Ψ m z G E V B (Z^N) ρ c₁ c₂ θ₁ θ₂
    hG hE hV hB hX hρ hc₁ hc₁b hc₂ hc₂b hblock
  exact henergy p hp hcop hg hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ ω₁ ω₂ G E V B Y R L Z N Vlabel εchild
    ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright

end SevenEighths.InverseMoment

end

end OAI

end Source2627

/- Original source: OAI/NumberTheory/DirichletL/Descent/PriorityCellEnergyWindowOrder.lean; sha256: 2cf5455fbb6a5f996832606147cb8d99e4ae5b74a9daddcc61826e87111e306b -/
section Source2628
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_cell_recursive_window_order
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (Aker K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
    actual_second_fixed_block_recursive_window_order (ι:=ι) (σ:=σ) (conjugateProfile g) g Φ mg mg 1
      (fun _=>1) (fun _=>2) B₀ hm hm (le_refl 1) (fun _=>zero_lt_one)
      (fun _=>by norm_num) hB₀ hcg hg Aker K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩:=hordered J
  refine ⟨C,hC,?_⟩
  intro p hp _ hcop hg₀ hpr hinj hc Jo source hs d hcell pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
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

end Source2628

/- Original source: OAI/NumberTheory/DirichletL/Descent/PriorityMovingRadiusWindowOrder.lean; sha256: 1473d36b066166d6f051fa10513c3c9871794b6348a06d83bd9cedb1c3d7727f -/
section Source2629
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_source_moving_radius_window_order
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
    actual_priority_cell_recursive_window_order (ι:=ι) (σ:=σ) om Φ lo hi hlo hsupport negative B₀ hB₀ 0 K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩:=hordered J
  refine ⟨C,hC,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
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

end Source2629

/- Original source: OAI/NumberTheory/DirichletL/Descent/PriorityRetainedMovingRadiusWindowOrder.lean; sha256: f3c70c5a0e6a64a6f71385aae2f678947c04ba28fac6f209aed6b85a51e8fb6a -/
section Source2630
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_retained_moving_radius_window_order
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
    actual_priority_source_moving_radius_window_order (ι:=ι) (σ:=σ) om Φ lo hi hlo hsupport negative B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩:=hordered J
  obtain ⟨Cbin,hCbin,hbudget⟩:=priority_source_scalar_budget caps hcaps
  refine ⟨36*(2:ℝ)^(2*K)*C,Cbin,by positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
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

end Source2630

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityFilteredEnergy.lean; sha256: 258765823be9f29960d6fb4d4d197e2af9fb9fd22f85148e0495b42ad390480f -/
section Source2631
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
theorem global_priority_filtered_moving_radius
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
    actual_priority_retained_moving_radius_window_order (ι:=ι) (σ:=σ) om rowMajorant lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  refine ⟨coefficientBound*C,Cbin,mul_nonneg coefficientBound_pos.le hC,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
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

end Source2631

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityFilteredRays.lean; sha256: 8f386e8e46af56bf21bf8064c0477bf12b10fd1d98a7509af9b4aca3366ca764 -/
section Source2632
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
theorem global_priority_filtered_all_rays
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
    global_priority_filtered_moving_radius (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  refine ⟨C*(512*32^2),Cbin,by positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
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

end Source2632

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityFilteredAggregate.lean; sha256: c30f12bb7c6002a082ef231f971376c13229ac3abbf30fef25cf060060f78766 -/
section Source2633
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
theorem global_priority_filtered_aggregate
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
    global_priority_filtered_all_rays (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  let Ctot:=(32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*
    (Fintype.card FirstCoreIndex:ℝ)*C
  refine ⟨Ctot,Cbin,by dsimp [Ctot];positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
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

end Source2633

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityFilteredStep.lean; sha256: b948b583fa24a0ffced088bffb1b6a4f1b3d477f4d00e353999c9f652c241f0a -/
section Source2634
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
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_filtered_physical_step
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤Real.exp window)(hLcap:0≤Lcap)(htau:0<tau)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
    global_priority_filtered_aggregate (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  obtain ⟨sz,Cz,hCz,hzero⟩:=global_priority_zero_physical εmass hεmass Jmax dsmall hdsmall
  obtain ⟨st,Ct,hCt,htail⟩:=global_physical_tail_rapid Jmax Lcap tau saving hLcap htau
  let Cz':=Cz*(4:ℝ)^K*(sz.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+εmass))
  let Ct':=Ct*(4:ℝ)^K*(st.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2
  refine ⟨C,Cbin,Cz',Ct',hC,hCbin,by dsimp [Cz'];positivity,by dsimp [Ct'];positivity,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
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

end Source2634

/- Original source: OAI/NumberTheory/DirichletL/Descent/ClippedChild.lean; sha256: d0e52b05cce323949b3d3d1c588f33f5b7a516cb99df6d10e7f38fbd4f12bf5d -/
section Source2635
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns JointLogSeparation InverseAmbientProfileTower
open InverseSecondSourceBlocks
local notation "O"=>ActualEisensteinCubic.O

def secondChildHeight (right:Bool)(t:Ambient (Fin 6)):ℝ :=
  if right then profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2 5
  else -profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2 4

theorem second_child_height_budget (J:ℕ)(right:Bool)(t:Ambient (Fin 6)):
    (1+‖secondChildHeight right t‖)^J≤tripleHeight J t.1*coordinateHeight J t.2:=by
  cases right
  · have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedLeft 4 t‖) (inheritedLeft_bound 4 t) J
    rw [←ambientWeight_eq_pow] at h
    simpa only [secondChildHeight,Bool.false_eq_true,ite_false,norm_neg,
      second_inherited_left_eq,ambientWeight,tripleHeight,coordinateHeight] using h
  · have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedRight 5 t‖) (inheritedRight_bound 5 t) J
    rw [←ambientWeight_eq_pow] at h
    simpa only [secondChildHeight,ite_true,second_inherited_right_eq,norm_neg,
      ambientWeight,tripleHeight,coordinateHeight] using h

theorem canonical_actual_child_uniform
    (W:ℝ→ℂ)(lo hi b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀J:ℕ,∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(_hD:∀f∈labels,0≤D f)
      (Z X F E:ℝ)(d:BlockIndex)(right:Bool)(t:Ambient (Fin 6)),
      1<Z→0<X→scales d 0*scales d 2≤b*X→0≤E→
      (∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) (Z^(max 0 (secondCellColumnExponent Z X d))) Z F≤E*(1+‖s‖)^(2*J))→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (clippedTest W (Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d))
          (secondChildHeight right t)) (Z^(max 0 (secondCellColumnExponent Z X d))) Z F≤
        C*E*(tripleHeight (2*J) t.1*coordinateHeight (2*J) t.2):=by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,he⟩:=canonical_clipped_uniform W lo hi b hlo hb hs hW
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  obtain ⟨C,hC,hbound⟩:=he J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD Z X F E d right t hZ hX hgeom hE hmoment
  obtain ⟨hc1,hcb⟩:=second_cell_clipping_ratio Z X b d hZ hX hb hgeom
  have hz:0<Z:=zero_lt_one.trans hZ
  exact (hbound p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
    _ (secondChildHeight right t) _ Z F E hc1 hcb (Real.rpow_pos_of_pos hz _) hE hmoment).trans
      (mul_le_mul_of_nonneg_left (second_child_height_budget (2*J) right t) (mul_nonneg hC.le hE))

end SevenEighths.InverseMoment

end

end OAI

end Source2635

/- Original source: OAI/NumberTheory/DirichletL/Descent/GlobalPriorityFixedChildStep.lean; sha256: f182075056626fb227dfd9b301de44e2c7ddc53d6de94b38a796dd0ec6dfb81f -/
section Source2636
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
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_fixed_child_step
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤Real.exp window)(hLcap:0≤Lcap)(htau:0<tau)
    (bcap:ℝ)(hbcap:1≤bcap)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
    global_priority_filtered_physical_step (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
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
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
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

end Source2636

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondDeletedMovingEnergyUniform.lean; sha256: 85a0d47e0c697ec2cdfad7d13543b8261ab855e08ce0325b373408f501d91693 -/
section Source2637
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedMovingPhysicalUnitsUniform : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
open InverseSecondProfileUniform InverseAmbientProfileTower
theorem actual_second_deleted_moving_physical_recursive_uniform_types
    (U₀ : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 6 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
        (ω₁ ω₂ : ℝ → ℂ) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K : ℕ) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (fun x => star (positiveSource g₁ c₁ θ₁ x)) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₁ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (positiveSource g₂ c₂ θ₂) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₂ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/(Z^N)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/(Z^N)) ≠ 0 → ∀ i,
        U₀ i ((secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B (Z^N) i)+ρ i) = 1) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  obtain ⟨C,hC,hmeasure⟩ := InverseSecondProfileUniform.second_profile_common_measure
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    ω₁ ω₂ G E V B Y R L Z N Vlabel εchild ρ c₁ c₂ θ₁ θ₂ w labels K A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hRad : 0 < Y*B/(E*V^2*(Z^N)^2) := by positivity
  obtain ⟨b₃,hb₃⟩ := hmeasure (Y*B/(E*V^2*(Z^N)^2)) hRad
  obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  let g := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
  let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) hg₁
  let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) hg₂
  let den := density g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have hden : Integrable den := balanced_density_integrable g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have he := actual_second_deleted_physical_recursive p hp hcop hg hpr hinj hc source hs
    pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) ω₁ ω₂ Φ
    G E V B Y R L Z N Vlabel εchild (fun i y => U₀ i (y+ρ i)) den w labels K J A
    hd₁ hd₂ hZ hG hE hV hB hX hden (by simpa only [star_star] using hsep)
    hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have hd : (∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖den t‖) ≤
      C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+Y*B/(E*V^2*(Z^N)^2))^Aker := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact (mul_comm _ _).le.trans hMoment
  exact he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hd (by
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ))) (by positivity))

end
end SevenEighths.InverseMoment

end OAI

end Source2637

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondDeletedMovingMassUniform.lean; sha256: 044c70861fe16c3be040d9ce28c72be883d557422b86bdd7b488a853b8220e40 -/
section Source2638
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedMovingMassUnitsUniform : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
open InverseSecondProfileUniform InverseAmbientProfileTower
theorem actual_second_deleted_moving_mass_recursive_uniform_types
    (U₀ : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 6 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J K : ℕ) (εmass : ℝ) (hεmass : 0 < εmass) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
        (ω₁ ω₂ : ℝ → ℂ) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (fun x => star (positiveSource g₁ c₁ θ₁ x)) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₁ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (positiveSource g₂ c₂ θ₂) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₂ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/(Z^N)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/(Z^N)) ≠ 0 → ∀ i,
        U₀ i ((secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B (Z^N) i)+ρ i) = 1) →
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
          (clippedTest ω₁ (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  obtain ⟨Cp,hCp,hmoving⟩ := actual_second_deleted_moving_physical_recursive_uniform_types
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  obtain ⟨Cm,hCm,hmass⟩ := actual_second_original_mass K εmass hεmass
  refine ⟨Cp*Cm,mul_nonneg hCp hCm.le,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    ω₁ ω₂ G E V B Y R L Z N Vlabel εchild ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have he := hmoving p hp hcop hg hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ ω₁ ω₂ G E V B Y R L Z N Vlabel εchild
    ρ c₁ c₂ θ₁ θ₂ w labels K A hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hm := hmass p hp source 1 1 Z ell Ractive j tcount gcount theta eta hZ
    hs.quotient_nonzero hs.second_divisor hcube₁ hcube₂ hactive hj hquot hcommon hdiv
  have hfac : 0 ≤ 36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild)) := by positivity
  have hh : 0 ≤ Cp*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
        (1+Y*B/(E*V^2*(Z^N)^2))^Aker := by positivity
  have hpref : 0 ≤ Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N):ℝ):ℂ)⁻¹‖ := by positivity
  have hb := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hfac) hh) hpref
  exact he.trans (hb.trans_eq (by ring))

end
end SevenEighths.InverseMoment

end OAI

end Source2638

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondBlockEnergyWindowOrderUniform.lean; sha256: 5fad7e42b8c35847adcf033d0a098bb9a3ab84831d85b2f3e616678c49367906 -/
section Source2639
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff SchwartzMap

namespace SevenEighths.InverseMoment
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory InverseInitialClippedColumns
open InverseSecondProfileUniform InverseAmbientProfileTower
local notation "Eis" => ActualEisensteinCubic.O
theorem actual_second_fixed_block_recursive_window_order_uniform_types
    (g₁ g₂ Φ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 4→ℝ) (B₀ : Fin 6→ℝ)
    (hm₁ : 0≤m₁) (hm₂ : 0≤m₂) (hcap : 1≤bcap)
    (hlo : ∀ i,0<lo i) (hhi : ∀ i,lo i≤hi i) (hB₀ : ∀ i,0≤B₀ i)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂) (Aker K : ℕ) (εmass : ℝ) (hεmass : 0 < εmass) :
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
        (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,∀ i,InverseSecondChildWindows.actualOuterRatios p x G E V B i∈Set.Icc (lo i) (hi i)) →
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
          (clippedTest ω₁ (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  obtain ⟨ω₁,ω₂,U₀,M₀,af,bf,haf,habf,hωc₁,hωc₂,hωs₁,hωs₂,hM,hUc,hUs,hwindows⟩ :=
    InverseSecondChildWindows.actual_second_child_windows g₁ g₂ m₁ m₂ bcap lo hi B₀
      hm₁ hm₂ hcap hg₁ hg₂ hlo hhi hB₀
  refine ⟨ω₁,ω₂,af,bf,haf,habf,hωc₁,hωc₂,hωs₁,hωs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩ := actual_second_deleted_moving_mass_recursive_uniform_types
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hUs hg₁ hg₂ Aker J K εmass hεmass
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    G E V B Y R L Z N Vlabel εchild ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hblock hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  obtain ⟨hω₁,hω₂,hcut⟩ := hwindows p hp source pool Ψ m z G E V B (Z^N) ρ c₁ c₂ θ₁ θ₂
    hG hE hV hB hX hρ hc₁ hc₁b hc₂ hc₂b hblock
  exact henergy p hp hcop hg hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ ω₁ ω₂ G E V B Y R L Z N Vlabel εchild
    ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright

end SevenEighths.InverseMoment

end

end OAI

end Source2639
