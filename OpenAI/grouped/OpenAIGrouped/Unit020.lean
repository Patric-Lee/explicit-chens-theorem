import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit010
import OpenAIGrouped.Unit016
import OpenAIGrouped.Unit014
import OpenAIGrouped.Unit015
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit008
import OpenAIGrouped.Unit017
import OpenAIGrouped.Unit009

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalWholeSource.lean; sha256: 293cfef7f9b8786691a164d981e52a9842753b3abda4ca18a593518cc6466b9a -/
section Source800
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentExceptionalWholeSource
open HeckeFamily UniqueFactorizationMonoid CenteredMomentWholeDivisorShell
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell CenteredMomentExceptionalSourceShell
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

lemma weight_nonneg {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Source α)(v:Source κ)(D:Ideal O)
    (a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (Z r:ℝ)(hZ:0≤Z):0≤exceptionalWeight s v D a b Z r:=Real.rpow_nonneg hZ _

 theorem whole_weight_bound (lo hi:ι→ℝ)(B δ:ℝ)(hB:0≤B)(hδ:0<δ):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Source I)(v:Source L),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^B) →
      ∀r:ℝ,(∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤C*Z^(δ-r):=by
  obtain ⟨Cs,hCs,hshell⟩:=exceptional_shell_subpower lo hi B (δ/2) hB (by linarith)
  obtain ⟨Cn,hCn,hcard⟩:=selected_card_subpower B (δ/2) hB (by linarith)
  refine ⟨Cn*Cs,mul_pos hCn hCs,?_⟩
  filter_upwards [hcard] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v hlo hhi Ds hDs r
  rw [sum_norm_moebius_shells]
  have hz:=zero_lt_one.trans hZ.1
  have hs (n:ℤ)(hn:n∈selectedShells Ds):
      (∑D∈shell Ds n,‖(moebius D:ℂ)‖*
        ∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤Cs*Z^(δ/2-r):=by
    have ht:=selected_scale_bounds Ds (Z^B) hDs n hn
    apply (Finset.sum_le_sum (fun D hD=>mul_le_of_le_one_left
      (Finset.sum_nonneg (fun a _=>Finset.sum_nonneg (fun b _=>weight_nonneg s v D a b Z r hz.le)))
      (moebius_norm_le_one D))).trans
    exact hshell I L s v hlo hhi (shell Ds n)
      (fun D hD=>(shell_member_data Ds n D hD).2.2.1) (dyadicScale n) Z r ht.1 hZ.1 ht.2
      (fun D hD=>(shell_member_data Ds n D hD).2.2.2.2.1)
      (fun D hD=>(shell_member_data Ds n D hD).2.2.2.2.2)
  calc
    _≤∑n∈selectedShells Ds,Cs*Z^(δ/2-r):=Finset.sum_le_sum hs
    _=((selectedShells Ds).card:ℝ)*(Cs*Z^(δ/2-r)):=by simp
    _≤(Cn*Z^(δ/2))*(Cs*Z^(δ/2-r)):=
      mul_le_mul_of_nonneg_right (hZ.2 Ds hDs) (mul_nonneg hCs.le (Real.rpow_nonneg hz.le _))
    _=(Cn*Cs)*Z^(δ-r):=by
      rw [show δ-r=δ/2+(δ/2-r) by ring,Real.rpow_add hz]
      ring

theorem actual_whole_source (lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r:ℝ,∀rows:Finset O,(∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B r z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-r)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_paired_amplitude ε B hε hB
  obtain ⟨Cs,hCs,hmass⟩:=whole_weight_bound lo hi Lbound δ hL hδ
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨Ca,hCa,hpoint⟩:=hJ Q hQ
  refine ⟨Ca*Cs,mul_pos hCa hCs,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rows hs hv Ds hDs
  have hz:=zero_lt_one.trans hZ.1
  let A:ℝ:=Ca*(rows.card:ℝ)*Z^(2*ε)*profileMass s v p q J
  have hA:0≤A:=mul_nonneg (by positivity) (profileMass_nonneg s v p q J)
  have hterm (D:Ideal O)(a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (I⊕Fin 2)))
      (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (L⊕Fin 2))):
      (∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        A*exceptionalWeight s.toSource v.toSource D a b Z r:=by
    calc
      _≤∑z∈rows,Ca*Z^(2*ε)*profileMass s v p q J*
          exceptionalWeight s.toSource v.toSource D a b Z r:=by
        apply Finset.sum_le_sum
        intro z hzrow
        exact (hpoint I L s v p q Z r hZ.1 z (hs z hzrow) (hv z hzrow) D a b).trans_eq
          (by dsimp [profileMass];ring)
      _=_:=by simp only [Finset.sum_const, nsmul_eq_mul];dsimp [A];ring
  calc
    _≤∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          A*exceptionalWeight s.toSource v.toSource D a b Z r:=by
      apply Finset.sum_le_sum
      intro D hD
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hterm D a b))
    _=A*(∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          exceptionalWeight s.toSource v.toSource D a b Z r):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _≤A*(Cs*Z^(δ-r)):=mul_le_mul_of_nonneg_left (hZ.2 I L s.toSource v.toSource hlo hhi Ds hDs r) hA
    _=_:=by
      rw [show 2*ε+δ-r=2*ε+(δ-r) by ring,Real.rpow_add hz]
      dsimp [A]
      ring

end SevenEighths.CenteredMomentExceptionalWholeSource

end

end OAI

end Source800

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceRectangle.lean; sha256: acd85c381e6006addb0d4f1322f7b5c21a488eebf0043436ee1caa16501acb9e -/
section Source801
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRectangle
open ActualEisensteinCubic HeckeFamily CenteredMomentHeckeExpansion CenteredMomentRectangle
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentExtraction CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentRemainingBox
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def tuplePools (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O)) :
    (ι⊕Fin 2)→Finset (Ideal O) := Sum.elim slots (fun j=>if j=0 then S₁ else S₂)

def tuplePool (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O)) : Finset (Tuple ι) :=
  Fintype.piFinset (tuplePools slots S₁ S₂)

def pack (v : ι→Ideal O) (I J : Ideal O) : Tuple ι :=
  Sum.elim v (fun j=>if j=0 then I else J)

omit [Fintype ι] in
@[simp] theorem pack_slot (v : ι→Ideal O) (I J : Ideal O) (i : ι) :
    pack v I J (Sum.inl i)=v i := rfl
omit [Fintype ι] in
@[simp] theorem pack_left (v : ι→Ideal O) (I J : Ideal O) :
    pack v I J (Sum.inr 0)=I := by simp [pack]
omit [Fintype ι] in
@[simp] theorem pack_right (v : ι→Ideal O) (I J : Ideal O) :
    pack v I J (Sum.inr 1)=J := by simp [pack]

theorem pack_product (v : ι→Ideal O) (I J : Ideal O) :
    finiteTupleProduct (pack v I J)=(∏ i,v i)*I*J := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,pack_slot,Fin.prod_univ_two,
    pack_left,pack_right,mul_assoc]

def tuplePoolEquiv (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O)) :
    tuplePool slots S₁ S₂ ≃ ((∀ i,slots i)×S₁×S₂) where
  toFun v := ((fun i=>⟨v.val (Sum.inl i),Fintype.mem_piFinset.mp v.property (Sum.inl i)⟩),
    ⟨v.val (Sum.inr 0),by simpa [tuplePools] using Fintype.mem_piFinset.mp v.property (Sum.inr 0)⟩,
    ⟨v.val (Sum.inr 1),by simpa [tuplePools] using Fintype.mem_piFinset.mp v.property (Sum.inr 1)⟩)
  invFun v := ⟨pack (fun i=>v.1 i) v.2.1 v.2.2,by
    apply Fintype.mem_piFinset.mpr
    intro i
    cases i with
    | inl i => exact (v.1 i).property
    | inr j => fin_cases j <;> simp [pack,tuplePools]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    cases i with
    | inl i => rfl
    | inr j => fin_cases j <;> rfl
  right_inv v := rfl

theorem sum_tuplePool (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (f : Tuple ι→ℂ) :
    (∑ v∈tuplePool slots S₁ S₂,f v)=
      ∑ v : (∀ i,slots i),∑ I : S₁,∑ J : S₂,f (pack (fun i=>v i) I J) := by
  rw [← Finset.sum_coe_sort (tuplePool slots S₁ S₂) f]
  have he := (tuplePoolEquiv slots S₁ S₂).symm.sum_comp (fun v : tuplePool slots S₁ S₂=>f v)
  change (∑ x : ((∀ i,slots i)×S₁×S₂),f (pack (fun i=>x.1 i) x.2.1 x.2.2))=
    (∑ v : tuplePool slots S₁ S₂,f v) at he
  simpa only [Fintype.sum_prod_type] using he.symm

theorem finite_column_regroup (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (w : Ideal O→ℂ) :
    (∑ I∈finiteColumns S,finiteColumnCoefficient S β I*w I)=
      ∑ v∈S,β v*w (finiteTupleProduct v) := by
  simp only [finiteColumnCoefficient,Finset.sum_mul]
  calc
    _ = ∑ I∈finiteColumns S,∑ v∈S.filter (fun v=>finiteTupleProduct v=I),
        β v*w (finiteTupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

def PlainCoverage (S : Finset (Ideal O)) (W : ℝ→ℂ) (B : Ideal O) (X Y : ℝ) : Prop :=
  ∀ I, W ((Ideal.absNorm (B*I):ℝ)/X)≠0 ∨ W ((Ideal.absNorm (B*I):ℝ)/Y)≠0 → I∈S

theorem rectangle_zero_left (S₁ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (I J : Ideal O) (hI : I∉S₁) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)=0 := by
  have hx : W₁ ((Ideal.absNorm (B₁*I):ℝ)/X₁)=0 := by
    by_contra hn;exact hI (h I (Or.inl hn))
  have hy : W₁ ((Ideal.absNorm (B₁*I):ℝ)/Y₁)=0 := by
    by_contra hn;exact hI (h I (Or.inr hn))
  simp only [idealRectangle,hx,hy,zero_mul,sub_self]

theorem rectangle_zero_right (S₂ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h : PlainCoverage S₂ W₂ B₂ X₂ Y₂) (I J : Ideal O) (hJ : J∉S₂) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)=0 := by
  have hx : W₂ ((Ideal.absNorm (B₂*J):ℝ)/X₂)=0 := by
    by_contra hn;exact hJ (h J (Or.inl hn))
  have hy : W₂ ((Ideal.absNorm (B₂*J):ℝ)/Y₂)=0 := by
    by_contra hn;exact hJ (h J (Or.inr hn))
  simp only [idealRectangle,hx,hy,mul_zero,sub_self]

theorem finite_plain_rectangle (S₁ S₂ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂)
    (f : Ideal O→Ideal O→ℂ) :
    (∑ I : S₁,∑ J : S₂,f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J))=
      ∑' I : Ideal O,∑' J : Ideal O,f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J) := by
  symm
  rw [tsum_eq_sum (s := S₁)]
  · rw [← Finset.sum_coe_sort S₁ (fun I=>∑' J : Ideal O,
      f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J))]
    apply Finset.sum_congr rfl
    intro I hI
    rw [tsum_eq_sum (s := S₂)]
    · exact (Finset.sum_coe_sort S₂ _).symm
    · intro J hJ
      rw [rectangle_zero_right S₂ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₂ I J hJ,mul_zero]
  · intro I hI
    simp only [rectangle_zero_left S₁ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₁ I _ hI,mul_zero,tsum_zero]

def fullMaskedRectangle (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (R L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) : ℂ :=
  ∑ v : (∀ i,slots i),(∏ i,ν i (v i)*Wslot i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      (if IsCoprime ((∏ i,(v i:Ideal O))*I*J) R then (1:ℂ) else 0)*
      (if L∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
      idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)

theorem source_polynomial_eq_full_masked_rectangle (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈finiteColumns (tuplePool slots S₁ S₂),
      finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      fullMaskedRectangle η m A z t slots ν (fun i I=>Wslot i ((Ideal.absNorm I:ℝ)/P i))
        R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ := by
  rw [finite_column_regroup,sum_tuplePool]
  unfold fullMaskedRectangle
  apply Finset.sum_congr rfl
  intro v hv
  rw [← finite_plain_rectangle S₁ S₂ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₁ h₂]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [profileCoefficient,pack_product,pack_slot,pack_left,pack_right]
  ring

theorem fullMaskedRectangle_pullback (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (R L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    fullMaskedRectangle η m A z t slots ν Wslot R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ =
      fullMaskedRectangle η m A z t slots ν Wslot R L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) 1 1 := by
  unfold fullMaskedRectangle
  simp only [one_mul,idealRectangle_extract]

theorem pullback_same_product (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/Ideal.absNorm B₁)*(X₂/Ideal.absNorm B₂)=T/(Ideal.absNorm B₁*Ideal.absNorm B₂:ℝ) ∧
    (Y₁/Ideal.absNorm B₁)*(Y₂/Ideal.absNorm B₂)=T/(Ideal.absNorm B₁*Ideal.absNorm B₂:ℝ) :=
  extracted_product_scale X₁ X₂ Y₁ Y₂ T B₁ B₂ hX hY

theorem fullMaskedRectangle_modulus_one [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    fullMaskedRectangle η m A z t slots ν Wslot 1 L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ =
      CenteredMomentDivisorRowEnergy.maskedRectangle η m A z t slots
        (fun i I=>ν i I*Wslot i I) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) := by
  simp only [fullMaskedRectangle,CenteredMomentDivisorRowEnergy.maskedRectangle,
    isCoprime_one_right,ite_true,one_mul,idealRectangle_extract]
  apply Finset.sum_congr (by ext; simp)
  intro v hv
  rfl

theorem source_polynomial_eq_maskedRectangle [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈finiteColumns (tuplePool slots S₁ S₂),
      finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient 1 ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      CenteredMomentDivisorRowEnergy.maskedRectangle η m A z t slots
        (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) :=
  (source_polynomial_eq_full_masked_rectangle η m A z t slots S₁ S₂ 1 L ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂).trans
    (fullMaskedRectangle_modulus_one η m A z t slots ν _ L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)

theorem plainCoverage_residualPool (S : Finset (Ideal O)) (W : ℝ→ℂ)
    (B C : Ideal O) (hC : C≠0) (X Y : ℝ) (h : PlainCoverage S W B X Y) :
    PlainCoverage (residualPool C hC S) W (B*C) X Y := by
  intro I hi
  apply (mem_residualPool C hC S I).mpr
  apply h (C*I)
  simpa only [mul_assoc] using hi

def plainSupportPool (b X Y : ℝ) : Finset (Ideal O) := idealBall (b*X)∪idealBall (b*Y)

theorem plainSupportPool_coverage (W : ℝ→ℂ) (b X Y : ℝ)
    (hW₀ : W 0=0) (hs : Function.support W⊆Set.Iic b) (hX : 0<X) (hY : 0<Y) :
    PlainCoverage (plainSupportPool b X Y) W 1 X Y := by
  intro I hi
  simp only [one_mul] at hi
  have cover (Q : ℝ) (hQ : 0<Q) (hne : W ((Ideal.absNorm I:ℝ)/Q)≠0) :
      I∈idealBall (b*Q) := by
    apply (mem_idealBall _ _).mpr
    constructor
    · intro hI
      subst I
      apply hne
      simp only [map_zero,Nat.cast_zero,zero_div,hW₀]
    · exact (div_le_iff₀ hQ).mp (hs hne)
  obtain hi|hi := hi
  · exact Finset.mem_union_left _ (cover X hX hi)
  · exact Finset.mem_union_right _ (cover Y hY hi)

theorem extracted_plainSupportPool_coverage (W : ℝ→ℂ) (B : Ideal O) (hB : B≠0)
    (b X Y : ℝ) (hW₀ : W 0=0) (hs : Function.support W⊆Set.Iic b)
    (hX : 0<X) (hY : 0<Y) :
    PlainCoverage (residualPool B hB (plainSupportPool b X Y)) W B X Y := by
  simpa only [one_mul] using plainCoverage_residualPool (plainSupportPool b X Y)
    W 1 B hB X Y (plainSupportPool_coverage W b X Y hW₀ hs hX hY)

theorem supported_source_polynomial_eq_full_rectangle
    (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (R L : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hw₁ : W₁ 0=0) (hw₂ : W₂ 0=0)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) :
    let T := tuplePool slots
      (residualPool B₁ hB₁ (plainSupportPool b₁ X₁ Y₁))
      (residualPool B₂ hB₂ (plainSupportPool b₂ X₂ Y₂))
    (∑ I∈finiteColumns T,finiteColumnCoefficient T
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I*rowWeight η m A z t I)=
      fullMaskedRectangle η m A z t slots ν (fun i I=>Wslot i ((Ideal.absNorm I:ℝ)/P i))
        R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ :=
  source_polynomial_eq_full_masked_rectangle η m A z t slots _ _ R L ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
    (extracted_plainSupportPool_coverage W₁ B₁ hB₁ b₁ X₁ Y₁ hw₁ hs₁ hX₁ hY₁)
    (extracted_plainSupportPool_coverage W₂ B₂ hB₂ b₂ X₂ Y₂ hw₂ hs₂ hX₂ hY₂)

theorem liveBox_eq_tuplePool (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ i,B i≠0) :
    liveBox S B hB = tuplePool
      (fun i : liveIndices B=>residualPool (B (Sum.inl i.val)) (hB _) (S (Sum.inl i.val)))
      (residualPool (B (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
      (residualPool (B (Sum.inr 1)) (hB _) (S (Sum.inr 1))) := by
  ext v
  simp only [liveBox,tuplePool,Fintype.mem_piFinset]
  constructor <;> intro h i
  all_goals
    cases i with
    | inl i => exact h (Sum.inl i)
    | inr j =>
      fin_cases j
      · exact h (Sum.inr 0)
      · exact h (Sum.inr 1)

theorem live_source_polynomial_eq_full_rectangle
    (η : Character) (m A z : O) (t : ℝ)
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι) (hB : ∀ i,B i≠0)
    (C R : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁)
    (h₂ : PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂) :
    (∑ I∈finiteColumns (liveBox S B hB),finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I * rowWeight η m A z t I)=
      fullMaskedRectangle η m A z t
        (fun i : liveIndices B=>residualPool (B (Sum.inl i.val)) (hB _) (S (Sum.inl i.val)))
        (fun i=>ν i.val) (fun i I=>Wslot i.val ((Ideal.absNorm I:ℝ)/P i.val))
        (R*C) 1 W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) := by
  rw [liveBox_eq_tuplePool]
  exact source_polynomial_eq_full_masked_rectangle η m A z t _ _ _ (R*C) 1
    (fun i : liveIndices B=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ _ _
    (plainCoverage_residualPool _ W₁ B₁ _ (hB _) X₁ Y₁ h₁)
    (plainCoverage_residualPool _ W₂ B₂ _ (hB _) X₂ Y₂ h₂)

end SevenEighths.CenteredMomentSourceRectangle

end

end OAI

end Source801

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceRectangleMask.lean; sha256: 84c74c8e4f557c9709a986a4a44c7e1f98d0799a2ed1b4ba1b995346d39eb6db -/
section Source802
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceRectangleMask
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSourceRectangle
open CenteredMomentDivisorRowEnergy CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_ideal_mask (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (R I : Ideal O) :
    (if IsCoprime I R then (1:ℂ) else 0)*rowWeight η m A z t I=
      rowWeight η (m*idealGenerator R) A z t I := by
  by_cases hI : Supported I
  · have hm : (m*idealGenerator R)^6*(A*z)=(idealGenerator R)^6*(m^6*(A*z)) := by ring
    change (if IsCoprime I R then (1:ℂ) else 0)*
      ((idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))=
      (idealCoeff η I*idealRowHom ((m*idealGenerator R)^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)
    rw [hm,idealRowHom_argument_mul ((idealGenerator R)^6) (m^6*(A*z)) I,
      idealRowHom_sixth_mask (idealGenerator R) I hI,span_idealGenerator]
    ring
  · rw [rowWeight_zero_of_not_supported η m A z t hmLam hm2 I hI,
      rowWeight_zero_of_not_supported η (m*idealGenerator R) A z t
        (hmLam.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _)) I hI,mul_zero]

theorem ideal_mask_nonzero (m : O) (hm : m≠0) (R : Ideal O) (hR : R≠0) :
    m*idealGenerator R≠0 := mul_ne_zero hm (idealGenerator_ne_zero R hR)

theorem fullMaskedRectangle_eq_maskedRectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (R L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    fullMaskedRectangle η m A z t slots ν Wslot R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂=
      maskedRectangle η (m*idealGenerator R) A z t slots
        (fun i I=>ν i I*Wslot i I) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) := by
  unfold fullMaskedRectangle maskedRectangle
  apply Finset.sum_congr (by ext;simp)
  intro v hv
  congr 1
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [idealRectangle_extract]
  rw [mul_right_comm (if IsCoprime _ R then (1:ℂ) else 0) _,rowWeight_ideal_mask η m A z t hmLam hm2]
  ring

theorem source_polynomial_eq_maskedRectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈CenteredMomentSourceMass.finiteColumns (tuplePool slots S₁ S₂),
      CenteredMomentSourceMass.finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (CenteredMomentSourceProfileMass.profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      maskedRectangle η (m*idealGenerator R) A z t slots
        (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) :=
  (source_polynomial_eq_full_masked_rectangle η m A z t slots S₁ S₂ R L ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂).trans
    (fullMaskedRectangle_eq_maskedRectangle η m A z t hmLam hm2 slots ν _ R L W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂)

end SevenEighths.CenteredMomentSourceRectangleMask

end

end OAI

end Source802

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceRectangleEnergy.lean; sha256: 186a7da59349235c6b2232fb5fe0f7b70811addf4f1c22ba581037063f2e7c03 -/
section Source803
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRectangleEnergy
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedDomain CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSourceRectangle
open CenteredMomentSourceRectangleMask CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentDivisorRowEnergy CenteredMomentDivisorRetained
local notation "O" => ActualEisensteinCubic.O

theorem height_source_row (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S=>β I*heightCoeff η t I) z=
      ∑ I∈S,β I*rowWeight η fixedBadMask 1 z t I := by
  rw [source_rowPolynomial S (fun I=>β I*heightCoeff η t I) z]
  calc
    _ = ∑ I∈supportedColumns S,β I*rowWeight η fixedBadMask 1 z t I := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp hI).2,
        rowWeight_split η fixedBadMask 1 z t I]
      ring
    _ = _ := Finset.sum_filter_of_ne (fun I hI hn => by
      by_contra hs
      apply hn
      rw [rowWeight_zero_of_not_supported η fixedBadMask 1 z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) I hs,mul_zero])

theorem source_restricted_energy_eq_rectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (t : ℝ) (keep : O→Prop)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (tuplePool slots S₁ S₂))
      (finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L))
      (heightCoeff η t) W K=
      ∑' z : O,if keep z then
        ‖maskedRectangle η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
          (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2*
        (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0 := by
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_congr
  intro z
  rw [height_source_row]
  rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    η fixedBadMask 1 z t (dvd_mul_right _ _) (dvd_mul_left _ _)
    slots S₁ S₂ R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂]

end SevenEighths.CenteredMomentSourceRectangleEnergy

end

end OAI

end Source803

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalMaskedSource.lean; sha256: 53b0f7e4dc3cc14bfbf1d6b9c148df2fe80f24f2367aa957fb0afa8ab126575c -/
section Source804
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentExceptionalMaskedSource
open HeckeFamily UniqueFactorizationMonoid CenteredMomentEligibleEnergy
open CenteredMomentDivisorRowEnergy CenteredMomentActiveAllocation
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalWholeSource
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSourceRow CenteredMomentRowNorm
local notation "O" => HeckeFamily.O
universe u
variable {ι κ:Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def maskedAmplitude (s:Data ι)(D:Ideal O)(z:O):ℂ:=
  (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

theorem maskedAmplitude_eq (s:Data ι)(D:Ideal O)(hD:Squarefree D)(z:O):
    maskedAmplitude s D z=∑a∈s.toSource.active D,amplitude s D a z:=by
  unfold maskedAmplitude
  rw [masked_eq_active_allocations s.η s.m s.A z s.t s.slots s.coefficient D hD
    s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos,Finset.mul_sum]
  rfl

theorem source_polynomial_eq (s:Data ι)(S₁ S₂:Finset (Ideal O))(R D B₁ B₂:Ideal O)
    (X₁ X₂ Y₁ Y₂:ℝ)
    (hm:s.m=fixedBadMask*idealGenerator R)(hA:s.A=1)
    (hX₁:s.X₁=X₁/Ideal.absNorm B₁)(hX₂:s.X₂=X₂/Ideal.absNorm B₂)
    (hY₁:s.Y₁=Y₁/Ideal.absNorm B₁)(hY₂:s.Y₂=Y₂/Ideal.absNorm B₂)
    (hc₁:PlainCoverage S₁ s.W₁ B₁ X₁ Y₁)(hc₂:PlainCoverage S₂ s.W₂ B₂ X₂ Y₂)(z:O):
    (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
      rowPolynomial Finset.univ (sourceGenerator (finiteColumns (tuplePool s.slots S₁ S₂)))
        (fun I: supportedColumns (finiteColumns (tuplePool s.slots S₁ S₂))=>
          finiteColumnCoefficient (tuplePool s.slots S₁ S₂)
            (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ D) I*
              heightCoeff s.η s.t I) z=maskedAmplitude s D z:=by
  rw [height_source_row]
  rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    s.η fixedBadMask 1 z s.t (dvd_mul_right _ _) (dvd_mul_left _ _)
    s.slots S₁ S₂ R D s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hc₁ hc₂]
  simp only [maskedAmplitude,hm,hA,hX₁,hX₂,hY₁,hY₂]
  rfl

theorem paired_masked_le (s:Data ι)(v:Data κ)(D:Ideal O)(hD:Squarefree D)(rows:Finset O):
    (∑z∈rows,‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
      ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖:=by
  calc
    _≤∑z∈rows,(∑a∈s.toSource.active D,‖amplitude s D a z‖)*
        (∑b∈v.toSource.active D,‖amplitude v D b z‖):=by
      apply Finset.sum_le_sum
      intro z hz
      rw [maskedAmplitude_eq s D hD,maskedAmplitude_eq v D hD]
      exact mul_le_mul (norm_sum_le _ _) (norm_sum_le _ _) (norm_nonneg _)
        (Finset.sum_nonneg (fun a _=>norm_nonneg _))
    _=_:=by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s:=rows) (t:=s.toSource.active D)]
      exact Finset.sum_comm

theorem whole_masked_le (s:Data ι)(v:Data κ)(Ds:Finset (Ideal O))(rows:Finset O):
    (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
      ∑D∈Ds,‖(moebius D:ℂ)‖*∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖:=by
  apply Finset.sum_le_sum
  intro D hD
  by_cases hμ:(moebius D:ℂ)=0
  · simp [hμ]
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply paired_masked_le s v D
    exact CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero D hμ

theorem actual_masked_whole_source (lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r:ℝ,∀rows:Finset O,(∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B r z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,
        ‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-r)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_whole_source lo hi ε δ B Lbound hε hδ hB hL
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hCZ⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  filter_upwards [hCZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rows hs hv Ds hDs
  exact (whole_masked_le s v Ds rows).trans (hZ.2 I L s v p q hlo hhi r rows hs hv Ds hDs)

end SevenEighths.CenteredMomentExceptionalMaskedSource

end

end OAI

end Source804

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalAsymmetricSource.lean; sha256: 0e8a2a4a392e4cb5ea04583944921ab76559460ca4bb875deb8c608a37d22965 -/
section Source805
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentExceptionalAsymmetricSource
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentDetectorDictionary
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentExceptionalAllocationShell CenteredMomentExceptionalWholeSource
open CenteredMomentExceptionalMaskedSource UniqueFactorizationMonoid CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_paired_asymmetric (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(ι κ:Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ],
      ∀(s:Data ι)(v:Data κ)(p q:Tests)(Z r rRight:ℝ),1<Z → ∀z:O,
      Admissible s p Q Z B r z → Admissible v q Q Z B rRight z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*Z^(2*ε)*p.heightWeight s.t^J*q.heightWeight v.t^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z r:=by
  obtain ⟨J,hJ⟩:=actual_allocated_amplitude ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι κ _ _ _ _ s v p q Z r rRight hZ z hs hv D a b
  have hpoint (α:Type u) [Fintype α] [DecidableEq α] (s:Data α)(p:Tests)(r0:ℝ)
      (hs:Admissible s p Q Z B r0 z)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):
      ‖amplitude s D a z‖≤C*Z^ε*p.heightWeight s.t^J*slotControl s*Real.sqrt (volume s)/
        (formalReductionFactor D a s.P*Z^(max (r0-Real.logb Z (formalReductionFactor D a s.P)) 0)):=by
    obtain ⟨hP,hm,hA,hz,hml,hm2,hcond,hex,hW₁,hW₂,hX₁,hX₂,hY₁,hY₂⟩:=hs
    apply norm_le_of_squared _ _ _ _ _
    · exact mul_nonneg (by dsimp [Tests.heightWeight]; positivity) (slotControl_nonneg s)
    · exact (volume_pos s).le
    · exact s.reduction_pos D a
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact hbound α s Z hZ hP z hm hA hz hml hm2 hcond hex D a
        (p.reverse 0) (p.reverse 1) (p.index 0) (p.index 1) (p.index_le 0) (p.index_le 1)
        (p.sigma 0) (p.sigma_mem 0) (p.sigma 1) (p.sigma_mem 1)
        (p.height 0) (p.height 1) r0 hW₁ hW₂ hX₁ hX₂ hY₁ hY₂
  have hl:=hpoint ι s p r hs a
  have hr:=hpoint κ v q rRight hv b
  have hcap:1≤Z^(max (rRight-Real.logb Z (formalReductionFactor D b v.P)) 0):=
    Real.one_le_rpow hZ.le (le_max_right _ _)
  have hr':‖amplitude v D b z‖≤
      C*Z^ε*q.heightWeight v.t^J*slotControl v*Real.sqrt (volume v)/formalReductionFactor D b v.P:=by
    apply hr.trans
    apply div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity) (slotControl_nonneg v)) (Real.sqrt_nonneg _))
      (v.reduction_pos D b)
    exact le_mul_of_one_le_right (v.reduction_pos D b).le hcap
  apply (mul_le_mul hl hr' (norm_nonneg _) (by
    exact div_nonneg (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity)
      (slotControl_nonneg s)) (Real.sqrt_nonneg _)) (mul_nonneg (s.reduction_pos D a).le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))).trans_eq
  rw [←reduction_cap_identity s v D a b Z r hZ]
  have hp:Z^(2*ε)=(Z^ε)^2:=by rw [mul_comm (2:ℝ) ε,Real.rpow_mul (zero_lt_one.trans hZ).le,Real.rpow_two]
  rw [hp]
  ring

lemma reduction_ge_one {α:Type u} [Fintype α] [DecidableEq α]
    (s:Data α)(hP:∀i,1≤s.P i)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):1≤formalReductionFactor D a s.P:=by
  have hn (j:Fin 2):(1:ℝ)≤Ideal.absNorm (selectedPlain D a j):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hn 0) (hn 1))
    (Finset.one_le_prod₀ (fun i _=>hP i))

lemma raw_cap_weight {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(hP:∀i,1≤s.P i)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2)))(Z r:ℝ)(hZ:1<Z):
    exceptionalWeight s.toSource v.toSource D a b Z r=
      exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
  have hd:0≤Real.logb Z (formalReductionFactor D a s.P):=
    Real.logb_nonneg hZ (reduction_ge_one s hP D a)
  unfold exceptionalWeight
  congr 2
  by_cases hr:0≤r
  · rw [max_eq_left hr]
  · have h0:r≤0:=le_of_not_ge hr
    rw [max_eq_right h0,max_eq_right (by linarith:r-Real.logb Z (formalReductionFactor D a s.P)≤0),
      max_eq_right (by linarith:0-Real.logb Z (formalReductionFactor D a s.P)≤0)]

theorem actual_paired_capped (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(α κ:Type u) [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ],
      ∀(s:Data α)(v:Data κ)(p q:Tests)(Z r rRight:ℝ),1<Z → ∀z:O,
      Admissible s p Q Z B r z → Admissible v q Q Z B rRight z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*Z^(2*ε)*p.heightWeight s.t^J*q.heightWeight v.t^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
  obtain ⟨J,hJ⟩:=actual_paired_asymmetric ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro α κ _ _ _ _ s v p q Z r rRight hZ z hs hv D a b
  rw [←raw_cap_weight s v hs.1 D a b Z r hZ]
  exact hbound α κ s v p q Z r rRight hZ z hs hv D a b

theorem actual_whole_asymmetric (lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r rRight:ℝ,∀rows:Finset O,(∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B rRight z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-max r 0)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_paired_capped ε B hε hB
  obtain ⟨Cs,hCs,hmass⟩:=whole_weight_bound lo hi Lbound δ hL hδ
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨Ca,hCa,hpoint⟩:=hJ Q hQ
  refine ⟨Ca*Cs,mul_pos hCa hCs,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rRight rows hs hv Ds hDs
  have hz:=zero_lt_one.trans hZ.1
  let A:ℝ:=Ca*(rows.card:ℝ)*Z^(2*ε)*profileMass s v p q J
  have hA:0≤A:=mul_nonneg (by positivity) (profileMass_nonneg s v p q J)
  have hterm (D:Ideal O)(a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (I⊕Fin 2)))
      (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (L⊕Fin 2))):
      (∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        A*exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
    calc
      _≤∑z∈rows,Ca*Z^(2*ε)*profileMass s v p q J*
          exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
        apply Finset.sum_le_sum
        intro z hzrow
        exact (hpoint I L s v p q Z r rRight hZ.1 z (hs z hzrow) (hv z hzrow) D a b).trans_eq
          (by dsimp [profileMass];ring)
      _=_:=by simp only [Finset.sum_const, nsmul_eq_mul];dsimp [A];ring
  calc
    _≤∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          A*exceptionalWeight s.toSource v.toSource D a b Z (max r 0):=by
      apply Finset.sum_le_sum
      intro D hD
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hterm D a b))
    _=A*(∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          exceptionalWeight s.toSource v.toSource D a b Z (max r 0)):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _≤A*(Cs*Z^(δ-max r 0)):=mul_le_mul_of_nonneg_left (hZ.2 I L s.toSource v.toSource hlo hhi Ds hDs (max r 0)) hA
    _=_:=by
      rw [show 2*ε+δ-max r 0=2*ε+(δ-max r 0) by ring,Real.rpow_add hz]
      dsimp [A]
      ring

theorem actual_masked_asymmetric (lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r rRight:ℝ,∀rows:Finset O,(∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B rRight z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,
        ‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-max r 0)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_whole_asymmetric lo hi ε δ B Lbound hε hδ hB hL
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hCZ⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  filter_upwards [hCZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rRight rows hs hv Ds hDs
  exact (whole_masked_le s v Ds rows).trans (hZ.2 I L s v p q hlo hhi r rRight rows hs hv Ds hDs)

end SevenEighths.CenteredMomentExceptionalAsymmetricSource

end

end OAI

end Source805

/- Original source: OAI/NumberTheory/DirichletL/Moments/RadialSourceDictionary.lean; sha256: d0a264c68ef251fcadb6b211d98ba68087ac3affc49b047609072c206778893c -/
section Source806
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentRadialSourceDictionary
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

 theorem actual_source_energy {ι:Type*} [Fintype ι] [DecidableEq ι]
    (s:Data ι) (r:Radial) (S₁ S₂:Finset (Ideal O)) (R L B₁ B₂:Ideal O)
    (X₁ X₂ Y₁ Y₂:ℝ)
    (hm:s.m=fixedBadMask*idealGenerator R) (hA:s.A=1)
    (hX₁:s.X₁=X₁/Ideal.absNorm B₁) (hX₂:s.X₂=X₂/Ideal.absNorm B₂)
    (hY₁:s.Y₁=Y₁/Ideal.absNorm B₁) (hY₂:s.Y₂=Y₂/Ideal.absNorm B₂)
    (hcov₁:PlainCoverage S₁ s.W₁ B₁ X₁ Y₁) (hcov₂:PlainCoverage S₂ s.W₂ B₂ X₂ Y₂) :
    sourceRestrictedEnergy r.keep (finiteColumns (tuplePool s.slots S₁ S₂))
      (finiteColumnCoefficient (tuplePool s.slots S₁ S₂)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L))
      (heightCoeff s.η s.t) r.profile r.scale/(s.X₁*s.X₂*∏i,s.P i)=energy s r L := by
  rw [source_restricted_energy_eq_rectangle s.η s.t r.keep s.slots S₁ S₂ R L
    s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hcov₁ hcov₂ r.profile r.scale]
  unfold energy
  rw [←tsum_div_const]
  apply tsum_congr
  intro z
  have ht:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
  have hc:s.coefficient=(fun i I=>s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)):=rfl
  rw [hc]
  dsimp only [Radial.weight]
  rw [hm,hA,hX₁,hX₂,hY₁,hY₂]
  split_ifs <;> ring

end SevenEighths.CenteredMomentRadialSourceDictionary

end

end OAI

end Source806

/- Original source: OAI/NumberTheory/DirichletL/Moments/ActiveSourceRetained.lean; sha256: 50823529a670b4ff7b972d1c0366c0b4980e8467bc31a4843965a0aadda130f2 -/
section Source807
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentActiveSourceRetained
open CenteredMomentActiveAllocation HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_to_active_retained (N : ℕ) (hslots : Fintype.card ι≤N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
      ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i,0≤M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤M i) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
      ∀ (rows : Finset O) (ω : O→ℝ),(∀ z∈rows,0≤ω z) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      let coeff := fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
      (∑ z∈rows,ω z*‖(Real.sqrt (raw*∏ i,P i):ℂ)⁻¹*
        rowPolynomial Finset.univ (sourceGenerator Q)
          (fun I : supportedColumns Q=>β I*heightCoeff η t I) z‖^2)≤
      C*(Ideal.absNorm L:ℝ)^ε*
        ∑ a ∈ activeAllocations η (fixedBadMask*idealGenerator R) 1 t slots coeff L W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂) (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
          ∑ z∈rows,ω z*
            (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
             ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2) := by
  obtain ⟨C,hC,hbound⟩ := active_raw_to_retained_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hX hY hcov₁ hcov₂ rows ω hω
  dsimp only
  simp_rw [height_source_row]
  simp_rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    η fixedBadMask 1 _ t (dvd_mul_right _ _) (dvd_mul_left _ _)
    slots S₁ S₂ R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hcov₁ hcov₂]
  have hb₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hb₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  obtain ⟨hx,hy⟩ := pullback_same_product X₁ X₂ Y₁ Y₂ T B₁ B₂ hX hY
  exact hbound η (fixedBadMask*idealGenerator R) 1 t slots hp
    (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) M P hM hP hcoeff L hL
    W₁ W₂ b₁ b₂ _ _ _ _ _ hs₁ hs₂
    (div_pos hX₁ hb₁) (div_pos hX₂ hb₂) (div_pos hY₁ hb₁) (div_pos hY₂ hb₂)
    hx hy rows ω hω

end SevenEighths.CenteredMomentActiveSourceRetained

end

end OAI

end Source807

/- Original source: OAI/NumberTheory/DirichletL/Moments/ActiveSmoothedSource.lean; sha256: 152c934dc7ad106cd76e46faa3a1dfe63d2c2b3c970d9f122b2e317d025fbbb1 -/
section Source808
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentActiveSmoothedSource
open CenteredMomentActiveAllocation HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentPositiveSummability
open CenteredMomentActiveSourceRetained
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_to_active_smoothed (N : ℕ) (hslots : Fintype.card ι≤N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
      ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i,0≤M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤M i) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
      ∀(keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ),0<K →
      (∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      let coeff := fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      C*(Ideal.absNorm L:ℝ)^ε*
        ∑ a ∈ activeAllocations η (fixedBadMask*idealGenerator R) 1 t slots coeff L W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂) (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
          ∑' z:O,(if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)*
            (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
             ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2) := by
  obtain ⟨C,hC,hbound⟩:=source_plain_to_active_retained (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  dsimp only
  let Q:=finiteColumns (tuplePool slots S₁ S₂)
  let β:=finiteColumnCoefficient (tuplePool slots S₁ S₂)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
  let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
  let coeff:=fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
  let ω:=fun z:O=>if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hω (z:O):0≤ω z:=by dsimp only [ω];split_ifs;exact hΦ z;exact le_rfl
  have hbn (B:Ideal O) (hB:B≠0):(0:ℝ)<Ideal.absNorm B:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hraw:0<raw:=div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have htotal:0<raw*∏i,P i:=mul_pos hraw (Finset.prod_pos (fun i _=>hP i))
  change sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤_
  unfold sourceRestrictedEnergy restrictedEnergy
  rw [←tsum_div_const]
  have he (z:O):
      (if keep z then ‖rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)/(raw*∏i,P i)=
      ω z*‖(Real.sqrt (raw*∏i,P i):ℂ)⁻¹*rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2 := by
    rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ htotal]
    dsimp only [ω]
    split_ifs <;> ring
  simp_rw [he]
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (hω z) (sq_nonneg _))
  intro rows
  have hh:=hbound η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂
    rows ω (fun z _=>hω z)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  have hf:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hP i))
  have hfac:0≤(2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P:=by
    apply div_nonneg _ hf.le
    exact mul_nonneg (by positivity) (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left ?_ hfac
  have hX:=allocated_positive_summable η (fixedBadMask*idealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hX₁ (hbn B₁ hB₁)) (div_pos hX₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hY:=allocated_positive_summable η (fixedBadMask*idealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hY₁ (hbn B₁ hB₁)) (div_pos hY₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hs:Summable (fun z:O=>ω z*
    (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
     ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)):=by
    convert hX.add hY using 1
    funext z
    dsimp only [ω]
    split_ifs <;> ring
  exact sum_le_hasSum rows (fun z _=>mul_nonneg (hω z) (add_nonneg (sq_nonneg _) (sq_nonneg _))) hs.hasSum
end SevenEighths.CenteredMomentActiveSmoothedSource

end

end OAI

end Source808

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceRetainedEnergy.lean; sha256: 0d5131c8cf804a842383ba9e1b7af6e052a458bfcc4466689b490d7e8f0a8f80 -/
section Source809
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceRetainedEnergy
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_to_retained (N : ℕ) (hslots : Fintype.card ι≤N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
      ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i,0≤M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤M i) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
      ∀ (rows : Finset O) (ω : O→ℝ),(∀ z∈rows,0≤ω z) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      let coeff := fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
      (∑ z∈rows,ω z*‖(Real.sqrt (raw*∏ i,P i):ℂ)⁻¹*
        rowPolynomial Finset.univ (sourceGenerator Q)
          (fun I : supportedColumns Q=>β I*heightCoeff η t I) z‖^2)≤
      C*(Ideal.absNorm L:ℝ)^ε*
        ∑ a : Allocation L (Finset.univ : Finset (ι⊕Fin 2)),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
          ∑ z∈rows,ω z*
            (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
             ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2) := by
  obtain ⟨C,hC,hbound⟩ := masked_raw_to_retained_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hX hY hcov₁ hcov₂ rows ω hω
  dsimp only
  simp_rw [height_source_row]
  simp_rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    η fixedBadMask 1 _ t (dvd_mul_right _ _) (dvd_mul_left _ _)
    slots S₁ S₂ R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hcov₁ hcov₂]
  have hb₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hb₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  obtain ⟨hx,hy⟩ := pullback_same_product X₁ X₂ Y₁ Y₂ T B₁ B₂ hX hY
  exact hbound η (fixedBadMask*idealGenerator R) 1 t slots hp
    (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) M P hM hP hcoeff L hL
    W₁ W₂ b₁ b₂ _ _ _ _ _ hs₁ hs₂
    (div_pos hX₁ hb₁) (div_pos hX₂ hb₂) (div_pos hY₁ hb₁) (div_pos hY₂ hb₂)
    hx hy rows ω hω

end SevenEighths.CenteredMomentSourceRetainedEnergy

end

end OAI

end Source809

/- Original source: OAI/NumberTheory/DirichletL/Moments/SmoothedRetainedSource.lean; sha256: 8149aee09790360c053fd4446c88213eb6036fb5d62fac2cb50af09efb83d32b -/
section Source810
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSmoothedRetainedSource
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentPositiveSummability
open CenteredMomentSourceRetainedEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_to_smoothed_retained (N : ℕ) (hslots : Fintype.card ι≤N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
      ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i,0≤M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤M i) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
      ∀(keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ),0<K →
      (∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      let coeff := fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      C*(Ideal.absNorm L:ℝ)^ε*
        ∑ a : Allocation L (Finset.univ : Finset (ι⊕Fin 2)),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
          ∑' z:O,(if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)*
            (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
             ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2) := by
  obtain ⟨C,hC,hbound⟩:=source_plain_to_retained (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  dsimp only
  let Q:=finiteColumns (tuplePool slots S₁ S₂)
  let β:=finiteColumnCoefficient (tuplePool slots S₁ S₂)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
  let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
  let coeff:=fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
  let ω:=fun z:O=>if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hω (z:O):0≤ω z:=by dsimp only [ω];split_ifs;exact hΦ z;exact le_rfl
  have hbn (B:Ideal O) (hB:B≠0):(0:ℝ)<Ideal.absNorm B:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hraw:0<raw:=div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have htotal:0<raw*∏i,P i:=mul_pos hraw (Finset.prod_pos (fun i _=>hP i))
  change sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤_
  unfold sourceRestrictedEnergy restrictedEnergy
  rw [←tsum_div_const]
  have he (z:O):
      (if keep z then ‖rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)/(raw*∏i,P i)=
      ω z*‖(Real.sqrt (raw*∏i,P i):ℂ)⁻¹*rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2 := by
    rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ htotal]
    dsimp only [ω]
    split_ifs <;> ring
  simp_rw [he]
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (hω z) (sq_nonneg _))
  intro rows
  have hh:=hbound η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂
    rows ω (fun z _=>hω z)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  have hf:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hP i))
  have hfac:0≤(2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P:=by
    apply div_nonneg _ hf.le
    exact mul_nonneg (by positivity) (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left ?_ hfac
  have hX:=allocated_positive_summable η (fixedBadMask*idealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hX₁ (hbn B₁ hB₁)) (div_pos hX₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hY:=allocated_positive_summable η (fixedBadMask*idealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hY₁ (hbn B₁ hB₁)) (div_pos hY₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hs:Summable (fun z:O=>ω z*
    (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
     ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)):=by
    convert hX.add hY using 1
    funext z
    dsimp only [ω]
    split_ifs <;> ring
  exact sum_le_hasSum rows (fun z _=>mul_nonneg (hω z) (add_nonneg (sq_nonneg _) (sq_nonneg _))) hs.hasSum
end SevenEighths.CenteredMomentSmoothedRetainedSource

end

end OAI

end Source810

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSourceMask.lean; sha256: 43bb4c2c8310dab139b58754cfe6796173e6f6639b8a857de9ba2673e7a4997c -/
section Source811
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSourceMask
open CanonicalQuadraticSieve CenteredMomentSecondSectorColumns CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask
open CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

theorem divisor_dvd_common (C D a b s : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b)
    (hsI : s∣C*a) (hsJ : s∣D*b) : s∣C ∧ s∣D := by
  have hDa := (coprime_of_same_support C D a hC hD ha hCD).mp hCa
  have hDb := (coprime_of_same_support C D b hC hD hb hCD).mp hCb
  have hsa : IsCoprime s a := ((hDa.symm.mul_right hab).of_isCoprime_of_dvd_right hsJ).symm
  have hsb : IsCoprime s b := ((hCb.symm.mul_right hab.symm).of_isCoprime_of_dvd_right hsI).symm
  exact ⟨hsa.dvd_mul_right_iff.mp hsI,hsb.dvd_mul_right_iff.mp hsJ⟩

variable {ι : Type*} [Fintype ι]

theorem column_nonzero_divisor (S : Finset (Tuple ι)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I : Ideal O)
    (h : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) : s∣I := by
  rw [column_mask] at h
  by_contra hn
  exact h (by rw [ite_eq_right hn,mul_zero])

theorem source_pair_divisor_common (S : Finset (Tuple ι)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b)
    (hleft : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*a)≠0)
    (hright : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (D*b)≠0) : s∣C ∧ s∣D :=
  divisor_dvd_common C D a b s hC hD ha hb hCD hCa hCb hab
    (column_nonzero_divisor S R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s _ hleft)
    (column_nonzero_divisor S R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s _ hright)

end SevenEighths.CenteredMomentSecondSourceMask

end

end OAI

end Source811

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondLiveEnergy.lean; sha256: e2544280b28d244034cb79abf39e7dccadcccc1c8c5f7a654f9ef25b0ea7512a -/
section Source812
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRestrictedSource
open CenteredMomentRestrictedEnergy CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass
open CenteredMomentSourceMass CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentFirstSectors RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem live_divisor_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R L : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB) (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
      (fun I => (if L∣I then 1 else 0)*f I) W K=
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB) (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K := by
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  rw [maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  ring

theorem actual_second_child_live_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*CanonicalRowCompletion.idealRowHom A I*
        rayCharacter χ (CompletedGauss.primaryGenerator I))
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ L : Ideal O) (t : ℝ)
    (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    let Q := finiteColumns (Fintype.piFinset S)
    let β := finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 Q)
      (divisorCoefficient L (sectorElement C hC.1 Q)
        (movingCoefficient A (sectorElement C hC.1 Q)
          (fun J : sectorPool C hC.1 Q => β (C*J)*heightCoeff η t J)) χ) W K≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff τ t) W K := by
  dsimp only
  rw [sector_child_energy η τ χ A hτ (finiteColumns (Fintype.piFinset S))
    (finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) C hC L t keep W K]
  have he := original_restricted_child_energy S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
    (fun I => (if L∣I then 1 else 0)*heightCoeff τ t I) keep W K hK hW
  simp_rw [live_divisor_energy] at he
  refine le_trans ?_ he
  apply le_of_eq
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs <;> simp_all

end SevenEighths.CenteredMomentSecondLiveEnergy

end

end OAI

end Source812

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonRawCost.lean; sha256: 65b5e4b8485badb4e4885eeff03b84fa94c8fe69713359d6e09acd1d0e01fa57 -/
section Source813
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonRawCost
open CenteredMomentCommonRawScale CenteredMomentAllocationCost CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem frozen_normalized_cost (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : C≠0)
    (hprod : finiteTupleProduct B=C) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P M : ι → ℝ) (hP : ∀ i,0<P i)
    (hν : ∀ i I,‖ν i I‖≤1) (hWnorm : ∀ i x,‖Wslot i x‖≤M i) (hM : ∀ i,1≤M i)
    (a b : ℝ) (ha : 0<a) (hW : ∀ i,Function.support (Wslot i)⊆Set.Icc a b) :
    ‖frozenCoefficient B C R ν Wslot P‖^2/rawReduction B P≤
      ((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ) := by
  have hN : (0:ℝ)<Ideal.absNorm C := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hR := rawReduction_pos B hB P hP
  by_cases hz : frozenCoefficient B C R ν Wslot P=0
  · rw [hz,norm_zero,zero_pow (by decide : 2≠0),zero_div]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)) hN.le
  · have hm := frozenCoefficient_norm B C R ν Wslot P M hν hWnorm hM
    have hh := (actual_reduction_norm B hB C R hprod ν Wslot P hP a b ha hW hz).2
    have hi : (1:ℝ)/rawReduction B P≤(max 1 b)^Fintype.card ι/(Ideal.absNorm C:ℝ) := by
      apply (div_le_div_iff₀ hR hN).mpr
      simpa only [one_mul] using hh
    calc
      _ ≤ (∏ i,M i)^2/rawReduction B P :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hm _) hR.le
      _ = (∏ i,M i)^2*(1/rawReduction B P) := by ring
      _ ≤ (∏ i,M i)^2*((max 1 b)^Fintype.card ι/(Ideal.absNorm C:ℝ)) :=
        mul_le_mul_of_nonneg_left hi (sq_nonneg _)
      _ = _ := by ring

end SevenEighths.CenteredMomentCommonRawCost

end

end OAI

end Source813

/- Original source: OAI/NumberTheory/DirichletL/Moments/RestrictedSourceNormalization.lean; sha256: 99244d1662cc762800d8e55d73aa537eb47a18a4c6b34102cd6c2ce6aeb69c68 -/
section Source814
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedSourceNormalization
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentRestrictedSource
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost CenteredMomentRestrictedEnergy
local notation "O" => ActualEisensteinCubic.O

theorem sourceRestrictedEnergy_nonneg (keep : O → Prop) (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (_hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤sourceRestrictedEnergy keep Q c f W K := by
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_nonneg
  intro z
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (hW z)
  · exact le_rfl

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem normalized_restricted_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (Traw : ℝ) (hTraw : 0<Traw) (hP : ∀ i,0<P i)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K)/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        (‖frozenCoefficient B C R ν Wslot P‖^2/rawReduction B P)*
          ((sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K)/remainingRaw B Traw P) := by
  have h := original_restricted_child_energy S hS hp C R s hC hsC ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ f keep W K hK hW
  have htotal : 0<Traw*∏ i,P i := mul_pos hTraw (Finset.prod_pos (fun i _ => hP i))
  apply (div_le_div_of_nonneg_right h htotal.le).trans_eq
  rw [mul_div_assoc,Finset.sum_div]
  apply congrArg (fun x : ℝ => ((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  have hb := (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
  have hr := raw_scale_identity B hb Traw P
  have hpR := rawReduction_pos B hb P hP
  have hpL : 0<remainingRaw B Traw P := by
    apply (mul_pos_iff_of_pos_right hpR).mp
    exact hr.symm ▸ htotal
  have alg (d e n r l : ℝ) (hr : 0<r) (hl : 0<l) (hn : l*r=n) :
      d*e/n=(d/r)*(e/l) := by
    rw [←hn]
    field_simp [hr.ne',hl.ne']
  exact alg _ _ _ _ _ hpR hpL hr

theorem restricted_child_common_saving (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (Traw : ℝ) (hTraw : 0<Traw) (hP : ∀ i,0<P i)
    (M : ι → ℝ) (hν : ∀ i I,‖ν i I‖≤1) (hWnorm : ∀ i x,‖Wslot i x‖≤M i)
    (hM : ∀ i,1≤M i) (a b : ℝ) (ha : 0<a)
    (hslot : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K)/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*
        (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          ∑ B : actualAllocations S C, ((sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K)/remainingRaw B Traw P) := by
  have h := normalized_restricted_child_energy S hS hp C R s hC hsC ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ Traw hTraw hP f keep W K hK hW
  apply h.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B hB
  have hb := (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
  have hprod : finiteTupleProduct (B : Tuple ι)=C := (Finset.mem_filter.mp B.property).2
  have hc := frozen_normalized_cost (ι:=ι) (B : Tuple ι) hb C R hC.1 hprod ν Wslot P M hP hν hWnorm hM a b ha hslot
  apply mul_le_mul_of_nonneg_right hc
  have hr := raw_scale_identity B hb Traw P
  have hpR := rawReduction_pos B hb P hP
  have htotal : 0<Traw*∏ i,P i := mul_pos hTraw (Finset.prod_pos (fun i _ => hP i))
  have hpL : 0<remainingRaw B Traw P := (mul_pos_iff_of_pos_right hpR).mp (hr.symm ▸ htotal)
  exact div_nonneg (sourceRestrictedEnergy_nonneg keep _ _ f W K hK hW) hpL.le

end SevenEighths.CenteredMomentRestrictedSourceNormalization

end

end OAI

end Source814

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSourceCost.lean; sha256: 7180ffb8a5817dfdf16cecbbaec29e087b75a6c78f99b40a985ad5e7ed6f9d9c -/
section Source815
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceCost
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRestrictedSource
open CenteredMomentRestrictedEnergy CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass
open CenteredMomentSourceMass CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentSecondLiveEnergy CenteredMomentRestrictedSourceNormalization
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem source_divisor_common_saving (τ : Character)
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ L : Ideal O) (t : ℝ)
    (Traw : ℝ) (hTraw : 0<Traw) (hP : ∀ i,0<P i)
    (M : ι → ℝ) (hν : ∀ i I,‖ν i I‖≤1) (hWnorm : ∀ i x,‖Wslot i x‖≤M i)
    (hM : ∀ i,1≤M i) (a b : ℝ) (ha : 0<a)
    (hslot : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    let Q := finiteColumns (Fintype.piFinset S)
    let β := finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
    sourceRestrictedEnergy keep (residualPool C hC.1 Q)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ t) W K/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*
        (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          ∑ B : actualAllocations S C, (sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff τ t) W K)/CenteredMomentCommonRawScale.remainingRaw B Traw P := by
  dsimp only
  have he := restricted_child_common_saving S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ Traw hTraw hP M hν hWnorm hM a b ha hslot
    (fun I => (if L∣I then 1 else 0)*heightCoeff τ t I) keep W K hK hW
  simp_rw [live_divisor_energy] at he
  refine le_trans ?_ he
  apply le_of_eq
  congr 1
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs <;> simp_all

end SevenEighths.CenteredMomentSecondSourceCost

end

end OAI

end Source815

/- Original source: OAI/NumberTheory/DirichletL/Moments/CanonicalRetainedSource.lean; sha256: 51ec41ed3471e8e26e3c238fc0e5e6f7f8195b3e35883092055eda2ffa41f038 -/
section Source816
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCanonicalRetainedSource
open CanonicalQuadraticSieve CenteredMomentFirstSectors
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentCommonRawScale CenteredMomentRestrictedSourceNormalization
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveChildren (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑ a : Allocation L (Finset.univ : Finset (ι⊕Fin 2)),
    ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
      ∑' z:O,(if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)*
        (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
         ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)

theorem positiveChildren_nonneg (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (hP : ∀ i,0<P i) (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg
  · apply div_nonneg
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact (mul_pos (selectedNorm_pos L a) (Finset.prod_pos (fun i _=>hP i))).le
  · apply tsum_nonneg
    intro z
    apply mul_nonneg
    · split_ifs;exact hΦ z;exact le_rfl
    · exact add_nonneg (sq_nonneg _) (sq_nonneg _)

def SmoothedBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
    ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
    ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i,0≤M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤M i) →
    ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
    ∀(keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ),0<K →
      (∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      D*(Ideal.absNorm L:ℝ)^ε*
        positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_smoothed_bound (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ J:Finset ι,SmoothedBound J D ε := by
  have hex (J:Finset ι) : ∃ D:ℝ,0<D ∧ SmoothedBound J D ε := by
    simpa only [SmoothedBound,positiveChildren] using
      CenteredMomentSmoothedRetainedSource.source_plain_to_smoothed_retained
        (ι:=J) (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose D hD hbound using hex
  let C:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hC:0<C:=by dsimp [C];linarith
  have hDC (J:Finset ι):D J≤C:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  have hh:=hbound J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hDC J) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (positiveChildren_nonneg η t slots R L ν Wslot P M hP W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K hΦ))

omit [DecidableEq ι] in

theorem live_residual_pool (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ j,B j≠0) (i : liveIndices B) :
    residualPool (B (Sum.inl i.val)) (hB _) (S (Sum.inl i.val))=S (Sum.inl i.val) := by
  ext I
  rw [mem_residualPool,(Finset.mem_filter.mp i.property).2,one_mul]

omit [DecidableEq ι] in
theorem liveBox_original_pools (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ j,B j≠0) :
    liveBox S B hB=tuplePool (fun i:liveIndices B=>S (Sum.inl i.val))
      (residualPool (B (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
      (residualPool (B (Sum.inr 1)) (hB _) (S (Sum.inr 1))) := by
  rw [liveBox_eq_tuplePool]
  simp_rw [live_residual_pool]

def commonPositiveChildren (τ : Character) (t : ℝ)
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι) (C R L : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  positiveChildren τ t (fun i:liveIndices B=>S (Sum.inl i.val)) (R*C) L
    (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val) (fun i=>M i.val)
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) keep Φ K

local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤M i) → (∀ i,1≤M i) →
      ∀ (a b : ℝ),0<a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  obtain ⟨D,hD,hbound⟩:=uniform_smoothed_bound (ι:=ι) ε hε
  refine ⟨D,hD,?_⟩
  intro τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  dsimp only
  have hbn (I:Ideal O) (hI:I≠0):(0:ℝ)<Ideal.absNorm I:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hraw:0<T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂):=
    div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have hcommon:=CenteredMomentSecondSourceCost.source_divisor_common_saving τ S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L t _ hraw hP M hν hWnorm hM a b ha hslot keep Φ K hK hΦ
  dsimp only at hcommon
  refine hcommon.trans ?_
  let pref:ℝ:=((actualAllocations S C).card:ℝ)*
    (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))
  have hpref:0≤pref:=by dsimp [pref];positivity
  change pref*_≤pref*D*(Ideal.absNorm L:ℝ)^ε*_
  calc
    _ ≤ pref*∑ B:actualAllocations S C,
      D*(Ideal.absNorm L:ℝ)^ε*commonPositiveChildren τ t S B C R L ν Wslot P M
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
      apply mul_le_mul_of_nonneg_left ?_ hpref
      apply Finset.sum_le_sum
      intro B _
      have hB:= (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
      have hcoeff (i:liveIndices (B:Tuple ι)) (I:Ideal O) :
          ‖ν i.val I*Wslot i.val ((Ideal.absNorm I:ℝ)/P i.val)‖≤M i.val := by
        rw [norm_mul]
        calc
          _ ≤ 1*M i.val := mul_le_mul (hν _ _) (hWnorm _ _) (norm_nonneg _) (by norm_num)
          _ = _ := one_mul _
      have hh:=hbound (liveIndices (B:Tuple ι)) τ t
        (fun i:liveIndices (B:Tuple ι)=>S (Sum.inl i.val))
        (fun i I hI=>hp i.val I hI)
        (residualPool (B.val (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
        (residualPool (B.val (Sum.inr 1)) (hB _) (S (Sum.inr 1)))
        (R*C) L hL (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val) (fun i=>M i.val)
        (fun i=>hP i.val) (fun i=>(hM i.val).trans' zero_le_one) (fun i I _=>hcoeff i I)
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1))
        (mul_ne_zero hB₁ (hB _)) (mul_ne_zero hB₂ (hB _)) hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT
        (plainCoverage_residualPool _ W₁ B₁ _ (hB _) X₁ Y₁ hcov₁)
        (plainCoverage_residualPool _ W₂ B₂ _ (hB _) X₂ Y₂ hcov₂) keep Φ K hK hΦ
      dsimp only at hh
      rw [remainingRaw_source B hB B₁ B₂ hB₁ hB₂ T P,liveBox_original_pools]
      exact hh
    _ = _ := by rw [←Finset.mul_sum];ring

def CanonicalBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤M i) → (∀ i,1≤M i) →
      ∀ (a b : ℝ),0<a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ J:Finset ι,CanonicalBound J D ε := by
  have hex (J:Finset ι):∃ D:ℝ,0<D ∧ CanonicalBound J D ε:=by
    simpa only [CanonicalBound] using canonical_source_to_positive (ι:=J) ε hε
  choose D hD hbound using hex
  let E:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hE:0<E:=by dsimp [E];linarith
  have hDE (J:Finset ι):D J≤E:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [E];linarith
  refine ⟨E,hE,?_⟩
  intro J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  have hh:=hbound J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  refine hh.trans ?_
  have hsum:0≤∑ B:actualAllocations S C,
      commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
        b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K:=by
    apply Finset.sum_nonneg
    intro B _
    exact positiveChildren_nonneg (ι:=liveIndices (B.val : Tuple J)) τ t
      (fun i=>S (Sum.inl i.val)) (R*C) L (fun i=>ν i.val) (fun i=>Wslot i.val)
      (fun i=>P i.val) (fun i=>M i.val) (fun i=>hP i.val)
      W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1)) keep Φ K hΦ
  apply mul_le_mul_of_nonneg_right ?_ hsum
  apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  apply mul_le_mul_of_nonneg_left (hDE J)
  positivity

end SevenEighths.CenteredMomentCanonicalRetainedSource

end

end OAI

end Source816

/- Original source: OAI/NumberTheory/DirichletL/Moments/ActiveCanonicalSource.lean; sha256: 62b5feef525e49582220765c16c9d2faaeb2097fcf992dc4c9321b2359d95c81 -/
section Source817
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentActiveCanonicalSource
open CenteredMomentActiveAllocation
open CanonicalQuadraticSieve CenteredMomentFirstSectors
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentCommonRawScale CenteredMomentRestrictedSourceNormalization
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveChildren (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑ a ∈ activeAllocations η (fixedBadMask*idealGenerator R) 1 t slots
    (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
    (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂) (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂),
    ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
      ∑' z:O,(if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)*
        (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
         ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)

theorem positiveChildren_nonneg (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (hP : ∀ i,0<P i) (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg
  · apply div_nonneg
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact (mul_pos (selectedNorm_pos L a) (Finset.prod_pos (fun i _=>hP i))).le
  · apply tsum_nonneg
    intro z
    apply mul_nonneg
    · split_ifs;exact hΦ z;exact le_rfl
    · exact add_nonneg (sq_nonneg _) (sq_nonneg _)

def SmoothedBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
    ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
    ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i,0≤M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤M i) →
    ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
    ∀(keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ),0<K →
      (∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      D*(Ideal.absNorm L:ℝ)^ε*
        positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_smoothed_bound (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ J:Finset ι,SmoothedBound J D ε := by
  have hex (J:Finset ι) : ∃ D:ℝ,0<D ∧ SmoothedBound J D ε := by
    simpa only [SmoothedBound,positiveChildren] using
      CenteredMomentActiveSmoothedSource.source_plain_to_active_smoothed
        (ι:=J) (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose D hD hbound using hex
  let C:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hC:0<C:=by dsimp [C];linarith
  have hDC (J:Finset ι):D J≤C:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  have hh:=hbound J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hDC J) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (positiveChildren_nonneg η t slots R L ν Wslot P M hP W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K hΦ))

omit [DecidableEq ι] in

def commonPositiveChildren (τ : Character) (t : ℝ)
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι) (C R L : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  positiveChildren τ t (fun i:liveIndices B=>S (Sum.inl i.val)) (R*C) L
    (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val) (fun i=>M i.val)
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) keep Φ K

local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤M i) → (∀ i,1≤M i) →
      ∀ (a b : ℝ),0<a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  obtain ⟨D,hD,hbound⟩:=uniform_smoothed_bound (ι:=ι) ε hε
  refine ⟨D,hD,?_⟩
  intro τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  dsimp only
  have hbn (I:Ideal O) (hI:I≠0):(0:ℝ)<Ideal.absNorm I:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hraw:0<T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂):=
    div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have hcommon:=CenteredMomentSecondSourceCost.source_divisor_common_saving τ S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L t _ hraw hP M hν hWnorm hM a b ha hslot keep Φ K hK hΦ
  dsimp only at hcommon
  refine hcommon.trans ?_
  let pref:ℝ:=((actualAllocations S C).card:ℝ)*
    (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))
  have hpref:0≤pref:=by dsimp [pref];positivity
  change pref*_≤pref*D*(Ideal.absNorm L:ℝ)^ε*_
  calc
    _ ≤ pref*∑ B:actualAllocations S C,
      D*(Ideal.absNorm L:ℝ)^ε*commonPositiveChildren τ t S B C R L ν Wslot P M
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
      apply mul_le_mul_of_nonneg_left ?_ hpref
      apply Finset.sum_le_sum
      intro B _
      have hB:= (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
      have hcoeff (i:liveIndices (B:Tuple ι)) (I:Ideal O) :
          ‖ν i.val I*Wslot i.val ((Ideal.absNorm I:ℝ)/P i.val)‖≤M i.val := by
        rw [norm_mul]
        calc
          _ ≤ 1*M i.val := mul_le_mul (hν _ _) (hWnorm _ _) (norm_nonneg _) (by norm_num)
          _ = _ := one_mul _
      have hh:=hbound (liveIndices (B:Tuple ι)) τ t
        (fun i:liveIndices (B:Tuple ι)=>S (Sum.inl i.val))
        (fun i I hI=>hp i.val I hI)
        (residualPool (B.val (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
        (residualPool (B.val (Sum.inr 1)) (hB _) (S (Sum.inr 1)))
        (R*C) L hL (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val) (fun i=>M i.val)
        (fun i=>hP i.val) (fun i=>(hM i.val).trans' zero_le_one) (fun i I _=>hcoeff i I)
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1))
        (mul_ne_zero hB₁ (hB _)) (mul_ne_zero hB₂ (hB _)) hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT
        (plainCoverage_residualPool _ W₁ B₁ _ (hB _) X₁ Y₁ hcov₁)
        (plainCoverage_residualPool _ W₂ B₂ _ (hB _) X₂ Y₂ hcov₂) keep Φ K hK hΦ
      dsimp only at hh
      rw [remainingRaw_source B hB B₁ B₂ hB₁ hB₂ T P,CenteredMomentCanonicalRetainedSource.liveBox_original_pools]
      exact hh
    _ = _ := by rw [←Finset.mul_sum];ring

def CanonicalBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤M i) → (∀ i,1≤M i) →
      ∀ (a b : ℝ),0<a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ J:Finset ι,CanonicalBound J D ε := by
  have hex (J:Finset ι):∃ D:ℝ,0<D ∧ CanonicalBound J D ε:=by
    simpa only [CanonicalBound] using canonical_source_to_positive (ι:=J) ε hε
  choose D hD hbound using hex
  let E:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hE:0<E:=by dsimp [E];linarith
  have hDE (J:Finset ι):D J≤E:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [E];linarith
  refine ⟨E,hE,?_⟩
  intro J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  have hh:=hbound J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  refine hh.trans ?_
  have hsum:0≤∑ B:actualAllocations S C,
      commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
        b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K:=by
    apply Finset.sum_nonneg
    intro B _
    exact positiveChildren_nonneg (ι:=liveIndices (B.val : Tuple J)) τ t
      (fun i=>S (Sum.inl i.val)) (R*C) L (fun i=>ν i.val) (fun i=>Wslot i.val)
      (fun i=>P i.val) (fun i=>M i.val) (fun i=>hP i.val)
      W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1)) keep Φ K hΦ
  apply mul_le_mul_of_nonneg_right ?_ hsum
  apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  apply mul_le_mul_of_nonneg_left (hDE J)
  positivity

end SevenEighths.CenteredMomentActiveCanonicalSource

end

end OAI

end Source817

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonRadialData.lean; sha256: 13afe68386129a4505e177ef3391ecdf576955c635419e3a5e5c7e0482e0be76 -/
section Source818
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonRadialData
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale
open CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

structure Input (ι:Type*) [Fintype ι] extends Data ι where
  plain₁ : Finset (Ideal O)
  plain₂ : Finset (Ideal O)
  plain₁_ne : ∀I∈plain₁,I≠0
  plain₂_ne : ∀I∈plain₂,I≠0
  coverage₁ : PlainCoverage plain₁ W₁ 1 X₁ Y₁
  coverage₂ : PlainCoverage plain₂ W₂ 1 X₂ Y₂
  ν_bound : ∀i I,‖ν i I‖≤1
  W_bound : ∀i x,‖W i x‖≤M i
  lower : ℝ
  upper : ℝ
  lower_pos : 0<lower
  lower_le : ∀i,lower≤lo i
  upper_ge : ∀i,hi i≤upper

 def Input.pools (s:Input ι) : (ι⊕Fin 2)→Finset (Ideal O) :=
  Sum.elim s.slots (fun j=>if j=0 then s.plain₁ else s.plain₂)

omit [DecidableEq ι] in
lemma Input.pools_ne (s:Input ι) (j:ι⊕Fin 2) : ∀I∈s.pools j,I≠0 := by
  cases j with
  | inl i => exact fun I hI=>(s.prime i I hI).ne_zero
  | inr j =>
    fin_cases j
    · simpa [Input.pools] using s.plain₁_ne
    · simpa [Input.pools] using s.plain₂_ne

omit [DecidableEq ι] in
lemma Input.slot_support (s:Input ι) (i:ι) : Function.support (s.W i)⊆Set.Icc s.lower s.upper :=
  fun _x hx=>⟨(s.lower_le i).trans (s.support i hx).1,((s.support i hx).2).trans (s.upper_ge i)⟩

omit [DecidableEq ι] in
lemma alloc_ne (s:Input ι) (C:Ideal O) (B:actualAllocations s.pools C)
    (j:ι⊕Fin 2) : B.val j≠0 :=
  (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1 j

omit [DecidableEq ι] in
lemma alloc_norm_pos (s:Input ι) (C:Ideal O) (B:actualAllocations s.pools C)
    (j:ι⊕Fin 2) : (0:ℝ)<Ideal.absNorm (B.val j) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B j))

 def commonData (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C) : Data (liveIndices B.val) where
  η:=s.η
  m:=fixedBadMask*idealGenerator (R*C)
  A:=1
  t:=s.t
  slots:=fun i=>s.slots i.val
  prime:=fun i I hI=>s.prime i.val I hI
  ν:=fun i=>s.ν i.val
  W:=fun i=>s.W i.val
  lo:=fun i=>s.lo i.val
  hi:=fun i=>s.hi i.val
  P:=fun i=>s.P i.val
  lo_pos:=fun i=>s.lo_pos i.val
  P_pos:=fun i=>s.P_pos i.val
  support:=fun i=>s.support i.val
  W₁:=s.W₁
  W₂:=s.W₂
  X₁:=s.X₁/Ideal.absNorm (B.val (Sum.inr 0))
  X₂:=s.X₂/Ideal.absNorm (B.val (Sum.inr 1))
  Y₁:=s.Y₁/Ideal.absNorm (B.val (Sum.inr 0))
  Y₂:=s.Y₂/Ideal.absNorm (B.val (Sum.inr 1))
  M:=fun i=>s.M i.val
  M_ge_one:=fun i=>s.M_ge_one i.val
  coefficient_bound:=fun i I hI=>s.coefficient_bound i.val I hI
  b₁:=s.b₁
  b₂:=s.b₂
  support₁:=s.support₁
  support₂:=s.support₂
  X₁_pos:=div_pos s.X₁_pos (alloc_norm_pos s C B _)
  X₂_pos:=div_pos s.X₂_pos (alloc_norm_pos s C B _)
  Y₁_pos:=div_pos s.Y₁_pos (alloc_norm_pos s C B _)
  Y₂_pos:=div_pos s.Y₂_pos (alloc_norm_pos s C B _)
  same_product:=by rw [div_mul_div_comm,div_mul_div_comm,s.same_product]
  rows:=∅
  weight:=fun _=>0
  weight_nonneg:=by simp

omit [DecidableEq ι] in
lemma common_profile_le (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C) :
    (commonData s C R B).profileFactor≤s.toData.profileFactor := by
  unfold Data.profileFactor
  change (2*(max 1 s.b₁*max 1 s.b₂))*(∏i:liveIndices B.val,s.M i.val)^2≤_
  rw [Finset.prod_coe_sort]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)

end SevenEighths.CenteredMomentCommonRadialData

end

end OAI

end Source818

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonLinearSource.lean; sha256: 0c9e65f319dad87a5fc9afc3aab699774e834aae8f810dca371fbbd3292a63ea -/
section Source819
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLinearSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentOriginalChildEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedDomain
open CenteredMomentAmplificationLiveMask CenteredMomentExceptionalMaskedSource
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def sourceColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))
  let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then β (C*I) else 0)*heightCoeff s.η s.t I) z

def liveColumn (s:Input ι)(C R L:Ideal O)(B:actualAllocations s.pools C)(z:O):ℂ:=
  let S:=liveBox s.pools B.val (alloc_ne s C B)
  rowPolynomial Finset.univ (sourceGenerator (finiteColumns S))
    (fun I:supportedColumns (finiteColumns S)=>finiteColumnCoefficient S
      (maskedLiveProfile B.val C R L s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I*
        heightCoeff s.η s.t I) z

omit [DecidableEq ι] in
theorem source_column_allocation (s:Input ι)(C:Ideal O)(hC:Supported C)
    (R seed L:Ideal O)(hseed:seed∣C)(z:O):
    sourceColumn s C hC R seed L z=
      ∑B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P*
        liveColumn s C R L B z:=by
  let Q:=residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))
  let b:=fun B:actualAllocations s.pools C=>frozenCoefficient B.val C R s.ν s.W s.P
  let d:=fun (B:actualAllocations s.pools C)(I:supportedColumns Q)=>
    finiteColumnCoefficient (liveBox s.pools B.val (alloc_ne s C B))
      (liveProfile B.val C R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I*
      ((if L∣(I:Ideal O) then 1 else 0)*heightCoeff s.η s.t I)
  have he (I:supportedColumns Q):
      (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then
        finiteColumnCoefficient (Fintype.piFinset s.pools)
          (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I)
          else 0)*heightCoeff s.η s.t I=∑B,b B*d B I:=by
    have hc:=original_source_punctured_column s.pools s.pools_ne (fun i J hJ=>s.prime i J hJ)
      C R seed I hC.1 (Finset.mem_filter.mp I.property).2.1 hseed
      s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
    by_cases hl:L∣(I:Ideal O)
    · simp only [hl,and_true]
      rw [hc,Finset.sum_mul]
      simp only [b,d,hl,ite_true,one_mul,mul_assoc]
    · simp only [hl,and_false,ite_false,zero_mul,b,d,mul_zero,Finset.sum_const_zero]
  change rowPolynomial Finset.univ (sourceGenerator Q) _ z=_
  rw [funext he,rowPolynomial_allocation]
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun w:ℂ=>b B*w)
  have hh:=live_rowPolynomial s.pools s.pools_ne (fun i J hJ=>s.prime i J hJ)
    B.val (alloc_ne s C B) C R hC (Finset.mem_filter.mp B.property).1
    (Finset.mem_filter.mp B.property).2 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
    (fun I=>(if L∣I then 1 else 0)*heightCoeff s.η s.t I) z
  change rowPolynomial Finset.univ (sourceGenerator Q) (d B) z=_ at hh
  rw [hh]
  unfold liveColumn
  congr 1
  funext I
  rw [maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  ring

theorem live_column_rectangle (s:Input ι)(C R L:Ideal O)(B:actualAllocations s.pools C)(z:O):
    liveColumn s C R L B z=
      CenteredMomentDivisorRowEnergy.maskedRectangle
        (commonData s C R B).η (commonData s C R B).m (commonData s C R B).A z
        (commonData s C R B).t (commonData s C R B).slots (commonData s C R B).coefficient L
        (commonData s C R B).W₁ (commonData s C R B).W₂
        (commonData s C R B).X₁ (commonData s C R B).X₂
        (commonData s C R B).Y₁ (commonData s C R B).Y₂:=by
  unfold liveColumn
  rw [CenteredMomentCanonicalRetainedSource.liveBox_original_pools]
  have hc₁:=plainCoverage_residualPool (s.pools (Sum.inr 0)) s.W₁ 1 _
    (alloc_ne s C B (Sum.inr 0)) s.X₁ s.Y₁ s.coverage₁
  have hc₂:=plainCoverage_residualPool (s.pools (Sum.inr 1)) s.W₂ 1 _
    (alloc_ne s C B (Sum.inr 1)) s.X₂ s.Y₂ s.coverage₂
  simp only [one_mul] at hc₁ hc₂
  have he:=CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    s.η fixedBadMask 1 z s.t (dvd_mul_right _ _) (dvd_mul_left _ _)
    (commonData s C R B).slots
    (residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) (s.pools (Sum.inr 0)))
    (residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) (s.pools (Sum.inr 1)))
    (R*C) L (commonData s C R B).ν (commonData s C R B).W (commonData s C R B).P
    s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (B.val (Sum.inr 0)) (B.val (Sum.inr 1)) hc₁ hc₂
  rw [height_source_row]
  convert he using 1 <;> simp only [maskedLiveProfile,commonData,one_mul,Input.pools,Sum.elim_inl]
  all_goals rfl

end SevenEighths.CenteredMomentCommonLinearSource

end

end OAI

end Source819

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonLinearNormalization.lean; sha256: a5c6a0a75ce25269f36738583fba75278958e3153c3bdff3dbc1bf3cab805bda -/
section Source820
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLinearNormalization
open HeckeFamily CenteredMomentCommonLinearSource CenteredMomentCommonRadialData
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost CenteredMomentEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def commonScalar (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):ℂ:=
  (Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*frozenCoefficient B.val C R s.ν s.W s.P

omit [DecidableEq ι] in
theorem common_volume (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    volume (commonData s C R B)=remainingRaw B.val (s.X₁*s.X₂) s.P:=by
  dsimp only [volume,commonData,remainingRaw,plainNorm]
  ring

theorem source_normalized (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (hseed:seed∣C)(z:O):
    (Real.sqrt (volume s.toData):ℂ)⁻¹*sourceColumn s C hC R seed L z=
      ∑B:actualAllocations s.pools C,commonScalar s C R B*maskedAmplitude (commonData s C R B) L z:=by
  rw [source_column_allocation s C hC R seed L hseed z,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [live_column_rectangle]
  have hv:=volume_pos (commonData s C R B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have he:volume (commonData s C R B)*rawReduction B.val s.P=volume s.toData:=by
    rw [common_volume]
    exact raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hs:Real.sqrt (volume s.toData)=Real.sqrt (volume (commonData s C R B))*
      Real.sqrt (rawReduction B.val s.P):=by rw [←he,Real.sqrt_mul hv.le]
  unfold commonScalar maskedAmplitude
  change (Real.sqrt (volume s.toData):ℂ)⁻¹*(_*_) =
    ((Real.sqrt (rawReduction B.val s.P):ℂ)⁻¹*_)*
      ((Real.sqrt (volume (commonData s C R B)):ℂ)⁻¹*_)
  rw [hs,Complex.ofReal_mul,mul_inv_rev]
  ring

omit [DecidableEq ι] in
theorem commonScalar_sq (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖^2=
      ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P:=
  CenteredMomentDivisorRawEnergy.normalized_norm_sq _
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) _

omit [DecidableEq ι] in
theorem commonScalar_sq_bound (s:Input ι)(C R:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖^2≤
      ((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)/(Ideal.absNorm C:ℝ):=by
  rw [commonScalar_sq]
  exact frozen_normalized_cost B.val (alloc_ne s C B) C R hC
    (Finset.mem_filter.mp B.property).2 s.ν s.W s.P s.M s.P_pos s.ν_bound s.W_bound
    s.M_ge_one s.lower s.upper s.lower_pos s.slot_support

end SevenEighths.CenteredMomentCommonLinearNormalization

end

end OAI

end Source820

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonPairedSource.lean; sha256: e54bc6bc5b7da6b0cbbca43ca58a43f7e7ddb5df76d9c2e3bf135b6cfd844e55 -/
section Source821
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonPairedSource
open HeckeFamily UniqueFactorizationMonoid CanonicalQuadraticSieve
open CenteredMomentCommonLinearSource CenteredMomentCommonLinearNormalization
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def normalizedColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):ℂ:=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*sourceColumn s C hC R seed L z

theorem norm_column (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (hseed:seed∣C)(z:O):
    ‖normalizedColumn s C hC R seed L z‖≤
      ∑B:actualAllocations s.pools C,‖commonScalar s C R B‖*
        ‖maskedAmplitude (commonData s C R B) L z‖:=by
  unfold normalizedColumn
  rw [source_normalized s C hC R seed L hseed]
  simpa only [norm_mul] using norm_sum_le
    (Finset.univ:Finset (actualAllocations s.pools C))
    (fun B=>commonScalar s C R B*maskedAmplitude (commonData s C R B) L z)

theorem paired_columns (s:Input ι)(v:Input κ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed L:Ideal O)(hsC:seed∣C)(hsD:seed∣D)(rows:Finset O):
    (∑z∈rows,‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑z∈rows,‖maskedAmplitude (commonData s C R B) L z‖*
            ‖maskedAmplitude (commonData v D R E) L z‖:=by
  calc
    _≤∑z∈rows,(∑B:actualAllocations s.pools C,‖commonScalar s C R B‖*
        ‖maskedAmplitude (commonData s C R B) L z‖)*
      (∑E:actualAllocations v.pools D,‖commonScalar v D R E‖*
        ‖maskedAmplitude (commonData v D R E) L z‖):=by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul (norm_column s C hC R seed L hsC z)
        (norm_column v D hD R seed L hsD z) (norm_nonneg _)
        (Finset.sum_nonneg (fun B _=>mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _=_:=by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s:=rows) (t:=Finset.univ)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      apply Finset.sum_congr rfl
      intro E hE
      apply Finset.sum_congr rfl
      intro z hz
      ring

theorem whole_paired_columns (s:Input ι)(v:Input κ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed:Ideal O)(hsC:seed∣C)(hsD:seed∣D)(Ds:Finset (Ideal O))(rows:Finset O):
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
            ‖maskedAmplitude (commonData s C R B) L z‖*
              ‖maskedAmplitude (commonData v D R E) L z‖:=by
  calc
    _≤∑L∈Ds,‖(moebius L:ℂ)‖*
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑z∈rows,‖maskedAmplitude (commonData s C R B) L z‖*
            ‖maskedAmplitude (commonData v D R E) L z‖:=
      Finset.sum_le_sum (fun L hL=>mul_le_mul_of_nonneg_left
        (paired_columns s v C D hC hD R seed L hsC hsD rows) (norm_nonneg _))
    _=_:=by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E hE
      apply Finset.sum_congr rfl
      intro L hL
      apply Finset.sum_congr rfl
      intro z hz
      ring

end SevenEighths.CenteredMomentCommonPairedSource

end

end OAI

end Source821

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonExceptionalCost.lean; sha256: b90e4890e8d9eb6c6f2ab0f5260faee9d0d2d9a9eac453e602563eec64a646e5 -/
section Source822
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonExceptionalCost
open HeckeFamily CenteredMomentCommonLinearNormalization CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentCommonRawCost CenteredMomentExceptionalAmplitudePair
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentAllocationCost CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def frozenProfile (s:Input ι):ℝ:=(∏i,s.M i)*(max 1 s.upper)^Fintype.card ι

omit [DecidableEq ι] in
lemma frozenProfile_nonneg (s:Input ι):0≤frozenProfile s:=by
  unfold frozenProfile
  exact mul_nonneg (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)

omit [DecidableEq ι] in
theorem scalar_volume_exact (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖*Real.sqrt (volume (commonData s C R B))=
      ‖frozenCoefficient B.val C R s.ν s.W s.P‖*Real.sqrt (volume s.toData)/rawReduction B.val s.P:=by
  have hv:=volume_pos (commonData s C R B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have he:volume (commonData s C R B)*rawReduction B.val s.P=volume s.toData:=by
    rw [common_volume]
    exact raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hs:Real.sqrt (volume s.toData)=Real.sqrt (volume (commonData s C R B))*
      Real.sqrt (rawReduction B.val s.P):=by rw [←he,Real.sqrt_mul hv.le]
  rw [commonScalar,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),hs]
  have hsq:=Real.sq_sqrt hr.le
  have hn:Real.sqrt (rawReduction B.val s.P)≠0:=(Real.sqrt_pos.mpr hr).ne'
  field_simp
  rw [hsq]
  ring

omit [DecidableEq ι] in
theorem scalar_volume_bound (s:Input ι)(C R:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖*Real.sqrt (volume (commonData s C R B))≤
      frozenProfile s*Real.sqrt (volume s.toData)/(Ideal.absNorm C:ℝ):=by
  rw [scalar_volume_exact]
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hN:(0:ℝ)<Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  by_cases hz:frozenCoefficient B.val C R s.ν s.W s.P=0
  · rw [hz,norm_zero,zero_mul,zero_div]
    exact div_nonneg (mul_nonneg (frozenProfile_nonneg s) (Real.sqrt_nonneg _)) hN.le
  · have hn:=(actual_reduction_norm B.val (alloc_ne s C B) C R
      (Finset.mem_filter.mp B.property).2 s.ν s.W s.P s.P_pos s.lower s.upper
      s.lower_pos s.slot_support hz).2
    have hc:=frozenCoefficient_norm B.val C R s.ν s.W s.P s.M s.ν_bound s.W_bound s.M_ge_one
    have hi:(1:ℝ)/rawReduction B.val s.P≤(max 1 s.upper)^Fintype.card ι/(Ideal.absNorm C:ℝ):=
      (div_le_div_iff₀ hr hN).mpr (by simpa using hn)
    calc
      _≤((∏i,s.M i)*Real.sqrt (volume s.toData))/rawReduction B.val s.P:=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)) hr.le
      _=((∏i,s.M i)*Real.sqrt (volume s.toData))*(1/rawReduction B.val s.P):=by ring
      _≤((∏i,s.M i)*Real.sqrt (volume s.toData))*
          ((max 1 s.upper)^Fintype.card ι/(Ideal.absNorm C:ℝ)):=
        mul_le_mul_of_nonneg_left hi (mul_nonneg
          (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))) (Real.sqrt_nonneg _))
      _=_:=by unfold frozenProfile;ring

omit [DecidableEq ι] in
theorem common_slotControl (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C):
    slotControl (commonData s C R B)≤slotControl s.toData:=by
  unfold slotControl
  change (∏i:liveIndices B.val,s.M i.val)*
    (∏i:liveIndices B.val,max 1 (128*max 0 (s.hi i.val)*s.M i.val))≤_
  rw [Finset.prod_coe_sort (liveIndices B.val) s.M,
    Finset.prod_coe_sort (liveIndices B.val) (fun i:ι=>max 1 (128*max 0 (s.hi i)*s.M i))]
  apply mul_le_mul
  · exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
  · exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (le_max_left _ _)) (fun i _ _=>le_max_left _ _)
  · exact Finset.prod_nonneg (fun i _=>zero_le_one.trans (le_max_left _ _))
  · exact Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))

end SevenEighths.CenteredMomentCommonExceptionalCost

end

end OAI

end Source822

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonExceptionalMass.lean; sha256: c3033064945b9fba1394d955b95162dbc6d98c2e96a2002069eacace56c3e656 -/
section Source823
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonExceptionalMass
open HeckeFamily CenteredMomentCommonLinearNormalization CenteredMomentCommonRadialData
open CenteredMomentCommonExceptionalCost CenteredMomentCommonAllocationSum
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentAllocatedDetectorAmplitude
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma scalar_profile_volume (s:Input ι)(C R:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C):
    ‖commonScalar s C R B‖*slotControl (commonData s C R B)*Real.sqrt (volume (commonData s C R B))≤
      slotControl s.toData*frozenProfile s*Real.sqrt (volume s.toData)/(Ideal.absNorm C:ℝ):=by
  calc
    _=slotControl (commonData s C R B)*
        (‖commonScalar s C R B‖*Real.sqrt (volume (commonData s C R B))):=by ring
    _≤slotControl s.toData*(frozenProfile s*Real.sqrt (volume s.toData)/(Ideal.absNorm C:ℝ)):=
      mul_le_mul (common_slotControl s C R B) (scalar_volume_bound s C R hC B)
        (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (slotControl_nonneg s.toData)
    _=_:=by ring

lemma common_pair_profile_bound (s v:Input ι)(C D R:Ideal O)(hC:C≠0)(hD:D≠0)
    (B:actualAllocations s.pools C)(E:actualAllocations v.pools D)(p q:Tests)(J:ℕ):
    (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
      profileMass (commonData s C R B) (commonData v D R E) p q J≤
        profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/
          ((Ideal.absNorm C:ℝ)*Ideal.absNorm D):=by
  have hs:=scalar_profile_volume s C R hC B
  have hv:=scalar_profile_volume v D R hD E
  have hprod:=mul_le_mul hs hv
    (mul_nonneg (mul_nonneg (norm_nonneg _) (slotControl_nonneg _)) (Real.sqrt_nonneg _))
    (div_nonneg (mul_nonneg (mul_nonneg (slotControl_nonneg _) (frozenProfile_nonneg _))
      (Real.sqrt_nonneg _)) (Nat.cast_nonneg _))
  have hh:=mul_le_mul_of_nonneg_left hprod
    (show 0≤p.heightWeight s.t^J*q.heightWeight v.t^J by dsimp [Tests.heightWeight];positivity)
  convert hh using 1 <;> dsimp only [profileMass,commonData] <;> ring

theorem common_profile_mass (δ:ℝ)(hδ:0<δ):
    ∃K:ℝ,0<K ∧ ∀(s v:Input ι)(C D R:Ideal O),C≠0 → D≠0 → ∀(p q:Tests)(J:ℕ),
      (∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          profileMass (commonData s C R B) (commonData v D R E) p q J)≤
        K*((Ideal.absNorm C:ℝ)*Ideal.absNorm D)^δ*
          (profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((Ideal.absNorm C:ℝ)*Ideal.absNorm D)):=by
  obtain ⟨K,hK,hcard⟩:=actualAllocations_small_power (ι:=ι⊕Fin 2) δ hδ
  refine ⟨K^2,sq_pos_of_pos hK,?_⟩
  intro s v C D R hC hD p q J
  let A:=profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/
    ((Ideal.absNorm C:ℝ)*Ideal.absNorm D)
  have hA:0≤A:=div_nonneg (mul_nonneg (mul_nonneg (profileMass_nonneg _ _ _ _ _)
    (frozenProfile_nonneg _)) (frozenProfile_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc
    _≤∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,A:=
      Finset.sum_le_sum (fun B _=>Finset.sum_le_sum (fun E _=>common_pair_profile_bound s v C D R hC hD B E p q J))
    _=((actualAllocations s.pools C).card:ℝ)*((actualAllocations v.pools D).card:ℝ)*A:=by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul];ring
    _≤((K*(Ideal.absNorm C:ℝ)^δ)*(K*(Ideal.absNorm D:ℝ)^δ))*A:=
      mul_le_mul_of_nonneg_right (mul_le_mul (hcard s.pools C hC) (hcard v.pools D hD)
        (Nat.cast_nonneg _) (mul_nonneg hK.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))) hA
    _=_:=by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      dsimp only [A]
      ring

end SevenEighths.CenteredMomentCommonExceptionalMass

end

end OAI

end Source823

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonExceptionalGates.lean; sha256: b87d2abdd3e763c615aadca9a14e46786682ce90bc5d75155b085247aad04a57 -/
section Source824
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonExceptionalGates
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentFixedRowMask CenteredExceptionalProfile CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem coordinate_dvd (s:Input ι)(C:Ideal O)(B:actualAllocations s.pools C)(j:ι⊕Fin 2):
    B.val j∣C:=by
  exact (Finset.dvd_prod_of_mem B.val (Finset.mem_univ j)).trans
    (dvd_of_eq (Finset.mem_filter.mp B.property).2)

omit [DecidableEq ι] in
theorem coordinate_norm_le (s:Input ι)(C:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(j:ι⊕Fin 2):
    (Ideal.absNorm (B.val j):ℝ)≤Ideal.absNorm C:=by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC))
    (map_dvd Ideal.absNorm (coordinate_dvd s C B j))

omit [DecidableEq ι] in
theorem extracted_lower (s:Input ι)(C:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C)
    (j:ι⊕Fin 2)(Z r X:ℝ)(hZ:1<Z)(hX:Z^r≤X):
    Z^(r-Real.logb Z (Ideal.absNorm C:ℝ))≤X/Ideal.absNorm (B.val j):=by
  have hz:=zero_lt_one.trans hZ
  have hN:(0:ℝ)<Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hN]
  exact div_le_div₀ ((Real.rpow_nonneg hz.le r).trans hX) hX (alloc_norm_pos s C B j)
    (coordinate_norm_le s C hC B j)

omit [DecidableEq ι] in
theorem common_mask_inducing (s:Input ι)(C R Q:Ideal O)(hC:C≠0)(hR:R≠0)
    (B:actualAllocations s.pools C)(z:O)(hz:z≠0):
    FixedInducingRow (commonData s C R B).η Q (commonData s C R B).m
      (commonData s C R B).A z ↔ FixedInducingRow s.η Q fixedBadMask 1 z:=by
  exact fixedInducingRow_mul_mask_iff s.η Q fixedBadMask (idealGenerator (R*C)) 1 z
    fixedBadMask_ne_zero (idealGenerator_ne_zero _ (mul_ne_zero hR hC)) one_ne_zero hz
    (dvd_mul_right _ _) (dvd_mul_left _ _)

omit [DecidableEq ι] in
theorem common_conductor (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)(z:O):
    HeckeRowClosure.rowConductorBound (commonData s C R B).η (commonData s C R B).m 1
      ((commonData s C R B).A*z)=
      s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:=by
  simp only [commonData,HeckeRowClosure.rowConductorBound,one_mul,
    ←Ideal.span_singleton_mul_span_singleton,span_idealGenerator,map_mul,Ideal.span_singleton_one,Ideal.absNorm_top,one_pow]
  ring

omit [DecidableEq ι] in
theorem common_admissible (s:Input ι)(p:Tests)(C R Q:Ideal O)(hC:C≠0)(hR:R≠0)
    (B:actualAllocations s.pools C)(Z width r:ℝ)(hZ:1<Z)(z:O)(hz:z≠0)
    (hP:∀i,1≤s.P i)(hex:FixedInducingRow s.η Q fixedBadMask 1 z)
    (hcond:(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^width)
    (hW₁:s.W₁=p.profile 0)(hW₂:s.W₂=p.profile 1)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    Admissible (commonData s C R B) p Q Z width
      (r-Real.logb Z (Ideal.absNorm C:ℝ)) z:=by
  refine ⟨fun i=>hP i.val,?_,one_ne_zero,hz,?_,?_,?_,?_,hW₁,hW₂,?_,?_,?_,?_⟩
  · exact mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ (mul_ne_zero hR hC))
  · exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  · exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  · rw [common_conductor]
    simpa only [Nat.cast_mul] using hcond
  · exact (common_mask_inducing s C R Q hC hR B z hz).mpr hex
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂

end SevenEighths.CenteredMomentCommonExceptionalGates

end

end OAI

end Source824

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonExceptionalSource.lean; sha256: 95bbe1eaae8717c970c83b1b92c1d770776096c658f72b029e6c8307a934dee6 -/
section Source825
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentCommonExceptionalSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonExceptionalCost CenteredMomentCommonExceptionalMass CenteredMomentCommonExceptionalGates
open CenteredMomentExceptionalAsymmetricSource CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_common_exceptional (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Tests),(∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤s.X₁ → Z^rLeft≤s.X₂ → Z^rLeft≤s.Y₁ → Z^rLeft≤s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
        K*(rows.card:ℝ)*Z^(2*ε+δ-max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((C.absNorm:ℝ)*D.absNorm)):=by
  obtain ⟨J,hJ⟩:=actual_masked_asymmetric lo hi ε δ B Lbound hε hδ hB hL
  obtain ⟨Km,hKm,hmass⟩:=common_profile_mass (ι:=ι) θ hθ
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨Ka,hKa,hbound⟩:=hJ Q hQ
  refine ⟨Ka*Km,mul_pos hKa hKm,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond Ds hDs
  let H:=Ka*(rows.card:ℝ)*Z^(2*ε+δ-max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hH:0≤H:=by dsimp [H];positivity
  have hb (c:actualAllocations s.pools C)(d:actualAllocations v.pools D):
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖maskedAmplitude (commonData s C R c) L z‖*
          ‖maskedAmplitude (commonData v D R d) L z‖)≤
        H*profileMass (commonData s C R c) (commonData v D R d) p q J:=by
    apply hZ.2 _ _ (commonData s C R c) (commonData v D R d) p q
      (fun i=>hlo i.val) (fun i=>hhi i.val)
      (rLeft-Real.logb Z (C.absNorm:ℝ)) (rRight-Real.logb Z (D.absNorm:ℝ)) rows
    · intro z hz
      exact common_admissible s p C R Q hC.1 hR c Z B rLeft hZ.1 z (hn z hz) hsP
        (hsEx z hz) (hsCond z hz) hsW₁ hsW₂ hsX₁ hsX₂ hsY₁ hsY₂
    · intro z hz
      exact common_admissible v q D R Q hD.1 hR d Z B rRight hZ.1 z (hn z hz) hvP
        (hvEx z hz) (hvCond z hz) hvW₁ hvW₂ hvX₁ hvX₂ hvY₁ hvY₂
    · exact hDs
  apply (whole_paired_columns s v C D hC hD R seed hsC hsD Ds rows).trans
  calc
    _≤∑c:actualAllocations s.pools C,∑d:actualAllocations v.pools D,
      (‖commonScalar s C R c‖*‖commonScalar v D R d‖)*
        (H*profileMass (commonData s C R c) (commonData v D R d) p q J):=by
      apply Finset.sum_le_sum
      intro c hc
      exact Finset.sum_le_sum (fun d hd=>mul_le_mul_of_nonneg_left (hb c d)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _=H*(∑c:actualAllocations s.pools C,∑d:actualAllocations v.pools D,
      (‖commonScalar s C R c‖*‖commonScalar v D R d‖)*
        profileMass (commonData s C R c) (commonData v D R d) p q J):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _≤H*(Km*((C.absNorm:ℝ)*D.absNorm)^θ*
      (profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/
        ((C.absNorm:ℝ)*D.absNorm))):=
      mul_le_mul_of_nonneg_left (hmass s v C D R hC.1 hD.1 p q J) hH
    _=_:=by dsimp only [H];ring

end SevenEighths.CenteredMomentCommonExceptionalSource

end

end OAI

end Source825

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonRadialSource.lean; sha256: 8d003a96692c1d53ef10aacadd412aa0e37664d527e89931cdbbcd4cb40b9760 -/
section Source826
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonRadialSource
open CenteredMomentCommonRadialData CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale
open CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

 def sourceEnergy (s:Input ι) (r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O) : ℝ :=
  let Q:=finiteColumns (Fintype.piFinset s.pools)
  let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  sourceRestrictedEnergy r.keep (residualPool C hC.1 Q)
    (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
    (heightCoeff s.η s.t) r.profile r.scale/(s.X₁*s.X₂*∏i,s.P i)

 def commonCost (s:Input ι) (C:Ideal O) : ℝ :=
  ((actualAllocations s.pools C).card:ℝ)*
    (((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)/(Ideal.absNorm C:ℝ))

omit [DecidableEq ι] in
lemma commonCost_nonneg (s:Input ι) (C:Ideal O) : 0≤commonCost s C := by
  unfold commonCost
  positivity

 theorem live_source_eq (s:Input ι) (r:Radial) (C R L:Ideal O) (B:actualAllocations s.pools C) :
    sourceRestrictedEnergy r.keep
      (finiteColumns (liveBox s.pools B.val (alloc_ne s C B)))
      (finiteColumnCoefficient (liveBox s.pools B.val (alloc_ne s C B))
        (maskedLiveProfile B.val C R L s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1))
      (heightCoeff s.η s.t) r.profile r.scale/remainingRaw B.val (s.X₁*s.X₂) s.P=
      energy (commonData s C R B) r L := by
  rw [CenteredMomentCanonicalRetainedSource.liveBox_original_pools]
  have hcov₁:=plainCoverage_residualPool (s.pools (Sum.inr 0)) s.W₁ 1 _
    (alloc_ne s C B (Sum.inr 0)) s.X₁ s.Y₁ s.coverage₁
  have hcov₂:=plainCoverage_residualPool (s.pools (Sum.inr 1)) s.W₂ 1 _
    (alloc_ne s C B (Sum.inr 1)) s.X₂ s.Y₂ s.coverage₂
  simp only [one_mul] at hcov₁ hcov₂
  have hh:=CenteredMomentRadialSourceDictionary.actual_source_energy (commonData s C R B) r
    (residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) (s.pools (Sum.inr 0)))
    (residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) (s.pools (Sum.inr 1)))
    (R*C) L (B.val (Sum.inr 0)) (B.val (Sum.inr 1)) s.X₁ s.X₂ s.Y₁ s.Y₂
    rfl rfl rfl rfl rfl rfl hcov₁ hcov₂
  refine Eq.trans ?_ hh
  apply congrArg₂ (fun x y : ℝ => x / y)
  · simp only [maskedLiveProfile,commonData,one_mul,Input.pools,Sum.elim_inl]
  · dsimp only [remainingRaw,plainNorm,commonData]
    ring

 theorem original_source_common_bound (s:Input ι) (r:Radial) (C:Ideal O) (hC:Supported C)
    (R seed L:Ideal O) (hseed:seed∣C) :
    sourceEnergy s r C hC R seed L≤commonCost s C*
      ∑B:actualAllocations s.pools C,energy (commonData s C R B) r L := by
  have hh:=CenteredMomentSecondSourceCost.source_divisor_common_saving (ι:=ι) s.η s.pools s.pools_ne
    (fun i I hI=>s.prime i I hI) C R seed hC hseed s.ν s.W s.P s.W₁ s.W₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L s.t (s.X₁*s.X₂) (mul_pos s.X₁_pos s.X₂_pos)
    s.P_pos s.M s.ν_bound s.W_bound s.M_ge_one s.lower s.upper s.lower_pos s.slot_support
    r.keep r.profile r.scale r.scale_pos r.nonneg
  have hsum:(∑B:actualAllocations s.pools C,
      sourceRestrictedEnergy r.keep
        (finiteColumns (liveBox s.pools B.val (alloc_ne s C B)))
        (finiteColumnCoefficient (liveBox s.pools B.val (alloc_ne s C B))
          (maskedLiveProfile B.val C R L s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1))
        (heightCoeff s.η s.t) r.profile r.scale/remainingRaw B.val (s.X₁*s.X₂) s.P)=
      ∑B:actualAllocations s.pools C,energy (commonData s C R B) r L:=
    Finset.sum_congr rfl (fun B _=>live_source_eq s r C R L B)
  rw [hsum] at hh
  exact hh

end SevenEighths.CenteredMomentCommonRadialSource

end

end OAI

end Source826

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonRadialCost.lean; sha256: 07871a55bb5ba7af1c4b4498a40f5829c646a6c99d0ea391a97afeabc068ec52 -/
section Source827
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadialCost
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentAllocationCost
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma sqrt_nat_le_add_one (n:ℕ) : Real.sqrt (n:ℝ)≤(n:ℝ)+1 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]

omit [DecidableEq ι] in
 theorem paired_card_subpower (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι) (C D:Ideal O),C≠0 → D≠0 →
      ∀Z:ℝ,1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      (Real.sqrt ((actualAllocations s.pools C).card:ℝ)*Real.sqrt ((actualAllocations s.pools D).card:ℝ))*
        (((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ))≤C0*Z^δ := by
  let ε:ℝ:=δ/(4*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  obtain ⟨D0,hD0,hcard⟩:=actualAllocations_uniform_small_power (Fintype.card (ι⊕Fin 2)) ε hε
  refine ⟨(D0+1)^4,by positivity,?_⟩
  intro s C D hC hD Z hZ hNC hND
  have hz:0<Z:=zero_lt_one.trans hZ
  have bound (I:Ideal O) (hI:I≠0) (hn:(Ideal.absNorm I:ℝ)≤Z^B):
      ((actualAllocations s.pools I).card:ℝ)+1≤(D0+1)*Z^(B*ε):=by
    have hi:(1:ℝ)≤Ideal.absNorm I:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have hh:=hcard (le_refl (Fintype.card (ι⊕Fin 2))) s.pools I hI
    have hp:(Ideal.absNorm I:ℝ)^ε≤Z^(B*ε):=by
      apply (Real.rpow_le_rpow (by positivity) hn hε.le).trans_eq
      rw [←Real.rpow_mul hz.le]
    have hone:1≤Z^(B*ε):=Real.one_le_rpow hZ.le (mul_nonneg hB hε.le)
    nlinarith [mul_le_mul_of_nonneg_left hp hD0.le]
  have hc:=bound C hC hNC
  have hd:=bound D hD hND
  have hSc:Real.sqrt ((actualAllocations s.pools C).card:ℝ)≤(D0+1)*Z^(B*ε):=
    (sqrt_nat_le_add_one _).trans hc
  have hSd:Real.sqrt ((actualAllocations s.pools D).card:ℝ)≤(D0+1)*Z^(B*ε):=
    (sqrt_nat_le_add_one _).trans hd
  have hcc:((actualAllocations s.pools C).card:ℝ)≤(D0+1)*Z^(B*ε):=by linarith
  have hdd:((actualAllocations s.pools D).card:ℝ)≤(D0+1)*Z^(B*ε):=by linarith
  calc
    _≤(((D0+1)*Z^(B*ε))*((D0+1)*Z^(B*ε)))*
        (((D0+1)*Z^(B*ε))*((D0+1)*Z^(B*ε))):=by gcongr
    _=(D0+1)^4*Z^(4*B*ε):=by
      rw [show ((D0+1)*Z^(B*ε)*((D0+1)*Z^(B*ε)))*
        ((D0+1)*Z^(B*ε)*((D0+1)*Z^(B*ε)))=(D0+1)^4*(Z^(B*ε))^4 by ring]
      rw [←Real.rpow_mul_natCast hz.le]
      congr 2
      ring
    _≤_:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have he:ε*(4*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
      nlinarith

omit [DecidableEq ι] in
 theorem card_squared_subpower (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι) (C:Ideal O),C≠0 →
      ∀Z:ℝ,1<Z → (Ideal.absNorm C:ℝ)≤Z^B →
      ((actualAllocations s.pools C).card:ℝ)^2≤C0*Z^δ := by
  obtain ⟨C0,hC0,hbound⟩:=paired_card_subpower (ι:=ι) B δ hB hδ
  refine ⟨C0,hC0,?_⟩
  intro s C hC Z hZ hn
  have hh:=hbound s C C hC hC Z hZ hn hn
  have he:Real.sqrt ((actualAllocations s.pools C).card:ℝ)*
      Real.sqrt ((actualAllocations s.pools C).card:ℝ)=((actualAllocations s.pools C).card:ℝ):=by
    rw [←pow_two,Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [he] at hh
  by_cases hz:(actualAllocations s.pools C).card=0
  · rw [hz,Nat.cast_zero,zero_pow (by decide)]
    positivity
  · have hc:(1:ℝ)≤(actualAllocations s.pools C).card:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    apply le_trans ?_ hh
    nlinarith [sq_nonneg ((actualAllocations s.pools C).card:ℝ)]

end SevenEighths.CenteredMomentCommonRadialCost

end

end OAI

end Source827

/- Original source: OAI/NumberTheory/DirichletL/Moments/RadialPointwiseEnergy.lean; sha256: eb3ea2a640a69eeb2db9de78fe5c59cd1996150f3afe4c6c6820bd223c378bf8 -/
section Source828
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRadialPointwiseEnergy
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentSlotRatios CenteredMomentUniformDivisorShell
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma inverse_reduction (s:Data ι) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (ha:a∈s.toSource.active D)
    (Z:ℝ) (hZ:1<Z) :
    1/formalReductionFactor D a s.P≤Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ) := by
  have hh:=s.toSource.active_pair_weight s.toSource D hD a a ha ha Z hZ
  rw [show formalReductionFactor D a s.P*formalReductionFactor D a s.P=
    (formalReductionFactor D a s.P)^2 by ring,Real.sqrt_sq (s.reduction_pos D a).le] at hh
  convert hh using 1
  congr 2
  ring

 theorem actual_pointwise_divisor (N:ℕ) (hι:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
      ∀E Z:ℝ,0≤E → 1<Z → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^(2*ε)*Z^(s.toSource.allowance Z)*
        (s.profileFactor*E)/(Ideal.absNorm D:ℝ) := by
  obtain ⟨C₁,hC₁,henergy⟩:=CenteredMomentRadialEligibleEnergy.actual_source_from_children N hι ε hε
  obtain ⟨C₂,hC₂,hcard⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro s r D hD E Z hE hZ hc
  have hn:0<(Ideal.absNorm D:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg hn.le _
  have hsz:((s.toSource.active D).card:ℝ)≤C₂*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((s.toSource.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard D hD.ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hs:(∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)≤
      (C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ)):=by
    calc
      _≤∑a∈s.toSource.active D,Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ):=
        Finset.sum_le_sum (fun a ha=>inverse_reduction s D hD a ha Z hZ)
      _=((s.toSource.active D).card:ℝ)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ)):=by simp
      _≤_:=mul_le_mul_of_nonneg_right hsz (div_nonneg (Real.rpow_nonneg (by linarith) _) hn.le)
  apply (henergy s r D hD E hE hc).trans
  calc
    _≤C₁*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ((C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ))):=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg (mul_nonneg hC₁.le hp) s.profile_nonneg) hE)
    _=_:=by
      have he:(Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε=(Ideal.absNorm D:ℝ)^(2*ε):=by
        rw [←Real.rpow_add hn];congr 1;ring
      calc
        _=(C₁*C₂)*((Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε)*
          Z^(s.toSource.allowance Z)*(s.profileFactor*E)/(Ideal.absNorm D:ℝ):=by ring
        _=_:=by rw [he]

end SevenEighths.CenteredMomentRadialPointwiseEnergy

end

end OAI

end Source828

/- Original source: OAI/NumberTheory/DirichletL/Moments/RadialPointwiseUniform.lean; sha256: 4e107a1e9f20f92539c65ea3bca114beabca99a2b3f35fc60c63f3024bc5d525 -/
section Source829
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRadialPointwiseUniform
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentRadialPointwiseEnergy CenteredMomentUniformDivisorShell
open CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Bound (ι:Type*) [Fintype ι] [DecidableEq ι] (C ε:ℝ) : Prop :=
  ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
    ∀E Z:ℝ,0≤E → 1<Z → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
    energy s r D≤C*(Ideal.absNorm D:ℝ)^(2*ε)*Z^(s.toSource.allowance Z)*
      (s.profileFactor*E)/(Ideal.absNorm D:ℝ)

 theorem uniform_subset (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀J:Finset ι,Bound J C ε := by
  have he (J:Finset ι):∃C:ℝ,0<C ∧ Bound J C ε:=
    actual_pointwise_divisor (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose C hC hb using he
  let D:ℝ:=1+∑J:Finset ι,C J
  have hs:0≤∑J:Finset ι,C J:=Finset.sum_nonneg (fun J _=>(hC J).le)
  refine ⟨D,by dsimp [D];linarith,?_⟩
  intro J s r I hI E Z hE hZ hc
  have hd:C J≤D:=by
    have hh:=Finset.single_le_sum (fun J _=>(hC J).le) (Finset.mem_univ J)
    dsimp [D];linarith
  apply (hb J s r I hI E Z hE hZ hc).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg s.profile_nonneg hE)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
  exact mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (Nat.cast_nonneg _) _)

 theorem actual_uniform_divisor (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀(J:Finset ι) (s:Data J),(∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      ∀(r:Radial) (D:Ideal O),Squarefree D → ∀E Z:ℝ,0≤E → 1<Z →
      (Ideal.absNorm D:ℝ)≤Z^B → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*Z^δ*(s.profileFactor*E)/(Ideal.absNorm D:ℝ) := by
  let ε:ℝ:=δ/(2*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  obtain ⟨C,hC,hbound⟩:=uniform_subset (ι:=ι) ε hε
  let A:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*A,by dsimp [A];positivity,?_⟩
  intro J s hlo hhi r D hD E Z hE hZ hN hc
  have hz:0<Z:=zero_lt_one.trans hZ
  have ha:Z^(s.toSource.allowance Z)≤A:=by
    dsimp [A]
    rw [←numerical_allowance Z _ hZ]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (subset_allowance J s.toSource lo hi hlo hhi Z hZ)
  have hp:(Ideal.absNorm D:ℝ)^(2*ε)≤Z^δ:=by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    have he:ε*(2*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  apply (hbound J s r D hD E Z hE hZ hc).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg s.profile_nonneg hE)
  calc
    _≤C*Z^δ*A:=mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) ha
      (Real.rpow_nonneg hz.le _) (by positivity)
    _=_:=by ring

end SevenEighths.CenteredMomentRadialPointwiseUniform

end

end OAI

end Source829

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonRadialPointwise.lean; sha256: 4869ba015a3bcd735458488cbaef6f75e8be77cad17b80ebddd6d4a40cf59983 -/
section Source830
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialSource CenteredMomentCommonRadialData CenteredMomentCommonRadialCost
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

 def profileCost (s:Input ι) : ℝ :=
  ((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)*s.toData.profileFactor

omit [DecidableEq ι] in
lemma profileCost_nonneg (s:Input ι) : 0≤profileCost s :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) s.toData.profile_nonneg

 theorem actual_common_source_pointwise (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      ∀(r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O),seed∣C → Squarefree L →
      ∀E Z:ℝ,0≤E → 1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm L:ℝ)≤Z^B →
      (∀b:actualAllocations s.pools C,∀a∈(commonData s C R b).toSource.active L,
        childEnergy (commonData s C R b) r L a≤E) →
      sourceEnergy s r C hC R seed L≤C0*Z^δ*(profileCost s*E)/
        ((Ideal.absNorm C:ℝ)*Ideal.absNorm L) := by
  obtain ⟨C₁,hC₁,hchild⟩:=CenteredMomentRadialPointwiseUniform.actual_uniform_divisor lo hi B (δ/2) hB (by linarith)
  obtain ⟨C₂,hC₂,hcount⟩:=card_squared_subpower (ι:=ι) B (δ/2) hB (by linarith)
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro s hlo hhi r C hC R seed L hseed hL E Z hE hZ hNC hNL hc
  have hnC:0<(Ideal.absNorm C:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hnL:0<(Ideal.absNorm L:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL.ne_zero)
  have hz:0<Z:=zero_lt_one.trans hZ
  have heach (b:actualAllocations s.pools C):
      energy (commonData s C R b) r L≤C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(Ideal.absNorm L:ℝ):=by
    have hh:=hchild (liveIndices b.val) (commonData s C R b)
      (fun i=>hlo i.val) (fun i=>hhi i.val) r L hL E Z hE hZ hNL (hc b)
    apply hh.trans
    apply div_le_div_of_nonneg_right _ hnL.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right (common_profile_le s C R b) hE
  have hh:sourceEnergy s r C hC R seed L≤commonCost s C*
      (((actualAllocations s.pools C).card:ℝ)*(C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(Ideal.absNorm L:ℝ))):=by
    apply (original_source_common_bound s r C hC R seed L hseed).trans
    apply mul_le_mul_of_nonneg_left _ (commonCost_nonneg s C)
    apply (Finset.sum_le_sum (fun b _=>heach b)).trans_eq
    simp
  apply hh.trans
  have hc2:=hcount s C hC.1 Z hZ hNC
  calc
    _=((actualAllocations s.pools C).card:ℝ)^2*
        (C₁*Z^(δ/2)*(profileCost s*E)/((Ideal.absNorm C:ℝ)*Ideal.absNorm L)):=by
      unfold commonCost profileCost
      ring
    _≤(C₂*Z^(δ/2))*(C₁*Z^(δ/2)*(profileCost s*E)/
        ((Ideal.absNorm C:ℝ)*Ideal.absNorm L)):=
      mul_le_mul_of_nonneg_right hc2 (div_nonneg (mul_nonneg (by positivity)
        (mul_nonneg (profileCost_nonneg s) hE)) (mul_nonneg hnC.le hnL.le))
    _=_:=by
      have hp:Z^(δ/2)*Z^(δ/2)=Z^δ:=by rw [←Real.rpow_add hz];congr 1;ring
      calc
        _=(C₁*C₂)*(Z^(δ/2)*Z^(δ/2))*(profileCost s*E)/
          ((Ideal.absNorm C:ℝ)*Ideal.absNorm L):=by ring
        _=_:=by rw [hp]

end SevenEighths.CenteredMomentCommonRadialPointwise

end

end OAI

end Source830

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonHeightEnvelope.lean; sha256: b7e29bdd6c0c9bf0267d7f7d36a43db9ee73b320ef7e05d352b49dbacacdf186 -/
section Source831
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonHeightEnvelope
open HeckeFamily CenteredMomentCommonRadialSource CenteredMomentCommonRadialData
open CenteredMomentCommonRadialPointwise CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentCommonAllocationSum CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

 def withHeight (s:Input ι) (η:Character) (t:ℝ) : Input ι := {s with η:=η,t:=t}

 def envelope (s:Input ι) (C L:Ideal O) (C0 Z δ E:ℝ) : ℝ :=
  C0*Z^δ*(profileCost s*E)*(s.X₁*s.X₂*∏i,s.P i)/((Ideal.absNorm C:ℝ)*Ideal.absNorm L)

 theorem actual_height_envelope (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      ∀(r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O),seed∣C → Squarefree L →
      ∀E Z:ℝ,0≤E → 1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm L:ℝ)≤Z^B →
      ∀J:ℕ,∀(τ:Character) (v:ℝ),
      (∀b:actualAllocations s.pools C,∀a∈(commonData (withHeight s τ v) C R b).toSource.active L,
        childEnergy (commonData (withHeight s τ v) C R b) r L a≤E*(1+‖v‖)^(2*J)) →
      let Q:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      sourceRestrictedEnergy r.keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ v) r.profile r.scale≤envelope s C L C0 Z δ E*(1+‖v‖)^(2*J) := by
  obtain ⟨C0,hC0,hbound⟩:=actual_common_source_pointwise lo hi B δ hB hδ
  refine ⟨C0,hC0,?_⟩
  intro s hlo hhi r C hC R seed L hs hL E Z hE hZ hNC hNL J τ v hc
  have hh:=hbound (withHeight s τ v) hlo hhi r C hC R seed L hs hL
    (E*(1+‖v‖)^(2*J)) Z (mul_nonneg hE (by positivity)) hZ hNC hNL hc
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  unfold sourceEnergy at hh
  have hmul:=(div_le_iff₀ hraw).mp hh
  apply hmul.trans_eq
  change (C0*Z^δ*(profileCost s*(E*(1+‖v‖)^(2*J)))/
      ((Ideal.absNorm C:ℝ)*Ideal.absNorm L))*(s.X₁*s.X₂*∏i,s.P i)=_
  unfold envelope
  ring

end SevenEighths.CenteredMomentCommonHeightEnvelope

end

end OAI

end Source831

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeRow.lean; sha256: a19dbab6d87b075b90f272b819e8ce37e744284c92e9a25a806480cfc0bc1f28 -/
section Source832
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate BigOperators
namespace SevenEighths.HeckePrimeRow
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem identityClass_coprime {I : Ideal O} (hI : I∈RayQuotient.identityClass M H) :
    IsCoprime I M := by
  obtain ⟨hI,a,ha,u,hu,huH⟩ := hI
  rw [←ha]
  exact (IdealCharacter.isUnit_mk_iff_isCoprime M a).mp (hu ▸ u.isUnit)

omit [NeZero M] in
theorem identityClass_coprime_larger {I J : Ideal O}
    (hI : I∈RayQuotient.identityClass M H) (hMJ : M≤J) : IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  apply top_unique
  rw [←Ideal.isCoprime_iff_sup_eq.mp (identityClass_coprime M H hI)]
  exact sup_le_sup_left hMJ I

omit [NeZero M] in
theorem identityClass_prime_good (m : O) (hmLam : λ₀∣m) (hMm : M≤Ideal.span {m})
    (P : Ideal O) [P.IsMaximal] (hP : P∈RayQuotient.identityClass M H) : λ₀∉P := by
  have hm : m∉P := (SixthPowerAverage.prime_coprime_span_iff P m).mp
    (identityClass_coprime_larger M H hP hMm)
  intro hLam
  obtain ⟨a,rfl⟩ := hmLam
  exact hm (P.mul_mem_right a hLam)

include hH in
theorem identityClass_principal_coeff {I : Ideal O} (hI : I∈RayQuotient.identityClass M H) :
    idealCoeff (HeckeRayFamily.character M 1) I=1 := by
  have hc := identityClass_coprime M H hI
  change RayQuotient.idealCharacter M H hH 1 I=1
  rw [RayQuotient.idealCharacter_one M H hH I,ite_eq_right hI.1,ite_eq_left hc]

include hH in
theorem exists_actual_prime_row (m u : O) (hm : m≠0) (hu : u≠0)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) (hMm : M≤Ideal.span {m}) :
    ∃ χ : Character, χ.modulus.absNorm≤rowConductorBound (HeckeRayFamily.character M 1) m 1 u ∧
      ∀ (P : Ideal O) [P.IsMaximal] (hg : λ₀∉P),
      P∈RayQuotient.identityClass M H →
      idealCoeff χ P = starRingEnd ℂ
        (CompletedGauss.actualSextic P hg (Ideal.Quotient.mk P u)) := by
  obtain ⟨χ,hbound,hχ⟩ := exists_row_character_with_conductor (HeckeRayFamily.character M 1) m 1 u hm one_ne_zero hu hmLam hm2
  refine ⟨χ.inverse,hbound,?_⟩
  intro P _ hg hP
  have hc : IsCoprime P (Ideal.span {m}) := by
    rw [Ideal.isCoprime_iff_sup_eq] at ⊢
    apply top_unique
    rw [←Ideal.isCoprime_iff_sup_eq.mp (identityClass_coprime M H hP)]
    exact sup_le_sup_left hMm P
  rw [idealCoeff_inverse_conj,idealCoeff_eq_row _ χ m 1 u hχ,
    identityClass_principal_coeff M H hH hP,one_mul,one_pow,mul_one,
    idealRowHom_argument_mul,idealRowHom_prime_sixth_mask m P hg,ite_eq_left hc,one_mul,
    idealRowHom_prime u P hg]

def canonicalPrimeAmplitude (u : O) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ P∈(HeckePrimeAnnular.annulusSet b D).filter
    (fun P => Prime P ∧ P∈RayQuotient.identityClass M H),
    starRingEnd ℂ (idealRowHom u P)*W ((P.absNorm : ℝ)/D)*
      (((P.absNorm : ℝ)/D : ℝ) : ℂ)^(z-1)

include hH in

theorem exists_amplitude_character (m u : O) (hm : m≠0) (hu : u≠0)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) (hMm : M≤Ideal.span {m}) :
    ∃ χ : Character, χ.modulus.absNorm≤rowConductorBound (HeckeRayFamily.character M 1) m 1 u ∧
      ∀ (W : ℝ→ℂ) (b D : ℝ) (z : ℂ),
        canonicalPrimeAmplitude M H u W b D z =
          HeckePrimeRay.rayPrimePolynomial M H χ W b D (1-z.re) z.im := by
  obtain ⟨χ,hbound,hχ⟩ := exists_actual_prime_row M H hH m u hm hu hmLam hm2 hMm
  refine ⟨χ,hbound,?_⟩
  intro W b D z
  unfold canonicalPrimeAmplitude HeckePrimeRay.rayPrimePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨_,hprime,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hg := identityClass_prime_good M H m hmLam hMm P hclass
  have hc := hχ P hg hclass
  rw [←idealRowHom_prime u P hg] at hc
  rw [hc]
  have he : -HeckeDyadic.shift (1-z.re) z.im=z-1 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  simp only [HeckePrimeAnnular.annularWeight,he]
  ring

end SevenEighths.HeckePrimeRow

end

end OAI

end Source832

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeScale.lean; sha256: a8e153a9a63be08a449498fce4fce1665fe50a605feb1d9ce6cc9aa700d74a64 -/
section Source833
namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SevenEighths.HeckePrimeScale
open HeckeFamily

theorem log_scale_eventually (dmin rmin K : ℝ) (hd : 0<dmin) (hr : 0<rmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d r : ℝ, dmin≤d → rmin≤r →
      K≤Real.log ((Z^d)^r) := by
  have hlog : ∀ᶠ Z : ℝ in atTop, max 0 (K/(dmin*rmin))≤Real.log Z :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlog,eventually_ge_atTop (1 : ℝ)] with Z hlog hZ
  intro d r hd' hr'
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [Real.log_rpow (Real.rpow_pos_of_pos hZp _),Real.log_rpow hZp]
  have hp : 0<dmin*rmin := mul_pos hd hr
  have hk : K≤dmin*rmin*Real.log Z := by
    have hh := (div_le_iff₀ hp).mp ((le_max_right 0 _).trans hlog)
    nlinarith
  have hprod : dmin*rmin≤d*r := mul_le_mul hd' hr' hr.le (hd.trans_le hd').le
  have hl : 0≤Real.log Z := (le_max_left _ _).trans hlog
  nlinarith [mul_le_mul_of_nonneg_right hprod hl]

theorem product_modulus_bound (χ ψ : Character) :
    (χ.product ψ).modulus.absNorm≤χ.modulus.absNorm*ψ.modulus.absNorm := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (O ⧸ ψ.modulus) := Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  exact FiniteConductor.absNorm_inf_le_mul χ.modulus ψ.modulus

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem twisted_modulus_bound (χ : Character) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ θ).modulus.absNorm≤χ.modulus.absNorm*M.absNorm :=
  product_modulus_bound χ (HeckeRayQuotient.character M H hH θ)

theorem twisted_row_modulus_bound (χ : Character) (m u : O)
    (hχ : χ.modulus.absNorm≤HeckeRowClosure.rowConductorBound (HeckeRayFamily.character M 1) m 1 u)
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ θ).modulus.absNorm≤
      M.absNorm^2*(Ideal.span {m}).absNorm*(Ideal.span {(72 : O)}).absNorm*(Ideal.span {u}).absNorm := by
  apply (twisted_modulus_bound M H hH χ θ).trans
  have hn := Nat.mul_le_mul_right M.absNorm hχ
  simpa [HeckeRowClosure.rowConductorBound,HeckeRayFamily.character,
    Character.ofResidue,pow_two,mul_assoc,mul_left_comm,mul_comm] using hn

end SevenEighths.HeckePrimeScale

end

end OAI

end Source833

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectedSource.lean; sha256: 81e1c25f49295e0a58465642f1bf73c115b06eff3dc83210dee5639b64dd983f -/
section Source834
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentReflectedSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CanonicalUnitEuler
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonLinearSource CenteredMomentCommonPairedSource
open CenteredMomentFirstSectors CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondHeightFamily CenteredMomentSourceRow
local notation "O" => HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def reflected (η:Character):Character:=η.product (HeckeUnitRows.character (-1:Oˣ))

theorem unit_ideal (I:Ideal O)(hI:Supported I):
    idealCoeff (HeckeUnitRows.character (-1:Oˣ)) I=idealRowHom (-1) I:=by
  rw [←ConcretePrimeRowBridge.span_idealGenerator I,
    idealCoeff_span _ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI.1),
    HeckeUnitRows.elementCoeff_character]
  change (if Supported (Ideal.span {ConcretePrimeRowBridge.idealGenerator I}) then _ else 0)=_
  rw [ConcretePrimeRowBridge.span_idealGenerator,ite_eq_left hI]
  rfl

theorem reflected_height (η:Character)(t:ℝ)(I:Ideal O)(hI:Supported I):
    heightCoeff (reflected η) t I=heightCoeff η t I*idealRowHom (-1) I:=by
  rw [heightCoeff,reflected,idealCoeff_product,unit_ideal I hI,heightCoeff]
  ring

theorem polynomial_neg {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(η:Character)(t:ℝ)(z:O):
    rowPolynomial S a (fun i=>c i*heightCoeff η t (Ideal.span {a i})) (-z)=
      rowPolynomial S a (fun i=>c i*heightCoeff (reflected η) t (Ideal.span {a i})) z:=by
  unfold rowPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [reflected_height η t _ (ha i),show -z=(-1)*z by ring,idealRowHom_argument_mul]
  ring

theorem sourceColumn_neg {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):
    sourceColumn s C hC R seed L (-z)=
      sourceColumn (withHeight s (reflected s.η) s.t) C hC R seed L z:=by
  let Q:=residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))
  let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  have h:=polynomial_neg Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then β (C*I) else 0)
    s.η s.t z
  have hspan (I:supportedColumns Q):Ideal.span {sourceGenerator Q I}=(I:Ideal O):=
    primary_span_supported I (Finset.mem_filter.mp I.property).2
  simp only [hspan] at h
  dsimp only [sourceColumn, withHeight, Input.pools, Q, β] at h ⊢
  convert h using 1
  rfl

theorem normalizedColumn_neg {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):
    normalizedColumn s C hC R seed L (-z)=
      normalizedColumn (withHeight s (reflected s.η) s.t) C hC R seed L z:=by
  unfold normalizedColumn
  rw [sourceColumn_neg]
  simp only [withHeight,CenteredMomentExceptionalAmplitudePair.volume]

theorem reflected_row (η:Character)(m A z n:O)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m):
    rowTwist (HeckeRowClosure.elementHom η) m 1 (A*(-z)) n=
      rowTwist (HeckeRowClosure.elementHom (reflected η)) m 1 (A*z) n:=by
  by_cases hn:Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ m 1 _ n hn,rowTwist_extract_sixth_mask _ m 1 _ n hn]
    simp only [one_pow,one_mul]
    change elementCoeff η n*coprimalityMask m n*idealRowHom (A*(-z)) (Ideal.span {n})=
      elementCoeff (reflected η) n*coprimalityMask m n*idealRowHom (A*z) (Ideal.span {n})
    rw [reflected,elementCoeff_product,HeckeUnitRows.elementCoeff_character]
    have hu:unitSupplement (-1:Oˣ) n=idealRowHom (-1) (Ideal.span {n}):=by
      change (if Supported (Ideal.span {n}) then idealRowHom (-1) (Ideal.span {n}) else 0)=_
      rw [ite_eq_left hn]
    rw [hu,show A*(-z)=(-1)*(A*z) by ring,idealRowHom_argument_mul]
    ring
  · rw [CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn,
      CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn]

theorem reflected_inducing (η:Character)(Q:Ideal O)(m A z:O)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m):
    CenteredExceptionalProfile.FixedInducingRow η Q m A (-z) ↔
      CenteredExceptionalProfile.FixedInducingRow (reflected η) Q m A z:=by
  unfold CenteredExceptionalProfile.FixedInducingRow
  simp_rw [←reflected_row η m A z _ hmLam hm2]

end SevenEighths.CenteredMomentReflectedSource

end

end OAI

end Source834

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalFamily.lean; sha256: 125db37041979feb43ef85e1b111faa4ab0dbb387e5d33380106d203c5b8af7e -/
section Source835
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace SevenEighths.CenteredMomentSecondExceptionalFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentPartitionNorm
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedWidth
open CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource CenteredMomentSecondRadicalColumns
open CenteredMomentSecondReducedPredicate CenteredMomentSecondLiveBlock CenteredMomentSecondBlockSupport
open CenteredMomentSecondPhysicalBlock CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentRestrictedEnergy CenteredMomentSectorLocalization RayFourExpansion
open CenteredExceptionalProfile CenteredMomentReflectedSource
local notation "O" => HeckeFamily.O

theorem span_thirty_six_norm : (Ideal.span {(36:O)}).absNorm=1296 := by
  have h := ActualEisensteinCubic.rational_modulus_card 36 (by norm_num)
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply]
  exact h

theorem reflected_modulus_bound (τ:Character) :
    (reflected τ).modulus.absNorm≤1296*τ.modulus.absNorm := by
  have h := HeckePrimeScale.product_modulus_bound τ (HeckeUnitRows.character (-1:Oˣ))
  change (reflected τ).modulus.absNorm≤τ.modulus.absNorm*(Ideal.span {(36:O)}).absNorm at h
  simpa only [span_thirty_six_norm,mul_comm] using h

theorem common_subproduct_dvd_left (C D:Ideal O) (hC:Supported C)
    (hCD:primeSupport C=primeSupport D) (S:Finset (CommonIndex C D)) :
    (∏P∈S,P.val)∣C := by
  have h₁ := Finset.prod_dvd_prod_of_subset S Finset.univ
    (fun P:CommonIndex C D=>P.val) (Finset.subset_univ S)
  have h₂ : (∏P:CommonIndex C D,P.val)∣
      ∏P:CommonIndex C D,Ideal.span {commonPrime C D P}^leftExponent C D P := by
    apply Finset.prod_dvd_prod_of_dvd
    intro P _
    rw [commonPrime_span C D hC]
    exact dvd_pow_self _ (Nat.ne_zero_of_lt (leftExponent_pos C D P))
  rw [left_ideal_product C D hC hCD] at h₂
  exact h₁.trans h₂

theorem common_subproduct_dvd_right (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (S:Finset (CommonIndex C D)) :
    (∏P∈S,P.val)∣D := by
  have h₁ := Finset.prod_dvd_prod_of_subset S Finset.univ
    (fun P:CommonIndex C D=>P.val) (Finset.subset_univ S)
  have h₂ : (∏P:CommonIndex C D,P.val)∣
      ∏P:CommonIndex C D,Ideal.span {commonPrime C D P}^rightExponent C D P := by
    apply Finset.prod_dvd_prod_of_dvd
    intro P _
    rw [commonPrime_span C D hC]
    exact dvd_pow_self _ (Nat.ne_zero_of_lt (rightExponent_pos C D P))
  rw [right_ideal_product C D hC hD hCD] at h₂
  exact h₁.trans h₂

theorem selected_nonunit_product (C D:Ideal O) (hC:Supported C)
    (U:Finset (CommonIndex C D)) :
    (∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}=
      ∏P∈U∪nonunitPartitionSet C D U,P.val := by
  have hd : Disjoint U (nonunitPartitionSet C D U) := by
    apply Finset.disjoint_left.mpr
    intro P hP hV
    exact (Finset.mem_sdiff.mp hV).2 hP
  rw [Finset.prod_union hd,nonunitFrequencyGenerator_span]
  simp only [unitIdeal,commonPrime_span C D hC]

theorem selected_nonunit_dvd (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D)) :
    ((∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}∣C) ∧
    ((∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}∣D) := by
  rw [selected_nonunit_product C D hC]
  exact ⟨common_subproduct_dvd_left C D hC hCD _,
    common_subproduct_dvd_right C D hC hD hCD _⟩

theorem selected_nonunit_norm (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D)) :
    (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm≤C.absNorm ∧
    (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm≤D.absNorm := by
  obtain ⟨h₁,h₂⟩ := selected_nonunit_dvd C D hC hD hCD U
  constructor
  · simpa only [map_mul] using Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)) (map_dvd Ideal.absNorm h₁)
  · simpa only [map_mul] using Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)) (map_dvd Ideal.absNorm h₂)

structure Family (η:Character) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (τ:RayCharacter→Character) : Prop where
  element_eq : ∀χ n,elementCoeff (τ χ) n=
    rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n
  height_eq : ∀χ I,Supported I→(IsCoprime C I ∨ IsCoprime D I)→∀t,
    heightCoeff (τ χ) t I=heightCoeff η t I*
      idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
      rayCharacter χ (primaryGenerator I)
  physical_budget : ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U R rows W K n≠0→∀χ,
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
    ∀Z:ℝ,1<Z→∀z∈liveRows C D U R rows,
      Real.logb Z (normValue z)+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
        Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ))

theorem exists_exceptional_family (η:Character) (C D:Ideal O)
    (hC:Supported C) (hD:Supported D) (hCD:primeSupport C=primeSupport D)
    (U:Finset (CommonIndex C D)) : ∃τ,Family η C D hC hD U τ := by
  choose τ he ht hrest using fun χ:RayCharacter=>exists_retained_width_family η χ C D hC U
  refine ⟨τ,he,?_,?_⟩
  · intro χ I hI hi t
    rw [ht χ I hI t]
    rcases hi with hi|hi
    · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
    · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]
  · intro t S β R rows W K hK n hne χ
    have hne':physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n≠0:=by
      rwa [←physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
    obtain ⟨w,_,hwc⟩:=physicalBlock_nonzero_common η t S β C D hC hD hCD U R
      (liveRows C D U R rows) (fun z hz=>(liveRows_geometry C D U R rows z hz).2.1)
      W K hK n hne'
    obtain ⟨hN,hwidth⟩:=hrest χ hD hCD (nonunitFrequencyGenerator C D U*w) hwc
    refine ⟨hN,?_⟩
    intro Z hZ z hz
    exact (hwidth Z R hZ z (liveRows_weight C D U R rows z hz)).2.2.2.2.2

namespace Family
variable {η:Character} {C D:Ideal O} {hC:Supported C} {hD:Supported D}
  {U:Finset (CommonIndex C D)} {τ:RayCharacter→Character}

theorem nonexceptional_iff (h:Family η C D hC hD U τ) (χ:RayCharacter)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      z≠0 ∧ ¬FixedInducingRow (τ χ) Q fixedBadMask 1 z :=
  actual_nonexceptional_iff η (τ χ) χ C D hC U (h.element_eq χ) Q m z hm hml hm2

theorem inducing_iff (h:Family η C D hC hD U τ) (χ:RayCharacter)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      FixedInducingRow (τ χ) Q fixedBadMask 1 z :=
  actual_reduced_inducing_iff η (τ χ) χ C D hC U (h.element_eq χ) Q m z hm hz hml hm2

theorem paired_inducing_iff (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O) (hQ:Q≤Ideal.span {(72:O)}) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (τ χ) Q fixedBadMask 1 z ↔
      FixedInducingRow (τ ξ) Q fixedBadMask 1 (-z) :=
  (h.inducing_iff χ Q m z hm hz hml hm2).symm.trans
    ((CenteredMomentExceptionalReflection.fixedInducingRow_reflection_iff η χ ξ Q hQ m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z hml hm2).trans
      (h.inducing_iff ξ Q m (-z) hm (neg_ne_zero.mpr hz) hml hm2))

theorem both_inducing (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O) (hQ:Q≤Ideal.span {(72:O)}) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m)
    (hex:FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) :
    FixedInducingRow (τ χ) Q fixedBadMask 1 z ∧
      FixedInducingRow (reflected (τ ξ)) Q fixedBadMask 1 z := by
  have hleft := (h.inducing_iff χ Q m z hm hz hml hm2).mp hex
  refine ⟨hleft,?_⟩
  exact (reflected_inducing (τ ξ) Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp
    ((h.paired_inducing_iff χ ξ Q hQ m z hm hz hml hm2).mp hleft)

theorem reflected_height_eq (h:Family η C D hC hD U τ) (ξ:RayCharacter)
    (I:Ideal O)(hI:Supported I)(hi:IsCoprime C I ∨ IsCoprime D I)(t:ℝ) :
    heightCoeff (reflected (τ ξ)) t I=heightCoeff η t I*
      idealRowHom (-(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)) I*
      rayCharacter ξ (primaryGenerator I) := by
  have hneg : idealRowHom (-(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)) I=
      idealRowHom (-1) I*idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I := by
    rw [show -(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)=
      (-1)*(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) by ring]
    exact idealRowHom_argument_mul _ _ _
  rw [reflected_height _ _ _ hI,h.height_eq ξ I hI hi t,hneg]
  ring

theorem live_both_inducing (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O)(hQ:Q≤Ideal.span {(72:O)})(m z:O)(hm:m≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)
    (radius:ℝ)(rows:Finset O)(hz:z∈liveRows C D U radius rows)
    (hex:FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) :
    z≠0 ∧ FixedInducingRow (τ χ) Q fixedBadMask 1 z ∧
      FixedInducingRow (reflected (τ ξ)) Q fixedBadMask 1 z := by
  have hz0 := (liveRows_geometry C D U radius rows z hz).2.1
  exact ⟨hz0,h.both_inducing χ ξ Q hQ m z hm hz0 hml hm2 hex⟩

theorem physical_conductor_bounds (h:Family η C D hC hD U τ)
    (hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)(χ:RayCharacter) :
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*C.absNorm ∧
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*D.absNorm := by
  have hN := (h.physical_budget t S β R rows W K hK n hne χ).1
  obtain ⟨h₁,h₂⟩ := selected_nonunit_norm C D hC hD hCD U
  constructor
  · exact hN.trans <| by
      simpa only [mul_assoc] using (Nat.mul_le_mul_left (η.modulus.absNorm*fixedFactor) h₁)
  · exact hN.trans <| by
      simpa only [mul_assoc] using (Nat.mul_le_mul_left (η.modulus.absNorm*fixedFactor) h₂)

end Family

def expandedConductor (τ:Character)(R C:Ideal O)(z:O):ℕ :=
  τ.modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
    (R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm

def expandedFactor (η:Character):ℕ :=
  1296*η.modulus.absNorm*fixedFactor*(Ideal.span {fixedBadMask}).absNorm*
    (Ideal.span {(72:O)}).absNorm

theorem expanded_conductor_bounds {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (χ ξ:RayCharacter)(R:Ideal O)(z:O) :
    expandedConductor (τ χ) R C z≤
      expandedFactor η*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm ∧
    expandedConductor (reflected (τ ξ)) R D z≤
      expandedFactor η*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm := by
  have hl := (h.physical_conductor_bounds hCD t S β radius rows W K hK n hne χ).2
  have hr := (h.physical_conductor_bounds hCD t S β radius rows W K hK n hne ξ).1
  have hl' : (τ χ).modulus.absNorm≤1296*(η.modulus.absNorm*fixedFactor*D.absNorm) := by
    exact hl.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  have hr' := (reflected_modulus_bound (τ ξ)).trans (Nat.mul_le_mul_left 1296 hr)
  constructor
  · calc
      expandedConductor (τ χ) R C z≤
        (1296*(η.modulus.absNorm*fixedFactor*D.absNorm))*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm := by
            unfold expandedConductor
            gcongr
      _=_ := by unfold expandedFactor;ring
  · calc
      expandedConductor (reflected (τ ξ)) R D z≤
        (1296*(η.modulus.absNorm*fixedFactor*C.absNorm))*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm := by
            unfold expandedConductor
            gcongr
      _=_ := by unfold expandedFactor;ring

theorem eventually_expanded_conductor_caps (η:Character)(ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(z:O)(c d r m:ℝ),
    (C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→(R.absNorm:ℝ)≤Z^r→normValue z≤Z^m→
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+ε) := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (expandedFactor η:ℝ)
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.1 he
  refine ⟨max 2 Z₀,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ C D hC hD hCD U τ h t S β radius rows W K hK n hne χ ξ R z c d r m hCN hDN hRN hzn
  have hZpos : 0<Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have hconstant := hZ₀ Z ((le_max_right _ _).trans hZ)
  have hproduct : (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm≤
      Z^(c+d+r+m+ε) := by
    calc
      _≤Z^ε*Z^r*Z^c*Z^d*Z^m := by
        change (Ideal.absNorm (Ideal.span {z}):ℝ)≤_ at hzn
        gcongr
      _=Z^(c+d+r+m+ε) := by
        rw [←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos]
        congr 1
        ring
  obtain ⟨hl,hr⟩ := expanded_conductor_bounds h hCD t S β radius rows W K hK n hne χ ξ R z
  constructor
  · exact (show (expandedConductor (τ χ) R C z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hl).trans hproduct
  · exact (show (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hr).trans hproduct

theorem live_norm_le_four_radius (C D:Ideal O)(U:Finset (CommonIndex C D))
    (radius:ℝ)(rows:Finset O)(z:O)(hz:z∈liveRows C D U radius rows) :
    normValue z≤4*radius := by
  obtain ⟨hr,hg,hv,_,_,hn,_⟩ := retained_geometry radius
    (commonFrequencyGenerator C D) (nonunitFrequencyGenerator C D U) z
    (liveRows_weight C D U radius rows z hz)
  have hG := normValue_ge_one _ hg
  have hV := normValue_ge_one _ hv
  have hprod : 1≤normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hG) (sub_nonneg.mpr hV)]
  exact hn.trans (div_le_self (by positivity) hprod)

theorem eventually_live_expanded_conductor_caps (η:Character)(ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(c d r m:ℝ),
    (C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→(R.absNorm:ℝ)≤Z^r→ radius≤Z^m→
    ∀z∈liveRows C D U radius rows,z≠0 ∧
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+ε) := by
  obtain ⟨Z₁,hZ₁,h₁⟩ := eventually_expanded_conductor_caps η (ε/2) (by positivity)
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<ε/2 by positivity))) (4:ℝ)
  obtain ⟨Z₂,h₂⟩ := Filter.eventually_atTop.1 he
  refine ⟨max Z₁ Z₂,hZ₁.trans_le (le_max_left _ _),?_⟩
  intro Z hZ C D hC hD hCD U τ h t S β radius rows W K hK n hne χ ξ R c d r m hCN hDN hRN hrad z hz
  have hZpos : 0<Z := zero_lt_one.trans (hZ₁.trans_le ((le_max_left _ _).trans hZ))
  have hfour := h₂ Z ((le_max_right _ _).trans hZ)
  have hfreq : normValue z≤Z^(m+ε/2) := by
    calc
      _≤4*radius := live_norm_le_four_radius C D U radius rows z hz
      _≤Z^(ε/2)*Z^m := mul_le_mul hfour hrad
        (liveRows_geometry C D U radius rows z hz).1.le (Real.rpow_nonneg hZpos.le _)
      _=Z^(m+ε/2) := by rw [←Real.rpow_add hZpos,add_comm]
  have hc := h₁ Z ((le_max_left _ _).trans hZ) C D hC hD hCD U τ h t S β radius rows W K hK
    n hne χ ξ R z c d r (m+ε/2) hCN hDN hRN hfreq
  have hexp : c+d+r+(m+ε/2)+ε/2=c+d+r+m+ε := by ring
  rw [hexp] at hc
  exact ⟨(liveRows_geometry C D U radius rows z hz).2.1,hc⟩

end SevenEighths.CenteredMomentSecondExceptionalFamily

end

end OAI

end Source835

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondDyadicRowSupport.lean; sha256: 9396fd4431fffacd5fbbdd712086717b359e74b3c139f88b4382089b11144f40 -/
section Source836
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondDyadicRowSupport
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
local notation "O"=>HeckeFamily.O

 def dyadicRows (rows:Finset O) (n:Fin 4→ℤ):Finset O:=
  rows.filter (fun z=>dyadicWeight (n 1) (normValue z)≠0)

 theorem mem_dyadicRows (rows:Finset O)(n:Fin 4→ℤ)(z:O):
    z∈dyadicRows rows n ↔ z∈rows ∧ dyadicWeight (n 1) (normValue z)≠0:=
  Finset.mem_filter

 theorem dyadicRows_subset (rows:Finset O)(n:Fin 4→ℤ):dyadicRows rows n⊆rows:=
  Finset.filter_subset _ _

 theorem dyadicRows_norm (rows:Finset O)(n:Fin 4→ℤ)(z:O)(hz:z∈dyadicRows rows n):
    dyadicScale (n 1)/4<normValue z ∧ normValue z<dyadicScale (n 1):=
  dyadicWeight_support (n 1) ((mem_dyadicRows rows n z).mp hz).2

 theorem dyadicRows_nonzero (rows:Finset O)(n:Fin 4→ℤ)(z:O)(hz:z∈dyadicRows rows n):z≠0:=by
  have hn:0<normValue z:=(div_pos (dyadicScale_pos (n 1)) (by norm_num)).trans
    (dyadicRows_norm rows n z hz).1
  intro he
  simp only [he,normValue_eq_embedding,map_zero,norm_zero,zero_pow (by decide : 2≠0)] at hn
  exact (lt_irrefl 0) hn

 theorem dyadicRows_power_cap (rows:Finset O)(n:Fin 4→ℤ)(Z:ℝ)(hZ:1<Z)
    (z:O)(hz:z∈dyadicRows rows n):
    (Ideal.absNorm (Ideal.span {z}):ℝ)≤Z^(Real.logb Z (dyadicScale (n 1))):=by
  rw [Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (dyadicScale_pos (n 1))]
  exact (dyadicRows_norm rows n z hz).2.le

 theorem physicalBlock_dyadic_rows (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (dyadicRows rows n) W K n:=by
  unfold physicalBlock dyadicRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hd:dyadicWeight (n 1) (normValue z)=0
  · simp only [hd,ne_eq,not_true_eq_false,mul_zero,zero_mul,
      Complex.ofReal_zero,Finset.sum_const_zero,ite_self]
  · simp only [hd,ne_eq,not_false_eq_true,ite_true]

 theorem dyadicRows_liveRows (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)
    (rows:Finset O)(n:Fin 4→ℤ):
    dyadicRows (liveRows C D U R rows) n=liveRows C D U R (dyadicRows rows n):=by
  ext z
  simp only [dyadicRows,liveRows,Finset.mem_filter]
  tauto

 theorem physicalBlock_live_dyadic_rows (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (dyadicRows (liveRows C D U R rows) n) W K n:=
  (physicalBlock_live_rows η t S β C D hC hD U R rows W K n).trans
    (physicalBlock_dyadic_rows η t S β C D hC hD U R _ W K n)

end SevenEighths.CenteredMomentSecondDyadicRowSupport

end

end OAI

end Source836

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondActualWidth.lean; sha256: 464991e23f1358e0857966baf9e0af3268c0b03134cf65a7ccd15f565d53f2ec -/
section Source837
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondActualWidth
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondRadicalBudget CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentSupport CenteredMomentDescentLedger
open CenteredMomentPartitionNorm CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem actual_common_log_ge_unit (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)≤Real.logb Z (normValue (commonFrequencyGenerator C D)) := by
  have hh:=common_log_ge_unit (commonPrime C D) (commonPrime_supported C D hC)
    (leftExponent C D) (rightExponent C D) (leftExponent_pos C D) (rightExponent_pos C D) U Z hZ
  rw [←commonFrequencyGenerator_span C D hC] at hh
  simpa only [unitIdeal,commonPrime_span C D hC,normValue] using hh

theorem actual_width_bound (η τ : Character) (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z Tsec Csec L ξ : ℝ)
    (hZ : 1<Z) (hCsec : 0<Csec) (hT : Tsec≤Csec*Z^L)
    (hτ : Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z (fixedFactor:ℝ)+Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ))
    (h : O) (hne : retainedWeight (frequencyRadius Tsec Z ξ)
      (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))≠0) :
    max 0 (L-Real.logb Z (normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))+
      frequencyLoss Z Csec ξ)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
      L+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z (fixedFactor:ℝ)+frequencyLoss Z Csec ξ-
        (Real.logb Z (normValue (commonFrequencyGenerator C D))-
          Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)) := by
  have hn:=actual_nonempty_width_of_weight Tsec Z Csec L ξ hZ hCsec hT _ h hne
  rw [max_eq_right hn]
  have hg := normValue_pos (commonFrequencyGenerator C D)
    (CenteredMomentSecondCanonicalFrequency.commonFrequencyGenerator_ne_zero C D hC)
  have hv := normValue_pos (nonunitFrequencyGenerator C D U)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  rw [normValue_mul,Real.logb_mul hg.ne' hv.ne']
  change _≤_
  change Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
    Real.logb Z (fixedFactor:ℝ)+Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
      Real.logb Z (normValue (nonunitFrequencyGenerator C D U)) at hτ
  linarith

theorem exists_actual_width_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ:Character,
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        CanonicalRowCompletion.idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD:Supported D),primeSupport C=primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      ∀Z Tsec Csec L ξ M σ:ℝ,1<Z → 0<Csec → Tsec≤Csec*Z^L →
      L+Real.logb Z (η.modulus.absNorm:ℝ)≤M-σ →
      ∀h:O,retainedWeight (frequencyRadius Tsec Z ξ)
        (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))≠0 →
      max 0 (L-Real.logb Z (normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))+
        frequencyLoss Z Csec ξ)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          M-σ+Real.logb Z (fixedFactor:ℝ)+frequencyLoss Z Csec ξ := by
  obtain ⟨τ,he,ht,hN⟩:=exists_second_log_budgeted_family η χ C D hC U
  refine ⟨τ,ht,?_⟩
  intro hD hCD w hw Z Tsec Csec L ξ M σ hZ hCs hT hnom h hh
  have hb:=actual_width_bound η τ C D hC U Z Tsec Csec L ξ hZ hCs hT
    (hN hD hCD w hw Z hZ) h hh
  have hg:=actual_common_log_ge_unit C D hC U Z hZ
  linarith

end SevenEighths.CenteredMomentSecondActualWidth

end

end OAI

end Source837

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondWidthDrop.lean; sha256: c54ec925d4b034f80203e0eb3a763177578d59d0fbb8f33cf107e9b44260d455 -/
section Source838
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondWidthDrop
open HeckeFamily CenteredMomentSecondActualWidth CenteredMomentSecondRadicalBudget
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
local notation "O" => HeckeFamily.O

def amplificationIncrement (η:Character) (Z H K M σ:ℝ) : ℝ :=
  max (2*Real.logb Z H-Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-M) 0+σ

def nominalLength (Z H K g:ℝ) : ℝ := 2*Real.logb Z H-Real.logb Z K-g

lemma physical_frequency_scale (Z H K g:ℝ) (hZ:1<Z) (hH:0<H) (hK:0<K) :
    H^2/(K*Z^g)=Z^(nominalLength Z H K g) := by
  have hzg:0<Z^g:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hp:0<H^2/(K*Z^g):=div_pos (sq_pos_of_pos hH) (mul_pos hK hzg)
  have he:Real.logb Z (H^2/(K*Z^g))=nominalLength Z H K g := by
    rw [Real.logb_div (sq_pos_of_pos hH).ne' (mul_pos hK hzg).ne',Real.logb_pow,
      Real.logb_mul hK.ne' hzg.ne',Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)]
    unfold nominalLength
    norm_num
    ring
  rw [←he,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) hp]

lemma actual_nominal_drop (η:Character) (Z H K M σ:ℝ) :
    nominalLength Z H K (amplificationIncrement η Z H K M σ)+
      Real.logb Z (η.modulus.absNorm:ℝ)≤M-σ := by
  have hh:=le_max_left (2*Real.logb Z H-Real.logb Z K+
    Real.logb Z (η.modulus.absNorm:ℝ)-M) 0
  unfold nominalLength amplificationIncrement
  linarith

theorem exists_physical_width_family (η:Character) (χ:RayCharacter)
    (C D:Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D)) :
    ∃τ:Character,
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        CanonicalRowCompletion.idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD:Supported D),CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      ∀Z H K Tsec Csec ξ M σ g:ℝ,1<Z → 0<H → 0<K → 0<Csec →
      amplificationIncrement η Z H K M σ≤g →
      Tsec≤Csec*(H^2/(K*Z^g)) →
      ∀h:O,retainedWeight (frequencyRadius Tsec Z ξ)
        (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))≠0 →
      max 0 (nominalLength Z H K g-
        Real.logb Z (normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))+
        frequencyLoss Z Csec ξ)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          M-σ+Real.logb Z (fixedFactor:ℝ)+frequencyLoss Z Csec ξ := by
  obtain ⟨τ,hτ,hw⟩:=exists_actual_width_family η χ C D hC U
  refine ⟨τ,hτ,?_⟩
  intro hD hCD w hn Z H K Tsec Csec ξ M σ g hZ hH hK hCs hg hscale h hret
  apply hw hD hCD w hn Z Tsec Csec (nominalLength Z H K g) ξ M σ hZ hCs
  · rwa [←physical_frequency_scale Z H K g hZ hH hK]
  · have hh:=actual_nominal_drop η Z H K M σ
    unfold nominalLength at hh ⊢
    linarith
  · exact hret

end SevenEighths.CenteredMomentSecondWidthDrop

end

end OAI

end Source838

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondChildRadialWidth.lean; sha256: f77e9340e2f881c350255e3015e88b32a791dc328bd972e23163e7735719f9bb -/
section Source839
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondChildRadialWidth
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondDyadicRowSupport CenteredMomentSectorLocalization
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRadicalBudget
open CenteredMomentSecondActualWidth CenteredMomentSecondWidthDrop
local notation "O" => HeckeFamily.O

theorem physicalBlock_live_dyadic_witness (η:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z:O,z∈liveRows C D U R rows ∧ z∈dyadicRows rows n ∧
      z≠0 ∧ dyadicScale (n 1)<4*normValue z := by
  rw [physicalBlock_live_dyadic_rows η t S β C D hC hD U R rows W K n] at hne
  unfold physicalBlock at hne
  obtain ⟨z,hz,_⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hl,hd⟩:=(mem_dyadicRows _ n z).mp hz
  have hz':z∈dyadicRows rows n:=(mem_dyadicRows rows n z).mpr
    ⟨(Finset.mem_filter.mp hl).1,hd⟩
  exact ⟨z,hl,hz',dyadicRows_nonzero rows n z hz',by
    have hh:=(dyadicRows_norm rows n z hz').1
    linarith⟩

section Family
variable {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
  {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
  (h:Family η C D hC hD U τ)
  (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
  (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
  (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)

include h hK hne

theorem dyadic_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*(fixedFactor:ℝ)) := by
  obtain ⟨z,hzl,_,hz0,hscale⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U R rows W K n hne
  have hw:=(h.physical_budget t S β R rows W K hK n hne χ).2 Z hZ z hzl
  have hh:=Real.logb_le_logb_of_le hZ (dyadicScale_pos (n 1)) hscale.le
  rw [Real.logb_mul (by norm_num : (4:ℝ)≠0) (normValue_pos z hz0).ne'] at hh
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*(fixedFactor:ℝ))=
      Real.logb Z (4:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul (by norm_num : (4:ℝ)≠0) (by positivity : 4*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [hf]
  linarith

omit h hK hne in

theorem radial_support_bound (Φ:ℝ→ℂ)(b:ℝ)
    (hs:Function.support Φ⊆Set.Iic b)(y:O)
    (hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y≤b*dyadicScale (n 1) :=
  (div_le_iff₀ (dyadicScale_pos (n 1))).mp (hs hy)

theorem radial_radius_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)(b:ℝ)(hb:0<b) :
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hh:=dyadic_log_budget h t S β R rows W K hK n hne Z hZ χ
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*(fixedFactor:ℝ))=
      Real.logb Z b+Real.logb Z (16*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hb.ne' (by positivity : 16*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [Real.logb_mul hb.ne' (dyadicScale_pos (n 1)).ne',hf]
  linarith

theorem radial_point_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (normValue y)+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hl:=Real.logb_le_logb_of_le hZ (normValue_pos y hy0)
    (radial_support_bound n Φ b hs y hy)
  have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb
  linarith

theorem declared_radial_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hbH:1≤b*dyadicScale (n 1):=(normValue_ge_one y hy0).trans
    (radial_support_bound n Φ b hs y hy)
  rw [max_eq_right hbH]
  exact radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb

theorem whole_radial_norm_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ))) := by
  have hτ:(0:ℝ)<(τ χ).modulus.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (τ χ).modulus_ne_bot)
  have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb
  rw [←Real.logb_mul (mul_pos hb (dyadicScale_pos (n 1))).ne' hτ.ne'] at hh
  exact (mul_le_mul_of_nonneg_right (radial_support_bound n Φ b hs y hy) hτ.le).trans
    ((Real.logb_le_iff_le_rpow hZ (mul_pos (mul_pos hb (dyadicScale_pos (n 1))) hτ)).mp hh)

end Family

theorem fixed_radial_cost_eventually (b ε:ℝ)(hb:0<b)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→Real.logb Z (16*b*(fixedFactor:ℝ))≤ε := by
  have he:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (16*b*(fixedFactor:ℝ))
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.1 (he.and (Filter.eventually_gt_atTop (1:ℝ)))
  refine ⟨max 2 Z₀,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ
  obtain ⟨hc,hZ1⟩:=hZ₀ Z ((le_max_right _ _).trans hZ)
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  exact (Real.logb_le_iff_le_rpow hZ1 (by positivity)).mpr hc

theorem eventually_whole_radial_width (b ε:ℝ)(hb:0<b)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→
    ∀(η:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
      (U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U R rows W K n≠0→
    ∀(χ:RayCharacter)(Φ:ℝ→ℂ),Function.support Φ⊆Set.Iic b→
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε ∧
    ∀y:O,Φ (normValue y/dyadicScale (n 1))≠0→
      normValue y*((τ χ).modulus.absNorm:ℝ)≤
        Z^(Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
          Real.logb Z (normValue (commonFrequencyGenerator C D))+
          Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε) := by
  obtain ⟨Z₀,hZ₀,hcost⟩:=fixed_radial_cost_eventually b ε hb hε
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ η C D hC hD U τ h t S β R rows W K hK n hne χ Φ hs
  have hZ1:=hZ₀.trans_le hZ
  have hc:=hcost Z hZ
  constructor
  · have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ1 χ b hb
    linarith
  · intro y hy
    exact (whole_radial_norm_budget h t S β R rows W K hK n hne Z hZ1 χ Φ b hb hs y hy).trans
      (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))

theorem physical_declared_radial_width_drop {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H K Tsec Csec ξ M σ g:ℝ)(hZ:1<Z)(hH:0<H)(hK:0<K)
    (hT:0<Tsec)(hCs:0<Csec)
    (hg:amplificationIncrement η Z H K M σ≤g)
    (hscale:Tsec≤Csec*(H^2/(K*Z^g))) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ)
      rows W (K*Z^g) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      M-σ+ξ/2+Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hKg:0<K*Z^g:=mul_pos hK (Real.rpow_pos_of_pos hz _)
  have hw:=declared_radial_log_budget h t S β (frequencyRadius Tsec Z ξ) rows W
    (K*Z^g) hKg n hne Z hZ χ Φ b hb hs y hy0 hy
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hn:nominalLength Z H K g+Real.logb Z (η.modulus.absNorm:ℝ)≤M-σ := by
    have hnom:=actual_nominal_drop η Z H K M σ
    unfold nominalLength at hnom ⊢
    linarith
  rw [physical_frequency_scale Z H K g hZ hH hK] at hscale
  have hl:=Real.logb_le_logb_of_le hZ hT hscale
  rw [Real.logb_mul hCs.ne' (Real.rpow_pos_of_pos hz _).ne',
    Real.logb_rpow hz hZ.ne'] at hl
  have hr:Real.logb Z (frequencyRadius Tsec Z ξ)≤
      nominalLength Z H K g+ξ/2+Real.logb Z Csec := by
    rw [frequencyRadius,Real.logb_mul hT.ne' (Real.rpow_pos_of_pos hz _).ne',
      Real.logb_rpow hz hZ.ne']
    linarith
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*Csec*(fixedFactor:ℝ))=
      Real.logb Z Csec+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hCs.ne' (by positivity : 16*b*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [hf]
  linarith

end SevenEighths.CenteredMomentSecondChildRadialWidth

end

end OAI

end Source839
