import OpenAIGrouped.Unit041
import OpenAIGrouped.Unit039
import OpenAIGrouped.Unit040
import OpenAIGrouped.Unit038
import OpenAIGrouped.Unit007
import OpenAIGrouped.Unit035
import OpenAIGrouped.Unit033
import OpenAIGrouped.Unit009

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalActiveReflection.lean; sha256: 83f88188c824395ae882fa5147b29c93af9e6c1e035051d4bbef08880fa37d3a -/
section Source1680
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem actual_marked_active_reflection
    (hS : ∀ p : ∀ i,L i,Pairwise (Function.onFun IsCoprime (slotChoiceFamily L hmax hgood p).ideal))
    (hSodd : ∀ p : ∀ i,L i,∀ i,ringChar (Eis⧸(slotChoiceFamily L hmax hgood p).ideal i)≠2)
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h,(9:Eis)*(G h).c0∣N)
    (hNp : ∀ p : ∀ i,L i,∀ i,IsCoprime (Ideal.span {N}) ((markedRowFamily D (slotChoiceFamily L hmax hgood p) Q).ideal i))
    (C : ∀ h : Eis⧸Ideal.span {c},
      ∀ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ,
      ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected
          (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
          (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (w : ∀ i,L i→ℂ) (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    (∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (slotChoiceFamily L hmax hgood p).ideal i∣A then (1:ℂ) else 0))=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
      ∑ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
        frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
        ∑ T : Finset σ,
          ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
            ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
            (rowResidualPart I (Ideal.span {m}*F)),
            ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
              ∑ a : supportedSlotChoices (fun i : T => L i.val)
                ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
                (rowResidualPart I (Ideal.span {m}*F)),
                (∏ i : T,w i.val (a.val i))*
                  originalSplitPhysical R I F (Q*Ideal.span {(72:Eis)}) hbad L hmax hgood
                    ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
                    T (C h A T) (G h).shape (G h).denominator_ne_zero
                    (fun b : A => completedLocalExponent R F b.val.val) W X (b,a) := by
  let Call := fun (p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L)
    (h : Eis⧸Ideal.span {c})
    (A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}))) (T : Finset σ) =>
      originalSplitControlled D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood
        ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A) T (C h A T) p
  rw [actual_marked_slot_split_reflection D R I F Q hR hI hF hm hf hz hbad hcop hpow hmask
    L hmax hgood hS hSodd Ψ hΨnorm hQ hΨperiod hmLam hm2 c hc hcQ G N hN hNp Call
    w W hWcompact lo hi hlo hsupp hW X hX]
  dsimp only
  apply congrArg (fun z : ℂ => thetaDerivativeScalar⁻¹*z)
  apply Finset.sum_congr rfl
  intro h hh
  apply congrArg (fun z : ℂ => fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*z)
  apply Finset.sum_congr rfl
  intro A hA
  apply congrArg (fun z : ℂ => frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*z)
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro b hb
  apply congrArg (fun z : ℂ =>
    ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*z)
  apply Finset.sum_congr rfl
  intro a ha
  apply congrArg (fun z : ℂ => (∏ i : T,w i.val (a.val i))*z)
  dsimp only [Call]
  have hv := originalSplitControlled_physical D R I F (Q*Ideal.span {(72:Eis)})
    hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood
    ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A) T (C h A T)
    ((originalSlotSplit D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a))
    (G h).shape (G h).denominator_ne_zero (fun b : A => completedLocalExponent R F b.val.val) W X
  exact hv.trans (congrArg
    (originalSplitPhysical R I F (Q*Ideal.span {(72:Eis)}) hbad L hmax hgood
      ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A) T (C h A T)
      (G h).shape (G h).denominator_ne_zero (fun b : A => completedLocalExponent R F b.val.val) W X)
    ((originalSlotSplit D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).apply_symm_apply (b,a)))

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1680

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CompletedFiberSource.lean; sha256: 2d62873a79aed266ba71dac61e92d7f486169e5a85cf2739ed7a4619153734cd -/
section Source1681
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (parents : Finset (Ideal Eis)) (J F : Ideal Eis) (hJ : J≠0) (hF : Squarefree F)
    (m : Eis) (hm : m≠0) (hparents : ∀ I∈parents,I≠0) (v : Eisˣ)
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)

def residualOriginalData (K : originalResidualRows parents J (Ideal.span {m}*F)) :
    GoodMaskRowData m (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J (Ideal.span {m}*F) K.val)) :=
  fiberGoodMaskRowData parents J F m hm hF.ne_zero hparents v
    ⟨reconstructFiberRow J (Ideal.span {m}*F) K.val,
      (originalResidualRows_reconstruct parents J (Ideal.span {m}*F) hparents K.val K.property).1⟩

variable (Q : Ideal Eis) (hQ : Q≠0) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (hcop : ∀ K∈originalResidualRows parents J (Ideal.span {m}*F),IsCoprime (Q*Ideal.span {(72:Eis)}) K)
    (lists : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
    (hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
    (hodd : ∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2)
    (hperiod : ∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P)

abbrev originalResidualAdmissible : ∀ K∈originalResidualRows parents J (Ideal.span {m}*F),Admissible K := by
  intro K hK
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  exact rowResidualPart_admissible I _ hbad

variable (D : ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
    ∀ T : Finset σ,OriginalSplitCompletion (N:=(9:Eis)*c) (a:=(G h).a0) (c:=(G h).c0) (mode:=(G h).mode)
      ((poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
      (poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal
      (originalResidualRows parents J (Ideal.span {m}*F)) (originalResidualAdmissible parents J F m hbad)
      lists hmax hgood T)

include hJ hQ hcQ hcop hdis hodd hperiod

theorem original_completed_residual_source
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W) (lo hi : ℝ) (hlo : 0<lo)
    (hsupp : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X)
    (w : ∀ i,lists i→ℂ) (K : originalResidualRows parents J (Ideal.span {m}*F)) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (v.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J (Ideal.span {m}*F) K.val))) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},
      fixedThetaRowCoeff c hc ((residualOriginalData parents J F hF m hm hparents v K).fixedFactor Ψ Q) h*
        ∑ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
          frozenInactiveWeight J F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
          ∑ T : Finset σ,originalInactivePhysical
            ((poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
            (poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal
            (originalResidualRows parents J (Ideal.span {m}*F)) (originalResidualAdmissible parents J F m hbad)
            lists hmax hgood T (D h A T) (G h).shape (G h).denominator_ne_zero
            (fun b : A => completedLocalExponent J F b.val.val) W X w K := by
  rcases K with ⟨K,hK⟩
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  have hI0 := hparents I (Finset.mem_filter.mp hI).1
  have hrec := reconstructFiberRow_of_original parents J (Ideal.span {m}*F) I hI hI0
  obtain ⟨hIp,hpow,hmask⟩ := Finset.mem_filter.mp hI
  let K : originalResidualRows parents J (Ideal.span {m}*F) :=
    ⟨rowResidualPart I (Ideal.span {m}*F),Finset.mem_image.mpr ⟨I,Finset.mem_filter.mpr ⟨hIp,hpow,hmask⟩,rfl⟩⟩
  let D0 := residualOriginalData parents J F hF m hm hparents v K
  have hz : Ideal.span {v.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J (Ideal.span {m}*F) K.val)}=I := by
    rw [Ideal.span_singleton_mul_left_unit v.isUnit,ConcretePrimeRowBridge.span_idealGenerator]
    exact hrec
  have hS : ∀ p : ∀ i,lists i,Pairwise (Function.onFun IsCoprime (slotChoiceFamily lists hmax hgood p).ideal) := by
    intro p i j hij
    apply Ideal.isCoprime_of_isMaximal
    intro he
    change (p i).val=(p j).val at he
    exact Finset.disjoint_left.mp (hdis hij) (p i).property (he.symm ▸ (p j).property)
  have he := actual_marked_active_reflection D0 J I F Q hJ hI0 hF hm
    (ConcretePrimeRowBridge.span_idealGenerator F) hz hbad
    (hcop K.val K.property) hpow.symm hmask.symm lists hmax hgood hS
    (fun p i => hodd i _ (p i).property) Ψ hΨnorm hQ hΨperiod hmLam hm2 c hc hcQ.le G ((9:Eis)*c)
    (fun h => mul_dvd_mul_left (9:Eis) (G h).denominator_dvd)
    (fun p => markedRowFamily_period D0 (slotChoiceFamily lists hmax hgood p) Q
      (fun i => hperiod i _ (p i).property) c hcQ)
    (fun h A T b p => D h A T K b p)
    w W hWcompact lo hi hlo hsupp hW X hX
  exact he
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1681

/- Original source: OAI/NumberTheory/DirichletL/Reflection/TupleSectors.lean; sha256: 9d0e54babc0d390bc779b9feb2cf0a7f4928cc43c88459d659ec5e3416982beb -/
section Source1682
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ]

lemma tuplePrimeFamily_pairwise (L : σ→Finset (Ideal Eis))
    (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hT : ∀ p∈tuples, ∀ i, p i∈L i)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i) (P : Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (tuplePrimeFamily tuples hne hmax hgood P).ideal) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  intro he
  have hp := tupleRepresentative_mem tuples hne P
  change tupleRepresentative tuples hne P i=tupleRepresentative tuples hne P j at he
  exact Finset.disjoint_left.mp (hL hij) (hT _ hp i) (he.symm ▸ hT _ hp j)

omit [Fintype φ] in
lemma tuplePrimeFamily_sum_pairwise (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (L : σ→Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hT : ∀ p∈tuples, ∀ i, p i∈L i)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i)
    (hfixed : ∀ p∈tuples, ∀ f i, p i≠F.ideal f) (P : Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (F.sum (tuplePrimeFamily tuples hne hmax hgood P)).ideal) := by
  intro i j hij
  cases i with
  | inl f => cases j with
    | inl g => exact hF (fun h => hij (congrArg Sum.inl h))
    | inr t =>
      apply Ideal.isCoprime_of_isMaximal
      exact (hfixed _ (tupleRepresentative_mem tuples hne P) f t).symm
  | inr t => cases j with
    | inl f =>
      apply Ideal.isCoprime_of_isMaximal
      exact hfixed _ (tupleRepresentative_mem tuples hne P) f t
    | inr u => exact tuplePrimeFamily_pairwise L hL tuples hne hT hmax hgood P (fun h => hij (congrArg Sum.inr h))

theorem exists_tuple_sector_arithmetic (F : PrimeFamily φ)
    (L : σ→Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hT : ∀ p∈tuples, ∀ i, p i∈L i)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i)
    (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows, Admissible K)
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c≠0) (hN : (9:Eis)*c∣N)
    (hbase : if mode then λ₀^2∣a-1 else λ₀^2∣c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K∈rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hfixed : ∀ p∈tuples, ∀ f i, p i≠F.ideal f)
    (hperiod : ∀ p∈tuples, ∀ i, IsCoprime (Ideal.span {N}) (p i))
    (rowClass slotClass : Eis⧸Ideal.span {N^2})
    (hrowClass : ∀ K∈rows, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=rowClass)
    (hslotClass : ∀ p∈tuples, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator (slotTupleProduct p))=slotClass) :
    ∃ E : ∀ x : SourcePair rows (tuples.image slotTupleProduct),
      ControlledStratumArithmetic
        (F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property)
          (tuplePrimeFamily tuples hne hmax hgood x.val.2.val)).generator N a c mode,
      ∀ x0 x, (E x).fixedFactor=(E x0).fixedFactor ∧
        ∀ u m n b, actualCuspColumn (E x) s hc u m n b=actualCuspColumn (E x0) s hc u m n b := by
  refine exists_fixed_ray_source_arithmetic F rows (tuples.image slotTupleProduct)
    (tuplePrimeFamily tuples hne hmax hgood) hrows
    (tuplePrimeFamily_product tuples hne hmax hgood) N a c mode s hc hN hbase hac hF hNF hrowcop ?_ ?_ rowClass slotClass hrowClass ?_
  · intro P hP
    exact tuplePrimeFamily_sum_pairwise F hF L hL tuples hne hT hmax hgood hfixed P
  · intro P hP i
    exact hperiod _ (tupleRepresentative_mem tuples hne P) i
  · intro P hP
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
    exact hslotClass p hp
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1682

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CellArithmetic.lean; sha256: aa59dbd1b2db9c63c6a924ea4dce56133d480a2bbc9fc2663d199d77da352325 -/
section Source1683
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma residual_level_coprime (K Q₀ : Ideal Eis) (hK : Admissible K)
    (c : Eis) (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) (hcop : IsCoprime Q₀ K) :
    IsCoprime (Ideal.span {(9:Eis)*c}) K := by
  rw [←PrimeFamily.residual_product K hK]
  apply IsCoprime.prod_right_iff.mpr
  intro i hi
  exact (PrimeFamily.residual K hK).level_coprime Q₀ c hc
    (fun i => hcop.of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK i)) i

lemma original_residual_completion_conditions (rows : Finset (Ideal Eis)) (J Q Q₀ : Ideal Eis)
    (hJ : J≠0) (hQ : Q≠0) (hrows : ∀ I∈rows,I≠0)
    (hbad : ∀ P∈fixedBadPrimes,P∣Q) (hperiod : Q₀∣Q)
    (A : Finset (FreeReflection.pool J Q Q₀)) (c : Eis)
    (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) :
    ∀ K∈originalResidualRows rows J Q,
      Admissible K ∧
      (∀ b : A,IsCoprime (((poolPrimeFamily J Q Q₀).restrict A).ideal b) K) ∧
      IsCoprime (Ideal.span {(9:Eis)*c}) K := by
  intro K hK
  obtain ⟨I,hI,he⟩ := Finset.mem_image.mp hK
  subst K
  obtain ⟨hi,hp,hm⟩ := Finset.mem_filter.mp hI
  have hk := rowResidualPart_admissible I Q hbad
  refine ⟨hk,?_,?_⟩
  · intro b
    exact poolPrimeFamily_fiber_row_coprime J I Q Q₀ hJ (hrows I hi) hQ hp.symm hm.symm b.val
  · apply residual_level_coprime _ Q₀ hk c hc
    exact (squarefreeResidualPart_coprime (rowSimplePart I) Q).symm.of_isCoprime_of_dvd_left hperiod

variable {φ σ : Type*} [Fintype σ] [DecidableEq σ]

theorem original_tuple_cell_conditions (Frozen : PrimeFamily φ)
    (hFrozen : Pairwise (Function.onFun IsCoprime Frozen.ideal))
    (L : σ→Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hsub : tuples⊆fixedSlotTupleSet L Frozen.ideal)
    (N : Eis) (hFN : ∀ b,IsCoprime (Ideal.span {N}) (Frozen.ideal b))
    (hFodd : ∀ b,ringChar (Eis⧸Frozen.ideal b)≠2)
    (hLN : ∀ i,∀ P∈L i,IsCoprime (Ideal.span {N}) P)
    (hLodd : ∀ i,∀ P∈L i,ringChar (Eis⧸P)≠2) :
    let S := tuplePrimeFamily tuples hne
      (fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1 i))
      (fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1 i))
    ∀ P∈tuples.image slotTupleProduct,
      (∏ i,(S P).ideal i)=P ∧
      Pairwise (Function.onFun IsCoprime (Frozen.sum (S P)).ideal) ∧
      (∀ b,IsCoprime (Ideal.span {N}) ((Frozen.sum (S P)).ideal b)) ∧
      (∀ b,ringChar (Eis⧸(Frozen.sum (S P)).ideal b)≠2) := by
  dsimp only
  let hm := fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1 i)
  let hg := fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1 i)
  have hs : ∀ p∈tuples,∀ i,p i∈L i := fun p hp => ((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1
  intro P hP
  refine ⟨tuplePrimeFamily_product tuples hne hm hg P hP,?_,?_,?_⟩
  · exact tuplePrimeFamily_sum_pairwise Frozen hFrozen L hL tuples hne hs hm hg
      (fun p hp => ((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).2) P
  · intro b
    cases b with
    | inl b => exact hFN b
    | inr b => exact hLN b _ (hs _ (tupleRepresentative_mem tuples hne P) b)
  · intro b
    cases b with
    | inl b => exact hFodd b
    | inr b => exact hLodd b _ (hs _ (tupleRepresentative_mem tuples hne P) b)

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1683

/- Original source: OAI/NumberTheory/DirichletL/Reflection/PuncturedMarks.lean; sha256: 23864d5cb76ed076dff385473ec44764e69c0f90297232a6863cef6627290afd -/
section Source1684
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma markedCompletedT_zero_punctured (Ψ : Eis→*ℂ) (m f z : Eis)
    (P : Ideal Eis) (hP : Prime P) (hm : m∈P)
    (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) (hd : ∀ A,¬P∣A → d A=0) :
    markedCompletedT (rowTwist Ψ m f z) W X d=0 := by
  have hz (I J : Ideal Eis) : summand (rowTwist Ψ m f z) W X I J*d (I*J^3)=0 := by
    by_cases hdiv : P∣I*J^3
    · rcases hP.dvd_mul.mp hdiv with hI|hJ
      · have hz := CanonicalRowCompletion.columnWeight_zero_of_mask Ψ m f z hP hI hm
        simp only [summand,hz,zero_div,zero_mul]
      · have hz := cubeWeight_zero_of_prime_mask Ψ m f z hP (hP.dvd_of_dvd_pow hJ) hm
        simp only [summand,hz,mul_zero,zero_mul]
    · rw [hd _ hdiv,mul_zero]
  simp only [markedCompletedT,hz,tsum_zero]

lemma markedCompletedT_zero_punctured_slot {σ : Type*} [Fintype σ]
    (S : PrimeFamily σ) (i : σ) (Ψ : Eis→*ℂ) (m f z : Eis) (hm : m∈S.ideal i)
    (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ j,if S.ideal j∣A then (1:ℂ) else 0)=0 := by
  apply markedCompletedT_zero_punctured Ψ m f z (S.ideal i)
    (Ideal.prime_of_isPrime (NeZero.ne (S.ideal i)) inferInstance) hm W X
  intro A hA
  exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1684

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalRetainedSlots.lean; sha256: c7d632dfe389b8a393596ffdc1d4d73f7d9a653a33770c3aa7507a26938cd2ee -/
section Source1685
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {α σ : Type*} [Fintype σ]

def punctureRetainedTuples (tuples : Finset α) (S : α→PrimeFamily σ) (m : Eis) : Finset α :=
  tuples.filter (fun p => ∀ i,m∉(S p).ideal i)

theorem original_tuple_filter_puncture (tuples : Finset α) (S : α→PrimeFamily σ)
    (w : α→ℂ) (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) :
    (∑ p∈tuples,w p*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (S p).ideal i∣A then (1:ℂ) else 0))=
    ∑ p∈punctureRetainedTuples tuples S m,w p*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (S p).ideal i∣A then (1:ℂ) else 0) := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpbad
  have hh : ¬∀ i,m∉(S p).ideal i := fun h => hpbad (Finset.mem_filter.mpr ⟨hp,h⟩)
  push Not at hh
  obtain ⟨i,hi⟩ := hh
  rw [markedCompletedT_zero_punctured_slot (S p) i Ψ m f z hi W X,mul_zero]

lemma retained_slot_period (tuples : Finset α) (S : α→PrimeFamily σ)
    (m : Eis) (Q : Ideal Eis) (hQ : Q∣Ideal.span {m})
    (p : α) (hp : p∈punctureRetainedTuples tuples S m) (i : σ) :
    IsCoprime Q ((S p).ideal i) := by
  apply (maximal_coprime_of_not_dvd _ _ ?_).symm
  intro h
  have hd := dvd_trans h hQ
  exact (Finset.mem_filter.mp hp).2 i ((Ideal.dvd_iff_le.mp hd) (Ideal.subset_span (by simp)))

lemma retained_markedRowFamily_period {m f z : Eis} (D : GoodMaskRowData m f z)
    (tuples : Finset α) (S : α→PrimeFamily σ) (Q : Ideal Eis) (c : Eis)
    (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (hpuncture : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (p : α) (hp : p∈punctureRetainedTuples tuples S m) :
    ∀ i,IsCoprime (Ideal.span {(9:Eis)*c}) ((markedRowFamily D (S p) Q).ideal i) := by
  exact markedRowFamily_period D (S p) Q
    (fun i => retained_slot_period tuples S m _ hpuncture p hp i) c hcQ

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1685

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CanonicalCellArithmetic.lean; sha256: f14e33fa05fae52b9e978349b06586f5515121e4f492c092a287667993e0a04c -/
section Source1686
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma canonical_retained_slot_not_excluded {α σ : Type*} [Fintype σ]
    (tuples : Finset α) (S : α→PrimeFamily σ) (q : ℕ) (m : Eis)
    (p : α) (hp : p∈punctureRetainedTuples tuples S (ActualFiber.maskElement q m)) (i : σ) :
    (S p).ideal i∉reflectionExcludedPrimes q := by
  intro hi
  have hm : ActualFiber.maskElement q m∈(S p).ideal i :=
    Ideal.mul_mem_left _ m (excludedGenerator_mem _ hi)
  exact (Finset.mem_filter.mp hp).2 i hm

lemma canonical_retained_slot_free_period {α σ : Type*} [Fintype σ]
    (tuples : Finset α) (S : α→PrimeFamily σ) (q : ℕ) (hq : q≠0) (m : Eis)
    (p : α) (hp : p∈punctureRetainedTuples tuples S (ActualFiber.maskElement q m)) (i : σ) :
    IsCoprime (ActualFiber.freeConductor q) ((S p).ideal i) := by
  have hc := reflectionConductor_coprime_of_not_excluded q hq ((S p).ideal i)
    (canonical_retained_slot_not_excluded tuples S q m p hp i)
  rw [reflectionConductor_ideal] at hc
  exact hc.of_isCoprime_of_dvd_left (dvd_mul_left _ (Ideal.span {(9:Eis)}))

lemma canonical_retained_marked_period {α σ : Type*} [Fintype σ]
    (q : ℕ) (hq : q≠0) (m f z : Eis) (D : GoodMaskRowData (ActualFiber.maskElement q m) f z)
    (tuples : Finset α) (S : α→PrimeFamily σ)
    (p : α) (hp : p∈punctureRetainedTuples tuples S (ActualFiber.maskElement q m)) :
    ∀ i,IsCoprime (Ideal.span {(9:Eis)*reflectionConductor q})
      ((markedRowFamily D (S p) (CanonicalCoefficientClass.fixedBaseConductor q)).ideal i) := by
  exact markedRowFamily_period D (S p) (CanonicalCoefficientClass.fixedBaseConductor q)
    (fun i => canonical_retained_slot_free_period tuples S q hq m p hp i)
    (reflectionConductor q) (reflectionConductor_ideal q)

theorem canonical_original_cell_conditions (q : ℕ) (hq : q≠0) (m : Eis) (hm : m≠0)
    (rows : Finset (Ideal Eis)) (J F : Ideal Eis) (hJ : J≠0) (hF : F≠0)
    (hrows : ∀ I∈rows,I≠0)
    (A : Finset (FreeReflection.pool J (ActualFiber.maskIdeal q m F) (ActualFiber.freeConductor q))) :
    ∀ K∈originalResidualRows rows J (ActualFiber.maskIdeal q m F),
      Admissible K ∧
      (∀ b : A,IsCoprime (((poolPrimeFamily J (ActualFiber.maskIdeal q m F)
        (ActualFiber.freeConductor q)).restrict A).ideal b) K) ∧
      IsCoprime (Ideal.span {(9:Eis)*reflectionConductor q}) K := by
  intro K hK
  obtain ⟨I,hI,he⟩ := Finset.mem_image.mp hK
  subst K
  obtain ⟨hi,hp,hmask⟩ := Finset.mem_filter.mp hI
  have hk := rowResidualPart_admissible I _ (ActualFiber.mask_bad q m F)
  refine ⟨hk,?_,?_⟩
  · intro b
    exact poolPrimeFamily_fiber_row_coprime J I _ _ hJ (hrows I hi)
      (ActualFiber.maskIdeal_ne_zero q m hm F hF) hp.symm hmask.symm b.val
  · exact residual_level_coprime _ (ActualFiber.freeConductor q) hk (reflectionConductor q)
      (reflectionConductor_ideal q) (residual_coprime_free_base q hq m F I)

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1686

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CompletedCanonicalEnergy.lean; sha256: 3f35018ad5a1574d8bc48ffd977fe47f7d70f5c1829f34a5a0a9bd8a1611a983 -/
section Source1687
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

lemma maximal_prime_level_coprime (P : Ideal Eis) (hP : P.IsMaximal)
    (hg : ConcretePrimeRowBridge.goodLambda∉P) (Q₀ : Ideal Eis) (c : Eis)
    (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) (hQ : IsCoprime Q₀ P) :
    IsCoprime (Ideal.span {(9:Eis)*c}) P := by
  let S : PrimeFamily Unit := ⟨fun _ => P,fun _ => hP,fun _ => hg⟩
  exact S.level_coprime Q₀ c hc (fun _ => hQ) ()

lemma original_powerful_norm_le (J : Ideal Eis) (hJ : J≠0) :
    (Ideal.absNorm (rowPowerfulPart J):ℝ)≤(Ideal.absNorm J:ℝ) := by
  have he := congrArg (fun I : Ideal Eis => (Ideal.absNorm I:ℝ)) (row_powerful_simple_product J hJ)
  simp only [map_mul,Nat.cast_mul] at he
  have hs := QuadraticMainBoundary.norm_one_le (rowSimplePart_ne_zero J)
  have hp : (0:ℝ)≤Ideal.absNorm (rowPowerfulPart J) := Nat.cast_nonneg _
  nlinarith

theorem canonical_completed_fiber_energy (q : ℕ) (hq : q≠0)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η)
    (hη1 : η≤1) (hηc : η≤cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F : Ideal Eis) (_hJ : J≠0) (_hF : Squarefree F)
      (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm J:ℝ)≤Z^M → (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
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
      (∑ I∈representativeRowFiber parents J (ActualFiber.maskIdeal q m F),
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/16)*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ)) := by
  let Q := CanonicalCoefficientClass.fixedBaseConductor q
  have hQ : Q≠0 := CanonicalCoefficientClass.fixedBaseConductor_ne_zero q hq
  let c := reflectionConductor q
  have hc : c≠0 := reflectionConductor_ne_zero q hq
  let : Finite (Eis⧸Ideal.span {c}) := ConcreteTraceCRT.finite_quotient_span hc
  let : Fintype (Eis⧸Ideal.span {c}) := Fintype.ofFinite _
  let : Finite (Eis⧸Ideal.span {((9:Eis)*c)^2}) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero 2 (mul_ne_zero (by norm_num) hc))
  let : Fintype (Eis⧸Ideal.span {((9:Eis)*c)^2}) := Fintype.ofFinite _
  let b := excludedGenerator (reflectionExcludedPrimes q)
  let B : Ideal Eis := Ideal.span {b}
  have hb : b≠0 := reflectionExcludedGenerator_ne_zero q
  have hB : B≠0 := Ideal.span_singleton_eq_bot.not.mpr hb
  let E := fixedFourierGeometry c hc
  have hEc : ∀ h,(E h).c0≠0 := fun h => (E h).denominator_ne_zero
  have hEN : ∀ h,(9:Eis)*(E h).c0∣(9:Eis)*c := fun h => mul_dvd_mul_left (9:Eis) (E h).denominator_dvd
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_original_frozen_energy
    (fun h => (E h).a0) (fun h => (E h).c0) (fun h => (E h).mode) lo hi hlo W hWs hW
    (fun h => (E h).shape) hEc hEN (fun h => (E h).primary) (fun h => (E h).coprime)
    B hB L cstar η hL hcstar hη hη1 hηc rmax
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ J F hJ hF m hm Z N V M z₀ margin hhat d hZ hN hM hMc hVc hzc hhc
    hJn hFn hRn hinv hmargin hVd hhd hd parents hparents hcard lists H hdis hmax hgood hprime hodd hexcluded
    hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let mfull := ActualFiber.maskElement q m
  have hmfull : mfull≠0 := ActualFiber.maskElement_ne_zero q m hm
  let mask := Ideal.span {mfull}*F
  let Q₀ := Q*Ideal.span {(72:Eis)}
  have hmask : mask=B*F*Ideal.span {m} := by
    dsimp only [mask,mfull,ActualFiber.maskElement,B,b]
    rw [←Ideal.span_singleton_mul_span_singleton]
    ring
  have hmask0 : mask≠0 := mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hmfull) hF.ne_zero
  have hbad : ∀ P∈fixedBadPrimes,P∣mask := ActualFiber.mask_bad q m F
  let rows := originalResidualRows parents J mask
  have hparents0 : ∀ I∈parents,I≠0 := fun I hI => (hparents I hI).1
  let hrows : ∀ K∈rows,Admissible K := originalResidualAdmissible parents J F mfull hbad
  have hcop : ∀ K∈rows,IsCoprime Q₀ K := by
    intro K hK
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
    exact residual_coprime_free_base q hq m F I
  have hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀ := reflectionConductor_ideal q
  have hGN : ∀ f,IsCoprime (Ideal.span {(9:Eis)*c}) ((poolPrimeFamily J mask Q₀).ideal f) :=
    (poolPrimeFamily J mask Q₀).level_coprime Q₀ c hcQ (poolPrimeFamily_period J mask Q₀)
  have hrowcop : ∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J mask Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {(9:Eis)*c}) K := by
    intro K hK
    refine ⟨?_,residual_level_coprime K Q₀ (hrows K hK) c hcQ (hcop K hK)⟩
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨hIp,hpow,hmask'⟩ := Finset.mem_filter.mp hI
    exact poolPrimeFamily_fiber_row_coprime J I mask Q₀ hJ (hparents0 I hIp) hmask0 hpow.symm hmask'.symm
  have hLP : ∀ i,∀ P∈lists i,IsCoprime Q₀ P := by
    intro i P hP
    let : P.IsMaximal := hmax i P hP
    have hh := reflectionConductor_coprime_of_not_excluded q hq P (hexcluded i P hP)
    rw [reflectionConductor_ideal] at hh
    exact hh.of_isCoprime_of_dvd_left (dvd_mul_left _ (Ideal.span {(9:Eis)}))
  have hLN : ∀ i,∀ P∈lists i,IsCoprime (Ideal.span {(9:Eis)*c}) P :=
    fun i P hP => maximal_prime_level_coprime P (hmax i P hP) (hgood i P hP) Q₀ c hcQ (hLP i P hP)
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzp : 0<Z := lt_trans zero_lt_one hz
  let O := normWidth Z (rowPowerfulPart J)
  have hO : 0≤O := normWidth_nonneg Z hz _ (rowPowerfulPart_ne_zero J)
  have hPowPos : 0<(Ideal.absNorm (rowPowerfulPart J):ℝ) := by
    have := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
    linarith
  have hOM : O≤M := by
    have hh := Real.logb_le_logb_of_le hz hPowPos ((original_powerful_norm_le J hJ).trans hJn)
    rwa [Real.logb_rpow hzp (ne_of_gt hz)] at hh
  have hOn : Z^O≤(Ideal.absNorm (rowPowerfulPart J):ℝ) := by
    dsimp [O,normWidth]
    rw [Real.rpow_logb hzp (ne_of_gt hz) hPowPos]
  have ha := he (σ:=σ) J F (Ideal.span {m}) Q₀ hJ hF.ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm)
  rw [←hmask] at ha
  obtain ⟨D,hD⟩ := ha Z N V M z₀ margin O hhat d hZ hN hM hMc hVc hzc hhc
    hJn hFn hRn hO hOM hOn hinv hmargin hVd hhd hd parents rows hparents (Finset.Subset.refl _) hbad
    hcard lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN (poolPrimeFamily_odd J mask Q₀)
    hrowcop hLN hodd
  let scalar := fun h (K : rows) => fixedThetaRowCoeff c hc
    ((residualOriginalData parents J F hF mfull hmfull hparents0 u K).fixedFactor Ψ Q) h
  have hscalar : ∀ h K,‖scalar h K‖≤1 := fun h K =>
    (residualOriginalData parents J F hF mfull hmfull hparents0 u K).fixedCoefficient_norm Ψ Q hΨnorm c hc h
  have henergy := hD θ w scalar hw hscalar
  have hTw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) :=
    CanonicalRowCompletion.normTwistedSource_contDiff W lo hi hlo hWs hW θ
  have hTs := (CompletedHeight.normTwistedSource_support W θ).trans hWs
  have hTc : HasCompactSupport (CompletedHeight.normTwistedSource W θ) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => by
      by_contra hn
      exact hx (hTs hn))
  have hmLam : ConcretePrimeRowBridge.goodLambda∣mfull :=
    ((reflectionExcludedGenerator_bad q).1).trans (dvd_mul_left _ m)
  have hm2 : (2:Eis)∣mfull := ((reflectionExcludedGenerator_bad q).2).trans (dvd_mul_left _ m)
  have hid (K : rows) := original_completed_residual_source parents J F hJ hF mfull hmfull hparents0 u hbad
    Q hQ c hc hcQ E hcop lists hmax hgood hdis hodd hLP D Ψ hΨnorm hΨperiod hmLam hm2
    (CompletedHeight.normTwistedSource W θ) hTc lo hi hlo hTs hTw (Z^(N-3*hhat)) (Real.rpow_pos_of_pos hzp _) w K
  have hre := original_fiber_energy_reindex parents J (ActualFiber.maskIdeal q m F) hparents0
    (fun I => ∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ mfull (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator I))
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))
  rw [hre]
  have heq : (∑ K : rows,‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ mfull (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J mask K.val)))
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)=
      ∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ h,scalar h K*
        ∑ A : Finset (FreeReflection.pool J mask Q₀),frozenInactiveWeight J F mask Q₀ A*
          ∑ T : Finset σ,originalInactivePhysical ((poolPrimeFamily J mask Q₀).restrict A)
            (poolPrimeFamily J mask Q₀).ideal rows hrows lists hmax hgood T (D h A T) (E h).shape (E h).denominator_ne_zero
            (fun b : A => completedLocalExponent J F b.val.val)
            (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) w K‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    exact congrArg (fun z : ℂ => ‖z‖^2) (hid K)
  have hbound := heq.trans_le henergy
  have hp : Z^O=(Ideal.absNorm (rowPowerfulPart J):ℝ) := Real.rpow_logb hzp (ne_of_gt hz) hPowPos
  have hR : C*(1+‖θ‖)^degree*Z^(N+V-cstar/16-O/2)=
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/16)*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ)) := by
    rw [show N+V-cstar/16-O/2=(N+V-cstar/16)+O*(-(1/2:ℝ)) by ring,
      Real.rpow_add hzp,Real.rpow_mul hzp.le,hp]
    ring
  have hs := Finset.sum_coe_sort rows (fun K : Ideal Eis =>
    ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ mfull (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J mask K)))
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
  exact hs.symm.trans_le (hbound.trans_eq hR)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1687

/- Original source: OAI/NumberTheory/DirichletL/Reflection/LowFixedMember.lean; sha256: db4c0a89f2fe817bb22b1eaf32829a5a72becd3702c1c8384b06c3e9d2a712a6 -/
section Source1688
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem low_fixed_member_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J I F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z d ell0 shift O₀ QK QP : ℝ),
      Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart I) →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      QK/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      1≤QK → QK≤2*Ck*Z^(5/6-2*d) → 2≤QP → QP/2≤Z^ell0 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ (Z^(1+ell0+shift)) r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+504*η-O₀/2) := by
  let ε := η/(200*(1+η))
  have hε : 0<ε := (low_reflection_parameters η hη).1
  obtain ⟨degree,C,Z₁,hC,hZ₁,he⟩ := original_low_member_geometry_uniform a c₀ mode
    ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac (η/8) (by positivity) η hη
    η (η/2) 57 8 hη (by positivity) (by norm_num) 8 2 (by positivity)
  obtain ⟨Z₂,hZ₂,hscale⟩ := geometry_source_scale_cap a c₀ mode s
  obtain ⟨Z₃,hZ₃,hlogQ⟩ := constant_log_error (Ideal.absNorm Q:ℝ) η (actual_ideal_norm_pos Q hQ) hη
  obtain ⟨Z₄,hZ₄,hlogC⟩ := constant_log_error (2*Ck) η (by positivity) hη
  obtain ⟨Z₅,hZ₅,hlog16⟩ := constant_log_error 16 η (by norm_num) hη
  let Z₀ := max Z₁ (max Z₂ (max Z₃ (max Z₄ (max Z₅ (max 2 (max Ck (Ideal.absNorm Q:ℝ)))))))
  have hz1 : Z₁≤Z₀ := le_max_left _ _
  have hz2 : Z₂≤Z₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hz3 : Z₃≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hz4 : Z₄≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hz5 : Z₅≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hzcap : max 2 (max Ck (Ideal.absNorm Q:ℝ))≤Z₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  refine ⟨degree,C,Z₀,hC,hZ₁.trans_le hz1,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F Q₀ hJ hI hF hpower hmask A Z d ell0 shift O₀ QK QP
    hZ hd hd1 hell hellcap hshift hOeq hIn hKr hK1 hKcap hP2 hPcap
  have hz : 1<Z := lt_of_lt_of_le hZ₁ (hz1.trans hZ)
  have hzpos : 0<Z := lt_trans zero_lt_one hz
  have hZ2 : 2≤Z := (le_max_left _ _).trans (hzcap.trans hZ)
  have hCkZ : Ck≤Z := (le_max_left _ _).trans ((le_max_right _ _).trans (hzcap.trans hZ))
  have hQZ : (Ideal.absNorm Q:ℝ)≤Z := (le_max_right _ _).trans ((le_max_right _ _).trans (hzcap.trans hZ))
  obtain ⟨hIcap,hFcap,hK8,hP8,hX8⟩ := low_actual_scale_caps J I Q Q₀ hJ hI hQ hpower hmask A
    Z Ck d ell0 shift η QK QP hZ2 hCk hCkZ hQZ hd hell hellcap hshift hη1 hIn hKcap hPcap
  let G := (poolPrimeFamily J Q Q₀).restrict A
  have hXp : 0<Z^(1+ell0+shift) := Real.rpow_pos_of_pos hzpos _
  have hQK : 0<QK := by linarith
  have hQP : 0<QP := by linarith
  have hsc := hscale i G Z (Z^(1+ell0+shift)) QK QP 8 (hz2.trans hZ) hXp hQK.le hQP.le
    hFcap hK8 hP8 hX8
  norm_num only at hsc
  have hO : 0≤O₀ := hOeq ▸ normWidth_nonneg Z hz _ (rowPowerfulPart_ne_zero I)
  have hOp : 0<(Ideal.absNorm (rowPowerfulPart I):ℝ) := actual_ideal_norm_pos _ (rowPowerfulPart_ne_zero I)
  have hOn : Z^O₀=(Ideal.absNorm (rowPowerfulPart I):ℝ) := by
    rw [hOeq]
    exact Real.rpow_logb hzpos (ne_of_gt hz) hOp
  have hO2 : O₀≤2 := by
    have hh := Real.logb_le_logb_of_le hz hOp ((original_powerful_norm_le I hI).trans hIcap)
    rw [←Real.rpow_natCast,Real.logb_rpow hzpos (ne_of_gt hz)] at hh
    norm_num at hh
    exact hOeq.symm ▸ hh
  have hza : Real.logb Z (QP/2)≤ell0+η := by
    have hh := Real.logb_le_logb_of_le hz (by positivity : 0<QP/2) hPcap
    rw [Real.logb_rpow hzpos (ne_of_gt hz)] at hh
    linarith
  have hrowlower : Z^(Real.logb Z QK)/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ) := by
    rw [Real.rpow_logb hzpos (ne_of_gt hz) hQK]
    exact hKr
  have hslot8 : QP/2≤Z^(8:ℝ) := by linarith
  have hbudget : ε*(8+8+2*(η/2+57+η))+η/2≤2*η := (low_reflection_parameters η hη).2
  have hh := he i (σ:=σ) J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ (Real.logb Z QK) (Real.logb Z (QP/2)) (1+ell0+shift) d ell0 shift (2*η)
    Ck 1 2 (Z^(1+ell0+shift)) QK QP 8 8
    (hz1.trans hZ) hCk (by norm_num) (by norm_num) hXp hQK hQP hIn
    (by simpa only [div_one,hOn] using le_refl (Ideal.absNorm (rowPowerfulPart I):ℝ)) hrowlower
    (by simpa only [mul_one] using hlogC Z (hz4.trans hZ))
    (by rw [hOeq];linarith) (hlogQ Z (hz3.trans hZ)) hd hd1 hellcap hO hza hshift rfl rfl rfl
    (by rw [Real.logb_rpow hzpos (ne_of_gt hz)]) (by positivity) (by linarith)
    hK8 hslot8 (hlog16 Z (hz5.trans hZ)) hbudget hX8 hK8 hP8 (by linarith)
    hFcap hsc hFcap
  dsimp only at hh ⊢
  intro rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  obtain ⟨D,hD⟩ := hh rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKn hPn hr haw
  apply (hD θ r aw hqk hqp hKn hPn hr haw).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1688

/- Original source: OAI/NumberTheory/DirichletL/Reflection/LowDyads.lean; sha256: 69b1e6526f6e3589bccb9d7cd5b7bd7b209046c40ae600dbf1af48b8edcca83d -/
section Source1689
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem low_dyadic_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0),
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z d ell0 shift O₀ : ℝ),
      Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart J) →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      rows⊆originalResidualRows parents J Q →
      (∀ P∈fixedBadPrimes,P∣Q) →
      let Hrow := (Ck*Z^(5/6-2*d))/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ))
      let Hslot := Z^ell0
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (tuples : Finset (σ→Ideal Eis))
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (_hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
      (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hmax hgood p)).ideal)) →
      (∀ p : tuples,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)) →
      (∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)≠2) →
      (∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot) →
    ∃ D : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      CellCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g) G rows hrows tuples hmax hgood Hrow Hslot i j,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖∑ p : tuples,
        dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D (s g) (hc₀ g) jF W θ (Z^(1+ell0+shift)) r aw K p‖^2)≤
        (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*
          (C*(1+‖θ‖)^degree*Z^((5/6-2*d)+504*η-O₀/2)) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_fixed_member_geometry_uniform a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac Q hQ Ck η hCk hη hη1
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro g σ _ _ J F Q₀ hJ hF A Z d ell0 shift O₀ hZ hd hd1 hell hellcap hshift hOeq
    parents rows hparents hsub hbad
  dsimp only
  intro tuples hmax hgood hinj hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
  let Hrow := (Ck*Z^(5/6-2*d))/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ))
  let Hslot := Z^ell0
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let jF := fun b : A => completedLocalExponent J F b.val.val
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzp : 0<Z := lt_trans zero_lt_one hz
  have hrowNorm : ∀ K∈rows,1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤Hrow :=
    fun K hK => original_residual_norm_bounds parents J Q hbad (Ck*Z^(5/6-2*d)) hparents K (hsub hK)
  have htupleNorm : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
      (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot := fun p hp =>
    ⟨QuadraticMainBoundary.norm_one_le (primaryGenerator_ne_zero_ideal _ (hPnorm p hp).1.2),(hPnorm p hp).2⟩
  apply physical_dyad_selection_energy G rows hrows tuples hmax hgood Hrow Hslot
    (s g) (hc₀ g) jF W (Z^(1+ell0+shift)) (fun θ => C*(1+‖θ‖)^degree*Z^((5/6-2*d)+504*η-O₀/2))
    (fun θ => by positivity)
  intro i j hi hj
  let Rc := divisorDyadicBin rows Hrow i
  let Tc := activeTupleDyad tuples Hslot j
  let hm := fun p hp k => hmax p (activeTupleDyad_subset tuples Hslot j hp) k
  let hg := fun p hp k => hgood p (activeTupleDyad_subset tuples Hslot j hp) k
  have hTc : Tc.Nonempty := hj
  have hRi : ∀ K∈Rc,Admissible K := fun K hK => hrows K (divisorDyadicBin_subset rows Hrow i hK)
  have hti : Set.InjOn slotTupleProduct (↑Tc : Set (σ→Ideal Eis)) :=
    hinj.mono (activeTupleDyad_subset tuples Hslot j)
  have hKr := divisorDyadicBin_bounds rows Hrow hrowNorm i
  have hPr := activeTupleDyad_bounds tuples Hslot htupleNorm j
  obtain ⟨K,hK⟩ := hi
  obtain ⟨I,hI,heI⟩ := Finset.mem_image.mp (hsub (divisorDyadicBin_subset rows Hrow i hK))
  obtain ⟨hIp,hpow,hmask⟩ := Finset.mem_filter.mp hI
  have hI0 := (hparents I hIp).1
  have hIn := (hparents I hIp).2
  have hKlower : (2*divisorDyadicScale i.val)/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ) := by
    rw [heI]
    convert (hKr K hK).1 using 1 ; ring
  have hKupper : 2*divisorDyadicScale i.val≤2*Ck*Z^(5/6-2*d) := by
    have hres : (Ideal.absNorm (rowResidualPart I Q):ℝ)≤(Ideal.absNorm I:ℝ) := by
      rw [rowResidualPart_norm I Q hI0]
      apply div_le_self (Nat.cast_nonneg _)
      exact one_le_mul_of_one_le_of_one_le
        (QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero I))
        (QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart I) Q))
    have hs := hKlower.trans (hres.trans hIn)
    linarith
  have hPupper : (2*divisorDyadicScale j.val)/2≤Z^ell0 := by
    convert activeTupleDyad_scale_le tuples Hslot htupleNorm j hj using 1 ; dsimp [Hslot] ; ring
  let S := tuplePrimeFamily Tc hTc hm hg
  have hScop : ∀ P∈Tc.image slotTupleProduct,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal) := by
    intro P hP
    exact hpair ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  have hSN : ∀ P∈Tc.image slotTupleProduct,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b) := by
    intro P hP
    exact hPN ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  have hSchar : ∀ P∈Tc.image slotTupleProduct,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2 := by
    intro P hP
    exact hPchar ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  obtain ⟨D,hD⟩ := he g J I F Q₀ hJ hI0 hF hpow.symm hmask.symm A
    Z d ell0 shift O₀ (2*divisorDyadicScale i.val) (2*divisorDyadicScale j.val)
    hZ hd hd1 hell hellcap hshift (by rw [hpow];exact hOeq) hIn hKlower
    (by linarith [divisorDyadicScale_ge_one i.val]) hKupper
    (by linarith [divisorDyadicScale_ge_one j.val]) hPupper
    Rc Tc hTc hm hg hti hRi hGN hGchar
    (fun K hK => hrowcop K (divisorDyadicBin_subset rows Hrow i hK))
    (tuplePrimeFamily_product Tc hTc hm hg) hScop hSN hSchar
  let Dc : CellCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g)
      G rows hrows tuples hmax hgood Hrow Hslot i j := fun K p hp =>
    memberTupleControlled Tc hm hg G K.val (hRi K.val K.property) hTc hti (D K) p hp
  refine ⟨Dc,?_⟩
  intro θ r aw hr haw
  have hb := hD θ r aw (by linarith [divisorDyadicScale_ge_one i.val])
    (by linarith [divisorDyadicScale_ge_one j.val])
    (fun K hK => by convert hKr K hK using 1 ; ring_nf)
    (by
      intro P hP
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
      refine ⟨(hPnorm p (activeTupleDyad_subset tuples Hslot j hp)).1,?_⟩
      convert hPr p hp using 1 ; ring_nf)
    (fun K hK => hr K (divisorDyadicBin_subset rows Hrow i hK))
    (fun p hp => haw p (activeTupleDyad_subset tuples Hslot j hp))
  exact hb
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1689

/- Original source: OAI/NumberTheory/DirichletL/Reflection/LowChoiceEnergy.lean; sha256: e33e38b31854ac98b71c736e1e81b33cac598149c5fc4891376725ce7eafaeb3 -/
section Source1690
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem low_original_choice_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0),
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z d ell0 shift O₀ : ℝ),
      Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart J) →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      rows⊆originalResidualRows parents J Q →
      (∀ P∈fixedBadPrimes,P∣Q) →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∃ D : ∀ K : rows,∀ p : supportedSlotChoices lists (poolPrimeFamily J Q Q₀).ideal K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily lists hmax hgood p.val)).generator Nlevel (a g) (c₀ g) (mode g),
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ), (∀ i P,‖w i P‖≤1) →
      (∑ K : rows,‖∑ p : supportedSlotChoices lists (poolPrimeFamily J Q Q₀).ideal K.val,
        (∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
          (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
          (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
          (reflectedExponent jF) (slotIndices A (PrimeIndex K.val) σ)
          (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+505*η-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_dyadic_geometry_uniform a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac Q hQ Ck η hCk hη hη1
  obtain ⟨Cb,hCb,hbins⟩ := actual_dyad_count_budget 8 η (by norm_num) hη
  refine ⟨degree,Cb*C,max Z₀ (max 2 Ck),mul_pos hCb hC,hZ₀.trans_le (le_max_left _ _),?_⟩
  intro g σ _ _ J F Q₀ hJ hF A Z d ell0 shift O₀ hZ hd hd1 hell hellcap hshift hOeq parents rows hparents hsub hbad
  have hZbase : Z₀≤Z := (le_max_left _ _).trans hZ
  have hCkZ : Ck≤Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  dsimp only
  intro lists H hdis hmax hgood hprime hrows hH hprod hGN hGchar hrowcop hLN hLchar
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let FF := (poolPrimeFamily J Q Q₀).ideal
  let tuples := fixedSlotTupleSet lists FF
  let hm := originalTupleMax lists FF hmax
  let hg := originalTupleGood lists FF hgood
  have htuples : ∀ p∈tuples,∀ i,p i∈lists i := fun p hp => ((mem_fixedSlotTupleSet lists FF p).mp hp).1
  have hpair : ∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hm hg p)).ideal) := by
    intro p
    apply PrimeFamily.sum_pairwise G _ ((poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A)
    · intro i j hij
      apply Ideal.isCoprime_of_isMaximal
      intro heq
      change p.val i=p.val j at heq
      exact Finset.disjoint_left.mp (hdis hij) (htuples p.val p.property i)
        (heq.symm ▸ htuples p.val p.property j)
    · intro f i
      apply Ideal.isCoprime_of_isMaximal
      exact (((mem_fixedSlotTupleSet lists FF p.val).mp p.property).2 f.val i).symm
  have hPN : ∀ p : tuples,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (memberTupleFamily tuples hm hg p)).ideal b) := by
    intro p b
    cases b with
    | inl f => exact hGN f
    | inr i => exact hLN i _ (htuples p.val p.property i)
  have hPchar : ∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hm hg p)).ideal b)≠2 := by
    intro p b
    cases b with
    | inl f => exact hGchar f
    | inr i => exact hLchar i _ (htuples p.val p.property i)
  have hPnorm : ∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Z^ell0 := by
    intro p hp
    refine ⟨slotTupleProduct_admissible lists hdis hprime ?_ p (htuples p hp),?_⟩
    · intro i P hPi
      let : P.IsMaximal := hmax i P hPi
      exact (primaryPrime_eq_primaryGenerator P).symm ▸ primaryPrime_ne_zero P (hgood i P hPi)
    · exact (slotTupleProduct_norm_bound lists H (fun i P hPi => (hprime i P hPi).ne_zero) hH p (htuples p hp)).2.trans hprod
  let Hrow := (Ck*Z^(5/6-2*d))/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ))
  let Hslot := Z^ell0
  obtain ⟨Dc,hDc⟩ := he g J F Q₀ hJ hF A Z d ell0 shift O₀
    hZbase hd hd1 hell hellcap hshift hOeq
    parents rows hparents hsub hbad tuples hm hg (fixedSlotTupleSet_product_injective lists FF hdis hprime)
    hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
  let D := fun (K : rows) (p : supportedSlotChoices lists FF K.val) =>
    memberChoiceControlled lists FF hmax hgood G K.val (hrows K.val K.property)
      (dyadicTupleControlled G rows hrows tuples hm hg Hrow Hslot Dc K) p
  refine ⟨D,?_⟩
  intro θ w hw
  have hsource (K : rows) :
      (∑ p : tuples,dyadicPhysicalTerm G rows hrows tuples hm hg Hrow Hslot Dc (s g) (hc₀ g)
        (fun b : A => completedLocalExponent J F b.val.val) W θ (Z^(1+ell0+shift)) (fun _ => 1)
        (fixedTupleCoefficient lists w) K p)=
      ∑ p : supportedSlotChoices lists FF K.val,(∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
        (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) := by
    simpa only [dyadicPhysicalTerm,D,one_mul] using member_source_eq_original_choices lists FF hmax hgood G K.val
      (hrows K.val K.property) (dyadicTupleControlled G rows hrows tuples hm hg Hrow Hslot Dc K)
      (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val)
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) 1 w
  have hb := hDc θ (fun _ => 1) (fixedTupleCoefficient lists w) (by simp) (fun p hp => fixedTupleCoefficient_norm lists w hw p)
  have hid : (∑ K : rows,‖∑ p : tuples,dyadicPhysicalTerm G rows hrows tuples hm hg Hrow Hslot Dc
      (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val) W θ (Z^(1+ell0+shift))
      (fun _ => 1) (fixedTupleCoefficient lists w) K p‖^2)=
      ∑ K : rows,‖∑ p : supportedSlotChoices lists FF K.val,(∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
        (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    exact congrArg (fun z : ℂ => ‖z‖^2) (hsource K)
  apply (hid.symm.trans_le hb).trans
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZbase
  have hzpos : 0<Z := lt_trans zero_lt_one hz
  have hp : (1:ℝ)≤Ideal.absNorm (rowPowerfulPart J) := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
  have hm' : (1:ℝ)≤Ideal.absNorm (rowMaskPart J Q) :=
    QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart J) Q)
  have hRpos : 0<Hrow := by dsimp [Hrow];positivity
  have hScap : Hslot≤Z^(8:ℝ) := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
  have hRcap : Hrow≤Z^(8:ℝ) := by
    apply (div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le hp hm')).trans
    calc
      Ck*Z^(5/6-2*d) ≤ Z*Z^(5/6-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hzpos.le _)
      _ = Z^(1+(5/6-2*d)) := by rw [Real.rpow_add hzpos,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
  have hcount := hbins Z Hrow Hslot hz.le hRpos (Real.rpow_pos_of_pos hzpos _) hRcap hScap
  calc
    _ ≤ (Cb*Z^(η))*(C*(1+‖θ‖)^degree*Z^((5/6-2*d)+504*η-O₀/2)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (Cb*C)*(1+‖θ‖)^degree*Z^(η+((5/6-2*d)+504*η-O₀/2)) := by
      rw [Real.rpow_add hzpos];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1690

/- Original source: OAI/NumberTheory/DirichletL/Reflection/LowInactiveEnergy.lean; sha256: ba399931005e1a226c95d5d8700eaf38a3e699c98c8222c742b76ce9b0c049bc -/
section Source1691
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem low_original_inactive_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0),
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z d ell0 shift O₀ : ℝ),
      Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart J) →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      rows⊆originalResidualRows parents J Q →
      (∀ P∈fixedBadPrimes,P∣Q) →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∀ T : Finset σ,
    ∃ D : ∀ K : rows,
      ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) (poolPrimeFamily J Q Q₀).ideal K.val,
      ∀ p : supportedSlotChoices (fun i : T => lists i.val) (poolPrimeFamily J Q Q₀).ideal K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator
          Nlevel (a g) (c₀ g) (mode g),
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ), (∀ i P,‖w i P‖≤1) →
      (∑ K : rows,‖∑ b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val)
        (poolPrimeFamily J Q Q₀).ideal K.val,
        ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
        ∑ p : supportedSlotChoices (fun i : T => lists i.val) (poolPrimeFamily J Q Q₀).ideal K.val,
          (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) (s g)
          (G.reflected K.val (hrows K.val K.property)
            (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero (hc₀ g)
          (G.reflected K.val (hrows K.val K.property)
            (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
          (reflectedExponent jF) (slotIndices A (PrimeIndex K.val) T)
          (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))‖^2)≤
        (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2*
          (C*(1+‖θ‖)^degree*Z^((5/6-2*d)+505*η-O₀/2)) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_original_choice_energy a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac Q hQ Ck η hCk hη hη1
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro g σ _ _ J F Q₀ hJ hF A Z d ell0 shift O₀ hZ hd hd1 hell hellcap hshift hOeq parents rows hparents hsub hbad
  dsimp only
  intro lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar T
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let FF := (poolPrimeFamily J Q Q₀).ideal
  let rowsb := fun b : ∀ i : {i // i∉T},lists i.val => inactiveRowSet rows lists T FF b
  have hbsub (b : ∀ i : {i // i∉T},lists i.val) : rowsb b⊆rows := by
    intro K hK
    exact ((inactiveRows_mem rows lists T FF b K).mp hK).1
  have hbr (b : ∀ i : {i // i∉T},lists i.val) : ∀ K∈rowsb b,Admissible K := fun K hK => hrows K (hbsub b hK)
  have hdisT : Pairwise (fun i j : T => Disjoint (lists i.val) (lists j.val)) := by
    intro i j hij
    exact hdis (fun hv => hij (Subtype.ext hv))
  have hpT : (∏ i : T,H i.val)≤Z^ell0 := by
    rw [Finset.prod_coe_sort]
    apply le_trans _ hprod
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ T)
      (fun i _ => zero_le_one.trans (hH1 i)) (fun i _ _ => hH1 i)
  have hall := fun b : ∀ i : {i // i∉T},lists i.val =>
    he g J F Q₀ hJ hF A Z d ell0 shift O₀
      hZ hd hd1 hell hellcap hshift hOeq
      parents (rowsb b) hparents ((hbsub b).trans hsub) hbad
      (fun i : T => lists i.val) (fun i : T => H i.val) hdisT
      (fun i => hmax i.val) (fun i => hgood i.val) (fun i => hprime i.val) (hbr b)
      (fun i => hH i.val) hpT hGN hGchar (fun K hK => hrowcop K (hbsub b hK))
      (fun i => hLN i.val) (fun i => hLchar i.val)
  choose Db hDb using hall
  let D := fun (K : rows)
    (b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val)
    (p : supportedSlotChoices (fun i : T => lists i.val) FF K.val) =>
      Db b.val ⟨K.val,(inactiveRows_mem rows lists T FF b.val K.val).mpr ⟨K.property,b.property⟩⟩ p
  refine ⟨D,?_⟩
  intro θ w hw
  let f := fun (K : rows) (b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val) =>
    ∑ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
      (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) (s g)
      (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero (hc₀ g)
      (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
      (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) T)
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  apply supported_inactive_source_energy rows lists T FF H (fun i P hP => (hprime i P hP).ne_zero)
    hH w hw f (C*(1+‖θ‖)^degree*Z^((5/6-2*d)+505*η-O₀/2)) (by positivity)
  intro b
  exact hDb b θ (fun i : T => w i.val) (fun i P => hw i.val P)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1691

/- Original source: OAI/NumberTheory/DirichletL/Reflection/LowFrozenEnergy.lean; sha256: 3e02d4e496947aba21a963cb85e491bc7e4a79f5e7c6de52a03c95776db5619c -/
section Source1692
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem low_original_frozen_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0),
    ∀ (Z d ell0 shift O₀ : ℝ),
      Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart J) → (Ideal.absNorm J:ℝ)≤Ck*Z^(5/6-2*d) →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      rows⊆originalResidualRows parents J Q →
      (∀ P∈fixedBadPrimes,P∣Q) →
    Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) ((poolPrimeFamily J Q Q₀).ideal f)) →
      (∀ f,ringChar (Eis⧸(poolPrimeFamily J Q Q₀).ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J Q Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∃ D : ∀ g : γ,∀ A : Finset (FreeReflection.pool J Q Q₀),∀ T : Finset σ,
      OriginalSplitCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g)
        ((poolPrimeFamily J Q Q₀).restrict A) (poolPrimeFamily J Q Q₀).ideal
        rows hrows lists hmax hgood T,
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ) (scalar : γ → rows → ℂ),
      (∀ i P,‖w i P‖≤1) → (∀ g K,‖scalar g K‖≤1) →
      (∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ g : γ,scalar g K*
        ∑ A : Finset (FreeReflection.pool J Q Q₀),frozenInactiveWeight J F Q Q₀ A*
          ∑ T : Finset σ,originalInactivePhysical
            ((poolPrimeFamily J Q Q₀).restrict A) (poolPrimeFamily J Q Q₀).ideal
            rows hrows lists hmax hgood T (D g A T) (s g) (hc₀ g)
            (fun b : A => completedLocalExponent J F b.val.val)
            (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w K‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+506*η-O₀/2) := by
  obtain ⟨degree,C,Z₁,hC,hZ₁,he⟩ := low_original_inactive_energy a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac Q hQ Ck η hCk hη hη1
  let ε := η/8
  have hε : 0<ε := by dsimp [ε];positivity
  obtain ⟨Cb,hCb,hcost⟩ := original_source_cost_budget (χ:=γ) rmax ε hε
  let Z₀ := max Z₁ (max 2 (max Ck (Ideal.absNorm Q:ℝ)))
  refine ⟨degree,(‖thetaDerivativeScalar⁻¹‖^2+1)*Cb*C,Z₀,by positivity,hZ₁.trans_le (le_max_left _ _),?_⟩
  intro σ _ _ J F Q₀ hJ hF Z d ell0 shift O₀ hZ hd hd1 hell hellcap hshift hOeq hJn
    parents rows hparents hsub hbad
    hcard lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar
  have hz1 : Z₁≤Z := (le_max_left _ _).trans hZ
  have hz : 1<Z := lt_of_lt_of_le hZ₁ hz1
  have hzp : 0<Z := lt_trans zero_lt_one hz
  let FF := (poolPrimeFamily J Q Q₀).ideal
  have hall := fun (g : γ) (A : Finset (FreeReflection.pool J Q Q₀)) (T : Finset σ) =>
    he g J F Q₀ hJ hF A Z d ell0 shift O₀
      hz1 hd hd1 hell hellcap hshift hOeq
      parents rows hparents hsub hbad lists H hdis hmax hgood hprime hrows hH1 hH hprod
      (fun f => hGN f.val) (fun f => hGchar f.val)
      (fun K hK => ⟨fun f => (hrowcop K hK).1 f.val,(hrowcop K hK).2⟩) hLN hLchar T
  choose D hD using hall
  refine ⟨D,?_⟩
  intro θ w scalar hw hscalar
  let energy := C*(1+‖θ‖)^degree*Z^((5/6-2*d)+505*η-O₀/2)
  let harm := (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2
  let source := fun (g : γ) (A : Finset (FreeReflection.pool J Q Q₀)) (T : Finset σ) (K : rows) =>
    originalInactivePhysical ((poolPrimeFamily J Q Q₀).restrict A) FF rows hrows lists hmax hgood T
      (D g A T) (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val)
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w K
  have hs (g : γ) (A : Finset (FreeReflection.pool J Q Q₀)) (T : Finset σ) :
      (∑ K : rows,‖source g A T K‖^2)≤harm*energy := by
    apply (hD g A T θ w hw).trans
    apply mul_le_mul_of_nonneg_right _ (by dsimp [energy];positivity)
    apply pow_le_pow_left₀ (by positivity)
    exact subtype_product_le_full (fun i => i∉T) (fun i => 256*(columnDyadicLength (H i)+1:ℝ)) (fun i => by have hn : (0:ℝ)≤columnDyadicLength (H i) := Nat.cast_nonneg _; linarith)
  let Labels := γ×(Finset (FreeReflection.pool J Q Q₀)×Finset σ)
  let f := fun (b : Labels) (K : rows) => (scalar b.1 K*frozenInactiveWeight J F Q Q₀ b.2.1)*source b.1 b.2.1 b.2.2 K
  have hf (b : Labels) : (∑ K : rows,‖f b K‖^2)≤harm*energy := by
    apply (bounded_row_multiplier_energy Finset.univ _ _ (fun K hK => ?_)).trans (hs b.1 b.2.1 b.2.2)
    rw [norm_mul]
    exact (mul_le_mul (hscalar b.1 K) (frozenInactiveWeight_norm J F Q Q₀ b.2.1)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hfam := weighted_finite_row_energy_uniform (Finset.univ : Finset Labels) (Finset.univ : Finset rows)
    (fun _ => (1:ℂ)) f (harm*energy) (fun b _ => hf b)
  simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hfam
  have hid (K : rows) : (∑ b : Labels,f b K)=∑ g : γ,scalar g K*
      ∑ A : Finset (FreeReflection.pool J Q Q₀),frozenInactiveWeight J F Q Q₀ A*
        ∑ T : Finset σ,source g A T K := by
    simp only [Labels,f,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  have hsource : (∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ g : γ,scalar g K*
      ∑ A : Finset (FreeReflection.pool J Q Q₀),frozenInactiveWeight J F Q Q₀ A*
        ∑ T : Finset σ,source g A T K‖^2)≤
      ‖thetaDerivativeScalar⁻¹‖^2*(Fintype.card Labels:ℝ)^2*harm*energy := by
    simp_rw [←hid]
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hfam (sq_nonneg _)).trans_eq (by ring)
  apply hsource.trans
  have hQn : (Ideal.absNorm Q:ℝ)≤Z := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hCkZ : Ck≤Z := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hJcap : (Ideal.absNorm J:ℝ)≤Z^(2:ℝ) := by
    apply hJn.trans
    calc
      Ck*Z^(5/6-2*d) ≤ Z*Z^(5/6-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hzp.le _)
      _ = Z^(1+(5/6-2*d)) := by rw [Real.rpow_add hzp,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
  have hpool : (Ideal.absNorm (J*Q):ℝ)≤Z^(3:ℝ) := by
    rw [map_mul,Nat.cast_mul]
    calc
      _ ≤ Z^(2:ℝ)*Z := mul_le_mul hJcap hQn (Nat.cast_nonneg _) (Real.rpow_nonneg hzp.le _)
      _ = _ := by norm_num;ring
  have hslot : (∏ i,H i)≤Z^(2:ℝ) := hprod.trans
    (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith))
  have hcst := hcost H hcard hH1 J Q Q₀ hJ hQ Z 3 2 η hz hpool hslot (by dsimp [ε];linarith)
  calc
    _ = ‖thetaDerivativeScalar⁻¹‖^2*((Fintype.card Labels:ℝ)^2*harm)*energy := by ring
    _ ≤ (‖thetaDerivativeScalar⁻¹‖^2+1)*(Cb*Z^(η))*energy := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [energy];positivity)
      exact mul_le_mul (by linarith) hcst (by dsimp [harm];positivity) (by positivity)
    _ = ((‖thetaDerivativeScalar⁻¹‖^2+1)*Cb*C)*(1+‖θ‖)^degree*
        Z^(η+((5/6-2*d)+505*η-O₀/2)) := by
      dsimp only [energy]
      rw [Real.rpow_add hzp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1692

/- Original source: OAI/NumberTheory/DirichletL/Reflection/LowCompletedFiber.lean; sha256: b0df9532dc3b031cf34afb7b2cd75cae80025aaad3745ce2a84b4a3ede50b9b9 -/
section Source1693
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem low_completed_fiber_energy (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J : Ideal Eis) (_hJ : J≠0)
      (Z d ell0 shift : ℝ), Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
      (Ideal.absNorm J:ℝ)≤Ck*Z^(5/6-2*d) →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈representativeRowFiber parents J (Ideal.span {m}*F),
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^((5/6-2*d)+506*η)*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ)) := by
  let Q₀ := Q*Ideal.span {(72:Eis)}
  let c : Eis := (9:Eis)*(ConcretePrimeRowBridge.idealGenerator Q)*(72:Eis)
  have hc : c≠0 := mul_ne_zero (mul_ne_zero (by norm_num)
    (ConcretePrimeRowBridge.idealGenerator_ne_zero Q hQ)) (by norm_num)
  have hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀ := by
    dsimp only [c,Q₀]
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
      ConcretePrimeRowBridge.span_idealGenerator]
    ring
  let : Finite (Eis⧸Ideal.span {c}) := ConcreteTraceCRT.finite_quotient_span hc
  let : Fintype (Eis⧸Ideal.span {c}) := Fintype.ofFinite _
  let : Finite (Eis⧸Ideal.span {((9:Eis)*c)^2}) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero 2 (mul_ne_zero (by norm_num) hc))
  let : Fintype (Eis⧸Ideal.span {((9:Eis)*c)^2}) := Fintype.ofFinite _
  let mask := Ideal.span {m}*F
  have hmask0 : mask≠0 := mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero
  let E := fixedFourierGeometry c hc
  have hEc : ∀ h,(E h).c0≠0 := fun h => (E h).denominator_ne_zero
  have hEN : ∀ h,(9:Eis)*(E h).c0∣(9:Eis)*c := fun h => mul_dvd_mul_left (9:Eis) (E h).denominator_dvd
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_original_frozen_energy
    (fun h => (E h).a0) (fun h => (E h).c0) (fun h => (E h).mode) lo hi hlo W hWs hW
    (fun h => (E h).shape) hEc hEN (fun h => (E h).primary) (fun h => (E h).coprime)
    mask hmask0 Ck η hCk hη hη1 rmax
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ J hJ Z d ell0 shift hZ hd hd1 hell hellcap hshift hJn
    parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let rows := originalResidualRows parents J mask
  have hparents0 : ∀ I∈parents,I≠0 := fun I hI => (hparents I hI).1
  let hrows : ∀ K∈rows,Admissible K := originalResidualAdmissible parents J F m hbad
  have hcop : ∀ K∈rows,IsCoprime Q₀ K := by
    intro K hK
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
    exact rowResidualPart_coprime_period I F Q₀ m hperiod
  have hGN : ∀ f,IsCoprime (Ideal.span {(9:Eis)*c}) ((poolPrimeFamily J mask Q₀).ideal f) :=
    (poolPrimeFamily J mask Q₀).level_coprime Q₀ c hcQ (poolPrimeFamily_period J mask Q₀)
  have hrowcop : ∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J mask Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {(9:Eis)*c}) K := by
    intro K hK
    refine ⟨?_,residual_level_coprime K Q₀ (hrows K hK) c hcQ (hcop K hK)⟩
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨hIp,hpow,hmask'⟩ := Finset.mem_filter.mp hI
    exact poolPrimeFamily_fiber_row_coprime J I mask Q₀ hJ (hparents0 I hIp) hmask0 hpow.symm hmask'.symm
  have hLN : ∀ i,∀ P∈lists i,IsCoprime (Ideal.span {(9:Eis)*c}) P :=
    fun i P hP => maximal_prime_level_coprime P (hmax i P hP) (hgood i P hP) Q₀ c hcQ (hLP i P hP)
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzp : 0<Z := lt_trans zero_lt_one hz
  let O := normWidth Z (rowPowerfulPart J)
  have hO : 0≤O := normWidth_nonneg Z hz _ (rowPowerfulPart_ne_zero J)
  have hPowPos : 0<(Ideal.absNorm (rowPowerfulPart J):ℝ) := by
    have := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
    linarith
  obtain ⟨D,hD⟩ := he (σ:=σ) J F Q₀ hJ hF.ne_zero Z d ell0 shift O
    hZ hd hd1 hell hellcap hshift rfl hJn parents rows hparents (Finset.Subset.refl _) hbad
    hcard lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN (poolPrimeFamily_odd J mask Q₀)
    hrowcop hLN hodd
  let scalar := fun h (K : rows) => fixedThetaRowCoeff c hc
    ((residualOriginalData parents J F hF m hm hparents0 u K).fixedFactor Ψ Q) h
  have hscalar : ∀ h K,‖scalar h K‖≤1 := fun h K =>
    (residualOriginalData parents J F hF m hm hparents0 u K).fixedCoefficient_norm Ψ Q hΨnorm c hc h
  have henergy := hD θ w scalar hw hscalar
  have hTw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) :=
    CanonicalRowCompletion.normTwistedSource_contDiff W lo hi hlo hWs hW θ
  have hTs := (CompletedHeight.normTwistedSource_support W θ).trans hWs
  have hTc : HasCompactSupport (CompletedHeight.normTwistedSource W θ) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => by
      by_contra hn
      exact hx (hTs hn))
  have hid (K : rows) := original_completed_residual_source parents J F hJ hF m hm hparents0 u hbad
    Q hQ c hc hcQ E hcop lists hmax hgood hdis hodd hLP D Ψ hΨnorm hΨperiod hmLam hm2
    (CompletedHeight.normTwistedSource W θ) hTc lo hi hlo hTs hTw (Z^(1+ell0+shift)) (Real.rpow_pos_of_pos hzp _) w K
  have hre := original_fiber_energy_reindex parents J (mask) hparents0
    (fun I => ∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator I))
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))
  rw [hre]
  have heq : (∑ K : rows,‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J mask K.val)))
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)=
      ∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ h,scalar h K*
        ∑ A : Finset (FreeReflection.pool J mask Q₀),frozenInactiveWeight J F mask Q₀ A*
          ∑ T : Finset σ,originalInactivePhysical ((poolPrimeFamily J mask Q₀).restrict A)
            (poolPrimeFamily J mask Q₀).ideal rows hrows lists hmax hgood T (D h A T) (E h).shape (E h).denominator_ne_zero
            (fun b : A => completedLocalExponent J F b.val.val)
            (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w K‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    exact congrArg (fun z : ℂ => ‖z‖^2) (hid K)
  have hbound := heq.trans_le henergy
  have hp : Z^O=(Ideal.absNorm (rowPowerfulPart J):ℝ) := Real.rpow_logb hzp (ne_of_gt hz) hPowPos
  have hR : C*(1+‖θ‖)^degree*Z^((5/6-2*d)+506*η-O/2)=
      C*(1+‖θ‖)^degree*Z^((5/6-2*d)+506*η)*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ)) := by
    rw [show (5/6-2*d)+506*η-O/2=((5/6-2*d)+506*η)+O*(-(1/2:ℝ)) by ring,
      Real.rpow_add hzp,Real.rpow_mul hzp.le,hp]
    ring
  have hs := Finset.sum_coe_sort rows (fun K : Ideal Eis =>
    ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J mask K)))
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
  exact hs.symm.trans_le (hbound.trans_eq hR)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1693

/- Original source: OAI/NumberTheory/DirichletL/Reflection/PowerfulBudget.lean; sha256: 1009d9196abc52da0f22df00e68a066ba491a2c20d4f6d45e8a36c095fc1850b -/
section Source1694
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseReflectedPhasePowerfulBudget
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem powerful_half_norm_sum (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (X : ℝ),1≤X →
      (∀ I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X) →
      ∑ I∈S,(Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤ C*X^ε := by
  let δ := ε/2
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨D,hD,hcount⟩ := powerful_ideal_count δ hδ
  let C := D*(2:ℝ)^(1/2+δ)*(2+1/(δ*Real.log 2))
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro S X hX hS
  have hx : 0<X := zero_lt_one.trans_le hX
  have hnorm (I : Ideal O) (hI : I∈S) :
      1≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤X :=
    ⟨QuadraticMainBoundary.norm_one_le (hS I hI).1.1,(hS I hI).2⟩
  have hbin (j : Fin (columnDyadicLength X+1)) :
      ∑ I∈divisorDyadicBin S X j,(Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤
        D*(2:ℝ)^(1/2+δ)*X^δ := by
    let R := divisorDyadicScale j.val
    have hR : 1≤R := divisorDyadicScale_ge_one _
    have hr : 0<R := zero_lt_one.trans_le hR
    by_cases he : (divisorDyadicBin S X j).Nonempty
    · have hRX : R≤X := divisorDyadicBin_scale_le S X hnorm j he
      have hc : ((divisorDyadicBin S X j).card:ℝ) ≤ D*(2*R)^(1/2+δ) := by
        apply hcount _ _ (by linarith)
        intro I hI
        exact ⟨(hS I (Finset.mem_filter.mp hI).1).1,
          (divisorDyadicBin_bounds S X hnorm j I hI).2⟩
      have hw (I : Ideal O) (hI : I∈divisorDyadicBin S X j) :
          (Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤ R^(-1/2:ℝ) :=
        Real.rpow_le_rpow_of_nonpos hr (divisorDyadicBin_bounds S X hnorm j I hI).1
          (by norm_num)
      calc
        _ ≤ ((divisorDyadicBin S X j).card:ℝ)*R^(-1/2:ℝ) := by
          apply (Finset.sum_le_sum hw).trans_eq
          simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ (D*(2*R)^(1/2+δ))*R^(-1/2:ℝ) :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hr.le _)
        _ = (D*(2:ℝ)^(1/2+δ))*(R^(1/2+δ)*R^(-1/2:ℝ)) := by
          rw [Real.mul_rpow (by norm_num) hr.le]
          ring
        _ = D*(2:ℝ)^(1/2+δ)*R^δ := by
          rw [←Real.rpow_add hr]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hRX hδ.le) (by positivity)
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
      positivity
  rw [sum_divisorDyadicBins S X]
  calc
    _ ≤ ∑ _j : Fin (columnDyadicLength X+1),D*(2:ℝ)^(1/2+δ)*X^δ :=
      Finset.sum_le_sum (fun j _=>hbin j)
    _ = (columnDyadicLength X+1:ℝ)*(D*(2:ℝ)^(1/2+δ)*X^δ) := by simp
    _ ≤ ((2+1/(δ*Real.log 2))*X^δ)*(D*(2:ℝ)^(1/2+δ)*X^δ) :=
      mul_le_mul_of_nonneg_right (columnDyadicLength_small_power δ hδ X hX) (by positivity)
    _ = C*X^ε := by
      calc
        _ = C*(X^δ*X^δ) := by dsimp [C];ring
        _ = _ := by rw [←Real.rpow_add hx,show δ+δ=ε by dsimp [δ];ring]

lemma rowPowerful_norm_le (I : Ideal O) (hI : I≠0) :
    (Ideal.absNorm (rowPowerfulPart I):ℝ) ≤ Ideal.absNorm I := by
  apply QuadraticMainBoundary.norm_le_of_dvd hI
  exact ⟨rowSimplePart I,(row_powerful_simple_product I hI).symm⟩

theorem row_mask_powerful_budget (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (Z : ℝ),2≤Z → ∀ (S : Finset (Ideal O)) (Q : Ideal O),
      (∀ I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^L) → Q≠0 → (Ideal.absNorm Q:ℝ)≤Z^L →
      ((S.image (fun I=>rowMaskPart I Q)).card:ℝ)*
        (∑ A∈S.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-1/2:ℝ)) ≤ C*Z^ε := by
  let δ := ε/(2*(L+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨Cp,hCp,hpower⟩ := powerful_half_norm_sum δ hδ
  obtain ⟨Cd,hCd,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨Cd*Cp,mul_pos hCd hCp,?_⟩
  intro Z hZ S Q hS hQ hQN
  have hz : 0<Z := by linarith
  have hX : 1≤Z^L := Real.one_le_rpow (by linarith) hL
  have hp : (∑ A∈S.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-1/2:ℝ)) ≤ Cp*(Z^L)^δ := by
    apply hpower _ _ hX
    intro A hA
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
    exact ⟨rowPowerfulPart_powerful I,(rowPowerful_norm_le I (hS I hI).1).trans (hS I hI).2⟩
  have hm : ((S.image (fun I=>rowMaskPart I Q)).card:ℝ) ≤ Cd*(Z^L)^δ :=
    ((Nat.cast_le.mpr (rowMaskPart_image_card S Q hQ)).trans (hdiv Q hQ)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hQN hδ.le) hCd.le)
  have he : L*(δ+δ) ≤ ε := by
    have heq : δ*(2*(L+1))=ε := by dsimp [δ];field_simp
    nlinarith
  calc
    _ ≤ (Cd*(Z^L)^δ)*(Cp*(Z^L)^δ) :=
      mul_le_mul hm hp (Finset.sum_nonneg (fun A _=>Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity)
    _ = (Cd*Cp)*((Z^L)^δ*(Z^L)^δ) := by ring
    _ = (Cd*Cp)*Z^(L*(δ+δ)) := by
      rw [←Real.rpow_add (Real.rpow_pos_of_pos hz L),←Real.rpow_mul hz.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) he) (mul_pos hCd hCp).le

end SevenEighths.InverseReflectedPhasePowerfulBudget

end

end OAI

end Source1694

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CompletedAggregation.lean; sha256: c287756f27b57e66652b0ed6765804865e2ad7401197b222053d298fc8c44f1b -/
section Source1695
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem completed_representative_aggregation (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (Z : ℝ),2≤Z → ∀ (parents : Finset (Ideal Eis)) (Q : Ideal Eis),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^L) → Q≠0 → (Ideal.absNorm Q:ℝ)≤Z^L →
      ∀ (E : ℝ) (f : Ideal Eis→ℝ),0≤E →
      (∀ J∈parents,(∑ I∈representativeRowFiber parents J Q,f I)≤
        E*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ))) →
      (∑ I∈parents,f I)≤C*Z^ε*E := by
  obtain ⟨C,hC,hbudget⟩ := InverseReflectedPhasePowerfulBudget.row_mask_powerful_budget L ε hL hε
  refine ⟨C,hC,?_⟩
  intro Z hZ parents Q hparents hQ hQN E f hE hf
  have hb := hbudget Z hZ parents Q hparents hQ hQN
  simp only [neg_div] at hb
  have hblocks (A T : Ideal Eis) : (∑ I∈completedRowFiber parents Q A T,f I)≤
      E*(Ideal.absNorm A:ℝ)^(-(1/2:ℝ)) := by
    by_cases he : (completedRowFiber parents Q A T).Nonempty
    · obtain ⟨J,hJ⟩ := he
      obtain ⟨hJS,hJA,hJT⟩ := Finset.mem_filter.mp hJ
      have hh := hf J hJS
      simpa only [representativeRowFiber,hJA,hJT] using hh
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
      exact mul_nonneg hE (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [←sum_completedRowFibers parents Q f]
  calc
    _ ≤ ∑ A∈parents.image rowPowerfulPart,∑ _T∈parents.image (fun I => rowMaskPart I Q),
          E*(Ideal.absNorm A:ℝ)^(-(1/2:ℝ)) :=
      Finset.sum_le_sum (fun A _ => Finset.sum_le_sum (fun T _ => hblocks A T))
    _ = (((parents.image (fun I => rowMaskPart I Q)).card:ℝ)*
          (∑ A∈parents.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-(1/2:ℝ))))*E := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb hE
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1695

/- Original source: OAI/NumberTheory/DirichletL/Reflection/LowCompletedRows.lean; sha256: 1d0865cdb4a4434c447b3562d8419353acbd8953868d3b4307a8fea982402bb3 -/
section Source1696
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem low_completed_rows_energy (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (Z d ell0 shift : ℝ), Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^((5/6-2*d)+507*η) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_completed_fiber_energy Q hQ F hF m hm hmLam hm2 hperiod hbad
    lo hi hlo W hWs hW Ck η hCk hη hη1 rmax
  obtain ⟨D,hD,ha⟩ := completed_representative_aggregation 2 η (by norm_num) hη
  let mask := Ideal.span {m}*F
  let Z₁ := max Z₀ (max 2 (max Ck (Ideal.absNorm mask:ℝ)))
  refine ⟨degree,D*C,Z₁,mul_pos hD hC,lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ _ Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  have hZZ : Z₀≤Z := (le_max_left _ _).trans hZ
  have hZ2 : 2≤Z := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hZ
  have hz : 0<Z := by linarith
  have hz1 : 1≤Z := by linarith
  have hCkZ : Ck≤Z := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hmaskZ : (Ideal.absNorm mask:ℝ)≤Z := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hmaskn : (Ideal.absNorm mask:ℝ)≤Z^(2:ℝ) := hmaskZ.trans
    (by simpa using Real.rpow_le_rpow_of_exponent_le hz1 (show (1:ℝ)≤2 by norm_num))
  have hparentn : ∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(2:ℝ) := by
    intro I hI
    refine ⟨(hparents I hI).1,(hparents I hI).2.trans ?_⟩
    calc
      _ ≤ Z*Z^(5/6-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hz.le _)
      _ = Z^(1+(5/6-2*d)) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
  have hh := ha Z hZ2 parents mask hparentn
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero) hmaskn
    (C*(1+‖θ‖)^degree*Z^((5/6-2*d)+506*η))
    (fun I => ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
      (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
    (by positivity) (fun J hJ => he (σ:=σ) J (hparents J hJ).1 Z d ell0 shift
      hZZ hd hd1 hell hellcap hshift (hparents J hJ).2
      parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod
      Ψ hΨnorm hΨperiod u θ w hw)
  apply hh.trans_eq
  calc
    _ = (D*C)*(1+‖θ‖)^degree*(Z^η*Z^((5/6-2*d)+506*η)) := by ring
    _ = _ := by rw [←Real.rpow_add hz]; congr 2; ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1696

/- Original source: OAI/NumberTheory/DirichletL/Reflection/PunctureLists.lean; sha256: 08817b2b6358d12a7d2b19e41960a0aeaef94d781c137e7a3272d425ada03a4f -/
section Source1697
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def punctureLists (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis)) : σ→Finset (Ideal Eis) :=
  fun i => (lists i).filter (fun P => P∉S)

def punctureListLift (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis))
    (p : ∀ i,punctureLists lists S i) : ∀ i,lists i :=
  fun i => ⟨(p i).val,(Finset.mem_filter.mp (p i).property).1⟩

def punctureListEquiv (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis)) :
    (∀ i,punctureLists lists S i) ≃ {p : ∀ i,lists i // ∀ i,(p i).val∉S} where
  toFun p := ⟨punctureListLift lists S p,fun i => (Finset.mem_filter.mp (p i).property).2⟩
  invFun p i := ⟨(p.val i).val,Finset.mem_filter.mpr ⟨(p.val i).property,p.property i⟩⟩
  left_inv _p := rfl
  right_inv _p := rfl

lemma sum_puncture_lists (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis))
    (f : (∀ i,lists i)→ℂ) (hz : ∀ p,(∃ i,(p i).val∈S) → f p=0) :
    (∑ p : ∀ i,lists i,f p)=∑ p : ∀ i,punctureLists lists S i,f (punctureListLift lists S p) := by
  have he := (punctureListEquiv lists S).sum_comp (fun p => f p.val)
  have hs := sum_subtype_dite_decidable (fun p : ∀ i,lists i => ∀ i,(p i).val∉S) (fun p _ => f p)
  calc
    _ = ∑ p : ∀ i,lists i,if h:∀ i,(p i).val∉S then f p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs with h
      · rfl
      · exact hz p (by simpa only [not_forall,not_not] using h)
    _ = ∑ p : {p : ∀ i,lists i // ∀ i,(p i).val∉S},f p.val := hs.symm
    _ = _ := he.symm

theorem original_completed_puncture_lists (lists : σ→Finset (Ideal Eis))
    (hprime : ∀ i,∀ P∈lists i,Prime P) (S : Finset (Ideal Eis))
    (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ (m*excludedGenerator S) f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    ∑ p : ∀ i,punctureLists lists S i,(∏ i,w i (punctureListLift lists S p i))*markedCompletedT
      (rowTwist Ψ (m*excludedGenerator S) f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0) := by
  apply sum_puncture_lists lists S
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have hm : m*excludedGenerator S∈(p i).val := (p i).val.mul_mem_left m (excludedGenerator_mem S hi)
  have hz := markedCompletedT_zero_punctured Ψ (m*excludedGenerator S) f z (p i).val
    (hprime i _ (p i).property) hm W X (fun A => ∏ j,if (p j).val∣A then (1:ℂ) else 0)
    (fun A hA => Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA))
  exact mul_eq_zero_of_right _ hz
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1697

/- Original source: OAI/NumberTheory/DirichletL/Reflection/LowPunctureLists.lean; sha256: 0fdf324818742c123a0fffbbe203ffad6f36f7f4f8bbda2bb427660298328e4d -/
section Source1698
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def actualPuncturePrimes (lists : σ→Finset (Ideal Eis)) (m : Eis) : Finset (Ideal Eis) :=
  (Finset.univ.biUnion lists).filter (fun P => m∈P)

omit [DecidableEq σ] in
lemma actualPuncturePrimes_mem (lists : σ→Finset (Ideal Eis)) (m : Eis)
    (i : σ) (P : Ideal Eis) (hP : P∈lists i) :
    P∈actualPuncturePrimes lists m ↔ m∈P := by
  simp only [actualPuncturePrimes,Finset.mem_filter]
  exact and_iff_right (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hP⟩)

lemma puncture_period_coprime (Q : Ideal Eis) (m : Eis) (hQ : Q∣Ideal.span {m})
    (P : Ideal Eis) (hP : P.IsMaximal) (hm : m∉P) : IsCoprime Q P := by
  let : P.IsMaximal := hP
  have hp : ¬P∣Ideal.span {m} := by
    intro h
    exact hm ((Ideal.dvd_iff_le.mp h) (Ideal.subset_span (Set.mem_singleton m)))
  exact (maximal_coprime_of_not_dvd P (Ideal.span {m}) hp).symm.of_isCoprime_of_dvd_left hQ

theorem original_completed_actual_puncture_lists (lists : σ→Finset (Ideal Eis))
    (hprime : ∀ i,∀ P∈lists i,Prime P)
    (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    ∑ p : ∀ i,punctureLists lists (actualPuncturePrimes lists m) i,
      (∏ i,w i (punctureListLift lists (actualPuncturePrimes lists m) p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0) := by
  apply sum_puncture_lists lists (actualPuncturePrimes lists m)
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have hm : m∈(p i).val := (Finset.mem_filter.mp hi).2
  have hz := markedCompletedT_zero_punctured Ψ m f z (p i).val
    (hprime i _ (p i).property) hm W X (fun A => ∏ j,if (p j).val∣A then (1:ℂ) else 0)
    (fun A hA => Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA))
  exact mul_eq_zero_of_right _ hz
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1698

/- Original source: OAI/NumberTheory/DirichletL/Reflection/LowOriginalEnergy.lean; sha256: 9b79212ff72aeaa4d246d59c03194c6772d55dc528b9bcbadb62c5d0a1d27b09 -/
section Source1699
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem low_original_completed_energy (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (Z d ell0 shift : ℝ), Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^((5/6-2*d)+507*η) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_completed_rows_energy Q hQ F hF m hm hmLam hm2 hperiod hbad
    lo hi hlo W hWs hW Ck η hCk hη hη1 rmax
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let S := actualPuncturePrimes lists m
  let lists' := punctureLists lists S
  have hsub (i : σ) : lists' i⊆lists i := Finset.filter_subset _ _
  let w' : ∀ i,lists' i→ℂ := fun i P => w i ⟨P.val,hsub i P.property⟩
  have hLP (i : σ) (P : Ideal Eis) (hP : P∈lists' i) : IsCoprime (Q*Ideal.span {(72:Eis)}) P := by
    apply puncture_period_coprime _ m hperiod P (hmax i P (hsub i hP))
    intro hmP
    exact (Finset.mem_filter.mp hP).2 ((actualPuncturePrimes_mem lists m i P (hsub i hP)).mpr hmP)
  have hh := he (σ:=σ) Z d ell0 shift hZ hd hd1 hell hellcap hshift
    parents hparents hcard lists' H
    (fun i j hij => (hdis hij).mono (hsub i) (hsub j))
    (fun i P hP => hmax i P (hsub i hP)) (fun i P hP => hgood i P (hsub i hP))
    (fun i P hP => hprime i P (hsub i hP)) (fun i P hP => hodd i P (hsub i hP))
    hLP hH1 (fun i P hP => hH i P (hsub i hP)) hprod
    Ψ hΨnorm hΨperiod u θ w' (fun i P => hw i ⟨P.val,hsub i P.property⟩)
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro I hI
  exact congrArg (fun z : ℂ => ‖z‖^2) (original_completed_actual_puncture_lists lists hprime Ψ m
    (ConcretePrimeRowBridge.idealGenerator F) (u.val*ConcretePrimeRowBridge.idealGenerator I)
    (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1699

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowSelectedBound.lean; sha256: 766514b55a0c29c78f12dbf72bea2f35289a772f2fd36ac7f24c0410dcda4161 -/
section Source1700
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma gaussianFixedWindow_support : Function.support gaussianFixedWindow⊆Set.Icc (1/2:ℝ) 2 := by
  intro y hy
  constructor
  · by_contra h; exact hy (gaussianFixedWindow_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h; exact hy (gaussianFixedWindow_large y (le_of_lt (lt_of_not_ge h)))

lemma lowReflectionMask_bad_ideals (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    ∀P∈fixedBadPrimes,P∣Ideal.span {lowReflectionMask η S hS}*(1:Id) := by
  intro P hP
  rw [mul_one,lowReflectionMask,←Ideal.span_singleton_mul_span_singleton,calibrationForSet_span]
  exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (fun P : Id=>P) (hbad hP)) _

theorem low_selected_physical_energy (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (K : ℕ) (Ck ε : ℝ) (hCk : 0<Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
    ∀(Z d ell0 shift : ℝ),Z₀≤Z→0≤d→d≤1/6→0≤ell0→ell0≤1/6-d+ε→|shift|≤ε→
    ∀(R : Finset O),(∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^(5/6-2*d))→
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
    ∀(J : Finset (Fin K))(H : SelectedSlot J→ℝ),
      (∀i,1≤H i)→(∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤H i)→(∏i,H i)≤Z^ell0→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) (Z^(1+ell0+shift)) t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^((5/6-2*d)+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := InverseReflectedPhase.low_original_completed_energy
    (lowReflectionPeriod η S hS) (lowReflectionPeriod_ne_zero η S hS)
    (1:Id) squarefree_one (lowReflectionMask η S hS) (lowReflectionMask_ne_zero η S hS)
    (lowReflectionMask_bad η S hS hbad).1 (lowReflectionMask_bad η S hS hbad).2
    (lowReflectionMask_period η S hS) (lowReflectionMask_bad_ideals η S hS hbad)
    (1/2) 2 (by norm_num) gaussianFixedWindow gaussianFixedWindow_support gaussianFixedWindow_contDiff
    Ck ε hCk hε hε1 K
  let C0 := (lowCorrectionEnergy+1)*((Fintype.card RayCharacter:ℝ)+1)*6*C
  have hC0 : 0<C0 := by have hh := lowCorrectionEnergy_nonneg;dsimp [C0];positivity
  refine ⟨degree,C0,Z₀,hC0,hZ₀,?_⟩
  intro Z d ell0 shift hZ hd hd1 hell hellcap hshift R hR T hT hout hdis J H hH1 hH hprod W hW Y t σ
  let L := fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val))
  have hLP (i : SelectedSlot J) : lowPeriodPrimeList η S hS (T i.val)⊆T i.val := Finset.filter_subset _ _
  have hLS (i : SelectedSlot J) : ∀P∈lowPeriodPrimeList η S hS (T i.val),Supported P.val :=
    fun P hP=>hT i.val P (hLP i hP)
  have hlists : Pairwise (fun i j=>Disjoint (L i) (L j)) :=
    lowPrimeIdealList_disjoint _ (lowPeriodPrimeList_disjoint η S hS _
      (fun i j hij=>hdis (fun h=>hij (Subtype.ext h))))
  have hparents : ∀I∈lowIdealRows R,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) :=
    fun I hI=>⟨lowIdealRows_nonzero R (fun z hz=>(hR z hz).1) I hI,
      lowIdealRows_norm_bound R _ (fun z hz=>(hR z hz).2) I hI⟩
  have hcard : Fintype.card (SelectedSlot J)≤K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  have hrow (χ : RayCharacter) (u : Oˣ) :
      (∑I∈lowIdealRows R,‖lowActualIdealPolynomial L
        (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS)
          (ConcretePrimeRowBridge.idealGenerator (1:Id)) (u.val*ConcretePrimeRowBridge.idealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) (Z^(1+ell0+shift))‖^2)≤
          C*(1+‖t‖)^degree*Z^((5/6-2*d)+507*ε) := by
    convert he Z d ell0 shift hZ hd hd1 hell hellcap hshift (lowIdealRows R) hparents hcard L H
      hlists (fun i=>lowPrimeIdealList_maximal _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).1)
      (fun i=>lowPrimeIdealList_prime _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).2)
      hH1 (fun i=>lowPrimeIdealList_norm _ _ (fun P hP=>hH i P (hLP i hP))) hprod
      (physicalRayPeriodicBase η S hS σ χ) (lowReflectionPeriod_actual η S hS σ χ).2
      (lowReflectionPeriod_actual η S hS σ χ).1 u t
      (fun i P=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator P.val))
      (fun i P=>low_actual_ideal_weight_bound η (W i.val) (hW i.val) (Y i.val) t P.val) using 1
    apply Finset.sum_congr rfl
    intro I hI
    congr 2
    unfold lowActualIdealPolynomial
    congr 1
    ext p
    simp
  apply (lowSelectedInverseRow_actual_reflected_energy η S hS hbad T hT hout hdis J W Y
    (Z^(1+ell0+shift)) t σ R (fun z hz=>(hR z hz).1)).trans
  have hh := Finset.sum_le_sum (fun χ (_ : χ∈(Finset.univ:Finset RayCharacter))=>
    Finset.sum_le_sum (fun u (_ : u∈(Finset.univ:Finset Oˣ))=>hrow χ u))
  have hm := mul_le_mul_of_nonneg_left hh lowCorrectionEnergy_nonneg
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,low_unit_card] at hm
  simp only [Nat.cast_ofNat,Real.norm_eq_abs] at hm ⊢
  apply hm.trans
  dsimp [C0]
  have hc0 := lowCorrectionEnergy_nonneg
  have hcount : 0≤(Fintype.card RayCharacter:ℝ) := Nat.cast_nonneg _
  have hzpos : 0≤Z^((5/6-2*d)+507*ε) := Real.rpow_nonneg (le_trans zero_le_one (hZ₀.le.trans hZ)) _
  have htpos : 0≤(1+|t|)^degree := by positivity
  calc
    _=(lowCorrectionEnergy*(Fintype.card RayCharacter:ℝ)*6*C)*(1+|t|)^degree*
        Z^((5/6-2*d)+507*ε) := by ring
    _≤_ := by gcongr <;> linarith

end SevenEighths.ProbePhysical
end

end OAI

end Source1700

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGramProfile.lean; sha256: bba8c4d8d6a6fd68a0a653f1aac45f410fca089ddd58550081a0c0e24d8b48fb -/
section Source1701
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramCoefficient (C : CalibrationData) (σ : RayRing)
    (s : {I : Id // Supported I}) : ℂ :=
  if physicalIdealRay s=σ then lowArithmeticCoefficient C s else 0

def lowGramProfile (W1 : ℝ→ℂ) (v r : ℝ) : ℂ :=
  W1 r*(r:ℂ)^(-1+(v:ℂ)*Complex.I)

def lowGramScale (Y : ℝ) : ℂ := (Y:ℂ)⁻¹*(Real.sqrt Y:ℂ)⁻¹

lemma lowGramCoefficient_source_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (s : {I : Id // Supported I}) :
    ‖lowGramCoefficient (calibrationForSet S hS) σ s‖≤1 := by
  unfold lowGramCoefficient
  split_ifs
  · exact lowArithmeticCoefficient_source_norm S hS s
  · simp

lemma lowGramProfile_norm (W1 : ℝ→ℂ) (v r : ℝ) (hr : 0<r) :
    ‖lowGramProfile W1 v r‖=‖W1 r‖/r := by
  rw [lowGramProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp only [Complex.add_re,Complex.neg_re,Complex.one_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,
    Real.rpow_neg_one,div_eq_mul_inv]

lemma lowGramScale_cpow (Y : ℝ) (hY : 0<Y) : lowGramScale Y=(Y:ℂ)^(-(3/2:ℂ)) := by
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  rw [show -(3/2:ℂ)=(-1)+(-(1/2:ℂ)) by norm_num,Complex.cpow_add _ _ hy,
    Complex.cpow_neg_one,Complex.cpow_neg,ProbeEuler.cpow_half_eq_sqrt _ hY.le]
  rfl

lemma lowGramScale_mul_star (Y : ℝ) (hY : 0<Y) :
    lowGramScale Y*star (lowGramScale Y)=((Y^3:ℝ):ℂ)⁻¹ := by
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hs : (Real.sqrt Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hY).ne'
  have hsquare : (Real.sqrt Y:ℂ)^2=(Y:ℂ) := by exact_mod_cast Real.sq_sqrt hY.le
  simp only [lowGramScale,map_mul,map_inv₀,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_pow]
  field_simp
  ring_nf
  rw [hsquare]

theorem lowGaussColumn_unnormalized (C : CalibrationData) (W1 : ℝ→ℂ)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) :
    lowGaussColumn C W1 Y σ v s/(Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ)=
      lowGramScale Y*(lowGramCoefficient C σ s*
        lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y)) := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  have hr : 0<(Ideal.absNorm s.val:ℝ)/Y := div_pos hq hY
  have hrc : (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hsqrt : Real.sqrt (Ideal.absNorm s.val:ℝ)=
      Real.sqrt Y*Real.sqrt ((Ideal.absNorm s.val:ℝ)/Y) := by
    rw [←Real.sqrt_mul hY.le,mul_div_cancel₀ _ hY.ne']
  have hp : (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*
      (Real.sqrt ((Ideal.absNorm s.val:ℝ)/Y):ℂ)⁻¹=
        (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-1+(v:ℂ)*Complex.I) := by
    rw [←ProbeEuler.cpow_half_eq_sqrt _ hr.le,←Complex.cpow_neg,←Complex.cpow_add _ _ hrc]
    congr 1
    ring
  unfold lowGaussColumn lowGramCoefficient
  split_ifs
  · rw [hsqrt,Complex.ofReal_mul]
    simp only [div_eq_mul_inv,mul_inv_rev]
    calc
      _ = (Y:ℂ)⁻¹*(Real.sqrt Y:ℂ)⁻¹*(lowArithmeticCoefficient C s*W1 ((Ideal.absNorm s.val:ℝ)/Y))*
        ((((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*
          (Real.sqrt ((Ideal.absNorm s.val:ℝ)/Y):ℂ)⁻¹) := by ring_nf
      _ = _ := by rw [hp];unfold lowGramScale lowGramProfile;ring_nf
  · simp

theorem lowRayAmplitude_unnormalized (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (m : O) :
    lowRayAmplitude C W1 Y σ m v=lowGramScale Y*
      ∑s∈lowGaussColumns W1 hW1 Y hY,
        lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y)*
          sexticGauss (primaryGenerator s.val) (supported_primaryGenerator_ne_zero s.val s.property) (-m) := by
  rw [lowRayAmplitude_source_columns C W1 hW1 Y hY σ v]
  unfold gaussPolynomial gaussRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have he := congrArg Ideal.absNorm ((primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1)
  rw [he]
  calc
    _ = (lowGaussColumn C W1 Y σ v s/(Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ))*
      sexticGauss (primaryGenerator s.val) (supported_primaryGenerator_ne_zero s.val s.property) (-m) := by ring
    _ = _ := by rw [lowGaussColumn_unnormalized C W1 Y hY σ v s];ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1701

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGramArithmetic.lean; sha256: bf0f768891c15321156627f4a4e1051e52818a7b36790e60c53fe76e47443b20 -/
section Source1702
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ConcreteTraceCRT ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def gramPeriodicMonoid (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : O→*ℂ :=
  conjugateMonoid C.residueMonoid*actualPeriodicRow 1 B D.numeratorUnit D.numeratorLambda D.numeratorTwo
    D.numeratorGood D.numeratorSupported

lemma gramPeriodicMonoid_norm (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (n : O) : ‖gramPeriodicMonoid C B D n‖≤1 := by
  rw [gramPeriodicMonoid,MonoidHom.mul_apply,norm_mul]
  change ‖star (C.residueMonoid n)‖*_≤1
  rw [norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one n)).trans (actualPeriodicRow_norm 1 (fun _=>by simp) B D.numeratorUnit D.numeratorLambda D.numeratorTwo
      D.numeratorGood D.numeratorSupported n)

lemma gramPeriodicMonoid_periodic (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) :
    FactorsModulo (Ideal.span {C.generator}*calibrationRowModulus C B D) (gramPeriodicMonoid C B D) := by
  have hp := actualPeriodicRow_periodic (1:O→*ℂ) 1 (fun _ _ _=>rfl)
    B D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change star (C.residueMonoid x)*_=star (C.residueMonoid y)*_
  congr 1
  · apply congrArg star
    apply congrArg C.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left hxy)
  · exact hp x y (Ideal.mul_le_right hxy)

lemma gramPeriodicMonoid_zero (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (n : O) (hn : ¬IsCoprime B n) :
    gramPeriodicMonoid C B D n=0 := by
  have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [ite_eq_right hn]
  change star (C.residueMonoid n)*
    ((((1:O→*ℂ) n*coprimalityMask B n)*
      numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n)*
      movingNumeratorRow D.numeratorGood D.numeratorSupported n)=0
  rw [hm]
  simp

lemma gramPeriodicMonoid_primary (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    gramPeriodicMonoid C B D n=(C.residueMonoid n)⁻¹*idealRowHom C.generator (Ideal.span {n}) := by
  have he := rowTwist_eq_actualPeriodicRow_primary (1:O→*ℂ) B 1 C.generator hBL hB2
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn
  rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn] at he
  have hm : coprimalityMask B n=(1:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=1;rw [ite_eq_left hc]
  simp only [MonoidHom.one_apply,hm,one_mul,one_pow] at he
  change star (C.residueMonoid n)*_=_
  rw [←he]
  congr 1
  let := finite_quotient_span C.generator_ne_zero
  let : Fintype (O⧸Ideal.span {C.generator}) := Fintype.ofFinite _
  change star (C.residue (Ideal.Quotient.mk _ n))=(C.residue (Ideal.Quotient.mk _ n))⁻¹
  rw [MulChar.star_apply',MulChar.inv_apply_eq_inv']

theorem lowArithmeticCoefficient_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (s : {I : Id // Supported I}) :
    lowArithmeticCoefficient (calibrationForSet S hS) s=
      (calibrationForSet S hS).tau⁻¹*
        gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator
          (calibrationLowData S hS) (primaryGenerator s.val) := by
  let C := calibrationForSet S hS
  have hn := supported_primaryGenerator_ne_zero s.val s.property
  have he := (primaryGenerator_spec s.val hn).1
  have hp := (primaryGenerator_spec s.val hn).2
  have hsupp := (supported_span_primaryGenerator_iff s.val).mpr s.property
  have hb := calibration_generator_bad S hS hbad
  by_cases hc : IsCoprime C.generator (primaryGenerator s.val)
  · have hguard : ∀P∈C.excluded,¬P∣s.val := by
      rw [show C.excluded=S from calibrationForSet_excluded S hS,←he]
      exact (calibration_coprime_iff_excluded_span S hS _).mp hc
    rw [lowArithmeticCoefficient,ite_eq_left hguard,
      gramPeriodicMonoid_primary C C.generator (calibrationLowData S hS) hb.1 hb.2 _ hsupp hp hc,he]
    ring
  · have hguard : ¬∀P∈C.excluded,¬P∣s.val := by
      rw [show C.excluded=S from calibrationForSet_excluded S hS,←he]
      exact fun h=>hc ((calibration_coprime_iff_excluded_span S hS _).mpr h)
    rw [lowArithmeticCoefficient,ite_eq_right hguard,gramPeriodicMonoid_zero C C.generator (calibrationLowData S hS) _ hc,mul_zero]

end SevenEighths.ProbePhysical
end

end OAI

end Source1702

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGramFixedCoefficient.lean; sha256: e41627489e06ac66953e33821cf8c6e769a2eaa8371f63cca11ce1799ae58752 -/
section Source1703
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gramFixedModulus (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  (Ideal.span {(calibrationForSet S hS).generator}*
    calibrationRowModulus (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS))*
      Ideal.span {(4:O)}

lemma gramFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : gramFixedModulus S hS≠0 := by
  unfold gramFixedModulus
  apply mul_ne_zero
  · exact mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr (calibrationForSet S hS).generator_ne_zero)
      (calibrationRowModulus_ne_zero _ _ (calibrationForSet S hS).generator_ne_zero _)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

def gramCoefficientExtension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) : ℂ :=
  if physicalRay n=σ then (calibrationForSet S hS).tau⁻¹*
    gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS) n
  else 0

lemma gramCoefficientExtension_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) :
    ‖gramCoefficientExtension S hS σ n‖≤1 := by
  unfold gramCoefficientExtension
  split_ifs
  · rw [norm_mul,norm_inv,calibrationForSet_tau_norm,inv_one,one_mul]
    exact gramPeriodicMonoid_norm _ _ _ _
  · simp

lemma gramCoefficientExtension_zero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O)
    (hn : ¬IsCoprime (calibrationForSet S hS).generator n) : gramCoefficientExtension S hS σ n=0 := by
  unfold gramCoefficientExtension
  split_ifs
  · rw [gramPeriodicMonoid_zero _ _ _ _ hn,mul_zero]
  · rfl

theorem lowGramCoefficient_eq_extension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (s : {I : Id // Supported I}) :
    lowGramCoefficient (calibrationForSet S hS) σ s=
      gramCoefficientExtension S hS σ (primaryGenerator s.val) := by
  unfold lowGramCoefficient gramCoefficientExtension
  change (if physicalRay (primaryGenerator s.val)=σ then _ else 0)=_
  rw [lowArithmeticCoefficient_periodic S hS hbad s]

theorem gramCoefficientExtension_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (x y : O) (hxy : x-y∈gramFixedModulus S hS) :
    gramCoefficientExtension S hS σ x=gramCoefficientExtension S hS σ y := by
  have hr : physicalRay x=physicalRay y := Ideal.Quotient.eq.mpr (Ideal.mul_le_right hxy)
  have hm := gramPeriodicMonoid_periodic (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS) x y (Ideal.mul_le_left hxy)
  simp only [gramCoefficientExtension,hr,hm]

lemma gramCoefficientExtension_scaled_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (d x y : O) (hxy : x-y∈gramFixedModulus S hS) :
    gramCoefficientExtension S hS σ (d*x)=gramCoefficientExtension S hS σ (d*y) := by
  apply gramCoefficientExtension_periodic
  rw [←mul_sub]
  exact (gramFixedModulus S hS).mul_mem_left d hxy

end SevenEighths.ProbePhysical
end

end OAI

end Source1703

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramCommonParam.lean; sha256: 8e7b58b840b0c14f5118402a93cf7c10a57692530c3f083c3f760629f8acc334 -/
section Source1704
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]
abbrev ResidueQ (a : A) := A⧸Ideal.span {a}

def condition (C n₁ n₂ k : A) (p : ResidueQ (C*n₁) × ResidueQ (C*n₂)) : Prop :=
  scaledResidue (C*n₁) (C*n₂) ((C*n₁)*(C*n₂)) rfl p.1-
    scaledResidue (C*n₂) (C*n₁) ((C*n₁)*(C*n₂)) (mul_comm _ _) p.2=
    Ideal.Quotient.mk (Ideal.span {(C*n₁)*(C*n₂)}) (C*k)

abbrev Solutions (C n₁ n₂ k : A) := {p : ResidueQ (C*n₁) × ResidueQ (C*n₂) // condition C n₁ n₂ k p}

def leftParam (C n₁ b k : A) (t : ResidueQ C) : ResidueQ (C*n₁) :=
  Ideal.Quotient.mk _ (b*k)+scaledResidue C n₁ (C*n₁) rfl t

def rightParam (C n₂ a k : A) (t : ResidueQ C) : ResidueQ (C*n₂) :=
  Ideal.Quotient.mk _ (-a*k)+scaledResidue C n₂ (C*n₂) rfl t

omit [IsDomain A] in
@[simp] lemma leftParam_mk (C n₁ b k t : A) :
    leftParam C n₁ b k (Ideal.Quotient.mk _ t)=Ideal.Quotient.mk _ (b*k+n₁*t) := by
  simp only [leftParam,scaledResidue_mk,map_add]

omit [IsDomain A] in
@[simp] lemma rightParam_mk (C n₂ a k t : A) :
    rightParam C n₂ a k (Ideal.Quotient.mk _ t)=Ideal.Quotient.mk _ (-a*k+n₂*t) := by
  simp only [rightParam,scaledResidue_mk,map_add]

omit [IsDomain A] in
lemma param_condition (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (t : ResidueQ C) :
    condition C n₁ n₂ k (leftParam C n₁ b k t,rightParam C n₂ a k t) := by
  obtain ⟨t,rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [leftParam_mk,rightParam_mk]
  unfold condition
  rw [scaledResidue_congruence]
  have he : C*n₂*(b*k+n₁*t)-C*n₁*(-a*k+n₂*t)-C*k=C*k*(a*n₁+b*n₂-1) := by ring
  rw [he,hab,sub_self,mul_zero]
  exact dvd_zero _

def param (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (t : ResidueQ C) : Solutions C n₁ n₂ k :=
  ⟨(leftParam C n₁ b k t,rightParam C n₂ a k t),param_condition C n₁ n₂ a b k hab t⟩

lemma param_injective (C n₁ n₂ a b k : A) (hab : a*n₁+b*n₂=1) (hn₁ : n₁≠0) :
    Function.Injective (param C n₁ n₂ a b k hab) := by
  intro t u he
  have hl : leftParam C n₁ b k t=leftParam C n₁ b k u := congrArg (fun p=>p.val.1) he
  apply scaledResidue_injective C n₁ (C*n₁) rfl hn₁
  exact add_left_cancel hl

lemma condition_divided (C n₁ n₂ k x y : A) (hC : C≠0)
    (hc : condition C n₁ n₂ k (Ideal.Quotient.mk _ x,Ideal.Quotient.mk _ y)) :
    C*n₁*n₂∣n₂*x-n₁*y-k := by
  unfold condition at hc
  rw [scaledResidue_congruence] at hc
  have hh : C*(C*n₁*n₂)∣C*(n₂*x-n₁*y-k) := by convert hc using 1 <;> ring
  exact (mul_dvd_mul_iff_left hC).mp hh

lemma param_surjective (C n₁ n₂ a b k : A) (hC : C≠0) (hab : a*n₁+b*n₂=1) :
    Function.Surjective (param C n₁ n₂ a b k hab) := by
  intro p
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective p.val.1
  obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective p.val.2
  have hc : condition C n₁ n₂ k (Ideal.Quotient.mk _ x,Ideal.Quotient.mk _ y) := by
    rw [hx,hy]
    exact p.property
  have hd := condition_divided C n₁ n₂ k x y hC hc
  refine ⟨Ideal.Quotient.mk _ (a*x+b*y),?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change leftParam C n₁ b k (Ideal.Quotient.mk _ (a*x+b*y))=p.val.1
    rw [leftParam_mk,←hx,Ideal.Quotient.eq]
    apply Ideal.mem_span_singleton.mpr
    have hh : C*n₁∣n₂*x-n₁*y-k := (dvd_mul_right (C*n₁) n₂).trans hd
    have he : b*k+n₁*(a*x+b*y)-x= -b*(n₂*x-n₁*y-k) := by
      linear_combination x*hab
    rw [he]
    exact dvd_mul_of_dvd_right hh _
  · change rightParam C n₂ a k (Ideal.Quotient.mk _ (a*x+b*y))=p.val.2
    rw [rightParam_mk,←hy,Ideal.Quotient.eq]
    apply Ideal.mem_span_singleton.mpr
    have hh : C*n₂∣n₂*x-n₁*y-k := by
      apply dvd_trans _ hd
      exact ⟨n₁,by ring⟩
    have he : -a*k+n₂*(a*x+b*y)-y=a*(n₂*x-n₁*y-k) := by
      linear_combination y*hab
    rw [he]
    exact dvd_mul_of_dvd_right hh _

def solutionEquiv (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1) : ResidueQ C≃Solutions C n₁ n₂ k :=
  Equiv.ofBijective (param C n₁ n₂ a b k hab)
    ⟨param_injective C n₁ n₂ a b k hab hn₁,param_surjective C n₁ n₂ a b k hC hab⟩

@[simp] lemma solutionEquiv_val (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1) (t : ResidueQ C) :
    (solutionEquiv C n₁ n₂ a b k hC hn₁ hab t).val=(leftParam C n₁ b k t,rightParam C n₂ a k t) := rfl

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1704

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramCommonLinear.lean; sha256: 8e3a9c94eefe0a667e4bac935d71b54f325d05f2d22c57acaad6df1e2a2e3405 -/
section Source1705
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {R : Type*} [CommRing R]

def bezoutPairEquiv (n₁ n₂ a b : R) (hab : a*n₁+b*n₂=1) : R×R≃R×R where
  toFun p := (b*p.2+n₁*p.1,-a*p.2+n₂*p.1)
  invFun p := (a*p.1+b*p.2,n₂*p.1-n₁*p.2)
  left_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab
  right_inv p := by
    apply Prod.ext
    · dsimp only
      linear_combination p.1*hab
    · dsimp only
      linear_combination p.2*hab

theorem fullCorrelation_bezout [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) :
    fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k=
      ∑t : R,f (b*k+n₁*t)*star (g (-a*k+n₂*t)) := by
  unfold fullCorrelation
  rw [←Fintype.sum_prod_type (fun p : R×R=>if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0)]
  have he := (Fintype.sum_equiv (bezoutPairEquiv n₁ n₂ a b hab)
    (fun p : R×R=>if p.2=k then f (b*p.2+n₁*p.1)*star (g (-a*p.2+n₂*p.1)) else 0)
    (fun p : R×R=>if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0) (by
      intro p
      have hh : n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=p.2 := by
        linear_combination p.2*hab
      change (if p.2=k then _ else 0)=(if n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=k then _ else 0)
      rw [hh]
      rfl)).symm
  rw [he,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem fullCorrelation_bezout_norm [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) (hf : ∀x,‖f x‖≤1) (hg : ∀x,‖g x‖≤1) :
    ‖fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k‖≤(Fintype.card R:ℝ) := by
  rw [fullCorrelation_bezout n₁ n₂ a b k hab]
  calc
    _ ≤ ∑t : R,‖f (b*k+n₁*t)*star (g (-a*k+n₂*t))‖ := norm_sum_le _ _
    _ ≤ ∑_t : R,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [norm_mul,norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hg _)
    _ = _ := by simp

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1705

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramLocalExtension.lean; sha256: 39de489d5411cbc12b1e3e31ce50620977e10b9d00aaca843d9b365fa42f558a -/
section Source1706
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge CenteredMomentCorrelation CenteredMomentCanonical
local notation "O" => ActualEisensteinCubic.O

lemma finiteField_local_norm {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (u v k : F) (huv : u≠0 ∨ v≠0) :
    ‖localCorrelation χ u v k‖≤(Fintype.card F:ℝ) := by
  rcases huv with hu|hv
  · exact fullCorrelation_bezout_norm u v u⁻¹ 0 k (by simp [hu]) χ χ
      (FiniteRayExpansion.norm_char_le_one χ) (FiniteRayExpansion.norm_char_le_one χ)
  · exact fullCorrelation_bezout_norm u v 0 v⁻¹ k (by simp [hv]) χ χ
      (FiniteRayExpansion.norm_char_le_one χ) (FiniteRayExpansion.norm_char_le_one χ)

def localExtension (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (n₁ n₂ k : O) : ℂ := by
  letI : Fintype (O⧸P) := Fintype.ofFinite _
  letI : Field (O⧸P) := Ideal.Quotient.field P
  exact if n₁∈P ∧ n₂∈P then 0 else (Ideal.absNorm P:ℂ)^(c-1)*
    localCorrelation (actualSextic P hg^c) (Ideal.Quotient.mk P n₁)
      (Ideal.Quotient.mk P n₂) (Ideal.Quotient.mk P k)

lemma localExtension_both_zero (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (n₁ n₂ k : O) (h₁ : n₁∈P) (h₂ : n₂∈P) :
    localExtension P hg c n₁ n₂ k=0 := by simp [localExtension,h₁,h₂]

theorem localExtension_periodic (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (n₁ n₂ m₁ m₂ k l : O)
    (h₁ : n₁-m₁∈P) (h₂ : n₂-m₂∈P) (hk : k-l∈P) :
    localExtension P hg c n₁ n₂ k=localExtension P hg c m₁ m₂ l := by
  have he₁ := Ideal.Quotient.eq.mpr h₁
  have he₂ := Ideal.Quotient.eq.mpr h₂
  have hek := Ideal.Quotient.eq.mpr hk
  have hm₁ : n₁∈P↔m₁∈P := by
    rw [←Ideal.Quotient.eq_zero_iff_mem,he₁,Ideal.Quotient.eq_zero_iff_mem]
  have hm₂ : n₂∈P↔m₂∈P := by
    rw [←Ideal.Quotient.eq_zero_iff_mem,he₂,Ideal.Quotient.eq_zero_iff_mem]
  simp only [localExtension,hm₁,hm₂,he₁,he₂,hek]

theorem localExtension_norm (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (hc : 1≤c) (n₁ n₂ k : O) :
    ‖localExtension P hg c n₁ n₂ k‖≤(Ideal.absNorm P:ℝ)^c := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  let : Field (O⧸P) := Ideal.Quotient.field P
  unfold localExtension
  split_ifs with hn
  · simp only [norm_zero]
    positivity
  have huv : Ideal.Quotient.mk P n₁≠0 ∨ Ideal.Quotient.mk P n₂≠0 := by
    by_contra hh
    push Not at hh
    exact hn ⟨Ideal.Quotient.eq_zero_iff_mem.mp hh.1,Ideal.Quotient.eq_zero_iff_mem.mp hh.2⟩
  have hh := finiteField_local_norm (actualSextic P hg^c) (Ideal.Quotient.mk P n₁)
    (Ideal.Quotient.mk P n₂) (Ideal.Quotient.mk P k) huv
  rw [norm_mul,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ (Ideal.absNorm P:ℝ)^(c-1)*(Ideal.absNorm P:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hh
    _ = _ := by rw [←pow_succ,Nat.sub_add_cancel hc]

theorem primePower_common_extension (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (hc : 1≤c) [Fintype (O⧸P^c)] (n₁ n₂ k : O)
    (hn : n₁∉P ∨ n₂∉P) :
    fullCorrelation (fun x : O⧸P^c=>Ideal.Quotient.mk _ n₂*x)
      (fun y : O⧸P^c=>Ideal.Quotient.mk _ n₁*y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) (Ideal.Quotient.mk _ k)=
      localExtension P hg c n₁ n₂ k := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  let : Field (O⧸P) := Ideal.Quotient.field P
  have hn' : ¬(n₁∈P ∧ n₂∈P) := by tauto
  rw [localExtension,ite_eq_right hn']
  rcases hn with h₁|h₂
  · have hu : IsUnit (Ideal.Quotient.mk (P^c) n₁) :=
      (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
        (isUnit_iff_ne_zero.mpr (fun hz=>h₁ (Ideal.Quotient.eq_zero_iff_mem.mp hz)))
    obtain ⟨u,hu⟩ := hu
    rw [←hu]
    unfold primePowerRow
    rw [primePower_localCorrelation]
    simp only [primePowerReduction,Ideal.Quotient.factor_mk,hu]
  · have hv : IsUnit (Ideal.Quotient.mk (P^c) n₂) :=
      (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
        (isUnit_iff_ne_zero.mpr (fun hz=>h₂ (Ideal.Quotient.eq_zero_iff_mem.mp hz)))
    obtain ⟨v,hv⟩ := hv
    rw [←hv]
    unfold primePowerRow
    rw [fullCorrelation_reduction_unit_left _ (primePowerReduction_surjective P hc),
      primePowerReduction_multiplicity,Nat.cast_pow]
    change (Ideal.absNorm P:ℂ)^(c-1)*localCorrelation (actualSextic P hg^c)
      (primePowerReduction P hc (Ideal.Quotient.mk _ n₁)) (primePowerReduction P hc v)
      (primePowerReduction P hc (Ideal.Quotient.mk _ k))=_
    simp only [hv,primePowerReduction,Ideal.Quotient.factor_mk]

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1706

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramCommonSum.lean; sha256: 9a535de804ab686b34673b4729493d2c875381ffdd8b03cb8e16d4e527ae1568 -/
section Source1707
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
lemma fullModulusCorrelation_solutions (C n₁ n₂ k : A)
    [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑p : Solutions C n₁ n₂ k,χ p.val.1*star (ψ p.val.2) := by
  unfold fullModulusCorrelation fullCorrelation
  change (∑x : ResidueQ (C*n₁),∑y : ResidueQ (C*n₂),
    if condition C n₁ n₂ k (x,y) then χ x*star (ψ y) else 0)=_
  rw [←Fintype.sum_prod_type (fun p : ResidueQ (C*n₁)×ResidueQ (C*n₂)=>
    if condition C n₁ n₂ k p then χ p.1*star (ψ p.2) else 0)]
  change (∑p : ResidueQ (C*n₁)×ResidueQ (C*n₂),
    if condition C n₁ n₂ k p then χ p.1*star (ψ p.2) else 0)=_
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem fullModulusCorrelation_parameter (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1)
    [Fintype (ResidueQ C)] [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑t : ResidueQ C,χ (leftParam C n₁ b k t)*star (ψ (rightParam C n₂ a k t)) := by
  rw [fullModulusCorrelation_solutions]
  symm
  exact Fintype.sum_equiv (solutionEquiv C n₁ n₂ a b k hC hn₁ hab) _ _ (fun _=>rfl)

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1707

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramCommonActual.lean; sha256: 5f7a2d6f6e92cac158c8a770156dc65a83f67d4587af2646bcc8010f058bd567 -/
section Source1708
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def actualCommon (C : O) (hC : Supported (Ideal.span {C})) (n₁ n₂ k : O) : ℂ := by
  letI := finite_quotient_span (supported_element_ne_zero C hC)
  letI : Fintype (ResidueQ C) := Fintype.ofFinite _
  exact fullCorrelation (fun x : ResidueQ C=>Ideal.Quotient.mk _ n₂*x)
    (fun y : ResidueQ C=>Ideal.Quotient.mk _ n₁*y)
    (supportedModulusCharacter C hC) (supportedModulusCharacter C hC) (Ideal.Quotient.mk _ k)

lemma actualCommon_parameter (C : O) (hC : Supported (Ideal.span {C})) (n₁ n₂ a b k : O)
    (hab : a*n₁+b*n₂=1) :
    letI := finite_quotient_span (supported_element_ne_zero C hC)
    letI : Fintype (ResidueQ C) := Fintype.ofFinite _
    actualCommon C hC n₁ n₂ k=
      ∑t : ResidueQ C,
        supportedModulusCharacter C hC (Ideal.Quotient.mk _ (b*k)+Ideal.Quotient.mk _ n₁*t)*
          star (supportedModulusCharacter C hC (Ideal.Quotient.mk _ (-a*k)+Ideal.Quotient.mk _ n₂*t)) := by
  let := finite_quotient_span (supported_element_ne_zero C hC)
  let : Fintype (ResidueQ C) := Fintype.ofFinite _
  have hh : Ideal.Quotient.mk (Ideal.span {C}) a*Ideal.Quotient.mk _ n₁+
      Ideal.Quotient.mk _ b*Ideal.Quotient.mk _ n₂=1 := by rw [←map_mul,←map_mul,←map_add,hab,map_one]
  rw [actualCommon,fullCorrelation_bezout _ _ _ _ _ hh]
  simp only [map_mul,map_neg]

theorem actualCommon_norm (C : O) (hC : Supported (Ideal.span {C})) (n₁ n₂ k : O)
    (hn : IsCoprime n₁ n₂) : ‖actualCommon C hC n₁ n₂ k‖≤(Ideal.absNorm (Ideal.span {C}):ℝ) := by
  obtain ⟨a,b,hab⟩ := hn
  let := finite_quotient_span (supported_element_ne_zero C hC)
  let : Fintype (ResidueQ C) := Fintype.ofFinite _
  have hh : Ideal.Quotient.mk (Ideal.span {C}) a*Ideal.Quotient.mk _ n₁+
      Ideal.Quotient.mk _ b*Ideal.Quotient.mk _ n₂=1 := by rw [←map_mul,←map_mul,←map_add,hab,map_one]
  have hc (x : ResidueQ C) : ‖supportedModulusCharacter C hC x‖≤1 := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    exact idealRowHom_norm _ _
  have hd := fullCorrelation_bezout_norm (Ideal.Quotient.mk (Ideal.span {C}) n₁)
    (Ideal.Quotient.mk _ n₂) _ _ (Ideal.Quotient.mk _ k) hh
    (supportedModulusCharacter C hC) (supportedModulusCharacter C hC) hc hc
  simpa only [actualCommon,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hd

theorem actual_common_lift_bezout (C n₁ n₂ a b k : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂})) (hab : a*n₁+b*n₂=1) :
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) (C*k)=
      (idealRowHom (b*k) (Ideal.span {n₁})*star (idealRowHom (-a*k) (Ideal.span {n₂})))*
        actualCommon C hC n₁ n₂ k := by
  have hc := supported_element_ne_zero C hC
  have h₁n := supported_element_ne_zero n₁ h₁
  have h₂n := supported_element_ne_zero n₂ h₂
  let := finite_quotient_span hc
  let := finite_quotient_span (mul_ne_zero hc h₁n)
  let := finite_quotient_span (mul_ne_zero hc h₂n)
  let : Fintype (ResidueQ C) := Fintype.ofFinite _
  let : Fintype (ResidueQ (C*n₁)) := Fintype.ofFinite _
  let : Fintype (ResidueQ (C*n₂)) := Fintype.ofFinite _
  change fullModulusCorrelation (C*n₁) (C*n₂) _ _ (C*k)=_
  rw [fullModulusCorrelation_parameter C n₁ n₂ a b k hc h₁n hab,
    actualCommon_parameter C hC n₁ n₂ a b k hab,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨t,rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [leftParam_mk,rightParam_mk,supportedModulusCharacter_mul C n₁ hC h₁,
    supportedModulusCharacter_mul C n₂ hC h₂]
  have hleft : idealRowHom (b*k+n₁*t) (Ideal.span {n₁})=idealRowHom (b*k) (Ideal.span {n₁}) := by
    apply idealRowHom_congr_mod
    exact Ideal.mem_span_singleton.mpr ⟨t,by ring⟩
  have hright : idealRowHom (-a*k+n₂*t) (Ideal.span {n₂})=idealRowHom (-a*k) (Ideal.span {n₂}) := by
    apply idealRowHom_congr_mod
    exact Ideal.mem_span_singleton.mpr ⟨t,by ring⟩
  simp only [←map_mul,←map_add]
  simp only [supportedModulusCharacter_mk,hleft,hright,star_mul]
  ring

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1708

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramCommonPhase.lean; sha256: 5441902b9c1938ce4949cbe6a07d9aa882bf28e68c5c95ad3cb22f43d5d9ee12 -/
section Source1709
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation CenteredMomentCommonSupport
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma supported_bezout_inverse (n m a b : O) (hn : Supported (Ideal.span {n}))
    (hab : a*n+b*m=1) :
    idealRowHom b (Ideal.span {n})=star (idealRowHom m (Ideal.span {n})) := by
  have he : idealRowHom (b*m) (Ideal.span {n})=1 := by
    rw [←idealRowHom_one_supported (Ideal.span {n}) hn]
    apply idealRowHom_congr_mod
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-a,?_⟩
    linear_combination hab
  rw [idealRowHom_argument_mul] at he
  let := finite_quotient_span (supported_element_ne_zero n hn)
  let : Fintype (ResidueQ n) := Fintype.ofFinite _
  change supportedModulusCharacter n hn (Ideal.Quotient.mk _ b)=
    star (supportedModulusCharacter n hn (Ideal.Quotient.mk _ m))
  rw [MulChar.star_apply',MulChar.inv_apply_eq_inv']
  exact eq_inv_of_mul_eq_one_left he

theorem actual_common_lift (C n₁ n₂ k : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂}))
    (hp₁ : ConcretePrimeRowBridge.goodLambda^2∣n₁-1)
    (hp₂ : ConcretePrimeRowBridge.goodLambda^2∣n₂-1) (hn : IsCoprime n₁ n₂) :
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) (C*k)=
      idealRowHom k (Ideal.span {n₁})*star (idealRowHom (-k) (Ideal.span {n₂}))*
        sexticReciprocityPhase n₁ n₂*actualCommon C hC n₁ n₂ k := by
  obtain ⟨a,b,hab⟩ := hn
  rw [actual_common_lift_bezout C n₁ n₂ a b k hC h₁ h₂ hab]
  have h₁b := supported_bezout_inverse n₁ n₂ a b h₁ hab
  have h₂a := supported_bezout_inverse n₂ n₁ b a h₂ (by simpa only [add_comm] using hab)
  have he : idealRowHom (-a*k) (Ideal.span {n₂})=
      idealRowHom a (Ideal.span {n₂})*idealRowHom (-k) (Ideal.span {n₂}) := by
    rw [show -a*k=a*(-k) by ring,idealRowHom_argument_mul]
  rw [idealRowHom_argument_mul,he,h₁b,h₂a,star_mul,star_star]
  let := finite_quotient_span (supported_element_ne_zero n₁ h₁)
  let : Fintype (ResidueQ n₁) := Fintype.ofFinite _
  have hphase := supported_opposite_phase n₁ n₂ h₁ h₂ hp₁ hp₂ ⟨a,b,hab⟩
  calc
    _ = idealRowHom k (Ideal.span {n₁})*star (idealRowHom (-k) (Ideal.span {n₂}))*
        (idealRowHom n₁ (Ideal.span {n₂})*star (idealRowHom n₂ (Ideal.span {n₁})))*actualCommon C hC n₁ n₂ k := by ring
    _ = _ := by rw [hphase]

theorem actual_common_norm (C n₁ n₂ k : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂})) (hn : IsCoprime n₁ n₂) :
    ‖actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) (C*k)‖≤(Ideal.absNorm (Ideal.span {C}):ℝ) := by
  obtain ⟨a,b,hab⟩ := hn
  rw [actual_common_lift_bezout C n₁ n₂ a b k hC h₁ h₂ hab,norm_mul,norm_mul,norm_star]
  have hc := actualCommon_norm C hC n₁ n₂ k ⟨a,b,hab⟩
  have hp : ‖idealRowHom (b*k) (Ideal.span {n₁})‖*‖idealRowHom (-a*k) (Ideal.span {n₂})‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans (idealRowHom_norm _ _)
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (by simpa using hc)

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1709

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramGlobalExtension.lean; sha256: 77aa056ca889446afc142e937b352d13fb3ed0142e903f2bf1afd724540d286e -/
section Source1710
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCorrelation CenteredMomentCanonical CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def globalExtension (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,goodLambda∉P i) (c : ι→ℕ) (n₁ n₂ k : O) : ℂ :=
  ∏i,localExtension (P i) (hg i) (c i) n₁ n₂ k

lemma globalExtension_norm (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,goodLambda∉P i) (c : ι→ℕ) (hc : ∀i,1≤c i) (n₁ n₂ k : O) :
    ‖globalExtension P hg c n₁ n₂ k‖≤(Ideal.absNorm (∏i,P i^c i):ℝ) := by
  rw [globalExtension,norm_prod]
  calc
    _ ≤ ∏i,(Ideal.absNorm (P i):ℝ)^c i :=
      Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun i _=>localExtension_norm (P i) (hg i) (c i) (hc i) n₁ n₂ k)
    _ = _ := by simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow]

theorem globalExtension_periodic (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,goodLambda∉P i) (c : ι→ℕ) (n₁ n₂ m₁ m₂ k l : O)
    (h₁ : n₁-m₁∈∏i,P i) (h₂ : n₂-m₂∈∏i,P i) (hk : k-l∈∏i,P i) :
    globalExtension P hg c n₁ n₂ k=globalExtension P hg c m₁ m₂ l := by
  apply Finset.prod_congr rfl
  intro i hi
  have hle : (∏i,P i)≤P i := Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))
  exact localExtension_periodic (P i) (hg i) (c i) n₁ n₂ m₁ m₂ k l (hle h₁) (hle h₂) (hle hk)

theorem canonical_common_extension (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,goodLambda∉P i) (c : ι→ℕ) (hc : ∀i,1≤c i)
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (n₁ n₂ k : O) (hn : IsCoprime n₁ n₂) :
    fullCorrelation (fun x : O⧸∏i,P i^c i=>Ideal.Quotient.mk _ n₂*x)
      (fun y : O⧸∏i,P i^c i=>Ideal.Quotient.mk _ n₁*y)
      (canonicalCRTCharacter P hg c hc hcop) (canonicalCRTCharacter P hg c hc hcop)
      (Ideal.Quotient.mk _ k)=globalExtension P hg c n₁ n₂ k := by
  have hpc : Pairwise (Function.onFun IsCoprime (fun i => P i ^ c i)) := by
    intro i j hij
    exact (hcop hij).pow
  have he := canonicalCRTCorrelation P hg c hc hcop
    (Ideal.Quotient.mk _ n₁) (Ideal.Quotient.mk _ n₂) (Ideal.Quotient.mk _ k)
  have hprod : fullCorrelation (fun x : O⧸∏i,P i^c i=>Ideal.Quotient.mk _ n₂*x)
      (fun y : O⧸∏i,P i^c i=>Ideal.Quotient.mk _ n₁*y)
      (canonicalCRTCharacter P hg c hc hcop) (canonicalCRTCharacter P hg c hc hcop)
      (Ideal.Quotient.mk _ k) =
      ∏i,fullCorrelation (fun x : O⧸P i^c i=>Ideal.Quotient.mk _ n₂*x)
        (fun y : O⧸P i^c i=>Ideal.Quotient.mk _ n₁*y)
        (primePowerRow (P i) (hg i) (hc i)) (primePowerRow (P i) (hg i) (hc i))
        (Ideal.Quotient.mk _ k) := by
    simpa only [IdealGaussCRT.quotientProdEquivPi_mk
      (fun i => P i ^ c i) hpc] using he
  rw [hprod]
  apply Finset.prod_congr rfl
  intro i hi
  apply primePower_common_extension
  by_contra h
  push Not at h
  obtain ⟨a,b,hab⟩ := hn
  have hmem : (1:O)∈P i := by
    rw [←hab]
    exact (P i).add_mem ((P i).mul_mem_left a h.1) ((P i).mul_mem_left b h.2)
  exact (Ideal.IsMaximal.ne_top (I:=P i) inferInstance) ((Ideal.eq_top_iff_one (P i)).mpr hmem)

theorem actualCommon_eq_globalExtension (C : O) (hC : Supported (Ideal.span {C}))
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i)
    (c : ι→ℕ) (hc : ∀i,1≤c i) (hcop : Pairwise (Function.onFun IsCoprime P))
    (he : Ideal.span {C}=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (n₁ n₂ k : O) (hn : IsCoprime n₁ n₂) :
    actualCommon C hC n₁ n₂ k=globalExtension P hg c n₁ n₂ k := by
  let := finite_quotient_span (supported_element_ne_zero C hC)
  let : Fintype (O⧸Ideal.span {C}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq he
  have hchar : (supportedModulusCharacter C hC : (O⧸Ideal.span {C})→ℂ)=
      (fun x=>canonicalCRTCharacter P hg c hc hcop (e x)) := by
    funext x
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [show e (Ideal.Quotient.mk _ x)=Ideal.Quotient.mk _ x from Ideal.quotEquivOfEq_mk he x,
      canonicalCRTCharacter_mk,supportedModulusCharacter_mk,he]
  rw [actualCommon,hchar,fullCorrelation_ringEquiv e]
  simp only [e,Ideal.quotEquivOfEq_mk]
  exact canonical_common_extension P hg c hc hcop n₁ n₂ k hn

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1710

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramMean.lean; sha256: c298915ba1c4a95e74763dc8a28326d18c2bd213613c2e7d39b4a61148b64d5e -/
section Source1711
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation CenteredMomentCanonical
local notation "O" => ActualEisensteinCubic.O

lemma actualSextic_power_nonprincipal (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (O⧸P)≠2) (e : ℕ) (he : ¬6∣e) :
    actualSextic P hg^e≠1 := by
  intro h
  have hd := (orderOf_dvd_iff_pow_eq_one).mpr h
  rw [actualSextic_order_six P hg hchar] at hd
  exact he hd

theorem primePower_mean_zero (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (O⧸P)≠2)
    (c e : ℕ) (hc : 1≤c) (he : ¬6∣e) [Fintype (O⧸P^c)] (d : O) :
    (∑x : O⧸P^c,(actualSextic P hg^e)
      (Ideal.Quotient.mk P d*primePowerReduction P hc x))=0 := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  simp_rw [map_mul]
  rw [←Finset.mul_sum,sum_reduction _ (primePowerReduction_surjective P hc),
    MulChar.sum_eq_zero_of_ne_one (actualSextic_power_nonprincipal P hg hchar e he),mul_zero,mul_zero]

theorem crt_joint_mean_zero (Q P : Ideal O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (O⧸P)≠2)
    (c e : ℕ) (hc : 1≤c) (he : ¬6∣e) (hcop : IsCoprime Q (P^c))
    [Fintype (O⧸Q)] [Fintype (O⧸P^c)] [Fintype (O⧸Q*P^c)]
    (F : (O⧸Q)→(O⧸Q*P^c)→ℂ) (d : O) :
    (∑x : O⧸Q*P^c,∑y : O⧸Q*P^c,
      (actualSextic P hg^e) (Ideal.Quotient.mk P d*
        primePowerReduction P hc ((Ideal.quotientMulEquivQuotientProd Q (P^c) hcop x).2))*
      F ((Ideal.quotientMulEquivQuotientProd Q (P^c) hcop x).1) y)=0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y hy
  let E := Ideal.quotientMulEquivQuotientProd Q (P^c) hcop
  have heq := E.toEquiv.sum_comp (fun p : (O⧸Q)×(O⧸P^c)=>
    (actualSextic P hg^e) (Ideal.Quotient.mk P d*primePowerReduction P hc p.2)*F p.1 y)
  change (∑x : O⧸Q*P^c,(actualSextic P hg^e)
    (Ideal.Quotient.mk P d*primePowerReduction P hc (E x).2)*F (E x).1 y)=0
  calc
    _ = ∑p : (O⧸Q)×(O⧸P^c),(actualSextic P hg^e)
        (Ideal.Quotient.mk P d*primePowerReduction P hc p.2)*F p.1 y := heq
    _ = 0 := by
      rw [Fintype.sum_prod_type]
      simp_rw [←Finset.sum_mul,primePower_mean_zero P hg hchar c e hc he d,zero_mul]
      simp

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1711

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramNumerator.lean; sha256: 72efa3c26c25e49179980f36ba00a21abd736b708f509ea32abbf2dc91f48510 -/
section Source1712
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def numeratorExtension (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) : O→*ℂ :=
  numeratorBadTwist u a b r hr*movingNumeratorRow r hr

lemma numeratorExtension_norm (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n : O) :
    ‖numeratorExtension u a b r hr n‖≤1 := by
  rw [numeratorExtension,MonoidHom.mul_apply,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (numeratorBadTwist_norm _ _ _ _ _ _)).trans (movingNumeratorRow_norm _ _ _)

lemma numeratorExtension_periodic (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(72:O)}*Ideal.span {r})
      (numeratorExtension u a b r hr) := by
  intro x y hxy
  change numeratorBadTwist u a b r hr x*movingNumeratorRow r hr x=
    numeratorBadTwist u a b r hr y*movingNumeratorRow r hr y
  rw [numeratorBadTwist_periodic _ _ _ _ _ x y (Ideal.mul_le_left hxy),
    movingNumeratorRow_periodic _ _ x y (Ideal.mul_le_right hxy)]

lemma numeratorExtension_primary (u : Oˣ) (a b : ℕ) (r k n : O)
    (hr : Supported (Ideal.span {r})) (hpr : λ₀^2∣r-1)
    (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) :
    numeratorExtension u a b r hr n=idealRowHom k (Ideal.span {n}) := by
  rw [hk]
  exact (idealRowHom_factor_numerator u a b r n hr hpr hn hpn).symm

lemma numeratorExtension_neg_primary (u : Oˣ) (a b : ℕ) (r k n : O)
    (hr : Supported (Ideal.span {r})) (hpr : λ₀^2∣r-1)
    (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) :
    numeratorExtension (-u) a b r hr n=idealRowHom (-k) (Ideal.span {n}) := by
  apply numeratorExtension_primary _ _ _ _ _ _ hr hpr _ hn hpn
  simp only [Units.val_neg,hk]
  ring

lemma numerator_good_norm_le (u : Oˣ) (a b : ℕ) (r k : O)
    (hk : k=u.val*λ₀^a*(2:O)^b*r) (hk0 : k≠0) :
    Ideal.absNorm (Ideal.span {r})≤Ideal.absNorm (Ideal.span {k}) := by
  apply Nat.le_of_dvd
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hk0))
  · apply map_dvd Ideal.absNorm
    rw [Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    exact ⟨u.val*λ₀^a*(2:O)^b,by rw [hk];ring⟩

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1712

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramJointFixed.lean; sha256: e7ca0544e169878f2b6d6aa030fe92af9440fb4077a1c5b79f57a799c78292e8 -/
section Source1713
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def primaryCoefficient (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) : ℂ :=
  if λ₀^2∣n-1 then gramCoefficientExtension S hS σ n else 0

lemma primaryCoefficient_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) :
    ‖primaryCoefficient S hS σ n‖≤1 := by
  unfold primaryCoefficient
  split_ifs
  · exact gramCoefficientExtension_norm _ _ _ _
  · simp

def jointFixedModulus (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  gramFixedModulus S hS*Ideal.span {λ₀^2}*Ideal.span {(72:O)}

lemma jointFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : jointFixedModulus S hS≠0 := by
  apply mul_ne_zero
  · apply mul_ne_zero (gramFixedModulus_nonzero S hS)
    exact Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ ConcretePrimeRowBridge.goodLambda_prime.ne_zero)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

lemma primaryCoefficient_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (x y : O) (hxy : x-y∈jointFixedModulus S hS) :
    primaryCoefficient S hS σ x=primaryCoefficient S hS σ y := by
  have hg := gramCoefficientExtension_periodic S hS σ x y (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hp : λ₀^2∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_right (Ideal.mul_le_left hxy))
  have hi : (λ₀^2∣x-1)↔(λ₀^2∣y-1) := by
    constructor
    · intro h
      convert dvd_sub h hp using 1 ; ring
    · intro h
      convert dvd_add hp h using 1 ; ring
  simp only [primaryCoefficient,hi,hg]

def jointFixed (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ : O) : ℂ :=
  primaryCoefficient S hS σ (C*n₁)*star (primaryCoefficient S hS σ (C*n₂))*
    numeratorBadTwist u a b r hr n₁*star (numeratorBadTwist (-u) a b r hr n₂)*
      sexticReciprocityPhase n₁ n₂

lemma jointFixed_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ : O) :
    ‖jointFixed S hS σ C u a b r hr n₁ n₂‖≤1 := by
  unfold jointFixed
  simp only [norm_mul,norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (sexticReciprocityPhase_norm _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (numeratorBadTwist_norm _ _ _ _ _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (numeratorBadTwist_norm _ _ _ _ _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (primaryCoefficient_norm _ _ _ _)).trans (primaryCoefficient_norm _ _ _ _)

lemma jointFixed_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ m₁ m₂ : O)
    (h₁ : n₁-m₁∈jointFixedModulus S hS) (h₂ : n₂-m₂∈jointFixedModulus S hS) :
    jointFixed S hS σ C u a b r hr n₁ n₂=jointFixed S hS σ C u a b r hr m₁ m₂ := by
  have hc₁ := primaryCoefficient_periodic S hS σ (C*n₁) (C*m₁)
    (by rw [←mul_sub];exact (jointFixedModulus S hS).mul_mem_left C h₁)
  have hc₂ := primaryCoefficient_periodic S hS σ (C*n₂) (C*m₂)
    (by rw [←mul_sub];exact (jointFixedModulus S hS).mul_mem_left C h₂)
  have hb₁ := numeratorBadTwist_periodic u a b r hr n₁ m₁ (Ideal.mul_le_right h₁)
  have hb₂ := numeratorBadTwist_periodic (-u) a b r hr n₂ m₂ (Ideal.mul_le_right h₂)
  have hfour (x y : O) (h : x-y∈jointFixedModulus S hS) : (4:O)∣x-y :=
    (show (4:O)∣72 from ⟨18,by norm_num⟩).trans (Ideal.mem_span_singleton.mp (Ideal.mul_le_right h))
  have hp : sexticReciprocityPhase n₁ n₂=sexticReciprocityPhase m₁ m₂ := by
    unfold sexticReciprocityPhase
    rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub n₁ m₁ (hfour _ _ h₁),
      QuadraticGaussRay.residue_eq_of_four_dvd_sub n₂ m₂ (hfour _ _ h₂)]
  simp only [jointFixed,hc₁,hc₂,hb₁,hb₂,hp]

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1713

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramJoint.lean; sha256: a30a7cb48f7bcf839267160dcf01536a74657043799cf4957195c8a79535a518 -/
section Source1714
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

def jointExtension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ) (n₁ n₂ : O) : ℂ :=
  jointFixed S hS σ C u a b r hr n₁ n₂*
    (idealRowHom n₁ (Ideal.span {r})*star (idealRowHom n₂ (Ideal.span {r})))*
      globalExtension P hg c n₁ n₂ k

lemma jointExtension_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ) (hc : ∀i,1≤c i)
    (n₁ n₂ : O) : ‖jointExtension S hS σ C k u a b r hr P hg c n₁ n₂‖≤Ideal.absNorm (∏i,P i^c i) := by
  rw [jointExtension,norm_mul]
  have ha : ‖jointFixed S hS σ C u a b r hr n₁ n₂*
      (idealRowHom n₁ (Ideal.span {r})*star (idealRowHom n₂ (Ideal.span {r})))‖≤1 := by
    rw [norm_mul,norm_mul,norm_star]
    exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (jointFixed_norm _ _ _ _ _ _ _ _ _ _ _)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans (idealRowHom_norm _ _))
  exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using globalExtension_norm P hg c hc n₁ n₂ k)

def jointPeriod (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (P : ι→Id) (r : O) : Id :=
  jointFixedModulus S hS*(∏i,P i)*Ideal.span {r}

lemma jointExtension_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (n₁ n₂ m₁ m₂ : O) (h₁ : n₁-m₁∈jointPeriod S hS P r) (h₂ : n₂-m₂∈jointPeriod S hS P r) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      jointExtension S hS σ C k u a b r hr P hg c m₁ m₂ := by
  have hf := jointFixed_periodic S hS σ C u a b r hr n₁ n₂ m₁ m₂
    (Ideal.mul_le_left (Ideal.mul_le_left h₁)) (Ideal.mul_le_left (Ideal.mul_le_left h₂))
  have hm₁ := idealRowHom_congr_mod (Ideal.span {r}) n₁ m₁ (Ideal.mul_le_right h₁)
  have hm₂ := idealRowHom_congr_mod (Ideal.span {r}) n₂ m₂ (Ideal.mul_le_right h₂)
  have he := globalExtension_periodic P hg c n₁ n₂ m₁ m₂ k k
    (Ideal.mul_le_right (Ideal.mul_le_left h₁)) (Ideal.mul_le_right (Ideal.mul_le_left h₂)) (by simp)
  simp only [jointExtension,hf,hm₁,hm₂,he]

lemma jointExtension_dilation_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (d n₁ n₂ m₁ m₂ : O) (h₁ : n₁-m₁∈jointPeriod S hS P r) (h₂ : n₂-m₂∈jointPeriod S hS P r) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n₁) (d*n₂)=
      jointExtension S hS σ C k u a b r hr P hg c (d*m₁) (d*m₂) := by
  apply jointExtension_periodic
  · rw [←mul_sub];exact (jointPeriod S hS P r).mul_mem_left d h₁
  · rw [←mul_sub];exact (jointPeriod S hS P r).mul_mem_left d h₂

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1714

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramJointSource.lean; sha256: a142826e225c4286b90f7abdbb7262ab87671364d5a4762cb98734c97d5e6356 -/
section Source1715
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation CenteredMomentCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

theorem jointExtension_source (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (hC : Supported (Ideal.span {C}))
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (hcop : Pairwise (Function.onFun IsCoprime P))
    (he : Ideal.span {C}=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (n₁ n₂ : O) (h₁ : Supported (Ideal.span {n₁})) (h₂ : Supported (Ideal.span {n₂}))
    (hp₁ : λ₀^2∣n₁-1) (hp₂ : λ₀^2∣n₂-1) (hn : IsCoprime n₁ n₂) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      primaryCoefficient S hS σ (C*n₁)*star (primaryCoefficient S hS σ (C*n₂))*
        actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
          (supported_mul_elements C n₂ hC h₂) (C*k) := by
  rw [actual_common_lift C n₁ n₂ k hC h₁ h₂ hp₁ hp₂ hn,
    actualCommon_eq_globalExtension C hC P hg c hc hcop he n₁ n₂ k hn,
    ←numeratorExtension_primary u a b r k n₁ hr hpr hk h₁ hp₁,
    ←numeratorExtension_neg_primary u a b r k n₂ hr hpr hk h₂ hp₂]
  simp only [jointExtension,jointFixed,numeratorExtension,MonoidHom.mul_apply,
    movingNumeratorRow,MonoidHom.coe_mk,OneHom.coe_mk,star_mul]
  ring

lemma lowGramCoefficient_eq_primary (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (s : {I : Id // Supported I}) :
    lowGramCoefficient (calibrationForSet S hS) σ s=
      primaryCoefficient S hS σ (primaryGenerator s.val) := by
  have hp : λ₀^2∣primaryGenerator s.val-1 := (primaryGenerator_spec s.val
    (supported_primaryGenerator_ne_zero s.val s.property)).2
  rw [primaryCoefficient,ite_eq_left hp]
  exact lowGramCoefficient_eq_extension S hS hbad σ s

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1715

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramGcd.lean; sha256: 0b4ac98d07f67fd7a90a40ae660d2f393139a9791f3d338444b7cf44b46960dc -/
section Source1716
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
abbrev SupportedIdeal := {I : Id // Supported I}

lemma gram_supported_divisor (I D : Id) (hI : Supported I) (hd : D∣I) : Supported D := by
  obtain ⟨J,rfl⟩ := hd
  exact (supported_mul_iff D J).mp hI |>.1

lemma gram_supported_quotient (I D : Id) (hI : Supported I) (hd : D∣I) :
    Supported (idealQuotient D I) := gram_supported_divisor I _ hI (idealQuotient_dvd hd)

def gcdCommon (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨gcd I.val J.val,gram_supported_divisor I.val _ I.property (gcd_dvd_left _ _)⟩

def gcdLeft (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨idealQuotient (gcdCommon I J).val I.val,
    gram_supported_quotient I.val _ I.property (gcd_dvd_left _ _)⟩

def gcdRight (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨idealQuotient (gcdCommon I J).val J.val,
    gram_supported_quotient J.val _ J.property (gcd_dvd_right _ _)⟩

lemma gcd_residual_coprime (I J : SupportedIdeal) : IsCoprime (gcdLeft I J).val (gcdRight I J).val :=
  (gcd_eq_iff_quotient_coprime _ _ _ (gcdCommon I J).property.1
    (gcd_dvd_left _ _) (gcd_dvd_right _ _)).mp rfl

lemma gcd_common_left (I J : SupportedIdeal) : (gcdCommon I J).val*(gcdLeft I J).val=I.val :=
  idealQuotient_mul (gcd_dvd_left _ _)

lemma gcd_common_right (I J : SupportedIdeal) : (gcdCommon I J).val*(gcdRight I J).val=J.val :=
  idealQuotient_mul (gcd_dvd_right _ _)

abbrev CoprimeTriple := {t : SupportedIdeal×SupportedIdeal×SupportedIdeal // IsCoprime t.2.1.val t.2.2.val}

def gcdTriple (p : SupportedIdeal×SupportedIdeal) : CoprimeTriple :=
  ⟨(gcdCommon p.1 p.2,gcdLeft p.1 p.2,gcdRight p.1 p.2),gcd_residual_coprime p.1 p.2⟩

def multiplyTriple (t : CoprimeTriple) : SupportedIdeal×SupportedIdeal :=
  (⟨t.val.1.val*t.val.2.1.val,(supported_mul_iff _ _).mpr ⟨t.val.1.property,t.val.2.1.property⟩⟩,
   ⟨t.val.1.val*t.val.2.2.val,(supported_mul_iff _ _).mpr ⟨t.val.1.property,t.val.2.2.property⟩⟩)

lemma multiply_gcdTriple (p : SupportedIdeal×SupportedIdeal) : multiplyTriple (gcdTriple p)=p := by
  apply Prod.ext <;> apply Subtype.ext
  · exact gcd_common_left _ _
  · exact gcd_common_right _ _

lemma gcdTriple_multiply (t : CoprimeTriple) : gcdTriple (multiplyTriple t)=t := by
  have he : gcd (t.val.1.val*t.val.2.1.val) (t.val.1.val*t.val.2.2.val)=t.val.1.val := by
    rw [_root_.gcd_mul_left,normalize_eq,Ideal.isCoprime_iff_gcd.mp t.property,mul_one]
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext he
  · apply Prod.ext <;> apply Subtype.ext
    · change idealQuotient (gcd _ _) (t.val.1.val*t.val.2.1.val)=t.val.2.1.val
      dsimp only [multiplyTriple]
      rw [he]
      exact mul_left_cancel₀ t.val.1.property.1 (idealQuotient_mul (dvd_mul_right _ _))
    · change idealQuotient (gcd _ _) (t.val.1.val*t.val.2.2.val)=t.val.2.2.val
      dsimp only [multiplyTriple]
      rw [he]
      exact mul_left_cancel₀ t.val.1.property.1 (idealQuotient_mul (dvd_mul_right _ _))

def gcdPairEquiv : (SupportedIdeal×SupportedIdeal)≃CoprimeTriple where
  toFun := gcdTriple
  invFun := multiplyTriple
  left_inv := multiply_gcdTriple
  right_inv := gcdTriple_multiply

lemma gcdPair_tsum (f : SupportedIdeal×SupportedIdeal→ℂ) :
    (∑'p,f p)=∑'t : CoprimeTriple,f (multiplyTriple t) := by
  exact (gcdPairEquiv.symm.tsum_eq f).symm

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1716

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramIdealDilation.lean; sha256: bafa64cc4010869a50b843696ef9cf457602e3e791172166b520f998cd1faa5f -/
section Source1717
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev DivisibleSupported (D : SupportedIdeal) := {I : SupportedIdeal // D.val∣I.val}

def supportedIdealProduct (D J : SupportedIdeal) : SupportedIdeal :=
  ⟨D.val*J.val,(supported_mul_iff _ _).mpr ⟨D.property,J.property⟩⟩

def supportedDilationEquiv (D : SupportedIdeal) : SupportedIdeal≃DivisibleSupported D where
  toFun J := ⟨supportedIdealProduct D J,dvd_mul_right _ _⟩
  invFun I := ⟨idealQuotient D.val I.val.val,gram_supported_quotient I.val.val D.val I.val.property I.property⟩
  left_inv J := by
    apply Subtype.ext
    exact mul_left_cancel₀ D.property.1 (idealQuotient_mul (dvd_mul_right D.val J.val))
  right_inv I := by
    apply Subtype.ext
    apply Subtype.ext
    exact idealQuotient_mul I.property

lemma supported_dilation_generator (D J : SupportedIdeal) :
    primaryGenerator (supportedIdealProduct D J).val=primaryGenerator D.val*primaryGenerator J.val :=
  primaryGenerator_mul _ _

lemma supported_dilation_norm (D J : SupportedIdeal) :
    Ideal.absNorm (supportedIdealProduct D J).val=Ideal.absNorm D.val*Ideal.absNorm J.val :=
  map_mul Ideal.absNorm _ _

theorem supported_divisor_tsum (D : SupportedIdeal) (f : SupportedIdeal→ℂ) :
    (∑'I : SupportedIdeal,if D.val∣I.val then f I else 0)=
      ∑'J : SupportedIdeal,f (supportedIdealProduct D J) := by
  change (∑'I : SupportedIdeal,({I : SupportedIdeal | D.val∣I.val}.indicator f) I)=_
  rw [←tsum_subtype (s:={I : SupportedIdeal | D.val∣I.val}) (f:=f)]
  exact (supportedDilationEquiv D).tsum_eq (fun I : DivisibleSupported D=>f I.val) |>.symm

theorem supported_divisor_pair_tsum (D : SupportedIdeal) (f : SupportedIdeal→SupportedIdeal→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      if D.val∣I.val ∧ D.val∣J.val then f I J else 0)=
      ∑'I : SupportedIdeal,∑'J : SupportedIdeal,
        f (supportedIdealProduct D I) (supportedIdealProduct D J) := by
  have hinner (I : SupportedIdeal) : (∑'J : SupportedIdeal,if D.val∣I.val ∧ D.val∣J.val then f I J else 0)=
      if D.val∣I.val then ∑'J : SupportedIdeal,f I (supportedIdealProduct D J) else 0 := by
    by_cases hI : D.val∣I.val
    · simp only [hI,true_and,ite_true]
      exact supported_divisor_tsum D (f I)
    · simp [hI]
  simp_rw [hinner]
  exact supported_divisor_tsum D (fun I=>∑'J : SupportedIdeal,f I (supportedIdealProduct D J))

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1717

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramMobiusPool.lean; sha256: 1e150d0e8e9ebb098b2a15c962b51d58b415aad1528504d7d0dc70311541585e -/
section Source1718
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentMobiusRegroup
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma divisorPool_supported (G : Finset SupportedIdeal) (D : Id) (hD : D∈divisorPool G Subtype.val) :
    Supported D := by
  obtain ⟨J,hJ,hd⟩ := Finset.mem_biUnion.mp hD
  exact gram_supported_divisor J.val D J.property ((mem_idealDivisors J.property.1).mp hd)

def poolDivisor (G : Finset SupportedIdeal) (D : Id) : SupportedIdeal :=
  if hD : D∈divisorPool G Subtype.val then ⟨D,divisorPool_supported G D hD⟩
  else ⟨1,by
    constructor
    · exact one_ne_zero
    · intro P hP
      change P∈normalizedFactors (1:Id) at hP
      rw [normalizedFactors_one] at hP
      simp at hP⟩

lemma poolDivisor_val (G : Finset SupportedIdeal) (D : Id) (hD : D∈divisorPool G Subtype.val) :
    (poolDivisor G D).val=D := by simp [poolDivisor,hD]

lemma finite_pair_eq_tsum (F G : Finset SupportedIdeal) (f : SupportedIdeal→SupportedIdeal→ℂ)
    (hf : ∀I J,I∉F ∨ J∉G→f I J=0) :
    (∑I∈F,∑J∈G,f I J)=∑'I : SupportedIdeal,∑'J : SupportedIdeal,f I J := by
  have hinner (I : SupportedIdeal) : (∑J∈G,f I J)=∑'J : SupportedIdeal,f I J :=
    (tsum_eq_sum (fun J hJ=>hf I J (Or.inr hJ))).symm
  simp_rw [hinner]
  symm
  apply tsum_eq_sum
  intro I hI
  simp only [hf I _ (Or.inl hI),tsum_zero]

theorem finite_pair_mobius_dilation (F G : Finset SupportedIdeal)
    (f : SupportedIdeal→SupportedIdeal→ℂ) (hf : ∀I J,I∉F ∨ J∉G→f I J=0) :
    (∑I∈F,∑J∈G,if IsCoprime I.val J.val then f I J else 0)=
      ∑D∈divisorPool G Subtype.val,(moebius D:ℂ)*
        ∑'I : SupportedIdeal,∑'J : SupportedIdeal,
          f (supportedIdealProduct (poolDivisor G D) I) (supportedIdealProduct (poolDivisor G D) J) := by
  rw [finite_pair_mobius F G Subtype.val Subtype.val (fun J _=>J.property.1) f]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hd := poolDivisor_val G D hD
  rw [finite_pair_eq_tsum F G (fun I J=>if D∣I.val ∧ D∣J.val then f I J else 0) (by
    intro I J h
    simp only [hf I J h,ite_self])]
  convert supported_divisor_pair_tsum (poolDivisor G D) f using 1
  rw [hd]

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1718

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramFrequency.lean; sha256: 7380b7aebc0a7f87f659c5fba68576ce595f1a87b08343fb8d94d008e79825bb -/
section Source1719
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

lemma actual_common_frequency_zero (C n₁ n₂ j : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂})) (hj : ¬C∣j) :
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) j=0 := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero C hC) (supported_element_ne_zero n₁ h₁))
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero C hC) (supported_element_ne_zero n₂ h₂))
  let : Fintype (O⧸Ideal.span {C*n₁}) := Fintype.ofFinite _
  let : Fintype (O⧸Ideal.span {C*n₂}) := Fintype.ofFinite _
  exact fullModulusCorrelation_eq_zero_of_common_not_dvd _ _ C j _ _
    (dvd_mul_right _ _) (dvd_mul_right _ _) hj

lemma tsum_element_divisible (C : O) (hC : C≠0) (f : O→ℂ) :
    (∑'j : O,if C∣j then f j else 0)=∑'k : O,f (C*k) := by
  have hinj : Function.Injective (fun k : O=>C*k) := fun _ _ h=>mul_left_cancel₀ hC h
  have hs : Function.support (fun j : O=>if C∣j then f j else 0)⊆Set.range (fun k : O=>C*k) := by
    intro j hj
    have hd : C∣j := by by_contra h;simp [h] at hj
    obtain ⟨k,rfl⟩ := hd
    exact ⟨k,rfl⟩
  have ht := hinj.tsum_eq hs
  calc
    _ = ∑'k : O,if C∣C*k then f (C*k) else 0 := ht.symm
    _ = _ := by simp only [dvd_mul_right,ite_true]

theorem actual_common_frequency_tsum (C n₁ n₂ : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂})) (W : O→ℂ) :
    (∑'j : O,actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) j*W j)=
      ∑'k : O,actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
        (supported_mul_elements C n₂ hC h₂) (C*k)*W (C*k) := by
  rw [←tsum_element_divisible C (supported_element_ne_zero C hC) (fun j=>
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) j*W j)]
  apply tsum_congr
  intro j
  by_cases hj : C∣j
  · rw [ite_eq_left hj]
  · rw [ite_eq_right hj,actual_common_frequency_zero C n₁ n₂ j hC h₁ h₂ hj,zero_mul]

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1719
