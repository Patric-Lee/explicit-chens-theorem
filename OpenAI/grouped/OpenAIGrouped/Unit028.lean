import OpenAIGrouped.Unit026
import OpenAIGrouped.Unit027
import OpenAIGrouped.Unit025
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import OpenAIGrouped.Unit009
import Mathlib.Algebra.BigOperators.Ring.Finset
import OpenAIGrouped.Unit017

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Detector/TupleScaling.lean; sha256: 7559d476cb2b2f5ddd9b5eacc8ec3b33c1738aef4e2f3ee4c1d8b1cf061e49a4 -/
section Source1120
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical

lemma sourceMellinWeight_subset (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q R : ℝ)
    (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (hQ : 0<Q) (hR : 0<R)
    (a x w z : ℂ) :
    ((Q^(-(3/2:ℝ)):ℝ):ℂ)*a*sourceMellinWeight W0 W1 (X/Q) (Y/Q) (Z*R) x w z=
      sourceMellinWeight W0 W1 X Y Z x w z*(Q:ℂ)^(z-w-1)*a*(R:ℂ)^(x+z-1) := by
  rw [sourceMellinWeight_marked W0 W1 (X/Q) (Y/Q) Z R hZ hR x w z]
  calc
    _ = a*(R:ℂ)^(x+z-1)*
        (((Q^(-(3/2:ℝ)):ℝ):ℂ)*sourceMellinWeight W0 W1 (X/Q) (Y/Q) Z x w z) := by ring
    _ = _ := by rw [sourceMellinWeight_rescaled W0 W1 X Y Z Q hX hY hQ x w z];ring

lemma tuple_norm_pos {K : ℕ} (p : Fin K→ActualEisensteinCubic.O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) : 0<elementNorm (∏i∈J,p i) := by
  apply elementNorm_pos
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)

end SevenEighths.ProbePhysical
end

end OAI

end Source1120

/- Original source: OAI/NumberTheory/DirichletL/Detector/SourceIntegrable.lean; sha256: f74394369c95acf0f8db7a9cbc53f6e2e51764b3c6c7a0ef5d8987f730d2bf06 -/
section Source1121
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩

lemma sourceRows_initial_integrable (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun p : HeightSpace=>
      sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
        ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
      sourceRowSeries η S (calibrationForSet S hS) D ((3:ℂ)+p.1.1*Complex.I)
        ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  have hi := rawSourceOnLines_integrable η S hS D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ
  apply hi.integral_prod_right.congr
  filter_upwards [hi.prod_left_ae] with p hp
  rw [integral_count_eq_tsum _ hp]
  have he := rawArithmeticSeries_eq_sixth_high S hS hpS hbad D η
    ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
  change rawArithmeticSeries S D η (calibrationForSet S hS) _ _ _=
    sourceRowSeries η S (calibrationForSet S hS) D _ _ _ at he
  rw [←he,rawArithmeticSeries_eq_sourceRaw]
  simp only [rawSourceOnLines,initialHighOnLines,Complex.ofReal_ofNat,tsum_mul_right]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1121

/- Original source: OAI/NumberTheory/DirichletL/Detector/TupleMellin.lean; sha256: 1bdc62ad9e68d44931270a8d636c3220809fd6e7c6b81a99aa84487b16acb879 -/
section Source1122
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def tupleSourceSeries {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (x w z : ℂ) : ℂ :=
  ∑J∈(Finset.univ:Finset (Fin K)).powerset,
    (-1:ℂ)^J.card*(elementNorm (∏i∈J,p i):ℂ)^(z-w-1)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
      (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(x+z-1)*
      sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z

def tupleSourceTripleIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (W0 W1 : SchwartzMap ℝ ℂ) (p : Fin K→O) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    tupleSourceSeries η S C p ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I) ∂heightMeasure

theorem compensatedTuple_eq_source_triple {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (p : Fin K→O) (hp : ∀i,p i≠0)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      tupleSourceTripleIntegral η S (calibrationForSet S hS) W0 W1 p X Y Z := by
  let A : Finset (Fin K)→ℂ := fun J=>(-1:ℂ)^J.card*
    ((elementNorm (∏i∈J,p i)^(-(3/2:ℝ)):ℝ):ℂ)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))
  let F : Finset (Fin K)→HeightSpace→ℂ := fun J t=>
    sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
      (Z*elementNorm (∏i∈Finset.univ\J,p i))
      ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    sourceRowSeries η S (calibrationForSet S hS) (Ideal.span {∏i∈Finset.univ\J,p i})
      ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
  have hF (J : Finset (Fin K)) : Integrable (F J) heightMeasure :=
    sourceRows_initial_integrable η S hS hpS hbad _ W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
      (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J)))
  have hpoint (J : Finset (Fin K)) (t : HeightSpace) :
      A J*F J t=sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
        ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
      ((-1:ℂ)^J.card*(elementNorm (∏i∈J,p i):ℂ)^(((2:ℂ)+t.1.2*Complex.I)-((3:ℂ)+t.2*Complex.I)-1)*
        star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
        (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(((3:ℂ)+t.1.1*Complex.I)+((2:ℂ)+t.1.2*Complex.I)-1)*
        sourceRowSeries η S (calibrationForSet S hS) (Ideal.span {∏i∈Finset.univ\J,p i})
          ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)) := by
    have he := sourceMellinWeight_subset W0 W1 X Y Z (elementNorm (∏i∈J,p i))
      (elementNorm (∏i∈Finset.univ\J,p i)) hX hY hZ (tuple_norm_pos p hp J)
      (tuple_norm_pos p hp (Finset.univ\J))
      (star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i)))
      ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
    dsimp only [A,F]
    linear_combination (-1:ℂ)^J.card * he *
      sourceRowSeries η S (calibrationForSet S hS) (Ideal.span {∏i∈Finset.univ\J,p i})
        ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
  have hleft : compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ∑J∈(Finset.univ:Finset (Fin K)).powerset,∫t,A J*F J t ∂heightMeasure := by
    unfold compensatedTuple ProbeCompensation.tupleOperation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only
    rw [markedPhysicalProbe_eq_source_triple η S hS hpS hbad hSne _ W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
      (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J)))]
    rw [integral_const_mul]
    change A J*(((1/(2*Real.pi):ℝ):ℂ)^3*∫t,F J t ∂heightMeasure)=_
    ring
  rw [hleft,←integral_finsetSum _ (fun J _=>(hF J).const_mul (A J))]
  unfold tupleSourceTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  unfold tupleSourceSeries
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun J _=>hpoint J t)

end SevenEighths.ProbePhysical
end

end OAI

end Source1122

/- Original source: OAI/NumberTheory/DirichletL/Detector/TupleProducts.lean; sha256: 505618146e7e32b27f8701284e7effa8fec3b8d2f415beb135975dac103d74ed -/
section Source1123
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

lemma tuple_norm_cpow {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0)
    (J : Finset (Fin K)) (s : ℂ) :
    (elementNorm (∏i∈J,p i):ℂ)^s=∏i∈J,(elementNorm (p i):ℂ)^s := by
  induction J using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,elementNorm_one,Complex.ofReal_one,Complex.one_cpow]
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi,elementNorm_mul,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (elementNorm_pos _ (hp i)).le (tuple_norm_pos p hp J).le,
      ih,Finset.prod_insert hi]

lemma tuple_target_star {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) :
    star (HeckeFamily.elementCoeff η (∏i∈J,p i))=∏i∈J,star (HeckeFamily.elementCoeff η (p i)) := by
  change star (ProbeRow.targetMonoid η (∏i∈J,p i))=_
  rw [map_prod,star_prod]
  rfl

lemma tuple_source_scalar {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) (x w z : ℂ) :
    (elementNorm (∏i∈J,p i):ℂ)^(z-w-1)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
      (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(x+z-1)=
    (∏i,(elementNorm (p i):ℂ)^(z-1))*
      (∏i∈J,(elementNorm (p i):ℂ)^(-w))*
      (∏i∈Finset.univ\J,star (HeckeFamily.elementCoeff η (p i))*(elementNorm (p i):ℂ)^x) := by
  rw [tuple_norm_cpow p hp J,tuple_norm_cpow p hp (Finset.univ\J),tuple_target_star]
  have he (i : Fin K) : (elementNorm (p i):ℂ)^(z-w-1)=
      (elementNorm (p i):ℂ)^(z-1)*(elementNorm (p i):ℂ)^(-w) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (elementNorm_pos _ (hp i)).ne')]
    congr 1
    ring
  have hf (i : Fin K) : (elementNorm (p i):ℂ)^(x+z-1)=
      (elementNorm (p i):ℂ)^(z-1)*(elementNorm (p i):ℂ)^x := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (elementNorm_pos _ (hp i)).ne')]
    congr 1
    ring
  simp only [he,hf,Finset.prod_mul_distrib]
  have hc := Finset.prod_sdiff (Finset.subset_univ J) (f:=fun i : Fin K=>(elementNorm (p i):ℂ)^(z-1))
  rw [←hc]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1123

/- Original source: OAI/NumberTheory/DirichletL/Detector/TupleRows.lean; sha256: ef7207fbf188d9a1dbaef6b2a3bcfb6ad0fa6b3a489fd3792310aa147753d9f6 -/
section Source1124
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sourceRowSummand_summable (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (D : Id) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re) :
    Summable (fun u : FreeRow=>star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      markedIdealHighSeries S D η u.val x w z) := by
  let e : FreeRow×((Id×Id)×(Id×Id))→FullHighIndex := fun p=>(⟨p.1.val,p.1.property.1⟩,p.2)
  have he : Function.Injective e := by
    intro a b h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun t : FullHighIndex=>t.1.val) h
    · exact congrArg (fun t : FullHighIndex=>t.2) h
  have hs := (fullHighSummand_summable S D η x w z hx hw hz
    (fun H=>star (C.residueMonoid H.val))
    (fun H=>by simpa only [norm_star] using C.residueMonoid_norm_le_one H.val)).comp_injective he
  have ht := hs.prod
  apply ht.congr
  intro u
  dsimp only [Function.comp_def,e]
  exact tsum_mul_left (a:=star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩)
    (f:=fun c : (Id×Id)×(Id×Id)=>markedIdealHighSummand S D η u.val x w z c.1.1 c.1.2 c.2.1 c.2.2)

def tupleIndexedCoefficient {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) (x w : ℂ) : ℂ :=
  (-1:ℂ)^J.card*(∏i∈J,(elementNorm (p i):ℂ)^(-w))*
    (∏i∈Finset.univ\J,star (HeckeFamily.elementCoeff η (p i))*(elementNorm (p i):ℂ)^x)

def indexedCompensatedHigh {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (p : Fin K→O) (u : O) (x w z : ℂ) : ℂ :=
  ∑J∈(Finset.univ:Finset (Fin K)).powerset,tupleIndexedCoefficient η p J x w*
    markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z

lemma tupleSourceSeries_common_scale {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0) (x w z : ℂ) :
    tupleSourceSeries η S C p x w z=
      (∏i,(elementNorm (p i):ℂ)^(z-1))*
        ∑J∈(Finset.univ:Finset (Fin K)).powerset,tupleIndexedCoefficient η p J x w*
          sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z := by
  unfold tupleSourceSeries
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have he := tuple_source_scalar η p hp J x w z
  unfold tupleIndexedCoefficient
  linear_combination (-1:ℂ)^J.card*he*
    sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z

theorem tupleSourceSeries_eq_rows {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re) :
    tupleSourceSeries η S C p x w z=
      (∏i,(elementNorm (p i):ℂ)^(z-1))*
        ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
          indexedCompensatedHigh η S p u.val x w z := by
  rw [tupleSourceSeries_common_scale η S C p hp]
  congr 1
  let f : Finset (Fin K)→FreeRow→ℂ := fun J u=>tupleIndexedCoefficient η p J x w*
    (star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u.val x w z)
  have hf (J : Finset (Fin K)) : Summable (f J) :=
    (sourceRowSummand_summable η S C _ x w z hx hw hz).mul_left _
  have hsum := Summable.tsum_finsetSum (s:=(Finset.univ:Finset (Fin K)).powerset)
    (f:=f) (fun J _=>hf J)
  unfold sourceRowSeries
  simp only [←tsum_mul_left]
  change (∑J∈(Finset.univ:Finset (Fin K)).powerset,∑'u,f J u)=_
  rw [←hsum]
  apply tsum_congr
  intro u
  unfold indexedCompensatedHigh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  dsimp only [f]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1124

/- Original source: OAI/NumberTheory/DirichletL/Detector/MarkedLocal.lean; sha256: eb543169fd2fcdfd23d30d92490479dda536336b3cc6af63818bfb67cd855cb1 -/
section Source1125
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def idealMarkedLocalFactor (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∑e : Fin 2,∑'l,∑'k,∑'m,
    completedValuationMark P ((e.val,l),(k,m))*highPrimeTerm η x w z P ((e.val,l),(k,m))

lemma markedPrimeTerm_summable_norm (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun b : HighValuation=>‖completedValuationMark P b*highPrimeTerm η x w z P b‖) := by
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (highPrimeTerm_summable_norm η x w z hx hw hz P)
  intro b
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (completedValuationMark_norm P b)

lemma markedPrimeTerm_tsum (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (∑'b : HighValuation,completedValuationMark P b*highPrimeTerm η x w z P b)=
      idealMarkedLocalFactor η P x w z := by
  have hs := (markedPrimeTerm_summable_norm η P x w z hx hw hz).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) : (∑'b : ℕ×ℕ,completedValuationMark P ((e,l),b)*highPrimeTerm η x w z P ((e,l),b))=
      ∑'k,∑'m,completedValuationMark P ((e,l),(k,m))*highPrimeTerm η x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [highPrimeTerm_zero_of_two_le η x w z P e _ _ _ hh,mul_zero,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

lemma selectedLocal_outside (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (∑'b : HighValuation,ProbeEulerFinsupp.markedLocal T completedValuationMark
      (excludedHighPrimeTerm S η x w z) P b)=
      if P∈T then idealMarkedLocalFactor η P x w z else idealHighLocalFactor η P.val x w z := by
  have he (b : HighValuation) : excludedHighPrimeTerm S η x w z P b=highPrimeTerm η x w z P b := by
    simp only [excludedHighPrimeTerm,excludedHighArray,markedIdealHighSummand,
      highIdealMask_prime_outside S hS P hP,one_mul,highPrimeTerm]
  simp only [ProbeEulerFinsupp.markedLocal,he]
  by_cases hPT : P∈T
  · simp only [ite_eq_left hPT]
    exact markedPrimeTerm_tsum η P x w z hx hw hz
  · simp only [ite_eq_right hPT,one_mul]
    exact highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz P

lemma idealMarkedLocalFactor_eq_source (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    let p := primaryGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    letI : (Ideal.span {p}:Id).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hg := (supported_prime_data p hp ((span_primaryGenerator_of_supported P.val hs).symm ▸ hs)).1
    idealMarkedLocalFactor η P x w z=
      principalMarkedSeries p hp hg (targetMonoid η p) (actualACube η p)
        ((Ideal.absNorm P.val:ℂ)^(-x)) ((Ideal.absNorm P.val:ℂ)^(-w))
        (coordV (Ideal.absNorm P.val) z) := by
  dsimp only
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Id).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  unfold idealMarkedLocalFactor principalMarkedSeries principalInner
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  change completedValuationMark P ((e.val,l),(k,m))*bareIdealHighSummand η 1 x w z
    (P.val^e.val) (P.val^l) (P.val^k) (P.val^m)=_
  have hterm := bareIdealHighSummand_at_prime η p hp hg.1 hg.2 hprimary hsp e.val l k m (by omega) x w z
  conv_lhs at hterm => rw [hspan]
  rw [hterm]
  by_cases ht : e.val+3*l=0
  · have he0 : e.val=0 := by omega
    have hl0 : l=0 := by omega
    simp only [completedValuationMark,ht,ne_eq,not_true_eq_false,ite_false,zero_mul]
    rw [he0,hl0]
    simpa only [hspan] using (markedTerm_zero_index p hp hg.1 (targetMonoid η p)
      (actualACube η p) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) k m).symm
  · simp only [completedValuationMark,ht,ne_eq,not_false_eq_true,ite_true,one_mul]
    simpa only [hspan] using sourcePrincipalTerm_pos p hp hg.1 (targetMonoid η p) (actualACube η p) x w z e.val l k m ht

end SevenEighths.ProbePhysical
end

end OAI

end Source1125

/- Original source: OAI/NumberTheory/DirichletL/Detector/EulerRegion.lean; sha256: 11b6a0464af2b386a26ad8a5ad67da54f983944c2ba11310625677e8db2fc911 -/
section Source1126
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma rpow_le_half (Q a : ℝ) (hQ : 4 ≤ Q) (ha : a ≤ -(1/2)) : Q^a ≤ 1/2 := by
  have hQ0 : 0 < Q := by linarith
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ0
  have hs2 := Real.sq_sqrt hQ0.le
  calc
    Q^a ≤ Q^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha
    _ = (Real.sqrt Q)⁻¹ := by rw [Real.rpow_neg hQ0.le, ← Real.sqrt_eq_rpow]
    _ ≤ 1/2 := by rw [← one_div, div_le_iff₀ hs]; nlinarith [Real.sqrt_nonneg Q]

theorem unramifiedClosed_second_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (7/8:ℝ) ≤ x.re) (hw : (19/20:ℝ) ≤ w.re) (hz : (33/200:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(363/200:ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(99/100:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(56/25:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(19/20:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(7/8:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(33/40:ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(19/20:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(363/200:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(363/200:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num)
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num)
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI

end Source1126

/- Original source: OAI/NumberTheory/DirichletL/Detector/GlobalRegion.lean; sha256: ad70278668b25b0aa988c583dca9632affebda26aa009a159dd5f92a20a6d2ee -/
section Source1127
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem unramifiedClosed_open_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (7/8:ℝ) ≤ x.re) (hw : (9/10:ℝ) ≤ w.re) (hz : (4/25:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(24/25:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(221/100:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(9/10:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(7/8:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(31/40:ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(9/10:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(17/10:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(17/10:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num)
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num)
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI

end Source1127

/- Original source: OAI/NumberTheory/DirichletL/Detector/EulerHolomorphic.lean; sha256: 18c6e835736b404bedb9916d1419aec59ff41b25b6687e1f649efc406c527752 -/
section Source1128
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma coordR_differentiable (Q : ℝ) (hQ : 0 < Q) (A z : ℂ) :
    Differentiable ℂ (fun x : ℂ => coordR Q A x z) := by
  unfold coordR
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  exact (((differentiable_const (4:ℂ)).sub (differentiable_id.const_mul 6)).sub_const (6*z)).const_cpow
    (Or.inl hn) |>.const_mul A

lemma coordD_differentiable (Q : ℝ) (hQ : 0 < Q) (eta v : ℂ) :
    Differentiable ℂ (fun x : ℂ => coordD Q eta v x) := by
  unfold coordD
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul (eta*star v)

lemma coordK_differentiable (Q : ℝ) (hQ : 0 < Q) (eta w : ℂ) :
    Differentiable ℂ (fun x : ℂ => coordK Q eta x w) := by
  unfold coordK
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  exact ((differentiable_id.neg.sub_const w).const_cpow (Or.inl hn)).const_mul (eta*(Q-1))

lemma unramifiedClosed_differentiableAt (Q : ℝ) (hQ : 0 < Q) (A eta v x w z : ℂ)
    (hR : 1-coordR Q A x z ≠ 0) (_hV : 1-coordV Q z ≠ 0)
    (hD : 1-coordD Q eta v x ≠ 0) :
    DifferentiableAt ℂ (fun s : ℂ => unramifiedClosed Q A eta v s w z) x := by
  have hr := coordR_differentiable Q hQ A z
  have hd := coordD_differentiable Q hQ eta v
  have hk := coordK_differentiable Q hQ eta w
  have hp : DifferentiableAt ℂ (fun s : ℂ =>
      markedFactor (coordR Q A s z) (coordV Q z) (Q:ℂ)⁻¹
        (coordK Q eta s w) (-coordD Q eta v s + coordW Q v w*coordR Q A s z) 1) x := by
    unfold markedFactor
    fun_prop (disch := assumption)
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  fun_prop (disch := assumption)

theorem principalClosed_analytic (Q : ℝ) (hQ : 4 ≤ Q) (A eta : ℂ)
    (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun s : ℂ => unramifiedClosed Q A eta 1 s 1 (1/6))
      {s : ℂ | 7/8 < s.re} := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hv : 1-coordV Q (1/6) ≠ 0 := by
    apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    norm_num
  have hdif : DifferentiableOn ℂ (fun s : ℂ => unramifiedClosed Q A eta 1 s 1 (1/6))
      {s : ℂ | 7/8 < s.re} := by
    intro s hs
    apply (unramifiedClosed_differentiableAt Q hQ0 A eta 1 s 1 (1/6) ?_ hv ?_).differentiableWithinAt
    · apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
      apply (coordR_norm_le Q hQ0 A s (1/6) hA).trans
      apply rpow_le_half Q _ hQ
      norm_num
      change (7/8:ℝ) < s.re at hs
      linarith
    · apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
      apply (coordD_norm_le Q hQ0 eta 1 s heta (by simp)).trans
      apply rpow_le_half Q _ hQ
      change (7/8:ℝ) < s.re at hs
      linarith
  exact hdif.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

end SevenEighths.ProbeEuler
end

end OAI

end Source1128

/- Original source: OAI/NumberTheory/DirichletL/Detector/GlobalHolomorphic.lean; sha256: b80c82079e56bf6188afc6b957d4e24c1346a2b50f90f835edb7439de0586591 -/
section Source1129
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma coordV_differentiable (Q : ℝ) (hQ : 0<Q) : Differentiable ℂ (coordV Q) := by
  unfold coordV
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact (differentiable_id.const_mul (-6)).const_cpow (Or.inl hn)

lemma coordW_differentiable (Q : ℝ) (hQ : 0<Q) (v : ℂ) : Differentiable ℂ (coordW Q v) := by
  unfold coordW
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul v

lemma coordR_z_differentiable (Q : ℝ) (hQ : 0<Q) (A x : ℂ) :
    Differentiable ℂ (fun z=>coordR Q A x z) := by
  unfold coordR
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact (((differentiable_id.const_mul 6).const_sub (4-6*x)).const_cpow (Or.inl hn)).const_mul A

lemma coordK_w_differentiable (Q : ℝ) (hQ : 0<Q) (eta x : ℂ) :
    Differentiable ℂ (fun w=>coordK Q eta x w) := by
  unfold coordK
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact ((differentiable_id.const_sub (-x)).const_cpow (Or.inl hn)).const_mul (eta*(Q-1))

lemma unramifiedClosed_differentiableAt_w (Q : ℝ) (hQ : 0<Q) (A eta v x w z : ℂ)
    (_hR : 1-coordR Q A x z≠0) (_hV : 1-coordV Q z≠0) (_hD : 1-coordD Q eta v x≠0) :
    DifferentiableAt ℂ (fun t=>unramifiedClosed Q A eta v x t z) w := by
  have hw := coordW_differentiable Q hQ v
  have hk := coordK_w_differentiable Q hQ eta x
  have hp : DifferentiableAt ℂ (fun t=>
      markedFactor (coordR Q A x z) (coordV Q z) (Q:ℂ)⁻¹
        (coordK Q eta x t) (-coordD Q eta v x+coordW Q v t*coordR Q A x z) 1) w := by
    unfold markedFactor
    fun_prop (disch := assumption)
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  fun_prop (disch := assumption)

lemma unramifiedClosed_differentiableAt_z (Q : ℝ) (hQ : 0<Q) (A eta v x w z : ℂ)
    (hR : 1-coordR Q A x z≠0) (hV : 1-coordV Q z≠0) (_hD : 1-coordD Q eta v x≠0) :
    DifferentiableAt ℂ (fun t=>unramifiedClosed Q A eta v x w t) z := by
  have hv := coordV_differentiable Q hQ
  have hr := coordR_z_differentiable Q hQ A x
  have hp : DifferentiableAt ℂ (fun t=>
      markedFactor (coordR Q A x t) (coordV Q t) (Q:ℂ)⁻¹
        (coordK Q eta x w) (-coordD Q eta v x+coordW Q v w*coordR Q A x t) 1) z := by
    unfold markedFactor
    fun_prop (disch := assumption)
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  fun_prop (disch := assumption)

lemma open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 7/8≤x.re) (hz : 4/25≤z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem unramifiedClosed_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedClosed Q A eta v x w z) {x : ℂ|7/8<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 7/8≤x.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun w=>unramifiedClosed Q A eta v x w z) {w : ℂ|9/10<w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hd := open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : 7/8≤x.re) :
    AnalyticOnNhd ℂ (fun z=>unramifiedClosed Q A eta v x w z) {z : ℂ|4/25<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

end SevenEighths.ProbeEuler
end

end OAI

end Source1129

/- Original source: OAI/NumberTheory/DirichletL/Detector/NormalProduct.lean; sha256: 5422bbcb8d26d29deb76d2b0f5a614720deadc0535b9928893c8fa533f107f63 -/
section Source1130
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeEuler

lemma factor_ne_zero_of_defect (a : ℂ) (ha : ‖a-1‖ ≤ 1/2) : a ≠ 0 := by
  intro h
  rw [h] at ha
  norm_num at ha

lemma norm_log_le_defect (a : ℂ) (ha : ‖a-1‖ ≤ 1/2) :
    ‖Complex.log a‖ ≤ (3/2:ℝ)*‖a-1‖ := by
  simpa only [add_sub_cancel] using Complex.norm_log_one_add_half_le_self ha

lemma log_summable_of_defect {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2) :
    Summable (fun i => ‖Complex.log (F i)‖) := by
  apply (hb.mul_left (3/2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  exact (norm_log_le_defect _ ((hF i).trans (hhalf i))).trans
    (mul_le_mul_of_nonneg_left (hF i) (by norm_num))

lemma product_eq_exp_log {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2) :
    (∏' i, F i) = Complex.exp (∑' i, Complex.log (F i)) := by
  apply HasProd.tprod_eq
  apply ((log_summable_of_defect F b hb hF hhalf).of_norm.hasSum.cexp).congr
  intro s
  apply Finset.prod_congr rfl
  intro i hi
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hF i).trans (hhalf i)))

lemma norm_log_sum_le {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2) :
    ‖∑' i, Complex.log (F i)‖ ≤ (3/2:ℝ) * ∑' i, b i := by
  have hs := log_summable_of_defect F b hb hF hhalf
  calc
    _ ≤ ∑' i, ‖Complex.log (F i)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' i, (3/2:ℝ)*b i := Summable.tsum_le_tsum
      (fun i => (norm_log_le_defect _ ((hF i).trans (hhalf i))).trans
        (mul_le_mul_of_nonneg_left (hF i) (by norm_num))) hs (hb.mul_left _)
    _ = _ := tsum_mul_left

theorem product_defect_le {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2)
    (hsmall : (∑' i, b i) ≤ 1/6) : ‖(∏' i, F i)-1‖ ≤ 1/2 := by
  have hlog := norm_log_sum_le F b hb hF hhalf
  have hlog1 : ‖∑' i, Complex.log (F i)‖ ≤ 1 := by linarith
  rw [product_eq_exp_log F b hb hF hhalf]
  exact (Complex.norm_exp_sub_one_le hlog1).trans (by linarith)

theorem normalProduct_analytic {ι : Type*} (F : ι → ℂ → ℂ) (b : ι → ℝ)
    (U : Set ℂ) (hU : IsOpen U) (hb : Summable b)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U)
    (hbound : ∀ i s, s ∈ U → ‖F i s-1‖ ≤ b i)
    (hhalf : ∀ i, b i ≤ 1/2) :
    AnalyticOnNhd ℂ (fun s => ∏' i, F i s) U := by
  have hlogs : ∀ i, DifferentiableOn ℂ (fun s => Complex.log (F i s)) U := by
    intro i
    apply (hF i).differentiableOn.clog
    intro s hs
    have hsmall : ‖F i s-1‖ < 1 := lt_of_le_of_lt ((hbound i s hs).trans (hhalf i)) (by norm_num)
    simpa only [add_sub_cancel] using Complex.mem_slitPlane_of_norm_lt_one hsmall
  have hd := Complex.differentiableOn_tsum_of_summable_norm (hb.mul_left (3/2)) hlogs hU
    (fun i s hs => (norm_log_le_defect _ ((hbound i s hs).trans (hhalf i))).trans
      (mul_le_mul_of_nonneg_left (hbound i s hs) (by norm_num)))
  apply DifferentiableOn.analyticOnNhd _ hU
  apply hd.cexp.congr
  intro s hs
  exact product_eq_exp_log (fun i => F i s) b hb (fun i => hbound i s hs) hhalf

end SevenEighths.ProbeEuler
end

end OAI

end Source1130

/- Original source: OAI/NumberTheory/DirichletL/Detector/PrincipalProduct.lean; sha256: aae40d351969536fa8e3faae9f588ba4b94f1ad0e0429e74bcdcce5da414a198 -/
section Source1131
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss SmoothMobiusCorrection
local notation "O" => ActualEisensteinCubic.O

def primeDefectBound (P : PrimeIdeal) : ℝ :=
  240 * (Ideal.absNorm P.val : ℝ) ^ (-(363/200:ℝ))

def principalLocal (eta : HeckeFamily.Character) (P : PrimeIdeal) (s : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm P.val) (actualAPhase eta (primaryGenerator P.val))
    (HeckeFamily.elementCoeff eta (primaryGenerator P.val)) 1 s 1 (1/6)

def principalCorrection (eta : HeckeFamily.Character) (S : Finset (Ideal O)) (s : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val ∉ S}, principalLocal eta P.val s

lemma primeDefectBound_nonneg (P : PrimeIdeal) : 0 ≤ primeDefectBound P := by
  unfold primeDefectBound
  positivity

lemma primeDefectBound_summable : Summable primeDefectBound := by
  have h : Summable (fun P : PrimeIdeal => ‖CubicEisenstein.fullIdealWeight ((363/200:ℝ):ℂ) P.val‖) :=
    (CubicEisenstein.fullIdealWeight_summable_norm ((363/200:ℝ):ℂ) (by norm_num)).comp_injective
      Subtype.val_injective
  apply (h.mul_left 240).congr
  intro P
  unfold primeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero, ite_false]
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

lemma principalLocal_bound (eta : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) (s : ℂ) (hs : 7/8 < s.re) :
    ‖principalLocal eta P s-1‖ ≤ primeDefectBound P := by
  apply unramifiedClosed_second_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one eta _
  · exact ProbeRow.targetMonoid_norm_le_one eta _
  · simp
  · exact hs.le
  · norm_num
  · norm_num

lemma principalLocal_analytic (eta : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) :
    AnalyticOnNhd ℂ (principalLocal eta P) {s : ℂ | 7/8 < s.re} := by
  apply principalClosed_analytic
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one eta _
  · exact ProbeRow.targetMonoid_norm_le_one eta _

theorem exists_uniform_principal_cutoff :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ (S : Finset (Ideal O)),
      (∀ P : PrimeIdeal, Ideal.absNorm P.val ≤ N → P.val ∈ S) →
      ∀ eta : HeckeFamily.Character,
        AnalyticOnNhd ℂ (principalCorrection eta S) {s : ℂ | 7/8 < s.re} ∧
        ∀ s : ℂ, 7/8 < s.re → ‖principalCorrection eta S s-1‖ ≤ 1/2 := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero primeDefectBound)).2 (1/6) (by norm_num)
  obtain ⟨F, hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P => Ideal.absNorm P.val))
  refine ⟨N, le_max_left _ _, ?_⟩
  intro S hS eta
  let T := {P : PrimeIdeal // P.val ∉ S}
  have hnot (P : T) : P.val ∉ F := by
    intro hm
    apply P.property
    apply hS P.val
    exact (Finset.le_sup (f := fun Q : PrimeIdeal => Ideal.absNorm Q.val) hm).trans (le_max_right _ _)
  let inc : T → {P : PrimeIdeal // P ∉ F} := fun P => ⟨P.val, hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    apply Subtype.ext
    exact congrArg (fun t : {P : PrimeIdeal // P ∉ F} => t.val) h
  have hnorm (P : T) : 4 ≤ Ideal.absNorm P.val.val := by
    have hh : ¬ Ideal.absNorm P.val.val ≤ N := fun h => P.property (hS P.val h)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hh))
  have hsum : Summable (fun P : T => primeDefectBound P.val) :=
    primeDefectBound_summable.subtype _
  have hsmall : (∑' P : T, primeDefectBound P.val) ≤ 1/6 := by
    apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _ => primeDefectBound_nonneg P.val) (fun _ => le_rfl)
      hsum (primeDefectBound_summable.subtype _)
  have hhalf (P : T) : primeDefectBound P.val ≤ 1/2 := by
    have hterm := Summable.le_tsum hsum P (fun Q _ => primeDefectBound_nonneg Q.val)
    linarith
  constructor
  · exact normalProduct_analytic (fun P : T => principalLocal eta P.val)
      (fun P : T => primeDefectBound P.val) _ (Complex.isOpen_re_gt _) hsum
      (fun P => principalLocal_analytic eta P.val (hnorm P))
      (fun P s hs => principalLocal_bound eta P.val (hnorm P) s hs) hhalf
  · intro s hs
    exact product_defect_le (fun P : T => principalLocal eta P.val s)
      (fun P : T => primeDefectBound P.val) hsum
      (fun P => principalLocal_bound eta P.val (hnorm P) s hs) hhalf hsmall

def smallPrimeSet (N : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le N).toFinset.filter Prime

lemma mem_smallPrimeSet (N : ℕ) (P : PrimeIdeal) :
    P.val ∈ smallPrimeSet N ↔ Ideal.absNorm P.val ≤ N := by
  simp [smallPrimeSet, P.property]

theorem exists_principal_correction (S₀ : Finset (Ideal O)) :
    ∃ S : Finset (Ideal O), S₀ ⊆ S ∧ ∀ eta : HeckeFamily.Character,
      AnalyticOnNhd ℂ (principalCorrection eta S) {s : ℂ | 7/8 < s.re} ∧
      ∀ s : ℂ, 7/8 < s.re → ‖principalCorrection eta S s-1‖ ≤ 1/2 := by
  obtain ⟨N, hN, hcut⟩ := exists_uniform_principal_cutoff
  refine ⟨S₀ ∪ smallPrimeSet N, Finset.subset_union_left, ?_⟩
  apply hcut
  intro P hP
  exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

end SevenEighths.ProbeEuler
end

end OAI

end Source1131

/- Original source: OAI/NumberTheory/DirichletL/Detector/GlobalCorrection.lean; sha256: 93fe6f7968ef080b15cfe60b0f007948c6acee2949a8d8f8cce83e8ca2cb49a6 -/
section Source1132
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def globalPrimeDefectBound (P : PrimeIdeal) : ℝ :=
  240*(Ideal.absNorm P.val:ℝ)^(-(17/10:ℝ))

def globalClosedCorrection (η : HeckeFamily.Character) (S : Finset Id) (x w z : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val∉S},idealClosedCorrection η P.val x w z

lemma globalPrimeDefectBound_nonneg (P : PrimeIdeal) : 0≤globalPrimeDefectBound P := by
  unfold globalPrimeDefectBound
  positivity

lemma globalPrimeDefectBound_summable : Summable globalPrimeDefectBound := by
  have h := (CubicEisenstein.fullIdealWeight_summable_norm ((17/10:ℝ):ℂ) (by norm_num)).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*‖CubicEisenstein.fullIdealWeight ((17/10:ℝ):ℂ) P.val‖=globalPrimeDefectBound P
  unfold globalPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

structure CorrectionTail (S : Finset Id) : Prop where
  norm_four : ∀P : PrimeIdeal,P.val∉S → 4≤Ideal.absNorm P.val
  small : (∑' P : {P : PrimeIdeal // P.val∉S},globalPrimeDefectBound P.val)≤1/6

lemma CorrectionTail.summable {S : Finset Id} (_h : CorrectionTail S) :
    Summable (fun P : {P : PrimeIdeal // P.val∉S}=>globalPrimeDefectBound P.val) :=
  globalPrimeDefectBound_summable.subtype _

lemma CorrectionTail.half {S : Finset Id} (h : CorrectionTail S)
    (P : {P : PrimeIdeal // P.val∉S}) : globalPrimeDefectBound P.val≤1/2 := by
  have hh := Summable.le_tsum h.summable P (fun Q _=>globalPrimeDefectBound_nonneg Q.val)
  linarith [h.small]

lemma idealClosedCorrection_bound (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 7/8≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤globalPrimeDefectBound P := by
  apply unramifiedClosed_open_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem globalClosedCorrection_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 7/8≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=>idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma globalClosedCorrection_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 7/8≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤B P :=
    idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem globalClosedCorrection_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun x=>globalClosedCorrection η S x w z) {x : ℂ|7/8<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem globalClosedCorrection_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : 7/8≤x.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun w=>globalClosedCorrection η S x w z) {w : ℂ|9/10<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem globalClosedCorrection_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : 7/8≤x.re) (hw : 9/10≤w.re) :
    AnalyticOnNhd ℂ (fun z=>globalClosedCorrection η S x w z) {z : ℂ|4/25<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

theorem globalClosedCorrection_principal (η : HeckeFamily.Character) (S : Finset Id)
    (hs : ∀P : PrimeIdeal,P.val∉S → CanonicalQuadraticSieve.Supported P.val) (x : ℂ) :
    globalClosedCorrection η S x 1 (1/6)=principalCorrection η S x := by
  apply tprod_congr
  intro P
  unfold idealClosedCorrection principalLocal
  rw [←targetMonoid_primaryGenerator η P.val.val (hs P.val P.property)]
  rfl

theorem exists_uniform_global_cutoff :
    ∃N : ℕ,4≤N ∧ ∀S : Finset Id,
      (∀P : PrimeIdeal,Ideal.absNorm P.val≤N → P.val∈S) → CorrectionTail S := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero globalPrimeDefectBound)).2 (1/6) (by norm_num)
  obtain ⟨F,hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P=>Ideal.absNorm P.val))
  refine ⟨N,le_max_left _ _,?_⟩
  intro S hS
  let T := {P : PrimeIdeal // P.val∉S}
  have hnot (P : T) : P.val∉F := by
    intro hm
    exact P.property (hS P.val ((Finset.le_sup (f:=fun P : PrimeIdeal=>Ideal.absNorm P.val) hm).trans (le_max_right _ _)))
  let inc : T→{P : PrimeIdeal // P∉F} := fun P=>⟨P.val,hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun P : {P : PrimeIdeal // P∉F}=>P.val) h)
  constructor
  · intro P hP
    have hn : ¬Ideal.absNorm P.val≤N := fun hn=>hP (hS P hn)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
  · apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _=>globalPrimeDefectBound_nonneg P.val) (fun _=>le_rfl)
      (globalPrimeDefectBound_summable.subtype _) (globalPrimeDefectBound_summable.subtype _)

theorem exists_global_correction (S₀ : Finset Id) :
    ∃S : Finset Id,S₀⊆S ∧ CorrectionTail S := by
  obtain ⟨N,hN,hcut⟩ := exists_uniform_global_cutoff
  refine ⟨S₀∪smallPrimeSet N,Finset.subset_union_left,hcut _ ?_⟩
  intro P hP
  exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

end SevenEighths.ProbePhysical
end

end OAI

end Source1132

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighLFactorization.lean; sha256: d8c8a3a586e22d112f6f91b080c8d1fbb7fa8cfa177bfdf93ba12d3abe18df29 -/
section Source1133
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem principalHigh_L_factorization (S : Finset Id) (hS : ∀P∈S,Prime P)
    (hgood : ∀P : PrimeIdeal,P.val∉S → Supported P.val) (htail : CorrectionTail S)
    (η : Character) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η 1 x w z =
      LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (fixedSourcePrincipal S hS) w /
        LFunction (η.excludePrimes S hS) x * globalClosedCorrection η S x w z := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by
    norm_num [Complex.mul_re]
    linarith
  have hH := globalClosedCorrection_multipliable η S htail x w z (by linarith) (by linarith) (by linarith)
  have he := (((fixedSourcePrincipal_hasProd S hS (6*z) hz1).mul
    (fixedSourcePrincipal_hasProd S hS w hw1)).mul
      ((excludedTarget_hasProd η S hS x hx1).inv₀
        (LFunction_ne_zero_of_one_lt_re (η.excludePrimes S hS) hx1))).mul hH.hasProd
  have hlocal (P : {P : PrimeIdeal // P.val∉S}) :
      ((1-CubicEisenstein.fullIdealWeight (6*z) P.val.val)⁻¹ *
       (1-CubicEisenstein.fullIdealWeight w P.val.val)⁻¹ *
       ((1-idealCoeff η P.val.val*CubicEisenstein.fullIdealWeight x P.val.val)⁻¹)⁻¹) *
       idealClosedCorrection η P.val x w z = idealHighLocalFactor η P.val.val x w z := by
    rw [idealHighLocalFactor_rational η P.val (hgood P.val P.property) x w z hx hw hz]
    simp only [CubicEisenstein.fullIdealWeight,P.val.property.ne_zero,ite_false,
      Complex.ofReal_natCast,div_eq_mul_inv,mul_inv_rev,inv_inv]
    rw [show -(6*z)=(-6:ℂ)*z by ring]
    ring
  have he' : HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealHighLocalFactor η P.val.val x w z)
      (LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (fixedSourcePrincipal S hS) w /
        LFunction (η.excludePrimes S hS) x * globalClosedCorrection η S x w z) := by
    simpa only [hlocal,div_eq_mul_inv,globalClosedCorrection] using he
  exact (excludedIdealHighSeries_hasProd_outside S hS η x w z hx hw hz).unique he'

end SevenEighths.ProbePhysical
end

end OAI

end Source1133

/- Original source: OAI/NumberTheory/DirichletL/Detector/SourceExclusions.lean; sha256: 1430bb9bf9e3d40b8162a9155578ac7c9e80c3d8416016614ebdc4e0533fffcd -/
section Source1134
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid ProbeEuler
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma outside_prime_supported (S : Finset Id) (hbad : fixedBadPrimes⊆S)
    (P : PrimeIdeal) (hP : P.val∉S) : Supported P.val := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  refine ⟨P.property.ne_zero,?_⟩
  intro Q hQ
  have heq : Q=P.val := by
    simpa only [normalizedFactors_irreducible P.property.irreducible,normalize_eq,
      Multiset.mem_singleton] using hQ
  subst Q
  exact (prime_good_iff_not_bad P.val).mpr (fun h=>hP (hbad h))

structure SourceExclusions (S : Finset Id) : Prop where
  prime : ∀P∈S,Prime P
  bad : fixedBadPrimes⊆S
  tail : CorrectionTail S

theorem exists_source_exclusions (S₀ : Finset Id) (hp : ∀P∈S₀,Prime P)
    (hbad : fixedBadPrimes⊆S₀) :
    ∃S : Finset Id,S₀⊆S ∧ SourceExclusions S := by
  obtain ⟨N,hN,hcut⟩ := exists_uniform_global_cutoff
  refine ⟨S₀∪smallPrimeSet N,Finset.subset_union_left,?_⟩
  constructor
  · intro P hP
    rcases Finset.mem_union.mp hP with hP|hP
    · exact hp P hP
    · exact (Finset.mem_filter.mp hP).2
  · exact hbad.trans Finset.subset_union_left
  · apply hcut
    intro P hP
    exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

theorem source_principalHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η 1 x w z =
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
        HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z :=
  principalHigh_L_factorization S hS.prime (outside_prime_supported S hS.bad) hS.tail η x w z hx hw hz

theorem source_globalCorrection_principal (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (x : ℂ) :
    globalClosedCorrection η S x 1 (1/6)=principalCorrection η S x :=
  globalClosedCorrection_principal η S (outside_prime_supported S hS.bad) x

end SevenEighths.ProbePhysical
end

end OAI

end Source1134

/- Original source: OAI/NumberTheory/DirichletL/Detector/MarkedProduct.lean; sha256: efbc67fd5af2c9e1137415b22e5d5b82b74baa46e1ded3b979a187a098b97f1e -/
section Source1135
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler ProbeEulerFinsupp
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma source_idealHighLocalFactor_ne_zero (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    idealHighLocalFactor η P.val x w z≠0 := by
  rw [idealHighLocalFactor_rational η P (outside_prime_supported S hS.bad P hP) x w z hx hw hz]
  have hQ : (1:ℝ)<Ideal.absNorm P.val := by
    have hh := hS.tail.norm_four P hP
    exact_mod_cast (by omega : 1<Ideal.absNorm P.val)
  have hQ0 : (0:ℝ)<Ideal.absNorm P.val := by linarith
  have hD : ‖HeckeFamily.idealCoeff η P.val*(Ideal.absNorm P.val:ℂ)^(-x)‖<1 := by
    rw [norm_mul,Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0),Complex.neg_re]
    apply (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (HeckeFamily.idealCoeff_norm_le_one η P.val)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  have hV : ‖(Ideal.absNorm P.val:ℂ)^(-6*z)‖<1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0)]
    apply Real.rpow_lt_one_of_one_lt_of_neg hQ
    norm_num [Complex.mul_re]
    linarith
  have hW : ‖(Ideal.absNorm P.val:ℂ)^(-w)‖<1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0),Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  apply mul_ne_zero
  · exact div_ne_zero (one_sub_ne_zero_of_norm_lt_one _ hD)
      (mul_ne_zero (one_sub_ne_zero_of_norm_lt_one _ hV) (one_sub_ne_zero_of_norm_lt_one _ hW))
  · exact factor_ne_zero_of_defect _ ((idealClosedCorrection_bound η P (hS.tail.norm_four P hP)
      x w z (by linarith) (by linarith) (by linarith)).trans (hS.tail.half ⟨P,hP⟩))

theorem markedIdealHighSeries_eq_product (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z=
      markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z := by
  let R := fun P : PrimeIdeal=>if P∈T then
    idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z else 1
  have hR : HasProd R (∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R) (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := (excludedIdealHighSeries_hasProd S hS.prime η x w z hx hw hz).mul hR
  have heq (P : PrimeIdeal) :
      (∑'b : HighValuation,excludedHighPrimeTerm S η x w z P b)*R P=
      ∑'b : HighValuation,markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b := by
    by_cases hp : P∈T
    · rw [selectedLocal_outside S hS.prime T η P (hT P hp) x w z hx hw hz,ite_eq_left hp]
      have hu : (∑'b : HighValuation,excludedHighPrimeTerm S η x w z P b)=idealHighLocalFactor η P.val x w z := by
        simpa only [excludedHighPrimeTerm,excludedHighArray,ite_eq_right (hT P hp)] using
          excludedHighLocalFactor S hS.prime η x w z hx hw hz P
      rw [hu,show R P=idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z from ite_eq_left hp]
      exact mul_div_cancel₀ _ (source_idealHighLocalFactor_ne_zero S hS η P (hT P hp) x w z hx hw hz)
    · simp only [R,hp,ite_false,mul_one,markedLocal,one_mul]
  have he' : HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b)
      (markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z) := by
    convert he using 1
    funext P
    exact (heq P).symm
  exact (markedIdealHighSeries_hasProd S hS.prime T η x w z hx hw hz).unique he'

theorem source_markedHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z := by
  rw [markedIdealHighSeries_eq_product S hS T hT η x w z hx hw hz,
    source_principalHigh_L_factorization S hS η x w z hx hw hz]

end SevenEighths.ProbePhysical
end

end OAI

end Source1135

/- Original source: OAI/NumberTheory/DirichletL/Detector/MarkedRational.lean; sha256: 6a8890944d7f0a04f03919e98e0152c020bf3d4a1fba05255559dbcd20017eaf -/
section Source1136
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def idealMarkedClosed (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm P.val
  let R := coordR Q (actualAPhase η (primaryGenerator P.val)) x z
  markedFactor R (coordV Q z) (Q:ℂ)⁻¹ (coordK Q (HeckeFamily.idealCoeff η P.val) x w)
    (-coordD Q (HeckeFamily.idealCoeff η P.val) 1 x+coordW Q 1 w*R) 1

theorem idealMarkedLocalFactor_rational (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hx : 3/2<x.re) (hz : 1/6<z.re) :
    idealMarkedLocalFactor η P x w z=idealMarkedClosed η P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    rw [hspan]
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1 := by
    rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hr := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (actualACube η p) x z
  simp only [Complex.ofReal_natCast] at hr
  have he := principalMarkedSeries_eq p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p)
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) hV (by simpa only [hr] using hR)
  have hsource := idealMarkedLocalFactor_eq_source η P hs x w z
  dsimp only at hsource
  rw [hsource]
  have hk := coordK_eq_geometric (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (targetMonoid η p) x w
  simp only [Complex.ofReal_natCast] at hr hk
  rw [hr,←hk] at he
  simp only [actualACube_sq] at he
  convert he using 1
  · congr 2 <;> simp only [hspan,p]
  · simp only [idealMarkedClosed,coordD,coordW,star_one,mul_one,one_mul]
    simp only [hspan,p,targetMonoid_primaryGenerator η P.val hs,Complex.ofReal_natCast,neg_mul]

end SevenEighths.ProbePhysical
end

end OAI

end Source1136

/- Original source: OAI/NumberTheory/DirichletL/Detector/SpectralCompensation.lean; sha256: 381c5b2cc795b103df2bccb08c84e0e44a6af830085e5039c0079ad61dee1552 -/
section Source1137
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def spectralCompensatedHigh (S : Finset Id) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (x w z : ℂ) (B q : PrimeIdeal→ℂ) : ℂ :=
  ∑J∈T.powerset,(-1:ℂ)^J.card*(∏P∈J,q P)*(∏P∈T\J,B P)*
    markedIdealHighSeries S (∏P∈T\J,P.val) η 1 x w z

theorem spectralCompensatedHigh_eq_product (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedHigh S T η x w z B q=
      markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,(B P*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q P) := by
  rw [spectralCompensatedHigh,Finset.prod_sub,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [markedIdealHighSeries_eq_product S hS (T\J)
    (fun P hP=>hT P (Finset.mem_sdiff.mp hP).1) η x w z hx hw hz]
  simp only [mul_div_assoc,Finset.prod_mul_distrib]
  ring

theorem spectralCompensatedHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedHigh S T η x w z B q=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,(B P*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q P) := by
  rw [spectralCompensatedHigh_eq_product S hS T hT η x w z B q hx hw hz,
    source_principalHigh_L_factorization S hS η x w z hx hw hz]

end SevenEighths.ProbePhysical
end

end OAI

end Source1137

/- Original source: OAI/NumberTheory/DirichletL/Detector/CompensationActual.lean; sha256: c7f72f741d57675d44a573b4a6e0f2a62323f193e31b5462d57fe9d1535497ce -/
section Source1138
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler ProbeLocal
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma initialPrime_denominators (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 0<x.re) (hw : 0<w.re) (hz : 0<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    (1-coordV Q z≠0) ∧ (1-coordW Q 1 w≠0) ∧
      (1-coordD Q (HeckeFamily.idealCoeff η P.val) 1 x≠0) := by
  dsimp only
  have hQ : (1:ℝ)<Ideal.absNorm P.val := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 1<Ideal.absNorm P.val)
  have hQ0 : (0:ℝ)<Ideal.absNorm P.val := by linarith
  constructor
  · apply one_sub_ne_zero_of_norm_lt_one
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  constructor
  · apply one_sub_ne_zero_of_norm_lt_one
    apply (coordW_norm_le _ hQ0 1 w (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  · apply one_sub_ne_zero_of_norm_lt_one
    apply (coordD_norm_le _ hQ0 _ 1 x (HeckeFamily.idealCoeff_norm_le_one η P.val) (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)

lemma idealClosedCorrection_eq_continued (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) :
    let Q : ℝ := Ideal.absNorm P.val
    idealClosedCorrection η P x w z=continuedCorrection (coordV Q z) (coordW Q 1 w)
      (coordD Q (HeckeFamily.idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z) := rfl

lemma standardFactor_times_continued (V W D M : ℂ)
    (hV : 1-V≠0) (hW : 1-W≠0) (hD : 1-D≠0) :
    (1-D)/((1-V)*(1-W))*continuedCorrection V W D M=localFactor V W M := by
  unfold continuedCorrection localFactor
  field_simp
  ring

lemma idealHighLocalFactor_eq_raw (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : CanonicalQuadraticSieve.Supported P.val) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    idealHighLocalFactor η P.val x w z=
      localFactor (coordV Q z) (coordW Q 1 w) (idealMarkedClosed η P x w z) := by
  have hd := initialPrime_denominators η P x w z (by linarith) (by linarith) (by linarith)
  have he := idealHighLocalFactor_rational η P hs x w z hx hw hz
  have hc := standardFactor_times_continued (coordV (Ideal.absNorm P.val) z)
    (coordW (Ideal.absNorm P.val) 1 w) (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
    (idealMarkedClosed η P x w z) hd.1 hd.2.1 hd.2.2
  rw [←idealClosedCorrection_eq_continued] at hc
  dsimp only at he hc ⊢
  rw [he]
  simpa only [coordV,coordW,coordD,star_one,mul_one,one_mul] using hc

theorem idealCompensatedRatio_eq_continued (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z B q : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    B*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q=
      compensatedReplacement (coordV Q z) (coordW Q 1 w)
        (coordD Q (HeckeFamily.idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z) B q /
          idealClosedCorrection η P x w z := by
  have hs := outside_prime_supported S hS.bad P hP
  have hd := initialPrime_denominators η P x w z (by linarith) (by linarith) (by linarith)
  have hraw := idealHighLocalFactor_eq_raw η P hs x w z hx hw hz
  have hn := source_idealHighLocalFactor_ne_zero S hS η P hP x w z hx hw hz
  rw [hraw] at hn
  have hH : idealClosedCorrection η P x w z≠0 :=
    factor_ne_zero_of_defect _ ((idealClosedCorrection_bound η P (hS.tail.norm_four P hP)
      x w z (by linarith) (by linarith) (by linarith)).trans (hS.tail.half ⟨P,hP⟩))
  have he := compensatedReplacement_eq_raw (coordV (Ideal.absNorm P.val) z)
    (coordW (Ideal.absNorm P.val) 1 w) (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
    (idealMarkedClosed η P x w z) B q hd.1 hd.2.1 hd.2.2 hn
  rw [←continuedCorrection_eq_raw _ _ _ _ hd.1 hd.2.1 hd.2.2,
    ←idealClosedCorrection_eq_continued] at he
  dsimp only at hraw he ⊢
  rw [idealMarkedLocalFactor_rational η P hs x w z hx hz,hraw,he]
  exact (mul_div_cancel_left₀ _ hH).symm

theorem spectralCompensatedHigh_continued (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedHigh S T η x w z B q=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,(compensatedReplacement (coordV (Ideal.absNorm P.val) z)
          (coordW (Ideal.absNorm P.val) 1 w)
          (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
          (idealMarkedClosed η P x w z) (B P) (q P) / idealClosedCorrection η P x w z) := by
  rw [spectralCompensatedHigh_L_factorization S hS T hT η x w z B q hx hw hz]
  congr 1
  apply Finset.prod_congr rfl
  intro P hP
  exact idealCompensatedRatio_eq_continued S hS η P (hT P hP) x w z (B P) (q P) hx hw hz

end SevenEighths.ProbePhysical
end

end OAI

end Source1138

/- Original source: OAI/NumberTheory/DirichletL/Detector/TuplePrime.lean; sha256: 4591bab4c7fd1641ac05f04a4b9707ee51ebbb95ec81de015988581ec0cbc92f -/
section Source1139
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma span_tupleProduct {K : ℕ} (p : Fin K→O) (J : Finset (Fin K)) :
    Ideal.span {∏i∈J,p i}=∏i∈J,Ideal.span {p i} := by
  induction J using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Ideal.span_singleton_one,Ideal.one_eq_top]
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi,←Ideal.span_singleton_mul_span_singleton,ih,Finset.prod_insert hi]

lemma primaryTuple_norm (P : PrimeIdeal) (hP : Supported P.val) :
    elementNorm (primaryGenerator P.val)=(Ideal.absNorm P.val:ℝ) := by
  unfold elementNorm
  rw [span_primaryGenerator_of_supported P.val hP]

theorem indexedCompensatedHigh_principal {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hs : ∀i,Supported (P i).val)
    (x w z : ℂ) :
    indexedCompensatedHigh η S (fun i=>primaryGenerator (P i).val) 1 x w z=
      spectralCompensatedHigh S (Finset.univ.image P) η x w z
        (fun Q=>star (HeckeFamily.idealCoeff η Q.val)*(Ideal.absNorm Q.val:ℂ)^x)
        (fun Q=>(Ideal.absNorm Q.val:ℂ)^(-w)) := by
  unfold indexedCompensatedHigh spectralCompensatedHigh
  rw [Finset.powerset_image,Finset.sum_image (Finset.image_injective hP).injOn]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.card_image_of_injective J hP,←Finset.image_sdiff _ _ hP]
  simp only [Finset.prod_image hP.injOn]
  have hnorm (i : Fin K) : (elementNorm (primaryGenerator (P i).val):ℂ)=(Ideal.absNorm (P i).val:ℂ) := by
    rw [primaryTuple_norm (P i) (hs i)]
    norm_cast
  have hc (i : Fin K) : HeckeFamily.elementCoeff η (primaryGenerator (P i).val)=
      HeckeFamily.idealCoeff η (P i).val := targetMonoid_primaryGenerator η (P i).val (hs i)
  simp only [tupleIndexedCoefficient,hnorm,hc,span_tupleProduct,
    span_primaryGenerator_of_supported _ (hs _)]

end SevenEighths.ProbePhysical
end

end OAI

end Source1139

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/MarkedSubset.lean; sha256: dfe5f667a25ad9f65aa633a463918423225eb80fa6fbfc8fac913858a370b66b -/
section Source1140
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp
local notation "O" => HeckeFamily.O

theorem markedRowSeries_subset_replacement (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T J : Finset PrimeIdeal) (hJ : J⊆T) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T\J,P.val) η u x w z=
      markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        (∏P∈T\J,idealRowMarkedLocalFactor η u P x w z)*
        (∏P∈J,idealRowHighLocalFactor η u P.val x w z) := by
  let A := fun P : PrimeIdeal=>if P∈T\J then idealRowMarkedLocalFactor η u P x w z else 1
  let B := fun P : PrimeIdeal=>if P∈J then idealRowHighLocalFactor η u P.val x w z else 1
  have hA : HasProd A (∏P∈T\J,idealRowMarkedLocalFactor η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T\J) (f:=A)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [A,Finset.prod_ite_mem,Finset.inter_self] using hh
  have hB : HasProd B (∏P∈J,idealRowHighLocalFactor η u P.val x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=J) (f:=B)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [B,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := ((excludedIdealHighSeries_row_hasProd (markExclusions S T)
    (markExclusions_prime S hS T) η u x w z hx hw hz).mul hA).mul hB
  have heq (P : PrimeIdeal) :
      ((∑'b : HighValuation,markedIdealHighSummand (markExclusions S T) 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*A P)*B P=
      ∑'b : HighValuation,markedLocal (T\J) completedValuationMark
        (excludedRowPrimeTerm S η u x w z) P b := by
    rw [excludedRowHighLocalFactor _ (markExclusions_prime S hS T) η u x w z hx hw hz]
    by_cases hPJ : P∈J
    · have hPT := hJ hPJ
      have hPA : P∉T\J := by simp only [Finset.mem_sdiff]; tauto
      rw [ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hPT)),
        selectedRowLocal_outside S hS (T\J) η u P (hT P hPT) x w z hx hw hz,ite_eq_right hPA]
      simp only [A,B,ite_eq_right hPA,ite_eq_left hPJ,one_mul]
    · by_cases hPT : P∈T
      · have hPA : P∈T\J := Finset.mem_sdiff.mpr ⟨hPT,hPJ⟩
        rw [ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hPT)),
          selectedRowLocal_outside S hS (T\J) η u P (hT P hPT) x w z hx hw hz,ite_eq_left hPA]
        simp only [A,B,ite_eq_left hPA,ite_eq_right hPJ,one_mul,mul_one]
      · have hPA : P∉T\J := fun h=>hPT (Finset.mem_sdiff.mp h).1
        simp only [A,B,ite_eq_right hPA,ite_eq_right hPJ,mul_one,markedLocal,one_mul]
        change _=∑'b : HighValuation,markedIdealHighSummand S 1 η u x w z
          (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)
        rw [excludedRowHighLocalFactor S hS η u x w z hx hw hz]
        simp only [mem_markExclusions,hPT,or_false]
  apply (markedRowSeries_hasProd S hS (T\J) η u x w z hx hw hz).unique
  convert he using 1
  funext P
  exact (heq P).symm

def spectralCompensatedRow (S : Finset (Ideal O)) (T : Finset PrimeIdeal)
    (η : Character) (u : O) (x w z : ℂ) (B q : PrimeIdeal→ℂ) : ℂ :=
  ∑J∈T.powerset,(-1:ℂ)^J.card*(∏P∈J,q P)*(∏P∈T\J,B P)*
    markedIdealHighSeries S (∏P∈T\J,P.val) η u x w z

theorem spectralCompensatedRow_eq_product (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : O)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedRow S T η u x w z B q=
      markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,(B P*idealRowMarkedLocalFactor η u P x w z-
          q P*idealRowHighLocalFactor η u P.val x w z) := by
  rw [spectralCompensatedRow,Finset.prod_sub,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [markedRowSeries_subset_replacement S hS T J (Finset.mem_powerset.mp hJ) hT η u x w z hx hw hz]
  simp only [Finset.prod_mul_distrib]
  ring

theorem indexedCompensatedHigh_eq_spectral {K : ℕ} (η : Character) (S : Finset (Ideal O))
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hs : ∀i,CanonicalQuadraticSieve.Supported (P i).val) (u : O) (x w z : ℂ) :
    indexedCompensatedHigh η S (fun i=>CompletedGauss.primaryGenerator (P i).val) u x w z=
      spectralCompensatedRow S (Finset.univ.image P) η u x w z
        (fun Q=>star (idealCoeff η Q.val)*(Q.val.absNorm:ℂ)^x)
        (fun Q=>(Q.val.absNorm:ℂ)^(-w)) := by
  unfold indexedCompensatedHigh spectralCompensatedRow
  rw [Finset.powerset_image,Finset.sum_image (Finset.image_injective hP).injOn]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.card_image_of_injective J hP,←Finset.image_sdiff _ _ hP]
  simp only [Finset.prod_image hP.injOn]
  have hnorm (i : Fin K) : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)=
      ((P i).val.absNorm:ℂ) := by
    rw [primaryTuple_norm (P i) (hs i)]
    norm_cast
  have hc (i : Fin K) : elementCoeff η (CompletedGauss.primaryGenerator (P i).val)=
      idealCoeff η (P i).val := targetMonoid_primaryGenerator η (P i).val (hs i)
  simp only [tupleIndexedCoefficient,hnorm,hc,span_tupleProduct,
    span_primaryGenerator_of_supported _ (hs _)]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1140

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/FiniteNormalization.lean; sha256: 35060fe8342a6893577fc091838a308603cacb5a1a8a44fcc84dae548ca23706 -/
section Source1141
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def globalNormalization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  (LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
    (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x

theorem globalNormalization_finite_split (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 1<x.re) (hw : 1<w.re) (hz : 1<(6*z).re) :
    globalNormalization S hS η u x w z=
      globalNormalization (markExclusions S T) (markExclusions_prime S hS T) η u x w z*
        ∏P∈T,localNormalization η u P x w z := by
  have hleft := localNormalization_hasProd S hS hbad η u x w z hx hw hz
  have hbase := localNormalization_hasProd (markExclusions S T) (markExclusions_prime S hS T)
    (hbad.trans Finset.subset_union_left) η u x w z hx hw hz
  let R := fun P : PrimeIdeal=>if P∈T then localNormalization η u P x w z else 1
  have hR : HasProd R (∏P∈T,localNormalization η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  apply hleft.unique
  convert hbase.mul hR using 1
  · funext P
    by_cases hP : P∈T
    · simp only [ite_eq_right (hT P hP),mem_markExclusions,hP,or_true,ite_true,R,ite_eq_left hP,one_mul]
    · simp only [mem_markExclusions,hP,or_false,R,ite_eq_right hP,mul_one]
  · rfl

theorem finite_replacement_normalized (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (g : PrimeIdeal→ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (markedIdealHighSeries (markExclusions S T) 1 η u.val x w z*∏P∈T,g P)*
      globalNormalization S hS η u x w z=
      globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,g P*localNormalization η u P x w z := by
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  rw [globalNormalization_finite_split S hS hbad T hT η u x w z (by linarith) (by linarith) hz1,
    globalCorrection,(localCorrection_hasProd (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz).tprod_eq,
    Finset.prod_mul_distrib,globalNormalization]
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1141

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/MarkedCompensation.lean; sha256: 6263a2c392520556bfc5453dab8d272a51578cf58b69dc5ef5a07e7cc2b9cb61 -/
section Source1142
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def compensatedLocalCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (x w z B q : ℂ) : ℂ :=
  B*markedLocalCorrection η u P x w z-q*localCorrection η u P x w z

theorem compensatedLocalCorrection_eq_raw (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (x w z B q : ℂ) :
    compensatedLocalCorrection η u P x w z B q=
      (B*idealRowMarkedLocalFactor η u.val P x w z-q*idealRowHighLocalFactor η u.val P.val x w z)*
        localNormalization η u P x w z := by
  rw [compensatedLocalCorrection,markedLocalCorrection,localCorrection_eq_normalization]
  ring

theorem spectralCompensatedRow_original_L_factorization
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedRow S T η u.val x w z B q=
      (LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (rowCharacter S hS u) w/
        LFunction ((targetRow η u).excludePrimes S hS) x)*
      (globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,compensatedLocalCorrection η u P x w z (B P) (q P)) := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hZ := LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := LFunction_ne_zero_of_one_lt_re ((targetRow η u).excludePrimes S hS) hx1
  have hn := finite_replacement_normalized S hS hbad T hT η u x w z
    (fun P=>B P*idealRowMarkedLocalFactor η u.val P x w z-q P*idealRowHighLocalFactor η u.val P.val x w z)
    hx hw hz
  simp_rw [←compensatedLocalCorrection_eq_raw] at hn
  rw [←spectralCompensatedRow_eq_product S hS T hT η u.val x w z B q hx hw hz] at hn
  rw [←hn,globalNormalization]
  field_simp

theorem indexedCompensatedHigh_original_L_factorization {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    indexedCompensatedHigh η S (fun i=>CompletedGauss.primaryGenerator (P i).val) u.val x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (rowCharacter S hS.prime u) w/
        LFunction ((targetRow η u).excludePrimes S hS.prime) x)*
      (globalCorrection (markExclusions S (Finset.univ.image P)) η u x w z*
        ∏i,compensatedLocalCorrection η u (P i) x w z
          (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
          (((P i).val.absNorm:ℂ)^(-w))) := by
  have hs (i : Fin K) := outside_prime_supported S hS.bad (P i) (hPS i)
  rw [indexedCompensatedHigh_eq_spectral η S P hP hs u.val x w z]
  have ht : ∀Q∈Finset.univ.image P,Q.val∉S := by
    intro Q hQ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
    exact hPS i
  rw [spectralCompensatedRow_original_L_factorization S hS.prime hS.bad
    (Finset.univ.image P) ht η u x w z _ _ hx hw hz,Finset.prod_image hP.injOn]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1142

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsDiagonal.lean; sha256: 661fde25248dfde6aa250286691d9fe434fb688e0b928fb5099de2e5121483fe -/
section Source1143
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeEuler

theorem diagonal_recurrence_eq (f : ℕ→ℕ→ℂ) (R : ℂ)
    (hstep : ∀ r m,f (r+1) (m+1)=R*f r m) (hz : ∀ r,f (r+1) 0=0) :
    ∀ r m,f r m=if r≤m then R^r*f 0 (m-r) else 0 := by
  intro r
  induction r with
  | zero => intro m; simp
  | succ r ih =>
    intro m
    cases m with
    | zero => simp [hz]
    | succ m =>
      rw [hstep,ih]
      by_cases h : r≤m
      · simp only [h,ite_true,Nat.succ_le_succ_iff,Nat.succ_sub_succ_eq_sub,pow_succ]
        ring
      · simp only [h,ite_false,Nat.succ_le_succ_iff,mul_zero]

theorem diagonal_recurrence_inner_hasSum (f : ℕ→ℕ→ℂ) (R : ℂ)
    (hstep : ∀ r m,f (r+1) (m+1)=R*f r m) (hz : ∀ r,f (r+1) 0=0)
    (hs : Summable (f 0)) (r : ℕ) : HasSum (f r) (R^r*∑' m,f 0 m) := by
  have he := diagonal_recurrence_eq f R hstep hz
  have htail : HasSum (fun m=>f r (m+r)) (R^r*∑' m,f 0 m) := by
    convert hs.hasSum.mul_left (R^r) using 1
    funext m
    rw [he,ite_eq_left (Nat.le_add_left r m),Nat.add_sub_cancel]
  have hzero : (∑ m∈Finset.range r,f r m)=0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [he,ite_eq_right (by have := Finset.mem_range.mp hm; omega)]
  simpa only [hzero,zero_add] using htail.sum_range_add

theorem diagonal_recurrence_hasSum (f : ℕ→ℕ→ℂ) (R : ℂ)
    (hstep : ∀ r m,f (r+1) (m+1)=R*f r m) (hz : ∀ r,f (r+1) 0=0)
    (hs : Summable (f 0)) (hR : ‖R‖<1) :
    HasSum (fun r=>∑' m,f r m) ((∑' m,f 0 m)/(1-R)) := by
  have he (r : ℕ) := (diagonal_recurrence_inner_hasSum f R hstep hz hs r).tsum_eq
  have hg : HasSum (fun r=>R^r*(∑' m,f 0 m)) ((∑' m,f 0 m)/(1-R)) := by
    simpa only [div_eq_mul_inv,mul_comm] using
      (hasSum_geometric_of_norm_lt_one hR).mul_right (∑' m,f 0 m)
  convert hg using 1
  funext r
  exact he r

end SevenEighths.ProbeEuler
end

end OAI

end Source1143

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsSummability.lean; sha256: e1f342674d292eebc3043f2cdc147a3a70915b1dfdee7d6ad9f269d0d05876e4 -/
section Source1144
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma geometric_indicator_summable (V A : ℂ) (hV : ‖V‖<1) (p : ℕ→Prop) :
    Summable (fun m=>(if p m then A else 0)*V^m) := by
  convert (((hasSum_geometric_of_norm_lt_one hV).summable.mul_left A).indicator {m | p m}) using 1
  funext m
  by_cases hm : p m <;> simp [hm]

lemma gaussValuationTable_geometric_summable (Q G V : ℂ) (hV : ‖V‖<1)
    (r n : ℕ) (j : ℕ→ℕ) :
    Summable (fun m=>gaussValuationTable Q G r n (j m)*V^m) := by
  by_cases hr : 6∣r
  · have ha := geometric_indicator_summable V (Q^(n+1)) hV (fun m=>n+1≤j m)
    have hb := geometric_indicator_summable V (Q^n) hV (fun m=>n≤j m)
    convert ha.sub hb using 1
    funext m
    simp only [gaussValuationTable,ite_eq_left hr,sub_mul]
    split_ifs <;> rfl
  · convert geometric_indicator_summable V (Q^n*G) hV (fun m=>j m=n) using 1
    funext m
    simp only [gaussValuationTable,ite_eq_right hr]
    split_ifs <;> rfl

theorem positiveScalar_geometric_summable (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k : ℕ) (j : ℕ→ℕ) (V : ℂ) (hV : ‖V‖<1) :
    Summable (fun m=>positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k (j m)*V^m) := by
  simp only [positiveScalar_actual_table p hp hg hc]
  by_cases hk : k=0
  · simp only [ite_eq_left hk]
    exact gaussValuationTable_geometric_summable _ _ V hV (n+1) n j
  · simp only [ite_eq_right hk]
    have hs := (gaussValuationTable_geometric_summable (Ideal.absNorm (Ideal.span {p}))
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^n) 1) V hV n n (fun m=>j m-1)).mul_left
      (((actualSextic (Ideal.span {p}) hg (-1))⁻¹)*primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
    convert hs.indicator {m | k=1 ∧ 1≤j m} using 1
    funext m
    by_cases hm : k=1 ∧ 1≤j m <;> simp [hm,mul_assoc]

end SevenEighths.ProbePrimePower
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
include hc

theorem rowMarkedTerm_frequency_summable (eta a X W V rho : ℂ) (hV : ‖V‖<1)
    (j e l k : ℕ) : Summable (fun m=>rowMarkedTerm p hp hg eta a X W V rho j e l k m) := by
  by_cases ht : e+3*l=0
  · simp only [rowMarkedTerm,ite_eq_left ht,summable_zero]
  · simp only [rowMarkedTerm,ite_eq_right ht,rowWeightedScalar,weightedScalar]
    have hs := SevenEighths.ProbePrimePower.positiveScalar_geometric_summable p hp hg hc (e+3*l-1) k (fun m=>j+6*m) V hV
    convert hs.mul_left ((rho^k/rho^(e+3*l)) *
      ((-eta*X/primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)^e *
        (a*X^3/(Ideal.absNorm (Ideal.span {p}):ℂ))^l *
        localCubePhase (star (localGamma p hp.ne_zero hg 3))
          (actualSextic (Ideal.span {p}) hg (-1)) e l k) *W^k) using 1
    funext m
    ring

theorem rowMarkedTerm_zero_lower_edge (eta a X W V rho : ℂ)
    (j e l k : ℕ) (hj : j<6) (ht : 0<e+3*l) :
    rowMarkedTerm p hp hg eta a X W V rho j e (l+2) k 0=0 := by
  unfold rowMarkedTerm
  rw [ite_eq_right (by omega),positiveScalar_zero_below p hp hg hc _ _ _ (by omega),
    rowWeightedScalar_zero]

theorem rowMarkedFamily_hasSum (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j e l k : ℕ) (hj : j<6) (ht : 0<e+3*l) :
    HasSum (fun r=>∑' m,rowMarkedTerm p hp hg eta a X W V rho j e (l+2*r) k m)
      ((∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l k m)/
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  apply diagonal_recurrence_hasSum
  · intro r m
    rw [show l+2*(r+1)=(l+2*r)+2 by omega]
    exact rowMarkedTerm_step p hp hg hc eta a X W V rho hρ j e (l+2*r) k m (by omega)
  · intro r
    rw [show l+2*(r+1)=(l+2*r)+2 by omega]
    exact rowMarkedTerm_zero_lower_edge p hp hg hc eta a X W V rho j e (l+2*r) k hj (by omega)
  · simpa only [mul_zero,add_zero] using rowMarkedTerm_frequency_summable p hp hg hc eta a X W V rho hV j e l k
  · exact hR

end SevenEighths.ProbeEuler
end

end OAI

end Source1144

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsFamilies.lean; sha256: 80cadd5d2e6b0ff109700c54b42cb5e476e26c7e6842c8e4a2879bd39e15428b -/
section Source1145
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def rowInner (eta a X W V rho : ℂ) (j e l : ℕ) : ℂ :=
  ∑' k, ∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l k m

def rowMarkedSeries (eta a X W V rho : ℂ) (j : ℕ) : ℂ :=
  ∑ e : Fin 2, ∑' l,rowInner p hp hg eta a X W V rho j e.val l

lemma rowInner_two (eta a X W V rho : ℂ) (j e l : ℕ) :
    rowInner p hp hg eta a X W V rho j e l=
      (∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l 0 m)+
      (∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l 1 m) := by
  apply tsum_two_of_rest_zero
  intro k
  simp only [rowMarkedTerm_higher_outer,tsum_zero]

@[simp] lemma rowInner_zero (eta a X W V rho : ℂ) (j : ℕ) :
    rowInner p hp hg eta a X W V rho j 0 0=0 := by
  simp only [rowInner,rowMarkedTerm,mul_zero,add_zero,ite_true,tsum_zero]

include hc in
theorem rowInner_family_hasSum (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j e l : ℕ) (hj : j<6) (ht : 0<e+3*l) :
    HasSum (fun r=>rowInner p hp hg eta a X W V rho j e (l+2*r))
      (rowInner p hp hg eta a X W V rho j e l/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  have h0 := rowMarkedFamily_hasSum p hp hg hc eta a X W V rho hρ hV hR j e l 0 hj ht
  have h1 := rowMarkedFamily_hasSum p hp hg hc eta a X W V rho hρ hV hR j e l 1 hj ht
  convert h0.add h1 using 1
  · funext r
    exact rowInner_two p hp hg eta a X W V rho j e (l+2*r)
  · rw [rowInner_two,add_div]

include hc in

theorem rowMarkedSeries_four_families (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j : ℕ) (hj : j<6) :
    rowMarkedSeries p hp hg eta a X W V rho j=
      (rowInner p hp hg eta a X W V rho j 0 2+
       rowInner p hp hg eta a X W V rho j 1 0+
       rowInner p hp hg eta a X W V rho j 0 1+
       rowInner p hp hg eta a X W V rho j 1 1)/
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) := by
  have h02 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 2 hj (by omega)
  have h10 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 1 0 hj (by omega)
  have h01 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 1 hj (by omega)
  have h11 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 1 1 hj (by omega)
  have he0 : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r))
      (rowInner p hp hg eta a X W V rho j 0 2/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    have hshift : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*(r+1)))
        (rowInner p hp hg eta a X W V rho j 0 2/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
      convert h02 using 1
      funext r
      congr 1
      omega
    have h := hshift.sum_range_add (f:=fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r)) (k:=1)
    simpa only [Finset.sum_range_one,mul_zero,rowInner_zero,zero_add] using h
  have he1 : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 1 (2*r))
      (rowInner p hp hg eta a X W V rho j 1 0/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [zero_add] using h10
  have ho0 : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r+1))
      (rowInner p hp hg eta a X W V rho j 0 1/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [Nat.add_comm 1] using h01
  have ho1 : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 1 (2*r+1))
      (rowInner p hp hg eta a X W V rho j 1 1/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [Nat.add_comm 1] using h11
  unfold rowMarkedSeries
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one]
  rw [(he0.even_add_odd ho0).tsum_eq,(he1.even_add_odd ho1).tsum_eq]
  ring

end SevenEighths.ProbeEuler
end

end OAI

end Source1145

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsTail.lean; sha256: 58af46e19a0c5a84d3da2e1cf1047302f0114e22480fa71fd959cc1025980ae6 -/
section Source1146
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma gaussValuationTable_above (Q G : ℂ) (r n j : ℕ) (hj : n+1≤j) :
    gaussValuationTable Q G r n j=if 6∣r then Q^(n+1)-Q^n else 0 := by
  unfold gaussValuationTable
  by_cases hd : 6∣r
  · rw [ite_eq_left hd,ite_eq_left hd,ite_eq_left hj,ite_eq_left (by omega)]
  · rw [ite_eq_right hd,ite_eq_right hd,ite_eq_right (by omega)]

theorem positiveScalar_stable_large (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (n k j j' : ℕ)
    (hj : n+1<j) (hj' : n+1<j') :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j=
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j' := by
  simp only [positiveScalar_actual_table p hp hg hc,
    show 1≤j by omega,show 1≤j' by omega,and_true,
    gaussValuationTable_above _ _ _ n j (by omega),
    gaussValuationTable_above _ _ _ n j' (by omega),
    gaussValuationTable_above _ _ _ n (j-1) (by omega),
    gaussValuationTable_above _ _ _ n (j'-1) (by omega)]

end SevenEighths.ProbePrimePower
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc

theorem rowMarkedTerm_base_tail (eta a X W V rho : ℂ)
    (j e l k m : ℕ) (ht : 0<e+3*l) (ht6 : e+3*l≤6) :
    rowMarkedTerm p hp hg eta a X W V rho j e l k (m+2)=
      rowMarkedTerm p hp hg eta a X W V rho j e l k 2*V^m := by
  unfold rowMarkedTerm
  rw [ite_eq_right (by omega),ite_eq_right (by omega),
    SevenEighths.ProbePrimePower.positiveScalar_stable_large p hp hg hc (e+3*l-1) k (j+6*(m+2)) (j+6*2) (by omega) (by omega)]
  unfold rowWeightedScalar weightedScalar
  rw [pow_add V m 2]
  ring

theorem rowInner_base_rational (eta a X W V rho : ℂ) (hV : ‖V‖<1)
    (j e l : ℕ) (ht : 0<e+3*l) (ht6 : e+3*l≤6) :
    rowInner p hp hg eta a X W V rho j e l=
      ∑ k : Fin 2,
        (rowMarkedTerm p hp hg eta a X W V rho j e l k.val 0+
         rowMarkedTerm p hp hg eta a X W V rho j e l k.val 1+
         rowMarkedTerm p hp hg eta a X W V rho j e l k.val 2/(1-V)) := by
  have hsum (k : ℕ) : (∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l k m)=
      rowMarkedTerm p hp hg eta a X W V rho j e l k 0+
      rowMarkedTerm p hp hg eta a X W V rho j e l k 1+
      rowMarkedTerm p hp hg eta a X W V rho j e l k 2/(1-V) := by
    have ht' : HasSum (fun m=>rowMarkedTerm p hp hg eta a X W V rho j e l k (m+2))
        (rowMarkedTerm p hp hg eta a X W V rho j e l k 2/(1-V)) := by
      have hgeo := (hasSum_geometric_of_norm_lt_one hV).mul_left (rowMarkedTerm p hp hg eta a X W V rho j e l k 2)
      rw [←div_eq_mul_inv] at hgeo
      convert hgeo using 1
      funext m
      exact rowMarkedTerm_base_tail p hp hg hc eta a X W V rho j e l k m ht ht6
    have h := ht'.sum_range_add (f:=fun m=>rowMarkedTerm p hp hg eta a X W V rho j e l k m) (k:=2)
    simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] using h.tsum_eq
  rw [rowInner_two,hsum 0,hsum 1]
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one]

end SevenEighths.ProbeEuler
end

end OAI

end Source1146

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsZero.lean; sha256: 834355e893a176809d69957b902848b38026a5cea5e58a2668f166b504b6c1fd -/
section Source1147
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p})

def rowZeroIndexTerm (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) (j k m : ℕ) : ℂ :=
  (if k=0 then 1 else (χ^k) (Ideal.Quotient.mk _ (p^(j+6*m))))*W^k*V^m

theorem sourceRowTerm_zero (eta a rho x w z : ℂ) (j k m : ℕ) :
    sourceRowTerm p hp hg eta a rho x w z j 0 0 k m=
      rowZeroIndexTerm p (actualSextic (Ideal.span {p}) hg)
        (rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) j k m := by
  unfold sourceRowTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [rowZeroIndexTerm,sourceScalar,weightedScalar,localCubePhase,
    coordV,Complex.ofReal_natCast,mul_zero,add_zero,pow_zero,one_mul,mul_one,
    zero_mul,Nat.choose_zero_succ,ite_true,div_one,mul_pow]
  ring

omit [(Ideal.span {p}).IsMaximal] in
lemma rowZeroIndex_zero (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j : ℕ) (hV : ‖V‖<1) :
    HasSum (fun m=>rowZeroIndexTerm p χ W V j 0 m) (1/(1-V)) := by
  simpa only [rowZeroIndexTerm,ite_true,pow_zero,one_mul,one_div] using
    hasSum_geometric_of_norm_lt_one hV

include hp in
theorem rowZeroIndex_pos_ramified (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j k m : ℕ) (hj : j≠0) (hk : k≠0) : rowZeroIndexTerm p χ W V j k m=0 := by
  rw [rowZeroIndexTerm,ite_eq_right hk,zero_index_scalar p hp χ k (j+6*m) hk,
    ite_eq_right (by omega),zero_mul,zero_mul]

include hp in
theorem rowZeroIndexSeries_eq (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j : ℕ) (hW : ‖W‖<1) (hV : ‖V‖<1) :
    (∑' k,∑' m,rowZeroIndexTerm p χ W V j k m)=
      1/(1-V)+(if j=0 then W/(1-W) else 0) := by
  by_cases hj : j=0
  · subst j
    simp only [rowZeroIndexTerm,zero_add,ite_true]
    exact zeroIndexSeries_eq p hp χ W V hW hV
  · rw [ite_eq_right hj,add_zero]
    rw [tsum_eq_single 0]
    · exact (rowZeroIndex_zero p χ W V j hV).tsum_eq
    · intro k hk
      simp only [rowZeroIndex_pos_ramified p hp χ W V j k _ hj hk,tsum_zero]

end SevenEighths.ProbeEuler
end

end OAI

end Source1147

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsClosed.lean; sha256: f46abcd5097dc05f09dfd87ea06aec8b94ce44bfe3cbb7ac0b6eec3ceb346dca -/
section Source1148
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def rowBaseFinite (eta a X W V rho : ℂ) (j e l : ℕ) : ℂ :=
  ∑ k : Fin 2,
    (rowMarkedTerm p hp hg eta a X W V rho j e l k.val 0+
     rowMarkedTerm p hp hg eta a X W V rho j e l k.val 1+
     rowMarkedTerm p hp hg eta a X W V rho j e l k.val 2/(1-V))

def rowClosedMarked (eta a X W V rho : ℂ) (j : ℕ) : ℂ :=
  (rowBaseFinite p hp hg eta a X W V rho j 0 2+
   rowBaseFinite p hp hg eta a X W V rho j 1 0+
   rowBaseFinite p hp hg eta a X W V rho j 0 1+
   rowBaseFinite p hp hg eta a X W V rho j 1 1)/
    (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)

include hc in
theorem rowMarkedSeries_eq_closed (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j : ℕ) (hj : j<6) :
    rowMarkedSeries p hp hg eta a X W V rho j=rowClosedMarked p hp hg eta a X W V rho j := by
  rw [rowMarkedSeries_four_families p hp hg hc eta a X W V rho hρ hV hR j hj]
  unfold rowClosedMarked rowBaseFinite
  rw [rowInner_base_rational p hp hg hc eta a X W V rho hV j 0 2 (by omega) (by omega),
    rowInner_base_rational p hp hg hc eta a X W V rho hV j 1 0 (by omega) (by omega),
    rowInner_base_rational p hp hg hc eta a X W V rho hV j 0 1 (by omega) (by omega),
    rowInner_base_rational p hp hg hc eta a X W V rho hV j 1 1 (by omega) (by omega)]

include hc in
lemma rowInner_zero_squarefree_summable (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j : ℕ) (hj : j<6) : Summable (fun l=>rowInner p hp hg eta a X W V rho j 0 l) := by
  have h02 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 2 hj (by omega)
  have h01 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 1 hj (by omega)
  have hs : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*(r+1)))
      (rowInner p hp hg eta a X W V rho j 0 2/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    convert h02 using 1
    funext r
    congr 1
    omega
  have he := hs.sum_range_add (f:=fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r)) (k:=1)
  have ho : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r+1))
      (rowInner p hp hg eta a X W V rho j 0 1/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [Nat.add_comm 1] using h01
  exact (he.even_add_odd ho).summable

def sourceRowSeries (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  ∑ e : Fin 2,∑' l,∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j e.val l k m

include hc in

theorem sourceRowSeries_eq_closed (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1) (j : ℕ) (hj : j<6) :
    sourceRowSeries p hp hg eta a rho x w z j=
      1/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)+
      (if j=0 then (rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))/
        (1-rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))) else 0)+
      rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j := by
  let X : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)
  let W : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)
  let V : ℂ := coordV (Ideal.absNorm (Ideal.span {p})) z
  let Z0 := 1/(1-V)+(if j=0 then rho*W/(1-rho*W) else 0)
  have he0 (l : ℕ) : (∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j 0 l k m)=
      rowInner p hp hg eta a X W V rho j 0 l+(if l=0 then Z0 else 0) := by
    by_cases hl : l=0
    · subst l
      simp only [sourceRowTerm_zero,rowInner_zero,ite_true,zero_add]
      exact rowZeroIndexSeries_eq p hp (actualSextic (Ideal.span {p}) hg) (rho*W) V j hW hV
    · rw [ite_eq_right hl,add_zero]
      apply tsum_congr
      intro k
      apply tsum_congr
      intro m
      exact sourceRowTerm_pos p hp hg eta a rho x w z j 0 l k m (by omega)
  have he1 (l : ℕ) : (∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j 1 l k m)=
      rowInner p hp hg eta a X W V rho j 1 l := by
    apply tsum_congr
    intro k
    apply tsum_congr
    intro m
    exact sourceRowTerm_pos p hp hg eta a rho x w z j 1 l k m (by omega)
  have hs := rowInner_zero_squarefree_summable p hp hg hc eta a X W V rho hρ hV hR j hj
  have hc' := rowMarkedSeries_eq_closed p hp hg hc eta a X W V rho hρ hV hR j hj
  unfold rowMarkedSeries at hc'
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one] at hc'
  unfold sourceRowSeries
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one,he0,he1]
  rw [hs.tsum_add (hasSum_ite_eq 0 Z0).summable,tsum_ite_eq]
  change _=Z0+rowClosedMarked p hp hg eta a X W V rho j
  rw [←hc']
  ring

end SevenEighths.ProbeEuler
end

end OAI

end Source1148

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsActual.lean; sha256: 2c0cd6b295f08a019a91fb7d20239ee71d2385083fb10fb2bd219eba7bc9a9cc -/
section Source1149
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem actualSextic_unit_six (p b : O) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hb : IsCoprime b p) :
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^6=1 := by
  have h := congrArg (fun χ : MulChar (O ⧸ Ideal.span {p}) ℂ =>
    χ (Ideal.Quotient.mk _ b)) (actualSextic_six _ hg hc)
  simpa only [MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),
    MulChar.one_apply ((isUnit_quotient_span_iff p b).mpr hb.symm)] using h

theorem idealRowHighLocalFactor_eq_closed (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (j : ℕ) (hj : j<6) (x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1) :
    idealRowHighLocalFactor η (b*p^j) (Ideal.span {p}) x w z=
      1/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)+
      (if j=0 then
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))/
        (1-actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))) else 0)+
      rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) j := by
  rw [idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs b hb j x w z]
  exact sourceRowSeries_eq_closed p hp hg hc _ _ _ x w z
    (actualSextic_unit_six p b hg hc hb) hV hR hW j hj

end SevenEighths.ProbePhysical
end

end OAI

end Source1149

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsUnramified.lean; sha256: 16fcaa8d157aa5cb64478d76f335f8123b49aa27dbdfe01f17f796141ccb4a2d -/
section Source1150
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma rowMarkedTerm_unramified (eta a X W V rho : ℂ) (e l k m : ℕ) :
    rowMarkedTerm p hp hg eta a X W V rho 0 e l k m=
      principalMarkedTerm p hp hg (eta/rho) (a/rho^3) X (rho*W) V e l k m := by
  unfold rowMarkedTerm principalMarkedTerm
  split_ifs
  · rfl
  · simp only [zero_add,rowWeightedScalar_parameters]

lemma rowMarkedSeries_unramified (eta a X W V rho : ℂ) :
    rowMarkedSeries p hp hg eta a X W V rho 0=
      principalMarkedSeries p hp hg (eta/rho) (a/rho^3) X (rho*W) V := by
  unfold rowMarkedSeries principalMarkedSeries rowInner principalInner
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact rowMarkedTerm_unramified p hp hg eta a X W V rho e.val l k m

include hc in
lemma rowClosedMarked_unramified (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    rowClosedMarked p hp hg eta a X W V rho 0=
      markedFactor (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) V
        (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹
        (eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W)
        (-(eta/rho)*X+(rho*W)*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) 1 := by
  have hn : rho≠0 := by intro h; simp [h] at hρ
  rw [←rowMarkedSeries_eq_closed p hp hg hc eta a X W V rho hρ hV hR 0 (by decide),
    rowMarkedSeries_unramified p hp hg,
    principalMarkedSeries_eq p hp hg hc _ _ _ _ _ hV
      (by simpa only [evenRatio_unit _ _ _ _ _ hρ] using hR),
    evenRatio_unit _ _ _ _ _ hρ]
  congr 1
  field_simp

include hc in

theorem sourceRowSeries_unramified_euler (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) rho w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta rho x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    sourceRowSeries p hp hg eta a rho x w z 0=
      (1-coordD Q eta rho x)/((1-coordV Q z)*(1-coordW Q rho w))*
        unramifiedClosed Q (a^2) eta rho x w z := by
  dsimp only
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hr := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a x z
  simp only [Complex.ofReal_natCast] at hr
  have hr' : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hr]; exact hR
  rw [sourceRowSeries_eq_closed p hp hg hc eta a rho x w z hρ hV hr' hW 0 (by decide)]
  rw [rowClosedMarked_unramified p hp hg hc _ _ _ _ _ _ hρ hV hr',hr]
  have hk := coordK_eq_geometric (Ideal.absNorm (Ideal.span {p}):ℝ) hQ eta x w
  simp only [Complex.ofReal_natCast] at hk
  rw [←hk]
  have hinv : rho⁻¹=star rho := Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hρ (by decide))
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hw := one_sub_ne_zero_of_norm_lt_one _ hW
  simp only [ite_true,div_eq_mul_inv,hinv]
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  simp only [coordW,coordD,Complex.ofReal_natCast] at hD hw ⊢
  field_simp [hD,hv,hw]
  ; ring

end SevenEighths.ProbeEuler
end

end OAI

end Source1150

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsRegion.lean; sha256: eb55f04a7c709ceaab8ad689480be86b8eee67450d53bc37734cf1be12820b8d -/
section Source1151
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma row_initial_geometric (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (b : O) (hb : IsCoprime b p)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)
    ‖coordV Q z‖<1 ∧ ‖coordR Q ((actualACube η p)^2) x z‖<1 ∧
      ‖coordW Q rho w‖<1 ∧ ‖coordD Q (targetMonoid η p) rho x‖<1 := by
  dsimp only
  have hP : Prime (Ideal.span {p}:Ideal O) := (Ideal.prime_span_singleton_iff).mpr hp
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hn : ‖actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)‖≤1 :=
    (Complex.norm_eq_one_of_pow_eq_one (actualSextic_unit_six p b hg hc hb) (by decide)).le
  refine ⟨?_,?_,?_,?_⟩
  · rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · apply (coordW_norm_le _ hQ0 _ w hn).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · apply (coordD_norm_le _ hQ0 _ _ x (targetMonoid_norm_le_one η p) hn).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)

theorem idealRowHighLocalFactor_unramified (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)
    idealRowHighLocalFactor η b (Ideal.span {p}) x w z=
      (1-coordD Q (targetMonoid η p) rho x)/((1-coordV Q z)*(1-coordW Q rho w))*
        unramifiedClosed Q (actualAPhase η p) (targetMonoid η p) rho x w z := by
  have hd := row_initial_geometric η p hp hg hc b hb x w z hx hw hz
  dsimp only at hd ⊢
  have he := idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs b hb 0 x w z
  simp only [pow_zero,mul_one] at he
  rw [he]
  simpa only [actualACube_sq,OAI.SevenEighths.ProbeEuler.sourceRowSeries] using
    sourceRowSeries_unramified_euler p hp hg hc (targetMonoid η p) (actualACube η p)
      _ x w z (actualSextic_unit_six p b hg hc hb) hd.1 hd.2.1 hd.2.2.1
      (one_sub_ne_zero_of_norm_lt_one _ hd.2.2.2)

end SevenEighths.ProbePhysical
end

end OAI

end Source1151

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/Unramified.lean; sha256: 7bcd7958c7f9f33e72a86fb0c48ea390d930a4272f0f7c612dde487e65f620a9 -/
section Source1152
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem localCorrection_coordinates (η : Character) (u : FreeRow) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (x w z : ℂ) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u.val)
    localCorrection η u ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ x w z=
      idealRowHighLocalFactor η u.val (Ideal.span {p}) x w z *
        (1-coordV Q z)*(1-coordW Q rho w)/(1-coordD Q (targetMonoid η p) rho x) := by
  dsimp only
  have hP0 : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  unfold localCorrection coordV coordW coordD
  simp only [CubicEisenstein.fullIdealWeight,hP0,ite_false,Complex.ofReal_natCast]
  rw [idealCoeff_span η hp.ne_zero,idealRowHom_prime u.val (Ideal.span {p}) hg]
  rw [show -(6*z)=(-6 : ℂ)*z by ring]
  rfl

theorem localCorrection_unramified (η : Character) (u : FreeRow) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : CanonicalQuadraticSieve.Supported (Ideal.span {p})) (hu : IsCoprime u.val p)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ x w z=
      actualUnramifiedClosed η p u.val hg x w z := by
  rw [localCorrection_coordinates η u p hp hg]
  rw [idealRowHighLocalFactor_unramified η p hp hg hc hprimary hs u.val hu x w z hx hw hz]
  have hgeom := row_initial_geometric η p hp hg hc u.val hu x w z hx hw hz
  dsimp only at hgeom
  have hV := one_sub_ne_zero_of_norm_lt_one _ hgeom.1
  have hW := one_sub_ne_zero_of_norm_lt_one _ hgeom.2.2.1
  have hD := one_sub_ne_zero_of_norm_lt_one _ hgeom.2.2.2
  unfold actualUnramifiedClosed
  change _=unramifiedClosed _ _ (targetMonoid η p) _ x w z
  field_simp

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1152

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/Ideal.lean; sha256: a9a8f8dc102822a4293979612b584be9325eb4a01c16147e2b3bdef627490b66 -/
section Source1153
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def idealUnramifiedCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  unramifiedClosed P.val.absNorm (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) (idealRowHom u.val P.val) x w z

theorem localCorrection_unramified_ideal (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hcop : IsCoprime P.val (Ideal.span {u.val}))
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u P x w z=idealUnramifiedCorrection η u P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  have hu : IsCoprime u.val p := ((Ideal.isCoprime_span_singleton_iff p u.val).mp
    (by rw [hspan]; exact hcop)).symm
  have he := localCorrection_unramified η u p hp hg.1 hg.2 hprimary hsp hu x w z hx hw hz
  have hP : (⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ : PrimeIdeal)=P := Subtype.ext hspan
  rw [hP] at he
  unfold actualUnramifiedClosed at he
  rw [←idealCoeff_span η hp.ne_zero,←idealRowHom_prime u.val (Ideal.span {p}) hg.1,hspan] at he
  exact he

theorem localCorrection_outside_unramified (S : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (P : PrimeIdeal) (hP : P.val∉S) (hcop : IsCoprime P.val (Ideal.span {u.val}))
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u P x w z=idealUnramifiedCorrection η u P x w z :=
  localCorrection_unramified_ideal η u P (outside_prime_supported S hbad P hP) hcop x w z hx hw hz

theorem localCorrection_ramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    localCorrection η u P x w z=
      idealRowHighLocalFactor η u.val P.val x w z*(1-CubicEisenstein.fullIdealWeight (6*z) P.val) := by
  have hu : u.val∈P.val := (Ideal.dvd_iff_le.mp hP) (Ideal.subset_span (by simp))
  have hr : idealRowHom u.val P.val=0 := idealRowHom_zero_of_dvd u.val P.property (dvd_refl _) hu
  simp only [localCorrection,hr,map_zero,mul_zero,zero_mul,sub_zero,mul_one,div_one]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1153

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsScalarBounds.lean; sha256: 2ab5a4a256af16fe1741e6ad756c823fb94af8e047866506f2a8a1c03f3a1df2 -/
section Source1154
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma primeGauss_norm_le (p : O) (hp : p≠0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (h : O) :
    ‖primeGauss p hp χ h‖≤(Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let := finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primeGauss,tsum_fintype]
  calc
    _ ≤ ∑ x : O ⧸ Ideal.span {p},‖χ x*quotientTrace p hp (Ideal.Quotient.mk _ h*x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : O ⧸ Ideal.span {p},(1:ℝ) := Finset.sum_le_sum fun x _=>by
      rw [norm_mul,(quotientTrace p hp).norm_apply,mul_one]
      exact QuadraticInitialBound.norm_finite_character_le_one χ x
    _ = _ := by simp [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

lemma primeGauss_actual_norm (p : O) (hp : p≠0) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2) :
    ‖primeGauss p hp (actualSextic (Ideal.span {p}) hg) 1‖=
      Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn := localGamma_norm_one p hp hg hc 1 (by decide) (by decide)
  rw [localGamma,ProbePhase.normalizedTraceGauss_eq_normalizedGauss] at hn
  simp only [pow_one,ProbeGauss.normalizedGauss,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp))
  have hcard : (Fintype.card (O ⧸ Ideal.span {p}):ℝ)=Ideal.absNorm (Ideal.span {p}) := by
    rw [←Nat.card_eq_fintype_card];rfl
  rw [hcard] at hn
  have hn' := (div_eq_one_iff_eq (Real.sqrt_pos.mpr hQ).ne').mp hn
  simpa only [primeGauss,tsum_fintype,gaussSum,map_one,one_mul] using hn'

lemma gaussValuationTable_norm_le (Q : ℝ) (hQ : 1≤Q) (G : ℂ) (hG : ‖G‖≤Q)
    (r n j : ℕ) : ‖gaussValuationTable (Q:ℂ) G r n j‖≤2*Q^(n+1) := by
  have hQ0 : 0≤Q := by linarith
  have hn : Q^n≤Q^(n+1) := by simpa only [pow_succ] using
    (le_mul_of_one_le_right (pow_nonneg hQ0 n) hQ)
  have hpow (a : ℕ) : ‖(Q:ℂ)^a‖=Q^a := by simp [norm_pow,abs_of_nonneg hQ0]
  have hi (a : ℕ) : ‖(if a≤j then (Q:ℂ)^a else 0)‖≤Q^a := by
    split_ifs
    · exact (hpow a).le
    · simpa only [norm_zero] using pow_nonneg hQ0 a
  unfold gaussValuationTable
  by_cases hr : 6∣r
  · rw [ite_eq_left hr]
    exact (norm_sub_le _ _).trans ((add_le_add (hi (n+1)) (hi n)).trans (by linarith))
  · rw [ite_eq_right hr]
    by_cases hj : j=n
    · rw [ite_eq_left hj,norm_mul,hpow]
      calc
        _ ≤ Q^n*Q := mul_le_mul_of_nonneg_left hG (pow_nonneg hQ0 n)
        _ ≤ 2*Q^(n+1) := by rw [←pow_succ];nlinarith [pow_nonneg hQ0 (n+1)]
    · rw [ite_eq_right hj,norm_zero]
      positivity

lemma positiveScalar_norm_le (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (n k j : ℕ) (hk : k≤1) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)*
        (Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ))^k := by
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ : (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
    change 2≤Ideal.absNorm (Ideal.span {p}) at hh
    exact_mod_cast (by omega : 1≤Ideal.absNorm (Ideal.span {p}))
  have ht (r j : ℕ) := gaussValuationTable_norm_le (Ideal.absNorm (Ideal.span {p}):ℝ) hQ
    (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^r) 1)
    (primeGauss_norm_le p hp.ne_zero _ _) r n j
  have ho : ‖actualSextic (Ideal.span {p}) hg (-1)‖=1 :=
    Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide)
  rw [positiveScalar_actual_table p hp hg hc]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
  · simpa only [ite_true,pow_zero,mul_one,Complex.ofReal_natCast] using ht (n+1) j
  · simp only [Nat.one_ne_zero,ite_false,true_and]
    split_ifs
    · rw [norm_mul,norm_mul,norm_inv,ho,inv_one,one_mul,primeGauss_actual_norm p hp.ne_zero hg hc]
      simpa only [pow_one,mul_comm,Complex.ofReal_natCast] using
        mul_le_mul_of_nonneg_left (ht n (j-1)) (Real.sqrt_nonneg (Ideal.absNorm (Ideal.span {p}):ℝ))
    · simp only [norm_zero,pow_one]
      positivity

end SevenEighths.ProbePrimePower
end

end OAI

end Source1154

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsTermBounds.lean; sha256: c06cf490e4ea8a021af76d4298846351b856fc3d2b48e3b85074a1d281978684 -/
section Source1155
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma sourceWeightedScalar_norm_le (Q : ℝ) (hQ : 0<Q)
    (eta a gamma C omega x w z scalar : ℂ) (heta : ‖eta‖≤1) (ha : ‖a‖≤1)
    (hgamma : ‖gamma‖=1) (hC : ‖C‖=1) (ho : ‖omega‖=1) (e l k m : ℕ) :
    ‖sourceWeightedScalar Q eta a gamma C omega x w z scalar e l k m‖≤
      ‖scalar‖*Q^(-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) := by
  let coeff : ℂ := (-1:ℂ)^e*gamma^(-(e:ℤ))*eta^e*(a*C)^l*
    omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ))
  have hn : ‖coeff‖≤1 := by
    simp only [coeff,norm_mul,norm_pow,norm_zpow,hgamma,hC,ho,norm_neg,norm_one,
      one_pow,one_zpow,mul_one,one_mul]
    exact (mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) heta)).trans (pow_le_one₀ (norm_nonneg _) ha)
  change ‖coeff*scalar*(Q:ℂ)^_‖≤_
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  have he : (-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)).re=
      -(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ) := by simp
  rw [he]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hn) (by positivity)

lemma scalar_spectral_power (Q x w z : ℝ) (hQ : 0<Q) (e l k m : ℕ) :
    (2*Q^(e+3*l)*(Real.sqrt Q)^k)*
      Q^(-(x+1/2)*(e:ℝ)-(1+3*x)*(l:ℝ)-w*(k:ℝ)-6*z*(m:ℝ))=
      2*Q^((1/2-x)*(e:ℝ)+(2-3*x)*(l:ℝ)+(1/2-w)*(k:ℝ)-6*z*(m:ℝ)) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul_natCast hQ.le,←Real.rpow_natCast Q (e+3*l)]
  rw [mul_assoc 2,←Real.rpow_add hQ,mul_assoc 2,←Real.rpow_add hQ]
  congr 1
  push_cast
  ring_nf

theorem sourceRowTerm_norm_le (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (eta a rho x w z : ℂ) (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (ht : 0<e+3*l) (hk : k≤1) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^((1/2-x.re)*(e:ℝ)+(2-3*x.re)*(l:ℝ)+
        (1/2-w.re)*(k:ℝ)-6*z.re*(m:ℝ)) := by
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hrho := Complex.norm_eq_one_of_pow_eq_one hρ (by decide : (6:ℕ)≠0)
  rw [sourceRowTerm,norm_mul,norm_div,norm_pow,norm_pow,hrho,one_pow,one_pow,div_self (by norm_num : (1:ℝ)≠0),one_mul]
  apply (sourceWeightedScalar_norm_le _ hQ eta a _ _ _ x w z _ heta ha
    (localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide))
    (by rw [norm_star];exact localGamma_norm_one p hp.ne_zero hg hc 3 (by decide) (by decide))
    (Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide)) e l k m).trans
  have hs := positiveScalar_norm_le p hp hg hc (e+3*l-1) k (j+6*m) hk
  rw [show e+3*l-1+1=e+3*l by omega] at hs
  rw [sourceScalar,ite_eq_right (by omega)]
  exact (mul_le_mul_of_nonneg_right hs (by positivity)).trans_eq
    (scalar_spectral_power _ x.re w.re z.re hQ e l k m)

end SevenEighths.ProbeEuler
end

end OAI

end Source1155

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsFiniteBounds.lean; sha256: 53d5ba3bedc3dd1ddcda7d13c5c27dc4b887c4df36b9e5d60b9f6ec8efcc7644 -/
section Source1156
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma rowMarkedTerm_second_region (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (19/20:ℝ)≤w.re) (hz : (33/200:ℝ)≤z.re)
    (j e l k m : ℕ) (ht : 0<e+3*l) (hk : k≤1) :
    ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l k m‖≤2 := by
  rw [←sourceRowTerm_pos p hp hg eta a rho x w z j e l k m (by omega)]
  apply (sourceRowTerm_norm_le p hp hg hc eta a rho x w z heta ha hρ j e l k m ht hk).trans
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ1 : (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
    change 2≤Ideal.absNorm (Ideal.span {p}) at hh
    exact_mod_cast (by omega : 1≤Ideal.absNorm (Ideal.span {p}))
  have he : (1/2-x.re)*(e:ℝ)+(2-3*x.re)*(l:ℝ)+(1/2-w.re)*(k:ℝ)-6*z.re*(m:ℝ)≤0 := by
    have h1 := mul_nonpos_of_nonpos_of_nonneg (show 1/2-x.re≤0 by linarith) (Nat.cast_nonneg e : (0:ℝ)≤_)
    have h2 := mul_nonpos_of_nonpos_of_nonneg (show 2-3*x.re≤0 by linarith) (Nat.cast_nonneg l : (0:ℝ)≤_)
    have h3 := mul_nonpos_of_nonpos_of_nonneg (show 1/2-w.re≤0 by linarith) (Nat.cast_nonneg k : (0:ℝ)≤_)
    have h4 : 0≤6*z.re*(m:ℝ) := by positivity
    linarith
  have hh := Real.rpow_le_one_of_one_le_of_nonpos hQ1 he
  linarith

lemma second_region_V_half (Q : ℝ) (hQ : 4≤Q) (z : ℂ) (hz : (33/200:ℝ)≤z.re) :
    ‖coordV Q z‖≤1/2 := by
  rw [coordV_norm Q (by linarith)]
  exact rpow_le_half Q _ hQ (by linarith)

lemma second_region_R_half (Q : ℝ) (hQ : 4≤Q) (a x z : ℂ) (ha : ‖a‖≤1)
    (hx : (7/8:ℝ)≤x.re) (hz : (33/200:ℝ)≤z.re) :
    ‖evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z)‖≤1/2 := by
  rw [evenRatio_eq_coordR Q (by linarith)]
  apply (coordR_norm_le Q (by linarith) (a^2) x z (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha)).trans
  exact rpow_le_half Q _ hQ (by linarith)

include hc in
lemma rowBaseFinite_second_region (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (19/20:ℝ)≤w.re) (hz : (33/200:ℝ)≤z.re)
    (j e l : ℕ) (ht : 0<e+3*l) :
    ‖rowBaseFinite p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l‖≤16 := by
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (second_region_V_half _ hQ z hz)
  have ht' (k : Fin 2) (m : ℕ) := rowMarkedTerm_second_region p hp hg hc eta a rho x w z heta ha hρ hx hw hz
    j e l k.val m ht (by omega)
  unfold rowBaseFinite
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : Fin 2,(8:ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_add_le _ _).trans
      have hab := (norm_add_le _ _).trans (add_le_add (ht' k 0) (ht' k 1))
      have hd : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
          rho j e l k.val 2/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)‖≤4 := by
        rw [div_eq_mul_inv,norm_mul]
        exact (mul_le_mul (ht' k 2) hv (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
      linarith
    _ = _ := by norm_num

include hc in
theorem rowClosedMarked_second_region (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (19/20:ℝ)≤w.re) (hz : (33/200:ℝ)≤z.re) (j : ℕ) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤128 := by
  have h02 := rowBaseFinite_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 2 (by omega)
  have h10 := rowBaseFinite_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 0 (by omega)
  have h01 := rowBaseFinite_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 1 (by omega)
  have h11 := rowBaseFinite_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 1 (by omega)
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (second_region_R_half _ hQ a x z ha hx hz)
  simp only [Complex.ofReal_natCast] at hr
  unfold rowClosedMarked
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI

end Source1156

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsRamified.lean; sha256: 79be9321e84e1b91ac7373396d174039977a83cb9442f4c0876b6b548da16592 -/
section Source1157
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedClosed (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  1+(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j

include hc in
theorem ramifiedClosed_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (19/20:ℝ)≤w.re) (hz : (33/200:ℝ)≤z.re) (j : ℕ) :
    ‖ramifiedClosed p hp hg eta a rho x w z j‖≤193 := by
  have hb := rowClosedMarked_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j
  have hv := second_region_V_half _ hQ z hz
  have hs := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
  simp only [norm_one] at hs
  unfold ramifiedClosed
  apply (norm_add_le _ _).trans
  rw [norm_one,norm_mul]
  have hm := mul_le_mul (show ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 by linarith)
    hb (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)
  linarith

include hc in

theorem sourceRowSeries_ramified (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1)
    (j : ℕ) (hj0 : j≠0) (hj : j<6) :
    sourceRowSeries p hp hg eta a rho x w z j*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)=
      ramifiedClosed p hp hg eta a rho x w z j := by
  rw [sourceRowSeries_eq_closed p hp hg hc eta a rho x w z hρ hV hR hW j hj,ite_eq_right hj0,add_zero]
  unfold ramifiedClosed
  have hn := one_sub_ne_zero_of_norm_lt_one _ hV
  field_simp

end SevenEighths.ProbeEuler
end

end OAI

end Source1157

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/Ramified.lean; sha256: 14578f8c697837766554b8785707efb24a5df290a387b83f3cfcc88f15a3da6f -/
section Source1158
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def ramifiedCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  letI : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  ramifiedClosed p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    x w z (multiplicity p u.val)

theorem ramifiedCorrection_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (19/20 : ℝ)≤w.re) (hz : (33/200 : ℝ)≤z.re) :
    ‖ramifiedCorrection η u P hs x w z‖≤193 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  exact ramifiedClosed_bound p hp hg.1 hg.2 _ _ _ x w z
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) ha
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)) hx hw hz _

theorem localCorrection_eq_ramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hPu : P.val∣Ideal.span {u.val})
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u P x w z=ramifiedCorrection η u P hs x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  have hdiv : p∣u.val := Ideal.span_singleton_le_span_singleton.mp
    (by rw [hspan]; exact Ideal.dvd_iff_le.mp hPu)
  have hj0 : multiplicity p u.val≠0 := ne_of_gt (multiplicity_pos_of_dvd hdiv
    (FiniteMultiplicity.of_prime_left hp u.property.1))
  have hρ := actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)
  have hgeom := row_initial_geometric η p hp hg.1 hg.2 (unitPart u p hp)
    (unitPart_coprime u p hp) x w z hx hw hz
  dsimp only at hgeom
  have hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    have hpos : (0 : ℝ)<Ideal.absNorm (Ideal.span {p}) :=
      HeckeDyadic.norm_pos ⟨Ideal.span {p},Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero⟩
    have he := evenRatio_eq_coordR _ hpos (actualACube η p) x z
    simp only [Complex.ofReal_natCast] at he
    rw [he]
    exact hgeom.2.1
  rw [localCorrection_ramified η u P hPu,←hspan,
    idealRowHighLocalFactor_canonical η u p hp hg.1 hg.2 hprimary hsp]
  have he := sourceRowSeries_ramified p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p) _ x w z hρ hgeom.1 hR
    hgeom.2.2.1 (multiplicity p u.val) hj0 (multiplicity_lt_six u p hp)
  have hP0 : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  convert he using 1
  · simp only [OAI.SevenEighths.ProbeEuler.sourceRowSeries,CubicEisenstein.fullIdealWeight,
      hP0,ite_false,Complex.ofReal_natCast,coordV]
    rw [show -(6*z)=(-6 : ℂ)*z by ring]
  · rfl

def ramifiedPrimes (S : Finset (Ideal O)) (u : FreeRow) : Finset PrimeIdeal :=
  (SmoothMobiusCorrection.primeSet (Ideal.span {u.val})).filter (fun P => P.val∉S)

theorem ramified_product_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (η : Character) (u : FreeRow) (x w z : ℂ),
      (7/8 : ℝ)≤x.re → (19/20 : ℝ)≤w.re → (33/200 : ℝ)≤z.re →
      ‖∏ P∈(ramifiedPrimes S u).attach,
        ramifiedCorrection η u P.val
          (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound 193 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro S hS η u x w z hx hw hz
  rw [norm_prod]
  calc
    _ ≤ ∏ P∈(ramifiedPrimes S u).attach,(193 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P hP
      exact ramifiedCorrection_bound η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x w z hx hw hz
    _ = (193 : ℝ)^(ramifiedPrimes S u).card := by simp
    _ ≤ (193 : ℝ)^(IdealMobiusDivisorSum.primeSupport (Ideal.span {u.val})).card := by
      apply pow_le_pow_right₀ (by norm_num)
      rw [←HeckeDeletionBounds.primeSet_card]
      exact Finset.card_filter_le _ _
    _ ≤ _ := hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1158

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/Product.lean; sha256: 87d374b4ce7333ce7a602dfc626ee7667231fef148978221a6683ed301efafa4 -/
section Source1159
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

def unramifiedFactor (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  if P.val∣Ideal.span {u.val} then 1 else idealUnramifiedCorrection η u P x w z

def unramifiedProduct (S : Finset (Ideal O)) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val∉S},unramifiedFactor η u P.val x w z

theorem unramifiedFactor_defect (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hP : 4≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    ‖unramifiedFactor η u P x w z-1‖≤globalPrimeDefectBound P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using globalPrimeDefectBound_nonneg P
  · apply unramifiedClosed_open_region_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact hx
    · exact hw
    · exact hz

theorem unramifiedProduct_defect (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    ‖unramifiedProduct S η u x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P => unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

theorem unramifiedProduct_multipliable (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S} =>unramifiedFactor η u P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S} => unramifiedFactor η u P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S} => globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤B P :=
    unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem unramifiedProduct_analytic_x (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (w z : ℂ) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>unramifiedProduct S η u x w z) {x : ℂ | 7/8<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply unramifiedClosed_analytic_x
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hz
  · intro P x hx
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem unramifiedProduct_analytic_w (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x z : ℂ) (hx : (7/8 : ℝ)≤x.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w =>unramifiedProduct S η u x w z) {w : ℂ | 9/10<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply unramifiedClosed_analytic_w
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hx
      · exact hz
  · intro P w hw
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem unramifiedProduct_analytic_z (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w : ℂ) (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) :
    AnalyticOnNhd ℂ (fun z =>unramifiedProduct S η u x w z) {z : ℂ | 4/25<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ => if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [ite_eq_right h]
      apply unramifiedClosed_analytic_z
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hx
  · intro P z hz
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1159
