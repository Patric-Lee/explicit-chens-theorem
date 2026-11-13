import OpenAIGrouped.Unit003
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/GaussSum/BranchScaling.lean; sha256: 9d0e679cd9254946d3f6d70785a903348f00b70f1823443737815995fd632a81 -/
section Source160
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

def completedResidualScale (K : ℝ) (I Q : Ideal O) : ℝ :=
  K/((Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ))

def completedBranchScale {ι : Type*} [Fintype ι]
    (K X : ℝ) (I F Q : Ideal O) (P : ι→Ideal O) (e : ι→Fin 3) : ℝ :=
  (completedResidualScale K I Q)^2*(Ideal.absNorm (∏i,P i):ℝ)^2/
    (X*(Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 1):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2):ℝ)^3)

theorem completed_reflected_fiber
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K X : ℝ,1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i),
      Pairwise (fun i j => IsCoprime (P i) (P j)) →
      (∀i,P i∣I*Q) → (∀i,¬P i∣rowResidualPart I Q) →
    ∀e : ι→Fin 3,∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀J∈S i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀J∈T i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ,(∀i k,‖σ i k‖≤1) →
      (∑k : idealRange (completedResidualScale K I Q),‖∑'i : ℕ×ℕ×ℕ,
        reflectedBranchBlock P hg (fun i => completedLocalExponent I F (P i)) e W
          (completedResidualScale K I Q) (completedBranchScale K X I F Q P e) ρ q S T η σ i k‖^2)
        ≤C*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨C,hC,h⟩ := completed_reflected_branch_series W a b ha hsupp hW deltaLoss ρ q hδ hρ hq
  refine ⟨C,hC,?_⟩
  intro K X hK hX I F Q hI hQ hIK hscale ι _ P _ hg hcop hpool hres e S T hS hT η hη σ hσ
  have hn (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj (v : Fin 3) := hn _
    (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i))
      (fun i => completedLocalExponent I F (P i)) e v)
  have hp := hn (∏i,P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hy : 0<completedBranchScale K X I F Q P e := by
    unfold completedBranchScale
    have hk : 0<completedResidualScale K I Q := by linarith
    have hx : 0<X := by linarith
    have hd := hj 1
    have he := hj 2
    positivity
  have hb := (h (completedResidualScale K I Q) (completedBranchScale K X I F Q P e)
    hscale hy P hg (fun i => completedLocalExponent I F (P i)) e S T hS hT η hη σ hσ).2
  have hc := completed_actual_fiber_cost deltaLoss K X hδ.le hK hX I F Q hI hQ hIK P hcop hpool hres e
  have hm := mul_le_mul_of_nonneg_left hc hC.le
  apply hb.trans
  convert hm using 1 <;> (try dsimp [completedResidualScale,completedBranchScale]) <;> ring

end CompletedGauss

open scoped BigOperators Classical
namespace LocalReflectionBrackets
variable {F : Type*} [Field F] [Fintype F]

def unitArgumentFactor (χ : MulChar F ℂ) (j : ℕ) (z : F) : ℂ :=
  if j=4 then 1 else (χ^(j+2))⁻¹ z

theorem bracket_mul_unit (χ : MulChar F ℂ) (j : ℕ) (z x : F) (hz : z≠0) :
    bracket χ j (z*x)=unitArgumentFactor χ j z*bracket χ j x := by
  by_cases hj4 : j=4
  · simp [unitArgumentFactor,bracket,hj4,hz]
  · by_cases hj0 : j=0
    · subst j
      simp only [unitArgumentFactor,bracket,show (0:ℕ)≠4 by decide,ite_false,ite_true,
        zero_add,map_mul]
      ring
    · simp only [unitArgumentFactor,bracket,ite_eq_right hj4,ite_eq_right hj0,map_mul]

theorem unitArgumentFactor_norm (χ : MulChar F ℂ) (j : ℕ) (z : F) (hz : z≠0) :
    ‖unitArgumentFactor χ j z‖=1 := by
  by_cases hj : j=4
  · simp [unitArgumentFactor,hj]
  · rw [unitArgumentFactor,ite_eq_right hj]
    exact FiniteRayExpansion.norm_char_unit ((χ^(j+2))⁻¹) (Units.mk0 z hz)

end LocalReflectionBrackets
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets

theorem unit_ramified_quotient_ne_zero (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (u : Oˣ) (m : ℕ) :
    Ideal.Quotient.mk P ((u:O)*lambda^m)≠0 := by
  rw [map_mul,map_pow]
  apply mul_ne_zero
  · exact (u.isUnit.map (Ideal.Quotient.mk P)).ne_zero
  · exact pow_ne_zero _ (fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h))

def ramifiedBranchPhase {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (u : Oˣ) (m : ℕ) : ℂ :=
  ∏i,unitArgumentFactor (actualSextic (P i) (hg i)) (j i)
    (Ideal.Quotient.mk (P i) ((u:O)*lambda^m))

theorem ramifiedBranchPhase_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (u : Oˣ) (m : ℕ) : ‖ramifiedBranchPhase P hg j u m‖=1 := by
  rw [ramifiedBranchPhase,norm_prod]
  have hh (i : ι) := unitArgumentFactor_norm (actualSextic (P i) (hg i)) (j i)
    _ (unit_ramified_quotient_ne_zero (P i) (hg i) u m)
  simp only [hh,Finset.prod_const_one]

theorem ramified_bracket_full_expansion {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (u : Oˣ) (m : ℕ) (n b : O) :
    (∏i,bracket (actualSextic (P i) (hg i)) (j i)
      (Ideal.Quotient.mk (P i) ((u:O)*lambda^m*(n*b^3))))=
      ramifiedBranchPhase P hg j u m*∑e : ι→Fin 3,reflectedBranch P hg j e n b := by
  have hl (i : ι) : bracket (actualSextic (P i) (hg i)) (j i)
      (Ideal.Quotient.mk (P i) ((u:O)*lambda^m*(n*b^3)))=
      unitArgumentFactor (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) ((u:O)*lambda^m))*
      bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (n*b^3)) := by
    rw [map_mul]
    exact bracket_mul_unit _ _ _ _ (unit_ramified_quotient_ne_zero (P i) (hg i) u m)
  simp_rw [hl]
  rw [Finset.prod_mul_distrib,prod_bracket_eq_full_branches P hg j n b]
  rfl

end CompletedGauss

namespace InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open ConcretePrimeRowBridge (idealGenerator)

local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def sourceLabelUnit (f : O) : Oˣ :=
  Classical.choose (exists_label_unit f (Ideal.span {f}) rfl)

lemma sourceLabelUnit_spec (f : O) : f=(sourceLabelUnit f : O)*idealGenerator (Ideal.span {f}) :=
  Classical.choose_spec (exists_label_unit f (Ideal.span {f}) rfl)

def sourceIdealPoint (z : O × O) : Ideal O × O := (Ideal.span {z.2},z.1)

def sourceUnitPoint (z : O × O) : Oˣ × (Ideal O × O) :=
  (sourceLabelUnit z.2,sourceIdealPoint z)

lemma sourceUnitPoint_injective : Function.Injective sourceUnitPoint := by
  intro x y h
  have hu : sourceLabelUnit x.2=sourceLabelUnit y.2 := congrArg Prod.fst h
  have hi : Ideal.span {x.2}=Ideal.span {y.2} := congrArg (fun z => z.2.1) h
  have hr : x.1=y.1 := congrArg (fun z => z.2.2) h
  apply Prod.ext hr
  rw [sourceLabelUnit_spec x.2,sourceLabelUnit_spec y.2,hu,hi]

def sourceIdealTarget (T : Finset (O × O)) : Finset (Ideal O × O) :=
  T.image sourceIdealPoint

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem sourceChildEnergy_le_ideal (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (O × O)) (V : ℝ → ℂ) (X : ℝ) (tn rn : Bool) (a b : ℝ) :
    sourceChildEnergy p hp hcop hg F Ψ m T V X tn rn a b ≤
      childEnergy p hp hcop hg F Ψ m (sourceIdealTarget T) V X tn rn a b := by
  let E : Oˣ × (Ideal O × O) → ℝ := fun z =>
    ‖idealChildRow p hp hcop hg F Ψ m (fixedSecondTest p V X a b tn) rn z.1 z.2‖^2
  have hsub : T.image sourceUnitPoint ⊆ Finset.univ ×ˢ sourceIdealTarget T := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨x,hx,rfl⟩⟩
  calc
    _ = ∑ z ∈ T.image sourceUnitPoint,E z := by
      rw [Finset.sum_image (fun x _ y _ h => sourceUnitPoint_injective h)]
      apply Finset.sum_congr rfl
      intro z hz
      simp only [E,sourceUnitPoint,sourceIdealPoint,idealChildRow]
      rw [←sourceLabelUnit_spec]
    _ ≤ ∑ z ∈ Finset.univ ×ˢ sourceIdealTarget T,E z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro z hz hn
      exact sq_nonneg _
    _ = _ := by rw [Finset.sum_product]; rfl

theorem sourceGeometricMean_le_ideal (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (q : Frequency) :
    sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ q ≤
      childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m (sourceIdealTarget T) V₁ V₂ X₁ X₂ q := by
  apply mul_le_mul
    (Real.sqrt_le_sqrt (sourceChildEnergy_le_ideal p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2))
    (Real.sqrt_le_sqrt (sourceChildEnergy_le_ideal p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end

theorem sourceIdealTarget_bounds (T : Finset (O × O)) (K lengthScale : ℝ)
    (hT : ∀ z ∈ T, z.2 ≠ 0 ∧ elementNorm z.2 ≤ lengthScale ∧ elementNorm z.1 ≤ K) :
    ∀ z ∈ sourceIdealTarget T, z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hne,hn,hk⟩ := hT x hx
  refine ⟨Ideal.span_singleton_eq_bot.not.mpr hne,?_,hk⟩
  simpa only [sourceIdealPoint,elementNorm,eisEmbedding_norm_sq_eq_absNorm_span] using hn

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem positive_nested_density_bound (f : Frequency → ℝ) (C : ℝ)
    (hf : ∀ q, 0 ≤ f q)
    (hbound : ∀ q, f q ≤ C*firstLogDensity 0 q.1*firstLogDensity 0 q.2.1*firstLogDensity 0 q.2.2) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, f (x,y,z)) ≤
      C*(∫ t : ℝ,firstLogDensity 0 t)^3 := by
  let I := ∫ t : ℝ,firstLogDensity 0 t
  have hz (x y : ℝ) : (∫ z : ℝ,f (x,y,z)) ≤
      C*firstLogDensity 0 x*firstLogDensity 0 y*I := by
    have h := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z : ℝ => hf (x,y,z)))
      ((firstLogDensity_integrable 0).const_mul (C*firstLogDensity 0 x*firstLogDensity 0 y))
      (Filter.Eventually.of_forall (fun z : ℝ => hbound (x,y,z)))
    simpa only [integral_const_mul,I] using h
  have hy (x : ℝ) : (∫ y : ℝ, ∫ z : ℝ,f (x,y,z)) ≤ C*firstLogDensity 0 x*I*I := by
    have h := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z))))
      (((firstLogDensity_integrable 0).const_mul (C*firstLogDensity 0 x)).mul_const I)
      (Filter.Eventually.of_forall (hz x))
    simpa only [integral_mul_const,integral_const_mul,I] using h
  have h := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x : ℝ => integral_nonneg
      (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z)))))
    ((((firstLogDensity_integrable 0).const_mul C).mul_const I).mul_const I)
    (Filter.Eventually.of_forall hy)
  simp only [integral_mul_const,integral_const_mul] at h
  convert h using 1 ; dsimp [I] ; ring

theorem polynomial_density_cost (B G : Frequency → ℝ) (J : ℕ) (S C E : ℝ)
    (hS : 0 < S) (hC : 0 ≤ C) (_hE : 0 ≤ E)
    (hB : ∀ q, 0 ≤ B q) (hG : ∀ q, 0 ≤ G q)
    (hdec : ∀ q, S*B q ≤ C*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (henergy : ∀ q, G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,B (x,y,z)*G (x,y,z)) ≤
      (C*E/S)*(∫ t : ℝ,firstLogDensity 0 t)^3 := by
  apply positive_nested_density_bound _ (C*E/S)
    (fun q => mul_nonneg (hB q) (hG q))
  intro q
  have hc : 0 ≤ C*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (firstLogDensity_nonneg _ _))
      (firstLogDensity_nonneg _ _)) (firstLogDensity_nonneg _ _)
  have hb := mul_le_mul (hdec q) (henergy q) (hG q) hc
  have heq :
      (C*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)*
        (E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) =
      C*E*firstLogDensity 0 q.1*firstLogDensity 0 q.2.1*firstLogDensity 0 q.2.2 := by
    rw [←density_weight_identity J q.1,←density_weight_identity J q.2.1,
      ←density_weight_identity J q.2.2]
    ring
  rw [heq] at hb
  calc
    _ ≤ (C*E*firstLogDensity 0 q.1*firstLogDensity 0 q.2.1*firstLogDensity 0 q.2.2)/S := by
      apply (le_div_iff₀ hS).mpr
      convert hb using 1 ; ring
    _ = _ := by ring

theorem initialBinCost_of_child_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hCₛ : 0 ≤ Cₛ) (hCc : 0 ≤ Cchild)
    (j : SecondLogIndex) (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ)
    (J N : ℕ) (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hchild : ∀ q,
      let s := secondLogSector p ∅ F K R Z M j
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      childGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X q ≤
        (Cchild*(X*initialLogLabel j))*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) :
    initialBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      ((H/Z)*Real.exp 2*Cchild*Cₛ*(∫ t : ℝ,firstLogDensity 0 t)^3)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  let s := secondLogSector p ∅ F K R Z M j
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let G := sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X
  let E := Cchild*(X*initialLogLabel j)
  let S := (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N
  have hpR : 0 < primeProductNorm p R := primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hpR)
  have hlabel : 0 < initialLogLabel j := by
    unfold initialLogLabel secondLogE secondLogV
    exact mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) (Real.exp_pos _)
  have hE : 0 ≤ E := mul_nonneg hCc (mul_pos hX hlabel).le
  have hS : 0 < S := by
    dsimp [S]
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  have hG : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have henergy : ∀ q, G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J := by
    intro q
    exact (sourceGeometricMean_le_ideal p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X q).trans (hchild q)
  have hb := polynomial_density_cost B G J S Cₛ E hS hCₛ hE hB hG hdec henergy
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  calc
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ*E/S)*(∫ t : ℝ,firstLogDensity 0 t)^3) := mul_le_mul_of_nonneg_left hb hpref
    _ = _ := by
      dsimp only [E,X,S]
      rw [initial_log_mass Z (primeProductNorm p R) hpR.ne']
      have hz := hZ.ne'
      have hr := hpR.ne'
      field_simp

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma blockRow_mul (S : Finset ι) (e : ι→ℕ) (a b:O) :
    blockRow p hg S e (a*b)=blockRow p hg S e a*blockRow p hg S e b := by
  simp only [blockRow_eq_product,map_mul,Finset.prod_mul_distrib]

omit [DecidableEq ι] in
lemma blockRow_unit_mul_star (S : Finset ι) (e : ι→ℕ) (u:Oˣ) :
    blockRow p hg S e (u:O)*star (blockRow p hg S e (u:O))=1 := by
  exact GaussGeneratorTransport.finiteSexticRow_unit_mul_star
    (fun i:S=>Ideal.span {p i.val}) (fun i=>hg i.val) (fun i=>e i.val) u

omit [DecidableEq ι] in
lemma originalLabelColumn_unit_c (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (C : Finset ι→ℂ) (u c f : O) (S : Finset ι) :
    originalLabelColumn p hg B ε₁ ε₂ negative C (u*c) f S =
      originalLabelColumn p hg B ε₁ ε₂ negative C c f S*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S u^4 := by
  simp only [originalLabelColumn,finiteSquarefreeRow_mul,mul_pow]
  ring

omit [DecidableEq ι] in
lemma row_four_eq_star_square (S : Finset ι) (u:O) :
    finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S u^4=
      star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S (u^2)) := by
  have h1 : finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S 1=1 := by simp [finiteSquarefreeRow]
  simpa only [h1,star_one,mul_one,one_mul] using
    row_four_star (fun i=>Ideal.span {p i}) hg S u 1

theorem threeGaussRowFactor_common_unit
    (N P B : Finset ι) (hNP:Disjoint N P) (hNB:Disjoint N B) (hPB:Disjoint P B)
    (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (C₁ C₂:Finset ι→ℂ) (u:Oˣ) (c f d h:O) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ ((u:O)*c) f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ ((u:O)*c) f) d h =
    blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)*
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) d ((u:O)^2*h) := by
  have hU:=blockRow_unit_mul_star p hg (cubeActiveSupport B v ε₁ ε₂)
    (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) (u^2)
  simp only [Units.val_pow_eq_pow_val] at hU
  simp only [threeGaussRowFactor,originalLabelColumn_unit_c,row_four_eq_star_square,
    star_mul,star_star,blockRow_mul]
  rw [threeBlockRow_factor p hg N P B hNP hNB hPB v ε₁ ε₂ ((u:O)^2)]
  simp only [star_mul,star_star]
  let a : ℂ := threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
    (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
    (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) d h *
    finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg N ((u:O)^2) *
    star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg P ((u:O)^2))
  convert congrArg (fun z:ℂ=>a*z) hU.symm using 1 <;>
    simp only [a,threeGaussRowFactor,star_mul] <;> ring

theorem actualFirstKernel_common_unit (F B : Finset ι) (hFB:Disjoint F B)
    (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (C₁ C₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ) (X₁ X₂ K:ℝ) (u:Oˣ) (c f d h:O) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ ((u:O)*c) f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ ((u:O)*c) f) W V₁ V₂ X₁ X₂ K d h =
    blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)*
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) W V₁ V₂ X₁ X₂ K d ((u:O)^2*h) := by
  have hn : ‖eisEmbedding ((u:O)^2*h)‖=‖eisEmbedding h‖ := by
    rw [map_mul,norm_mul,map_pow,norm_pow,GaussGeneratorTransport.norm_eisEmbedding_unit,one_pow,one_mul]
  simp only [actualFirstKernel,Finset.mul_sum,hn]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP:Disjoint N P
  · simp only [hNP,ite_true]
    rw [threeGaussRowFactor_common_unit p hp hcop hg N P B hNP
      (hFB.mono_left (Finset.mem_powerset.mp hN)) (hFB.mono_left (Finset.mem_powerset.mp hP))
      v ε₁ ε₂ C₁ C₂ u c f d h]
    ring
  · simp only [hNP,ite_false,mul_zero]

omit [DecidableEq ι] in
theorem commonUnitPhase_norm (B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (u:Oˣ) :
    ‖blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)‖=1 := by
  have h:=blockRow_unit_mul_star p hg (cubeActiveSupport B v ε₁ ε₂)
    (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) (u^2)
  have hn:=congrArg norm h
  simp only [norm_mul,norm_star,norm_one,Units.val_pow_eq_pow_val] at hn
  nlinarith [norm_nonneg (blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2))]

def unitSquareRowEquiv (u:Oˣ) : O≃O where
  toFun h := (u:O)^2*h
  invFun h := ((u⁻¹:Oˣ):O)^2*h
  left_inv h := by
    dsimp only
    rw [←mul_assoc,←mul_pow]
    simp
  right_inv h := by
    dsimp only
    rw [←mul_assoc,←mul_pow]
    simp

theorem tsum_actualFirstKernel_common_unit (F B:Finset ι) (hFB:Disjoint F B)
    (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (C₁ C₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ) (X₁ X₂ K:ℝ) (u:Oˣ) (c f d:O) :
    (∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ ((u:O)*c) f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ ((u:O)*c) f) W V₁ V₂ X₁ X₂ K d h) =
    blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)*
    ∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) W V₁ V₂ X₁ X₂ K d h := by
  let F₀ : O→ℂ := actualFirstKernel p hp hcop hg F B v ε₁ ε₂
    (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
    (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) W V₁ V₂ X₁ X₂ K d
  let q := blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
    (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)
  calc
    _ = ∑'h:O,q*F₀ ((u:O)^2*h) := by
      apply tsum_congr
      intro h
      exact actualFirstKernel_common_unit p hp hcop hg F B hFB v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K u c f d h
    _ = q*∑'h:O,F₀ ((u:O)^2*h) := tsum_mul_left
    _ = q*∑'h:O,F₀ h := by
      exact congrArg (fun z:ℂ=>q*z) ((unitSquareRowEquiv u).tsum_eq F₀)

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

lemma blockRow_at_zero (S:Finset ι) (e:ι→ℕ) :
    blockRow p hg S e 0=if S=∅ then 1 else 0 := by
  by_cases hS:S=∅
  · simp [hS,blockRow_eq_product]
  · rw [ite_eq_right hS,blockRow_eq_product]
    obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr hS
    apply Finset.prod_eq_zero hi
    simp only [map_zero,MulChar.map_zero]

lemma threeGaussRowFactor_zero_nonempty
    (N P B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)
    (C₁ C₂:Finset ι→ℂ) (d:O)
    (hne:(N∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d 0=0 := by
  simp only [threeGaussRowFactor,blockRow_at_zero,ite_eq_right hne,star_zero,mul_zero]

theorem actualFirstKernel_zero
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)
    (C₁ C₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ)
    (X₁ X₂ K:ℝ) (d:O) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d 0 =
      if cubeActiveSupport B v ε₁ ε₂=∅ then
        (V₁ (columnLog p X₁ ∅)*V₂ (columnLog p X₂ ∅))*(K:ℂ)*paperRadialFourier W 0*
          threeGaussRowFactor p hp hcop hg ∅ ∅ B v ε₁ ε₂ C₁ C₂ d 0 else 0 := by
  unfold actualFirstKernel
  by_cases hB:cubeActiveSupport B v ε₁ ε₂=∅
  · rw [ite_eq_left hB,Finset.sum_eq_single ∅]
    · rw [Finset.sum_eq_single ∅]
      · simp only [Finset.disjoint_empty_left,ite_true,Finset.empty_union,hB,
          Finset.prod_empty,map_one,norm_one,Complex.ofReal_one,div_one,map_zero,norm_zero,
          zero_pow (by decide:2≠0),mul_zero,zero_div]
      · intro P hP hP0
        have hn:(∅∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅ := by simpa only [Finset.empty_union,hB,Finset.union_empty] using hP0
        simp only [threeGaussRowFactor_zero_nonempty p hp hcop hg ∅ P B v ε₁ ε₂ C₁ C₂ d hn,mul_zero,ite_self]
      · simp
    · intro N hN hN0
      apply Finset.sum_eq_zero
      intro P hP
      have hn:(N∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅ := by
        intro he
        exact hN0 (Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=>by
          have : i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂:=Finset.mem_union_left _ (Finset.mem_union_left _ hi)
          simp only [he, Finset.notMem_empty] at this))
      simp only [threeGaussRowFactor_zero_nonempty p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d hn,mul_zero,ite_self]
    · simp
  · rw [ite_eq_right hB]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro P hP
    have hn:(N∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅ := by
      intro he
      exact hB (Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=>by
        have : i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂:=Finset.mem_union_right _ hi
        simp only [he, Finset.notMem_empty] at this))
    simp only [threeGaussRowFactor_zero_nonempty p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d hn,mul_zero,ite_self]

theorem actualFirstKernel_truncate
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)
    (C₁ C₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ)
    (X₁ X₂ K:ℝ) (hK:0<K) (d:O) (hd:d≠0) (T:Finset O) :
    (∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h)=
      (∑h∈T,actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h)+
      ∑'h:{h:O//h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val := by
  exact (actualFirstKernel_summable p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd).sum_add_tsum_subtype_compl T |>.symm

end FirstPassCubeLabels

end

end OAI

end Source160

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/H1.lean; sha256: 1f57f218bf2c278403e9af36dfa2578beac71723bbe62fe9c34f51d6012761b8 -/
section Source161
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1`

An upstream-friendly **definition** of a Euclidean `H¹`-type energy space built from `L²`.

At the current Mathlib pin, we do not have a ready-made Sobolev-space development for domains or
manifolds. For the Laplace–Beltrami compact-resolvent discharge, we mainly need:

1. a Hilbert space `H¹` equipped with a continuous embedding into `L²`;
2. a continuous “gradient” map `H¹ → L²(E)`; and later
3. a compactness theorem for the inclusion on bounded domains / compact manifolds (Rellich).

This file defines `H¹` as the closed submodule of `L² × L²(E)` generated by `C¹`-functions with
compact support and their gradients (expressed using the Riesz representation `toDual`).

## Main definitions

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.C1c`:
  the `ℝ`-submodule of `C¹` compactly supported functions `E → ℝ`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1`:
  the (closed) `H¹` submodule of `L²(E) × L²(E,E)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2`:
  the continuous embedding `H¹ → L²`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1ToL2Grad`:
  the continuous gradient map `H¹ → L²(E)`.

No analytic “Sobolev theorems” are proved here; those are tracked separately (Rellich / elliptic
regularity beads).
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory
open MeasureTheory

section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceH1 : MeasurableSpace E := borel E
local instance instBorelSpaceH1 : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceH1 : OpensMeasurableSpace E := by infer_instance

variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

/-- The space of square-integrable real-valued functions. -/
abbrev L2ℝ : Type _ := ↥(E →₂[μ] ℝ)
/-- The space of square-integrable vector-valued functions. -/
abbrev L2E : Type _ := ↥(E →₂[μ] E)
/-- The product space containing a function and its first derivative. -/
abbrev H1Target : Type _ := L2ℝ (μ := μ) × L2E (μ := μ)

/-- `C¹` real-valued functions on `E` with compact support, as a submodule of `E → ℝ`. -/
def C1c : Submodule ℝ (E → ℝ) where
  carrier := {f | ContDiff ℝ 1 f ∧ HasCompactSupport f}
  zero_mem' := by
    refine ⟨contDiff_const, ?_⟩
    simpa using (HasCompactSupport.zero : HasCompactSupport (fun _ : E => (0 : ℝ)))
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c, ?_⟩
    -- `HasCompactSupport` is stable under pointwise scalar multiplication.
    exact (HasCompactSupport.smul_left (f := fun _ : E => c) hf.2)

/-- The pointwise gradient (as an `E`-valued function), via Riesz representation. -/
noncomputable def grad (f : E → ℝ) : E → E :=
  fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)

lemma continuous_grad {f : E → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (grad (E := E) f) := by
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have : Continuous fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp hcont
  exact this

lemma hasCompactSupport_grad {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (grad (E := E) f) := by
  -- Outside the support of `f`, `fderiv` is identically `0`, hence so is `grad`.
  have hf' : HasCompactSupport (fderiv ℝ f) := hf.fderiv ℝ
  -- `grad` is composition with a linear map sending `0` to `0`.
  exact
    (HasCompactSupport.comp_left (f := fderiv ℝ f) (g := (InnerProductSpace.toDual ℝ E).symm)
      hf' (by simp))

lemma tsupport_grad_subset (f : E → ℝ) : tsupport (grad (E := E) f) ⊆ tsupport f := by
  have hcomp :
      tsupport (grad (E := E) f) ⊆ tsupport (fderiv ℝ f) := by
    exact
      (tsupport_comp_subset
        (g := (InnerProductSpace.toDual ℝ E).symm) (hg := by simp)
        (f := fderiv ℝ f))
  exact hcomp.trans (tsupport_fderiv_subset (𝕜 := ℝ) (f := f))

omit [CompleteSpace E] in
lemma memLp_of_mem_C1c {f : E → ℝ} (hf : f ∈ C1c (E := E)) : MemLp f 2 μ := by
  exact (hf.1.continuous.memLp_of_hasCompactSupport (μ := μ) (p := (2 : ℝ≥0∞)) hf.2)

lemma memLp_grad_of_mem_C1c {f : E → ℝ} (hf : f ∈ C1c (E := E)) :
    MemLp (grad (E := E) f) 2 μ := by
  have hcont : Continuous (grad (E := E) f) := continuous_grad (E := E) (f := f) hf.1
  have hcs : HasCompactSupport (grad (E := E) f) := hasCompactSupport_grad (E := E) (f := f) hf.2
  exact hcont.memLp_of_hasCompactSupport (μ := μ) (p := (2 : ℝ≥0∞)) hcs

/-- The `L²` class of a `C¹` compactly supported function. -/
noncomputable def toL2 (f : ↥(C1c (E := E))) : L2ℝ (μ := μ) :=
  (memLp_of_mem_C1c (μ := μ) (E := E) f.2).toLp f.1

/-- The `L²` class of the gradient of a `C¹` compactly supported function. -/
noncomputable def toL2Grad (f : ↥(C1c (E := E))) : L2E (μ := μ) :=
  (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).toLp (grad (E := E) f.1)

omit [CompleteSpace E] in
private lemma toL2_add (f g : ↥(C1c (E := E))) :
    toL2 (μ := μ) (E := E) (f + g) =
      toL2 (μ := μ) (E := E) f + toL2 (μ := μ) (E := E) g := by
  apply Lp.ext
  have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hg : (toL2 (μ := μ) (E := E) g : E → ℝ) =ᵐ[μ] g.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) g.2).coeFn_toLp
  have hfg : (toL2 (μ := μ) (E := E) (f + g) : E → ℝ) =ᵐ[μ] (f.1 + g.1) :=
    (memLp_of_mem_C1c (μ := μ) (E := E) (f + g).2).coeFn_toLp
  -- Both sides agree a.e. with `f + g`.
  refine hfg.trans ?_
  filter_upwards [Lp.coeFn_add (toL2 (μ := μ) (E := E) f) (toL2 (μ := μ) (E := E) g), hf, hg]
    with x hxadd hxf hxg
  -- Rewrite both sides in terms of pointwise evaluation.
  calc
    f.1 x + g.1 x =
        (toL2 (μ := μ) (E := E) f : E → ℝ) x +
          (toL2 (μ := μ) (E := E) g : E → ℝ) x := by
      simp [hxf, hxg]
    _ = ((toL2 (μ := μ) (E := E) f + toL2 (μ := μ) (E := E) g : L2ℝ (μ := μ)) : E → ℝ) x := by
      simpa [Pi.add_apply] using hxadd.symm

omit [CompleteSpace E] in
private lemma toL2_smul (c : ℝ) (f : ↥(C1c (E := E))) :
    toL2 (μ := μ) (E := E) (c • f) = c • toL2 (μ := μ) (E := E) f := by
  apply Lp.ext
  have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hcf : (toL2 (μ := μ) (E := E) (c • f) : E → ℝ) =ᵐ[μ] (c • f.1) :=
    (memLp_of_mem_C1c (μ := μ) (E := E) (c • f).2).coeFn_toLp
  refine hcf.trans ?_
  filter_upwards [Lp.coeFn_smul c (toL2 (μ := μ) (E := E) f), hf] with x hxsmul hxf
  simp [Pi.smul_apply, hxsmul, hxf]

/-- Linear map sending `C¹_c` functions to their `L²` classes. -/
noncomputable def toL2Linear : ↥(C1c (E := E)) →ₗ[ℝ] L2ℝ (μ := μ) where
  toFun := toL2 (μ := μ) (E := E)
  map_add' := by exact toL2_add (μ := μ) (E := E)
  map_smul' := by exact toL2_smul (μ := μ) (E := E)

private lemma toL2Grad_add (f g : ↥(C1c (E := E))) :
    toL2Grad (μ := μ) (E := E) (f + g) =
      toL2Grad (μ := μ) (E := E) f + toL2Grad (μ := μ) (E := E) g := by
  apply Lp.ext
  have hf : (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hg : (toL2Grad (μ := μ) (E := E) g : E → E) =ᵐ[μ] grad (E := E) g.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) g.2).coeFn_toLp
  have hfg :
      (toL2Grad (μ := μ) (E := E) (f + g) : E → E) =ᵐ[μ] grad (E := E) (f.1 + g.1) :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) (f + g).2).coeFn_toLp
  refine hfg.trans ?_
  filter_upwards [Lp.coeFn_add (toL2Grad (μ := μ) (E := E) f) (toL2Grad (μ := μ) (E := E) g), hf,
    hg] with x hxadd hxf hxg
  have hdf : DifferentiableAt ℝ f.1 x :=
    (f.2.1.differentiable one_ne_zero).differentiableAt
  have hdg : DifferentiableAt ℝ g.1 x :=
    (g.2.1.differentiable one_ne_zero).differentiableAt
  -- Rewrite in terms of pointwise evaluation and use linearity of `grad`.
  have hgrad :
      grad (E := E) (f.1 + g.1) x = grad (E := E) f.1 x + grad (E := E) g.1 x := by
    simp [grad, fderiv_add hdf hdg, map_add]
  calc
    grad (E := E) (f.1 + g.1) x = grad (E := E) f.1 x + grad (E := E) g.1 x := hgrad
    _ =
        (toL2Grad (μ := μ) (E := E) f : E → E) x +
          (toL2Grad (μ := μ) (E := E) g : E → E) x := by
        simp [hxf, hxg]
    _ = ((toL2Grad (μ := μ) (E := E) f +
            toL2Grad (μ := μ) (E := E) g : L2E (μ := μ)) :
            E → E) x := by
        simpa [Pi.add_apply] using hxadd.symm

private lemma toL2Grad_smul (c : ℝ) (f : ↥(C1c (E := E))) :
    toL2Grad (μ := μ) (E := E) (c • f) = c • toL2Grad (μ := μ) (E := E) f := by
  apply Lp.ext
  have hf : (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hcf :
      (toL2Grad (μ := μ) (E := E) (c • f) : E → E) =ᵐ[μ] grad (E := E) (c • f.1) :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) (c • f).2).coeFn_toLp
  refine hcf.trans ?_
  filter_upwards [Lp.coeFn_smul c (toL2Grad (μ := μ) (E := E) f), hf] with x hxsmul hxf
  have hdf : DifferentiableAt ℝ f.1 x :=
    (f.2.1.differentiable one_ne_zero).differentiableAt
  have hgrad : grad (E := E) (c • f.1) x = c • grad (E := E) f.1 x := by
    simp [grad, fderiv_const_smul hdf, map_smul]
  calc
    grad (E := E) (c • f.1) x = c • grad (E := E) f.1 x := hgrad
    _ = c • (toL2Grad (μ := μ) (E := E) f : E → E) x := by
      simp [hxf]
    _ = ((c • toL2Grad (μ := μ) (E := E) f : L2E (μ := μ)) : E → E) x := by
      -- `Lp.coeFn_smul` gives the pointwise evaluation of `c • f` in `L²`.
      simpa [Pi.smul_apply] using hxsmul.symm

/-- Linear map sending `C¹_c` functions to the `L²` class of their gradient. -/
noncomputable def toL2GradLinear : ↥(C1c (E := E)) →ₗ[ℝ] L2E (μ := μ) where
  toFun := toL2Grad (μ := μ) (E := E)
  map_add' := by exact toL2Grad_add (μ := μ) (E := E)
  map_smul' := by exact toL2Grad_smul (μ := μ) (E := E)

/-- The graph map `f ↦ (f, ∇f)` into `L² × L²(E)`. -/
noncomputable def graph : ↥(C1c (E := E)) →ₗ[ℝ] H1Target (μ := μ) :=
  (toL2Linear (μ := μ) (E := E)).prod (toL2GradLinear (μ := μ) (E := E))

/-- The Euclidean `H¹` space (as a closed submodule of `L² × L²(E)`). -/
noncomputable def h1 : Submodule ℝ (H1Target (μ := μ)) :=
  (LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure

/-- The Euclidean `H¹` submodule is closed by construction. -/
theorem isClosed_h1 : IsClosed (h1 (μ := μ) (E := E) : Set (H1Target (μ := μ))) := by
  delta h1
  exact Submodule.isClosed_topologicalClosure (LinearMap.range (graph (μ := μ) (E := E)))

/-- `H¹` is complete (a Hilbert space once the ambient `L²` spaces are). -/
instance instCompleteSpaceh1 : CompleteSpace (↥(h1 (μ := μ) (E := E))) := by
  classical
  exact (isClosed_h1 (μ := μ) (E := E)).isComplete.completeSpace_coe

/-- The continuous embedding `H¹ → L²`. -/
noncomputable def h1ToL2 : (↥(h1 (μ := μ) (E := E))) →L[ℝ] L2ℝ (μ := μ) :=
  (ContinuousLinearMap.fst ℝ (L2ℝ (μ := μ)) (L2E (μ := μ))).comp
    (Submodule.subtypeL (h1 (μ := μ) (E := E)))

/-- The continuous gradient map `H¹ → L²(E)`. -/
noncomputable def h1ToL2Grad : (↥(h1 (μ := μ) (E := E))) →L[ℝ] L2E (μ := μ) :=
  (ContinuousLinearMap.snd ℝ (L2ℝ (μ := μ)) (L2E (μ := μ))).comp
    (Submodule.subtypeL (h1 (μ := μ) (E := E)))

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source161

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/Translation.lean; sha256: d5400e025eab0f4308c8023e62d4a1c6b2166e86ea4be2c9c6b68363831235c5 -/
section Source162
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation`

Translation utilities for the Euclidean Sobolev model spaces.

This file is intentionally “pre-Rellich”: it provides the algebraic/measure-theoretic translation
operators and their interaction with the `C¹_c` graph embedding used to define `H¹`.

## Main results

- `translateC1c`: translation as a linear endomorphism of `C¹_c`.
- `translateL2`: translation as a linear isometry of `L²` (under an invariant measure).
- `translateL2_toL2` / `translateL2_toL2Grad`: translation commutes with `toL2` / `toL2Grad`.
- `grad_translate`: the Euclidean gradient commutes with translation.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory

section Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Translate a function by `a` (right translation): `x ↦ f (x + a)`. -/
def translate {F : Type*} (a : E) (f : E → F) : E → F :=
  fun x => f (x + a)

omit [CompleteSpace E] in
lemma contDiff_translate {f : E → ℝ} (hf : ContDiff ℝ 1 f) (a : E) :
    ContDiff ℝ 1 (translate (E := E) a f) := by
  -- `x ↦ x + a` is `C^∞`; compose.
  exact hf.comp (contDiff_id.add contDiff_const)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma hasCompactSupport_translate {F : Type*} [Zero F] {f : E → F}
    (hf : HasCompactSupport f) (a : E) : HasCompactSupport (translate (E := E) a f) := by
  exact hf.comp_homeomorph (Homeomorph.addRight a)

lemma grad_translate (a : E) (f : E → ℝ) (x : E) :
    grad (E := E) (translate (E := E) a f) x = grad (E := E) f (x + a) := by
  classical
  -- `fderiv` commutes with translation, hence so does `grad`.
  -- Reduce to the standard `fderiv` translation lemma, applied under the Riesz dual map.
  have hfderiv : fderiv ℝ (translate (E := E) a f) x = fderiv ℝ f (x + a) :=
    fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) a
  simp only [grad, hfderiv]

omit [CompleteSpace E] in
lemma mem_C1c_translate {f : E → ℝ} (hf : f ∈ C1c (E := E)) (a : E) :
    translate (E := E) a f ∈ C1c (E := E) :=
  ⟨contDiff_translate (E := E) hf.1 a, hasCompactSupport_translate (E := E) hf.2 a⟩

/-- Translation as a linear endomorphism of `C¹_c`. -/
noncomputable def translateC1c (a : E) : ↥(C1c (E := E)) →ₗ[ℝ] ↥(C1c (E := E)) where
  toFun f := ⟨translate (E := E) a f.1, mem_C1c_translate (E := E) (f := f.1) f.2 a⟩
  map_add' f g := by
    ext x
    simp [translate]
  map_smul' c f := by
    ext x
    simp [translate]

end Topology

section Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceTranslation : MeasurableSpace E := borel E
local instance instBorelSpaceTranslation : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceTranslation : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddTranslation : MeasurableAdd E := by
  infer_instance

variable (μ : Measure E) [μ.IsAddRightInvariant]

/-- Translation on `L²` as a linear isometry, under an additive right-invariant measure. -/
noncomputable def translateL2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E) :
    (E →₂[μ] F) →ₗᵢ[ℝ] (E →₂[μ] F) := by
  classical
  simpa using
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := F) (p := (2 : ENNReal))
      (μ := μ) (μb := μ) (f := fun x : E => x + a) (MeasureTheory.measurePreserving_add_right μ a))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma translateL2_ae_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (g : E →₂[μ] F) :
    (translateL2 (μ := μ) (F := F) a g : E → F) =ᵐ[μ] fun x => (g : E → F) (x + a) := by
  classical
  -- Reduce to `Lp.coeFn_compMeasurePreserving`.
  exact
    (MeasureTheory.Lp.coeFn_compMeasurePreserving (g := (g : MeasureTheory.Lp F (2 : ENNReal) μ))
      (hf := MeasureTheory.measurePreserving_add_right μ a))

variable [IsFiniteMeasureOnCompacts μ]

omit [CompleteSpace E] in
lemma translateL2_toL2 (a : E) (f : ↥(C1c (E := E))) :
    translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) =
      toL2 (μ := μ) (E := E) (translateC1c (E := E) a f) := by
  apply Lp.ext
  have h₁ :
      (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) : E → ℝ) =ᵐ[μ]
        fun x => f.1 (x + a) := by
    have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hf' :
        (fun x => (toL2 (μ := μ) (E := E) f : E → ℝ) (x + a)) =ᵐ[μ] fun x => f.1 (x + a) := by
      -- Move the a.e. equality through a measure-preserving map.
      exact
        (Measure.QuasiMeasurePreserving.ae_eq_comp
          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
    exact (translateL2_ae_eq (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f)).trans hf'
  have h₂ :
      (toL2 (μ := μ) (E := E) (translateC1c (E := E) a f) : E → ℝ) =ᵐ[μ]
        fun x => f.1 (x + a) := by
    -- `toL2` agrees a.e. with the underlying translated function.
    exact
      (memLp_of_mem_C1c (μ := μ) (E := E) (translateC1c (E := E) a f).2).coeFn_toLp
  exact h₁.trans h₂.symm

lemma translateL2_toL2Grad (a : E) (f : ↥(C1c (E := E))) :
    translateL2 (μ := μ) (F := E) a (toL2Grad (μ := μ) (E := E) f) =
      toL2Grad (μ := μ) (E := E) (translateC1c (E := E) a f) := by
  apply Lp.ext
  have h₁ :
      (translateL2 (μ := μ) (F := E) a (toL2Grad (μ := μ) (E := E) f) : E → E) =ᵐ[μ]
        fun x => grad (E := E) f.1 (x + a) := by
    have hf :
        (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hf' :
        (fun x => (toL2Grad (μ := μ) (E := E) f : E → E) (x + a)) =ᵐ[μ]
          fun x => grad (E := E) f.1 (x + a) := by
      exact
        (Measure.QuasiMeasurePreserving.ae_eq_comp
          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
    exact
      (translateL2_ae_eq (μ := μ) (F := E) a (toL2Grad (μ := μ) (E := E) f)).trans hf'
  have h₂ :
      (toL2Grad (μ := μ) (E := E) (translateC1c (E := E) a f) : E → E) =ᵐ[μ]
        fun x => grad (E := E) f.1 (x + a) := by
    have hTo :
        (toL2Grad (μ := μ) (E := E) (translateC1c (E := E) a f) : E → E) =ᵐ[μ]
          grad (E := E) (translate (E := E) a f.1) :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) (translateC1c (E := E) a f).2).coeFn_toLp
    have hGrad :
        grad (E := E) (translate (E := E) a f.1) = fun x => grad (E := E) f.1 (x + a) := by
      funext x
      simpa [translate] using grad_translate (E := E) a f.1 x
    exact hTo.trans (by simp [hGrad])
  exact h₁.trans h₂.symm

end Measure

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source162

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/TranslationEstimate.lean; sha256: 2cad4121361afa1f790c17f1af1f2feeb8bde75e2d9b26136e7a17992ee6bf17 -/
section Source163
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimate`

Pointwise translation estimates for `C¹_c` functions on Euclidean spaces.

This file provides the key analytic inequality used later in the Euclidean Rellich step:
translation differences are controlled by the `L²`-gradient.

At this stage we only prove *pointwise* inequalities along the segment `t ↦ x + t • a`.
The measure-theoretic lifting to `L²` is tracked separately under `lean-103.5.2.26.5.3.2.3`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceTranslationEstimate :
    MeasurableSpace E := borel E
local instance instBorelSpaceTranslationEstimate :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceTranslationEstimate :
    OpensMeasurableSpace E := by
  infer_instance

/-! ## Derivative along a translated line -/

/-- The affine line `t ↦ x + t • a`. -/
def line (x a : E) (t : ℝ) : E :=
  x + t • a

lemma hasDerivAt_line (x a : E) (t : ℝ) :
    HasDerivAt (line (x := x) (a := a)) a t := by
  -- `t ↦ t • a` has derivative `a`, and adding the constant `x` preserves the derivative.
  have hsmul : HasDerivAt (fun t : ℝ => t • a) a t := by
    simpa [one_smul] using (hasDerivAt_id t).smul_const a
  exact HasDerivAt.const_add x hsmul

lemma deriv_line (x a : E) (t : ℝ) :
    deriv (line (x := x) (a := a)) t = a :=
  (hasDerivAt_line (x := x) (a := a) t).deriv

lemma hasDerivAt_comp_line
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    HasDerivAt (fun t => f (line (x := x) (a := a) t))
      (fderiv ℝ f (line (x := x) (a := a) t) a) t := by
  have hf' : HasFDerivAt f (fderiv ℝ f (line (x := x) (a := a) t)) (line (x := x) (a := a) t) :=
    (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  exact
    HasFDerivAt.comp_hasDerivAt_of_eq t hf' (hasDerivAt_line (x := x) (a := a) t) rfl

lemma deriv_comp_line {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    deriv (fun t => f (line (x := x) (a := a) t)) t =
      fderiv ℝ f (line (x := x) (a := a) t) a :=
  (hasDerivAt_comp_line (hf := hf) (x := x) (a := a) t).deriv

/-! ## Pointwise translation bound via the gradient -/

section

variable [CompleteSpace E]

lemma enorm_fderiv_apply_le_enorm_grad_mul (f : E → ℝ) (x a : E) :
    ‖fderiv ℝ f x a‖ₑ ≤ ‖grad (E := E) f x‖ₑ * ‖a‖ₑ := by
  -- Use the operator norm bound, then identify `‖fderiv‖` with `‖grad‖` via the Riesz isometry.
  have h₁ :
      ‖fderiv ℝ f x a‖ₑ ≤ ‖fderiv ℝ f x‖ₑ * ‖a‖ₑ :=
    (ContinuousLinearMap.le_opENorm (f := fderiv ℝ f x) a)
  have h₂ : ‖grad (E := E) f x‖ₑ = ‖fderiv ℝ f x‖ₑ := by
    -- `grad f x = (toDual).symm (fderiv f x)` and `toDual.symm` is an isometry.
    simp only [grad]
    exact
      (LinearIsometry.enorm_map
        (f := (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry)
        (fderiv ℝ f x))
  -- Replace the operator norm by the gradient norm.
  simpa [h₂, mul_assoc, mul_left_comm, mul_comm] using h₁

lemma enorm_deriv_comp_line_le (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    ‖deriv (fun t => f (line (x := x) (a := a) t)) t‖ₑ ≤
      ‖a‖ₑ * ‖grad (E := E) f (line (x := x) (a := a) t)‖ₑ := by
  -- Reduce to the `fderiv` bound.
  have :=
    enorm_fderiv_apply_le_enorm_grad_mul
      (E := E) (f := f) (x := line (x := x) (a := a) t) (a := a)
  -- Rewrite `deriv` and commute the product.
  simpa [deriv_comp_line (hf := hf) (x := x) (a := a) t,
    mul_comm, mul_left_comm, mul_assoc] using this

lemma enorm_sub_le_enorm_mul_lintegral_grad (x a : E) {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    ‖f (x + a) - f x‖ₑ ≤
      ‖a‖ₑ * ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖grad (E := E) f (x + t • a)‖ₑ := by
  -- Apply FTC along the segment `t ↦ x + t • a`, then bound the derivative pointwise.
  have hCont :
      ContDiffOn ℝ 1 (fun t : ℝ => f (x + t • a)) (Set.Icc (0 : ℝ) 1) := by
    -- `t ↦ x + t • a` is `C^∞`; compose with `f`.
    have hInner : ContDiff ℝ ⊤ (fun t : ℝ => x + t • a) := by
      simpa [line] using
        (contDiff_const.add (contDiff_id.smul (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => a))))
    have hInner' : ContDiff ℝ 1 (fun t : ℝ => x + t • a) := hInner.of_le (by simp)
    exact (hf.comp hInner').contDiffOn
  have hFTC :
      ‖f (x + a) - f x‖ₑ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ := by
    simpa using
      (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (f := fun t : ℝ => f (x + t • a))
        (a := (0 : ℝ)) (b := 1) hCont (by exact zero_le_one))
  refine hFTC.trans ?_
  have hDerivBound :
      (fun t : ℝ => ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ)
        ≤ᵐ[Measure.restrict volume (Set.Icc (0 : ℝ) 1)]
          fun t : ℝ => ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    -- Pointwise bound holds everywhere.
    refine (ae_of_all _ fun t => ?_)
    -- `deriv` along `t ↦ x + t•a` is controlled by the gradient.
    simpa [line, mul_assoc, mul_left_comm, mul_comm] using
      (enorm_deriv_comp_line_le (x := x) (a := a) (f := f) hf (t := t))
  -- Pull out the constant `‖a‖ₑ`.
  have :
      (∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun t : ℝ => f (x + t • a)) t‖ₑ) ≤
        ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖a‖ₑ * ‖grad (E := E) f (x + t • a)‖ₑ := by
    exact lintegral_mono_ae hDerivBound
  refine this.trans ?_
  -- Pull out the constant factor.
  have hMeas :
      Measurable fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ := by
    -- `grad f` is continuous when `f` is `C¹`.
    have hgradCont : Continuous (grad (E := E) f) := continuous_grad (E := E) (f := f) (by
      -- `ContDiff` gives continuity of `grad`.
      exact hf)
    -- hence `t ↦ grad f (x + t•a)` is measurable; take `enorm`.
    exact (hgradCont.comp (by
      have : Continuous (fun t : ℝ => x + t • a) := by
        fun_prop
      exact this)).measurable.enorm
  -- Now finish: `∫⁻ t in Set.Icc, ‖a‖ * g t = ‖a‖ * ∫⁻ t in Set.Icc, g t`.
  exact le_of_eq <| by
    simpa [mul_assoc] using
      (MeasureTheory.lintegral_const_mul (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (r := ‖a‖ₑ)
        (f := fun t : ℝ => ‖grad (E := E) f (x + t • a)‖ₑ) hMeas)

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source163

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/TranslationEstimateL2.lean; sha256: d1ea05bbbe6ae3fcc0effc4b46b2ddfc2c898f30c9ab4e2f52453b48d54c11a7 -/
section Source164
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2`

`L²` translation estimates for Euclidean `C¹_c` functions (and derived `H¹`) under invariant
measures.

This file lifts the pointwise fundamental-theorem-of-calculus bound from
`Euclidean.TranslationEstimate` to an `L²` bound using Tonelli and the measure-preserving property
of translations.

## Main results

- `enorm_translateL2_sub_toL2_le`: for `f ∈ C¹_c`, `‖τ_a f - f‖₂ ≤ ‖a‖ · ‖∇f‖₂` (as an `ℝ≥0∞`
  inequality on `L²` norms), under a right-invariant measure.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceTranslationEstimateL2 :
    MeasurableSpace E := borel E
local instance instBorelSpaceTranslationEstimateL2 :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceTranslationEstimateL2 :
    OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddTranslationEstimateL2 : MeasurableAdd E := by
  infer_instance

variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

private abbrev μI : Measure ℝ := (volume.restrict (Set.Icc (0 : ℝ) 1))

private lemma μI_univ : (μI : Measure ℝ) Set.univ = (1 : ℝ≥0∞) := by
  simp [μI, Measure.restrict_apply, Real.volume_Icc]

private lemma holderConj_two_two : (2 : ℝ).HolderConjugate (2 : ℝ) := by
  refine (Real.holderConjugate_iff).2 ?_
  constructor
  · linarith
  · norm_num

private lemma lintegral_rpow_two_le_lintegral_rpow_two
    {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g (μI : Measure ℝ)) :
    (∫⁻ t, g t ∂(μI : Measure ℝ)) ^ (2 : ℝ) ≤ ∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
  -- Hölder with `g * 1` gives `∫ g ≤ (∫ g^2)^(1/2) * (∫ 1^2)^(1/2)`.
  have hHolder :
      (∫⁻ t, g t ∂(μI : Measure ℝ)) ≤
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ _t : ℝ, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [Pi.mul_apply] using
      (ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := (μI : Measure ℝ)) holderConj_two_two
        hg (aemeasurable_const : AEMeasurable (fun _t : ℝ => (1 : ℝ≥0∞)) (μI : Measure ℝ)))
  have h1 : (∫⁻ _t : ℝ, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) = (1 : ℝ≥0∞) := by
    -- `μI` has total mass `1`, and `1^2 = 1`.
    simp
  have h :
      (∫⁻ t, g t ∂(μI : Measure ℝ)) ≤
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [h1, mul_one] using hHolder
  -- Raise to the power `2` and simplify `((A)^(1/2))^2 = A`.
  have h' :=
    ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  -- Rewrite the RHS using `rpow_mul`.
  simpa [ENNReal.rpow_mul] using (h'.trans_eq (by
    have : (1 / (2 : ℝ)) * (2 : ℝ) = (1 : ℝ) := by norm_num
    simpa [this] using
      (ENNReal.rpow_mul
        (∫⁻ t, g t ^ (2 : ℝ) ∂(μI : Measure ℝ))
        (1 / (2 : ℝ)) (2 : ℝ)).symm))

omit [IsFiniteMeasureOnCompacts μ] in
/-- `L²` translation estimate for `C¹_c` functions under a right-invariant measure. -/
private lemma lintegral_enorm_sub_sq_le (a : E) (f : ↥(C1c (E := E))) :
    (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
      ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
  -- Pointwise: Cauchy–Schwarz in `t`, then Tonelli in `(x,t)`.
  have hpt :
      ∀ x : E,
        ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
          ‖a‖ₑ ^ (2 : ℝ) *
            ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
    intro x
    have h0 := enorm_sub_le_enorm_mul_lintegral_grad (E := E) (x := x) (a := a) (f := f.1)
      (hf := f.2.1)
    -- Square both sides and apply Cauchy–Schwarz in `t`.
    have h1 :
        ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ≤
          (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
      exact ENNReal.rpow_le_rpow h0 (by norm_num)
    have hcs :
        (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) ≤
          ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) := by
      refine lintegral_rpow_two_le_lintegral_rpow_two (g := fun t : ℝ =>
        ‖grad (E := E) f.1 (x + t • a)‖ₑ) ?_
      -- measurability from continuity of `grad`.
      have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
      have hline : Continuous fun t : ℝ => x + t • a := by
        fun_prop
      exact (hgrad.comp hline).measurable.enorm.aemeasurable
    -- Combine and rewrite.
    calc
      ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ)
          ≤ (‖a‖ₑ * ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ∂(μI : Measure ℝ)) ^ (2 : ℝ) := h1
      _ = ‖a‖ₑ ^ (2 : ℝ) *
          (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
            ∂(μI : Measure ℝ)) ^ (2 : ℝ) := by
          simpa using
            (ENNReal.mul_rpow_of_nonneg ‖a‖ₑ
              (∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ
                ∂(μI : Measure ℝ))
              (show (0 : ℝ) ≤ (2 : ℝ) by norm_num))
      _ ≤ ‖a‖ₑ ^ (2 : ℝ) *
          ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
            ∂(μI : Measure ℝ) := by
          gcongr
      _ = ‖a‖ₑ ^ (2 : ℝ) *
          ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ)
            ∂(μI : Measure ℝ) := rfl
  -- Integrate over `x` and apply Tonelli to swap integrals.
  let F : E × ℝ → ℝ≥0∞ :=
    fun z => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ ^ (2 : ℝ)
  have hmeas :
      AEMeasurable
        F (μ.prod (μI : Measure ℝ)) := by
    have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
    have hcont : Continuous fun z : E × ℝ => z.1 + z.2 • a := by
      fun_prop
    have hbase : Measurable fun z : E × ℝ => ‖grad (E := E) f.1 (z.1 + z.2 • a)‖ₑ := by
      exact (hgrad.comp hcont).measurable.enorm
    have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
      (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
    exact (hpow.comp hbase).aemeasurable
  have hTonelli :
      (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) =
        ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
    -- Tonelli in both orders, via the product measure.
    have hprod :
        (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
          ∫⁻ x, ∫⁻ t, F (x, t) ∂(μI : Measure ℝ) ∂μ :=
      MeasureTheory.lintegral_prod (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
    have hprod_symm :
        (∫⁻ z, F z ∂μ.prod (μI : Measure ℝ)) =
          ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) :=
      MeasureTheory.lintegral_prod_symm (μ := μ) (ν := (μI : Measure ℝ)) F hmeas
    calc
      (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ)
          = ∫⁻ z, F z ∂μ.prod (μI : Measure ℝ) := by
              simpa [F] using hprod.symm
      _ = ∫⁻ t, ∫⁻ x, F (x, t) ∂μ ∂(μI : Measure ℝ) := hprod_symm
      _ = ∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ) := by
              simp [F]
  -- Now use measure-preserving translation in `x` and evaluate the `t`-integral.
  have hShift :
      (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) =
        ∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ) := by
    refine MeasureTheory.lintegral_congr fun t => ?_
    -- Change of variables `x ↦ x + t•a`.
    have hmeas' : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) := by
      have hgrad : Continuous (grad (E := E) f.1) := continuous_grad (E := E) (f := f.1) f.2.1
      have hbase : Measurable fun x : E => ‖grad (E := E) f.1 x‖ₑ := hgrad.measurable.enorm
      have hpow : Measurable fun r : ℝ≥0∞ => r ^ (2 : ℝ) :=
        (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable
      exact hpow.comp hbase
    simpa [Function.comp, add_assoc] using
      (MeasureTheory.measurePreserving_add_right μ (t • a)).lintegral_comp (μ := μ) (ν := μ)
        (f := fun x : E => ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ)) hmeas'
  have hEval :
      (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) =
        (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
    -- `μI` has total mass `1`.
    simp [μI, Measure.restrict_apply, Real.volume_Icc]
  -- Put everything together.
  have hInt :
      (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ≤
        ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
    calc
      (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ)
          ≤ ∫⁻ x, ‖a‖ₑ ^ (2 : ℝ) *
                ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ := by
            refine MeasureTheory.lintegral_mono ?_
            intro x
            exact hpt x
      _ = ‖a‖ₑ ^ (2 : ℝ) *
            (∫⁻ x, ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ) ∂μ) := by
            -- Pull out the constant using `lintegral_const_mul''`.
            have hInner :
                AEMeasurable
                  (fun x : E =>
                    ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) μ := by
              -- Measurability of the inner integral follows
              -- from `hmeas` via
              -- `AEMeasurable.lintegral_prod_right'`.
              simpa [F] using (hmeas.lintegral_prod_right' (μ := μ) (ν := (μI : Measure ℝ)))
            simpa [mul_assoc] using
              (MeasureTheory.lintegral_const_mul'' (μ := μ) (r := ‖a‖ₑ ^ (2 : ℝ))
                (f := fun x : E =>
                  ∫⁻ t, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂(μI : Measure ℝ)) hInner)
      _ = ‖a‖ₑ ^ (2 : ℝ) *
            (∫⁻ t, ∫⁻ x, ‖grad (E := E) f.1 (x + t • a)‖ₑ ^ (2 : ℝ) ∂μ ∂(μI : Measure ℝ)) := by
            exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hTonelli
      _ = ‖a‖ₑ ^ (2 : ℝ) *
            (∫⁻ t, (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ∂(μI : Measure ℝ)) := by
            exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hShift
      _ = ‖a‖ₑ ^ (2 : ℝ) * (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) := by
            exact congrArg (fun z => ‖a‖ₑ ^ (2 : ℝ) * z) hEval
  exact hInt

lemma enorm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ₑ ≤
      ‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ := by
  classical
  -- Reduce to an `eLpNorm` inequality on representatives.
  have hL2 :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
          toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => (f.1 (x + a) - f.1 x)) (2 : ℝ≥0∞) μ := by
    -- Both terms agree a.e. with the underlying pointwise translation.
    have h₁ :
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) := by
      have hf :
          (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
        (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
      have hf' :
          (fun x => (toL2 (μ := μ) (E := E) f : E → ℝ) (x + a)) =ᵐ[μ] fun x => f.1 (x + a) := by
        exact
          (Measure.QuasiMeasurePreserving.ae_eq_comp
            (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
      exact (translateL2_ae_eq (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f)).trans hf'
    have h₂ : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] fun x => f.1 x :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hsub :
        ((translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
              toL2 (μ := μ) (E := E) f : E →₂[μ] ℝ) : E → ℝ) =ᵐ[μ]
          fun x => f.1 (x + a) - f.1 x := by
      filter_upwards [Lp.coeFn_sub
        (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f))
        (toL2 (μ := μ) (E := E) f), h₁, h₂] with x hxsub hx1 hx2
      simpa [hx1, hx2, Pi.sub_apply] using hxsub
    -- Convert the `Lp` norm to `eLpNorm` and rewrite using a.e. equality.
    let d : E →₂[μ] ℝ :=
      translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) - toL2 (μ := μ) (E := E) f
    have hd0 : (‖d‖ₑ : ℝ≥0∞) = MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have hd1 :
        MeasureTheory.eLpNorm (fun x : E => (d : E → ℝ) x) (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) (by simpa [d] using hsub)
    simpa [d] using hd0.trans hd1
  have hGrad :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
        MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    have h₁ :
        (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] fun x => grad (E := E) f.1 x :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have h0 :
        (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) =
          MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ := by
      simp [MeasureTheory.Lp.enorm_def]
    have h1 :
        MeasureTheory.eLpNorm (fun x : E => (toL2Grad (μ := μ) (E := E) f : E → E) x)
            (2 : ℝ≥0∞) μ =
          MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ :=
      MeasureTheory.eLpNorm_congr_ae (μ := μ) (p := (2 : ℝ≥0∞)) h₁
    exact h0.trans h1
  -- Prove the `eLpNorm` inequality by squaring, using Tonelli and measure-preserving translation.
  have hCore :
      MeasureTheory.eLpNorm (fun x : E => f.1 (x + a) - f.1 x) (2 : ℝ≥0∞) μ ≤
        ‖a‖ₑ * MeasureTheory.eLpNorm (fun x : E => grad (E := E) f.1 x) (2 : ℝ≥0∞) μ := by
    -- Expand the definition of `eLpNorm` at exponent `2`.
    have h2_ne0 : (2 : ℝ≥0∞) ≠ 0 := by simp
    have h2_netop : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by simp
    have hf_meas : MeasureTheory.AEStronglyMeasurable (fun x : E => f.1 x) μ :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).aestronglyMeasurable
    have hshift_meas :
        MeasureTheory.AEStronglyMeasurable (fun x : E => f.1 (x + a) - f.1 x) μ := by
      have hshift : MeasureTheory.AEStronglyMeasurable (fun x : E => f.1 (x + a)) μ :=
        hf_meas.comp_quasiMeasurePreserving
          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving
      exact hshift.sub hf_meas
    have hgrad_meas :
        MeasureTheory.AEStronglyMeasurable (fun x : E => grad (E := E) f.1 x) μ :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).aestronglyMeasurable
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne0 h2_netop hshift_meas,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne0 h2_netop hgrad_meas,
      ENNReal.toReal_ofNat]
    -- It suffices to compare the squared integrals.
    have hsq := lintegral_enorm_sub_sq_le (μ := μ) a f
    -- Take the `1/2` power on both sides and simplify.
    have hsq' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ) * ∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      exact ENNReal.rpow_le_rpow hsq (by norm_num)
    -- Rewrite the RHS as `‖a‖ * (...)^(1/2)`.
    have hsq'' :
        (∫⁻ x, ‖f.1 (x + a) - f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (‖a‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∫⁻ x, ‖grad (E := E) f.1 x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      simpa [ENNReal.mul_rpow_of_nonneg, show (0 : ℝ) ≤ (1 / (2 : ℝ)) by nlinarith,
        mul_assoc, mul_left_comm, mul_comm] using hsq'
    have hroot : (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = ‖a‖ₑ := by
      -- `(x^2)^(1/2) = x` in `ℝ≥0∞`, accounting for simp-normalization of `2` and `1/2`.
      have hnat : (‖a‖ₑ ^ (2 : ℕ)) = ‖a‖ₑ ^ (2 : ℝ) := by
        simp
      calc
        (‖a‖ₑ ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = (‖a‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) :=
          congrArg (fun r : ℝ≥0∞ => r ^ ((2 : ℝ)⁻¹)) hnat
        _ = ‖a‖ₑ := by
          have := (ENNReal.rpow_mul ‖a‖ₑ (2 : ℝ) ((2 : ℝ)⁻¹)).symm
          have hmul : (2 : ℝ) * ((2 : ℝ)⁻¹) = (1 : ℝ) := by norm_num
          simpa [hmul, ENNReal.rpow_one] using this
    simpa [hroot, mul_assoc, mul_left_comm, mul_comm] using hsq''
  -- Finish: translate back to the original `L²` norms.
  -- (The final `simp` is safe since we have explicit `eLpNorm` equalities above.)
  simpa [hL2, hGrad] using hCore

/-- Real-norm form of `enorm_translateL2_sub_toL2_le`. -/
lemma norm_translateL2_sub_toL2_le (a : E) (f : ↥(C1c (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
        toL2 (μ := μ) (E := E) f‖ ≤
      ‖a‖ * ‖toL2Grad (μ := μ) (E := E) f‖ := by
  have h := enorm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hA_ne_top :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by
    simp [enorm]
  have hGrad_ne_top :
      (‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by
    simp [enorm]
  have hB_ne_top : (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by
    refine ENNReal.mul_ne_top ?_ hGrad_ne_top
    simp [enorm]
  have h' :
      (‖translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) -
            toL2 (μ := μ) (E := E) f‖ₑ).toReal ≤
        (‖a‖ₑ * ‖toL2Grad (μ := μ) (E := E) f‖ₑ).toReal := by
    exact (ENNReal.toReal_le_toReal hA_ne_top hB_ne_top).2 h
  simpa only [ENNReal.toReal_mul, toReal_enorm] using h'

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source164

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/TranslationEstimateH1.lean; sha256: 752734c4de2da765690db871a1abc4b878f92c07c5bae0cf1086b8d23bf63918 -/
section Source165
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1`

Extend Euclidean `L²` translation estimates from `C¹_c` to the closure-based Euclidean `H¹` space.

## Main results

- `norm_translateL2_sub_h1ToL2_le`: for `u ∈ H¹`, `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂`, where `∇u` is the
  `L²(E)` component in our `H¹ ⊆ L² × L²(E)` model.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceTranslationEstimateH1 :
    MeasurableSpace E := borel E
local instance instBorelSpaceTranslationEstimateH1 :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceTranslationEstimateH1 :
    OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddTranslationEstimateH1 : MeasurableAdd E := by
  infer_instance

variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

/-- `H¹` translation estimate via closure: `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂`. -/
theorem norm_translateL2_sub_h1ToL2_le (a : E) (u : ↥(h1 (μ := μ) (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (h1ToL2 (μ := μ) (E := E) u) -
        h1ToL2 (μ := μ) (E := E) u‖ ≤
      ‖a‖ * ‖h1ToL2Grad (μ := μ) (E := E) u‖ := by
  classical
  -- Work in the ambient space `L² × L²(E)`.
  let V : Type _ := (E →₂[μ] ℝ) × (E →₂[μ] E)
  let S : Set V :=
    {v |
      ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ ≤
        ‖a‖ * ‖v.2‖}
  have hS_closed : IsClosed S := by
    -- Closedness follows from continuity of both sides.
    have hf :
        Continuous fun v : V =>
          ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ := by
      -- `v ↦ v.1` is continuous, translation is continuous,
      -- subtraction is continuous, and norm is continuous.
      have hfst : Continuous fun v : V => v.1 := continuous_fst
      have htr :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 := by
        -- `translateL2` is a continuous linear isometry.
        exact (translateL2 (μ := μ) (F := ℝ) a).toContinuousLinearMap.continuous.comp hfst
      have hsub :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 - v.1 := by
        exact htr.sub hfst
      exact (continuous_norm.comp hsub)
    have hg :
        Continuous fun v : V =>
          ‖a‖ * ‖v.2‖ := by
      have hsnd : Continuous fun v : V => v.2 := continuous_snd
      have hnorm : Continuous fun v : V => ‖v.2‖ := continuous_norm.comp hsnd
      exact (continuous_const.mul hnorm)
    exact isClosed_le hf hg
  have hRange : (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S := by
    rintro v ⟨f, rfl⟩
    -- Reduce to the `C¹_c` estimate.
    simpa [S, graph, toL2Linear, toL2GradLinear] using
      norm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hClosure :
      closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S :=
    closure_minimal hRange hS_closed
  have hu :
      (u : V) ∈ closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) := by
    -- `u ∈ H¹` means `u` is in the topological closure of the range of `graph`.
    have hu0 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := by
      have hu0 : (u : V) ∈ h1 (μ := μ) (E := E) := u.2
      dsimp [h1] at hu0
      exact hu0
    have hu1 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := hu0
    rw [Submodule.topologicalClosure_coe] at hu1
    exact hu1
  have huS : (u : V) ∈ S := hClosure hu
  -- Unpack membership in `S` and rewrite in terms of the bundled maps `h1ToL2` and `h1ToL2Grad`.
  simpa [S, V, h1ToL2, h1ToL2Grad] using huS

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source165

/- Original source: RellichKondrachov/MeasureTheory/Function/LpSpace/Restrict.lean; sha256: 4e742ed3312d7a68091bf610fd9bbe25754d533d2034e7c2a1d4c90496b10fd1 -/
section Source166
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict`

`«L»^p` extension-by-zero maps for restricted measures.

Mathlib provides the equivalence

`MemLp (s.indicator f) p μ ↔ MemLp f p (μ.restrict s)`

(`MeasureTheory.memLp_indicator_iff_restrict`). This file packages the corresponding map on `Lp`
spaces:

`Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ`,

given by extension-by-zero (via `Set.indicator`).

## Main definitions

- `MeasureTheory.Lp.extendByZeroₗ`
- `MeasureTheory.Lp.extendByZeroₗᵢ`
-/

namespace MeasureTheory

open scoped ENNReal

namespace Lp

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {s : Set α} (hs : MeasurableSet s)

/-- Extend an Lp function from a restricted measure by zero outside the set. -/
noncomputable def extendByZeroFun (f : Lp E p (μ.restrict s)) : Lp E p μ :=
  let hf : MemLp (fun x : α => f x) p (μ.restrict s) := Lp.memLp f
  let hfi : MemLp (s.indicator fun x : α => f x) p μ :=
    (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s) (f := fun x : α => f x) hs).2 hf
  hfi.toLp (s.indicator fun x : α => f x)

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
private lemma extendByZeroFun_coe (f : Lp E p (μ.restrict s)) :
    extendByZeroFun (μ := μ) (p := p) (s := s) hs f =ᵐ[μ] s.indicator fun x : α => f x := by
  dsimp [extendByZeroFun]
  exact MemLp.coeFn_toLp _

/-- Extension-by-zero as a linear map `Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ`. -/
noncomputable def extendByZeroₗ : Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ where
  toFun := extendByZeroFun (μ := μ) (p := p) (s := s) hs
  map_add' f g := by
    classical
    -- Prove equality by comparing pointwise representatives.
    refine Lp.ext ?_
    have h_add_restrict :
        (fun x : α => (f + g) x) =ᵐ[μ.restrict s] fun x : α => f x + g x := by
      exact (Lp.coeFn_add (μ := μ.restrict s) f g)
    have h_add_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (f + g) x = f x + g x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_add_restrict
    filter_upwards
      [ extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (f + g)
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs g
      , coeFn_add (extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
          (extendByZeroFun (μ := μ) (p := p) (s := s) hs g)
      , h_add_on
      ] with x hfg hf hg hadd hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hadd' :
          extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using hadd.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = (f + g) x := by simp [Set.indicator_of_mem, hx]
        _ = f x + g x := hsum'
        _ = s.indicator (fun x : α => f x) x + s.indicator (fun x : α => g x) x := by
            simp [Set.indicator_of_mem, hx]
        _ = extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            simp [hf, hg]
        _ = (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
    · have hadd' :
          extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using hadd.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            -- both summands are zero off `s`
            simp [Set.indicator_of_notMem, hx, hf, hg]
        _ = (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
  map_smul' c f := by
    classical
    refine Lp.ext ?_
    have h_smul_restrict :
        (fun x : α => (c • f) x) =ᵐ[μ.restrict s] fun x : α => c • f x := by
      exact (Lp.coeFn_smul (μ := μ.restrict s) c f)
    have h_smul_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (c • f) x = c • f x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_smul_restrict
    filter_upwards
      [ extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (c • f)
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , coeFn_smul c (extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
      , h_smul_on
      ] with x hcf hf hsmul hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hsmul' :
          c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using hsmul.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = (c • f) x := by simp [Set.indicator_of_mem, hx]
        _ = c • f x := hsum'
        _ = c • s.indicator (fun x : α => f x) x := by simp [Set.indicator_of_mem, hx]
        _ = c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by simp [hf]
        _ = (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := hsmul'
    · have hsmul' :
          c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using hsmul.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
            have hf0 :
                extendByZeroFun (μ := μ) (p := p) (s := s) hs f x = 0 := by
              simpa [Set.indicator_of_notMem, hx] using hf
            have hcx :
                (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x = 0 := by
              calc
                (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x =
                    c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by
                      simpa [Pi.smul_apply] using hsmul
                _ = 0 := by simp [hf0]
            simpa using hcx.symm

/-- Extension-by-zero as a linear isometry. -/
noncomputable def extendByZeroₗᵢ : Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ where
  toLinearMap := extendByZeroₗ (μ := μ) (p := p) (s := s) hs
  norm_map' f := by
    classical
    -- Unfold into `MemLp.toLp` and reduce to `eLpNorm_indicator_eq_eLpNorm_restrict`.
    have hfi :
        MemLp (s.indicator fun x : α => f x) p μ :=
      (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs).2 (Lp.memLp f)
    -- Norm in the codomain is the `eLpNorm` of the indicator.
    have hnorm_out :
        ‖extendByZeroₗ (μ := μ) (p := p) (s := s) hs f‖ =
          ENNReal.toReal (eLpNorm (s.indicator fun x : α => f x) p μ) := by
      dsimp [extendByZeroₗ, extendByZeroFun]
      simp [norm_toLp (f := s.indicator (fun x : α => f x)) hfi]
    -- Rewrite the `eLpNorm` of the indicator as a restricted `eLpNorm`.
    have hnorm_restrict :
        eLpNorm (s.indicator fun x : α => f x) p μ =
          eLpNorm (fun x : α => f x) p (μ.restrict s) := by
      simpa using (eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs)
    -- Combine with the definition of the `Lp` norm on the restricted space.
    simp [hnorm_out, hnorm_restrict, norm_def]

lemma extendByZeroₗᵢ_ae_eq (f : Lp E p (μ.restrict s)) :
    ((extendByZeroₗᵢ (μ := μ) (p := p) (s := s) hs) f : α → E) =ᵐ[μ]
      s.indicator fun x : α => f x := by
  -- Unfold to the underlying `extendByZeroFun` and use the defining AE equality.
  simpa [extendByZeroₗᵢ, extendByZeroₗ] using
    (extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f)

lemma extendByZeroₗᵢ_congr (hs₁ hs₂ : MeasurableSet s) :
    extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₁ =
      extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₂ := by
  -- `extendByZeroₗᵢ` is characterized by its pointwise representative.
  refine LinearIsometry.toLinearMap_injective ?_
  refine LinearMap.ext ?_
  intro f
  refine MeasureTheory.Lp.ext (E := E) (p := p) (μ := μ) ?_
  have h₁ :
      ((extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₁) f : α → E) =ᵐ[μ]
        s.indicator fun x : α => f x :=
    extendByZeroₗᵢ_ae_eq (μ := μ) (E := E) (p := p) (s := s) (hs := hs₁) f
  have h₂ :
      ((extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₂) f : α → E) =ᵐ[μ]
        s.indicator fun x : α => f x :=
    extendByZeroₗᵢ_ae_eq (μ := μ) (E := E) (p := p) (s := s) (hs := hs₂) f
  exact h₁.trans h₂.symm

end

end Lp

end MeasureTheory

end Source166

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Smoothing.lean; sha256: ed5a2fddef969b53a73eedebbff39fbd46b8d017f3ee2e12e941729f4a0a0d1a -/
section Source167
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: smoothing setup (Euclidean)

This file provides the basic “extend by zero + smooth by convolution” infrastructure used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main results

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.extendByZeroL2`:
  extend `u : L²(volume.restrict K)` by zero to an element of `L²(volume)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothL2`:
  a smoothing operator obtained by convolution with a compactly supported continuous kernel `ψ`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceSmoothing : MeasurableSpace E := borel E
local instance instBorelSpaceSmoothing : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceSmoothing : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddSmoothing : MeasurableAdd E := by
  infer_instance

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private lemma tsupport_indicator_subset_closure (s : Set E) (f : E → ℝ) :
    tsupport (s.indicator f) ⊆ closure s := by
  -- `Function.support (s.indicator f) ⊆ s`, hence the topological support is contained in
  -- `closure s`.
  simpa [tsupport] using closure_mono (Set.support_indicator_subset (s := s) (f := f))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private lemma hasCompactSupport_indicator_of_isCompact (s : Set E) (hs : IsCompact s) (f : E → ℝ) :
    HasCompactSupport (s.indicator f) := by
  have hs_closed : IsClosed s := hs.isClosed
  -- `tsupport (s.indicator f)` is closed and contained in the compact set `s`.
  refine hs.of_isClosed_subset (isClosed_tsupport _) ?_
  have : tsupport (s.indicator f) ⊆ closure s := tsupport_indicator_subset_closure (E := E) s f
  simpa [hs_closed.closure_eq] using this

end

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- `volume` is the canonical Haar measure on finite-dimensional real vector spaces.
/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceSmoothing1 : MeasurableSpace E := borel E
local instance instBorelSpaceSmoothing1 : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceSmoothing1 : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddSmoothing1 : MeasurableAdd E := by
  infer_instance

variable {K : Set E}

/-- Extend an `L²` function on `K` by zero to a pointwise function on the ambient space. -/
def extendByZeroFun (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : E → ℝ :=
  K.indicator fun x : E => u x

lemma hasCompactSupport_extendByZeroFun (hK : IsCompact K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    HasCompactSupport (extendByZeroFun (K := K) u) := by
  classical
  -- The indicator is pointwise supported in `K`.
  simpa [extendByZeroFun] using
    (hasCompactSupport_indicator_of_isCompact (E := E) (s := K) hK (f := fun x => u x))

/-- `extendByZeroFun` packaged as an element of `L²(volume)`. -/
noncomputable def extendByZeroL2 (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (E →₂[(volume : Measure E)] ℝ) := by
  classical
  have hu : MeasureTheory.MemLp (fun x : E => u x) (2 : ℝ≥0∞) (volume.restrict K) :=
    MeasureTheory.Lp.memLp u
  have hm :
      MeasureTheory.MemLp (extendByZeroFun (K := K) u) (2 : ℝ≥0∞) (volume : Measure E) := by
    simpa [extendByZeroFun] using
      (MeasureTheory.memLp_indicator_iff_restrict (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
          (s := K) (f := fun x : E => u x) hKm).2 hu
  exact hm.toLp (extendByZeroFun (K := K) u)

lemma extendByZeroL2_ae_eq (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (extendByZeroL2 (E := E) (K := K) hKm u : E → ℝ) =ᵐ[(volume : Measure E)]
      extendByZeroFun (E := E) (K := K) u := by
  classical
  simp [extendByZeroL2, MeasureTheory.MemLp.coeFn_toLp]

lemma extendByZeroL2_eq_extendByZeroₗᵢ (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    extendByZeroL2 (E := E) (K := K) hKm u =
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm) u := by
  classical
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  refine MeasureTheory.Lp.ext ?_
  have h1 :
      (extendByZeroL2 (E := E) (K := K) hKm u : E → ℝ) =ᵐ[(volume : Measure E)]
        extendByZeroFun (E := E) (K := K) u :=
    extendByZeroL2_ae_eq (E := E) (K := K) hKm u
  have h2 :
      ((MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm) u : E → ℝ) =ᵐ[(volume : Measure E)]
        extendByZeroFun (E := E) (K := K) u := by
    exact
      (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq (μ := (volume : Measure E)) (E := ℝ)
        (p := (2 : ℝ≥0∞)) (s := K) hKm u)
  exact h1.trans h2.symm

lemma norm_extendByZeroL2 (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖extendByZeroL2 (E := E) (K := K) hKm u‖ = ‖u‖ := by
  classical
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  calc
    ‖extendByZeroL2 (E := E) (K := K) hKm u‖ =
        ‖(MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
          (s := K) hKm) u‖ := by
          simp [extendByZeroL2_eq_extendByZeroₗᵢ (E := E) (K := K) hKm u]
    _ = ‖u‖ :=
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm).norm_map u
variable (ψ : E → ℝ)

/-- Smoothing by convolution with a fixed kernel `ψ`, applied to the zero-extension from `K`. -/
def smoothFun (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : E → ℝ :=
  (extendByZeroFun (K := K) u) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ

lemma continuous_smoothFun
    (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    Continuous (smoothFun (K := K) ψ u) := by
  -- `extendByZeroFun u` is `L²`, hence locally integrable; convolution with a compactly supported
  -- continuous kernel is continuous.
  have hf_memLp :
      MeasureTheory.MemLp (extendByZeroFun (K := K) u)
        (2 : ℝ≥0∞) (volume : Measure E) := by
    have hu : MeasureTheory.MemLp (fun x : E => u x) (2 : ℝ≥0∞) (volume.restrict K) :=
      MeasureTheory.Lp.memLp u
    simpa [extendByZeroFun] using
      (MeasureTheory.memLp_indicator_iff_restrict (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
          (s := K) (f := fun x : E => u x) hKm).2 hu
  have hf_loc :
      MeasureTheory.LocallyIntegrable (extendByZeroFun (K := K) u)
        (volume : Measure E) := by
    have h12 : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
    exact hf_memLp.locallyIntegrable h12
  simpa [smoothFun] using
    (hψcs.continuous_convolution_right
      («L» := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure E)) hf_loc hψc)

lemma hasCompactSupport_smoothFun (hK : IsCompact K) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    HasCompactSupport (smoothFun (K := K) ψ u) := by
  have hf : HasCompactSupport (extendByZeroFun (K := K) u) :=
    hasCompactSupport_extendByZeroFun (K := K) hK u
  simpa [smoothFun] using
    (hf.convolution («L» := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure E)) hψcs)

lemma support_smoothFun_subset_add_tsupport
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    Function.support (smoothFun (E := E) (K := K) ψ u) ⊆ K + tsupport ψ := by
  classical
  have hsupp :
      Function.support (smoothFun (E := E) (K := K) ψ u) ⊆
        Function.support (extendByZeroFun (E := E) (K := K) u) + Function.support ψ := by
    simpa [smoothFun] using
      (support_convolution_subset («L» := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure E))
        (f := extendByZeroFun (E := E) (K := K) u) (g := ψ))
  have h1 : Function.support (extendByZeroFun (E := E) (K := K) u) ⊆ K := by
    simp [extendByZeroFun]
  have h2 : Function.support ψ ⊆ tsupport ψ := by
    simpa [tsupport] using (subset_closure : Function.support ψ ⊆ closure (Function.support ψ))
  exact hsupp.trans (add_subset_add h1 h2)

/-- `smoothFun` packaged as an element of `L²(volume)`. -/
noncomputable def smoothL2 (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : (E →₂[(volume : Measure E)] ℝ) :=
  let hs : HasCompactSupport (smoothFun (K := K) ψ u) :=
    hasCompactSupport_smoothFun (K := K) ψ hK hψcs u
  let hm : MeasureTheory.MemLp (smoothFun (K := K) ψ u) (2 : ℝ≥0∞) (volume : Measure E) := by
    have hc : Continuous (smoothFun (K := K) ψ u) := continuous_smoothFun (K := K) ψ hKm hψc hψcs u
    exact hc.memLp_of_hasCompactSupport (μ := (volume : Measure E)) hs
  hm.toLp (smoothFun (K := K) ψ u)

lemma smoothL2_ae_eq (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u : E → ℝ) =ᵐ[(volume : Measure E)]
      smoothFun (E := E) (K := K) ψ u := by
  classical
  simp [smoothL2, MeasureTheory.MemLp.coeFn_toLp]
end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source167

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Approximation.lean; sha256: fb29e974cc552663b48fc95cc0c63fb87427be78fef26a24c762563607554ee2 -/
section Source168
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: approximation-by-translation bounds (Euclidean)

This file will prove the key inequality used in the Fréchet–Kolmogorov approach: smoothing by a
probability kernel controls the `L²` error by the translation modulus.

## Main results (planned)

The principal statement will control `‖smoothL2 ψ u - extendByZeroL2 u‖₂` by an average (or sup) of
`‖translateL2 t (extendByZeroL2 u) - extendByZeroL2 u‖₂` over `t` in the support of `ψ`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceApproximation : MeasurableSpace E := borel E
local instance instBorelSpaceApproximation : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceApproximation : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddApproximation : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegApproximation : MeasurableNeg E := by
  infer_instance

variable {K : Set E} (hK : IsCompact K) (hKm : MeasurableSet K)
variable (ψ : E → ℝ)

/-- The measure with density `ψ` with respect to Lebesgue measure. This will be a probability
measure once `ψ ≥ 0` and `∫ ψ = 1`. -/
noncomputable def kernelMeasure : Measure E :=
  (volume : Measure E).withDensity fun x => ENNReal.ofReal (ψ x)

lemma kernelMeasure_univ (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) :
    kernelMeasure (E := E) ψ Set.univ = 1 := by
  have hψi : MeasureTheory.Integrable ψ (volume : Measure E) :=
    Continuous.integrable_of_hasCompactSupport (μ := (volume : Measure E)) hψc hψcs
  have hψae : (MeasureTheory.ae (volume : Measure E)).EventuallyLE 0 ψ :=
    Filter.Eventually.of_forall hψ0
  have hlin :
      (∫⁻ x, ENNReal.ofReal (ψ x) ∂(volume : Measure E)) =
        ENNReal.ofReal (∫ x, ψ x ∂(volume : Measure E)) := by
    symm
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hψi hψae
  -- `withDensity` on `univ` is the `lintegral` of the density.
  have hwd :
      kernelMeasure (E := E) ψ Set.univ =
        ∫⁻ x, ENNReal.ofReal (ψ x) ∂(volume : Measure E) := by
    simp [kernelMeasure, MeasureTheory.withDensity_apply, MeasurableSet.univ]
  -- Conclude using `∫ ψ = 1`.
  simpa [hψint] using (hwd.trans hlin)

/-- The kernel measure `kernelMeasure ψ` is a probability measure when `ψ` is a continuous,
compactly supported, nonnegative density integrating to `1`. -/
lemma isProbabilityMeasure_kernelMeasure
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) :
    MeasureTheory.IsProbabilityMeasure (kernelMeasure (E := E) ψ) :=
  ⟨kernelMeasure_univ (E := E) (ψ := ψ) hψc hψcs hψ0 hψint⟩

lemma integral_kernelMeasure_eq_integral_smul (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (g : E → ℝ) :
    (∫ x, g x ∂kernelMeasure (E := E) ψ) =
      ∫ x, (ψ x) • (g x) ∂(volume : Measure E) := by
  have hmeas : Measurable fun x => ENNReal.ofReal (ψ x) :=
    (hψc.measurable.ennreal_ofReal : Measurable fun x => ENNReal.ofReal (ψ x))
  have htop :
      (MeasureTheory.ae (volume : Measure E)).Eventually
        (fun x => ENNReal.ofReal (ψ x) < (⊤ : ℝ≥0∞)) :=
    Filter.Eventually.of_forall (fun _ => by simp)
  have hwd :=
    (integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure E))
      (f := fun x => ENNReal.ofReal (ψ x)) hmeas htop g)
  have hwd' :
      (∫ x, g x ∂kernelMeasure (E := E) ψ) =
        ∫ x, (ENNReal.ofReal (ψ x)).toReal • (g x) ∂(volume : Measure E) := by
    simpa [kernelMeasure] using hwd
  -- Simplify `toReal (ofReal _)` using `ψ ≥ 0`.
  refine hwd'.trans ?_
  refine integral_congr_ae ?_
  refine ae_of_all _ (fun x => ?_)
  have hx : (ENNReal.ofReal (ψ x)).toReal = ψ x :=
    ENNReal.toReal_ofReal (hψ0 x)
  -- After rewriting `toReal (ofReal _)`, both sides are definitional.
  simp [hx]

lemma integral_kernelMeasure_eq_integral_mul (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (g : E → ℝ) :
    (∫ x, g x ∂kernelMeasure (E := E) ψ) =
      ∫ x, (ψ x) * (g x) ∂(volume : Measure E) := by
  simpa [smul_eq_mul] using integral_kernelMeasure_eq_integral_smul (E := E) (ψ := ψ) hψc hψ0 g

lemma smoothFun_eq_integral_kernelMeasure (hψc : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    smoothFun (E := E) (K := K) ψ u x =
      ∫ t, extendByZeroFun (E := E) (K := K) u (x - t) ∂kernelMeasure (E := E) ψ := by
  have hconv :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (extendByZeroFun (E := E) (K := K) u) (x - t) • (ψ t) ∂(volume : Measure E) := by
    simp [smoothFun, convolution_lsmul_swap]
  have hconv' :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (ψ t) * extendByZeroFun (E := E) (K := K) u (x - t) ∂(volume : Measure E) := by
    refine hconv.trans ?_
    refine integral_congr_ae ?_
    refine ae_of_all _ (fun t => ?_)
    -- In `ℝ`, scalar multiplication is multiplication, so we can commute the factors.
    change
      extendByZeroFun (E := E) (K := K) u (x - t) • ψ t =
        ψ t * extendByZeroFun (E := E) (K := K) u (x - t)
    rw [smul_eq_mul]
    simp [mul_comm]
  -- Rewrite the convolution integral as an integral against the density measure.
  have hwd :
      (∫ t, extendByZeroFun (E := E) (K := K) u (x - t) ∂kernelMeasure (E := E) ψ) =
        ∫ t, (ψ t) * extendByZeroFun (E := E) (K := K) u (x - t) ∂(volume : Measure E) := by
    exact integral_kernelMeasure_eq_integral_mul (E := E) (ψ := ψ) hψc hψ0
      (g := fun t => extendByZeroFun (E := E) (K := K) u (x - t))
  exact hconv'.trans hwd.symm

lemma sq_integral_le_integral_sq_of_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [MeasureTheory.IsProbabilityMeasure μ] (f : α → ℝ)
    (hf : MeasureTheory.MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, (f x) ^ 2 ∂μ := by
  have hvar := ProbabilityTheory.variance_nonneg (X := f) μ
  have hvar' :
      0 ≤ (∫ x, (f x) ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
    simpa [ProbabilityTheory.variance_eq_sub (μ := μ) hf] using hvar
  linarith

private lemma norm_sq_eq_integral_sq (v : (E →₂[(volume : Measure E)] ℝ)) :
    ‖v‖ ^ 2 = ∫ x, (v x) ^ 2 ∂(volume : Measure E) := by
  have hn : ‖v‖ ^ 2 = RCLike.re (inner ℝ v v) :=
    norm_sq_eq_re_inner (𝕜 := ℝ) v
  -- Unfold the `L²` inner product as an integral; for `ℝ`, `re` is the identity.
  rw [hn]
  -- `L²` inner product is an integral of pointwise inner products.
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ) (μ := (volume : Measure E)) v v]
  -- For `ℝ`, `RCLike.re` is the identity and `inner` simplifies to a square.
  simp [pow_two]

lemma norm_sq_translateL2_sub_extendByZeroL2_eq_integral_sq (t : E)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖(translateL2 (μ := (volume : Measure E)) (-t))
        (extendByZeroL2 (E := E) (K := K) hKm u)
        - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 =
      ∫ x,
        (extendByZeroFun (E := E) (K := K) u (x - t) - extendByZeroFun (E := E) (K := K) u x) ^ 2
          ∂(volume : Measure E) := by
  classical
  let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  have hF_ae : (F : E → ℝ) =ᵐ[(volume : Measure E)] f :=
    extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
  -- Translate AE equality along `x ↦ x - t`.
  have hF_shift :
      (fun x : E => (F : E → ℝ) (x - t)) =ᵐ[(volume : Measure E)] fun x => f (x - t) := by
    have hmp :
        MeasureTheory.MeasurePreserving (fun x : E => x - t)
          (volume : Measure E) (volume : Measure E) :=
      MeasureTheory.measurePreserving_sub_right (μ := (volume : Measure E)) t
    exact (hmp.quasiMeasurePreserving.ae_eq_comp hF_ae)
  -- TranslateL2 gives `F(x - t)` a.e.
  have htrans :
      ((translateL2 (μ := (volume : Measure E)) (-t)) F : E → ℝ) =ᵐ[(volume : Measure E)]
        fun x => (F : E → ℝ) (x - t) := by
    simpa [sub_eq_add_neg] using (translateL2_ae_eq (μ := (volume : Measure E)) (-t) F)
  have htrans' :
      ((translateL2 (μ := (volume : Measure E)) (-t)) F : E → ℝ) =ᵐ[(volume : Measure E)]
        fun x => f (x - t) := by
    exact htrans.trans hF_shift
  have hdiff :
      (fun x => ((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x) =ᵐ[(volume : Measure E)]
        fun x => f (x - t) - f x := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub ((translateL2 (μ := (volume : Measure E)) (-t)) F) F,
      htrans', hF_ae] with x hxsub hx1 hx2
    -- `Lp.coeFn_sub` gives the pointwise relation between coercions of `Lp` subtraction.
    have hxsub' :
        ((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x =
          ((translateL2 (μ := (volume : Measure E)) (-t)) F) x - F x := by
      simpa using hxsub
    -- Rewrite to the desired expression using the two pointwise identities.
    rw [hxsub', hx1, hx2]
  have hcalc :
      ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 =
        ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E) := by
    have h1 :=
      norm_sq_eq_integral_sq (E := E) (v := ((translateL2 (μ := (volume : Measure E)) (-t)) F - F))
    have h2 :
        ∫ x, (((translateL2 (μ := (volume : Measure E)) (-t)) F - F) x) ^ 2
            ∂(volume : Measure E) =
          ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E) := by
      refine MeasureTheory.integral_congr_ae ?_
      exact hdiff.pow_const 2
    exact h1.trans h2
  simpa [F, f] using hcalc

private lemma kernelMeasure_le_smul_volume (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ kernelMeasure (E := E) ψ ≤ c • (volume : Measure E) := by
  classical
  obtain ⟨C, hC⟩ := hψcs.exists_bound_of_continuous hψc
  refine ⟨ENNReal.ofReal C, by simp, ?_⟩
  refine (Measure.le_iff).2 ?_
  intro s hs
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (ψ 0)) (hC 0)
  have hψle : ∀ x, ENNReal.ofReal (ψ x) ≤ ENNReal.ofReal C := by
    intro x
    have hx : ψ x ≤ C := by
      have hx' : ‖ψ x‖ ≤ C := hC x
      -- `ψ ≥ 0`, so `‖ψ x‖ = ψ x`.
      simpa [Real.norm_eq_abs, abs_of_nonneg (hψ0 x)] using hx'
    exact ENNReal.ofReal_le_ofReal hx
  -- Unfold `withDensity` and bound the density by the constant `ENNReal.ofReal C`.
  simp only [kernelMeasure, MeasureTheory.withDensity_apply, hs]
  have hle :
      (∫⁻ x in s, ENNReal.ofReal (ψ x) ∂(volume : Measure E)) ≤
        ∫⁻ x in s, ENNReal.ofReal C ∂(volume : Measure E) := by
    refine MeasureTheory.lintegral_mono ?_
    intro x
    exact hψle x
  refine hle.trans ?_
  simp

lemma smoothFun_sub_extendByZeroFun_sq_le_integral_sq
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    (smoothFun (E := E) (K := K) ψ u x - extendByZeroFun (E := E) (K := K) u x) ^ 2 ≤
      ∫ t,
        (extendByZeroFun (E := E) (K := K) u (x - t) - extendByZeroFun (E := E) (K := K) u x) ^ 2
          ∂kernelMeasure (E := E) ψ := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  have : MeasureTheory.IsProbabilityMeasure μ :=
    isProbabilityMeasure_kernelMeasure (E := E) (ψ := ψ) hψc hψcs hψ0 hψint
  have : MeasureTheory.IsFiniteMeasure μ := by infer_instance
  rcases kernelMeasure_le_smul_volume (E := E) (ψ := ψ) hψc hψcs hψ0 with ⟨c, hc_top, hμle⟩
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  have hf_vol : MeasureTheory.MemLp f (2 : ℝ≥0∞) (volume : Measure E) := by
    -- Use the `L²` packaging of `extendByZeroFun` and the AE bridge.
    let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
    have hF : MeasureTheory.MemLp (fun x : E => (F : E → ℝ) x) (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp F
    have hF_ae : (fun x : E => (F : E → ℝ) x) =ᵐ[(volume : Measure E)] f :=
      extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
    exact (MeasureTheory.memLp_congr_ae hF_ae).1 hF
  have hmp :
      MeasureTheory.MeasurePreserving (fun t : E => x - t)
        (volume : Measure E) (volume : Measure E) := by
    -- `t ↦ x - t = (-t) + x` is measure-preserving for Lebesgue (Haar) measure.
    have hneg :
        MeasureTheory.MeasurePreserving (Neg.neg : E → E)
          (volume : Measure E) (volume : Measure E) :=
      (volume : Measure E).measurePreserving_neg
    have hadd :
        MeasureTheory.MeasurePreserving (fun y : E => y + x)
          (volume : Measure E) (volume : Measure E) :=
      MeasureTheory.measurePreserving_add_right
        (μ := (volume : Measure E)) x
    have hcomp : ((fun y : E => y + x) ∘ fun t : E => -t) = fun t : E => x - t := by
      funext t
      simp [sub_eq_add_neg, add_comm]
    have := hadd.comp hneg
    rwa [hcomp] at this
  have hf_shift_vol :
      MeasureTheory.MemLp (fun t : E => f (x - t))
        (2 : ℝ≥0∞) (volume : Measure E) :=
    hf_vol.comp_measurePreserving hmp
  have hf_shift :
      MeasureTheory.MemLp (fun t : E => f (x - t))
        (2 : ℝ≥0∞) μ := by
    exact MeasureTheory.MemLp.of_measure_le_smul
      (μ := (volume : Measure E)) (μ' := μ) (c := c)
      hc_top hμle hf_shift_vol
  have hf_const : MeasureTheory.MemLp (fun _ : E => f x) (2 : ℝ≥0∞) μ :=
    MeasureTheory.memLp_const (μ := μ) (c := f x)
  have hg : MeasureTheory.MemLp (fun t : E => f (x - t) - f x) (2 : ℝ≥0∞) μ :=
    hf_shift.sub hf_const
  have hsmooth :
      smoothFun (E := E) (K := K) ψ u x = ∫ t, f (x - t) ∂μ := by
    simpa [μ, f] using smoothFun_eq_integral_kernelMeasure (E := E) (K := K) (ψ := ψ) hψc hψ0 u x
  have hdiff :
      smoothFun (E := E) (K := K) ψ u x - f x = ∫ t, (f (x - t) - f x) ∂μ := by
    have hconst : (∫ _t : E, f x ∂μ) = f x := by
      simp [MeasureTheory.integral_const]
    have hint : MeasureTheory.Integrable (fun t : E => f (x - t)) μ :=
      hf_shift.integrable (by norm_num)
    have :
        (∫ t, f (x - t) ∂μ) - (∫ _t : E, f x ∂μ) =
          ∫ t, (f (x - t) - f x) ∂μ := by
      simpa using (MeasureTheory.integral_sub hint (MeasureTheory.integrable_const (f x))).symm
    simpa [hsmooth, hconst] using this
  -- Apply Jensen/variance inequality to `t ↦ f(x - t) - f(x)`.
  have hJ :=
    sq_integral_le_integral_sq_of_isProbabilityMeasure
      (μ := μ) (f := fun t : E => f (x - t) - f x) hg
  simpa [hdiff, μ, f] using hJ

lemma norm_sq_smoothL2_sub_extendByZeroL2_le_integral_norm_sq_translateL2_sub_extendByZeroL2
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 ≤
      ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) (extendByZeroL2 (E := E) (K := K) hKm u)
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
          ∂kernelMeasure (E := E) ψ := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  have : MeasureTheory.IsProbabilityMeasure μ :=
    isProbabilityMeasure_kernelMeasure (E := E) (ψ := ψ) hψc hψcs hψ0 hψint
  have : MeasureTheory.IsFiniteMeasure μ := by infer_instance
  have : MeasureTheory.SFinite μ := by infer_instance
  let F : (E →₂[(volume : Measure E)] ℝ) := extendByZeroL2 (E := E) (K := K) hKm u
  let f : E → ℝ := extendByZeroFun (E := E) (K := K) u
  let S : (E →₂[(volume : Measure E)] ℝ) := smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
  have hS_ae :
      (S : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
    smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
  have hF_ae : (F : E → ℝ) =ᵐ[(volume : Measure E)] f :=
    extendByZeroL2_ae_eq (E := E) (K := K) (hKm := hKm) u
  have hSF_ae :
      (fun x : E => (S - F) x) =ᵐ[(volume : Measure E)] fun x =>
        smoothFun (E := E) (K := K) ψ u x - f x := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub S F, hS_ae, hF_ae] with x hxsub hxS hxF
    have hxsub' : (S - F) x = S x - F x := by
      simpa using hxsub
    rw [hxsub', hxS, hxF]
  have hnorm_sq :
      ‖S - F‖ ^ 2 =
        ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) := by
    have h1 := norm_sq_eq_integral_sq (E := E) (v := (S - F))
    have h2 :
        (∫ x, ((S - F) x) ^ 2 ∂(volume : Measure E)) =
          ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) := by
      refine MeasureTheory.integral_congr_ae ?_
      exact hSF_ae.pow_const 2
    exact h1.trans h2
  have hLHS_int :
      MeasureTheory.Integrable (fun x : E => (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2)
        (volume : Measure E) := by
    have hv_mem : MeasureTheory.MemLp (fun x : E => (S - F : E →₂[(volume : Measure E)] ℝ) x)
        (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp (S - F)
    have hv_int :
        MeasureTheory.Integrable
          (fun x : E => ‖(S - F : E →₂[(volume : Measure E)] ℝ) x‖ ^ (2 : ℕ))
          (volume : Measure E) :=
      MeasureTheory.MemLp.integrable_norm_pow (μ := (volume : Measure E)) (f := fun x =>
        (S - F : E →₂[(volume : Measure E)] ℝ) x) (p := 2) hv_mem (by decide)
    -- Replace `‖·‖^2` by `(_)^2` in `ℝ`, then transport along the AE equality.
    have hv_sq :
        MeasureTheory.Integrable (fun x : E => ((S - F : E →₂[(volume : Measure E)] ℝ) x) ^ 2)
          (volume : Measure E) := by
      simpa [Real.norm_eq_abs, sq_abs] using hv_int
    exact hv_sq.congr (hSF_ae.pow_const 2)
  -- Show integrability on the product measure, so we can use Fubini/Tonelli for the translation
  -- error.
  let h : E × E → ℝ := fun z => (f (z.1 - z.2) - f z.1) ^ 2
  have hf_mem : MeasureTheory.MemLp f (2 : ℝ≥0∞) (volume : Measure E) := by
    -- Again use the AE bridge from the `L²` packaging.
    have hF : MeasureTheory.MemLp (fun x : E => (F : E → ℝ) x) (2 : ℝ≥0∞) (volume : Measure E) :=
      MeasureTheory.Lp.memLp F
    exact (MeasureTheory.memLp_congr_ae hF_ae).1 hF
  have hf_sq_int : MeasureTheory.Integrable (fun x : E => (f x) ^ 2) (volume : Measure E) := by
    have hf_int :
        MeasureTheory.Integrable (fun x : E => ‖f x‖ ^ (2 : ℕ)) (volume : Measure E) :=
      MeasureTheory.MemLp.integrable_norm_pow
        (μ := (volume : Measure E)) (f := f) (p := 2)
        hf_mem (by decide)
    simpa [Real.norm_eq_abs, sq_abs] using hf_int
  have hfst_map :
      MeasureTheory.Integrable (fun x : E => (f x) ^ 2)
        (Measure.map Prod.fst ((volume : Measure E).prod μ)) := by
    simpa [Measure.map_fst_prod] using hf_sq_int
  have hf_fst_sq_prod :
      MeasureTheory.Integrable (fun z : E × E => (f z.1) ^ 2) ((volume : Measure E).prod μ) :=
    (MeasureTheory.Integrable.comp_measurable (μ := (volume : Measure E).prod μ) (f := Prod.fst)
      (g := fun x : E => (f x) ^ 2) hfst_map measurable_fst)
  have hsub :
      MeasureTheory.MeasurePreserving
        (fun z : E × E => (z.1 - z.2, z.2))
        ((volume : Measure E).prod μ)
        ((volume : Measure E).prod μ) :=
    MeasureTheory.measurePreserving_sub_prod (μ := (volume : Measure E)) (ν := μ)
  have hf_shift_sq_prod :
      MeasureTheory.Integrable (fun z : E × E => (f (z.1 - z.2)) ^ 2)
        ((volume : Measure E).prod μ) := by
    have := (hsub.integrable_comp hf_fst_sq_prod.aestronglyMeasurable).2 hf_fst_sq_prod
    exact this
  have hdom :
      MeasureTheory.Integrable (fun z : E × E => (2 : ℝ) * ((f (z.1 - z.2)) ^ 2 + (f z.1) ^ 2))
        ((volume : Measure E).prod μ) := by
    simpa [mul_add, two_mul] using (hf_shift_sq_prod.add hf_fst_sq_prod).const_mul (2 : ℝ)
  have hf_fst_aesm :
      MeasureTheory.AEStronglyMeasurable (fun z : E × E => f z.1)
        ((volume : Measure E).prod μ) := by
    have hf_map :
        MeasureTheory.AEStronglyMeasurable f
          (Measure.map Prod.fst
            ((volume : Measure E).prod μ)) := by
      simpa [Measure.map_fst_prod] using hf_mem.aestronglyMeasurable
    exact MeasureTheory.AEStronglyMeasurable.comp_measurable
      (μ := (volume : Measure E).prod μ) (f := Prod.fst)
      (g := f) hf_map measurable_fst
  have hf_shift_aesm :
      MeasureTheory.AEStronglyMeasurable
        (fun z : E × E => f (z.1 - z.2))
        ((volume : Measure E).prod μ) := by
    have := MeasureTheory.AEStronglyMeasurable.comp_measurePreserving (g := fun z : E × E => f z.1)
      hf_fst_aesm hsub
    exact this
  have h_aesm :
      MeasureTheory.AEStronglyMeasurable h ((volume : Measure E).prod μ) := by
    -- Build up AE-strong measurability from the two components.
    have hsub' :
        MeasureTheory.AEStronglyMeasurable (fun z : E × E => f (z.1 - z.2) - f z.1)
          ((volume : Measure E).prod μ) :=
      hf_shift_aesm.sub hf_fst_aesm
    exact (hsub'.pow 2)
  have hint_h : MeasureTheory.Integrable h ((volume : Measure E).prod μ) := by
    refine MeasureTheory.Integrable.mono (μ := (volume : Measure E).prod μ) hdom h_aesm ?_
    refine Filter.Eventually.of_forall ?_
    rintro ⟨x, t⟩
    have hineq :
        (f (x - t) - f x) ^ 2 ≤ (2 : ℝ) * ((f (x - t)) ^ 2 + (f x) ^ 2) := by
      -- `(a - b)^2 ≤ 2(a^2 + b^2)` as a special case of `add_sq_le`.
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (add_sq_le (a := f (x - t)) (b := -f x))
    have hnonneg : 0 ≤ (f (x - t) - f x) ^ 2 := by nlinarith
    have hsum_nonneg : 0 ≤ (f (x - t)) ^ 2 + (f x) ^ 2 := by nlinarith
    simpa [h, Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_mul,
      abs_of_nonneg (show 0 ≤ (2 : ℝ) by norm_num),
      abs_of_nonneg hsum_nonneg] using hineq
  have hRHS_int :
      MeasureTheory.Integrable
        (fun x : E => ∫ t, (f (x - t) - f x) ^ 2 ∂μ) (volume : Measure E) := by
    simpa [h] using hint_h.integral_prod_left
  have hpoint :
      (fun x : E => (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2)
        ≤ᶠ[MeasureTheory.ae (volume : Measure E)]
        fun x : E => ∫ t, (f (x - t) - f x) ^ 2 ∂μ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simpa [f, μ] using
      (smoothFun_sub_extendByZeroFun_sq_le_integral_sq (E := E) (K := K) (ψ := ψ)
        hψc hψcs hψ0 hψint hKm u x)
  have hinterm :
      ∫ x, (smoothFun (E := E) (K := K) ψ u x - f x) ^ 2 ∂(volume : Measure E) ≤
        ∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E) :=
    MeasureTheory.integral_mono_ae hLHS_int hRHS_int hpoint
  -- Swap the order of integration on the right-hand side.
  have hswap :
      (∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E)) =
        ∫ t, (∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) ∂μ := by
    simpa using (MeasureTheory.integral_integral_swap (μ := (volume : Measure E)) (ν := μ)
      (f := fun x t => (f (x - t) - f x) ^ 2) hint_h)
  -- Identify the inner `x` integral with the `L²` translation norm squared.
  have hinner :
      (fun t : E => ∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) =
        fun t : E =>
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 := by
    funext t
    -- Use the previously proved integral identity.
    simpa [F, f] using
      (norm_sq_translateL2_sub_extendByZeroL2_eq_integral_sq
        (E := E) (K := K) (hKm := hKm) t u).symm
  have hRHS_rewrite :
      (∫ t, (∫ x, (f (x - t) - f x) ^ 2 ∂(volume : Measure E)) ∂μ) =
        ∫ t, ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ∂μ := by
    simp [hinner]
  -- Assemble everything.
  have hmain :
      ‖S - F‖ ^ 2 ≤
        ∫ t, ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ∂μ := by
    -- Convert `‖S-F‖²` to an `x`-integral and apply the integral inequality chain.
    have : ‖S - F‖ ^ 2 ≤ ∫ x, (∫ t, (f (x - t) - f x) ^ 2 ∂μ) ∂(volume : Measure E) := by
      simpa [hnorm_sq] using hinterm
    exact this.trans_eq (hswap.trans hRHS_rewrite)
  -- Restore the original statement.
  simpa [S, F, μ] using hmain

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source168

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Compactness.lean; sha256: 161eb7a47ef0799f196371a8840bffb44e92cd3b751ec2b5dceb2e09c1ca3501 -/
section Source169
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: compact smoothing operator (Euclidean)

This file proves the compactness of the fixed-kernel smoothing operator used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main results

- `Kψ`: the compact set `K + tsupport ψ` controlling supports of smoothed functions.
- `smoothBCF`: `smoothFun` packaged as a `BoundedContinuousFunction` on `Kψ`.
- `uniformContinuous_ψ`: `UniformContinuous ψ` from `Continuous ψ` + `HasCompactSupport ψ`.

The Arzelà–Ascoli compactness statement for `smoothBCF` lives in
`RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.ArzelaAscoli`.

This is tracked under Beads `lean-103.5.2.26.5.3.2.2.1`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEL2CompactnessCompactness : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessCompactness : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessCompactness : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddEL2CompactnessCompactness : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegEL2CompactnessCompactness : MeasurableNeg E := by
  infer_instance

variable {K : Set E}
variable {ψ : E → ℝ}

/-- The natural compact codomain for smoothing on `K` by a compactly supported kernel `ψ`. -/
def Kψ : Set E :=
  K + tsupport ψ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma isCompact_Kψ (hK : IsCompact K) (hψcs : HasCompactSupport ψ) :
    IsCompact (Kψ (K := K) (ψ := ψ)) :=
  IsCompact.add hK hψcs.isCompact

/-- Restrict the smoothed function to its compact domain as a continuous map. -/
def smoothOn (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    C(↥(Kψ (K := K) (ψ := ψ)), ℝ) where
  toFun x := smoothFun (E := E) (K := K) ψ u x
  continuous_toFun := by
    have : Continuous (smoothFun (E := E) (K := K) ψ u) :=
      continuous_smoothFun (E := E) (K := K) (ψ := ψ) (hKm := hKm) hψc hψcs u
    exact this.comp continuous_subtype_val

/-- `smoothFun` packaged as a `BoundedContinuousFunction` on the compact set `K + tsupport ψ`. -/
def smoothBCF (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ :=
  letI : CompactSpace ↥(Kψ (K := K) (ψ := ψ)) :=
    isCompact_iff_compactSpace.1 (isCompact_Kψ (K := K) (ψ := ψ) hK hψcs)
  BoundedContinuousFunction.mkOfCompact (smoothOn (E := E) (K := K) (ψ := ψ) hKm hψc hψcs u)

@[simp] lemma smoothBCF_apply (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
    (x : ↥(Kψ (K := K) (ψ := ψ))) :
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x =
      smoothFun (E := E) (K := K) ψ u x := by
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma uniformContinuous_ψ (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) :
    UniformContinuous ψ := by
  classical
  -- `HasCompactSupport` implies `ψ = 0` outside a compact set, hence `ψ → 0` along `cocompact`.
  refine
    Continuous.uniformContinuous_of_tendsto_cocompact (f := ψ) (x := (0 : ℝ)) hψc ?_
  -- Show `ψ → 0` along `cocompact` using the `ε`-ball characterization.
  refine (Metric.tendsto_nhds.2 ?_)
  intro ε hε
  refine Filter.mem_cocompact'.mpr ⟨tsupport ψ, hψcs, ?_⟩
  intro x hx
  -- If `ψ x` is `ε`-far from `0`, then `ψ x ≠ 0`, hence `x` belongs to the support and therefore
  -- to the topological support.
  have hx' : ¬ dist (ψ x) 0 < ε := by
    simpa [Set.mem_compl_iff, Set.mem_ofPred_eq] using hx
  have hxε : ε ≤ dist (ψ x) 0 := le_of_not_gt (by simpa [gt_iff_lt] using hx')
  have hx0 : ψ x ≠ 0 := by
    intro hψ0
    have : dist (ψ x) 0 = 0 := by simp [hψ0]
    have : ε ≤ 0 := by simpa [this] using hxε
    exact not_lt_of_ge this hε
  have hx_supp : x ∈ Function.support ψ := by
    simpa [Function.support] using hx0
  have hx_tsupp : x ∈ tsupport ψ := by
    have : x ∈ closure (Function.support ψ) := subset_closure hx_supp
    simpa [tsupport] using this
  exact hx_tsupp

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma aestronglyMeasurable_const_one
    (μ : Measure E) : AEStronglyMeasurable (fun _x : E => (1 : ℝ)) μ :=
  (aestronglyMeasurable_const : AEStronglyMeasurable (fun _x : E => (1 : ℝ)) μ)

private lemma integrable_norm_L2_restrict (hK : IsCompact K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    Integrable (fun x : E => ‖u x‖) (volume.restrict K) := by
  classical
  -- On a finite measure space, `L² ⊆ L¹`.
  have hμ : (volume : Measure E) K < (⊤ : ℝ≥0∞) :=
    (hK.measure_lt_top (μ := (volume : Measure E)))
  let : Fact ((volume : Measure E) K < (⊤ : ℝ≥0∞)) := ⟨hμ⟩
  have : IsFiniteMeasure (volume.restrict K) := by
    infer_instance
  have hu2 : MemLp (fun x : E => u x) (2 : ℝ≥0∞) (volume.restrict K) :=
    MeasureTheory.Lp.memLp u
  have hu1 : MemLp (fun x : E => u x) (1 : ℝ≥0∞) (volume.restrict K) :=
    hu2.mono_exponent (by norm_num)
  -- `MemLp` with exponent `1` is `Integrable`.
  exact (memLp_one_iff_integrable.mp hu1).norm

/-!
The remainder of the compactness proof (Arzelà–Ascoli on the family `smoothBCF '' closedBall`)
is tracked as part of `lean-103.5.2.26.5.3.2.2.1`.

We intentionally keep the helper lemmas above in this file so the final proof can stay short and
only reference re-usable bounds.
-/

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source169

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/ArzelaAscoli.lean; sha256: 2a07daadbe0f7dc940182aa51ed0a62042e7a5e503653e8022ff99d3d39bcd47 -/
section Source170
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: Arzelà–Ascoli for the smoothing operator (Euclidean)

This file proves the Arzelà–Ascoli step for the compact smoothing operator used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main result

- `smoothBCF_image_closedBall_isCompact`:
  For a compact set `K` and a continuous compactly supported kernel `ψ`, the family
  `{ smoothFun ψ u | ‖u‖ ≤ R }` restricted to the compact set `K + tsupport ψ`
  has compact closure in `BoundedContinuousFunction`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.1.1`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEL2CompactnessArzelaAscoli : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessArzelaAscoli : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessArzelaAscoli : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddEL2CompactnessArzelaAscoli : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegEL2CompactnessArzelaAscoli : MeasurableNeg E := by
  infer_instance

variable {K : Set E} {ψ : E → ℝ}

private lemma smoothFun_eq_integral_restrict (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) (x : E) :
    smoothFun (E := E) (K := K) ψ u x =
      ∫ t, u t * ψ (x - t) ∂(volume.restrict K) := by
  classical
  -- Unfold convolution, then restrict the integral using the indicator defining `extendByZeroFun`.
  have :
      smoothFun (E := E) (K := K) ψ u x =
        ∫ t, (extendByZeroFun (E := E) (K := K) u t) • ψ (x - t) ∂(volume : Measure E) := by
    simp [smoothFun, MeasureTheory.convolution_lsmul]
  have h_ind :
      (fun t : E => extendByZeroFun (E := E) (K := K) u t * ψ (x - t)) =
        K.indicator (fun t : E => u t * ψ (x - t)) := by
    funext t
    by_cases ht : t ∈ K <;> simp [extendByZeroFun, ht]
  -- Restrict to `K` using the indicator.
  simp [this, h_ind, MeasureTheory.integral_indicator hKm]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma isCompact_diffSet (hK : IsCompact K) (hψcs : HasCompactSupport ψ) :
    IsCompact
      ((fun p : E × E => p.1 - p.2) '' ((Kψ (K := K) (ψ := ψ)) ×ˢ K)) := by
  have hKψ : IsCompact (Kψ (K := K) (ψ := ψ)) := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hprod : IsCompact ((Kψ (K := K) (ψ := ψ)) ×ˢ K) := hKψ.prod hK
  refine hprod.image ?_
  exact (continuous_fst.sub continuous_snd)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private lemma exists_norm_ψ_bound_on_diffSet (hK : IsCompact K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ↥(Kψ (K := K) (ψ := ψ)), ∀ t : E, t ∈ K → ‖ψ ((x : E) - t)‖ ≤ C := by
  classical
  let diffSet : Set E :=
    (fun p : E × E => p.1 - p.2) '' ((Kψ (K := K) (ψ := ψ)) ×ˢ K)
  have hdiff : IsCompact diffSet := isCompact_diffSet (E := E) (K := K) (ψ := ψ) hK hψcs
  by_cases hne : diffSet.Nonempty
  · -- Use the extreme value theorem on the continuous function `z ↦ ‖ψ z‖`.
    have hcont : Continuous (fun z : E => ‖ψ z‖) := hψc.norm
    rcases hdiff.exists_isMaxOn hne (hcont.continuousOn) with ⟨z0, hz0, hzmax⟩
    refine ⟨‖ψ z0‖, norm_nonneg _, ?_⟩
    intro x t ht
    have hx : (x : E) ∈ Kψ (K := K) (ψ := ψ) := x.2
    have hx_t : (x : E) - t ∈ diffSet := by
      refine ⟨((x : E), t), ?_, rfl⟩
      exact ⟨hx, ht⟩
    exact (isMaxOn_iff.1 hzmax) _ hx_t
  · -- `diffSet = ∅`: take the trivial bound.
    refine ⟨0, le_rfl, ?_⟩
    intro x t ht
    exfalso
    have hx : (x : E) ∈ Kψ (K := K) (ψ := ψ) := x.2
    have : (x : E) - t ∈ diffSet := by
      refine ⟨((x : E), t), ?_, rfl⟩
      exact ⟨hx, ht⟩
    exact hne ⟨(x : E) - t, this⟩

private lemma smoothFun_image_mem_closedBall (hK : IsCompact K)
    (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ}
    (hRpos : 0 < R) (Cψ : ℝ) (hCψ_nonneg : 0 ≤ Cψ)
    (hψ_bound : ∀ x : ↥(Kψ (K := K) (ψ := ψ)), ∀ t : E, t ∈ K → ‖ψ ((x : E) - t)‖ ≤ Cψ) :
    let mK : ℝ :=
      (MeasureTheory.measureUnivNNReal (volume.restrict K)) ^ ((2 : ℝ≥0∞).toReal⁻¹)
    ∀ (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) (x : ↥(Kψ (K := K) (ψ := ψ))),
      f ∈ (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs ''
            Metric.closedBall (0 : _) R) →
        f x ∈ Metric.closedBall (0 : ℝ) (R * (mK * Cψ)) := by
  intro mK
  classical
  have hR : 0 ≤ R := hRpos.le
  have hμK : (volume : Measure E) K < (⊤ : ℝ≥0∞) := hK.measure_lt_top (μ := (volume : Measure E))
  have : Fact ((volume : Measure E) K < (⊤ : ℝ≥0∞)) := ⟨hμK⟩
  have : IsFiniteMeasure ((volume : Measure E).restrict K) := by infer_instance
  let μ : Measure E := (volume : Measure E).restrict K
  have hmK : 0 ≤ mK := by
    have : 0 ≤ (MeasureTheory.measureUnivNNReal (volume.restrict K)) := by simp
    exact Real.rpow_nonneg this _
  intro f x hfA
  rcases hfA with ⟨u, hu_ball, rfl⟩
  have hu_norm : ‖u‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
  -- Build the `L²(K)` kernel element.
  have hker :
      MemLp (fun t : E => ψ ((x : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
    refine MemLp.of_bound (μ := (volume.restrict K))
      (hf := (hψc.aestronglyMeasurable.comp_measurable
        (measurable_const.sub measurable_id))) Cψ ?_
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (μ := (volume : Measure E)) hKm] with t ht
    exact hψ_bound x t ht
  let kx : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
    hker.toLp (fun t : E => ψ ((x : E) - t))
  have hkx_norm : ‖kx‖ ≤ mK * Cψ := by
    have h_ae :
        ∀ᵐ t ∂(volume.restrict K), ‖(fun t : E => ψ ((x : E) - t)) t‖ ≤ Cψ := by
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm] with t ht
      exact hψ_bound x t ht
    have := (MeasureTheory.Lp.norm_le_of_ae_bound
      (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
      (f := kx) (hC := hCψ_nonneg) (by
        -- transport the bound through the `toLp` representative
        filter_upwards [h_ae,
          MeasureTheory.MemLp.coeFn_toLp
            (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
            (f := fun t : E => ψ ((x : E) - t))
            hker] with t ht hrep
        simpa [kx, hrep] using ht))
    simpa [mK] using this
  -- Express the smoothing value as an `L²` inner product, then apply Cauchy–Schwarz.
  have hsmooth :
      smoothFun (E := E) (K := K) ψ u (x : E) =
        ∫ t, u t * kx t ∂(volume.restrict K) := by
    have h_ae :
        (fun t : E => u t * kx t) =ᵐ[volume.restrict K] fun t : E => u t * ψ ((x : E) - t) := by
      filter_upwards [MeasureTheory.MemLp.coeFn_toLp
        (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
        (f := fun t : E => ψ ((x : E) - t))
        hker] with t ht
      simp [kx, ht]
    -- rewrite `smoothFun` as an integral on `volume.restrict K`
    rw [smoothFun_eq_integral_restrict
      (E := E) (K := K) (ψ := ψ) (hKm := hKm) u (x : E)]
    exact (MeasureTheory.integral_congr_ae h_ae.symm)
  have hsmooth' :
      smoothFun (E := E) (K := K) ψ u (x : E) =
        ∫ t, kx t * u t ∂(volume.restrict K) := by
    simp [hsmooth, mul_comm]
  have hinner :
      smoothFun (E := E) (K := K) ψ u (x : E) =
        inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx := by
    erw [MeasureTheory.L2.inner_def]; exact hsmooth'
  have habs :
      |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ ‖u‖ * ‖kx‖ := by
    simpa [hinner] using
      (abs_real_inner_le_norm (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx)
  have habs' : |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ R * (mK * Cψ) := by
    calc
      |smoothFun (E := E) (K := K) ψ u (x : E)|
          ≤ ‖u‖ * ‖kx‖ := habs
      _ ≤ R * (mK * Cψ) := by
        exact mul_le_mul hu_norm hkx_norm (norm_nonneg _) hR
  have : dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x) 0 ≤ R * (mK * Cψ) := by
    simpa [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x,
      dist_eq_norm, Real.norm_eq_abs] using habs'
  simpa [Metric.mem_closedBall, dist_eq_norm] using this

/-- Arzelà--Ascoli: smoothing maps `L²(K)` bounded sets into a precompact set
in `BCF(K + tsupport ψ)`. -/
private lemma uniformEquicontinuous_smoothBCF_closedBall (hK : IsCompact K)
    (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ}
    (hRpos : 0 < R) (Cψ : ℝ) (hCψ_nonneg : 0 ≤ Cψ)
    (hψ_bound : ∀ x : ↥(Kψ (K := K) (ψ := ψ)), ∀ t : E, t ∈ K → ‖ψ ((x : E) - t)‖ ≤ Cψ) :
    let A : Set (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
      smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' Metric.closedBall (0 : _) R
    UniformEquicontinuous ((↑) : A → ↥(Kψ (K := K) (ψ := ψ)) → ℝ) := by
  intro A
  classical
  have hR : 0 ≤ R := hRpos.le
  have hR0 : R ≠ 0 := ne_of_gt hRpos
  have hμK : (volume : Measure E) K < (⊤ : ℝ≥0∞) := hK.measure_lt_top (μ := (volume : Measure E))
  have : Fact ((volume : Measure E) K < (⊤ : ℝ≥0∞)) := ⟨hμK⟩
  have : IsFiniteMeasure ((volume : Measure E).restrict K) := by infer_instance
  let μ : Measure E := (volume : Measure E).restrict K
  let mK : ℝ :=
    (MeasureTheory.measureUnivNNReal (volume.restrict K)) ^ ((2 : ℝ≥0∞).toReal⁻¹)
  have hmK : 0 ≤ mK := Real.rpow_nonneg (by simp) _
  let s : Set ℝ := Metric.closedBall (0 : ℝ) (R * (mK * Cψ))
  have in_s :=
    smoothFun_image_mem_closedBall (K := K) (ψ := ψ) hK hKm hψc hψcs
      (R := R) hRpos Cψ hCψ_nonneg hψ_bound
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  -- Handle the zero-measure case separately (then `mK = 0` and everything is constant).
  by_cases hmK0 : mK = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro x y _ f
    -- With `mK = 0`, the range bound forces all values to be `0`.
    set F : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ :=
      (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) with hF
    have hzero : ∀ z, F z = 0 := by
      intro z
      have hmem : F z ∈ s := in_s (f := F) z f.property
      have hle : dist (F z) 0 ≤ 0 := by
        have : dist (F z) 0 ≤ R * (mK * Cψ) := by simpa [s, Metric.mem_closedBall] using hmem
        simpa [hmK0] using this
      exact dist_eq_zero.1 (le_antisymm hle dist_nonneg)
    simpa [hzero x, hzero y] using hε
  · have hRmK_ne : R * mK ≠ 0 := mul_ne_zero hR0 hmK0
    let ε2 : ℝ := ε / 2
    have hε2pos : 0 < ε2 := by
      simpa [ε2] using half_pos hε
    let ε' : ℝ := ε2 / (R * mK)
    have hε'pos : 0 < ε' :=
      div_pos hε2pos (mul_pos hRpos (lt_of_le_of_ne hmK (Ne.symm hmK0)))
    have hε'lt : R * mK * ε' = ε2 := by
      dsimp [ε']
      field_simp [hRmK_ne, mul_assoc, mul_left_comm, mul_comm]
    -- Use uniform continuity of `ψ` to get `deltaLoss`.
    have hUC : UniformContinuous ψ := uniformContinuous_ψ (E := E) (ψ := ψ) hψc hψcs
    rcases (Metric.uniformContinuous_iff.1 hUC) ε' hε'pos with ⟨deltaLoss, hδpos, hδ⟩
    refine ⟨deltaLoss, hδpos, ?_⟩
    intro x y hxy f
    -- Work with the `smoothBCF` representative of `f`.
    rcases f.property with ⟨u, hu_ball, hu_eq⟩
    have hu_eq' :
        (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) =
          smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u := by
      simpa using hu_eq.symm
    have hu_norm : ‖u‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
    -- Kernel elements at `x` and `y`.
    have hkerx :
        MemLp (fun t : E => ψ ((x : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
      refine MemLp.of_bound (μ := (volume.restrict K))
        (hf := (hψc.aestronglyMeasurable.comp_measurable
          (measurable_const.sub measurable_id))) Cψ ?_
      filter_upwards
        [MeasureTheory.ae_restrict_mem
          (μ := (volume : Measure E)) hKm] with t ht
      exact hψ_bound x t ht
    have hkery :
        MemLp (fun t : E => ψ ((y : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
      refine MemLp.of_bound (μ := (volume.restrict K))
        (hf := (hψc.aestronglyMeasurable.comp_measurable
          (measurable_const.sub measurable_id))) Cψ ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm] with t ht
      exact hψ_bound y t ht
    let kx : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
      hkerx.toLp (fun t : E => ψ ((x : E) - t))
    let ky : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
      hkery.toLp (fun t : E => ψ ((y : E) - t))
    -- AE bound on `‖kx - ky‖` by `ε'`.
    have h_ae :
        ∀ᵐ t ∂(volume.restrict K), ‖(kx - ky) t‖ ≤ ε' := by
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm,
        MeasureTheory.MemLp.coeFn_toLp (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
          (f := fun t : E => ψ ((x : E) - t)) hkerx,
        MeasureTheory.MemLp.coeFn_toLp (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
          (f := fun t : E => ψ ((y : E) - t)) hkery,
        (MeasureTheory.Lp.coeFn_sub (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞)) kx ky)] with
        t ht hx_t hy_t hsub
      have hxy' : dist ((x : E) - t) ((y : E) - t) < deltaLoss := by
        rw [dist_sub_right]
        exact hxy
      have hψxy : dist (ψ ((x : E) - t)) (ψ ((y : E) - t)) < ε' :=
        hδ (a := (x : E) - t) (b := (y : E) - t) hxy'
      have : ‖ψ ((x : E) - t) - ψ ((y : E) - t)‖ ≤ ε' := by
        simpa [dist_eq_norm, sub_eq_add_neg] using le_of_lt hψxy
      have hx' : kx t = ψ ((x : E) - t) := by simpa [kx] using hx_t
      have hy' : ky t = ψ ((y : E) - t) := by simpa [ky] using hy_t
      have hnorm : ‖kx t - ky t‖ ≤ ε' := by
        simpa [hx', hy'] using this
      have hsub' : (kx - ky) t = kx t - ky t := by
        simpa [Pi.sub_apply] using hsub
      simpa [hsub'.symm] using hnorm
    have hkdiff : ‖kx - ky‖ ≤ mK * ε' := by
      have := (MeasureTheory.Lp.norm_le_of_ae_bound (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
        (f := (kx - ky : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ)) (hC := le_of_lt hε'pos) h_ae)
      simpa [mK, mul_comm, mul_left_comm, mul_assoc] using this
    -- Bound the difference of values using Cauchy–Schwarz.
    have hdist :
        dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
            (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
          ≤ ‖u‖ * ‖kx - ky‖ := by
      -- Express each value as an inner product.
      have hx_val :
          smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x =
            inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx := by
        have hsmooth :
            smoothFun (E := E) (K := K) ψ u (x : E) =
              ∫ t, u t * kx t ∂(volume.restrict K) := by
          have h_ae' :
              (fun t : E => u t * kx t) =ᵐ[volume.restrict K]
                fun t : E => u t * ψ ((x : E) - t) := by
            filter_upwards [MeasureTheory.MemLp.coeFn_toLp
              (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
              (f := fun t : E => ψ ((x : E) - t))
              hkerx] with t ht
            simp [kx, ht]
          rw [smoothFun_eq_integral_restrict
            (E := E) (K := K) (ψ := ψ) (hKm := hKm)
            u (x : E)]
          exact (MeasureTheory.integral_congr_ae h_ae'.symm)
        have hsmooth' :
            smoothFun (E := E) (K := K) ψ u (x : E) =
              ∫ t, kx t * u t ∂(volume.restrict K) := by
          simp [hsmooth, mul_comm]
        erw [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x,
          MeasureTheory.L2.inner_def]; exact hsmooth'
      have hy_val :
          smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y =
            inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) ky := by
        have hsmooth :
            smoothFun (E := E) (K := K) ψ u (y : E) =
              ∫ t, u t * ky t ∂(volume.restrict K) := by
          have h_ae' :
              (fun t : E => u t * ky t) =ᵐ[volume.restrict K]
                fun t : E => u t * ψ ((y : E) - t) := by
            filter_upwards [MeasureTheory.MemLp.coeFn_toLp
              (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
              (f := fun t : E => ψ ((y : E) - t))
              hkery] with t ht
            simp [ky, ht]
          rw [smoothFun_eq_integral_restrict
            (E := E) (K := K) (ψ := ψ) (hKm := hKm)
            u (y : E)]
          exact (MeasureTheory.integral_congr_ae h_ae'.symm)
        have hsmooth' :
            smoothFun (E := E) (K := K) ψ u (y : E) =
              ∫ t, ky t * u t ∂(volume.restrict K) := by
          simp [hsmooth, mul_comm]
        erw [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y,
          MeasureTheory.L2.inner_def]; exact hsmooth'
      have :
          ‖smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x -
              smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y‖ ≤
            ‖u‖ * ‖kx - ky‖ := by
        have :
            smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x -
                smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y =
              inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky) := by
          simp [hx_val, hy_val, inner_sub_right]
        have this' :
            smoothFun (E := E) (K := K) ψ u (x : E) - smoothFun (E := E) (K := K) ψ u (y : E) =
              inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky) := by
          simpa [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs] using this
        have hCS :=
          (abs_real_inner_le_norm (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) (kx - ky))
        simpa [this', dist_eq_norm, Real.norm_eq_abs] using hCS
      simpa [dist_eq_norm] using this
    have hle :
        dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
            (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
          ≤ R * (mK * ε') := by
      calc
        dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
            (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y)
            ≤ ‖u‖ * ‖kx - ky‖ := hdist
        _ ≤ ‖u‖ * (mK * ε') := by
          exact mul_le_mul_of_nonneg_left hkdiff (norm_nonneg _)
        _ ≤ R * (mK * ε') := by
          have hmKε' : 0 ≤ mK * ε' := mul_nonneg hmK (le_of_lt hε'pos)
          exact mul_le_mul_of_nonneg_right hu_norm hmKε'
    have hRmkε' : R * (mK * ε') = ε2 := by
      have : R * mK * ε' = ε2 := by
        simpa [ε', mul_assoc] using hε'lt
      simpa [mul_assoc] using this
    have hle' :
        dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
            (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y) ≤ ε2 := by
      simpa [hRmkε'] using hle
    have hε2lt : ε2 < ε := by
      simpa [ε2] using half_lt_self hε
    have :
        dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x)
            (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u y) < ε :=
      lt_of_le_of_lt hle' hε2lt
    simpa [hu_eq'] using this

theorem smoothBCF_image_closedBall_isCompact (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact
        (closure
          (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' Metric.closedBall (0 : _)
            R)) := by
  classical
  -- Radius `0`: the image is a singleton, hence compact.
  by_cases hR0 : R = 0
  · subst hR0
    have hball :
        Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) 0 = {0} := by
      ext u
      simp
    -- Reduce to a singleton.
    simp [hball]
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    -- Compactness of the codomain.
    let : CompactSpace ↥(Kψ (K := K) (ψ := ψ)) :=
      isCompact_iff_compactSpace.1 (isCompact_Kψ (K := K) (ψ := ψ) hK hψcs)
    let A :
        Set (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
      smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' Metric.closedBall (0 : _) R
    -- `volume.restrict K` is finite since `K` is compact.
    have hμK : (volume : Measure E) K < (⊤ : ℝ≥0∞) := hK.measure_lt_top (μ := (volume : Measure E))
    let : Fact ((volume : Measure E) K < (⊤ : ℝ≥0∞)) := ⟨hμK⟩
    have : IsFiniteMeasure (volume.restrict K) := by
      infer_instance
    let μ : Measure E := (volume : Measure E).restrict K
    let mK : ℝ :=
      (MeasureTheory.measureUnivNNReal (volume.restrict K)) ^ ((2 : ℝ≥0∞).toReal⁻¹)
    have hmK : 0 ≤ mK := by
      have : 0 ≤ (MeasureTheory.measureUnivNNReal (volume.restrict K)) := by simp
      exact Real.rpow_nonneg this _
    -- Uniform bound on `ψ` over the relevant compact difference set.
    obtain ⟨Cψ, hCψ_nonneg, hψ_bound⟩ :=
      exists_norm_ψ_bound_on_diffSet (E := E) (K := K) (ψ := ψ) hK hψc hψcs
    -- A compact ball controlling all values.
    let s : Set ℝ := Metric.closedBall (0 : ℝ) (R * (mK * Cψ))
    have hs : IsCompact s := by
      simpa [s] using isCompact_closedBall (0 : ℝ) (R * (mK * Cψ))
    -- Pointwise compact range: each function in `A` takes values in `s`.
    have in_s :
        ∀ (f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) (x : ↥(Kψ (K := K) (ψ := ψ))),
          f ∈ A → f x ∈ s := by
      intro f x hfA
      rcases hfA with ⟨u, hu_ball, rfl⟩
      have hu_norm : ‖u‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
      -- Build the `L²(K)` kernel element.
      have hker :
          MemLp (fun t : E => ψ ((x : E) - t)) (2 : ℝ≥0∞) (volume.restrict K) := by
        refine MemLp.of_bound (μ := (volume.restrict K))
          (hf := (hψc.aestronglyMeasurable.comp_measurable
            (measurable_const.sub measurable_id))) Cψ ?_
        filter_upwards
          [MeasureTheory.ae_restrict_mem
            (μ := (volume : Measure E)) hKm] with t ht
        exact hψ_bound x t ht
      let kx : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ :=
        hker.toLp (fun t : E => ψ ((x : E) - t))
      have hkx_norm : ‖kx‖ ≤ mK * Cψ := by
        have h_ae :
            ∀ᵐ t ∂(volume.restrict K), ‖(fun t : E => ψ ((x : E) - t)) t‖ ≤ Cψ := by
          filter_upwards [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hKm] with t ht
          exact hψ_bound x t ht
        have := (MeasureTheory.Lp.norm_le_of_ae_bound
          (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
          (f := kx) (hC := hCψ_nonneg) (by
            -- transport the bound through the `toLp` representative
            filter_upwards [h_ae,
              MeasureTheory.MemLp.coeFn_toLp
                (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
                (f := fun t : E => ψ ((x : E) - t))
                hker] with t ht hrep
            simpa [kx, hrep] using ht))
        simpa [mK] using this
      -- Express the smoothing value as an `L²` inner product, then apply Cauchy–Schwarz.
      have hsmooth :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            ∫ t, u t * kx t ∂(volume.restrict K) := by
        have h_ae :
            (fun t : E => u t * kx t) =ᵐ[volume.restrict K] fun t : E => u t * ψ ((x : E) - t) := by
          filter_upwards [MeasureTheory.MemLp.coeFn_toLp
            (μ := (volume.restrict K)) (p := (2 : ℝ≥0∞))
            (f := fun t : E => ψ ((x : E) - t))
            hker] with t ht
          simp [kx, ht]
        -- rewrite `smoothFun` as an integral on `volume.restrict K`
        rw [smoothFun_eq_integral_restrict
          (E := E) (K := K) (ψ := ψ) (hKm := hKm) u (x : E)]
        exact (MeasureTheory.integral_congr_ae h_ae.symm)
      have hsmooth' :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            ∫ t, kx t * u t ∂(volume.restrict K) := by
        simp [hsmooth, mul_comm]
      have hinner :
          smoothFun (E := E) (K := K) ψ u (x : E) =
            inner ℝ (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx := by
        erw [MeasureTheory.L2.inner_def]; exact hsmooth'
      have habs :
          |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ ‖u‖ * ‖kx‖ := by
        simpa [hinner] using
          (abs_real_inner_le_norm (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μ) kx)
      have habs' : |smoothFun (E := E) (K := K) ψ u (x : E)| ≤ R * (mK * Cψ) := by
        calc
          |smoothFun (E := E) (K := K) ψ u (x : E)|
              ≤ ‖u‖ * ‖kx‖ := habs
          _ ≤ R * (mK * Cψ) := by
            exact mul_le_mul hu_norm hkx_norm (norm_nonneg _) hR
      have : dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x) 0 ≤ R * (mK * Cψ) := by
        simpa [smoothBCF_apply (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u x,
          dist_eq_norm, Real.norm_eq_abs] using habs'
      simpa [s, Metric.mem_closedBall, dist_eq_norm] using this
    -- Equicontinuity for `A`.
    have H' :
        UniformEquicontinuous ((↑) : A → ↥(Kψ (K := K) (ψ := ψ)) → ℝ) :=
      uniformEquicontinuous_smoothBCF_closedBall (K := K) (ψ := ψ) hK hKm hψc hψcs
        (R := R) hRpos Cψ hCψ_nonneg hψ_bound
    have H : Equicontinuous ((↑) : A → ↥(Kψ (K := K) (ψ := ψ)) → ℝ) := H'.equicontinuous
    -- Apply Arzelà–Ascoli.
    simpa [A, s] using
      (BoundedContinuousFunction.arzela_ascoli (α := ↥(Kψ (K := K) (ψ := ψ))) (β := ℝ)
        (s := s) hs A (fun f x hf => in_s f x hf) H)

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source170

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Transfer.lean; sha256: baaccc11a03d74694c2d9cd5a159442bec32085edd2517aeb9eb0e840b89c532 -/
section Source171
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: transfer from `BCF` compactness to `L²` (Euclidean)

This file transfers the Arzelà–Ascoli compactness of the `BoundedContinuousFunction` packaging of
`smoothFun` on the compact set `K + tsupport ψ` to a compactness statement in `L²(volume)`.

## Main results

- `smoothL2_image_closedBall_isCompact`:
  For a compact set `K` and a continuous compactly supported kernel `ψ`, the family
  `{ smoothL2 ψ u | ‖u‖ ≤ R }` has compact closure in `L²(volume)`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.1.2`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEL2CompactnessTransfer : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessTransfer : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessTransfer : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddEL2CompactnessTransfer : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegEL2CompactnessTransfer : MeasurableNeg E := by
  infer_instance

variable {K : Set E} {ψ : E → ℝ}

private lemma dist_smoothL2_le_mul_dist_smoothBCF (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) :
    ∀ u v : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K),
      dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs v) ≤
        (MeasureTheory.measureUnivNNReal ((volume : Measure E).restrict (Kψ (K := K) (ψ := ψ)))) ^
            ((2 : ℝ≥0∞).toReal⁻¹) *
          dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
              (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs v) := by
  classical
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let s : Set E := Kψ (K := K) (ψ := ψ)
  have hs_compact : IsCompact s := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hs : MeasurableSet s := hs_compact.measurableSet
  have hs_lt_top : (volume : Measure E) s < (⊤ : ℝ≥0∞) :=
    hs_compact.measure_lt_top (μ := (volume : Measure E))
  let μs : Measure E := (volume : Measure E).restrict s
  have : Fact ((volume : Measure E) s < (⊤ : ℝ≥0∞)) := ⟨hs_lt_top⟩
  have : IsFiniteMeasure μs := by
    infer_instance
  let mS : ℝ := (MeasureTheory.measureUnivNNReal μs) ^ ((2 : ℝ≥0∞).toReal⁻¹)
  intro u v
  set Su :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
  set Sv :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs v
  set Bu :=
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u
  set Bv :=
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs v
  have hBuBv : 0 ≤ ‖Bu - Bv‖ := norm_nonneg _
  -- Work on `F := Su - Sv` and restrict to the finite-measure set `s`.
  let F : (E →₂[(volume : Measure E)] ℝ) := Su - Sv
  let g : E → ℝ := fun x => (F : E → ℝ) x
  have hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (volume : Measure E) := MeasureTheory.Lp.memLp F
  have hg_restrict : MeasureTheory.MemLp g (2 : ℝ≥0∞) μs := hg.restrict s
  let Fs : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) μs := hg_restrict.toLp g
  -- Show `Fs` is pointwise bounded by `‖Bu - Bv‖` on `μs`.
  have hF_ae :
      (g =ᵐ[μs] fun x : E =>
        smoothFun (E := E) (K := K) ψ u x -
          smoothFun (E := E) (K := K) ψ v x) := by
    have hsub :
        (F : E → ℝ) =ᵐ[(volume : Measure E)] (Su : E → ℝ) - (Sv : E → ℝ) := by
      simpa [F, g, Su, Sv] using
        (MeasureTheory.Lp.coeFn_sub (μ := (volume : Measure E)) Su Sv)
    have hu :
        (Su : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
      smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
    have hv :
        (Sv : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ v :=
      smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs v
    have hF :
        (F : E → ℝ) =ᵐ[(volume : Measure E)]
          fun x : E =>
            smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x := by
      have h := hsub.trans (hu.sub hv)
      filter_upwards [h] with x hx
      simpa [Pi.sub_apply] using hx
    exact MeasureTheory.ae_restrict_of_ae (μ := (volume : Measure E)) (s := s) hF
  have hFs_ae : ((Fs : E → ℝ) =ᵐ[μs] g) := by
    simpa [Fs, g] using
      (MeasureTheory.MemLp.coeFn_toLp (μ := μs) (p := (2 : ℝ≥0∞)) (f := g) hg_restrict)
  have hbound :
      ∀ᵐ x ∂μs, ‖Fs x‖ ≤ ‖Bu - Bv‖ := by
    have hpoint :
        ∀ x : E, x ∈ s → ‖smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x‖ ≤
          ‖Bu - Bv‖ := by
      intro x hx
      let x' : ↥(Kψ (K := K) (ψ := ψ)) := ⟨x, hx⟩
      have hBu : Bu x' = smoothFun (E := E) (K := K) ψ u x := by
        simp [Bu, x']
      have hBv : Bv x' = smoothFun (E := E) (K := K) ψ v x := by
        simp [Bv, x']
      have : ‖(Bu - Bv) x'‖ ≤ ‖Bu - Bv‖ :=
        (Bu - Bv).norm_coe_le_norm x'
      simpa [hBu, hBv] using this
    filter_upwards
      [MeasureTheory.ae_restrict_mem (μ := (volume : Measure E)) hs,
        hFs_ae, hF_ae] with x hx hFs hF
    have := hpoint x hx
    -- rewrite through the AE equalities
    simpa [hFs, hF] using this
  have hnorm_Fs : ‖Fs‖ ≤ mS * ‖Bu - Bv‖ := by
    have := (MeasureTheory.Lp.norm_le_of_ae_bound (μ := μs) (p := (2 : ℝ≥0∞))
      (f := Fs) (hC := hBuBv) hbound)
    simpa [mS] using this
  -- Relate the `L²` norm on `volume` to the restricted norm on `μs` using extension-by-zero.
  have hsupport :
      ∀ x : E, x ∉ s →
        smoothFun (E := E) (K := K) ψ u x -
          smoothFun (E := E) (K := K) ψ v x = 0 := by
    intro x hx
    have hu_supp : Function.support (smoothFun (E := E) (K := K) ψ u) ⊆ s := by
      exact
        (support_smoothFun_subset_add_tsupport (E := E) (K := K) (ψ := ψ) u)
    have hv_supp : Function.support (smoothFun (E := E) (K := K) ψ v) ⊆ s := by
      exact
        (support_smoothFun_subset_add_tsupport (E := E) (K := K) (ψ := ψ) v)
    have hu0 : smoothFun (E := E) (K := K) ψ u x = 0 := by
      have : x ∉ Function.support (smoothFun (E := E) (K := K) ψ u) := fun hx' => hx (hu_supp hx')
      simpa [Function.support] using this
    have hv0 : smoothFun (E := E) (K := K) ψ v x = 0 := by
      have : x ∉ Function.support (smoothFun (E := E) (K := K) ψ v) := fun hx' => hx (hv_supp hx')
      simpa [Function.support] using this
    simp [hu0, hv0]
  have hF0 :
      ∀ᵐ x ∂(volume : Measure E), x ∉ s → g x = 0 := by
    have hF_ae_full :
        (g =ᵐ[(volume : Measure E)]
          fun x : E =>
            smoothFun (E := E) (K := K) ψ u x -
              smoothFun (E := E) (K := K) ψ v x) := by
      have hsub :
          (F : E → ℝ) =ᵐ[(volume : Measure E)] (Su : E → ℝ) - (Sv : E → ℝ) := by
        simpa [F, g, Su, Sv] using
          (MeasureTheory.Lp.coeFn_sub (μ := (volume : Measure E)) Su Sv)
      have hu :
          (Su : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ u :=
        smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs u
      have hv :
          (Sv : E → ℝ) =ᵐ[(volume : Measure E)] smoothFun (E := E) (K := K) ψ v :=
        smoothL2_ae_eq (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs v
      have hF :
          (F : E → ℝ) =ᵐ[(volume : Measure E)]
            fun x : E =>
              smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x := by
        have h := hsub.trans (hu.sub hv)
        filter_upwards [h] with x hx
        simpa [Pi.sub_apply] using hx
      simpa [g] using hF
    filter_upwards [hF_ae_full] with x hx
    intro hxnot
    have : smoothFun (E := E) (K := K) ψ u x - smoothFun (E := E) (K := K) ψ v x = 0 :=
      hsupport x hxnot
    simpa [hx] using this
  have hF_ind :
      (s.indicator g =ᵐ[(volume : Measure E)] g) := by
    filter_upwards [hF0] with x hx
    by_cases hxmem : x ∈ s
    · simp [g, hxmem]
    · have : g x = 0 := hx hxmem
      simp [g, hxmem, this]
  -- Conclude `‖F‖ = ‖Fs‖` using `extendByZeroₗᵢ` and the indicator identity.
  let Fext :
      MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume : Measure E) :=
    (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
      (s := s) hs) Fs
  have hFext_ae :
      ((Fext : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume : Measure E)) :
          E → ℝ) =ᵐ[(volume : Measure E)]
        s.indicator fun x : E => (Fs : E → ℝ) x := by
    simpa [Fext] using
      (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq
        (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
        (s := s) hs Fs)
  have hFs_on :
      ∀ᵐ x ∂(volume : Measure E), x ∈ s → (Fs : E → ℝ) x = g x := by
    -- rewrite the AE equality `Fs = g` on the restricted measure as an implication on `volume`
    have := (MeasureTheory.ae_restrict_iff' (μ := (volume : Measure E)) (s := s) hs).1 hFs_ae
    simpa [g] using this
  have hindicator :
      (s.indicator (fun x : E => (Fs : E → ℝ) x) =ᵐ[(volume : Measure E)] s.indicator g) := by
    filter_upwards [hFs_on] with x hx
    by_cases hxmem : x ∈ s
    · simp [hxmem, hx hxmem]
    · simp [hxmem]
  have hFext_ae' :
      (Fext : E → ℝ) =ᵐ[(volume : Measure E)] g := by
    exact hFext_ae.trans (hindicator.trans hF_ind)
  have hFext_eq : Fext = F := by
    refine MeasureTheory.Lp.ext ?_
    simpa [g, F] using hFext_ae'
  have hnorm_F : ‖F‖ ≤ mS * ‖Bu - Bv‖ := by
    -- use `‖F‖ = ‖Fs‖` via the isometry.
    have hnorm_ext : ‖Fext‖ = ‖Fs‖ := by
      simp [Fext]
    -- `Fext = F` and `Fs` is bounded.
    have : ‖Fext‖ ≤ mS * ‖Bu - Bv‖ := by
      simpa [hnorm_ext] using hnorm_Fs
    simpa [hFext_eq] using this
  -- Convert to the `dist` statement.
  simpa [Su, Sv, Bu, Bv, F, dist_eq_norm, mS, mul_assoc] using hnorm_F

theorem smoothL2_image_closedBall_isCompact (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact
        (closure
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' Metric.closedBall (0 : _) R)) := by
  classical
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let s : Set E := Kψ (K := K) (ψ := ψ)
  have hs_compact : IsCompact s := isCompact_Kψ (K := K) (ψ := ψ) hK hψcs
  have hs : MeasurableSet s := hs_compact.measurableSet
  have hs_lt_top : (volume : Measure E) s < (⊤ : ℝ≥0∞) :=
    hs_compact.measure_lt_top (μ := (volume : Measure E))
  let μs : Measure E := (volume : Measure E).restrict s
  have : Fact ((volume : Measure E) s < (⊤ : ℝ≥0∞)) := ⟨hs_lt_top⟩
  have : IsFiniteMeasure μs := by
    infer_instance
  let mS : ℝ := (MeasureTheory.measureUnivNNReal μs) ^ ((2 : ℝ≥0∞).toReal⁻¹)
  have hmS : 0 ≤ mS := by
    have : 0 ≤ (MeasureTheory.measureUnivNNReal μs) := by simp
    exact Real.rpow_nonneg this _
  let U : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :=
    Metric.closedBall (0 : _) R
  let A :
      Set (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
    smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs '' U
  let B : Set (E →₂[(volume : Measure E)] ℝ) :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' U
  have hA_compact : IsCompact (closure A) :=
    smoothBCF_image_closedBall_isCompact (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (R := R) hR
  have hdist_smoothL2_le :=
    dist_smoothL2_le_mul_dist_smoothBCF (K := K) (ψ := ψ) hK hKm hψc hψcs
  have hTB_B : TotallyBounded B := by
    -- Use a finite `BCF` ε-net for `A` with centers in the image, then transfer to `L²`.
    rw [Metric.totallyBounded_iff]
    intro ε hε
    by_cases hmS0 : mS = 0
    · let c : (E →₂[(volume : Measure E)] ℝ) :=
        smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (0 : _)
      refine ⟨{c}, by simp [c], ?_⟩
      intro w hw
      rcases hw with ⟨u, huU, rfl⟩
      have hle :=
        hdist_smoothL2_le u (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
      have hdist0 :
          dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
              c = 0 := by
        have hmS0' :
            (MeasureTheory.measureUnivNNReal ((volume : Measure E).restrict s) : ℝ) ^
              ((2 : ℝ≥0∞).toReal⁻¹) = 0 := hmS0
        have :
            dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) c ≤ 0 := by
          have hle' := hle
          simp only [s] at hmS0'
          rw [hmS0', zero_mul] at hle'
          simpa [c] using hle'
        exact le_antisymm this dist_nonneg
      refine mem_iUnion.2 ?_
      refine ⟨c, mem_iUnion.2 ?_⟩
      refine ⟨by simp, ?_⟩
      -- membership in the open ball follows from `dist = 0` and `ε > 0`
      simpa [Metric.mem_ball, hdist0] using hε
    · have hmSpos : 0 < mS := lt_of_le_of_ne hmS (Ne.symm hmS0)
      let deltaLoss : ℝ := ε / mS
      have hδpos : 0 < deltaLoss := div_pos hε hmSpos
      obtain ⟨t, htAsub, htFin, htCover⟩ :=
        exists_finite_cover_balls_of_isCompact_closure (s := A) (ε := deltaLoss) hA_compact hδpos
      let tFin : Finset (BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ) :=
        htFin.toFinset
      have htFin_mem :
          ∀ {f : BoundedContinuousFunction (↥(Kψ (K := K) (ψ := ψ))) ℝ}, f ∈ tFin ↔ f ∈ t := by
        intro f
        simp [tFin, htFin.mem_toFinset (a := f)]
      let ι : Type _ := { f // f ∈ tFin }
      have hrep :
          ∀ f : ι,
            ∃ u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K),
              u ∈ U ∧
                smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u = f.1 := by
        intro f
        have hf_t : f.1 ∈ t := (htFin_mem (f := f.1)).1 f.2
        have hfA : f.1 ∈ A := htAsub hf_t
        rcases hfA with ⟨u, huU, huEq⟩
        exact ⟨u, huU, huEq⟩
      choose uOf huOfU huOfEq using hrep
      let tL2 : Set (E →₂[(volume : Measure E)] ℝ) :=
        Set.range fun f : ι => smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f)
      have htL2_fin : tL2.Finite := Set.finite_range _
      refine ⟨tL2, htL2_fin, ?_⟩
      intro w hw
      rcases hw with ⟨u, huU, rfl⟩
      have hBu : (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u) ∈ A := by
        exact ⟨u, huU, rfl⟩
      have : smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u ∈ ⋃ x ∈ t, Metric.ball x deltaLoss :=
        htCover hBu
      rcases mem_iUnion.1 this with ⟨f, hf⟩
      rcases mem_iUnion.1 hf with ⟨hf_t, hf_ball⟩
      have hf_tFin : f ∈ tFin := (htFin_mem (f := f)).2 hf_t
      let f' : ι := ⟨f, hf_tFin⟩
      have hf_ball' :
          dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u) f < deltaLoss := hf_ball
      have hdist :
          dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
              (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f')) < ε := by
        have hle := hdist_smoothL2_le u (uOf f')
        have hf_eq :
            smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f') = f := by
          simpa [f'] using huOfEq f'
        have hdist' :
            dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < deltaLoss := by
          simpa [hf_eq] using hf_ball'
        have : mS * dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < ε := by
          have : mS * dist (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs u)
                  (smoothBCF (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (uOf f')) < mS * deltaLoss := by
            exact mul_lt_mul_of_pos_left hdist' hmSpos
          have hmul : mS * deltaLoss = ε := by
            have hmS_ne : mS ≠ 0 := ne_of_gt hmSpos
            calc
              mS * deltaLoss = mS * (ε / mS) := by simp [deltaLoss]
              _ = mS * ε / mS := (mul_div_assoc mS ε mS).symm
              _ = ε := by simpa using (mul_div_cancel_left₀ ε hmS_ne)
          simpa [hmul] using this
        exact lt_of_le_of_lt hle this
      refine mem_iUnion.2 ?_
      refine ⟨smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs (uOf f'), ?_⟩
      refine mem_iUnion.2 ?_
      refine ⟨?_, hdist⟩
      -- show the chosen center lies in `tL2`
      exact ⟨f', rfl⟩
  -- Compactness follows from total boundedness + completeness of `L²`.
  have hTB_closure : TotallyBounded (closure B) := hTB_B.closure
  have hcomplete : IsComplete (closure B) := isClosed_closure.isComplete
  have hcompact_closure : IsCompact (closure B) :=
    isCompact_iff_totallyBounded_isComplete.2 ⟨hTB_closure, hcomplete⟩
  simpa [B, U] using hcompact_closure

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source171

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/FrechetKolmogorov.lean; sha256: 0697f8661f8e5dbd9a7ec60bbdd09067cbc1768821e41c407cc311899e70eb8f -/
section Source172
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: Fréchet–Kolmogorov (Euclidean, compact support case)

This file packages the final “precompactness via smoothing” step behind the Euclidean `L²`
compactness criterion used by the Rellich–Kondrachov stack:

- the **smoothing operator** `smoothL2 ψ` has compact image on `Metric.closedBall 0 R`;
- the **approximation inequality** bounds `‖smoothL2 ψ u - extendByZeroL2 u‖` by a translation
  error.

We state the criterion at the level needed by the project: families of `L²` functions with common
compact support (modeled as `Lp ℝ 2 (volume.restrict K)` and embedded into `L²(volume)` via
`extendByZeroL2`).

## Main results

- `norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le`:
  if the translation error averaged against `kernelMeasure ψ` is ≤ `η²`, then smoothing approximates
  `extendByZeroL2` within `η`.
- `totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small`:
  if a bounded family admits, at every scale `ε`, a kernel `ψ` for which the above translation error
  is uniformly small, then the embedded family is totally bounded in `L²(volume)`.
- `isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small`:
  the corresponding compact-closure statement.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.3`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEL2CompactnessFrechetKolmogorov : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessFrechetKolmogorov : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessFrechetKolmogorov :
    OpensMeasurableSpace E := by infer_instance
local instance instMeasurableAddEL2CompactnessFrechetKolmogorov : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegEL2CompactnessFrechetKolmogorov : MeasurableNeg E := by
  infer_instance

variable {K : Set E} {ψ : E → ℝ}

lemma norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le
    (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) {η : ℝ} (hη : 0 ≤ η)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
    (htrans :
      ∫ t,
          ‖(translateL2 (μ := (volume : Measure E)) (-t))
                (extendByZeroL2 (E := E) (K := K) hKm u)
              - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
        ∂kernelMeasure (E := E) ψ ≤ η ^ 2) :
    ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
        - extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ η := by
  have hsq :
      ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2 ≤ η ^ 2 := by
    refine (le_trans ?_ htrans)
    simpa using
      norm_sq_smoothL2_sub_extendByZeroL2_le_integral_norm_sq_translateL2_sub_extendByZeroL2
        (E := E) (K := K) (ψ := ψ) (hK := hK) (hKm := hKm) hψc hψcs hψ0 hψint u
  exact (sq_le_sq₀ (norm_nonneg _) hη).1 hsq

theorem totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small
    (hK : IsCompact K) (hKm : MeasurableSet K) {R : ℝ} (hR : 0 ≤ R)
    {A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))}
    (hA : A ⊆ Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) R)
    (hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (extendByZeroL2 (E := E) (K := K) hKm u)
                    - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2) :
    TotallyBounded (extendByZeroL2 (E := E) (K := K) hKm '' A) := by
  classical
  -- Use the finite `ε`-net characterization of total boundedness.
  refine (Metric.totallyBounded_iff).2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hApprox ε hε with ⟨ψ, hψc, hψcs, hψ0, hψint, htrans⟩
  let B : Set (E →₂[(volume : Measure E)] ℝ) :=
    smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs '' Metric.closedBall (0 : _) R
  have hB_compact : IsCompact (closure B) :=
    smoothL2_image_closedBall_isCompact (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs (R := R) hR
  have hB_tot : TotallyBounded B :=
    (totallyBounded_closure).1 hB_compact.totallyBounded
  rcases Metric.finite_approx_of_totallyBounded hB_tot (ε / 2) hε2 with ⟨t, htB, htfin, hBcover⟩
  refine ⟨t, htfin, ?_⟩
  intro x hx
  rcases hx with ⟨u, huA, rfl⟩
  have huR : u ∈ Metric.closedBall (0 : _) R := hA huA
  have hSu_mem : smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u ∈ B := ⟨u, huR, rfl⟩
  have hSu_cover :
      smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u ∈
        ⋃ y, ⋃ (_ : y ∈ t), Metric.ball y (ε / 2) :=
    hBcover hSu_mem
  rcases Set.mem_iUnion.1 hSu_cover with ⟨y, hy⟩
  rcases Set.mem_iUnion.1 hy with ⟨hyT, hyBall⟩
  have hyDist : dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y < ε / 2 := by
    simpa [Metric.ball, Set.mem_ofPred_eq] using hyBall
  have hdist_smooth_ext :
      dist (extendByZeroL2 (E := E) (K := K) hKm u)
          (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) ≤ ε / 2 := by
    have hη : 0 ≤ ε / 2 := le_of_lt hε2
    have hnorm :
        ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
            - extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ ε / 2 :=
      norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le
        (E := E) (K := K) (ψ := ψ) hK hKm hψc hψcs hψ0 hψint (η := ε / 2) hη u (htrans u huA)
    -- Switch to `dist` with the argument order used by `dist_triangle`.
    have hdist :
        dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            (extendByZeroL2 (E := E) (K := K) hKm u) ≤ ε / 2 := by
      simpa [dist_eq_norm] using hnorm
    simpa [dist_comm] using hdist
  have hxDist : dist (extendByZeroL2 (E := E) (K := K) hKm u) y < ε := by
    have htri :=
      dist_triangle (extendByZeroL2 (E := E) (K := K) hKm u)
        (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y
    have hlt :
        dist (extendByZeroL2 (E := E) (K := K) hKm u)
              (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u)
            + dist (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u) y
          < ε / 2 + ε / 2 :=
      add_lt_add_of_le_of_lt hdist_smooth_ext hyDist
    have htmp :
        dist (extendByZeroL2 (E := E) (K := K) hKm u) y < ε / 2 + ε / 2 :=
      lt_of_le_of_lt htri hlt
    simpa [add_halves ε] using htmp
  have hxBall : extendByZeroL2 (E := E) (K := K) hKm u ∈ Metric.ball y ε := by
    simpa [Metric.ball, Set.mem_ofPred_eq] using hxDist
  exact Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hyT, hxBall⟩⟩

theorem isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small
    (hK : IsCompact K) (hKm : MeasurableSet K) {R : ℝ} (hR : 0 ≤ R)
    {A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))}
    (hA : A ⊆ Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) R)
    (hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (extendByZeroL2 (E := E) (K := K) hKm u)
                    - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2) :
    IsCompact (closure (extendByZeroL2 (E := E) (K := K) hKm '' A)) := by
  have ht :
      TotallyBounded (extendByZeroL2 (E := E) (K := K) hKm '' A) :=
    totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small
      (E := E) (K := K) hK hKm hR hA hApprox
  exact (ht.closure).isCompact_of_isClosed isClosed_closure

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source172

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/Kernels.lean; sha256: 0ecda2b05f6092f4728b904c69ebc98368d1b33a3e1ac4d16b54744c26a40103 -/
section Source173
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: existence of small-support probability kernels (Euclidean)

This file provides a “kernel factory” for the Euclidean Fréchet–Kolmogorov / Riesz–Kolmogorov
criterion: for any radius `deltaLoss > 0`, produce a continuous compactly supported function `ψ : E → ℝ`
such that:

- `ψ ≥ 0`,
- `tsupport ψ ⊆ Metric.ball 0 deltaLoss`,
- `∫ ψ = 1` (so `kernelMeasure ψ` is a probability measure).

The construction uses mathlib’s `exists_smooth_tsupport_subset` bump-function lemma and normalizes
by its (positive) integral.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.5`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEL2CompactnessKernels : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessKernels : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessKernels : OpensMeasurableSpace E := by
  infer_instance

/-- For any `deltaLoss > 0`, there exists a continuous compactly supported kernel `ψ` supported in
`Metric.ball 0 deltaLoss`, with `ψ ≥ 0` and `∫ ψ = 1` (w.r.t. Lebesgue measure). -/
theorem exists_kernel_tsupport_subset_ball_integral_eq_one {deltaLoss : ℝ} (hδ : 0 < deltaLoss) :
    ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∫ x, ψ x ∂(volume : Measure E) = 1) ∧ tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss := by
  classical
  -- Start from a smooth bump supported in `ball 0 deltaLoss` with value `1` at `0`.
  have hs : (Metric.ball (0 : E) deltaLoss) ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ hδ
  rcases exists_contDiff_tsupport_subset (n := ⊤)
    (E := E) (s := Metric.ball (0 : E) deltaLoss) (x := (0 : E)) hs with
    ⟨f, hf_tsupp, hf_cs, hf_smooth, hf_range, hf0⟩
  have hf_cont : Continuous f := hf_smooth.continuous
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    have hx : f x ∈ Set.Icc (0 : ℝ) 1 := hf_range ⟨x, rfl⟩
    exact hx.1
  have hf0_ne : f (0 : E) ≠ 0 := by
    -- `f 0 = 1`.
    simp [hf0]
  -- The integral is strictly positive (Lebesgue is an open-positive measure).
  have hIpos :
      0 < ∫ x, f x ∂(volume : Measure E) := by
    simpa using
      (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure E))
        hf_cont hf_cs hf_nonneg hf0_ne)
  set I : ℝ := ∫ x, f x ∂(volume : Measure E)
  have hI0 : I ≠ 0 := ne_of_gt hIpos
  have hIpos' : 0 < I := by simpa [I] using hIpos
  -- Normalize: `ψ = I⁻¹ • f`.
  let ψ : E → ℝ := fun x => I⁻¹ * f x
  have hψc : Continuous ψ := by
    exact (continuous_const.mul hf_cont)
  have hψcs : HasCompactSupport ψ := by
    exact
      (HasCompactSupport.smul_left (f := fun _x : E => I⁻¹) (f' := f) hf_cs)
  have hψ0 : ∀ x, 0 ≤ ψ x := by
    intro x
    have hInv : 0 ≤ I⁻¹ := by
      have : 0 ≤ I := le_of_lt hIpos'
      simpa using inv_nonneg.2 this
    simpa [ψ] using mul_nonneg hInv (hf_nonneg x)
  have hψint : ∫ x, ψ x ∂(volume : Measure E) = 1 := by
    have : (∫ x, ψ x ∂(volume : Measure E)) = I⁻¹ * I := by
      -- Pull out the constant scalar.
      simpa [ψ, I] using
        (MeasureTheory.integral_const_mul (μ := (volume : Measure E)) (r := I⁻¹) (f := f))
    simp [this, hI0]
  have hψ_tsupp : tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss := by
    -- Scaling does not enlarge topological support; use the bump support inclusion.
    have hsub : tsupport ψ ⊆ tsupport f := by
      simpa [ψ, smul_eq_mul] using (tsupport_smul_subset_right (f := fun _x : E => I⁻¹) (g := f))
    exact hsub.trans hf_tsupp
  exact ⟨ψ, hψc, hψcs, hψ0, hψint, hψ_tsupp⟩

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source173

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/L2Compactness/TranslationIntegral.lean; sha256: e5bdb6250b56f202cad71a5f8b2f1bf9eb2e32442975c563ee66e1fd394ecc1e -/
section Source174
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `L²` compactness criterion: bounding the translation-integral by a translation modulus

This file provides a small but crucial bridge lemma used to connect a uniform translation modulus
on `L²(volume)` with the `kernelMeasure` translation-integral bound appearing in the
approximation-identity estimate.

The core observation is that if `ψ` is supported in a neighborhood where the translation modulus is
≤ `η`, then the averaged squared translation error against the probability measure
`kernelMeasure ψ` is ≤ `η²`.

Tracking: Beads `lean-103.5.2.26.5.3.2.2.4`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceEL2CompactnessTranslationIntegral : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessTranslationIntegral : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessTranslationIntegral :
    OpensMeasurableSpace E := by infer_instance
local instance instMeasurableAddEL2CompactnessTranslationIntegral : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegEL2CompactnessTranslationIntegral : MeasurableNeg E := by
  infer_instance

variable {ψ : E → ℝ}

private lemma kernelMeasure_compl_ball_eq_zero_of_tsupport_subset {deltaLoss : ℝ}
    (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss) :
    kernelMeasure (E := E) ψ ((Metric.ball (0 : E) deltaLoss)ᶜ) = 0 := by
  classical
  have hψzero : ∀ x : E, x ∈ (Metric.ball (0 : E) deltaLoss)ᶜ → ψ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ψ := by
      intro hx_ts
      exact hx (hψsupp hx_ts)
    exact image_eq_zero_of_notMem_tsupport (f := ψ) hx'
  have hmeas : MeasurableSet ((Metric.ball (0 : E) deltaLoss)ᶜ) :=
    (measurableSet_ball : MeasurableSet (Metric.ball (0 : E) deltaLoss)).compl
  have hEq :
      Set.EqOn (fun x : E => ENNReal.ofReal (ψ x)) 0 ((Metric.ball (0 : E) deltaLoss)ᶜ) := by
    intro x hx
    simp [hψzero x hx]
  -- Expand `kernelMeasure` and note the density is identically `0` on the set.
  simp [kernelMeasure, MeasureTheory.withDensity_apply, hmeas,
    MeasureTheory.setLIntegral_eq_zero
      (μ := (volume : Measure E))
      (s := (Metric.ball (0 : E) deltaLoss)ᶜ) hmeas hEq]

theorem integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    {deltaLoss η : ℝ} (hη : 0 ≤ η) (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss)
    (F : (E →₂[(volume : Measure E)] ℝ))
    (hmod :
      ∀ t : E, t ∈ Metric.ball (0 : E) deltaLoss →
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η) :
    ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
      ∂kernelMeasure (E := E) ψ ≤ η ^ 2 := by
  classical
  let μ : Measure E := kernelMeasure (E := E) ψ
  have : MeasureTheory.IsProbabilityMeasure μ :=
    ⟨kernelMeasure_univ (E := E) (ψ := ψ) hψc hψcs hψ0 hψint⟩
  have hμzero : μ ((Metric.ball (0 : E) deltaLoss)ᶜ) = 0 := by
    simpa [μ] using kernelMeasure_compl_ball_eq_zero_of_tsupport_subset (E := E) (ψ := ψ) hψsupp
  have hAE_ball : (Metric.ball (0 : E) deltaLoss) ∈ MeasureTheory.ae μ :=
    (MeasureTheory.mem_ae_iff.2 hμzero)
  -- On `Metric.ball 0 deltaLoss`, the squared translation error is bounded by `η²`.
  have hAE_bound :
      ∀ᵐ t : E ∂μ,
        ‖‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2‖ ≤ η ^ 2 := by
    filter_upwards [hAE_ball] with t ht
    have hle : ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η := hmod t ht
    have hsq :
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 ≤ η ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hη).2 hle
    have hnonneg : 0 ≤ ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2 :=
      sq_nonneg _
    have hηnonneg : 0 ≤ η ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hηnonneg] using hsq
  have hnorm_int :
      ‖∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ‖ ≤ η ^ 2 * μ.real Set.univ := by
    simpa using
      (MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun t : E => ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2)
        (C := η ^ 2) hAE_bound)
  have hμreal : μ.real Set.univ = 1 := by
    -- `μ` is a probability measure.
    simp [MeasureTheory.measureReal_def]
  have hnonneg_int :
      0 ≤ ∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ := by
    refine MeasureTheory.integral_nonneg ?_
    intro t
    exact sq_nonneg _
  -- Use `|∫ f| = ∫ f` for a nonnegative integrand.
  have habs :
      |∫ t,
            ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
          ∂μ| ≤ η ^ 2 := by
    have := hnorm_int
    -- Replace `‖·‖` by `abs` in `ℝ` and simplify `μ.real univ = 1`.
    simpa [Real.norm_eq_abs, hμreal, mul_one] using this
  simpa [abs_of_nonneg hnonneg_int, μ] using habs

end Volume

end

end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source174

/- Original source: RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/Rellich.lean; sha256: e256d6064b982f40627992bdd67fa35b668daed89c00b3ef717b80efbb37146f -/
section Source175
/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`

Euclidean Rellich–Kondrachov compactness for fixed compact support (Lebesgue `volume`).

This file discharges the “Euclidean heart” needed by the manifold Rellich glue:
for a fixed compact set `K ⊆ E`, the inclusion `H¹ → L²` is compact when restricted to the closed
subspace of `H¹` whose `L²` component is supported in `K` (a.e.).

The proof uses:

1. the Euclidean `H¹` translation estimate
   `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂` (`TranslationEstimateH1`);
2. the Fréchet–Kolmogorov / smoothing-based `L²` compactness criterion
   (`L2CompactnessCriterion`).

## Main definitions / results

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On`:
  the closed subspace of `H¹(volume)` whose `L²` component is supported in `K` (a.e.).
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2`:
  the restricted inclusion map `h1On K →L[ℝ] L²(volume)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2`:
  compactness of the inclusion.

Tracking: Beads `lean-103.5.2.26.5.3.2.1`.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceRellich : MeasurableSpace E := borel E
local instance instBorelSpaceRellich : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceRellich : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddRellich : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegRellich : MeasurableNeg E := by
  infer_instance
local instance instFactOneLeTwoSobolevEuclideanRellich : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ### Supported `H¹` subspace -/

/-- The subspace of `H¹(volume)` whose `L²` component is (a.e.) supported in `K`.

We model “supported in `K`” as belonging to the closed range of the extension-by-zero map
`Lp(volume.restrict K) →ₗᵢ Lp(volume)`. -/
noncomputable def h1On (K : Set E) (hKm : MeasurableSet K) :
    Submodule ℝ (↥(h1 (μ := (volume : Measure E)) (E := E))) :=
  Submodule.comap
    (h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
    (LinearMap.range
      ((MeasureTheory.Lp.extendByZeroₗᵢ
          (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))

/-- The inclusion `h1On K → L²(volume)` as a continuous linear map. -/
noncomputable def h1OnToL2 (K : Set E) (hKm : MeasurableSet K) :
    ↥(h1On K hKm) →L[ℝ] (E →₂[(volume : Measure E)] ℝ) :=
  (h1ToL2 (μ := (volume : Measure E)) (E := E)).comp (h1On K hKm).subtypeL

/-! ### Euclidean Rellich on fixed compact support -/

/-- Euclidean Rellich–Kondrachov compactness (Lebesgue): on a fixed compact support `K`, the
inclusion `H¹ → L²` is a compact operator. -/
theorem isCompactOperator_h1OnToL2 {K : Set E} (_hK : IsCompact K) (hKm : MeasurableSet K) :
    IsCompactOperator (h1OnToL2 (E := E) K hKm) := by
  classical
  have hr : (0 : ℝ) < 1 := by norm_num
  let H1vol : Type _ := ↥(h1 (μ := (volume : Measure E)) (E := E))
  let T : ↥(h1On (E := E) K hKm) →L[ℝ] (E →₂[(volume : Measure E)] ℝ) :=
    h1OnToL2 (E := E) K hKm
  let A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ((volume : Measure E).restrict K)) :=
    {u |
      L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u ∈
        T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1}
  let C : ℝ :=
    ‖h1ToL2 (μ := (volume : Measure E)) (E := E)‖
  have hCnonneg : 0 ≤ C := by
    exact norm_nonneg (h1ToL2 (μ := (volume : Measure E)) (E := E))
  have hA_ball :
      A ⊆
        Metric.closedBall
          (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) ((volume : Measure E).restrict K))
          C := by
    intro u hu
    rcases hu with ⟨x, hx, hxEq⟩
    have hx' : ‖(x : H1vol)‖ ≤ (1 : ℝ) := by
      -- `h1On` inherits the ambient norm, so this is definitional.
      change ‖x‖ ≤ (1 : ℝ)
      simpa only [Metric.mem_closedBall,dist_zero_right x] using hx
    have hTx' : ‖T x‖ ≤ C := by
      have hTx : ‖T x‖ ≤ C * ‖(x : H1vol)‖ := by
        have h :=
          (h1ToL2 (μ := (volume : Measure E)) (E := E)).le_opNorm (x : H1vol)
        simpa [T, h1OnToL2, C] using h
      refine hTx.trans ?_
      have : C * ‖(x : H1vol)‖ ≤ C * (1 : ℝ) := mul_le_mul_of_nonneg_left hx' hCnonneg
      simpa [mul_one] using this
    have hnorm_ext :
        ‖L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ = ‖u‖ :=
      L2Compactness.norm_extendByZeroL2 (E := E) (K := K) hKm u
    have hu' : ‖u‖ ≤ C := by
      have : ‖L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ C := by
        simpa [hxEq] using hTx'
      simpa [hnorm_ext] using this
    simpa [Metric.closedBall, dist_eq_norm] using hu'
  have hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u)
                    - L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂L2Compactness.kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2 := by
    intro ε hε
    have hδ : 0 < ε / 2 := by linarith
    rcases
        L2Compactness.exists_kernel_tsupport_subset_ball_integral_eq_one
          (E := E) (deltaLoss := ε / 2) hδ with
      ⟨ψ, hψc, hψcs, hψ0, hψint, hψsupp⟩
    refine ⟨ψ, hψc, hψcs, hψ0, hψint, ?_⟩
    intro u huA
    rcases huA with ⟨x, hx, hxEq⟩
    have hxH1 : ‖(x : H1vol)‖ ≤ (1 : ℝ) := by
      change ‖x‖ ≤ (1 : ℝ)
      simpa only [Metric.mem_closedBall,dist_zero_right x] using hx
    have hmod :
        ∀ t : E, t ∈ Metric.ball (0 : E) (ε / 2) →
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) (T x) - T x‖ ≤ ε / 2 := by
      intro t ht
      have ht' : ‖t‖ ≤ ε / 2 := le_of_lt (by
        simpa [Metric.ball, dist_eq_norm, mem_ofPred_eq] using ht)
      have hgrad_le :
          ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ ‖(x : H1vol)‖ := by
        let V : Type _ := (E →₂[(volume : Measure E)] ℝ) × (E →₂[(volume : Measure E)] E)
        simpa [h1ToL2Grad, V] using (norm_snd_le (x := ((x : H1vol) : V)))
      have hgrad_le_one :
          ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ (1 : ℝ) :=
        hgrad_le.trans hxH1
      have htr :=
        norm_translateL2_sub_h1ToL2_le (μ := (volume : Measure E)) (E := E) (-t) (x : H1vol)
      have htr' :
          ‖(translateL2 (μ := (volume : Measure E)) (-t))
                (h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol))
              - h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤
            ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ := by
        simpa [neg_neg] using htr
      have hle :
          ‖(translateL2 (μ := (volume : Measure E)) (-t)) (T x) - T x‖ ≤
            ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ := by
        simpa [T, h1OnToL2, hxEq] using htr'
      refine hle.trans ?_
      have :
          ‖t‖ * ‖h1ToL2Grad (μ := (volume : Measure E)) (E := E) (x : H1vol)‖ ≤ (ε / 2) * 1 := by
        refine (mul_le_mul_of_nonneg_right ht' (norm_nonneg _)).trans ?_
        refine mul_le_mul_of_nonneg_left hgrad_le_one (by linarith)
      simpa [mul_one] using this
    have hη : 0 ≤ ε / 2 := le_of_lt hδ
    have hbound :=
      L2Compactness.integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
        (E := E) (ψ := ψ) hψc hψcs hψ0 hψint (deltaLoss := ε / 2) (η := ε / 2) hη hψsupp (T x) hmod
    simpa [hxEq] using hbound
  have hcomp : IsCompact (closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1)) := by
    have hR : 0 ≤ C := hCnonneg
    have hA_eq :
        T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1 =
          L2Compactness.extendByZeroL2 (E := E) (K := K) hKm '' A := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        have hxRange :
            (h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol)) ∈
              LinearMap.range
                ((MeasureTheory.Lp.extendByZeroₗᵢ
                      (μ := (volume : Measure E)) (E := ℝ)
                      (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) := by
          -- Unfold membership in the defining `comap` without
          -- letting `simp` use `x.property`
          -- (which would rewrite the goal to `True`).
          have hxmem :
              (x : H1vol) ∈ h1On (E := E) K hKm := x.property
          dsimp [h1On] at hxmem
          change
              ((h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
                    (x : H1vol)) ∈
                LinearMap.range
                  ((MeasureTheory.Lp.extendByZeroₗᵢ
                        (μ := (volume : Measure E)) (E := ℝ)
                        (p := (2 : ℝ≥0∞))
                        (s := K) hKm).toLinearMap)
          exact hxmem
        rcases hxRange with ⟨u, hu⟩
        have hu0 :
            (MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm) u =
              h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol) := by
          simpa using hu
        have hTx : T x = L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u := by
          calc
            T x = h1ToL2 (μ := (volume : Measure E)) (E := E) (x : H1vol) := by
                  simp [T, h1OnToL2]
            _ = (MeasureTheory.Lp.extendByZeroₗᵢ
                  (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm) u := by
                  simpa using hu0.symm
            _ = L2Compactness.extendByZeroL2 (E := E) (K := K) hKm u := by
                  simpa using
                    (L2Compactness.extendByZeroL2_eq_extendByZeroₗᵢ (E := E) (K := K) hKm u).symm
        refine ⟨u, ?_, hTx.symm⟩
        exact ⟨x, hx, hTx⟩
      · intro hy
        rcases hy with ⟨u, huA, rfl⟩
        exact huA
    have : IsCompact
        (closure (L2Compactness.extendByZeroL2 (E := E) (K := K) hKm '' A)) :=
    L2Compactness.isCompact_closure_extendByZeroL2_image_of_forall_exists_translationIntegral_small
      (E := E) (K := K) (hK := (_hK : IsCompact K))
      (hKm := hKm) hR hA_ball hApprox
    simpa [hA_eq] using this
  -- Use the topological definition of `IsCompactOperator` to avoid expensive normed-space
  -- characterizations.
  refine ⟨closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1), hcomp, ?_⟩
  have hball :
      Metric.ball (0 : ↥(h1On (E := E) K hKm)) 1 ⊆
        T ⁻¹' closure (T '' Metric.closedBall (0 : ↥(h1On (E := E) K hKm)) 1) := by
    intro x hx
    refine subset_closure ?_
    refine ⟨x, ?_, rfl⟩
    exact Metric.ball_subset_closedBall hx
  exact Filter.mem_of_superset
    (Metric.ball_mem_nhds (x := (0 : ↥(h1On (E := E) K hKm))) (ε := (1 : ℝ)) hr) hball

/-!
### Codomain restriction and a compact map into `L²(volume.restrict K)`

The definition of `h1On` forces the image of `h1OnToL2` to lie in the (closed) range of the
extension-by-zero map from `volume.restrict K`. We record a codomain-restricted version and a
convenient compact map to the restricted `L²` space.
-/

omit [CompleteSpace E] in
lemma isClosed_range_extendByZero (K : Set E) (hKm : MeasurableSet K) :
    IsClosed
      (LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap) :
        Set (E →₂[(volume : Measure E)] ℝ)) := by
  classical
  let e :=
    MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm
  have hcr : IsClosed (Set.range (fun u => e u)) :=
    (e.isometry.isClosedEmbedding).isClosed_range
  have hEq :
      (Set.range (fun u => e u)) =
        (LinearMap.range e.toLinearMap : Set (E →₂[(volume : Measure E)] ℝ)) := by
    ext y
    constructor <;> rintro ⟨u, rfl⟩ <;> exact ⟨u, rfl⟩
  simpa [hEq] using hcr

theorem isCompactOperator_h1OnToL2_codRestrict_range_extendByZero {K : Set E} (hK : IsCompact K)
    (hKm : MeasurableSet K) :
    IsCompactOperator
      (Set.codRestrict
        (h1OnToL2 (E := E) K hKm)
        (LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))
        (by
          intro x
          have hxmem : (x : ↥(h1 (μ := (volume : Measure E)) (E := E))) ∈ h1On (E := E) K hKm :=
            x.property
          dsimp [h1On] at hxmem
          -- Rewrite the codomain-restricted inclusion as `h1ToL2` on the underlying `H¹` element.
          change
              ((h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
                    (x : ↥(h1 (μ := (volume : Measure E)) (E := E)))) ∈
                LinearMap.range
                  ((MeasureTheory.Lp.extendByZeroₗᵢ
                        (μ := (volume : Measure E)) (E := ℝ)
                        (p := (2 : ℝ≥0∞))
                        (s := K) hKm).toLinearMap)
          -- This is exactly the unfolded membership in
          -- the `comap`.
          exact hxmem)) := by
  -- First, use Euclidean Rellich compactness into `L²(volume)`.
  have hcomp : IsCompactOperator (h1OnToL2 (E := E) K hKm) :=
    isCompactOperator_h1OnToL2 (E := E) (K := K) hK hKm
  -- Now codomain-restrict using the closedness of the range.
  -- `hV` is definitional from the codomain restriction in the statement (unification fills it).
  exact
    IsCompactOperator.codRestrict (f := h1OnToL2 (E := E) K hKm) hcomp
      (V := LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))
      (hV := by
        intro x
        have hxmem : (x : ↥(h1 (μ := (volume : Measure E)) (E := E))) ∈ h1On (E := E) K hKm :=
          x.property
        dsimp [h1On] at hxmem
        change
            ((h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
                  (x : ↥(h1 (μ := (volume : Measure E)) (E := E)))) ∈
              LinearMap.range
                ((MeasureTheory.Lp.extendByZeroₗᵢ
                      (μ := (volume : Measure E)) (E := ℝ)
                      (p := (2 : ℝ≥0∞))
                      (s := K) hKm).toLinearMap)
        exact hxmem)
      (h_closed :=
        isClosed_range_extendByZero (E := E) K hKm)

end Volume

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov

end Source175

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/RadialWindows.lean; sha256: 0a49c50c4d2f90ad82c36977b3e215b04ec673851514bc3954afc467ba2fe975 -/
section Source176
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma columnLog_three_split (A C S:Finset ι) (hAC:Disjoint A C)
    (hAS:Disjoint A S) (hCS:Disjoint C S) (ell:ℝ) (hell:0<ell) :
    columnLog p ell ((A∪C)∪S)=columnLog p (ell/(primeProductNorm p A*primeProductNorm p C)) S := by
  unfold columnLog
  rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hAS,hCS⟩),
    primeProductNorm_union p A C hAC]
  congr 1
  have hA := (primeProductNorm_pos p hp A).ne'
  have hC := (primeProductNorm_pos p hp C).ne'
  field_simp

include hp in
lemma canonicalCubeResidual_log
    (b:CubeCoordinates ι) (hb:b.Admissible) (C S:Finset ι)
    (hCB:Disjoint C b.support) (hSC:Disjoint S C) (hSB:Disjoint S b.support)
    (negative:Bool) (Ψ:O→*ℂ) (m f:O) (g:𝓢(ℝ,ℂ)) (ell:ℝ) (hell:0<ell) :
    canonicalCubeResidual p hg b C negative Ψ m f (fun U=>g (columnLog p ell U)) S =
      originalLabelColumn p hg b.support b.leftBit b.rightBit negative
        (multiplicativeCoreColumn p Ψ m (fun U=>g (columnLog p
          (ell/(primeProductNorm p (b.sideDivisor (!negative))*primeProductNorm p C)) U)))
        (∏i∈C,p i) f S := by
  have hA : b.sideDivisor (!negative)⊆b.support := by
    cases negative
    · exact hb.1
    · exact hb.2
  have hlog:=columnLog_three_split p hp (b.sideDivisor (!negative)) C S
    (hCB.symm.mono_left hA) (hSB.symm.mono_left hA) hSC.symm ell hell
  unfold canonicalCubeResidual originalLabelColumn multiplicativeCoreColumn
  have hside : (if negative then b.rightDivisor else b.leftDivisor)=b.sideDivisor (!negative) := by cases negative <;> rfl
  rw [hside]
  dsimp only
  rw [hlog]

lemma actualFirstKernel_insert_windows
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (Ψ₁ Ψ₂:O→*ℂ)
    (m₁ m₂ c f:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (X₁ X₂ K:ℝ) (d h:O)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) c f)
      (originalLabelColumn p hg B ε₁ ε₂ false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) c f)
      W (fun _=>1) (fun _=>1) X₁ X₂ K d h =
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) c f)
      (originalLabelColumn p hg B ε₁ ε₂ false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) c f)
      W V₁ V₂ X₁ X₂ K d h := by
  unfold actualFirstKernel
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP:Disjoint N P
  · simp only [hNP,ite_true,one_mul]
    by_cases h₁:g₁ (columnLog p X₁ N)=0
    · simp only [threeGaussRowFactor,originalLabelColumn,multiplicativeCoreColumn,h₁,mul_zero,zero_mul,star_zero]
    by_cases h₂:g₂ (columnLog p X₂ P)=0
    · simp only [threeGaussRowFactor,originalLabelColumn,multiplicativeCoreColumn,h₂,mul_zero,zero_mul]
    rw [hV₁ _ h₁,hV₂ _ h₂,one_mul,one_mul]
  · simp only [hNP,ite_false]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic

lemma conductor_zero_swap (parityBit a b:Bool) :
    conductorExponent parityBit a b=0 ↔ conductorExponent parityBit b a=0 := by
  cases parityBit <;> cases a <;> cases b <;> decide

lemma conductor_parity_swap (parityBit a b:Bool) :
    (conductorExponent parityBit a b).val%2=(conductorExponent parityBit b a).val%2 := by
  cases parityBit <;> cases a <;> cases b <;> decide

lemma dilationExponent_swap (parityBit a b:Bool) :
    dilationExponent parityBit a b=dilationExponent parityBit b a := by
  cases parityBit <;> cases a <;> cases b <;> rfl

lemma retained_swap (parityBit a b:Bool) : retained parityBit a b=retained parityBit b a := by
  cases parityBit <;> cases a <;> cases b <;> rfl

lemma b0Exponent_swap (m:ℕ) (a b:Bool) : b0Exponent m a b=b0Exponent m b a := by
  cases a <;> cases b <;> simp [b0Exponent,evenDouble]

variable {ι:Type*} (p:ι→O) (B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)

lemma cubeActiveSupport_swap : cubeActiveSupport B v ε₁ ε₂=cubeActiveSupport B v ε₂ ε₁ := by
  ext i
  simp only [cubeActiveSupport,Finset.mem_filter]
  constructor
  · rintro ⟨hi,he⟩
    exact ⟨hi,fun hx=>he ((conductor_zero_swap (parity (v i)) (ε₁ i) (ε₂ i)).mpr hx)⟩
  · rintro ⟨hi,he⟩
    exact ⟨hi,fun hx=>he ((conductor_zero_swap (parity (v i)) (ε₁ i) (ε₂ i)).mp hx)⟩

lemma cubeOddSupport_swap : cubeOddSupport B v ε₁ ε₂=cubeOddSupport B v ε₂ ε₁ := by
  ext i
  simp only [cubeOddSupport,Finset.mem_filter,conductor_parity_swap (parity (v i)) (ε₁ i) (ε₂ i)]

lemma dilationLabel_swap : dilationLabel p B v ε₁ ε₂=dilationLabel p B v ε₂ ε₁ := by
  unfold dilationLabel primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [dilationExponent_swap (parity (v i)) (ε₁ i) (ε₂ i)]

lemma jLabel_swap : jLabel p B v ε₁ ε₂=jLabel p B v ε₂ ε₁ := by
  unfold jLabel primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [retained_swap (parity (v i)) (ε₁ i) (ε₂ i)]

lemma b0Label_swap : b0Label p B v ε₁ ε₂=b0Label p B v ε₂ ε₁ := by
  unfold b0Label primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [b0Exponent_swap (v i) (ε₁ i) (ε₂ i)]
end FirstPassCubeLabels

namespace SecondPassArithmetic

section
open ActualEisensteinCubic FirstPassCubeLabels

theorem firstInputFamilyEnergy_swap {ι:Type*} [DecidableEq ι]
    (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hg:∀i,lambda∉Ideal.span {p i})
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (negative:Bool)
    (Ψ:O→*ℂ) (m:O) (H:Finset ι→ℂ) (V:ℝ→ℂ) (X:ℝ) (c d:O) (J:ℕ) (T:Finset O) :
    firstInputFamilyEnergy p hg F B v ε₁ ε₂ negative Ψ m H V X c d J T =
    firstInputFamilyEnergy p hg F B v ε₂ ε₁ negative Ψ m H V X c d J T := by
  simp only [firstInputFamilyEnergy,firstCoreOuter,firstCoreInputRow,
    cubeOddSupport_swap B v ε₁ ε₂,b0Label_swap p B v ε₁ ε₂,jLabel_swap p B v ε₁ ε₂]

namespace CubeCoordinates
variable {ι:Type*}
def swap (b:CubeCoordinates ι) : CubeCoordinates ι :=
  ⟨b.rightExponent,b.leftExponent,b.rightDivisor,b.leftDivisor⟩
@[simp] lemma swap_swap (b:CubeCoordinates ι) : b.swap.swap=b := by cases b;rfl
end CubeCoordinates
end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def orientedCubeFirstBlock (pool : Finset ι) (b : GlobalCubeBlock ι)
    (s : Finset (Ideal O × O)) (a : Ideal O × O → ℂ)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ W V₁ V₂ : 𝓢(ℝ,ℂ)) (K ell : ℝ) : ℂ :=
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) b.common
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor
  let X₁ := globalCubeColumnScale p ell true b
  let X₂ := globalCubeColumnScale p ell false b
  (primeProductNorm p b.firstDivisor : ℂ)⁻¹ * ∑ x∈s,a x*actualFirstKernel p hp hcop hg (globalCubePool pool b) b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit
    (originalLabelColumn p hg b.cube.support b.cube.rightBit b.cube.leftBit true
      (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    (originalLabelColumn p hg b.cube.support b.cube.rightBit b.cube.leftBit false
      (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    W V₁ V₂ X₁ X₂ K d x.2

end

theorem orientedCubeFirstBlock_input_transfer
    (W V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ : ℝ) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤M₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    ∃ C : ℝ,0≤C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ,ℂ)) (K ell B F Ymax : ℝ),
      0<K → 0<ell → 0<B → 0<F →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      C*Ymax^deltaLoss*
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F true b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F false b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by
  obtain ⟨C,hC,hfirst⟩ := first_passage_full_uniform_input_family W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F Ymax hK hell hB hF hΨ₁ hΨ₂ hw ha hYmax hsf hs0 hmap hT0 hT
  by_cases hempty : blocks=∅
  · subst blocks
    simp only [Finset.sum_empty,mul_zero,norm_zero,Real.sqrt_zero,le_refl]
  have hne : blocks.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let E₁ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)
  let E₂ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)
  let v := fun b => w b*globalCubeCoefficient p K ell B F true b
  have hv (b) (hb : b∈blocks) : 0≤v b := mul_nonneg (hw b hb)
    (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hE₁ (b) : 0≤E₁ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hE₂ (b) : 0≤E₂ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hden : 0<ell*B^2*F := by positivity
  have hYmax0 : 0≤Ymax := by
    obtain ⟨b,hb⟩ := hne
    exact (globalPooledRowScale_pos K ell B F hK hell hB hF _).le.trans (hYmax b hb)
  have hpref : 0≤C*Ymax^deltaLoss := mul_nonneg hC (Real.rpow_nonneg hYmax0 deltaLoss)
  have hpoint (b) (hb : b∈blocks) : (ell*B^2*F)⁻¹*
      ‖orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      (C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
    have hFB : Disjoint (globalCubePool pool b) b.cube.support := by
      apply Finset.disjoint_left.mpr
      intro i hi hiB
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB)
    have hX₁ := globalCubeColumnScale_pos p hp ell hell true b
    have hX₂ := globalCubeColumnScale_pos p hp ell hell false b
    have hD := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor
    have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalFirstIndex p true (b.withCommon ∅))
    have hswapD := FirstPassCubeLabels.dilationLabel_swap p b.cube.support
      (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit
    have hh := hfirst p hp hinj hcop hg hc hpr (globalCubePool pool b) b.cube.support hFB
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit b.cube.support_pos
      Ψ₁ Ψ₂ m₁ m₂ (fun A => g₁ (columnLog p (globalCubeColumnScale p ell true b) A))
      (fun A => g₂ (columnLog p (globalCubeColumnScale p ell false b) A))
      (fun A hA => hΨ₁ _) (fun A hA => hΨ₂ _)
      _ _ hX₁ hX₂ K hK (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) (primeSubsetGenerator_ne_zero _ _)
      (s b) (T b) (a b) (w b) (globalFirstPooledRow p K ell B F true (b.withCommon ∅))
      (hw b hb) hY.le (hsf b hb) (hs0 b hb) (by simpa only [hswapD] using hmap b hb) (hT0 b hb) (hT b hb) (ha b hb)
    rw [firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit true,
      firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit false,
      FirstPassCubeLabels.cubeActiveSupport_swap b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit] at hh
    have hscl := globalCube_first_scalar_bound p hp K ell B F hK hell hB hF b
    have hpow := Real.rpow_le_rpow hY.le (hYmax b hb) hδ.le
    have hmul := mul_le_mul_of_nonneg_left hh
      (show 0≤(ell*B^2*F)⁻¹*(primeProductNorm p b.firstDivisor)⁻¹ by positivity)
    simp only [orientedCubeFirstBlock,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_of_nonneg hD.le,←mul_assoc]
    apply hmul.trans
    calc
      _ = ((ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
          ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
            (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))*
          (w b*C*(globalFirstPooledRow p K ell B F true (b.withCommon ∅))^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by dsimp [E₁,E₂,globalCubeInputFamilyEnergy];ring
      _ ≤ globalCubeCoefficient p K ell B F true b*(w b*C*Ymax^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        apply mul_le_mul hscl
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hw b hb) hC))
          (mul_nonneg (mul_nonneg (hw b hb) hC) (Real.rpow_nonneg hY.le _))
          (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
      _ = _ := by dsimp [v];ring
  rw [norm_mul, norm_inv]
  have hn : ‖(ell*B^2*F : ℂ)‖=ell*B^2*F := by
    norm_cast
    exact abs_of_pos hden
  rw [hn]
  calc
    _ ≤ (ell*B^2*F)⁻¹*∑ b∈blocks,‖orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hden.le)
    _ ≤ ∑ b∈blocks,(C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ = (C*Ymax^deltaLoss)*∑ b∈blocks,Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Real.sqrt_mul (hv b hb),Real.sqrt_mul (hv b hb)]
      have hs := Real.sq_sqrt (hv b hb)
      calc
        _ = (C*Ymax^deltaLoss)*(Real.sqrt (v b))^2*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by rw [hs]
        _ = _ := by ring
    _ ≤ (C*Ymax^deltaLoss)*(Real.sqrt (∑ b∈blocks,v b*E₁ b)*Real.sqrt (∑ b∈blocks,v b*E₂ b)) :=
      mul_le_mul_of_nonneg_left (by
        have hcauchy := Real.sum_sqrt_mul_sqrt_le blocks.attach
          (fun b => mul_nonneg (hv b.val b.property) (hE₁ b.val))
          (fun b => mul_nonneg (hv b.val b.property) (hE₂ b.val))
        simpa only [Finset.sum_attach (f := fun b => Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b)),
          Finset.sum_attach (f := fun b => v b*E₁ b),Finset.sum_attach (f := fun b => v b*E₂ b)] using hcauchy) hpref
    _ = _ := by simp only [v,E₁,E₂,globalCubeCoefficient_side,mul_assoc]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem orientedTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H U : ℝ),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := orientedCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  obtain ⟨windows₁,C₁,Cd₁,Ct₁,hC₁,hCd₁,hCt₁,hwc₁,hws₁,hwb₁,hleft⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₁ V₁ M₁ hM₁ hg₁ true A J N
  obtain ⟨windows₂,C₂,Cd₂,Ct₂,hC₂,hCd₂,hCt₂,hwc₂,hws₂,hwb₂,hright⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₂ V₂ M₂ hM₂ hg₂ false A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCfirst,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H U
    hΓ hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  have hB0 : 0<B := by linarith
  let T := fun b => globalCubeFirstTargets p b (s b)
  have hT0 (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) : z≠0 :=
    globalCubeFirstTargets_ne_zero p hp b (s b) (hsf b hb) (hs0 b hb) z hz
  have hT (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) :=
    globalCubeFirstTargets_norm_bound p hp b (s b) K ell B F hK hell hB0 hF
      (hb₁ b hb) (hb₂ b hb) (hf b hb) (hh b hb) z hz
  have hTc (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F false (b.withCommon ∅) := by
    rw [globalFirstPooledRow_side]
    exact hT b hb z hz
  have hblock := hfirst p hp hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F
    (globalFirstRowCap K ell B F) hK hell hB0 hF hΨ₁ hΨ₂ (fun b hb => (hw b hb).1) ha
    (fun b hb => globalFirstPooledRow_le_cap p hp K ell B F hK hell hB0 hF b (hadm b hb) (hb₁ b hb) (hb₂ b hb))
    hsf hs0 (fun b _ x hx => globalCubeFirstTargets_mem p b (s b) x hx) hT0 hT
  have hl := hleft p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₁ m₁ T
    hΓ hw hK hell hB hF hH hU hellU1 hadm hΨ₁ hb₁ hb₂ hT hT0
  have hr := hright p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₂ m₂ T
    hΓ hw hK hell hB hF hH hU hellU2 hadm hΨ₂ hb₁ hb₂ hTc hT0
  have hprefix : 0≤Cfirst*(globalFirstRowCap K ell B F)^deltaLoss :=
    mul_nonneg hCfirst (Real.rpow_nonneg (globalFirstRowCap_pos K ell B F hK hell hB0 hF).le _)
  exact hblock.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hprefix)
    (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (mul_nonneg hprefix (Real.sqrt_nonneg _)))

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
local instance : BorelSpace EuclideanSpatial := ⟨rfl⟩

def euclideanC1cToH1 (f : C1c (E := EuclideanSpatial)) :
    h1 (E := EuclideanSpatial) («μ» := (volume : Measure EuclideanSpatial)) := by
  let gr := graph (E := EuclideanSpatial) («μ» := (volume : Measure EuclideanSpatial))
  refine ⟨gr f,?_⟩
  exact (LinearMap.range gr).le_topologicalClosure ⟨f,rfl⟩

lemma euclideanC1cToH1_norm (f : C1c (E := EuclideanSpatial)) :
    ‖euclideanC1cToH1 f‖=max ‖toL2 («μ» := volume) f‖ ‖toL2Grad («μ» := volume) f‖ := rfl

lemma euclideanC1c_supported_range (K : Set EuclideanSpatial) (hK : MeasurableSet K)
    (f : C1c (E := EuclideanSpatial)) (hf : Function.support f.1⊆K) :
    toL2 («μ» := volume) f∈LinearMap.range
      (Lp.extendByZeroₗᵢ («μ» := (volume : Measure EuclideanSpatial)) (p := (2:ℝ≥0∞)) hK).toLinearMap := by
  have hmem := memLp_of_mem_C1c («μ» := (volume : Measure EuclideanSpatial)) f.2
  have hres : MemLp f.1 2 (volume.restrict K) := hmem.mono_measure Measure.restrict_le_self
  refine ⟨hres.toLp f.1,?_⟩
  apply Lp.ext
  have hext := Lp.extendByZeroₗᵢ_ae_eq («μ» := (volume : Measure EuclideanSpatial)) hK (hres.toLp f.1)
  have hr : ∀ᵐx ∂(volume : Measure EuclideanSpatial),x∈K→hres.toLp f.1 x=f.1 x :=
    (ae_restrict_iff' hK).mp hres.coeFn_toLp
  have hg : (toL2 («μ» := volume) f : EuclideanSpatial→ℝ)=ᵐ[volume]f.1 := hmem.coeFn_toLp
  filter_upwards [hext,hr,hg] with x hx hrx hgx
  simp only [LinearIsometry.coe_toLinearMap]
  rw [hx,hgx]
  by_cases hxm : x∈K
  · simpa only [Set.indicator_of_mem hxm] using hrx hxm
  · rw [Set.indicator_of_notMem hxm]
    symm
    by_contra hne
    exact hxm (hf hne)

def euclideanC1cToSupportedH1 (K : Set EuclideanSpatial) (hK : MeasurableSet K)
    (f : C1c (E := EuclideanSpatial)) (hf : Function.support f.1⊆K) :
    h1On (E := EuclideanSpatial) K hK :=
  ⟨euclideanC1cToH1 f,euclideanC1c_supported_range K hK f hf⟩

lemma compact_clm_closedBall {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace ℝ V] [NormedSpace ℝ W] (T : V →L[ℝ] W)
    (hT : IsCompactOperator T) (R : ℝ) : IsCompact (closure (T '' Metric.closedBall 0 R)) :=
  IsCompactOperator.isCompact_closure_image_closedBall (f := T.toLinearMap) hT R

theorem euclidean_C1c_family_precompact (K : Set EuclideanSpatial) (hK : IsCompact K)
    (family : Set (C1c (E := EuclideanSpatial))) (R : ℝ)
    (hsupp : ∀f∈family,Function.support f.1⊆K)
    (hmass : ∀f∈family,‖toL2 («μ» := volume) f‖≤R)
    (hgrad : ∀f∈family,‖toL2Grad («μ» := volume) f‖≤R) :
    IsCompact (closure (toL2 («μ» := (volume : Measure EuclideanSpatial)) '' family)) := by
  let hKm := hK.measurableSet
  have hc := compact_clm_closedBall
    (V := h1On (E := EuclideanSpatial) K hKm)
    (W := Lp ℝ 2 (volume : Measure EuclideanSpatial))
    (h1OnToL2 (E := EuclideanSpatial) K hKm)
    (isCompactOperator_h1OnToL2 (E := EuclideanSpatial) hK hKm) R
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨euclideanC1cToSupportedH1 K hKm f (hsupp f hf),?_,rfl⟩
  have hn : ‖euclideanC1cToSupportedH1 K hKm f (hsupp f hf)‖≤R :=
    max_le (hmass f hf) (hgrad f hf)
  simpa only [Metric.mem_closedBall,dist_zero_right (euclideanC1cToSupportedH1 K hKm f (hsupp f hf))] using hn

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal InnerProductSpace

namespace CubicEisenstein

abbrev KernelFundamentalVolume : Measure HyperbolicSpace :=
  hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)

abbrev KernelGradientL2 := Lp (EuclideanSpace ℂ (Fin 3)) 2 KernelFundamentalVolume

lemma kernelTestPartial_continuous (f : kernelSmoothTests) (j : Fin 3) :
    Continuous (fun w => kernelTestPartial f w j) := by
  rw [continuous_iff_continuousAt]
  intro w
  exact (((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).continuousAt_fderiv
    (by simp)).clm_apply continuousAt_const).comp
      hyperbolicEuclideanCoordinates_continuous.continuousAt

lemma kernelGradientAt_continuous (f : kernelSmoothTests) :
    Continuous (fun w => kernelGradientAt w f) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  exact (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
    (kernelTestPartial_continuous f j)

lemma kernelGradientAt_memLp (f : kernelSmoothTests) :
    MemLp (fun w => kernelGradientAt w f) 2 KernelFundamentalVolume := by
  apply (memLp_two_iff_integrable_sq_norm
    (kernelGradientAt_continuous f).aestronglyMeasurable).mpr
  have hh := (quotient_projection_measurePreserving globalKubotaKernel).integrable_comp_of_integrable
    (kernelQuotientEnergyDensity_integrable f)
  have he : (fun w => kernelQuotientEnergyDensity f (integralOrbitProjection globalKubotaKernel w))=
      kernelTestEnergyDensity f := rfl
  dsimp only [Function.comp_def] at hh
  rw [he] at hh
  simpa only [kernelGradientAt_norm_sq] using hh

def kernelGradientToL2 (f : kernelSmoothTests) : KernelGradientL2 :=
  (kernelGradientAt_memLp f).toLp (fun w => kernelGradientAt w f)

lemma kernelGradientToL2_coe (f : kernelSmoothTests) :
    (kernelGradientToL2 f : HyperbolicSpace → EuclideanSpace ℂ (Fin 3))=ᵐ[KernelFundamentalVolume]
      fun w => kernelGradientAt w f := (kernelGradientAt_memLp f).coeFn_toLp

lemma kernelGradientToL2_inner (f g : kernelSmoothTests) :
    inner ℂ (kernelGradientToL2 f) (kernelGradientToL2 g)=kernelDirichletForm f g := by
  rw [L2.inner_def,kernelDirichletForm,integralQuotientVolume_integral _ _
    (kernelDirichletPairDensity_integrable f g).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [kernelGradientToL2_coe f,kernelGradientToL2_coe g] with w hf hg
  rw [hf,hg,kernelDirichletPairDensity_coordinate]

lemma kernelGradientToL2_norm_sq (f : kernelSmoothTests) :
    ‖kernelGradientToL2 f‖^2=kernelDirichletEnergy f := by
  have hh := kernelGradientToL2_inner f f
  rw [inner_self_eq_norm_sq_to_K,kernelDirichletForm_self] at hh
  rw [RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow] at hh
  exact Complex.ofReal_injective hh

def kernelGradientLinear : kernelSmoothTests →ₗ[ℂ] KernelGradientL2 where
  toFun := kernelGradientToL2
  map_add' f g := by
    apply Lp.ext
    filter_upwards [kernelGradientToL2_coe (f+g),kernelGradientToL2_coe f,
      kernelGradientToL2_coe g,Lp.coeFn_add (kernelGradientToL2 f) (kernelGradientToL2 g)]
      with w hfg hf hg hadd
    simp only [hfg,hadd,Pi.add_apply,hf,hg,map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [kernelGradientToL2_coe (c•f),kernelGradientToL2_coe f,
      Lp.coeFn_smul c (kernelGradientToL2 f)] with w hcf hf hsmul
    simp only [RingHom.id_apply,hcf,hsmul,Pi.smul_apply,hf,map_smul]

def kernelInitialGradientGraph : Submodule ℂ (KernelQuotientL2 × KernelGradientL2) :=
  LinearMap.range (kernelSmoothTestsToL2.prod kernelGradientLinear)

lemma kernelInitialGradientGraph_unique (x : KernelQuotientL2 × KernelGradientL2)
    (hx : x∈kernelInitialGradientGraph) (hz : x.1=0) : x.2=0 := by
  obtain ⟨f,hf⟩ := hx
  have hf1 : kernelSmoothTestsToL2 f=x.1 := congrArg Prod.fst hf
  have hf2 : kernelGradientLinear f=x.2 := congrArg Prod.snd hf
  have hzero : f=0 := kernelSmoothTestsToL2_injective (by
    simpa only [map_zero] using hf1.trans hz)
  rw [hzero,map_zero] at hf2
  exact hf2.symm

def kernelInitialGradient : KernelQuotientL2 →ₗ.[ℂ] KernelGradientL2 :=
  kernelInitialGradientGraph.toLinearPMap

lemma kernelInitialGradient_graph :
    kernelInitialGradient.graph=kernelInitialGradientGraph :=
  Submodule.toLinearPMap_graph_eq _ kernelInitialGradientGraph_unique

lemma kernelInitialGradient_dense_domain :
    Dense (kernelInitialGradient.domain : Set KernelQuotientL2) := by
  apply kernelSmoothTestsToL2_dense.mono
  rintro _ ⟨f,rfl⟩
  apply LinearPMap.mem_domain_of_mem_graph
  rw [kernelInitialGradient_graph]
  exact ⟨f,rfl⟩

end CubicEisenstein

end

end OAI

end Source176

/- Original source: OAI/NumberTheory/DirichletL/Eisenstein/LocalCutoffs.lean; sha256: 1791d6dd574ee0d8288d77b087b9e2d6f485dc2beb401a600846eba6cdc0a316 -/
section Source177
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology SchwartzMap LineDeriv ContDiff

structure PositiveChartCutoff where
  func : EuclideanSpatial → ℝ
  smooth : ContDiff ℝ ∞ func
  compact : HasCompactSupport func
  positive : tsupport func ⊆ {p | 0 < p 2}

lemma kernelChartCutoff_exists (p : EuclideanSpatial) (hp : 0<p 2) :
    ∃χ : PositiveChartCutoff, χ.func p=1 ∧ Set.range χ.func ⊆ Set.Icc 0 1 ∧
      Set.InjOn (integralOrbitProjection globalKubotaKernel ∘ euclideanToHyperbolic)
        (tsupport χ.func) := by
  obtain ⟨U,hU,hw,hUinj⟩ :=
    kernelQuotient_localHomeomorph.isLocallyInjective (euclideanToHyperbolic p)
  have hn : {q : EuclideanSpatial | 0<q 2} ∩ euclideanToHyperbolic ⁻¹' U ∈ 𝓝 p :=
    inter_mem ((isOpen_lt continuous_const (by fun_prop)).mem_nhds hp)
      ((euclideanToHyperbolic_contMDiffAt p hp).continuousAt (hU.mem_nhds hw))
  obtain ⟨χ,hχ,hcomp,hsmooth,hrange,hvalue⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hn
  refine ⟨⟨χ,hsmooth,hcomp,fun q hq => (hχ hq).1⟩,hvalue,hrange,?_⟩
  intro q hq r hr heq
  have hwEq := hUinj (hχ hq).2 (hχ hr).2 heq
  have hc := congrArg hyperbolicEuclideanCoordinates hwEq
  simpa only [hyperbolicEuclideanCoordinates_toHyperbolic _ (hχ hq).1,
    hyperbolicEuclideanCoordinates_toHyperbolic _ (hχ hr).1] using hc

def kernelLocalizedField (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) : ℂ := χ.func p • kernelTestField f p

lemma kernelLocalizedField_compact (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    HasCompactSupport (kernelLocalizedField χ f) := χ.compact.smul_right

lemma kernelLocalizedField_tsupport (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    tsupport (kernelLocalizedField χ f) ⊆ tsupport χ.func := tsupport_smul_subset_left _ _

lemma kernelLocalizedField_smooth (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    ContDiff ℝ ∞ (kernelLocalizedField χ f) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : 0 < p 2
  · exact χ.smooth.contDiffAt.smul (kernelTestField_contDiffAt f p hp)
  · have hn : p ∉ tsupport χ.func := fun h => hp (χ.positive h)
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : EuclideanSpatial => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [hz] with q hq
    simp only [kernelLocalizedField,hq,Pi.zero_apply,zero_smul]

def kernelLocalizedSchwartz (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    𝓢(EuclideanSpatial,ℂ) :=
  (kernelLocalizedField_compact χ f).toSchwartzMap (kernelLocalizedField_smooth χ f)

lemma kernelLocalizedSchwartz_coe (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    (kernelLocalizedSchwartz χ f : EuclideanSpatial → ℂ)=kernelLocalizedField χ f := rfl

def kernelLocalizedH1 (χ : PositiveChartCutoff) (f : kernelSmoothTests) : EuclideanH1 := by
  let g := kernelLocalizedSchwartz χ f
  let v := WithLp.toLp 2 (fun j => (∂_{euclideanCoordinateVector j} g).toLp 2 volume)
  refine ⟨WithLp.toLp 2 (g.toLp 2 volume,v),?_⟩
  change (g.toLp 2 volume,v)∈euclideanWeakGradientGraph
  exact schwartz_mem_euclideanWeakGradientGraph g

lemma kernelLocalizedH1_embedding (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    euclideanH1Embedding (kernelLocalizedH1 χ f)=
      (kernelLocalizedSchwartz χ f).toLp 2 volume := rfl

lemma kernelLocalizedH1_gradient (χ : PositiveChartCutoff) (f : kernelSmoothTests) (j : Fin 3) :
    euclideanH1Gradient (kernelLocalizedH1 χ f) j=
      (∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).toLp 2 volume := rfl

lemma kernelLocalizedField_fderiv (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0 < p 2) (u : EuclideanSpatial) :
    fderiv ℝ (kernelLocalizedField χ f) p u=
      χ.func p • fderiv ℝ (kernelTestField f) p u+
        (fderiv ℝ χ.func p u) • kernelTestField f p := by
  change fderiv ℝ (χ.func • kernelTestField f) p u=_
  rw [fderiv_smul (χ.smooth.differentiable (by simp)).differentiableAt
    ((kernelTestField_contDiffAt f p hp).differentiableAt (by simp))]
  rfl

lemma complex_norm_add_sq_le (z w : ℂ) :
    ‖z+w‖^2 ≤ 2*‖z‖^2+2*‖w‖^2 := by
  have hh := norm_add_le z w
  have hn := norm_nonneg (z+w)
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

lemma kernelLocalizedField_energy_bound (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    (p 2)^2*(∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) ≤
    2*(χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)+
      2*(p 2)^2*(∑j : Fin 3,‖fderiv ℝ χ.func p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)*‖kernelTestField f p‖^2 := by
  have hsum : (∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) ≤
      ∑j : Fin 3,(2*(χ.func p)^2*‖fderiv ℝ (kernelTestField f) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2+
        2*‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2*
          ‖kernelTestField f p‖^2) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [kernelLocalizedField_fderiv χ f p hp]
    simpa only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,mul_assoc] using
      complex_norm_add_sq_le
        (χ.func p • fderiv ℝ (kernelTestField f) p (EuclideanSpace.basisFun (Fin 3) ℝ j))
        (fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j) • kernelTestField f p)
  have he : kernelTestEnergyDensity f (euclideanToHyperbolic p)=
      (p 2)^2*∑j : Fin 3,‖fderiv ℝ (kernelTestField f) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2 := by
    rw [kernelTestEnergyDensity_eq_partials]
    have hc := hyperbolicEuclideanCoordinates_toHyperbolic p hp
    have hv : hyperbolicHeight (euclideanToHyperbolic p)=p 2 := congrArg (fun q : EuclideanSpatial => q 2) hc
    simp only [hv,kernelTestPartial,hc]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg (p 2))
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,
    mul_add,mul_assoc,mul_left_comm,mul_comm] using hh

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff ENNReal

def kernelEuclideanProjection : EuclideanSpatial → KernelQuotient :=
  integralOrbitProjection globalKubotaKernel ∘ euclideanToHyperbolic

lemma kernelEuclideanProjection_measurable : Measurable kernelEuclideanProjection :=
  (measurable_integralOrbitProjection _).comp euclideanToHyperbolic_measurable

lemma euclideanToHyperbolic_measurePreserving_on (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (_hpos : S⊆euclideanUpperHalf) :
    MeasurePreserving euclideanToHyperbolic (hyperbolicEuclideanVolume.restrict S)
      (hyperbolicVolume.restrict (hyperbolicEuclideanCoordinates ⁻¹' S)) := by
  have hU : MeasurableSet (hyperbolicEuclideanCoordinates ⁻¹' S) :=
    hyperbolicEuclideanCoordinates_continuous.measurable hS
  have hset : euclideanToHyperbolic ⁻¹' (hyperbolicEuclideanCoordinates ⁻¹' S)=ᵐ[hyperbolicEuclideanVolume]S := by
    filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
    simp only [Set.mem_preimage,hyperbolicEuclideanCoordinates_toHyperbolic p hp]
  refine ⟨euclideanToHyperbolic_measurable,?_⟩
  rw [hyperbolicVolume,Measure.restrict_map euclideanToHyperbolic_measurable hU,
    Measure.restrict_congr_set hset]

lemma euclideanToHyperbolic_image_positive (S : Set EuclideanSpatial)
    (hpos : S⊆euclideanUpperHalf) :
    euclideanToHyperbolic '' S=hyperbolicEuclideanCoordinates ⁻¹' S := by
  ext w
  constructor
  · rintro ⟨p,hp,rfl⟩
    simpa only [Set.mem_preimage,hyperbolicEuclideanCoordinates_toHyperbolic p (hpos hp)] using hp
  · intro hw
    exact ⟨hyperbolicEuclideanCoordinates w,hw,euclideanToHyperbolic_coordinates w⟩

lemma kernelEuclideanProjection_measurePreserving_on (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) :
    MeasurePreserving kernelEuclideanProjection (hyperbolicEuclideanVolume.restrict S)
      ((integralQuotientVolume globalKubotaKernel).restrict (kernelEuclideanProjection '' S)) := by
  have hU : MeasurableSet (hyperbolicEuclideanCoordinates ⁻¹' S) :=
    hyperbolicEuclideanCoordinates_continuous.measurable hS
  have hi : Set.InjOn (integralOrbitProjection globalKubotaKernel)
      (hyperbolicEuclideanCoordinates ⁻¹' S) := by
    intro u hu v hv heq
    have hh := hinj hu hv (by simpa only [kernelEuclideanProjection,Function.comp_apply,
      euclideanToHyperbolic_coordinates] using heq)
    have hh' := congrArg euclideanToHyperbolic hh
    simpa only [euclideanToHyperbolic_coordinates] using hh'
  have hcomp := (kernelProjection_measurePreserving_on _ hU hi).comp
    (euclideanToHyperbolic_measurePreserving_on S hS hpos)
  have himage : integralOrbitProjection globalKubotaKernel ''
      (hyperbolicEuclideanCoordinates ⁻¹' S)=kernelEuclideanProjection '' S := by
    rw [←euclideanToHyperbolic_image_positive S hpos,Set.image_image]
    rfl
  rwa [himage] at hcomp

lemma kernelEuclideanProjection_integral (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient → ℝ)
    (hg : AEStronglyMeasurable g (integralQuotientVolume globalKubotaKernel)) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)=
      ∫q in kernelEuclideanProjection '' S,g q∂integralQuotientVolume globalKubotaKernel := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hh := hg.mono_measure (Measure.restrict_le_self (s := kernelEuclideanProjection '' S))
  rw [←hm.map_eq] at hh ⊢
  exact (integral_map hm.measurable.aemeasurable hh).symm

lemma kernelEuclideanProjection_integral_le (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient → ℝ)
    (hg : Integrable g (integralQuotientVolume globalKubotaKernel)) (hgn : ∀q,0≤g q) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)≤
      ∫q,g q∂integralQuotientVolume globalKubotaKernel := by
  rw [kernelEuclideanProjection_integral S hS hpos hinj g hg.aestronglyMeasurable]
  exact setIntegral_le_integral hg (Eventually.of_forall hgn)

lemma kernelLocalEnergy_le (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (f : kernelSmoothTests) :
    (∫p in S,kernelTestEnergyDensity f (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume)≤
      kernelDirichletEnergy f := by
  exact kernelEuclideanProjection_integral_le S hS hpos hinj _
    (kernelQuotientEnergyDensity_integrable f) (kernelQuotientEnergyDensity_nonneg f)

lemma kernelSmoothTestsToL2_norm_sq (f : kernelSmoothTests) :
    ‖kernelSmoothTestsToL2 f‖^2=
      ∫q,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel := by
  calc
    ‖kernelSmoothTestsToL2 f‖^2=inner ℝ (kernelSmoothTestsToL2 f) (kernelSmoothTestsToL2 f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫q,inner ℝ (kernelSmoothTestsToL2 f q) (kernelSmoothTestsToL2 f q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(kernelSmoothTests_memLp f).coeFn_toLp] with q hq
      change inner ℝ (((kernelSmoothTests_memLp f).toLp f.1) q)
        (((kernelSmoothTests_memLp f).toLp f.1) q)=_
      rw [hq,real_inner_self_eq_norm_sq]

lemma kernelLocalMass_le (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (f : kernelSmoothTests) :
    (∫p in S,‖kernelTestField f p‖^2∂hyperbolicEuclideanVolume)≤‖kernelSmoothTestsToL2 f‖^2 := by
  rw [kernelSmoothTestsToL2_norm_sq]
  exact kernelEuclideanProjection_integral_le S hS hpos hinj _
    (kernelSmoothTests_memLp f).norm.integrable_sq (fun _ => sq_nonneg _)

lemma euclideanVolume_le_heightCube_hyperbolic (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf) (b : ℝ) (hb : 0≤b)
    (hheight : ∀p∈S,p 2≤b) :
    volume.restrict S≤ENNReal.ofReal (b^3) • hyperbolicEuclideanVolume.restrict S := by
  have hw : hyperbolicEuclideanVolume.restrict S=(volume.restrict S).withDensity hyperbolicDensity := by
    rw [hyperbolicEuclideanVolume,MeasureTheory.restrict_withDensity hS,
      Measure.restrict_restrict hS,Set.inter_eq_left.mpr hpos]
  rw [hw]
  have hbd : (1 : EuclideanSpatial→ℝ≥0∞)≤ᵐ[volume.restrict S]
      ENNReal.ofReal (b^3) • hyperbolicDensity := by
    filter_upwards [ae_restrict_mem hS] with p hp
    have ht : 0<p 2 := hpos hp
    have hpow : (p 2)^3≤b^3 := pow_le_pow_left₀ ht.le (hheight p hp) 3
    have hreal : 1≤b^3*((p 2)^3)⁻¹ := by
      calc
        1=(p 2)^3*((p 2)^3)⁻¹ := (mul_inv_cancel₀ (pow_ne_zero _ ht.ne')).symm
        _ ≤b^3*((p 2)^3)⁻¹ := mul_le_mul_of_nonneg_right hpow (by positivity)
    change (1 : ℝ≥0∞)≤ENNReal.ofReal (b^3)*ENNReal.ofReal (((p 2)^3)⁻¹)
    rw [←ENNReal.ofReal_mul (pow_nonneg hb 3)]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hreal
  simpa only [MeasureTheory.withDensity_one,MeasureTheory.withDensity_smul _ hyperbolicDensity_measurable] using
    (MeasureTheory.withDensity_mono hbd)

lemma kernelEuclideanProjection_volume_integral_le (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (b : ℝ) (hb : 0≤b)
    (hheight : ∀p∈S,p 2≤b) (g : KernelQuotient→ℝ)
    (hg : Integrable g (integralQuotientVolume globalKubotaKernel)) (hgn : ∀q,0≤g q) :
    (∫p in S,g (kernelEuclideanProjection p))≤
      b^3*∫q,g q∂integralQuotientVolume globalKubotaKernel := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hgi := hm.integrable_comp_of_integrable hg.integrableOn
  have hh := integral_mono_measure
    (euclideanVolume_le_heightCube_hyperbolic S hS hpos b hb hheight)
    (Eventually.of_forall (fun p => hgn (kernelEuclideanProjection p)))
    (hgi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure,ENNReal.toReal_ofReal (pow_nonneg hb 3)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (kernelEuclideanProjection_integral_le S hS hpos hinj g hg hgn) (pow_nonneg hb 3))

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

theorem completed_scaled_shape (ε k y H c B : ℝ) (hε : 0≤ε) (hk : 0<k)
    (hy : 0<y) (hH : 0<H) (hc : 0<c) (hcB : c≤B) (hB : 1≤B) :
    (k*(c*y))^ε*(k+c*y)/H≤B^(ε+1)*((k*y)^ε*(k+y)/H) := by
  have hB0 : 0<B := by linarith
  have hp : (k*(c*y))^ε≤B^ε*(k*y)^ε := by
    rw [show k*(c*y)=c*(k*y) by ring,Real.mul_rpow hc.le (mul_pos hk hy).le]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hc.le hcB hε) (by positivity)
  have hs : k+c*y≤B*(k+y) := by nlinarith
  calc
    _ ≤ (B^ε*(k*y)^ε)*(B*(k+y))/H :=
      div_le_div_of_nonneg_right (mul_le_mul hp hs (by positivity) (by positivity)) hH.le
    _ = (B^ε*B)*((k*y)^ε*(k+y)/H) := by ring
    _ = _ := by rw [←Real.rpow_add_one hB0.ne']

theorem completedBranchScale_div {ι : Type*} [Fintype ι]
    (K X c : ℝ) (I F Q : Ideal O) (P : ι→Ideal O) (e : ι→Fin 3) :
    completedBranchScale K (X/c) I F Q P e=c*completedBranchScale K X I F Q P e := by
  unfold completedBranchScale
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem completed_reflected_fiber_fixed_scale
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q B : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hB : 1≤B) :
    ∃C : ℝ,0<C ∧ ∀K X c : ℝ,1≤K → 1≤X → 0<c → c≤B →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i),
      Pairwise (fun i j => IsCoprime (P i) (P j)) →
      (∀i,P i∣I*Q) → (∀i,¬P i∣rowResidualPart I Q) →
    ∀e : ι→Fin 3,∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀J∈S i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀J∈T i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ,(∀i k,‖σ i k‖≤1) →
      (∑k : idealRange (completedResidualScale K I Q),‖∑'i : ℕ×ℕ×ℕ,
        reflectedBranchBlock P hg (fun i => completedLocalExponent I F (P i)) e W
          (completedResidualScale K I Q) (completedBranchScale K (X/c) I F Q P e) ρ q S T η σ i k‖^2)
        ≤C*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨C,hC,h⟩ := completed_reflected_branch_series W a b ha hsupp hW deltaLoss ρ q hδ hρ hq
  refine ⟨C*B^(2*deltaLoss+1),by positivity,?_⟩
  intro K X c hK hX hc hcB I F Q hI hQ hIK hk ι _ P _ hg hcop hpool hres e S T hS hT η hη σ hσ
  have hn (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj (v : Fin 3) := hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i))
    (fun i => completedLocalExponent I F (P i)) e v)
  have hp := hn (∏i,P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hk0 : 0<completedResidualScale K I Q := by linarith
  have hy : 0<completedBranchScale K X I F Q P e := by
    unfold completedBranchScale
    have hX0 : 0<X := by linarith
    have hd := hj 1
    have he := hj 2
    positivity
  rw [completedBranchScale_div]
  have hb := (h (completedResidualScale K I Q) (c*completedBranchScale K X I F Q P e)
    hk (mul_pos hc hy) P hg (fun i => completedLocalExponent I F (P i)) e S T hS hT η hη σ hσ).2
  have hs := completed_scaled_shape (2*deltaLoss) (completedResidualScale K I Q)
    (completedBranchScale K X I F Q P e) _ c B (by positivity) hk0 hy
    (mul_pos (hj 0) (hj 2)) hc hcB hB
  have hcst := completed_actual_fiber_cost deltaLoss K X hδ.le hK hX I F Q hI hQ hIK P hcop hpool hres e
  have hh := hs.trans (mul_le_mul_of_nonneg_left hcst (by positivity : 0≤B^(2*deltaLoss+1)))
  apply hb.trans
  have hfinal := mul_le_mul_of_nonneg_left hh hC.le
  convert hfinal using 1 <;> (try dsimp [completedResidualScale,completedBranchScale]) <;> ring

end

open ActualEisensteinCubic CanonicalQuadraticSieve

structure ReflectedBranchData (levelBound K : ℝ) (I F Q : Ideal O) where
  levelScale : ℝ
  levelScale_pos : 0<levelScale
  levelScale_le : levelScale≤levelBound
  primes : Finset (Ideal O)
  maximal : ∀p : primes,p.val.IsMaximal
  good : ∀p : primes,lambda∉p.val
  coprime : Pairwise (fun p r : primes => IsCoprime p.val r.val)
  divides : ∀p : primes,p.val∣I*Q
  nonresidual : ∀p : primes,¬p.val∣rowResidualPart I Q
  label : primes→Fin 3
  nColumns : (ℕ×ℕ×ℕ)→Finset (Ideal O)
  bColumns : (ℕ×ℕ×ℕ)→Finset (Ideal O)
  nBounds : ∀i,∀J∈nColumns i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2
  bBounds : ∀i,∀J∈bColumns i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1
  amplitude : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ
  amplitude_bound : ∀i,∀n∈nColumns i,∀b∈bColumns i,‖amplitude i n b‖≤1
  rowPhase : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ
  rowPhase_bound : ∀i k,‖rowPhase i k‖≤1

namespace ReflectedBranchData

def value {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedBranchData levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ := by
  letI : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact ∑'i : ℕ×ℕ×ℕ,reflectedBranchBlock (fun p : d.primes => p.val) d.good
    (fun p => completedLocalExponent I F p.val) d.label W
    (completedResidualScale K I Q) (completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes => p.val) d.label)
    ρ q d.nColumns d.bColumns d.amplitude d.rowPhase i k

theorem energy_bound
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀K X : ℝ,1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q → ∀d : ReflectedBranchData levelBound K I F Q,
      (∑k,‖d.value W X ρ q k‖^2)≤
        C*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨C,hC,h⟩ := completed_reflected_fiber_fixed_scale W a b ha hsupp hW deltaLoss ρ q levelBound hδ hρ hq hlevel
  refine ⟨C,hC,?_⟩
  intro K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact h K X d.levelScale hK hX d.levelScale_pos d.levelScale_le I F Q hI hQ hIK hk _ d.good d.coprime d.divides d.nonresidual
    d.label d.nColumns d.bColumns d.nBounds d.bBounds d.amplitude d.amplitude_bound
    d.rowPhase d.rowPhase_bound

end ReflectedBranchData

structure ReflectedFiberData (rays : ℕ) (levelBound K : ℝ) (I F Q : Ideal O) where
  pool : Finset (Ideal O)
  maximal : ∀p : pool,p.val.IsMaximal
  divides : ∀p : pool,p.val∣I*Q
  branch : (Fin rays×(pool→Fin 6))→ReflectedBranchData levelBound K I F Q
  weight : (Fin rays×(pool→Fin 6))→ℂ
  weight_bound : ∀b,‖weight b‖≤1

namespace ReflectedFiberData

def value {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ :=
  ∑b,d.weight b*(d.branch b).value W X ρ q k

theorem finite_energy_bound {κ τ : Type*} [Fintype κ] [Fintype τ]
    (f : τ→κ→ℂ) (w : τ→ℂ) (hw : ∀t,‖w t‖≤1) (E : ℝ)
    (hf : ∀t,(∑k,‖f t k‖^2)≤E) :
    (∑k,‖∑t,w t*f t k‖^2)≤(Fintype.card τ:ℝ)^2*E := by
  have hpoint (k : κ) : ‖∑t,w t*f t k‖^2≤(Fintype.card τ:ℝ)*∑t,‖f t k‖^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : τ => (1:ℝ)) (fun t => ‖w t*f t k‖)
    have hn : ‖∑t,w t*f t k‖^2≤(∑t,‖w t*f t k‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    apply hn.trans
    apply (show (∑t,‖w t*f t k‖)^2≤(Fintype.card τ:ℝ)*∑t,‖w t*f t k‖^2 by simpa using h).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro t _
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hw t)
  calc
    _ ≤ ∑k,(Fintype.card τ:ℝ)*∑t,‖f t k‖^2 := Finset.sum_le_sum (fun k _ => hpoint k)
    _ = (Fintype.card τ:ℝ)*∑t,∑k,‖f t k‖^2 := by rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ (Fintype.card τ:ℝ)*∑_t : τ,E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => hf t)) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

theorem energy_bound
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀(rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q → ∀d : ReflectedFiberData rays levelBound K I F Q,
      (∑k,‖d.value W X ρ q k‖^2)≤
        C*(rays:ℝ)^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨Cb,hCb,hb⟩ := ReflectedBranchData.energy_bound W a b ha hsupp hW deltaLoss ρ q levelBound hδ hρ hq hlevel
  obtain ⟨Cp,hCp,hp⟩ := completed_branch_count_small_power ε hε
  refine ⟨Cb*Cp,by positivity,?_⟩
  intro rays K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.pool,p.val.IsMaximal := d.maximal
  have hcount := hp (I*Q) (mul_ne_zero hI hQ) (fun p : d.pool => p.val)
    Subtype.val_injective d.divides
  have hnorm : (Ideal.absNorm (I*Q):ℝ)≤K*(Ideal.absNorm Q:ℝ) := by
    simp only [map_mul,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hIK (Nat.cast_nonneg _)
  have hcount' : (6:ℝ)^(2*d.pool.card)≤Cp*(K*(Ideal.absNorm Q:ℝ))^ε := by
    have hc : (6:ℝ)^(2*d.pool.card)≤Cp*(Ideal.absNorm (I*Q):ℝ)^ε := by
      simpa only [Fintype.card_coe] using hcount
    exact hc.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hε.le) hCp.le)
  have he := finite_energy_bound
    (fun b => (d.branch b).value W X ρ q) d.weight d.weight_bound _
    (fun b => hb K X hK hX I F Q hI hQ hIK hk (d.branch b))
  change (∑k,‖d.value W X ρ q k‖^2)≤_ at he
  apply he.trans
  have hc : (Fintype.card (Fin rays×(d.pool→Fin 6)):ℝ)^2=(rays:ℝ)^2*(6:ℝ)^(2*d.pool.card) := by
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_mul,Nat.cast_pow]
    rw [mul_pow,←pow_mul,Nat.mul_comm d.pool.card 2]
    norm_num
  rw [hc]
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hKQ : 0<K*(Ideal.absNorm Q:ℝ) := mul_pos (by linarith) hnQ
  calc
    _ ≤ ((rays:ℝ)^2*(Cp*(K*(Ideal.absNorm Q:ℝ))^ε))*
      (Cb*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcount' (sq_nonneg _)
    _ = _ := by rw [Real.rpow_add hKQ]; ring

end ReflectedFiberData

open ActualEisensteinCubic CanonicalQuadraticSieve

theorem one_le_completedResidualScale (K : ℝ) (I Q : Ideal O)
    (hI : I≠0) (hIK : (Ideal.absNorm I:ℝ)≤K) : 1≤completedResidualScale K I Q := by
  have hn : 1≤(Ideal.absNorm (rowResidualPart I Q):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz =>
      squarefreeResidualPart_ne_zero (rowSimplePart I) Q (Ideal.absNorm_eq_zero_iff.mp hz))
  apply hn.trans
  rw [rowResidualPart_norm I Q hI,completedResidualScale]
  exact div_le_div_of_nonneg_right hIK (by positivity)

namespace ReflectedFiberData

def idealValue {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (J : Ideal O) : ℂ :=
  if h : J∈idealRange (completedResidualScale K I Q) then d.value W X ρ q ⟨J,h⟩ else 0

theorem idealValue_at {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (J : idealRange (completedResidualScale K I Q)) :
    d.idealValue W X ρ q J.val=d.value W X ρ q J := by
  simp only [idealValue,dite_eq_left J.property]

end ReflectedFiberData

def HasExactCompletedModels (rays : ℕ) (rows : Finset (Ideal O))
    (K X ρ q levelBound : ℝ) (F Q : Ideal O) (W : ℝ→ℂ) (Ψ : Ideal O→O→*ℂ) (lengthScale : ℂ) : Prop :=
  ∀A∈rows.image rowPowerfulPart,∀T∈rows.image (fun I => rowMaskPart I Q),
    (completedRowFiber rows Q A T).Nonempty →
    ∃I∈completedRowFiber rows Q A T,∃d : ReflectedFiberData rays levelBound K I F Q,
      ∀J∈completedRowFiber rows Q A T,
        completedT (Ψ J) W X=lengthScale*d.idealValue W X ρ q (rowResidualPart J Q)

theorem completed_energy_of_exact_models
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀(rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal O)) (F Q : Ideal O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal O→O→*ℂ) (lengthScale : ℂ),HasExactCompletedModels rays rows K X ρ q levelBound F Q W Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) W X‖^2)≤
        C*(rays:ℝ)^2*‖lengthScale‖^2*(Ideal.absNorm Q:ℝ)^ε*
          (K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  obtain ⟨Cm,hCm,hm⟩ := ReflectedFiberData.energy_bound W a b ha hsupp hW deltaLoss ε ρ q levelBound hδ hε hρ hq hlevel
  obtain ⟨Co,hCo,ho⟩ := completed_outer_row_small_power ε hε
  refine ⟨Co*Cm,by positivity,?_⟩
  intro rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hexact
  let B : ℝ := Cm*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*
    (K+K^2*(Ideal.absNorm Q:ℝ)/X)
  have hB : 0≤B := by dsimp [B]; positivity
  have hblocks : ∀A∈rows.image rowPowerfulPart,∀T∈rows.image (fun I => rowMaskPart I Q),
      (∑I∈completedRowFiber rows Q A T,‖completedT (Ψ I) W X‖^2)≤B/(Ideal.absNorm A:ℝ) := by
    intro A hA T hT
    by_cases hempty : (completedRowFiber rows Q A T).Nonempty
    · obtain ⟨I,hIf,d,hd⟩ := hexact A hA T hT hempty
      obtain ⟨hIr,hIA,hIT⟩ := Finset.mem_filter.mp hIf
      have hI := (hrows I hIr).1
      have hIK := (hrows I hIr).2
      have hk := one_le_completedResidualScale K I Q hI hIK
      have hdenergy := hm rays K X hK hX I F Q hI hQ hIK hk d
      have hembed := completedRowFiber_energy_le rows Q A T hbad K hrows
        (d.idealValue W X ρ q)
      have hscale : K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))=completedResidualScale K I Q := by
        simp only [completedResidualScale,hIA,hIT]
      rw [hscale] at hembed
      simp_rw [ReflectedFiberData.idealValue_at] at hembed
      have hsource : (∑J∈completedRowFiber rows Q A T,‖completedT (Ψ J) W X‖^2)=
          ‖lengthScale‖^2*∑J∈completedRowFiber rows Q A T,‖d.idealValue W X ρ q (rowResidualPart J Q)‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hd J hJ,norm_mul,mul_pow]
      rw [hsource]
      apply (mul_le_mul_of_nonneg_left (hembed.trans hdenergy) (sq_nonneg _)).trans
      apply le_of_eq
      dsimp [B]
      rw [hIA]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.sum_empty]
      exact div_nonneg hB (Nat.cast_nonneg _)
  have hh := ho rows Q hQ (fun I => ‖completedT (Ψ I) W X‖^2) B hB hblocks
  apply hh.trans_eq
  dsimp [B]
  ring

end CompletedGauss

end

end OAI

end Source177

/- Original source: OAI/NumberTheory/DirichletL/GaussSum/CompletedDyadicRows.lean; sha256: df231006e788b1255565e1914b703bb3f78a8c513426232334c4d41ac2cdde98 -/
section Source178
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace CompletedGauss

section

open ActualEisensteinCubic

theorem two_pow_clog_le_double (n : ℕ) (hn : 1≤n) : 2^Nat.clog 2 n≤2*n := by
  by_cases h : n=1
  · simp [h]
  have hn1 : 1<n := lt_of_le_of_ne hn (Ne.symm h)
  have hl : 0<Nat.clog 2 n := Nat.clog_pos (by norm_num) hn1
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1<2) hn1
  have he : (Nat.clog 2 n).pred+1=Nat.clog 2 n := Nat.succ_pred_eq_of_pos hl
  calc
    _ = 2^(Nat.clog 2 n).pred*2 := by rw [←he,pow_succ]; rfl
    _ ≤ n*2 := Nat.mul_le_mul_right 2 hp.le
    _ = _ := Nat.mul_comm _ _

def completedRowDyad (rows : Finset (Ideal O)) (j : ℕ) : Finset (Ideal O) :=
  rows.filter (fun I => Nat.clog 2 (Ideal.absNorm I)=j)

def completedRowDyadicLength (K : ℝ) : ℕ := Nat.clog 2 ⌊K⌋₊

theorem completedRowDyad_bounds (rows : Finset (Ideal O)) (j : ℕ)
    (hrows : ∀I∈rows,I≠0) (I : Ideal O) (hI : I∈completedRowDyad rows j) :
    I≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^j := by
  obtain ⟨hIr,hj⟩ := Finset.mem_filter.mp hI
  have hn : 1≤Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr (fun hz => hrows I hIr (Ideal.absNorm_eq_zero_iff.mp hz))
  have hu := Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)
  have hl := two_pow_clog_le_double (Ideal.absNorm I) hn
  rw [hj] at hu hl
  refine ⟨hrows I hIr,?_,?_⟩
  · have hh : (2:ℝ)^j≤2*(Ideal.absNorm I:ℝ) := by exact_mod_cast hl
    linarith
  · exact_mod_cast hu

theorem completedRowDyad_sum {M : Type*} [AddCommMonoid M]
    (rows : Finset (Ideal O)) (K : ℝ) (hK : 0≤K)
    (hrows : ∀I∈rows,(Ideal.absNorm I:ℝ)≤K) (f : Ideal O→M) :
    (∑j∈Finset.range (completedRowDyadicLength K+1),∑I∈completedRowDyad rows j,f I)=∑I∈rows,f I := by
  have hm : ∀I∈rows,Nat.clog 2 (Ideal.absNorm I)∈Finset.range (completedRowDyadicLength K+1) := by
    intro I hI
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.clog_mono_right 2 ((Nat.le_floor_iff hK).mpr (hrows I hI)))
  simpa only [completedRowDyad] using Finset.sum_fiberwise_of_maps_to hm f

theorem completedRowDyadic_top (K : ℝ) (hK : 1≤K) :
    (2:ℝ)^(completedRowDyadicLength K)≤2*K := by
  have hh := two_pow_clog_le_double ⌊K⌋₊ ((Nat.one_le_floor_iff K).mpr hK)
  have hr : (2:ℝ)^(completedRowDyadicLength K)≤2*(⌊K⌋₊:ℝ) := by exact_mod_cast hh
  exact hr.trans (mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith : 0≤K)) (by norm_num))

theorem completedRowDyadic_scale (K : ℝ) (hK : 1≤K) (j : ℕ)
    (hj : j∈Finset.range (completedRowDyadicLength K+1)) : (2:ℝ)^j≤2*K :=
  (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).trans
    (completedRowDyadic_top K hK)

theorem completedRowDyadic_mass (K : ℝ) (hK : 1≤K) :
    (∑j∈Finset.range (completedRowDyadicLength K+1),(2:ℝ)^j)≤4*K ∧
    (∑j∈Finset.range (completedRowDyadicLength K+1),((2:ℝ)^j)^2)≤16*K^2 := by
  have ht := completedRowDyadic_top K hK
  constructor
  · rw [geom_sum_eq (by norm_num : (2:ℝ)≠1),pow_succ]
    norm_num
    linarith
  · have he (j : ℕ) : ((2:ℝ)^j)^2=(4:ℝ)^j := by rw [←pow_mul,Nat.mul_comm j 2,pow_mul]; norm_num
    simp_rw [he]
    rw [geom_sum_eq (by norm_num : (4:ℝ)≠1),pow_succ,←he]
    norm_num
    have hp := pow_le_pow_left₀ (by positivity : 0≤(2:ℝ)^(completedRowDyadicLength K)) ht 2
    nlinarith

theorem completedRowDyadic_shape (s K X Q : ℝ) (hs : 0≤s) (hK : 1≤K)
    (hX : 0<X) (hQ : 0<Q) :
    (∑j∈Finset.range (completedRowDyadicLength K+1),
      ((2:ℝ)^j*Q)^s*((2:ℝ)^j+((2:ℝ)^j)^2*Q/X))≤
      (16*(2:ℝ)^s)*(K*Q)^s*(K+K^2*Q/X) := by
  have hb (j : ℕ) (hj : j∈Finset.range (completedRowDyadicLength K+1)) :
      ((2:ℝ)^j*Q)^s≤(2*(K*Q))^s := by
    apply Real.rpow_le_rpow (by positivity) _ hs
    have h := mul_le_mul_of_nonneg_right (completedRowDyadic_scale K hK j hj) hQ.le
    nlinarith
  calc
    _ ≤ ∑j∈Finset.range (completedRowDyadicLength K+1),
      (2*(K*Q))^s*((2:ℝ)^j+((2:ℝ)^j)^2*Q/X) :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hb j hj) (by positivity))
    _ = (2*(K*Q))^s*((∑j∈Finset.range (completedRowDyadicLength K+1),(2:ℝ)^j)+
      (∑j∈Finset.range (completedRowDyadicLength K+1),((2:ℝ)^j)^2)*Q/X) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_div,←Finset.sum_mul]
    _ ≤ (2*(K*Q))^s*(4*K+16*K^2*Q/X) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (completedRowDyadic_mass K hK).1
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (completedRowDyadic_mass K hK).2 hQ.le) hX.le)
    _ ≤ (2*(K*Q))^s*(16*(K+K^2*Q/X)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ = 4*K+16*(K^2*Q/X) := by ring
        _ ≤ 16*(K+K^2*Q/X) := by linarith
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring

open ActualEisensteinCubic CanonicalQuadraticSieve

def HasExactCompletedDyadicModels (rays : ℕ) (rows : Finset (Ideal O))
    (K X ρ q levelBound : ℝ) (F Q : Ideal O) (W : ℝ→ℂ) (Ψ : Ideal O→O→*ℂ) (lengthScale : ℂ) : Prop :=
  ∀j∈Finset.range (completedRowDyadicLength K+1),
    HasExactCompletedModels rays (completedRowDyad rows j) ((2:ℝ)^j) X ρ q levelBound F Q W Ψ lengthScale

theorem completed_mean_square_of_exact_reflection
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀(rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal O)) (F Q : Ideal O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal O→O→*ℂ) (lengthScale : ℂ),HasExactCompletedDyadicModels rays rows K X ρ q levelBound F Q W Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) W X‖^2)≤
        C*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
          (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  let deltaLoss : ℝ := ε/12
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨C,hC,h⟩ := completed_energy_of_exact_models W a b ha hsupp hW deltaLoss deltaLoss ρ q levelBound hδ hδ hρ hq hlevel
  let s : ℝ := 10*deltaLoss+deltaLoss
  have hs : 0≤s := by dsimp [s]; positivity
  refine ⟨C*(16*(2:ℝ)^s),by positivity,?_⟩
  intro rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hmodels
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  let A : ℝ := C*(rays:ℝ)^2*‖lengthScale‖^2*(Ideal.absNorm Q:ℝ)^deltaLoss
  have hA : 0≤A := by dsimp [A]; positivity
  rw [←completedRowDyad_sum rows K (by linarith : 0≤K) (fun I hI => (hrows I hI).2)
    (fun I => ‖completedT (Ψ I) W X‖^2)]
  have hper (j : ℕ) (hj : j∈Finset.range (completedRowDyadicLength K+1)) :
      (∑I∈completedRowDyad rows j,‖completedT (Ψ I) W X‖^2)≤
        A*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
          ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := by
    have hb := h rays ((2:ℝ)^j) X (one_le_pow₀ (by norm_num)) hX
      (completedRowDyad rows j) F Q hQ hbad
      (fun I hI => ⟨(completedRowDyad_bounds rows j (fun I hI => (hrows I hI).1) I hI).1,
        (completedRowDyad_bounds rows j (fun I hI => (hrows I hI).1) I hI).2.2⟩)
      Ψ lengthScale (hmodels j hj)
    convert hb using 1
    dsimp [A,s]
    ring
  calc
    _ ≤ ∑j∈Finset.range (completedRowDyadicLength K+1),
      A*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
        ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := Finset.sum_le_sum hper
    _ = A*∑j∈Finset.range (completedRowDyadicLength K+1),
      ((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
        ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*((16*(2:ℝ)^s)*(K*(Ideal.absNorm Q:ℝ))^s*(K+K^2*(Ideal.absNorm Q:ℝ)/X)) :=
      mul_le_mul_of_nonneg_left (completedRowDyadic_shape s K X (Ideal.absNorm Q:ℝ) hs hK
        (by linarith) hnQ) hA
    _ ≤ (C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
        (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
      have hnq : (Ideal.absNorm Q:ℝ)^deltaLoss≤(K*(Ideal.absNorm Q:ℝ))^deltaLoss := by
        apply Real.rpow_le_rpow hnQ.le _ hδ.le
        exact le_mul_of_one_le_left hnQ.le hK
      have hpower : (Ideal.absNorm Q:ℝ)^deltaLoss*(K*(Ideal.absNorm Q:ℝ))^s≤
          (K*(Ideal.absNorm Q:ℝ))^ε := by
        apply (mul_le_mul_of_nonneg_right hnq (by positivity)).trans_eq
        rw [←Real.rpow_add (mul_pos (by linarith) hnQ)]
        congr 1
        dsimp [s,deltaLoss]
        ring
      calc
        _ = ((C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K+K^2*(Ideal.absNorm Q:ℝ)/X))*
          ((Ideal.absNorm Q:ℝ)^deltaLoss*(K*(Ideal.absNorm Q:ℝ))^s) := by dsimp [A]; ring
        _ ≤ ((C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K+K^2*(Ideal.absNorm Q:ℝ)/X))*
          (K*(Ideal.absNorm Q:ℝ))^ε := mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = _ := by ring

end
section

open CompletedDyadic

def completedRamifiedInitial : ℝ := (3:ℝ)^(-(4/3:ℝ))
def completedRamifiedStep : ℝ := (3:ℝ)^(1/3:ℝ)

theorem completedRamifiedInitial_pos : 0<completedRamifiedInitial := by
  unfold completedRamifiedInitial
  positivity

theorem completedRamifiedStep_gt_one : 1<completedRamifiedStep := by
  exact Real.one_lt_rpow (by norm_num) (by norm_num)

theorem actual_ramified_scale (m : ℕ) :
    ramifiedScale completedRamifiedInitial completedRamifiedStep m=(3:ℝ)^(((m:ℝ)-4)/3) := by
  unfold ramifiedScale completedRamifiedInitial completedRamifiedStep
  rw [←Real.rpow_mul_natCast (by norm_num),←Real.rpow_add (by norm_num)]
  congr 1
  ring

theorem actual_ramified_norm (m : ℕ) :
    (ramifiedScale completedRamifiedInitial completedRamifiedStep m)^3=(3:ℝ)^((m:ℝ)-4) := by
  rw [actual_ramified_scale,←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

theorem cusp_coefficient_normalization (m n b : ℝ) (hn : 0<n) (hb : 0<b) :
    (3:ℝ)^(m/6)*Real.sqrt b/Real.sqrt ((3:ℝ)^m*n*b^3)=
      1/((3:ℝ)^(m/3)*Real.sqrt n*b) := by
  have hroot : Real.sqrt ((3:ℝ)^m)=(3:ℝ)^(m/6)*(3:ℝ)^(m/3) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (by norm_num),←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hbroot : Real.sqrt (b^3)=b*Real.sqrt b := by
    rw [show b^3=b^2*b by ring,Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq hb.le]
  rw [Real.sqrt_mul (mul_nonneg (by positivity) hn.le),Real.sqrt_mul (by positivity),hroot,hbroot]
  have hr1 : (3:ℝ)^(m/6)≠0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hr2 : (3:ℝ)^(m/3)≠0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hbn : Real.sqrt b≠0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  field_simp

def normalizedCuspAmplitude (d : ℂ) (m b : ℝ) : ℂ :=
  d/((27*(3:ℝ)^(m/6)*Real.sqrt b:ℝ):ℂ)

theorem normalizedCuspAmplitude_norm (d : ℂ) (m b : ℝ) (hb : 0<b)
    (hd : ‖d‖≤27*(3:ℝ)^(m/6)*Real.sqrt b) : ‖normalizedCuspAmplitude d m b‖≤1 := by
  unfold normalizedCuspAmplitude
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).mpr hd

theorem cusp_coefficient_norm (d : ℂ) (m n b : ℝ) (hn : 0<n) (hb : 0<b)
    (hd : ‖d‖≤27*(3:ℝ)^(m/6)*Real.sqrt b) :
    ‖d/((Real.sqrt ((3:ℝ)^m*n*b^3):ℝ):ℂ)‖≤
      27/((3:ℝ)^(m/3)*Real.sqrt n*b) := by
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_div_of_nonneg_right hd (Real.sqrt_nonneg _)).trans_eq
  calc
    _ = 27*((3:ℝ)^(m/6)*Real.sqrt b/Real.sqrt ((3:ℝ)^m*n*b^3)) := by ring
    _ = _ := by rw [cusp_coefficient_normalization m n b hn hb]; ring

end

open ActualEisensteinCubic CanonicalQuadraticSieve

theorem short_completed_average_of_exact_reflection
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀(rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal O→O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) W (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (Ψ f I) W X (Z^(1/1000:ℝ))‖^2)/F≤
        C*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨Cr,hCr,hr⟩ := completed_mean_square_of_exact_reflection
    W a b ha hsupp hW ε ρ q levelBound hε hρ hq hlevel
  obtain ⟨Cs,hCs,hs⟩ := short_completed_normalized_small_power ε hε
  refine ⟨Cs*Cr,by positivity,?_⟩
  intro rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodels
  have hG1 : 1≤(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hG (Ideal.absNorm_eq_zero_iff.mp hz))
  let A : ℝ := Cr*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε
  have hA : 0≤A := by dsimp [A]; positivity
  have hcompleted (f : idealRange F) (H : Ideal O) (hH : H∈shortCubeRange (Z^(1/1000:ℝ))) :
      (∑I : rows,‖completedT (Ψ f I.val) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
        A*(K+K^2*(Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X) := by
    have hf0 := (mem_idealRange.mp f.property).1.1
    have hfN := (mem_idealRange.mp f.property).2
    have hHN := (mem_shortCubeRange _ H).mp hH
    have hH1 : 1≤(Ideal.absNorm H:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hHN.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hH0 : (Ideal.absNorm H:ℝ)≠0 := by linarith
    have hscale := short_cube_scales Z K (Ideal.absNorm G:ℝ) X F (Ideal.absNorm H:ℝ)
      hZ hK hG1 hF hFZ hH1 hHN.2.le hmargin
    have hb := hr rays K (X/(Ideal.absNorm H:ℝ)^3) hK hscale.1 rows f.val (G*f.val)
      (mul_ne_zero hG hf0) (fun P hP => dvd_trans (hbad P hP) (dvd_mul_right G f.val))
      hrows (Ψ f) lengthScale (hmodels f H hH)
    rw [Finset.sum_coe_sort (s := rows) (f := fun I : Ideal O => ‖completedT (Ψ f I) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)]
    apply hb.trans
    simp only [map_mul,Nat.cast_mul]
    have hpow : (K*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)))^ε≤
        (K*(Ideal.absNorm G:ℝ)*F)^ε := by
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      have hh := mul_le_mul_of_nonneg_left hfN (show 0≤K*(Ideal.absNorm G:ℝ) by positivity)
      nlinarith
    have hshape : K+K^2*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ))/(X/(Ideal.absNorm H:ℝ)^3)=
        K+K^2*(Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X := by
      field_simp

    rw [hshape]
    change Cr*(rays:ℝ)^2*‖lengthScale‖^2*(K*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)))^ε*_≤A*_
    have hX0 : 0<X := by
      have hh := (le_div_iff₀ (show 0<(Ideal.absNorm H:ℝ)^3 by positivity)).mp hscale.1
      exact (show 0<(Ideal.absNorm H:ℝ)^3 by positivity).trans_le (by simpa only [one_mul] using hh)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  have hb := hs Z K (Ideal.absNorm G:ℝ) X F A hZ hK hG1 hF hFZ hA hmargin
    (fun f (I : rows) => Ψ f I.val) (fun f I z => hΨ f I.val z) W hcompleted
  have hsum (f : idealRange F) :
      (∑I : rows,‖shortCompletedSum (Ψ f I.val) W X (Z^(1/1000:ℝ))‖^2)=
      ∑I∈rows,‖shortCompletedSum (Ψ f I) W X (Z^(1/1000:ℝ))‖^2 :=
    Finset.sum_coe_sort (s := rows) (f := fun I : Ideal O => ‖shortCompletedSum (Ψ f I) W X (Z^(1/1000:ℝ))‖^2)
  simp_rw [hsum] at hb
  apply hb.trans_eq
  dsimp [A]
  ring

end CompletedGauss

open scoped BigOperators Classical SchwartzMap
namespace InitialMeanSquare

section
open ActualEisensteinCubic SecondPassArithmetic
open CanonicalQuadraticSieve (Admissible)

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def initialSquarefreeSector (s : Finset (SecondExpansionData ι)) : Finset (SecondExpansionData ι) :=
  s.filter (fun x => Squarefree (Ideal.span {(sourceObservation p x).2}))

theorem initial_weight_squarefree (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (hw : secondArithmeticWeight p hp hcop hg Ψ m 1 1 ray x ≠ 0) :
    Squarefree (Ideal.span {(sourceObservation p x).2}) := by
  have hs := secondArithmeticWeight_squarefree p hp hcop hg Ψ m 1 1 ray x hE
    (by simp : Squarefree (Ideal.span {(1 : O)})) hw
  rw [sourceLabel_span]
  simpa using hs

theorem initial_source_eq_squarefree (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (F : Finset ι) (s : Finset (SecondExpansionData ι))
    (hE : ∀ x ∈ s, x.divisor ⊆ x.sourceCommon)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s H₁ H₂ W Y =
      secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (initialSquarefreeSector p s) H₁ H₂ W Y := by
  unfold secondExpansionSource initialSquarefreeSector
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : Squarefree (Ideal.span {(sourceObservation p x).2})
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs]
    have hw : secondArithmeticWeight p hp hcop hg Ψ m 1 1 ray x=0 := by
      by_contra hn
      exact hs (initial_weight_squarefree p hp hcop hg Ψ m ray x (hE x hx) hn)
    unfold secondArithmeticWeight at hw
    rcases mul_eq_zero.mp hw with h1 | h2
    · rw [h1]
      ring
    · rw [h2]
      ring

include hp hg in
omit [DecidableEq ι] in
theorem initial_squarefree_label_admissible
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (x : SecondExpansionData ι) (hs : Squarefree (Ideal.span {(sourceObservation p x).2})) :
    Admissible (Ideal.span {(sourceObservation p x).2}) := by
  have hn : (sourceObservation p x).2 ≠ 0 :=
    mul_ne_zero (primeSubsetGenerator_ne_zero _ _)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hnI : Ideal.span {(sourceObservation p x).2} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr hn
  refine ⟨hnI,hs,?_⟩
  intro P hP
  obtain ⟨hprime,hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hnI).mp hP
  rw [sourceLabel_span] at hdiv
  have hfactor (S : Finset ι) (hd : P ∣ ∏ i ∈ S,Ideal.span {p i}) :
      lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2 := by
    obtain ⟨i,hi,hPi⟩ := (hprime.dvd_finsetProd_iff (fun i => Ideal.span {p i})).mp hd
    have hpi : Prime (Ideal.span {p i}) :=
      Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
    have he := (prime_dvd_prime_iff_eq hprime hpi).mp hPi
    rw [he]
    exact ⟨hg i,hc i⟩
  rcases hprime.dvd_or_dvd hdiv with h1 | h2
  · exact hfactor _ h1
  · exact hfactor _ h2

include hp hg in
omit [DecidableEq ι] in
theorem initial_squarefree_target_admissible
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (s : Finset (SecondExpansionData ι)) :
    ∀ z ∈ sourceIdealTarget ((initialSquarefreeSector p s).image (sourceObservation p)),
      Admissible z.1 := by
  intro z hz
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  exact initial_squarefree_label_admissible p hp hg hc x (Finset.mem_filter.mp hx).2

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)

theorem initial_subbin_transfer
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU : ∀ t, g t ≠ 0 → U t=1) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (N J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cₛ : ℝ), 0 ≤ C ∧ 0 ≤ Cₛ ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (Z H M : ℝ) (j : SecondLogIndex)
        (s : Finset (SecondExpansionData ι)),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        s ⊆ secondLogSector p ∅ F K R Z M j →
        let X := initialLogColumn Z (primeProductNorm p R) j
        let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
        ∃ B : Frequency → ℝ,
          (∀ q, 0 ≤ B q) ∧
          (∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) W H‖ ≤
          (C*H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
            (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,ht⟩ :=
    initial_sector_transfer U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F R Ψ m ray K Z H M j s hZ hH hΨ hsub
  dsimp only
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let X := initialLogColumn Z (primeProductNorm p R) j
  have hR : 0 < primeProductNorm p R := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hR)
  have hs : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x
      (secondLogSector_subset p ∅ F K R Z M j (hsub hx))
  have hk : ∀ x ∈ s, x.frequency ≠ 0 := by
    intro x hx
    exact (secondSupportedSector_mem p F K R Z M x (Finset.mem_filter.mp (hsub hx)).1).2.2.2.1
  have hcoords := initial_sector_coordinates p hp F R K Z M hZ j
  obtain ⟨B,hB,hdec,hbound⟩ := ht p hp hcop hg hinj hc hpr F Ψ m r ray s Z H
    (secondLogE j) (secondLogV j) X (secondLogK j) hZ hH
    (normLogScale_pos _) (normLogScale_pos _) hX (normLogScale_pos _) hΨ hs hk
    (fun x hx => (hcoords x (hsub hx)).1) (fun x hx => (hcoords x (hsub hx)).2.1)
    (fun x hx => (hcoords x (hsub hx)).2.2.1) (fun x hx => (hcoords x (hsub hx)).2.2.2)
  refine ⟨B,hB,?_,?_⟩
  · simpa only [X, initial_log_radial Z H (primeProductNorm p R) hZ.ne' hR.ne'] using hdec
  · simpa only [r, elementNorm, primeSubsetGenerator_norm_eq_productNorm] using hbound

end InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem initialBinCost_of_canonical_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hCₛ : 0 ≤ Cₛ) (hCc : 0 ≤ Cchild)
    (j : SecondLogIndex) (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ)
    (J N : ℕ) (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hchild : ∀ q,
      let s := secondLogSector p ∅ F K R Z M j
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      childGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X q ≤
        (Cchild*(X*initialLogLabel j)^2)*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) :
    initialBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ*(∫ t : ℝ,firstLogDensity 0 t)^3)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  let s := secondLogSector p ∅ F K R Z M j
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let G := sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X
  let E := Cchild*(X*initialLogLabel j)^2
  let S := (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N
  have hpR : 0 < primeProductNorm p R := primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hpR)
  have hlabel : 0 < initialLogLabel j := by
    unfold initialLogLabel secondLogE secondLogV
    exact mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) (Real.exp_pos _)
  have hE : 0 ≤ E := mul_nonneg hCc (sq_nonneg _)
  have hS : 0 < S := by
    dsimp [S]
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  have hG : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have henergy : ∀ q, G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J := by
    intro q
    exact (sourceGeometricMean_le_ideal p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X q).trans (hchild q)
  have hb := polynomial_density_cost B G J S Cₛ E hS hCₛ hE hB hG hdec henergy
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  calc
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ*E/S)*(∫ t : ℝ,firstLogDensity 0 t)^3) := mul_le_mul_of_nonneg_left hb hpref
    _ = _ := by
      dsimp only [E,X,S]
      rw [initial_log_mass Z (primeProductNorm p R) hpR.ne',
        mul_pow (Z/primeProductNorm p R) (Real.exp 2) 2]
      have he : (Real.exp 2)^2=Real.exp 4 := by
        rw [pow_two,←Real.exp_add]
        norm_num
      rw [he]
      have hz := hZ.ne'
      have hr := hpR.ne'
      field_simp

end InitialMeanSquare

end

end OAI

end Source178

/- Original source: OAI/NumberTheory/DirichletL/MeanSquare/HarmonicAggregation.lean; sha256: 7c9ad1bd2f44c4de6567080753e9afb64252392366337cb628db4e02f9696c58 -/
section Source179
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)

def initialRayMass : ℝ := ∑ ray : SecondRayIndex,‖secondRayCoefficient ray‖

lemma initialRayMass_nonneg : 0 ≤ initialRayMass := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem initial_complementary_harmonic (F : Finset ι) (U : ℝ) :
    (∑ R ∈ boundedPrimeSupports p F U,1/primeProductNorm p R) ≤
      128*Real.exp 1*(normLogBin U+1 : ℝ) := by
  let f : Finset ι → Ideal O := fun R => ∏ i ∈ R,Ideal.span {p i}
  have hf : Function.Injective f := FirstCauchyArithmetic.family_product_injective _ hinj
  let T := (boundedPrimeSupports p F U).image f
  have hT : ∀ I ∈ T,I ≠ (0 : Ideal O) := by
    intro I hI
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hI
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i}))
  have hU : ∀ I ∈ T,(Ideal.absNorm I : ℝ) ≤ U := by
    intro I hI
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hI
    rw [←primeProductNorm_eq_ideal_norm p R]
    exact (Finset.mem_filter.mp hR).2
  have hb := descent_ideal_inverse_sum T U hT hU
  rw [Finset.sum_image (fun R _ S _ h => hf h)] at hb
  simpa only [f,←primeProductNorm_eq_ideal_norm p] using hb

include hinj in

theorem initial_harmonic_aggregation (F : Finset ι) (U K D : ℝ) (hD : 0 ≤ D)
    (a : SecondRayIndex → Finset ι → SecondLogIndex → ℝ)
    (ha : ∀ ray, ∀ R ∈ boundedPrimeSupports p F U, ∀ j ∈ secondLogBinBox U K,
      a ray R j ≤ D/primeProductNorm p R*‖secondRayCoefficient ray‖) :
    (∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F U,
      ∑ j ∈ secondLogBinBox U K,a ray R j) ≤
    D*initialRayMass*((secondLogBinBox U K).card : ℝ)*
      (128*Real.exp 1*(normLogBin U+1 : ℝ)) := by
  let B := secondLogBinBox U K
  let C := 128*Real.exp 1*(normLogBin U+1 : ℝ)
  have hinner (ray : SecondRayIndex) :
      (∑ R ∈ boundedPrimeSupports p F U,∑ j ∈ B,a ray R j) ≤
      (D*‖secondRayCoefficient ray‖*(B.card : ℝ))*C := by
    calc
      _ ≤ ∑ R ∈ boundedPrimeSupports p F U,∑ _j ∈ B,
          D/primeProductNorm p R*‖secondRayCoefficient ray‖ := by
        apply Finset.sum_le_sum
        intro R hR
        exact Finset.sum_le_sum (fun j hj => ha ray R hR j hj)
      _ = (D*‖secondRayCoefficient ray‖*(B.card : ℝ))*
          ∑ R ∈ boundedPrimeSupports p F U,1/primeProductNorm p R := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro R hR
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (initial_complementary_harmonic p hinj F U)
        (by positivity)
  calc
    _ ≤ ∑ ray : SecondRayIndex,(D*‖secondRayCoefficient ray‖*(B.card : ℝ))*C :=
      Finset.sum_le_sum (fun ray _ => hinner ray)
    _ = _ := by
      unfold initialRayMass
      simp only [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hray
      ring

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic FirstPassCubeLabels
open ConcretePrimeRowBridge (idealGenerator)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def sourceGlobalBlock (b:CubeCoordinates ι) (C D:Finset ι) : GlobalCubeBlock ι :=
  ⟨b.swap,C,D⟩

lemma cube_swap_support (b:CubeCoordinates ι) : b.swap.support=b.support := by
  simp only [CubeCoordinates.swap,CubeCoordinates.support,Finset.union_comm]

omit [DecidableEq ι] in
lemma cube_swap_sum (b:CubeCoordinates ι) :
    (fun i=>b.swap.leftExponent i+b.swap.rightExponent i)=
      (fun i=>b.leftExponent i+b.rightExponent i) := by
  funext i
  exact Nat.add_comm _ _

lemma orientedCubeFirstBlock_single_source
    (pool:Finset ι) (b:CubeCoordinates ι) (C D:Finset ι) (I:Ideal O) (h:O)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) :
    orientedCubeFirstBlock p hp hcop hg pool (sourceGlobalBlock b C D) {(I,h)} (fun _=>1)
      Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell =
    (primeProductNorm p D:ℂ)⁻¹ *
      actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (originalLabelColumn p hg b.support b.leftBit b.rightBit true
          (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p
            (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)) S)))
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) C) (idealGenerator I))
        (originalLabelColumn p hg b.support b.leftBit b.rightBit false
          (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p
            (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) S)))
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) C) (idealGenerator I))
        W V₁ V₂ (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
          (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) K
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  have hl : b.swap.leftBit=b.rightBit := rfl
  have hr : b.swap.rightBit=b.leftBit := rfl
  have hst : b.swap.sideDivisor true=b.rightDivisor := rfl
  have hsf : b.swap.sideDivisor false=b.leftDivisor := rfl
  simp only [orientedCubeFirstBlock,sourceGlobalBlock,globalCubePool,globalCubeColumnScale,
    globalFirstBlockColumnScale,GlobalCubeBlock.withCommon,cube_swap_support,cube_swap_sum,
    hl,hr,hst,hsf,Finset.sum_singleton,one_mul]

lemma canonical_log_kernel
    (pool:Finset ι) (b:CubeCoordinates ι) (hb:b.Admissible) (C:Finset ι)
    (hCB:Disjoint C b.support) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f d h:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (K ell:ℝ) (hell:0<ell) :
    actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun U=>g₁ (columnLog p ell U)))
      (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun U=>g₂ (columnLog p ell U)))
      W (fun _=>1) (fun _=>1) 1 1 K d h =
    actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (originalLabelColumn p hg b.support b.leftBit b.rightBit true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p
          (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)) S))) (∏i∈C,p i) f)
      (originalLabelColumn p hg b.support b.leftBit b.rightBit false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p
          (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) S))) (∏i∈C,p i) f)
      W (fun _=>1) (fun _=>1) (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
        (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) K d h := by
  unfold actualFirstKernel
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  have hdis (S:Finset ι) (hS:S∈(pool\(b.support∪C)).powerset) :
      Disjoint S C ∧ Disjoint S b.support := by
    constructor <;> apply Finset.disjoint_left.mpr
    · intro i hi hx
      exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hi)).2 (Finset.mem_union_right _ hx)
    · intro i hi hx
      exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hi)).2 (Finset.mem_union_left _ hx)
  have h₁:=canonicalCubeResidual_log p hp hg b hb C N hCB (hdis N hN).1 (hdis N hN).2 true Ψ₁ m₁ f g₁ ell hell
  have h₂:=canonicalCubeResidual_log p hp hg b hb C P hCB (hdis P hP).1 (hdis P hP).2 false Ψ₂ m₂ f g₂ ell hell
  simp only [CubeCoordinates.sideDivisor,Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_false,ite_true] at h₁ h₂
  simp only [threeGaussRowFactor,h₁,h₂]

def commonProductUnit (C:Finset ι) : Oˣ :=
  Classical.choose (exists_label_unit (∏i∈C,p i) (∏i∈C,Ideal.span {p i})
    (FiniteGaussPhase.span_finset_prod C p))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma commonProductUnit_spec (C:Finset ι) :
    (∏i∈C,p i)=(commonProductUnit p C:O)*primeSubsetGenerator (fun i=>Ideal.span {p i}) C :=
  Classical.choose_spec (exists_label_unit (∏i∈C,p i) (∏i∈C,Ideal.span {p i})
    (FiniteGaussPhase.span_finset_prod C p))

def commonCubePhase (b:CubeCoordinates ι) (C:Finset ι) : ℂ :=
  blockRow p hg (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
    (fun i=>(conductorExponent (parity (b.leftExponent i+b.rightExponent i)) (b.leftBit i) (b.rightBit i)).val)
    ((commonProductUnit p C:O)^2)

lemma commonCubePhase_norm (b:CubeCoordinates ι) (C:Finset ι) :
    ‖commonCubePhase p hg b C‖=1 :=
  commonUnitPhase_norm p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit (commonProductUnit p C)

theorem canonicalSource_mode_attachment
    (pool:Finset ι) (b:CubeCoordinates ι) (hb:b.Admissible) (C D:Finset ι)
    (hCB:Disjoint C b.support) (I:Ideal O) (h:O)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) (hell:0<ell)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    ((UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ))*
      actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ (idealGenerator I) (fun U=>g₁ (columnLog p ell U)))
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ (idealGenerator I) (fun U=>g₂ (columnLog p ell U)))
        W (fun _=>1) (fun _=>1) 1 1 K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h =
    (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)*commonCubePhase p hg b C*
      orientedCubeFirstBlock p hp hcop hg pool (sourceGlobalBlock b C D)
        {(I,(commonProductUnit p C:O)^2*h)} (fun _=>1) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
  have hFB:Disjoint (pool\(b.support∪C)) b.support :=
    Finset.disjoint_left.mpr (fun i hi hiB=>(Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB))
  rw [canonical_log_kernel p hp hcop hg pool b hb C hCB Ψ₁ Ψ₂ m₁ m₂ (idealGenerator I) _ h g₁ g₂ W K ell hell]
  rw [actualFirstKernel_insert_windows p hp hcop hg _ _ _ _ _ Ψ₁ Ψ₂ m₁ m₂ _ _
    g₁ g₂ W V₁ V₂ _ _ K _ h hV₁ hV₂]
  rw [commonProductUnit_spec p C]
  rw [actualFirstKernel_common_unit p hp hcop hg _ _ hFB _ _ _ _ _ W V₁ V₂ _ _ K
    (commonProductUnit p C) _ (idealGenerator I) _ h]
  rw [orientedCubeFirstBlock_single_source]
  unfold commonCubePhase
  ring

end
section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcretePrimeRowBridge (idealGenerator)
open ConcreteTraceCRT (eisEmbedding)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

lemma orientedCubeFirstBlock_eq_sum_single (pool:Finset ι) (b:GlobalCubeBlock ι)
    (s:Finset (Ideal O×O)) (a:Ideal O×O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) :
    orientedCubeFirstBlock p hp hcop hg pool b s a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell=
      ∑x∈s,a x*orientedCubeFirstBlock p hp hcop hg pool b {x} (fun _=>1)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
  unfold orientedCubeFirstBlock
  simp only [Finset.sum_singleton,one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

def rawCanonicalBlock (pool:Finset ι) (b:GlobalCubeBlock ι)
    (s:Finset (Ideal O×O)) (a:Ideal O×O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (K ell:ℝ) : ℂ :=
  let q:=b.cube.swap
  ∑x∈s,a x*((UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)/
    (primeProductNorm p b.firstDivisor:ℂ))*
    actualFirstKernel p hp hcop hg (pool\(q.support∪b.common)) q.support
      (fun i=>q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit
      (canonicalCubeResidual p hg q b.common true Ψ₁ m₁ (idealGenerator x.1)
        (fun U=>g₁ (columnLog p ell U)))
      (canonicalCubeResidual p hg q b.common false Ψ₂ m₂ (idealGenerator x.1)
        (fun U=>g₂ (columnLog p ell U)))
      W (fun _=>1) (fun _=>1) 1 1 K
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) b.firstDivisor) x.2

def sourceFrequencyEquiv (C:Finset ι) : (Ideal O×O)≃(Ideal O×O) :=
  Equiv.prodCongr (Equiv.refl _) (unitSquareRowEquiv (commonProductUnit p C))

def sourceRotatedCoefficient (b:GlobalCubeBlock ι) (a:Ideal O×O→ℂ) (x:Ideal O×O) : ℂ :=
  (UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)*
    commonCubePhase p hg b.cube.swap b.common*a ((sourceFrequencyEquiv p b.common).symm x)

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceFrequencyEquiv_label (C:Finset ι) (x:Ideal O×O) :
    (sourceFrequencyEquiv p C x).1=x.1 := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceFrequencyEquiv_row_norm (C:Finset ι) (x:Ideal O×O) :
    ‖eisEmbedding (sourceFrequencyEquiv p C x).2‖=‖eisEmbedding x.2‖ := by
  have hr : (sourceFrequencyEquiv p C x).2=(commonProductUnit p C:O)^2*x.2 := rfl
  rw [hr,map_mul,norm_mul,map_pow,norm_pow,GaussGeneratorTransport.norm_eisEmbedding_unit,one_pow,one_mul]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceFrequencyEquiv_row_ne_zero (C:Finset ι) (x:Ideal O×O) (hx:x.2≠0) :
    (sourceFrequencyEquiv p C x).2≠0 := by
  change (commonProductUnit p C:O)^2*x.2≠0
  exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hx

lemma sourceRotatedCoefficient_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (b:GlobalCubeBlock ι) (a:Ideal O×O→ℂ) (x:Ideal O×O) :
    ‖sourceRotatedCoefficient p hg b a x‖=‖a ((sourceFrequencyEquiv p b.common).symm x)‖ := by
  have hprime (i:ι):Prime (Ideal.span {p i}):=
    Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have hμ : ‖(UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)‖=1 := by
    have hh:=congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj b.firstDivisor)
    simp only [norm_mul,norm_one] at hh
    change ‖FirstCauchyArithmetic.supportMobius (fun i=>Ideal.span {p i}) b.firstDivisor‖=1
    nlinarith [norm_nonneg (FirstCauchyArithmetic.supportMobius (fun i=>Ideal.span {p i}) b.firstDivisor)]
  simp only [sourceRotatedCoefficient,norm_mul,hμ,commonCubePhase_norm,one_mul]

theorem rawCanonicalBlock_eq_oriented
    (pool:Finset ι) (b:GlobalCubeBlock ι) (hb:GlobalCubeAdmissible b)
    (s:Finset (Ideal O×O)) (a:Ideal O×O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) (hell:0<ell)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    rawCanonicalBlock p hp hcop hg pool b s a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell =
    orientedCubeFirstBlock p hp hcop hg pool b (s.image (sourceFrequencyEquiv p b.common))
      (sourceRotatedCoefficient p hg b a) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
  have hq:b.cube.swap.Admissible := by
    constructor
    · change b.cube.rightDivisor⊆b.cube.swap.support
      rw [cube_swap_support]
      exact hb.1.2
    · change b.cube.leftDivisor⊆b.cube.swap.support
      rw [cube_swap_support]
      exact hb.1.1
  have hc:Disjoint b.common b.cube.swap.support := by
    rw [cube_swap_support]
    exact hb.2.1
  have hback:sourceGlobalBlock b.cube.swap b.common b.firstDivisor=b := by
    cases b
    simp only [sourceGlobalBlock,CubeCoordinates.swap_swap]
  rw [orientedCubeFirstBlock_eq_sum_single,Finset.sum_image]
  · unfold rawCanonicalBlock
    dsimp only
    apply Finset.sum_congr rfl
    intro x hx
    have hmode:=canonicalSource_mode_attachment p hp hcop hg pool b.cube.swap hq b.common b.firstDivisor hc
      x.1 x.2 Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell hell hV₁ hV₂
    rw [hback] at hmode
    have hidx : (x.1,(commonProductUnit p b.common:O)^2*x.2)=sourceFrequencyEquiv p b.common x := rfl
    rw [hidx] at hmode
    simp only [sourceRotatedCoefficient,Equiv.symm_apply_apply]
    calc
      _ = a x*((UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)/
          (primeProductNorm p b.firstDivisor:ℂ)*
          actualFirstKernel p hp hcop hg (pool\(b.cube.swap.support∪b.common)) b.cube.swap.support
            (fun i=>b.cube.swap.leftExponent i+b.cube.swap.rightExponent i) b.cube.swap.leftBit b.cube.swap.rightBit
            (canonicalCubeResidual p hg b.cube.swap b.common true Ψ₁ m₁ (idealGenerator x.1) (fun U=>g₁ (columnLog p ell U)))
            (canonicalCubeResidual p hg b.cube.swap b.common false Ψ₂ m₂ (idealGenerator x.1) (fun U=>g₂ (columnLog p ell U)))
            W (fun _=>1) (fun _=>1) 1 1 K (primeSubsetGenerator (fun i=>Ideal.span {p i}) b.firstDivisor) x.2) := by ring
      _ = _ := by rw [hmode];ring
  · exact fun x hx y hy hxy=>(sourceFrequencyEquiv p b.common).injective hxy

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem rawCanonicalTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (hWin₁ : ∀ t,g₁ t≠0 → V₁ t=1) (hWin₂ : ∀ t,g₂ t≠0 → V₂ t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H U : ℝ),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,rawCanonicalBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hc₁,hs₁,hb₁,hc₂,hs₂,hb₂,htransfer⟩ :=
    orientedTwoPassage_quantitative W g₁ g₂ V₁ V₂ M₁ M₂ N₁ N₂ hM₁ hM₂ hN₁ hN₂ hg₁ hg₂ hV₁ hV₂ ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hc₁,hs₁,hb₁,hc₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H U
    hΓ hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  let s' := fun b:GlobalCubeBlock ι=>(s b).image (sourceFrequencyEquiv p b.common)
  let a' := fun b:GlobalCubeBlock ι=>sourceRotatedCoefficient p hg b (a b)
  have heq : (∑b∈blocks,rawCanonicalBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell)=
      ∑b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s' b) (a' b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
    apply Finset.sum_congr rfl
    intro b hb
    exact rawCanonicalBlock_eq_oriented p hp hcop hg pool b (hadm b hb) (s b) (a b)
      Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell hell hWin₁ hWin₂
  rw [heq]
  apply htransfer p hp hinj hcop hg hc hpr pool blocks s' a' w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H U
    hΓ hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    dsimp only [a']
    rw [sourceRotatedCoefficient_norm p hg hinj,Equiv.symm_apply_apply]
    exact ha b hb y hy
  · exact hadm
  · exact hb₁
  · exact hb₂
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_label]
    exact hsf b hb y hy
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    exact sourceFrequencyEquiv_row_ne_zero p b.common y (hs0 b hb y hy)
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_label]
    exact hf b hb y hy
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_row_norm]
    exact hh b hb y hy

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)

theorem padded_orientedCubeFirstBlock_input_transfer
    (W V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ : ℝ) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤M₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    ∃ C : ℝ,0≤C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ,ℂ)) (Ksrc K ell B F Ymax : ℝ),
      0<Ksrc → 0<K → 0<ell → 0<B → 0<F →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ ≤
      (Ksrc/K)*C*Ymax^deltaLoss*
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F true b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F false b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by
  obtain ⟨C,hC,hfirst⟩ := first_passage_full_uniform_input_family W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ Ksrc K ell B F Ymax hKsrc hK hell hB hF hΨ₁ hΨ₂ hw ha hYmax hsf hs0 hmap hT0 hT
  by_cases hempty : blocks=∅
  · subst blocks
    simp only [Finset.sum_empty,mul_zero,norm_zero,Real.sqrt_zero,le_refl]
  have hne : blocks.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let E₁ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)
  let E₂ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)
  let v := fun b => w b*globalCubeCoefficient p K ell B F true b
  have hv (b) (hb : b∈blocks) : 0≤v b := mul_nonneg (hw b hb)
    (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hE₁ (b) : 0≤E₁ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hE₂ (b) : 0≤E₂ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hden : 0<ell*B^2*F := by positivity
  have hYmax0 : 0≤Ymax := by
    obtain ⟨b,hb⟩ := hne
    exact (globalPooledRowScale_pos K ell B F hK hell hB hF _).le.trans (hYmax b hb)
  have hpref : 0≤(Ksrc/K)*C*Ymax^deltaLoss := mul_nonneg (mul_nonneg (div_nonneg hKsrc.le hK.le) hC) (Real.rpow_nonneg hYmax0 deltaLoss)
  have hpoint (b) (hb : b∈blocks) : (ell*B^2*F)⁻¹*
      ‖orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ ≤
      ((Ksrc/K)*C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
    have hFB : Disjoint (globalCubePool pool b) b.cube.support := by
      apply Finset.disjoint_left.mpr
      intro i hi hiB
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB)
    have hX₁ := globalCubeColumnScale_pos p hp ell hell true b
    have hX₂ := globalCubeColumnScale_pos p hp ell hell false b
    have hD := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor
    have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalFirstIndex p true (b.withCommon ∅))
    have hswapD := FirstPassCubeLabels.dilationLabel_swap p b.cube.support
      (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit
    have hh := hfirst p hp hinj hcop hg hc hpr (globalCubePool pool b) b.cube.support hFB
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit b.cube.support_pos
      Ψ₁ Ψ₂ m₁ m₂ (fun A => g₁ (columnLog p (globalCubeColumnScale p ell true b) A))
      (fun A => g₂ (columnLog p (globalCubeColumnScale p ell false b) A))
      (fun A hA => hΨ₁ _) (fun A hA => hΨ₂ _)
      _ _ hX₁ hX₂ Ksrc hKsrc (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) (primeSubsetGenerator_ne_zero _ _)
      (s b) (T b) (a b) (w b) (globalFirstPooledRow p K ell B F true (b.withCommon ∅))
      (hw b hb) hY.le (hsf b hb) (hs0 b hb) (by simpa only [hswapD] using hmap b hb) (hT0 b hb) (hT b hb) (ha b hb)
    rw [firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit true,
      firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit false,
      FirstPassCubeLabels.cubeActiveSupport_swap b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit] at hh
    have hscl := globalCube_first_scalar_bound p hp K ell B F hK hell hB hF b
    have hscl' : (ell*B^2*F)⁻¹*((Ksrc/primeProductNorm p b.firstDivisor)/
        ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
          (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) ≤
        (Ksrc/K)*globalCubeCoefficient p K ell B F true b := by
      have hKratio : Ksrc=(Ksrc/K)*K := by field_simp
      calc
        _ = (Ksrc/K)*((ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
          ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
            (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖)) := by
          conv_lhs => rw [hKratio]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscl (div_nonneg hKsrc.le hK.le)
    have hpow := Real.rpow_le_rpow hY.le (hYmax b hb) hδ.le
    have hmul := mul_le_mul_of_nonneg_left hh
      (show 0≤(ell*B^2*F)⁻¹*(primeProductNorm p b.firstDivisor)⁻¹ by positivity)
    simp only [orientedCubeFirstBlock,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_of_nonneg hD.le,←mul_assoc]
    apply hmul.trans
    calc
      _ = ((ell*B^2*F)⁻¹*((Ksrc/primeProductNorm p b.firstDivisor)/
          ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
            (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))*
          (w b*C*(globalFirstPooledRow p K ell B F true (b.withCommon ∅))^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by dsimp [E₁,E₂,globalCubeInputFamilyEnergy];ring
      _ ≤ ((Ksrc/K)*globalCubeCoefficient p K ell B F true b)*(w b*C*Ymax^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        apply mul_le_mul hscl'
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hw b hb) hC))
          (mul_nonneg (mul_nonneg (hw b hb) hC) (Real.rpow_nonneg hY.le _))
          (mul_nonneg (div_nonneg hKsrc.le hK.le) (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _))
      _ = _ := by dsimp [v];ring
  rw [norm_mul, norm_inv]
  have hn : ‖(ell*B^2*F : ℂ)‖=ell*B^2*F := by
    norm_cast
    exact abs_of_pos hden
  rw [hn]
  calc
    _ ≤ (ell*B^2*F)⁻¹*∑ b∈blocks,‖orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hden.le)
    _ ≤ ∑ b∈blocks,((Ksrc/K)*C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ = ((Ksrc/K)*C*Ymax^deltaLoss)*∑ b∈blocks,Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Real.sqrt_mul (hv b hb),Real.sqrt_mul (hv b hb)]
      have hs := Real.sq_sqrt (hv b hb)
      calc
        _ = ((Ksrc/K)*C*Ymax^deltaLoss)*(Real.sqrt (v b))^2*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by rw [hs]
        _ = _ := by ring
    _ ≤ ((Ksrc/K)*C*Ymax^deltaLoss)*(Real.sqrt (∑ b∈blocks,v b*E₁ b)*Real.sqrt (∑ b∈blocks,v b*E₂ b)) :=
      mul_le_mul_of_nonneg_left (by
        have hcauchy := Real.sum_sqrt_mul_sqrt_le blocks.attach
          (fun b => mul_nonneg (hv b.val b.property) (hE₁ b.val))
          (fun b => mul_nonneg (hv b.val b.property) (hE₂ b.val))
        simpa only [Finset.sum_attach (f := fun b => Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b)),
          Finset.sum_attach (f := fun b => v b*E₁ b),Finset.sum_attach (f := fun b => v b*E₂ b)] using hcauchy) hpref
    _ = _ := by simp only [v,E₁,E₂,globalCubeCoefficient_side,mul_assoc]

end SecondPassArithmetic

end

end OAI

end Source179

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/PaddedPassage.lean; sha256: 324b2bf1a21040a9994dbd94853f14d8bca1aa297a78be699bc11e9ab95e50d8 -/
section Source180
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem padded_orientedTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ Ksrc K ell B F H U : ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ ≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := padded_orientedCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  obtain ⟨windows₁,C₁,Cd₁,Ct₁,hC₁,hCd₁,hCt₁,hwc₁,hws₁,hwb₁,hleft⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₁ V₁ M₁ hM₁ hg₁ true A J N
  obtain ⟨windows₂,C₂,Cd₂,Ct₂,hC₂,hCd₂,hCt₂,hwc₂,hws₂,hwb₂,hright⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₂ V₂ M₂ hM₂ hg₂ false A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCfirst,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  have hB0 : 0<B := by linarith
  let T := fun b => globalCubeFirstTargets p b (s b)
  have hT0 (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) : z≠0 :=
    globalCubeFirstTargets_ne_zero p hp b (s b) (hsf b hb) (hs0 b hb) z hz
  have hT (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) :=
    globalCubeFirstTargets_norm_bound p hp b (s b) K ell B F hK hell hB0 hF
      (hb₁ b hb) (hb₂ b hb) (hf b hb) (hh b hb) z hz
  have hTc (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F false (b.withCommon ∅) := by
    rw [globalFirstPooledRow_side]
    exact hT b hb z hz
  have hblock := hfirst p hp hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ Ksrc K ell B F
    (globalFirstRowCap K ell B F) hKsrc hK hell hB0 hF hΨ₁ hΨ₂ (fun b hb => (hw b hb).1) ha
    (fun b hb => globalFirstPooledRow_le_cap p hp K ell B F hK hell hB0 hF b (hadm b hb) (hb₁ b hb) (hb₂ b hb))
    hsf hs0 (fun b _ x hx => globalCubeFirstTargets_mem p b (s b) x hx) hT0 hT
  have hl := hleft p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₁ m₁ T
    hΓ hw hK hell hB hF hH hU hellU1 hadm hΨ₁ hb₁ hb₂ hT hT0
  have hr := hright p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₂ m₂ T
    hΓ hw hK hell hB hF hH hU hellU2 hadm hΨ₂ hb₁ hb₂ hTc hT0
  have hprefix : 0≤(Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss :=
    mul_nonneg (mul_nonneg (div_nonneg hKsrc.le hK.le) hCfirst) (Real.rpow_nonneg (globalFirstRowCap_pos K ell B F hK hell hB0 hF).le _)
  exact hblock.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hprefix)
    (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (mul_nonneg hprefix (Real.sqrt_nonneg _)))

theorem padded_rawCanonicalTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (hWin₁ : ∀ t,g₁ t≠0 → V₁ t=1) (hWin₂ : ∀ t,g₂ t≠0 → V₂ t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ Ksrc K ell B F H U : ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,rawCanonicalBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell‖ ≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hc₁,hs₁,hb₁,hc₂,hs₂,hb₂,htransfer⟩ :=
    padded_orientedTwoPassage_quantitative W g₁ g₂ V₁ V₂ M₁ M₂ N₁ N₂ hM₁ hM₂ hN₁ hN₂ hg₁ hg₂ hV₁ hV₂ ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hc₁,hs₁,hb₁,hc₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  let s' := fun b:GlobalCubeBlock ι=>(s b).image (sourceFrequencyEquiv p b.common)
  let a' := fun b:GlobalCubeBlock ι=>sourceRotatedCoefficient p hg b (a b)
  have heq : (∑b∈blocks,rawCanonicalBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell)=
      ∑b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s' b) (a' b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell := by
    apply Finset.sum_congr rfl
    intro b hb
    exact rawCanonicalBlock_eq_oriented p hp hcop hg pool b (hadm b hb) (s b) (a b)
      Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell hell hWin₁ hWin₂
  rw [heq]
  apply htransfer p hp hinj hcop hg hc hpr pool blocks s' a' w Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    dsimp only [a']
    rw [sourceRotatedCoefficient_norm p hg hinj,Equiv.symm_apply_apply]
    exact ha b hb y hy
  · exact hadm
  · exact hb₁
  · exact hb₂
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_label]
    exact hsf b hb y hy
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    exact sourceFrequencyEquiv_row_ne_zero p b.common y (hs0 b hb y hy)
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_label]
    exact hf b hb y hy
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_row_norm]
    exact hh b hb y hy

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

def firstFrequencyDisk (R:ℝ) : Finset O :=
  (ShortDraftLatticeCount.rowNormBall ⌈R⌉₊).filter (fun h=>‖eisEmbedding h‖^2≤R)

lemma mem_firstFrequencyDisk (R:ℝ) (h:O) :
    h∈firstFrequencyDisk R ↔ ‖eisEmbedding h‖^2≤R := by
  constructor
  · exact fun hh=>(Finset.mem_filter.mp hh).2
  · intro hh
    apply Finset.mem_filter.mpr
    refine ⟨?_,hh⟩
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    rw [eisEmbedding_norm_sq_eq_absNorm_span] at hh
    exact_mod_cast hh.trans (Nat.le_ceil R)

lemma firstFrequencyDisk_zero (R:ℝ) (hR:0≤R) : (0:O)∈firstFrequencyDisk R := by
  rw [mem_firstFrequencyDisk]
  simpa using hR

lemma outside_firstFrequencyDisk (R:ℝ) (h:O) (hh:h∉firstFrequencyDisk R) :
    R<‖eisEmbedding h‖^2 := lt_of_not_ge (fun hb=>hh ((mem_firstFrequencyDisk R h).mpr hb))

lemma firstFrequencyDisk_unit_invariant (R:ℝ) (u:Oˣ) (h:O) :
    (u:O)*h∈firstFrequencyDisk R ↔ h∈firstFrequencyDisk R := by
  simp only [mem_firstFrequencyDisk,GaussGeneratorTransport.norm_eisEmbedding_unit_mul]

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

lemma euclideanCoordinateVector_eq_basis (j : Fin 3) :
    euclideanCoordinateVector j=EuclideanSpace.basisFun (Fin 3) ℝ j := by
  rw [EuclideanSpace.basisFun_apply]
  rfl

lemma schwartz_toL2_norm_sq (g : 𝓢(EuclideanSpatial,ℂ)) :
    ‖g.toLp 2 volume‖^2=∫p,‖g p‖^2 := by
  calc
    ‖g.toLp 2 volume‖^2=inner ℝ (g.toLp 2 volume) (g.toLp 2 volume) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫p,inner ℝ (g.toLp 2 volume p) (g.toLp 2 volume p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [g.coeFn_toLp 2 volume] with p hp
      rw [hp,real_inner_self_eq_norm_sq]

def kernelLocalizedDensity (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) : ℝ :=
  ‖kernelLocalizedField χ f p‖^2+∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
    (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2

lemma kernelLocalizedDensity_eq_schwartz (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) :
    kernelLocalizedDensity χ f p=‖kernelLocalizedSchwartz χ f p‖^2+
      ∑j : Fin 3,‖(∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)) p‖^2 := by
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,euclideanCoordinateVector_eq_basis,
    kernelLocalizedSchwartz_coe]
  rfl

lemma kernelLocalizedDensity_integrable (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    Integrable (kernelLocalizedDensity χ f) volume := by
  change Integrable (fun p => kernelLocalizedDensity χ f p) volume
  simp_rw [kernelLocalizedDensity_eq_schwartz]
  exact ((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq.add
    (integrable_finsetSum _ (fun j _ =>
      ((∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).memLp 2 volume).norm.integrable_sq))

lemma kernelLocalizedH1_norm_sq (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    ‖kernelLocalizedH1 χ f‖^2=∫p,kernelLocalizedDensity χ f p := by
  rw [euclideanH1_norm_sq,kernelLocalizedH1_embedding,PiLp.norm_sq_eq_of_L2]
  simp_rw [kernelLocalizedH1_gradient,schwartz_toL2_norm_sq,kernelLocalizedDensity_eq_schwartz]
  rw [integral_add (((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq)
    (integrable_finsetSum _ (fun j _ =>
      ((∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).memLp 2 volume).norm.integrable_sq)),
    integral_finsetSum _ (fun j _ =>
      ((∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).memLp 2 volume).norm.integrable_sq)]

lemma kernelLocalizedDensity_zero (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∉tsupport χ.func) : kernelLocalizedDensity χ f p=0 := by
  have hz : kernelLocalizedField χ f=ᶠ[𝓝 p]0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
    simp only [kernelLocalizedField,hq,Pi.zero_apply,zero_smul]
  simp only [kernelLocalizedDensity,hz.self_of_nhds,hz.fderiv_eq,fderiv_zero,
    Pi.zero_apply,_root_.zero_apply,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero]

lemma kernelLocalizedDensity_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) (M D A : ℝ)
    (hM : (χ.func p)^2≤M)
    (hD : (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D)
    (hA : (χ.func p)^2≤A*(p 2)^2) :
    kernelLocalizedDensity χ f p≤
      (M+2*D)*‖kernelTestField f p‖^2+
        2*A*kernelTestEnergyDensity f (euclideanToHyperbolic p) := by
  have he := kernelLocalizedField_energy_bound χ f p hp
  have he' : (p 2)^2*(∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤
      (p 2)^2*(2*A*kernelTestEnergyDensity f (euclideanToHyperbolic p)+
        2*D*‖kernelTestField f p‖^2) := by
    refine he.trans ?_
    calc
      _ ≤ 2*(A*(p 2)^2)*kernelTestEnergyDensity f (euclideanToHyperbolic p)+
          2*(p 2)^2*D*‖kernelTestField f p‖^2 := by
        gcongr
        · exact kernelTestEnergyDensity_nonneg _ _
      _ = _ := by ring
  have hs := le_of_mul_le_mul_left he' (sq_pos_of_pos hp)
  have hm : ‖kernelLocalizedField χ f p‖^2≤M*‖kernelTestField f p‖^2 := by
    simp only [kernelLocalizedField,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    exact mul_le_mul_of_nonneg_right hM (sq_nonneg _)
  unfold kernelLocalizedDensity
  nlinarith

lemma kernelEuclideanProjection_volume_integrable (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (b : ℝ) (hb : 0≤b)
    (hheight : ∀p∈S,p 2≤b) (g : KernelQuotient→ℝ)
    (hg : Integrable g (integralQuotientVolume globalKubotaKernel)) :
    IntegrableOn (fun p => g (kernelEuclideanProjection p)) S volume := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hh := (hm.integrable_comp_of_integrable hg.integrableOn).smul_measure
    (c := ENNReal.ofReal (b^3)) ENNReal.ofReal_ne_top
  exact hh.mono_measure (euclideanVolume_le_heightCube_hyperbolic S hS hpos b hb hheight)

theorem kernelLocalizedH1_norm_sq_le (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (M D A b : ℝ) (hM0 : 0≤M) (hD0 : 0≤D) (hA0 : 0≤A) (hb : 0≤b)
    (hheight : ∀p∈tsupport χ.func,p 2≤b)
    (hM : ∀p∈tsupport χ.func,(χ.func p)^2≤M)
    (hD : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D)
    (hA : ∀p∈tsupport χ.func,(χ.func p)^2≤A*(p 2)^2)
    (f : kernelSmoothTests) :
    ‖kernelLocalizedH1 χ f‖^2≤b^3*((M+2*D)*‖kernelSmoothTestsToL2 f‖^2+
      2*A*kernelDirichletEnergy f) := by
  let G : KernelQuotient→ℝ := fun q =>
    (M+2*D)*‖f.1 q‖^2+2*A*kernelQuotientEnergyDensity f q
  have hG : Integrable G (integralQuotientVolume globalKubotaKernel) :=
    (((kernelSmoothTests_memLp f).norm.integrable_sq).const_mul _).add
      ((kernelQuotientEnergyDensity_integrable f).const_mul _)
  have hGn : ∀q,0≤G q := by
    intro q
    dsimp only [G]
    positivity [kernelQuotientEnergyDensity_nonneg f q]
  have hS := χ.compact.measurableSet
  have hGI := kernelEuclideanProjection_volume_integrable (tsupport χ.func) hS χ.positive
    hinj b hb hheight G hG
  rw [kernelLocalizedH1_norm_sq]
  calc
    (∫p,kernelLocalizedDensity χ f p) =
        ∫p in tsupport χ.func,kernelLocalizedDensity χ f p :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (kernelLocalizedDensity_zero χ f)).symm
    _ ≤ ∫p in tsupport χ.func,G (kernelEuclideanProjection p) := by
      apply setIntegral_mono_on (kernelLocalizedDensity_integrable χ f).integrableOn hGI hS
      intro p hp
      exact kernelLocalizedDensity_le χ f p (χ.positive hp) M D A (hM p hp) (hD p hp) (hA p hp)
    _ ≤ b^3*∫q,G q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_volume_integral_le (tsupport χ.func) hS χ.positive hinj
        b hb hheight G hG hGn
    _ = _ := by
      dsimp only [G]
      rw [integral_add (((kernelSmoothTests_memLp f).norm.integrable_sq).const_mul _)
        ((kernelQuotientEnergyDensity_integrable f).const_mul _),integral_const_mul,integral_const_mul,
        ←kernelSmoothTestsToL2_norm_sq]
      rfl

theorem kernelLocalizedH1_bounded (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      ‖kernelLocalizedH1 χ f‖^2≤C*(‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f) := by
  have hgrad : Continuous (fun p : EuclideanSpatial =>
      ∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) := by
    apply continuous_finsetSum
    intro j hj
    exact (((χ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2)
  have hratio : ContinuousOn (fun p : EuclideanSpatial => (χ.func p)^2/(p 2)^2) (tsupport χ.func) :=
    (χ.smooth.continuous.pow 2).continuousOn.div (by fun_prop)
      (fun p hp => pow_ne_zero _ (ne_of_gt (χ.positive hp)))
  obtain ⟨m,hm⟩ := χ.compact.bddAbove_image (χ.smooth.continuous.pow 2).continuousOn
  obtain ⟨d,hd⟩ := χ.compact.bddAbove_image hgrad.continuousOn
  obtain ⟨a,ha⟩ := χ.compact.bddAbove_image hratio
  obtain ⟨b,hb⟩ := χ.compact.bddAbove_image (f := fun p : EuclideanSpatial => p 2) (by fun_prop)
  let M := max 0 m
  let D := max 0 d
  let A := max 0 a
  let B := max 0 b
  have hM0 : 0≤M := le_max_left _ _
  have hD0 : 0≤D := le_max_left _ _
  have hA0 : 0≤A := le_max_left _ _
  have hB0 : 0≤B := le_max_left _ _
  have hheight : ∀p∈tsupport χ.func,p 2≤B := fun p hp =>
    (hb ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hM : ∀p∈tsupport χ.func,(χ.func p)^2≤M := fun p hp =>
    (hm ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hD : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D := fun p hp =>
    (hd ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hA : ∀p∈tsupport χ.func,(χ.func p)^2≤A*(p 2)^2 := fun p hp =>
    (div_le_iff₀ (sq_pos_of_pos (χ.positive hp))).mp
      ((ha ⟨p,hp,rfl⟩).trans (le_max_right _ _))
  refine ⟨B^3*(M+2*D+2*A),by positivity,fun f => ?_⟩
  refine (kernelLocalizedH1_norm_sq_le χ hinj M D A B hM0 hD0 hA0 hB0 hheight hM hD hA f).trans ?_
  rw [mul_assoc (B^3) (M+2*D+2*A)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB0 3)
  have hm0 := sq_nonneg ‖kernelSmoothTestsToL2 f‖
  have he0 := kernelDirichletEnergy_nonneg f
  nlinarith [mul_nonneg (by positivity : 0≤M+2*D) he0,mul_nonneg hA0 hm0]

def kernelLocalizedSchwartzLinear (χ : PositiveChartCutoff) :
    kernelSmoothTests →ₗ[ℂ] 𝓢(EuclideanSpatial,ℂ) where
  toFun := kernelLocalizedSchwartz χ
  map_add' f g := by
    ext p
    change χ.func p • (kernelTestField f p+kernelTestField g p)=_
    exact smul_add _ _ _
  map_smul' c f := by
    ext p
    change χ.func p • (c • kernelTestField f p)=c • (χ.func p • kernelTestField f p)
    exact smul_comm _ _ _

def kernelLocalizedH1Linear (χ : PositiveChartCutoff) : kernelSmoothTests →ₗ[ℂ] EuclideanH1 where
  toFun := kernelLocalizedH1 χ
  map_add' f g := by
    apply euclideanH1Embedding_injective
    simp only [map_add,kernelLocalizedH1_embedding]
    rw [show kernelLocalizedSchwartz χ (f+g)=kernelLocalizedSchwartz χ f+kernelLocalizedSchwartz χ g
      from (kernelLocalizedSchwartzLinear χ).map_add f g]
    rfl
  map_smul' c f := by
    apply euclideanH1Embedding_injective
    simp only [map_smul,kernelLocalizedH1_embedding,RingHom.id_apply]
    rw [show kernelLocalizedSchwartz χ (c•f)=c•kernelLocalizedSchwartz χ f
      from (kernelLocalizedSchwartzLinear χ).map_smul c f]
    rfl

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

namespace CubicEisenstein

abbrev KernelEnergyAmbient := WithLp 2 (KernelQuotientL2 × KernelGradientL2)

def kernelEnergyCore : kernelSmoothTests →ₗ[ℂ] KernelEnergyAmbient :=
  (WithLp.linearEquiv 2 ℂ (KernelQuotientL2 × KernelGradientL2)).symm.toLinearMap.comp
    (kernelSmoothTestsToL2.prod kernelGradientLinear)

def kernelEnergyGraphSubmodule : Submodule ℂ KernelEnergyAmbient :=
  (LinearMap.range kernelEnergyCore).topologicalClosure

abbrev KernelEnergyGraph := kernelEnergyGraphSubmodule

instance kernelEnergyGraph_complete : CompleteSpace KernelEnergyGraph :=
  (LinearMap.range kernelEnergyCore).isClosed_topologicalClosure.completeSpace_coe

example : InnerProductSpace ℂ KernelEnergyGraph := inferInstance

def kernelEnergyGraphCore : kernelSmoothTests →ₗ[ℂ] KernelEnergyGraph :=
  kernelEnergyCore.codRestrict kernelEnergyGraphSubmodule
    (fun f => (LinearMap.range kernelEnergyCore).le_topologicalClosure ⟨f,rfl⟩)

lemma kernelEnergyGraphCore_dense : DenseRange kernelEnergyGraphCore := by
  rw [DenseRange,Subtype.dense_iff,←Set.range_comp]
  change closure (Set.range kernelEnergyCore)⊆closure (Set.range kernelEnergyCore)
  rfl

def kernelEnergyMass : KernelEnergyGraph →L[ℂ] KernelQuotientL2 :=
  (ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).toContinuousLinearMap.comp
      kernelEnergyGraphSubmodule.subtypeL)

def kernelEnergyGradient : KernelEnergyGraph →L[ℂ] KernelGradientL2 :=
  (ContinuousLinearMap.snd ℂ KernelQuotientL2 KernelGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).toContinuousLinearMap.comp
      kernelEnergyGraphSubmodule.subtypeL)

lemma kernelEnergyMass_core (f : kernelSmoothTests) :
    kernelEnergyMass (kernelEnergyGraphCore f)=kernelSmoothTestsToL2 f := rfl

lemma kernelEnergyGradient_core (f : kernelSmoothTests) :
    kernelEnergyGradient (kernelEnergyGraphCore f)=kernelGradientToL2 f := rfl

lemma kernelEnergyGraph_norm_sq (u : KernelEnergyGraph) :
    ‖u‖^2=‖kernelEnergyMass u‖^2+‖kernelEnergyGradient u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

lemma kernelEnergyGraphCore_norm_sq (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore f‖^2=‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f := by
  rw [kernelEnergyGraph_norm_sq,kernelEnergyMass_core,kernelEnergyGradient_core,
    kernelGradientToL2_norm_sq]

lemma kernelEnergyMass_dense : DenseRange kernelEnergyMass := by
  apply kernelSmoothTestsToL2_dense.mono
  rintro _ ⟨f,rfl⟩
  exact ⟨kernelEnergyGraphCore f,rfl⟩

lemma kernelLocalizedH1_graph_bound (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,∀f : kernelSmoothTests,
      ‖kernelLocalizedH1Linear χ f‖≤C*‖kernelEnergyGraphCore f‖ := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedH1_bounded χ hinj
  refine ⟨Real.sqrt C,fun f => ?_⟩
  have hh := hbound f
  rw [←kernelEnergyGraphCore_norm_sq] at hh
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mp
  change ‖kernelLocalizedH1 χ f‖^2≤(Real.sqrt C*‖kernelEnergyGraphCore f‖)^2
  rw [mul_pow,Real.sq_sqrt hC]
  exact hh

def kernelEnergyLocalize (χ : PositiveChartCutoff) : KernelEnergyGraph →L[ℂ] EuclideanH1 :=
  (kernelLocalizedH1Linear χ).extendOfNorm kernelEnergyGraphCore

lemma kernelEnergyLocalize_core (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (f : kernelSmoothTests) :
    kernelEnergyLocalize χ (kernelEnergyGraphCore f)=kernelLocalizedH1 χ f :=
  LinearMap.extendOfNorm_eq kernelEnergyGraphCore_dense (kernelLocalizedH1_graph_bound χ hinj) f

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

namespace CubicEisenstein

def kernelLocalizedL2Linear (χ : PositiveChartCutoff) : kernelSmoothTests →ₗ[ℂ] EuclideanL2 :=
  euclideanH1Embedding.toLinearMap.comp (kernelLocalizedH1Linear χ)

lemma kernelLocalizedL2Linear_apply (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    kernelLocalizedL2Linear χ f=(kernelLocalizedSchwartz χ f).toLp 2 volume := rfl

lemma kernelLocalizedL2_bounded (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      ‖kernelLocalizedL2Linear χ f‖^2≤C*‖kernelSmoothTestsToL2 f‖^2 := by
  obtain ⟨m,hm⟩ := χ.compact.bddAbove_image (χ.smooth.continuous.pow 2).continuousOn
  obtain ⟨b,hb⟩ := χ.compact.bddAbove_image (f := fun p : EuclideanSpatial => p 2) (by fun_prop)
  let M := max 0 m
  let B := max 0 b
  have hM0 : 0≤M := le_max_left _ _
  have hB0 : 0≤B := le_max_left _ _
  have hheight : ∀p∈tsupport χ.func,p 2≤B := fun p hp =>
    (hb ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hM : ∀p∈tsupport χ.func,(χ.func p)^2≤M := fun p hp =>
    (hm ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  refine ⟨B^3*M,by positivity,fun f => ?_⟩
  let G : KernelQuotient→ℝ := fun q => M*‖f.1 q‖^2
  have hG : Integrable G (integralQuotientVolume globalKubotaKernel) :=
    ((kernelSmoothTests_memLp f).norm.integrable_sq).const_mul M
  have hGn : ∀q,0≤G q := fun q => mul_nonneg hM0 (sq_nonneg _)
  have hS := χ.compact.measurableSet
  have hGI := kernelEuclideanProjection_volume_integrable (tsupport χ.func) hS χ.positive
    hinj B hB0 hheight G hG
  have hfi := ((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq
  rw [kernelLocalizedL2Linear_apply,schwartz_toL2_norm_sq]
  calc
    (∫p,‖kernelLocalizedSchwartz χ f p‖^2) =
        ∫p in tsupport χ.func,‖kernelLocalizedSchwartz χ f p‖^2 := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro p hp
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).self_of_nhds
      change ‖χ.func p • kernelTestField f p‖^2=0
      simp only [hz,Pi.zero_apply,zero_smul,norm_zero,zero_pow (by decide : 2≠0)]
    _ ≤ ∫p in tsupport χ.func,G (kernelEuclideanProjection p) := by
      apply setIntegral_mono_on hfi.integrableOn hGI hS
      intro p hp
      change ‖χ.func p • kernelTestField f p‖^2≤M*‖kernelTestField f p‖^2
      simp only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
      exact mul_le_mul_of_nonneg_right (hM p hp) (sq_nonneg _)
    _ ≤ B^3*∫q,G q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_volume_integral_le (tsupport χ.func) hS χ.positive hinj
        B hB0 hheight G hG hGn
    _ = _ := by
      dsimp only [G]
      rw [integral_const_mul,←kernelSmoothTestsToL2_norm_sq,mul_assoc]

lemma kernelLocalizedL2_bound (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,∀f : kernelSmoothTests,
      ‖kernelLocalizedL2Linear χ f‖≤C*‖kernelSmoothTestsToL2 f‖ := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedL2_bounded χ hinj
  refine ⟨Real.sqrt C,fun f => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hC]
  exact hbound f

def kernelL2Localize (χ : PositiveChartCutoff) : KernelQuotientL2 →L[ℂ] EuclideanL2 :=
  (kernelLocalizedL2Linear χ).extendOfNorm kernelSmoothTestsToL2

lemma kernelL2Localize_core (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (f : kernelSmoothTests) :
    kernelL2Localize χ (kernelSmoothTestsToL2 f)=(kernelLocalizedSchwartz χ f).toLp 2 volume :=
  LinearMap.extendOfNorm_eq kernelSmoothTestsToL2_dense (kernelLocalizedL2_bound χ hinj) f

lemma kernelEnergyLocalize_mass (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (u : KernelEnergyGraph) :
    euclideanH1Embedding (kernelEnergyLocalize χ u)=kernelL2Localize χ (kernelEnergyMass u) := by
  have heq : (fun v => euclideanH1Embedding (kernelEnergyLocalize χ v))=
      fun v => kernelL2Localize χ (kernelEnergyMass v) :=
    kernelEnergyGraphCore_dense.equalizer (by fun_prop) (by fun_prop) (by
      funext f
      simp only [Function.comp_apply,kernelEnergyLocalize_core χ hinj,
        kernelLocalizedH1_embedding,kernelEnergyMass_core,kernelL2Localize_core χ hinj])
  exact congrFun heq u

lemma kernelEnergyLocalize_eq_zero_of_mass_zero (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (u : KernelEnergyGraph)
    (hu : kernelEnergyMass u=0) : kernelEnergyLocalize χ u=0 := by
  apply euclideanH1Embedding_eq_zero
  rw [kernelEnergyLocalize_mass χ hinj u,hu,map_zero]

end CubicEisenstein

end

end OAI

end Source180

/- Original source: OAI/NumberTheory/DirichletL/MeanSquare/DiagonalDensity.lean; sha256: fe5c40e52effbe06e56ca897b86b56ff3e69513df6259e1ce2f366bb3da0f045 -/
section Source181
namespace OAI

noncomputable section

namespace InitialMeanSquare

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem initial_diagonal_fixed_profile (g W : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
      (Z Y : ℝ),0<Z → 0<Y →
      ∀K : Finset ι→Finset ι→Finset O,
      (∀G∈F.powerset,∀E∈G.powerset,(0:O)∈K G E) →
      ‖truncatedSecondZero p hg F Ψ m c d
        (fun S => star (normalizedColumn p (fun T => g (columnLog p Z T)) S)) W Y K‖≤C*Y := by
  obtain ⟨C₀,hC₀,h₀⟩ := full_uniform_normalized_second_mass (conjugateProfile g) M
    (conjugateProfile_support_bound g M hgM)
  refine ⟨‖paperRadialFourier W 0‖*C₀+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj F Ψ hΨ m c d Z Y hZ hY K hK
  simp_rw [star_normalizedColumn]
  apply (truncatedSecondZero_norm_le p hg hinj F Ψ m c d _ W Y K hK).trans
  rw [abs_of_pos hY]
  have hh := h₀ p hp hg hinj F Ψ hΨ m c d Z hZ
  calc
    _ ≤ Y*‖paperRadialFourier W 0‖*C₀ := mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ (‖paperRadialFourier W 0‖*C₀+1)*Y := by nlinarith

theorem initial_normalized_diagonal
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1)
      (Z Y : ℝ),0<Z → 0<Y →
      ∀K : Finset ι→Finset ι→Finset O,
      (∀G∈F.powerset,∀E∈G.powerset,(0:O)∈K G E) →
      ‖truncatedSecondZero p hg F Ψ 1 1 1
        (fun S => star (normalizedColumn p
          (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) S)) rowMajorant Y K‖≤C*Y := by
  obtain ⟨C,hC,h⟩ := initial_diagonal_fixed_profile (initialLogProfile W a b ha hs hW)
    rowMajorant (|Real.log a|+|Real.log b|+1) (initialLogProfile_support W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hg hinj F Ψ hΨ Z Y hZ hY K hK
  exact h p hp hg hinj F Ψ hΨ 1 1 1 Z Y hZ hY K hK

end

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def initialFrequencyCutoff (Z Y M T : ℝ) : Finset O :=
  secondFrequencyCutoff (Y/(1+Z*Real.exp M)^3) T

theorem initialFrequencyCutoff_zero (Z Y M T : ℝ) :
    (0:O)∈initialFrequencyCutoff Z Y M T := secondFrequencyCutoff_zero _ _

theorem initialFrequencyCutoff_valid
    {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (Ψ : O→*ℂ) (m c d : O) (g : 𝓢(ℝ,ℂ)) (M Z Y T : ℝ)
    (hZ : 0<Z) (hY : 0<Y) (hgM : ∀t,g t≠0 → |t|≤M)
    (G E S R : Finset ι) (hEG : E⊆G) (hSR : Disjoint S R)
    (hw : residualPairWeight p hg Ψ Ψ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p Z V)) (G∪U))
      (fun U => normalizedColumn p (fun V => g (columnLog p Z V)) (G∪U)) S R≠0)
    (k : O) (hk : k∉initialFrequencyCutoff Z Y M T) :
    T≤(Y/(‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2*
      ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2))*‖eisEmbedding k‖^2 := by
  let lengthScale : ℝ := 1+Z*Real.exp M
  have hL : 0<lengthScale := by dsimp [lengthScale]; positivity
  obtain ⟨hG,hE,hS,hR⟩ := residualPairWeight_support_bounds p hp hg Ψ m c d g M Z hZ hgM G E S R hEG hw
  have hZL : Z*Real.exp M≤lengthScale := by dsimp [lengthScale]; linarith
  have hn : ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2=primeProductNorm p S*primeProductNorm p R :=
    active_norm_sq_disjoint p S R hSR
  have hden : ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2*
      ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2≤lengthScale^3 := by
    rw [primeSubsetGenerator_norm_eq_productNorm,hn]
    have hSRn := mul_le_mul (hS.trans hZL) (hR.trans hZL)
      (FirstPassCubeLabels.primeProductNorm_pos p hp R).le hL.le
    have hESR := mul_le_mul (hE.trans hZL) hSRn
      (mul_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
        (FirstPassCubeLabels.primeProductNorm_pos p hp R).le) hL.le
    nlinarith
  have hden0 : 0<‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2*
      ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2 := by
    rw [primeSubsetGenerator_norm_eq_productNorm,hn]
    exact mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp E)
      (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp S) (FirstPassCubeLabels.primeProductNorm_pos p hp R))
  have hout := (outside_secondFrequencyCutoff (Y/lengthScale^3) T (by positivity) k hk).le
  exact hout.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hY.le hden0 hden) (sq_nonneg _))

theorem initial_tail_polynomial (g W : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0 → |t|≤M) (A : ℕ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
      (Z Y T : ℝ),0<Z → 0<Y → 0≤T →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (normalizedColumn p (fun V => g (columnLog p Z V))) W Y
        (fun _ _ => initialFrequencyCutoff Z Y M T)‖≤
        C*(1+Z*Real.exp M)^4*Y*(1+(1+Z*Real.exp M)^3/Y)^2/(1+T)^A := by
  obtain ⟨s,C,hC,h⟩ := full_uniform_secondSourceTail_bound A
  let P : ℝ := C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let C₀ : ℝ := 128^4*(SchwartzMap.seminorm ℝ 0 0 g)^2*P
  have hP : 0≤P := by dsimp [P]; positivity
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Z Y T hZ hY hT
  have hb := h p hp hg hinj hc F Ψ m c d
    (normalizedColumn p (fun V => g (columnLog p Z V))) W Y T hY hT
    (fun _ _ => initialFrequencyCutoff Z Y M T)
    (fun G hG E S hS R hR hSR hw k hk => initialFrequencyCutoff_valid p hp hg Ψ m c d g M Z Y T
      hZ hY hgM G E.val S R (Finset.mem_powerset.mp E.property) hSR hw k hk)
  have hpoly := secondSourceTailCost_polynomial p hp hg hinj F Ψ hΨ m c d g M Z Y T
    (1+Z*Real.exp M) P A hZ hY hT hP (by linarith [mul_pos hZ (Real.exp_pos M)]) (by linarith) hgM
  apply (hb.trans hpoly).trans
  calc
    _ = C₀*(1+Z*Real.exp M)^4*Y*(1+(1+Z*Real.exp M)^3/Y)^2/(1+T)^A := by dsimp [C₀]; ring
    _ ≤ _ := by gcongr; linarith

def initialTailHeight (Z Y M : ℝ) : ℝ :=
  (1+Z*Real.exp M)^2*(1+(1+Z*Real.exp M)^3/Y)

theorem initialTailHeight_pos (Z Y M : ℝ) (hZ : 0<Z) (hY : 0<Y) :
    0 < initialTailHeight Z Y M := by unfold initialTailHeight; positivity

theorem initial_tail_fixed_profile (g W : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
      (Z Y : ℝ),0<Z → 0<Y →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (fun S => star (normalizedColumn p (fun V => g (columnLog p Z V)) S)) W Y
        (fun _ _ => initialFrequencyCutoff Z Y M (initialTailHeight Z Y M))‖≤C*Y := by
  obtain ⟨C,hC,h⟩ := initial_tail_polynomial (conjugateProfile g) W M
    (conjugateProfile_support_bound g M hgM) 2
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Z Y hZ hY
  simp_rw [star_normalizedColumn]
  apply (h p hp hg hinj hc F Ψ hΨ m c d Z Y (initialTailHeight Z Y M) hZ hY
    (initialTailHeight_pos Z Y M hZ hY).le).trans
  have hth := initialTailHeight_pos Z Y M hZ hY
  apply (div_le_iff₀ (by positivity : 0<(1+initialTailHeight Z Y M)^2)).mpr
  have hh : (1+Z*Real.exp M)^4*(1+(1+Z*Real.exp M)^3/Y)^2≤(1+initialTailHeight Z Y M)^2 := by
    have hp := initialTailHeight_pos Z Y M hZ hY
    calc
      _ = (initialTailHeight Z Y M)^2 := by unfold initialTailHeight; ring
      _ ≤ _ := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hh (show 0≤C*Y by positivity)
  nlinarith

end

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)
open ConcreteTraceCRT (eisEmbedding)

def initialErrorWindow (a b : ℝ) : ℝ := |Real.log a|+|Real.log b|+1

def initialErrorCutoff (a b Z Y : ℝ) : Finset O :=
  initialFrequencyCutoff Z Y (initialErrorWindow a b)
    (initialTailHeight Z Y (initialErrorWindow a b))

theorem initialErrorCutoff_zero (a b Z Y : ℝ) : (0:O)∈initialErrorCutoff a b Z Y :=
  initialFrequencyCutoff_zero _ _ _ _

def initialErrorFrequencyBound (a b Z Y : ℝ) : ℝ :=
  3*(initialTailHeight Z Y (initialErrorWindow a b)*
    (1+Z*Real.exp (initialErrorWindow a b))^3/Y+2)^2

theorem initialErrorCutoff_norm_bound (a b Z Y : ℝ) (hZ : 0<Z) (hY : 0<Y)
    (k : O) (hk : k∈initialErrorCutoff a b Z Y) :
    ‖eisEmbedding k‖^2≤ initialErrorFrequencyBound a b Z Y := by
  let M := initialErrorWindow a b
  let v : ℝ := initialTailHeight Z Y M/(Y/(1+Z*Real.exp M)^3)
  have hv : 0≤v := by
    dsimp [v]
    exact div_nonneg (initialTailHeight_pos Z Y M hZ hY).le (by positivity)
  have hb := secondFrequencyCutoff_norm_sq_le (Y/(1+Z*Real.exp M)^3)
    (initialTailHeight Z Y M) k hk
  have hc : (⌈v⌉₊:ℝ)+1≤v+2 := by
    have hh := (Nat.ceil_lt_add_one hv).le
    linarith
  apply hb.trans
  change 3*((⌈v⌉₊:ℝ)+1)^2≤_
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc 2) (by norm_num : (0:ℝ)≤3)
  convert hsq using 1
  dsimp [initialErrorFrequencyBound,v,M]
  congr 2
  field_simp

theorem initial_normalized_errors
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1)
      (Z Y : ℝ),0<Z → 0<Y →
      let G := normalizedColumn p
        (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T))
      let K := fun (_ _ : Finset ι) => initialErrorCutoff a b Z Y
      ‖truncatedSecondZero p hg F Ψ 1 1 1 (fun T => star (G T)) rowMajorant Y K‖+
        ‖secondSourceTail p hp hg hinj F Ψ 1 1 1 (fun T => star (G T)) rowMajorant Y K‖≤C*Y := by
  obtain ⟨Cd,hCd,hd⟩ := initial_normalized_diagonal W a b ha hs hW
  obtain ⟨Ct,hCt,ht⟩ := initial_tail_fixed_profile (initialLogProfile W a b ha hs hW)
    rowMajorant (initialErrorWindow a b) (initialLogProfile_support W a b ha hs hW)
  refine ⟨Cd+Ct,by positivity,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ Z Y hZ hY
  dsimp only
  have h₁ := hd p hp hg hinj F Ψ hΨ Z Y hZ hY
    (fun (_ _ : Finset ι) => initialErrorCutoff a b Z Y)
    (fun G hG E hE => initialErrorCutoff_zero a b Z Y)
  have h₂ := ht p hp hg hinj hc F Ψ hΨ 1 1 1 Z Y hZ hY
  change ‖secondSourceTail p hp hg hinj F Ψ 1 1 1
    (fun T => star (normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V)) T))
    rowMajorant Y (fun (_ _ : Finset ι) => initialErrorCutoff a b Z Y)‖≤Ct*Y at h₂
  linarith

end

open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem outside_mean_square_source_with_errors
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃C : ℝ,0<C ∧ ∀{q : ℕ} (χ : DirichletCharacter ℂ q)
      (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
      (hSp : ∀P∈S,Prime P) (Z Y : ℝ),0<Z → 0<Y → b*Z≤D →
    ∀T : Finset O,(∀z∈T,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Y) → (∀z∈T,z≠0) →
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    let p := poolPrimary F
    let hp := poolPrimary_ne_zero F hF
    let hg := poolPrimary_good F hF
    letI : ∀i : primePool F,(Ideal.span {p i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
      intro i j hij
      apply Subtype.ext
      simpa only [p,poolPrimary_span F hF] using hij
    let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
    let Ψ := conjugateMonoid (normCharacter χ)
    (∑z∈T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)/Z≤
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
        rowMajorant Y (fun _ _ => (initialErrorCutoff a b Z Y).erase 0)‖+
      C*Y-‖G ∅‖^2 := by
  obtain ⟨C,hC,h⟩ := initial_normalized_errors W a b ha hs hW
  refine ⟨C,hC,?_⟩
  intro q χ S D hbad hSp Z Y hZ hY hD T hT hT0
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let p := poolPrimary F
  let hp := poolPrimary_ne_zero F hF
  let hg := poolPrimary_good F hF
  let : ∀i : primePool F,(Ideal.span {p i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
    intro i j hij
    apply Subtype.ext
    simpa only [p,poolPrimary_span F hF] using hij
  let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
  let Ψ := conjugateMonoid (normCharacter χ)
  let K : Finset (primePool F)→Finset (primePool F)→Finset O := fun _ _ => initialErrorCutoff a b Z Y
  have he := h p hp hg hinj (poolPrimary_odd F hF) Finset.univ Ψ
    (conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)) Z Y hZ hY
  have hm := outside_mean_square_source χ S D hbad hSp W a b Z Y ha hZ hY hs hW hD T hT hT0 K
  have hz := Complex.re_le_norm (truncatedSecondZero p hg Finset.univ Ψ 1 1 1
    (fun V => star (G V)) rowMajorant Y K)
  change ‖truncatedSecondZero p hg Finset.univ Ψ 1 1 1 (fun V => star (G V)) rowMajorant Y K‖+
    ‖secondSourceTail p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V)) rowMajorant Y K‖≤C*Y at he
  apply hm.trans
  linarith

end

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem initial_nonzero_source_norm_le_squarefree_bins
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1) (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g W : 𝓢(ℝ,ℂ)) (Z H M Kmax : ℝ) (hZ : 0 < Z)
    (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z M,
      elementNorm (sourceObservation p x).1 ≤ Kmax) :
    let G := fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S
    ‖truncatedSecondSource p hp hg hinj F Ψ m 1 1 G W H (fun C E => (K C E).erase 0)‖ ≤
      ∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray
            (initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)) G G W H‖ := by
  dsimp only
  apply (initial_nonzero_source_norm_le_bins p hp hcop hg hinj hc hpr
    F Ψ m g W Z H M Kmax hZ hgM K hK).trans_eq
  apply Finset.sum_congr rfl
  intro ray hray
  apply Finset.sum_congr rfl
  intro R hR
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg norm
  apply initial_source_eq_squarefree p hp hcop hg Ψ m ray F _ _ _ _ W H
  intro x hx
  exact (secondSupportedSector_mem p F K R Z M x (Finset.mem_filter.mp hx).1).2.1

end

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)

def initialSquarefreeBinCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε : ℝ) (j : SecondLogIndex)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) : ℝ :=
  let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
    (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃))

theorem initial_nonzero_source_squarefree_transfer
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU : ∀ t, g t ≠ 0 → U t=1) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (N J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cₛ : ℝ), 0 ≤ C ∧ 0 ≤ Cₛ ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O)
        (K : Finset ι → Finset ι → Finset O) (Z H Kmax : ℝ),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        (∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z A,
          elementNorm (sourceObservation p x).1 ≤ Kmax) →
        ∃ B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ,
          (∀ ray R j q, 0 ≤ B ray R j q) ∧
          (∀ ray R j q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B ray R j q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖truncatedSecondSource p hp hg hinj F Ψ m 1 1
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            W H (fun C E => (K C E).erase 0)‖ ≤
            C*(∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp A),
              ∑ j ∈ secondLogBinBox (Z*Real.exp A) Kmax,
                initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H A ε j windows (B ray R j)) := by
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,ht⟩ :=
    initial_subbin_transfer U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m K Z H Kmax hZ hH hΨ hK
  let B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H A j
        (initialSquarefreeSector p (secondLogSector p ∅ F K R Z A j)) hZ hH hΨ
        (Finset.filter_subset _ _))
  have hB (ray : SecondRayIndex) (R : Finset ι) (j : SecondLogIndex) :=
    Classical.choose_spec (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H A j
        (initialSquarefreeSector p (secondLogSector p ∅ F K R Z A j)) hZ hH hΨ
        (Finset.filter_subset _ _))
  refine ⟨B,fun ray R j => (hB ray R j).1,fun ray R j => (hB ray R j).2.1,?_⟩
  apply (initial_nonzero_source_norm_le_squarefree_bins p hp hcop hg hinj hc hpr F Ψ m
    g W Z H A Kmax hZ hgA K hK).trans
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ray hray
  apply Finset.sum_le_sum
  intro R hR
  apply Finset.sum_le_sum
  intro j hj
  convert (hB ray R j).2.2 using 1 ; dsimp only [initialSquarefreeBinCost, B] ; ring

end

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem initialSquarefreeBinCost_of_canonical_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hCₛ : 0 ≤ Cₛ) (hCc : 0 ≤ Cchild)
    (j : SecondLogIndex) (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ)
    (J N : ℕ) (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hchild : ∀ q,
      let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      childGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X q ≤
        (Cchild*(X*initialLogLabel j)^2)*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) :
    initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ*(∫ t : ℝ,firstLogDensity 0 t)^3)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let G := sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X
  let E := Cchild*(X*initialLogLabel j)^2
  let S := (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N
  have hpR : 0 < primeProductNorm p R := primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hpR)
  have hlabel : 0 < initialLogLabel j := by
    unfold initialLogLabel secondLogE secondLogV
    exact mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) (Real.exp_pos _)
  have hE : 0 ≤ E := mul_nonneg hCc (sq_nonneg _)
  have hS : 0 < S := by
    dsimp [S]
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  have hG : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have henergy : ∀ q, G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J := by
    intro q
    exact (sourceGeometricMean_le_ideal p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X q).trans (hchild q)
  have hb := polynomial_density_cost B G J S Cₛ E hS hCₛ hE hB hG hdec henergy
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  calc
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ*E/S)*(∫ t : ℝ,firstLogDensity 0 t)^3) := mul_le_mul_of_nonneg_left hb hpref
    _ = _ := by
      dsimp only [E,X,S]
      rw [initial_log_mass Z (primeProductNorm p R) hpR.ne',
        mul_pow (Z/primeProductNorm p R) (Real.exp 2) 2]
      have he : (Real.exp 2)^2=Real.exp 4 := by
        rw [pow_two,←Real.exp_add]
        norm_num
      rw [he]
      have hz := hZ.ne'
      have hr := hpR.ne'
      field_simp

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem positive_nested_density_transfer (f G : Frequency → ℝ) (J : ℕ)
    (hG : Continuous G) (M : ℝ) (hGM : ∀ q, ‖G q‖ ≤ M)
    (C : ℝ) (hf : ∀ q, 0 ≤ f q)
    (hbound : ∀ q, f q ≤ C*tripleLogDensity J q*G q) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,f (x,y,z)) ≤
      C*(∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,tripleLogDensity J (x,y,z)*G (x,y,z)) := by
  let u : Frequency → ℝ := fun q => C*(tripleLogDensity J q*G q)
  have hu : Integrable u := (tripleLogDensity_bounded_integrable J G hG M hGM).const_mul C
  have hux (x : ℝ) : Integrable (fun yz : ℝ × ℝ => u (x,yz)) :=
    (tripleLogDensity_slice_integrable J G hG M hGM x).const_mul C
  have huxy (x y : ℝ) : Integrable (fun z : ℝ => u (x,y,z)) := by
    have hd : Integrable (fun z : ℝ =>
        C*firstLogDensity J x*firstLogDensity J y*firstLogDensity J z) :=
      (firstLogDensity_integrable J).const_mul _
    have hgxy : Continuous (fun z : ℝ => G (x,y,z)) :=
      hG.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hi := hd.mul_bdd hgxy.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z : ℝ => hGM (x,y,z)))
    convert hi using 1
    funext z
    dsimp [u,tripleLogDensity]
    ring
  have hz (x y : ℝ) : (∫ z : ℝ,f (x,y,z)) ≤ ∫ z : ℝ,u (x,y,z) := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z : ℝ => hf (x,y,z))) (huxy x y)
    exact Filter.Eventually.of_forall (fun z : ℝ => by simpa only [u,mul_assoc] using hbound (x,y,z))
  have hy (x : ℝ) : (∫ y : ℝ,∫ z : ℝ,f (x,y,z)) ≤ ∫ y : ℝ,∫ z : ℝ,u (x,y,z) := by
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z))))
      (hux x).integral_prod_left (Filter.Eventually.of_forall (hz x))
  have hui : Integrable (fun x : ℝ => ∫ y : ℝ, ∫ z : ℝ,u (x,y,z)) := by
    apply hu.integral_prod_left.congr
    filter_upwards [] with x
    exact integral_prod _ (hux x)
  have hx := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x : ℝ => integral_nonneg
      (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z))))) hui
    (Filter.Eventually.of_forall hy)
  simpa only [u,integral_const_mul] using hx

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem initial_source_density_transfer (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m : O) (T : Finset (O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (B : Frequency → ℝ) (J : ℕ) (S C : ℝ) (hS : 0 < S) (hC : 0 ≤ C)
    (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,S*B q ≤ C*tripleLogDensity J q) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,B (x,y,z)*
      sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (x,y,z)) ≤
    (C/S)*densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m (sourceIdealTarget T) V₁ V₂ X₁ X₂ J := by
  let G := childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m (sourceIdealTarget T) V₁ V₂ X₁ X₂
  have hc₁ := childEnergy_continuous p hp hcop hg F Ψ₁ m (sourceIdealTarget T) V₁ X₁ true false
    (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := childEnergy_continuous p hp hcop hg F Ψ₂ m (sourceIdealTarget T) V₂ X₂ false true
    (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀ q,0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (energyMagnitude p hp hcop hg F Ψ₁ m (sourceIdealTarget T) V₁ X₁ true false)*
    Real.sqrt (energyMagnitude p hp hcop hg F Ψ₂ m (sourceIdealTarget T) V₂ X₂ false true)
  have hGM : ∀ q,‖G q‖ ≤ M := by
    intro q
    rw [Real.norm_of_nonneg (hG0 q)]
    exact mul_le_mul
      (Real.sqrt_le_sqrt (childEnergy_le p hp hcop hg F Ψ₁ m (sourceIdealTarget T) V₁ X₁ true false q.1 q.2.2))
      (Real.sqrt_le_sqrt (childEnergy_le p hp hcop hg F Ψ₂ m (sourceIdealTarget T) V₂ X₂ false true q.2.1 q.2.2))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  change _ ≤ (C/S)*(∫ x : ℝ,∫ y : ℝ,∫ z : ℝ,tripleLogDensity J (x,y,z)*G (x,y,z))
  apply positive_nested_density_transfer
    (fun q => B q*sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ q)
    G J hG M hGM (C/S)
  · intro q
    exact mul_nonneg (hB q) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · intro q
    have hb : B q ≤ (C/S)*tripleLogDensity J q := by
      have hd : B q ≤ (C*tripleLogDensity J q)/S :=
        (le_div_iff₀ hS).mpr (by simpa only [mul_comm] using hdec q)
      convert hd using 1 ; ring
    exact mul_le_mul hb (sourceGeometricMean_le_ideal p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ q)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (div_nonneg hC hS.le) (tripleLogDensity_nonneg _ _))

end InitialMeanSquare

end

end OAI

end Source181

/- Original source: OAI/NumberTheory/DirichletL/MeanSquare/HighRadialBounds.lean; sha256: 62e5ea716c68c1bae7449bceb3650220667fee2ee8d6f972b2e877efa8f09822 -/
section Source182
namespace OAI

noncomputable section

namespace InitialMeanSquare

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open CanonicalQuadraticSieve (Admissible)

theorem initial_squarefree_target_geometry {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (Z M : ℝ) (j : SecondLogIndex) :
    let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
    ∀ z ∈ sourceIdealTarget (s.image (sourceObservation p)),
      Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
      z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 1 := by
  dsimp only
  intro z hz
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hxs,hsq⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxp,hj⟩ := Finset.mem_filter.mp hxs
  have hk := (secondSupportedSector_mem p F K R Z M x hxp).2.2.2.1
  have hgeom := initial_log_target_bounds p hp x hk
  rw [initialLogIndex_eq_second,hj] at hgeom
  refine ⟨initial_squarefree_label_admissible p hp hg hc x hsq,?_,sourceRow_nonzero p x hk,hgeom.2⟩
  simpa only [sourceIdealPoint,elementNorm,eisEmbedding_norm_sq_eq_absNorm_span] using hgeom.1

end

section

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem initialSquarefreeBinCost_of_density_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hCₛ : 0 ≤ Cₛ)
    (j : SecondLogIndex) (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ)
    (J N : ℕ) (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hdensity :
      let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X J ≤
        Cchild*(X*initialLogLabel j)^2) :
    initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let E := densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X J
  let S := (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N
  have hR : 0 < primeProductNorm p R := primeProductNorm_pos p hp R
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hS : 0 < S := by dsimp [S]; positivity
  have hd := initial_source_density_transfer p hp hcop hg F (secondRayMinus Ψ ray)
    (secondRayPlus Ψ ray) (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6)
    X X B J S Cₛ hS hCₛ hB (fun q => by
      simpa only [S,tripleLogDensity,mul_assoc] using hdec q)
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by positivity
  calc
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ/S)*E) := mul_le_mul_of_nonneg_left hd hpref
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ/S)*(Cchild*(X*initialLogLabel j)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdensity (div_nonneg hCₛ hS.le)) hpref
    _ = _ := by
      dsimp only [X,S]
      rw [initial_log_mass Z (primeProductNorm p R) hR.ne',
        mul_pow (Z/primeProductNorm p R) (Real.exp 2) 2]
      have he : (Real.exp 2)^2=Real.exp 4 := by rw [pow_two,←Real.exp_add]; norm_num
      rw [he]
      have hz := hZ.ne'
      have hr := hR.ne'
      field_simp

end

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

lemma initial_bin_row_scale_le (U K : ℝ) (hK : 1 ≤ K) (j : SecondLogIndex)
    (hj : j ∈ secondLogBinBox U K) : secondLogK j ≤ K := by
  have hj' : j.1 < normLogBin U+1 ∧ j.2.1 < normLogBin U+1 ∧ j.2.2 < normLogBin K+1 := by
    simpa only [secondLogBinBox,Finset.mem_product,Finset.mem_range] using hj
  have hscale : secondLogK j ≤ normLogScale (normLogBin K) := by
    unfold secondLogK normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.2.2
  exact hscale.trans (normLogBin_scale_bounds K hK).1

theorem initial_bin_cost_uniform {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M Kmax ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hKmax : 1 ≤ Kmax) (hε : 0 ≤ ε)
    (hCₛ : 0 ≤ Cₛ) (hCc : 0 ≤ Cchild)
    (j : SecondLogIndex) (hj : j ∈ secondLogBinBox (Z*Real.exp M) Kmax)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) (J N : ℕ)
    (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hdensity :
      let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X J ≤
        Cchild*(X*initialLogLabel j)^2) :
    initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      (H*Real.exp 4*Cchild*Cₛ*(Kmax*Real.exp 2)^ε)/primeProductNorm p R*
        ‖secondRayCoefficient ray‖ := by
  have hb := initialSquarefreeBinCost_of_density_bound p hp hcop hg F R Ψ m ray K
    Z H M ε Cₛ Cchild hZ hH hCₛ j windows B J N hB hdec hdensity
  have hR := primeProductNorm_pos p hp R
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hden : 1 ≤ (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
    apply one_le_pow₀
    have hnon : 0 ≤ H*secondLogK j*(primeProductNorm p R)^2/Z^2 := by positivity
    linarith
  have hnum : 0 ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
      ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε := by positivity
  have hrow : (secondLogK j*Real.exp 2)^ε ≤ (Kmax*Real.exp 2)^ε :=
    Real.rpow_le_rpow (mul_pos hk (Real.exp_pos 2)).le
    (mul_le_mul_of_nonneg_right (initial_bin_row_scale_le (Z*Real.exp M) Kmax hKmax j hj)
      (Real.exp_pos 2).le) hε
  calc
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε :=
      hb.trans (div_le_self hnum hden)
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(Kmax*Real.exp 2)^ε :=
      mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = _ := by ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge

theorem outside_prime_divisor_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I Q : Ideal O} (hI : I ∈ outsideIdealsUpTo S D) (hQ : Prime Q)
    (hd : Q ∣ I) : Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  have hQpos : 1 ≤ Ideal.absNorm Q := Nat.one_le_iff_ne_zero.mpr
    (fun hz => hQ.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  have hQI : Ideal.absNorm Q ≤ Ideal.absNorm I :=
    Nat.le_of_dvd (mem_outsideIdealsUpTo.mp hI).1 (map_dvd Ideal.absNorm hd)
  have hQo : Q ∈ outsideIdealsUpTo S D := mem_outsideIdealsUpTo.mpr
    ⟨hQpos, hQI.trans (mem_outsideIdealsUpTo.mp hI).2.1,
      fun P hP hPQ => (mem_outsideIdealsUpTo.mp hI).2.2 P hP (hPQ.trans hd)⟩
  apply mem_primePool_iff.mpr
  refine ⟨Q, Finset.mem_filter.mpr ⟨hQo,hQ.squarefree⟩,?_⟩
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hQ.ne_zero).mpr
    ⟨hQ,dvd_rfl⟩

theorem outside_factors_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I : Ideal O} (hI : I ∈ outsideIdealsUpTo S D) :
    ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  intro Q hQ
  obtain ⟨hprime,hdiv⟩ :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff
      (outsideIdealsUpTo_ne_bot S D I hI)).mp hQ
  exact outside_prime_divisor_mem_pool S D hI hprime hdiv

theorem outside_prime_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {Q : Ideal O} (hQ : Prime Q) (hQD : Ideal.absNorm Q ≤ D)
    (hQS : ∀ P ∈ S, ¬ P ∣ Q) :
    Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  apply outside_prime_divisor_mem_pool S D (I := Q) _ hQ dvd_rfl
  exact mem_outsideIdealsUpTo.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr
      (fun hz => hQ.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz)),hQD,hQS⟩

end

section

open MeasureTheory
open scoped BigOperators Classical

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialElementaryConstant (A V : ℝ) : ℝ := 6*128^4*(Real.exp A*V)^2

lemma initialElementaryConstant_nonneg (A V : ℝ) : 0 ≤ initialElementaryConstant A V := by
  unfold initialElementaryConstant
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_child_energy_elementary (F : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (T : Finset (Ideal O × O)) (V : ℝ → ℂ)
    (X lengthScale K A Vmax a b : ℝ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV : ∀ t,‖V t‖ ≤ Vmax) (hs : ∀ t,V t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) (tn rn : Bool) :
    childEnergy p hp hcop hg F Ψ m T V X tn rn a b ≤
      initialElementaryConstant A Vmax*K*X^2*lengthScale := by
  by_cases hscale : 1 ≤ X*Real.exp A
  · have hb := childEnergy_elementary_normalized p hp hcop hg hc hinj F Ψ hΨ m T V
      X lengthScale K A Vmax a b hX hL hK hA hVmax hV hs hT tn rn
    have hXL : 0 < X*lengthScale := mul_pos hX (zero_lt_one.trans_le hL)
    have hb' := (div_le_iff₀ hXL).mp hb
    rw [max_eq_right hscale] at hb'
    convert hb' using 1
    unfold initialElementaryConstant
    field_simp

  · rw [childEnergy_subunit p hp hcop hg F Ψ m T V X A hX hs
      (lt_of_not_ge hscale) a b tn rn]
    exact mul_nonneg (mul_nonneg (mul_nonneg (initialElementaryConstant_nonneg A Vmax)
      (zero_le_one.trans hK)) (sq_nonneg X)) (zero_le_one.trans hL)

include hc hinj in

theorem initial_child_geometric_elementary (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X lengthScale K A Vmax : ℝ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) (q : Frequency) :
    childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X X q ≤
      initialElementaryConstant A Vmax*K*(X*lengthScale)^2 := by
  let E := initialElementaryConstant A Vmax*K*X^2*lengthScale
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (mul_nonneg (initialElementaryConstant_nonneg A Vmax)
      (zero_le_one.trans hK)) (sq_nonneg X)) (zero_le_one.trans hL)
  have he₁ := initial_child_energy_elementary p hp hcop hg hc hinj F Ψ₁ hΨ₁ m T V₁
    X lengthScale K A Vmax q.1 q.2.2 hX hL hK hA hVmax hV₁ hs₁ hT true false
  have he₂ := initial_child_energy_elementary p hp hcop hg hc hinj F Ψ₂ hΨ₂ m T V₂
    X lengthScale K A Vmax q.2.1 q.2.2 hX hL hK hA hVmax hV₂ hs₂ hT false true
  have hb : childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X X q ≤ E := by
    calc
      _ ≤ Real.sqrt E*Real.sqrt E := mul_le_mul (Real.sqrt_le_sqrt he₁)
        (Real.sqrt_le_sqrt he₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = E := Real.mul_self_sqrt hE
  apply hb.trans
  calc
    E ≤ E*lengthScale := le_mul_of_one_le_right hE hL
    _ = _ := by dsimp only [E]; ring

include hp in

theorem initial_subbin_target_bounds (F R : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (Z M : ℝ) (j : SecondLogIndex)
    (s : Finset (SecondExpansionData ι)) (hs : s ⊆ secondLogSector p ∅ F K R Z M j) :
    ∀ z ∈ sourceIdealTarget (s.image (sourceObservation p)),z.1 ≠ ⊥ ∧
      (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2 := by
  apply sourceIdealTarget_bounds
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  have hx' := hs hx
  obtain ⟨hxsec,hj⟩ := Finset.mem_filter.mp hx'
  have hk := (secondSupportedSector_mem p F K R Z M x hxsec).2.2.2.1
  have hji : initialLogIndex p x=j := (initialLogIndex_eq_second p x).trans hj
  have ht := initial_log_target_bounds p hp x hk
  rw [hji] at ht
  refine ⟨?_,ht.1,?_⟩
  · exact mul_ne_zero (primeSubsetGenerator_ne_zero _ _)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  · exact ht.2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num))
      (normLogScale_pos _).le)

include hc hinj in

theorem initial_subbin_geometric_elementary (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z M A Vmax : ℝ)
    (hZ : 0 < Z) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (q : Frequency) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
    childGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (sourceIdealTarget (s.image (sourceObservation p))) V₁ V₂ X X q ≤
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*(X*initialLogLabel j)^2 := by
  dsimp only
  have hR := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hX : 0 < initialLogColumn Z (primeProductNorm p R) j :=
    div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hR)
  have hL : 1 ≤ initialLogLabel j := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _))
    (Real.one_le_exp (by norm_num))
  have hrow : 1 ≤ secondLogK j*Real.exp 2 :=
    one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  exact initial_child_geometric_elementary p hp hcop hg hc hinj F
    (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (fun a => (secondRayMinus_norm_le Ψ ray a).trans (hΨ a))
    (fun a => (secondRayPlus_norm_le Ψ ray a).trans (hΨ a)) _ _ V₁ V₂
    _ _ _ A Vmax hX hL hrow hA hVmax hV₁ hV₂ hs₁ hs₂
    (initial_subbin_target_bounds p hp F R K Z M j s hs) q

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialRestrictedBinCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (Z H ε : ℝ) (j : SecondLogIndex)
    (V₁ V₂ : ℝ → ℂ) (B : Frequency → ℝ) : ℝ :=
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
    (∫ t₁ : ℝ,∫ t₂ : ℝ,∫ t₃ : ℝ,B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) V₁ V₂ X X (t₁,t₂,t₃))

lemma initialRestrictedBinCost_full {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε : ℝ) (j : SecondLogIndex)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray
      (secondLogSector p ∅ F K R Z M j) Z H ε j (windows 5) (windows 6) B =
    initialBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B := rfl

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_subbin_density_elementary (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
    (∫ t₁ : ℝ,∫ t₂ : ℝ,∫ t₃ : ℝ,B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) V₁ V₂ X X (t₁,t₂,t₃)) ≤
    (Cs*(initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2)*(X*initialLogLabel j)^2)/
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N)*(∫ t : ℝ,firstLogDensity 0 t)^3 := by
  dsimp only
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let G := sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (s.image (sourceObservation p)) V₁ V₂ X X
  let E := initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2)*(X*initialLogLabel j)^2
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hE : 0 ≤ E := mul_nonneg
    (mul_nonneg (initialElementaryConstant_nonneg A Vmax) (mul_nonneg hk.le (Real.exp_pos _).le))
    (sq_nonneg _)
  have hG : ∀ q,0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hbound (q : Frequency) : G q ≤ E :=
    (sourceGeometricMean_le_ideal p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (s.image (sourceObservation p)) V₁ V₂ X X q).trans
    (initial_subbin_geometric_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z M A Vmax
      hZ hA hVmax j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ q)
  have hweighted (q : Frequency) :
      G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J := by
    have h₁ := one_le_pow₀ (show 1 ≤ 1+‖q.1‖ by linarith [norm_nonneg q.1]) (n := J)
    have h₂ := one_le_pow₀ (show 1 ≤ 1+‖q.2.1‖ by linarith [norm_nonneg q.2.1]) (n := J)
    have h₃ := one_le_pow₀ (show 1 ≤ 1+‖q.2.2‖ by linarith [norm_nonneg q.2.2]) (n := J)
    exact (hbound q).trans ((le_mul_of_one_le_right hE h₁).trans
      ((le_mul_of_one_le_right (mul_nonneg hE (zero_le_one.trans h₁)) h₂).trans
        (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hE (zero_le_one.trans h₁))
          (zero_le_one.trans h₂)) h₃)))
  exact polynomial_density_cost B G J _ Cs E (by positivity) hCs hE hB hG hdec hweighted

include hc hinj in

theorem initial_subbin_cost_elementary (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray s Z H ε j V₁ V₂ B ≤
    ((H/primeProductNorm p R)*Real.exp 4*
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
      (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  have hb := initial_subbin_density_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z H M
    A Vmax Cs hZ hH hA hVmax hCs j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J N hB hdec
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hR := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by positivity
  have h := mul_le_mul_of_nonneg_left hb hpref
  apply h.trans_eq
  rw [initial_log_mass Z (primeProductNorm p R) hR.ne',mul_pow]
  have he : (Real.exp 2)^2=Real.exp 4 := by rw [pow_two,←Real.exp_add]; norm_num
  rw [he]
  have hz := hZ.ne'
  have hr := hR.ne'
  field_simp

end

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialRadial (Z H R : ℝ) (j : SecondLogIndex) : ℝ :=
  H*secondLogK j*R^2/Z^2

theorem initial_radial_absorbs_rows (Z H R k : ℝ) (N : ℕ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hR : 1 ≤ R) (hk : 0 ≤ k) :
    H*k^2/(1+H*k*R^2/Z^2)^(N+2) ≤ Z^4/(1+H*k*R^2/Z^2)^N := by
  let r := H*k*R^2/Z^2
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have h1 : 0 < 1+r := by linarith
  have hHR : 1 ≤ H*R^4 := one_le_mul_of_one_le_of_one_le hH (one_le_pow₀ hR)
  have he : Z^4*r^2=(H*k^2)*(H*R^4) := by
    dsimp [r]
    field_simp

  have hnum : H*k^2 ≤ Z^4*r^2 := by
    rw [he]
    exact le_mul_of_one_le_right (mul_nonneg hH0 (sq_nonneg k)) hHR
  change H*k^2/(1+r)^(N+2) ≤ Z^4/(1+r)^N
  calc
    _ ≤ Z^4*r^2/(1+r)^(N+2) := div_le_div_of_nonneg_right hnum (pow_nonneg h1.le _)
    _ ≤ Z^4*(1+r)^2/(1+r)^(N+2) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg h1.le _)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr (by linarith) 2) (by positivity)
    _ = _ := by rw [pow_add]; field_simp

def initialHighRadialConstant (A Vmax Cs : ℝ) : ℝ :=
  Real.exp 8*initialElementaryConstant A Vmax*Cs*(∫ t : ℝ,firstLogDensity 0 t)^3

lemma initialHighRadialConstant_nonneg (A Vmax Cs : ℝ) (hCs : 0 ≤ Cs) :
    0 ≤ initialHighRadialConstant A Vmax Cs := by
  have hi : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t := integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hc := initialElementaryConstant_nonneg A Vmax
  unfold initialHighRadialConstant
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_subbin_cost_radial_decay (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hε : ε ≤ 1)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray s Z H ε j V₁ V₂ B ≤
      initialHighRadialConstant A Vmax Cs*Z^4/primeProductNorm p R*
        ‖secondRayCoefficient ray‖/(1+initialRadial Z H (primeProductNorm p R) j)^N := by
  have hH0 := zero_lt_one.trans_le hH
  have hb := initial_subbin_cost_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z H M
    ε A Vmax Cs hZ hH0 hA hVmax hCs j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J (N+2) hB hdec
  have hR1 := primeProductNorm_ge_one p hp R
  have hR0 := zero_lt_one.trans_le hR1
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hrow : 1 ≤ secondLogK j*Real.exp 2 :=
    one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  have hrowpow : (secondLogK j*Real.exp 2)^ε ≤ secondLogK j*Real.exp 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hrow hε
  have hcc := initialElementaryConstant_nonneg A Vmax
  have hi : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t := integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hfixed := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hpref : 0 ≤ ((H/primeProductNorm p R)*Real.exp 4*
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
      (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖ := by positivity
  have hden : 0 ≤ (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2) := by positivity
  apply hb.trans
  calc
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*
        (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
        (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖*
        (secondLogK j*Real.exp 2)/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrowpow hpref) hden
    _ = (initialHighRadialConstant A Vmax Cs/primeProductNorm p R*‖secondRayCoefficient ray‖)*
        (H*(secondLogK j)^2/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)) := by
      unfold initialHighRadialConstant
      have he : Real.exp 4*(Real.exp 2)^2=Real.exp 8 := by
        rw [pow_two,←Real.exp_add,←Real.exp_add]; norm_num
      rw [←he]
      ring
    _ ≤ (initialHighRadialConstant A Vmax Cs/primeProductNorm p R*‖secondRayCoefficient ray‖)*
        (Z^4/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N) :=
      mul_le_mul_of_nonneg_left (initial_radial_absorbs_rows Z H (primeProductNorm p R)
        (secondLogK j) N hZ hH hR1 hk.le) (by positivity)
    _ = _ := by unfold initialRadial; ring

end InitialMeanSquare

end

end OAI

end Source182

/- Original source: OAI/NumberTheory/DirichletL/MeanSquare/SourceRemainders.lean; sha256: 17730eaa323879fc918194fddc78c1b95db74c949e85f6842dcf0049442f3141 -/
section Source183
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialHighRadialCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι))
    (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ)
    (Z H U Kmax ε θ : ℝ) (V₁ V₂ : ℝ → ℂ) : ℝ :=
  ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F U,∑ j ∈ secondLogBinBox U Kmax,
    if Z^θ < initialRadial Z H (primeProductNorm p R) j then
      initialRestrictedBinCost p hp hcop hg F R Ψ m ray (s ray R j) Z H ε j V₁ V₂ (B ray R j)
    else 0

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_high_radial_sum (F : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
    (K : Finset ι → Finset ι → Finset O) (Z H U Kmax M ε θ A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hε : ε ≤ 1)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι))
    (hs : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,
      s ray R j ⊆ secondLogSector p ∅ F K R Z M j)
    (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ) (J N : ℕ)
    (hB : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,0 ≤ B ray R j q)
    (hdec : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B ray R j q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialHighRadialCost p hp hcop hg F Ψ m s B Z H U Kmax ε θ V₁ V₂ ≤
      (initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass*
        ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) := by
  have hconstant := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hzpow : 0 < Z^θ := Real.rpow_pos_of_pos hZ _
  unfold initialHighRadialCost
  apply initial_harmonic_aggregation p hinj F U Kmax _ (by positivity)
  intro ray R hR j hj
  split_ifs with hh
  · have hc' := initial_subbin_cost_radial_decay p hp hcop hg hc hinj F R Ψ hΨ m ray K
      Z H M ε A Vmax Cs hZ hH hε hA hVmax hCs j (s ray R j) (hs ray R hR j hj)
      V₁ V₂ hV₁ hV₂ hs₁ hs₂ (B ray R j) J N (hB ray R hR j hj) (hdec ray R hR j hj)
    have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
    have hd : (Z^θ)^N ≤ (1+initialRadial Z H (primeProductNorm p R) j)^N :=
      pow_le_pow_left₀ hzpow.le (by linarith) N
    have hnum : 0 ≤ initialHighRadialConstant A Vmax Cs*Z^4/primeProductNorm p R*
        ‖secondRayCoefficient ray‖ := by positivity
    apply hc'.trans
    calc
      _ ≤ (initialHighRadialConstant A Vmax Cs*Z^4/primeProductNorm p R*
        ‖secondRayCoefficient ray‖)/(Z^θ)^N :=
        div_le_div_of_nonneg_left hnum (pow_pos hzpow _) hd
      _ = _ := by ring
  · have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
    positivity

end

theorem initial_log_harmonic_polynomial :
    ∃ C : ℝ,0 < C ∧ ∀ (Y U Kmax : ℝ),1 ≤ Y → 0 < U → 0 < Kmax → U ≤ Y → Kmax ≤ Y →
      ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) ≤ C*Y^2 := by
  obtain ⟨C,hC,hbound⟩ := initial_log_box_small_power 1 (by norm_num)
  refine ⟨C*(256*Real.exp 1),by positivity,?_⟩
  intro Y U Kmax hY hU hK hUY hKY
  have hc := hbound Y U Kmax hY hU hK hUY hKY
  rw [Real.rpow_one] at hc
  have hu := normLogBin_le_log_upper U Y hU hUY hY
  have hl := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hY)
  have hlog : (normLogBin U : ℝ)+1 ≤ 2*Y := by linarith
  have hh : 128*Real.exp 1*(normLogBin U+1 : ℝ) ≤ (256*Real.exp 1)*Y := by
    have he := Real.exp_pos (1:ℝ)
    nlinarith
  have hnon : 0 ≤ 128*Real.exp 1*(normLogBin U+1 : ℝ) := by positivity
  calc
    _ ≤ (C*Y)*((256*Real.exp 1)*Y) := mul_le_mul hc hh hnon (by positivity)
    _ = _ := by ring

theorem initial_high_radial_order (θ τ : ℝ) (hθ : 0 < θ) :
    ∃ N : ℕ,38+τ ≤ θ*(N : ℝ) := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((38+τ)/θ)
  refine ⟨N,?_⟩
  have hh := (div_lt_iff₀ hθ).mp hN
  linarith

theorem initial_high_radial_negligible (θ τ A Vmax Cs Ccap : ℝ) (N : ℕ)
    (hN : 38+τ ≤ θ*(N : ℝ)) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hCs : 0 ≤ Cs) (hcap : 1 ≤ Ccap) :
    ∃ C : ℝ,0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
      (K : Finset ι → Finset ι → Finset O) (Z H U Kmax M ε : ℝ),
      1 ≤ Z → 1 ≤ H → 0 < U → 0 < Kmax → ε ≤ 1 →
      U ≤ Ccap*Z^17 → Kmax ≤ Ccap*Z^17 →
      ∀ (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι)),
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,
        s ray R j ⊆ secondLogSector p ∅ F K R Z M j) →
      ∀ (V₁ V₂ : ℝ → ℂ),
      (∀ t,‖V₁ t‖ ≤ Vmax) → (∀ t,‖V₂ t‖ ≤ Vmax) →
      (∀ t,V₁ t ≠ 0 → |t| ≤ A) → (∀ t,V₂ t ≠ 0 → |t| ≤ A) →
      ∀ (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ) (J : ℕ),
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,0 ≤ B ray R j q) →
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B ray R j q ≤
        Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) →
      initialHighRadialCost p hp hcop hg F Ψ m s B Z H U Kmax ε θ V₁ V₂ ≤ C*Z^(-τ) := by
  obtain ⟨Clog,hClog,hlog⟩ := initial_log_harmonic_polynomial
  let Cbase := initialHighRadialConstant A Vmax Cs*initialRayMass*Clog*Ccap^2
  have hfixed := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hray := initialRayMass_nonneg
  have hbase : 0 ≤ Cbase := by
    dsimp [Cbase]
    exact mul_nonneg (mul_nonneg (mul_nonneg hfixed initialRayMass_nonneg) hClog.le) (sq_nonneg _)
  refine ⟨Cbase+1,by linarith,?_⟩
  intro ι _ p hp _ hcop hg hc hinj F Ψ hΨ m K Z H U Kmax M ε hZ hH hU hK hε hUcap hKcap
    s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J hB hdec
  have hZ0 := zero_lt_one.trans_le hZ
  have hy : 1 ≤ Ccap*Z^17 := one_le_mul_of_one_le_of_one_le hcap (one_le_pow₀ hZ)
  have hlogs := hlog (Ccap*Z^17) U Kmax hy hU hK hUcap hKcap
  have hb := initial_high_radial_sum p hp hcop hg hc hinj F Ψ hΨ m K Z H U Kmax M ε θ
    A Vmax Cs hZ0 hH hε hA hVmax hCs s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J N hB hdec
  have hscalar : Z^(38 : ℕ)/(Z^θ)^N ≤ Z^(-τ) := by
    have he : Z^(38 : ℕ)/(Z^θ)^N=Z^((38 : ℝ)-θ*(N : ℝ)) := by
      rw [Real.rpow_sub hZ0,Real.rpow_mul_natCast hZ0.le]
      norm_cast
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ (initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass*
        ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) := hb
    _ = ((initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass)*
        (((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ))) := by ring
    _ ≤ ((initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass)*
        (Clog*(Ccap*Z^17)^2) := mul_le_mul_of_nonneg_left hlogs (by positivity)
    _ = Cbase*(Z^(38 : ℕ)/(Z^θ)^N) := by dsimp [Cbase]; ring
    _ ≤ Cbase*Z^(-τ) := mul_le_mul_of_nonneg_left hscalar hbase
    _ ≤ (Cbase+1)*Z^(-τ) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ0.le _)

end

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

theorem initialErrorFrequencyBound_le (a b Z H : ℝ) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    initialErrorFrequencyBound a b Z H ≤
      48*(1+Real.exp (initialErrorWindow a b))^16*Z^16 := by
  let Q := 1+Z*Real.exp (initialErrorWindow a b)
  have hZ0 := zero_lt_one.trans_le hZ
  have hH0 := zero_lt_one.trans_le hH
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    have hh : 0 ≤ Z*Real.exp (initialErrorWindow a b) := by positivity
    linarith
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have h3 : Q^3/H ≤ Q^3 := div_le_self (pow_nonneg hQ0 _) hH
  have hinner : 1+Q^3/H ≤ 2*Q^3 := by linarith [one_le_pow₀ hQ (n := 3)]
  have hT : initialTailHeight Z H (initialErrorWindow a b) ≤ 2*Q^5 := by
    change Q^2*(1+Q^3/H) ≤ 2*Q^5
    calc
      _ ≤ Q^2*(2*Q^3) := mul_le_mul_of_nonneg_left hinner (sq_nonneg Q)
      _ = _ := by ring
  have hT0 : 0 ≤ initialTailHeight Z H (initialErrorWindow a b) :=
    (initialTailHeight_pos Z H _ hZ0 hH0).le
  have hv : initialTailHeight Z H (initialErrorWindow a b)*Q^3/H ≤ 2*Q^8 := by
    calc
      _ ≤ initialTailHeight Z H (initialErrorWindow a b)*Q^3 :=
        div_le_self (mul_nonneg hT0 (pow_nonneg hQ0 _)) hH
      _ ≤ (2*Q^5)*Q^3 := mul_le_mul_of_nonneg_right hT (pow_nonneg hQ0 _)
      _ = _ := by ring
  have hv2 : initialTailHeight Z H (initialErrorWindow a b)*Q^3/H+2 ≤ 4*Q^8 := by
    linarith [one_le_pow₀ hQ (n := 8)]
  have hb : initialErrorFrequencyBound a b Z H ≤ 48*Q^16 := by
    unfold initialErrorFrequencyBound
    change 3*(initialTailHeight Z H (initialErrorWindow a b)*Q^3/H+2)^2 ≤ _
    calc
      _ ≤ 3*(4*Q^8)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hv2 2) (by norm_num)
      _ = _ := by ring
  have hQZ : Q ≤ (1+Real.exp (initialErrorWindow a b))*Z := by
    dsimp [Q]
    nlinarith
  calc
    _ ≤ 48*Q^16 := hb
    _ ≤ 48*((1+Real.exp (initialErrorWindow a b))*Z)^16 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 hQZ 16) (by norm_num)
    _ = _ := by rw [mul_pow]; ring

def initialErrorRowBound (a b Z H : ℝ) : ℝ :=
  Z*Real.exp (initialErrorWindow a b)*initialErrorFrequencyBound a b Z H

lemma initialErrorRowBound_pos (a b Z H : ℝ) (hZ : 0 < Z) (hH : 0 < H) :
    0 < initialErrorRowBound a b Z H := by
  have ht := initialTailHeight_pos Z H (initialErrorWindow a b) hZ hH
  unfold initialErrorRowBound initialErrorFrequencyBound
  positivity

theorem initialErrorRowBound_valid {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (F R : Finset ι) (a b Z H : ℝ) (hZ : 0 < Z) (hH : 0 < H)
    (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F (fun _ _ => initialErrorCutoff a b Z H) R Z
      (initialErrorWindow a b)) :
    elementNorm (sourceObservation p x).1 ≤ initialErrorRowBound a b Z H := by
  obtain ⟨hG,hE,hV,hk,hkf,hR,hs⟩ := secondSupportedSector_mem p F
    (fun _ _ => initialErrorCutoff a b Z H) R Z (initialErrorWindow a b) x hx
  have he := (secondSourceSupport_bounds p hp Z (initialErrorWindow a b) x hs hE).2.1
  have hf := initialErrorCutoff_norm_bound a b Z H hZ hH x.frequency hkf
  have hh := mul_le_mul he hf (sq_nonneg ‖eisEmbedding x.frequency‖) (by positivity)
  simpa only [initialErrorRowBound,sourceObservation,elementNorm,map_mul,norm_mul,mul_pow,
    primeSubsetGenerator_norm_eq_productNorm] using hh

def initialPolynomialCap (a b : ℝ) : ℝ :=
  1+Real.exp (initialErrorWindow a b)+
    48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16

lemma initialPolynomialCap_ge_one (a b : ℝ) : 1 ≤ initialPolynomialCap a b := by
  unfold initialPolynomialCap
  have he := Real.exp_pos (initialErrorWindow a b)
  have hh : 0 ≤ 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 := by positivity
  linarith

theorem initial_actual_bin_polynomial_caps (a b Z H : ℝ) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    Z*Real.exp (initialErrorWindow a b) ≤ initialPolynomialCap a b*Z^17 ∧
    initialErrorRowBound a b Z H ≤ initialPolynomialCap a b*Z^17 := by
  have he := Real.exp_pos (initialErrorWindow a b)
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hz17 : Z ≤ Z^17 := by
    simpa only [pow_one] using pow_le_pow_right₀ hZ (by decide : 1 ≤ 17)
  have hC1 : Real.exp (initialErrorWindow a b) ≤ initialPolynomialCap a b := by
    unfold initialPolynomialCap
    have hh : 0 ≤ 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 := by positivity
    linarith
  have hC2 : 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 ≤
      initialPolynomialCap a b := by
    unfold initialPolynomialCap
    have hh : 0 ≤ 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 := by positivity
    linarith
  constructor
  · calc
      _ ≤ Real.exp (initialErrorWindow a b)*Z^17 := by
        rw [mul_comm Z]; exact mul_le_mul_of_nonneg_left hz17 he.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hC1 (pow_nonneg hZ0 _)
  · have hb := mul_le_mul_of_nonneg_left (initialErrorFrequencyBound_le a b Z H hZ hH)
      (mul_nonneg hZ0 he.le)
    change initialErrorRowBound a b Z H ≤ _ at hb
    calc
      _ ≤ (Z*Real.exp (initialErrorWindow a b))*(48*(1+Real.exp (initialErrorWindow a b))^16*Z^16) := hb
      _ = (48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16)*Z^17 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC2 (pow_nonneg hZ0 _)

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity normalizedColumn columnLog)

theorem initial_two_windows_bounded (V₁ V₂ : ℝ → ℂ)
    (hc₁ : HasCompactSupport V₁) (hc₂ : HasCompactSupport V₂)
    (hs₁ : Continuous V₁) (hs₂ : Continuous V₂) :
    ∃ A Vmax : ℝ,0 ≤ A ∧ 0 ≤ Vmax ∧
      (∀ t,‖V₁ t‖ ≤ Vmax) ∧ (∀ t,‖V₂ t‖ ≤ Vmax) ∧
      (∀ t,V₁ t ≠ 0 → |t| ≤ A) ∧ (∀ t,V₂ t ≠ 0 → |t| ≤ A) := by
  obtain ⟨A₁,hA₁,hbound₁⟩ := hc₁.exists_pos_le_norm
  obtain ⟨A₂,hA₂,hbound₂⟩ := hc₂.exists_pos_le_norm
  obtain ⟨B₁,hB₁⟩ := hc₁.exists_bound_of_continuous hs₁
  obtain ⟨B₂,hB₂⟩ := hc₂.exists_bound_of_continuous hs₂
  refine ⟨max A₁ A₂,max 0 (max B₁ B₂),?_,le_max_left _ _,?_,?_,?_,?_⟩
  · exact hA₁.le.trans (le_max_left _ _)
  · intro t
    exact (hB₁ t).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro t
    exact (hB₂ t).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro t ht
    have hh : ‖t‖ < A₁ := lt_of_not_ge (fun h => ht (hbound₁ t h))
    simpa only [Real.norm_eq_abs] using hh.le.trans (le_max_left A₁ A₂)
  · intro t ht
    have hh : ‖t‖ < A₂ := lt_of_not_ge (fun h => ht (hbound₂ t h))
    simpa only [Real.norm_eq_abs] using hh.le.trans (le_max_right A₁ A₂)

theorem initial_high_radial_source
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b θ τ ε : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hθ : 0 < θ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ,0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (Z H : ℝ),
      1 ≤ Z → 1 ≤ H → (∀ x,‖Ψ x‖ ≤ 1) →
      ∀ (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι)),
      (∀ ray R j,s ray R j ⊆ secondLogSector p ∅ F
        (fun _ _ => initialErrorCutoff a b Z H) R Z (initialErrorWindow a b) j) →
      let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if Z^θ < initialRadial Z H (primeProductNorm p R) j then
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (s ray R j) G G W H‖ else 0) ≤
      C*Z^(-τ) := by
  obtain ⟨N,hN⟩ := initial_high_radial_order θ τ hθ
  have hM : 0 ≤ initialErrorWindow a b := by unfold initialErrorWindow; positivity
  obtain ⟨windows,Ct,Cs,hCt,hCs,hwc,hws,ht⟩ :=
    initial_subbin_transfer U hUc hUs g W (initialErrorWindow a b) hM hU hgs ε hε (N+2) 0
  obtain ⟨A,Vmax,hA,hVmax,hV₁,hV₂,hs₁,hs₂⟩ :=
    initial_two_windows_bounded (windows 5) (windows 6) (hwc 5) (hwc 6)
      (hws 5).continuous (hws 6).continuous
  obtain ⟨Ch,hCh,hh⟩ := initial_high_radial_negligible θ τ A Vmax Cs (initialPolynomialCap a b)
    N hN hA hVmax hCs (initialPolynomialCap_ge_one a b)
  refine ⟨Ct*Ch+1,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m Z H hZ hH hΨ s hs
  dsimp only
  have hZ0 := zero_lt_one.trans_le hZ
  have hH0 := zero_lt_one.trans_le hH
  let K := fun (_ _ : Finset ι) => initialErrorCutoff a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H (initialErrorWindow a b) j
        (s ray R j) hZ0 hH0 hΨ (hs ray R j))
  have hB (ray : SecondRayIndex) (R : Finset ι) (j : SecondLogIndex) :=
    Classical.choose_spec
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H (initialErrorWindow a b) j
        (s ray R j) hZ0 hH0 hΨ (hs ray R j))
  have hcost := hh p hp hcop hg hc hinj F Ψ hΨ m K Z H
    (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H)
    (initialErrorWindow a b) ε hZ hH (by positivity) (initialErrorRowBound_pos a b Z H hZ0 hH0)
    hε1 (initial_actual_bin_polynomial_caps a b Z H hZ hH).1
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).2
    s (fun ray R _ j _ => hs ray R j) (windows 5) (windows 6) hV₁ hV₂ hs₁ hs₂ B 0
    (fun ray R _ j _ => (hB ray R j).1) (fun ray R _ j _ => (hB ray R j).2.1)
  have hsum :
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if Z^θ < initialRadial Z H (primeProductNorm p R) j then
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (s ray R j) G G W H‖ else 0) ≤
      Ct*initialHighRadialCost p hp hcop hg F Ψ m s B Z H
        (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H) ε θ (windows 5) (windows 6) := by
    unfold initialHighRadialCost
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ray hray
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with hjrad
    · convert (hB ray R j).2.2 using 1 ;
        dsimp only [initialRestrictedBinCost,G,B] ; ring
    · simp
  calc
    _ ≤ Ct*initialHighRadialCost p hp hcop hg F Ψ m s B Z H
        (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H) ε θ (windows 5) (windows 6) := hsum
    _ ≤ Ct*(Ch*Z^(-τ)) := mul_le_mul_of_nonneg_left hcost hCt
    _ ≤ (Ct*Ch+1)*Z^(-τ) := by
      have hz := Real.rpow_nonneg hZ0.le (-τ)
      nlinarith

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma threeBlockExponent_ne_zero_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i≠0 := by
  intro i hi
  by_cases hn:i∈N
  · simp [threeBlockExponent,hn]
  by_cases hp':i∈P
  · simp [threeBlockExponent,hn,hp']
  · have hiC:i∈cubeActiveSupport B v ε₁ ε₂ := by simpa [hn,hp'] using hi
    simp only [threeBlockExponent,ite_eq_right hn,ite_eq_right hp']
    exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2

lemma threeBlockExponent_lt_six_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i<6 := by
  intro i hi
  unfold threeBlockExponent
  split_ifs <;> first | omega | exact ZMod.val_lt _

lemma threeGaussRowFactor_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (d h : O) :
    ‖threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h‖≤‖C₁ N‖*‖C₂ P‖ := by
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  have hG := FiniteGaussPhase.norm_canonicalProductGauss
    (fun i:S=>p i.val) (fun i=>hp i.val) (columnPrimeCoprime p hcop S)
    (fun i=>hg i.val) (fun i=>hc i.val) (fun i=>e i.val)
    (fun i=>threeBlockExponent_ne_zero_on N P B v ε₁ ε₂ i.val i.property)
    (fun i=>threeBlockExponent_lt_six_on N P B v ε₁ ε₂ i.val i.property)
  change ‖star (columnCoefficient p hp hcop hg N*C₁ N)*
    (columnCoefficient p hp hcop hg P*C₂ P)*
    FiniteGaussPhase.canonicalProductGauss (fun i:S=>p i.val) (fun i=>hp i.val)
      (columnPrimeCoprime p hcop S) (fun i=>hg i.val) (fun i=>e i.val)*
    (blockRow p hg S e d*star (blockRow p hg S e h))‖≤_
  simp only [norm_mul,norm_star,SecondPassArithmetic.columnCoefficient_norm_one p hp hcop hg hc,
    hG,one_mul,mul_one]
  apply mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (blockRow_norm_le_one p hg S e d)).trans (blockRow_norm_le_one p hg S e h)

lemma canonicalPairMode_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d h : O) :
    ‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖)*
        (‖C₁ N‖*‖C₂ P‖))*
      ‖paperRadialFourier W ((K/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2)‖ := by
  have hn : 0<‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i hi=>hp i)))
  have ha : K*‖eisEmbedding h‖^2/(‖eisEmbedding d‖^2*
      primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)) =
      (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*
        ‖eisEmbedding h‖^2 := by ring
  simp only [canonicalPairMode,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hK,abs_of_pos hn,ha]
  calc
    _ ≤ (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖))*
      ‖paperRadialFourier W ((K/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2)‖*
      (‖C₁ N‖*‖C₂ P‖) := mul_le_mul_of_nonneg_left
        (threeGaussRowFactor_norm_le p hp hcop hg hc N P B v ε₁ ε₂ C₁ C₂ d h) (by positivity)
    _ = _ := by ring

end

theorem full_uniform_canonicalPairMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K H : ℝ),0<K → 0≤H → ∀(d : O),d≠0 → ∀T:Finset O,
      let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
      (∀h:O,h∉T → H≤scale*‖eisEmbedding h‖^2) →
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K H hK hH d hd T
  dsimp only
  intro hT
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
  let c := ‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖)
  have hscale : 0<scale := div_pos hK (mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))) (primeProductNorm_pos p hp S))
  have hc0 : 0≤c := by dsimp [c]; positivity
  let small : Set O := {h|h∉T}
  let large : Set O := {h|H≤scale*‖eisEmbedding h‖^2}
  let f : small→large := fun h=>⟨h.val,hT h.val h.property⟩
  have hfi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x:large=>x.val) hab)
  have hrad := EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale
  have hmajor := (hrad.subtype small).mul_left c
  have hpnt (h:small) :
      ‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
    canonicalPairMode_norm_le p hp hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d h.val
  have hsmall := Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑'h:small,‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖ :=
      norm_tsum_le_tsum_norm hsmall
    _ ≤ ∑'h:small,c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      hsmall.tsum_le_tsum hpnt hmajor
    _ = c*∑'h:small,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ := tsum_mul_left
    _ ≤ c*∑'h:large,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      mul_le_mul_of_nonneg_left ((hrad.subtype small).tsum_le_tsum_of_inj f hfi
        (fun _ _=>norm_nonneg _) (fun _=>le_rfl) (hrad.subtype large)) hc0
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb W scale H hscale hH) hc0

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open SecondPassArithmetic (firstFrequencyDisk outside_firstFrequencyDisk columnLog_norm_upper)

def canonicalFirstFrequencyRadius {ι : Type*} [DecidableEq ι]
    (p : ι→O) (B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (d : O) (X₁ X₂ K P : ℝ) : ℝ :=
  P*(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*X₁*X₂)/K

theorem firstFrequencyDisk_uniform {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0)
    (N Q B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hNQ : Disjoint N Q) (hNB : Disjoint N B) (hQB : Disjoint Q B)
    (d : O) (hd : d≠0) (X₁ X₂ K P M₁ M₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hK : 0<K)
    (hN : columnLog p X₁ N≤M₁) (hQ : columnLog p X₂ Q≤M₂)
    (h : O) (hh : h∉firstFrequencyDisk
      (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)) :
    P/Real.exp (M₁+M₂)≤
      (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪Q)∪cubeActiveSupport B v ε₁ ε₂)))*
        ‖eisEmbedding h‖^2 := by
  let S := cubeActiveSupport B v ε₁ ε₂
  have hNS : Disjoint N S := hNB.mono_right (Finset.filter_subset _ _)
  have hQS : Disjoint Q S := hQB.mono_right (Finset.filter_subset _ _)
  have hNQS : Disjoint (N∪Q) S := Finset.disjoint_union_left.mpr ⟨hNS,hQS⟩
  have hnorm : primeProductNorm p ((N∪Q)∪S)=
      primeProductNorm p N*primeProductNorm p Q*primeProductNorm p S := by
    rw [primeProductNorm_union p _ _ hNQS,primeProductNorm_union p _ _ hNQ]
  have hNd : 0<‖eisEmbedding d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hU₁ : 0<X₁*Real.exp M₁ := mul_pos hX₁ (Real.exp_pos _)
  have hU₂ : 0<X₂*Real.exp M₂ := mul_pos hX₂ (Real.exp_pos _)
  let slow := K/(‖eisEmbedding d‖^2*(X₁*Real.exp M₁)*(X₂*Real.exp M₂)*primeProductNorm p S)
  have hs : 0<slow := div_pos hK (mul_pos (mul_pos (mul_pos hNd hU₁) hU₂) (primeProductNorm_pos p hp S))
  have hn := columnLog_norm_upper p hp X₁ M₁ hX₁ N hN
  have hq := columnLog_norm_upper p hp X₂ M₂ hX₂ Q hQ
  have hprod : primeProductNorm p N*primeProductNorm p Q≤(X₁*Real.exp M₁)*(X₂*Real.exp M₂) :=
    mul_le_mul hn hq (primeProductNorm_pos p hp Q).le hU₁.le
  have hscale : slow≤K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪Q)∪S)) := by
    apply div_le_div_of_nonneg_left hK.le
      (mul_pos hNd (primeProductNorm_pos p hp _))
    rw [hnorm]
    calc
      _ ≤ ‖eisEmbedding d‖^2*((X₁*Real.exp M₁)*(X₂*Real.exp M₂)*primeProductNorm p S) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
      _ = _ := by ring
  have hr : (P/Real.exp (M₁+M₂))/slow=
      canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P := by
    dsimp [slow,canonicalFirstFrequencyRadius,S]
    rw [Real.exp_add]
    field_simp

  have ho := outside_firstFrequencyDisk _ h hh
  rw [←hr] at ho
  have hbase : P/Real.exp (M₁+M₂)≤slow*‖eisEmbedding h‖^2 := by
    have hz := (div_lt_iff₀ hs).mp ho
    simpa only [mul_comm] using hz.le
  exact hbase.trans (mul_le_mul_of_nonneg_right hscale (sq_nonneg _))

theorem full_uniform_canonicalPairMode_disk_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N Q B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      Disjoint N Q → Disjoint N B → Disjoint Q B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K P M₁ M₂ : ℝ),0<X₁ → 0<X₂ → 0<K → 0≤P →
      columnLog p X₁ N≤M₁ → columnLog p X₂ Q≤M₂ → ∀(d : O),d≠0 →
      let S := (N∪Q)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ Q)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ Q‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 scale)^2*(1+P/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hcop hg hc N Q B v ε₁ ε₂ hNQ hNB hQB C₁ C₂ W V₁ V₂ X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hP hN hQ d hd
  apply hb p hp hcop hg hc N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K _ hK
    (div_nonneg hP (Real.exp_pos _).le) d hd
  intro h hh
  exact firstFrequencyDisk_uniform p hp N Q B v ε₁ ε₂ hNQ hNB hQB d hd
    X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hN hQ h hh

end FirstPassCubeLabels

end

end OAI

end Source183

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/DualZeroMode.lean; sha256: 432fcac889c9a486a39f7fb0ec4268756cd30f0f7b007a5a8f7b33a12436ccab -/
section Source184
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FiniteGaussPhase (canonicalProductGauss_cross_factors)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma threeGaussRowFactor_empty
    (B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (d h : O)
    (hB : cubeActiveSupport B v ε₁ ε₂=∅) :
    threeGaussRowFactor p hp hcop hg ∅ ∅ B v ε₁ ε₂ C₁ C₂ d h=
      star (C₁ ∅)*C₂ ∅ := by
  let : IsEmpty {i:ι // i∈(((∅:Finset ι)∪∅)∪cubeActiveSupport B v ε₁ ε₂)} :=
    ⟨fun x=>by simpa [hB] using x.property⟩
  simp [MixedCrossSeparation.columnCoefficient,FiniteGaussPhase.canonicalProductCoefficient,
    threeGaussRowFactor,canonicalProductGauss_cross_factors,FiniteGaussPhase.angularFactor,
    blockRow,finiteSexticRow]

end FirstPassCubeLabels

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma canonicalCubeResidual_empty (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) :
    canonicalCubeResidual p hg b C negative Ψ m f H ∅=
      H ((if negative then b.rightDivisor else b.leftDivisor)∪C) := by
  simp [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn,
    finiteSquarefreeRow,rowCoprimeMask]

def canonicalCubeDualZero (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
      actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) 0

theorem canonicalCubeDualZero_eq_density
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K=
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
          (star (H₁ (b.rightDivisor∪C))*H₂ (b.leftDivisor∪C))*
          (K:ℂ)*paperRadialFourier W 0*
          ∏i∈C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit,
            (1-(1:ℂ)/Ideal.absNorm (Ideal.span {p i}))
      else 0 := by
  unfold canonicalCubeDualZero
  simp_rw [actualFirstKernel_zero]
  split_ifs with hB
  · simp only [threeGaussRowFactor_empty p hp hcop hg _ _ _ _ _ _ _ _ hB,
      canonicalCubeResidual_empty,Bool.false_eq_true,ite_true,ite_false,one_mul]
    rw [←Finset.sum_mul]
    have hprime (i : ι) : Prime (Ideal.span {p i}) :=
      Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
    have hd (D : Finset ι) : (primeProductNorm p D:ℂ)=
        (Ideal.absNorm (∏i∈D,Ideal.span {p i}):ℂ) := by
      rw [primeProductNorm_eq_ideal_norm,Complex.ofReal_natCast]
    simp_rw [hd]
    rw [primeSubset_moebius_norm_sum _ hprime hinj]
    ring
  · simp only [mul_zero,Finset.sum_const_zero]

theorem canonicalCubeDualZero_norm_le
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    ‖canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        ‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖*|K| *‖paperRadialFourier W 0‖ else 0 := by
  rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj]
  split_ifs with hB
  · let M := C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit
    have hprod : (∏i∈M,(1-(1:ℂ)/Ideal.absNorm (Ideal.span {p i})))=
        ((∏i∈M,(1-(1:ℝ)/Ideal.absNorm (Ideal.span {p i}))):ℝ) := by
      simp only [Complex.ofReal_prod,Complex.ofReal_sub,Complex.ofReal_one,
        Complex.ofReal_div,Complex.ofReal_natCast]
    rw [show (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)=M from rfl,hprod]
    simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (primeDensity_nonneg_le_one (fun i=>Ideal.span {p i}) M).1]
    calc
      _ ≤ 1*(‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖)*|K| *‖paperRadialFourier W 0‖*
          ∏i∈M,(1-(1:ℝ)/Ideal.absNorm (Ideal.span {p i})) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (abs_nonneg _)) (norm_nonneg _))
          (primeDensity_nonneg_le_one (fun i=>Ideal.span {p i}) M).1
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_of_le_one_right
          (show 0≤(1*(‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖)*|K| *‖paperRadialFourier W 0‖) by positivity)
          (primeDensity_nonneg_le_one (fun i=>Ideal.span {p i}) M).2
  · simp

end

open ActualEisensteinCubic
open FirstPassCubeLabels

theorem boundedPrimeSupports_card_positive {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (X : ℝ) (hX : 0<X) :
    ((boundedPrimeSupports p F X).card:ℝ)≤128*X := by
  by_cases hx : 1≤X
  · exact boundedPrimeSupports_card p hinj F X hx
  · have he : boundedPrimeSupports p F X=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      exact hx ((primeProductNorm_ge_one p hp S).trans (Finset.mem_filter.mp hS).2)
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end SecondPassArithmetic

namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open SecondPassArithmetic (boundedPrimeSupports boundedPrimeSupports_card_positive
  columnLog_norm_upper firstFrequencyDisk primeProductNorm_ge_one)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem actualFirstKernel_complement_eq_pairs
    (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) (T : Finset O) :
    (∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val)=
      ∑N∈F.powerset,∑Q∈F.powerset,if Disjoint N Q then
        ∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val
        else 0 := by
  have hs (N Q : Finset ι) : Summable (fun h:{h:O // h∉T}=>if Disjoint N Q then
      canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val else 0) := by
    by_cases hNQ : Disjoint N Q
    · simp only [hNQ,ite_true]
      exact (canonicalPairMode_summable p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd).subtype _
    · simp only [hNQ,ite_false]
      exact summable_zero
  change (∑'h:{h:O // h∉T},∑N∈F.powerset,∑Q∈F.powerset,if Disjoint N Q then
    canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val else 0)=_
  rw [Summable.tsum_finsetSum (fun N hN=>summable_sum (fun Q hQ=>hs N Q))]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Summable.tsum_finsetSum (fun Q hQ=>hs N Q)]
  apply Finset.sum_congr rfl
  intro Q hQ
  split_ifs <;> simp

end

theorem full_uniform_actualFirstKernel_disk_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),Disjoint F B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0≤G₁ → 0≤G₂ → 0<X₁ → 0<X₂ → 0<K → 0≤P →
      (∀N∈F.powerset,‖C₁ N‖≤G₁) → (∀N∈F.powerset,‖C₂ N‖≤G₂) →
      (∀N∈F.powerset,C₁ N≠0 → columnLog p X₁ N≤M₁) →
      (∀N∈F.powerset,C₂ N≠0 → columnLog p X₂ N≤M₂) →
      ∀(d : O),d≠0 →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let slow := K/(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*K)*
        ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_disk_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc F B v ε₁ ε₂ hFB C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂ hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hS₁ hS₂ d hd
  dsimp only
  let U₁:=X₁*Real.exp M₁
  let U₂:=X₂*Real.exp M₂
  let S:=cubeActiveSupport B v ε₁ ε₂
  let T:=firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
  let slow:=K/(‖eisEmbedding d‖^2*primeProductNorm p S*U₁*U₂)
  let tail:ℝ:=(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^A)
  let Q:ℝ:=G₁*G₂*K*tail
  have hU₁:0<U₁:=mul_pos hX₁ (Real.exp_pos _)
  have hU₂:0<U₂:=mul_pos hX₂ (Real.exp_pos _)
  have hNd:0<‖eisEmbedding d‖^2:=sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hslow:0<slow:=div_pos hK (mul_pos (mul_pos (mul_pos hNd (primeProductNorm_pos p hp S)) hU₁) hU₂)
  have hH:0≤P/Real.exp (M₁+M₂):=div_nonneg hP (Real.exp_pos _).le
  have htail:0≤tail:=by dsimp [tail]; positivity
  have hQ:0≤Q:=mul_nonneg (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le) htail
  let rem (N R:Finset ι):ℂ:=if Disjoint N R then
    ∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val else 0
  have hnzero (N R:Finset ι) (hn:C₁ N=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hn]
  have hrzero (N R:Finset ι) (hr:C₂ R=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hr]
  have heq : (∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val)=
      ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,rem N R := by
    rw [actualFirstKernel_complement_eq_pairs p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K hK d hd T]
    change (∑N∈F.powerset,∑R∈F.powerset,rem N R)=_
    calc
      _ = ∑N∈boundedPrimeSupports p F U₁,∑R∈F.powerset,rem N R := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro N hN hn
        have hz:C₁ N=0:=by
          by_contra h
          exact hn (Finset.mem_filter.mpr ⟨hN,columnLog_norm_upper p hp X₁ M₁ hX₁ N (hS₁ N hN h)⟩)
        simp only [hnzero N _ hz,Finset.sum_const_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro N hN
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro R hR hr
        have hz:C₂ R=0:=by
          by_contra h
          exact hr (Finset.mem_filter.mpr ⟨hR,columnLog_norm_upper p hp X₂ M₂ hX₂ R (hS₂ R hR h)⟩)
        exact hrzero N R hz
  have hrem (N:Finset ι) (hN:N∈boundedPrimeSupports p F U₁) (R:Finset ι) (hR:R∈boundedPrimeSupports p F U₂):‖rem N R‖≤Q:=by
    have hNF: N∈F.powerset:=(Finset.mem_filter.mp hN).1
    have hRF: R∈F.powerset:=(Finset.mem_filter.mp hR).1
    by_cases hn:C₁ N=0
    · rw [hnzero N R hn,norm_zero]; exact hQ
    by_cases hr:C₂ R=0
    · rw [hrzero N R hr,norm_zero]; exact hQ
    by_cases hNR:Disjoint N R
    · have hNB:=hFB.mono_left (Finset.mem_powerset.mp hNF)
      have hRB:=hFB.mono_left (Finset.mem_powerset.mp hRF)
      have hNS:Disjoint N S:=hNB.mono_right (Finset.filter_subset _ _)
      have hRS:Disjoint R S:=hRB.mono_right (Finset.filter_subset _ _)
      have hnorm:primeProductNorm p ((N∪R)∪S)=primeProductNorm p N*primeProductNorm p R*primeProductNorm p S:=by
        rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hNS,hRS⟩),primeProductNorm_union p _ _ hNR]
      have hprod:=mul_le_mul (Finset.mem_filter.mp hN).2 (Finset.mem_filter.mp hR).2
        (primeProductNorm_pos p hp R).le hU₁.le
      have hscale:slow≤K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S)):=by
        apply div_le_div_of_nonneg_left hK.le (mul_pos hNd (primeProductNorm_pos p hp _))
        rw [hnorm]
        calc
          _ ≤ ‖eisEmbedding d‖^2*(U₁*U₂*primeProductNorm p S):=mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
          _ = _ := by ring
      have hnroot:1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖:=by
        have hx:=primeProductNorm_ge_one p hp ((N∪R)∪S)
        change 1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖^2 at hx
        nlinarith [norm_nonneg (eisEmbedding (∏i∈(N∪R)∪S,p i))]
      have hpre:(K/‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖)*(‖C₁ N‖*‖C₂ R‖)≤G₁*G₂*K:=by
        calc
          _ ≤ K*(G₁*G₂):=mul_le_mul (div_le_self hK.le hnroot)
            (mul_le_mul (hC₁ N hNF) (hC₂ R hRF) (norm_nonneg _) hG₁)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK.le
          _ = _ := by ring
      have hfrac:(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S))))^2*(1+P/Real.exp (M₁+M₂))^A)≤tail:=by
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos (sq_pos_of_pos (lt_min (by norm_num) hslow)) (pow_pos (by linarith) _))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_min zero_le_one hslow.le)
          (min_le_min_left 1 hscale) 2) (pow_nonneg (by linarith) _)
      have hpair:=hb p hp hcop hg hc N R B v ε₁ ε₂ hNR hNB hRB C₁ C₂ W (fun _=>1) (fun _=>1)
        X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hP (hS₁ N hNF hn) (hS₂ R hRF hr) d hd
      simp only [norm_one,one_mul] at hpair
      dsimp only [rem]
      rw [ite_eq_left hNR]
      exact hpair.trans (mul_le_mul hpre hfrac (by positivity) (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le))
    · simp only [rem,ite_eq_right hNR,norm_zero];exact hQ
  rw [heq]
  calc
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,‖rem N R‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun N hN=>norm_sum_le _ _))
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,Q:=
      Finset.sum_le_sum (fun N hN=>Finset.sum_le_sum (fun R hR=>hrem N hN R hR))
    _ = ((boundedPrimeSupports p F U₁).card:ℝ)*((boundedPrimeSupports p F U₂).card:ℝ)*Q:=by simp;ring
    _ ≤ (128*U₁)*(128*U₂)*Q:=mul_le_mul_of_nonneg_right
      (mul_le_mul (boundedPrimeSupports_card_positive p hp hinj F U₁ hU₁)
        (boundedPrimeSupports_card_positive p hp hinj F U₂ hU₂) (Nat.cast_nonneg _) (by positivity)) hQ
    _ = _ := by dsimp [Q,tail,slow,U₁,U₂,S];ring

end FirstPassCubeLabels

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))
  (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)

include hinj

theorem canonicalCubeDualZero_support
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (ell K M : ℝ) (hell : 0<ell) (hgM : ∀t,g₁ t≠0→t≤M)
    (hC : ¬primeProductNorm p C≤ell*Real.exp M) :
    canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K=0 := by
  have hz : g₁ (columnLog p ell (b.rightDivisor∪C))=0 := by
    by_contra h
    exact hC ((primeProductNorm_mono p hp (Finset.subset_union_right)).trans
      (columnLog_norm_upper p hp ell M hell _ (hgM _ h)))
  rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj]
  split_ifs <;> simp [hz]

include hc

theorem canonicalCubeDualZero_fixed_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ f : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (G₁ G₂ ell K : ℝ) (hG₁ : 0≤G₁) (_hG₂ : 0≤G₂)
    (hg₁ : ∀t,‖g₁ t‖≤G₁) (hg₂ : ∀t,‖g₂ t‖≤G₂) :
    ‖canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        G₁*G₂*|K| *‖paperRadialFourier W 0‖ else 0 := by
  apply (canonicalCubeDualZero_norm_le p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f _ _ W K).trans
  split_ifs
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul (hg₁ _) (hg₂ _) (norm_nonneg _) hG₁) (abs_nonneg _)) (norm_nonneg _)
  · exact le_rfl

theorem canonicalCubeZero_common_sum_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (labels : Finset (Ideal O))
    (a : Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂ : O→*ℂ)
    (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (Γ G₁ G₂ ell K M : ℝ) (hΓ : 0≤Γ) (hG₁ : 0≤G₁) (hG₂ : 0≤G₂) (hell : 0<ell)
    (ha : ∀C∈(pool\b.support).powerset,∀I∈labels,‖a C I‖≤Γ)
    (hg₁ : ∀t,‖g₁ t‖≤G₁) (hg₂ : ∀t,‖g₂ t‖≤G₂) (hgM : ∀t,g₁ t≠0→t≤M) :
    ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator I)
        (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        (128*(ell*Real.exp M))*(labels.card:ℝ)*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) else 0 := by
  let z (C:Finset ι) (I:Ideal O):ℂ:=canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
    (ConcretePrimeRowBridge.idealGenerator I)
    (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K
  let Q:ℝ:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hL:0<ell*Real.exp M:=mul_pos hell (Real.exp_pos _)
  have heq : (∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I)=
      ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,a C I*z C I := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro C hC hnot
    have hbnd : ¬primeProductNorm p C≤ell*Real.exp M:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h⟩)
    apply Finset.sum_eq_zero
    intro I hI
    rw [show z C I=0 from canonicalCubeDualZero_support p hp hcop hg hinj pool b C Ψ₁ Ψ₂ m₁ m₂ _ g₁ g₂ W ell K M hell hgM hbnd,mul_zero]
  change ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I‖≤_
  rw [heq]
  by_cases hb : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  · rw [ite_eq_left hb]
    have hpnt (C:Finset ι) (hC:C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M)) (I:Ideal O) (hI:I∈labels):‖a C I*z C I‖≤Q:=by
      rw [norm_mul]
      have hz:=canonicalCubeDualZero_fixed_bound p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I) g₁ g₂ W G₁ G₂ ell K hG₁ hG₂ hg₁ hg₂
      rw [ite_eq_left hb] at hz
      exact mul_le_mul (ha C (Finset.mem_filter.mp hC).1 I hI) hz (norm_nonneg _) hΓ
    calc
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,‖a C I*z C I‖:=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC=>norm_sum_le _ _))
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,Q:=
        Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun I hI=>hpnt C hC I hI))
      _ = ((boundedPrimeSupports p (pool\b.support) (ell*Real.exp M)).card:ℝ)*(labels.card:ℝ)*Q:=by simp;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (boundedPrimeSupports_card_positive p hp hinj _ _ hL) (Nat.cast_nonneg _)) hQ
  · rw [ite_eq_right hb]
    have hz (C:Finset ι) (I:Ideal O):z C I=0:=by
      dsimp [z]
      rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj,ite_eq_right hb]
    simp only [hz,mul_zero,Finset.sum_const_zero,norm_zero,le_refl]

end

theorem full_uniform_canonicalFirstZero_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ ell K M B F:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<ell → 1≤B → 1≤F →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) → (∀t,g₁ t≠0→t≤M) →
      ‖∑b∈bs,∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      C*B^(1+ε)*(ell*Real.exp M)*F*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) := by
  obtain ⟨C,hC,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨C*128*128,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Γ G₁ G₂ ell K M B F hΓ hG₁ hG₂ hell hB hF hΨ₁ hΨ₂ hadm hb1 hb2 hI0 hIF ha hg₁ hg₂ hgM
  let Q:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  let good:=fun b:CubeCoordinates ι=>cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hlabel:(labels.card:ℝ)≤128*F:=DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hbcount:((bs.filter good).card:ℝ)≤C*B^(1+ε):=by
    have h:=hcount p hp hinj (bs.filter good) B 1 hB (by norm_num)
      (fun b hb=>hadm b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb1 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb2 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>by
        have he : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ := (Finset.mem_filter.mp hb).2
        rw [he]
        simp)
    simpa only [mul_one] using h
  calc
    _ ≤ ∑b∈bs,‖∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖:=norm_sum_le _ _
    _ ≤ ∑b∈bs,if good b then (128*(ell*Real.exp M))*(labels.card:ℝ)*Q else 0:=by
      apply Finset.sum_le_sum
      intro b hb
      exact canonicalCubeZero_common_sum_bound p hp hcop hg hinj hc pool b labels (a b) Ψ₁ Ψ₂ hΨ₁ hΨ₂
        m₁ m₂ g₁ g₂ W Γ G₁ G₂ ell K M hΓ hG₁ hG₂ hell (ha b hb) hg₁ hg₂ hgM
    _ = ((bs.filter good).card:ℝ)*((128*(ell*Real.exp M))*(labels.card:ℝ)*Q):=by
      rw [←Finset.sum_filter];simp
    _ ≤ (C*B^(1+ε))*((128*(ell*Real.exp M))*(128*F)*Q):=by
      apply mul_le_mul hbcount _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlabel (by positivity)) hQ
    _ = _ := by dsimp [Q];ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma originalLabelColumn_core_norm_le
    (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (Ψ : O→*ℂ) (hΨ : ∀u,‖Ψ u‖≤1) (m c f : O) (H : Finset ι→ℂ) (S : Finset ι) :
    ‖originalLabelColumn p hg B ε₁ ε₂ negative (multiplicativeCoreColumn p Ψ m H) c f S‖≤‖H S‖ := by
  have hm (z:O):‖rowCoprimeMask (fun i=>Ideal.span {p i}) S z‖≤1:=by
    unfold rowCoprimeMask;split_ifs <;> simp
  have hrow (z:O):‖finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z‖^4≤1:=by
    simpa using pow_le_pow_left₀ (norm_nonneg _)
      (finiteSquarefreeRow_norm_le_one (fun i=>Ideal.span {p i}) hg S z) 4
  simp only [originalLabelColumn,multiplicativeCoreColumn,norm_mul,norm_pow]
  calc
    _ ≤ 1*‖H S‖*1*1*1 := by
      exact mul_le_mul
        (mul_le_mul
          (mul_le_mul
            (mul_le_mul_of_nonneg_right
              ((mul_le_mul (hΨ _) (hm m) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)) (norm_nonneg _))
            (hm _) (norm_nonneg _) (by positivity))
          (hrow _) (pow_nonneg (norm_nonneg _) _) (by positivity))
        (hrow _) (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by ring

omit [DecidableEq ι] in
lemma originalLabelColumn_core_test_ne_zero
    (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (Ψ : O→*ℂ) (m c f : O) (H : Finset ι→ℂ) (S : Finset ι)
    (h : originalLabelColumn p hg B ε₁ ε₂ negative
      (multiplicativeCoreColumn p Ψ m H) c f S≠0) : H S≠0 := by
  intro hz
  apply h
  simp only [originalLabelColumn,multiplicativeCoreColumn,hz,mul_zero,zero_mul]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem canonicalFirstFrequencyRadius_eq_global
    (b : CubeCoordinates ι) (hb : b.Admissible) (C D : Finset ι)
    (Ksrc K ell : ℝ) (hKsrc : 0<Ksrc) (hK : 0<K) :
    canonicalFirstFrequencyRadius p b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit (primeSubsetGenerator (fun i=>Ideal.span {p i}) D)
      (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
      (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) Ksrc (Ksrc/K)=
    globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D) := by
  have hl:b.swap.leftBit=b.rightBit:=rfl
  have hr:b.swap.rightBit=b.leftBit:=rfl
  simp only [canonicalFirstFrequencyRadius,globalFirstFrequencyScale,sourceGlobalBlock,
    cube_swap_support,cube_swap_sum,hl,hr,
    cubeActiveSupport_swap,primeSubsetGenerator_norm_eq_productNorm,
    CubeCoordinates.aLabel_left p b hb,CubeCoordinates.aLabel_right p b hb]
  change (Ksrc/K)*(primeProductNorm p D*primeProductNorm p
    (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)*
    (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))*
    (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)))/Ksrc = _
  have hC:primeProductNorm p C≠0:=(primeProductNorm_pos p hp C).ne'
  have hL:primeProductNorm p b.leftDivisor≠0:=(primeProductNorm_pos p hp _).ne'
  have hR:primeProductNorm p b.rightDivisor≠0:=(primeProductNorm_pos p hp _).ne'
  simp only [primeProductNorm]
  simp only [primeProductNorm] at hC hL hR
  field_simp

end

theorem full_uniform_canonicalSource_kernel_tail (A : ℕ) :
    ∃(s:Finset (ℕ×ℕ)) (Ctail:ℝ),0<Ctail ∧
    ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (b:CubeCoordinates ι),b.Admissible → ∀ C D:Finset ι,Disjoint C b.support →
      ∀(Ψ₁ Ψ₂:O→*ℂ),(∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      ∀(m₁ m₂ f:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (G₁ G₂ M₁ M₂ Ksrc K ell:ℝ),
      0≤G₁ → 0≤G₂ → 0<Ksrc → 0<K → 0<ell →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) →
      (∀t,g₁ t≠0→t≤M₁) → (∀t,g₂ t≠0→t≤M₂) →
      let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
      let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
      let U₁:=X₁*Real.exp M₁
      let U₂:=X₂*Real.exp M₂
      let slow:=Ksrc/(primeProductNorm p D*primeProductNorm p
        (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)*U₁*U₂)
      let T:=firstFrequencyDisk (globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D))
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun S=>g₁ (columnLog p ell S)))
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun S=>g₂ (columnLog p ell S)))
        W (fun _=>1) (fun _=>1) 1 1 Ksrc
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*Ksrc)*
        ((Ctail*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+(Ksrc/K)/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,Ctail,hCtail,hbound⟩:=full_uniform_actualFirstKernel_disk_remainder A
  refine ⟨s,Ctail,hCtail,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool b hb C D hCB Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f g₁ g₂ W G₁ G₂ M₁ M₂ Ksrc K ell hG₁ hG₂ hKsrc hK hell hg₁ hg₂ hM₁ hM₂
  dsimp only
  let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
  let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
  have hX₁:0<X₁:=div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
  have hX₂:0<X₂:=div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
  have hFB:Disjoint (pool\(b.support∪C)) b.support:=Finset.disjoint_left.mpr (fun i hi hb=>
    (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hb))
  let C₁:=originalLabelColumn p hg b.support b.leftBit b.rightBit true
    (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) (∏i∈C,p i) f
  let C₂:=originalLabelColumn p hg b.support b.leftBit b.rightBit false
    (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) (∏i∈C,p i) f
  have hcoef₁ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset):‖C₁ N‖≤G₁:=
    (originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit true Ψ₁ hΨ₁ m₁ _ f _ N).trans (hg₁ _)
  have hcoef₂ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset):‖C₂ N‖≤G₂:=
    (originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit false Ψ₂ hΨ₂ m₂ _ f _ N).trans (hg₂ _)
  have hs₁ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset) (hn:C₁ N≠0):columnLog p X₁ N≤M₁:=
    hM₁ _ (originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit true Ψ₁ m₁ _ f _ N hn)
  have hs₂ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset) (hn:C₂ N≠0):columnLog p X₂ N≤M₂:=
    hM₂ _ (originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit false Ψ₂ m₂ _ f _ N hn)
  have h:=hbound p hp hinj hcop hg hc (pool\(b.support∪C)) b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit hFB C₁ C₂ W
    G₁ G₂ X₁ X₂ Ksrc (Ksrc/K) M₁ M₂ hG₁ hG₂ hX₁ hX₂ hKsrc (div_pos hKsrc hK).le
    hcoef₁ hcoef₂ hs₁ hs₂ (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) (primeSubsetGenerator_ne_zero _ _)
  rw [canonicalFirstFrequencyRadius_eq_global p hp b hb C D Ksrc K ell hKsrc hK] at h
  simp only [primeSubsetGenerator_norm_eq_productNorm] at h
  have heq := fun h:O=>canonical_log_kernel p hp hcop hg pool b hb C hCB Ψ₁ Ψ₂ m₁ m₂ f
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h g₁ g₂ W Ksrc ell hell
  simp_rw [heq]
  exact h

end SecondPassArithmetic

end

end OAI

end Source184

/- Original source: OAI/NumberTheory/DirichletL/Eisenstein/VariationalLaplacian.lean; sha256: 056490af1a915e434289b57c9ed6943ca6c522b427512f78bba9f31346d827da -/
section Source185
namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

def kernelLiftedCutoff (χ : PositiveChartCutoff) (w : HyperbolicSpace) : ℝ :=
  χ.func (hyperbolicEuclideanCoordinates w)

lemma kernelLiftedCutoff_continuous (χ : PositiveChartCutoff) : Continuous (kernelLiftedCutoff χ) :=
  χ.smooth.continuous.comp hyperbolicEuclideanCoordinates_continuous

lemma kernelLiftedCutoff_compact (χ : PositiveChartCutoff) : HasCompactSupport (kernelLiftedCutoff χ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (χ.compact.image_of_continuousOn (fun p hp =>
      (euclideanToHyperbolic_contMDiffAt p (χ.positive hp)).continuousAt.continuousWithinAt))
  intro w hw
  refine ⟨hyperbolicEuclideanCoordinates w,?_,euclideanToHyperbolic_coordinates w⟩
  exact subset_tsupport χ.func hw

lemma kernelLiftedCutoff_bounded (χ : PositiveChartCutoff) :
    ∃C : ℝ,∀w,‖kernelLiftedCutoff χ w‖≤C := by
  obtain ⟨w,hw⟩ := (kernelLiftedCutoff_continuous χ).norm.exists_forall_ge_of_hasCompactSupport
    (kernelLiftedCutoff_compact χ).norm
  exact ⟨_,hw⟩

lemma kernelCutoffGradient_memLp (χ : PositiveChartCutoff) (g : KernelGradientL2) :
    MemLp (fun w => kernelLiftedCutoff χ w • g w) 2 KernelFundamentalVolume := by
  obtain ⟨C,hC⟩ := kernelLiftedCutoff_bounded χ
  have hm : AEStronglyMeasurable (fun w => kernelLiftedCutoff χ w • g w) KernelFundamentalVolume :=
    (kernelLiftedCutoff_continuous χ).aestronglyMeasurable.smul (Lp.aestronglyMeasurable g)
  refine (Lp.memLp g).of_le_mul (c := C) hm (Eventually.of_forall (fun w => ?_))
  change ‖kernelLiftedCutoff χ w • g w‖≤C*‖g w‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC w) (norm_nonneg (g w))

def kernelCutoffGradient (χ : PositiveChartCutoff) (g : KernelGradientL2) : KernelGradientL2 :=
  (kernelCutoffGradient_memLp χ g).toLp (fun w => kernelLiftedCutoff χ w • g w)

lemma kernelCutoffGradient_coe (χ : PositiveChartCutoff) (g : KernelGradientL2) :
    (kernelCutoffGradient χ g : HyperbolicSpace→EuclideanSpace ℂ (Fin 3))=ᵐ[KernelFundamentalVolume]
      fun w => kernelLiftedCutoff χ w • g w := (kernelCutoffGradient_memLp χ g).coeFn_toLp

def kernelCutoffGradientLinear (χ : PositiveChartCutoff) : KernelGradientL2 →ₗ[ℂ] KernelGradientL2 where
  toFun := kernelCutoffGradient χ
  map_add' g h := by
    apply Lp.ext
    filter_upwards [kernelCutoffGradient_coe χ (g+h),kernelCutoffGradient_coe χ g,
      kernelCutoffGradient_coe χ h,Lp.coeFn_add g h,
      Lp.coeFn_add (kernelCutoffGradient χ g) (kernelCutoffGradient χ h)] with w hgh hg hh ha ha'
    simp only [hgh,ha',ha,Pi.add_apply,hg,hh,smul_add]
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [kernelCutoffGradient_coe χ (c•g),kernelCutoffGradient_coe χ g,
      Lp.coeFn_smul c g,Lp.coeFn_smul c (kernelCutoffGradient χ g)] with w hcg hg ha ha'
    simp only [RingHom.id_apply,hcg,ha',ha,Pi.smul_apply,hg]
    exact smul_comm _ _ _

lemma kernelCutoffGradient_bound (χ : PositiveChartCutoff) :
    ∃C : ℝ,∀g : KernelGradientL2,‖kernelCutoffGradientLinear χ g‖≤C*‖g‖ := by
  obtain ⟨C,hC⟩ := kernelLiftedCutoff_bounded χ
  refine ⟨C,fun g => ?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [kernelCutoffGradient_coe χ g] with w hw
  change ‖kernelCutoffGradient χ g w‖≤_
  rw [hw,norm_smul]
  exact mul_le_mul_of_nonneg_right (hC w) (norm_nonneg _)

def kernelCutoffGradientCLM (χ : PositiveChartCutoff) : KernelGradientL2 →L[ℂ] KernelGradientL2 :=
  (kernelCutoffGradientLinear χ).mkContinuousOfExistsBound (kernelCutoffGradient_bound χ)

lemma kernelCutoffGradient_norm_sq (χ : PositiveChartCutoff) (g : KernelGradientL2) :
    ‖kernelCutoffGradientCLM χ g‖^2=
      ∫w,(kernelLiftedCutoff χ w)^2*‖g w‖^2∂KernelFundamentalVolume := by
  calc
    ‖kernelCutoffGradientCLM χ g‖^2=inner ℝ (kernelCutoffGradientCLM χ g) (kernelCutoffGradientCLM χ g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫w,inner ℝ (kernelCutoffGradient χ g w) (kernelCutoffGradient χ g w)∂KernelFundamentalVolume := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [kernelCutoffGradient_coe χ g] with w hw
      rw [hw,real_inner_self_eq_norm_sq,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

lemma kernelCutoffGradient_core_norm_sq (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    ‖kernelCutoffGradientCLM χ (kernelGradientToL2 f)‖^2=
      ∫w,(kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w∂KernelFundamentalVolume := by
  rw [kernelCutoffGradient_norm_sq]
  apply integral_congr_ae
  filter_upwards [kernelGradientToL2_coe f] with w hw
  rw [hw,kernelGradientAt_norm_sq]

lemma kernelLocalizedField_reverse_energy (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    (χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)≤
      2*(p 2)^2*kernelLocalizedDensity χ f p+
      2*(p 2)^2*(∑j : Fin 3,‖fderiv ℝ χ.func p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)*‖kernelTestField f p‖^2 := by
  have hsum : (χ.func p)^2*(∑j : Fin 3,‖fderiv ℝ (kernelTestField f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤
      2*(∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)+
      2*(∑j : Fin 3,‖fderiv ℝ χ.func p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)*‖kernelTestField f p‖^2 := by
    simp only [Finset.mul_sum,Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have he := kernelLocalizedField_fderiv χ f p hp (EuclideanSpace.basisFun (Fin 3) ℝ j)
    have he' : χ.func p • fderiv ℝ (kernelTestField f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)=
        fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)-
        fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j) • kernelTestField f p := by rw [he]; abel
    have hb := complex_norm_add_sq_le
      (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j))
      (- (fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j) • kernelTestField f p))
    rw [←sub_eq_add_neg,←he'] at hb
    simpa only [norm_smul,norm_neg,mul_pow,Real.norm_eq_abs,sq_abs,mul_assoc] using hb
  have hc := hyperbolicEuclideanCoordinates_toHyperbolic p hp
  have hv : hyperbolicHeight (euclideanToHyperbolic p)=p 2 := congrArg (fun q : EuclideanSpatial => q 2) hc
  rw [kernelTestEnergyDensity_eq_partials,hv]
  simp only [kernelTestPartial,hc]
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg (p 2))
  unfold kernelLocalizedDensity
  nlinarith [mul_nonneg (sq_nonneg (p 2)) (sq_nonneg ‖kernelLocalizedField χ f p‖)]

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff ENNReal

lemma kernelLocalizedDensity_nonneg (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) : 0≤kernelLocalizedDensity χ f p := by
  unfold kernelLocalizedDensity
  positivity

lemma hyperbolicVolume_le_densityBound (S : Set EuclideanSpatial) (hS : MeasurableSet S)
    (hpos : S⊆euclideanUpperHalf) (H : ℝ)
    (hH : ∀p∈S,((p 2)^3)⁻¹≤H) :
    hyperbolicEuclideanVolume.restrict S≤ENNReal.ofReal H • volume.restrict S := by
  rw [hyperbolicEuclideanVolume,MeasureTheory.restrict_withDensity hS,
    Measure.restrict_restrict hS,Set.inter_eq_left.mpr hpos]
  have hh : hyperbolicDensity≤ᵐ[volume.restrict S] (fun _ => ENNReal.ofReal H) := by
    filter_upwards [ae_restrict_mem hS] with p hp
    exact ENNReal.ofReal_le_ofReal (hH p hp)
  simpa only [MeasureTheory.withDensity_const] using MeasureTheory.withDensity_mono hh

instance hyperbolicVolume_finiteOnCompacts : IsFiniteMeasureOnCompacts hyperbolicVolume where
  lt_top_of_isCompact K hK := by
    let S := hyperbolicEuclideanCoordinates '' K
    have hSK : IsCompact S := hK.image hyperbolicEuclideanCoordinates_continuous
    have hS : MeasurableSet S := hSK.measurableSet
    have hpos : S⊆euclideanUpperHalf := by
      rintro p ⟨w,hw,rfl⟩
      exact hyperbolicHeight_pos w
    have hrho : ContinuousOn (fun p : EuclideanSpatial => ((p 2)^3)⁻¹) S :=
      (by fun_prop : Continuous (fun p : EuclideanSpatial => (p 2)^3)).continuousOn.inv₀
        (fun p hp => pow_ne_zero _ (ne_of_gt (hpos hp)))
    obtain ⟨H,hH⟩ := hSK.bddAbove_image hrho
    have hb := hyperbolicVolume_le_densityBound S hS hpos H (fun p hp => hH ⟨p,hp,rfl⟩)
    have hm : hyperbolicEuclideanVolume S< (∞ : ℝ≥0∞) := by
      have hbu := Measure.le_iff.mp hb Set.univ MeasurableSet.univ
      simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Measure.smul_apply,
        smul_eq_mul] at hbu
      exact hbu.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSK.measure_lt_top)
    have heq : euclideanToHyperbolic ⁻¹' K=ᵐ[hyperbolicEuclideanVolume]S := by
      filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
      apply propext
      constructor
      · intro h
        exact ⟨euclideanToHyperbolic p,h,hyperbolicEuclideanCoordinates_toHyperbolic p hp⟩
      · rintro ⟨w,hw,rfl⟩
        simpa only [Set.mem_preimage,euclideanToHyperbolic_coordinates] using hw
    rw [hyperbolicVolume,Measure.map_apply euclideanToHyperbolic_measurable hK.measurableSet,
      measure_congr heq]
    exact hm

private lemma integrable_sq_mul_of_compact (a b : HyperbolicSpace → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : HasCompactSupport a) :
    Integrable (fun w => (a w)^2*b w) hyperbolicVolume := by
  have hs : HasCompactSupport (fun w => (a w)^2) :=
    hc.comp_left (g := fun x : ℝ => x^2) (by simp)
  exact ((ha.pow 2).mul hb).integrable_of_hasCompactSupport hs.mul_right

lemma kernelLiftedCutoffEnergy_integrable (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    Integrable (fun w => (kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w) hyperbolicVolume :=
  integrable_sq_mul_of_compact (kernelLiftedCutoff χ) (kernelTestEnergyDensity f)
    (kernelLiftedCutoff_continuous χ) (kernelTestEnergyDensity_continuous f)
    (kernelLiftedCutoff_compact χ)

lemma kernelLiftedCutoffEnergy_integral (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    (∫w,(kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w∂hyperbolicVolume)=
      ∫p,(χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
  rw [hyperbolicVolume,integral_map euclideanToHyperbolic_measurable.aemeasurable
    (kernelLiftedCutoffEnergy_integrable χ f).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
  simp only [kernelLiftedCutoff,hyperbolicEuclideanCoordinates_toHyperbolic p hp]

lemma kernelCutoffGradient_core_estimate (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (B D H : ℝ) (_hB : 0≤B) (hD : 0≤D) (hH : 0≤H)
    (hheight : ∀p∈tsupport χ.func,p 2≤B)
    (hderiv : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D)
    (hdensity : ∀p∈tsupport χ.func,((p 2)^3)⁻¹≤H)
    (f : kernelSmoothTests) :
    ‖kernelCutoffGradientCLM χ (kernelGradientToL2 f)‖^2≤
      2*B^2*(H*‖kernelLocalizedH1 χ f‖^2+D*‖kernelSmoothTestsToL2 f‖^2) := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have hpos : S⊆euclideanUpperHalf := χ.positive
  have hmeasure := hyperbolicVolume_le_densityBound S hS hpos H hdensity
  have hloc : IntegrableOn (kernelLocalizedDensity χ f) S hyperbolicEuclideanVolume :=
    (((kernelLocalizedDensity_integrable χ f).integrableOn).smul_measure
      (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top).mono_measure hmeasure
  have hmass : IntegrableOn (fun p => ‖kernelTestField f p‖^2) S hyperbolicEuclideanVolume := by
    exact (kernelEuclideanProjection_measurePreserving_on S hS hpos hinj).integrable_comp_of_integrable
      ((kernelSmoothTests_memLp f).norm.integrable_sq.integrableOn)
  have hweight : IntegrableOn (fun p => (χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p))
      S hyperbolicEuclideanVolume := by
    have hh := (kernelLiftedCutoffEnergy_integrable χ f).comp_measurable euclideanToHyperbolic_measurable
    have heq : (fun p => (kernelLiftedCutoff χ (euclideanToHyperbolic p))^2*
        kernelTestEnergyDensity f (euclideanToHyperbolic p))=ᵐ[hyperbolicEuclideanVolume]
        fun p => (χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p) := by
      filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
      simp only [kernelLiftedCutoff,hyperbolicEuclideanCoordinates_toHyperbolic p hp]
    exact (hh.congr heq).integrableOn
  have hlocBound : (∫p in S,kernelLocalizedDensity χ f p∂hyperbolicEuclideanVolume)≤
      H*‖kernelLocalizedH1 χ f‖^2 := by
    have hh := integral_mono_measure hmeasure
      (Eventually.of_forall (kernelLocalizedDensity_nonneg χ f))
      (((kernelLocalizedDensity_integrable χ f).integrableOn).smul_measure
        (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top)
    rw [integral_smul_measure,ENNReal.toReal_ofReal hH] at hh
    rw [kernelLocalizedH1_norm_sq]
    exact hh.trans (mul_le_mul_of_nonneg_left
      (setIntegral_le_integral (kernelLocalizedDensity_integrable χ f)
        (Eventually.of_forall (kernelLocalizedDensity_nonneg χ f))) hH)
  rw [kernelCutoffGradient_core_norm_sq]
  calc
    _ ≤ ∫w,(kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w∂hyperbolicVolume :=
      setIntegral_le_integral (kernelLiftedCutoffEnergy_integrable χ f)
        (Eventually.of_forall (fun w => mul_nonneg (sq_nonneg _) (kernelTestEnergyDensity_nonneg f w)))
    _ = ∫p in S,(χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
      rw [kernelLiftedCutoffEnergy_integral]
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro p hp
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).self_of_nhds
      simp only [hz,Pi.zero_apply,zero_pow (by decide : 2≠0),zero_mul]
    _ ≤ ∫p in S,(2*B^2*kernelLocalizedDensity χ f p+2*B^2*D*‖kernelTestField f p‖^2)
        ∂hyperbolicEuclideanVolume := by
      apply setIntegral_mono_on hweight ((hloc.const_mul _).add (hmass.const_mul _)) hS
      intro p hp
      refine (kernelLocalizedField_reverse_energy χ f p (hpos hp)).trans ?_
      simp only [Pi.add_apply]
      gcongr
      · exact kernelLocalizedDensity_nonneg _ _ _
      · exact (hpos hp).le
      · exact hheight p hp
      · exact (hpos hp).le
      · exact hheight p hp
      · exact hderiv p hp
    _ = 2*B^2*((∫p in S,kernelLocalizedDensity χ f p∂hyperbolicEuclideanVolume)+
        D*(∫p in S,‖kernelTestField f p‖^2∂hyperbolicEuclideanVolume)) := by
      rw [integral_add (hloc.const_mul _) (hmass.const_mul _),integral_const_mul,integral_const_mul]
      ring
    _ ≤ _ := by
      gcongr
      exact kernelLocalMass_le S hS hpos hinj f

lemma kernelCutoffGradient_core_bounded (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      ‖kernelCutoffGradientCLM χ (kernelGradientToL2 f)‖^2≤
        C*(‖kernelLocalizedH1 χ f‖^2+‖kernelSmoothTestsToL2 f‖^2) := by
  have hgrad : Continuous (fun p : EuclideanSpatial =>
      ∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) := by
    apply continuous_finsetSum
    intro j hj
    exact (((χ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2)
  have hrho : ContinuousOn (fun p : EuclideanSpatial => ((p 2)^3)⁻¹) (tsupport χ.func) :=
    (by fun_prop : Continuous (fun p : EuclideanSpatial => (p 2)^3)).continuousOn.inv₀
      (fun p hp => pow_ne_zero _ (ne_of_gt (χ.positive hp)))
  obtain ⟨d,hd⟩ := χ.compact.bddAbove_image hgrad.continuousOn
  obtain ⟨r,hr⟩ := χ.compact.bddAbove_image hrho
  obtain ⟨b,hb⟩ := χ.compact.bddAbove_image (f := fun p : EuclideanSpatial => p 2) (by fun_prop)
  let D := max 0 d
  let H := max 0 r
  let B := max 0 b
  have hD : 0≤D := le_max_left _ _
  have hH : 0≤H := le_max_left _ _
  have hB : 0≤B := le_max_left _ _
  have hheight : ∀p∈tsupport χ.func,p 2≤B := fun p hp =>
    (hb ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hderiv : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D := fun p hp =>
    (hd ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hdensity : ∀p∈tsupport χ.func,((p 2)^3)⁻¹≤H := fun p hp =>
    (hr ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  refine ⟨2*B^2*(H+D),by positivity,fun f => ?_⟩
  refine (kernelCutoffGradient_core_estimate χ hinj B D H hB hD hH hheight hderiv hdensity f).trans ?_
  rw [mul_assoc (2*B^2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [mul_nonneg hH (sq_nonneg ‖kernelSmoothTestsToL2 f‖),
    mul_nonneg hD (sq_nonneg ‖kernelLocalizedH1 χ f‖)]

lemma kernelEnergyCutoffGradient_eq_zero (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (u : KernelEnergyGraph)
    (hu : kernelEnergyMass u=0) : kernelCutoffGradientCLM χ (kernelEnergyGradient u)=0 := by
  obtain ⟨C,hC,hbound⟩ := kernelCutoffGradient_core_bounded χ hinj
  have hh : ‖kernelCutoffGradientCLM χ (kernelEnergyGradient u)‖^2≤
      C*(‖kernelEnergyLocalize χ u‖^2+‖kernelEnergyMass u‖^2) :=
    kernelEnergyGraphCore_dense.induction_on u (isClosed_le (by fun_prop) (by fun_prop))
      (fun f => by simpa only [kernelEnergyGradient_core,kernelEnergyMass_core,
        kernelEnergyLocalize_core χ hinj] using hbound f)
  rw [kernelEnergyLocalize_eq_zero_of_mass_zero χ hinj u hu,hu] at hh
  have hz : ‖kernelCutoffGradientCLM χ (kernelEnergyGradient u)‖=0 := by simpa using hh
  exact norm_eq_zero.mp hz

lemma kernelCutoffGradient_faithful (g : KernelGradientL2)
    (hg : ∀χ : PositiveChartCutoff,
      Set.InjOn kernelEuclideanProjection (tsupport χ.func) → kernelCutoffGradientCLM χ g=0) : g=0 := by
  let Cutoff := {χ : PositiveChartCutoff // Set.InjOn kernelEuclideanProjection (tsupport χ.func)}
  let U : Cutoff→Set HyperbolicSpace := fun χ => {w | kernelLiftedCutoff χ.1 w≠0}
  have hU : ∀χ,IsOpen (U χ) := fun χ =>
    isOpen_ne.preimage (kernelLiftedCutoff_continuous χ.1)
  have hcover : (Set.univ : Set HyperbolicSpace)⊆⋃χ,U χ := by
    intro w hw
    obtain ⟨χ,hχ,hrange,hinj⟩ :=
      kernelChartCutoff_exists (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
    refine Set.mem_iUnion.mpr ⟨⟨χ,hinj⟩,?_⟩
    change χ.func (hyperbolicEuclideanCoordinates w)≠0
    rw [hχ]
    norm_num
  obtain ⟨r,hr,hcov⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  let : Countable r := hr.to_subtype
  have heach (χ : Cutoff) : ∀ᵐw∂KernelFundamentalVolume,kernelLiftedCutoff χ.1 w • g w=0 := by
    have hzero := hg χ.1 χ.2
    change kernelCutoffGradient χ.1 g=0 at hzero
    filter_upwards [kernelCutoffGradient_coe χ.1 g,
      (Lp.coeFn_zero (E := EuclideanSpace ℂ (Fin 3)) (p := (2:ℝ≥0∞)) («μ» := KernelFundamentalVolume))]
      with w hw hz
    rw [hzero] at hw
    exact hw.symm.trans hz
  have hall : ∀ᵐw∂KernelFundamentalVolume,∀χ : r,kernelLiftedCutoff χ.1.1 w • g w=0 :=
    ae_all_iff.mpr (fun χ => heach χ.1)
  apply Lp.ext
  filter_upwards [hall,
    (Lp.coeFn_zero (E := EuclideanSpace ℂ (Fin 3)) (p := (2:ℝ≥0∞)) («μ» := KernelFundamentalVolume))]
    with w hw hz
  obtain ⟨χ,hχ⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ w))
  obtain ⟨hχr,hχw⟩ := Set.mem_iUnion.mp hχ
  have hsm := hw ⟨χ,hχr⟩
  have hne : kernelLiftedCutoff χ.1 w≠0 := hχw
  exact ((smul_eq_zero.mp hsm).resolve_left hne).trans hz.symm

theorem kernelEnergyMass_eq_zero (u : KernelEnergyGraph) (hu : kernelEnergyMass u=0) : u=0 := by
  have hgrad : kernelEnergyGradient u=0 :=
    kernelCutoffGradient_faithful _ (fun χ hinj => kernelEnergyCutoffGradient_eq_zero χ hinj u hu)
  apply norm_eq_zero.mp
  have hn := kernelEnergyGraph_norm_sq u
  simp only [hu,hgrad,norm_zero,zero_pow (by decide : 2≠0),add_zero] at hn
  nlinarith [norm_nonneg u]

theorem kernelEnergyMass_injective : Function.Injective kernelEnergyMass := by
  intro u v huv
  apply sub_eq_zero.mp
  apply kernelEnergyMass_eq_zero
  rw [map_sub,huv,sub_self]

lemma kernelInitialGradient_closure_unique (x : KernelQuotientL2 × KernelGradientL2)
    (hx : x∈kernelInitialGradient.graph.topologicalClosure) (hz : x.1=0) : x.2=0 := by
  let J := (WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).symm
  have hi : J '' (kernelInitialGradientGraph : Set (KernelQuotientL2 × KernelGradientL2))=
      Set.range kernelEnergyCore := by
    ext y
    constructor
    · rintro ⟨z,⟨f,rfl⟩,rfl⟩
      exact ⟨f,rfl⟩
    · rintro ⟨f,rfl⟩
      exact ⟨(kernelSmoothTestsToL2 f,kernelGradientLinear f),⟨f,rfl⟩,rfl⟩
  rw [kernelInitialGradient_graph] at hx
  change x∈closure (kernelInitialGradientGraph : Set (KernelQuotientL2 × KernelGradientL2)) at hx
  have hh := image_closure_subset_closure_image J.continuous ⟨x,hx,rfl⟩
  rw [hi] at hh
  let u : KernelEnergyGraph := ⟨J x,hh⟩
  have hu : kernelEnergyMass u=0 := hz
  have hu0 := kernelEnergyMass_eq_zero u hu
  have hv := congrArg kernelEnergyGradient hu0
  change x.2=kernelEnergyGradient 0 at hv
  simpa only [map_zero] using hv

theorem kernelInitialGradient_isClosable : kernelInitialGradient.IsClosable := by
  refine ⟨kernelInitialGradient.graph.topologicalClosure.toLinearPMap,?_⟩
  exact (Submodule.toLinearPMap_graph_eq _ kernelInitialGradient_closure_unique).symm

def kernelWeakGradient : KernelQuotientL2 →ₗ.[ℂ] KernelGradientL2 := kernelInitialGradient.closure

theorem kernelWeakGradient_closed : kernelWeakGradient.IsClosed :=
  kernelInitialGradient_isClosable.closure_isClosed

theorem kernelWeakGradient_dense_domain : Dense (kernelWeakGradient.domain : Set KernelQuotientL2) :=
  kernelInitialGradient_dense_domain.mono (LinearPMap.le_closure kernelInitialGradient).1

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff InnerProductSpace

lemma kernelEnergyGraph_inner (u v : KernelEnergyGraph) :
    inner ℂ u v=inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
      inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v) := rfl

lemma kernelEnergyMass_norm_le (u : KernelEnergyGraph) : ‖kernelEnergyMass u‖≤‖u‖ := by
  have hh := kernelEnergyGraph_norm_sq u
  nlinarith [sq_nonneg ‖kernelEnergyGradient u‖,norm_nonneg (kernelEnergyMass u),norm_nonneg u]

lemma kernelEnergyMass_opNorm_le : ‖kernelEnergyMass‖≤1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using kernelEnergyMass_norm_le)

def kernelVariationalSolution : KernelQuotientL2 →L[ℂ] KernelEnergyGraph :=
  kernelEnergyMass.adjoint

lemma kernelVariationalSolution_equation (F : KernelQuotientL2) (v : KernelEnergyGraph) :
    inner ℂ (kernelEnergyMass (kernelVariationalSolution F)) (kernelEnergyMass v)+
      inner ℂ (kernelEnergyGradient (kernelVariationalSolution F)) (kernelEnergyGradient v)=
        inner ℂ F (kernelEnergyMass v) := by
  rw [←kernelEnergyGraph_inner]
  exact kernelEnergyMass.adjoint_inner_left v F

lemma kernelVariationalSolution_unique (F : KernelQuotientL2) (u : KernelEnergyGraph)
    (hu : ∀v : KernelEnergyGraph,
      inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
        inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)=inner ℂ F (kernelEnergyMass v)) :
    u=kernelVariationalSolution F := by
  apply ext_inner_right ℂ
  intro v
  rw [kernelEnergyGraph_inner,kernelEnergyGraph_inner]
  exact (hu v).trans (kernelVariationalSolution_equation F v).symm

theorem kernelVariationalSolution_existsUnique (F : KernelQuotientL2) :
    ∃!u : KernelEnergyGraph,∀v : KernelEnergyGraph,
      inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
        inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)=inner ℂ F (kernelEnergyMass v) :=
  ⟨kernelVariationalSolution F,kernelVariationalSolution_equation F,
    fun u hu => kernelVariationalSolution_unique F u hu⟩

lemma kernelVariationalSolution_norm_le (F : KernelQuotientL2) :
    ‖kernelVariationalSolution F‖≤‖F‖ := by
  have hnorm : ‖kernelVariationalSolution‖=‖kernelEnergyMass‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  calc
    ‖kernelVariationalSolution F‖≤‖kernelVariationalSolution‖*‖F‖ :=
      kernelVariationalSolution.le_opNorm F
    _ ≤1*‖F‖ := mul_le_mul_of_nonneg_right (hnorm ▸ kernelEnergyMass_opNorm_le) (norm_nonneg F)
    _ = _ := one_mul _

def kernelVariationalResolvent : KernelQuotientL2 →L[ℂ] KernelQuotientL2 :=
  kernelEnergyMass.comp kernelVariationalSolution

lemma kernelVariationalResolvent_norm_le (F : KernelQuotientL2) :
    ‖kernelVariationalResolvent F‖≤‖F‖ :=
  (kernelEnergyMass_norm_le _).trans (kernelVariationalSolution_norm_le F)

private lemma selfAdjoint_comp_adjoint {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) : IsSelfAdjoint (A.comp A.adjoint) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

lemma kernelVariationalResolvent_selfAdjoint : IsSelfAdjoint kernelVariationalResolvent :=
  selfAdjoint_comp_adjoint kernelEnergyMass

lemma kernelVariationalResolvent_positive (F : KernelQuotientL2) :
    0≤(inner ℂ F (kernelVariationalResolvent F)).re := by
  change 0≤(inner ℂ F (kernelEnergyMass (kernelEnergyMass.adjoint F))).re
  rw [←kernelEnergyMass.adjoint_inner_left]
  exact inner_self_nonneg (𝕜 := ℂ) (x := kernelEnergyMass.adjoint F)

lemma kernelVariationalResolvent_injective : Function.Injective kernelVariationalResolvent := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro F hF
  change kernelEnergyMass (kernelVariationalSolution F)=0 at hF
  have hu : kernelVariationalSolution F=0 := kernelEnergyMass_injective (by
    rw [map_zero]
    exact hF)
  have he : (fun g : KernelQuotientL2 => inner ℂ F g)=(fun _ => (0 : ℂ)) :=
    kernelEnergyMass_dense.equalizer (by fun_prop) continuous_const (by
      funext v
      change inner ℂ F (kernelEnergyMass v)=0
      rw [←kernelEnergyMass.adjoint_inner_left]
      change inner ℂ (kernelVariationalSolution F) v=0
      rw [hu,inner_zero_left])
  exact inner_self_eq_zero.mp (congrFun he F)

lemma kernelVariationalResolvent_dense : DenseRange kernelVariationalResolvent := by
  change Dense (kernelVariationalResolvent.range : Set KernelQuotientL2)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hh := kernelVariationalResolvent.orthogonal_ker
  rw [LinearMap.ker_eq_bot.mpr kernelVariationalResolvent_injective,Submodule.bot_orthogonal_eq_top,
    kernelVariationalResolvent_selfAdjoint.adjoint_eq] at hh
  exact hh.symm

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelLaplacianEquation : (KernelQuotientL2 × KernelQuotientL2) →L[ℂ] KernelQuotientL2 :=
  kernelVariationalResolvent.comp ((ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelQuotientL2)+
    (ContinuousLinearMap.snd ℂ KernelQuotientL2 KernelQuotientL2))-
      (ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelQuotientL2)

def kernelLaplacianGraph : Submodule ℂ (KernelQuotientL2 × KernelQuotientL2) :=
  kernelLaplacianEquation.ker

lemma mem_kernelLaplacianGraph (u f : KernelQuotientL2) :
    (u,f)∈kernelLaplacianGraph ↔ kernelVariationalResolvent (u+f)=u := by
  change kernelVariationalResolvent (u+f)-u=0 ↔ _
  exact sub_eq_zero

lemma kernelLaplacianGraph_unique (x : KernelQuotientL2 × KernelQuotientL2)
    (hx : x∈kernelLaplacianGraph) (hz : x.1=0) : x.2=0 := by
  have hh := (mem_kernelLaplacianGraph x.1 x.2).mp hx
  rw [hz,zero_add] at hh
  apply kernelVariationalResolvent_injective
  rw [map_zero]
  exact hh

def kernelEnergyLaplacian : KernelQuotientL2 →ₗ.[ℂ] KernelQuotientL2 :=
  kernelLaplacianGraph.toLinearPMap

lemma kernelEnergyLaplacian_graph : kernelEnergyLaplacian.graph=kernelLaplacianGraph :=
  Submodule.toLinearPMap_graph_eq _ kernelLaplacianGraph_unique

lemma kernelEnergyLaplacian_closed : kernelEnergyLaplacian.IsClosed := by
  rw [LinearPMap.IsClosed,kernelEnergyLaplacian_graph]
  exact kernelLaplacianEquation.isClosed_ker

lemma kernelEnergyLaplacian_resolvent_graph (F : KernelQuotientL2) :
    (kernelVariationalResolvent F,F-kernelVariationalResolvent F)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  congr 1
  abel

lemma kernelEnergyLaplacian_resolvent_domain (F : KernelQuotientL2) :
    kernelVariationalResolvent F∈kernelEnergyLaplacian.domain :=
  LinearPMap.mem_domain_of_mem_graph (kernelEnergyLaplacian_resolvent_graph F)

lemma kernelEnergyLaplacian_resolvent_apply (F : KernelQuotientL2) :
    kernelEnergyLaplacian ⟨kernelVariationalResolvent F,kernelEnergyLaplacian_resolvent_domain F⟩=
      F-kernelVariationalResolvent F :=
  kernelEnergyLaplacian.mem_graph_snd_inj (kernelEnergyLaplacian.mem_graph _)
    (kernelEnergyLaplacian_resolvent_graph F) rfl

lemma kernelEnergyLaplacian_dense_domain :
    Dense (kernelEnergyLaplacian.domain : Set KernelQuotientL2) := by
  apply kernelVariationalResolvent_dense.mono
  rintro _ ⟨F,rfl⟩
  exact kernelEnergyLaplacian_resolvent_domain F

lemma kernelEnergyLaplacian_resolvent_relation (u : kernelEnergyLaplacian.domain) :
    kernelVariationalResolvent (kernelEnergyLaplacian u+u)=u := by
  have hh := kernelEnergyLaplacian.mem_graph u
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph] at hh
  simpa only [add_comm] using hh

lemma kernelEnergyLaplacian_isFormalAdjoint :
    kernelEnergyLaplacian.IsFormalAdjoint kernelEnergyLaplacian := by
  intro u v
  have hh := kernelVariationalResolvent_selfAdjoint.isSymmetric
    (kernelEnergyLaplacian u+u) (kernelEnergyLaplacian v+v)
  simp only [ContinuousLinearMap.coe_coe] at hh
  rw [kernelEnergyLaplacian_resolvent_relation,kernelEnergyLaplacian_resolvent_relation] at hh
  simp only [inner_add_left,inner_add_right] at hh
  exact add_right_cancel hh.symm

lemma kernelEnergyLaplacian_form (u : kernelEnergyLaplacian.domain) (v : KernelEnergyGraph) :
    inner ℂ (kernelEnergyLaplacian u) (kernelEnergyMass v)=
      inner ℂ (kernelEnergyGradient (kernelVariationalSolution (kernelEnergyLaplacian u+u)))
        (kernelEnergyGradient v) := by
  have hh := kernelVariationalSolution_equation (kernelEnergyLaplacian u+u) v
  have he : kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u))=u :=
    kernelEnergyLaplacian_resolvent_relation u
  rw [he,inner_add_left] at hh
  exact (add_left_cancel (hh.trans (add_comm _ _))).symm

lemma kernelEnergyLaplacian_nonnegative (u : kernelEnergyLaplacian.domain) :
    0≤(inner ℂ (kernelEnergyLaplacian u) (u : KernelQuotientL2)).re := by
  have hh := kernelEnergyLaplacian_form u
    (kernelVariationalSolution (kernelEnergyLaplacian u+u))
  have he : kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u))=u :=
    kernelEnergyLaplacian_resolvent_relation u
  rw [he] at hh
  rw [hh]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem kernelEnergyLaplacian_selfAdjoint : IsSelfAdjoint kernelEnergyLaplacian := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    intro x hx
    obtain ⟨u,hu,hv⟩ := (kernelEnergyLaplacian.adjoint.mem_graph_iff).mp hx
    change (x.1,x.2)∈kernelEnergyLaplacian.graph
    rw [←hu,←hv,kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
    apply ext_inner_right ℂ
    intro F
    have ha := LinearPMap.adjoint_isFormalAdjoint kernelEnergyLaplacian_dense_domain u
      ⟨kernelVariationalResolvent F,kernelEnergyLaplacian_resolvent_domain F⟩
    rw [kernelEnergyLaplacian_resolvent_apply] at ha
    have hs := kernelVariationalResolvent_selfAdjoint.isSymmetric
      ((u : KernelQuotientL2)+kernelEnergyLaplacian.adjoint u) F
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [hs,inner_add_left,ha,inner_sub_right]
    abel
  · exact LinearPMap.IsFormalAdjoint.le_adjoint kernelEnergyLaplacian_dense_domain
      kernelEnergyLaplacian_isFormalAdjoint

end CubicEisenstein

end

end OAI

end Source185

/- Original source: OAI/NumberTheory/DirichletL/MeanSquare/CanonicalDensity.lean; sha256: 110aad3190ef2f2bfb7dc422ed4f02f4b8dbd5b7eba685c841b0b38771fd52bf -/
section Source186
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve

theorem outsideIdealsUpTo_mono (S : Finset (Ideal O)) {D E : ℕ} (hDE : D ≤ E) :
    outsideIdealsUpTo S D ⊆ outsideIdealsUpTo S E := by
  intro I hI
  obtain ⟨hpos,hn,hS⟩ := mem_outsideIdealsUpTo.mp hI
  exact mem_outsideIdealsUpTo.mpr ⟨hpos,hn.trans hDE,hS⟩

theorem outside_row_cutoff_stable (S : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ S)
    {D E : ℕ} (hDE : D ≤ E) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W : ℝ → ℂ) (b Z : ℝ) (hZ : 0 < Z)
    (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*Z ≤ D) (z : O) :
    idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z =
    idealRowSum (outsideIdealsUpTo S E) (outsideIdealsUpTo_ne_bot S E)
      (outside_good S E hbad) χ (fun n => W (n/Z)) z := by
  have hsub := outsideIdealsUpTo_mono S hDE
  unfold idealRowSum
  calc
    _ = ∑ I ∈ outsideIdealsUpTo S D,
        ShortDraftHeckeBridge.baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ)/Z) *
        idealSexticRow (outsideIdealsUpTo S E) (outsideIdealsUpTo_ne_bot S E)
          (outside_good S E hbad) I z := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [idealSexticRow_ambient (outsideIdealsUpTo S D) (outsideIdealsUpTo S E)
        (outsideIdealsUpTo_ne_bot S D) (outsideIdealsUpTo_ne_bot S E)
        (outside_good S D hbad) (outside_good S E hbad) I hI (hsub hI) z]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro I hIE hID
      have hw : W ((Ideal.absNorm I : ℝ)/Z) = 0 := by
        by_contra hn
        have hbound : (Ideal.absNorm I : ℝ) ≤ D :=
          ((div_le_iff₀ hZ).mp (hW _ hn)).trans hD
        have hnat : Ideal.absNorm I ≤ D := by exact_mod_cast hbound
        obtain ⟨hpos,_,hS⟩ := mem_outsideIdealsUpTo.mp hIE
        exact hID (mem_outsideIdealsUpTo.mpr ⟨hpos,hnat,hS⟩)
      rw [hw,mul_zero,zero_mul]

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def canonicalCubeDualFinite (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (T:Finset ι→Finset O):ℂ:=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
      ∑h∈(T D).erase 0,actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h

def canonicalCubeDualTail (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (T:Finset ι→Finset O):ℂ:=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
      ∑'h:{h:O // h∉T D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val

theorem canonicalCubeBeforePoisson_split
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) (T:Finset ι→Finset O)
    (hT:∀D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,(0:O)∈T D):
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K=
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K+
      canonicalCubeDualFinite p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K T+
      canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K T := by
  rw [canonicalCubeBeforePoisson_eq_all_modes p hp hcop hg hinj hc]
  · unfold canonicalCubeDualZero canonicalCubeDualFinite canonicalCubeDualTail
    rw [←mul_add,←mul_add,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply congrArg
    apply Finset.sum_congr rfl
    intro D hD
    rw [actualFirstKernel_truncate p hp hcop hg _ _ _ _ _ _ _ _ _ _ _ _ _ hK _
      (primeSubsetGenerator_ne_zero _ _) (T D)]
    rw [←Finset.sum_erase_add _ _ (hT D hD)]
    ring
  · exact hK

theorem canonicalCubeDualFinite_eq_raw_blocks
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι) (labels:Finset (Ideal O))
    (a:Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ))
    (K ell:ℝ) (T:Finset ι→Finset O):
    (∑I∈labels,a I*canonicalCubeDualFinite p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W K T)=
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      rawCanonicalBlock p hp hcop hg pool (sourceGlobalBlock b C D) (labels.product ((T D).erase 0))
        (fun x=>a x.1*canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator x.1)) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell := by
  simp only [canonicalCubeDualFinite,rawCanonicalBlock,sourceGlobalBlock,
    CubeCoordinates.swap_swap,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro h hh
  ring

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels

variable {ι:Type*} [DecidableEq ι]

def canonicalSourceBlocks (pool:Finset ι) (bs:Finset (CubeCoordinates ι)):Finset (GlobalCubeBlock ι):=
  bs.biUnion (fun b=>(pool\b.support).powerset.biUnion (fun C=>
    (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.image
      (sourceGlobalBlock b C)))

theorem canonicalSourceBlocks_mem (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (q:GlobalCubeBlock ι):
    q∈canonicalSourceBlocks pool bs ↔ ∃b∈bs,∃C∈(pool\b.support).powerset,
      ∃D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        sourceGlobalBlock b C D=q := by
  simp only [canonicalSourceBlocks,Finset.mem_biUnion,Finset.mem_image]

theorem sum_canonicalSourceBlocks {M:Type*} [AddCommMonoid M]
    (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (f:GlobalCubeBlock ι→M):
    (∑q∈canonicalSourceBlocks pool bs,f q)=
      ∑b∈bs,∑C∈(pool\b.support).powerset,
        ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
          f (sourceGlobalBlock b C D) := by
  unfold canonicalSourceBlocks
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro C hC
      rw [Finset.sum_image]
      intro D hD E hE he
      exact congrArg GlobalCubeBlock.firstDivisor he
    · intro C hC D hD hne
      apply Finset.disjoint_left.mpr
      intro q hq hq'
      obtain ⟨E,hE,he⟩:=Finset.mem_image.mp hq
      obtain ⟨F,hF,hf⟩:=Finset.mem_image.mp hq'
      exact hne (congrArg GlobalCubeBlock.common (he.trans hf.symm))
  · intro b hb c hc hne
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨C,hC,E,hE,he⟩:=by
      simpa only [Finset.mem_biUnion,Finset.mem_image] using hq
    obtain ⟨D,hD,F,hF,hf⟩:=by
      simpa only [Finset.mem_biUnion,Finset.mem_image] using hq'
    have hswap:=congrArg (fun q:GlobalCubeBlock ι=>q.cube.swap) (he.trans hf.symm)
    exact hne (by simpa only [sourceGlobalBlock,CubeCoordinates.swap_swap] using hswap)

theorem canonicalSourceBlocks_admissible (pool:Finset ι) (bs:Finset (CubeCoordinates ι))
    (hadm:∀b∈bs,b.Admissible) (q:GlobalCubeBlock ι) (hq:q∈canonicalSourceBlocks pool bs):
    GlobalCubeAdmissible q := by
  obtain ⟨b,hb,C,hC,D,hD,rfl⟩:=(canonicalSourceBlocks_mem pool bs q).mp hq
  have ha:=hadm b hb
  constructor
  · constructor
    · change b.rightDivisor⊆b.swap.support
      rw [cube_swap_support]
      exact ha.2
    · change b.leftDivisor⊆b.swap.support
      rw [cube_swap_support]
      exact ha.1
  constructor
  · change Disjoint C b.swap.support
    rw [cube_swap_support]
    exact Finset.disjoint_left.mpr (fun i hi hbi=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hi)).2 hbi)
  · change D⊆C∪b.swap.support
    rw [cube_swap_support]
    exact (Finset.mem_powerset.mp hD).trans
      (Finset.union_subset_union_right (Finset.filter_subset _ _))

theorem canonicalSourceBlocks_cube_norms
    (p:ι→O) (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (B:ℝ)
    (hleft:∀b∈bs,‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hright:∀b∈bs,‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B)
    (q:GlobalCubeBlock ι) (hq:q∈canonicalSourceBlocks pool bs):
    ‖ConcreteTraceCRT.eisEmbedding (primeProduct p q.cube.support q.cube.leftExponent)‖^2≤B ∧
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p q.cube.support q.cube.rightExponent)‖^2≤B := by
  obtain ⟨b,hb,C,hC,D,hD,rfl⟩:=(canonicalSourceBlocks_mem pool bs q).mp hq
  change ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.swap.support b.rightExponent)‖^2≤B ∧
    ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.swap.support b.leftExponent)‖^2≤B
  rw [cube_swap_support]
  exact ⟨hright b hb,hleft b hb⟩

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def canonicalSourceCutoff (K ell:ℝ) (b:CubeCoordinates ι) (C D:Finset ι):Finset O:=
  firstFrequencyDisk (globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma canonicalSourceCutoff_zero (K ell:ℝ) (hK:0≤K) (b:CubeCoordinates ι) (C D:Finset ι):
    (0:O)∈canonicalSourceCutoff p K ell b C D := by
  apply firstFrequencyDisk_zero
  unfold globalFirstFrequencyScale
  simp only [primeProductNorm]
  positivity

def canonicalSourceTotal (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc

def canonicalSourceZero (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc

def canonicalSourceFinite (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeDualFinite p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc (canonicalSourceCutoff p K ell b C)

def canonicalSourceTail (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc (canonicalSourceCutoff p K ell b C)

def canonicalBlockFrequencies (K ell:ℝ) (labels:Finset (Ideal O)) (q:GlobalCubeBlock ι):Finset (Ideal O×O):=
  labels.product ((firstFrequencyDisk (globalFirstFrequencyScale p K ell q)).erase 0)

def canonicalBlockCoefficient (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (q:GlobalCubeBlock ι) (x:Ideal O×O):ℂ:=
  a q.cube.swap q.common x.1*canonicalCubeOuter p hp hcop hg q.cube.swap q.common
    Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1)

theorem canonicalSourceFinite_eq_raw
    (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ):
    canonicalSourceFinite p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell=
      ∑q∈canonicalSourceBlocks pool bs,rawCanonicalBlock p hp hcop hg pool q
        (canonicalBlockFrequencies p K ell labels q)
        (canonicalBlockCoefficient p hp hcop hg a Ψ₁ Ψ₂ m₁ m₂ q)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell := by
  rw [sum_canonicalSourceBlocks]
  unfold canonicalSourceFinite
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro C hC
  rw [canonicalCubeDualFinite_eq_raw_blocks]
  apply Finset.sum_congr rfl
  intro D hD
  simp only [canonicalBlockFrequencies,canonicalSourceCutoff,
    sourceGlobalBlock]
  rfl

theorem canonicalSourceTotal_split
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ) (hKsrc:0<Ksrc) (hK:0≤K):
    canonicalSourceTotal p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell=
      canonicalSourceZero p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell+
      canonicalSourceFinite p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell+
      canonicalSourceTail p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell := by
  unfold canonicalSourceTotal canonicalSourceZero canonicalSourceFinite canonicalSourceTail
  have hsplit (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal O):=
    canonicalCubeBeforePoisson_split p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc hKsrc (canonicalSourceCutoff p K ell b C)
      (fun D hD=>canonicalSourceCutoff_zero p K ell hK b C D)
  simp_rw [hsplit]
  simp only [mul_add,Finset.sum_add_distrib]

theorem canonicalBlockCoefficient_bound
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (Γ K ell:ℝ) (hΓ:0≤Γ) (hΨ₁:∀u,‖Ψ₁ u‖≤1) (hΨ₂:∀u,‖Ψ₂ u‖≤1)
    (ha:∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ)
    (q:GlobalCubeBlock ι) (hq:q∈canonicalSourceBlocks pool bs)
    (x:Ideal O×O) (hx:x∈canonicalBlockFrequencies p K ell labels q):
    ‖canonicalBlockCoefficient p hp hcop hg a Ψ₁ Ψ₂ m₁ m₂ q x‖≤Γ := by
  have hI:x.1∈labels:=(Finset.mem_product.mp hx).1
  obtain ⟨b,hb,C,hC,D,hD,rfl⟩:=(canonicalSourceBlocks_mem pool bs q).mp hq
  simp only [canonicalBlockCoefficient,sourceGlobalBlock,CubeCoordinates.swap_swap,norm_mul]
  exact (mul_le_mul (ha b hb C hC x.1 hI)
    (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _)
    (norm_nonneg _) hΓ).trans_eq (mul_one Γ)

end

open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

theorem canonicalSource_twoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀t,g₁ t≠0→|t|≤M₁) (hg₂ : ∀t,g₂ t≠0→|t|≤M₂)
    (hV₁ : ∀t,V₁ t≠0→|t|≤N₁) (hV₂ : ∀t,V₂ t≠0→|t|≤N₂)
    (hWin₁ : ∀t,g₁ t≠0→V₁ t=1) (hWin₂ : ∀t,g₂ t≠0→V₂ t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M₁+6+1) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M₂+6+1) ∧
      ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ)
      (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (Γ Ksrc K ell B F H U:ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U →
      ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,Squarefree I) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      ‖(ell*B^2*F:ℂ)⁻¹*
        (canonicalSourceTotal p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
         canonicalSourceZero p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
         canonicalSourceTail p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell)‖≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true)*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,htransfer⟩:=
    padded_rawCanonicalTwoPassage_quantitative W g₁ g₂ V₁ V₂ M₁ M₂ N₁ N₂ hM₁ hM₂ hN₁ hN₂
      hg₁ hg₂ hV₁ hV₂ hWin₁ hWin₂ ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool bs labels a Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hMU₁ hMU₂ hΨ₁ hΨ₂ ha hadm hleft hright hsf hf
  have hcenter : canonicalSourceTotal p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
      canonicalSourceZero p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
      canonicalSourceTail p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell=
      canonicalSourceFinite p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell := by
    rw [canonicalSourceTotal_split p hp hcop hg hinj hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell hKsrc hK.le]
    ring
  rw [hcenter,canonicalSourceFinite_eq_raw]
  apply htransfer p hp hinj hcop hg hc hpr pool (canonicalSourceBlocks pool bs)
    (canonicalBlockFrequencies p K ell labels) (canonicalBlockCoefficient p hp hcop hg a Ψ₁ Ψ₂ m₁ m₂)
    (fun _=>Γ) Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U hΓ hKsrc hK hell hB hF hH hU hMU₁ hMU₂ hΨ₁ hΨ₂
  · exact fun q hq=>⟨hΓ,le_rfl⟩
  · exact fun q hq x hx=>canonicalBlockCoefficient_bound p hp hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ Γ K ell hΓ hΨ₁ hΨ₂ ha q hq x hx
  · exact canonicalSourceBlocks_admissible pool bs hadm
  · exact fun q hq=>(canonicalSourceBlocks_cube_norms p pool bs B hleft hright q hq).1
  · exact fun q hq=>(canonicalSourceBlocks_cube_norms p pool bs B hleft hright q hq).2
  · intro q hq x hx
    exact hsf x.1 (Finset.mem_product.mp hx).1
  · intro q hq x hx
    exact (Finset.mem_erase.mp (Finset.mem_product.mp hx).2).1
  · intro q hq x hx
    exact hf x.1 (Finset.mem_product.mp hx).1
  · intro q hq x hx
    exact (mem_firstFrequencyDisk _ _).mp (Finset.mem_erase.mp (Finset.mem_product.mp hx).2).2

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (firstLogDensity)

theorem initial_subunit_row_le_label (Z X lengthScale K R κ : ℝ)
    (hZ : 1 ≤ Z) (hX : X ≤ 1) (hL : 0 ≤ lengthScale) (hK : 0 ≤ K)
    (hR : 1 ≤ R) (hκ : 0 ≤ κ) (hinv : K*R ≤ X*lengthScale*Z^(-κ)) : K ≤ lengthScale := by
  have hpow : Z^(-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hZ (by linarith)
  have hpow0 : 0 ≤ Z^(-κ) := Real.rpow_nonneg (zero_le_one.trans hZ) _
  calc
    K ≤ K*R := le_mul_of_one_le_right hK hR
    _ ≤ X*lengthScale*Z^(-κ) := hinv
    _ ≤ 1*lengthScale*Z^(-κ) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hX hL) hpow0
    _ ≤ lengthScale := by simpa only [one_mul,mul_one] using mul_le_mul_of_nonneg_left hpow hL

theorem initial_subunit_density_bound {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : ActualEisensteinCubic.O) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ)
    (X lengthScale K A Vmax : ℝ) (J : ℕ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hKL : K ≤ lengthScale) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J) ≤
      (initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3)*(X*lengthScale)^2 := by
  let C := initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3
  have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hC : 0 ≤ C := mul_nonneg (initialElementaryConstant_nonneg A Vmax) (pow_nonneg hI _)
  have hd := childDensity_elementary_all_scales p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m T V₁ V₂ X lengthScale K A Vmax J hX hL hK hA hVmax hV₁ hV₂ hs₁ hs₂ hT
  change _/(X*lengthScale) ≤ C*K*X at hd
  have hraw := (div_le_iff₀ (mul_pos hX (zero_lt_one.trans_le hL))).mp hd
  calc
    _ ≤ (C*K*X)*(X*lengthScale) := hraw
    _ ≤ (C*lengthScale*X)*(X*lengthScale) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKL hC) hX.le)
      (mul_nonneg hX.le (zero_le_one.trans hL))
    _ = _ := by dsimp only [C]; ring

lemma initialErrorFrequencyBound_ge_one (a b Z H : ℝ) (hZ : 0 < Z) (hH : 0 < H) :
    1 ≤ initialErrorFrequencyBound a b Z H := by
  have ht := initialTailHeight_pos Z H (initialErrorWindow a b) hZ hH
  have hv : 0 ≤ initialTailHeight Z H (initialErrorWindow a b)*
      (1+Z*Real.exp (initialErrorWindow a b))^3/H := by positivity
  unfold initialErrorFrequencyBound
  nlinarith [sq_nonneg (initialTailHeight Z H (initialErrorWindow a b)*
      (1+Z*Real.exp (initialErrorWindow a b))^3/H)]

lemma initialErrorRowBound_ge_one (a b Z H : ℝ) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    1 ≤ initialErrorRowBound a b Z H := by
  have hM : 0 ≤ initialErrorWindow a b := by unfold initialErrorWindow; positivity
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hZ (Real.one_le_exp hM))
    (initialErrorFrequencyBound_ge_one a b Z H (zero_lt_one.trans_le hZ) (zero_lt_one.trans_le hH))

end InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm)

abbrev OutsidePrimeIndex (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) :=
  primePool (outsideSquarefreeIdeals S D)

def outsidePrime (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) : OutsidePrimeIndex S D → ActualEisensteinCubic.O :=
  poolPrimary (outsideSquarefreeIdeals S D)

lemma outsidePrime_ne_zero (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    ∀ i,outsidePrime S D i ≠ 0 :=
  poolPrimary_ne_zero _ (outsideSquarefree_admissible S D hbad)

lemma outsidePrime_maximal (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    ∀ i,(Ideal.span {outsidePrime S D i}).IsMaximal := by
  intro i
  rw [show Ideal.span {outsidePrime S D i}=i.val from
    poolPrimary_span _ (outsideSquarefree_admissible S D hbad) i]
  infer_instance

lemma outsidePrime_coprime (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {outsidePrime S D i})) :=
  poolPrimary_coprime _ (outsideSquarefree_admissible S D hbad)

lemma outsidePrime_good (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    ∀ i,lambda ∉ Ideal.span {outsidePrime S D i} :=
  poolPrimary_good _ (outsideSquarefree_admissible S D hbad)

lemma outsidePrime_odd (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {outsidePrime S D i}) ≠ 2 :=
  poolPrimary_odd _ (outsideSquarefree_admissible S D hbad)

lemma outsidePrime_injective (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    Function.Injective (fun i => Ideal.span {outsidePrime S D i}) := by
  intro i j hij
  apply Subtype.ext
  simpa only [outsidePrime,poolPrimary_span _ (outsideSquarefree_admissible S D hbad)] using hij

lemma outsidePrime_primary (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    ∀ i,lambda^2 ∣ outsidePrime S D i-1 := by
  intro i
  exact (CompletedGauss.primaryPrime_spec i.val (outsidePrime_ne_zero S hbad D i)).2.2.2

def initialExcludedNorm (S : Finset (Ideal ActualEisensteinCubic.O)) : ℝ :=
  max 1 (∏ P ∈ S,(Ideal.absNorm P : ℝ))

lemma initialExcludedNorm_ge_one (S : Finset (Ideal ActualEisensteinCubic.O)) : 1 ≤ initialExcludedNorm S :=
  le_max_left _ _

def outsideCanonicalDensity {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ)
    (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D))
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ) (X : ℝ) (J : ℕ) : ℝ :=
  letI := outsidePrime_maximal S hbad D
  densityChildEnergy (outsidePrime S D) (outsidePrime_ne_zero S hbad D)
    (outsidePrime_coprime S hbad D) (outsidePrime_good S hbad D) Finset.univ
    (secondRayMinus (conjugateMonoid (normCharacter χ)) ray)
    (secondRayPlus (conjugateMonoid (normCharacter χ)) ray)
    (primeSubsetGenerator (fun i => Ideal.span {outsidePrime S D i}) R) T V₁ V₂ X X (2*J)

def HasInitialCanonicalDensity {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) : Prop :=
  ∀ deltaLoss : ℝ,0 < deltaLoss → ∀ P : ℕ,∃ J : ℕ,
    ∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
    ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ P ≤ E ∧ ∀ (D : ℕ) (Z X lengthScale K : ℝ)
      (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
      1 ≤ Z → Cpool*Z^E ≤ D → 1 ≤ X → 1 ≤ lengthScale → 1 ≤ K →
      X ≤ Z^P → lengthScale ≤ Z^P → K ≤ Z^P →
      initialExcludedNorm S*primeProductNorm (outsidePrime S D) R ≤ Z^P →
      X*lengthScale ≤ Z^2 →
      K*(initialExcludedNorm S*primeProductNorm (outsidePrime S D) R) ≤ X*lengthScale*Z^(-(1 : ℝ)/20) →
      (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
        z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) →
      outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ C*Z^deltaLoss*(X*lengthScale)^2

end InitialMeanSquare

end

end OAI

end Source186

/- Original source: OAI/NumberTheory/DirichletL/MeanSquare/RetainedDensity.lean; sha256: 1723ab7836b304eb9ec5388dd105613bace95e7c2a8e2c728ecfe75774b97ca0 -/
section Source187
namespace OAI

noncomputable section

namespace InitialMeanSquare

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (primeProductNorm)

lemma initialLogLabel_ge_one (j : SecondLogIndex) : 1 ≤ initialLogLabel j :=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _))
    (Real.one_le_exp (by norm_num))

lemma initialLogColumn_pos (Z B : ℝ) (j : SecondLogIndex) (hZ : 0 < Z) (hB : 0 < B) :
    0 < initialLogColumn Z B j :=
  div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hB)

lemma initialLogColumn_le (Z B : ℝ) (j : SecondLogIndex) (hZ : 0 ≤ Z) (hB : 1 ≤ B) :
    initialLogColumn Z B j ≤ Z := div_le_self hZ
  (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _)) hB)

lemma initialLogLabel_cap (U Kmax : ℝ) (hU : 1 ≤ U) (j : SecondLogIndex)
    (hj : j ∈ secondLogBinBox U Kmax) : initialLogLabel j ≤ U^2*Real.exp 2 := by
  have hj' : j.1 < normLogBin U+1 ∧ j.2.1 < normLogBin U+1 ∧ j.2.2 < normLogBin Kmax+1 := by
    simpa only [secondLogBinBox,Finset.mem_product,Finset.mem_range] using hj
  have he : secondLogE j ≤ U := by
    apply le_trans _ (normLogBin_scale_bounds U hU).1
    unfold secondLogE normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.1
  have hv : secondLogV j ≤ U := by
    apply le_trans _ (normLogBin_scale_bounds U hU).1
    unfold secondLogV normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.2.1
  unfold initialLogLabel
  simpa only [pow_two] using mul_le_mul_of_nonneg_right
    (mul_le_mul he hv (normLogScale_pos _).le (zero_le_one.trans hU)) (Real.exp_pos 2).le

theorem initial_radial_invariant (Z B c σ θ deltaLoss κ : ℝ) (j : SecondLogIndex)
    (hZ : 1 ≤ Z) (hB : 0 < B) (hc : 0 ≤ c) (hcZ : c ≤ Z^deltaLoss)
    (hmargin : deltaLoss+θ ≤ σ-κ)
    (hrad : initialRadial Z (Z^(1+σ)) B j ≤ Z^θ) :
    (secondLogK j*Real.exp 2)*(c*B) ≤
      initialLogColumn Z B j*initialLogLabel j*Z^(-κ) := by
  have hZ0 := zero_lt_one.trans_le hZ
  have hH : 0 < Z^(1+σ) := Real.rpow_pos_of_pos hZ0 _
  have hm : 0 < initialLogColumn Z B j*initialLogLabel j := by
    rw [initial_log_mass Z B hB.ne' j]
    positivity
  have he : Z/Z^(1+σ)=Z^(-σ) := by
    rw [show -σ=(1 : ℝ)-(1+σ) by ring,Real.rpow_sub hZ0,Real.rpow_one]
  have hid : (secondLogK j*Real.exp 2)*(c*B)/(initialLogColumn Z B j*initialLogLabel j)=
      c*(Z/(Z^(1+σ)))*(Z^(1+σ)*secondLogK j*B^2/Z^2) := by
    rw [initial_log_mass Z B hB.ne' j]
    have hE := (Real.exp_pos (2 : ℝ)).ne'
    have hz := hZ0.ne'
    have hh := hH.ne'
    field_simp

  rw [mul_comm (initialLogColumn Z B j*initialLogLabel j)]
  apply (div_le_iff₀ hm).mp
  rw [hid,he]
  calc
    c*Z^(-σ)*(Z^(1+σ)*secondLogK j*B^2/Z^2) ≤ c*Z^(-σ)*Z^θ :=
      mul_le_mul_of_nonneg_left hrad (mul_nonneg hc (Real.rpow_nonneg hZ0.le _))
    _ ≤ Z^deltaLoss*Z^(-σ)*Z^θ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcZ (Real.rpow_nonneg hZ0.le _)) (Real.rpow_nonneg hZ0.le _)
    _ = Z^(deltaLoss-σ+θ) := by rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]; congr 1
    _ ≤ Z^(-κ) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem initial_large_threshold (a b c deltaLoss : ℝ) (hc : 1 ≤ c) (hδ : 0 < deltaLoss) :
    ∃ Z0 : ℝ,1 ≤ Z0 ∧ ∀ Z : ℝ,Z0 ≤ Z →
      Real.exp 2 ≤ Z ∧ c*Real.exp (initialErrorWindow a b) ≤ Z ∧
      initialPolynomialCap a b*Real.exp 2 ≤ Z ∧
      (Real.exp (initialErrorWindow a b))^2*Real.exp 2 ≤ Z ∧ c ≤ Z^deltaLoss := by
  let M := initialErrorWindow a b
  let Q := initialPolynomialCap a b
  let Z0 := 1+Real.exp 2+c*Real.exp M+Q*Real.exp 2+(Real.exp M)^2*Real.exp 2+c^(1/deltaLoss)
  have hc0 := (zero_lt_one.trans_le hc).le
  have hQ := initialPolynomialCap_ge_one a b
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have he2 := Real.exp_pos (2 : ℝ)
  have heM := Real.exp_pos M
  have hr : 0 ≤ c^(1/deltaLoss) := Real.rpow_nonneg hc0 _
  have hp : 0 ≤ (Real.exp M)^2*Real.exp 2 := by positivity
  have hcp : 0 ≤ c*Real.exp M := by positivity
  have hqp : 0 ≤ Q*Real.exp 2 := by positivity
  have hZ0 : 1 ≤ Z0 := by dsimp [Z0]; linarith
  refine ⟨Z0,hZ0,?_⟩
  intro Z hZ
  have hzroot : c^(1/deltaLoss) ≤ Z := by dsimp [Z0] at hZ; linarith
  have hroot : (c^(1/deltaLoss))^deltaLoss=c := by
    rw [←Real.rpow_mul hc0]
    have hd : (1/deltaLoss)*deltaLoss=1 := by field_simp
    rw [hd,Real.rpow_one]
  refine ⟨?_,?_,?_,?_,?_⟩
  · dsimp [Z0] at hZ; linarith
  · change c*Real.exp M ≤ Z; dsimp [Z0] at hZ; linarith
  · change Q*Real.exp 2 ≤ Z; dsimp [Z0] at hZ; linarith
  · change (Real.exp M)^2*Real.exp 2 ≤ Z; dsimp [Z0] at hZ; linarith
  · rw [←hroot]
    exact Real.rpow_le_rpow hr hzroot hδ.le

theorem initial_large_bin_geometry {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (F R : Finset ι) (a b Z σ θ deltaLoss c : ℝ) (j : SecondLogIndex)
    (hZ : 1 ≤ Z) (hc : 1 ≤ c)
    (hR : R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)))
    (hj : j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b))
      (initialErrorRowBound a b Z (Z^(1+σ))))
    (hσ : 0 ≤ σ) (hmargin : deltaLoss+θ ≤ σ-(1 : ℝ)/20)
    (hlarge : Real.exp 2 ≤ Z ∧ c*Real.exp (initialErrorWindow a b) ≤ Z ∧
      initialPolynomialCap a b*Real.exp 2 ≤ Z ∧
      (Real.exp (initialErrorWindow a b))^2*Real.exp 2 ≤ Z ∧ c ≤ Z^deltaLoss)
    (hrad : initialRadial Z (Z^(1+σ)) (primeProductNorm p R) j ≤ Z^θ) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    let lengthScale := initialLogLabel j
    let K := secondLogK j*Real.exp 2
    X ≤ Z^20 ∧ lengthScale ≤ Z^20 ∧ K ≤ Z^20 ∧ c*primeProductNorm p R ≤ Z^20 ∧
      X*lengthScale ≤ Z^2 ∧ K*(c*primeProductNorm p R) ≤ X*lengthScale*Z^(-(1 : ℝ)/20) := by
  dsimp only
  have hZ0 := zero_lt_one.trans_le hZ
  have hB := primeProductNorm_ge_one p hp R
  have hBp := zero_lt_one.trans_le hB
  have hU : 1 ≤ Z*Real.exp (initialErrorWindow a b) := one_le_mul_of_one_le_of_one_le hZ
    (Real.one_le_exp (by unfold initialErrorWindow; positivity))
  have hH : 1 ≤ Z^(1+σ) := Real.one_le_rpow hZ (by linarith)
  have hKmax := initialErrorRowBound_ge_one a b Z (Z^(1+σ)) hZ hH
  have hBcap := (Finset.mem_filter.mp hR).2
  have hKcap := (initial_actual_bin_polynomial_caps a b Z (Z^(1+σ)) hZ hH).2
  have hKbin := initial_bin_row_scale_le (Z*Real.exp (initialErrorWindow a b))
    (initialErrorRowBound a b Z (Z^(1+σ))) hKmax j hj
  have hL := initialLogLabel_cap _ _ hU j hj
  have hp20 (n : ℕ) (hn : n ≤ 20) : Z^n ≤ Z^20 := pow_le_pow_right₀ hZ hn
  have hinv := initial_radial_invariant Z (primeProductNorm p R) c σ θ deltaLoss
    ((1 : ℝ)/20) j hZ hBp (zero_le_one.trans hc) hlarge.2.2.2.2 hmargin hrad
  rw [show -((1 : ℝ)/20)=(-1 : ℝ)/20 by ring] at hinv
  refine ⟨?_,?_,?_,?_,?_,hinv⟩
  · exact (initialLogColumn_le Z _ j hZ0.le hB).trans (by simpa using hp20 1 (by decide))
  · apply hL.trans
    calc
      _ = ((Real.exp (initialErrorWindow a b))^2*Real.exp 2)*Z^2 := by ring
      _ ≤ Z*Z^2 := mul_le_mul_of_nonneg_right hlarge.2.2.2.1 (sq_nonneg Z)
      _ ≤ Z^20 := by simpa [pow_succ,mul_comm] using hp20 3 (by decide)
  · calc
      _ ≤ (initialPolynomialCap a b*Z^17)*Real.exp 2 :=
        mul_le_mul_of_nonneg_right (hKbin.trans hKcap) (Real.exp_pos _).le
      _ = (initialPolynomialCap a b*Real.exp 2)*Z^17 := by ring
      _ ≤ Z*Z^17 := mul_le_mul_of_nonneg_right hlarge.2.2.1 (pow_nonneg hZ0.le _)
      _ ≤ Z^20 := by simpa [pow_succ,mul_comm] using hp20 18 (by decide)
  · calc
      _ ≤ c*(Z*Real.exp (initialErrorWindow a b)) := mul_le_mul_of_nonneg_left hBcap (zero_le_one.trans hc)
      _ = (c*Real.exp (initialErrorWindow a b))*Z := by ring
      _ ≤ Z*Z := mul_le_mul_of_nonneg_right hlarge.2.1 hZ0.le
      _ ≤ Z^20 := by simpa [pow_two] using hp20 2 (by decide)
  · rw [initial_log_mass Z (primeProductNorm p R) hBp.ne' j]
    calc
      _ ≤ Z*Real.exp 2 := mul_le_mul_of_nonneg_right (div_le_self hZ0.le hB) (Real.exp_pos _).le
      _ ≤ Z^2 := by simpa [pow_two] using mul_le_mul_of_nonneg_left hlarge.1 hZ0.le

end

section

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (firstLogDensity)

theorem initial_density_elementary_squared_mass {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : ActualEisensteinCubic.O) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ)
    (X lengthScale K A Vmax : ℝ) (J : ℕ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J) ≤
      (initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3)*K*(X*lengthScale)^2 := by
  let C := initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3
  have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hC : 0 ≤ C := mul_nonneg (initialElementaryConstant_nonneg A Vmax) (pow_nonneg hI _)
  have hd := childDensity_elementary_all_scales p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m T V₁ V₂ X lengthScale K A Vmax J hX hL hK hA hVmax hV₁ hV₂ hs₁ hs₂ hT
  change _/(X*lengthScale) ≤ C*K*X at hd
  have hraw := (div_le_iff₀ (mul_pos hX (zero_lt_one.trans_le hL))).mp hd
  have hbase : 0 ≤ (C*K*X)*(X*lengthScale) := by positivity
  calc
    _ ≤ (C*K*X)*(X*lengthScale) := hraw
    _ ≤ ((C*K*X)*(X*lengthScale))*lengthScale := le_mul_of_one_le_right hbase hL
    _ = _ := by dsimp only [C]; ring

end

section

open MeasureTheory
open scoped BigOperators Classical ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

theorem HasInitialCanonicalDensity.retained_density {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S)
    (hcan : HasInitialCanonicalDensity χ S hbad)
    (a b σ θ ν η : ℝ) (hσ : 0 ≤ σ) (hν : 0 < ν) (hη : 0 < η)
    (hmargin : ν+θ ≤ σ-(1 : ℝ)/20) :
    ∃ J : ℕ,∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
      ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
      ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧ ∀ (D : ℕ) (Z : ℝ)
        (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (j : SecondLogIndex)
        (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
        1 ≤ Z → Cpool*Z^E ≤ D →
        R ∈ boundedPrimeSupports (outsidePrime S D) Finset.univ (Z*Real.exp (initialErrorWindow a b)) →
        j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z (Z^(1+σ))) →
        initialRadial Z (Z^(1+σ)) (primeProductNorm (outsidePrime S D) R) j ≤ Z^θ →
        (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
          z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2) →
        outsideCanonicalDensity χ S hbad D ray R T V₁ V₂
          (initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j) J ≤
        C*Z^η*(initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j*initialLogLabel j)^2 := by
  obtain ⟨J,hJ⟩ := hcan η hη 20
  refine ⟨J,?_⟩
  intro V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂
  obtain ⟨Cc,Cpool,E,hCc,hCpool,hPE,hcanonical⟩ := hJ V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂
  obtain ⟨A,Vmax,hA,hVmax,hV₁,hV₂,hs₁,hs₂⟩ :=
    initial_two_windows_bounded V₁ V₂ hVc₁ hVc₂ hVs₁.continuous hVs₂.continuous
  obtain ⟨Z0,hZ0,hthreshold⟩ := initial_large_threshold a b (initialExcludedNorm S) ν
    (initialExcludedNorm_ge_one S) hν
  let Ce := initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3
  let K0 := initialPolynomialCap a b*Z0^17*Real.exp 2
  let C := Cc+Ce*(K0+1)+1
  have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hCe : 0 ≤ Ce := mul_nonneg (initialElementaryConstant_nonneg A Vmax) (pow_nonneg hI _)
  have hcap := initialPolynomialCap_ge_one a b
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCcC : Cc ≤ C := by dsimp [C]; nlinarith
  have hCeC : Ce ≤ C := by dsimp [C]; nlinarith
  have hCeKC : Ce*K0 ≤ C := by dsimp [C]; nlinarith
  refine ⟨C,Cpool,E,hC,hCpool,hPE,?_⟩
  intro D Z R ray j T hZ hpool hR hj hrad hT
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let lengthScale := initialLogLabel j
  let Kr := secondLogK j*Real.exp 2
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ Z^(1+σ) := Real.one_le_rpow hZ (by linarith)
  have hB := primeProductNorm_ge_one p hp R
  have hBpos := zero_lt_one.trans_le hB
  have hX : 0 < X := initialLogColumn_pos Z _ j hZp hBpos
  have hL : 1 ≤ lengthScale := initialLogLabel_ge_one j
  have hKr : 1 ≤ Kr := one_le_mul_of_one_le_of_one_le
    (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  have hZη : 1 ≤ Z^η := Real.one_le_rpow hZ hη.le
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hΨ₁ : ∀ z,‖secondRayMinus Ψ ray z‖ ≤ 1 :=
    fun z => (secondRayMinus_norm_le Ψ ray z).trans (hΨ z)
  have hΨ₂ : ∀ z,‖secondRayPlus Ψ ray z‖ ≤ 1 :=
    fun z => (secondRayPlus_norm_le Ψ ray z).trans (hΨ z)
  have hTb : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ Kr := by
    intro z hz
    exact ⟨(hT z hz).1.1,(hT z hz).2.1,(hT z hz).2.2.2⟩
  have promote (d : ℝ) (hd : d ≤ C)
      (he : outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ d*(X*lengthScale)^2) :
      outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ C*Z^η*(X*lengthScale)^2 :=
    he.trans (mul_le_mul_of_nonneg_right (hd.trans (le_mul_of_one_le_right hC.le hZη)) (sq_nonneg _))
  by_cases hzlarge : Z0 ≤ Z
  · have hgeom := initial_large_bin_geometry p hp Finset.univ R a b Z σ θ ν (initialExcludedNorm S)
      j hZ (initialExcludedNorm_ge_one S) hR hj hσ hmargin (hthreshold Z hzlarge) hrad
    dsimp only at hgeom
    by_cases hxlarge : 1 ≤ X
    · exact (hcanonical D Z X lengthScale Kr R ray T hZ hpool hxlarge hL hKr
        hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2.1 hgeom.2.2.2.2.2 hT).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcC (Real.rpow_nonneg hZp.le _)) (sq_nonneg _))
    · have hKL : Kr ≤ lengthScale := initial_subunit_row_le_label Z X lengthScale Kr
        (initialExcludedNorm S*primeProductNorm p R) ((1 : ℝ)/20) hZ (le_of_not_ge hxlarge)
        (zero_le_one.trans hL) (zero_le_one.trans hKr)
        (one_le_mul_of_one_le_of_one_le (initialExcludedNorm_ge_one S) hB)
        (by norm_num) (by simpa only [Kr,X,lengthScale,neg_div] using hgeom.2.2.2.2.2)
      apply promote Ce hCeC
      exact initial_subunit_density_bound p hp hcop hg (outsidePrime_odd S hbad D)
        (outsidePrime_injective S hbad D) Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        hΨ₁ hΨ₂ _ T V₁ V₂ X lengthScale Kr A Vmax J hX hL hKr hKL hA hVmax hV₁ hV₂ hs₁ hs₂ hTb
  · have hKmax := initialErrorRowBound_ge_one a b Z (Z^(1+σ)) hZ hH
    have hkr : Kr ≤ K0 := by
      have hbin := initial_bin_row_scale_le (Z*Real.exp (initialErrorWindow a b))
        (initialErrorRowBound a b Z (Z^(1+σ))) hKmax j hj
      have hcapZ := (initial_actual_bin_polynomial_caps a b Z (Z^(1+σ)) hZ hH).2
      have hpow : Z^17 ≤ Z0^17 := pow_le_pow_left₀ hZp.le (le_of_not_ge hzlarge) 17
      calc
        Kr ≤ (initialPolynomialCap a b*Z^17)*Real.exp 2 :=
          mul_le_mul_of_nonneg_right (hbin.trans hcapZ) (Real.exp_pos _).le
        _ ≤ K0 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hcap)) (Real.exp_pos _).le
    apply promote (Ce*Kr) ((mul_le_mul_of_nonneg_left hkr hCe).trans hCeKC)
    exact initial_density_elementary_squared_mass p hp hcop hg (outsidePrime_odd S hbad D)
      (outsidePrime_injective S hbad D) Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      hΨ₁ hΨ₂ _ T V₁ V₂ X lengthScale Kr A Vmax J hX hL hKr hA hVmax hV₁ hV₂ hs₁ hs₂ hTb

end

section

open scoped BigOperators Classical
open SecondPassArithmetic

theorem initial_log_harmonic_small_power (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ,0 < C ∧ ∀ (Y U Kmax : ℝ),1 ≤ Y → 0 < U → 0 < Kmax → U ≤ Y → Kmax ≤ Y →
      ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) ≤ C*Y^η := by
  obtain ⟨C,hC,hbound⟩ := globalLogFactor_small_power η hη
  refine ⟨128*Real.exp 1*C,by positivity,?_⟩
  intro Y U Kmax hY hU hK hUY hKY
  let B := 1+Real.log 27+22*Real.log Y
  have hlog := Real.log_nonneg hY
  have h27 : 0 ≤ Real.log 27 := Real.log_nonneg (by norm_num)
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hu := normLogBin_le_log_upper U Y hU hUY hY
  have hk := normLogBin_le_log_upper Kmax Y hK hKY hY
  have huB : (normLogBin U : ℝ)+1 ≤ B := by dsimp [B]; linarith
  have hkB : (normLogBin Kmax : ℝ)+1 ≤ B := by dsimp [B]; linarith
  have hcard : ((secondLogBinBox U Kmax).card : ℝ) ≤ B^3 := by
    rw [secondLogBinBox_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ B^2*B := mul_le_mul (pow_le_pow_left₀ (by positivity) huB 2) hkB (by positivity) (sq_nonneg B)
      _ = _ := by ring
  have hh : 128*Real.exp 1*(normLogBin U+1 : ℝ) ≤ 128*Real.exp 1*B :=
    mul_le_mul_of_nonneg_left huB (by positivity)
  calc
    _ ≤ B^3*(128*Real.exp 1*B) := mul_le_mul hcard hh (by positivity) (pow_nonneg (zero_le_one.trans hB) _)
    _ = 128*Real.exp 1*B^4 := by ring
    _ ≤ 128*Real.exp 1*B^10 := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hB (by decide)) (by positivity)
    _ ≤ 128*Real.exp 1*(C*Y^η) := mul_le_mul_of_nonneg_left (hbound Y hY) (by positivity)
    _ = _ := by ring

theorem initial_row_log_budget (η Ccap : ℝ) (hη : 0 < η) (hcap : 1 ≤ Ccap) :
    ∃ C : ℝ,0 < C ∧ ∀ (Z U Kmax : ℝ),1 ≤ Z → 0 < U → 0 < Kmax →
      U ≤ Ccap*Z^17 → Kmax ≤ Ccap*Z^17 →
      (Kmax*Real.exp 2)^η*((secondLogBinBox U Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin U+1 : ℝ)) ≤ C*Z^(34*η) := by
  obtain ⟨C,hC,hlog⟩ := initial_log_harmonic_small_power η hη
  refine ⟨C*(Real.exp 2)^η*Ccap^(2*η),by positivity,?_⟩
  intro Z U Kmax hZ hU hK hUY hKY
  have hZ0 := zero_lt_one.trans_le hZ
  have hcap0 := zero_lt_one.trans_le hcap
  let Y := Ccap*Z^17
  have hY : 1 ≤ Y := one_le_mul_of_one_le_of_one_le hcap (one_le_pow₀ hZ)
  have hlogs := hlog Y U Kmax hY hU hK hUY hKY
  have hrow : (Kmax*Real.exp 2)^η ≤ (Y*Real.exp 2)^η := Real.rpow_le_rpow
    (mul_pos hK (Real.exp_pos _)).le (mul_le_mul_of_nonneg_right hKY (Real.exp_pos _).le) hη.le
  calc
    _ = (Kmax*Real.exp 2)^η*(((secondLogBinBox U Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin U+1 : ℝ))) := by ring
    _ ≤ (Y*Real.exp 2)^η*(C*Y^η) := mul_le_mul hrow hlogs (by positivity) (by positivity)
    _ = C*(Real.exp 2)^η*Y^(2*η) := by
      rw [Real.mul_rpow (zero_le_one.trans hY) (Real.exp_pos _).le]
      rw [show 2*η=η+η by ring,Real.rpow_add (zero_lt_one.trans_le hY)]
      ring
    _ = (C*(Real.exp 2)^η*Ccap^(2*η))*Z^(34*η) := by
      dsimp [Y]
      rw [Real.mul_rpow hcap0.le (pow_nonneg hZ0.le _),←Real.rpow_natCast_mul hZ0.le]
      norm_num
      ring_nf

end

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity normalizedColumn columnLog)

theorem HasInitialCanonicalDensity.retained_source {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S)
    (hcan : HasInitialCanonicalDensity χ S hbad)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b σ θ ν η : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hσ : 0 ≤ σ) (hν : 0 < ν) (hη : 0 < η)
    (hmargin : ν+θ ≤ σ-(1 : ℝ)/20) :
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧
      ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → Cpool*Z^E ≤ D →
      let p := outsidePrime S D
      let hp := outsidePrime_ne_zero S hbad D
      let hcop := outsidePrime_coprime S hbad D
      let hg := outsidePrime_good S hbad D
      letI := outsidePrime_maximal S hbad D
      let Ψ := conjugateMonoid (normCharacter χ)
      let H := Z^(1+σ)
      let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
      let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray
            (initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z (initialErrorWindow a b) j))
            G G W H‖ else 0) ≤ C*H*Z^(35*η) := by
  obtain ⟨J,hJ⟩ := HasInitialCanonicalDensity.retained_density χ S hbad hcan a b σ θ ν η hσ hν hη hmargin
  have hM : 0 ≤ initialErrorWindow a b := by unfold initialErrorWindow; positivity
  obtain ⟨windows,Ct,Cs,hCt,hCs,hwc,hws,ht⟩ :=
    initial_subbin_transfer U hUc hUs g W (initialErrorWindow a b) hM hU hgs η hη 0 (2*J)
  obtain ⟨Ce,Cpool,E,hCe,hCpool,hPE,henergy⟩ := hJ (windows 5) (windows 6) (hwc 5) (hwc 6) (hws 5) (hws 6)
  obtain ⟨Cl,hCl,hlog⟩ := initial_row_log_budget η (initialPolynomialCap a b) hη (initialPolynomialCap_ge_one a b)
  let C0 := Ct*Real.exp 4*Ce*Cs*initialRayMass*Cl
  have hray := initialRayMass_nonneg
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨C0+1,Cpool,E,by linarith,hCpool,hPE,?_⟩
  intro D Z hZ hpool
  dsimp only
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let M := initialErrorWindow a b
  let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
  let Kmax := initialErrorRowBound a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let s := fun (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z M j)
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hKmax : 1 ≤ Kmax := initialErrorRowBound_ge_one a b Z H hZ hH
  let B : SecondRayIndex → Finset (OutsidePrimeIndex S D) → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg (outsidePrime_injective S hbad D) (outsidePrime_odd S hbad D)
        (outsidePrime_primary S hbad D) Finset.univ R Ψ 1 ray K Z H M j (s R j)
        hZp hHp hΨ (Finset.filter_subset _ _))
  have hB (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) :=
    Classical.choose_spec
      (ht p hp hcop hg (outsidePrime_injective S hbad D) (outsidePrime_odd S hbad D)
        (outsidePrime_primary S hbad D) Finset.univ R Ψ 1 ray K Z H M j (s R j)
        hZp hHp hΨ (Finset.filter_subset _ _))
  let d := H*Real.exp 4*(Ce*Z^η)*Cs*(Kmax*Real.exp 2)^η
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hterm (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D))
      (hR : R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M))
      (j : SecondLogIndex) (hj : j ∈ secondLogBinBox (Z*Real.exp M) Kmax)
      (hlow : initialRadial Z H (primeProductNorm p R) j ≤ Z^θ) :
      initialSquarefreeBinCost p hp hcop hg Finset.univ R Ψ 1 ray K Z H M η j windows (B ray R j) ≤
        d/primeProductNorm p R*‖secondRayCoefficient ray‖ := by
    have hT := initial_squarefree_target_geometry p hp hg (outsidePrime_odd S hbad D)
      Finset.univ R K Z M j
    have hTe : ∀ z ∈ sourceIdealTarget ((s R j).image (sourceObservation p)),
        Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧ z.2 ≠ 0 ∧
        ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2 := by
      intro z hz
      exact ⟨(hT z hz).1,(hT z hz).2.1,(hT z hz).2.2.1,(hT z hz).2.2.2.trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num)) (normLogScale_pos _).le)⟩
    have he := henergy D Z R ray j _ hZ hpool hR hj hlow hTe
    have he' :
        densityChildEnergy p hp hcop hg Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (1*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (sourceIdealTarget ((s R j).image (sourceObservation p)))
          (windows 5) (windows 6) (initialLogColumn Z (primeProductNorm p R) j)
          (initialLogColumn Z (primeProductNorm p R) j) (2*J) ≤
          (Ce*Z^η)*(initialLogColumn Z (primeProductNorm p R) j*initialLogLabel j)^2 := by
      simpa only [outsideCanonicalDensity,one_mul] using he
    exact initial_bin_cost_uniform p hp hcop hg Finset.univ R Ψ 1 ray K Z H M Kmax η Cs
      (Ce*Z^η) hZp hHp hKmax hη.le hCs (by positivity) j hj windows (B ray R j) (2*J) 0
      (hB ray R j).1 (hB ray R j).2.1 he'
  have hsum :
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
        if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray (s R j) G G W H‖ else 0) ≤
      Ct*(d*initialRayMass*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left
      (initial_harmonic_aggregation p (outsidePrime_injective S hbad D) Finset.univ
        (Z*Real.exp M) Kmax d hd
        (fun ray R j => if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          initialSquarefreeBinCost p hp hcop hg Finset.univ R Ψ 1 ray K Z H M η j windows (B ray R j)
          else 0) (by
          intro ray R hR j hj
          split_ifs with hlow
          · exact hterm ray R hR j hj hlow
          · have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
            positivity)) hCt)
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ray hray
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with hlow
    · convert (hB ray R j).2.2 using 1 ;
        dsimp only [initialSquarefreeBinCost,s,G,B] ; ring
    · simp
  have hlogBound := hlog Z (Z*Real.exp M) Kmax hZ (by positivity) (zero_lt_one.trans_le hKmax)
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).1
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).2
  calc
    _ ≤ Ct*(d*initialRayMass*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := hsum
    _ = (Ct*Real.exp 4*Ce*Cs*initialRayMass)*H*Z^η*
        ((Kmax*Real.exp 2)^η*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := by dsimp [d]; ring
    _ ≤ (Ct*Real.exp 4*Ce*Cs*initialRayMass)*H*Z^η*(Cl*Z^(34*η)) :=
      mul_le_mul_of_nonneg_left hlogBound (by positivity)
    _ = C0*H*Z^(35*η) := by
      rw [show 35*η=η+34*η by ring,Real.rpow_add hZp]
      dsimp [C0]
      ring
    _ ≤ (C0+1)*H*Z^(35*η) := by
      gcongr
      linarith

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

theorem HasInitialCanonicalDensity.nonzero_source_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S)
    (hcan : HasInitialCanonicalDensity χ S hbad)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b σ ε : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hσ : (1 : ℝ)/20 < σ) (hε : 0 < ε) :
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧
      ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → Cpool*Z^E ≤ D →
      let p := outsidePrime S D
      let hp := outsidePrime_ne_zero S hbad D
      let hg := outsidePrime_good S hbad D
      let hinj := outsidePrime_injective S hbad D
      letI := outsidePrime_maximal S hbad D
      let Ψ := conjugateMonoid (normCharacter χ)
      let H := Z^(1+σ)
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
        W H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖ ≤ C*H*Z^ε := by
  let η := min 1 (ε/100)
  let ν := (σ-(1 : ℝ)/20)/3
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : 35*η ≤ ε := by
    have hh : η ≤ ε/100 := min_le_right _ _
    linarith
  have hν : 0 < ν := by dsimp [ν]; linarith
  have hσ0 : 0 ≤ σ := by linarith
  have hmargin : ν+ν ≤ σ-(1 : ℝ)/20 := by dsimp [ν]; linarith
  obtain ⟨Cl,Cpool,E,hCl,hCpool,hPE,hlow⟩ := HasInitialCanonicalDensity.retained_source χ S hbad hcan U hUc hUs g W
    a b σ ν ν η hU hgs hσ0 hν hη hmargin
  obtain ⟨Ch,hCh,hhigh⟩ := initial_high_radial_source U hUc hUs g W a b ν 1 η hU hgs hν hη hη1
  refine ⟨Cl+Ch,Cpool,E,by positivity,hCpool,hPE,?_⟩
  intro D Z hZ hpool
  dsimp only
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let hinj := outsidePrime_injective S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let M := initialErrorWindow a b
  let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
  let Kmax := initialErrorRowBound a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let s := fun (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z M j)
  let f := fun (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray (s R j) G G W H‖
  let Lsum := ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
    ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
      if initialRadial Z H (primeProductNorm p R) j ≤ Z^ν then f ray R j else 0
  let Hsum := ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
    ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
      if Z^ν < initialRadial Z H (primeProductNorm p R) j then f ray R j else 0
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hL : Lsum ≤ Cl*H*Z^(35*η) := hlow D Z hZ hpool
  have hHi : Hsum ≤ Ch*Z^(-(1 : ℝ)) :=
    hhigh p hp hcop hg hinj (outsidePrime_odd S hbad D) (outsidePrime_primary S hbad D)
      Finset.univ Ψ 1 Z H hZ hH hΨ (fun _ R j => s R j) (fun _ _ _ => Finset.filter_subset _ _)
  have hrow : ∀ R ∈ (Finset.univ : Finset (OutsidePrimeIndex S D)).powerset,
      ∀ x ∈ secondSupportedSector p Finset.univ K R Z M,elementNorm (sourceObservation p x).1 ≤ Kmax := by
    intro R hR x hx
    exact initialErrorRowBound_valid p hp Finset.univ R a b Z H hZp hHp x hx
  have htotal := initial_nonzero_source_norm_le_squarefree_bins p hp hcop hg hinj
    (outsidePrime_odd S hbad D) (outsidePrime_primary S hbad D) Finset.univ Ψ 1 g W
    Z H M Kmax hZp hgs K hrow
  have hpart : (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
      ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,f ray R j)=Lsum+Hsum := by
    dsimp only [Lsum,Hsum]
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ray hray
    apply Finset.sum_congr rfl
    intro R hR
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hh : initialRadial Z H (primeProductNorm p R) j ≤ Z^ν
    · rw [ite_eq_left hh,ite_eq_right (not_lt.mpr hh),add_zero]
    · rw [ite_eq_right hh,ite_eq_left (lt_of_not_ge hh),zero_add]
  have hpower : Z^(35*η) ≤ Z^ε := Real.rpow_le_rpow_of_exponent_le hZ hηε
  have hsmall : Z^(-(1 : ℝ)) ≤ H*Z^ε := by
    have h1 : Z^(-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hZ (by norm_num)
    exact h1.trans (one_le_mul_of_one_le_of_one_le hH (Real.one_le_rpow hZ hε.le))
  calc
    _ ≤ ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
      ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,f ray R j := htotal
    _ = Lsum+Hsum := hpart
    _ ≤ Cl*H*Z^(35*η)+Ch*Z^(-(1 : ℝ)) := add_le_add hL hHi
    _ ≤ Cl*H*Z^ε+Ch*(H*Z^ε) := add_le_add
      (mul_le_mul_of_nonneg_left hpower (mul_nonneg hCl.le hHp.le))
      (mul_le_mul_of_nonneg_left hsmall hCh.le)
    _ = (Cl+Ch)*H*Z^ε := by ring

end InitialMeanSquare

end

end OAI

end Source187

/- Original source: OAI/NumberTheory/DirichletL/MeanSquare/CanonicalTailBounds.lean; sha256: 4a7fe863e5abd113e7c98a36506f20bb80f89253e9b01aba0c31d6bd71b1173d -/
section Source188
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem outside_mean_square_of_canonical_density {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S,Prime P)
    (hcan : HasInitialCanonicalDensity χ S hbad)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (σ ε : ℝ) (hσ : (1 : ℝ)/20 < σ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → b*Z ≤ D →
      ∀ T : Finset ActualEisensteinCubic.O,
      (∀ z ∈ T,(Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Z^(1+σ)) →
      (∀ z ∈ T,z ≠ 0) →
      (∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
        (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2) ≤ C*Z*(Z^(1+σ))*Z^ε := by
  let g0 := initialLogProfile W a b ha hs hW
  let g := conjugateProfile g0
  let M := initialErrorWindow a b
  have hM : 0 ≤ M := by dsimp [M,initialErrorWindow]; positivity
  have hg0 : ∀ t,g0 t ≠ 0 → |t| ≤ M := initialLogProfile_support W a b ha hs hW
  have hg : ∀ t,g t ≠ 0 → |t| ≤ M := conjugateProfile_support_bound g0 M hg0
  obtain ⟨U,hUc,hUs,hUeq,hUsupp,hUzero⟩ := FourierBridge.exists_complex_smooth_cutoff M hM
  have hU : ∀ t,g t ≠ 0 → U t=1 := fun t ht => hUeq t (hg t ht)
  obtain ⟨Cs,Cpool,E,hCs,hCpool,hE,hsource⟩ := HasInitialCanonicalDensity.nonzero_source_bound χ S hbad hcan
    U hUc hUs g rowMajorant a b σ ε hU hg hσ hε
  obtain ⟨Ce,hCe,herrors⟩ := outside_mean_square_source_with_errors W a b ha hs hW
  refine ⟨Cs+Ce,by positivity,?_⟩
  intro D Z hZ hD T hT hT0
  let Db : ℕ := max D ⌈Cpool*Z^E⌉₊
  have hDDb : D ≤ Db := le_max_left _ _
  have hpool : Cpool*Z^E ≤ (Db : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right D ⌈Cpool*Z^E⌉₊)
  have hDb : b*Z ≤ (Db : ℝ) := hD.trans (by exact_mod_cast hDDb)
  let p := outsidePrime S Db
  let hp := outsidePrime_ne_zero S hbad Db
  let hg := outsidePrime_good S hbad Db
  let hinj := outsidePrime_injective S hbad Db
  let := outsidePrime_maximal S hbad Db
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let G := fun V => normalizedColumn p (fun T => g0 (columnLog p Z T)) V
  let MS := ∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S Db) (outsideIdealsUpTo_ne_bot S Db)
    (outside_good S Db hbad) χ (fun n => W (n/Z)) z‖^2
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hεZ : 1 ≤ Z^ε := Real.one_le_rpow hZ hε.le
  have he := herrors χ S Db hbad hSp Z H hZp hHp hDb T hT hT0
  have hsrc := hsource Db Z hZ hpool
  have hstar : (fun V => star (G V)) =
      (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) := by
    funext V
    exact star_normalizedColumn p g0 Z V
  have hsrc' :
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
        rowMajorant H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖ ≤ Cs*H*Z^ε := by
    rw [hstar]
    exact hsrc
  change MS/Z ≤
    ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
      rowMajorant H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖+Ce*H-‖G ∅‖^2 at he
  have herr : Ce*H ≤ Ce*H*Z^ε := le_mul_of_one_le_right (mul_nonneg hCe.le hHp.le) hεZ
  have hnorm : MS/Z ≤ (Cs+Ce)*H*Z^ε := by
    nlinarith [sq_nonneg ‖G ∅‖]
  have hfinal := (div_le_iff₀ hZp).mp hnorm
  have hMS : (∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)=MS := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [outside_row_cutoff_stable S hbad hDDb χ W b Z hZp (fun t ht => (hs ht).2) hD z]
  rw [hMS]
  convert hfinal using 1 ; dsimp only [H] ; ring

end InitialMeanSquare

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

lemma firstTail_inverse_scale_bound (K D U:ℝ) (hK:0<K) (hD:0<D) (hU:D≤U):
    ((min 1 (K/D))⁻¹)^2≤(1+U/K)^2 := by
  have hU0:0≤U/K:=div_nonneg (hD.le.trans hU) hK.le
  have hi:(min 1 (K/D))⁻¹≤1+U/K:=by
    by_cases h:1≤K/D
    · rw [min_eq_left h,inv_one];linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)),inv_div]
      exact (div_le_div_of_nonneg_right hU hK.le).trans (by linarith)
  exact pow_le_pow_left₀ (inv_nonneg.mpr (le_min zero_le_one (div_pos hK hD).le)) hi 2

lemma firstTail_scalar_bound (K D E U₁ U₂ lengthScale B G₁ G₂ P H:ℝ) (A:ℕ)
    (hK:0<K) (hD:0<D) (hE:0<E) (hU₁:0<U₁) (hU₂:0<U₂)
    (hL:0≤lengthScale) (hG₁:0≤G₁) (hG₂:0≤G₂) (hP:0≤P) (hH:0≤H)
    (hDb:D≤lengthScale*B^2) (hEb:E≤B^2) (hU₁b:U₁≤lengthScale) (hU₂b:U₂≤lengthScale):
    (128*U₁)*(128*U₂)*(G₁*G₂*K)*
      (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+H)^A))≤
    (128*lengthScale)^2*(G₁*G₂*K)*P*(1+lengthScale^3*B^4/K)^2/(1+H)^A := by
  have hden:D*E*U₁*U₂≤lengthScale^3*B^4:=by
    calc
      _ ≤ (lengthScale*B^2)*B^2*lengthScale*lengthScale:=mul_le_mul
        (mul_le_mul (mul_le_mul hDb hEb hE.le (mul_nonneg hL (sq_nonneg _))) hU₁b hU₁.le (by positivity))
        hU₂b hU₂.le (by positivity)
      _ = _:=by ring
  have hi:=firstTail_inverse_scale_bound K (D*E*U₁*U₂) (lengthScale^3*B^4) hK (by positivity) hden
  have hpref:(128*U₁)*(128*U₂)*(G₁*G₂*K)≤(128*lengthScale)^2*(G₁*G₂*K):=by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      _ ≤ (128*lengthScale)*(128*lengthScale):=mul_le_mul (mul_le_mul_of_nonneg_left hU₁b (by norm_num))
        (mul_le_mul_of_nonneg_left hU₂b (by norm_num)) (by positivity) (by positivity)
      _ = _:=by ring
  calc
    _ = ((128*U₁)*(128*U₂)*(G₁*G₂*K))*P*((min 1 (K/(D*E*U₁*U₂)))⁻¹)^2/(1+H)^A:=by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_pow];ring
    _ ≤ _:=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hpref hP) hi (sq_nonneg _) (by positivity)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma cubeCoordinates_radical_bound (b:CubeCoordinates ι) (B:ℝ) (hB:0≤B)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B):
    primeProductNorm p b.support≤B^2 := by
  have hd:(∏i∈b.support,p i)∣primeProduct p b.support b.leftExponent*primeProduct p b.support b.rightExponent:=by
    rw [←primeProduct_add]
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    simpa only [pow_one] using pow_dvd_pow (p i) (b.support_pos i hi)
  have hb0:=mul_ne_zero (primeProduct_ne_zero p hp b.support b.leftExponent)
    (primeProduct_ne_zero p hp b.support b.rightExponent)
  have hn:=element_norm_le_of_dvd hb0 hd
  simp only [map_mul,norm_mul,mul_pow] at hn
  exact hn.trans (by simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma cubeSourceDivisor_norm_bound (b:CubeCoordinates ι) (C D:Finset ι) (B lengthScale:ℝ)
    (hB:0≤B) (hL:0≤lengthScale) (hCB:Disjoint C b.support)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B)
    (hC:primeProductNorm p C≤lengthScale)
    (hD:D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit):
    primeProductNorm p D≤lengthScale*B^2 := by
  calc
    _ ≤ primeProductNorm p (C∪b.support):=primeProductNorm_mono p hp
      (hD.trans (Finset.union_subset_union_right (Finset.filter_subset _ _)))
    _ = primeProductNorm p C*primeProductNorm p b.support:=primeProductNorm_union p _ _ hCB
    _ ≤ _:=mul_le_mul hC (cubeCoordinates_radical_bound p hp b B hB hb₁ hb₂)
      (primeProductNorm_pos p hp _).le hL

lemma cubeSourceDivisors_card
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (b:CubeCoordinates ι) (C:Finset ι) (B lengthScale:ℝ) (hB:0<B) (hL:0<lengthScale) (hCB:Disjoint C b.support)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B)
    (hC:primeProductNorm p C≤lengthScale):
    ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)≤128*(lengthScale*B^2) := by
  let M:=C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit
  have he:boundedPrimeSupports p M (lengthScale*B^2)=M.powerset:=by
    apply Finset.filter_eq_self.mpr
    intro D hD
    exact cubeSourceDivisor_norm_bound p hp b C D B lengthScale hB.le hL.le hCB hb₁ hb₂ hC (Finset.mem_powerset.mp hD)
  rw [←he]
  exact boundedPrimeSupports_card_positive p hp hinj M _ (mul_pos hL (sq_pos_of_pos hB))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceMobiusDivisor_norm_le_one (D:Finset ι):
    ‖(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)‖≤1 := by
  have hmu : ‖(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)‖≤1 := by
    unfold UniqueFactorizationMonoid.moebius
    split_ifs <;> simp
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (primeProductNorm_pos p hp D)]
  exact (div_le_div_of_nonneg_right hmu (primeProductNorm_pos p hp D).le).trans
    ((div_le_one (primeProductNorm_pos p hp D)).mpr (primeProductNorm_ge_one p hp D))

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem canonicalCubeDualTail_support
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:ActualEisensteinCubic.O→*ℂ) (m₁ m₂ f:ActualEisensteinCubic.O) (g₁ g₂ W:𝓢(ℝ,ℂ))
    (ell K M:ℝ) (hell:0<ell) (hgM:∀t,g₁ t≠0→t≤M)
    (hC:¬primeProductNorm p C≤ell*Real.exp M) (T:Finset ι→Finset ActualEisensteinCubic.O):
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K T=0 := by
  have hz (S:Finset ι):g₁ (columnLog p ell ((b.rightDivisor∪C)∪S))=0:=by
    by_contra h
    exact hC ((primeProductNorm_mono p hp
      (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)).trans
      (columnLog_norm_upper p hp ell M hell _ (hgM _ h)))
  have hcoef (S:Finset ι):canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun R=>g₁ (columnLog p ell R)) S=0:=by
    simp only [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn,ite_true,hz,mul_zero,zero_mul]
  simp only [canonicalCubeDualTail,actualFirstKernel,threeGaussRowFactor,hcoef,mul_zero,
    star_zero,zero_mul,ite_self,Finset.sum_const_zero,tsum_zero]

end

theorem full_uniform_canonicalSourceTail_bound (ε:ℝ) (hε:0<ε) (A:ℕ):
    ∃(s:Finset (ℕ×ℕ)) (C:ℝ),0<C ∧
    ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal ActualEisensteinCubic.O))
      (a:CubeCoordinates ι→Finset ι→Ideal ActualEisensteinCubic.O→ℂ) (Ψ₁ Ψ₂:ActualEisensteinCubic.O→*ℂ)
      (m₁ m₂:ActualEisensteinCubic.O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ M₁ M₂ Ksrc K ell B F lengthScale:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<Ksrc → 0<K → 0<ell → 1≤B → 1≤F → 1≤lengthScale →
      ell*Real.exp M₁≤lengthScale → ell*Real.exp M₂≤lengthScale →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) →
      (∀t,g₁ t≠0→t≤M₁) → (∀t,g₂ t≠0→t≤M₂) →
      ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell‖≤
      C*B^(4+ε)*lengthScale^4*F*Γ*(G₁*G₂*Ksrc)*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*
        (1+lengthScale^3*B^4/Ksrc)^2/(1+(Ksrc/K)/Real.exp (M₁+M₂))^A := by
  obtain ⟨s,Ct,hCt,hkernel⟩:=full_uniform_canonicalSource_kernel_tail A
  obtain ⟨Cb,hCb,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨s,Cb*128^5*Ct,by positivity,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Γ G₁ G₂ M₁ M₂ Ksrc K ell B F lengthScale
    hΓ hG₁ hG₂ hKsrc hK hell hB hF hL hL₁ hL₂ hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha hg₁ hg₂ hM₁ hM₂
  have hB0:0<B:=zero_lt_one.trans_le hB
  have hL0:0<lengthScale:=zero_lt_one.trans_le hL
  let P:=Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let H:ℝ:=(Ksrc/K)/Real.exp (M₁+M₂)
  let Q:ℝ:=(128*lengthScale)^2*(G₁*G₂*Ksrc)*P*(1+lengthScale^3*B^4/Ksrc)^2/(1+H)^A
  have hP:0≤P:=by dsimp [P];positivity
  have hH:0≤H:=by dsimp [H];positivity
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hlabel:(labels.card:ℝ)≤128*F:=DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hbcount:(bs.card:ℝ)≤Cb*B^(1+ε)*B:=by
    apply hcount p hp hinj bs B B hB hB0.le hadm hb₁ hb₂
    intro b hb
    have hn:primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)≤B^2:=
      (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
        (cubeCoordinates_radical_bound p hp b B hB0.le (hb₁ b hb) (hb₂ b hb))
    change ‖eisEmbedding (∏i∈cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖^2≤B^2 at hn
    nlinarith [norm_nonneg (eisEmbedding (∏i∈cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i))]
  let z (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal ActualEisensteinCubic.O):ℂ:=
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I)
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W Ksrc (canonicalSourceCutoff p K ell b C)
  have hblock (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι) (hC:C∈boundedPrimeSupports p (pool\b.support) lengthScale) (I:Ideal ActualEisensteinCubic.O):
      ‖z b C I‖≤(128*(lengthScale*B^2))*Q:=by
    have hCb:primeProductNorm p C≤lengthScale:=(Finset.mem_filter.mp hC).2
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hiB=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hiB)
    let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
    let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
    let U₁:=X₁*Real.exp M₁
    let U₂:=X₂*Real.exp M₂
    let E:=primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
    have hU₁:0<U₁:=mul_pos (div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))) (Real.exp_pos _)
    have hU₂:0<U₂:=mul_pos (div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))) (Real.exp_pos _)
    have hE:0<E:=primeProductNorm_pos p hp _
    have hU₁b:U₁≤lengthScale:=(mul_le_mul_of_nonneg_right (div_le_self hell.le
      (one_le_mul_of_one_le_of_one_le (primeProductNorm_ge_one p hp _) (primeProductNorm_ge_one p hp _))) (Real.exp_pos M₁).le).trans hL₁
    have hU₂b:U₂≤lengthScale:=(mul_le_mul_of_nonneg_right (div_le_self hell.le
      (one_le_mul_of_one_le_of_one_le (primeProductNorm_ge_one p hp _) (primeProductNorm_ge_one p hp _))) (Real.exp_pos M₂).le).trans hL₂
    have hEb:E≤B^2:=(primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
      (cubeCoordinates_radical_bound p hp b B hB0.le (hb₁ b hb) (hb₂ b hb))
    have hlocal (D:Finset ι) (hD:D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset):
        ‖∑'h:{h:ActualEisensteinCubic.O // h∉canonicalSourceCutoff p K ell b C D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
          (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
          (canonicalCubeResidual p hg b C true Ψ₁ m₁ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S)))
          (canonicalCubeResidual p hg b C false Ψ₂ m₂ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₂ (columnLog p ell S)))
          W (fun _=>1) (fun _=>1) 1 1 Ksrc (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖≤Q:=by
      have hDb:=cubeSourceDivisor_norm_bound p hp b C D B lengthScale hB0.le hL0.le hCB (hb₁ b hb) (hb₂ b hb) hCb (Finset.mem_powerset.mp hD)
      exact (hkernel p hp hinj hcop hg hc pool b (hadm b hb) C D hCB Ψ₁ Ψ₂ hΨ₁ hΨ₂
        m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I) g₁ g₂ W G₁ G₂ M₁ M₂ Ksrc K ell hG₁ hG₂ hKsrc hK hell hg₁ hg₂ hM₁ hM₂).trans
        (firstTail_scalar_bound Ksrc (primeProductNorm p D) E U₁ U₂ lengthScale B G₁ G₂ P H A
          hKsrc (primeProductNorm_pos p hp _) hE hU₁ hU₂ hL0.le hG₁ hG₂ hP hH hDb hEb hU₁b hU₂b)
    dsimp only [z,canonicalCubeDualTail]
    rw [norm_mul]
    calc
      _ ≤ ‖∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
          (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
          ∑'h:{h:ActualEisensteinCubic.O // h∉canonicalSourceCutoff p K ell b C D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
            (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
            (canonicalCubeResidual p hg b C true Ψ₁ m₁ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S)))
            (canonicalCubeResidual p hg b C false Ψ₂ m₂ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₂ (columnLog p ell S)))
            W (fun _=>1) (fun _=>1) 1 1 Ksrc (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖:=
        mul_le_of_le_one_left (norm_nonneg _) (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _)
      _ ≤ ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,Q:=by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro D hD
        rw [norm_mul]
        exact (mul_le_mul (sourceMobiusDivisor_norm_le_one p hp D) (hlocal D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul Q)
      _ = ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)*Q:=by simp
      _ ≤ _:=mul_le_mul_of_nonneg_right (cubeSourceDivisors_card p hp hinj b C B lengthScale hB0 hL0 hCB (hb₁ b hb) (hb₂ b hb) hCb) hQ
  have hcommon (b:CubeCoordinates ι) (hb:b∈bs):
      ‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤
      (128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q):=by
    have heq:(∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I)=
        ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,a b C I*z b C I:=by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro C hC hnot
      have hn:¬primeProductNorm p C≤ell*Real.exp M₁:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h.trans hL₁⟩)
      apply Finset.sum_eq_zero
      intro I hI
      rw [show z b C I=0 from canonicalCubeDualTail_support p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ _ g₁ g₂ W ell Ksrc M₁ hell hM₁ hn _,mul_zero]
    rw [heq]
    calc
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,‖a b C I*z b C I‖:=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC=>norm_sum_le _ _))
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,Γ*((128*(lengthScale*B^2))*Q):=by
        apply Finset.sum_le_sum
        intro C hC
        apply Finset.sum_le_sum
        intro I hI
        rw [norm_mul]
        exact mul_le_mul (ha b hb C (Finset.mem_filter.mp hC).1 I hI) (hblock b hb C hC I) (norm_nonneg _) hΓ
      _ = ((boundedPrimeSupports p (pool\b.support) lengthScale).card:ℝ)*(labels.card:ℝ)*Γ*((128*(lengthScale*B^2))*Q):=by simp;ring
      _ ≤ _:=by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hΓ
        exact mul_le_mul (boundedPrimeSupports_card_positive p hp hinj _ lengthScale hL0) hlabel (Nat.cast_nonneg _) (by positivity)
  change ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤_
  calc
    _ ≤ ∑b∈bs,‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖:=norm_sum_le _ _
    _ ≤ ∑b∈bs,(128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q):=Finset.sum_le_sum hcommon
    _ = (bs.card:ℝ)*((128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q)):=by simp
    _ ≤ (Cb*B^(1+ε)*B)*((128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q)):=
      mul_le_mul_of_nonneg_right hbcount (by positivity)
    _ = _:=by
      dsimp [Q,P,H]
      rw [Real.rpow_add hB0,Real.rpow_add hB0]
      norm_num
      ring

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open SecondPassIntegration (densityChildEnergy)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem globalBin_canonical_child_bound
    (pool:Finset ι) (source:Finset (GlobalSecondData ι)) (side:Bool) (j:GlobalLogIndex)
    (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (V₁ V₂:ℝ→ℂ) (C E ε K ell B F:ℝ) (A J:ℕ)
    (hC:0≤C) (hE:0≤E) (hε:0<ε) (hK:0<K) (hell:0<ell) (hB:0<B) (hF:0<F)
    (hk:∀x∈source,x.source.frequency≠0)
    (hb₁:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B)
    (hb₂:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B)
    (he:∀ray:SecondRayIndex,∀q∈globalBinTriples p source side j,
      densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J≤
        E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2):
    (∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
      globalDescentWeight C ε 0 0 K ell B F A J j ray q*
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J/
        (globalPooledColumnScale ell j*globalPooledLabelScale j)))≤
    E*C*globalRayTripleConstant*((ell*B^3)*F)*(globalBinLossScale B j)^ε/
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A := by
  let M:=globalPooledColumnScale ell j*globalPooledLabelScale j
  have hM:0<M:=mul_pos (globalPooledColumnScale_pos ell hell j)
    (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j))
  calc
    _ ≤ ∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
        globalDescentWeight C ε 0 0 K ell B F A J j ray q*(E*M):=by
      apply Finset.sum_le_sum
      intro ray hray
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (globalDescentWeight_nonneg C ε 0 0 K ell B F A J j ray q hC hK hell hB hF)
      apply (div_le_iff₀ hM).mpr
      simpa only [M,pow_two,mul_assoc] using he ray q hq
    _ = E*(∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
        globalDescentWeight C ε 0 0 K ell B F A J j ray q*M):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hray
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ E*((C*(globalBinLossScale B j)^ε/
        (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A)*
        globalRayTripleConstant*((ell*B^3)*F)):=by
      apply mul_le_mul_of_nonneg_left _ hE
      simpa only [norm_zero,add_zero,one_pow,mul_one,globalRayTripleConstant,M] using
        globalDescentWeight_mass p hp C ε 0 0 K ell B F A J hC hε hK hell hB hF side source j hk hb₁ hb₂
    _ = _:=by ring

end

theorem globalSelected_canonical_child_bound (deltaLoss:ℝ) (hδ:0<deltaLoss) (ε:ℝ) (hε:0<ε):
    ∃Cbox:ℝ,0<Cbox ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (pool:Finset ι) (source:Finset (GlobalSecondData ι)) (side:Bool)
      (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (V₁ V₂:ℝ→ℂ) (C E K ell B F M H U:ℝ) (A J:ℕ)
      (keep:GlobalLogIndex→Prop) [DecidablePred keep],
      0≤C → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U →
      (∀x∈source,x.source.frequency≠0) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
      (∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter keep,
        ∀ray:SecondRayIndex,∀q∈globalBinTriples p source side j,
        densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J≤
          E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2) →
      (∑j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter keep,
        ∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
        globalDescentWeight C ε 0 0 K ell B F A J j ray q*
        (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J/
          (globalPooledColumnScale ell j*globalPooledLabelScale j)))≤
        E*C*globalRayTripleConstant*((ell*B^3)*F)*Cbox*U^(deltaLoss+8*ε) := by
  obtain ⟨Cbox,hCbox,hbox⟩:=globalLogBox_total_loss deltaLoss hδ ε hε.le
  refine ⟨Cbox,hCbox,?_⟩
  intro ι _ p hp _ hcop hg pool source side Ψ m V₁ V₂ C E K ell B F M H U A J keep _
    hC hE hU hK hell hB hF hH hKU hellU hBU hHU heU hk hb₁ hb₂ he
  let S:=globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let Q:=E*C*globalRayTripleConstant*((ell*B^3)*F)
  have hB0:0<B:=zero_lt_one.trans_le hB
  have hF0:0<F:=zero_lt_one.trans_le hF
  have hQ:0≤Q:=by dsimp [Q,globalRayTripleConstant];positivity
  have hloss (j:GlobalLogIndex):0≤(globalBinLossScale B j)^ε:=by
    unfold globalBinLossScale
    have hx:=globalLogRep_pos j 4
    have hl:=globalPooledLabelScale_ge_one j
    positivity
  calc
    _ ≤ ∑j∈S.filter keep,Q*(globalBinLossScale B j)^ε:=by
      apply Finset.sum_le_sum
      intro j hj
      have hb:=globalBin_canonical_child_bound p hp hcop hg pool source side j Ψ m V₁ V₂ C E ε K ell B F A J
        hC hE hε hK hell hB0 hF0 hk hb₁ hb₂ (he j hj)
      apply hb.trans
      apply div_le_self (mul_nonneg hQ (hloss j))
      have hr:=globalBinRadial_pos ell (globalPooledRowScale K ell B F j) hell
        (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
      exact one_le_pow₀ (by linarith)
    _ ≤ ∑j∈S,Q*(globalBinLossScale B j)^ε:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j hj hnot=>mul_nonneg hQ (hloss j))
    _ = Q*∑j∈S,(globalBinLossScale B j)^ε:=by rw [Finset.mul_sum]
    _ ≤ Q*(Cbox*U^(deltaLoss+8*ε)):=mul_le_mul_of_nonneg_left
      (hbox K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU) hQ
    _ = _:=by dsimp [Q];ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)

theorem globalPooled_mass_le_parent (_K ell B F:ℝ) (hell:0<ell) (hB:0<B) (hF:0<F)
    (j:GlobalLogIndex) (hJ:globalLogRep j 4≤B^2) (hlarge:Real.exp 4≤B*F):
    globalPooledColumnScale ell j*globalPooledLabelScale j≤(ell*B^3)*F := by
  have hD:=globalPooledDelta_pos B F hB hF j
  have hM:0<(ell*B^3)*F:=by positivity
  rw [globalPooled_mass ell B F hB hF j]
  calc
    _ ≤ Real.exp 4*((ell*B^3)*F)*B^2/(globalPooledDelta B F j*B^2):=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = Real.exp 4*((ell*B^3)*F)/globalPooledDelta B F j:=by field_simp
    _ ≤ (ell*B^3)*F:=by
      apply (div_le_iff₀ hD).mpr
      have he:=hlarge.trans (globalPooledDelta_ge B F hB.le hF.le j)
      nlinarith

variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit hp in
theorem globalArithmeticTargets_nonzero (source:Finset (GlobalSecondData ι)) (side:Bool)
    (q:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (j:GlobalLogIndex)
    (hk:∀x∈source,x.source.frequency≠0):
    ∀z∈globalArithmeticTargets p source side q j,z.2≠0 := by
  intro z hz
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
  have hxs:x∈source:=(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  exact actualSecondRow_ne_zero p _ _ _ (hk x hxs)

include hp in

theorem globalRetained_canonical_geometry
    (source:Finset (GlobalSecondData ι)) (side:Bool) (q:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (j:GlobalLogIndex)
    (hq:q∈globalBinTriples p source side j)
    (Z η Ksrc K ell B F:ℝ) (m:ActualEisensteinCubic.O)
    (hZ:1<Z) (hη:η≤(1:ℝ)/1000) (hKsrc:0<Ksrc) (hK:0<K) (hKle:K≤Ksrc)
    (hell:0<ell) (hB:0<B) (hF:1≤F) (hprogress:Z^((1:ℝ)/1000)≤B*F)
    (hlarge:Real.exp 4≤B*F) (hstart:Ksrc≤Z^3)
    (hk:∀x∈source,x.source.frequency≠0)
    (hb₁:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B)
    (hb₂:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B)
    (hretained:globalBinRadial ell (globalPooledRowScale K ell B F j) j≤Z^η):
    let X:=globalPooledColumnScale ell j
    let lengthScale:=globalPooledLabelScale j
    let Kchild:=globalLogRep j 8*Real.exp 1
    0<X ∧ 1≤lengthScale ∧ 1≤Kchild ∧ X*lengthScale≤(ell*B^3)*F ∧
      Kchild≤Ksrc/Z^((1:ℝ)/1000) ∧ fixedDepthRank Z Kchild+1≤fixedDepthRank Z Ksrc ∧
      fixedDepthRank Z Ksrc≤3000 ∧ Kchild*‖eisEmbedding (fixedTripleMask m q)‖^2/(X*lengthScale)≤
        Z^η*(K*‖eisEmbedding m‖^2/((ell*B^3)*F)) ∧
      (∀z∈globalArithmeticTargets p source side q j,
        Squarefree z.1 ∧ z.2≠0 ∧ (Ideal.absNorm z.1:ℝ)≤lengthScale ∧ ‖eisEmbedding z.2‖^2≤Kchild) := by
  obtain ⟨x,hx,hqx⟩:=Finset.mem_image.mp hq
  obtain ⟨hxs,hj⟩:=Finset.mem_filter.mp hx
  have hF0:0<F:=zero_lt_one.trans_le hF
  have hJ:globalLogRep j 4≤B^2:=by
    simpa only [hj] using globalPooled_J_bound p hp B hB side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)
  have hD:Z^η≤globalPooledDelta B F j:=
    (Real.rpow_le_rpow_of_exponent_le hZ.le hη).trans
      (hprogress.trans (globalPooledDelta_ge B F hB.le hF0.le j))
  have hr:globalLogRep j 8*Real.exp 1≤K/globalPooledDelta B F j:=
    globalPooledRow_contraction K ell B F hK hell hB hF0 j hJ (hretained.trans hD)
  have hKchild:1≤globalLogRep j 8*Real.exp 1:=one_le_mul_of_one_le_of_one_le
    (globalLogRep_ge_one j 8) (Real.one_le_exp (by norm_num))
  have hsmall:globalLogRep j 8*Real.exp 1≤Ksrc/Z^((1:ℝ)/1000):=by
    apply hr.trans
    calc
      _ ≤ K/Z^((1:ℝ)/1000):=div_le_div_of_nonneg_left hK.le
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
        (hprogress.trans (globalPooledDelta_ge B F hB.le hF0.le j))
      _ ≤ _:=div_le_div_of_nonneg_right hKle (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hinv:=globalBin_invariant_small_padding p hp Z η K ell B F hZ hK hell hB hF side x
    (hk x hxs) m (hb₁ x hxs) (hb₂ x hxs) (by simpa only [hj] using hretained)
  simp only [hj,hqx] at hinv
  refine ⟨globalPooledColumnScale_pos ell hell j,globalPooledLabelScale_ge_one j,hKchild,
    globalPooled_mass_le_parent K ell B F hell hB hF0 j hJ hlarge,hsmall,
    fixedDepthRank_step Z Ksrc _ hZ hKsrc hKchild hsmall,
    fixedDepthRank_initial Z Ksrc hZ hKsrc hstart,hinv,?_⟩
  intro z hz
  have hb:=globalArithmeticTargets_bounds p hp source side q j hk z hz
  exact ⟨globalArithmeticTargets_squarefree p source side q j z hz,
    globalArithmeticTargets_nonzero p source side q j hk z hz,hb.2.1,hb.2.2⟩

end SecondPassArithmetic

end

end OAI

end Source188

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/ReopenedFibers.lean; sha256: 47a6cabf590d0fbff7882955afb52dae789c4164c8b2f65fc9bd5a01859d693c -/
section Source189
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open SecondPassIntegration (densityChildEnergy)
open ConcreteTraceCRT (eisEmbedding)

theorem globalChildBudget_canonical_bound (deltaLoss:ℝ) (hδ:0<deltaLoss) (ε:ℝ) (hε:0<ε):
    ∃Clo Chi:ℝ,0<Clo ∧ 0<Chi ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (pool:Finset ι) (source:Finset (GlobalSecondData ι)) (side:Bool)
      (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (windows:Fin 7→ℝ→ℂ)
      (C E K ell B F M H U Z θ A₀ Vmax:ℝ) (N J:ℕ),
      0≤C → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀u,‖Ψ u‖≤1) → (∀x∈source,x.source.frequency≠0) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
      (∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
        (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),
        ∀ray:SecondRayIndex,∀q∈globalBinTriples p source side j,
        densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J)≤
          E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2) →
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H (N+1) (2*J) side≤
        C*globalRayTripleConstant*((ell*B^3)*F)*U^(deltaLoss+8*ε)*
          (E*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N)) := by
  obtain ⟨Clo,hClo,hlow⟩:=globalSelected_canonical_child_bound deltaLoss hδ ε hε
  obtain ⟨Chi,hChi,hhigh⟩:=globalChild_large_radial_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj pool source side Ψ m windows C E K ell B F M H U Z θ A₀ Vmax N J
    hC hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hk hb₁ hb₂ he
  have hlo:=hlow p hp hcop hg pool source side Ψ m (windows 5) (windows 6) C E K ell B F M H U (N+1) (2*J)
    (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ)
    hC hE hU hK hell hB hF hH hKU hellU hBU hHU heU hk hb₁ hb₂ he
  have hhi:=hhigh p hp hcop hg hc hinj pool Ψ m (windows 5) (windows 6) C K ell B F M H U Z θ A₀ Vmax N J
    source side hC hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hk hb₁ hb₂
  let S:=globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let f:=fun j:GlobalLogIndex=>∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
      globalDescentWeight C ε 0 0 K ell B F (N+1) (2*J) j ray q*
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J)/
        (globalPooledColumnScale ell j*globalPooledLabelScale j))
  have hsplit:(∑j∈S,f j)=
      (∑j∈S.filter (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),f j)+
      (∑j∈S.filter (fun j=>Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),f j):=by
    simpa only [not_lt] using (Finset.sum_filter_add_sum_filter_not S
      (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ) f).symm
  change (∑j∈S,f j)≤_
  rw [hsplit]
  apply (add_le_add hlo hhi).trans_eq
  ring

end
section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]

def reopenedCubeFiber (v₁ v₂ : ι →₀ ℕ) : Finset (CubeCoordinates ι) :=
  (((v₁.support ∪ v₂.support).powerset).product
    ((v₁.support ∪ v₂.support).powerset)).image
    (fun A => ⟨v₁,v₂,A.2,A.1⟩)

lemma mem_reopenedCubeFiber (v₁ v₂ : ι →₀ ℕ) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFiber v₁ v₂ ↔
      b.leftExponent=v₁ ∧ b.rightExponent=v₂ ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨h₂,h₁⟩ := Finset.mem_product.mp hA
    exact ⟨rfl,rfl,Finset.mem_powerset.mp h₁,Finset.mem_powerset.mp h₂⟩
  · rintro ⟨hl,hr,hb⟩
    apply Finset.mem_image.mpr
    refine ⟨(b.rightDivisor,b.leftDivisor),?_,?_⟩
    · apply Finset.mem_product.mpr
      have hs : b.support=v₁.support∪v₂.support := by rw [CubeCoordinates.support,hl,hr]
      exact ⟨Finset.mem_powerset.mpr (hs ▸ hb.2),Finset.mem_powerset.mpr (hs ▸ hb.1)⟩
    · exact CubeCoordinates.ext hl.symm hr.symm rfl rfl

def reopenedCubeFamily (Q : Finset (ι →₀ ℕ)) : Finset (CubeCoordinates ι) :=
  (Q.product Q).biUnion (fun v => reopenedCubeFiber v.2 v.1)

lemma mem_reopenedCubeFamily (Q : Finset (ι →₀ ℕ)) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFamily Q ↔ b.leftExponent ∈ Q ∧ b.rightExponent ∈ Q ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨v,hv,hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFiber v.2 v.1 b).mp hb
    exact ⟨hl ▸ (Finset.mem_product.mp hv).2,hr ▸ (Finset.mem_product.mp hv).1,ha⟩
  · rintro ⟨hl,hr,ha⟩
    exact Finset.mem_biUnion.mpr ⟨(b.rightExponent,b.leftExponent),Finset.mem_product.mpr ⟨hr,hl⟩,
      (mem_reopenedCubeFiber _ _ b).mpr ⟨rfl,rfl,ha⟩⟩

lemma reopenedCubeFamily_admissible (Q : Finset (ι →₀ ℕ)) :
    ∀ b ∈ reopenedCubeFamily Q,b.Admissible :=
  fun b hb => ((mem_reopenedCubeFamily Q b).mp hb).2.2

lemma reopenedCubeFamily_support (pool : Finset ι) (Q : Finset (ι →₀ ℕ))
    (hQ : ∀ v ∈ Q,v.support ⊆ pool) :
    ∀ b ∈ reopenedCubeFamily Q,b.support ⊆ pool := by
  intro b hb
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  exact Finset.union_subset (hQ _ hl) (hQ _ hr)

theorem sum_reopenedCubeFamily {M : Type*} [AddCommMonoid M]
    (Q : Finset (ι →₀ ℕ)) (f : CubeCoordinates ι → M) :
    (∑ b ∈ reopenedCubeFamily Q,f b) =
      ∑ v₂ ∈ Q,∑ v₁ ∈ Q,∑ A₂ ∈ (v₁.support∪v₂.support).powerset,
        ∑ A₁ ∈ (v₁.support∪v₂.support).powerset,f ⟨v₁,v₂,A₁,A₂⟩ := by
  unfold reopenedCubeFamily
  rw [Finset.sum_biUnion]
  · change (∑ x ∈ Q ×ˢ Q,∑ i ∈ reopenedCubeFiber x.2 x.1,f i)=_
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro v₂ hv₂
    apply Finset.sum_congr rfl
    intro v₁ hv₁
    unfold reopenedCubeFiber
    rw [Finset.sum_image]
    · change (∑ x ∈ (v₁.support∪v₂.support).powerset ×ˢ (v₁.support∪v₂.support).powerset,
        f ⟨v₁,v₂,x.2,x.1⟩)=_
      rw [Finset.sum_product]
    · intro A hA B hB he
      exact Prod.ext (congrArg CubeCoordinates.rightDivisor he) (congrArg CubeCoordinates.leftDivisor he)
  · intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro b hb hc
    obtain ⟨hbl,hbr,ha⟩ := (mem_reopenedCubeFiber v.2 v.1 b).mp hb
    obtain ⟨hcl,hcr,hc⟩ := (mem_reopenedCubeFiber w.2 w.1 b).mp hc
    exact hne (Prod.ext (hbr.symm.trans hcr) (hbl.symm.trans hcl))

omit [DecidableEq ι] in
lemma primeProduct_finsupp_support (p : ι → ActualEisensteinCubic.O) (B : Finset ι) (v : ι →₀ ℕ)
    (hv : v.support ⊆ B) : primeProduct p B v=primeProduct p v.support v := by
  unfold primeProduct
  symm
  apply Finset.prod_subset hv
  intro i hi hn
  have hv0 : v i=0 := by simpa only [Finsupp.mem_support_iff,not_not] using hn
  simp only [hv0,pow_zero]

lemma reopenedCubeFamily_cube_norms (p : ι → ActualEisensteinCubic.O) (Q : Finset (ι →₀ ℕ)) (B : ℝ)
    (hQ : ∀ v ∈ Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ B) :
    ∀ b ∈ reopenedCubeFamily Q,
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2 ≤ B ∧
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2 ≤ B := by
  intro b hb
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  rw [primeProduct_finsupp_support p b.support b.leftExponent Finset.subset_union_left,
    primeProduct_finsupp_support p b.support b.rightExponent Finset.subset_union_right]
  exact ⟨hQ _ hl,hQ _ hr⟩

def reopenedPairCoefficient (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (b : CubeCoordinates ι) (_C : Finset ι) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  star (β I b.rightExponent)*β I b.leftExponent

omit [DecidableEq ι] in
lemma reopenedPairCoefficient_independent_common (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (b : CubeCoordinates ι) (C D : Finset ι) (I : Ideal ActualEisensteinCubic.O) :
    reopenedPairCoefficient β b C I=reopenedPairCoefficient β b D I := rfl

lemma reopenedPairCoefficient_bound (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hβ : ∀ I ∈ labels,∀ v ∈ Q,‖β I v‖ ≤ Γ) :
    ∀ b ∈ reopenedCubeFamily Q,∀ C,∀ I ∈ labels,
      ‖reopenedPairCoefficient β b C I‖ ≤ Γ^2 := by
  intro b hb C I hI
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  simp only [reopenedPairCoefficient,norm_mul,norm_star]
  simpa only [pow_two] using mul_le_mul (hβ I hI _ hr) (hβ I hI _ hl) (norm_nonneg _) hΓ

end
section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)

theorem reopenedCanonicalRow_smoothed_eq_source {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ : ∀ v ∈ Q,v.support ⊆ pool)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (g W : 𝓢(ℝ,ℂ)) (K ell : ℝ) (hK : 0 < K) :
    (∑ I ∈ labels,∑' z : ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/K)*
      (‖reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun S => g (columnLog p ell S)) z‖^2 : ℝ)) =
    canonicalSourceTotal p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W K ell := by
  rw [canonicalSourceTotal,sum_reopenedCubeFamily]
  simp only [reopenedPairCoefficient,CubeCoordinates.support]
  calc
    _ = ∑ I ∈ labels,∑ v₂ ∈ Q,∑ v₁ ∈ Q,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (idealGenerator I) (fun S => g (columnLog p ell S))
          (fun S => g (columnLog p ell S)) W K := by
      apply Finset.sum_congr rfl
      intro I hI
      exact reopenedCanonicalRow_smoothed_expand p hp hcop hg pool Q hQ (β I) Ψ m
        (idealGenerator I) (fun S => g (columnLog p ell S)) W K hK
    _ = ∑ v₂ ∈ Q,∑ v₁ ∈ Q,∑ I ∈ labels,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (idealGenerator I) (fun S => g (columnLog p ell S))
          (fun S => g (columnLog p ell S)) W K := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      apply Finset.sum_congr rfl
      intro v₁ hv₁
      have hs : v₁.support∪v₂.support ⊆ pool := Finset.union_subset (hQ v₁ hv₁) (hQ v₂ hv₂)
      simp_rw [canonicalCubeCorrelation_eq_blocks p hp hcop hg hinj hpr pool v₁ v₂ hs,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₂ hA₂
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₁ hA₁
      rw [Finset.sum_comm]

end
section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]

theorem reopenedCubeFamily_card (Q : Finset (ι →₀ ℕ)) :
    (reopenedCubeFamily Q).card =
      ∑ v₂ ∈ Q,∑ v₁ ∈ Q,(2^((v₁.support∪v₂.support).card))^2 := by
  have h := sum_reopenedCubeFamily Q (fun _ => (1 : ℕ))
  simpa [pow_two] using h

theorem reopenedCubeFamily_card_le (pool : Finset ι) (Q : Finset (ι →₀ ℕ))
    (hQ : ∀ v ∈ Q,v.support ⊆ pool) :
    (reopenedCubeFamily Q).card ≤ Q.card^2*(2^pool.card)^2 := by
  rw [reopenedCubeFamily_card]
  calc
    _ ≤ ∑ v₂ ∈ Q,∑ v₁ ∈ Q,(2^pool.card)^2 := by
      apply Finset.sum_le_sum
      intro v₂ hv₂
      apply Finset.sum_le_sum
      intro v₁ hv₁
      have hc := Finset.card_le_card (Finset.union_subset (hQ v₁ hv₁) (hQ v₂ hv₂))
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hc) 2
    _ = _ := by simp [pow_two,mul_assoc]

theorem reopenedSourceBlocks_bounds (p : ι → ActualEisensteinCubic.O) (pool : Finset ι) (Q : Finset (ι →₀ ℕ))
    (B : ℝ) (hQ : ∀ v ∈ Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ B) :
    ∀ q ∈ canonicalSourceBlocks pool (reopenedCubeFamily Q),GlobalCubeAdmissible q ∧
      ‖eisEmbedding (primeProduct p q.cube.support q.cube.leftExponent)‖^2 ≤ B ∧
      ‖eisEmbedding (primeProduct p q.cube.support q.cube.rightExponent)‖^2 ≤ B := by
  intro q hq
  exact ⟨canonicalSourceBlocks_admissible pool _ (reopenedCubeFamily_admissible Q) q hq,
    canonicalSourceBlocks_cube_norms p pool _ B
      (fun b hb => (reopenedCubeFamily_cube_norms p Q B hQ b hb).1)
      (fun b hb => (reopenedCubeFamily_cube_norms p Q B hQ b hb).2) q hq⟩

end

theorem reopenedCubeFamily_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → ActualEisensteinCubic.O) (_hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (Q : Finset (ι →₀ ℕ)) (B : ℝ),1 ≤ B →
      (∀ v ∈ Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ B) →
      ((reopenedCubeFamily Q).card : ℝ) ≤ C*B^(2+ε) := by
  obtain ⟨C,hC,hcount⟩ := cube_coordinates_parity_count ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Q B hB hQ
  have hBp := zero_lt_one.trans_le hB
  have hb := reopenedCubeFamily_cube_norms p Q B hQ
  have hactive (b : CubeCoordinates ι) (hbf : b ∈ reopenedCubeFamily Q) :
      ‖eisEmbedding (∏ i ∈ cubeActiveSupport b.support
        (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖ ≤ B := by
    have hn : primeProductNorm p (cubeActiveSupport b.support
        (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) ≤ B^2 :=
      (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
        (cubeCoordinates_radical_bound p hp b B hBp.le (hb b hbf).1 (hb b hbf).2)
    change ‖eisEmbedding (∏ i ∈ cubeActiveSupport b.support
      (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖^2 ≤ B^2 at hn
    nlinarith [norm_nonneg (eisEmbedding (∏ i ∈ cubeActiveSupport b.support
      (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i))]
  have h := hcount p hp hinj (reopenedCubeFamily Q) B B hB hBp.le
    (reopenedCubeFamily_admissible Q) (fun b hb' => (hb b hb').1)
    (fun b hb' => (hb b hb').2) hactive
  apply h.trans_eq
  calc
    C*B^(1+ε)*B = C*(B^(1+ε)*B^(1 : ℝ)) := by rw [Real.rpow_one]; ring
    _ = C*B^((1+ε)+1) := by rw [Real.rpow_add hBp (1+ε) (1 : ℝ)]
    _ = C*B^(2+ε) := by congr 2; ring

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)

theorem reopenedCanonicalRow_smoothed_split {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ : ∀ v ∈ Q,v.support ⊆ pool)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (g W : 𝓢(ℝ,ℂ)) (Ksrc K ell : ℝ)
    (hKsrc : 0 < Ksrc) (hK : 0 ≤ K) :
    (∑ I ∈ labels,∑' z : ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/Ksrc)*
      (‖reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun S => g (columnLog p ell S)) z‖^2 : ℝ)) =
    canonicalSourceZero p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc ell+
    canonicalSourceFinite p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc K ell+
    canonicalSourceTail p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc K ell := by
  rw [reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m g W Ksrc ell hKsrc]
  exact canonicalSourceTotal_split p hp hcop hg hinj hc pool (reopenedCubeFamily Q) labels
    (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc K ell hKsrc hK

theorem reopenedCanonicalBlockCoefficient_bound {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hβ : ∀ I ∈ labels,∀ v ∈ Q,‖β I v‖ ≤ Γ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀ u,‖Ψ u‖ ≤ 1) (m : ActualEisensteinCubic.O) (K ell : ℝ)
    (b : GlobalCubeBlock ι) (hb : b ∈ canonicalSourceBlocks pool (reopenedCubeFamily Q))
    (x : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) (hx : x ∈ canonicalBlockFrequencies p K ell labels b) :
    ‖canonicalBlockCoefficient p hp hcop hg (reopenedPairCoefficient β) Ψ Ψ m m b x‖ ≤ Γ^2 := by
  exact canonicalBlockCoefficient_bound p hp hcop hg hc pool (reopenedCubeFamily Q) labels
    (reopenedPairCoefficient β) Ψ Ψ m m (Γ^2) K ell (sq_nonneg _) hΨ hΨ
    (fun b hb C hC I hI => reopenedPairCoefficient_bound Q labels β Γ hΓ hβ b hb C I hI) b hb x hx

end SecondPassArithmetic

namespace CubicEisenstein
open MeasureTheory
open scoped SchwartzMap

lemma euclideanIntegral_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (g : EuclideanSpatial→ℝ) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     ∫p,g p) =
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     ∫p,g p) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanIntegrable_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (g : EuclideanSpatial→ℝ) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     Integrable g volume) ↔
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Integrable g volume) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanNativeIntegral_eq_borel (g : EuclideanSpatial→ℝ) :
    (∫p,g p)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     ∫p,g p) :=
  euclideanIntegral_borel_transport inferInstance inferInstance g

lemma euclideanNativeIntegrable_iff_borel (g : EuclideanSpatial→ℝ) :
    Integrable g volume ↔
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Integrable g volume) :=
  euclideanIntegrable_borel_transport inferInstance inferInstance g

def euclideanLp_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) ≃ₗᵢ[ℂ]
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) := by
  have he := hm.measurable_eq
  subst m
  exact LinearIsometryEquiv.refl ℂ _

def euclideanNativeLpBorelEquiv : EuclideanL2 ≃ₗᵢ[ℂ]
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) :=
  euclideanLp_borel_transport inferInstance inferInstance

lemma euclideanLp_borel_transport_schwartz (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (f : 𝓢(EuclideanSpatial,ℂ)) :
    euclideanLp_borel_transport m hm
      (letI : MeasurableSpace EuclideanSpatial := m
       letI : BorelSpace EuclideanSpatial := hm
       f.toLp 2 volume)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     f.toLp 2 volume) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanNativeLpBorelEquiv_schwartz (f : 𝓢(EuclideanSpatial,ℂ)) :
    euclideanNativeLpBorelEquiv (f.toLp 2 volume)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     f.toLp 2 volume) :=
  euclideanLp_borel_transport_schwartz inferInstance inferInstance f

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap

namespace CubicEisenstein
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

lemma euclideanOriginalMeasurable_eq_borel :
    (inferInstance : MeasurableSpace EuclideanSpatial)=borel EuclideanSpatial :=
  BorelSpace.measurable_eq

local instance : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
local instance : BorelSpace EuclideanSpatial := ⟨rfl⟩

def kernelLocalizedRealTest (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) : C1c (E := EuclideanSpatial) :=
  ⟨fun p => projection (kernelLocalizedField χ f p),
    (projection.contDiff.comp (kernelLocalizedField_smooth χ f)).of_le (by simp),
    (kernelLocalizedField_compact χ f).comp_left (map_zero projection)⟩

lemma sourceC1c_toL2_norm_sq (g : C1c (E := EuclideanSpatial)) :
    ‖toL2 («μ» := volume) g‖^2=∫p,‖g.1 p‖^2 := by
  calc
    ‖toL2 («μ» := volume) g‖^2=inner ℝ (toL2 («μ» := volume) g) (toL2 («μ» := volume) g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫p,inner ℝ (toL2 («μ» := volume) g p) (toL2 («μ» := volume) g p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_of_mem_C1c («μ» := volume) g.2).coeFn_toLp] with p hp
      change inner ℝ (((memLp_of_mem_C1c («μ» := volume) g.2).toLp g.1) p)
        (((memLp_of_mem_C1c («μ» := volume) g.2).toLp g.1) p)=_
      rw [hp,real_inner_self_eq_norm_sq]

lemma sourceC1c_toL2Grad_norm_sq (g : C1c (E := EuclideanSpatial)) :
    ‖toL2Grad («μ» := volume) g‖^2=∫p,‖grad g.1 p‖^2 := by
  calc
    ‖toL2Grad («μ» := volume) g‖^2=inner ℝ (toL2Grad («μ» := volume) g) (toL2Grad («μ» := volume) g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫p,inner ℝ (toL2Grad («μ» := volume) g p) (toL2Grad («μ» := volume) g p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_grad_of_mem_C1c («μ» := volume) g.2).coeFn_toLp] with p hp
      change inner ℝ (((memLp_grad_of_mem_C1c («μ» := volume) g.2).toLp (grad g.1)) p)
        (((memLp_grad_of_mem_C1c («μ» := volume) g.2).toLp (grad g.1)) p)=_
      rw [hp,real_inner_self_eq_norm_sq]

lemma kernelLocalizedRealTest_grad_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖) (p : EuclideanSpatial) :
    ‖grad (kernelLocalizedRealTest χ f projection).1 p‖^2≤
      ∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2 := by
  have hdiff : DifferentiableAt ℝ (kernelLocalizedField χ f) p :=
    ((kernelLocalizedField_smooth χ f).differentiable (by simp)).differentiableAt
  have hd := (projection.hasFDerivAt.comp p hdiff.hasFDerivAt).fderiv
  change fderiv ℝ (kernelLocalizedRealTest χ f projection).1 p=_ at hd
  unfold grad
  rw [LinearIsometryEquiv.norm_map,hd,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual]
  apply Finset.sum_le_sum
  intro j hj
  have hh := hprojection (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j))
  change (projection (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)))^2≤_
  simp only [Real.norm_eq_abs] at hh
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2

lemma kernelLocalizedRealTest_energy_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖) :
    ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2+
      ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2≤
        ‖kernelLocalizedH1 χ f‖^2 := by
  let g := kernelLocalizedRealTest χ f projection
  rw [sourceC1c_toL2_norm_sq,sourceC1c_toL2Grad_norm_sq,kernelLocalizedH1_norm_sq,
    ←integral_add (memLp_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq
      (memLp_grad_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq]
  rw [euclideanNativeIntegral_eq_borel]
  have hden := (euclideanNativeIntegrable_iff_borel (kernelLocalizedDensity χ f)).mp
    (kernelLocalizedDensity_integrable χ f)
  apply integral_mono
    ((memLp_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq.add
      (memLp_grad_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq)
    hden
  intro p
  have hm := hprojection (kernelLocalizedField χ f p)
  have hg := kernelLocalizedRealTest_grad_le χ f projection hprojection p
  change ‖projection (kernelLocalizedField χ f p)‖^2+_≤_
  unfold kernelLocalizedDensity
  nlinarith [norm_nonneg (projection (kernelLocalizedField χ f p)),norm_nonneg (kernelLocalizedField χ f p)]

lemma kernelLocalizedRealTest_support (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) :
    Function.support (kernelLocalizedRealTest χ f projection).1⊆tsupport χ.func := by
  intro p hp
  apply kernelLocalizedField_tsupport χ f
  apply subset_tsupport
  intro hz
  apply hp
  change projection (kernelLocalizedField χ f p)=0
  rw [hz,map_zero]

theorem kernelLocalizedReal_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖)
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)) '' family)) := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedH1_bounded χ hinj
  have hCB : 0≤C*B := mul_nonneg hC hB
  have henergy : ∀f∈family,
      ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2+
        ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2≤C*B := by
    intro f hf
    exact (kernelLocalizedRealTest_energy_le χ f projection hprojection).trans
      ((hbound f).trans (mul_le_mul_of_nonneg_left (hfamily f hf) hC))
  have hh := euclidean_C1c_family_precompact (tsupport χ.func) χ.compact
    ((fun f => kernelLocalizedRealTest χ f projection) '' family) (Real.sqrt (C*B))
    (by
      rintro _ ⟨f,hf,rfl⟩
      exact kernelLocalizedRealTest_support χ f projection)
    (by
      rintro _ ⟨f,hf,rfl⟩
      have he := henergy f hf
      have hs := Real.sq_sqrt hCB
      have hn := Real.sqrt_nonneg (C*B)
      nlinarith [sq_nonneg ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖,
        norm_nonneg (toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection))])
    (by
      rintro _ ⟨f,hf,rfl⟩
      have he := henergy f hf
      have hs := Real.sq_sqrt hCB
      have hn := Real.sqrt_nonneg (C*B)
      nlinarith [sq_nonneg ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖,
        norm_nonneg (toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection))])
  simpa only [Set.image_image,Function.comp_def] using hh

abbrev RellichRealL2 := Lp ℝ 2 (volume : Measure EuclideanSpatial)
abbrev RellichComplexL2 := Lp ℂ 2 (volume : Measure EuclideanSpatial)

def kernelComplexL2Assemble : (RellichRealL2 × RellichRealL2) →L[ℝ] RellichComplexL2 :=
  (Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial)).comp
    (ContinuousLinearMap.fst ℝ RellichRealL2 RellichRealL2)+
  (Complex.I • Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial)).comp
    (ContinuousLinearMap.snd ℝ RellichRealL2 RellichRealL2)

lemma kernelComplexL2Assemble_localized (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    kernelComplexL2Assemble
      (toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM),
        toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM))=
      (kernelLocalizedSchwartz χ f).toLp 2 volume := by
  let r := toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM)
  let i := toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM)
  let R := Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial) r
  let I := Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial) i
  have hr : (r : EuclideanSpatial→ℝ)=ᵐ[volume]fun p => (kernelLocalizedField χ f p).re :=
    (memLp_of_mem_C1c («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM).2).coeFn_toLp
  have hi : (i : EuclideanSpatial→ℝ)=ᵐ[volume]fun p => (kernelLocalizedField χ f p).im :=
    (memLp_of_mem_C1c («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM).2).coeFn_toLp
  change R+Complex.I•I=(kernelLocalizedSchwartz χ f).toLp 2 volume
  apply Lp.ext
  filter_upwards [hr,hi,Complex.ofRealCLM.coeFn_compLpL r,Complex.ofRealCLM.coeFn_compLpL i,
    Lp.coeFn_add R (Complex.I•I),Lp.coeFn_smul Complex.I I,
    (kernelLocalizedSchwartz χ f).coeFn_toLp 2 volume] with p hrp hip hR hI ha hs hf
  rw [ha,Pi.add_apply,hs,Pi.smul_apply,hR,hI,hrp,hip,hf]
  change ((kernelLocalizedField χ f p).re:ℂ)+Complex.I*((kernelLocalizedField χ f p).im:ℂ)=kernelLocalizedField χ f p
  simpa only [mul_comm] using Complex.re_add_im (kernelLocalizedField χ f p)

theorem kernelLocalizedComplex_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => (kernelLocalizedSchwartz χ f).toLp 2 volume) '' family)) := by
  have hr := kernelLocalizedReal_family_precompact χ hinj Complex.reCLM
    (fun z => by change ‖z.re‖≤‖z‖; simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm z) family B hB hfamily
  have hi := kernelLocalizedReal_family_precompact χ hinj Complex.imCLM
    (fun z => by change ‖z.im‖≤‖z‖; simpa only [Real.norm_eq_abs] using Complex.abs_im_le_norm z) family B hB hfamily
  have hc := (hr.prod hi).image kernelComplexL2Assemble.continuous
  apply hc.closure_of_subset
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨(toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM),
    toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM)),?_,?_⟩
  · exact ⟨subset_closure ⟨f,hf,rfl⟩,subset_closure ⟨f,hf,rfl⟩⟩
  · exact kernelComplexL2Assemble_localized χ f

theorem kernelLocalizedNative_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => kernelL2Localize χ (kernelSmoothTestsToL2 f)) '' family)) := by
  have hc := kernelLocalizedComplex_family_precompact χ hinj family B hB hfamily
  apply (hc.image euclideanNativeLpBorelEquiv.symm.continuous).closure_of_subset
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨(kernelLocalizedSchwartz χ f).toLp 2 volume,subset_closure ⟨f,hf,rfl⟩,?_⟩
  apply euclideanNativeLpBorelEquiv.injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  rw [kernelL2Localize_core χ hinj]
  exact (euclideanNativeLpBorelEquiv_schwartz _).symm

def kernelEnergyLocalizeL2 (χ : PositiveChartCutoff) : KernelEnergyGraph →L[ℂ] EuclideanL2 :=
  (kernelL2Localize χ).comp kernelEnergyMass

theorem kernelEnergyLocalizeL2_isCompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    IsCompactOperator (kernelEnergyLocalizeL2 χ) := by
  let family : Set kernelSmoothTests := {f | ‖kernelEnergyGraphCore f‖≤2}
  let C := closure ((fun f => kernelL2Localize χ (kernelSmoothTestsToL2 f)) '' family)
  have hc : IsCompact C := kernelLocalizedNative_family_precompact χ hinj family 4 (by norm_num) (by
    intro f hf
    rw [←kernelEnergyGraphCore_norm_sq]
    change ‖kernelEnergyGraphCore f‖≤2 at hf
    nlinarith [norm_nonneg (kernelEnergyGraphCore f)])
  let T := kernelEnergyLocalizeL2 χ
  have hclosed : IsClosed (T ⁻¹' C) := hc.isClosed.preimage T.continuous
  have hsub : closure (kernelEnergyGraphCore ''
      (kernelEnergyGraphCore ⁻¹' Metric.ball (0 : KernelEnergyGraph) 2))⊆T ⁻¹' C := by
    apply hclosed.closure_subset_iff.mpr
    rintro _ ⟨f,hf,rfl⟩
    change kernelL2Localize χ (kernelEnergyMass (kernelEnergyGraphCore f))∈C
    rw [kernelEnergyMass_core]
    apply subset_closure
    refine ⟨f,?_,rfl⟩
    change ‖kernelEnergyGraphCore f‖≤2
    exact le_of_lt (by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hf)
  have hball : Metric.ball (0 : KernelEnergyGraph) 2⊆T ⁻¹' C := by
    intro u hu
    exact hsub (kernelEnergyGraphCore_dense.subset_closure_image_preimage_of_isOpen
      Metric.isOpen_ball hu)
  refine ⟨C,hc,?_⟩
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : KernelEnergyGraph) (by norm_num : (0 : ℝ)<2)) hball

end CubicEisenstein

end

end OAI

end Source189

/- Original source: OAI/NumberTheory/DirichletL/Eisenstein/CompactEnergyFamilies.lean; sha256: 895150367a2a113d4e16b072eddc9ef1ce7f3cf861fb891641101fdd9c6c6893 -/
section Source190
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

section

lemma compact_of_norm_le_compact {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : E→L[ℂ]F) (g : E→L[ℂ]G) (hg : IsCompactOperator g)
    (hbound : ∃C : ℝ,∀x,‖f x‖≤C*‖g x‖) : IsCompactOperator f := by
  let S := (LinearMap.range g.toLinearMap).topologicalClosure
  have hS : IsClosed (S : Set G) := (LinearMap.range g.toLinearMap).isClosed_topologicalClosure
  have hmem : ∀x,g x∈S := fun x => (LinearMap.range g.toLinearMap).le_topologicalClosure ⟨x,rfl⟩
  let e : E→L[ℂ]S := g.codRestrict S hmem
  have he : DenseRange e := by
    rw [DenseRange,Subtype.dense_iff,←Set.range_comp]
    change closure (Set.range g)⊆closure (Set.range g)
    exact Set.Subset.rfl
  have hec : IsCompactOperator e := hg.codRestrict hmem hS
  let q : S→L[ℂ]F := f.toLinearMap.extendOfNorm e.toLinearMap
  have hfq : f=q.comp e := by
    ext x
    exact (LinearMap.extendOfNorm_eq he hbound x).symm
  rw [hfq]
  exact hec.clm_comp q

lemma compact_finite_pi {E G ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (T : ι→E→L[ℂ]G) (hT : ∀i,IsCompactOperator (T i)) :
    IsCompactOperator (ContinuousLinearMap.pi T) := by
  let K : ι→Set G := fun i => closure ((T i) '' Metric.ball (0 : E) 1)
  have hK : ∀i,IsCompact (K i) := fun i => (hT i).isCompact_closure_image_ball 1
  refine ⟨Set.pi Set.univ K,isCompact_univ_pi hK,?_⟩
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ)<1))
  intro x hx
  exact fun i hi => subset_closure ⟨x,hx,rfl⟩

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap

def kernelChartCore (χ : PositiveChartCutoff) : Set EuclideanSpatial :=
  {p | (1/2 : ℝ)<χ.func p}

def kernelChartCoreImage (χ : PositiveChartCutoff) : Set KernelQuotient :=
  kernelEuclideanProjection '' kernelChartCore χ

lemma kernelChartCore_open (χ : PositiveChartCutoff) : IsOpen (kernelChartCore χ) :=
  isOpen_lt continuous_const χ.smooth.continuous

lemma kernelChartCore_subset (χ : PositiveChartCutoff) : kernelChartCore χ⊆tsupport χ.func := by
  intro p hp
  apply subset_tsupport
  change χ.func p≠0
  have hh : (1/2 : ℝ)<χ.func p := hp
  linarith

lemma kernelChartCoreImage_open (χ : PositiveChartCutoff) : IsOpen (kernelChartCoreImage χ) := by
  have hp : kernelChartCore χ⊆euclideanUpperHalf := (kernelChartCore_subset χ).trans χ.positive
  have he : kernelChartCoreImage χ=integralOrbitProjection globalKubotaKernel ''
      (hyperbolicEuclideanCoordinates ⁻¹' kernelChartCore χ) := by
    rw [←euclideanToHyperbolic_image_positive _ hp,Set.image_image]
    rfl
  rw [he]
  exact (integralOrbitProjection_openQuotient globalKubotaKernel
    globalKubotaKernel_le_levelThree).isOpenMap _
      ((kernelChartCore_open χ).preimage hyperbolicEuclideanCoordinates_continuous)

abbrev KernelGoodCutoff := {χ : PositiveChartCutoff //
  Set.InjOn kernelEuclideanProjection (tsupport χ.func)}

lemma kernelChartCoreImage_cover : (Set.univ : Set KernelQuotient)⊆
    ⋃χ : KernelGoodCutoff,kernelChartCoreImage χ.1 := by
  intro q hq
  obtain ⟨w,rfl⟩ := Quotient.mk_surjective q
  obtain ⟨χ,hχ,hrange,hinj⟩ := kernelChartCutoff_exists
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
  refine Set.mem_iUnion.mpr ⟨⟨χ,hinj⟩,hyperbolicEuclideanCoordinates w,?_,?_⟩
  · change (1/2 : ℝ)<χ.func (hyperbolicEuclideanCoordinates w)
    rw [hχ]
    norm_num
  · simp only [kernelEuclideanProjection,Function.comp_apply,euclideanToHyperbolic_coordinates]
    rfl

lemma kernelCompact_finite_chart_cover (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃t : Finset KernelGoodCutoff,K⊆⋃χ∈t,kernelChartCoreImage χ.1 := by
  exact hK.elim_finite_subcover (fun χ : KernelGoodCutoff => kernelChartCoreImage χ.1)
    (fun χ => kernelChartCoreImage_open χ.1)
    (Set.subset_univ K |>.trans kernelChartCoreImage_cover)

lemma kernelChartCore_mass_estimate (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (H : ℝ) (hH : 0≤H) (hdensity : ∀p∈tsupport χ.func,((p 2)^3)⁻¹≤H)
    (f : kernelSmoothTests) :
    (∫q in kernelChartCoreImage χ,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
      4*H*‖kernelL2Localize χ (kernelSmoothTestsToL2 f)‖^2 := by
  let S := kernelChartCore χ
  have hS : MeasurableSet S := (kernelChartCore_open χ).measurableSet
  have hpos : S⊆euclideanUpperHalf := (kernelChartCore_subset χ).trans χ.positive
  have hi : Set.InjOn kernelEuclideanProjection S := hinj.mono (kernelChartCore_subset χ)
  have hm := hyperbolicVolume_le_densityBound S hS hpos H
    (fun p hp => hdensity p (kernelChartCore_subset χ hp))
  have hloc : Integrable (fun p => ‖kernelLocalizedField χ f p‖^2) volume := by
    exact ((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq
  have hlocHyp : IntegrableOn (fun p => ‖kernelLocalizedField χ f p‖^2) S hyperbolicEuclideanVolume :=
    (hloc.integrableOn.smul_measure (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top).mono_measure hm
  have hmass : IntegrableOn (fun p => ‖kernelTestField f p‖^2) S hyperbolicEuclideanVolume :=
    (kernelEuclideanProjection_measurePreserving_on S hS hpos hi).integrable_comp_of_integrable
      (kernelSmoothTests_memLp f).norm.integrable_sq.integrableOn
  rw [kernelL2Localize_core χ hinj,schwartz_toL2_norm_sq]
  have hEq := kernelEuclideanProjection_integral S hS hpos hi
    (fun q => ‖f.1 q‖^2) (kernelSmoothTests_memLp f).norm.integrable_sq.aestronglyMeasurable
  change (∫p in S,‖kernelTestField f p‖^2∂hyperbolicEuclideanVolume)=_ at hEq
  change (∫q in kernelEuclideanProjection '' S,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
    4*H*(∫p,‖kernelLocalizedField χ f p‖^2)
  rw [←hEq]
  calc
    _ ≤ ∫p in S,4*‖kernelLocalizedField χ f p‖^2∂hyperbolicEuclideanVolume := by
      apply setIntegral_mono_on hmass (hlocHyp.const_mul 4) hS
      intro p hp
      have hc : (1/2 : ℝ)<χ.func p := hp
      rw [kernelLocalizedField,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
      have hn := sq_nonneg ‖kernelTestField f p‖
      have hx : 1≤4*(χ.func p)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hx hn]
    _ = 4*(∫p in S,‖kernelLocalizedField χ f p‖^2∂hyperbolicEuclideanVolume) := integral_const_mul _ _
    _ ≤ 4*(H*(∫p in S,‖kernelLocalizedField χ f p‖^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hh := integral_mono_measure hm
        (Eventually.of_forall (fun p => sq_nonneg ‖kernelLocalizedField χ f p‖))
        (hloc.integrableOn.smul_measure (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top)
      simpa only [integral_smul_measure,ENNReal.toReal_ofReal hH,smul_eq_mul] using hh
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact setIntegral_le_integral hloc (Eventually.of_forall (fun p => sq_nonneg ‖kernelLocalizedField χ f p‖))

lemma kernelChartCore_mass_bound (χ : KernelGoodCutoff) : ∃C : ℝ,0≤C ∧
    ∀f : kernelSmoothTests,
      (∫q in kernelChartCoreImage χ.1,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
        C*‖kernelL2Localize χ.1 (kernelSmoothTestsToL2 f)‖^2 := by
  have hrho : ContinuousOn (fun p : EuclideanSpatial => ((p 2)^3)⁻¹) (tsupport χ.1.func) :=
    (by fun_prop : Continuous (fun p : EuclideanSpatial => (p 2)^3)).continuousOn.inv₀
      (fun p hp => pow_ne_zero _ (ne_of_gt (χ.1.positive hp)))
  obtain ⟨r,hr⟩ := χ.1.compact.bddAbove_image hrho
  refine ⟨4*max 0 r,by positivity,fun f => ?_⟩
  exact kernelChartCore_mass_estimate χ.1 χ.2 (max 0 r) (le_max_left _ _)
    (fun p hp => (hr ⟨p,hp,rfl⟩).trans (le_max_right _ _)) f

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

def kernelMassRestriction (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) : KernelQuotientL2 :=
  ((Lp.memLp f).indicator hK).toLp (K.indicator f)

lemma kernelMassRestriction_coe (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) :
    (kernelMassRestriction K hK f : KernelQuotient→ℂ)=ᵐ[integralQuotientVolume globalKubotaKernel]
      K.indicator f := ((Lp.memLp f).indicator hK).coeFn_toLp

def kernelMassRestrictionLinear (K : Set KernelQuotient) (hK : MeasurableSet K) :
    KernelQuotientL2→ₗ[ℂ]KernelQuotientL2 where
  toFun := kernelMassRestriction K hK
  map_add' f g := by
    apply Lp.ext
    filter_upwards [kernelMassRestriction_coe K hK (f+g),kernelMassRestriction_coe K hK f,
      kernelMassRestriction_coe K hK g,Lp.coeFn_add f g,
      Lp.coeFn_add (kernelMassRestriction K hK f) (kernelMassRestriction K hK g)] with q hfg hf hg ha hb
    rw [hfg,hb,Pi.add_apply,hf,hg]
    by_cases hq : q∈K
    · simp only [Set.indicator_of_mem hq,ha,Pi.add_apply]
    · simp only [Set.indicator_of_notMem hq,add_zero]
  map_smul' c f := by
    change kernelMassRestriction K hK (c•f)=c•kernelMassRestriction K hK f
    apply Lp.ext
    filter_upwards [kernelMassRestriction_coe K hK (c•f),kernelMassRestriction_coe K hK f,
      Lp.coeFn_smul c f,Lp.coeFn_smul c (kernelMassRestriction K hK f)] with q hcf hf ha hb
    rw [hcf,hb,Pi.smul_apply,hf]
    by_cases hq : q∈K
    · simp only [Set.indicator_of_mem hq,ha,Pi.smul_apply]
    · simp only [Set.indicator_of_notMem hq,smul_zero]

lemma kernelMassRestriction_norm_le (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) : ‖kernelMassRestriction K hK f‖≤‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [kernelMassRestriction_coe K hK f] with q hq
  rw [hq]
  by_cases hm : q∈K
  · simp only [Set.indicator_of_mem hm,le_refl]
  · simp only [Set.indicator_of_notMem hm,norm_zero,norm_nonneg]

def kernelMassRestrictionCLM (K : Set KernelQuotient) (hK : MeasurableSet K) :
    KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  (kernelMassRestrictionLinear K hK).mkContinuous 1 (by
    intro f
    change ‖kernelMassRestriction K hK f‖≤1*‖f‖
    simpa only [one_mul] using kernelMassRestriction_norm_le K hK f)

lemma kernelMassRestriction_norm_sq (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : KernelQuotientL2) :
    ‖kernelMassRestrictionCLM K hK f‖^2=
      ∫q in K,‖f q‖^2∂integralQuotientVolume globalKubotaKernel := by
  rw [←integral_indicator hK]
  calc
    _ = inner ℝ (kernelMassRestriction K hK f) (kernelMassRestriction K hK f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫q,inner ℝ (kernelMassRestriction K hK f q) (kernelMassRestriction K hK f q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [kernelMassRestriction_coe K hK f] with q hq
      rw [hq,real_inner_self_eq_norm_sq]
      by_cases hqK : q∈K
      · simp only [Set.indicator_of_mem hqK]
      · simp only [Set.indicator_of_notMem hqK,norm_zero,zero_pow (by decide : 2≠0)]

lemma kernelMassRestriction_smooth_norm_sq (K : Set KernelQuotient) (hK : MeasurableSet K)
    (f : kernelSmoothTests) :
    ‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2=
      ∫q in K,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel := by
  rw [kernelMassRestriction_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (kernelSmoothTests_memLp f).coeFn_toLp] with q hq
  change ‖((kernelSmoothTests_memLp f).toLp f.1) q‖^2=‖f.1 q‖^2
  rw [hq]

def kernelEnergyMassRestriction (K : Set KernelQuotient) (hK : MeasurableSet K) :
    KernelEnergyGraph→L[ℂ]KernelQuotientL2 :=
  (kernelMassRestrictionCLM K hK).comp kernelEnergyMass

lemma integral_le_finite_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) (K : Set X) (hK : MeasurableSet K) (U : ι→Set X)
    (hU : ∀i,MeasurableSet (U i)) (hcover : K⊆⋃i,U i)
    (g : X→ℝ) (hg : Integrable g ν) (hn : ∀x,0≤g x) :
    (∫x in K,g x∂ν)≤∑i,∫x in U i,g x∂ν := by
  have hi : ∀i,Integrable ((U i).indicator g) ν := fun i => hg.indicator (hU i)
  calc
    _ = ∫x,K.indicator g x∂ν := (integral_indicator hK).symm
    _ ≤ ∫x,∑i,(U i).indicator g x∂ν := by
      apply integral_mono (hg.indicator hK) (integrable_finsetSum _ (fun i himem => hi i))
      intro x
      have hnon : ∀i,0≤(U i).indicator g x := fun i => Set.indicator_nonneg (fun y hy => hn y) x
      by_cases hx : x∈K
      · rw [Set.indicator_of_mem hx]
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover hx)
        calc
          g x=(U i).indicator g x := (Set.indicator_of_mem hi g).symm
          _ ≤ ∑j,(U j).indicator g x := Finset.single_le_sum (fun j hj => hnon j) (Finset.mem_univ i)
      · rw [Set.indicator_of_notMem hx]
        exact Finset.sum_nonneg (fun i hi => hnon i)
    _ = _ := by
      rw [integral_finsetSum _ (fun i himem => hi i)]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_indicator (hU i)

def kernelEnergyChartFamily (t : Finset KernelGoodCutoff) :
    KernelEnergyGraph→L[ℂ](t→EuclideanL2) :=
  ContinuousLinearMap.pi (fun χ : t => kernelEnergyLocalizeL2 χ.1.1)

lemma kernelEnergyChartFamily_isCompact (t : Finset KernelGoodCutoff) :
    IsCompactOperator (kernelEnergyChartFamily t) :=
  compact_finite_pi _ (fun χ => kernelEnergyLocalizeL2_isCompact χ.1.1 χ.1.2)

lemma finite_sum_weighted_norm_sq_le {G ι : Type*} [Fintype ι]
    [NormedAddCommGroup G] (C : ι→ℝ) (hC : ∀i,0≤C i) (x : ι→G) :
    (∑i,C i*‖x i‖^2)≤(∑i,C i)*‖x‖^2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) 2) (hC i)

lemma kernelEnergyChartFamily_core_apply (t : Finset KernelGoodCutoff)
    (f : kernelSmoothTests) (χ : t) :
    kernelEnergyChartFamily t (kernelEnergyGraphCore f) χ=
      kernelL2Localize χ.1.1 (kernelSmoothTestsToL2 f) := by
  change kernelL2Localize χ.1.1 (kernelEnergyMass (kernelEnergyGraphCore f))=_
  rw [kernelEnergyMass_core]

lemma kernelCompact_mass_bound (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃t : Finset KernelGoodCutoff,∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      (∫q in K,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
        C*‖kernelEnergyChartFamily t (kernelEnergyGraphCore f)‖^2 := by
  obtain ⟨t,ht⟩ := kernelCompact_finite_chart_cover K hK
  have hcov : K⊆⋃χ : t,kernelChartCoreImage χ.1.1 := by
    intro q hq
    obtain ⟨χ,hχ,hqχ⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact Set.mem_iUnion.mpr ⟨⟨χ,hχ⟩,hqχ⟩
  choose C hC hbound using fun χ : t => kernelChartCore_mass_bound χ.1
  refine ⟨t,∑χ,C χ,Finset.sum_nonneg (fun χ hχ => hC χ),fun f => ?_⟩
  calc
    _ ≤ ∑χ : t,∫q in kernelChartCoreImage χ.1.1,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel :=
      integral_le_finite_cover _ K hK.measurableSet _
        (fun χ : t => (kernelChartCoreImage_open χ.1.1).measurableSet) hcov _
        (kernelSmoothTests_memLp f).norm.integrable_sq (fun _ => sq_nonneg _)
    _ ≤ ∑χ : t,C χ*‖kernelL2Localize χ.1.1 (kernelSmoothTestsToL2 f)‖^2 :=
      Finset.sum_le_sum (fun χ hχ => hbound χ f)
    _ = ∑χ : t,C χ*‖kernelEnergyChartFamily t (kernelEnergyGraphCore f) χ‖^2 := by
      simp only [kernelEnergyChartFamily_core_apply]
    _ ≤ _ := finite_sum_weighted_norm_sq_le C hC _

theorem kernelEnergyMassRestriction_isCompact (K : Set KernelQuotient) (hK : IsCompact K) :
    IsCompactOperator (kernelEnergyMassRestriction K hK.measurableSet) := by
  obtain ⟨t,C,hC,hbound⟩ := kernelCompact_mass_bound K hK
  have hsq : ∀u : KernelEnergyGraph,
      ‖kernelEnergyMassRestriction K hK.measurableSet u‖^2≤
        C*‖kernelEnergyChartFamily t u‖^2 := by
    intro u
    exact kernelEnergyGraphCore_dense.induction_on u
      (isClosed_le (by fun_prop : Continuous (fun v => ‖kernelEnergyMassRestriction K hK.measurableSet v‖^2))
        (by fun_prop : Continuous (fun v => C*‖kernelEnergyChartFamily t v‖^2)))
      (fun f => by
        change ‖kernelMassRestrictionCLM K hK.measurableSet
          (kernelEnergyMass (kernelEnergyGraphCore f))‖^2≤_
        rw [kernelEnergyMass_core,kernelMassRestriction_smooth_norm_sq]
        exact hbound f)
  apply compact_of_norm_le_compact _ (kernelEnergyChartFamily t)
    (kernelEnergyChartFamily_isCompact t)
  refine ⟨Real.sqrt C,fun u => ?_⟩
  have hs := hsq u
  have hc := Real.sq_sqrt hC
  have hn := mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg (kernelEnergyChartFamily t u))
  have he : (Real.sqrt C*‖kernelEnergyChartFamily t u‖)^2=C*‖kernelEnergyChartFamily t u‖^2 := by
    rw [mul_pow,Real.sq_sqrt hC]
  nlinarith [norm_nonneg (kernelEnergyMassRestriction K hK.measurableSet u)]

lemma kernelVariationalResolvent_compact_restriction (K : Set KernelQuotient)
    (hK : IsCompact K) :
    IsCompactOperator ((kernelMassRestrictionCLM K hK.measurableSet).comp kernelVariationalResolvent) := by
  exact (kernelEnergyMassRestriction_isCompact K hK).comp_clm kernelVariationalSolution

end CubicEisenstein

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss (actualSextic)

def primeValueHom (w : Ideal ActualEisensteinCubic.O → ℂ) : Ideal ActualEisensteinCubic.O →*₀ ℂ where
  toFun I := if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map w).prod
  map_zero' := by simp
  map_one' := by
    rw [ite_eq_right one_ne_zero,UniqueFactorizationMonoid.normalizedFactors_one]
    rfl
  map_mul' I J := by
    by_cases hI : I=0
    · simp [hI]
    by_cases hJ : J=0
    · simp [hJ]
    simp only [ite_eq_right hI,ite_eq_right hJ,ite_eq_right (mul_ne_zero hI hJ),
      UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,Multiset.map_add,Multiset.prod_add]

theorem primeValueHom_prime (w : Ideal ActualEisensteinCubic.O → ℂ) (P : Ideal ActualEisensteinCubic.O) (hP : Prime P) :
    primeValueHom w P = w P := by
  change (if P=0 then 0 else _) = w P
  rw [ite_eq_right hP.ne_zero,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hP.irreducible]
  simp only [normalize_eq,Multiset.map_singleton,Multiset.prod_singleton]

theorem primeValueHom_norm_le_one (w : Ideal ActualEisensteinCubic.O → ℂ) (hw : ∀ P,‖w P‖≤1)
    (I : Ideal ActualEisensteinCubic.O) : ‖primeValueHom w I‖≤1 := by
  by_cases hI : I=0
  · rw [hI,map_zero,norm_zero]
    exact zero_le_one
  change ‖if I=0 then 0 else _‖≤1
  rw [ite_eq_right hI]
  have hprod (s : Multiset (Ideal ActualEisensteinCubic.O)) : ‖(s.map w).prod‖≤1 := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hw P)).trans ih
  exact hprod _

def principalIdealHom : ActualEisensteinCubic.O →*₀ Ideal ActualEisensteinCubic.O where
  toFun n := Ideal.span {n}
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := (Ideal.span_singleton_mul_span_singleton a b).symm

def localRowValue (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) : ℂ :=
  if h : P.IsMaximal ∧ lambda∉P then
    letI : P.IsMaximal := h.1
    actualSextic P h.2 (Ideal.Quotient.mk P x)
  else 0

theorem localRowValue_good (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P) :
    localRowValue x P = actualSextic P hg (Ideal.Quotient.mk P x) := by
  simp only [localRowValue,dite_eq_left (show P.IsMaximal ∧ lambda∉P from ⟨inferInstance,hg⟩)]

theorem localRowValue_norm (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) : ‖localRowValue x P‖≤1 := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    let : Fintype (ActualEisensteinCubic.O⧸P) := Fintype.ofFinite _
    exact FiniteRayExpansion.norm_char_le_one _ _
  · simp

def idealRowHom (x : ActualEisensteinCubic.O) : Ideal ActualEisensteinCubic.O →*₀ ℂ := primeValueHom (localRowValue x)

def rowTwist (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) : ActualEisensteinCubic.O →* ℂ :=
  Ψ * (idealRowHom (m^6*f^4*z)).toMonoidHom.comp principalIdealHom.toMonoidHom

theorem idealRowHom_prime (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P) :
    idealRowHom x P = actualSextic P hg (Ideal.Quotient.mk P x) := by
  rw [idealRowHom,primeValueHom_prime _ P
    (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance),localRowValue_good]

theorem idealRowHom_norm (x : ActualEisensteinCubic.O) (I : Ideal ActualEisensteinCubic.O) : ‖idealRowHom x I‖≤1 :=
  primeValueHom_norm_le_one _ (localRowValue_norm x) I

theorem rowTwist_norm (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀n,‖Ψ n‖≤1) (m f z n : ActualEisensteinCubic.O) :
    ‖rowTwist Ψ m f z n‖≤1 := by
  change ‖Ψ n * idealRowHom (m^6*f^4*z) (Ideal.span {n})‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΨ n)).trans (idealRowHom_norm _ _)

theorem idealRowHom_product {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset ι) (x : ActualEisensteinCubic.O) :
    idealRowHom x (Ideal.span {∏i∈S,p i}) =
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S x := by
  rw [FiniteGaussPhase.span_finset_prod,map_prod]
  simp only [finiteSquarefreeRow]
  apply Finset.prod_congr rfl
  intro i hi
  exact idealRowHom_prime x _ (hg i)

theorem rowTwist_product {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) :
    rowTwist Ψ m f z (∏i∈S,p i) =
      Ψ (∏i∈S,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) S m*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S f^4*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z := by
  change Ψ _ * idealRowHom _ (Ideal.span {∏i∈S,p i}) = _
  rw [idealRowHom_product p hg S,finiteSquarefreeRow_mul,finiteSquarefreeRow_mul,
    FirstPassCubeLabels.row_pow,FirstPassCubeLabels.row_pow,FirstPassCubeLabels.row_sixth]
  ring

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open SecondPassArithmetic hiding O

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem squarefreeGaussCoefficient_finset (hpr : ∀i,lambda^2∣p i-1) (S : Finset ι) :
    squarefreeGaussCoefficient (Ideal.span {∏i∈S,p i}) =
      MixedCrossSeparation.columnCoefficient p hp hcop hg S := by
  have h := squarefreeGaussCoefficient_eq_canonicalProductCoefficient
    (fun i:S=>p i.val) (fun i=>hp i.val)
    (MixedCrossSeparation.columnPrimeCoprime p hcop S) (fun i=>hg i.val)
    (fun i=>hpr i.val)
  simpa only [Finset.prod_coe_sort,MixedCrossSeparation.columnCoefficient] using h

theorem columnWeight_finset (hpr : ∀i,lambda^2∣p i-1)
    (S : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι → ℂ) :
    columnWeight (rowTwist Ψ m f z) (Ideal.span {∏i∈S,p i}) * H S =
      canonicalSourceCoefficient p hp hcop hg Ψ m f H S *
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z := by
  have hn : (∏i∈S,p i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hprimary : lambda^2∣(∏i∈S,p i)-1 := by
    have h := product_primary (fun i:S=>p i.val) (fun i=>hpr i.val)
    simpa only [Finset.prod_coe_sort] using h
  rw [columnWeight,squarefreeGaussCoefficient_finset p hp hcop hg hpr S,
    primaryGenerator_span _ hn hprimary,rowTwist_product p hg S]
  simp only [canonicalSourceCoefficient]
  ring

end

theorem selected_column_sum (F : Finset (Ideal ActualEisensteinCubic.O))
    (hF : ∀I∈F,CanonicalQuadraticSieve.Admissible I)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℕ → ℂ) :
    let p := CanonicalQuadraticSieve.poolPrimary F
    let hp := CanonicalQuadraticSieve.poolPrimary_ne_zero F hF
    letI : ∀i:ConcretePrimeRowBridge.primePool F,(Ideal.span {p i}).IsMaximal :=
      fun i=>by rw [CanonicalQuadraticSieve.poolPrimary_span F hF i]; infer_instance
    let hcop := CanonicalQuadraticSieve.poolPrimary_coprime F hF
    let hg := CanonicalQuadraticSieve.poolPrimary_good F hF
    (∑I∈F,columnWeight (rowTwist Ψ m f z) I * W (Ideal.absNorm I)) =
      ∑S∈(Finset.univ:Finset (ConcretePrimeRowBridge.primePool F)).powerset,
        canonicalSourceCoefficient p hp hcop hg Ψ m f (InitialMeanSquare.selectedIdealTest F W) S *
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
      lambda^2∣CanonicalQuadraticSieve.poolPrimary F i-1 :=
    (primaryPrime_spec i.val (CanonicalQuadraticSieve.poolPrimary_ne_zero F hF i)).2.2.2
  have h := columnWeight_finset (CanonicalQuadraticSieve.poolPrimary F)
    (CanonicalQuadraticSieve.poolPrimary_ne_zero F hF)
    (CanonicalQuadraticSieve.poolPrimary_coprime F hF)
    (CanonicalQuadraticSieve.poolPrimary_good F hF) hpr S Ψ m f z
    (InitialMeanSquare.selectedIdealTest F W)
  rw [hspan] at h
  rw [←h]
  unfold InitialMeanSquare.selectedIdealTest
  split_ifs <;> simp

end CanonicalRowCompletion

end

end OAI

end Source190

/- Original source: OAI/NumberTheory/DirichletL/RowCompletion/SupportBounds.lean; sha256: e6ddea5d982cef3e63fc651ebc5508878b1c3bb9485dbf89c64894efa2ba5663 -/
section Source191
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight

theorem localRowValue_zero_of_mem (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) (hx : x∈P) :
    localRowValue x P = 0 := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact MulChar.map_nonunit _ (not_isUnit_zero)
  · rfl

theorem idealRowHom_zero_of_dvd (x : ActualEisensteinCubic.O) {P I : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPI : P∣I) (hx : x∈P) : idealRowHom x I = 0 := by
  obtain ⟨J,rfl⟩ := hPI
  rw [map_mul]
  have hz : idealRowHom x P = 0 := by
    rw [idealRowHom,primeValueHom_prime _ P hP,localRowValue_zero_of_mem x P hx]
  rw [hz,zero_mul]

theorem columnWeight_zero_of_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P I : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPI : P∣I) (hm : m∈P) :
    columnWeight (rowTwist Ψ m f z) I = 0 := by
  unfold columnWeight
  have hx : m^6*f^4*z∈P := by
    have hm6 : m^6∈P := by
      rw [show m^6=m^5*m by ring]
      exact P.mul_mem_left (m^5) hm
    exact P.mul_mem_right z (P.mul_mem_right (f^4) hm6)
  by_cases hg : primaryGenerator I=0
  · rw [hg]
    change squarefreeGaussCoefficient I * (Ψ 0 * idealRowHom _ (Ideal.span {0})) = 0
    rw [Ideal.span_singleton_zero]
    change squarefreeGaussCoefficient I * (Ψ 0 * idealRowHom _ (0:Ideal ActualEisensteinCubic.O)) = 0
    rw [map_zero (idealRowHom _),mul_zero,mul_zero]
  · change squarefreeGaussCoefficient I *
      (Ψ (primaryGenerator I) * idealRowHom _ (Ideal.span {primaryGenerator I})) = 0
    rw [(primaryGenerator_spec I hg).1,idealRowHom_zero_of_dvd _ hP hPI hx,mul_zero,mul_zero]

theorem columnWeight_zero_of_not_squarefree (Ψ : ActualEisensteinCubic.O →* ℂ) {I : Ideal ActualEisensteinCubic.O}
    (hI : ¬Squarefree I) : columnWeight Ψ I = 0 := by
  simp [columnWeight,squarefreeGaussCoefficient,hI]

theorem weighted_column_support (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X≤D)
    {I : Ideal ActualEisensteinCubic.O}
    (hn : columnWeight (rowTwist Ψ m f z) I * W ((Ideal.absNorm I:ℝ)/X) ≠ 0) :
    I∈InitialMeanSquare.outsideSquarefreeIdeals S D := by
  have hc : columnWeight (rowTwist Ψ m f z) I ≠ 0 :=
    fun h=>hn (by rw [h,zero_mul])
  have hwindow : W ((Ideal.absNorm I:ℝ)/X) ≠ 0 :=
    fun h=>hn (by rw [h,mul_zero])
  have hI : I≠0 := fun h=>hc (by rw [h,columnWeight_zero])
  have hsf : Squarefree I := by
    by_contra h
    exact hc (columnWeight_zero_of_not_squarefree _ h)
  apply Finset.mem_filter.mpr
  refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,?_⟩,hsf⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hI (Ideal.absNorm_eq_zero_iff.mp h))
  · exact_mod_cast ((div_le_iff₀ hX).mp (hW _ hwindow)).trans hD
  · intro P hP hPI
    exact hc (columnWeight_zero_of_mask Ψ m f z (hSp P hP) hPI (hm P hP))

theorem weighted_column_tsum_eq (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X≤D) :
    (∑'I:Ideal ActualEisensteinCubic.O,columnWeight (rowTwist Ψ m f z) I * W ((Ideal.absNorm I:ℝ)/X)) =
      ∑I∈InitialMeanSquare.outsideSquarefreeIdeals S D,
        columnWeight (rowTwist Ψ m f z) I * W ((Ideal.absNorm I:ℝ)/X) := by
  apply tsum_eq_sum
  intro I hI
  by_contra hn
  exact hI (weighted_column_support S D hSp Ψ m f z hm W b X hX hW hD hn)

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open FirstPassCubeLabels hiding O

theorem localRowValue_mul (a b : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) :
    localRowValue (a*b) P = localRowValue a P * localRowValue b P := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    simp only [map_mul]
  · simp

theorem idealRowHom_argument_mul (a b : ActualEisensteinCubic.O) (I : Ideal ActualEisensteinCubic.O) :
    idealRowHom (a*b) I = idealRowHom a I * idealRowHom b I := by
  by_cases hI : I=0
  · rw [hI,map_zero,map_zero,map_zero,zero_mul]
  change (if I=0 then 0 else _) = (if I=0 then 0 else _) * (if I=0 then 0 else _)
  simp only [ite_eq_right hI]
  have hprod (s : Multiset (Ideal ActualEisensteinCubic.O)) :
      (s.map (localRowValue (a*b))).prod =
        (s.map (localRowValue a)).prod * (s.map (localRowValue b)).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons]
      rw [localRowValue_mul,ih]
      ring
  exact hprod _

theorem rowTwist_row_factor (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z n : ActualEisensteinCubic.O) :
    rowTwist Ψ m f z n =
      rowTwist Ψ m f 1 n * idealRowHom z (Ideal.span {n}) := by
  change Ψ n * idealRowHom (m^6*f^4*z) (Ideal.span {n}) =
    (Ψ n * idealRowHom (m^6*f^4*1) (Ideal.span {n})) * idealRowHom z (Ideal.span {n})
  rw [mul_one,idealRowHom_argument_mul]
  ring

theorem cubeWeight_row_factor (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (B : Ideal ActualEisensteinCubic.O) :
    cubeWeight (rowTwist Ψ m f z) B =
      cubeWeight (rowTwist Ψ m f 1) B * idealRowHom z B^3 := by
  by_cases hB : primaryGenerator B=0
  · have hzero (x:ActualEisensteinCubic.O) : rowTwist Ψ m f x (primaryGenerator B) = 0 := by
      rw [hB]
      change Ψ 0 * idealRowHom _ (Ideal.span {(0:ActualEisensteinCubic.O)}) = 0
      rw [Ideal.span_singleton_zero]
      change Ψ 0 * idealRowHom _ (0:Ideal ActualEisensteinCubic.O) = 0
      rw [map_zero (idealRowHom _),mul_zero]
    change _ * rowTwist Ψ m f z (primaryGenerator B)^3 / _ =
      (_ * rowTwist Ψ m f 1 (primaryGenerator B)^3 / _) * _
    rw [hzero z,hzero 1]
    simp
  · change _ * rowTwist Ψ m f z (primaryGenerator B)^3 / _ =
      (_ * rowTwist Ψ m f 1 (primaryGenerator B)^3 / _) * _
    rw [rowTwist_row_factor,(primaryGenerator_spec B hB).1,mul_pow]
    ring

theorem idealRowHom_prime_powers {ι : Type*} (P : ι → Ideal ActualEisensteinCubic.O)
    [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (pool : Finset ι)
    (v : ι → ℕ) (z : ActualEisensteinCubic.O) :
    idealRowHom z (∏i∈pool,(P i)^v i) = multiplicityRow P hg pool v z := by
  rw [map_prod]
  simp only [map_pow,multiplicityRow]
  apply Finset.prod_congr rfl
  intro i hi
  rw [idealRowHom_prime z (P i) (hg i)]

theorem cubeWeight_prime_powers {ι : Type*} (P : ι → Ideal ActualEisensteinCubic.O)
    [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (pool : Finset ι)
    (v : ι → ℕ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) :
    cubeWeight (rowTwist Ψ m f z) (∏i∈pool,(P i)^v i) =
      cubeWeight (rowTwist Ψ m f 1) (∏i∈pool,(P i)^v i) *
        multiplicityRow P hg pool v z^3 := by
  rw [cubeWeight_row_factor,idealRowHom_prime_powers P hg pool v z]

end

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O

def excludedGenerator (S : Finset (Ideal ActualEisensteinCubic.O)) : ActualEisensteinCubic.O := idealGenerator (∏P∈S,P)

theorem excludedGenerator_mem (S : Finset (Ideal ActualEisensteinCubic.O)) {P : Ideal ActualEisensteinCubic.O} (hP : P∈S) :
    excludedGenerator S∈P := by
  have hdiv : P∣∏Q∈S,Q := Finset.dvd_prod_of_mem (fun Q:Ideal ActualEisensteinCubic.O=>Q) hP
  have hm : idealGenerator (∏Q∈S,Q)∈Ideal.span {idealGenerator (∏Q∈S,Q)} :=
    Ideal.subset_span (by simp)
  rw [span_idealGenerator] at hm
  exact (Ideal.dvd_iff_le.mp hdiv) hm

theorem excludedGenerator_not_mem_pool (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P)
    (i : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)) :
    excludedGenerator S∉i.val := by
  intro hm
  have hprime : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hspan : Ideal.span {excludedGenerator S} ≤ i.val :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
  change Ideal.span {idealGenerator (∏Q∈S,Q)} ≤ i.val at hspan
  rw [span_idealGenerator] at hspan
  have hdiv : i.val∣∏Q∈S,Q := Ideal.dvd_iff_le.mpr hspan
  obtain ⟨P,hPS,hPi⟩ := (hprime.dvd_finsetProd_iff (fun Q:Ideal ActualEisensteinCubic.O=>Q)).mp hdiv
  have heq : i.val=P := (prime_dvd_prime_iff_eq hprime (hSp P hPS)).mp hPi
  obtain ⟨I,hI,hfactor⟩ := mem_primePool_iff.mp i.property
  have ho : I∈outsideIdealsUpTo S D := (Finset.mem_filter.mp hI).1
  have hd : i.val∣I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hfactor
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P hPS (heq ▸ hd)

theorem outside_pool_fixed_mask (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (T : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D))) :
    rowCoprimeMask (fun i=>Ideal.span {poolPrimary (InitialMeanSquare.outsideSquarefreeIdeals S D) i})
      T (excludedGenerator S) = 1 := by
  unfold rowCoprimeMask
  rw [ite_eq_right]
  rintro ⟨i,hi,hmem⟩
  change excludedGenerator S ∈ Ideal.span {poolPrimary (InitialMeanSquare.outsideSquarefreeIdeals S D) i} at hmem
  rw [poolPrimary_span _ (InitialMeanSquare.outsideSquarefree_admissible S D hbad)] at hmem
  exact excludedGenerator_not_mem_pool S D hSp i hmem

theorem canonicalSourceCoefficient_fixed_mask {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i}) (Ψ : ActualEisensteinCubic.O →* ℂ) (m c f : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (T : Finset ι)
    (hc : rowCoprimeMask (fun i=>Ideal.span {p i}) T c=1) :
    canonicalSourceCoefficient p hp hcop hg Ψ (m*c) f H T =
      canonicalSourceCoefficient p hp hcop hg Ψ m f H T := by
  simp only [canonicalSourceCoefficient,FirstPassCubeLabels.mask_mul _ hg,hc,mul_one]

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

def outsideCanonicalRow (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i]; infer_instance
  fixedChildRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) Finset.univ Ψ m
    (fun T=>W (primeProductNorm (poolPrimary F) T/X)) f z

theorem outsideCanonicalRow_eq_global (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    outsideCanonicalRow S D hbad Ψ m f z W X =
      ∑'I:Ideal ActualEisensteinCubic.O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I *
        W ((Ideal.absNorm I:ℝ)/X) := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i]; infer_instance
  symm
  rw [weighted_column_tsum_eq S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W b X hX hW hD]
  have he := selected_column_sum F hF Ψ (m*excludedGenerator S) f z (fun n=>W (n/X))
  dsimp only at he
  rw [he]
  unfold outsideCanonicalRow fixedChildRow
  dsimp only
  apply Finset.sum_congr rfl
  intro T hT
  rw [canonicalSourceCoefficient_fixed_mask _ _ _ _ Ψ m (excludedGenerator S) f _ T
    (outside_pool_fixed_mask S D hbad hSp T)]
  have ht := InitialMeanSquare.selectedIdealTest_outside S D hbad hSp W b X hX hW hD T
  simp only [canonicalSourceCoefficient,secondChildColumn]
  rw [ht]
  ring

theorem outsideCanonicalRow_cube_inverse (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X : ℝ) (hX : 0<X) (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      ∑'H:Ideal ActualEisensteinCubic.O,(UniqueFactorizationMonoid.moebius H:ℂ)*
        cubeWeight (rowTwist Ψ (m*excludedGenerator S) f z) H *
        completedT (rowTwist Ψ (m*excludedGenerator S) f z) W
          (X/(Ideal.absNorm H:ℝ)^3) := by
  rw [outsideCanonicalRow_eq_global S D hbad hSp Ψ m f z W b X hX hW hD]
  exact completed_cube_inverse _ W hWc X hX

theorem outsideCanonicalRow_cube_split (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑'I:Ideal ActualEisensteinCubic.O,∑'B:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B *
        summand (rowTwist Ψ (m*excludedGenerator S) f z) W X I B := by
  rw [outsideCanonicalRow_eq_global S D hbad hSp Ψ m f z W b X hX hW hD]
  exact completed_cube_inverse_split _ W hWc X H₀ hX

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open CompletedGauss hiding O

def cubeIndex (F : Finset (Ideal ActualEisensteinCubic.O)) (B : Ideal ActualEisensteinCubic.O) : primePool F →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i=>(UniqueFactorizationMonoid.normalizedFactors B).count i.val)

@[simp] theorem cubeIndex_apply (F : Finset (Ideal ActualEisensteinCubic.O)) (B : Ideal ActualEisensteinCubic.O) (i : primePool F) :
    cubeIndex F B i = (UniqueFactorizationMonoid.normalizedFactors B).count i.val := by
  simp [cubeIndex]

def cubeIdeal (F : Finset (Ideal ActualEisensteinCubic.O)) (v : primePool F →₀ ℕ) : Ideal ActualEisensteinCubic.O :=
  ∏i:primePool F,i.val^v i

theorem cubeIdeal_cubeIndex (F : Finset (Ideal ActualEisensteinCubic.O)) (B : Ideal ActualEisensteinCubic.O) (hB : B≠0)
    (hcover : ∀P∈UniqueFactorizationMonoid.normalizedFactors B,P∈primePool F) :
    cubeIdeal F (cubeIndex F B) = B := by
  have hsub : (UniqueFactorizationMonoid.normalizedFactors B).toFinset ⊆ primePool F := by
    intro P hP
    exact hcover P (Multiset.mem_toFinset.mp hP)
  calc
    _ = ∏P∈primePool F,P^(UniqueFactorizationMonoid.normalizedFactors B).count P := by
      simp only [cubeIdeal,cubeIndex_apply]
      exact Finset.prod_coe_sort (s := primePool F)
        (f := fun P:Ideal ActualEisensteinCubic.O=>P^(UniqueFactorizationMonoid.normalizedFactors B).count P)
    _ = (UniqueFactorizationMonoid.normalizedFactors B).prod :=
      (Finset.prod_multiset_count_of_subset _ _ hsub).symm
    _ = B := Ideal.prod_normalizedFactors_eq_self hB

theorem cubeIndex_inj (F : Finset (Ideal ActualEisensteinCubic.O)) (B C : Ideal ActualEisensteinCubic.O) (hB : B≠0) (hC : C≠0)
    (hb : ∀P∈UniqueFactorizationMonoid.normalizedFactors B,P∈primePool F)
    (hc : ∀P∈UniqueFactorizationMonoid.normalizedFactors C,P∈primePool F)
    (heq : cubeIndex F B = cubeIndex F C) : B=C := by
  have he := congrArg (cubeIdeal F) heq
  rwa [cubeIdeal_cubeIndex F B hB hb,cubeIdeal_cubeIndex F C hC hc] at he

theorem outside_cubeIdeal_cubeIndex (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    {B : Ideal ActualEisensteinCubic.O} (hB : B∈outsideIdealsUpTo S D) :
    cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D)
      (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D) B) = B := by
  exact cubeIdeal_cubeIndex _ B (outsideIdealsUpTo_ne_bot S D B hB)
    (InitialMeanSquare.outside_factors_mem_pool S D hB)

theorem sum_outside_cubeIndex (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (a : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑B∈outsideIdealsUpTo S D,a B) =
      ∑v∈(outsideIdealsUpTo S D).image (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D)),
        a (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro B hB
    rw [outside_cubeIdeal_cubeIndex S D hB]
  · intro B hB C hC he
    exact cubeIndex_inj _ B C (outsideIdealsUpTo_ne_bot S D B hB)
      (outsideIdealsUpTo_ne_bot S D C hC)
      (InitialMeanSquare.outside_factors_mem_pool S D hB)
      (InitialMeanSquare.outside_factors_mem_pool S D hC) he

theorem cubeIdeal_ne_zero (F : Finset (Ideal ActualEisensteinCubic.O)) (v : primePool F →₀ ℕ) :
    cubeIdeal F v ≠ 0 := by
  unfold cubeIdeal
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (NeZero.ne i.val))

theorem cubeIdeal_primaryGenerator (F : Finset (Ideal ActualEisensteinCubic.O))
    (v : primePool F →₀ ℕ) :
    primaryGenerator (cubeIdeal F v) =
      FirstPassCubeLabels.primeProduct (poolPrimary F) Finset.univ v := by
  change primaryGeneratorHom (∏i:primePool F,i.val^v i) = _
  rw [map_prod]
  simp only [map_pow]
  unfold FirstPassCubeLabels.primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  change primaryGenerator i.val^v i = poolPrimary F i^v i
  rw [←primaryPrime_eq_primaryGenerator i.val]
  rfl

end CanonicalRowCompletion

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic

theorem densityChildEnergy_canonical_terminal
    {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ)
    (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : ActualEisensteinCubic.O) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ)
    (X F K A M : ℝ) (J : ℕ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hKF : K ≤ F) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV₁ : ∀ s,‖V₁ s‖ ≤ M) (hV₂ : ∀ s,‖V₂ s‖ ≤ M)
    (hVs₁ : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hVs₂ : ∀ s,V₂ s ≠ 0 → |s| ≤ A)
    (hT : ∀ z∈T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J) ≤
      globalTerminalConstant A M*(X*F)^2 := by
  have hXF : 0 < X*F := mul_pos hX (zero_lt_one.trans_le hF)
  have he := childDensity_elementary_all_scales p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m T V₁ V₂ X F K A M J hX hF hK hA hM hV₁ hV₂ hVs₁ hVs₂ hT
  change _ ≤ globalTerminalConstant A M*K*X at he
  have hc0 := globalTerminalConstant_nonneg A M
  have he' : densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)/(X*F) ≤
      globalTerminalConstant A M*(X*F) := by
    calc
      _ ≤ globalTerminalConstant A M*K*X := he
      _ ≤ globalTerminalConstant A M*F*X :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKF hc0) hX.le
      _ = globalTerminalConstant A M*(X*F) := by ring
  convert (div_le_iff₀ hXF).mp he' using 1 ; ring

end SecondPassIntegration

open scoped BigOperators Classical
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm firstLogDensity)
open SecondPassIntegration (densityChildEnergy)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)

section
variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)
  [∀i,(Ideal.span {p i}).IsMaximal]

def globalQuantitativeSource (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
    (K ell B F M H U : ℝ) (side : Bool) : Finset (GlobalSecondData ι) :=
  globalFirstSupportedPool p pool
    ((globalFirstFamilySet pool blocks).filter
      (fun b => primeProductNorm p b.common ≤ U ∧ primeProductNorm p b.firstCommon ≤ U))
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side

theorem globalQuantitativeSource_block_mem (pool : Finset ι)
    (blocks : Finset (GlobalCubeBlock ι)) (K ell B F M H U : ℝ) (side : Bool)
    (x : GlobalSecondData ι) (hx : x∈globalQuantitativeSource p pool blocks K ell B F M H U side) :
    x.first.block∈blocks := by
  have hx' := (mem_globalFirstExpansionPool pool _ _ x).mp (Finset.mem_filter.mp hx).1
  exact ((mem_globalFirstFamilySet pool blocks x.first).mp (Finset.mem_filter.mp hx'.1).1).1

theorem globalQuantitativeSource_frequency_ne_zero (pool : Finset ι)
    (blocks : Finset (GlobalCubeBlock ι)) (K ell B F M H U : ℝ) (side : Bool)
    (x : GlobalSecondData ι) (hx : x∈globalQuantitativeSource p pool blocks K ell B F M H U side) :
    x.source.frequency ≠ 0 :=
  globalFirstSupportedPool_frequency_ne_zero p pool _ _ ell M side x hx

end

theorem globalFirstRayChildBudget_canonical_bound (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃ Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (windows : Fin 7 → ℝ → ℂ)
      (C Γ E K ell B F M H U Z θ A₀ Vmax : ℝ) (N J : ℕ),
      0≤C → 0≤Γ → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0 → |t|≤A₀) → (∀t,windows 6 t≠0 → |t|≤A₀) →
      (∀u,‖Ψ u‖≤1) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (let source := globalQuantitativeSource p pool blocks K ell B F M H U side
       ∀a : RayCharacter×RayCharacter,∀r : FirstCoreIndex,
       ∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),
       ∀ray : SecondRayIndex,∀q∈globalBinTriples p source side j,
       let Ψmode := firstCoreTwist side (if side then a.1 else a.2) Ψ r
       densityChildEnergy p hp hcop hg pool (secondRayMinus Ψmode ray) (secondRayPlus Ψmode ray)
         (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
         (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J) ≤
         E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2) →
      globalFirstRayChildBudget p hp hcop hg pool blocks Ψ m windows C Γ ε K ell B F M H U (N+1) (2*J) side ≤
        (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*C*globalRayTripleConstant*
          ((ell*B^3)*F)*U^(deltaLoss+8*ε)*
          (E*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N)) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalChildBudget_canonical_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj pool blocks side Ψ m windows C Γ E K ell B F M H U Z θ A₀ Vmax N J
    hC hΓ hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hb₁ hb₂ he
  let source := globalQuantitativeSource p pool blocks K ell B F M H U side
  let Q := (∫t : ℝ,firstLogDensity 0 t)*Γ*C*globalRayTripleConstant*((ell*B^3)*F)*
    U^(deltaLoss+8*ε)*(E*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N))
  have hI : 0≤∫t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hQ : 0≤Q := by
    have ht := globalTerminalConstant_nonneg A₀ Vmax
    have hB0 := zero_lt_one.trans_le hB
    have hF0 := zero_lt_one.trans_le hF
    dsimp [Q]
    unfold globalRayTripleConstant
    positivity
  have hrow (a : RayCharacter×RayCharacter) (r : FirstCoreIndex) :
      (∫t : ℝ,firstLogDensity 0 t)*globalChildBudget p hp hcop hg pool source
        (firstCoreTwist side (if side then a.1 else a.2) Ψ r) m windows (Γ*firstCoreUniformWeight r*C)
        ε 0 0 K ell B F M H (N+1) (2*J) side ≤ firstCoreUniformWeight r*Q := by
    have hcoeff : 0≤Γ*firstCoreUniformWeight r*C := by
      unfold firstCoreUniformWeight
      positivity
    have hk : ∀x∈source,x.source.frequency≠0 :=
      fun x hx => globalQuantitativeSource_frequency_ne_zero p pool blocks K ell B F M H U side x hx
    have hb₁' : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B :=
      fun x hx => hb₁ x.first.block (globalQuantitativeSource_block_mem p pool blocks K ell B F M H U side x hx)
    have hb₂' : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B :=
      fun x hx => hb₂ x.first.block (globalQuantitativeSource_block_mem p pool blocks K ell B F M H U side x hx)
    have hr := hbound p hp hcop hg hc hinj pool source side
      (firstCoreTwist side (if side then a.1 else a.2) Ψ r) m windows (Γ*firstCoreUniformWeight r*C)
      E K ell B F M H U Z θ A₀ Vmax N J hcoeff hE hU hK hell hB hF hH
      hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂
      (fun u => (firstCoreTwist_norm_le side (if side then a.1 else a.2) Ψ r u).trans (hΨ u))
      hk hb₁' hb₂' (he a r)
    exact (mul_le_mul_of_nonneg_left hr hI).trans_eq (by dsimp [Q]; ring)
  have hmass : (∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖)≤512 := by
    simpa only [Fintype.sum_prod_type] using RayFourExpansion.crossCoeff_sum_norm_le
  calc
    _ ≤ ∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*
        ∑r : FirstCoreIndex,firstCoreUniformWeight r*Q :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun r _ => hrow a r)) (norm_nonneg _))
    _ = (∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖)*
        (∑r : FirstCoreIndex,firstCoreUniformWeight r)*Q := by
      simp only [←Finset.sum_mul,mul_assoc]
    _ ≤ (512*(512*32))*Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul hmass firstCoreUniformWeight_mass
        (Finset.sum_nonneg (fun r _ => by unfold firstCoreUniformWeight; positivity)) (by norm_num)) hQ
    _ = _ := by dsimp [Q]; ring

theorem globalFirstQuantitativeBudget_canonical_bound (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃ Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (windows : Fin 7 → ℝ → ℂ)
      (C Cd Ct Γ E K ell B F M H U Z θ A₀ Vmax : ℝ) (N J Ntail : ℕ),
      0≤C → 0≤Γ → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0 → |t|≤A₀) → (∀t,windows 6 t≠0 → |t|≤A₀) →
      (∀u,‖Ψ u‖≤1) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (let source := globalQuantitativeSource p pool blocks K ell B F M H U side
       ∀a : RayCharacter×RayCharacter,∀r : FirstCoreIndex,
       ∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),
       ∀ray : SecondRayIndex,∀q∈globalBinTriples p source side j,
       let Ψmode := firstCoreTwist side (if side then a.1 else a.2) Ψ r
       densityChildEnergy p hp hcop hg pool (secondRayMinus Ψmode ray) (secondRayPlus Ψmode ray)
         (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
         (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J) ≤
         E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2) →
      globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ m windows
        C Cd Ct Γ ε K ell B F M H U (N+1) (2*J) Ntail side ≤
        (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*((ell*B^3)*F)*
          ((B*U)^ε*(Cd+Ct*globalFirstTailFactor K ell B F U H Ntail)+
           C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
             (E*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N))) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalFirstRayChildBudget_canonical_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj pool blocks side Ψ m windows C Cd Ct Γ E K ell B F M H U Z θ A₀ Vmax N J Ntail
    hC hΓ hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hb₁ hb₂ he
  have hr := hbound p hp hcop hg hc hinj pool blocks side Ψ m windows C Γ E K ell B F M H U Z θ A₀ Vmax N J
    hC hΓ hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hb₁ hb₂ he
  unfold globalFirstQuantitativeBudget
  calc
    _ ≤ (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*(ell*B^3*F)*(B*U)^ε*
          (Cd+Ct*globalFirstTailFactor K ell B F U H Ntail)+
        (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*C*globalRayTripleConstant*
          ((ell*B^3)*F)*U^(deltaLoss+8*ε)*
          (E*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N)) := add_le_add le_rfl hr
    _ = _ := by ring

end SecondPassArithmetic

end

end OAI

end Source191

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/ReopeningSeparation.lean; sha256: 79b1ffd159e3d6f3249876a22ab5476fc73d6bb81398c8cbee40b0ff98a52dfc -/
section Source192
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (columnLog primeProductNorm)
open FourierBridge (logPhase)
open JointLogSeparation (frequencyTwist)

def normPhase (t : ℝ) : ActualEisensteinCubic.O →* ℂ where
  toFun z := if z=0 then 0 else logPhase t (Real.log (‖eisEmbedding z‖^2))
  map_one' := by simp [FourierBridge.logPhase_zero]
  map_mul' a b := by
    by_cases ha : a=0
    · simp [ha]
    by_cases hb : b=0
    · simp [hb]
    simp only [ite_eq_right ha,ite_eq_right hb,ite_eq_right (mul_ne_zero ha hb),map_mul,norm_mul,mul_pow]
    rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha)))
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hb))),FourierBridge.logPhase_add]

@[simp] theorem normPhase_zero (t : ℝ) : normPhase t 0=0 := by simp [normPhase]

theorem normPhase_of_ne_zero (t : ℝ) (z : ActualEisensteinCubic.O) (hz : z≠0) :
    normPhase t z=logPhase t (Real.log (‖eisEmbedding z‖^2)) := by simp [normPhase,hz]

theorem normPhase_norm (t : ℝ) (z : ActualEisensteinCubic.O) (hz : z≠0) : ‖normPhase t z‖=1 := by
  rw [normPhase_of_ne_zero t z hz,FourierBridge.logPhase_norm]

theorem normPhase_norm_le_one (t : ℝ) (z : ActualEisensteinCubic.O) : ‖normPhase t z‖≤1 := by
  by_cases hz : z=0
  · simp [hz]
  · rw [normPhase_norm t z hz]

theorem normPhase_add (s t : ℝ) : normPhase (s+t)=normPhase s*normPhase t := by
  ext z
  by_cases hz : z=0
  · simp [hz]
  · simp only [MonoidHom.mul_apply,normPhase_of_ne_zero _ z hz,JointLogSeparation.logPhase_add_frequency]

theorem normPhase_star (t : ℝ) (z : ActualEisensteinCubic.O) : star (normPhase t z)=normPhase (-t) z := by
  by_cases hz : z=0
  · simp [hz]
  · simp only [normPhase_of_ne_zero _ z hz,SecondPassIntegration.logPhase_conjugate]

def normHeightTwist (Ψ : ActualEisensteinCubic.O →* ℂ) (t : ℝ) : ActualEisensteinCubic.O →* ℂ := Ψ*normPhase t

theorem normHeightTwist_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (t : ℝ) (z : ActualEisensteinCubic.O) :
    ‖normHeightTwist Ψ t z‖≤‖Ψ z‖ := by
  simp only [normHeightTwist,MonoidHom.mul_apply,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (normPhase_norm_le_one t z)

theorem normHeightTwist_twice (Ψ : ActualEisensteinCubic.O →* ℂ) (s t : ℝ) :
    normHeightTwist (normHeightTwist Ψ s) t=normHeightTwist Ψ (s+t) := by
  simp only [normHeightTwist,normPhase_add,mul_assoc]

theorem normHeightTwist_mul (Ψ Ξ : ActualEisensteinCubic.O →* ℂ) (t : ℝ) :
    normHeightTwist (Ψ*Ξ) t=normHeightTwist Ψ t*Ξ := by
  unfold normHeightTwist
  ac_rfl

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)

include hp in
omit [DecidableEq ι] in
theorem logPhase_columnLog (X t : ℝ) (hX : 0<X) (S : Finset ι) :
    logPhase t (columnLog p X S)=
      logPhase t (-Real.log X)*normPhase t (∏i∈S,p i) := by
  rw [normPhase_of_ne_zero t _ (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))]
  rw [columnLog,Real.log_div (FirstPassCubeLabels.primeProductNorm_pos p hp S).ne' hX.ne']
  rw [sub_eq_add_neg,FourierBridge.logPhase_add]
  exact mul_comm _ _

variable [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem canonicalSourceCoefficient_frequencyTwist (Ψ : ActualEisensteinCubic.O →* ℂ) (m f : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X t : ℝ) (hX : 0<X) (S : Finset ι) :
    canonicalSourceCoefficient p hp hcop hg Ψ m f
      (fun U=>frequencyTwist g t (columnLog p X U)) S=
    logPhase t (-Real.log X)*canonicalSourceCoefficient p hp hcop hg (normHeightTwist Ψ t) m f
      (fun U=>g (columnLog p X U)) S := by
  simp only [canonicalSourceCoefficient,JointLogSeparation.frequencyTwist_apply,
    logPhase_columnLog p hp X t hX S,normHeightTwist,MonoidHom.mul_apply]
  ring

theorem fixedChildRow_frequencyTwist (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f y : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X t : ℝ) (hX : 0<X) :
    fixedChildRow p hp hcop hg pool Ψ m (fun U=>frequencyTwist g t (columnLog p X U)) f y=
    logPhase t (-Real.log X)*fixedChildRow p hp hcop hg pool (normHeightTwist Ψ t) m
      (fun U=>g (columnLog p X U)) f y := by
  unfold fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,JointLogSeparation.frequencyTwist_apply,
    logPhase_columnLog p hp X t hX S,normHeightTwist,MonoidHom.mul_apply]
  ring

theorem fixedChildRow_frequencyTwist_norm (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f y : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X t : ℝ) (hX : 0<X) :
    ‖fixedChildRow p hp hcop hg pool Ψ m (fun U=>frequencyTwist g t (columnLog p X U)) f y‖=
    ‖fixedChildRow p hp hcop hg pool (normHeightTwist Ψ t) m
      (fun U=>g (columnLog p X U)) f y‖ := by
  rw [fixedChildRow_frequencyTwist p hp hcop hg pool Ψ m f y g X t hX,norm_mul,FourierBridge.logPhase_norm,one_mul]

end SecondPassArithmetic

section

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FourierBridge (logPhase)
open FirstPassCubeLabels (columnLog)

def secondSignedHeight (negative : Bool) (a b : ℝ) : ℝ :=
  if negative then b-a else a-b

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)

include hp in
omit [DecidableEq ι] in
theorem fixedSecondTest_normPhase (V : ℝ → ℂ) (X a b : ℝ) (hX : 0<X)
    (negative : Bool) (S : Finset ι) :
    fixedSecondTest p V X a b negative S=
      logPhase (secondSignedHeight negative a b) (-Real.log X)*
      normPhase (secondSignedHeight negative a b) (∏i∈S,p i)*
      fixedSecondTest p V X 0 0 negative S := by
  have hz (x : ℝ) : logPhase 0 x=1 := by simp [FourierBridge.logPhase]
  cases negative <;>
    simp only [secondSignedHeight,fixedSecondTest,JointLogSeparation.fixedColumnTest,
      Bool.false_eq_true,ite_false,ite_true,sub_self,hz,mul_one,star_mul,
      SecondPassIntegration.logPhase_conjugate,neg_sub] <;>
    rw [logPhase_columnLog p hp X _ hX S] ; ring

variable [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem fixedChildRow_secondTest_normPhase (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f y : ActualEisensteinCubic.O)
    (V : ℝ → ℂ) (X a b : ℝ) (hX : 0<X) (negative : Bool) :
    fixedChildRow p hp hcop hg pool Ψ m (fixedSecondTest p V X a b negative) f y=
      logPhase (secondSignedHeight negative a b) (-Real.log X)*
      fixedChildRow p hp hcop hg pool (normHeightTwist Ψ (secondSignedHeight negative a b)) m
        (fixedSecondTest p V X 0 0 negative) f y := by
  unfold fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,fixedSecondTest_normPhase p hp V X a b hX negative S,
    normHeightTwist,MonoidHom.mul_apply]
  ring

end SecondPassArithmetic

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem childEnergy_normHeight (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X a b : ℝ) (hX : 0<X)
    (testNegative rowNegative : Bool) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b=
      childEnergy p hp hcop hg pool (normHeightTwist Ψ (secondSignedHeight testNegative a b))
        m T V X testNegative rowNegative 0 0 := by
  unfold childEnergy idealChildRow
  simp_rw [fixedChildRow_secondTest_normPhase p hp hcop hg pool Ψ m _ _ V X a b hX testNegative,
    norm_mul,FourierBridge.logPhase_norm,one_mul]

theorem childEnergy_previousNormHeight (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X t a b : ℝ) (hX : 0<X)
    (testNegative rowNegative : Bool) :
    childEnergy p hp hcop hg pool (normHeightTwist Ψ t) m T V X testNegative rowNegative a b=
      childEnergy p hp hcop hg pool (normHeightTwist Ψ (t+secondSignedHeight testNegative a b))
        m T V X testNegative rowNegative 0 0 := by
  rw [childEnergy_normHeight p hp hcop hg pool (normHeightTwist Ψ t) m T V X a b hX
    testNegative rowNegative,normHeightTwist_twice]

end SecondPassIntegration

open scoped BigOperators Classical
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic

theorem firstCoreTwist_normHeight (negative : Bool) (χ : RayFourExpansion.RayCharacter)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (r : FirstCoreIndex) (t : ℝ) :
    firstCoreTwist negative χ (normHeightTwist Ψ t) r=
      normHeightTwist (firstCoreTwist negative χ Ψ r) t := by
  unfold firstCoreTwist normHeightTwist
  ac_rfl

theorem secondRayMinus_normHeight (Ψ : ActualEisensteinCubic.O →* ℂ) (r : SecondRayIndex) (t : ℝ) :
    secondRayMinus (normHeightTwist Ψ t) r=normHeightTwist (secondRayMinus Ψ r) t := by
  unfold secondRayMinus normHeightTwist
  ac_rfl

theorem secondRayPlus_normHeight (Ψ : ActualEisensteinCubic.O →* ℂ) (r : SecondRayIndex) (t : ℝ) :
    secondRayPlus (normHeightTwist Ψ t) r=normHeightTwist (secondRayPlus Ψ r) t := by
  unfold secondRayPlus normHeightTwist
  ac_rfl

end SecondPassArithmetic

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic

private theorem sqrt_height_weight (B t : ℝ) (hB : 0≤B) (J : ℕ) :
    Real.sqrt (B*(1+‖t‖)^(2*J))=Real.sqrt B*(1+‖t‖)^J := by
  rw [show 2*J=J*2 from Nat.mul_comm _ _,pow_mul,Real.sqrt_mul hB,
    Real.sqrt_sq (pow_nonneg (by positivity : 0≤1+‖t‖) J)]

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem densityChildEnergy_normHeight_polynomial
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ t₁ t₂ B₁ B₂ : ℝ) (J : ℕ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (h₁ : ∀t,childEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m T V₁ X₁ true false 0 0≤
      B₁*(1+‖t‖)^(2*J))
    (h₂ : ∀t,childEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m T V₂ X₂ false true 0 0≤
      B₂*(1+‖t‖)^(2*J)) :
    densityChildEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t₁) (normHeightTwist Ψ₂ t₂)
      m T V₁ V₂ X₁ X₂ (2*J)≤
      Real.sqrt B₁*Real.sqrt B₂*(1+‖t₁‖)^J*(1+‖t₂‖)^J*
        (∫t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  have ha₁ (a : ℝ) : childEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t₁) m T V₁ X₁ true false a 0≤
      (B₁*(1+‖t₁‖)^(2*J))*(1+‖a‖)^(2*J) := by
    rw [childEnergy_previousNormHeight p hp hcop hg pool Ψ₁ m T V₁ X₁ t₁ a 0 hX₁ true false]
    simp only [secondSignedHeight,ite_true,zero_sub,←sub_eq_add_neg]
    calc
      _ ≤ B₁*(1+‖t₁-a‖)^(2*J) := h₁ (t₁-a)
      _ ≤ B₁*((1+‖t₁‖)*(1+‖a‖))^(2*J) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (JointLogSeparation.one_add_norm_sub_le t₁ a) _) hB₁
      _ = _ := by rw [mul_pow]; ring
  have ha₂ (a : ℝ) : childEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t₂) m T V₂ X₂ false true a 0≤
      (B₂*(1+‖t₂‖)^(2*J))*(1+‖a‖)^(2*J) := by
    rw [childEnergy_previousNormHeight p hp hcop hg pool Ψ₂ m T V₂ X₂ t₂ a 0 hX₂ false true]
    simp only [secondSignedHeight,Bool.false_eq_true,ite_false,sub_zero]
    have hsum : 1+‖t₂+a‖≤(1+‖t₂‖)*(1+‖a‖) := by
      simpa only [sub_neg_eq_add,norm_neg] using JointLogSeparation.one_add_norm_sub_le t₂ (-a)
    calc
      _ ≤ B₂*(1+‖t₂+a‖)^(2*J) := h₂ (t₂+a)
      _ ≤ B₂*((1+‖t₂‖)*(1+‖a‖))^(2*J) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum _) hB₂
      _ = _ := by rw [mul_pow]; ring
  have hd := densityChildEnergy_polynomial_bound p hp hcop hg pool
    (normHeightTwist Ψ₁ t₁) (normHeightTwist Ψ₂ t₂) m T V₁ V₂ X₁ X₂ J
    (B₁*(1+‖t₁‖)^(2*J)) (B₂*(1+‖t₂‖)^(2*J))
    (mul_nonneg hB₁ (by positivity)) (mul_nonneg hB₂ (by positivity)) ha₁ ha₂
  rw [sqrt_height_weight B₁ t₁ hB₁ J,sqrt_height_weight B₂ t₂ hB₂ J] at hd
  exact hd.trans_eq (by ring)

end SecondPassIntegration
end

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog)
open FourierBridge (logPhase)
open JointLogSeparation (frequencyTwist)

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem reopenedCanonicalRow_frequencyTwist (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (g : 𝓢(ℝ,ℂ))
    (X t : ℝ) (hX : 0<X) :
    reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f
      (fun S=>frequencyTwist g t (columnLog p X S)) z=
      logPhase t (-Real.log X)*reopenedCanonicalRow p hp hcop hg pool Q β (normHeightTwist Ψ t) m f
        (fun S=>g (columnLog p X S)) z := by
  unfold reopenedCanonicalRow
  simp_rw [canonicalSourceCoefficient_frequencyTwist p hp hcop hg Ψ m f g X t hX,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro S hS
  ring

theorem reopenedCanonicalRow_frequencyTwist_norm (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (g : 𝓢(ℝ,ℂ))
    (X t : ℝ) (hX : 0<X) :
    ‖reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f
      (fun S=>frequencyTwist g t (columnLog p X S)) z‖=
      ‖reopenedCanonicalRow p hp hcop hg pool Q β (normHeightTwist Ψ t) m f
        (fun S=>g (columnLog p X S)) z‖ := by
  rw [reopenedCanonicalRow_frequencyTwist p hp hcop hg pool Q β Ψ m f z g X t hX,
    norm_mul,FourierBridge.logPhase_norm,one_mul]

theorem reopenedSource_frequencyTwist
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (hQ : ∀v∈Q,v.support⊆pool) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (g W : 𝓢(ℝ,ℂ))
    (K X t : ℝ) (hK : 0<K) (hX : 0<X) :
    canonicalSourceTotal p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      Ψ Ψ m m (frequencyTwist g t) (frequencyTwist g t) W K X=
    canonicalSourceTotal p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g W K X := by
  rw [←reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m
    (frequencyTwist g t) W K X hK,
    ←reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β
      (normHeightTwist Ψ t) m g W K X hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply tsum_congr
  intro z
  rw [reopenedCanonicalRow_frequencyTwist_norm p hp hcop hg pool Q (β I) Ψ m _ z g X t hX]

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

theorem reopenedCanonicalRow_twoPassage_uniform_height
    (W g V : 𝓢(ℝ,ℂ)) (M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+6+1) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+6+1) ∧
      ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (Q:Finset (ι→₀ℕ)) (labels:Finset (Ideal ActualEisensteinCubic.O))
      (β:Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ) (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (Γ t Ksrc K ell B F H U:ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U →
      ell*Real.exp M≤U → (∀u,‖Ψ u‖≤1) →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B) →
      (∀I∈labels,Squarefree I) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      ‖(ell*B^2*F:ℂ)⁻¹*
        ((∑I∈labels,∑'z:ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/Ksrc)*
           (‖reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
             (ConcretePrimeRowBridge.idealGenerator I)
             (fun S=>frequencyTwist g t (columnLog p ell S)) z‖^2:ℝ))-
         canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g W Ksrc ell-
         canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g W Ksrc K ell)‖≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₁ C₁ Cd₁ Ct₁ (Γ^2) ε K ell B F M H U A J N true)*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₂ C₂ Cd₂ Ct₂ (Γ^2) ε K ell B F M H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,htransfer⟩:=
    canonicalSource_twoPassage_quantitative W g g V V M M Nv Nv hM hM hNv hNv
      hgM hgM hV hV hWin hWin ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hMU hΨ hβ hQ hQB hsf hf
  dsimp only
  rw [reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m
    (frequencyTwist g t) W Ksrc ell hKsrc,
    reopenedSource_frequencyTwist p hp hcop hg hinj hpr pool Q hQ labels β Ψ m g W Ksrc ell t hKsrc hell]
  have hΨt : ∀u,‖normHeightTwist Ψ t u‖≤1 :=
    fun u=>(normHeightTwist_norm_le Ψ t u).trans (hΨ u)
  exact htransfer p hp hinj hcop hg hc hpr pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
    (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m (Γ^2) Ksrc K ell B F H U
    (sq_nonneg Γ) hKsrc hK hell hB hF hH hU hMU hMU hΨt hΨt
    (fun b hb C hC I hI=>reopenedPairCoefficient_bound Q labels β Γ hΓ hβ b hb C I hI)
    (reopenedCubeFamily_admissible Q)
    (fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).1)
    (fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).2) hsf hf

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

namespace CanonicalCubeSeparation
open FourierBridge JointLogSeparation FirstPassCubeLabels

def columnWindowRadius (a b : ℝ) : ℝ := |Real.log a| + |Real.log b| + 3

lemma columnWindowRadius_nonneg (a b : ℝ) : 0 ≤ columnWindowRadius a b := by
  unfold columnWindowRadius
  positivity

def sourceLogProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) := by
  have hc : HasCompactSupport (fun u : ℝ => W (Real.exp u)) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (Real.log a) (Real.log b)) isCompact_Icc
    intro u hu
    have hm := hs hu
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log ha hm.1
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hm.2
  exact hc.toSchwartzMap (hW.comp Real.contDiff_exp)

@[simp] lemma sourceLogProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (u : ℝ) :
    sourceLogProfile W a b ha hs hW u = W (Real.exp u) := rfl

def reopeningCoefficient (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  𝓕 (sourceLogProfile W a b ha hs hW)

def cubeFrequencyFactor (t ξ : ℝ) : ℂ :=
  (Real.exp (t/2) : ℂ) * logPhase ξ (3*t)

@[simp] lemma cubeFrequencyFactor_norm (t ξ : ℝ) :
    ‖cubeFrequencyFactor t ξ‖ = Real.exp (t/2) := by
  simp only [cubeFrequencyFactor, norm_mul, logPhase_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma cubeFrequencyFactor_bound (t ξ : ℝ) (ht : t ≤ 1) :
    ‖cubeFrequencyFactor t ξ‖ ≤ Real.exp (1/2) := by
  rw [cubeFrequencyFactor_norm]
  exact Real.exp_le_exp.mpr (by linarith)

lemma active_column_window (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (t u : ℝ)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hWu : W (Real.exp (u+3*t)) ≠ 0) :
    |u| ≤ columnWindowRadius a b := by
  have hab := hs hWu
  have hlo : Real.log a ≤ u+3*t := by
    simpa only [Real.log_exp] using Real.log_le_log ha hab.1
  have hhi : u+3*t ≤ Real.log b := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hab.2
  unfold columnWindowRadius
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b),
    abs_nonneg (Real.log a), abs_nonneg (Real.log b), ht.1, ht.2]

lemma reopening_integrable (b V : 𝓢(ℝ,ℂ)) (t u : ℝ) :
    Integrable (fun ξ : ℝ => b ξ * cubeFrequencyFactor t ξ * frequencyTwist V ξ u) := by
  have hi : Integrable (fun ξ : ℝ =>
      b ξ * ((Real.exp (t/2) : ℂ) * logPhase ξ (3*t) * (logPhase ξ u * V u))) := by
    apply b.integrable.mul_bdd (c := Real.exp (t/2) * ‖V u‖)
    · exact (((logPhase_continuous_left (3*t)).const_mul _).mul
        ((logPhase_continuous_left u).mul_const _)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ξ => by
        simp only [norm_mul, logPhase_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), one_mul, mul_one, le_refl])
  convert hi using 1
  funext ξ
  rw [frequencyTwist_apply]
  unfold cubeFrequencyFactor
  ring

theorem reopening_separation_with_window (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (t u : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (Real.exp (t/2) : ℂ) * W (Real.exp (u+3*t)) =
      ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
        cubeFrequencyFactor t ξ * frequencyTwist V ξ u := by
  have hwindow : V u * W (Real.exp (u+3*t)) = W (Real.exp (u+3*t)) := by
    by_cases hz : W (Real.exp (u+3*t)) = 0
    · simp [hz]
    · rw [hV u (active_column_window W a b ha hs t u ht hz), one_mul]
  have hinv := schwartz_phase_inversion
    (sourceLogProfile W a b ha hs hW) (u+3*t)
  change W (Real.exp (u+3*t)) =
    ∫ ξ : ℝ, logPhase ξ (u+3*t) * reopeningCoefficient W a b ha hs hW ξ at hinv
  calc
    _ = ((Real.exp (t/2) : ℂ) * V u) * W (Real.exp (u+3*t)) := by
      rw [mul_assoc, hwindow]
    _ = ∫ ξ : ℝ, ((Real.exp (t/2) : ℂ) * V u) *
        (logPhase ξ (u+3*t) * reopeningCoefficient W a b ha hs hW ξ) := by
      rw [hinv, integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [logPhase_add, frequencyTwist_apply]
      unfold cubeFrequencyFactor
      ring

theorem exists_reopening_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ V : 𝓢(ℝ,ℂ), HasCompactSupport V ∧
      (∀ u, |u| ≤ columnWindowRadius a b → V u = 1) ∧
      (∀ u, V u ≠ 0 → |u| ≤ columnWindowRadius a b + 1) ∧
      (∀ t u : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
        (Real.exp (t/2) : ℂ) * W (Real.exp (u+3*t)) =
          ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
            cubeFrequencyFactor t ξ * frequencyTwist V ξ u) ∧
      (∀ t u : ℝ, Integrable (fun ξ : ℝ => reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor t ξ * frequencyTwist V ξ u)) ∧
      (∀ J : ℕ, ∃ C : ℝ, 0 < C ∧
        Integrable (fun ξ : ℝ => (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖) ∧
        (∫ ξ : ℝ, (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖) ≤ C ∧
        ∀ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖ ≤ C * firstLogDensity J ξ) := by
  obtain ⟨v,hvc,hvs,hvone,hvsupp,_⟩ := exists_complex_smooth_cutoff
    (columnWindowRadius a b) (columnWindowRadius_nonneg a b)
  let V : 𝓢(ℝ,ℂ) := hvc.toSchwartzMap hvs
  have hVone : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1 := hvone
  refine ⟨V,hvc,hVone,?_,?_,reopening_integrable _ V,?_⟩
  · intro u hu
    have hmem := hvsupp (subset_tsupport v hu)
    exact abs_le.mpr hmem
  · exact fun t u ht => reopening_separation_with_window W a b ha hs hW V hVone t u ht
  · intro J
    let g := sourceLogProfile W a b ha hs hW
    let c := fourierPointBound (J+2) (profileSourceBound g (J+2))
    let m := ∫ ξ : ℝ, (1+‖ξ‖)^J * ‖reopeningCoefficient W a b ha hs hW ξ‖
    have hc : 0 ≤ c := fourierPointBound_nonneg _ _ (profileSourceBound_nonneg _ _)
    have hm : 0 ≤ m := integral_nonneg (fun ξ => by positivity)
    refine ⟨1+c+m,by positivity,weighted_schwartz_integrable _ J,by dsimp [m]; linarith,?_⟩
    intro ξ
    exact (profile_fourier_envelope g J ξ).trans
      (mul_le_mul_of_nonneg_right (by linarith : c ≤ 1+c+m) (firstLogDensity_nonneg J ξ))

end CanonicalCubeSeparation

end

end OAI

end Source192

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/LogSeparation.lean; sha256: 7ba99b6b53ffcc4a40c9a6315875df7e06441ea350781152fd94c30749551bf8 -/
section Source193
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CanonicalCubeSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open FourierBridge JointLogSeparation

lemma cube_log_bin (B n : ℝ) (hB : 0 < B) (hn : B ≤ n)
    (hn' : n ≤ Real.exp 1 * B) : Real.log (n/B) ∈ Set.Icc (0:ℝ) 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hn
  constructor
  · exact Real.log_nonneg ((le_div_iff₀ hB).mpr (by simpa using hn))
  · have hh : n/B ≤ Real.exp 1 := (div_le_iff₀ hB).mpr hn'
    have := Real.log_le_log (div_pos hn0 hB) hh
    simpa only [Real.log_exp] using this

lemma cube_log_argument (B ell n q : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) (hq : 0 < q) :
    Real.exp (Real.log (q/ell) + 3*Real.log (n/B)) = q*n^3/(B^3*ell) := by
  rw [Real.exp_add, Real.exp_log (div_pos hq hell)]
  have he : Real.exp (3*Real.log (n/B)) = (n/B)^3 := by
    rw [show (3:ℝ)*Real.log (n/B) =
      Real.log (n/B)+Real.log (n/B)+Real.log (n/B) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hn hB)]
    ring
  rw [he]
  field_simp

lemma cube_half_normalization (B ell n : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) :
    (Real.sqrt (B^3*ell))⁻¹ * Real.sqrt n =
      (B*Real.sqrt ell)⁻¹ * Real.exp (Real.log (n/B)/2) := by
  have hb0 := (Real.sqrt_pos.mpr hB).ne'
  have he0 := (Real.sqrt_pos.mpr hell).ne'
  have hs : Real.sqrt (B^3*ell) = B*Real.sqrt B*Real.sqrt ell := by
    rw [show B^3*ell=B^2*(B*ell) by ring,
      Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB.le, Real.sqrt_mul hB.le]
    ring
  have hnexp : Real.exp (Real.log (n/B)/2) = Real.sqrt n/Real.sqrt B := by
    rw [← sqrt_exp_half, Real.exp_log (div_pos hn hB), Real.sqrt_div hn.le]
  rw [hs, hnexp]
  field_simp

lemma cube_half_normalization_complex (B ell n : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) :
    (Real.sqrt (B^3*ell) : ℂ)⁻¹ * (Real.sqrt n : ℂ) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * (Real.exp (Real.log (n/B)/2) : ℂ) := by
  exact_mod_cast cube_half_normalization B ell n hB hell hn

theorem reopening_norm_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X n q : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : B ≤ n) (hn' : n ≤ Real.exp 1*B) (hq : 0 < q) :
    (Real.sqrt X : ℂ)⁻¹ * (Real.sqrt n : ℂ) * W (q*n^3/X) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor (Real.log (n/B)) ξ * frequencyTwist V ξ (Real.log (q/ell)) := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hn
  have hsep := reopening_separation_with_window W a b ha hs hW V hV
    (Real.log (n/B)) (Real.log (q/ell)) (cube_log_bin B n hB hn hn')
  rw [cube_log_argument B ell n q hB hell hn0 hq] at hsep
  rw [hX, cube_half_normalization_complex B ell n hB hell hn0, mul_assoc, hsep]

lemma completed_cube_half_weight (X n : ℝ) (hX : 0 < X) (hn : 0 < n) :
    n⁻¹ * (Real.sqrt (X/n^3))⁻¹ = (Real.sqrt X)⁻¹ * Real.sqrt n := by
  have hs : Real.sqrt (n^3) = n*Real.sqrt n := by
    rw [show n^3=n^2*n by ring, Real.sqrt_mul (sq_nonneg n), Real.sqrt_sq hn.le]
  rw [Real.sqrt_div hX.le, hs, inv_div]
  field_simp

lemma completed_cube_half_weight_complex (X n : ℝ) (hX : 0 < X) (hn : 0 < n) :
    (n : ℂ)⁻¹ * (Real.sqrt (X/n^3) : ℂ)⁻¹ =
      (Real.sqrt X : ℂ)⁻¹ * (Real.sqrt n : ℂ) := by
  exact_mod_cast completed_cube_half_weight X n hX hn

theorem completed_cube_norm_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X n q : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : B ≤ n) (hn' : n ≤ Real.exp 1*B) (hq : 0 < q) :
    (n : ℂ)⁻¹ * (Real.sqrt (X/n^3) : ℂ)⁻¹ * W (q/(X/n^3)) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor (Real.log (n/B)) ξ * frequencyTwist V ξ (Real.log (q/ell)) := by
  have hXp : 0 < X := hX ▸ mul_pos (pow_pos hB _) hell
  rw [completed_cube_half_weight_complex X n hXp (lt_of_lt_of_le hB hn), div_div_eq_mul_div]
  exact reopening_norm_separation W a b ha hs hW V hV B ell X n q hB hell hX hn hn' hq

def separatedCubeCoefficient {κ : Type*} (β : κ → ℂ) (n : κ → ℝ)
    (B ξ : ℝ) (v : κ) : ℂ := β v * cubeFrequencyFactor (Real.log (n v/B)) ξ

lemma separatedCubeCoefficient_bound {κ : Type*} (β : κ → ℂ) (n : κ → ℝ)
    (B ξ Γ : ℝ) (hB : 0 < B) (hΓ : 0 ≤ Γ) (v : κ)
    (hn : B ≤ n v) (hn' : n v ≤ Real.exp 1*B) (hβ : ‖β v‖ ≤ Γ) :
    ‖separatedCubeCoefficient β n B ξ v‖ ≤ Γ*Real.exp (1/2) := by
  unfold separatedCubeCoefficient
  rw [norm_mul]
  exact mul_le_mul hβ (cubeFrequencyFactor_bound _ ξ (cube_log_bin B _ hB hn hn').2)
    (norm_nonneg _) hΓ

theorem reopening_finite_sum_integrable {κ τ : Type*}
    (Q : Finset κ) (S : Finset τ) (β : κ → ℂ) (A : κ → τ → ℂ)
    (n : κ → ℝ) (q : τ → ℝ) (B ell : ℝ) (b V : 𝓢(ℝ,ℂ)) :
    Integrable (fun ξ : ℝ => b ξ * ∑v∈Q,∑j∈S,
      separatedCubeCoefficient β n B ξ v * A v j * frequencyTwist V ξ (Real.log (q j/ell))) := by
  have hi : Integrable (fun ξ : ℝ => ∑v∈Q,∑j∈S,
      (β v*A v j)*(b ξ*cubeFrequencyFactor (Real.log (n v/B)) ξ*
        frequencyTwist V ξ (Real.log (q j/ell)))) := by
    apply integrable_finsetSum
    intro v hv
    apply integrable_finsetSum
    intro j hj
    exact (reopening_integrable b V _ _).const_mul _
  convert hi using 1
  funext ξ
  simp only [Finset.mul_sum, separatedCubeCoefficient]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem reopening_finite_sum {κ τ : Type*}
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (Q : Finset κ) (S : Finset τ) (β : κ → ℂ) (A : κ → τ → ℂ)
    (n : κ → ℝ) (q : τ → ℝ) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀v∈Q,B ≤ n v) (hn' : ∀v∈Q,n v ≤ Real.exp 1*B)
    (hq : ∀j∈S,0 < q j) :
    (∑v∈Q,∑j∈S, (β v*A v j)*
      ((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ * W (q j/(X/(n v)^3)))) =
    ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ * ∑v∈Q,∑j∈S,
        separatedCubeCoefficient β n B ξ v * A v j *
          frequencyTwist V ξ (Real.log (q j/ell)) := by
  let G : ℝ → κ → τ → ℂ := fun ξ v j => (β v*A v j)*
    (reopeningCoefficient W a b ha hs hW ξ * cubeFrequencyFactor (Real.log (n v/B)) ξ *
      frequencyTwist V ξ (Real.log (q j/ell)))
  have hi (v : κ) (j : τ) : Integrable (fun ξ => G ξ v j) :=
    (reopening_integrable _ V _ _).const_mul _
  have hterm (v : κ) (hv : v∈Q) (j : τ) (hj : j∈S) :
      (β v*A v j)*((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ * W (q j/(X/(n v)^3))) =
        ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,G ξ v j := by
    rw [completed_cube_norm_separation W a b ha hs hW V hV B ell X (n v) (q j)
      hB hell hX (hn v hv) (hn' v hv) (hq j hj)]
    rw [show (∫ ξ : ℝ,G ξ v j) = (β v*A v j)*∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ * cubeFrequencyFactor (Real.log (n v/B)) ξ *
          frequencyTwist V ξ (Real.log (q j/ell)) from integral_const_mul _ _]
    ring
  calc
    _ = ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∑v∈Q,∑j∈S,∫ ξ : ℝ,G ξ v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => hterm v hv j hj)
    _ = ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,∑v∈Q,∑j∈S,G ξ v j := by
      congr 1
      rw [integral_finsetSum _ (fun v hv => integrable_finsetSum _ (fun j hj => hi v j))]
      apply Finset.sum_congr rfl
      intro v hv
      exact (integral_finsetSum _ (fun j hj => hi v j)).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [Finset.mul_sum, separatedCubeCoefficient]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [G]
      ring

end CanonicalCubeSeparation

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight

theorem rowTwist_primary_zero_of_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P B : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    rowTwist Ψ m f z (primaryGenerator B) = 0 := by
  have hx : m^6*f^4*z∈P := by
    have hm6 : m^6∈P := by
      rw [show m^6=m^5*m by ring]
      exact P.mul_mem_left (m^5) hm
    exact P.mul_mem_right z (P.mul_mem_right (f^4) hm6)
  by_cases hg : primaryGenerator B=0
  · rw [hg]
    change Ψ 0 * idealRowHom _ (Ideal.span {(0:ActualEisensteinCubic.O)}) = 0
    rw [Ideal.span_singleton_zero]
    change Ψ 0 * idealRowHom _ (0:Ideal ActualEisensteinCubic.O) = 0
    rw [map_zero (idealRowHom _),mul_zero]
  · change Ψ (primaryGenerator B) * idealRowHom _ (Ideal.span {primaryGenerator B}) = 0
    rw [(primaryGenerator_spec B hg).1,idealRowHom_zero_of_dvd _ hP hPB hx,mul_zero]

theorem cubeWeight_zero_of_prime_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P B : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    cubeWeight (rowTwist Ψ m f z) B = 0 :=
  cubeWeight_zero_of_mask _ B (rowTwist_primary_zero_of_mask Ψ m f z hP hPB hm)

theorem summand_cube_support (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D)
    (I B : Ideal ActualEisensteinCubic.O) (hn : summand (rowTwist Ψ m f z) W X I B≠0) :
    B∈outsideIdealsUpTo S D := by
  have hI : I≠0 := fun h=>hn (by rw [h,summand_zero_left])
  have hB : B≠0 := fun h=>hn (by rw [h,summand_zero_right])
  have hw : W ((Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X)≠0 :=
    fun h=>hn (summand_zero_window _ W X I B h)
  have hsize := (div_le_iff₀ hX).mp (hW _ hw)
  have hb := (triple_scale_bounds (Ideal.absNorm I:ℝ) (Ideal.absNorm B:ℝ) 1
    (norm_at_least_one I hI) (norm_at_least_one B hB) (by norm_num)).2.1
  simp only [one_pow,mul_one] at hb
  apply mem_outsideIdealsUpTo.mpr
  refine ⟨?_,?_,?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hB (Ideal.absNorm_eq_zero_iff.mp h))
  · exact_mod_cast (hb.trans hsize).trans hD
  · intro P hP hPB
    have hz := cubeWeight_zero_of_prime_mask Ψ m f z (hSp P hP) hPB (hm P hP)
    exact hn (by simp only [summand,hz,mul_zero,zero_mul])

theorem large_cube_sum_comm (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0<X) :
    (∑'I:Ideal ActualEisensteinCubic.O,∑'B:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand Ψ W X I B) =
      ∑'B:Ideal ActualEisensteinCubic.O,∑'I:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand Ψ W X I B := by
  let a : Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O → ℂ := fun p=>largeCubeCoefficient H₀ p.2*summand Ψ W X p.1 p.2
  have hf : (Function.support a).Finite :=
    (completedT_finite_support Ψ W hW X hX).subset (by
      intro p hp
      exact fun h=>hp (by simp only [a,h,mul_zero]))
  have hs : Summable a := summable_of_hasFiniteSupport hf
  let e := Equiv.prodComm (Ideal ActualEisensteinCubic.O) (Ideal ActualEisensteinCubic.O)
  have ht : Summable (fun p=>a (e p)) := e.summable_iff.mpr hs
  calc
    _ = ∑'p:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O,a p := hs.tsum_prod.symm
    _ = ∑'p:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O,a (e p) := (e.tsum_eq a).symm
    _ = _ := ht.tsum_prod

theorem large_cube_sum_finite (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (∑'I:Ideal ActualEisensteinCubic.O,∑'B:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand (rowTwist Ψ m f z) W X I B) =
      ∑B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑'I:Ideal ActualEisensteinCubic.O,summand (rowTwist Ψ m f z) W X I B := by
  rw [large_cube_sum_comm _ W hWc X H₀ hX]
  simp only [tsum_mul_left]
  apply tsum_eq_sum
  intro B hB
  have hz : ∀I:Ideal ActualEisensteinCubic.O,summand (rowTwist Ψ m f z) W X I B=0 := by
    intro I
    by_contra hn
    exact hB (summand_cube_support S D hSp Ψ m f z hm W b X hX hW hD I B hn)
  simp only [hz,tsum_zero,mul_zero]

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O

theorem inner_completed_sum (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (hX : 0<X)
    (B : Ideal ActualEisensteinCubic.O) (hB : B≠0) :
    (∑'I:Ideal ActualEisensteinCubic.O,summand Ψ W X I B) =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        ∑'I:Ideal ActualEisensteinCubic.O,columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3)) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := div_pos hX (pow_pos hN _)
  have ht (I:Ideal ActualEisensteinCubic.O) : summand Ψ W X I B =
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
  exact tsum_mul_left

theorem outsideCanonicalRow_reopened (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hb : 0 ≤ b) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑B∈outsideIdealsUpTo S D,
        (largeCubeCoefficient H₀ B * cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) B *
          (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) * idealRowHom z B^3 *
          outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm B:ℝ)^3) := by
  rw [outsideCanonicalRow_cube_split S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  rw [large_cube_sum_finite S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W hWc b X H₀ hX hW hD]
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  have hB0 : B≠0 := outsideIdealsUpTo_ne_bot S D B hB
  have hN := norm_at_least_one B hB0
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := by positivity
  have hYX : X/(Ideal.absNorm B:ℝ)^3 ≤ X :=
    div_le_self hX.le (one_le_pow₀ hN)
  have hDY : b*(X/(Ideal.absNorm B:ℝ)^3) ≤ D :=
    (mul_le_mul_of_nonneg_left hYX hb).trans hD
  rw [inner_completed_sum _ W X hX B hB0]
  rw [←outsideCanonicalRow_eq_global S D hbad hSp Ψ m f z W b
    (X/(Ideal.absNorm B:ℝ)^3) hY hW hDY]
  rw [cubeWeight_row_factor]
  ring

theorem outsideCanonicalRow_reopened_exponents (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hb : 0 ≤ b) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑v∈(outsideIdealsUpTo S D).image (cubeIndex F),
        (largeCubeCoefficient H₀ (cubeIdeal F v) *
          cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) *
          (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹) *
          idealRowHom z (cubeIdeal F v)^3 *
          outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3) := by
  dsimp only
  rw [outsideCanonicalRow_reopened S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD]
  rw [sum_outside_cubeIndex S D]

end

open ActualEisensteinCubic
open CompletedGauss hiding O

theorem cubeWeight_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal ActualEisensteinCubic.O) :
    ‖cubeWeight Ψ B‖ ≤ 1/(Ideal.absNorm B:ℝ) := by
  have hang : ‖FiniteGaussPhase.angularFactor (primaryGenerator B)‖ ≤ 1 := by
    by_cases hz : primaryGenerator B=0
    · simp [hz,FiniteGaussPhase.angularFactor]
    · exact (FiniteGaussPhase.norm_angularFactor _ hz).le
  change ‖star (FiniteGaussPhase.angularFactor (primaryGenerator B))^3*
    Ψ (primaryGenerator B)^3/(Ideal.absNorm B:ℂ)‖ ≤ _
  rw [norm_div,norm_mul,norm_pow,norm_pow,norm_star,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) hang)).trans (pow_le_one₀ (norm_nonneg _) (hΨ _))

def cubePhase (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) : ℂ :=
  (Ideal.absNorm B:ℂ)*cubeWeight Ψ B

theorem cubePhase_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal ActualEisensteinCubic.O) :
    ‖cubePhase Ψ B‖ ≤ 1 := by
  by_cases hB : B=0
  · simp [hB,cubePhase]
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  rw [cubePhase,norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (Ideal.absNorm B:ℝ)*(1/(Ideal.absNorm B:ℝ)) :=
      mul_le_mul_of_nonneg_left (cubeWeight_norm_le Ψ hΨ B) hN.le
    _ = 1 := by field_simp

theorem cube_weight_scale (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) (hB : B≠0)
    (X : ℝ) (hX : 0<X) :
    cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹ =
      cubePhase Ψ B * (Real.sqrt (Ideal.absNorm B:ℝ):ℂ)/(Real.sqrt X:ℂ) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hs3 : Real.sqrt ((Ideal.absNorm B:ℝ)^3) =
      (Ideal.absNorm B:ℝ)*Real.sqrt (Ideal.absNorm B:ℝ) := by
    rw [show (Ideal.absNorm B:ℝ)^3=(Ideal.absNorm B:ℝ)^2*(Ideal.absNorm B:ℝ) by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hN]
  have hs : Real.sqrt (X/(Ideal.absNorm B:ℝ)^3) =
      Real.sqrt X/((Ideal.absNorm B:ℝ)*Real.sqrt (Ideal.absNorm B:ℝ)) := by
    rw [Real.sqrt_div hX.le,hs3]
  rw [hs,Complex.ofReal_div,Complex.ofReal_mul,cubePhase]
  push_cast
  have hNc : (Ideal.absNorm B:ℂ)≠0 := by exact_mod_cast hN.ne'
  have hsN : (Real.sqrt (Ideal.absNorm B:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  have hsX : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  field_simp

def reopenedCubeCoefficient (H₀ : ℝ) (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) : ℂ :=
  largeCubeCoefficient H₀ B * cubePhase Ψ B

theorem reopenedCubeCoefficient_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀(H₀:ℝ) (Ψ:ActualEisensteinCubic.O →* ℂ), (∀z,‖Ψ z‖≤1) →
      ∀B:Ideal ActualEisensteinCubic.O,B≠0 → ‖reopenedCubeCoefficient H₀ Ψ B‖ ≤ C*(Ideal.absNorm B:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := largeCubeCoefficient_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro H₀ Ψ hΨ B hB
  rw [reopenedCubeCoefficient,norm_mul]
  calc
    _ ≤ ‖largeCubeCoefficient H₀ B‖*1 :=
      mul_le_mul_of_nonneg_left (cubePhase_norm_le Ψ hΨ B) (norm_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using hbound H₀ B hB

theorem reopenedCubeCoefficient_support (H₀:ℝ) (Ψ:ActualEisensteinCubic.O →* ℂ) (B:Ideal ActualEisensteinCubic.O)
    (h:reopenedCubeCoefficient H₀ Ψ B≠0) : B≠0 ∧ H₀ ≤ (Ideal.absNorm B:ℝ) := by
  exact largeCubeCoefficient_support H₀ B (fun hz=>h (by simp only [reopenedCubeCoefficient,hz,zero_mul]))

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels

def childLabelRotation (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O :=
  (z.1,(u : ActualEisensteinCubic.O)^4*(if negative then -z.2 else z.2))

theorem childLabelRotation_injective (u : ActualEisensteinCubic.Oˣ) (negative : Bool) :
    Function.Injective (childLabelRotation u negative) := by
  intro z w he
  have hf := congrArg Prod.fst he
  change z.1=w.1 at hf
  have hs := congrArg Prod.snd he
  change (u : ActualEisensteinCubic.O)^4*(if negative then -z.2 else z.2)=
    (u : ActualEisensteinCubic.O)^4*(if negative then -w.2 else w.2) at hs
  have hz := mul_left_cancel₀ (pow_ne_zero 4 u.ne_zero) hs
  apply Prod.ext hf
  cases negative <;> simpa only [Bool.false_eq_true,ite_false,ite_true,neg_inj] using hz

theorem childLabelRotation_norm (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) :
    ‖eisEmbedding (childLabelRotation u negative z).2‖^2=‖eisEmbedding z.2‖^2 := by
  cases negative <;> simp only [childLabelRotation,Bool.false_eq_true,ite_false,ite_true,
    map_mul,norm_mul,map_pow,norm_pow,GaussGeneratorTransport.norm_eisEmbedding_unit,
    one_pow,one_mul,map_neg,norm_neg]

theorem childLabelRotation_ne_zero (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)
    (hz : z.2≠0) : (childLabelRotation u negative z).2≠0 := by
  apply mul_ne_zero (pow_ne_zero 4 u.ne_zero)
  cases negative <;> simpa using hz

section
variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem fixedChildRow_label_mul (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (u f z : ActualEisensteinCubic.O) :
    fixedChildRow p hp hcop hg pool Ψ m H (u*f) z=
      fixedChildRow p hp hcop hg pool Ψ m H f (u^4*z) := by
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,finiteSquarefreeRow_mul,row_pow,mul_pow]
  ring

theorem idealChildRow_eq_rotated (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (negative : Bool) (u : ActualEisensteinCubic.Oˣ) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) :
    idealChildRow p hp hcop hg pool Ψ m H negative u z=
      fixedChildRow p hp hcop hg pool Ψ m H
        (ConcretePrimeRowBridge.idealGenerator (childLabelRotation u negative z).1)
        (childLabelRotation u negative z).2 := by
  exact fixedChildRow_label_mul p hp hcop hg pool Ψ m H (u : ActualEisensteinCubic.O) _ _

def canonicalSmoothedEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) : ℝ :=
  (∑I∈labels,nonzeroRowMajorantSum
    (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) K).re

theorem canonicalSmoothedEnergy_nonneg (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) (hK : 0<K) :
    0≤canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K := by
  unfold canonicalSmoothedEnergy
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro I hI
  have he := finite_nonzero_row_energy_le_majorant
    (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) ∅ K hK
    (by simp) (by simp)
  simpa using he

theorem canonicalSmoothedEnergy_zero_correction (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) (hK : 0<K) :
    canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K=
      (∑I∈labels,∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*
        (‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I) z‖^2:ℝ)).re-
      ∑I∈labels,‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I) 0‖^2 := by
  unfold canonicalSmoothedEnergy
  simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re,
    Complex.re_sum,Complex.ofReal_re]

theorem idealChildRow_energy_le_canonical (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (negative : Bool) (u : ActualEisensteinCubic.Oˣ)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (K : ℝ) (hK : 0<K)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    (∑z∈T,‖idealChildRow p hp hcop hg pool Ψ m H negative u z‖^2)≤
      canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K := by
  let f : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O → ℝ := fun z=>
    ‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator z.1) z.2‖^2
  let R := (firstFrequencyDisk K).erase 0
  have hsub : T.image (childLabelRotation u negative)⊆labels.product R := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_product.mpr
    refine ⟨hlabels z hz,Finset.mem_erase.mpr ⟨childLabelRotation_ne_zero u negative z (hzero z hz),?_⟩⟩
    apply (mem_firstFrequencyDisk K _).mpr
    rw [childLabelRotation_norm]
    exact hrows z hz
  calc
    _ = ∑w∈T.image (childLabelRotation u negative),f w := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro z hz
        rw [idealChildRow_eq_rotated]
      · exact fun _ _ _ _ he=>childLabelRotation_injective u negative he
    _ ≤ ∑w∈labels.product R,f w :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>sq_nonneg _)
    _ = ∑I∈labels,∑z∈R,f (I,z) := by rw [Finset.product_eq_sprod,Finset.sum_product]
    _ ≤ ∑I∈labels,(nonzeroRowMajorantSum
        (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) K).re := by
      apply Finset.sum_le_sum
      intro I hI
      apply finite_nonzero_row_energy_le_majorant _ R K hK
      · intro z hz
        rw [←eisEmbedding_norm_sq_eq_absNorm_span]
        exact (mem_firstFrequencyDisk K z).mp (Finset.mem_erase.mp hz).2
      · exact fun z hz=>(Finset.mem_erase.mp hz).1
    _ = _ := by unfold canonicalSmoothedEnergy; rw [Complex.re_sum]

def canonicalLogEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X K : ℝ) : ℝ :=
  canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels (fun S=>V (columnLog p X S)) K

end

def orientedLogProfile (negative : Bool) (V : ℝ → ℂ) : ℝ → ℂ :=
  if negative then fun s=>star (V s) else V

theorem fixedSecondTest_zero_profile {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)
    (V : ℝ → ℂ) (X : ℝ) (negative : Bool) :
    fixedSecondTest p V X 0 0 negative=(fun S=>orientedLogProfile negative V (columnLog p X S)) := by
  funext S
  cases negative <;> simp [fixedSecondTest,orientedLogProfile,JointLogSeparation.fixedColumnTest,FourierBridge.logPhase]

end SecondPassArithmetic

end

end OAI

end Source193

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/CanonicalLogEnergy.lean; sha256: cc7ce1c9b23ad546f7071389ec4db70479cb5a7c22eaa81e041d9a7dbf7a94d3 -/
section Source194
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic ConcreteTraceCRT

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem childEnergy_le_canonicalSmoothed (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ)
    (X K a b : ℝ) (hK : 0<K) (testNegative rowNegative : Bool)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b≤
      6*canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels
        (fixedSecondTest p V X a b testNegative) K := by
  apply idealChildRow_unit_energy_le
  intro u
  exact idealChildRow_energy_le_canonical p hp hcop hg pool Ψ m _ rowNegative u
    T labels K hK hlabels hrows hzero

theorem childEnergy_le_canonicalLogEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ)
    (X K a b : ℝ) (hX : 0<X) (hK : 0<K) (testNegative rowNegative : Bool)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b≤
      6*canonicalLogEnergy p hp hcop hg pool
        (normHeightTwist Ψ (secondSignedHeight testNegative a b)) m labels
        (orientedLogProfile testNegative V) X K := by
  rw [childEnergy_normHeight p hp hcop hg pool Ψ m T V X a b hX testNegative rowNegative]
  simpa only [canonicalLogEnergy,fixedSecondTest_zero_profile] using
    childEnergy_le_canonicalSmoothed p hp hcop hg pool
      (normHeightTwist Ψ (secondSignedHeight testNegative a b)) m T labels V X K 0 0 hK
      testNegative rowNegative hlabels hrows hzero

theorem childEnergy_le_canonicalLogEnergy_actual_labels (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V : ℝ → ℂ)
    (X K a b : ℝ) (hX : 0<X) (hK : 0<K) (testNegative rowNegative : Bool)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b≤
      6*canonicalLogEnergy p hp hcop hg pool
        (normHeightTwist Ψ (secondSignedHeight testNegative a b)) m (T.image Prod.fst)
        (orientedLogProfile testNegative V) X K :=
  childEnergy_le_canonicalLogEnergy p hp hcop hg pool Ψ m T (T.image Prod.fst) V X K a b hX hK
    testNegative rowNegative (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩) hrows hzero

end SecondPassIntegration

namespace CanonicalRowCompletion

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem fixedChildRow_coefficient_expansion
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι → ℂ) :
    fixedChildRow p hp hcop hg pool Ψ m H f z =
      ∑ T ∈ pool.powerset,
        canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z * H T := by
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro T hT
  simp only [secondChildColumn, canonicalSourceCoefficient]
  ring

theorem reopenedCanonicalRow_integrand
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι → ℂ) :
    reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f H z =
      ∑ v ∈ Q, ∑ T ∈ pool.powerset,
        β v * (multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
          canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z) * H T := by
  unfold reopenedCanonicalRow
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro T hT
  simp only [canonicalSourceCoefficient]
  ring

theorem canonical_bin_separation
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀ v ∈ Q, B ≤ n v) (hn' : ∀ v ∈ Q, n v ≤ Real.exp 1*B) :
    (∑ v ∈ Q, (β v * (n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹) *
      multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      fixedChildRow p hp hcop hg pool Ψ m
        (fun T => W (primeProductNorm p T/(X/(n v)^3))) f z) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          reopenedCanonicalRow p hp hcop hg pool Q
            (separatedCubeCoefficient β n B ξ) Ψ m f
            (fun T => frequencyTwist V ξ (columnLog p ell T)) z := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z
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
      rw [reopenedCanonicalRow_integrand p hp hcop hg]
      rfl

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

theorem cube_coefficient_restore (H₀ : ℝ) (Ψ : ActualEisensteinCubic.O →* ℂ) (I : Ideal ActualEisensteinCubic.O)
    (hI : I ≠ 0) :
    reopenedCubeCoefficient H₀ Ψ I * (Ideal.absNorm I : ℂ)⁻¹ =
      largeCubeCoefficient H₀ I * cubeWeight Ψ I := by
  have hN : (Ideal.absNorm I : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (norm_at_least_one I hI)))
  unfold reopenedCubeCoefficient cubePhase
  field_simp

theorem cubeIdeal_row (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀ I ∈ F, Admissible I)
    (v : primePool F →₀ ℕ) (z : ActualEisensteinCubic.O) :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealRowHom z (cubeIdeal F v) =
      multiplicityRow (fun i => Ideal.span {poolPrimary F i}) (poolPrimary_good F hF)
        Finset.univ v z := by
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hprod : cubeIdeal F v = ∏ i : primePool F, (Ideal.span {poolPrimary F i}) ^ v i := by
    unfold cubeIdeal
    exact Finset.prod_congr rfl (fun i _ => by rw [poolPrimary_span F hF i])
  rw [hprod, idealRowHom_prime_powers]

def outsideCanonicalBin (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (X H₀ : ℝ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  ∑ v ∈ Q,
    (largeCubeCoefficient H₀ (cubeIdeal F v) *
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) *
      (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v) : ℝ)^3) : ℂ)⁻¹) *
      idealRowHom z (cubeIdeal F v)^3 *
      outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm (cubeIdeal F v) : ℝ)^3)

theorem outsideCanonicalBin_separated
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X H₀ : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀ v ∈ Q, B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun v => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    outsideCanonicalBin S D hbad Q Ψ m f z W X H₀ =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF)
            (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
            (separatedCubeCoefficient β n B ξ) Ψ m f
            (fun T => frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z := by
  dsimp only
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  let β := fun v => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
  let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
  rw [← canonical_bin_separation (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) W a b ha hs hW V hV
    Finset.univ Q β n Ψ m f z B ell X hB hell hX hn hn']
  unfold outsideCanonicalBin
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [cubeIdeal_row F hF v z]
  have hc := cube_coefficient_restore H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
    (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  change _ = (β v * (n v : ℂ)⁻¹ * _) * _ * _
  have hc' : β v * (n v : ℂ)⁻¹ =
      largeCubeCoefficient H₀ (cubeIdeal F v) *
        cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) := by
    simpa only [β,n,Complex.ofReal_natCast] using hc
  rw [hc']
  rfl

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

theorem fixedChildRow_zero_of_subunit {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hsub : b*X < 1) :
    fixedChildRow p hp hcop hg pool Ψ m
      (fun T => W (primeProductNorm p T/X)) f z = 0 := by
  unfold fixedChildRow
  apply Finset.sum_eq_zero
  intro T hT
  have hw : W (primeProductNorm p T/X) = 0 := by
    by_contra hne
    have hh := (div_le_iff₀ hX).mp (hW _ hne)
    have hone := primeProductNorm_ge_one p hp T
    linarith
  simp only [secondChildColumn,hw,mul_zero]

theorem outsideCanonicalRow_zero_of_subunit
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hsub : b*X < 1) :
    outsideCanonicalRow S D hbad Ψ m f z W X = 0 := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  unfold outsideCanonicalRow
  dsimp only
  exact fixedChildRow_zero_of_subunit _ _ _ _ _ Ψ m f z W b X hX hW hsub

def activeCubeExponents (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ) :
    Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  ((outsideIdealsUpTo S D).image (cubeIndex F)).filter
    (fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)^3 ≤ b*X)

theorem outsideCanonicalBin_eq_active
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (b X H₀ : ℝ)
    (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) :
    outsideCanonicalBin S D hbad
      ((outsideIdealsUpTo S D).image (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      Ψ m f z W X H₀ =
    outsideCanonicalBin S D hbad (activeCubeExponents S D b X) Ψ m f z W X H₀ := by
  unfold outsideCanonicalBin activeCubeExponents
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hlarge : b*X < (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)^3 := by
    exact lt_of_not_ge (fun hh => hn (Finset.mem_filter.mpr ⟨hv,hh⟩))
  have hN : 0 < (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) :=
    lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  have hsub : b*(X/(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)^3) < 1 := by
    rw [← mul_div_assoc]
    exact (div_lt_one (pow_pos hN _)).mpr hlarge
  rw [outsideCanonicalRow_zero_of_subunit S D hbad Ψ m f z W b _
    (div_pos hX (pow_pos hN _)) hW hsub,mul_zero]

theorem outsideCanonicalRow_reopened_active
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    (Real.sqrt X : ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
        outsideCanonicalBin S D hbad (activeCubeExponents S D b X) Ψ m f z W X H₀ := by
  have hh := outsideCanonicalRow_reopened_exponents S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD
  change _ = _ + outsideCanonicalBin S D hbad
    ((outsideIdealsUpTo S D).image (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    Ψ m f z W X H₀ at hh
  rwa [outsideCanonicalBin_eq_active S D hbad Ψ m f z W b X H₀ hX hW] at hh

theorem activeCubeExponents_norm_bound
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeExponents S D b X) :
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ max 1 (b*X) := by
  have hcube := (Finset.mem_filter.mp hv).2
  have hN := norm_at_least_one _ (cubeIdeal_ne_zero (InitialMeanSquare.outsideSquarefreeIdeals S D) v)
  let n := (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)
  have hone : 1 ≤ n := hN
  have hnn : n ≤ n^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hone) (show 0 ≤ n^2+n by positivity)]
  exact (hnn.trans hcube).trans (le_max_right _ _)

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O

def cubeLogIndex (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) : ℕ :=
  normLogBin (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)

def cubeLogRange (b X : ℝ) : Finset ℕ :=
  Finset.range (normLogBin (max 1 (b*X)) + 1)

def activeCubeLogBin (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ) (j : ℕ) :
    Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) :=
  (activeCubeExponents S D b X).filter (fun v => cubeLogIndex S D v = j)

theorem activeCubeLogIndex_mem (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeExponents S D b X) : cubeLogIndex S D v ∈ cubeLogRange b X := by
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact normLogBin_mono
    (lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v)))
    (activeCubeExponents_norm_bound S D b X v hv)

theorem activeCubeLogBin_norms (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ) (j : ℕ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeLogBin S D b X j) :
    normLogScale j ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ∧
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*normLogScale j := by
  have hj := (Finset.mem_filter.mp hv).2
  rw [← hj]
  have hh := normLogBin_scale_bounds
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)
    (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  exact ⟨hh.1,by simpa only [mul_comm,cubeLogIndex] using hh.2⟩

theorem cubeLogRange_card (b X : ℝ) :
    (cubeLogRange b X).card = normLogBin (max 1 (b*X)) + 1 := by
  exact Finset.card_range _

theorem sum_activeCubeLogBins {M : Type*} [AddCommMonoid M]
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ)
    (a : (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) → M) :
    (∑ v ∈ activeCubeExponents S D b X, a v) =
      ∑ j ∈ cubeLogRange b X, ∑ v ∈ activeCubeLogBin S D b X j, a v := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun v hv => activeCubeLogIndex_mem S D b X v hv) a

theorem outsideCanonicalBin_log_bins
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (b X H₀ : ℝ) :
    outsideCanonicalBin S D hbad (activeCubeExponents S D b X) Ψ m f z W X H₀ =
      ∑ j ∈ cubeLogRange b X,
        outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀ := by
  unfold outsideCanonicalBin
  dsimp only
  exact sum_activeCubeLogBins S D b X _

theorem outsideCanonicalRow_reopened_binned
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    (Real.sqrt X : ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
        ∑ j ∈ cubeLogRange b X,
          outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀ := by
  rw [outsideCanonicalRow_reopened_active S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD,
    outsideCanonicalBin_log_bins]

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels

theorem nonzeroRowMajorantSum_exact_disk (P : ActualEisensteinCubic.O → ℂ) (K : ℝ) (hK : 0<K) :
    nonzeroRowMajorantSum P K=
      ∑z∈(firstFrequencyDisk (2*K)).erase 0,
        rowMajorant (‖eisEmbedding z‖^2/K)*(‖P z‖^2:ℝ) := by
  unfold nonzeroRowMajorantSum
  have hz (z : ActualEisensteinCubic.O) (hz : z∉(firstFrequencyDisk (2*K)).erase 0) :
      (if z=0 then 0 else rowMajorant (‖eisEmbedding z‖^2/K)*(‖P z‖^2:ℝ))=0 := by
    by_cases hzero : z=0
    · simp [hzero]
    have hn : z∉firstFrequencyDisk (2*K) := by
      intro hm
      exact hz (Finset.mem_erase.mpr ⟨hzero,hm⟩)
    have hlarge : 2<‖eisEmbedding z‖^2/K :=
      (lt_div_iff₀ hK).mpr (outside_firstFrequencyDisk (2*K) z hn)
    rw [ite_eq_right hzero,rowMajorant_zero _ hlarge,zero_mul]
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro z hz
  rw [ite_eq_right (Finset.mem_erase.mp hz).1]

def canonicalTerminalConstant (A M : ℝ) : ℝ :=
  2*128^4*SchwartzMap.seminorm ℝ 0 0 rowMajorant*(Real.exp A*M)^2

theorem canonicalTerminalConstant_nonneg (A M : ℝ) : 0≤canonicalTerminalConstant A M := by
  unfold canonicalTerminalConstant
  positivity

theorem fixedDepthRank_zero_iff (Z K : ℝ) (hZ : 1<Z) (hK : 0<K) :
    fixedDepthRank Z K=0 ↔ K≤1 := by
  rw [fixedDepthRank,Nat.ceil_eq_zero]
  constructor
  · intro h
    have hm := (div_le_iff₀ (Real.log_pos hZ)).mp h
    apply (Real.log_nonpos_iff hK.le).mp
    nlinarith
  · intro h
    apply (div_le_iff₀ (Real.log_pos hZ)).mpr
    have hm := (Real.log_nonpos_iff hK.le).mpr h
    nlinarith

theorem smallColumn_row_le_label (m : ActualEisensteinCubic.O) (hm : m≠0) (X F K : ℝ)
    (hX : X≤1) (hF : 0≤F) (hK : 0≤K)
    (hinv : K*‖eisEmbedding m‖^2≤X*F) : K≤F := by
  have hn := element_norm_ge_one m hm
  have h1 := mul_le_mul_of_nonneg_left hn hK
  have h2 := mul_le_mul_of_nonneg_right hX hF
  nlinarith

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem canonicalSmoothedEnergy_uniform_row_bound (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (F K D : ℝ)
    (hF : 1≤F) (hK : 1≤K) (_hD : 0≤D)
    (hI0 : ∀I∈labels,I≠⊥) (hIF : ∀I∈labels,(Ideal.absNorm I:ℝ)≤F)
    (hrow : ∀I∈labels,∀z,‖fixedChildRow p hp hcop hg pool Ψ m H
      (ConcretePrimeRowBridge.idealGenerator I) z‖≤D) :
    canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K≤
      2*128^2*SchwartzMap.seminorm ℝ 0 0 rowMajorant*F*K*D^2 := by
  have hK0 : 0<K := zero_lt_one.trans_le hK
  let R := (firstFrequencyDisk (2*K)).erase 0
  have hR : (R.card:ℝ)≤128*(2*K) := by
    apply DescentFiberCost.finite_element_count_real R (2*K) (by linarith)
    exact fun z hz=>(mem_firstFrequencyDisk (2*K) z).mp (Finset.mem_erase.mp hz).2
  have hI : (labels.card:ℝ)≤128*F := DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hm : 0≤SchwartzMap.seminorm ℝ 0 0 rowMajorant := by positivity
  unfold canonicalSmoothedEnergy
  simp_rw [nonzeroRowMajorantSum_exact_disk _ K hK0]
  rw [Complex.re_sum]
  calc
    _ ≤ ∑I∈labels,∑z∈R,SchwartzMap.seminorm ℝ 0 0 rowMajorant*D^2 := by
      apply Finset.sum_le_sum
      intro I hIL
      rw [Complex.re_sum]
      apply Finset.sum_le_sum
      intro z hz
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      exact mul_le_mul
        ((Complex.re_le_norm _).trans (rowMajorant.norm_le_seminorm ℝ _))
        (pow_le_pow_left₀ (norm_nonneg _) (hrow I hIL z) 2) (sq_nonneg _) hm
    _ = (labels.card:ℝ)*R.card*(SchwartzMap.seminorm ℝ 0 0 rowMajorant*D^2) := by simp; ring
    _ ≤ (128*F)*(128*(2*K))*(SchwartzMap.seminorm ℝ 0 0 rowMajorant*D^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hI hR (Nat.cast_nonneg _) (by linarith)) (by positivity)
    _ = _ := by ring

theorem canonicalLogEnergy_subunit (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X K A : ℝ) (hX : 0<X)
    (hV : ∀s,V s≠0→|s|≤A) (hsmall : X*Real.exp A<1) :
    canonicalLogEnergy p hp hcop hg pool Ψ m labels V X K=0 := by
  have hcol (S : Finset ι) : V (columnLog p X S)=0 := by
    by_contra hn
    have hupper := columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hV _ hn))
    have hlower := primeProductNorm_ge_one p hp S
    linarith
  have hrow (f y : ActualEisensteinCubic.O) : fixedChildRow p hp hcop hg pool Ψ m
      (fun S=>V (columnLog p X S)) f y=0 := by
    unfold fixedChildRow
    apply Finset.sum_eq_zero
    intro S hS
    simp only [secondChildColumn,hcol,mul_zero]
  simp only [canonicalLogEnergy,canonicalSmoothedEnergy,nonzeroRowMajorantSum,hrow,norm_zero,
    zero_pow (by decide : (2:ℕ)≠0),Complex.ofReal_zero,mul_zero,ite_self,tsum_zero,
    Finset.sum_const_zero,Complex.zero_re]

theorem canonicalLogEnergy_terminal
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X F K A M : ℝ)
    (hX : 0<X) (hF : 1≤F) (hK : 1≤K) (hKF : K≤F) (hM : 0≤M)
    (hV : ∀s,‖V s‖≤M) (hVs : ∀s,V s≠0→|s|≤A)
    (hI0 : ∀I∈labels,I≠⊥) (hIF : ∀I∈labels,(Ideal.absNorm I:ℝ)≤F) :
    canonicalLogEnergy p hp hcop hg pool Ψ m labels V X K≤canonicalTerminalConstant A M*(X*F)^2 := by
  by_cases hscale : 1≤X*Real.exp A
  · have hcol : ∀S,V (columnLog p X S)≠0→primeProductNorm p S≤X*Real.exp A :=
      fun S hn=>columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hVs _ hn))
    have hrow (I : Ideal ActualEisensteinCubic.O) (hI : I∈labels) (z : ActualEisensteinCubic.O) :
        ‖fixedChildRow p hp hcop hg pool Ψ m (fun S=>V (columnLog p X S))
          (ConcretePrimeRowBridge.idealGenerator I) z‖≤128*(X*Real.exp A)*M :=
      fixedChildRow_elementary p hp hcop hg hc hinj pool Ψ hΨ m _ z _ (X*Real.exp A) M hscale hM
        (fun S=>hV _) hcol
    have hb := canonicalSmoothedEnergy_uniform_row_bound p hp hcop hg pool Ψ m labels
      (fun S=>V (columnLog p X S)) F K (128*(X*Real.exp A)*M) hF hK (by positivity) hI0 hIF hrow
    change canonicalLogEnergy p hp hcop hg pool Ψ m labels V X K≤_ at hb
    calc
      _ ≤ 2*128^2*SchwartzMap.seminorm ℝ 0 0 rowMajorant*F*K*(128*(X*Real.exp A)*M)^2 := hb
      _ = canonicalTerminalConstant A M*X^2*F*K := by unfold canonicalTerminalConstant; ring
      _ ≤ canonicalTerminalConstant A M*X^2*F*F :=
        mul_le_mul_of_nonneg_left hKF (by have := canonicalTerminalConstant_nonneg A M; positivity)
      _ = _ := by ring
  · rw [canonicalLogEnergy_subunit p hp hcop hg pool Ψ m labels V X K A hX hVs (lt_of_not_ge hscale)]
    exact mul_nonneg (canonicalTerminalConstant_nonneg A M) (sq_nonneg _)

end SecondPassArithmetic

end

end OAI

end Source194

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/RadialProfiles.lean; sha256: a5924a8c9d2c3c82262a8d694e5501231bb076cf3ec7096849b1b157e31622f1 -/
section Source195
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter

def positiveRadialProfile (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0<x then V (Real.log x) else 0

theorem positiveRadialProfile_support (V : ℝ → ℂ) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (x : ℝ) (hx : positiveRadialProfile V x≠0) :
    x∈Set.Icc (Real.exp (-A)) (Real.exp A) := by
  have hpos : 0<x := by
    by_contra hn
    exact hx (by simp [positiveRadialProfile,hn])
  have hlog : |Real.log x|≤A := hV _ (by simpa [positiveRadialProfile,hpos] using hx)
  constructor
  · calc
      Real.exp (-A) ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (abs_le.mp hlog).1
      _ = x := Real.exp_log hpos
  · calc
      x = Real.exp (Real.log x) := (Real.exp_log hpos).symm
      _ ≤ Real.exp A := Real.exp_le_exp.mpr (abs_le.mp hlog).2

theorem positiveRadialProfile_compact (V : ℝ → ℂ) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) : HasCompactSupport (positiveRadialProfile V) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (fun x hx=>positiveRadialProfile_support V A hV x hx)

theorem positiveRadialProfile_smooth (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V)
    (A : ℝ) (hV : ∀s,V s≠0→|s|≤A) : ContDiff ℝ ∞ (positiveRadialProfile V) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hpos : 0<x
  · have he : positiveRadialProfile V =ᶠ[𝓝 x] (fun y=>V (Real.log y)) := by
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      change 0<y at hy
      simp only [positiveRadialProfile,ite_eq_left hy]
    exact (hVs.contDiffAt.comp x (Real.contDiffAt_log.mpr hpos.ne')).congr_of_eventuallyEq he
  · have hx : x<Real.exp (-A) := (le_of_not_gt hpos).trans_lt (Real.exp_pos _)
    have he : positiveRadialProfile V =ᶠ[𝓝 x] (fun _=>0) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      by_contra hn
      have hb := (positiveRadialProfile_support V A hV y hn).1
      exact (not_le_of_gt hy) hb
    exact (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq he

def radialFromLog (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) : 𝓢(ℝ,ℂ) :=
  (positiveRadialProfile_compact V A hV).toSchwartzMap (positiveRadialProfile_smooth V hVs A hV)

@[simp] theorem radialFromLog_apply_pos (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (x : ℝ) (hx : 0<x) :
    radialFromLog V hVs A hV x=V (Real.log x) := by
  change positiveRadialProfile V x=_
  simp only [positiveRadialProfile,ite_eq_left hx]

theorem radialFromLog_hasCompactSupport (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) : HasCompactSupport (radialFromLog V hVs A hV) :=
  positiveRadialProfile_compact V A hV

theorem radialFromLog_support (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (x : ℝ) (hx : radialFromLog V hVs A hV x≠0) :
    Real.exp (-A)≤x ∧ x≤Real.exp A := positiveRadialProfile_support V A hV x hx

theorem radialFromLog_column {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    (hp : ∀i,p i≠0) (V : ℝ → ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (X : ℝ) (hX : 0<X) (S : Finset ι) :
    radialFromLog V hVs A hV (FirstPassCubeLabels.primeProductNorm p S/X)=
      V (FirstPassCubeLabels.columnLog p X S) :=
  radialFromLog_apply_pos V hVs A hV _ (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp S) hX)

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

def kernelTestPartitionTerm {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
    (f : kernelSmoothTests) (i : ι) : kernelSmoothTests :=
  ⟨fun q => ρ i q • f.1 q,(ρ i).contMDiff.smul f.2.1,
    HasCompactSupport.smul_left (f := fun q => ρ i q) (f' := f.1) f.2.2⟩

lemma kernelTestPartitionTerm_tsupport {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
    (f : kernelSmoothTests) (i : ι) :
    tsupport (kernelTestPartitionTerm ρ f i).1⊆tsupport (ρ i) :=
  tsupport_smul_subset_left _ _

lemma kernelTestPartition_sum {ι : Type*} [Fintype ι]
    (f : kernelSmoothTests)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient (tsupport f.1)) :
    ∑i,kernelTestPartitionTerm ρ f i=f := by
  apply Subtype.ext
  funext q
  simp only [Submodule.coe_sum,Finset.sum_apply,kernelTestPartitionTerm]
  rw [←Finset.sum_smul]
  by_cases hq : q∈tsupport f.1
  · have hs := ρ.sum_eq_one hq
    rw [finsum_eq_sum_of_fintype] at hs
    rw [hs,one_smul]
  · have hz : f.1 q=0 := image_eq_zero_of_notMem_tsupport hq
    rw [hz,smul_zero]

theorem kernelSmoothTest_finite_chart_partition (f : kernelSmoothTests) :
    ∃t : Finset KernelGoodCutoff,∃g : t→kernelSmoothTests,
      (∑i,g i)=f ∧ ∀i,tsupport (g i).1⊆kernelChartCoreImage i.1.1 := by
  obtain ⟨t,ht⟩ := kernelCompact_finite_chart_cover (tsupport f.1) f.2.2
  have hc : tsupport f.1⊆⋃χ : t,kernelChartCoreImage χ.1.1 := by
    intro q hq
    obtain ⟨χ,hχ,hqχ⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact Set.mem_iUnion.mpr ⟨⟨χ,hχ⟩,hqχ⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,SpatialCoordinates)
    (isClosed_tsupport f.1) (fun χ : t => kernelChartCoreImage χ.1.1)
    (fun χ => kernelChartCoreImage_open χ.1.1) hc
  refine ⟨t,kernelTestPartitionTerm ρ f,kernelTestPartition_sum f ρ,fun i => ?_⟩
  exact (kernelTestPartitionTerm_tsupport ρ f i).trans (hρ i)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

namespace CubicEisenstein

def kernelFullCutoffFun (χ : PositiveChartCutoff) (p : EuclideanSpatial) : ℝ :=
  Real.smoothTransition (4*χ.func p-1)

lemma kernelFullCutoffFun_smooth (χ : PositiveChartCutoff) :
    ContDiff ℝ ∞ (kernelFullCutoffFun χ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul χ.smooth).sub contDiff_const)

lemma kernelFullCutoffFun_tsupport (χ : PositiveChartCutoff) :
    tsupport (kernelFullCutoffFun χ)⊆tsupport χ.func := by
  apply closure_mono
  intro p hp
  change kernelFullCutoffFun χ p≠0 at hp
  change χ.func p≠0
  intro hz
  apply hp
  simp only [kernelFullCutoffFun,hz,mul_zero,zero_sub]
  exact Real.smoothTransition.zero_of_nonpos (by norm_num)

lemma kernelFullCutoffFun_compact (χ : PositiveChartCutoff) :
    HasCompactSupport (kernelFullCutoffFun χ) :=
  χ.compact.of_isClosed_subset (isClosed_tsupport _) (kernelFullCutoffFun_tsupport χ)

def kernelFullCutoff (χ : PositiveChartCutoff) : PositiveChartCutoff where
  func := kernelFullCutoffFun χ
  smooth := kernelFullCutoffFun_smooth χ
  compact := kernelFullCutoffFun_compact χ
  positive := (kernelFullCutoffFun_tsupport χ).trans χ.positive

lemma kernelFullCutoff_one (χ : PositiveChartCutoff) (p : EuclideanSpatial)
    (hp : p∈kernelChartCore χ) : (kernelFullCutoff χ).func p=1 := by
  apply Real.smoothTransition.one_of_one_le
  change (1/2 : ℝ)<χ.func p at hp
  linarith

lemma kernelFullCutoff_eventually_one (χ : PositiveChartCutoff) (p : EuclideanSpatial)
    (hp : p∈kernelChartCore χ) : (kernelFullCutoff χ).func =ᶠ[𝓝 p] fun _ => 1 := by
  filter_upwards [(kernelChartCore_open χ).mem_nhds hp] with q hq
  exact kernelFullCutoff_one χ q hq

def kernelCoreLift (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    𝓢(EuclideanSpatial,ℂ) := kernelLocalizedSchwartz (kernelFullCutoff χ) f

lemma kernelCoreLift_eventually_eq (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∈kernelChartCore χ) :
    (kernelCoreLift χ f : EuclideanSpatial→ℂ)=ᶠ[𝓝 p] kernelTestField f := by
  filter_upwards [kernelFullCutoff_eventually_one χ p hp] with q hq
  change (kernelFullCutoff χ).func q • kernelTestField f q=kernelTestField f q
  rw [hq,one_smul]

lemma kernelCoreLift_tsupport_outer (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    tsupport (kernelCoreLift χ f)⊆tsupport χ.func :=
  (kernelLocalizedField_tsupport (kernelFullCutoff χ) f).trans (kernelFullCutoffFun_tsupport χ)

lemma kernelCoreLift_tsupport (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f : kernelSmoothTests) (hf : tsupport f.1⊆kernelChartCoreImage χ) :
    tsupport (kernelCoreLift χ f)⊆kernelChartCore χ := by
  intro p hp
  have houter := kernelCoreLift_tsupport_outer χ f hp
  by_contra hn
  have hfp : kernelEuclideanProjection p∉tsupport f.1 := by
    intro hfp
    obtain ⟨q,hq,heq⟩ := hf hfp
    have hqp := hinj (kernelChartCore_subset χ hq) houter heq
    exact hn (hqp ▸ hq)
  have hc : ContinuousAt kernelEuclideanProjection p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt p (χ.positive houter)).continuousAt
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hfp).comp_tendsto hc
  have hzero : (kernelCoreLift χ f : EuclideanSpatial→ℂ)=ᶠ[𝓝 p] 0 := by
    filter_upwards [hz] with q hq
    change (kernelFullCutoff χ).func q • f.1 (kernelEuclideanProjection q)=0
    change f.1 (kernelEuclideanProjection q)=0 at hq
    rw [hq,smul_zero]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hp

lemma kernelCoreLift_eq_on_outer (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f : kernelSmoothTests) (hf : tsupport f.1⊆kernelChartCoreImage χ) :
    Set.EqOn (kernelCoreLift χ f) (kernelTestField f) (tsupport χ.func) := by
  intro p hp
  by_cases hc : p∈kernelChartCore χ
  · exact (kernelCoreLift_eventually_eq χ f p hc).self_of_nhds
  · have hz : kernelTestField f p=0 := by
      change f.1 (kernelEuclideanProjection p)=0
      apply image_eq_zero_of_notMem_tsupport
      intro hfp
      obtain ⟨q,hq,heq⟩ := hf hfp
      have hqp := hinj (kernelChartCore_subset χ hq) hp heq
      exact hc (hqp ▸ hq)
    change (kernelFullCutoff χ).func p • kernelTestField f p=kernelTestField f p
    rw [hz,smul_zero]

def euclideanHeightCLM : EuclideanSpatial→L[ℝ]ℂ :=
  Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2)

lemma euclideanHeightCLM_apply (p : EuclideanSpatial) : euclideanHeightCLM p=(p 2:ℂ) := rfl

lemma upperHeightDivide_smooth (f : 𝓢(EuclideanSpatial,ℂ))
    (hpos : tsupport f⊆euclideanUpperHalf) :
    ContDiff ℝ ∞ (fun p : EuclideanSpatial => f p/(p 2:ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p 2=0
  · have hn : p∉tsupport f := by
      intro hf
      have hh := hpos hf
      change 0<p 2 at hh
      linarith
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : EuclideanSpatial => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [hz] with q hq
    simp only [hq,Pi.zero_apply,zero_div]
  · simpa only [div_eq_mul_inv,Pi.inv_apply,euclideanHeightCLM_apply] using
      (f.smooth ⊤).contDiffAt.mul (euclideanHeightCLM.contDiff.contDiffAt.fun_inv
        (Complex.ofReal_ne_zero.mpr hp))

lemma upperHeightDivide_compact (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) :
    HasCompactSupport (fun p : EuclideanSpatial => f p/(p 2:ℂ)) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hcompact ⊢
  exact hcompact.mono (fun p hp => by simp only [hp,Pi.zero_apply,zero_div])

def upperHeightDivide (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    𝓢(EuclideanSpatial,ℂ) :=
  (upperHeightDivide_compact f hcompact).toSchwartzMap (upperHeightDivide_smooth f hpos)

lemma upperHeightDivide_apply (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf)
    (p : EuclideanSpatial) : upperHeightDivide f hcompact hpos p=f p/(p 2:ℂ) := rfl

lemma upperHeightDivide_tsupport (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    tsupport (upperHeightDivide f hcompact hpos)⊆tsupport f := by
  apply closure_mono
  intro p hp
  change f p/(p 2:ℂ)≠0 at hp
  change f p≠0
  exact fun hz => hp (by rw [hz,zero_div])

lemma upperHeightDivide_lineDeriv (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf)
    (p u : EuclideanSpatial) (hp : p 2≠0) :
    (∂_{u} (upperHeightDivide f hcompact hpos)) p=
      ((∂_{u} f) p*(p 2:ℂ)-f p*(u 2:ℂ))/(p 2:ℂ)^2 := by
  have hf := (f.hasFDerivAt p).hasLineDerivAt u
  have hv := (euclideanHeightCLM.hasFDerivAt (x := p)).hasLineDerivAt u
  change HasDerivAt (fun t : ℝ => f (p+t•u)) ((∂_{u} f) p) 0 at hf
  change HasDerivAt (fun t : ℝ => ((p+t•u) 2:ℂ)) (u 2:ℂ) 0 at hv
  have hd := hf.div hv (by simpa using Complex.ofReal_ne_zero.mpr hp)
  have hline : HasLineDerivAt ℝ (upperHeightDivide f hcompact hpos)
      (((∂_{u} f) p*(p 2:ℂ)-f p*(u 2:ℂ))/(p 2:ℂ)^2) p u := by
    simpa only [HasLineDerivAt,upperHeightDivide_apply,Pi.div_apply,zero_smul,add_zero] using! hd
  exact ((upperHeightDivide f hcompact hpos).hasFDerivAt p).hasLineDerivAt u |>.unique hline

lemma upperSchwartz_derivative_compact (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (u : EuclideanSpatial) :
    HasCompactSupport (∂_{u} f : 𝓢(EuclideanSpatial,ℂ)) :=
  hcompact.fderiv_apply ℝ u

def upperWeightedPartial (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) (j : Fin 3) :
    𝓢(EuclideanSpatial,ℂ) :=
  upperHeightDivide (∂_{euclideanCoordinateVector j} f)
    (upperSchwartz_derivative_compact f hcompact _)
    ((SchwartzMap.tsupport_lineDerivOp_subset _ f).trans hpos)

def upperWeightedDivergence (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    𝓢(EuclideanSpatial,ℂ) :=
  -∑j : Fin 3,∂_{euclideanCoordinateVector j} (upperWeightedPartial f hcompact hpos j)

def complexHermitianBilin : ℂ→L[ℝ]ℂ→L[ℝ]ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp Complex.conjCLE.toContinuousLinearMap

lemma schwartz_hermitian_integrable (f g : 𝓢(EuclideanSpatial,ℂ)) :
    Integrable (fun p => star (f p)*g p) volume :=
  (SchwartzMap.bilinLeftCLM complexHermitianBilin g.hasTemperateGrowth f).integrable

lemma schwartz_hermitian_lineGreen (f g : 𝓢(EuclideanSpatial,ℂ)) (u : EuclideanSpatial) :
    (∫p,star (f p)*(∂_{u} g) p)=-∫p,star ((∂_{u} f) p)*g p :=
  SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left f g complexHermitianBilin u

lemma upperWeighted_green (f g : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    (∫p,∑j : Fin 3,star (upperWeightedPartial f hcompact hpos j p)*
      (∂_{euclideanCoordinateVector j} g) p)=
      ∫p,star (upperWeightedDivergence f hcompact hpos p)*g p := by
  calc
    _ = ∑j : Fin 3,∫p,star (upperWeightedPartial f hcompact hpos j p)*
        (∂_{euclideanCoordinateVector j} g) p :=
      integral_finsetSum _ (fun j hj => schwartz_hermitian_integrable _ _)
    _ = -∑j : Fin 3,∫p,star ((∂_{euclideanCoordinateVector j}
        (upperWeightedPartial f hcompact hpos j)) p)*g p := by
      simp only [schwartz_hermitian_lineGreen,Finset.sum_neg_distrib]
    _ = _ := by
      rw [←integral_finsetSum _ (fun j hj => schwartz_hermitian_integrable _ _),←integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        simp only [upperWeightedDivergence,_root_.neg_apply,_root_.sum_apply,star_neg,star_sum,
          Finset.sum_mul,neg_mul])

def upperPositiveLaplacian (f : 𝓢(EuclideanSpatial,ℂ)) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,(∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} f)) p)+
    (p 2:ℂ)*(∂_{euclideanCoordinateVector 2} f) p

lemma upperWeightedDivergence_apply_ne_zero (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf)
    (p : EuclideanSpatial) (hp : p 2≠0) :
    upperWeightedDivergence f hcompact hpos p=upperPositiveLaplacian f p/(p 2:ℂ)^3 := by
  have hd (j : Fin 3) : (∂_{euclideanCoordinateVector j} (upperWeightedPartial f hcompact hpos j)) p=
      ((∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} f)) p*(p 2:ℂ)-
        (∂_{euclideanCoordinateVector j} f) p*(euclideanCoordinateVector j 2:ℂ))/(p 2:ℂ)^2 :=
    upperHeightDivide_lineDeriv _ _ _ p _ hp
  simp only [upperWeightedDivergence,Fin.sum_univ_three,_root_.neg_apply,_root_.add_apply]
  rw [hd 0,hd 1,hd 2]
  simp only [upperPositiveLaplacian,Fin.sum_univ_three]
  norm_num [euclideanCoordinateVector]
  field_simp [Complex.ofReal_ne_zero.mpr hp]
  ring

lemma upperWeightedDivergence_apply (f : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf)
    (p : EuclideanSpatial) :
    upperWeightedDivergence f hcompact hpos p=upperPositiveLaplacian f p/(p 2:ℂ)^3 := by
  by_cases hp : p 2=0
  · have hz : ∀j : Fin 3,(∂_{euclideanCoordinateVector j}
        (upperWeightedPartial f hcompact hpos j)) p=0 := by
      intro j
      have hn : p∉tsupport (upperWeightedPartial f hcompact hpos j) := by
        intro hm
        have ht := hpos ((SchwartzMap.tsupport_lineDerivOp_subset _ f)
          (upperHeightDivide_tsupport _ _ _ hm))
        change 0<p 2 at ht
        linarith
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,fderiv_of_notMem_tsupport ℝ hn]
      rfl
    simp only [upperWeightedDivergence,_root_.neg_apply,_root_.sum_apply,hz,Finset.sum_const_zero,neg_zero,
      upperPositiveLaplacian,hp,Complex.ofReal_zero,zero_pow (by decide : 2≠0),
      zero_pow (by decide : 3≠0),zero_mul,zero_add,zero_div]
  · exact upperWeightedDivergence_apply_ne_zero f hcompact hpos p hp

theorem upperHyperbolic_green (f g : 𝓢(EuclideanSpatial,ℂ))
    (hcompact : HasCompactSupport f) (hpos : tsupport f⊆euclideanUpperHalf) :
    (∫p,∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} f) p)*
      (∂_{euclideanCoordinateVector j} g) p/(p 2:ℂ))=
      ∫p,star (upperPositiveLaplacian f p)*g p/(p 2:ℂ)^3 := by
  have hh := upperWeighted_green f g hcompact hpos
  simpa only [upperWeightedPartial,upperHeightDivide_apply,upperWeightedDivergence_apply,
    star_div₀,star_pow,Complex.star_def,Complex.conj_ofReal,div_mul_eq_mul_div] using hh

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

namespace CubicEisenstein

lemma kernelEuclideanProjection_integral_complex (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient→ℂ)
    (hg : AEStronglyMeasurable g (integralQuotientVolume globalKubotaKernel)) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)=
      ∫q in kernelEuclideanProjection '' S,g q∂integralQuotientVolume globalKubotaKernel := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hh := hg.mono_measure (Measure.restrict_le_self (s := kernelEuclideanProjection '' S))
  rw [←hm.map_eq] at hh ⊢
  exact (integral_map hm.measurable.aemeasurable hh).symm

lemma hyperbolicEuclidean_setIntegral_complex (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf) (g : EuclideanSpatial→ℂ) :
    (∫p in S,g p∂hyperbolicEuclideanVolume)=∫p in S,g p/(p 2:ℂ)^3 := by
  rw [hyperbolicEuclideanVolume,MeasureTheory.restrict_withDensity hS,
    Measure.restrict_restrict hS,Set.inter_eq_left.mpr hpos,
    integral_withDensity_eq_integral_toReal_smul hyperbolicDensity_measurable
      (Eventually.of_forall (fun p => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hS] with p hp
  have hpositive : 0<p 2 := hpos hp
  rw [hyperbolicDensity,ENNReal.toReal_ofReal (by positivity)]
  rw [Complex.real_smul]
  change (↑(((p 2)^3)⁻¹) : ℂ)*g p=g p/(p 2:ℂ)^3
  simp only [Complex.ofReal_inv,Complex.ofReal_pow,div_eq_mul_inv,mul_comm]

lemma kernelDirichletPairDensity_zero_of_notMem (f g : kernelSmoothTests) (q : KernelQuotient)
    (hq : q∉tsupport g.1) : kernelDirichletPairDensity f g q=0 := by
  have hz : kernelQuotientEnergyDensity g q=0 := by
    by_contra hn
    exact hq (kernelQuotientEnergyDensity_support g hn)
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)=0
    rw [kernelDirichletPairDensity_coordinate]
    have hg : kernelGradientAt w g=0 := by
      apply norm_eq_zero.mp
      have h := kernelGradientAt_norm_sq w g
      change kernelTestEnergyDensity g w=0 at hz
      rw [hz] at h
      nlinarith [norm_nonneg (kernelGradientAt w g)]
    rw [hg,inner_zero_right]

lemma kernelDirichletPairDensity_euclidean (f g : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    kernelDirichletPairDensity f g (kernelEuclideanProjection p)=
      (p 2:ℂ)^2*∑j : Fin 3,star (fderiv ℝ (kernelTestField f) p (euclideanCoordinateVector j))*
        fderiv ℝ (kernelTestField g) p (euclideanCoordinateVector j) := by
  have hc := hyperbolicEuclideanCoordinates_toHyperbolic p hp
  have hv : hyperbolicHeight (euclideanToHyperbolic p)=p 2 := congrArg (fun q : EuclideanSpatial => q 2) hc
  change kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic p))=_
  rw [kernelDirichletPairDensity_coordinate,PiLp.inner_apply]
  change (∑j : Fin 3,inner ℂ ((hyperbolicHeight (euclideanToHyperbolic p):ℂ)*kernelTestPartial f (euclideanToHyperbolic p) j)
    ((hyperbolicHeight (euclideanToHyperbolic p):ℂ)*kernelTestPartial g (euclideanToHyperbolic p) j))=_
  rw [hv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [kernelTestPartial,hc,←euclideanCoordinateVector_eq_basis,RCLike.inner_apply,
    map_mul,Complex.conj_ofReal,Complex.star_def]
  ring

lemma kernelCoreLift_fderiv_eq_on_outer (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f : kernelSmoothTests) (hf : tsupport f.1⊆kernelChartCoreImage χ)
    (p : EuclideanSpatial) (hp : p∈tsupport χ.func) :
    fderiv ℝ (kernelCoreLift χ f) p=fderiv ℝ (kernelTestField f) p := by
  by_cases hc : p∈kernelChartCore χ
  · exact (kernelCoreLift_eventually_eq χ f p hc).fderiv_eq
  · have hl : p∉tsupport (kernelCoreLift χ f) := fun h => hc (kernelCoreLift_tsupport χ hinj f hf h)
    have hfp : kernelEuclideanProjection p∉tsupport f.1 := by
      intro hfp
      obtain ⟨q,hq,heq⟩ := hf hfp
      exact hc ((hinj (kernelChartCore_subset χ hq) hp heq) ▸ hq)
    have hcont : ContinuousAt kernelEuclideanProjection p :=
      (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
        (euclideanToHyperbolic_contMDiffAt p (χ.positive hp)).continuousAt
    have hz : kernelTestField f=ᶠ[𝓝 p]0 := (notMem_tsupport_iff_eventuallyEq.mp hfp).comp_tendsto hcont
    rw [fderiv_of_notMem_tsupport ℝ hl,hz.fderiv_eq,fderiv_zero]
    rfl

lemma kernelCoreLift_pair_on_outer (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ)
    (p : EuclideanSpatial) (hp : p∈tsupport χ.func) :
    kernelDirichletPairDensity f g (kernelEuclideanProjection p)=
      (p 2:ℂ)^2*∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} (kernelCoreLift χ f)) p)*
        (∂_{euclideanCoordinateVector j} (kernelCoreLift χ g)) p := by
  rw [kernelDirichletPairDensity_euclidean f g p (χ.positive hp)]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [←kernelCoreLift_fderiv_eq_on_outer χ hinj g hg p hp]
  by_cases hc : p∈kernelChartCore χ
  · rw [(kernelCoreLift_eventually_eq χ f p hc).fderiv_eq]
  · have hn : p∉tsupport (kernelCoreLift χ g) := fun h => hc (kernelCoreLift_tsupport χ hinj g hg h)
    rw [fderiv_of_notMem_tsupport ℝ hn]
    simp only [_root_.zero_apply,mul_zero,Finset.sum_const_zero]

theorem kernelDirichletForm_eq_chart_pairing (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ) :
    kernelDirichletForm f g=
      ∫p,∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} (kernelCoreLift χ f)) p)*
        (∂_{euclideanCoordinateVector j} (kernelCoreLift χ g)) p/(p 2:ℂ) := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have himg : kernelChartCoreImage χ⊆kernelEuclideanProjection '' S :=
    Set.image_mono (kernelChartCore_subset χ)
  calc
    _ = ∫q in kernelEuclideanProjection '' S,kernelDirichletPairDensity f g q
        ∂integralQuotientVolume globalKubotaKernel := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      exact kernelDirichletPairDensity_zero_of_notMem f g q (fun h => hq (himg (hg h)))
    _ = ∫p in S,kernelDirichletPairDensity f g (kernelEuclideanProjection p)
        ∂hyperbolicEuclideanVolume :=
      (kernelEuclideanProjection_integral_complex S hS χ.positive hinj _
        (kernelDirichletPairDensity_integrable f g).aestronglyMeasurable).symm
    _ = ∫p in S,kernelDirichletPairDensity f g (kernelEuclideanProjection p)/(p 2:ℂ)^3 :=
      hyperbolicEuclidean_setIntegral_complex S hS χ.positive _
    _ = ∫p in S,∑j : Fin 3,star ((∂_{euclideanCoordinateVector j} (kernelCoreLift χ f)) p)*
        (∂_{euclideanCoordinateVector j} (kernelCoreLift χ g)) p/(p 2:ℂ) := by
      apply setIntegral_congr_fun hS
      intro p hp
      dsimp only
      rw [kernelCoreLift_pair_on_outer χ hinj f g hg p hp,←Finset.sum_div]
      have hv : (p 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (χ.positive hp).ne'
      field_simp [hv]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hn : p∉tsupport (kernelCoreLift χ g) := fun h => hp (kernelCoreLift_tsupport_outer χ g h)
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,fderiv_of_notMem_tsupport ℝ hn,
        _root_.zero_apply,mul_zero,zero_div,Finset.sum_const_zero]

theorem kernelDirichletForm_eq_chart_laplacian (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ) :
    kernelDirichletForm f g=
      ∫p,star (upperPositiveLaplacian (kernelCoreLift χ f) p)*kernelCoreLift χ g p/(p 2:ℂ)^3 := by
  rw [kernelDirichletForm_eq_chart_pairing χ hinj f g hg]
  exact upperHyperbolic_green _ _ (kernelLocalizedField_compact (kernelFullCutoff χ) f)
    ((kernelCoreLift_tsupport_outer χ f).trans χ.positive)

end CubicEisenstein

end

end OAI

end Source195

/- Original source: OAI/NumberTheory/DirichletL/RowCompletion/PolynomialHeight.lean; sha256: e225c890d9f8601b6358ca1158be947ff459a010480fd4f3fc13749c978bebdb -/
section Source196
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalCubeSeparation

theorem outside_separated_cube_coefficient_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (Ψ : ActualEisensteinCubic.O →* ℂ), (∀ z, ‖Ψ z‖ ≤ 1) →
      ∀ (m f : ActualEisensteinCubic.O) (H₀ B ξ : ℝ)
      (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ),
      0 < B →
      B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) →
      (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B →
      ‖separatedCubeCoefficient
        (fun u => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
          (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u))
        (fun u => (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u) : ℝ))
        B ξ v‖ ≤ C*(Real.exp 1*B)^ε := by
  obtain ⟨C,hC,hbound⟩ := reopenedCubeCoefficient_small_power ε hε
  refine ⟨C*Real.exp (1/2),mul_pos hC (Real.exp_pos _),?_⟩
  intro S D Ψ hΨ m f H₀ B ξ v hB hn hn'
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have ht : ∀ z, ‖rowTwist Ψ (m*excludedGenerator S) f 1 z‖ ≤ 1 :=
    rowTwist_norm Ψ hΨ (m*excludedGenerator S) f 1
  have hβ : ‖reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)‖ ≤
      C*(Real.exp 1*B)^ε := by
    apply (hbound H₀ _ ht _ (cubeIdeal_ne_zero F v)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hn' hε.le) hC.le
  have hh := separatedCubeCoefficient_bound
    (fun u => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F u))
    (fun u => (Ideal.absNorm (cubeIdeal F u) : ℝ)) B ξ (C*(Real.exp 1*B)^ε)
    hB (by positivity) v hn hn' hβ
  convert hh using 1 ; ring

end CanonicalRowCompletion

namespace CompletedHeight

open MeasureTheory Filter Set
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
open FourierBridge JointLogSeparation

def positiveCutoff (a b : ℝ) (ha : 0 < a) : ContDiffBump ((a+max a b)/2) where
  rIn := (max a b-a)/2+a/4
  rOut := (max a b-a)/2+a/2
  rIn_pos := by linarith [le_max_left a b]
  rIn_lt_rOut := by linarith

lemma positiveCutoff_one (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x∈Icc a b) :
    positiveCutoff a b ha x=1 := by
  apply (positiveCutoff a b ha).one_of_mem_closedBall
  change dist x ((a+max a b)/2) ≤ (max a b-a)/2+a/4
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith [hx.1,hx.2,le_max_right a b]

lemma positiveCutoff_zero (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < a/2) :
    positiveCutoff a b ha x=0 := by
  by_contra hn
  have hm : x∈Function.support (positiveCutoff a b ha) := hn
  rw [(positiveCutoff a b ha).support_eq] at hm
  change dist x ((a+max a b)/2) < (max a b-a)/2+a/2 at hm
  rw [Real.dist_eq,abs_lt] at hm
  linarith [hm.1]

def logCorrection (a b : ℝ) (ha : 0 < a) (x : ℝ) : ℝ :=
  positiveCutoff a b ha x*(Real.log x-x)

def patchedLog (a b : ℝ) (ha : 0 < a) (x : ℝ) : ℝ := x+logCorrection a b ha x

lemma logCorrection_compact (a b : ℝ) (ha : 0 < a) :
    HasCompactSupport (logCorrection a b ha) := (positiveCutoff a b ha).hasCompactSupport.mul_right

lemma logCorrection_smooth (a b : ℝ) (ha : 0 < a) :
    ContDiff ℝ ∞ (logCorrection a b ha) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x=0
  · subst x
    have he : logCorrection a b ha =ᶠ[𝓝 (0:ℝ)] (fun _=>0) := by
      filter_upwards [isOpen_Iio.mem_nhds (by linarith : (0:ℝ)<a/2)] with y hy
      simp only [logCorrection,positiveCutoff_zero a b ha y hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (positiveCutoff a b ha).contDiff.contDiffAt.mul
      ((Real.contDiffAt_log.mpr hx).sub contDiffAt_id)

lemma patchedLog_temperate (a b : ℝ) (ha : 0 < a) :
    Function.HasTemperateGrowth (patchedLog a b ha) :=
  Function.HasTemperateGrowth.id'.add
    ((logCorrection_compact a b ha).hasTemperateGrowth (logCorrection_smooth a b ha))

lemma patchedLog_proper (a b : ℝ) (ha : 0 < a) :
    ∃k : ℕ, ∃C : ℝ, ∀x : ℝ, ‖x‖ ≤ C*(1+‖patchedLog a b ha x‖)^k := by
  obtain ⟨x₀,hx₀⟩ := (logCorrection_smooth a b ha).continuous.norm.exists_forall_ge_of_hasCompactSupport
    (logCorrection_compact a b ha).norm
  refine ⟨1,‖logCorrection a b ha x₀‖+1,?_⟩
  intro x
  have ht : ‖x‖ ≤ ‖patchedLog a b ha x‖+‖logCorrection a b ha x‖ := by
    simpa only [patchedLog,add_sub_cancel_right] using
      norm_sub_le (patchedLog a b ha x) (logCorrection a b ha x)
  have hb := hx₀ x
  simp only [pow_one]
  nlinarith [norm_nonneg (patchedLog a b ha x),norm_nonneg (logCorrection a b ha x₀)]

lemma patchedLog_eq_log (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x∈Icc a b) :
    patchedLog a b ha x=Real.log x := by
  simp only [patchedLog,logCorrection,positiveCutoff_one a b ha x hx,one_mul]
  ring

def sourceTwistCLM (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a) :
    𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
  ((SchwartzMap.smulLeftCLM ℂ (W : ℝ→ℂ)).restrictScalars ℝ).comp
    (SchwartzMap.compCLM ℝ (patchedLog_temperate a b ha) (patchedLog_proper a b ha))

lemma sourceTwistCLM_apply (W g : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a) (x : ℝ) :
    sourceTwistCLM W a b ha g x = W x*g (patchedLog a b ha x) := by
  change (SchwartzMap.smulLeftCLM ℂ (W : ℝ→ℂ)
    ((SchwartzMap.compCLM ℝ (patchedLog_temperate a b ha) (patchedLog_proper a b ha)) g)) x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply W.hasTemperateGrowth]
  rfl

def normTwistedSource (W : ℝ→ℂ) (t x : ℝ) : ℂ := logPhase t (Real.log x)*W x

lemma normTwistedSource_support (W : ℝ→ℂ) (t : ℝ) :
    Function.support (normTwistedSource W t) ⊆ Function.support W := by
  intro x hx hz
  exact hx (by simp only [normTwistedSource,hz,mul_zero])

theorem frequencyTwist_finite_bound (g : 𝓢(ℝ,ℂ)) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ, ∃C : ℝ, 0 < C ∧ ∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frequencyTwist g t) ≤ C*(1+‖t‖)^n := by
  let n := S.sup Prod.snd
  let c : ℕ×ℕ → ℝ := fun z => (2:ℝ)^z.2*(1+2*Real.pi)^z.2*derivativeSeminormSum g z.1 z.2
  let C := 1+∑z∈S,c z
  have hc : ∀z,0≤c z := fun z => by dsimp [c]; exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
  have hC : 0<C := by dsimp [C]; have := Finset.sum_nonneg (fun z (_ : z∈S) => hc z); linarith
  refine ⟨n,C,hC,?_⟩
  intro t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzC : c z≤C := by
    have hh := Finset.single_le_sum (fun z (_ : z∈S) => hc z) hz
    dsimp [C]
    linarith
  have hzn : z.2≤n := Finset.le_sup hz
  have hh := frequencyTwist_seminorm_polynomial g t z.1 z.2
  exact hh.trans (mul_le_mul hzC (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hzn)
    (by positivity) hC.le)

theorem normTwistedSource_schwartz (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support (W : ℝ→ℂ) ⊆ Icc a b) :
    ∃ G : ℝ→𝓢(ℝ,ℂ), (∀t x,G t x=normTwistedSource W t x) ∧
      (∀S : Finset (ℕ×ℕ), ∃n : ℕ, ∃C : ℝ, 0<C ∧ ∀t : ℝ,
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G t)≤C*(1+‖t‖)^n) := by
  let M := |Real.log a|+|Real.log b|+1
  have hM : 0≤M := by dsimp [M]; positivity
  obtain ⟨v,hvc,hvs,hvone,hvsupp,_⟩ := exists_complex_smooth_cutoff M hM
  let V : 𝓢(ℝ,ℂ) := hvc.toSchwartzMap hvs
  let G : ℝ→𝓢(ℝ,ℂ) := fun t => sourceTwistCLM W a b ha (frequencyTwist V t)
  refine ⟨G,?_,?_⟩
  · intro t x
    rw [show G t x=sourceTwistCLM W a b ha (frequencyTwist V t) x from rfl,
      sourceTwistCLM_apply,frequencyTwist_apply]
    by_cases hx : W x=0
    · simp only [normTwistedSource,hx,zero_mul,mul_zero]
    · have hxi := hs hx
      rw [patchedLog_eq_log a b ha x hxi]
      have hlog : |Real.log x|≤M := by
        have hlo := Real.log_le_log ha hxi.1
        have hhi := Real.log_le_log (lt_of_lt_of_le ha hxi.1) hxi.2
        rw [abs_le]
        constructor <;> dsimp [M] <;> linarith [neg_abs_le (Real.log a),le_abs_self (Real.log b),
          abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
      have hv : V (Real.log x)=1 := hvone _ hlog
      simp only [hv,mul_one,normTwistedSource]
      ring
  · intro S
    obtain ⟨s,C,hC,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
      (sourceTwistCLM W a b ha) S
    obtain ⟨n,D,hD,hbound⟩ := frequencyTwist_finite_bound V s
    refine ⟨n,C*D,mul_pos hC hD,?_⟩
    intro t
    exact (hcontrol _).trans ((mul_le_mul_of_nonneg_left (hbound t) hC.le).trans_eq (by ring))

end CompletedHeight

namespace LocalLogFourier

open MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
theorem coupled_positive_log_separation_linear_constant
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : ℝ → ℂ),
      ContDiffOn ℝ ∞ F (Set.Ioi 0) → ∀ CF : ℝ, 0 ≤ CF →
      (∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ x : ℝ, 0 < x →
        (1 + x)^A * ‖eulerDeriv F i x‖ ≤ CF) →
      ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C * CF ∧
        (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C * CF) := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J + (volume : Measure ℝ).integrablePower
  let Lwin : ℝ := T + 1
  let m : ℝ := Real.exp (-Lwin)
  have hL : 0 ≤ Lwin := by dsimp [Lwin]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -Lwin ≤ 0 by linarith))
  obtain ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let P₀ : ℝ := momentConstant K Lwin CW 1
  let B₀ : ℝ := (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 P₀ +
    FourierBridge.coefficientMomentBound J P₀)
  let D₀ : ℝ := FourierBridge.fourierPointBound J P₀
  let C₀ : ℝ := (B₀+D₀)/m^A
  have hP₀ : 0 ≤ P₀ := momentConstant_nonneg K Lwin CW 1 hL hCW zero_le_one
  have hB₀ : 0 ≤ B₀ := by
    dsimp [B₀]
    exact mul_nonneg (by positivity) (add_nonneg
      (FourierBridge.coefficientMomentBound_nonneg 0 P₀ hP₀)
      (FourierBridge.coefficientMomentBound_nonneg J P₀ hP₀))
  have hD₀ : 0 ≤ D₀ := FourierBridge.fourierPointBound_nonneg J P₀ hP₀
  refine ⟨C₀,by dsimp [C₀]; positivity,?_⟩
  intro F hFpos CF hCF hEuler
  let P : ℝ := momentConstant K Lwin CW CF
  let B : ℝ := (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 P +
    FourierBridge.coefficientMomentBound J P)
  let Bpoint : ℝ := FourierBridge.fourierPointBound J P
  have hP : 0 ≤ P := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  have hPeq : P=P₀*CF := by
    dsimp [P,P₀]
    unfold momentConstant derivativeConstant
    simp only [Finset.sum_mul,Finset.mul_sum,mul_one]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hBeq : B=B₀*CF := by
    dsimp [B,B₀]
    rw [hPeq]
    unfold FourierBridge.coefficientMomentBound
    ring
  have hBpeq : Bpoint=D₀*CF := by
    dsimp [Bpoint,D₀]
    rw [hPeq]
    unfold FourierBridge.fourierPointBound FourierBridge.fourierSeminormBound
    ring
  intro R hR
  let b : 𝓢(ℝ, ℂ) := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      FourierBridge.coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_positive_log_separation W F V R a y
      hVc hVs hFpos hR hactive
  · exact AnalyticBridge.schwartz_fourier_one_plus_integrable
      (positiveLogProfile V F R hVc hVs hFpos hR) J
  · have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hbound := positive_log_fourier_bound V F R m Lwin CW CF A J
      hVc hVs hFpos hR hm hm1 hL hCW hCF
      (by simpa [K] using hVderiv)
      (by simpa only [K] using hwindow')
      (by simpa [K] using hEuler)
    have hb : (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ B / m ^ A := by
      simpa [B, P, b, K, Lwin, m] using hbound
    apply hb.trans
    rw [hBeq]
    dsimp [C₀]
    have hh := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD₀ : B₀≤B₀+D₀) hCF
    exact (div_le_div_of_nonneg_right hh (by positivity)).trans_eq (by ring)
  · intro t
    let g := positiveLogProfile V F R hVc hVs hFpos hR
    have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hsource (n : ℕ) (hn : n ≤ J) :
        (m ^ A * (1 + R) ^ A) *
          ((SchwartzMap.seminorm ℝ 0 n) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g) ≤ P := by
      apply positive_log_source_pair V F R m Lwin CW CF P A K n
        hVc hVs hFpos hR hm hm1 hL hCW hCF
      · dsimp [K]; omega
      · exact hVderiv
      · exact hwindow'
      · exact hEuler
      · intro i hi
        exact momentConstant_dominates K i Lwin CW CF hL hCW hCF hi
    have hpoint := FourierBridge.uniform_fourier_pointwise g J
      (m ^ A * (1 + R) ^ A) P (by positivity) hP hsource t
    have hb : (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ Bpoint / m ^ A := by
      apply (le_div_iff₀ (pow_pos hm A)).mpr
      simpa only [g, b, Bpoint, mul_assoc, mul_left_comm, mul_comm] using hpoint
    apply hb.trans
    rw [hBpeq]
    dsimp [C₀]
    have hh := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB₀ : D₀≤B₀+D₀) hCF
    exact (div_le_div_of_nonneg_right hh (by positivity)).trans_eq (by ring)

end LocalLogFourier

namespace CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open CompletedGauss

def HasPolynomialKernel (P : ℝ→ℝ→ℂ) : Prop :=
  (∀t,ContDiffOn ℝ ∞ (CubicReflectionKernel.paperKernel (Vstar (P t))) (Set.Ioi 0)) ∧
  ∀ A K : ℕ,∃n : ℕ,∃C : ℝ,0<C ∧ ∀t : ℝ,∀i≤K,∀x : ℝ,0<x →
    (1+x)^A*‖LocalLogFourier.eulerDeriv (CubicReflectionKernel.paperKernel (Vstar (P t))) i x‖≤
      C*(1+‖t‖)^n

theorem normTwistedSource_polynomial_kernel (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    HasPolynomialKernel (normTwistedSource W) := by
  let S := vstarSchwartz W a b ha hsupp hW
  have hS : Function.support (S : ℝ→ℂ) ⊆ Set.Icc a b := Vstar_support W a b hsupp
  obtain ⟨G,hG,hbound⟩ := normTwistedSource_schwartz S a b ha hS
  have hlink (t : ℝ) : (G t : ℝ→ℂ)=Vstar (normTwistedSource W t) := by
    funext x
    rw [hG t x]
    change FourierBridge.logPhase t (Real.log x)*((Real.sqrt x:ℂ)*W x)=
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase t (Real.log x)*W x)
    ring
  have hGs (t : ℝ) : Function.support (G t : ℝ→ℂ)⊆Set.Icc a b := by
    intro x hx
    change G t x≠0 at hx
    rw [hG t x] at hx
    exact hS (normTwistedSource_support S t hx)
  constructor
  · intro t
    rw [←hlink t]
    exact CubicReflectionKernel.paperKernel_compact_source_smooth (G t) a b ha (hGs t) ((G t).smooth ⊤)
  · intro A K
    obtain ⟨s,D,hD,hkernel⟩ := CubicReflectionKernel.paperKernel_euler_source_uniform_weighted_bound a b ha A K
    obtain ⟨n,C,hC,hsource⟩ := hbound s
    refine ⟨n,D*C,mul_pos hD hC,?_⟩
    intro t i hi x hx
    rw [←hlink t]
    exact (hkernel (G t) (hGs t) i hi x hx).trans
      ((mul_le_mul_of_nonneg_left (hsource t) hD.le).trans_eq (by ring))

theorem polynomial_kernel_log_separation {ι : Type*} [Fintype ι]
    (P : ℝ→ℝ→ℂ) (hP : HasPolynomialKernel P)
    (V : ι→ℝ→ℂ) (slope M : ι→ℝ) (hM : ∀i,0≤M i)
    (hV : ∀i y,V i y≠0 → |y|≤M i) (A J : ℕ) :
    ∃n : ℕ,∃C : ℝ,0≤C ∧ ∀θ R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀y : ι→ℝ,(∏i,V i (y i))*CubicReflectionKernel.paperKernel (Vstar (P θ))
          (R*Real.exp (∑i,slope i*y i))=
        ∫t : ℝ,(∏i,V i (y i)*FourierBridge.logPhase t (slope i*y i))*B t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖B t‖) ∧
      (1+R)^A*(∫t : ℝ,(1+‖t‖)^J*‖B t‖)≤C*(1+‖θ‖)^n ∧
      (∀t : ℝ,(1+R)^A*(1+‖t‖)^J*‖B t‖≤C*(1+‖θ‖)^n) := by
  obtain ⟨n,D,hD,hkernel⟩ := hP.2 A (J+(volume : Measure ℝ).integrablePower)
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    V slope M hM hV A J
  refine ⟨n,C*D,mul_nonneg hC hD.le,?_⟩
  intro θ R hR
  obtain ⟨B,hB,hi,hb,hp⟩ := hsep (CubicReflectionKernel.paperKernel (Vstar (P θ))) (hP.1 θ)
    (D*(1+‖θ‖)^n) (by positivity) (hkernel θ) R hR
  refine ⟨B,hB,hi,?_,?_⟩
  · exact hb.trans_eq (by ring)
  · intro t
    exact (hp t).trans_eq (by ring)

theorem polynomial_kernel_three_window
    (P : ℝ→ℝ→ℂ) (hP : HasPolynomialKernel P)
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂) (A : ℕ) :
    ∃n : ℕ,∃C : ℝ,0≤C ∧ ∀θ R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀r u v : ℝ,V₀ r*V₁ u*V₂ v*CubicReflectionKernel.paperKernel (Vstar (P θ))
        (R*Real.exp (-2*r+u+3*v))=
        ∫t : ℝ,(V₀ r*FourierBridge.logPhase t (-2*r))*
          (V₁ u*FourierBridge.logPhase t u)*(V₂ v*FourierBridge.logPhase t (3*v))*B t) ∧
      (1+R)^A*(∫t : ℝ,‖B t‖)≤C*(1+‖θ‖)^n := by
  let V : Fin 3→ℝ→ℂ := ![V₀,V₁,V₂]
  let slope : Fin 3→ℝ := ![-2,1,3]
  let M : Fin 3→ℝ := ![M₀,M₁,M₂]
  have hm : ∀i,0≤M i := by intro i; fin_cases i <;> assumption
  have hv : ∀i y,V i y≠0 → |y|≤M i := by intro i; fin_cases i <;> assumption
  obtain ⟨n,C,hC,h⟩ := polynomial_kernel_log_separation P hP V slope M hm hv A 0
  refine ⟨n,C,hC,?_⟩
  intro θ R hR
  obtain ⟨B,hB,hi,hbound,hpoint⟩ := h θ R hR
  refine ⟨B,?_,by simpa only [pow_zero,one_mul] using hbound⟩
  intro r u v
  simpa [V,slope,Fin.prod_univ_succ,Fin.sum_univ_succ,mul_assoc,add_assoc] using hB ![r,u,v]

end CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedHeight
open CompletedGauss hiding O
open ActualEisensteinCubic
open CanonicalQuadraticSieve hiding O
theorem polynomial_smooth_quadratic
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (P : ℝ→ℝ→ℂ) (hP : HasPolynomialKernel P)
    (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀θ K U B lengthScale R : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale → 0<R →
    ∀S T : Finset (Ideal ActualEisensteinCubic.O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,(∀n∈S,∀v∈T,‖β n v‖≤lengthScale) →
    ∀yr : idealRange K→ℝ,∀yn yb : Ideal ActualEisensteinCubic.O→ℝ,
    (∑k : idealRange K,‖∑n∈S,∑v∈T,
      quadraticRow k.val (primaryGenerator (n*v))*β n v*
      (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*CubicReflectionKernel.paperKernel (Vstar (P θ))
        (R*Real.exp (-2*yr k+yn n+3*yb v)))‖^2)≤
      (C*(1+‖θ‖)^heightDegree)*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2/(1+R)^(2*A) := by
  obtain ⟨Cq,hCq,hq⟩ := integrated_product_quadratic ε hε
  obtain ⟨heightDegree,Ck₀,hCk₀,hkernel⟩ := polynomial_kernel_three_window P hP V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ A
  refine ⟨2*heightDegree,Cq*(Ck₀^2+1),by positivity,?_⟩
  intro θ K U B lengthScale R hK hU hB hL hR S T hS hT β hβ yr yn yb
  let Ck := Ck₀*(1+‖θ‖)^heightDegree
  have hCk : 0≤Ck := by dsimp [Ck]; positivity
  have hCoeff : Cq*(Ck^2+1)≤(Cq*(Ck₀^2+1))*(1+‖θ‖)^(2*heightDegree) := by
    have hh : 1≤(1+‖θ‖)^(2*heightDegree) := one_le_pow₀ (by linarith [norm_nonneg θ])
    have he : Ck^2=Ck₀^2*(1+‖θ‖)^(2*heightDegree) := by
      dsimp [Ck]
      rw [mul_pow,←pow_mul]
      congr 2
      omega
    rw [he]
    nlinarith [sq_nonneg Ck₀]
  obtain ⟨g,hsep,hg⟩ := hkernel θ R hR
  change (1+R)^A*(∫t : ℝ,‖g t‖)≤Ck at hg
  let rowPhase : idealRange K→ℝ→ℂ := fun k t => V₀ (yr k)*FourierBridge.logPhase t (-2*yr k)
  let βt : ℝ→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ := fun t n v =>
    β n v*(V₁ (yn n)*FourierBridge.logPhase t (yn n))*(V₂ (yb v)*FourierBridge.logPhase t (3*yb v))
  have hphase (t x : ℝ) : ‖FourierBridge.logPhase t x‖=1 := FourierBridge.logPhase_norm t x
  have hrowPhase (k : idealRange K) (t : ℝ) : ‖rowPhase k t‖≤1 := by
    simp only [rowPhase,norm_mul,hphase,mul_one]
    exact hV₀n _
  have hβt (t : ℝ) (n : Ideal ActualEisensteinCubic.O) (hn : n∈S) (v : Ideal ActualEisensteinCubic.O) (hv : v∈T) : ‖βt t n v‖≤lengthScale := by
    simp only [βt,norm_mul,hphase,mul_one]
    exact (mul_le_of_le_one_right (by positivity)
      (hV₂n _)).trans ((mul_le_of_le_one_right (norm_nonneg _) (hV₁n _)).trans (hβ n hn v hv))
  have hrowPhasec (k : idealRange K) : Continuous (rowPhase k) :=
    continuous_const.mul (FourierBridge.logPhase_continuous_left _)
  have hβtc (n v : Ideal ActualEisensteinCubic.O) : Continuous (fun t => βt t n v) :=
    (continuous_const.mul (continuous_const.mul (FourierBridge.logPhase_continuous_left _))).mul
      (continuous_const.mul (FourierBridge.logPhase_continuous_left _))
  have hi := hq K U B lengthScale hK hU hB hL S T hS hT βt hβtc hβt rowPhase hrowPhasec hrowPhase g
  have he (k : idealRange K) :
      (∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β n v*
        (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*CubicReflectionKernel.paperKernel (Vstar (P θ))
          (R*Real.exp (-2*yr k+yn n+3*yb v)))) =
      ∫t : ℝ,g t*(rowPhase k t*∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*βt t n v) := by
    have hint (n v : Ideal ActualEisensteinCubic.O) : Integrable (fun t : ℝ =>
        g t*(rowPhase k t*(quadraticRow k.val (primaryGenerator (n*v))*βt t n v))) := by
      apply g.integrable.mul_bdd (c := ‖quadraticRow k.val (primaryGenerator (n*v))*β n v‖)
      · exact ((hrowPhasec k).mul (continuous_const.mul (hβtc n v))).aestronglyMeasurable
      · filter_upwards [] with t
        simp only [rowPhase,βt,norm_mul,hphase,mul_one]
        have hv01 : ‖V₀ (yr k)‖*‖V₁ (yn n)‖≤1 := by
          simpa only [one_mul] using mul_le_mul (hV₀n (yr k)) (hV₁n (yn n)) (norm_nonneg _) zero_le_one
        have hv012 : (‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖≤1 := by
          simpa only [one_mul] using mul_le_mul hv01 (hV₂n (yb v)) (norm_nonneg _) zero_le_one
        calc
          _ = (‖quadraticRow k.val (primaryGenerator (n*v))‖*‖β n v‖)*
            ((‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖) := by ring
          _ ≤ (‖quadraticRow k.val (primaryGenerator (n*v))‖*‖β n v‖)*1 :=
            mul_le_mul_of_nonneg_left hv012 (by positivity)
          _ = _ := by ring
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ (fun n hn => integrable_finsetSum _ (fun v hv => hint n v))]
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_finsetSum _ (fun v hv => hint n v)]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hsep (yr k) (yn n) (yb v),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [rowPhase,βt]
    ring
  simp_rw [he]
  apply hi.trans
  have hpow : 0<(1+R)^A := by positivity
  have hmass : (∫t : ℝ,‖g t‖)≤Ck/(1+R)^A := (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hg)
  have hmass2 := pow_le_pow_left₀ (integral_nonneg (fun t => norm_nonneg _)) hmass 2
  have hbase : 0≤Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2 := by positivity
  calc
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*(Ck/(1+R)^A)^2 :=
      mul_le_mul_of_nonneg_left hmass2 hbase
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*((Ck^2+1)/(1+R)^(2*A)) := by
      apply mul_le_mul_of_nonneg_left _ hbase
      rw [div_pow,←pow_mul]
      have hp : A*2=2*A := Nat.mul_comm _ _
      rw [hp]
      exact div_le_div_of_nonneg_right (by nlinarith : Ck^2≤Ck^2+1) (by positivity)
    _ = (Cq*(Ck^2+1))*((K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)/(1+R)^(2*A) := by ring
    _ ≤ _ := by
      have hb := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCoeff (by positivity : 0≤(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2))
        (by positivity : 0≤(1+R)^(2*A))
      convert hb using 1 ; ring

end CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedHeight
open CompletedGauss hiding O
open ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve hiding O
theorem polynomial_smooth_series_rowPhase
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (P : ℝ→ℝ→ℂ) (hP : HasPolynomialKernel P)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀θ K Y H : ℝ,1≤K → 0<Y → 0<H →
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal ActualEisensteinCubic.O),
      (∀i,∀I∈S i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀β : (ℕ×ℕ×ℕ)→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖β i n v‖≤
        1/(Real.sqrt ((2:ℝ)^i.2.2)*(2:ℝ)^i.2.1*ramifiedScale ρ q i.1*Real.sqrt H)) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,
        σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*Y)^(2*deltaLoss)*(K+Y)/H := by
  obtain ⟨A,hA⟩ := exists_nat_gt (deltaLoss+1/2)
  obtain ⟨heightDegree,Cbase,hCbase,hquadbase⟩ := polynomial_smooth_quadratic V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ hV₀n hV₁n hV₂n P hP A (2*deltaLoss) (by positivity)
  obtain ⟨Cs,hCs,hsum⟩ := normMajorant_sum_bound deltaLoss A ρ q hδ hA hρ hq
  refine ⟨heightDegree,2*Cbase*Cs^2,by positivity,?_⟩
  intro θ K Y H hK hY hH S T hS hT β hβ σ hσ
  let Cq := Cbase*(1+‖θ‖)^heightDegree
  have hCq : 0<Cq := by dsimp [Cq]; positivity
  have hquad := hquadbase θ
  have hKp : 0<K := by linarith
  have hqp : 0<q := by linarith
  let g : (ℕ×ℕ×ℕ)→ℝ := fun i => Real.sqrt Cq *
    normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
  have hg0 (i : ℕ×ℕ×ℕ) : 0≤g i := by
    dsimp [g]
    exact mul_nonneg (Real.sqrt_nonneg _) (normMajorant_nonneg _ _ _ _ _ _ _ _
      hKp (by positivity) (ramifiedScale_pos ρ q hρ hqp _) hH (by positivity) (by positivity))
  have henergy (i : ℕ×ℕ×ℕ) :
      (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2)
        ≤(g i)^2 := by
    let U : ℝ := (2:ℝ)^i.2.2
    let B : ℝ := (2:ℝ)^i.2.1
    let r : ℝ := ramifiedScale ρ q i.1
    let R : ℝ := Y⁻¹*r^3*B^3*U
    have hU : 1≤U := one_le_pow₀ (by norm_num)
    have hB : 1≤B := one_le_pow₀ (by norm_num)
    have hUp : 0<U := by positivity
    have hBp : 0<B := by positivity
    have hr : 0<r := ramifiedScale_pos ρ q hρ hqp _
    have hR : 0<R := by dsimp [R]; positivity
    have h := hquad K U B (1/(Real.sqrt U*B*r*Real.sqrt H)) R
      hK hU hB (by positivity) hR (S i) (T i) (hS i) (hT i) (β i) (hβ i)
      (fun k => Real.log ((Ideal.absNorm k.val:ℝ)/K))
      (fun n => Real.log ((Ideal.absNorm n:ℝ)/U))
      (fun v => Real.log ((Ideal.absNorm v:ℝ)/B))
    change (∑k,‖completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2)≤_ at h
    have hphase : (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2)≤
        ∑k : idealRange K,‖completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k‖^2 := by
      apply Finset.sum_le_sum
      intro k _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hσ i k)
    apply (hphase.trans h).trans
    have he : Cq*(K*(U*B))^(2*deltaLoss)*(K+U*B)*(U*B)*
        (1/(Real.sqrt U*B*r*Real.sqrt H))^2/(1+R)^(2*A)=
        Cq*((K*(U*B))^(2*deltaLoss)*(K+U*B)/(B*r^2*H)/(1+R)^(2*(A:ℝ))) := by
      rw [show 2*(A:ℝ)=((2*A:ℕ):ℝ) by norm_num,Real.rpow_natCast]
      simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt hUp.le,Real.sq_sqrt hH.le]
      field_simp

    rw [he]
    have hm := smooth_energy_le_normMajorant_sq deltaLoss A K Y⁻¹ r H U B
      hKp (by positivity) hr hH hUp hBp
    calc
      _ ≤ Cq*(normMajorant deltaLoss A K Y⁻¹ r H U B)^2 := mul_le_mul_of_nonneg_left hm hCq.le
      _ = (g i)^2 := by dsimp [g,U,B,r]; rw [mul_pow,Real.sq_sqrt hCq.le]
  obtain ⟨hs,hb⟩ := hsum K Y H hKp hY hH
  have hm := finite_tsum_energy_bound
    (fun i k => σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P θ) K Y ρ q S T β i k) g hg0
    (hs.mul_left (Real.sqrt Cq)) henergy
  refine ⟨hm.1,hm.2.trans ?_⟩
  have hb' : (∑'i,g i)≤Real.sqrt Cq*(Cs*(K*Y)^deltaLoss*(Real.sqrt K+Real.sqrt Y)/Real.sqrt H) := by
    rw [show g=(fun i => Real.sqrt Cq*normMajorant deltaLoss A K Y⁻¹
      (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)) from rfl,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ (tsum_nonneg hg0) hb' 2
  apply hsq.trans
  have hroot : (Real.sqrt K+Real.sqrt Y)^2≤2*(K+Y) := by
    nlinarith [Real.sq_sqrt hKp.le,Real.sq_sqrt hY.le,
      sq_nonneg (Real.sqrt K-Real.sqrt Y)]
  simp only [mul_pow,div_pow,Real.sq_sqrt hCq.le,Real.sq_sqrt hH.le]
  have hp : ((K*Y)^deltaLoss)^2=(K*Y)^(2*deltaLoss) := by
    rw [←Real.rpow_mul_natCast (mul_pos hKp hY).le]
    congr 1
    ring
  rw [hp]
  calc
    _ ≤ Cq*(Cs^2*(K*Y)^(2*deltaLoss)*(2*(K+Y))/H) := by
      apply mul_le_mul_of_nonneg_left _ hCq.le
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity)) hH.le
    _ = _ := by dsimp [Cq]; ring

end CompletedHeight

end

end OAI

end Source196

/- Original source: OAI/NumberTheory/DirichletL/MeanSquare/PolynomialHeight.lean; sha256: 6a2a9872f8a071e495291b5fc16ed5d9402c0e76728bb231c72f9e354e07c312 -/
section Source197
namespace OAI

noncomputable section

namespace CompletedHeight

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open CompletedGauss hiding O
open ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve hiding O
theorem polynomial_reflected_branch_series
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀θ K Y : ℝ,1≤K → 0<Y →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal ActualEisensteinCubic.O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i) (j : ι→ℕ) (e : ι→Fin 3),
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal ActualEisensteinCubic.O),
      (∀i,∀I∈S i,I≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖reflectedBranchBlock P hg j e (Wfamily θ) K Y ρ q S T η σ i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,reflectedBranchBlock P hg j e (Wfamily θ) K Y ρ q S T η σ i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*Y)^(2*deltaLoss)*(K+Y)/
          ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
            (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)) := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨heightDegree,C,hC,h⟩ := polynomial_smooth_series_rowPhase
    completedShellWindow completedShellWindow completedShellWindow (Real.log 2) (Real.log 2) (Real.log 2)
    hl hl hl completedShellWindow_support completedShellWindow_support completedShellWindow_support
    completedShellWindow_norm completedShellWindow_norm completedShellWindow_norm
    Wfamily hWfamily deltaLoss ρ q hδ hρ hq
  refine ⟨heightDegree,C,hC,?_⟩
  intro θ K Y hK hY ι _ P _ hg j e S T hS hT η hη σ hσ
  have hn (v : Fin 3) : 0<(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz =>
      reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e v
        (Ideal.absNorm_eq_zero_iff.mp hz))
  exact h θ K Y _ hK hY (mul_pos (hn 0) (hn 2)) S T
    (fun i I hI => ⟨(hS i I hI).1,(hS i I hI).2.2⟩)
    (fun i I hI => ⟨(hT i I hI).1,(hT i I hI).2.2⟩)
    (fun v => reflectedDyadicCoefficient P hg j e (η v) (ramifiedScale ρ q v.1))
    (fun i n hn v hv => reflectedDyadicCoefficient_norm P hg j e (η i)
      (ramifiedScale ρ q i.1) _ _ (ramifiedScale_pos ρ q hρ (by linarith) _) (by positivity) (by positivity)
      n v (hS i n hn).1 (hT i v hv).1 (hη i n hn v hv) (hS i n hn).2.1 (hT i v hv).2.1)
    σ hσ

theorem polynomial_reflected_fiber_fixed_scale
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (deltaLoss ρ q B : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hB : 1≤B) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀θ K X c : ℝ,1≤K → 1≤X → 0<c → c≤B →
    ∀I F Q : Ideal ActualEisensteinCubic.O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal ActualEisensteinCubic.O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i),
      Pairwise (fun i j => IsCoprime (P i) (P j)) →
      (∀i,P i∣I*Q) → (∀i,¬P i∣rowResidualPart I Q) →
    ∀e : ι→Fin 3,∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal ActualEisensteinCubic.O),
      (∀i,∀J∈S i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀J∈T i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ,(∀i k,‖σ i k‖≤1) →
      (∑k : idealRange (completedResidualScale K I Q),‖∑'i : ℕ×ℕ×ℕ,
        reflectedBranchBlock P hg (fun i => completedLocalExponent I F (P i)) e (Wfamily θ)
          (completedResidualScale K I Q) (completedBranchScale K (X/c) I F Q P e) ρ q S T η σ i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,Cbase,hCbase,hbase⟩ := polynomial_reflected_branch_series Wfamily hWfamily deltaLoss ρ q hδ hρ hq
  refine ⟨heightDegree,Cbase*B^(2*deltaLoss+1),by positivity,?_⟩
  intro θ K X c hK hX hc hcB I F Q hI hQ hIK hk ι _ P _ hg hcop hpool hres e S T hS hT η hη σ hσ
  let C := Cbase*(1+‖θ‖)^heightDegree
  have hC : 0<C := by dsimp [C]; positivity
  have h := hbase θ
  have hn (J : Ideal ActualEisensteinCubic.O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj (v : Fin 3) := hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i))
    (fun i => completedLocalExponent I F (P i)) e v)
  have hp := hn (∏i,P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hk0 : 0<completedResidualScale K I Q := by linarith
  have hy : 0<completedBranchScale K X I F Q P e := by
    unfold completedBranchScale
    have hX0 : 0<X := by linarith
    have hd := hj 1
    have he := hj 2
    positivity
  rw [completedBranchScale_div]
  have hb := (h (completedResidualScale K I Q) (c*completedBranchScale K X I F Q P e)
    hk (mul_pos hc hy) P hg (fun i => completedLocalExponent I F (P i)) e S T hS hT η hη σ hσ).2
  have hs := completed_scaled_shape (2*deltaLoss) (completedResidualScale K I Q)
    (completedBranchScale K X I F Q P e) _ c B (by positivity) hk0 hy
    (mul_pos (hj 0) (hj 2)) hc hcB hB
  have hcst := completed_actual_fiber_cost deltaLoss K X hδ.le hK hX I F Q hI hQ hIK P hcop hpool hres e
  have hh := hs.trans (mul_le_mul_of_nonneg_left hcst (by positivity : 0≤B^(2*deltaLoss+1)))
  apply hb.trans
  have hfinal := mul_le_mul_of_nonneg_left hh hC.le
  convert hfinal using 1 <;> (try dsimp [completedResidualScale,completedBranchScale,C]) <;> ring

theorem polynomial_branch_energy
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (deltaLoss ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀θ K X : ℝ,1≤K → 1≤X →
    ∀I F Q : Ideal ActualEisensteinCubic.O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q → ∀d : ReflectedBranchData levelBound K I F Q,
      (∑k,‖d.value (Wfamily θ) X ρ q k‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,C,hC,h⟩ := polynomial_reflected_fiber_fixed_scale Wfamily hWfamily deltaLoss ρ q levelBound hδ hρ hq hlevel
  refine ⟨heightDegree,C,hC,?_⟩
  intro θ K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact h θ K X d.levelScale hK hX d.levelScale_pos d.levelScale_le I F Q hI hQ hIK hk _ d.good d.coprime d.divides d.nonresidual
    d.label d.nColumns d.bColumns d.nBounds d.bBounds d.amplitude d.amplitude_bound
    d.rowPhase d.rowPhase_bound

theorem polynomial_fiber_energy
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀I F Q : Ideal ActualEisensteinCubic.O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q → ∀d : ReflectedFiberData rays levelBound K I F Q,
      (∑k,‖d.value (Wfamily θ) X ρ q k‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,Cbase,hCbase,hbase⟩ := polynomial_branch_energy Wfamily hWfamily deltaLoss ρ q levelBound hδ hρ hq hlevel
  obtain ⟨Cp,hCp,hp⟩ := completed_branch_count_small_power ε hε
  refine ⟨heightDegree,Cbase*Cp,by positivity,?_⟩
  intro θ rays K X hK hX I F Q hI hQ hIK hk d
  let Cb := Cbase*(1+‖θ‖)^heightDegree
  have hCb : 0<Cb := by dsimp [Cb]; positivity
  have hb := hbase θ
  let : ∀p : d.pool,p.val.IsMaximal := d.maximal
  have hcount := hp (I*Q) (mul_ne_zero hI hQ) (fun p : d.pool => p.val)
    Subtype.val_injective d.divides
  have hnorm : (Ideal.absNorm (I*Q):ℝ)≤K*(Ideal.absNorm Q:ℝ) := by
    simp only [map_mul,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hIK (Nat.cast_nonneg _)
  have hcount' : (6:ℝ)^(2*d.pool.card)≤Cp*(K*(Ideal.absNorm Q:ℝ))^ε := by
    have hc : (6:ℝ)^(2*d.pool.card)≤Cp*(Ideal.absNorm (I*Q):ℝ)^ε := by
      simpa only [Fintype.card_coe] using hcount
    exact hc.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hε.le) hCp.le)
  have he := ReflectedFiberData.finite_energy_bound
    (fun b => (d.branch b).value (Wfamily θ) X ρ q) d.weight d.weight_bound _
    (fun b => hb K X hK hX I F Q hI hQ hIK hk (d.branch b))
  change (∑k,‖d.value (Wfamily θ) X ρ q k‖^2)≤_ at he
  apply he.trans
  have hc : (Fintype.card (Fin rays×(d.pool→Fin 6)):ℝ)^2=(rays:ℝ)^2*(6:ℝ)^(2*d.pool.card) := by
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_mul,Nat.cast_pow]
    rw [mul_pow,←pow_mul,Nat.mul_comm d.pool.card 2]
    norm_num
  rw [hc]
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hKQ : 0<K*(Ideal.absNorm Q:ℝ) := mul_pos (by linarith) hnQ
  calc
    _ ≤ ((rays:ℝ)^2*(Cp*(K*(Ideal.absNorm Q:ℝ))^ε))*
      (Cb*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcount' (sq_nonneg _)
    _ = _ := by rw [Real.rpow_add hKQ]; dsimp [Cb]; ring

theorem polynomial_energy_of_exact_models
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),HasExactCompletedModels rays rows K X ρ q levelBound F Q (Wfamily θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) (Wfamily θ) X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(Ideal.absNorm Q:ℝ)^ε*
          (K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  obtain ⟨heightDegree,Cbase,hCbase,hbase⟩ := polynomial_fiber_energy Wfamily hWfamily deltaLoss ε ρ q levelBound hδ hε hρ hq hlevel
  obtain ⟨Co,hCo,ho⟩ := completed_outer_row_small_power ε hε
  refine ⟨heightDegree,Co*Cbase,by positivity,?_⟩
  intro θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hexact
  let Cm := Cbase*(1+‖θ‖)^heightDegree
  have hCm : 0<Cm := by dsimp [Cm]; positivity
  have hm := hbase θ
  let B : ℝ := Cm*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*
    (K+K^2*(Ideal.absNorm Q:ℝ)/X)
  have hB : 0≤B := by dsimp [B,Cm]; positivity
  have hblocks : ∀A∈rows.image rowPowerfulPart,∀T∈rows.image (fun I => rowMaskPart I Q),
      (∑I∈completedRowFiber rows Q A T,‖completedT (Ψ I) (Wfamily θ) X‖^2)≤B/(Ideal.absNorm A:ℝ) := by
    intro A hA T hT
    by_cases hempty : (completedRowFiber rows Q A T).Nonempty
    · obtain ⟨I,hIf,d,hd⟩ := hexact A hA T hT hempty
      obtain ⟨hIr,hIA,hIT⟩ := Finset.mem_filter.mp hIf
      have hI := (hrows I hIr).1
      have hIK := (hrows I hIr).2
      have hk := one_le_completedResidualScale K I Q hI hIK
      have hdenergy := hm rays K X hK hX I F Q hI hQ hIK hk d
      have hembed := completedRowFiber_energy_le rows Q A T hbad K hrows
        (d.idealValue (Wfamily θ) X ρ q)
      have hscale : K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))=completedResidualScale K I Q := by
        simp only [completedResidualScale,hIA,hIT]
      rw [hscale] at hembed
      simp_rw [ReflectedFiberData.idealValue_at] at hembed
      have hsource : (∑J∈completedRowFiber rows Q A T,‖completedT (Ψ J) (Wfamily θ) X‖^2)=
          ‖lengthScale‖^2*∑J∈completedRowFiber rows Q A T,‖d.idealValue (Wfamily θ) X ρ q (rowResidualPart J Q)‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hd J hJ,norm_mul,mul_pow]
      rw [hsource]
      apply (mul_le_mul_of_nonneg_left (hembed.trans hdenergy) (sq_nonneg _)).trans
      apply le_of_eq
      dsimp [B,Cm]
      rw [hIA]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.sum_empty]
      exact div_nonneg hB (Nat.cast_nonneg _)
  have hh := ho rows Q hQ (fun I => ‖completedT (Ψ I) (Wfamily θ) X‖^2) B hB hblocks
  apply hh.trans_eq
  dsimp [B,Cm]
  ring

theorem polynomial_mean_square_of_exact_reflection
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),HasExactCompletedDyadicModels rays rows K X ρ q levelBound F Q (Wfamily θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) (Wfamily θ) X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
          (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  let deltaLoss : ℝ := ε/12
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨heightDegree,Cbase,hCbase,hbase⟩ := polynomial_energy_of_exact_models Wfamily hWfamily deltaLoss deltaLoss ρ q levelBound hδ hδ hρ hq hlevel
  let s : ℝ := 10*deltaLoss+deltaLoss
  have hs : 0≤s := by dsimp [s]; positivity
  refine ⟨heightDegree,Cbase*(16*(2:ℝ)^s),by positivity,?_⟩
  intro θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hmodels
  let C := Cbase*(1+‖θ‖)^heightDegree
  have hC : 0<C := by dsimp [C]; positivity
  have h := hbase θ
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  let A : ℝ := C*(rays:ℝ)^2*‖lengthScale‖^2*(Ideal.absNorm Q:ℝ)^deltaLoss
  have hA : 0≤A := by dsimp [A]; positivity
  rw [←completedRowDyad_sum rows K (by linarith : 0≤K) (fun I hI => (hrows I hI).2)
    (fun I => ‖completedT (Ψ I) (Wfamily θ) X‖^2)]
  have hper (j : ℕ) (hj : j∈Finset.range (completedRowDyadicLength K+1)) :
      (∑I∈completedRowDyad rows j,‖completedT (Ψ I) (Wfamily θ) X‖^2)≤
        A*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
          ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := by
    have hb := h rays ((2:ℝ)^j) X (one_le_pow₀ (by norm_num)) hX
      (completedRowDyad rows j) F Q hQ hbad
      (fun I hI => ⟨(completedRowDyad_bounds rows j (fun I hI => (hrows I hI).1) I hI).1,
        (completedRowDyad_bounds rows j (fun I hI => (hrows I hI).1) I hI).2.2⟩)
      Ψ lengthScale (hmodels j hj)
    convert hb using 1
    dsimp [A,s,C]
    ring
  calc
    _ ≤ ∑j∈Finset.range (completedRowDyadicLength K+1),
      A*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
        ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := Finset.sum_le_sum hper
    _ = A*∑j∈Finset.range (completedRowDyadicLength K+1),
      ((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
        ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*((16*(2:ℝ)^s)*(K*(Ideal.absNorm Q:ℝ))^s*(K+K^2*(Ideal.absNorm Q:ℝ)/X)) :=
      mul_le_mul_of_nonneg_left (completedRowDyadic_shape s K X (Ideal.absNorm Q:ℝ) hs hK
        (by linarith) hnQ) hA
    _ ≤ (C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
        (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
      have hnq : (Ideal.absNorm Q:ℝ)^deltaLoss≤(K*(Ideal.absNorm Q:ℝ))^deltaLoss := by
        apply Real.rpow_le_rpow hnQ.le _ hδ.le
        exact le_mul_of_one_le_left hnQ.le hK
      have hpower : (Ideal.absNorm Q:ℝ)^deltaLoss*(K*(Ideal.absNorm Q:ℝ))^s≤
          (K*(Ideal.absNorm Q:ℝ))^ε := by
        apply (mul_le_mul_of_nonneg_right hnq (by positivity)).trans_eq
        rw [←Real.rpow_add (mul_pos (by linarith) hnQ)]
        congr 1
        dsimp [s,deltaLoss]
        ring
      calc
        _ = ((C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K+K^2*(Ideal.absNorm Q:ℝ)/X))*
          ((Ideal.absNorm Q:ℝ)^deltaLoss*(K*(Ideal.absNorm Q:ℝ))^s) := by dsimp [A]; ring
        _ ≤ ((C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K+K^2*(Ideal.absNorm Q:ℝ)/X))*
          (K*(Ideal.absNorm Q:ℝ))^ε := mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = _ := by ring

    _ = _ := by dsimp [C]; ring

theorem polynomial_short_completed_average
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal ActualEisensteinCubic.O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) (Wfamily θ) (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (Ψ f I) (Wfamily θ) X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨heightDegree,Cbase,hCbase,hbase⟩ := polynomial_mean_square_of_exact_reflection
    Wfamily hWfamily ε ρ q levelBound hε hρ hq hlevel
  obtain ⟨Cs,hCs,hs⟩ := short_completed_normalized_small_power ε hε
  refine ⟨heightDegree,Cs*Cbase,by positivity,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodels
  let Cr := Cbase*(1+‖θ‖)^heightDegree
  have hCr : 0<Cr := by dsimp [Cr]; positivity
  have hr := hbase θ
  have hG1 : 1≤(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hG (Ideal.absNorm_eq_zero_iff.mp hz))
  let A : ℝ := Cr*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε
  have hA : 0≤A := by dsimp [A]; positivity
  have hcompleted (f : idealRange F) (H : Ideal ActualEisensteinCubic.O) (hH : H∈shortCubeRange (Z^(1/1000:ℝ))) :
      (∑I : rows,‖completedT (Ψ f I.val) (Wfamily θ) (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
        A*(K+K^2*(Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X) := by
    have hf0 := (mem_idealRange.mp f.property).1.1
    have hfN := (mem_idealRange.mp f.property).2
    have hHN := (mem_shortCubeRange _ H).mp hH
    have hH1 : 1≤(Ideal.absNorm H:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hHN.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hH0 : (Ideal.absNorm H:ℝ)≠0 := by linarith
    have hscale := short_cube_scales Z K (Ideal.absNorm G:ℝ) X F (Ideal.absNorm H:ℝ)
      hZ hK hG1 hF hFZ hH1 hHN.2.le hmargin
    have hb := hr rays K (X/(Ideal.absNorm H:ℝ)^3) hK hscale.1 rows f.val (G*f.val)
      (mul_ne_zero hG hf0) (fun P hP => dvd_trans (hbad P hP) (dvd_mul_right G f.val))
      hrows (Ψ f) lengthScale (hmodels f H hH)
    rw [Finset.sum_coe_sort (s := rows) (f := fun I : Ideal ActualEisensteinCubic.O => ‖completedT (Ψ f I) (Wfamily θ) (X/(Ideal.absNorm H:ℝ)^3)‖^2)]
    apply hb.trans
    simp only [map_mul,Nat.cast_mul]
    have hpow : (K*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)))^ε≤
        (K*(Ideal.absNorm G:ℝ)*F)^ε := by
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      have hh := mul_le_mul_of_nonneg_left hfN (show 0≤K*(Ideal.absNorm G:ℝ) by positivity)
      nlinarith
    have hshape : K+K^2*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ))/(X/(Ideal.absNorm H:ℝ)^3)=
        K+K^2*(Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X := by
      field_simp

    rw [hshape]
    change Cr*(rays:ℝ)^2*‖lengthScale‖^2*(K*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)))^ε*_≤A*_
    have hX0 : 0<X := by
      have hh := (le_div_iff₀ (show 0<(Ideal.absNorm H:ℝ)^3 by positivity)).mp hscale.1
      exact (show 0<(Ideal.absNorm H:ℝ)^3 by positivity).trans_le (by simpa only [one_mul] using hh)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  have hb := hs Z K (Ideal.absNorm G:ℝ) X F A hZ hK hG1 hF hFZ hA hmargin
    (fun f (I : rows) => Ψ f I.val) (fun f I z => hΨ f I.val z) (Wfamily θ) hcompleted
  have hsum (f : idealRange F) :
      (∑I : rows,‖shortCompletedSum (Ψ f I.val) (Wfamily θ) X (Z^(1/1000:ℝ))‖^2)=
      ∑I∈rows,‖shortCompletedSum (Ψ f I) (Wfamily θ) X (Z^(1/1000:ℝ))‖^2 :=
    Finset.sum_coe_sort (s := rows) (f := fun I : Ideal ActualEisensteinCubic.O => ‖shortCompletedSum (Ψ f I) (Wfamily θ) X (Z^(1/1000:ℝ))‖^2)
  simp_rw [hsum] at hb
  apply hb.trans_eq
  dsimp [A,Cr]
  ring

end

section

open scoped BigOperators Classical SchwartzMap ContDiff
open CompletedGauss hiding O
open ActualEisensteinCubic
open CanonicalQuadraticSieve hiding O
theorem completed_mean_square_norm_height
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),HasExactCompletedDyadicModels rays rows K X ρ q levelBound F Q (normTwistedSource W θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) (normTwistedSource W θ) X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
          (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  exact polynomial_mean_square_of_exact_reflection (normTwistedSource W)
    (normTwistedSource_polynomial_kernel W a b ha hsupp hW)
    ε ρ q levelBound hε hρ hq hlevel

theorem short_completed_average_norm_height
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal ActualEisensteinCubic.O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) (normTwistedSource W θ) (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (Ψ f I) (normTwistedSource W θ) X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  exact polynomial_short_completed_average (normTwistedSource W)
    (normTwistedSource_polynomial_kernel W a b ha hsupp hW)
    ε ρ q levelBound hε hρ hq hlevel

end

section

open scoped BigOperators Classical
open CompletedGauss hiding O
open ActualEisensteinCubic
open SecondPassArithmetic (normPhase normHeightTwist)
open FourierBridge (logPhase)

lemma logPhase_triple (t x : ℝ) : logPhase t (3*x)=(logPhase t x)^3 := by
  rw [show 3*x=x+x+x by ring,FourierBridge.logPhase_add,FourierBridge.logPhase_add]
  ring

lemma columnWeight_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (t : ℝ) (I : Ideal ActualEisensteinCubic.O) :
    columnWeight (normHeightTwist Ψ t) I =
      logPhase t (Real.log (Ideal.absNorm I:ℝ))*columnWeight Ψ I := by
  by_cases hI : primaryGenerator I=0
  · have hz : squarefreeGaussCoefficient I=0 := by simp [squarefreeGaussCoefficient,hI]
    simp only [columnWeight,hz,zero_mul,mul_zero]
  · have hn := SecondPassArithmetic.normPhase_of_ne_zero t (primaryGenerator I) hI
    rw [primaryGenerator_norm_sq I hI] at hn
    simp only [columnWeight,normHeightTwist,MonoidHom.mul_apply,hn]
    ring

lemma cubeWeight_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (t : ℝ) (I : Ideal ActualEisensteinCubic.O) :
    cubeWeight (normHeightTwist Ψ t) I =
      logPhase t (3*Real.log (Ideal.absNorm I:ℝ))*cubeWeight Ψ I := by
  by_cases hI : primaryGenerator I=0
  · simp [cubeWeight,hI,FiniteGaussPhase.angularFactor]
  · have hn := SecondPassArithmetic.normPhase_of_ne_zero t (primaryGenerator I) hI
    rw [primaryGenerator_norm_sq I hI] at hn
    change star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*
        (Ψ (primaryGenerator I)*normPhase t (primaryGenerator I))^3/(Ideal.absNorm I:ℂ)=_
    rw [hn,logPhase_triple]
    change _ = (logPhase t (Real.log (Ideal.absNorm I:ℝ)))^3*
      (star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*
        Ψ (primaryGenerator I)^3/(Ideal.absNorm I:ℂ))
    ring

lemma summand_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ) (t X : ℝ) (hX : 0<X)
    (I J : Ideal ActualEisensteinCubic.O) :
    summand (normHeightTwist Ψ t) W X I J =
      logPhase t (Real.log X)*summand Ψ (normTwistedSource W t) X I J := by
  by_cases hI : I=0
  · simp only [hI,CompletedGauss.summand_zero_left,mul_zero]
  by_cases hJ : J=0
  · simp only [hJ,CompletedGauss.summand_zero_right,mul_zero]
  have hni : 0<(Ideal.absNorm I:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one I hI)
  have hnj : 0<(Ideal.absNorm J:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one J hJ)
  have hl : Real.log X+Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X)=
      Real.log (Ideal.absNorm I:ℝ)+3*Real.log (Ideal.absNorm J:ℝ) := by
    rw [Real.log_div (mul_pos hni (pow_pos hnj 3)).ne' hX.ne',
      Real.log_mul hni.ne' (pow_pos hnj 3).ne',Real.log_pow]
    push_cast
    ring
  have hphase : logPhase t (Real.log X)*
      logPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X)) =
      logPhase t (Real.log (Ideal.absNorm I:ℝ))*logPhase t (3*Real.log (Ideal.absNorm J:ℝ)) := by
    rw [←FourierBridge.logPhase_add,hl,FourierBridge.logPhase_add]
  simp only [summand,columnWeight_normHeight,cubeWeight_normHeight,Vstar,normTwistedSource]
  linear_combination -(columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I:ℝ):ℂ) * cubeWeight Ψ J *
    (Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X):ℂ)*
      W ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X))*hphase

theorem completedT_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ) (t X : ℝ) (hX : 0<X) :
    completedT (normHeightTwist Ψ t) W X =
      logPhase t (Real.log X)*completedT Ψ (normTwistedSource W t) X := by
  simp only [completedT,summand_normHeight Ψ W t X hX,tsum_mul_left]

@[simp] theorem completedT_normHeight_norm (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ)
    (t X : ℝ) (hX : 0<X) :
    ‖completedT (normHeightTwist Ψ t) W X‖=‖completedT Ψ (normTwistedSource W t) X‖ := by
  rw [completedT_normHeight Ψ W t X hX,norm_mul,FourierBridge.logPhase_norm,one_mul]

theorem shortCompletedSum_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ) (t X H₀ : ℝ) (hX : 0<X) :
    shortCompletedSum (normHeightTwist Ψ t) W X H₀ =
      logPhase t (Real.log X)*shortCompletedSum Ψ (normTwistedSource W t) X H₀ := by
  rw [shortCompletedSum_eq,shortCompletedSum_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H hH
  have hn : 0<(Ideal.absNorm H:ℝ) := lt_of_lt_of_le zero_lt_one
    (norm_at_least_one H ((mem_shortCubeRange H₀ H).mp hH).1)
  rw [cubeWeight_normHeight,completedT_normHeight Ψ W t _ (div_pos hX (pow_pos hn 3))]
  have hl : 3*Real.log (Ideal.absNorm H:ℝ)+Real.log (X/(Ideal.absNorm H:ℝ)^3)=Real.log X := by
    rw [Real.log_div hX.ne' (pow_pos hn 3).ne',Real.log_pow]
    push_cast
    ring
  have hphase : logPhase t (3*Real.log (Ideal.absNorm H:ℝ))*
      logPhase t (Real.log (X/(Ideal.absNorm H:ℝ)^3))=logPhase t (Real.log X) := by
    rw [←FourierBridge.logPhase_add,hl]
  linear_combination (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
    completedT Ψ (normTwistedSource W t) (X/(Ideal.absNorm H:ℝ)^3)*hphase

@[simp] theorem shortCompletedSum_normHeight_norm (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ)
    (t X H₀ : ℝ) (hX : 0<X) :
    ‖shortCompletedSum (normHeightTwist Ψ t) W X H₀‖=
      ‖shortCompletedSum Ψ (normTwistedSource W t) X H₀‖ := by
  rw [shortCompletedSum_normHeight Ψ W t X H₀ hX,norm_mul,FourierBridge.logPhase_norm,one_mul]

end

open scoped BigOperators Classical SchwartzMap ContDiff
open CompletedGauss hiding O
open ActualEisensteinCubic
open CanonicalQuadraticSieve hiding O
theorem completed_mean_square_twist
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),HasExactCompletedDyadicModels rays rows K X ρ q levelBound F Q (normTwistedSource W θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (SecondPassArithmetic.normHeightTwist (Ψ I) θ) W X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
          (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  obtain ⟨n,C,hC,h⟩ := completed_mean_square_norm_height W a b ha hsupp hW ε ρ q levelBound hε hρ hq hlevel
  refine ⟨n,C,hC,?_⟩
  intro θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hmodel
  simp_rw [completedT_normHeight_norm _ _ _ _ (lt_of_lt_of_le zero_lt_one hX)]
  exact h θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hmodel

theorem short_completed_average_twist
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal ActualEisensteinCubic.O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) (normTwistedSource W θ) (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (SecondPassArithmetic.normHeightTwist (Ψ f I) θ) W X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨n,C,hC,h⟩ := short_completed_average_norm_height W a b ha hsupp hW ε ρ q levelBound hε hρ hq hlevel
  refine ⟨n,C,hC,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodel
  have hGpos : 0<(Ideal.absNorm G:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one G hG)
  have hright : 0 < F*Z^(-(1/40:ℝ)) := mul_pos (lt_of_lt_of_le zero_lt_one hF)
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hZ) _)
  have hprod : 0 < X*(F*Z^(-(1/40:ℝ))) := by
    have hh := lt_of_lt_of_le (mul_pos (lt_of_lt_of_le zero_lt_one hK) hGpos) hmargin
    simpa only [mul_assoc] using hh
  have hX : 0<X := (mul_pos_iff_of_pos_right hright).mp hprod
  simp_rw [shortCompletedSum_normHeight_norm _ _ _ _ _ hX]
  exact h θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodel

end CompletedHeight

end

end OAI

end Source197

/- Original source: OAI/NumberTheory/DirichletL/Eisenstein/CoordinateLaplacian.lean; sha256: c2890bdef185a468f506b85e2c8abb4e0c276af30e01e66d49387e3c876c7787 -/
section Source198
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

def kernelCoordinateLaplacian (f : kernelSmoothTests) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,
    fderiv ℝ (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) p
      (euclideanCoordinateVector j))+
    (p 2:ℂ)*fderiv ℝ (kernelTestField f) p (euclideanCoordinateVector 2)

lemma kernelCoreLift_laplacian (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∈kernelChartCore χ) :
    upperPositiveLaplacian (kernelCoreLift χ f) p=kernelCoordinateLaplacian f p := by
  have he := kernelCoreLift_eventually_eq χ f p hp
  have hd (j : Fin 3) : (fun q => fderiv ℝ (kernelCoreLift χ f) q (euclideanCoordinateVector j))=ᶠ[𝓝 p]
      (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) :=
    (he.fderiv (𝕜 := ℝ)).mono (fun q hq => congrArg (fun d => d (euclideanCoordinateVector j)) hq)
  have hdd (j : Fin 3) :
      (∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} (kernelCoreLift χ f))) p=
        fderiv ℝ (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) p
          (euclideanCoordinateVector j) := by
    change fderiv ℝ (fun q => fderiv ℝ (kernelCoreLift χ f) q (euclideanCoordinateVector j)) p
      (euclideanCoordinateVector j)=_
    rw [(hd j).fderiv_eq]
  simp only [upperPositiveLaplacian,kernelCoordinateLaplacian,hdd,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,he.fderiv_eq]

lemma kernelDirichletForm_coordinate_equation_chart (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have hi : Integrable (fun q => star (A q)*g.1 q) (integralQuotientVolume globalKubotaKernel) :=
    hA.star.integrable_mul (kernelSmoothTests_memLp g)
  have himg : kernelChartCoreImage χ⊆kernelEuclideanProjection '' S :=
    Set.image_mono (kernelChartCore_subset χ)
  rw [kernelDirichletForm_eq_chart_laplacian χ hinj f g hg]
  calc
    _ = ∫p in S,star (upperPositiveLaplacian (kernelCoreLift χ f) p)*kernelCoreLift χ g p/(p 2:ℂ)^3 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (kernelCoreLift_tsupport_outer χ g h))
      rw [hz,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)/(p 2:ℂ)^3 := by
      apply setIntegral_congr_fun hS
      intro p hp
      dsimp only
      rw [kernelCoreLift_eq_on_outer χ hinj g hg hp]
      by_cases hc : p∈kernelChartCore χ
      · rw [kernelCoreLift_laplacian χ f p hc,heq p (χ.positive hp)]
        rfl
      · have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
          (fun h => hc (kernelCoreLift_tsupport χ hinj g hg h))
        rw [kernelCoreLift_eq_on_outer χ hinj g hg hp] at hz
        change g.1 (kernelEuclideanProjection p)=0 at hz
        change star _*g.1 (kernelEuclideanProjection p)/_=star _*g.1 (kernelEuclideanProjection p)/_
        rw [hz,mul_zero,zero_div,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)
        ∂hyperbolicEuclideanVolume :=
      (hyperbolicEuclidean_setIntegral_complex S hS χ.positive _).symm
    _ = ∫q in kernelEuclideanProjection '' S,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_integral_complex S hS χ.positive hinj _ hi.aestronglyMeasurable
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      have hz : g.1 q=0 := image_eq_zero_of_notMem_tsupport (fun h => hq (himg (hg h)))
      rw [hz,mul_zero]

lemma kernelDirichletForm_sum_right {ι : Type*} (f : kernelSmoothTests)
    (t : Finset ι) (g : ι→kernelSmoothTests) :
    kernelDirichletForm f (∑i∈t,g i)=∑i∈t,kernelDirichletForm f (g i) := by
  induction t using Finset.induction_on with
  | empty =>
    have hz := kernelDirichletForm_smul_right 0 f (0 : kernelSmoothTests)
    simpa only [Finset.sum_empty,zero_smul,zero_mul] using hz
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi,kernelDirichletForm_add_right,ih]

theorem kernelDirichletForm_coordinate_equation (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p))
    (g : kernelSmoothTests) :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  obtain ⟨t,G,hG,hGsupp⟩ := kernelSmoothTest_finite_chart_partition g
  calc
    _ = ∑i : t,kernelDirichletForm f (G i) := by
      rw [←hG,kernelDirichletForm_sum_right]
    _ = ∑i : t,∫q,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      apply Finset.sum_congr rfl
      intro i hi
      exact kernelDirichletForm_coordinate_equation_chart i.1.1 i.1.2 f (G i) (hGsupp i) A hA heq
    _ = ∫q,∑i : t,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      symm
      exact integral_finsetSum _ (fun i hi => hA.star.integrable_mul (kernelSmoothTests_memLp (G i)))
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun q => by
        have hq := congrArg (fun k : kernelSmoothTests => k.1 q) hG
        simp only [Submodule.coe_sum,Finset.sum_apply] at hq
        dsimp only
        rw [←Finset.mul_sum,hq])

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

lemma kernelL2_inner_toLp_smooth (A : KernelQuotient→ℂ)
    (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel)) (g : kernelSmoothTests) :
    inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g)=
      ∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  calc
    _ = ∫q,inner ℂ ((hA.toLp A) q) (kernelSmoothTestsToL2 g q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hA.coeFn_toLp,(kernelSmoothTests_memLp g).coeFn_toLp] with q hq hg
      change inner ℂ ((hA.toLp A) q) (((kernelSmoothTests_memLp g).toLp g.1) q)=_
      rw [hq,hg,RCLike.inner_apply]
      simp only [RCLike.star_def,mul_comm]

lemma kernelCoordinateLaplacian_form (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p))
    (v : KernelEnergyGraph) :
    inner ℂ (kernelEnergyGradient (kernelEnergyGraphCore f)) (kernelEnergyGradient v)=
      inner ℂ (hA.toLp A) (kernelEnergyMass v) := by
  exact kernelEnergyGraphCore_dense.induction_on v
    (isClosed_eq (by fun_prop : Continuous (fun u : KernelEnergyGraph =>
      inner ℂ (kernelEnergyGradient (kernelEnergyGraphCore f)) (kernelEnergyGradient u)))
      (by fun_prop : Continuous (fun u : KernelEnergyGraph => inner ℂ (hA.toLp A) (kernelEnergyMass u))))
    (fun g => by
      rw [kernelEnergyGradient_core,kernelEnergyGradient_core,kernelEnergyMass_core,
        kernelGradientToL2_inner,kernelL2_inner_toLp_smooth]
      exact kernelDirichletForm_coordinate_equation f A hA heq g)

theorem kernelEnergyLaplacian_graph_of_coordinate (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    (kernelSmoothTestsToL2 f,hA.toLp A)∈kernelEnergyLaplacian.graph := by
  have hu : kernelEnergyGraphCore f=
      kernelVariationalSolution (kernelSmoothTestsToL2 f+hA.toLp A) := by
    apply kernelVariationalSolution_unique
    intro v
    rw [kernelEnergyMass_core,kernelCoordinateLaplacian_form f A hA heq,inner_add_left]
  have hm := congrArg kernelEnergyMass hu
  rw [kernelEnergyMass_core] at hm
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  exact hm.symm

lemma kernelEnergyLaplacian_domain_of_coordinate (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelSmoothTestsToL2 f∈kernelEnergyLaplacian.domain :=
  LinearPMap.mem_domain_of_mem_graph (kernelEnergyLaplacian_graph_of_coordinate f A hA heq)

lemma kernelEnergyLaplacian_apply_of_coordinate (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelEnergyLaplacian ⟨kernelSmoothTestsToL2 f,kernelEnergyLaplacian_domain_of_coordinate f A hA heq⟩=
      hA.toLp A :=
  kernelEnergyLaplacian.mem_graph_snd_inj
    (kernelEnergyLaplacian.mem_graph ⟨kernelSmoothTestsToL2 f,kernelEnergyLaplacian_domain_of_coordinate f A hA heq⟩)
    (kernelEnergyLaplacian_graph_of_coordinate f A hA heq) rfl

end CubicEisenstein

section

open scoped BigOperators Classical
open MeasureTheory
namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic ConcreteTraceCRT

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem densityChildEnergy_from_canonical_state
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ)
    (X F K E t₁ t₂ : ℝ) (J : ℕ) (hX : 0<X) (hK : 0<K) (hE : 0≤E)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0)
    (h₁ : ∀t,canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m labels
      (orientedLogProfile true V₁) X K≤E*(X*F)^2*(1+‖t‖)^(2*J))
    (h₂ : ∀t,canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m labels
      (orientedLogProfile false V₂) X K≤E*(X*F)^2*(1+‖t‖)^(2*J)) :
    densityChildEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t₁) (normHeightTwist Ψ₂ t₂)
      m T V₁ V₂ X X (2*J)≤
      6*E*(X*F)^2*(1+‖t₁‖)^J*(1+‖t₂‖)^J*
        (∫t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  have hleft (t : ℝ) : childEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m T V₁ X true false 0 0≤
      (6*E*(X*F)^2)*(1+‖t‖)^(2*J) := by
    have hh := childEnergy_le_canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m
      T labels V₁ X K 0 0 hX hK true false hlabels hrows hzero
    simp only [normHeightTwist_twice,secondSignedHeight,ite_true,sub_self,add_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₁ t) (by norm_num : (0:ℝ)≤6)).trans_eq (by ring))
  have hright (t : ℝ) : childEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m T V₂ X false true 0 0≤
      (6*E*(X*F)^2)*(1+‖t‖)^(2*J) := by
    have hh := childEnergy_le_canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m
      T labels V₂ X K 0 0 hX hK false true hlabels hrows hzero
    simp only [normHeightTwist_twice,secondSignedHeight,Bool.false_eq_true,ite_false,sub_self,add_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₂ t) (by norm_num : (0:ℝ)≤6)).trans_eq (by ring))
  have hb : 0≤6*E*(X*F)^2 := by positivity
  have hd := densityChildEnergy_normHeight_polynomial p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂
    X X t₁ t₂ (6*E*(X*F)^2) (6*E*(X*F)^2) J hX hX hb hb hleft hright
  rw [Real.mul_self_sqrt hb] at hd
  exact hd

end SecondPassIntegration

namespace SecondPassArithmetic
open ActualEisensteinCubic FirstPassCubeLabels ConcreteTraceCRT

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

def globalCanonicalLabels (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex) : Finset (Ideal ActualEisensteinCubic.O) :=
  (globalArithmeticTargets p source side q j).image Prod.fst

include hp in
theorem globalCanonicalLabels_bounds (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hk : ∀x∈source,x.source.frequency≠0) :
    ∀I∈globalCanonicalLabels p source side q j,
      I≠⊥ ∧ Squarefree I ∧ (Ideal.absNorm I:ℝ)≤globalPooledLabelScale j := by
  intro I hI
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
  have hb := globalArithmeticTargets_bounds p hp source side q j hk z hz
  exact ⟨hb.1,globalArithmeticTargets_squarefree p source side q j z hz,hb.2.1⟩

end SecondPassArithmetic
end

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct jLabel)

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)

omit [DecidableEq ι] in
theorem actualSecondLabel_coprime (bad : Ideal ActualEisensteinCubic.O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    IsCoprime (actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂) bad := by
  have hprod (S : Finset ι) : IsCoprime (∏i∈S,Ideal.span {p i}) bad :=
    IsCoprime.prod_left (fun i _=>hbad i)
  have hJ : IsCoprime (Ideal.span {jLabel p B (fun i=>v₁ i+v₂ i) ε₁ ε₂}) bad := by
    simp only [jLabel,primeProduct,FiniteGaussPhase.span_finset_prod,←Ideal.span_singleton_pow]
    exact IsCoprime.prod_left (fun i _=>(hbad i).pow_left)
  exact ((hJ.mul_left (hprod C)).mul_left (hprod E)).mul_left (hprod V)

theorem globalNewLabel_coprime (bad : Ideal ActualEisensteinCubic.O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad) (x : GlobalSecondData ι) :
    IsCoprime (SecondPassFiber.newLabel (globalSecondTuple p x)) bad := by
  exact actualSecondLabel_coprime p bad hbad x.cube.support x.common x.source.divisor x.source.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit

theorem globalCanonicalLabels_coprime (bad : Ideal ActualEisensteinCubic.O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex) :
    ∀I∈globalCanonicalLabels p source side q j,IsCoprime I bad := by
  intro I hI
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  exact globalNewLabel_coprime p bad hbad x

end SecondPassArithmetic

namespace CanonicalRowCompletion

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O

theorem finite_integral_energy_polynomial {κ : Type*} [Fintype κ]
    (b : ℝ → ℂ) (φ : κ → ℝ → ℂ) (d : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖*(1+|t|)^d))
    (hφ : ∀ k, Integrable (fun t => b t*φ k t))
    (hbound : ∀ t, (∑ k, ‖φ k t‖^2) ≤ E*(1+|t|)^(2*d)) :
    (∑ k, ‖∫ t : ℝ, b t*φ k t‖^2) ≤
      E*(∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ → EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖ ≤ (‖b t‖*(1+|t|)^d)*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ k, ‖b t*φ k t‖^2) ≤ _
    simp only [norm_mul,mul_pow,← Finset.mul_sum,Real.sq_sqrt hE]
    have hp : (1+|t|)^(2*d) = ((1+|t|)^d)^2 := by
      rw [← pow_mul,Nat.mul_comm d 2]
    calc
      _ ≤ ‖b t‖^2 * (E*(1+|t|)^(2*d)) :=
        mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
      _ = _ := by rw [hp]; ring
  have he : (∫ t : ℝ, F t) = e.symm (fun k => ∫ t : ℝ, b t*φ k t) := by
    rw [show F = (fun t => e.symm (fun k => b t*φ k t)) from rfl,
      e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫ t : ℝ, b t*φ k t)‖ ≤
      (∫ t : ℝ, ‖b t‖*(1+|t|)^d)*Real.sqrt E := by
    rw [← he,← integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _)
      (Filter.Eventually.of_forall hF)
  have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hh
  change (∑ k, ‖∫ t : ℝ, b t*φ k t‖^2) ≤
    (∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 * E at hh
  simpa only [mul_comm] using hh

theorem norm_add_sum_sq_le {κ : Type*} (s : Finset κ) (a : ℂ) (b : κ → ℂ) :
    ‖a + ∑ k ∈ s, b k‖^2 ≤ 2*(‖a‖^2 + s.card*∑ k ∈ s, ‖b k‖^2) := by
  have hs : ‖∑ k ∈ s, b k‖^2 ≤ (s.card : ℝ)*∑ k ∈ s, ‖b k‖^2 := by
    calc
      _ ≤ (∑ k ∈ s, ‖b k‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by
        simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one]
          using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun k => ‖b k‖)
  have ha := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a (∑ k ∈ s, b k)) 2
  nlinarith [sq_nonneg (‖a‖ - ‖∑ k ∈ s, b k‖)]

theorem outsideCanonicalRow_binned_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    ‖outsideCanonicalRow S D hbad Ψ m f z W X‖^2 ≤
      2*X*(‖shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀‖^2 +
        (cubeLogRange b X).card * ∑ j ∈ cubeLogRange b X,
          ‖outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀‖^2) := by
  have hs := norm_add_sum_sq_le (cubeLogRange b X)
    (shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀)
    (fun j => outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀)
  rw [← outsideCanonicalRow_reopened_binned S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD] at hs
  have hn : ‖outsideCanonicalRow S D hbad Ψ m f z W X‖^2 =
      X*‖(Real.sqrt X : ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X‖^2 := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg X),
      mul_pow,inv_pow,Real.sq_sqrt hX.le]
    field_simp
  rw [hn]
  convert mul_le_mul_of_nonneg_left hs hX.le using 1 ; ring

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace CanonicalCoefficientClass

section
open ActualEisensteinCubic
open SecondPassArithmetic (rayMonoid conjugateRayMonoid rayMonoid_apply conjugateRayMonoid_apply
  FirstCoreIndex firstCoreTwist sideRayMonoid SecondRayIndex secondRayMinus secondRayPlus)
open RayFourExpansion (RayCharacter)

def IsBaseRayTwist (base Ψ : ActualEisensteinCubic.O→*ℂ) : Prop :=
  Ψ=base ∨ ∃χ : RayCharacter, Ψ=rayMonoid χ*base

def baseRayOrbit (base : ActualEisensteinCubic.O→*ℂ) : Finset (ActualEisensteinCubic.O→*ℂ) :=
  insert base (Finset.univ.image (fun χ : RayCharacter => rayMonoid χ*base))

lemma mem_baseRayOrbit (base Ψ : ActualEisensteinCubic.O→*ℂ) : Ψ∈baseRayOrbit base ↔ IsBaseRayTwist base Ψ := by
  simp only [baseRayOrbit,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and,IsBaseRayTwist]
  constructor
  · rintro (h|⟨χ,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨χ,h.symm⟩
  · rintro (h|⟨χ,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨χ,h.symm⟩

lemma baseRayOrbit_card (base : ActualEisensteinCubic.O→*ℂ) : (baseRayOrbit base).card≤17 := by
  have h1 := Finset.card_insert_le base (Finset.univ.image (fun χ : RayCharacter => rayMonoid χ*base))
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset RayCharacter))
    (f := fun χ : RayCharacter => rayMonoid χ*base)
  have h3 := RayFourExpansion.rayCharacter_card_le
  simp only [Finset.card_univ] at h2
  unfold baseRayOrbit
  omega

lemma rayMonoid_mul (χ η : RayCharacter) : rayMonoid (χ*η)=rayMonoid χ*rayMonoid η := by
  ext x
  simp only [rayMonoid_apply,RayFourExpansion.rayCharacter,MulChar.mul_apply,MonoidHom.mul_apply]

lemma conjugateRayMonoid_eq (χ : RayCharacter) : conjugateRayMonoid χ=rayMonoid (star χ) := by
  ext x
  simp only [conjugateRayMonoid_apply,rayMonoid_apply,RayFourExpansion.rayCharacter,MulChar.star_apply]

lemma IsBaseRayTwist.mul_ray {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ) (χ : RayCharacter) :
    IsBaseRayTwist base (rayMonoid χ*Ψ) := by
  rcases hΨ with h|⟨η,h⟩
  · exact Or.inr ⟨χ,by rw [h]⟩
  · exact Or.inr ⟨χ*η,by rw [h,rayMonoid_mul,mul_assoc]⟩

lemma firstCoreTwist_single_ray (side : Bool) (χ : RayCharacter) (Ψ : ActualEisensteinCubic.O→*ℂ)
    (r : FirstCoreIndex) :
    firstCoreTwist side χ Ψ r =
      rayMonoid ((if side then star χ else χ)*FirstPassCubeLabels.coreRayCharacter side r.1 r.2.2)*Ψ := by
  rw [rayMonoid_mul]
  have hcore : FirstPassCubeLabels.coreRayTwist side r.1 r.2.2 =
      rayMonoid (FirstPassCubeLabels.coreRayCharacter side r.1 r.2.2) := rfl
  unfold firstCoreTwist sideRayMonoid
  rw [hcore]
  cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true,conjugateRayMonoid_eq] <;> ac_rfl

lemma IsBaseRayTwist.firstCore {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (side : Bool) (χ : RayCharacter) (r : FirstCoreIndex) :
    IsBaseRayTwist base (firstCoreTwist side χ Ψ r) := by
  rw [firstCoreTwist_single_ray]
  exact hΨ.mul_ray _

lemma secondRayMinus_single_ray (Ψ : ActualEisensteinCubic.O→*ℂ) (r : SecondRayIndex) :
    secondRayMinus Ψ r=rayMonoid (star r.2.2*star r.1.2)*Ψ := by
  rw [rayMonoid_mul]
  simp only [secondRayMinus,conjugateRayMonoid_eq,mul_assoc]

lemma secondRayPlus_single_ray (Ψ : ActualEisensteinCubic.O→*ℂ) (r : SecondRayIndex) :
    secondRayPlus Ψ r=rayMonoid (r.2.1*star r.1.1)*Ψ := by
  rw [rayMonoid_mul]
  simp only [secondRayPlus,conjugateRayMonoid_eq,mul_assoc]

lemma IsBaseRayTwist.secondMinus {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (r : SecondRayIndex) : IsBaseRayTwist base (secondRayMinus Ψ r) := by
  rw [secondRayMinus_single_ray]
  exact hΨ.mul_ray _

lemma IsBaseRayTwist.secondPlus {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (r : SecondRayIndex) : IsBaseRayTwist base (secondRayPlus Ψ r) := by
  rw [secondRayPlus_single_ray]
  exact hΨ.mul_ray _

lemma IsBaseRayTwist.norm_le {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (hbase : ∀x,‖base x‖≤1) (x : ActualEisensteinCubic.O) : ‖Ψ x‖≤1 := by
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hbase x
  · rw [MonoidHom.mul_apply,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (FiniteRayExpansion.norm_char_le_one χ _)).trans (hbase x)

def FactorsModulo (Q : Ideal ActualEisensteinCubic.O) (Ψ : ActualEisensteinCubic.O→*ℂ) : Prop :=
  ∀x y : ActualEisensteinCubic.O,x-y∈Q → Ψ x=Ψ y

lemma IsBaseRayTwist.factorsModulo {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (Q : Ideal ActualEisensteinCubic.O) (hbase : FactorsModulo Q base) :
    FactorsModulo (Q*Ideal.span {(4:ActualEisensteinCubic.O)}) Ψ := by
  intro x y hxy
  have hb := hbase x y (Ideal.mul_le_left hxy)
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hb
  · simp only [MonoidHom.mul_apply]
    rw [hb]
    congr 1
    exact RayFourExpansion.rayCharacter_eq_of_mod_four χ x y
      (Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy))

def initialBase {q : ℕ} (χ : DirichletCharacter ℂ q) : ActualEisensteinCubic.O→*ℂ :=
  InitialMeanSquare.conjugateMonoid (InitialMeanSquare.normCharacter χ)

lemma initialBase_norm {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ActualEisensteinCubic.O) :
    ‖initialBase χ x‖≤1 := by
  change ‖star (InitialMeanSquare.normCharacter χ x)‖≤1
  rw [norm_star]
  exact InitialMeanSquare.normCharacter_norm_le_one χ x

lemma initial_minus_member {q : ℕ} (χ : DirichletCharacter ℂ q) (r : SecondRayIndex) :
    IsBaseRayTwist (initialBase χ) (secondRayMinus (initialBase χ) r) :=
  IsBaseRayTwist.secondMinus (Or.inl rfl : IsBaseRayTwist (initialBase χ) (initialBase χ)) r

lemma initial_plus_member {q : ℕ} (χ : DirichletCharacter ℂ q) (r : SecondRayIndex) :
    IsBaseRayTwist (initialBase χ) (secondRayPlus (initialBase χ) r) :=
  IsBaseRayTwist.secondPlus (Or.inl rfl : IsBaseRayTwist (initialBase χ) (initialBase χ)) r

end

open ActualEisensteinCubic
open ActualEisensteinCoordinates (eval coords eval_coords)
open ShortDraftLatticeCount (qNat qO_nonneg coords_eval)

lemma norm_eval_mod (m : ℕ) (a b : ℤ) :
    (Ideal.absNorm (Ideal.span {eval a b}) : ZMod m)=
      (a : ZMod m)^2-(a : ZMod m)*(b : ZMod m)+(b : ZMod m)^2 := by
  have hi : (Ideal.absNorm (Ideal.span {eval a b}) : ℤ)=a^2-a*b+b^2 := by
    rw [←qNat_eq_absNorm_span]
    change ((ShortDraftLatticeCount.q (coords (eval a b))).toNat : ℤ)=_
    rw [Int.toNat_of_nonneg (qO_nonneg _),coords_eval]
    rfl
  have hz := congrArg (fun k : ℤ => (k : ZMod m)) hi
  push_cast at hz
  exact hz

theorem normCharacter_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) :
    FactorsModulo (Ideal.span {(m : ActualEisensteinCubic.O)}) (InitialMeanSquare.normCharacter χ) := by
  intro x y hxy
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hxy
  let c := (coords y).1
  let d := (coords y).2
  let e := (coords z).1
  let f := (coords z).2
  have hy : y=eval c d := (eval_coords y).symm
  have hx : x=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
    calc
      x=y+(m : ActualEisensteinCubic.O)*z := by linear_combination hz
      _=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
        rw [hy,←eval_coords z]
        dsimp [eval,c,d,e,f]
        push_cast
        ring
  change χ (Ideal.absNorm (Ideal.span {x}))=χ (Ideal.absNorm (Ideal.span {y}))
  congr 1
  rw [hx,hy,norm_eval_mod,norm_eval_mod]
  simp

theorem initialBase_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) :
    FactorsModulo (Ideal.span {(m : ActualEisensteinCubic.O)}) (initialBase χ) := by
  intro x y hxy
  change star (InitialMeanSquare.normCharacter χ x)=star (InitialMeanSquare.normCharacter χ y)
  rw [normCharacter_factorsModulo χ x y hxy]

def fixedBaseConductor (m : ℕ) : Ideal ActualEisensteinCubic.O := Ideal.span {(m : ActualEisensteinCubic.O)}*Ideal.span {(4 : ActualEisensteinCubic.O)}

theorem initialOrbit_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : IsBaseRayTwist (initialBase χ) Ψ) : FactorsModulo (fixedBaseConductor m) Ψ :=
  hΨ.factorsModulo _ (initialBase_factorsModulo χ)

lemma fixedBaseConductor_principal (m : ℕ) :
    fixedBaseConductor m=Ideal.span {((4*m : ℕ) : ActualEisensteinCubic.O)} := by
  rw [fixedBaseConductor,Ideal.span_singleton_mul_span_singleton]
  congr 1
  push_cast
  ring_nf

lemma fixedBaseConductor_ne_zero (m : ℕ) (hm : m≠0) : fixedBaseConductor m≠0 := by
  rw [fixedBaseConductor_principal]
  change Ideal.span {((4*m : ℕ) : ActualEisensteinCubic.O)}≠⊥
  rw [ne_eq,Ideal.span_singleton_eq_bot]
  exact_mod_cast Nat.mul_ne_zero (by decide : (4:ℕ)≠0) hm

lemma fixedBaseConductor_norm (m : ℕ) (hm : m≠0) :
    Ideal.absNorm (fixedBaseConductor m)=16*m^2 := by
  rw [fixedBaseConductor_principal]
  have h := rational_modulus_card (4*m) (Nat.mul_ne_zero (by decide) hm)
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply]
  rw [h]
  ring

end CanonicalCoefficientClass

end

end OAI

end Source198

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/DensityBudgets.lean; sha256: 48a755cd21192079251f34a3c0680c14562e982da53d0bd4cddc6262c592c765 -/
section Source199
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace SecondPassArithmetic

section

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy_from_canonical_state)

def canonicalDensityConstant (E : ℝ) (J : ℕ) (t : ℝ) : ℝ :=
  6*E*(1+‖t‖)^(2*J)*(∫s : ℝ,firstLogDensity 0 s)^3

theorem canonicalDensityConstant_nonneg (E : ℝ) (hE : 0≤E) (J : ℕ) (t : ℝ) :
    0≤canonicalDensityConstant E J t := by
  have hi : 0≤∫s : ℝ,firstLogDensity 0 s :=
    integral_nonneg (fun s=>FirstPassCubeLabels.firstLogDensity_nonneg 0 s)
  unfold canonicalDensityConstant
  positivity

theorem globalFirstQuantitativeBudget_state_bound (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃ Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (windows : Fin 7 → ℝ → ℂ)
      (C Cd Ct Γ E oldHeight K ell B F M H U Z θ A₀ Vmax : ℝ) (N J Ntail : ℕ),
      0≤C → 0≤Γ → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0 → |t|≤A₀) → (∀t,windows 6 t≠0 → |t|≤A₀) →
      (∀u,‖Ψ u‖≤1) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (let source := globalQuantitativeSource p pool blocks K ell B F M H U side
       ∀a : RayCharacter×RayCharacter,∀r : FirstCoreIndex,
       ∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),
       ∀ray : SecondRayIndex,∀q∈globalBinTriples p source side j,
       let Ψmode := firstCoreTwist side (if side then a.1 else a.2) Ψ r
       ∀s : ℝ,
       (canonicalLogEnergy p hp hcop hg pool (normHeightTwist (secondRayMinus Ψmode ray) s)
         (fixedTripleMask m q) (globalCanonicalLabels p source side q j)
         (orientedLogProfile true (windows 5)) (globalPooledColumnScale ell j)
         (globalLogRep j 8*Real.exp 1)≤
         E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2*(1+‖s‖)^(2*J)) ∧
       (canonicalLogEnergy p hp hcop hg pool (normHeightTwist (secondRayPlus Ψmode ray) s)
         (fixedTripleMask m q) (globalCanonicalLabels p source side q j)
         (orientedLogProfile false (windows 6)) (globalPooledColumnScale ell j)
         (globalLogRep j 8*Real.exp 1)≤
         E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2*(1+‖s‖)^(2*J))) →
      globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ oldHeight) m windows
        C Cd Ct Γ ε K ell B F M H U (N+1) (2*J) Ntail side ≤
        (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*((ell*B^3)*F)*
          ((B*U)^ε*(Cd+Ct*globalFirstTailFactor K ell B F U H Ntail)+
           C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
             (canonicalDensityConstant E J oldHeight*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N))) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalFirstQuantitativeBudget_canonical_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj pool blocks side Ψ m windows C Cd Ct Γ E oldHeight K ell B F M H U Z θ A₀ Vmax N J Ntail
    hC hΓ hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hb₁ hb₂ he
  apply hbound p hp hcop hg hc hinj pool blocks side (normHeightTwist Ψ oldHeight) m windows
    C Cd Ct Γ (canonicalDensityConstant E J oldHeight) K ell B F M H U Z θ A₀ Vmax N J Ntail
    hC hΓ (canonicalDensityConstant_nonneg E hE J oldHeight) hU hK hell hB hF hH
    hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂
    (fun u=>(normHeightTwist_norm_le Ψ oldHeight u).trans (hΨ u)) hb₁ hb₂
  dsimp only
  intro a r j hj ray q hq
  rw [firstCoreTwist_normHeight,secondRayMinus_normHeight,secondRayPlus_normHeight]
  let source := globalQuantitativeSource p pool blocks K ell B F M H U side
  have hk : ∀x∈source,x.source.frequency≠0 :=
    fun x hx=>globalQuantitativeSource_frequency_ne_zero p pool blocks K ell B F M H U side x hx
  have hkc : 0<globalLogRep j 8*Real.exp 1 := mul_pos (globalLogRep_pos j 8) (Real.exp_pos 1)
  have hs := he a r j hj ray q hq
  have hd := densityChildEnergy_from_canonical_state p hp hcop hg pool
    (secondRayMinus (firstCoreTwist side (if side then a.1 else a.2) Ψ r) ray)
    (secondRayPlus (firstCoreTwist side (if side then a.1 else a.2) Ψ r) ray)
    (fixedTripleMask m q) (globalArithmeticTargets p source side q j)
    (globalCanonicalLabels p source side q j) (windows 5) (windows 6)
    (globalPooledColumnScale ell j) (globalPooledLabelScale j) (globalLogRep j 8*Real.exp 1)
    E oldHeight oldHeight J (globalPooledColumnScale_pos ell hell j) hkc hE
    (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩)
    (fun z hz=>(globalArithmeticTargets_bounds p hp source side q j hk z hz).2.2)
    (globalArithmeticTargets_nonzero p source side q j hk)
    (fun t=>(hs t).1) (fun t=>(hs t).2)
  exact hd.trans_eq (by unfold canonicalDensityConstant; rw [two_mul,pow_add]; ring)

end

open ActualEisensteinCubic ConcreteTraceCRT

def canonicalRankMass (Z : ℝ) (r : ℕ) : ℝ :=
  Real.exp (3*((3000-r:ℕ):ℝ))*Z^2

theorem canonicalRankMass_initial (Z : ℝ) (r : ℕ) : Z^2≤canonicalRankMass Z r := by
  have he : 1≤Real.exp (3*((3000-r:ℕ):ℝ)) := Real.one_le_exp (by positivity)
  simpa only [one_mul,canonicalRankMass] using mul_le_mul_of_nonneg_right he (sq_nonneg Z)

theorem canonicalRankMass_step (Z : ℝ) (r s : ℕ) (hr : r≤3000) (hs : s+1≤r) :
    Real.exp 3*canonicalRankMass Z r≤canonicalRankMass Z s := by
  have hn : 3000-r+1≤3000-s := by omega
  have hn' : ((3000-r:ℕ):ℝ)+1≤((3000-s:ℕ):ℝ) := by exact_mod_cast hn
  unfold canonicalRankMass
  rw [←mul_assoc,←Real.exp_add]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg Z)

theorem canonicalRankMass_child (Z X F X' F' : ℝ) (r s : ℕ)
    (hr : r≤3000) (hs : s+1≤r) (hparent : X*F≤canonicalRankMass Z r)
    (hchild : X'*F'≤Real.exp 3*(X*F)) : X'*F'≤canonicalRankMass Z s :=
  hchild.trans ((mul_le_mul_of_nonneg_left hparent (Real.exp_pos _).le).trans
    (canonicalRankMass_step Z r s hr hs))

theorem canonicalRankMass_global (Z : ℝ) (hZ : Real.exp 9000≤Z) (r : ℕ) :
    canonicalRankMass Z r≤Z^3 := by
  have hn : ((3000-r:ℕ):ℝ)≤3000 := by exact_mod_cast (Nat.sub_le 3000 r)
  have he : Real.exp (3*((3000-r:ℕ):ℝ))≤Z :=
    (Real.exp_le_exp.mpr (by linarith)).trans hZ
  calc
    canonicalRankMass Z r ≤ Z*Z^2 := mul_le_mul_of_nonneg_right he (sq_nonneg Z)
    _ = Z^3 := by ring

theorem lowerCubeBin_transfer_mass (X B F : ℝ) (hB : B≠0) :
    (X/B^3)*(Real.exp 1*B)^3*F=Real.exp 3*(X*F) := by
  have he : (Real.exp 1)^3=Real.exp 3 := by
    rw [show (3:ℝ)=1+1+1 by norm_num,Real.exp_add,Real.exp_add]
    ring
  rw [mul_pow,←he]
  field_simp

theorem lowerCubeBin_energy_normalization (ell B F : ℝ) (hell : 0<ell) (hB : 0<B) :
    (ell*B^3)*((B*Real.sqrt ell)^2)⁻¹*
      (ell*(Real.exp 1*B)^2*F)*(ell*(Real.exp 1*B)^3*F)=
      Real.exp 5*((ell*B^3)*F)^2 := by
  have he : (Real.exp 1)^5=Real.exp 5 := by
    rw [show (5:ℝ)=1+1+1+1+1 by norm_num]
    simp only [Real.exp_add]
    ring
  rw [mul_pow,Real.sq_sqrt hell.le]
  simp only [mul_pow]
  rw [←he]
  field_simp

theorem canonical_live_scale_bounds (Z X F : ℝ) (r : ℕ)
    (hZ : Real.exp 9000≤Z) (hX : 1≤X) (hF : 1≤F)
    (hmass : X*F≤canonicalRankMass Z r) : X≤Z^3 ∧ F≤Z^3 := by
  have hm := hmass.trans (canonicalRankMass_global Z hZ r)
  constructor <;> nlinarith

theorem canonical_small_or_live (Z X F K : ℝ) (r : ℕ) (m : ActualEisensteinCubic.O)
    (hZ : Real.exp 9000≤Z) (_hX : 0<X) (hF : 1≤F) (hK : 0≤K) (hm : m≠0)
    (hmass : X*F≤canonicalRankMass Z r) (hinv : K*‖eisEmbedding m‖^2≤X*F) :
    K≤F ∨ (1<X ∧ X≤Z^3 ∧ F≤Z^3) := by
  by_cases hx : X≤1
  · exact Or.inl (smallColumn_row_le_label m hm X F K hx (by linarith) hK hinv)
  · have hl := lt_of_not_ge hx
    exact Or.inr ⟨hl,canonical_live_scale_bounds Z X F r hZ hl.le hF hmass⟩

def canonicalPoolCutoff (Bsupport Z : ℝ) : ℕ := ⌈Bsupport*Z^3⌉₊

theorem canonicalPoolCutoff_covers (Bsupport b Z X : ℝ)
    (hB : 0≤Bsupport) (hb : b≤Bsupport) (hX : 0≤X) (hXZ : X≤Z^3) :
    b*X≤(canonicalPoolCutoff Bsupport Z:ℝ) := by
  calc
    b*X ≤ Bsupport*X := mul_le_mul_of_nonneg_right hb hX
    _ ≤ Bsupport*Z^3 := mul_le_mul_of_nonneg_left hXZ hB
    _ ≤ _ := Nat.le_ceil _

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

def rowFamilyEnergy (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) (K : ℝ) : ℝ :=
  (∑ I ∈ labels, nonzeroRowMajorantSum (P I) K).re

theorem rowFamilyEnergy_eq_sum (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ)
    (K : ℝ) (hK : 0 < K) :
    rowFamilyEnergy labels P K =
      ∑ I ∈ labels, ∑ z ∈ (firstFrequencyDisk (2*K)).erase 0,
        (rowMajorant (‖eisEmbedding z‖^2/K)).re * ‖P I z‖^2 := by
  unfold rowFamilyEnergy
  simp only [nonzeroRowMajorantSum_exact_disk _ K hK, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem rowFamilyEnergy_nonneg (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ)
    (K : ℝ) (hK : 0 < K) : 0 ≤ rowFamilyEnergy labels P K := by
  rw [rowFamilyEnergy_eq_sum labels P K hK]
  exact Finset.sum_nonneg (fun I hI => Finset.sum_nonneg
    (fun z hz => mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)))

theorem rowFamilyEnergy_integral_polynomial
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (K : ℝ) (hK : 0 < K)
    (b : ℝ → ℂ) (φ : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℝ → ℂ) (d : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖*(1+|t|)^d))
    (hφ : ∀ I z, Integrable (fun t => b t*φ I z t))
    (hbound : ∀ t, rowFamilyEnergy labels (fun I z => φ I z t) K ≤ E*(1+|t|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ∫ t : ℝ, b t*φ I z t) K ≤
      E*(∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 := by
  let R := (firstFrequencyDisk (2*K)).erase 0
  let w : ActualEisensteinCubic.O → ℝ := fun z => Real.sqrt ((rowMajorant (‖eisEmbedding z‖^2/K)).re)
  have hw (z : ActualEisensteinCubic.O) : 0 ≤ w z := Real.sqrt_nonneg _
  have hw2 (z : ActualEisensteinCubic.O) : (w z)^2 = (rowMajorant (‖eisEmbedding z‖^2/K)).re :=
    Real.sq_sqrt (rowMajorant_nonneg _)
  have hsum (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) :
      (∑ x : labels × R, ‖(w x.2.val : ℂ)*P x.1.val x.2.val‖^2) = rowFamilyEnergy labels P K := by
    rw [rowFamilyEnergy_eq_sum labels P K hK]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_coe_sort (s := labels)
      (f := fun I : Ideal ActualEisensteinCubic.O => ∑ z : R, ‖(w z.val : ℂ)*P I z.val‖^2)]
    apply Finset.sum_congr rfl
    intro I hI
    rw [Finset.sum_coe_sort (s := R) (f := fun z : ActualEisensteinCubic.O => ‖(w z : ℂ)*P I z‖^2)]
    apply Finset.sum_congr rfl
    intro z hz
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw z),mul_pow,hw2]
  let ψ : labels × R → ℝ → ℂ := fun x t => (w x.2.val : ℂ)*φ x.1.val x.2.val t
  have hψ (x : labels × R) : Integrable (fun t => b t*ψ x t) := by
    convert (hφ x.1.val x.2.val).const_mul (w x.2.val : ℂ) using 1
    funext t
    dsimp only [ψ]
    ring
  have hψbound (t : ℝ) : (∑ x : labels × R, ‖ψ x t‖^2) ≤ E*(1+|t|)^(2*d) := by
    change (∑ x : labels × R, ‖(w x.2.val : ℂ)*φ x.1.val x.2.val t‖^2) ≤ _
    rw [hsum (fun I z => φ I z t)]
    exact hbound t
  have hi (x : labels × R) :
      (∫ t : ℝ, b t*ψ x t) = (w x.2.val : ℂ)*(∫ t : ℝ, b t*φ x.1.val x.2.val t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [ψ]
    ring
  have hm := finite_integral_energy_polynomial b ψ d E hE hb hψ hψbound
  simp_rw [hi] at hm
  rwa [hsum (fun I z => ∫ t : ℝ, b t*φ I z t)] at hm

theorem rowFamilyEnergy_const_mul (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ)
    (K : ℝ) (hK : 0 < K) (c : ℂ) :
    rowFamilyEnergy labels (fun I z => c*P I z) K = ‖c‖^2*rowFamilyEnergy labels P K := by
  simp only [rowFamilyEnergy_eq_sum _ _ K hK, norm_mul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem canonicalSmoothedEnergy_eq_rowFamilyEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (H : Finset ι → ℂ) (K : ℝ) :
    canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K =
      rowFamilyEnergy labels (fun I z => fixedChildRow p hp hcop hg pool Ψ m H (idealGenerator I) z) K := rfl

end
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem separated_canonical_integrable
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O)
    (b V : 𝓢(ℝ,ℂ)) (B ell : ℝ) :
    Integrable (fun ξ : ℝ => b ξ *
      reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient β n B ξ)
        Ψ m f (fun T => frequencyTwist V ξ (columnLog p ell T)) z) := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z
  have hi := reopening_finite_sum_integrable Q pool.powerset β A n (primeProductNorm p) B ell b V
  convert hi using 1
  funext ξ
  rw [reopenedCanonicalRow_integrand p hp hcop hg]
  rfl

theorem separated_canonical_family_energy
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ) (n : (ι →₀ ℕ) → ℝ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (b V : 𝓢(ℝ,ℂ))
    (B ell K E : ℝ) (d : ℕ) (hB : 0 < B) (hell : 0 < ell) (hK : 0 < K) (hE : 0 ≤ E)
    (hbound : ∀ ξ : ℝ,
      rowFamilyEnergy labels (fun I z =>
        reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z) K ≤
        E*(1+|ξ|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, b ξ *
        reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z) K ≤
      (B^2*ell)⁻¹ * E*(∫ ξ : ℝ, ‖b ξ‖*(1+|ξ|)^d)^2 := by
  have hb : Integrable (fun ξ : ℝ => ‖b ξ‖*(1+|ξ|)^d) := by
    simpa only [Real.norm_eq_abs,mul_comm] using weighted_schwartz_integrable b d
  have hφ (I : Ideal ActualEisensteinCubic.O) (z : ActualEisensteinCubic.O) : Integrable (fun ξ : ℝ => b ξ *
      reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
        Ψ m (idealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z) :=
    separated_canonical_integrable p hp hcop hg pool Q (β I) n Ψ m (idealGenerator I) z b V B ell
  have hm := rowFamilyEnergy_integral_polynomial labels K hK b
    (fun I z ξ => reopenedCanonicalRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
      Ψ m (idealGenerator I) (fun T => frequencyTwist V ξ (columnLog p ell T)) z)
    d E hE hb hφ hbound
  have hn : ‖((B*Real.sqrt ell : ℝ) : ℂ)⁻¹‖^2 = (B^2*ell)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (mul_pos hB (Real.sqrt_pos.mpr hell)),inv_pow,mul_pow,Real.sq_sqrt hell.le]
  rw [rowFamilyEnergy_const_mul labels _ K hK, hn]
  convert mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (B^2*ell)⁻¹) using 1 ; ring

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

theorem rowFamilyEnergy_bound_sum {κ : Type*}
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (bins : Finset κ) (K : ℝ) (hK : 0 < K)
    (P A : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) (B : κ → Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) (c N : ℝ)
    (hbound : ∀ I ∈ labels, ∀ z ∈ (firstFrequencyDisk (2*K)).erase 0,
      ‖P I z‖^2 ≤ c*(‖A I z‖^2 + N*∑ j ∈ bins, ‖B j I z‖^2)) :
    rowFamilyEnergy labels P K ≤
      c*(rowFamilyEnergy labels A K + N*∑ j ∈ bins, rowFamilyEnergy labels (B j) K) := by
  let R := (firstFrequencyDisk (2*K)).erase 0
  let w : ActualEisensteinCubic.O → ℝ := fun z => (rowMajorant (‖eisEmbedding z‖^2/K)).re
  have hswap : (∑ I ∈ labels, ∑ z ∈ R, w z*∑ j ∈ bins, ‖B j I z‖^2) =
      ∑ j ∈ bins, rowFamilyEnergy labels (B j) K := by
    simp_rw [Finset.mul_sum]
    calc
      _ = ∑ I ∈ labels, ∑ j ∈ bins, ∑ z ∈ R, w z*‖B j I z‖^2 :=
        Finset.sum_congr rfl (fun I hI => Finset.sum_comm)
      _ = ∑ j ∈ bins, ∑ I ∈ labels, ∑ z ∈ R, w z*‖B j I z‖^2 := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun j hj => (rowFamilyEnergy_eq_sum labels (B j) K hK).symm)
  rw [rowFamilyEnergy_eq_sum labels P K hK]
  calc
    _ ≤ ∑ I ∈ labels, ∑ z ∈ R,
        (c*(w z*‖A I z‖^2) + c*N*(∑ j ∈ bins, w z*‖B j I z‖^2)) := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro z hz
      calc
        _ ≤ w z*(c*(‖A I z‖^2 + N*∑ j ∈ bins, ‖B j I z‖^2)) :=
          mul_le_mul_of_nonneg_left (hbound I hI z hz) (rowMajorant_nonneg _)
        _ = _ := by rw [← Finset.mul_sum]; ring
    _ = c*(rowFamilyEnergy labels A K + N*∑ j ∈ bins, rowFamilyEnergy labels (B j) K) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hswap, ← rowFamilyEnergy_eq_sum labels A K hK]
      ring

theorem outsideCanonicalRow_family_binned_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ K : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hK : 0 < K)
    (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    rowFamilyEnergy labels (fun I z => outsideCanonicalRow S D hbad Ψ m (idealGenerator I) z W X) K ≤
      2*X*(rowFamilyEnergy labels (fun I z =>
        shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W X H₀) K +
        (cubeLogRange b X).card * ∑ j ∈ cubeLogRange b X,
          rowFamilyEnergy labels (fun I z =>
            outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m (idealGenerator I) z W X H₀) K) := by
  apply rowFamilyEnergy_bound_sum labels (cubeLogRange b X) K hK
  intro I hI z hz
  exact outsideCanonicalRow_binned_energy S D hbad hSp Ψ m (idealGenerator I) z W hWc
    b X H₀ hb hX hW hD

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

theorem outsideCanonicalBin_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X H₀ K E : ℝ) (d : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell) (hK : 0 < K) (hE : 0 ≤ E)
    (hn : ∀ v ∈ Q, B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun I v => reopenedCubeCoefficient H₀
      (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    (∀ ξ : ℝ, rowFamilyEnergy labels (fun I z =>
      reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
        (separatedCubeCoefficient (β I) n B ξ) Ψ m (idealGenerator I)
        (fun T => frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) K ≤
      E*(1+|ξ|)^(2*d)) →
    rowFamilyEnergy labels (fun I z =>
      outsideCanonicalBin S D hbad Q Ψ m (idealGenerator I) z W X H₀) K ≤
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
  have hrows : (fun I z => outsideCanonicalBin S D hbad Q Ψ m (idealGenerator I) z W X H₀) =
      (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ *
          reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF)
            (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
            (separatedCubeCoefficient (β I) n B ξ) Ψ m (idealGenerator I)
            (fun T => frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) := by
    funext I z
    exact outsideCanonicalBin_separated S D hbad Q Ψ m (idealGenerator I) z W a b ha hs hW V hV
      B ell X H₀ hB hell hX hn hn'
  rw [hrows]
  exact separated_canonical_family_energy (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q labels β n Ψ m
    (reopeningCoefficient W a b ha hs hW) V B ell K E d hB hell hK hE hbound

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (primeProduct)

theorem canonicalProgress_large (Z : ℝ) (hZ : Real.exp 9000≤Z) :
    Real.exp 4≤Z^((1:ℝ)/1000) := by
  have hh := Real.rpow_le_rpow (Real.exp_pos 9000).le hZ (by norm_num : (0:ℝ)≤1/1000)
  rw [Real.rpow_def_of_pos (Real.exp_pos 9000), Real.log_exp] at hh
  norm_num at hh
  exact (Real.exp_le_exp.mpr (by norm_num : (4:ℝ)≤9)).trans hh

theorem paddedCanonicalRatio (K M R Z η : ℝ) (hM : 0<M) (hZ : 0<Z) :
    Z^η*((K/Z^η)*R/(Real.exp 3*M))=(K*R/M)/Real.exp 3 := by
  field_simp

def canonicalRankMargin (σ η : ℝ) (r : ℕ) : ℝ :=
  σ-η*((3000-r:ℕ):ℝ)

theorem canonicalRankMargin_lower (σ η : ℝ) (hη : 0≤η) (r : ℕ) :
    σ-3000*η≤canonicalRankMargin σ η r := by
  have hn : ((3000-r:ℕ):ℝ)≤3000 := by exact_mod_cast (Nat.sub_le 3000 r)
  unfold canonicalRankMargin
  nlinarith

theorem canonicalRankMargin_step (σ η : ℝ) (hη : 0≤η) (r s : ℕ)
    (hr : r≤3000) (hs : s+1≤r) :
    canonicalRankMargin σ η s+η≤canonicalRankMargin σ η r := by
  have hn : 3000-r+1≤3000-s := by omega
  have hn' : ((3000-r:ℕ):ℝ)+1≤((3000-s:ℕ):ℝ) := by exact_mod_cast hn
  unfold canonicalRankMargin
  nlinarith

theorem canonicalRatio_exp_loss (K M R : ℝ) (hM : 0<M) :
    K*R/(Real.exp 3*M)=(K*R/M)/Real.exp 3 := by
  field_simp

theorem canonicalRankMargin_padding (Z σ η a : ℝ) (r s : ℕ)
    (hZ : 1<Z) (hη : 0≤η) (hr : r≤3000) (hs : s+1≤r)
    (ha : 0≤a) (hbound : a≤Z^(-canonicalRankMargin σ η r)) :
    Z^η*(a/Real.exp 3)≤Z^(-canonicalRankMargin σ η s) := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hmargin := canonicalRankMargin_step σ η hη r s hr hs
  calc
    Z^η*(a/Real.exp 3) ≤ Z^η*a :=
      mul_le_mul_of_nonneg_left (div_le_self ha (Real.one_le_exp (by norm_num)))
        (Real.rpow_nonneg hZ0.le _)
    _ ≤ Z^η*Z^(-canonicalRankMargin σ η r) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hZ0.le _)
    _ = Z^(η-canonicalRankMargin σ η r) := by
      rw [sub_eq_add_neg,Real.rpow_add hZ0]
    _ ≤ Z^(-canonicalRankMargin σ η s) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem fixedTripleMask_ne_zero_of_bin (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j) (m : ActualEisensteinCubic.O) (hm : m≠0) :
    fixedTripleMask m q≠0 := by
  obtain ⟨x,hx,hqx⟩ := Finset.mem_image.mp hq
  have ht := globalSecondFixedTriple_nonzero p hp x
  rw [←hqx]
  unfold fixedTripleMask
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hm
    (ConcretePrimeRowBridge.idealGenerator_ne_zero _ ht.1))
    (ConcretePrimeRowBridge.idealGenerator_ne_zero _ ht.2.1))
    (ConcretePrimeRowBridge.idealGenerator_ne_zero _ ht.2.2)

include hp in

theorem canonical_retained_scale_closure
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (Z σ η X B F K : ℝ) (m : ActualEisensteinCubic.O)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hX : 0<X) (hB : 0<B) (hF : 1≤F) (hK : 1≤K) (hm : m≠0)
    (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hstart : K≤Z^3) (hmass : X*F≤canonicalRankMass Z (fixedDepthRank Z K))
    (hinv : K*‖eisEmbedding m‖^2≤(X*F)*Z^(-σ))
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale (K/Z^η) (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    0<X' ∧ 1≤F' ∧ 1≤K' ∧
      fixedDepthRank Z K'+1≤fixedDepthRank Z K ∧ K'≤Z^3 ∧
      X'*F'≤canonicalRankMass Z (fixedDepthRank Z K') ∧
      K'*‖eisEmbedding (fixedTripleMask m q)‖^2≤(X'*F')*Z^(-σ) ∧
      fixedTripleMask m q≠0 ∧
      (∀I∈globalCanonicalLabels p source side q j,
        I≠⊥ ∧ Squarefree I ∧ (Ideal.absNorm I:ℝ)≤F') := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hF0 : 0<F := zero_lt_one.trans_le hF
  have hBup : 0<Real.exp 1*B := mul_pos (Real.exp_pos _) hB
  have hell : 0<X/B^3 := div_pos hX (pow_pos hB 3)
  have hKpad : 0<K/Z^η := div_pos hK0 (Real.rpow_pos_of_pos hZ0 _)
  have hKle : K/Z^η≤K := div_le_self hK0.le (Real.one_le_rpow hZ.le hη)
  have hlarge : Real.exp 4≤(Real.exp 1*B)*F := (canonicalProgress_large Z hZbig).trans hprogress
  obtain ⟨hXc,hFc,hKc,hMc,hsmall,hrank,hrank0,hratio,hlabels⟩ :=
    globalRetained_canonical_geometry p hp source side q j hq Z η K (K/Z^η)
      (X/B^3) (Real.exp 1*B) F m hZ hηsmall hK0 hKpad hKle hell hBup hF
      hprogress hlarge hstart hk hb₁ hb₂ hretained
  have hMc' : globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j≤Real.exp 3*(X*F) := by
    simpa only [lowerCubeBin_transfer_mass X B F hB.ne'] using hMc
  have hratio' : globalLogRep j 8*Real.exp 1*‖eisEmbedding (fixedTripleMask m q)‖^2/
      (globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j)≤Z^(-σ) := by
    rw [lowerCubeBin_transfer_mass X B F hB.ne',paddedCanonicalRatio K (X*F)
      (‖eisEmbedding m‖^2) Z η (mul_pos hX hF0) hZ0] at hratio
    apply hratio.trans
    apply (div_le_self (div_nonneg (mul_nonneg hK0.le (sq_nonneg _)) (mul_pos hX hF0).le)
      (Real.one_le_exp (by norm_num))).trans
    exact (div_le_iff₀ (mul_pos hX hF0)).mpr (by simpa only [mul_comm] using hinv)
  refine ⟨hXc,hFc,hKc,hrank,?_,?_,?_,fixedTripleMask_ne_zero_of_bin p hp source side q j hq m hm,
    globalCanonicalLabels_bounds p hp source side q j hk⟩
  · exact hsmall.trans ((div_le_self hK0.le
      (Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤1/1000))).trans hstart)
  · exact canonicalRankMass_child Z X F _ _ _ _ hrank0 hrank hmass hMc'
  · exact (div_le_iff₀ (mul_pos hXc (zero_lt_one.trans_le hFc))).mp hratio' |>.trans_eq (by ring)

include hp in

theorem canonical_retained_unpadded_closure
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (Z σ η X B F K : ℝ) (m : ActualEisensteinCubic.O)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hX : 0<X) (hB : 0<B) (hF : 1≤F) (hK : 1≤K) (hm : m≠0)
    (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hstart : K≤Z^3) (hmass : X*F≤canonicalRankMass Z (fixedDepthRank Z K))
    (hinv : K*‖eisEmbedding m‖^2≤
      (X*F)*Z^(-canonicalRankMargin σ η (fixedDepthRank Z K)))
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale K (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    0<X' ∧ 1≤F' ∧ 1≤K' ∧
      fixedDepthRank Z K'+1≤fixedDepthRank Z K ∧ K'≤Z^3 ∧
      X'*F'≤canonicalRankMass Z (fixedDepthRank Z K') ∧
      K'*‖eisEmbedding (fixedTripleMask m q)‖^2≤
        (X'*F')*Z^(-canonicalRankMargin σ η (fixedDepthRank Z K')) ∧
      fixedTripleMask m q≠0 ∧
      (∀I∈globalCanonicalLabels p source side q j,
        I≠⊥ ∧ Squarefree I ∧ (Ideal.absNorm I:ℝ)≤F') := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hF0 : 0<F := zero_lt_one.trans_le hF
  have hBup : 0<Real.exp 1*B := mul_pos (Real.exp_pos _) hB
  have hell : 0<X/B^3 := div_pos hX (pow_pos hB 3)
  have hlarge : Real.exp 4≤(Real.exp 1*B)*F := (canonicalProgress_large Z hZbig).trans hprogress
  obtain ⟨hXc,hFc,hKc,hMc,hsmall,hrank,hrank0,hratio,hlabels⟩ :=
    globalRetained_canonical_geometry p hp source side q j hq Z η K K
      (X/B^3) (Real.exp 1*B) F m hZ hηsmall hK0 hK0 le_rfl hell hBup hF
      hprogress hlarge hstart hk hb₁ hb₂ hretained
  have hMc' : globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j≤Real.exp 3*(X*F) := by
    simpa only [lowerCubeBin_transfer_mass X B F hB.ne'] using hMc
  have hparent : K*‖eisEmbedding m‖^2/(X*F)≤
      Z^(-canonicalRankMargin σ η (fixedDepthRank Z K)) :=
    (div_le_iff₀ (mul_pos hX hF0)).mpr (by simpa only [mul_comm] using hinv)
  have hratio' : globalLogRep j 8*Real.exp 1*‖eisEmbedding (fixedTripleMask m q)‖^2/
      (globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j)≤
      Z^(-canonicalRankMargin σ η (fixedDepthRank Z (globalLogRep j 8*Real.exp 1))) := by
    rw [lowerCubeBin_transfer_mass X B F hB.ne',canonicalRatio_exp_loss K (X*F)
      (‖eisEmbedding m‖^2) (mul_pos hX hF0)] at hratio
    exact hratio.trans (canonicalRankMargin_padding Z σ η _ _ _ hZ hη hrank0 hrank
      (div_nonneg (mul_nonneg hK0.le (sq_nonneg _)) (mul_pos hX hF0).le) hparent)
  refine ⟨hXc,hFc,hKc,hrank,?_,?_,?_,fixedTripleMask_ne_zero_of_bin p hp source side q j hq m hm,
    globalCanonicalLabels_bounds p hp source side q j hk⟩
  · exact hsmall.trans ((div_le_self hK0.le
      (Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤1/1000))).trans hstart)
  · exact canonicalRankMass_child Z X F _ _ _ _ hrank0 hrank hmass hMc'
  · exact (div_le_iff₀ (mul_pos hXc (zero_lt_one.trans_le hFc))).mp hratio' |>.trans_eq (by ring)

end SecondPassArithmetic

end

end OAI

end Source199
