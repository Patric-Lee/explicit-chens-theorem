import OpenAIGrouped.Unit038
import OpenAIGrouped.Unit037
import OpenAIGrouped.Unit034
import OpenAIGrouped.Unit035
import OpenAIGrouped.Unit021
import OpenAIGrouped.Unit010

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Reflection/InactiveAggregation.lean; sha256: 06f4ceff18095bf48c8de79ffbb2788df006a603c3d7d36c8a500bafa6a2a7cb -/
section Source1560
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem inactive_slot_mass {ι : Type*} [Fintype ι] (P : PrimeFamily ι)
    (hinj : Function.Injective P.ideal) (L : Finset ι) (H : ℝ)
    (hH : ∀ i∈L, (Ideal.absNorm (P.ideal i):ℝ)≤H) :
    (∑ i∈L, ‖(Ideal.absNorm (P.ideal i):ℂ)⁻¹‖)≤256*(columnDyadicLength H+1:ℝ) := by
  have he : (∑ i∈L, ‖(Ideal.absNorm (P.ideal i):ℂ)⁻¹‖)=
      ∑ I∈L.image P.ideal, 1/(Ideal.absNorm I:ℝ) := by
    rw [Finset.sum_image hinj.injOn]
    simp only [norm_inv,Complex.norm_natCast,one_div]
  rw [he]
  apply finite_inverse_norm_sum
  · intro I hI
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact NeZero.ne (P.ideal i)
  · intro I hI
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact hH i hi

theorem inactive_slot_mass_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (P : PrimeFamily ι),
      Function.Injective P.ideal → ∀ (L : Finset ι) (H : ℝ), 1≤H →
      (∀ i∈L, (Ideal.absNorm (P.ideal i):ℝ)≤H) →
      (∑ i∈L, ‖(Ideal.absNorm (P.ideal i):ℂ)⁻¹‖)≤C*H^ε := by
  refine ⟨256*(2+(ε*Real.log 2)⁻¹),by positivity,?_⟩
  intro ι _ P hinj L H hH hnorm
  exact (inactive_slot_mass P hinj L H hnorm).trans
    (by simpa only [mul_assoc,one_div] using (mul_le_mul_of_nonneg_left
      (columnDyadicLength_small_power ε hε H hH) (by norm_num : (0:ℝ)≤256)))

theorem original_pool_choice_count (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (R Q Q₀ : Ideal Eis), R≠0 → Q≠0 →
      (Fintype.card (FreeReflection.pool R Q Q₀→Fin 6):ℝ)^2≤C*(Ideal.absNorm (R*Q):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := completed_branch_count_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro R Q Q₀ hR hQ
  let (P : FreeReflection.pool R Q Q₀) : P.val.IsMaximal := FreeReflection.pool_maximal R Q Q₀ P
  have hh := hbound (R*Q) (mul_ne_zero hR hQ) (fun P : FreeReflection.pool R Q Q₀ => P.val)
    Subtype.val_injective (FreeReflection.pool_divides R Q Q₀ hR hQ)
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,← pow_mul,
    Nat.mul_comm (Fintype.card (FreeReflection.pool R Q Q₀)) 2] using hh
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1560

/- Original source: OAI/NumberTheory/DirichletL/Reflection/InactiveEnergy.lean; sha256: f2e61885cb31a5379e330b07ac3fdb6b50afea7ec318c3045eaaa88050e82d95 -/
section Source1561
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma weighted_finite_row_energy {ι κ : Type*} (L : Finset ι) (rows : Finset κ)
    (w : ι→ℂ) (f : ι→κ→ℂ) :
    (∑ k∈rows, ‖∑ i∈L, w i*f i k‖^2)≤
      (∑ i∈L, ‖w i‖)*∑ i∈L, ‖w i‖*(∑ k∈rows, ‖f i k‖^2) := by
  calc
    _ ≤ ∑ k∈rows, (∑ i∈L, ‖w i‖*‖f i k‖^2)*(∑ i∈L, ‖w i‖) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [star_one,mul_one,norm_one,one_pow] using
        DescentWeightedCauchy.weighted_cauchy_sq L w (fun i => f i k) (fun _ => 1)
    _ = _ := by
      rw [← Finset.sum_mul,Finset.sum_comm]
      simp only [← Finset.mul_sum]
      ring

lemma weighted_finite_row_energy_uniform {ι κ : Type*} (L : Finset ι) (rows : Finset κ)
    (w : ι→ℂ) (f : ι→κ→ℂ) (B : ℝ)
    (hf : ∀ i∈L, (∑ k∈rows, ‖f i k‖^2)≤B) :
    (∑ k∈rows, ‖∑ i∈L, w i*f i k‖^2)≤(∑ i∈L, ‖w i‖)^2*B := by
  apply (weighted_finite_row_energy L rows w f).trans
  calc
    _ ≤ (∑ i∈L, ‖w i‖)*∑ i∈L, ‖w i‖*B := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun i hi => norm_nonneg _))
      exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hf i hi) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem inactive_slot_energy {ι κ : Type*} [Fintype ι] (P : PrimeFamily ι)
    (hinj : Function.Injective P.ideal) (L : Finset ι) (rows : Finset κ) (H B : ℝ)
    (hB : 0≤B) (hH : ∀ i∈L, (Ideal.absNorm (P.ideal i):ℝ)≤H)
    (a : ι→ℂ) (ha : ∀ i∈L, ‖a i‖≤1) (f : ι→κ→ℂ)
    (hf : ∀ i∈L, (∑ k∈rows, ‖f i k‖^2)≤B) :
    (∑ k∈rows, ‖∑ i∈L, (Ideal.absNorm (P.ideal i):ℂ)⁻¹*a i*f i k‖^2)≤
      (256*(columnDyadicLength H+1:ℝ))^2*B := by
  have hm : (∑ i∈L, ‖(Ideal.absNorm (P.ideal i):ℂ)⁻¹*a i‖)≤256*(columnDyadicLength H+1:ℝ) := by
    apply (Finset.sum_le_sum (fun i hi => ?_)).trans (inactive_slot_mass P hinj L H hH)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (ha i hi)
  apply (weighted_finite_row_energy_uniform L rows (fun i => (Ideal.absNorm (P.ideal i):ℂ)⁻¹*a i) f B hf).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun i hi => norm_nonneg _)) hm 2) hB
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1561

/- Original source: OAI/NumberTheory/DirichletL/Reflection/FixedLevel.lean; sha256: 2ba1c535046523c35ce85badeb7945ddd38696d472284d885d0e1debe0df6ae0 -/
section Source1562
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def reflectionSourceConductor (Q : Ideal Eis) : Eis :=
  ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))

lemma reflectionSourceConductor_span (Q : Ideal Eis) :
    Ideal.span {reflectionSourceConductor Q}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}) :=
  ConcretePrimeRowBridge.span_idealGenerator _

lemma reflectionSourceConductor_ne_zero (Q : Ideal Eis) (hQ : Q≠0) :
    reflectionSourceConductor Q≠0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  apply mul_ne_zero _ (mul_ne_zero hQ _)
  all_goals simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]; norm_num

def reflectionSourceLevel (Q : Ideal Eis) : Eis := (9:Eis)*reflectionSourceConductor Q

lemma reflectionSourceLevel_ne_zero (Q : Ideal Eis) (hQ : Q≠0) :
    reflectionSourceLevel Q≠0 := mul_ne_zero (by norm_num) (reflectionSourceConductor_ne_zero Q hQ)

lemma reflectionSourceGeometry_level (Q : Ideal Eis) (hQ : Q≠0)
    (h : Eis⧸Ideal.span {reflectionSourceConductor Q}) :
    (9:Eis)*(fixedFourierGeometry (reflectionSourceConductor Q)
      (reflectionSourceConductor_ne_zero Q hQ) h).c0∣reflectionSourceLevel Q :=
  mul_dvd_mul_left (9:Eis) (fixedFourierGeometry _ _ h).denominator_dvd

lemma reflectionSourceLevel_original_period {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis)
    (hS : ∀ i, IsCoprime (Q*Ideal.span {(72:Eis)}) (S.ideal i)) :
    ∀ i, IsCoprime (Ideal.span {reflectionSourceLevel Q}) ((markedRowFamily D S Q).ideal i) :=
  markedRowFamily_period D S Q hS (reflectionSourceConductor Q) (reflectionSourceConductor_span Q)

lemma reflectionSourceLevel_ray_finite (Q : Ideal Eis) (hQ : Q≠0) :
    Finite (Eis⧸Ideal.span {(reflectionSourceLevel Q)^2}) :=
  ConcreteTraceCRT.finite_quotient_span (pow_ne_zero 2 (reflectionSourceLevel_ne_zero Q hQ))

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1562

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SectorAggregation.lean; sha256: cd418ff226b8eca8f5563be94929e50d0901d428a5d4b9d2bdfd1be4859b616c -/
section Source1563
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def fullRaySector (N : Eis) (rows : Finset (Ideal Eis)) (r : Eis⧸Ideal.span {N^2}) : Finset (Ideal Eis) :=
  rows.filter (fun K => Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=r)

lemma mem_fullRaySector (N : Eis) (rows : Finset (Ideal Eis)) (r : Eis⧸Ideal.span {N^2}) (K : Ideal Eis) :
    K∈fullRaySector N rows r ↔ K∈rows ∧ Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=r :=
  Finset.mem_filter

lemma sum_fullRaySectors {M : Type*} [AddCommMonoid M] (N : Eis)
    [Fintype (Eis⧸Ideal.span {N^2})] (rows : Finset (Ideal Eis)) (f : Ideal Eis→M) :
    (∑ r : Eis⧸Ideal.span {N^2}, ∑ K∈fullRaySector N rows r,f K)=∑ K∈rows,f K :=
  Finset.sum_fiberwise rows (fun K => Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)) f

theorem full_ray_sector_energy (N : Eis) [Fintype (Eis⧸Ideal.span {N^2})]
    (rows Pset : Finset (Ideal Eis)) (f : Ideal Eis→Ideal Eis→ℂ) (E : ℝ)
    (hE : ∀ r p : Eis⧸Ideal.span {N^2},
      (∑ K∈fullRaySector N rows r, ‖∑ P∈fullRaySector N Pset p,f K P‖^2)≤E) :
    (∑ K∈rows,‖∑ P∈Pset,f K P‖^2)≤(Fintype.card (Eis⧸Ideal.span {N^2}):ℝ)^3*E := by
  rw [←sum_fullRaySectors N rows (fun K => ‖∑ P∈Pset,f K P‖^2)]
  calc
    _ ≤ ∑ r : Eis⧸Ideal.span {N^2}, (Fintype.card (Eis⧸Ideal.span {N^2}):ℝ)^2*E := by
      apply Finset.sum_le_sum
      intro r hr
      have hh := weighted_finite_row_energy_uniform (Finset.univ : Finset (Eis⧸Ideal.span {N^2}))
        (fullRaySector N rows r) (fun _ => (1:ℂ))
        (fun p K => ∑ P∈fullRaySector N Pset p,f K P) E (fun p _ => hE r p)
      simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
      have he : (∑ K∈fullRaySector N rows r, ‖∑ P∈Pset,f K P‖^2)=
          ∑ K∈fullRaySector N rows r, ‖∑ p : Eis⧸Ideal.span {N^2},∑ P∈fullRaySector N Pset p,f K P‖^2 := by
        apply Finset.sum_congr rfl
        intro K hK
        rw [sum_fullRaySectors]
      rw [he]
      exact hh
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1563

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SectorCover.lean; sha256: 4d60c70fa23cf53c3a7953dc4c8e801fbbe84f506a2b3222c6259d4790cb6606 -/
section Source1564
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma sector_arithmetic_prescribed (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (hcommon : ∀ (x y : SourcePair rows Pset),
      (D x.val.1 x.val.2 x.property).fixedFactor=(D y.val.1 y.val.2 y.property).fixedFactor ∧
      ∀ u m n b,actualCuspColumn (D x.val.1 x.val.2 x.property) s hc u m n b=
        actualCuspColumn (D y.val.1 y.val.2 y.property) s hc u m n b)
    (D0 : ControlledStratumArithmetic F.generator N a c mode) :
    ∃ E : SectorArithmetic (N:=N) F rows Pset S hrows s hc,E.completion=D := by
  by_cases hn : Nonempty (SourcePair rows Pset)
  · let x0 : SourcePair rows Pset := Classical.choice hn
    exact ⟨{
      referenceIndex := φ⊕(PrimeIndex x0.val.1.val⊕σ)
      referencePrimes := F.reflected x0.val.1.val (hrows x0.val.1.val x0.val.1.property) (S x0.val.2.val)
      referenceArithmetic := D x0.val.1 x0.val.2 x0.property
      completion := D
      fixedFactor_eq := fun K P hp => (hcommon ⟨(K,P),hp⟩ x0).1
      cuspColumn_eq := fun K P hp => (hcommon ⟨(K,P),hp⟩ x0).2
    },rfl⟩
  · let F0 : PrimeFamily (ULift.{v} φ) := ⟨fun x => F.ideal x.down,fun x => F.maximal x.down,fun x => F.good x.down⟩
    let e : ULift.{v} φ ≃ φ := Equiv.ulift
    let D0' := reindexControlled D0 e
    exact ⟨{
      referenceIndex := ULift.{v} φ
      referencePrimes := F0
      referenceArithmetic := D0'
      completion := D
      fixedFactor_eq := fun K P hp => (hn ⟨⟨(K,P),hp⟩⟩).elim
      cuspColumn_eq := fun K P hp => (hn ⟨⟨(K,P),hp⟩⟩).elim
    },rfl⟩

theorem exists_global_sector_completion (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hac : IsCoprime a c) (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f,IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K∈rows,(∀ f,IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hprod : ∀ P∈Pset,(∏ i,(S P).ideal i)=P)
    (hScop : ∀ P∈Pset,Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal))
    (hSN : ∀ P∈Pset,∀ i,IsCoprime (Ideal.span {N}) ((S P).ideal i)) :
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode,
    ∀ r p : Eis⧸Ideal.span {N^2},
    ∃ E : SectorArithmetic (N:=N) F (fullRaySector N rows r) (fullRaySector N Pset p) S
      (fun K hK => hrows K (Finset.mem_filter.mp hK).1) s hc,
    ∀ (K : fullRaySector N rows r) (P : fullRaySector N Pset p) hp,
      E.completion K P hp=D ⟨K.val,(Finset.mem_filter.mp K.property).1⟩
        ⟨P.val,(Finset.mem_filter.mp P.property).1⟩ hp := by
  obtain ⟨Dpair,κ,A,_,_,hκ,hA⟩ := exists_source_pair_templates F rows Pset S hrows hprod N a c mode s hc
    hN hbase hac hF hNF hrowcop hScop hSN
  let D := fun (K : rows) (P : Pset) (hp : IsCoprime K.val P.val) => Dpair ⟨(K,P),hp⟩
  refine ⟨D,?_⟩
  intro r p
  let Ds := fun (K : fullRaySector N rows r) (P : fullRaySector N Pset p) (hp : IsCoprime K.val P.val) =>
    D ⟨K.val,(Finset.mem_filter.mp K.property).1⟩ ⟨P.val,(Finset.mem_filter.mp P.property).1⟩ hp
  have hh (x y : SourcePair (fullRaySector N rows r) (fullRaySector N Pset p)) :
      (Ds x.val.1 x.val.2 x.property).fixedFactor=(Ds y.val.1 y.val.2 y.property).fixedFactor ∧
      ∀ u m n b,actualCuspColumn (Ds x.val.1 x.val.2 x.property) s hc u m n b=
        actualCuspColumn (Ds y.val.1 y.val.2 y.property) s hc u m n b := by
    have hsector (x : SourcePair (fullRaySector N rows r) (fullRaySector N Pset p)) :
        separateSector N (primaryGenerator x.val.1.val) (primaryGenerator x.val.2.val)=(r,p) :=
      Prod.ext (Finset.mem_filter.mp x.val.1.property).2 (Finset.mem_filter.mp x.val.2.property).2
    let lift (z : SourcePair (fullRaySector N rows r) (fullRaySector N Pset p)) :
        SourcePair rows Pset :=
      ⟨(⟨z.val.1.val, (Finset.mem_filter.mp z.val.1.property).1⟩,
        ⟨z.val.2.val, (Finset.mem_filter.mp z.val.2.property).1⟩), z.property⟩
    constructor
    · dsimp only [Ds,D]
      exact (hκ (lift x)).trans ((congrArg κ ((hsector x).trans (hsector y).symm)).trans (hκ (lift y)).symm)
    · intro u m n b
      dsimp only [Ds,D]
      exact (hA (lift x) u m n b).trans
        ((congrArg (fun q => A q u m n b) ((hsector x).trans (hsector y).symm)).trans
          (hA (lift y) u m n b).symm)
  obtain ⟨D0⟩ := F.exists_controlled N a c mode hc hN hbase hac hF hNF
  obtain ⟨E,hE⟩ := sector_arithmetic_prescribed F (fullRaySector N rows r) (fullRaySector N Pset p) S
    (fun K hK => hrows K (Finset.mem_filter.mp hK).1) s hc Ds hh D0
  refine ⟨E,?_⟩
  intro K P hp
  rw [hE]
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1564

/- Original source: OAI/NumberTheory/DirichletL/Reflection/KernelBaseline.lean; sha256: d5301cad5df2082759dbaea49c6e91cf9ca9af49a5855492f345c8bdceea7c0e -/
section Source1565
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem mixedReflectedValue_eq_actualKernelSource (F : PrimeFamily φ)
    (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue D s (F.reflected K hK S).generator_ne_zero hc
      (F.reflected K hK S).generator_good (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ) W X =
    fixedRadialCoefficientScalar*s.stratumShapeFactor (c*∏ i, (F.reflected K hK S).generator i)*
      ∑' t : ThetaFullIndex,
        actualKernelSourceTerm F K hK S jF D s hc t.1 t.2.1 t.2.2.1.val t.2.2.2.val
          (fun _ _ => 1) 1 1 1 1 W 0 X := by
  unfold mixedReflectedValue
  congr 1
  apply tsum_congr
  intro t
  have hx : sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t) =
      s.modelDualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val := by
    rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
    rfl
  have hW : CompletedHeight.normTwistedSource W 0 = W := by
    funext x
    simp [CompletedHeight.normTwistedSource,FourierBridge.logPhase]
  unfold actualKernelSourceTerm actualMixedCoefficient
  rw [hx,hW]
  simp only [Finset.prod_const_one,one_div]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1565

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CrudeCoefficient.lean; sha256: 42887e84e33fd324842e4a9c3d5a47fddf052d6c1a8c1f8f2f10e4298ea9f666 -/
section Source1566
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve LocalReflectionBrackets InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma norm_bracket_le_card {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (j : ℕ) (x : F) : ‖bracket χ j x‖≤(Fintype.card F:ℝ) := by
  have hq : (1:ℝ)≤Fintype.card F := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0:F)⟩
  have hr : 1≤rootCard F := by
    unfold rootCard
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hq)
  have hi : (rootCard F)⁻¹≤1 := (inv_le_one₀ rootCard_pos).mpr hr
  by_cases hj4 : j=4
  · subst j
    by_cases hx : x=0
    · subst x
      rw [norm_bracket_four_zero]
      apply (div_le_iff₀ rootCard_pos).mpr
      nlinarith
    · rw [norm_bracket_four_nonzero χ x hx]
      exact hi.trans hq
  · by_cases hj0 : j=0
    · subst j
      exact (norm_bracket_zero_le χ x).trans (hi.trans hq)
    · exact (norm_bracket_nonexceptional_le_one χ j hj4 hj0 x).trans hq

variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

lemma mixedActiveBracket_crude_norm (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (i : ι) (x : Eis) :
    ‖mixedActiveBracket G.generator_ne_zero G.generator_good j S D i x‖≤(Ideal.absNorm (G.ideal i):ℝ) := by
  rw [mixedActiveBracket_eq_signed]
  have hn : ‖(if i∈S then (-1:ℂ) else 1)‖=1 := by split_ifs <;> simp
  have hjm : markedActiveExponent S j i<6 := by
    unfold markedActiveExponent
    split_ifs
    · norm_num
    · exact hj i
  have hc : ∀ i, ringChar (Eis⧸Ideal.span {G.generator i})≠2 := by
    intro i
    rw [G.generator_span]
    exact hchar i
  rw [norm_mul,hn,one_mul,norm_mul,local_phase_norm D G.generator_ne_zero G.generator_good hc i _ hjm,one_mul]
  apply (norm_bracket_le_card _ _ _).trans_eq
  have he : Fintype.card (Eis⧸Ideal.span {G.generator i})=Ideal.absNorm (Ideal.span {G.generator i}) := by
    rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
  rw [he,G.generator_span]

lemma literal_mixed_coefficient_crude (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    ‖s.amplitude u m n b *
      (star D.fixedFactor*ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m n b))*
      ∏ i, mixedActiveBracket G.generator_ne_zero G.generator_good j S D i (s.modelDualNumerator u m n b)‖≤
      (Ideal.absNorm (∏ i,G.ideal i):ℝ) := by
  rw [norm_mul,norm_mul,norm_mul,norm_star,D.fixedFactor_norm hN G.generator_product_primary hbase,
    ShortDraftCusp.A4BadPhase_norm,one_mul,mul_one]
  apply (mul_le_of_le_one_left (norm_nonneg _) (s.amplitude_norm u m n b)).trans
  rw [norm_prod,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun i hi => norm_nonneg _) (fun i hi => mixedActiveBracket_crude_norm G D hchar j hj S i _)

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1566

/- Original source: OAI/NumberTheory/DirichletL/Reflection/RawTail.lean; sha256: 6e4047b7ac0903ed24493c9982b3b6d00082da02b89cf5538bff52d9b15dccfa -/
section Source1567
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

abbrev RawTailIndex := ℕ×NonzeroDualIdeal×NonzeroDualIdeal

def rawTailWeight (q : ℝ) (x : RawTailIndex) : ℝ :=
  ((q^6)⁻¹)^x.1*((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹

lemma rawTailWeight_nonneg (q : ℝ) (x : RawTailIndex) : 0≤rawTailWeight q x := by
  unfold rawTailWeight
  positivity

lemma rawTailWeight_summable (q : ℝ) (hq : 1<q) : Summable (rawTailWeight q) := by
  have hq6 : 1<q^6 := one_lt_pow₀ hq (by norm_num)
  have hg : Summable (fun m : ℕ => ((q^6)⁻¹)^m) :=
    summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ (by positivity)).mpr hq6)
  have hi := nonzeroDualIdeal_inv_pow_summable 2 (by norm_num)
  have hj := nonzeroDualIdeal_inv_pow_summable 6 (by norm_num)
  have hh := hg.mul_of_nonneg (hi.mul_of_nonneg hj (fun I => by positivity) (fun J => by positivity))
    (fun m => by positivity) (fun IJ => by positivity)
  exact hh.congr (fun x => by simp only [rawTailWeight]; ring)

lemma tail_power_gain (A : ℕ) (T x : ℝ) (hT : 0<T) (hTx : T≤x) :
    x^(-((A+2:ℕ):ℝ))≤T^(-(A:ℝ))*(x^2)⁻¹ := by
  have hx : 0<x := lt_of_lt_of_le hT hTx
  rw [show -((A+2:ℕ):ℝ)=-(A:ℝ)+(-2) by push_cast; ring,Real.rpow_add hx]
  rw [show x^(-2:ℝ)=(x^2)⁻¹ by rw [Real.rpow_neg hx.le,Real.rpow_two]]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hT hTx (neg_nonpos.mpr (Nat.cast_nonneg A))) (by positivity)

theorem raw_kernel_tail (a b q : ℝ) (ha : 0<a) (hq : 1<q) (A : ℕ) :
    ∃ (S : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc a b →
    ∀ (scale ρ B T : ℝ), 0<scale → 0<ρ → 0≤B → 0<T →
    ∀ (β : ℕ→Ideal Eis→Ideal Eis→ℂ),
      (∀ m, ∀ I J : NonzeroDualIdeal, ‖β m I.val J.val‖≤B) →
    ∀ cut : RawTailIndex→Prop,
      (∀ x, cut x → T≤scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3) →
    Summable (fun x => ‖if cut x then rawDualKernelTerm V scale ρ q β x else 0‖) ∧
      ‖∑' x, if cut x then rawDualKernelTerm V scale ρ q β x else 0‖≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*B*T^(-(A:ℝ))*(scale^2*ρ^6)⁻¹ := by
  obtain ⟨S,C,hC,hkernel⟩ := CubicReflectionKernel.paperKernel_euler_source_power_decay a b ha (A+2) 0
  let D : ℝ := (∑' x,rawTailWeight q x)+1
  have hsum := rawTailWeight_summable q hq
  have hD : 0<D := by
    have h : 0≤∑' x,rawTailWeight q x := tsum_nonneg (rawTailWeight_nonneg q)
    dsimp only [D]
    linarith
  refine ⟨S,C*D,mul_pos hC hD,?_⟩
  intro V hV scale ρ B T hs hρ hB hT β hβ cut hcut
  let M : ℝ := C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*B*T^(-(A:ℝ))*(scale^2*ρ^6)⁻¹
  have hM : 0≤M := by dsimp only [M]; positivity
  have hmajor : ∀ x : RawTailIndex,
      ‖if cut x then rawDualKernelTerm V scale ρ q β x else 0‖≤M*rawTailWeight q x := by
    intro x
    by_cases hx : cut x
    · rw [ite_eq_left hx,rawDualKernelTerm,norm_mul]
      let arg := scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3
      have harg : 0<arg := lt_of_lt_of_le hT (hcut x hx)
      have hk := (hkernel V hV arg harg).2
      simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hk
      have hp := tail_power_gain A T arg hT (hcut x hx)
      have hk' := hk.trans (mul_le_mul_of_nonneg_left hp (by positivity :
        0≤C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V))
      apply (mul_le_mul (hβ x.1 x.2.1 x.2.2) hk' (norm_nonneg _) hB).trans_eq
      dsimp only [M,arg]
      rw [rawDualKernel_inverse_square]
      unfold rawTailWeight
      ring
    · rw [ite_eq_right hx,norm_zero]
      exact mul_nonneg hM (rawTailWeight_nonneg q x)
  have hn := (hsum.mul_left M).of_nonneg_of_le (fun x => norm_nonneg _) hmajor
  refine ⟨hn,?_⟩
  calc
    _ ≤ ∑' x, ‖if cut x then rawDualKernelTerm V scale ρ q β x else 0‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' x, M*rawTailWeight q x := hn.tsum_le_tsum hmajor (hsum.mul_left M)
    _ = M*(∑' x,rawTailWeight q x) := tsum_mul_left
    _ ≤ M*D := mul_le_mul_of_nonneg_left (by dsimp only [D]; linarith) hM
    _ = _ := by dsimp only [M]; ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1567

/- Original source: OAI/NumberTheory/DirichletL/Reflection/RawCoefficient.lean; sha256: 321442ae80aef7223c34f9f49355acf250a15d9ea0fa2aeb5e3f2908f074b93a -/
section Source1568
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def literalRawCoefficient (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  if Squarefree n ∧ primaryGenerator n≠0 ∧ primaryGenerator b≠0 then
    (s.amplitude u m n b *
      (star D.fixedFactor*ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m n b))*
      ∏ i, mixedActiveBracket G.generator_ne_zero G.generator_good j S D i (s.modelDualNumerator u m n b)) /
        ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ):ℝ):ℂ)
  else 0

lemma literalRawCoefficient_norm (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : NonzeroDualIdeal) :
    ‖literalRawCoefficient G D s hc j S u m n.val b.val‖≤(Ideal.absNorm (∏ i,G.ideal i):ℝ) := by
  unfold literalRawCoefficient
  split_ifs
  · have hr : 1≤ramifiedScale 1 completedRamifiedStep m := by
      simpa only [ramifiedScale,one_mul] using one_le_pow₀ completedRamifiedStep_gt_one.le (n:=m)
    have hn : 1≤Real.sqrt (Ideal.absNorm n.val:ℝ) :=
      (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by simpa using norm_at_least_one n.val n.property)
    have hb := norm_at_least_one b.val b.property
    have hden : 1≤ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n.val:ℝ)*(Ideal.absNorm b.val:ℝ) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hr hn) hb
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (le_trans zero_le_one hden)]
    apply (div_le_div_of_nonneg_right (literal_mixed_coefficient_crude G D s hc hN hbase hchar j hj S u m n.val b.val)
      (le_trans zero_le_one hden)).trans
    exact div_le_self (Nat.cast_nonneg _) hden
  · simp only [norm_zero]
    exact Nat.cast_nonneg _

theorem literal_reflected_raw_tail (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
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
  intro V hV G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  have hh := hb V hV scale 1 (Ideal.absNorm (∏ i,G.ideal i):ℝ) T hs (by norm_num) (Nat.cast_nonneg _) hT
    (literalRawCoefficient G D s hc j S u) (literalRawCoefficient_norm G D s hc hN hbase hchar j hj S u) cut hcut
  simpa only [one_pow,mul_one] using hh
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1568

/- Original source: OAI/NumberTheory/DirichletL/Reflection/FullRaw.lean; sha256: aa62739f20e7293ce59939654822b2e577aff9e29b6fcd35d84dcec86fa15280 -/
section Source1569
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def thetaRawIndex (t : ThetaFullIndex) : Eisˣ×RawTailIndex :=
  (t.1,t.2.1,⟨t.2.2.1.val,t.2.2.1.property.1.ne_zero⟩,
    ⟨t.2.2.2.val,primaryGenerator_ne_zero_ideal _ t.2.2.2.property⟩)

lemma thetaRawIndex_injective : Function.Injective thetaRawIndex := by
  rintro ⟨u,m,⟨n,hn⟩,⟨b,hb⟩⟩ ⟨v,k,⟨n',hn'⟩,⟨b',hb'⟩⟩ h
  simpa only [thetaRawIndex,Prod.mk.injEq,Subtype.mk.injEq] using h

def literalRawScale (G : PrimeFamily ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (X : ℝ) : ℝ :=
  X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c*∏ i,G.generator i}):ℝ)^2)

lemma literalRawScale_pos (G : PrimeFamily ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (X : ℝ) (hX : 0<X) : 0<literalRawScale G s X := by
  have hn : (0:ℝ)<Ideal.absNorm (Ideal.span {c*∏ i,G.generator i}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun i _ => G.generator_ne_zero i)))))
  have hs := sourceCuspScale_pos s.index
  unfold literalRawScale
  positivity

def literalRawSeries (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) (t : Eisˣ×RawTailIndex) : ℂ :=
  rawDualKernelTerm (Vstar W) (literalRawScale G s X) 1 completedRamifiedStep
    (literalRawCoefficient G D s hc j S t.1) t.2

lemma literalRawSeries_support (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    Function.support (literalRawSeries G D s hc j S W X)⊆Set.range thetaRawIndex := by
  intro t ht
  have hp : Squarefree t.2.2.1.val ∧ primaryGenerator t.2.2.1.val≠0 ∧ primaryGenerator t.2.2.2.val≠0 := by
    by_contra hn
    exact ht (by simp only [literalRawSeries,rawDualKernelTerm,literalRawCoefficient,ite_eq_right hn,zero_mul])
  exact ⟨(t.1,t.2.1,⟨t.2.2.1.val,hp.1,hp.2.1⟩,⟨t.2.2.2.val,hp.2.2⟩),rfl⟩

theorem mixedReflectedValue_eq_fullRaw (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue D s G.generator_ne_zero hc G.generator_good j S W X=
      fixedRadialCoefficientScalar*s.stratumShapeFactor (c*∏ i,G.generator i)*
        ∑' t : Eisˣ×RawTailIndex, literalRawSeries G D s hc j S W X t := by
  unfold mixedReflectedValue
  congr 1
  refine (tsum_congr ?_).trans (thetaRawIndex_injective.tsum_eq (literalRawSeries_support G D s hc j S W X))
  intro t
  have hx : sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)=
      s.modelDualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val := by
    rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
    rfl
  unfold literalRawSeries rawDualKernelTerm literalRawCoefficient thetaRawIndex literalRawScale
  rw [ite_eq_left ⟨t.2.2.1.property.1,t.2.2.1.property.2,t.2.2.2.property⟩,hx]
  dsimp only
  simp only [ramifiedScale, one_mul]
  ring

theorem literalRawSeries_summable_norm (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    Summable (fun t : Eisˣ×RawTailIndex => ‖literalRawSeries G D s hc j S W X t‖) := by
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨?_,(hasSum_fintype _).summable⟩
  intro u
  exact rawDualKernelTerm_summable_norm (Vstar W) lo hi hlo (Vstar_support W lo hi hWs)
    (Vstar_contDiff W lo hi hlo hWs hW) (literalRawScale G s X) 1 completedRamifiedStep
    (Ideal.absNorm (∏ i,G.ideal i):ℝ) (literalRawScale_pos G s hc X hX) (by norm_num)
    completedRamifiedStep_gt_one (Nat.cast_nonneg _) (literalRawCoefficient G D s hc j S u)
    (literalRawCoefficient_norm G D s hc hN hbase hchar j hj S u)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1569

/- Original source: OAI/NumberTheory/DirichletL/Reflection/FullDyadic.lean; sha256: d2fe740d9a34855c5fb9ebb8fda5e26fa87f66384dbca9e7f2a8860dd9e8a077 -/
section Source1570
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def literalDyadicBlock (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) (u : Eisˣ) (i : ℕ×ℕ×ℕ) : ℂ :=
  ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
    literalRawSeries G D s hc j S W X
      (u,i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)

theorem mixedReflectedValue_eq_dyadic (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    mixedReflectedValue D s G.generator_ne_zero hc G.generator_good j S W X=
      fixedRadialCoefficientScalar*s.stratumShapeFactor (c*∏ i,G.generator i)*
        ∑' u : Eisˣ, ∑' i : ℕ×ℕ×ℕ, literalDyadicBlock G D s hc j S W X u i := by
  have hs := (literalRawSeries_summable_norm G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm
  rw [mixedReflectedValue_eq_fullRaw,hs.tsum_prod]
  congr 1
  apply tsum_congr
  intro u
  exact tsum_dualIdealDyads _ (hs.prod_factor u)

lemma dyadic_kernel_argument_lower (scale rho q : ℝ) (hs : 0≤scale)
    (hr : 0≤rho) (hq : 0≤q) (i : ℕ×ℕ×ℕ)
    (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1) :
    scale*(ramifiedScale rho q i.1)^3*(2:ℝ)^i.2.2*((2:ℝ)^i.2.1)^3/16 ≤
      scale*(ramifiedScale rho q i.1)^3*(Ideal.absNorm n.val:ℝ)*(Ideal.absNorm b.val:ℝ)^3 := by
  have hn := (dualIdealDyad_bounds _ _ n.property).2.1
  have hb := (dualIdealDyad_bounds _ _ b.property).2.1
  have hp : 0≤scale*(ramifiedScale rho q i.1)^3 := by
    unfold ramifiedScale
    positivity
  have hh := mul_le_mul hn (pow_le_pow_left₀ (by positivity) hb 3) (by positivity)
    (Nat.cast_nonneg (Ideal.absNorm n.val))
  have hh' := mul_le_mul_of_nonneg_left hh hp
  nlinarith only [hh']

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1570

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ShellSource.lean; sha256: 64790129209daadb643048c47e3cf616e778c020c3b32757f2c8d199b5390f05 -/
section Source1571
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma shell_windows_one (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (K P : Ideal Eis) (hK : K≠0) (hP : P≠0)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP)
    (j k : ℕ) (n : dualIdealDyad k) (b : dualIdealDyad j) :
    (∏ i : Fin 4, completedShellWindow (kernelLogCoordinates QK QP ((2:ℝ)^k) ((2:ℝ)^j)
      (Ideal.absNorm K:ℝ) (Ideal.absNorm P:ℝ) (Ideal.absNorm n.val:ℝ) (Ideal.absNorm b.val:ℝ) i))=1 := by
  have hnorm (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hn := dualIdealDyad_bounds k n.val n.property
  have hb := dualIdealDyad_bounds j b.val b.property
  apply Finset.prod_eq_one
  intro i hi
  fin_cases i <;> dsimp only [kernelLogCoordinates, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact completedShellWindow_log _ _ (hnorm K hK) hQK hKr.1 hKr.2
  · exact completedShellWindow_log _ _ (hnorm P hP) hQP hPr.1 hPr.2
  · exact completedShellWindow_log _ _ (hnorm n.val hn.1) (by positivity) hn.2.1 hn.2.2
  · exact completedShellWindow_log _ _ (hnorm b.val hb.1) (by positivity) hb.2.1 hb.2.2

theorem literalRawSeries_eq_shell_source (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1)
    (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    literalRawSeries (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X
      (u,i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)=
    if CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0 then
      actualKernelSourceTerm F K hK S jF D s hc u i.1 n.val b.val
        (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X else 0 := by
  have hw := shell_windows_one QK QP hQK hQP K (∏ i,S.ideal i) hK.1
    (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (S.ideal i))) hKr hPr i.2.1 i.2.2 n b
  by_cases hp : CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0
  · have hp' : Squarefree n.val ∧ primaryGenerator n.val≠0 ∧ primaryGenerator b.val≠0 :=
      ⟨hp.1.1,hp.1.2,hp.2⟩
    rw [ite_eq_left hp]
    unfold literalRawSeries rawDualKernelTerm literalRawCoefficient actualKernelSourceTerm actualMixedCoefficient literalRawScale
    rw [ite_eq_left hp',hw]
    dsimp only
    simp only [ramifiedScale,one_mul]
    ring
  · have hp' : ¬(Squarefree n.val ∧ primaryGenerator n.val≠0 ∧ primaryGenerator b.val≠0) :=
      fun h => hp ⟨⟨h.1,h.2.1⟩,h.2.2⟩
    simp only [ite_eq_right hp,literalRawSeries,rawDualKernelTerm,literalRawCoefficient,ite_eq_right hp',zero_mul]

theorem literalDyadicBlock_eq_shell_source (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    literalDyadicBlock (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i=
      ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
        if CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0 then
          actualKernelSourceTerm F K hK S jF D s hc u i.1 n.val b.val
            (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X else 0 := by
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  exact literalRawSeries_eq_shell_source F K hK S jF D s hc u i n b QK QP hQK hQP hKr hPr W θ X
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1571

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ShellDomains.lean; sha256: 2bb75ecaf5c25782c32478fba5649642b5303422b1ac00be933da8f7d2532e69 -/
section Source1572
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def reflectedNDyad (k : ℕ) : Finset (Ideal Eis) :=
  (dualIdealDyad k).filter CubicSieve.Admissible

def reflectedBDyad (j : ℕ) : Finset (Ideal Eis) :=
  (dualIdealDyad j).filter (fun b => primaryGenerator b≠0)

lemma reflectedNDyad_bounds (k : ℕ) : ∀ n∈reflectedNDyad k,
    CubicSieve.Admissible n ∧ (2:ℝ)^k/2≤(Ideal.absNorm n:ℝ) ∧ (Ideal.absNorm n:ℝ)≤(2:ℝ)^k := by
  intro n hn
  exact ⟨(Finset.mem_filter.mp hn).2,(dualIdealDyad_bounds k n (Finset.mem_filter.mp hn).1).2⟩

lemma reflectedBDyad_bounds (j : ℕ) : ∀ b∈reflectedBDyad j,
    primaryGenerator b≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm b:ℝ) ∧ (Ideal.absNorm b:ℝ)≤(2:ℝ)^j := by
  intro b hb
  exact ⟨(Finset.mem_filter.mp hb).2,(dualIdealDyad_bounds j b (Finset.mem_filter.mp hb).1).2⟩

lemma double_sum_coe (A B : Finset (Ideal Eis)) (f : Ideal Eis→Ideal Eis→ℂ) :
    (∑ n : A, ∑ b : B, f n.val b.val)=∑ n∈A, ∑ b∈B, f n b := by
  rw [Finset.sum_coe_sort A (fun n : Ideal Eis => ∑ b : B, f n b.val)]
  apply Finset.sum_congr rfl
  intro n hn
  exact Finset.sum_coe_sort B (f n)

lemma sum_dual_mask (j k : ℕ) (f : Ideal Eis→Ideal Eis→ℂ) :
    (∑ n : dualIdealDyad k, ∑ b : dualIdealDyad j,
      if CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0 then f n.val b.val else 0)=
      ∑ n : reflectedNDyad k, ∑ b : reflectedBDyad j, f n.val b.val := by
  rw [double_sum_coe (dualIdealDyad k) (dualIdealDyad j)
    (fun n b => if CubicSieve.Admissible n ∧ primaryGenerator b≠0 then f n b else 0),
    double_sum_coe (reflectedNDyad k) (reflectedBDyad j) f]
  simp only [reflectedNDyad,reflectedBDyad,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn' : CubicSieve.Admissible n
  · simp only [hn',true_and,ite_eq_left]
  · simp only [hn',false_and,ite_false,Finset.sum_const_zero]

theorem literalDyadicBlock_eq_filtered_source (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    literalDyadicBlock (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i=
      ∑ n : reflectedNDyad i.2.2, ∑ b : reflectedBDyad i.2.1,
        actualKernelSourceTerm F K hK S jF D s hc u i.1 n.val b.val
          (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X := by
  rw [literalDyadicBlock_eq_shell_source F K hK S jF D s hc u i QK QP hQK hQP hKr hPr W θ X]
  exact sum_dual_mask i.2.1 i.2.2 (fun n b => actualKernelSourceTerm F K hK S jF D s hc u i.1 n b
    (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1572

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ShellRows.lean; sha256: 6ae45151b779546a5ef853487340ca4164bff20ca3525573e9722d21e156c152 -/
section Source1573
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def literalDyadicRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    literalDyadicBlock (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc
      (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) X u i

theorem literalDyadicRow_eq_physical (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hprod : ∀ P∈Pset, (∏ j,(S P).ideal j)=P)
    (hPr : ∀ P∈Pset, QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) :
    literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw=
      weightedFinitePhysicalKernelRow F K hK S jF Pset (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
        D s hc u i.1 (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
        W θ X r aw (fun _ _ => 1) := by
  unfold literalDyadicRow weightedFinitePhysicalKernelRow CoprimeSourceIndex
  simp only [Fintype.sum_prod_type,mul_one]
  apply Finset.sum_congr rfl
  intro P hP
  have hp : QP/2≤(Ideal.absNorm (∏ j,(S P.val.val).ideal j):ℝ) ∧
      (Ideal.absNorm (∏ j,(S P.val.val).ideal j):ℝ)≤QP := by
    rw [hprod P.val.val P.val.property]
    exact hPr P.val.val P.val.property
  rw [literalDyadicBlock_eq_filtered_source F K hK (S P.val.val) jF (D P.val P.property)
    s hc u i QK QP hQK hQP hKr hp W θ X]
  simp only [Finset.mul_sum]
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1573

/- Original source: OAI/NumberTheory/DirichletL/Reflection/DyadicTail.lean; sha256: b35dce5dfd02cce176b45d41c46c0c4362740f9812a593365ae2ac21a1232221 -/
section Source1574
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def rawDyadicLabel (x : RawTailIndex) : ℕ×ℕ×ℕ :=
  (x.1,Nat.clog 2 (Ideal.absNorm x.2.2.val),Nat.clog 2 (Ideal.absNorm x.2.1.val))

def rawDyadicCenter (scale : ℝ) (i : ℕ×ℕ×ℕ) : ℝ :=
  scale*(ramifiedScale 1 completedRamifiedStep i.1)^3*(2:ℝ)^i.2.2*((2:ℝ)^i.2.1)^3

lemma rawDyadicCenter_lower (scale : ℝ) (hs : 0≤scale) (x : RawTailIndex) :
    rawDyadicCenter scale (rawDyadicLabel x)/16 ≤
      scale*(ramifiedScale 1 completedRamifiedStep x.1)^3*
        (Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3 := by
  exact dyadic_kernel_argument_lower scale 1 completedRamifiedStep hs (by norm_num)
    (le_trans zero_le_one completedRamifiedStep_gt_one.le) (rawDyadicLabel x)
    ⟨x.2.1.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.1.property,rfl⟩⟩
    ⟨x.2.2.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.2.property,rfl⟩⟩

theorem tsum_cut_dyadic (f : RawTailIndex→ℂ) (cut : (ℕ×ℕ×ℕ)→Prop)
    (hf : Summable (fun x => if cut (rawDyadicLabel x) then f x else 0)) :
    (∑' x, if cut (rawDyadicLabel x) then f x else 0)=
      ∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          f (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
            ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0 := by
  rw [tsum_dualIdealDyads _ hf]
  apply tsum_congr
  intro i
  have hl (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1) :
      rawDyadicLabel (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)=i := by
    simp only [rawDyadicLabel,((mem_dualIdealDyad _ _).mp n.property).2,
      ((mem_dualIdealDyad _ _).mp b.property).2]
  by_cases hi : cut i
  · simp only [hl,ite_eq_left hi]
  · simp only [hl,ite_eq_right hi,Finset.sum_const_zero]

theorem literal_reflected_dyadic_tail (lo hi : ℝ) (hlo : 0<lo) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc lo hi →
    ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
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
  obtain ⟨orders,C,hC,hb⟩ := literal_reflected_raw_tail (ι:=ι) (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A
  refine ⟨orders,C,hC,?_⟩
  intro V hV G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  obtain ⟨hn,hh⟩ := hb V hV G D s hc hN hbase hchar j hj S u scale T hs hT
    (fun x => cut (rawDyadicLabel x)) (fun x hx => by
      have hc' := hcut (rawDyadicLabel x) hx
      have hl := rawDyadicCenter_lower scale hs.le x
      linarith)
  rw [tsum_cut_dyadic _ cut hn.of_norm] at hh
  exact hh
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1574

/- Original source: OAI/NumberTheory/DirichletL/Reflection/DyadicBox.lean; sha256: 50bc40d79962351073652f1c6c2d79206f269037438c732e44193b67d3f6cd65 -/
section Source1575
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section

lemma ramifiedScale_one_cube (m : ℕ) : (ramifiedScale 1 completedRamifiedStep m)^3=(3:ℝ)^m := by
  have hs : completedRamifiedStep^3=(3:ℝ) := by
    unfold completedRamifiedStep
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  simp only [ramifiedScale,one_mul]
  rw [← pow_mul,Nat.mul_comm m 3,pow_mul,hs]

lemma rawDyadicCenter_pow_lower (scale : ℝ) (hs : 0≤scale) (i : ℕ×ℕ×ℕ) :
    scale*(2:ℝ)^(i.1+i.2.2+3*i.2.1)≤rawDyadicCenter scale i := by
  unfold rawDyadicCenter
  rw [ramifiedScale_one_cube,pow_add,pow_add,Nat.mul_comm 3 i.2.1,pow_mul]
  simp only [mul_assoc]
  have hm : (2:ℝ)^i.1≤(3:ℝ)^i.1 := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  gcongr

def retainedDyadicBox (scale B : ℝ) : Finset (ℕ×ℕ×ℕ) :=
  let n := columnDyadicLength (max 1 (B/scale))
  (Finset.range (n+1)) ×ˢ ((Finset.range (n+1)) ×ˢ (Finset.range (n+1)))

lemma center_mem_retainedDyadicBox (scale B : ℝ) (hs : 0<scale)
    (i : ℕ×ℕ×ℕ) (hi : rawDyadicCenter scale i≤B) : i∈retainedDyadicBox scale B := by
  let R := max 1 (B/scale)
  have hR : 1≤R := le_max_left _ _
  have hp : (2:ℝ)^(i.1+i.2.2+3*i.2.1)≤R :=
    ((le_div_iff₀ hs).mpr (by nlinarith only [rawDyadicCenter_pow_lower scale hs.le i,hi])).trans (le_max_right _ _)
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^(i.1+i.2.2+3*i.2.1)) hp
  rw [Real.log_pow] at hl
  have hc : ((i.1+i.2.2+3*i.2.1:ℕ):ℝ)≤columnDyadicLength R := by
    apply le_trans ((le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr hl)
    exact Nat.le_ceil _
  have hc' : i.1+i.2.2+3*i.2.1≤columnDyadicLength R := by exact_mod_cast hc
  simp only [retainedDyadicBox,Finset.mem_product,Finset.mem_range]
  change i.1<columnDyadicLength R+1 ∧ i.2.1<columnDyadicLength R+1 ∧ i.2.2<columnDyadicLength R+1
  omega

lemma retainedDyadicBox_card (scale B : ℝ) :
    (retainedDyadicBox scale B).card=(columnDyadicLength (max 1 (B/scale))+1)^3 := by
  simp only [retainedDyadicBox,Finset.card_product,Finset.card_range]
  ring

theorem retainedDyadicBox_count_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ scale B : ℝ,
      ((retainedDyadicBox scale B).card:ℝ)^2≤C*(max 1 (B/scale))^ε := by
  refine ⟨(2+1/((ε/6)*Real.log 2))^6,by positivity,?_⟩
  intro scale B
  have hR : 1≤max 1 (B/scale) := le_max_left _ _
  have hp : 0<max 1 (B/scale) := lt_of_lt_of_le zero_lt_one hR
  have hh := columnDyadicLength_small_power (ε/6) (by positivity) _ hR
  rw [retainedDyadicBox_card]
  push_cast
  rw [← pow_mul]
  norm_num only [show (3:ℕ)*2=6 by norm_num]
  apply (pow_le_pow_left₀ (by positivity) hh 6).trans_eq
  rw [mul_pow,← Real.rpow_mul_natCast hp.le]
  congr 2
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1575

/- Original source: OAI/NumberTheory/DirichletL/Reflection/HeightTail.lean; sha256: 6772fdadd7eb4c4a02777f30d53e806554700ade123f00826b666211426c6471 -/
section Source1576
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

theorem literal_dyadic_tail_uniform_height (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (θ X T : ℝ), 0<X → 0<T →
    ∀ cut : (ℕ×ℕ×ℕ)→Prop,
      (∀ i, cut i → 16*T≤rawDyadicCenter (literalRawScale G s X) i) →
      ‖∑' i : ℕ×ℕ×ℕ, if cut i then
        literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by
  obtain ⟨orders,C,hC,hbound⟩ := literal_reflected_dyadic_tail (ι:=ι) (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A
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
  intro G D s hc hN hbase hchar j hj S u θ X T hX hT cut hcut
  have hh := hbound (H θ) (hHs θ) G D s hc hN hbase hchar j hj S u
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
end SevenEighths.InverseReflectedPhase

end OAI

end Source1576

/- Original source: OAI/NumberTheory/DirichletL/Reflection/TruncatedSource.lean; sha256: e8e7a5776c505850ec4bb662b226fe7d2282b7c4e12b734b66457e4dfc436e3c -/
section Source1577
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def retainedDyads (scale B : ℝ) : Finset (ℕ×ℕ×ℕ) :=
  (retainedDyadicBox scale B).filter (fun i => rawDyadicCenter scale i≤B)

lemma mem_retainedDyads (scale B : ℝ) (hs : 0<scale) (i : ℕ×ℕ×ℕ) :
    i∈retainedDyads scale B ↔ rawDyadicCenter scale i≤B := by
  simp only [retainedDyads,Finset.mem_filter]
  exact ⟨And.right,fun hi => ⟨center_mem_retainedDyadicBox scale B hs i hi,hi⟩⟩

lemma retainedDyads_card_le (scale B : ℝ) :
    (retainedDyads scale B).card≤(retainedDyadicBox scale B).card := Finset.card_filter_le _ _

lemma literalDyadicBlock_summable (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) (u : Eisˣ) :
    Summable (literalDyadicBlock G D s hc j S W X u) := by
  have hs := ((literalRawSeries_summable_norm G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm).prod_factor u
  have hh := (dualDyadicIndexEquiv.symm.summable_iff.mpr hs).sigma
  apply hh.congr
  intro i
  simp only [tsum_fintype,Fintype.sum_prod_type,literalDyadicBlock,Function.comp_apply]
  rfl

lemma tsum_sub_finset_eq_tail {α : Type*} (f : α→ℂ) (hf : Summable f) (A : Finset α) :
    (∑' i,f i)-(∑ i∈A,f i)=∑' i,if i∉A then f i else 0 := by
  have hh := hf.sum_add_tsum_subtype_compl A
  have ht : (∑' x : {x // x∉A}, f x.val)=∑' i,if i∉A then f i else 0 := by
    calc
      _ = ∑' x, ({x | x∉A} : Set α).indicator f x := tsum_subtype {x | x∉A} f
      _ = _ := by
        apply tsum_congr
        intro i
        by_cases hi : i∈A <;> simp [hi]
  rw [ht] at hh
  exact eq_sub_of_add_eq' hh |>.symm

theorem actual_truncated_dyadic_tail (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (θ X T : ℝ), 0<X → 0<T →
      ‖(∑' i,literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i)-
        (∑ i∈retainedDyads (literalRawScale G s X) (16*T),
          literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i)‖≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by
  obtain ⟨degree,C,hC,hbound⟩ := literal_dyadic_tail_uniform_height (ι:=ι) (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro G D s hc hN hbase hchar j hj S u θ X T hX hT
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hs := literalDyadicBlock_summable G D s hc hN hbase hchar j hj S
    (CompletedHeight.normTwistedSource W θ) lo hi hlo
    ((CompletedHeight.normTwistedSource_support W θ).trans hWs) htw X hX u
  rw [tsum_sub_finset_eq_tail _ hs]
  have hb := hbound G D s hc hN hbase hchar j hj S u θ X T hX hT
    (fun i => i∉retainedDyads (literalRawScale G s X) (16*T))
    (fun i hi => (lt_of_not_ge (fun h => hi ((mem_retainedDyads _ _ (literalRawScale_pos G s hc X hX) i).mpr h))).le)
  apply le_trans ?_ hb
  apply le_of_eq
  congr 1
  apply tsum_congr
  intro i
  by_cases hi : i∈retainedDyads (literalRawScale G s X) (16*T) <;> simp [hi]
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1577

/- Original source: OAI/NumberTheory/DirichletL/Reflection/WholeRow.lean; sha256: 17a8523f814f48db5cd40a09ddb553a99ecd2d3416f22d1c55a4d04a29a9d0f1 -/
section Source1578
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def literalWholeRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    mixedReflectedValue (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
      (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X

lemma sum_tsum_tsum_finite_middle {α β γ : Type*} [Fintype β]
    (L : Finset α) (f : α→β→γ→ℂ) (hf : ∀ p∈L, ∀ u, Summable (f p u)) :
    (∑ p∈L,∑' u,∑' i,f p u i)=∑' u,∑' i,∑ p∈L,f p u i := by
  simp only [tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact (Summable.tsum_finsetSum (fun p hp => hf p hp u)).symm

theorem literalWholeRow_eq_dyadic (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2)
    (hj : ∀ i,jF i<6) (hprod : ∀ P∈Pset,(∏ j,(S P).ideal j)=P)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo) (hWs : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (θ X : ℝ) (hX : 0<X) (r aw : Ideal Eis→ℂ) :
    literalWholeRow F K hK S jF Pset D s hc W θ X r aw=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,
          literalDyadicRow F K hK S jF Pset D s hc u i W θ X
            (fun K => r K*shapeArgument (primaryGenerator K))
            (fun P => aw P*shapeArgument (primaryGenerator P)) := by
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hts := (CompletedHeight.normTwistedSource_support W θ).trans hWs
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) u i => literalDyadicBlock (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let wt := fun P : L => (r K*shapeArgument (primaryGenerator K))*(aw P.val.val*shapeArgument (primaryGenerator P.val.val))
  have hs (P : L) (u : Eisˣ) : Summable (fun i => wt P*block P u i) :=
    (literalDyadicBlock_summable (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX u).mul_left _
  have hp (P : L) : r K*aw P.val.val*
      mixedReflectedValue (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
        (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
        (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,wt P*block P u i := by
    rw [mixedReflectedValue_eq_dyadic (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX,
      actual_shape_separation,hprod P.val.val P.val.property]
    simp only [tsum_mul_left]
    dsimp only [wt,block]
    ring
  unfold literalWholeRow
  simp_rw [hp]
  rw [←Finset.mul_sum,sum_tsum_tsum_finite_middle Finset.univ (fun P u i => wt P*block P u i) (fun P _ u => hs P u)]
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1578

/- Original source: OAI/NumberTheory/DirichletL/Reflection/WholePair.lean; sha256: f1a10c6413dc7d53145debda427ce89e6e955aaeed357d45926dfd6e4e959964 -/
section Source1579
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma sum_subtype_dite {α : Type*} [Fintype α] (p : α→Prop) (f : ∀ x,p x→ℂ) :
    (∑ x : {x // p x},f x.val x.property)=∑ x,if h:p x then f x h else 0 := by
  have hh := Fintype.sum_subtype_add_sum_subtype p (fun x => if h:p x then f x h else 0)
  have hz : (∑ x : {x // ¬p x},if h:p x.val then f x.val h else 0)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact dite_eq_right x.property
  rw [hz,add_zero] at hh
  simpa only [Subtype.property,dite_eq_left] using hh

def literalPairEntry (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (K P : Ideal Eis) : ℂ :=
  if hK:K∈rows then if hP:P∈Pset then if hp:IsCoprime K P then
    r K*aw P*mixedReflectedValue (D ⟨K,hK⟩ ⟨P,hP⟩ hp) s
      (F.reflected K (hrows K hK) (S P)).generator_ne_zero hc
      (F.reflected K (hrows K hK) (S P)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X
  else 0 else 0 else 0

lemma literalWholeRow_eq_pairs (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (K : rows) :
    literalWholeRow F K.val (hrows K.val K.property) S jF Pset (D K) s hc W θ X r aw=
      ∑ P∈Pset,literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw K.val P := by
  let f := fun (P : Pset) (hp : IsCoprime K.val P.val) => r K.val*aw P.val*
    mixedReflectedValue (D K P hp) s (F.reflected K.val (hrows K.val K.property) (S P.val)).generator_ne_zero hc
      (F.reflected K.val (hrows K.val K.property) (S P.val)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X
  change (∑ P : {P : Pset // IsCoprime K.val P.val},f P.val P.property)=_
  rw [sum_subtype_dite (fun P : Pset => IsCoprime K.val P.val) f,
    ←Finset.sum_coe_sort Pset (literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw K.val)]
  apply Finset.sum_congr rfl
  intro P hP
  simp only [literalPairEntry,dite_eq_left K.property,dite_eq_left P.property,f]

lemma literalPairEntry_restrict (F : PrimeFamily φ) (rows Pset rows' Pset' : Finset (Ideal Eis))
    (hrow : rows'⊆rows) (hP : Pset'⊆Pset) (S : Ideal Eis→PrimeFamily σ)
    (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (E : SectorArithmetic (N:=N) F rows' Pset' S (fun K hK => hrows K (hrow hK)) s hc)
    (hE : ∀ (K : rows') (P : Pset') hp,E.completion K P hp=D ⟨K.val,hrow K.property⟩ ⟨P.val,hP P.property⟩ hp)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (K P : Ideal Eis) (hK : K∈rows') (hp : P∈Pset') :
    literalPairEntry F rows' Pset' S (fun K hK => hrows K (hrow hK)) jF E.completion s hc W θ X r aw K P=
      literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw K P := by
  simp only [literalPairEntry,dite_eq_left hK,dite_eq_left hp,dite_eq_left (hrow hK),dite_eq_left (hP hp)]
  by_cases hcop : IsCoprime K P
  · simp only [dite_eq_left hcop,hE]
  · simp only [dite_eq_right hcop]
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1579

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedTuples.lean; sha256: 7c9638130c35c55264bdad6d8bbdb80c6c28c132d704bbf83df8141605606327 -/
section Source1580
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
lemma sum_subtype_dite_decidable {α : Type*} [Fintype α] (p : α→Prop) [DecidablePred p]
    (f : ∀ x,p x→ℂ) :
    (∑ x : {x // p x},f x.val x.property)=∑ x,if h:p x then f x h else 0 := by
  have hh := Fintype.sum_subtype_add_sum_subtype p (fun x => if h:p x then f x h else 0)
  have hz : (∑ x : {x // ¬p x},if h:p x.val then f x.val h else 0)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact dite_eq_right x.property
  rw [hz,add_zero] at hh
  simpa only [Subtype.property,dite_eq_left] using hh

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable {α : Type*} [Fintype α] (Sp : α→PrimeFamily σ)
local notation "E" => D.primeFiberEquiv R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem actual_marked_tuple_reflection
    (hS : ∀ p,Pairwise (Function.onFun IsCoprime (Sp p).ideal))
    (hSodd : ∀ p i,ringChar (Eis⧸(Sp p).ideal i)≠2)
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h,(9:Eis)*(G h).c0∣N)
    (hNp : ∀ p i,IsCoprime (Ideal.span {N}) ((markedRowFamily D (Sp p) Q).ideal i))
    (C : ∀ p : {p : α // ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}),∀ i,(Sp p).ideal i≠P.val.val},
      ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ,ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected K hK ((Sp p.val).restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (w : α→ℂ) (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    (∑ p : α,w p*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (Sp p).ideal i∣A then (1:ℂ) else 0))=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
      ∑ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),∑ T : Finset σ,
        frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
        ∑ p : {p : α // ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}),∀ i,(Sp p).ideal i≠P.val.val},
          (∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm ((Sp p.val).ideal t):ℂ)⁻¹)*w p.val*
          mixedReflectedValue (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected K hK ((Sp p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected K hK ((Sp p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex K) T) W X := by
  let good := fun p : α => ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}),∀ i,(Sp p).ideal i≠P.val.val
  let row := fun p : α => markedCompletedT (rowTwist Ψ m f z) W X
    (fun A => ∏ i,if (Sp p).ideal i∣A then (1:ℂ) else 0)
  have hzrow (p : α) (hp : ¬good p) : row p=0 := by
    simp only [good,not_forall,not_not] at hp
    obtain ⟨P,i,he⟩ := hp
    exact actual_marked_row_overlap_zero D (Sp p) Ψ Q hmLam hm2 P i he W X
  have hrestrict : (∑ p : α,w p*row p)=∑ p : {p // good p},w p.val*row p.val := by
    calc
      _ = ∑ p : α,if h:good p then w p*row p else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hg : good p
        · rw [dite_eq_left hg]
        · rw [dite_eq_right hg,hzrow p hg,mul_zero]
      _ = _ := (sum_subtype_dite_decidable good (fun p _ => w p*row p)).symm
  change (∑ p : α,w p*row p)=_
  rw [hrestrict]
  have he (p : {p // good p}) := actual_marked_selected_reflection D R I F Q hR hI hF hm hf hz hbad hcop hpow hmask
    (Sp p.val) (hS p.val) (hSodd p.val) p.property Ψ hΨnorm hQ hΨperiod hmLam hm2 c hc hcQ G N hN
    (hNp p.val) (C p) W hWcompact lo hi hlo hsupp hW X hX
  dsimp only [row]
  simp_rw [he]
  simp only [Finset.mul_sum,frozenInactiveWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro p hp
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1580

/- Original source: OAI/NumberTheory/DirichletL/Reflection/PunctureAbsorption.lean; sha256: afaaafa52eed40a8409baa65b591ad57ff74a3d0c9b6ab531b66128811ebcab6 -/
section Source1581
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem rowTwist_absorb_puncture (Ψ : Eis→*ℂ) (m B f z : Eis)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hΨzero : ∀ n,¬IsCoprime B n → Ψ n=0) :
    rowTwist Ψ (m*B) f z=rowTwist Ψ m f z := by
  ext n
  by_cases hn : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask Ψ (m*B) f z n hn,rowTwist_extract_sixth_mask Ψ m f z n hn]
    by_cases hb : IsCoprime B n
    · change Ψ n*(if IsCoprime (m*B) n then (1:ℂ) else 0)*_=
        Ψ n*(if IsCoprime m n then (1:ℂ) else 0)*_
      simp only [IsCoprime.mul_left_iff,hb,and_true]
    · rw [hΨzero n hb]
      simp only [zero_mul]
  · rw [rowTwist_zero_of_not_supported Ψ (m*B) f z n
        (dvd_mul_of_dvd_left hmLam B) (dvd_mul_of_dvd_left hm2 B) hn,
      rowTwist_zero_of_not_supported Ψ m f z n hmLam hm2 hn]

lemma markedCompletedT_absorb_puncture (Ψ : Eis→*ℂ) (m B f z : Eis)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hΨzero : ∀ n,¬IsCoprime B n → Ψ n=0)
    (W : ℝ→ℂ) (X : ℝ) (mark : Ideal Eis→ℂ) :
    markedCompletedT (rowTwist Ψ (m*B) f z) W X mark=
      markedCompletedT (rowTwist Ψ m f z) W X mark := by
  rw [rowTwist_absorb_puncture Ψ m B f z hmLam hm2 hΨzero]

lemma rowResidualPart_coprime_period (I F Q : Ideal Eis) (m : Eis)
    (hQ : Q∣Ideal.span {m}) :
    IsCoprime Q (rowResidualPart I (Ideal.span {m}*F)) := by
  exact (squarefreeResidualPart_coprime (rowSimplePart I) (Ideal.span {m}*F)).symm.of_isCoprime_of_dvd_left
    (dvd_mul_of_dvd_left hQ F)

lemma rowResidualPart_coprime_enlarged_period (I F Q : Ideal Eis) (m B : Eis)
    (hQ : Q∣Ideal.span {B}) :
    IsCoprime Q (rowResidualPart I (Ideal.span {m*B}*F)) := by
  apply rowResidualPart_coprime_period I F Q (m*B)
  rw [←Ideal.span_singleton_mul_span_singleton]
  exact dvd_mul_of_dvd_right hQ _

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1581

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowTruePeriodPuncture.lean; sha256: 466017a739db5802f84f2b8b1fb5039f6df7ed93611d8e79d86259a02e6270ed -/
section Source1582
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss RayFourExpansion SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalRayPeriodicBase_support (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (n : O) (hn : physicalRayPeriodicBase η S hS σ χ n≠0) :
    IsCoprime (Ideal.span {n}) (lowPeriodIdeal η S hS) := by
  let C := calibrationForSet S hS
  let D := calibrationLowData S hS
  change ((rayMonoid χ n*HeckeFamily.elementCoeff η n)*
    star (C.residueMonoid n*CanonicalRowCompletion.actualPeriodicRow 1 C.generator
      D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n))*
      _≠0 at hn
  have ha := left_ne_zero_of_mul hn
  have heta := right_ne_zero_of_mul (left_ne_zero_of_mul ha)
  have hres := left_ne_zero_of_mul (star_ne_zero.mp (right_ne_zero_of_mul ha))
  have hc : IsCoprime C.generator n := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    exact ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp
      (C.residue.apply_ne_zero_iff.mp hres)).symm
  exact lowBaseModulus_coprime η C D (calibration_generator_bad S hS hbad).1
    (calibration_generator_bad S hS hbad).2 n hc heta

def lowTruePeriodGenerator (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : O := ConcretePrimeRowBridge.idealGenerator (lowPeriodIdeal η S hS)

lemma lowPeriodIdeal_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowPeriodIdeal η S hS≠0 := by
  unfold lowPeriodIdeal
  apply mul_ne_zero
  · exact lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _
  · apply Ideal.span_singleton_eq_bot.not.mpr
    norm_num

lemma lowTruePeriodGenerator_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowTruePeriodGenerator η S hS≠0 :=
  ConcretePrimeRowBridge.idealGenerator_ne_zero _ (lowPeriodIdeal_ne_zero η S hS)

lemma lowTruePeriodGenerator_span (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : Ideal.span {lowTruePeriodGenerator η S hS}=lowPeriodIdeal η S hS :=
  ConcretePrimeRowBridge.span_idealGenerator _

lemma physicalRayPeriodicBase_zero_true_puncture (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (n : O) (hn : ¬IsCoprime (lowTruePeriodGenerator η S hS) n) :
    physicalRayPeriodicBase η S hS σ χ n=0 := by
  by_contra hh
  apply hn
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [lowTruePeriodGenerator_span]
  exact (physicalRayPeriodicBase_support η S hS hbad σ χ n hh).symm

theorem physical_row_absorb_true_period (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (f z : O) :
    rowTwist (physicalRayPeriodicBase η S hS σ χ)
      ((calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS) f z=
    rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator f z := by
  exact InverseReflectedPhase.rowTwist_absorb_puncture _ _ _ f z
    (calibration_generator_bad S hS hbad).1 (calibration_generator_bad S hS hbad).2
    (physicalRayPeriodicBase_zero_true_puncture η S hS hbad σ χ)

lemma physical_true_period_residual_coprime (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (I F : Id) :
    IsCoprime (lowPeriodIdeal η S hS)
      (rowResidualPart I
        (Ideal.span {(calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS}*F)) := by
  apply InverseReflectedPhase.rowResidualPart_coprime_enlarged_period
  rw [lowTruePeriodGenerator_span]

def lowReflectionPeriod (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : Id :=
  lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS)

lemma lowReflectionPeriod_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowReflectionPeriod η S hS≠0 :=
  lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _

lemma lowReflectionPeriod_actual (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) :
    CanonicalCoefficientClass.FactorsModulo (lowReflectionPeriod η S hS) (physicalRayPeriodicBase η S hS σ χ) ∧
      ∀n : O,‖physicalRayPeriodicBase η S hS σ χ n‖≤1 := by
  exact ⟨lowPeriodicBase_periodic η _ _ _ _ _ χ,lowPeriodicBase_norm η _ _ _ _ _ χ⟩

def lowReflectionMask (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : O :=
  (calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS

lemma lowReflectionMask_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowReflectionMask η S hS≠0 :=
  mul_ne_zero (calibrationForSet S hS).generator_ne_zero (lowTruePeriodGenerator_ne_zero η S hS)

lemma lowReflectionMask_bad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    ConcretePrimeRowBridge.goodLambda∣lowReflectionMask η S hS ∧ (2:O)∣lowReflectionMask η S hS := by
  exact ⟨dvd_mul_of_dvd_left (calibration_generator_bad S hS hbad).1 _,
    dvd_mul_of_dvd_left (calibration_generator_bad S hS hbad).2 _⟩

lemma lowReflectionMask_period (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowPeriodIdeal η S hS∣Ideal.span {lowReflectionMask η S hS} := by
  rw [lowReflectionMask,←Ideal.span_singleton_mul_span_singleton,lowTruePeriodGenerator_span]
  exact dvd_mul_left _ _

lemma physical_markedCompletedT_absorb_true_period (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (f z : O) (W : ℝ→ℂ) (X : ℝ) (mark : Id→ℂ) :
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) f z) W X mark=
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator f z) W X mark := by
  rw [lowReflectionMask,physical_row_absorb_true_period η S hS hbad σ χ]

end SevenEighths.ProbePhysical
end

end OAI

end Source1582

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowActualIdealLists.lean; sha256: 493d963c8c7156432733c80cc2c014f31b117d06f46067d0f4925508709de18a -/
section Source1583
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowPrimeIdealList (T : Finset PrimeIdeal) : Finset Id := T.image Subtype.val

def lowPrimeListEquiv (T : Finset PrimeIdeal) : T≃lowPrimeIdealList T :=
  Equiv.ofBijective (fun p=>⟨p.val.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩) (by
    constructor
    · intro p q h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : lowPrimeIdealList T=>x.val) h))
    · intro I
      obtain ⟨P,hP,h⟩ := Finset.mem_image.mp I.property
      exact ⟨⟨P,hP⟩,Subtype.ext h⟩)

@[simp] lemma lowPrimeListEquiv_val (T : Finset PrimeIdeal) (p : T) :
    (lowPrimeListEquiv T p).val=p.val.val := rfl

lemma lowPrimeIdealList_prime (T : Finset PrimeIdeal) (I : Id) (hI : I∈lowPrimeIdealList T) : Prime I := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact P.property

lemma lowPrimeIdealList_supported (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (I : Id) (hI : I∈lowPrimeIdealList T) : Supported I := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact hT P hP

lemma lowPrimeIdealList_maximal (T : Finset PrimeIdeal) (I : Id) (hI : I∈lowPrimeIdealList T) : I.IsMaximal :=
  (Ideal.isPrime_of_prime (lowPrimeIdealList_prime T I hI)).isMaximal (lowPrimeIdealList_prime T I hI).ne_zero

lemma lowPrimeIdealList_good_odd (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (I : Id) (hI : I∈lowPrimeIdealList T) :
    ConcretePrimeRowBridge.goodLambda∉I ∧ ringChar (O⧸I)≠2 := by
  have hs := lowPrimeIdealList_supported T hT I hI
  exact hs.2 I ((Ideal.mem_normalizedFactors_iff hs.1).mpr
    ⟨Ideal.isPrime_of_prime (lowPrimeIdealList_prime T I hI),le_rfl⟩)

lemma lowPrimeIdealList_disjoint {ι : Type*} (T : ι→Finset PrimeIdeal)
    (hT : Pairwise (fun i j=>Disjoint (T i) (T j))) :
    Pairwise (fun i j=>Disjoint (lowPrimeIdealList (T i)) (lowPrimeIdealList (T j))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro I hI hJ
  obtain ⟨P,hP,hPI⟩ := Finset.mem_image.mp hI
  obtain ⟨Q,hQ,hQI⟩ := Finset.mem_image.mp hJ
  have he : P=Q := Subtype.ext (hPI.trans hQI.symm)
  exact Finset.disjoint_left.mp (hT hij) hP (he.symm ▸ hQ)

lemma lowPrimeIdealList_norm (T : Finset PrimeIdeal) (H : ℝ)
    (hT : ∀P∈T,(Ideal.absNorm P.val:ℝ)≤H) (I : Id) (hI : I∈lowPrimeIdealList T) :
    (Ideal.absNorm I:ℝ)≤H := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact hT P hP

lemma lowPrimeIdealList_coprime (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal)
    (I : Id) (hI : I∈lowPrimeIdealList (lowPeriodPrimeList η S hS T)) :
    IsCoprime I (lowPeriodIdeal η S hS) := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact lowPeriodPrimeList_coprime η S hS T P hP

theorem low_actual_ideal_polynomial {ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (T : ι→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hout : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Y : ι→ℝ) (t : ℝ) (F : (ι→Id)→ℂ) :
    (∑p : ∀i,canonicalSlotSupport (T i),
      (∏i,lowSingleSlotWeight η (W i) (Y i) t (p i).val)*F (fun i=>Ideal.span {(p i).val}))=
    ∑p : ∀i,lowPrimeIdealList (lowPeriodPrimeList η S hS (T i)),
      (∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryGenerator (p i).val))*F (fun i=>(p i).val) := by
  let E := Equiv.piCongrRight (fun i=>canonicalSlotEquiv (T i) (hT i))
  rw [←Equiv.sum_comp E]
  simp only [E,Equiv.piCongrRight_apply,Pi.map_apply,canonicalSlotEquiv_val]
  have hspan (p : ∀i,T i) (i : ι) : Ideal.span {primaryGenerator (p i).val.val}=(p i).val.val :=
    span_primaryGenerator_of_supported _ (hT i _ (p i).property)
  simp_rw [hspan]
  rw [low_canonical_polynomial_period_filter η S hS hbad T hT hout W Y t (fun p=>F (fun i=>(p i).val))]
  exact Equiv.sum_comp (Equiv.piCongrRight (fun i=>lowPrimeListEquiv (lowPeriodPrimeList η S hS (T i))))
    (fun p=>(∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryGenerator (p i).val))*F (fun i=>(p i).val))

lemma low_actual_ideal_weight_bound (η : HeckeFamily.Character) (W : ℝ→ℂ)
    (hW : ∀x,‖W x‖≤1) (Y t : ℝ) (I : Id) :
    ‖lowSingleSlotWeight η W Y t (primaryGenerator I)‖≤1 :=
  (lowSingleSlotWeight_norm η W Y t _).trans (hW _)

end SevenEighths.ProbePhysical
end

end OAI

end Source1583

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowInverseEnergy.lean; sha256: f23c722603ce13444c70d990ec8960bd050653abf880319722247d89789458e7 -/
section Source1584
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open RayFourExpansion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowCorrectionEnergy : ℝ := ∑χ : RayCharacter,‖ProbeCompleted.correctionCoeff χ‖^2

lemma lowCorrectionEnergy_nonneg : 0≤lowCorrectionEnergy :=
  Finset.sum_nonneg (fun _ _=>sq_nonneg _)

lemma fixed_correction_energy {ι κ : Type*} [Fintype ι] (R : Finset κ) (c : ι→ℂ) (F : ι→κ→ℂ) :
    (∑m∈R,‖∑χ : ι,c χ*F χ m‖^2)≤
      (∑χ : ι,‖c χ‖^2)*∑χ : ι,∑m∈R,‖F χ m‖^2 := by
  calc
    _≤∑m∈R,(∑χ : ι,‖c χ‖^2)*(∑χ : ι,‖F χ m‖^2) := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        _≤(∑χ : ι,‖c χ‖*‖F χ m‖)^2 := by
          apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>by positivity))).mpr
          simpa only [norm_mul] using norm_sum_le Finset.univ (fun χ=>c χ*F χ m)
        _≤_ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _=_ := by rw [←Finset.mul_sum,Finset.sum_comm]

theorem lowSelectedInverseRow_energy {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (R : Finset O) :
    (∑m∈R,‖lowSelectedInverseRow F c η S hS D T t σ m‖^2)≤
      lowCorrectionEnergy*∑χ : RayCharacter,∑m∈R,
        ‖∑k∈F,c k*InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
          (fun A=>if D k∣A then (1:ℂ) else 0)‖^2 := by
  simp_rw [lowSelectedInverseRow_correction]
  exact fixed_correction_energy R ProbeCompleted.correctionCoeff _

theorem lowCanonicalSelected_energy {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→CanonicalQuadraticSieve.Supported P.val)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (R : Finset O) :
    (∑m∈R,‖lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W P t)
      η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ m‖^2)≤
      lowCorrectionEnergy*∑χ : RayCharacter,∑m∈R,
        ‖∑b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J,
          (∏i : SelectedSlot J,lowSingleSlotWeight η (W i.val) (P i.val) t (b i).val)*
          InverseMoment.markedCompletedT
            (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
              (calibrationForSet S hS).generator 1 m)
            (CompletedHeight.normTwistedSource gaussianFixedWindow t) X
            (fun A=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0)‖^2 := by
  have hh := lowSelectedInverseRow_energy Finset.univ
    (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W P t)
    η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ R
  simp_rw [lowSelectedWeight_eq_product] at hh
  have he (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
      (fun A : Id=>if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
        (fun A=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0) := by
    funext A
    exact lowCanonicalSelected_mark T hT hdis J b A
  simp_rw [he] at hh
  exact hh

end SevenEighths.ProbePhysical
end

end OAI

end Source1584

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGaussEnergy.lean; sha256: f0bd6e81c8f86abf32c5993333f9d9c424cefa790ab3b0bafc9b8fa5ae385c9d -/
section Source1585
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGaussColumn (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) : ℂ :=
  if physicalIdealRay s=σ then
    (Y:ℂ)⁻¹*W1 ((Ideal.absNorm s.val:ℝ)/Y)*lowArithmeticCoefficient C s*
      (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)
  else 0

lemma lowGaussColumn_row (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) (m : O) :
    (if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0)=
      lowGaussColumn C W1 Y σ v s*
        gaussRow (primaryGenerator s.val) ((supported_span_primaryGenerator_iff s.val).mpr s.property) (-m) := by
  have he := (primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1
  unfold lowGaussColumn gaussRow
  rw [congrArg Ideal.absNorm he]
  split_ifs
  · rw [lowAdditiveCoefficient_eq]
    simp only [div_eq_mul_inv]
    ring
  · simp

theorem lowRayAmplitude_gaussPolynomial (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀σ : RayRing,∀v : ℝ,∀m : O,
      lowRayAmplitude C W1 Y σ m v=
        gaussPolynomial F (fun s=>primaryGenerator s.val)
          (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
          (lowGaussColumn C W1 Y σ v) (-m) := by
  obtain ⟨F,hF⟩ := lowRayAmplitude_eq_finite C W1 hW1 Y hY
  refine ⟨F,?_⟩
  intro σ v m
  rw [hF σ m v]
  unfold gaussPolynomial
  apply Finset.sum_congr rfl
  intro s hs
  exact lowGaussColumn_row C W1 Y σ v s m

theorem lowRayAmplitude_energy (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀σ : RayRing,∀v : ℝ,
      ∀U : SchwartzMap ℝ ℂ,∀Q : ℝ,0<Q→∀rows : Finset O,
      (∀z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/Q)).re)→
      (∀z∈rows,1≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/Q)).re)→
      (∑z∈rows,‖lowRayAmplitude C W1 Y σ z v‖^2)≤
        (gaussEnergy F (fun s=>primaryGenerator s.val)
          (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
          (lowGaussColumn C W1 Y σ v) U Q).re := by
  obtain ⟨F,hF⟩ := lowRayAmplitude_gaussPolynomial C W1 hW1 Y hY
  refine ⟨F,?_⟩
  intro σ v U Q hQ rows hU hmajor
  simp_rw [hF σ v]
  exact CenteredMomentReflectedChild.finite_reflected_energy_le_gaussEnergy F
    (fun s=>primaryGenerator s.val) (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
    (lowGaussColumn C W1 Y σ v) U Q hQ rows hU hmajor

end SevenEighths.ProbePhysical
end

end OAI

end Source1585

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowColumnBounds.lean; sha256: 807aa1a67c730624d734dd6063c69b1e95329bbb9fab993687474c7c0e203766 -/
section Source1586
namespace OAI

noncomputable section
open scoped Classical
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGaussColumns (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    Finset {I : Id // Supported I} :=
  ((idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn).toFinset

lemma lowGaussColumns_mem (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y)
    (s : {I : Id // Supported I}) :
    s∈lowGaussColumns W1 hW1 Y hY ↔ W1 ((Ideal.absNorm s.val:ℝ)/Y)≠0 := by
  simp only [lowGaussColumns,Set.Finite.mem_toFinset,Set.mem_preimage,Function.mem_support]

lemma lowRayAmplitude_source_columns (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (m : O) :
    lowRayAmplitude C W1 Y σ m v=
      CenteredMomentGaussEnergy.gaussPolynomial (lowGaussColumns W1 hW1 Y hY)
        (fun s=>primaryGenerator s.val)
        (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
        (lowGaussColumn C W1 Y σ v) (-m) := by
  unfold lowRayAmplitude
  rw [tsum_eq_sum (s:=lowGaussColumns W1 hW1 Y hY) (fun s hs=>by
    have hz : W1 ((Ideal.absNorm s.val:ℝ)/Y)=0 := by
      simpa only [lowGaussColumns_mem,not_not] using hs
    simp only [lowAdditiveCoefficient_outer_zero C W1 Y s m v hz,ite_self])]
  unfold CenteredMomentGaussEnergy.gaussPolynomial
  exact Finset.sum_congr rfl (fun s _=>lowGaussColumn_row C W1 Y σ v s m)

lemma lowGaussColumns_card (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 1≤Y)
    (a b : ℝ) (hW : Function.support W1⊆Set.Icc a b) :
    ((lowGaussColumns W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY)).card:ℝ)≤128*max 1 b*Y := by
  let F := lowGaussColumns W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY)
  have hH : 1≤max 1 b*Y := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hY
  have hh := DescentFiberCost.finite_ideal_count_real (F.image Subtype.val) (max 1 b*Y) hH
    (by intro I hI;obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hI;exact s.property.1)
    (by
      intro I hI
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hI
      have hw := (hW ((lowGaussColumns_mem W1 hW1 Y _ s).mp hs)).2
      have hn : (Ideal.absNorm s.val:ℝ)≤b*Y := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hY)).mp hw
      exact hn.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_trans zero_le_one hY)))
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  simpa only [mul_assoc,F] using hh

lemma lowGaussColumn_norm_bound (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (W1 : ℝ→ℂ) (a b B : ℝ) (ha : 0<a) (hB : 0≤B)
    (hW : Function.support W1⊆Set.Icc a b) (hWB : ∀x,‖W1 x‖≤B)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) :
    ‖lowGaussColumn (calibrationForSet S hS) W1 Y σ v s‖≤
      B*a^(-(1/2:ℝ))/Y := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  by_cases hzero : W1 ((Ideal.absNorm s.val:ℝ)/Y)=0
  · simp only [lowGaussColumn,hzero,mul_zero,zero_mul,ite_self,norm_zero]
    positivity
  have hqa := (hW hzero).1
  have hp : ‖(((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)‖=
      ((Ideal.absNorm s.val:ℝ)/Y)^(-(1/2:ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hq hY)]
    congr 1
    simp
  have hr : ((Ideal.absNorm s.val:ℝ)/Y)^(-(1/2:ℝ))≤a^(-(1/2:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha hqa (by norm_num)
  unfold lowGaussColumn
  split_ifs
  · rw [norm_mul,norm_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,hp]
    calc
      _ ≤ Y⁻¹*B*1*a^(-(1/2:ℝ)) := by
        gcongr
        · exact hWB _
        · exact lowArithmeticCoefficient_source_norm S hS s
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

theorem lowGaussColumn_l2_bound (a b B : ℝ) (ha : 0<a) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W1 : ℝ→ℂ,∀hW1 : HasCompactSupport W1,
      Function.support W1⊆Set.Icc a b → (∀x,‖W1 x‖≤B) →
      ∀Y : ℝ,∀hY : 1≤Y,∀σ : RayRing,∀v : ℝ,
      (∑s∈lowGaussColumns W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY),
        ‖lowGaussColumn (calibrationForSet S hS) W1 Y σ v s‖^2)≤C/Y := by
  let C := 128*max 1 b*(B*a^(-(1/2:ℝ)))^2+1
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro S hS W1 hW1 hW hWB Y hY σ v
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  have hcoef (s : {I : Id // Supported I}) := lowGaussColumn_norm_bound S hS W1 a b B ha hB hW hWB Y hy σ v s
  calc
    _ ≤ ∑_s∈lowGaussColumns W1 hW1 Y hy,(B*a^(-(1/2:ℝ))/Y)^2 := by
      apply Finset.sum_le_sum
      intro s hs
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoef s) 2
    _ = ((lowGaussColumns W1 hW1 Y hy).card:ℝ)*(B*a^(-(1/2:ℝ))/Y)^2 := by simp
    _ ≤ (128*max 1 b*Y)*(B*a^(-(1/2:ℝ))/Y)^2 :=
      mul_le_mul_of_nonneg_right (lowGaussColumns_card W1 hW1 Y hY a b hW) (sq_nonneg _)
    _ = (128*max 1 b*(B*a^(-(1/2:ℝ)))^2)/Y := by field_simp
    _ ≤ C/Y := div_le_div_of_nonneg_right (by dsimp only [C];linarith) hy.le

end SevenEighths.ProbePhysical
end

end OAI

end Source1586

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowCauchy.lean; sha256: b1083c5a2939ccc901af12a2f3d337d6534c0fb69e73342217ea11e37226409d -/
section Source1587
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def lowNumeratorWeight (C : CalibrationData) (Ω : ℝ→ℂ) (X Y : ℝ) (m : O) (v : ℝ) : ℂ :=
  Ω (elementNorm m/lowPhysicalScale C X Y)*C.residueMonoid m*
    ((elementNorm m/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))

lemma lowOuterCutoff_norm (a b x : ℝ) : ‖lowOuterCutoff a b x‖≤1 := by
  rw [lowOuterCutoff,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _),abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)

lemma lowNumeratorWeight_norm (C : CalibrationData) (Ω : ℝ→ℂ)
    (hΩ : ∀x,‖Ω x‖≤1) (hΩ0 : Ω 0=0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (m : O) (v : ℝ) :
    ‖lowNumeratorWeight C Ω X Y m v‖≤1 := by
  by_cases hm : m=0
  · simp [lowNumeratorWeight,hm,elementNorm,hΩ0]
  have hmpos : 0<elementNorm m := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
  have he : -((v:ℂ)*Complex.I)=((-v:ℝ):ℂ)*Complex.I := by simp
  rw [lowNumeratorWeight,norm_mul,norm_mul,he,
    low_mellin_phase_norm _ (-v) (div_pos hmpos (lowPhysicalScale_pos C X Y hX hY)),mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΩ _)).trans (C.residueMonoid_norm_le_one m)

lemma lowNumeratorWeight_common_support (C : CalibrationData) (Ω : ℝ→ℂ)
    (hΩ : HasCompactSupport Ω) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    ∃R : Finset O,∀m∉R,∀v : ℝ,lowNumeratorWeight C Ω X Y m v=0 := by
  have hh := elementWindow_finite_support Ω hΩ _ (lowPhysicalScale_pos C X Y hX hY)
  refine ⟨hh.toFinset,?_⟩
  intro m hm v
  have hz : Ω (elementNorm m/lowPhysicalScale C X Y)=0 := by
    simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hm
  simp [lowNumeratorWeight,hz]

theorem lowSeparatedIntegrand_cauchy (C : CalibrationData) (Ω : ℝ→ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ∀x,‖Ω x‖≤1) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    ∃R : Finset O,∀W0 W1 : ℝ→ℂ,∀B : RayRing→O→ℂ,∀v : ℝ,
      ‖lowSeparatedIntegrand C W0 W1 Ω X Y B v‖≤
        ‖mellin W0 ((v:ℂ)*Complex.I)‖*
          ∑σ : RayRing,Real.sqrt (∑m∈R,‖lowRayAmplitude C W1 Y σ m v‖^2)*
            Real.sqrt (∑m∈R,‖B σ m‖^2) := by
  obtain ⟨R,hR⟩ := lowNumeratorWeight_common_support C Ω hΩc X Y hX hY
  refine ⟨R,?_⟩
  intro W0 W1 B v
  have he : lowSeparatedIntegrand C W0 W1 Ω X Y B v=
      mellin W0 ((v:ℂ)*Complex.I)*
        ∑σ : RayRing,∑m∈R,lowNumeratorWeight C Ω X Y m v*lowRayAmplitude C W1 Y σ m v*B σ m := by
    unfold lowSeparatedIntegrand
    change mellin W0 ((v:ℂ)*Complex.I)*
      (∑'m : O,lowNumeratorWeight C Ω X Y m v*∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ m)=_
    rw [tsum_eq_sum (s:=R) (fun m hm=>by rw [hR m hm v,zero_mul])]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [he,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∑σ : RayRing,‖∑m∈R,lowNumeratorWeight C Ω X Y m v*lowRayAmplitude C W1 Y σ m v*B σ m‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun σ _=>CenteredMomentCauchy.bounded_row_cauchy R
      (fun m=>lowNumeratorWeight C Ω X Y m v) (fun m=>lowRayAmplitude C W1 Y σ m v) (B σ)
      (fun m _=>lowNumeratorWeight_norm C Ω hΩ hΩ0 X Y hX hY m v))

end SevenEighths.ProbePhysical
end

end OAI

end Source1587

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowActualEnergies.lean; sha256: c7e3fb2a96e6a0875fd6be32ae9d17f6f6c18e18c8210459322834ecadd4ade6 -/
section Source1588
namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

def lowNumeratorRows (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q) : Finset O :=
  (elementWindow_finite_support (lowOuterCutoff a b) (lowOuterCutoff_compact a b ha hb) Q hQ).toFinset

lemma lowNumeratorRows_mem (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q) (m : O) :
    m∈lowNumeratorRows a b ha hb Q hQ ↔ lowOuterCutoff a b (elementNorm m/Q)≠0 := by
  simp only [lowNumeratorRows,Set.Finite.mem_toFinset,Function.mem_support]

def lowGaussMajorant (a b : ℝ) (ha : 0<a) (hb : 0<b) : SchwartzMap ℝ ℂ :=
  (lowOuterCutoff_compact (a/2) (2*b) (by positivity) (by positivity)).toSchwartzMap
    (lowOuterCutoff_smooth (a/2) (2*b))

lemma lowGaussMajorant_nonneg (a b : ℝ) (ha : 0<a) (hb : 0<b) (x : ℝ) :
    0≤(lowGaussMajorant a b ha hb x).re := by
  change 0≤(lowOuterCutoff (a/2) (2*b) x).re
  simp only [lowOuterCutoff,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma lowGaussMajorant_on_rows (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q)
    (m : O) (hm : m∈lowNumeratorRows a b ha hb Q hQ) :
    lowGaussMajorant a b ha hb (‖ConcreteTraceCRT.eisEmbedding m‖^2/Q)=1 := by
  have hh := lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q hQ m).mp hm)
  change lowOuterCutoff (a/2) (2*b) (‖ConcreteTraceCRT.eisEmbedding m‖^2/Q)=1
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  exact lowOuterCutoff_one _ _ (by positivity) (by positivity) _ hh.1 hh.2

theorem lowRayAmplitude_actual_energy (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v Q : ℝ) (hQ : 0<Q) :
    (∑m∈lowNumeratorRows a b ha hb Q hQ,‖lowRayAmplitude C W1 Y σ m v‖^2)≤
      (gaussEnergy (lowGaussColumns W1 hW1 Y hY) (fun s=>primaryGenerator s.val)
        (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
        (lowGaussColumn C W1 Y σ v) (lowGaussMajorant a b ha hb) Q).re := by
  simp_rw [lowRayAmplitude_source_columns C W1 hW1 Y hY σ v]
  exact CenteredMomentReflectedChild.finite_reflected_energy_le_gaussEnergy _ _ _ _ _ Q hQ _
    (fun _=>lowGaussMajorant_nonneg a b ha hb _)
    (fun m hm=>by rw [lowGaussMajorant_on_rows a b ha hb Q hQ m hm];norm_num)

lemma lowSeparatedIntegrand_source_cauchy (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (B : RayRing→O→ℂ) (v : ℝ) :
    ‖lowSeparatedIntegrand C W0 W1 (lowOuterCutoff a b) X Y B v‖≤
      ‖mellin W0 ((v:ℂ)*Complex.I)‖*
        ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a b ha hb (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY),
          ‖lowRayAmplitude C W1 Y σ m v‖^2)*
          Real.sqrt (∑m∈lowNumeratorRows a b ha hb (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY),‖B σ m‖^2) := by
  let R := lowNumeratorRows a b ha hb (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY)
  have hR (m : O) (hm : m∉R) : lowNumeratorWeight C (lowOuterCutoff a b) X Y m v=0 := by
    have hz : lowOuterCutoff a b (elementNorm m/lowPhysicalScale C X Y)=0 := by
      simpa only [R,lowNumeratorRows_mem,not_not] using hm
    simp [lowNumeratorWeight,hz]
  have he : lowSeparatedIntegrand C W0 W1 (lowOuterCutoff a b) X Y B v=
      mellin W0 ((v:ℂ)*Complex.I)*
        ∑σ : RayRing,∑m∈R,lowNumeratorWeight C (lowOuterCutoff a b) X Y m v*lowRayAmplitude C W1 Y σ m v*B σ m := by
    unfold lowSeparatedIntegrand
    change mellin W0 ((v:ℂ)*Complex.I)*
      (∑'m : O,lowNumeratorWeight C (lowOuterCutoff a b) X Y m v*∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ m)=_
    rw [tsum_eq_sum (s:=R) (fun m hm=>by rw [hR m hm,zero_mul])]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [he,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∑σ : RayRing,‖∑m∈R,lowNumeratorWeight C (lowOuterCutoff a b) X Y m v*lowRayAmplitude C W1 Y σ m v*B σ m‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun σ _=>CenteredMomentCauchy.bounded_row_cauchy R
      (fun m=>lowNumeratorWeight C (lowOuterCutoff a b) X Y m v) (fun m=>lowRayAmplitude C W1 Y σ m v) (B σ)
      (fun m _=>lowNumeratorWeight_norm C _ (lowOuterCutoff_norm a b)
        (lowOuterCutoff_small a b ha 0 (by positivity)) X Y hX hY m v))

theorem lowSeparatedIntegrand_actual_energies (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) (v : ℝ) :
    ‖lowSeparatedIntegrand C W0 W1 (lowOuterCutoff a b) X Y B v‖≤
      ‖mellin W0 ((v:ℂ)*Complex.I)‖*
        ∑σ : RayRing,Real.sqrt ((gaussEnergy (lowGaussColumns W1 hW1 Y hY)
          (fun s=>primaryGenerator s.val) (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
          (lowGaussColumn C W1 Y σ v) (lowGaussMajorant a b ha hb) (lowPhysicalScale C X Y)).re)*
          Real.sqrt (∑m∈lowNumeratorRows a b ha hb (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY),‖B σ m‖^2) := by
  apply (lowSeparatedIntegrand_source_cauchy a b ha hb C W0 W1 X Y hX hY B v).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro σ hσ
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (lowRayAmplitude_actual_energy a b ha hb C W1 hW1 Y hY σ v
    (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY))) (Real.sqrt_nonneg _)

end SevenEighths.ProbePhysical
end

end OAI

end Source1588

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowElementRows.lean; sha256: a264127ba135a4332ca9c23dfa0150bbc60fd2753545a2bdc5088343cf41af30 -/
section Source1589
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def lowElementRowPoint (m : O) : Oˣ×Id :=
  (InitialMeanSquare.sourceLabelUnit m,Ideal.span {m})

def lowIdealRowElement (p : Oˣ×Id) : O := p.1.val*idealGenerator p.2

lemma lowIdealRowElement_point (m : O) : lowIdealRowElement (lowElementRowPoint m)=m :=
  (InitialMeanSquare.sourceLabelUnit_spec m).symm

lemma lowElementRowPoint_injective : Function.Injective lowElementRowPoint :=
  Function.LeftInverse.injective lowIdealRowElement_point

lemma lowIdealRowElement_span (p : Oˣ×Id) : Ideal.span {lowIdealRowElement p}=p.2 := by
  rw [lowIdealRowElement,Ideal.span_singleton_mul_left_unit p.1.isUnit,span_idealGenerator]

lemma lowElementRowPoint_element (p : Oˣ×Id) (hp : p.2≠0) :
    lowElementRowPoint (lowIdealRowElement p)=p := by
  apply Prod.ext
  · apply Units.ext
    have hh := InitialMeanSquare.sourceLabelUnit_spec (lowIdealRowElement p)
    rw [lowIdealRowElement_span] at hh
    exact (mul_right_cancel₀ (idealGenerator_ne_zero p.2 hp) hh).symm
  · exact lowIdealRowElement_span p

lemma lowIdealRowElement_norm (p : Oˣ×Id) :
    elementNorm (lowIdealRowElement p)=(Ideal.absNorm p.2:ℝ) := by
  unfold elementNorm
  rw [lowIdealRowElement_span]

def lowIdealRows (R : Finset O) : Finset Id := R.image (fun m=>Ideal.span {m})

lemma lowIdealRows_nonzero (R : Finset O) (hR : ∀m∈R,m≠0) (I : Id) (hI : I∈lowIdealRows R) : I≠0 := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hI
  exact Ideal.span_singleton_eq_bot.not.mpr (hR m hm)

lemma lowIdealRows_norm_bound (R : Finset O) (Q : ℝ) (hR : ∀m∈R,elementNorm m≤Q)
    (I : Id) (hI : I∈lowIdealRows R) : (Ideal.absNorm I:ℝ)≤Q := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hI
  exact hR m hm

theorem sum_low_element_rows (R : Finset O) (hR : ∀m∈R,m≠0) (F : O→ℂ) :
    (∑m∈R,F m)=∑u : Oˣ,∑I∈lowIdealRows R,
      if u.val*idealGenerator I∈R then F (u.val*idealGenerator I) else 0 := by
  let P := (Finset.univ×ˢlowIdealRows R).filter (fun p : Oˣ×Id=>lowIdealRowElement p∈R)
  have he : (∑m∈R,F m)=∑p∈P,F (lowIdealRowElement p) := by
    apply Finset.sum_bij (fun m hm=>lowElementRowPoint m)
    · intro m hm
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · exact Finset.mem_image.mpr ⟨m,hm,rfl⟩
      · rwa [lowIdealRowElement_point]
    · intro m hm n hn he
      exact lowElementRowPoint_injective he
    · intro p hp
      obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
      refine ⟨lowIdealRowElement p,hpr,?_⟩
      exact lowElementRowPoint_element p (lowIdealRows_nonzero R hR _ (Finset.mem_product.mp hp).2)
    · intro m hm
      rw [lowIdealRowElement_point]
  rw [he]
  dsimp only [P]
  rw [Finset.sum_filter,Finset.sum_product]
  rfl

theorem low_element_energy_le_units (R : Finset O) (_hR : ∀m∈R,m≠0) (F : O→ℂ) :
    (∑m∈R,‖F m‖^2)≤∑u : Oˣ,∑I∈lowIdealRows R,‖F (u.val*idealGenerator I)‖^2 := by
  let P : Finset (Oˣ×Id) := Finset.univ×ˢlowIdealRows R
  have hsub : R.image lowElementRowPoint⊆P := by
    intro p hp
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨m,hm,rfl⟩⟩
  have he : (∑m∈R,‖F m‖^2)=∑p∈R.image lowElementRowPoint,‖F (lowIdealRowElement p)‖^2 := by
    rw [Finset.sum_image (fun m _ n _ h=>lowElementRowPoint_injective h)]
    simp only [lowIdealRowElement_point]
  rw [he]
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _=>sq_nonneg ‖F (lowIdealRowElement p)‖)
  simpa only [P,Finset.sum_product,lowIdealRowElement] using hh

lemma low_rowTwist_label_one (Ψ : O→*ℂ) (m : O) (u : Oˣ) (I : Id) :
    CanonicalRowCompletion.rowTwist Ψ m 1 (u.val*idealGenerator I)=
      CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id))
        (((InitialMeanSquare.sourceLabelUnit 1)^4*u).val*idealGenerator I) := by
  have he : (InitialMeanSquare.sourceLabelUnit (1:O)).val*idealGenerator (1:Id)=1 := by
    simpa only [Ideal.span_singleton_one,Ideal.one_eq_top] using (InitialMeanSquare.sourceLabelUnit_spec (1:O)).symm
  have harg : m^6*(idealGenerator (1:Id))^4*
      (((InitialMeanSquare.sourceLabelUnit 1)^4*u).val*idealGenerator I)=m^6*1^4*(u.val*idealGenerator I) := by
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,one_pow]
    calc
      _=m^6*((InitialMeanSquare.sourceLabelUnit (1:O)).val*idealGenerator (1:Id))^4*(u.val*idealGenerator I) := by ring
      _=_ := by rw [he];ring
  unfold CanonicalRowCompletion.rowTwist
  rw [harg]

lemma low_units_label_one_sum (F : (O→*ℂ)→ℝ) (Ψ : O→*ℂ) (m : O) (I : Id) :
    (∑u : Oˣ,F (CanonicalRowCompletion.rowTwist Ψ m 1 (u.val*idealGenerator I)))=
      ∑u : Oˣ,F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I)) := by
  simp_rw [low_rowTwist_label_one]
  exact Equiv.sum_comp (Equiv.mulLeft ((InitialMeanSquare.sourceLabelUnit (1:O))^4))
    (fun u : Oˣ=>F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I)))

lemma low_element_rowTwist_energy (R : Finset O) (hR : ∀z∈R,z≠0)
    (Ψ : O→*ℂ) (m : O) (F : (O→*ℂ)→ℂ) :
    (∑z∈R,‖F (CanonicalRowCompletion.rowTwist Ψ m 1 z)‖^2)≤
      ∑u : Oˣ,∑I∈lowIdealRows R,
        ‖F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I))‖^2 := by
  apply (low_element_energy_le_units R hR (fun z=>F (CanonicalRowCompletion.rowTwist Ψ m 1 z))).trans_eq
  rw [Finset.sum_comm,Finset.sum_comm (f:=fun (u : Oˣ) (I : Id)=>
    ‖F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I))‖^2)]
  apply Finset.sum_congr rfl
  intro I hI
  exact low_units_label_one_sum (fun Ψ=>‖F Ψ‖^2) Ψ m I

lemma lowNumeratorRows_nonzero (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q)
    (z : O) (hz : z∈lowNumeratorRows a b ha hb Q hQ) : z≠0 := by
  intro he
  have hh := (lowNumeratorRows_mem a b ha hb Q hQ z).mp hz
  rw [he,elementNorm,Ideal.span_singleton_zero,Ideal.absNorm_bot,Nat.cast_zero,zero_div] at hh
  exact hh (lowOuterCutoff_small a b ha 0 (by positivity))

lemma lowNumeratorRows_norm_bound (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q)
    (z : O) (hz : z∈lowNumeratorRows a b ha hb Q hQ) : elementNorm z≤2*b*Q := by
  have hh := (lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q hQ z).mp hz)).2
  exact (div_le_iff₀ hQ).mp hh

theorem lowSelectedInverseRow_ideal_energy {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (X t : ℝ) (σ : RayFourExpansion.RayRing) (R : Finset O) (hR : ∀z∈R,z≠0) :
    (∑z∈R,‖lowSelectedInverseRow F c η S hS D X t σ z‖^2)≤
      lowCorrectionEnergy*∑χ : RayFourExpansion.RayCharacter,∑u : Oˣ,∑I∈lowIdealRows R,
        ‖∑k∈F,c k*InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator (idealGenerator (1:Id)) (u.val*idealGenerator I))
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) X
          (fun A=>if D k∣A then (1:ℂ) else 0)‖^2 := by
  apply (lowSelectedInverseRow_energy F c η S hS D X t σ R).trans
  apply mul_le_mul_of_nonneg_left _ lowCorrectionEnergy_nonneg
  apply Finset.sum_le_sum
  intro χ hχ
  exact low_element_rowTwist_energy R hR (physicalRayPeriodicBase η S hS σ χ)
    (calibrationForSet S hS).generator (fun Ψ=>∑k∈F,c k*InverseMoment.markedCompletedT Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X (fun A=>if D k∣A then (1:ℂ) else 0))

lemma low_unit_card : Fintype.card Oˣ=6 := by
  simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six

end SevenEighths.ProbePhysical
end

end OAI

end Source1589

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowActualReflectedEnergy.lean; sha256: 734d2beea6df9a2b319f30493a872c9e5c6a355a0c546c5161b557bb9eef6285 -/
section Source1590
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def lowActualIdealPolynomial {ι : Type*} [Fintype ι]
    (L : ι→Finset Id) (w : ι→Id→ℂ) (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  ∑p : ∀i,L i,(∏i,w i (p i).val)*InverseMoment.markedCompletedT Ψ W X
    (fun A=>∏i,if (p i).val∣A then (1:ℂ) else 0)

theorem lowSelectedInverseRow_actual_ideal {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (z : O) :
    lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
      η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ z=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        lowActualIdealPolynomial
          (fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
          (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
          (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) 1 z)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) X := by
  rw [lowSelectedInverseRow_correction]
  apply Finset.sum_congr rfl
  intro χ hχ
  congr 1
  simp_rw [lowSelectedWeight_eq_product]
  have hm (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
      (fun A : Id=>if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
        (fun A=>∏i : SelectedSlot J,if Ideal.span {(b i).val}∣A then (1:ℂ) else 0) := by
    funext A
    exact lowSelectedIdeal_mark _ J b (lowCanonicalSelected_coprime T hT hdis J b) A
  simp_rw [hm,←physical_markedCompletedT_absorb_true_period η S hS hbad σ χ]
  convert low_actual_ideal_polynomial η S hS hbad (fun i : SelectedSlot J=>T i.val)
    (fun i=>hT i.val) (fun i=>hout i.val) (fun i=>W i.val) (fun i=>Y i.val) t
    (fun p=>InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) 1 z)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X
      (fun A=>∏i : SelectedSlot J,if p i∣A then (1:ℂ) else 0)) using 1
  · congr 1
    ext p
    simp
  · rfl

theorem lowSelectedInverseRow_actual_reflected_energy {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (R : Finset O) (hR : ∀z∈R,z≠0) :
    (∑z∈R,‖lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
      η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ z‖^2)≤
    lowCorrectionEnergy*∑χ : RayCharacter,∑u : Oˣ,∑I∈lowIdealRows R,
      ‖lowActualIdealPolynomial
        (fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
        (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS)
          (ConcretePrimeRowBridge.idealGenerator (1:Id)) (u.val*ConcretePrimeRowBridge.idealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) X‖^2 := by
  simp_rw [lowSelectedInverseRow_actual_ideal η S hS hbad T hT hout hdis J W Y X t σ]
  apply (fixed_correction_energy R ProbeCompleted.correctionCoeff _).trans
  apply mul_le_mul_of_nonneg_left _ lowCorrectionEnergy_nonneg
  apply Finset.sum_le_sum
  intro χ hχ
  exact low_element_rowTwist_energy R hR (physicalRayPeriodicBase η S hS σ χ)
    (lowReflectionMask η S hS) (fun Ψ=>lowActualIdealPolynomial
      (fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
      (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I)) Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X)

end SevenEighths.ProbePhysical
end

end OAI

end Source1590

/- Original source: OAI/NumberTheory/DirichletL/Reflection/PoolArithmetic.lean; sha256: 170bfe42149a0dd8a096fc360584ebf65591fd3c2279fab8dca4552e8947636a -/
section Source1591
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma poolPrimeFamily_pairwise (R Q Q₀ : Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (poolPrimeFamily R Q Q₀).ideal) := by
  intro P T hPT
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPT)

lemma poolPrimeFamily_period (R Q Q₀ : Ideal Eis) (P : FreeReflection.pool R Q Q₀) :
    IsCoprime Q₀ ((poolPrimeFamily R Q Q₀).ideal P) := by
  apply (maximal_coprime_of_not_dvd _ _ ?_).symm
  intro h
  exact FreeReflection.pool_free R Q Q₀ P (Ideal.dvd_iff_le.mp h)

lemma poolPrimeFamily_odd (R Q Q₀ : Ideal Eis) (P : FreeReflection.pool R Q Q₀) :
    ringChar (Eis⧸(poolPrimeFamily R Q Q₀).ideal P)≠2 := FreeReflection.pool_odd R Q Q₀ P

lemma poolPrimeFamily_fiber_row_coprime (R I Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q₀) :
    IsCoprime ((poolPrimeFamily R Q Q₀).ideal P) (rowResidualPart I Q) := by
  apply maximal_coprime_of_not_dvd
  exact FreeReflection.pool_nonresidual I Q Q₀
    (nonresidualPoolEquiv R I Q Q₀ hR hI hQ hpow hmask P)

lemma poolPrimeFamily_fiber_divides (R I Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q₀) :
    (poolPrimeFamily R Q Q₀).ideal P∣I*Q :=
  FreeReflection.pool_divides I Q Q₀ hI hQ (nonresidualPoolEquiv R I Q Q₀ hR hI hQ hpow hmask P)

lemma poolPrimeFamily_fiber_exponent (R I F Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q₀) :
    completedLocalExponent I F ((poolPrimeFamily R Q Q₀).ideal P)=completedLocalExponent R F P.val :=
  nonresidualPoolEquiv_exponent R I F Q Q₀ hR hI hQ hpow hmask P

lemma pool_restrict_completion_coprime (R Q Q₀ : Ideal Eis)
    (B : Finset (FreeReflection.pool R Q Q₀)) (c : Eis)
    (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) :
    ∀ b : B, IsCoprime (Ideal.span {(9:Eis)*c}) (((poolPrimeFamily R Q Q₀).restrict B).ideal b) := by
  exact ((poolPrimeFamily R Q Q₀).restrict B).level_coprime Q₀ c hc
    (fun b => poolPrimeFamily_period R Q Q₀ b.val)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1591

/- Original source: OAI/NumberTheory/DirichletL/Reflection/LowWidth.lean; sha256: dff393b2375c318d249c62a3c607baa573add80ae70b6a7d63e96b1b2aac5ccd -/
section Source1592
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma nonresidual_prime_product_square_dvd {ι : Type*} [Fintype ι]
    (I Q : Ideal Eis) (hI : I≠0) (P : ι→Ideal Eis) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i,P i∣I*Q) (hres : ∀ i,¬P i∣rowResidualPart I Q) :
    (∏ i,P i)^2∣rowPowerfulPart I*Q^2 := by
  rw [←Finset.prod_pow]
  apply Fintype.prod_dvd_of_coprime (fun i j hij => (hcop hij).pow)
  intro i
  have hp := Ideal.prime_of_isPrime (NeZero.ne (P i)) (inferInstance : (P i).IsPrime)
  by_cases hi : P i∣I
  · exact (nonresidual_prime_square_dvd I Q (P i) hI hp hi (hres i)).trans
      (mul_dvd_mul_left _ (pow_dvd_pow_of_dvd (rowMaskPart_dvd I Q) 2))
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ((hp.dvd_mul.mp (hpool i)).resolve_left hi) 2) _

lemma nonresidual_prime_product_width {ι : Type*} [Fintype ι]
    (I Q : Ideal Eis) (hI : I≠0) (hQ : Q≠0) (P : ι→Ideal Eis) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i,P i∣I*Q) (hres : ∀ i,¬P i∣rowResidualPart I Q)
    (Z : ℝ) (hZ : 1<Z) :
    2*normWidth Z (∏ i,P i)≤normWidth Z (rowPowerfulPart I)+2*normWidth Z Q := by
  have hd := nonresidual_prime_product_square_dvd I Q hI P hcop hpool hres
  have hn := QuadraticMainBoundary.norm_le_of_dvd (mul_ne_zero (rowPowerfulPart_ne_zero I) (pow_ne_zero 2 hQ)) hd
  have hp : 0<(Ideal.absNorm (∏ i,P i):ℝ) := actual_ideal_norm_pos _
    (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hpn := actual_ideal_norm_pos _ (rowPowerfulPart_ne_zero I)
  have hqn := actual_ideal_norm_pos Q hQ
  simp only [map_pow,map_mul,Nat.cast_pow,Nat.cast_mul] at hn
  have hh := Real.logb_le_logb_of_le hZ (sq_pos_of_pos hp) hn
  rw [Real.logb_pow,Real.logb_mul hpn.ne' (pow_ne_zero 2 hqn.ne'),Real.logb_pow] at hh
  norm_num at hh
  simpa only [normWidth,map_prod,Nat.cast_prod] using hh

lemma original_optional_powerful_width (J I Q Q₀ : Ideal Eis) (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (A : Finset (FreeReflection.pool J Q Q₀)) (Z : ℝ) (hZ : 1<Z) :
    2*normWidth Z (∏ b : A,((poolPrimeFamily J Q Q₀).restrict A).ideal b)≤
      normWidth Z (rowPowerfulPart I)+2*normWidth Z Q := by
  exact nonresidual_prime_product_width I Q hI hQ ((poolPrimeFamily J Q Q₀).restrict A).ideal
    ((poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A)
    (fun b => poolPrimeFamily_fiber_divides J I Q Q₀ hJ hI hQ hpower hmask b.val)
    (fun b => FreeReflection.pool_nonresidual I Q Q₀
      (CanonicalRowCompletion.nonresidualPoolEquiv J I Q Q₀ hJ hI hQ hpower hmask b.val)) Z hZ
lemma frozenExtracted_width_le {ι : Type*} [Fintype ι] (G : PrimeFamily ι)
    (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) (Z : ℝ) (hZ : 1<Z) :
    normWidth Z (frozenExtracted G j e v)≤normWidth Z (∏ i,G.ideal i) := by
  have hd : reflectionExtractedDivisor G.ideal j e v∣∏ i,G.ideal i := by
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    unfold reflectionExtractedPrime
    split_ifs
    · rfl
    · exact one_dvd _
  rw [←frozenExtracted_eq_ideal] at hd
  have hn := QuadraticMainBoundary.norm_le_of_dvd
    (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (G.ideal i))) hd
  exact Real.logb_le_logb_of_le hZ (actual_ideal_norm_pos _ (frozenExtracted_ne_zero G j e v)) hn

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1592

/- Original source: OAI/NumberTheory/DirichletL/Reflection/UniformTail.lean; sha256: b43a0bce58c061aef0217805f9d386ab8679316d1400029834dc1d525119881c -/
section Source1593
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u
variable {N a c : Eis} {mode : Bool}

theorem literal_reflected_raw_tail_type_uniform (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc a₀ b₀ →
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
  intro V hV ι _ G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  have hh := hb V hV scale 1 (Ideal.absNorm (∏ i,G.ideal i):ℝ) T hs (by norm_num) (Nat.cast_nonneg _) hT
    (literalRawCoefficient G D s hc j S u) (literalRawCoefficient_norm G D s hc hN hbase hchar j hj S u) cut hcut
  simpa only [one_pow,mul_one] using hh

theorem literal_reflected_dyadic_tail_type_uniform (lo hi : ℝ) (hlo : 0<lo) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc lo hi →
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
  obtain ⟨orders,C,hC,hb⟩ := literal_reflected_raw_tail_type_uniform (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A
  refine ⟨orders,C,hC,?_⟩
  intro V hV ι _ G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  obtain ⟨hn,hh⟩ := hb V hV G D s hc hN hbase hchar j hj S u scale T hs hT
    (fun x => cut (rawDyadicLabel x)) (fun x hx => by
      have hc' := hcut (rawDyadicLabel x) hx
      have hl := rawDyadicCenter_lower scale hs.le x
      linarith)
  rw [tsum_cut_dyadic _ cut hn.of_norm] at hh
  exact hh

theorem literal_dyadic_tail_uniform_height_type_uniform (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {ι : Type u} [Fintype ι], ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (θ X T : ℝ), 0<X → 0<T →
    ∀ cut : (ℕ×ℕ×ℕ)→Prop,
      (∀ i, cut i → 16*T≤rawDyadicCenter (literalRawScale G s X) i) →
      ‖∑' i : ℕ×ℕ×ℕ, if cut i then
        literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by
  obtain ⟨orders,C,hC,hbound⟩ := literal_reflected_dyadic_tail_type_uniform (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A
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
  intro ι _ G D s hc hN hbase hchar j hj S u θ X T hX hT cut hcut
  have hh := hbound (H θ) (hHs θ) G D s hc hN hbase hchar j hj S u
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
end SevenEighths.InverseReflectedPhase

end OAI

end Source1593

/- Original source: OAI/NumberTheory/DirichletL/Reflection/FamilyTail.lean; sha256: 10563d9b22cb46e8da84d0cd88d5a49fb0c4f1a34bc77d6f73e2a25a26a51067 -/
section Source1594
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def familyRawScale (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (X QK QP : ℝ) : ℝ :=
  actualKernelCoefficient F s 0 X/(QK^2*QP^2)

lemma familyRawScale_pos (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (X QK QP : ℝ) (hX : 0<X) (hQK : 0<QK) (hQP : 0<QP) : 0<familyRawScale F s X QK QP :=
  div_pos (actualKernelCoefficient_pos F s hc 0 X hX) (mul_pos (sq_pos_of_pos hQK) (sq_pos_of_pos hQP))

lemma literalRawScale_reflected (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (X : ℝ) :
    literalRawScale (F.reflected K hK S) s X=
      actualKernelCoefficient F s 0 X/((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i,S.ideal i):ℝ)^2) := by
  have hh := actual_theta_kernel_argument F K hK S s 0 X 1 1
  simpa only [map_one,Nat.cast_one,one_pow,mul_one,ramifiedScale,pow_zero,literalRawScale] using hh

lemma familyRawScale_le_literal (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (X QK QP : ℝ) (hX : 0<X)
    (hKr : (Ideal.absNorm K:ℝ)≤QK) (hPr : (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP) :
    familyRawScale F s X QK QP≤literalRawScale (F.reflected K hK S) s X := by
  rw [literalRawScale_reflected]
  have hk : (0:ℝ)<Ideal.absNorm K := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hK.1)
  have hp : (0:ℝ)<Ideal.absNorm (∏ i,S.ideal i) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (S.ideal i))))
  apply div_le_div_of_nonneg_left (actualKernelCoefficient_pos F s hc 0 X hX).le (by positivity)
  exact mul_le_mul (pow_le_pow_left₀ hk.le hKr 2) (pow_le_pow_left₀ hp.le hPr 2) (sq_nonneg _) (sq_nonneg _)

lemma reflected_norm_le_centers (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (QK QP : ℝ) (hKr : (Ideal.absNorm K:ℝ)≤QK)
    (hPr : (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP) :
    (Ideal.absNorm (∏ i,(F.reflected K hK S).ideal i):ℝ)≤
      (Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP := by
  rw [F.reflected_product]
  simp only [map_mul,Nat.cast_mul]
  have hk : 0≤QK := le_trans (Nat.cast_nonneg _) hKr
  exact mul_le_mul (mul_le_mul_of_nonneg_left hKr (Nat.cast_nonneg _)) hPr
    (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hk)

theorem original_family_dyadic_tail (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
      (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸(F.reflected K hK S).ideal i)≠2) →
    ∀ jF : φ→ℕ, (∀ i, jF i<6) → ∀ (u : Eisˣ) (θ X T QK QP : ℝ),
      0<X → 0<T → 0<QK → 0<QP →
      (Ideal.absNorm K:ℝ)≤QK → (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP →
      ‖∑' i : ℕ×ℕ×ℕ, if i∉retainedDyads (familyRawScale F s X QK QP) (16*T) then
        literalDyadicBlock (F.reflected K hK S) D s hc (reflectedExponent jF)
          (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
        C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
          T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹ := by
  obtain ⟨degree,C,hC,hbound⟩ := literal_dyadic_tail_uniform_height_type_uniform
    (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro φ σ _ _ F K hK S D s hc hN hbase hchar jF hj u θ X T QK QP hX hT hQK hQP hKr hPr
  have hs := familyRawScale_le_literal F K hK S s hc X QK QP hX hKr hPr
  have hsp := familyRawScale_pos F s hc X QK QP hX hQK hQP
  have hcut (i : ℕ×ℕ×ℕ) (hi : i∉retainedDyads (familyRawScale F s X QK QP) (16*T)) :
      16*T≤rawDyadicCenter (literalRawScale (F.reflected K hK S) s X) i := by
    have hlt := lt_of_not_ge (fun h => hi ((mem_retainedDyads _ _ hsp i).mpr h))
    apply hlt.le.trans
    unfold rawDyadicCenter
    rw [ramifiedScale_one_cube]
    gcongr
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  have hh := hbound (F.reflected K hK S) D s hc hN hbase hchar (reflectedExponent jF) hj'
    (slotIndices φ (PrimeIndex K) σ) u θ X T hX hT
    (fun i => i∉retainedDyads (familyRawScale F s X QK QP) (16*T)) hcut
  have hleft : ‖∑' i : ℕ×ℕ×ℕ, if i∉retainedDyads (familyRawScale F s X QK QP) (16*T) then
        literalDyadicBlock (F.reflected K hK S) D s hc (reflectedExponent jF)
          (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
      C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,(F.reflected K hK S).ideal i):ℝ)*T^(-(A:ℝ))*
        (literalRawScale (F.reflected K hK S) s X^2)⁻¹ := by
    apply le_trans ?_ hh
    apply le_of_eq
    congr 1
    apply tsum_congr
    intro i
    by_cases hi : i∈retainedDyads (familyRawScale F s X QK QP) (16*T) <;> simp [hi]
  apply hleft.trans
  have hnorm := reflected_norm_le_centers F K hK S QK QP hKr hPr
  gcongr
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1594

/- Original source: OAI/NumberTheory/DirichletL/Reflection/RetainedWidth.lean; sha256: a6b0ef1306222d529cb569ddf3da10c422baa1164ff74ecf9f7d17aaf9fbe205 -/
section Source1595
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u
variable {a c : Eis} {mode : Bool}

lemma family_center_eq_kernel {φ : Type u} [Fintype φ] (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (X QK QP : ℝ) (i : ℕ×ℕ×ℕ) :
    rawDyadicCenter (familyRawScale F s X QK QP) i=
      kernelCenter (actualKernelCoefficient F s i.1 X) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) := by
  unfold rawDyadicCenter familyRawScale kernelCenter actualKernelCoefficient fixedKernelCoefficient
  simp only [map_one,Nat.cast_one,one_pow,mul_one,ramifiedScale,pow_zero,one_mul]
  ring

theorem actual_retained_width_uniform
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ {φ : Type u} [Fintype φ],
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3) (Z X QK QP δ : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<X → 0<QK → 0<QP →
      i∈retainedDyads (familyRawScale F s X QK QP) (16*Z^δ) →
      Real.logb Z (kn*((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1))+
        3*Real.logb Z (kb*((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2))+
        InverseTerminalWidths.ramifiedWidth Z i.1 ≤
      InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP)) (Real.logb Z X)
        F.ideal jF e + δ+η := by
  let Cf := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3/(kK^2*kP^2)
  have hcn : (0:ℝ)<Ideal.absNorm (Ideal.span {c}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
  have htau := sourceCuspScale_pos s.index
  have hCf : 0<Cf := by dsimp only [Cf]; positivity
  obtain ⟨Z₀,hZ₀,hlog⟩ := InverseTerminalWidths.constant_log_error (16*Cf) η (by positivity) hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro φ _ F jF e Z X QK QP δ i hZ hX hQK hQP hi
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hs := familyRawScale_pos F s hc X QK QP hX hQK hQP
  have hret := (mem_retainedDyads _ _ hs i).mp hi
  rw [family_center_eq_kernel] at hret
  have hR : 0<kernelCenter (actualKernelCoefficient F s i.1 X) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) := by
    have hcoef := actualKernelCoefficient_pos F s hc i.1 X hX
    unfold kernelCenter
    positivity
  have hrl := Real.logb_le_logb_of_le hz hR hret
  rw [Real.logb_mul (by norm_num : (16:ℝ)≠0) (Real.rpow_pos_of_pos (lt_trans zero_lt_one hz) δ).ne',
    Real.logb_rpow (lt_trans zero_lt_one hz) (ne_of_gt hz)] at hrl
  have he := actual_kernel_upper_threshold F jF e s hc i.1 Z X QK QP
    ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) kK kP kn kb hX hQK hQP (by positivity) (by positivity) hkK hkP hkn hkb
  rw [literal_ramified_width_offset] at he
  have hl : Real.logb Z 16+Real.logb Z Cf≤η := by
    rw [←Real.logb_mul (by norm_num : (16:ℝ)≠0) hCf.ne']
    exact hlog Z hZ
  have hoff : 0≤4*Real.logb Z 3 := mul_nonneg (by norm_num) (Real.logb_nonneg hz (by norm_num))
  change _ = _+Real.logb Z Cf at he
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1595

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SurvivingGate.lean; sha256: 00fa12362473bf0d71f3311d583805ec7ca97285ba4c40003efb2b9e53a0d45e -/
section Source1596
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u
variable {a c : Eis} {mode : Bool}

theorem actual_surviving_retained_gates
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ {φ : Type u} [Fintype φ],
    ∀ (F : PrimeFamily φ), Pairwise (Function.onFun IsCoprime F.ideal) →
    ∀ (jF : φ→ℕ) (A : Ideal Eis→Ideal Eis→ℂ) (e : φ→Fin 3)
      (Z X QK QP δ : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<X → 0<QK → 0<QP →
      i∈retainedDyads (familyRawScale F s X QK QP) (16*Z^δ) →
      e∈survivingFrozenBranches F jF A (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1))
      let ell := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2))
      0≤v ∧ 0≤ell ∧ -η≤InverseTerminalWidths.ramifiedWidth Z i.1 ∧
      v+3*ell+InverseTerminalWidths.ramifiedWidth Z i.1≤
        InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP)) (Real.logb Z X)
          F.ideal jF e+δ+η := by
  obtain ⟨Z₁,hZ₁,hwidth⟩ := actual_retained_width_uniform s hc kK kP 1 1 η hkK hkP (by norm_num) (by norm_num) hη
  obtain ⟨Z₂,hZ₂,hram⟩ := InverseTerminalWidths.ramified_width_threshold η hη
  refine ⟨max Z₁ Z₂,lt_of_lt_of_le hZ₁ (le_max_left _ _),?_⟩
  intro φ _ F hF jF A e Z X QK QP δ i hZ hX hQK hQP hi he
  have hz1 := (le_max_left Z₁ Z₂).trans hZ
  have hz2 := (le_max_right Z₁ Z₂).trans hZ
  have hz := lt_of_lt_of_le hZ₁ hz1
  have hnorm := surviving_forced_norms F hF jF A (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
    ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
    (fun n hn => ⟨(reflectedNDyad_bounds _ n hn).1.2,(reflectedNDyad_bounds _ n hn).2.2⟩)
    (fun b hb => ⟨(reflectedBDyad_bounds _ b hb).1,(reflectedBDyad_bounds _ b hb).2.2⟩) e he
  have hp (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  refine ⟨Real.logb_nonneg hz ((one_le_div (hp 1)).mpr hnorm.1),
    Real.logb_nonneg hz ((one_le_div (hp 2)).mpr hnorm.2),hram Z hz2 i.1,?_⟩
  simpa only [one_mul] using hwidth F jF e Z X QK QP δ i hz1 hX hQK hQP hi
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1596

/- Original source: OAI/NumberTheory/DirichletL/Reflection/RetainedCaps.lean; sha256: 5ec1a8ed61a846c7801ac246cc348050edcb654e886494debaf6394484d6f397 -/
section Source1597
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section

lemma retained_shell_le_ratio (scale T : ℝ) (hs : 0<scale)
    (i : ℕ×ℕ×ℕ) (hi : i∈retainedDyads scale (16*T)) :
    (2:ℝ)^i.2.2≤16*T/scale ∧ (2:ℝ)^i.2.1≤16*T/scale := by
  have hh := (mem_retainedDyads _ _ hs i).mp hi
  have hl := rawDyadicCenter_pow_lower scale hs.le i
  have hp : (2:ℝ)^(i.1+i.2.2+3*i.2.1)≤16*T/scale := by
    exact (le_div_iff₀ hs).mpr (by nlinarith)
  constructor
  · exact (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show i.2.2 ≤ i.1 + i.2.2 + 3 * i.2.1 by omega)).trans hp
  · exact (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show i.2.1 ≤ i.1 + i.2.2 + 3 * i.2.1 by omega)).trans hp

lemma retained_shell_log_cap (scale Z δ Lcap η : ℝ) (hs : 0<scale) (hZ : 1<Z)
    (hscale : scale⁻¹≤Z^Lcap) (hconst : Real.logb Z 16≤η)
    (i : ℕ×ℕ×ℕ) (hi : i∈retainedDyads scale (16*Z^δ)) :
    Real.logb Z ((2:ℝ)^i.2.2)≤δ+Lcap+η ∧
    Real.logb Z ((2:ℝ)^i.2.1)≤δ+Lcap+η := by
  have hz := lt_trans zero_lt_one hZ
  have hb : 16*Z^δ/scale≤16*Z^(δ+Lcap) := by
    rw [Real.rpow_add hz,div_eq_mul_inv,←mul_assoc]
    exact mul_le_mul_of_nonneg_left hscale (by positivity)
  have hshell := retained_shell_le_ratio scale (Z^δ) hs i hi
  have hlog (n : ℕ) (hn : (2:ℝ)^n≤16*Z^(δ+Lcap)) :
      Real.logb Z ((2:ℝ)^n)≤δ+Lcap+η := by
    have hh := Real.logb_le_logb_of_le hZ (by positivity : (0:ℝ)<2^n) hn
    rw [Real.logb_mul (by norm_num : (16:ℝ)≠0) (Real.rpow_pos_of_pos hz _).ne',
      Real.logb_rpow hz (ne_of_gt hZ)] at hh
    linarith
  exact ⟨hlog _ (hshell.1.trans hb),hlog _ (hshell.2.trans hb)⟩

lemma extracted_log_le_shell (Z Q : ℝ) (hZ : 1<Z) (hQ : 0<Q)
    (I : Ideal ActualEisensteinCubic.O) (hI : I≠0) :
    Real.logb Z (Q/Ideal.absNorm I)≤Real.logb Z Q := by
  have hn : (1:ℝ)≤Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  apply Real.logb_le_logb_of_le hZ (div_pos hQ (lt_of_lt_of_le zero_lt_one hn))
  exact div_le_self hQ.le hn

lemma retained_extracted_log_budget (scale Z δ Lscale Lrow Lslot η X L : ℝ)
    (hs : 0<scale) (hZ : 1<Z) (hX : 0<X) (hL : 0<L)
    (hscale : scale⁻¹≤Z^Lscale) (hconst : Real.logb Z 16≤η)
    (hrow : X≤Z^Lrow) (hslot : L≤Z^Lslot)
    (i : ℕ×ℕ×ℕ) (hi : i∈retainedDyads scale (16*Z^δ))
    (D1 D2 : Ideal ActualEisensteinCubic.O) (h1 : D1≠0) (h2 : D2≠0) :
    Real.logb Z X+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm D1)+
      Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm D2)+Real.logb Z L≤
        Lrow+Lslot+2*(δ+Lscale+η) := by
  have hz := lt_trans zero_lt_one hZ
  have hr := Real.logb_le_logb_of_le hZ hX hrow
  have hl := Real.logb_le_logb_of_le hZ hL hslot
  rw [Real.logb_rpow hz (ne_of_gt hZ)] at hr hl
  obtain ⟨hn,hb⟩ := retained_shell_log_cap scale Z δ Lscale η hs hZ hscale hconst i hi
  have hn' := extracted_log_le_shell Z ((2:ℝ)^i.2.2) hZ (by positivity) D1 h1
  have hb' := extracted_log_le_shell Z ((2:ℝ)^i.2.1) hZ (by positivity) D2 h2
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1597

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowReflectedExponent.lean; sha256: ab497dc85da3ae547aac9dfcf8a0b06c23a498be18bf8648bf5657aa1239a6fd -/
section Source1598
namespace OAI

namespace SevenEighths.ProbeLowReflected
open InverseTerminalWidths

lemma hybrid_half_with_error {v za ε : ℝ} (hv : -ε≤v) (hε : 0≤ε)
    (hu : hybridSaving v za≠za) : v/2-ε/2≤hybridSaving v za := by
  unfold hybridSaving at *
  rcases le_total v (min za ((v+za)/3)) with h|h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h] at *
    rcases le_total za ((v+za)/3) with hz|hz
    · exact (hu (min_eq_left hz)).elim
    · rw [min_eq_right hz]
      have hzv := min_le_left za ((v+za)/3)
      rw [min_eq_right hz] at hzv
      linarith

lemma retained_kernel_quarter (Td y : ℝ) : Td/4≤y/4+max 0 (Td-y)/2 := by
  have h0 := le_max_left 0 (Td-y)
  have h1 := le_max_right 0 (Td-y)
  linarith

theorem compensated_reflected_exponent (d O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hd : 0≤d) (_hd1 : d≤1/6) (hε : 0≤ε)
    (hO : -ε≤O₀) (hH : H≤(5/6-2*d)-O₀+ε)
    (hA : 2*A₀≤O₀+ε) (hN : 0≤N₀) (hNA : N₀≤A₀)
    (hS : 0≤S₀) (hB : 0≤B₀) (hz : za≤1/6-d)
    (hv : -ε≤v) (hl : -ε≤ell) (he : -ε≤el) (hθ : |θ|≤ε)
    (hret : v+3*ell+el≤2*H+2*A₀+2*za-1-(1/6-d)-θ-N₀-3*B₀+ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2*H+2*A₀+2*za-1-(1/6-d)-θ-N₀-3*B₀)≤5/6-2*d+20*ε := by
  let Td := 2*H+2*A₀+2*za-1-(1/6-d)-θ-N₀-3*B₀
  have hθlo : -ε≤θ := (abs_le.mp hθ).1
  have hθhi : θ≤ε := (abs_le.mp hθ).2
  have hTd : Td≤H-3*d+3*ε := by dsimp [Td];linarith
  have hcol : v+ell≤H+7*ε := by dsimp [Td] at hTd;linarith
  have hmax : max H (v+ell)≤H+7*ε := max_le (by linarith) hcol
  have hk := le_max_left 0 (Td-v-3*ell-el)
  by_cases hu : hybridSaving v za=za
  · unfold reflectedExponent
    rw [hu]
    change O₀/2+max H (v+ell)-S₀-B₀+za-za-ell-2*el/3-max 0 (Td-v-3*ell-el)/2≤_
    linarith
  · have hhalf := hybrid_half_with_error hv hε hu
    have hquarter := retained_kernel_quarter Td (v+3*ell+el)
    have hcharge : Td/4-17*ε/12≤
        hybridSaving v za+ell+2*el/3+max 0 (Td-v-3*ell-el)/2 := by
      have heq : Td-(v+3*ell+el)=Td-v-3*ell-el := by ring
      rw [heq] at hquarter
      linarith
    have hbound : reflectedExponent O₀ H S₀ B₀ za v ell el Td≤
        O₀/2+H-S₀-B₀+za-Td/4+(7+17/12)*ε := by
      unfold reflectedExponent
      linarith
    change reflectedExponent O₀ H S₀ B₀ za v ell el Td≤_
    apply hbound.trans
    dsimp [Td]
    linarith

end SevenEighths.ProbeLowReflected

end OAI

end Source1598

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowReflectedLength.lean; sha256: 4b78ca2d011881e543b7f2d9feb1e4de13b9cc61aba98524561a84dcc549908c -/
section Source1599
namespace OAI

namespace SevenEighths.ProbeLowReflected
open InverseTerminalWidths

theorem compensated_reflected_exponent_with_length (d ell₀ O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hd : 0≤d) (_hd1 : d≤1/6) (hε : 0≤ε)
    (hO : -ε≤O₀) (hH : H≤(5/6-2*d)-O₀+ε)
    (hA : 2*A₀≤O₀+ε) (hN : 0≤N₀) (hNA : N₀≤A₀)
    (hS : 0≤S₀) (hB : 0≤B₀) (hell : ell₀≤1/6-d+ε) (hz : za≤ell₀+ε)
    (hv : -ε≤v) (hl : -ε≤ell) (he : -ε≤el) (hθ : |θ|≤ε)
    (hret : v+3*ell+el≤2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀+ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀)≤5/6-2*d+40*ε := by
  let Td := 2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀
  have hθlo : -ε≤θ := (abs_le.mp hθ).1
  have hθhi : θ≤ε := (abs_le.mp hθ).2
  have hTd : Td≤H-3*d+6*ε := by dsimp [Td];linarith
  have hcol : v+ell≤H+10*ε := by dsimp [Td] at hTd;linarith
  have hmax : max H (v+ell)≤H+10*ε := max_le (by linarith) hcol
  have hk := le_max_left 0 (Td-v-3*ell-el)
  by_cases hu : hybridSaving v za=za
  · unfold reflectedExponent
    rw [hu]
    change O₀/2+max H (v+ell)-S₀-B₀+za-za-ell-2*el/3-max 0 (Td-v-3*ell-el)/2≤_
    linarith
  · have hhalf := hybrid_half_with_error hv hε hu
    have hquarter := retained_kernel_quarter Td (v+3*ell+el)
    have hcharge : Td/4-17*ε/12≤
        hybridSaving v za+ell+2*el/3+max 0 (Td-v-3*ell-el)/2 := by
      have heq : Td-(v+3*ell+el)=Td-v-3*ell-el := by ring
      rw [heq] at hquarter
      linarith
    have hbound : reflectedExponent O₀ H S₀ B₀ za v ell el Td≤
        O₀/2+H-S₀-B₀+za-Td/4+(10+17/12)*ε := by
      unfold reflectedExponent
      linarith
    change reflectedExponent O₀ H S₀ B₀ za v ell el Td≤_
    apply hbound.trans
    dsimp [Td]
    linarith

end SevenEighths.ProbeLowReflected

end OAI

end Source1599
