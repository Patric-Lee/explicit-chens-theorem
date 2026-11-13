import OpenAIGrouped.Unit037
import OpenAIGrouped.Unit034

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Reflection/Surviving.lean; sha256: 14341c8e3b084588f52720d0f118cee2a6c0b7d71cd01a8550a6e1c0aa24a483 -/
section Source1520
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {a c : Eis} {mode : Bool}

def survivingFrozenBranches (F : PrimeFamily φ) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) : Finset (φ→Fin 3) :=
  Finset.univ.filter (fun e => ∃ n∈nset, ∃ b∈bset, frozenBranchColumn F jF e A n b≠0)

lemma mem_survivingFrozenBranches (F : PrimeFamily φ) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) (e : φ→Fin 3) :
    e∈survivingFrozenBranches F jF A nset bset ↔
      ∃ n∈nset, ∃ b∈bset, frozenBranchColumn F jF e A n b≠0 := by
  simp [survivingFrozenBranches]

lemma frozenBranchColumn_weight (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (A w : Ideal Eis→Ideal Eis→ℂ) (n b : Ideal Eis) :
    frozenBranchColumn F jF e (fun n b => A n b*w n b) n b =
      w n b*frozenBranchColumn F jF e A n b := by
  unfold frozenBranchColumn
  ring

lemma weighted_branch_zero_of_not_surviving (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (S : Ideal Eis→PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis→Ideal Eis→ℂ)
    (r aw : Ideal Eis→ℂ) (w : Ideal Eis→Ideal Eis→ℂ) (u : Eisˣ) (m : ℕ)
    (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis)
    (he : e∉survivingFrozenBranches F jF A nset bset) :
    weightedReflectedBranchHybridRow F jF e S s κ A r aw w u m Pset nset bset K=0 := by
  have hz : ∀ n∈nset, ∀ b∈bset, frozenBranchColumn F jF e A n b=0 := by
    intro n hn b hb
    by_contra h
    exact he ((mem_survivingFrozenBranches F jF A nset bset e).mpr ⟨n,hn,b,hb,h⟩)
  unfold weightedReflectedBranchHybridRow hybridRow hybridInner
  simp only [frozenBranchColumn_weight]
  have hi (P : Ideal Eis) : (∑ n∈nset, ∑ b∈bset,
      w n b*frozenBranchColumn F jF e A n b * quadraticRow K (primaryGenerator (n*b))*
        inverseCubicKernel P n*(if IsCoprime P b then 1 else 0))=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    apply Finset.sum_eq_zero
    intro b hb
    simp [hz n hn b hb]
  simp only [hi,mul_zero,Finset.sum_const_zero]

lemma sum_branches_eq_surviving (F : PrimeFamily φ) (jF : φ→ℕ)
    (S : Ideal Eis→PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis→Ideal Eis→ℂ)
    (r aw : Ideal Eis→ℂ) (w : Ideal Eis→Ideal Eis→ℂ) (u : Eisˣ) (m : ℕ)
    (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis) :
    (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s κ A r aw w u m Pset nset bset K)=
    ∑ e∈survivingFrozenBranches F jF A nset bset,
      weightedReflectedBranchHybridRow F jF e S s κ A r aw w u m Pset nset bset K := by
  apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro e _ he
  exact weighted_branch_zero_of_not_surviving F jF e S s κ A r aw w u m Pset nset bset K he

theorem surviving_forced_norms (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) (Y B : ℝ)
    (hn : ∀ n∈nset, primaryGenerator n≠0 ∧ (Ideal.absNorm n:ℝ)≤Y)
    (hb : ∀ b∈bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B)
    (e : φ→Fin 3) (he : e∈survivingFrozenBranches F jF A nset bset) :
    (Ideal.absNorm (frozenExtracted F jF e 1):ℝ)≤Y ∧
    (Ideal.absNorm (frozenExtracted F jF e 2):ℝ)≤B := by
  obtain ⟨n,hn',b,hb',hz⟩ := (mem_survivingFrozenBranches F jF A nset bset e).mp he
  obtain ⟨hd1,hd2,_⟩ := frozenBranchColumn_divisibility F hF jF e A n b (hn n hn').1 (hb b hb').1 hz
  have hn0 : n≠0 := by intro h; exact (hn n hn').1 (by rw [h,primaryGenerator_zero])
  have hb0 : b≠0 := by intro h; exact (hb b hb').1 (by rw [h,primaryGenerator_zero])
  have hnpos : 0<Ideal.absNorm n := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn0)
  have hbpos : 0<Ideal.absNorm b := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hb0)
  constructor
  · exact le_trans (by exact_mod_cast Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm hd1)) (hn n hn').2
  · exact le_trans (by exact_mod_cast Nat.le_of_dvd hbpos (map_dvd Ideal.absNorm hd2)) (hb b hb').2

theorem surviving_extracted_scales (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis)) (Y B : ℝ)
    (hn : ∀ n∈nset, primaryGenerator n≠0 ∧ (Ideal.absNorm n:ℝ)≤Y)
    (hb : ∀ b∈bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B)
    (e : φ→Fin 3) (he : e∈survivingFrozenBranches F jF A nset bset) :
    extractedDualScale (frozenExtracted F jF e 1) Y = Y/Ideal.absNorm (frozenExtracted F jF e 1) ∧
    extractedDualScale (frozenExtracted F jF e 2) B = B/Ideal.absNorm (frozenExtracted F jF e 2) := by
  have h := surviving_forced_norms F hF jF A nset bset Y B hn hb e he
  have hp (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  exact ⟨max_eq_right ((one_le_div (hp 1)).mpr h.1),
    max_eq_right ((one_le_div (hp 2)).mpr h.2)⟩

theorem surviving_frozen_local_assignments (F : PrimeFamily φ) (jF : φ→ℕ)
    (A : Ideal Eis→Ideal Eis→ℂ) (nset bset : Finset (Ideal Eis))
    (e : φ→Fin 3) (he : e∈survivingFrozenBranches F jF A nset bset) :
    ∃ n∈nset, ∃ b∈bset, ∀ i,
      (jF i≠4 → e i=0) ∧
      (jF i=4 → e i=1 → primaryGenerator n∈F.ideal i) ∧
      (jF i=4 → e i=2 → primaryGenerator n∉F.ideal i ∧ primaryGenerator b∈F.ideal i) := by
  obtain ⟨n,hn,b,hb,hz⟩ := (mem_survivingFrozenBranches F jF A nset bset e).mp he
  refine ⟨n,hn,b,hb,?_⟩
  have hh := (mul_ne_zero_iff.mp hz).2
  intro i
  have hi := (Finset.prod_ne_zero_iff.mp hh) i (Finset.mem_univ i)
  simpa only [PrimeFamily.generator_span] using
    InverseTerminalWidths.surviving_local_piece (Ideal.span {F.generator i}) (F.generator_good i)
      (jF i) (e i) (primaryGenerator n) (primaryGenerator b) hi

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1520

/- Original source: OAI/NumberTheory/DirichletL/Reflection/FilteredEnergy.lean; sha256: 4ded73ee6203a2e2848a6a87d0d01cc7eac2bc85bc180aae9ea20e6704bcdfee -/
section Source1521
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem filtered_actual_weighted_reflected_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ) (E : Finset (φ→Fin 3))
      (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ K ∈ rows, ‖r K‖ ≤ 1) → (∀ P ∈ Pset, ‖aw P‖ ≤ 1) → (∀ n b, ‖w n b‖ ≤ 1) →
      (∑ K ∈ rows, ‖∑ e∈E, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2) ≤
      (E.card:ℝ) * ∑ e∈E,
        let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
        let Bq := extractedDualScale (frozenExtracted F jF e 2) B
        (frozenBranchScale F jF e)^2*
          (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := actual_weighted_reflected_branch_energy (φ := φ) (σ := σ)
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S E r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP hr haw hw
  calc
    _ ≤ ∑ K ∈ rows, (E.card:ℝ)*
        ∑ e∈E, ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2 := by
      apply Finset.sum_le_sum
      intro K hK
      exact CubicEisenstein.norm_sum_sq_le_card E
        (fun e : φ→Fin 3 => weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K)
    _ = (E.card:ℝ)*∑ e∈E, ∑ K ∈ rows,
        ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he'
      exact he X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
        G0 D0 u m rows nset bset Pset S r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP hr haw hw

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1521

/- Original source: OAI/NumberTheory/DirichletL/Reflection/FilteredMeasure.lean; sha256: 7fb6d8dbbaa6a7c9aaab75dbf5d1f54e1fabd66d9d630497dbffe7ccbfb80fe2 -/
section Source1522
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

theorem integrated_filtered_actual_reflected_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ) (branches : Finset (φ→Fin 3))
      (μ : Measure Ω) (density : Ω → ℂ) (scalar : ℂ)
      (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      Integrable density μ →
      (∀ K ∈ rows, AEStronglyMeasurable (fun t => r t K) μ) →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ) →
      (∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) →
      (∀ t, ∀ K ∈ rows, ‖r t K‖ ≤ 1) → (∀ t, ∀ P ∈ Pset, ‖aw t P‖ ≤ 1) →
      (∀ t n b, ‖w t n b‖ ≤ 1) →
      (∑ K ∈ rows, ‖scalar * ∫ t, density t * (∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2) ≤
      ‖scalar‖^2*((branches.card:ℝ)*∑ e∈branches,
          let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
          let Bq := extractedDualScale (frozenExtracted F jF e 2) B
          (frozenBranchScale F jF e)^2*
            (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))))*(∫ t, ‖density t‖ ∂μ)^2 := by
  obtain ⟨C,hC,he⟩ := filtered_actual_weighted_reflected_energy (φ := φ) (σ := σ)
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S branches μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
  let E : ℝ := (branches.card:ℝ)*∑ e∈branches,
          let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
          let Bq := extractedDualScale (frozenExtracted F jF e 2) B
          (frozenBranchScale F jF e)^2*
            (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ)))
  have hE : 0 ≤ E := by
    dsimp only [E]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro e he
    have hYq : 0 ≤ extractedDualScale (frozenExtracted F jF e 1) Y := le_trans zero_le_one (le_max_left _ _)
    have hBq : 0 ≤ extractedDualScale (frozenExtracted F jF e 2) B := le_trans zero_le_one (le_max_left _ _)
    positivity
  let ψ : rows → Ω → ℂ := fun K t => (∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val)
  have hbound (t : Ω) : (∑ K, ‖ψ K t‖^2) ≤ E := by
    change (∑ K : rows, ‖(∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val)‖^2) ≤ E
    rw [Finset.sum_coe_sort rows (fun K : Ideal Eis => ‖(∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K)‖^2)]
    exact he X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
      G0 D0 u m rows nset bset Pset S branches (r t) (aw t) (w t)
      hrows hrowcop hproducts hScop hSN hSchar hn hb hP (hr t) (haw t) (hw t)
  have hψM (K : rows) : AEStronglyMeasurable (ψ K) μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro e he
    exact weightedReflectedBranchHybridRow_aestronglyMeasurable μ F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K.val
      (hrM K.val K.property) hawM hwM
  have hpoint (K : rows) (t : Ω) : ‖ψ K t‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖ψ j t‖) (Finset.mem_univ K)).trans (hbound t)
  have hint (K : rows) : Integrable (fun t => density t*ψ K t) μ :=
    hdensity.mul_bdd (hψM K) (Filter.Eventually.of_forall (hpoint K))
  have hh := mul_le_mul_of_nonneg_left
    (common_measure_energy μ density ψ E hE hdensity.norm hint hbound) (sq_nonneg ‖scalar‖)
  have hsum : (∑ K : rows, ‖∫ t, density t*ψ K t ∂μ‖^2) =
      ∑ K ∈ rows, ‖∫ t, density t*(∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2 :=
    Finset.sum_coe_sort rows (fun K : Ideal Eis =>
      ‖∫ t, density t*(∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2)
  rw [hsum] at hh
  simp only [norm_mul,mul_pow,← Finset.mul_sum]
  simpa only [E,mul_assoc] using hh

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1522

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SurvivingEnergy.lean; sha256: edf57e7e7d1b6cfa63ef32087a272305edf67ba28c4966c2510f47f884777198 -/
section Source1523
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem surviving_physical_source_energy
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C₀ C : ℝ), 0≤C₀ ∧ 0<C ∧
    ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
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
  obtain ⟨C,hC,henergy⟩ := integrated_filtered_actual_reflected_energy
    (Ω := ℝ) (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode) ε hε
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsource⟩ := weighted_finite_physical_row_branch_measure
    (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode)
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW 0
  refine ⟨degree,C₀,C,hC₀,hC,?_⟩
  intro X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
  let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R
  let density := twistedDensity U W θ R
  let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
  let r := fun t K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ)
  let aw := fun t P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ)
  let w := fun t n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)
  obtain ⟨hsource',hdi,_,hl1,_⟩ := hsource F s hc u m θ T QK QP Qn Qb hT hQK hQP hQn hQb
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

end Source1523

/- Original source: OAI/NumberTheory/DirichletL/Reflection/AnnularNormalization.lean; sha256: 892dc0f7bd3dd7cae69efd652eefc912e3dca9967c232387741314882c202f88 -/
section Source1524
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

lemma reciprocal_annulus_normalization (r Qn Qb kn kb : ℝ)
    (hr : 0<r) (hn : 0<Qn) (hb : 0<Qb) (hkn : 0<kn) (hkb : 0<kb) :
    1/(r*Real.sqrt Qn*Qb) = Real.sqrt kn*kb/(r*Real.sqrt (kn*Qn)*(kb*Qb)) := by
  rw [Real.sqrt_mul hkn.le]
  have hs : Real.sqrt kn≠0 := (Real.sqrt_pos.mpr hkn).ne'
  field_simp

theorem physical_scalar_extracted (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r Qn Qb kn kb R A : ℝ)
    (hr : 0<r) (hn : 0<Qn) (hb : 0<Qb) (hkn : 0<kn) (hkb : 0<kb) :
    A/(r*Real.sqrt Qn*Qb)*smallScalar R =
      (A*Real.sqrt kn*kb)*extractedOutsideScalar F jF e r
        (kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1))
        (kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)) R := by
  have hp (v : Fin 3) : (Ideal.absNorm (frozenExtracted F jF e v):ℝ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v)
  unfold extractedOutsideScalar
  rw [mul_div_cancel₀ _ (hp 1),mul_div_cancel₀ _ (hp 2)]
  have h := reciprocal_annulus_normalization r Qn Qb kn kb hr hn hb hkn hkb
  calc
    _ = A*(1/(r*Real.sqrt Qn*Qb))*smallScalar R := by ring
    _ = _ := by rw [h]; ring

theorem annular_kernel_threshold (Z T tau C r QK QP Qn Qb kn kb D1 D2 : ℝ)
    (hT : 0<T) (htau : 0<tau) (hC : 0<C) (hr : 0<r)
    (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkn : 0<kn) (hkb : 0<kb) (h1 : 0<D1) (h2 : 0<D2) :
    Real.logb Z (kn*Qn/D1)+3*Real.logb Z (kb*Qb/D2)+3*Real.logb Z r-
      Real.logb Z (kernelCenter (T/(27*tau^2*C^2)*r^3) QK QP Qn Qb) =
    Real.logb Z (27*tau^2*C^2*QK^2*QP^2*kn*kb^3/(T*D1*D2^3)) := by
  have hR : 0<kernelCenter (T/(27*tau^2*C^2)*r^3) QK QP Qn Qb := by
    unfold kernelCenter
    positivity
  have hv : 0<kn*Qn/D1 := by positivity
  have hl : 0<kb*Qb/D2 := by positivity
  have heq : (kn*Qn/D1)*(kb*Qb/D2)^3*r^3 /
      kernelCenter (T/(27*tau^2*C^2)*r^3) QK QP Qn Qb =
      27*tau^2*C^2*QK^2*QP^2*kn*kb^3/(T*D1*D2^3) := by
    unfold kernelCenter
    field_simp
  rw [← heq,Real.logb_div (by positivity) hR.ne',
    Real.logb_mul (by positivity) (pow_ne_zero _ hr.ne'),
    Real.logb_mul hv.ne' (pow_ne_zero _ hl.ne'),Real.logb_pow,Real.logb_pow]
  norm_num

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1524

/- Original source: OAI/NumberTheory/DirichletL/Reflection/TerminalThreshold.lean; sha256: 4a99abb39bb99ad2ccba8f99db7dd6bc464c4b30067ee2b93c1d2825e4bcbaa6 -/
section Source1525
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}

lemma frozenExtracted_eq_ideal (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3) (v : Fin 3) :
    frozenExtracted F jF e v = reflectionExtractedDivisor F.ideal jF e v := by
  simp only [frozenExtracted,PrimeFamily.generator_span]

theorem actual_kernel_terminal_threshold (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (m : ℕ) (Z T QK QP Qn Qb kn kb : ℝ)
    (hT : 0<T) (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkn : 0<kn) (hkb : 0<kb) :
    Real.logb Z (kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1))+
      3*Real.logb Z (kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2))+
      3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)-
      Real.logb Z (kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb) =
    InverseTerminalWidths.terminalDualWidth Z (Real.logb Z QK) (Real.logb Z QP) (Real.logb Z T)
      F.ideal jF e +
    Real.logb Z (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3) := by
  have hr : 0<ramifiedScale 1 completedRamifiedStep m := ramifiedScale_pos _ _
    (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) _
  have htau := sourceCuspScale_pos s.index
  have hp (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hcn := hp (Ideal.span {c}) (Ideal.span_singleton_eq_bot.not.mpr hc)
  have hfn := hp (∏ i, F.ideal i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (F.ideal i)))
  have hd (v : Fin 3) := hp (frozenExtracted F jF e v) (frozenExtracted_ne_zero F jF e v)
  have hcc : actualKernelCoefficient F s m T =
      T/(27*(sourceCuspScale s.index)^2*
        ((Ideal.absNorm (Ideal.span {c}):ℝ)*(Ideal.absNorm (∏ i,F.ideal i):ℝ))^2)*
      (ramifiedScale 1 completedRamifiedStep m)^3 := by
    simp only [actualKernelCoefficient,fixedKernelCoefficient,map_one,Nat.cast_one,one_pow,mul_one,map_mul,Nat.cast_mul]
  rw [hcc,annular_kernel_threshold Z T (sourceCuspScale s.index)
    ((Ideal.absNorm (Ideal.span {c}):ℝ)*(Ideal.absNorm (∏ i,F.ideal i):ℝ))
    _ QK QP Qn Qb kn kb _ _ hT htau (mul_pos hcn hfn) hr hK hP hn hb hkn hkb (hd 1) (hd 2)]
  unfold InverseTerminalWidths.terminalDualWidth InverseTerminalWidths.normWidth
  rw [← frozenExtracted_eq_ideal F jF e 1,← frozenExtracted_eq_ideal F jF e 2]
  have hd1 := hd 1
  have hd2 := hd 2
  simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow]
  norm_num only [Nat.cast_ofNat]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1525

/- Original source: OAI/NumberTheory/DirichletL/Reflection/RamifiedWidth.lean; sha256: 1c4b39018b6e1bbf5592f6036f9a853f59fd57f78a66b56fb5c9fc0cc2b03599 -/
section Source1526
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open CompletedDyadic CompletedGauss
noncomputable section

lemma literal_ramified_log_width (Z : ℝ) (m : ℕ) :
    3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m) =
      (m:ℝ)*Real.logb Z 3 := by
  rw [ramifiedScale,one_mul,Real.logb_pow,completedRamifiedStep,
    Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0:ℝ)<3)]
  ring

lemma literal_ramified_width_offset (Z : ℝ) (m : ℕ) :
    3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m) =
      InverseTerminalWidths.ramifiedWidth Z m + 4*Real.logb Z 3 := by
  rw [literal_ramified_log_width]
  unfold InverseTerminalWidths.ramifiedWidth
  ring

lemma reflectedExponent_ramified_shift (O₀ H S₀ B₀ za v ell el Td δ : ℝ) :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell el Td =
      InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell (el-δ) (Td-δ)-2*δ/3 := by
  unfold InverseTerminalWidths.reflectedExponent
  rw [show Td-δ-v-3*ell-(el-δ)=Td-v-3*ell-el by ring]
  ring

theorem literal_reflectedExponent_le_signed (Z : ℝ) (hZ : 1<Z) (m : ℕ)
    (O₀ H S₀ B₀ za v ell Td : ℝ) :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)) Td ≤
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (InverseTerminalWidths.ramifiedWidth Z m) (Td-4*Real.logb Z 3) := by
  have hδ : 0≤4*Real.logb Z 3 := mul_nonneg (by norm_num) (Real.logb_nonneg hZ (by norm_num))
  rw [reflectedExponent_ramified_shift O₀ H S₀ B₀ za v ell _ Td (4*Real.logb Z 3),
    literal_ramified_width_offset]
  rw [add_sub_cancel_right]
  linarith

theorem ramified_offset_threshold (η : ℝ) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ Z : ℝ, Z₀≤Z →
      0≤4*Real.logb Z 3 ∧ 4*Real.logb Z 3≤η := by
  obtain ⟨Z₀,hZ₀,hw⟩ := InverseTerminalWidths.ramified_width_threshold η hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have he := hw Z hZ 0
  unfold InverseTerminalWidths.ramifiedWidth at he
  norm_num at he
  exact ⟨mul_nonneg (by norm_num) (Real.logb_nonneg hz (by norm_num)),by linarith⟩

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1526

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ThresholdError.lean; sha256: fa9456b9521a10138e3dbd3e55a17c38713dc13f581ed3b88cd736488dcaa865 -/
section Source1527
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open CompletedDyadic CompletedGauss
noncomputable section

lemma fixed_abs_log_threshold (C η : ℝ) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ Z : ℝ, Z₀≤Z → |Real.logb Z C|≤η := by
  obtain ⟨Z₀,hZ₀,h⟩ := InverseTerminalWidths.constant_log_error
    (Real.exp |Real.log C|) η (Real.exp_pos _) hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ
  have hz : 0<Real.log Z := Real.log_pos (lt_of_lt_of_le hZ₀ hZ)
  have hh := h Z hZ
  simpa only [Real.logb,Real.log_exp,abs_div,abs_of_pos hz] using hh

lemma reflectedExponent_threshold_error (O₀ H S₀ B₀ za v ell el Td err η : ℝ)
    (herr : |err|≤η) :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell el (Td+err) ≤
      InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell el Td+η/2 := by
  have hη : 0≤η := (abs_nonneg err).trans herr
  have he : -η≤err := (abs_le.mp herr).1
  have hh : max 0 (Td-v-3*ell-el) ≤ max 0 (Td+err-v-3*ell-el)+η := by
    apply max_le
    · linarith [le_max_left (0:ℝ) (Td+err-v-3*ell-el)]
    · linarith [le_max_right (0:ℝ) (Td+err-v-3*ell-el)]
  unfold InverseTerminalWidths.reflectedExponent
  linarith

theorem literal_threshold_error_uniform (C η : ℝ) (hC : 0<C) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ Z : ℝ, Z₀≤Z → ∀ (m : ℕ) (O₀ H S₀ B₀ za v ell Td : ℝ),
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)) (Td+Real.logb Z C) ≤
      InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
        (InverseTerminalWidths.ramifiedWidth Z m) Td+η/2 := by
  obtain ⟨Z₀,hZ₀,herr⟩ := fixed_abs_log_threshold (C/81) η hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ m O₀ H S₀ B₀ za v ell Td
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hid : Td+Real.logb Z C-4*Real.logb Z 3=Td+Real.logb Z (C/81) := by
    rw [Real.logb_div hC.ne' (by norm_num)]
    have hp := Real.logb_pow Z 3 4
    norm_num at hp
    linarith
  have hh := literal_reflectedExponent_le_signed Z hz m O₀ H S₀ B₀ za v ell (Td+Real.logb Z C)
  rw [hid] at hh
  exact hh.trans (reflectedExponent_threshold_error O₀ H S₀ B₀ za v ell
    (InverseTerminalWidths.ramifiedWidth Z m) Td (Real.logb Z (C/81)) η (herr Z hZ))

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1527

/- Original source: OAI/NumberTheory/DirichletL/Reflection/AnnularExponent.lean; sha256: a35bf6d46fbe61ced81db07113f174124f35db08f479e81092dfdc093a41ae0f -/
section Source1528
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

theorem physical_scalar_hybrid_shape (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (Z r Qn Qb kn kb R A C X L ε : ℝ)
    (hZ : 1<Z) (hr : 0<r) (hn : 0<Qn) (hb : 0<Qb) (hkn : 0<kn) (hkb : 0<kb)
    (hR : 0<R) (hC : 0≤C) (hX : 0<X) (hL : 0<L) :
    let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
    let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
    (A/(r*Real.sqrt Qn*Qb)*smallScalar R)^2 * (frozenBranchScale F jF e)^2 *
      (C*(X*U*B*L)^ε*(X+U*B)*B*(U+L+(U*L)^(2/3:ℝ))) ≤
      (A*Real.sqrt kn*kb)^2*(6*C)*Z^(
        InverseTerminalWidths.reflectedExponent 0 (Real.logb Z X)
          (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
          (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
          (Real.logb Z L) (Real.logb Z U) (Real.logb Z B) (3*Real.logb Z r)
          (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R) +
        ε*(Real.logb Z X+Real.logb Z U+Real.logb Z B+Real.logb Z L)) := by
  let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
  let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
  have hp (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  have hU : 0<U := div_pos (mul_pos hkn hn) (hp 1)
  have hB : 0<B := div_pos (mul_pos hkb hb) (hp 2)
  have hs := physical_scalar_extracted F jF e r Qn Qb kn kb R A hr hn hb hkn hkb
  have he := extractedOutsideScalar_log_widths F jF e Z r U B R hZ hr hU hB hR
  have hz0 : 0<Z := lt_trans zero_lt_one hZ
  have hpow (Q : ℝ) (hQ : 0<Q) : Z^(Real.logb Z Q)=Q := Real.rpow_logb hz0 (ne_of_gt hZ) hQ
  have hh := normalized_hybrid_shape hZ.le (Real.logb Z X) (Real.logb Z U) (Real.logb Z B)
    (3*Real.logb Z r) (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
    (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
    (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R) (Real.logb Z L) ε
  rw [hpow X hX,hpow U hU,hpow B hB,hpow L hL,← he] at hh
  have hbnd := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hC)
    (sq_nonneg (A*Real.sqrt kn*kb))
  dsimp only
  rw [hs]
  convert hbnd using 1 <;> ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1528

/- Original source: OAI/NumberTheory/DirichletL/Reflection/UpperThreshold.lean; sha256: d730fefa6a9d7f0ed1f6a8b7e379174380bcd5a1ce54973efe2cae931150c1d5 -/
section Source1529
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}

theorem actual_kernel_upper_threshold (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (m : ℕ) (Z T QK QP Qn Qb kK kP kn kb : ℝ)
    (hT : 0<T) (hK : 0<QK) (hP : 0<QP) (hn : 0<Qn) (hb : 0<Qb)
    (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) :
    Real.logb Z (kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1))+
      3*Real.logb Z (kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2))+
      3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)-
      Real.logb Z (kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb) =
    InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP)) (Real.logb Z T)
      F.ideal jF e +
    Real.logb Z (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3/(kK^2*kP^2)) := by
  rw [actual_kernel_terminal_threshold F jF e s hc m Z T QK QP Qn Qb kn kb hT hK hP hn hb hkn hkb]
  have hcn : (0:ℝ)<Ideal.absNorm (Ideal.span {c}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
  have htau := sourceCuspScale_pos s.index
  unfold InverseTerminalWidths.terminalDualWidth
  rw [Real.logb_div (by positivity) (by positivity),Real.logb_mul hkK.ne' hK.ne',
    Real.logb_mul hkP.ne' hP.ne',Real.logb_mul (pow_ne_zero _ hkK.ne') (pow_ne_zero _ hkP.ne'),
    Real.logb_pow,Real.logb_pow]
  norm_num only [Nat.cast_ofNat]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1529

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ActualExponent.lean; sha256: b7991eab53e90932dd7e53068ceff08cbd69feee562e6bf5ffa1f658dd8c7fd9 -/
section Source1530
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
open InverseKernelSourceUniform
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ] {a c : Eis} {mode : Bool}

theorem actual_physical_shape_uniform
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ Z : ℝ, Z₀≤Z →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3) (m : ℕ)
      (T QK QP Qn Qb A C ε : ℝ), 0<T → 0<QK → 0<QP → 0<Qn → 0<Qb → 0≤C →
    let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
    let r := ramifiedScale 1 completedRamifiedStep m
    let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
    let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
    (A/(r*Real.sqrt Qn*Qb)*smallScalar R)^2*(frozenBranchScale F jF e)^2*
      (C*((kK*QK)*U*B*(kP*QP))^ε*((kK*QK)+U*B)*B*
        (U+(kP*QP)+(U*(kP*QP))^(2/3:ℝ))) ≤
    (A*Real.sqrt kn*kb)^2*(6*C)*Z^(
      InverseTerminalWidths.reflectedExponent 0 (Real.logb Z (kK*QK))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
        (Real.logb Z (kP*QP)) (Real.logb Z U) (Real.logb Z B)
        (InverseTerminalWidths.ramifiedWidth Z m)
        (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK))
          (Real.logb Z (kP*QP)) (Real.logb Z T) F.ideal jF e) +
      ε*(Real.logb Z (kK*QK)+Real.logb Z U+Real.logb Z B+Real.logb Z (kP*QP))+η/2) := by
  let Cf := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3/(kK^2*kP^2)
  have hcn : (0:ℝ)<Ideal.absNorm (Ideal.span {c}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
  have htau := sourceCuspScale_pos s.index
  have hCf : 0<Cf := by dsimp only [Cf]; positivity
  obtain ⟨Z₀,hZ₀,he⟩ := literal_threshold_error_uniform Cf η hCf hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ F jF e m T QK QP Qn Qb A C ε hT hK hP hn hb hC
  let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
  let r := ramifiedScale 1 completedRamifiedStep m
  let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
  let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hr : 0<r := ramifiedScale_pos _ _ (by norm_num)
    (lt_trans zero_lt_one completedRamifiedStep_gt_one) _
  have hR : 0<R := by
    have hcc := actualKernelCoefficient_pos F s hc m T hT
    dsimp only [R,kernelCenter]
    positivity
  have hh := physical_scalar_hybrid_shape F jF e Z r Qn Qb kn kb R A C (kK*QK) (kP*QP) ε
    hz hr hn hb hkn hkb hR hC (mul_pos hkK hK) (mul_pos hkP hP)
  dsimp only at hh ⊢
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hC))
  apply Real.rpow_le_rpow_of_exponent_le hz.le
  have hthreshold := actual_kernel_upper_threshold F jF e s hc m Z T QK QP Qn Qb kK kP kn kb
    hT hK hP hn hb hkK hkP hkn hkb
  have hexp := he Z hZ m 0 (Real.logb Z (kK*QK))
    (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
    (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
    (Real.logb Z (kP*QP)) (Real.logb Z U) (Real.logb Z B)
    (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP))
      (Real.logb Z T) F.ideal jF e)
  change Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R = _ at hthreshold
  rw [hthreshold]
  linarith

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1530

/- Original source: OAI/NumberTheory/DirichletL/Reflection/NormalizedPhysical.lean; sha256: dc98d78e2a552a44404b105ccfc0ce362805ffbdc9ac9c8ae6deb2a9dc32bbae -/
section Source1531
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem normalized_surviving_physical_source_energy
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ (degree : ℕ) (C₀ C Z₀ : ℝ), 0≤C₀ ∧ 0<C ∧ 1<Z₀ ∧
    ∀ Z : ℝ, Z₀≤Z →
    ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ),
      (9:Eis)*c ∣ N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f, jF f<6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (T θ QK QP Qn Qb : ℝ),
      0<T → 0<QK → 0<QP → 0<Qn → 0<Qb →
      X=kK*QK → Y=kn*Qn → B=kb*Qb → L=kP*QP →
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
      let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
      (∑ K : rows, ‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀‖^2) ≤
      ((branches.card:ℝ)*∑ e∈branches,
        let U := Y/Ideal.absNorm (frozenExtracted F jF e 1)
        let Bb := B/Ideal.absNorm (frozenExtracted F jF e 2)
        (Real.exp (M 2/2+M 3)*Real.sqrt kn*kb)^2*(6*C)*Z^(
          InverseTerminalWidths.reflectedExponent 0 (Real.logb Z X)
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
            (Real.logb Z L) (Real.logb Z U) (Real.logb Z Bb)
            (InverseTerminalWidths.ramifiedWidth Z m)
            (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z X) (Real.logb Z L) (Real.logb Z T) F.ideal jF e)+
          ε*(Real.logb Z X+Real.logb Z U+Real.logb Z Bb+Real.logb Z L)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,C₀,C,hC₀,hC,hsource⟩ := surviving_physical_source_energy
    (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode)
    ε hε a₀ b₀ ha₀ windows M hM hwindowNorm hwindows W hWsupport hW
  obtain ⟨Z₀,hZ₀,hshape⟩ := actual_physical_shape_uniform (φ := φ) s hc
    kK kP kn kb η hkK hkP hkn hkb hη
  refine ⟨degree,C₀,C,Z₀,hC₀,hC,hZ₀,?_⟩
  intro Z hZ X Y B L hX hY hB hL F jF hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb hsX hsY hsB hsL
    rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  have hh := hsource X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
  let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*
    smallScalar (kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb)
  dsimp only at hh ⊢
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [mul_left_comm (scalar^2) (branches.card:ℝ)]
  rw [Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨heY,heB⟩ := surviving_extracted_scales F hF jF (actualCuspColumn D0 s hc u m)
    nset bset Y B (fun n h => ⟨(hn n h).1.2,(hn n h).2⟩) hb e he
  rw [heY,heB]
  have hee := hshape Z hZ F jF e m T QK QP Qn Qb (Real.exp (M 2/2+M 3)) C ε hT hQK hQP hQn hQb hC.le
  dsimp only at hee
  rw [hsX,hsY,hsB,hsL]
  convert hee using 1 ; ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1531

/- Original source: OAI/NumberTheory/DirichletL/Reflection/CanonicalPool.lean; sha256: 5c97ff635c2a0332fee7f02ee0efb42efda059bc645066ce87aa19c1b829d7b1 -/
section Source1532
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def canonicalFrozenFamily (I Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6) :
    PrimeFamily (FreeReflection.reflectionActivePool I Q Q₀ e) where
  ideal P := P.val
  maximal P := FreeReflection.pool_maximal I Q Q₀
    ⟨P.val,FreeReflection.reflectionActivePool_subset I Q Q₀ e P.property⟩
  good P := FreeReflection.pool_good I Q Q₀
    ⟨P.val,FreeReflection.reflectionActivePool_subset I Q Q₀ e P.property⟩

def canonicalFrozenExponent (I F Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool I Q Q₀ e) : ℕ := completedLocalExponent I F P.val

lemma canonicalFrozenExponent_lt (I F Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool I Q Q₀ e) : canonicalFrozenExponent I F Q Q₀ e P<6 :=
  Nat.mod_lt _ (by norm_num)

lemma canonicalFrozenFamily_pairwise (I Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6) :
    Pairwise (Function.onFun IsCoprime (canonicalFrozenFamily I Q Q₀ e).ideal) := by
  intro P R hPR
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPR)

lemma canonicalFrozenFamily_odd (I Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool I Q Q₀ e) :
    ringChar (Eis⧸(canonicalFrozenFamily I Q Q₀ e).ideal P)≠2 :=
  FreeReflection.pool_odd I Q Q₀ ⟨P.val,FreeReflection.reflectionActivePool_subset I Q Q₀ e P.property⟩

lemma maximal_coprime_of_not_dvd (P J : Ideal Eis) [P.IsMaximal] (h : ¬P∣J) : IsCoprime P J := by
  rw [Ideal.isCoprime_iff_codisjoint]
  apply ((Ideal.isMaximal_def.mp (inferInstance : P.IsMaximal)).not_le_iff_codisjoint).mp
  exact fun hle => h (Ideal.dvd_iff_le.mpr hle)

lemma canonicalFrozenFamily_row_coprime (I Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool I Q Q₀ e) :
    IsCoprime ((canonicalFrozenFamily I Q Q₀ e).ideal P) (rowResidualPart I Q) :=
  maximal_coprime_of_not_dvd _ _ (FreeReflection.pool_nonresidual I Q Q₀
    ⟨P.val,FreeReflection.reflectionActivePool_subset I Q Q₀ e P.property⟩)

lemma canonicalFrozenFamily_level_coprime (I Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool I Q Q₀ e) :
    IsCoprime Q₀ ((canonicalFrozenFamily I Q Q₀ e).ideal P) := by
  apply (maximal_coprime_of_not_dvd _ _ ?_).symm
  intro hd
  exact FreeReflection.pool_free I Q Q₀
    ⟨P.val,FreeReflection.reflectionActivePool_subset I Q Q₀ e P.property⟩ (Ideal.dvd_iff_le.mp hd)

theorem canonicalFrozenExponent_on_fiber (R I F Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (e : FreeReflection.pool R Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool R Q Q₀ e) :
    completedLocalExponent I F ((canonicalFrozenFamily R Q Q₀ e).ideal P)=
      canonicalFrozenExponent R F Q Q₀ e P := by
  exact CanonicalRowCompletion.nonresidualPoolEquiv_exponent R I F Q Q₀ hR hI hQ hpow hmask
    ⟨P.val,FreeReflection.reflectionActivePool_subset R Q Q₀ e P.property⟩

lemma canonicalFrozenFamily_row_coprime_on_fiber (R I Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (e : FreeReflection.pool R Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool R Q Q₀ e) :
    IsCoprime ((canonicalFrozenFamily R Q Q₀ e).ideal P) (rowResidualPart I Q) := by
  apply maximal_coprime_of_not_dvd
  exact FreeReflection.pool_nonresidual I Q Q₀
    (CanonicalRowCompletion.nonresidualPoolEquiv R I Q Q₀ hR hI hQ hpow hmask
      ⟨P.val,FreeReflection.reflectionActivePool_subset R Q Q₀ e P.property⟩)

lemma canonicalFrozenFamily_extracted (I F Q Q₀ : Ideal Eis) (e : FreeReflection.pool I Q Q₀→Fin 6)
    (v : Fin 3) :
    frozenExtracted (canonicalFrozenFamily I Q Q₀ e) (canonicalFrozenExponent I F Q Q₀ e)
      (FreeReflection.reflectionActiveLabel I Q Q₀ e) v =
    reflectionExtractedDivisor (fun P : FreeReflection.reflectionActivePool I Q Q₀ e => P.val)
      (fun P => completedLocalExponent I F P.val) (FreeReflection.reflectionActiveLabel I Q Q₀ e) v := by
  rw [frozenExtracted_eq_ideal]
  rfl

lemma canonicalFrozenFamily_divides_on_fiber (J I Q Q₀ : Ideal Eis)
    (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (e : FreeReflection.pool J Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool J Q Q₀ e) :
    (canonicalFrozenFamily J Q Q₀ e).ideal P ∣ I*Q :=
  FreeReflection.pool_divides I Q Q₀ hI hQ
    (CanonicalRowCompletion.nonresidualPoolEquiv J I Q Q₀ hJ hI hQ hpow hmask
      ⟨P.val,FreeReflection.reflectionActivePool_subset J Q Q₀ e P.property⟩)

lemma canonicalFrozenFamily_nonresidual_on_fiber (J I Q Q₀ : Ideal Eis)
    (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (e : FreeReflection.pool J Q Q₀→Fin 6)
    (P : FreeReflection.reflectionActivePool J Q Q₀ e) :
    ¬(canonicalFrozenFamily J Q Q₀ e).ideal P ∣ rowResidualPart I Q :=
  FreeReflection.pool_nonresidual I Q Q₀
    (CanonicalRowCompletion.nonresidualPoolEquiv J I Q Q₀ hJ hI hQ hpow hmask
      ⟨P.val,FreeReflection.reflectionActivePool_subset J Q Q₀ e P.property⟩)

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1532

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedRow.lean; sha256: 785580c9c70c49651db15a4d2a95eb8d609315deef20330571a0708dd665911d -/
section Source1533
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem markedCompletedT_twist_congr_primary (Ψ Φ : Eis→*ℂ)
    (h : ∀ n : Eis, λ₀^2∣n-1 → Ψ n=Φ n) (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) :
    markedCompletedT Ψ W X d=markedCompletedT Φ W X d := by
  unfold markedCompletedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [summand,summand,columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]

theorem actual_marked_row_fixed_factor {m f z : Eis} (D : GoodMaskRowData m f z)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hmLam : λ₀∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) :
    markedCompletedT (rowTwist Ψ m f z) W X d=
      markedCompletedT (D.fixedFactor Ψ Q*freePrimeRow D.movingIdeal D.movingSupported
        (Q*Ideal.span {(72:Eis)})) W X d :=
by
  apply markedCompletedT_twist_congr_primary
  intro n hn
  exact D.row_primary Ψ Q hmLam hm2 n hn

def freePrimeFamily (I Q : Ideal Eis) (hI : Supported I) : PrimeFamily (FreePrimeIndex I Q) where
  ideal P := P.val.val
  maximal _P := inferInstance
  good P := (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

def markedSumSlots {ι σ : Type*} [Fintype ι] [Fintype σ] : Finset (ι⊕σ) :=
  Finset.univ.filter (fun x => x.isRight)

lemma actual_sextic_power_congr (P Q : Ideal Eis) [P.IsMaximal] [Q.IsMaximal]
    (hP : λ₀∉P) (hQ : λ₀∉Q) (hPQ : P=Q) (j : ℕ) (n : Eis) :
    (actualSextic P hP^j) (Ideal.Quotient.mk P n)=
      (actualSextic Q hQ^j) (Ideal.Quotient.mk Q n) := by
  subst Q
  rfl

lemma unmarked_sum_twist {ι σ : Type*} [Fintype ι] [Fintype σ]
    (G : PrimeFamily ι) (S : PrimeFamily σ) (j : ι→ℕ) (n : Eis) :
    unmarkedSexticTwist (G.sum S).generator (G.sum S).generator_good
      (Sum.elim j (fun _ => 0)) markedSumSlots n =
    ∏ i, (actualSextic (G.ideal i) (G.good i)^j i) (Ideal.Quotient.mk _ n) := by
  let : DecidableEq (ι⊕σ) := Classical.decEq _
  have hset : (Finset.univ : Finset (ι⊕σ))\markedSumSlots = Finset.univ.filter (fun x => x.isLeft) := by
    ext x
    cases x <;> simp [markedSumSlots]
  unfold unmarkedSexticTwist
  change (∏ i∈Finset.univ\markedSumSlots, _) = _
  rw [hset,Finset.prod_filter,Fintype.prod_sum_type]
  simp only [Sum.isLeft_inl,Sum.isLeft_inr,Bool.false_eq_true,ite_false,ite_true,
    Finset.prod_const_one,mul_one,Sum.elim_inl]
  apply Finset.prod_congr rfl
  intro i hi
  exact actual_sextic_power_congr _ _ ((G.sum S).generator_good (Sum.inl i)) (G.good i)
    ((G.sum S).generator_span (Sum.inl i)) (j i) n

theorem free_row_eq_joined_unmarked {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : Supported I) (S : PrimeFamily σ) :
    freePrimeRow I hI Q =
      unmarkedSexticTwist ((freePrimeFamily I Q hI).sum S).generator
        ((freePrimeFamily I Q hI).sum S).generator_good
        (Sum.elim (fun P : FreePrimeIndex I Q => (UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6)
          (fun _ => 0)) markedSumSlots := by
  ext n
  rw [unmarked_sum_twist]
  rfl

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1533

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedOverlap.lean; sha256: 09ae8db976ce39b9c88535351b78760dc47d45beefa6be54a01a90082e674b26 -/
section Source1534
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma freePrimeRow_zero_at_prime (I Q : Ideal Eis) (hI : Supported I)
    (P : FreePrimeIndex I Q) (n : Eis) (hn : n∈P.val.val) : freePrimeRow I hI Q n=0 := by
  unfold freePrimeRow
  change (∏ p : FreePrimeIndex I Q, _)=0
  apply Finset.prod_eq_zero (Finset.mem_univ P)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hn,MulChar.map_zero]

lemma primaryGenerator_mem_of_ideal_dvd (P A : Ideal Eis) (hPA : P∣A) : primaryGenerator A∈P := by
  by_cases hz : primaryGenerator A=0
  · rw [hz]
    exact Ideal.zero_mem _
  have ha0 : primaryGenerator A∈Ideal.span {primaryGenerator A} := Ideal.subset_span (by simp)
  have ha : primaryGenerator A∈A := ((primaryGenerator_spec A hz).1.le) ha0
  exact (Ideal.dvd_iff_le.mp hPA) ha

lemma free_row_whole_mark_overlap {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : Supported I) (S : PrimeFamily σ)
    (P : FreePrimeIndex I Q) (i : σ) (heq : S.ideal i=P.val.val) (A : Ideal Eis) :
    freePrimeRow I hI Q (primaryGenerator A)*
      (∏ j, if S.ideal j∣A then (1:ℂ) else 0)=0 := by
  by_cases hd : S.ideal i∣A
  · have hn := primaryGenerator_mem_of_ideal_dvd (S.ideal i) A hd
    rw [heq] at hn
    rw [freePrimeRow_zero_at_prime I Q hI P _ hn,zero_mul]
  · have hz : (∏ j, if S.ideal j∣A then (1:ℂ) else 0)=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [ite_eq_right hd]
    rw [hz,mul_zero]

theorem markedCompletedT_free_overlap_zero {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : Supported I) (S : PrimeFamily σ)
    (P : FreePrimeIndex I Q) (i : σ) (heq : S.ideal i=P.val.val)
    (φ : Eis→*ℂ) (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (φ*freePrimeRow I hI Q) W X
      (fun A => ∏ j, if S.ideal j∣A then (1:ℂ) else 0)=0 := by
  unfold markedCompletedT
  calc
    _ = ∑' n : Ideal Eis, ∑' b : Ideal Eis, (0:ℂ) := by
      apply tsum_congr
      intro n
      apply tsum_congr
      intro b
      rw [mul_comm φ (freePrimeRow I hI Q),summand_mul_fixed_twist]
      have hgen : primaryGenerator (n*b^3)=primaryGenerator n*(primaryGenerator b)^3 := by
        rw [primaryGenerator_mul,show primaryGenerator (b^3)=primaryGenerator b^3 from map_pow primaryGeneratorHom b 3]
      rw [← hgen]
      have hz := free_row_whole_mark_overlap I Q hI S P i heq (n*b^3)
      calc
        _ = summand φ W X n b*(freePrimeRow I hI Q (primaryGenerator (n*b^3))*
          (∏ j, if S.ideal j∣n*b^3 then (1:ℂ) else 0)) := by ring
        _ = 0 := by rw [hz,mul_zero]
    _ = 0 := by simp

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1534

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedJoined.lean; sha256: 098c16dbe7a1f934c27bc848c9da9fa1c5dadd0ca88e3c209de0e07c1ab0d0a3 -/
section Source1535
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma joined_whole_prime_mark {ι σ : Type*} [Fintype ι] [Fintype σ]
    (G : PrimeFamily ι) (S : PrimeFamily σ) (A : Ideal Eis) :
    (∏ i∈(markedSumSlots : Finset (ι⊕σ)),
      if Ideal.span {(G.sum S).generator i}∣A then (1:ℂ) else 0)=
      ∏ i, if S.ideal i∣A then (1:ℂ) else 0 := by
  unfold markedSumSlots
  rw [Finset.prod_filter,Fintype.prod_sum_type]
  simp only [Sum.isRight_inl,Sum.isRight_inr,Bool.false_eq_true,ite_false,ite_true,
    Finset.prod_const_one,one_mul]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(G.sum S).generator_span]
  rfl

theorem actual_marked_row_eq_joined {σ : Type*} [Fintype σ]
    {m f z : Eis} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hmLam : λ₀∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (X : ℝ) :
    let Q₀ := Q*Ideal.span {(72:Eis)}
    let G := (freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S
    let j := Sum.elim
      (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) (fun _ => 0)
    markedCompletedT (rowTwist Ψ m f z) W X (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=
      markedCompletedT (D.fixedFactor Ψ Q*unmarkedSexticTwist G.generator G.generator_good j markedSumSlots)
        W X (fun A => ∏ i∈markedSumSlots, if Ideal.span {G.generator i}∣A then (1:ℂ) else 0) := by
  dsimp only
  rw [actual_marked_row_fixed_factor D Ψ Q hmLam hm2,
    free_row_eq_joined_unmarked D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported S]
  congr 1
  funext A
  exact (joined_whole_prime_mark (freePrimeFamily D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported) S A).symm

lemma joined_free_pairwise {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : Supported I) (S : PrimeFamily σ)
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hdis : ∀ P : FreePrimeIndex I Q, ∀ i, S.ideal i≠P.val.val) :
    Pairwise (Function.onFun IsCoprime ((freePrimeFamily I Q hI).sum S).ideal) := by
  apply PrimeFamily.sum_pairwise (freePrimeFamily I Q hI) S
  · exact freePrimeIndex_pairwise_coprime I Q
  · exact hS
  · intro P i
    exact Ideal.isCoprime_of_isMaximal (hdis P i).symm

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1535

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedSource.lean; sha256: 99d2d9bd49420d7b5f4405ecc984973d458b0a797cf2b5bb4e04a9fd959b383b -/
section Source1536
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι : Type*} (P : PrimeFamily ι)
lemma generator_prime (i : ι) : Prime (P.generator i) :=
  (Ideal.span_singleton_prime (P.generator_ne_zero i)).mp inferInstance

def restrict (A : Finset ι) : PrimeFamily A where
  ideal i := P.ideal i.val
  maximal i := P.maximal i.val
  good i := P.good i.val

lemma restrict_pairwise (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (A : Finset ι) :
    Pairwise (Function.onFun IsCoprime (P.restrict A).ideal) := by
  intro i k hik
  exact hP (fun h => hik (Subtype.ext h))

def activeControlled [Fintype ι]
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (c : Eis) (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (h : Eis⧸Ideal.span {c}) (A : Finset ι) :
    ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode :=
  Classical.choice ((P.restrict A).exists_controlled N (G h).a0 (G h).c0 (G h).mode
    (G h).denominator_ne_zero (hN h) (G h).primary (G h).coprime
    (P.restrict_pairwise hP A) (fun i => hNp i.val))

theorem marked_source [Fintype ι]
    (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        (P.activeControlled hP c G N hN hNp) t).smoothedKernel W X := by
  let Qall := (Q*Ideal.span {∏ i, P.generator i})*Ideal.span {∏ i∈S, P.generator i}
  have hprod : (∏ i, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hmark : (∏ i∈S, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hQall : Qall≠0 := mul_ne_zero (mul_ne_zero hQ
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hprod))
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hmark)
  let call := ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*Qall)
  have hcall : call≠0 := by
    apply ConcretePrimeRowBridge.idealGenerator_ne_zero
    apply mul_ne_zero _ hQall
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  let : Finite (Eis⧸Ideal.span {call}) := ConcreteTraceCRT.finite_quotient_span hcall
  let : Fintype (Eis⧸Ideal.span {call}) := Fintype.ofFinite _
  have hcallQ : Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall := by
    rw [ConcretePrimeRowBridge.span_idealGenerator]
  exact markedCompletedT_fixed_active_strata P.generator P.generator_ne_zero P.generator_prime
    P.generator_primary P.generator_good j S φ hφnorm Q hφperiod c hc hcQ G N hN
    (P.activeControlled hP c G N hN hNp) call hcall hcallQ W hWcompact lo hi hlo hsupp hW X hX
end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1536

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedRestriction.lean; sha256: 490fc94d5cadf83f951b2f2bcc285d632a02f3b95d378110e2de70f831f89641 -/
section Source1537
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι]
def activeMarks (A S : Finset ι) : Finset A := Finset.univ.filter (fun i => i.val∈S)

omit [Fintype ι] in
lemma mem_activeMarks (A S : Finset ι) (i : A) : i∈activeMarks A S ↔ i.val∈S := by
  simp [activeMarks]

omit [Fintype ι] in
lemma mixedPrimeFunction_restrict (P : PrimeFamily ι) (j : ι→ℕ) (A S : Finset ι)
    (i : A) (x : Eis⧸Ideal.span {P.generator i.val}) :
    mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
      (fun i => j i.val) (activeMarks A S) i x =
    mixedPrimeFunction P.generator P.generator_good j S i.val x := by
  simp only [mixedPrimeFunction,mem_activeMarks]
  rfl

omit [Fintype ι] in
lemma localActiveWeight_restrict (P : PrimeFamily ι) (j : ι→ℕ) (A S : Finset ι)
    (v : ∀ i : A, (Eis⧸Ideal.span {P.generator i.val})ˣ) :
    localActiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A v =
    fullLocalFourierWeight (P.restrict A).generator_ne_zero
      (mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
        (fun i => j i.val) (activeMarks A S)) v := by
  unfold localActiveWeight fullLocalFourierWeight
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  funext x
  exact (mixedPrimeFunction_restrict P j A S i x).symm

lemma active_sum_eq_mixed (P : PrimeFamily ι) (j : ι→ℕ) (S : Finset ι)
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (c : Eis) (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (h : Eis⧸Ideal.span {c}) (A : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    (∑ v : ∀ i : A, (Eis⧸Ideal.span {P.generator i.val})ˣ,
      localActiveWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) A v *
      (activeStratumDatum P.generator P.generator_ne_zero P.generator_primary
        (P.activeControlled hP c G N hN hNp h) (hN h) (G h).denominator_ne_zero
        (G h).primary (G h).shape A v).smoothedKernel W X)=
    mixedSmoothedValue (P.activeControlled hP c G N hN hNp h A) (hN h)
      (P.restrict A).generator_product_primary (G h).primary (G h).shape
      (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
      (fun i => j i.val) (activeMarks A S) W X := by
  unfold mixedSmoothedValue
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  rw [localActiveWeight_restrict]
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1537

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedInactive.lean; sha256: f0d60feddeb48bb87adc943f197ff500d0c871fad7ecd154166efdce5e1d0ca8 -/
section Source1538
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma mixed_inactive_coefficient (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (i : ι) :
    finiteAdditiveFourierCoeff (quotientTrace (P.generator i) (P.generator_ne_zero i))
      (mixedPrimeFunction P.generator P.generator_good j S i) 0 =
    if i∈S then (Ideal.absNorm (P.ideal i):ℂ)⁻¹
      else if j i=0 then 1-(Ideal.absNorm (P.ideal i):ℂ)⁻¹ else 0 := by
  change finiteAdditiveFourierCoeff (quotientTrace (P.generator i) (P.generator_ne_zero i))
    (fun x => if i∈S then zeroMark x else (actualSextic (Ideal.span {P.generator i}) (P.generator_good i)^j i) x) 0 = _
  by_cases hi : i∈S
  · simp only [hi,ite_true,zeroMark,finiteAdditiveFourierCoeff_zero_delta]
    have hcard : Fintype.card (Eis⧸Ideal.span {P.generator i})=Ideal.absNorm (P.ideal i) := by
      rw [← P.generator_span i,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    rw [hcard]
  · simp only [hi,ite_false]
    have ho : ringChar (Eis⧸Ideal.span {P.generator i})≠2 := by
      rw [P.generator_span]
      exact hodd i
    rw [prime_zeroFourier_norm_formula (P.generator i) (P.generator_ne_zero i)
      (P.generator_good i) ho (j i) (hj i),P.generator_span]

lemma mixed_inactive_weight (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S A : Finset ι) :
    localInactiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A =
    ∏ i∈(Finset.univ:Finset ι)\A,
      if i∈S then (Ideal.absNorm (P.ideal i):ℂ)⁻¹
        else if j i=0 then 1-(Ideal.absNorm (P.ideal i):ℂ)⁻¹ else 0 := by
  unfold localInactiveWeight
  apply Finset.prod_congr rfl
  intro i hi
  exact mixed_inactive_coefficient P hodd j hj S i

lemma mixed_inactive_zero_of_omitted (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S A : Finset ι) (i : ι) (hi : i∉S) (hji : j i≠0) (hiA : i∉A) :
    localInactiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A=0 := by
  rw [mixed_inactive_weight P hodd j hj]
  apply Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,hiA⟩)
  simp only [hi,hji,ite_false]

lemma mixed_inactive_nonzero_requires (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S A : Finset ι)
    (h : localInactiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A≠0) :
    ∀ i, i∉S → j i≠0 → i∈A := by
  intro i hi hji
  by_contra hiA
  exact h (mixed_inactive_zero_of_omitted P hodd j hj S A i hi hji hiA)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1538

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedActiveSets.lean; sha256: bd660fc8b02a1ca96603b6d6c266313ef3bb60347cd84f63de040b6a7fdf3953 -/
section Source1539
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CanonicalRowCompletion
noncomputable section
variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype σ]

def joinedFiberEquiv (e : α⊕β≃γ) : α⊕(β⊕σ)≃γ⊕σ :=
  (Equiv.sumAssoc α β σ).symm.trans (Equiv.sumCongr e (Equiv.refl σ))

def markedActiveSet (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) : Finset (γ⊕σ) :=
  residualActivePrimes (joinedFiberEquiv (σ:=σ) e) ∪
    (B.disjSum T).image (fun x => joinedFiberEquiv e (Sum.inr x))

lemma inactive_product_disjSum (z : β⊕σ→ℂ) (B : Finset β) (T : Finset σ) :
    (∏ x∈(Finset.univ:Finset (β⊕σ))\B.disjSum T,z x)=
    (∏ b∈(Finset.univ:Finset β)\B,z (Sum.inl b))*
    ∏ t∈(Finset.univ:Finset σ)\T,z (Sum.inr t) := by
  have hs : (Finset.univ:Finset (β⊕σ))\B.disjSum T=
      ((Finset.univ:Finset β)\B).disjSum ((Finset.univ:Finset σ)\T) := by
    ext x
    cases x <;> simp
  rw [hs,Finset.prod_disjSum]

theorem inactive_weight_three_blocks (e : α⊕β≃γ) (z : γ⊕σ→ℂ)
    (hz : ∀ a, z (Sum.inl (e (Sum.inl a)))=0) (F : Finset (γ⊕σ)→ℂ) :
    (∑ A : Finset (γ⊕σ), (∏ x∈(Finset.univ:Finset (γ⊕σ))\A,z x)*F A)=
    ∑ B : Finset β, ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset β)\B,z (Sum.inl (e (Sum.inr b))))*
        ∏ t∈(Finset.univ:Finset σ)\T,z (Sum.inr t))*F (markedActiveSet e B T) := by
  have he := inactive_weight_nonresidual_subsets (joinedFiberEquiv e) z hz F
  refine Eq.trans ?_ (Eq.trans he ?_)
  · apply Finset.sum_congr (by ext A; simp only [Finset.mem_univ])
    intro A hA
    congr 1
    apply Finset.prod_congr (by ext x; simp only [Finset.mem_sdiff,Finset.mem_univ])
    intro x hx
    rfl
  · rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv Finset.sumEquiv.toEquiv
    intro B
    have hB : B=B.toLeft.disjSum B.toRight := (Finset.toLeft_disjSum_toRight).symm
    conv_lhs => rw [hB]
    congr 1
    · refine Eq.trans ?_ (inactive_product_disjSum (fun x => z (joinedFiberEquiv e (Sum.inr x))) B.toLeft B.toRight)
      apply Finset.prod_congr (by ext x; simp only [Finset.mem_sdiff,Finset.mem_univ])
      intro x hx
      rfl
    · apply congrArg F
      ext x
      simp only [markedActiveSet,Finset.sumEquiv,Equiv.coe_fn_mk,Finset.mem_union,Finset.mem_image]
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1539

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedActualSource.lean; sha256: 2158670d117e58e507bc4f39461b47033fbf37f376db208efe6db15e82a89a8a -/
section Source1540
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

abbrev markedRowFamily {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis) :=
  (freePrimeFamily D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported).sum S

def markedRowExponent {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (Q : Ideal Eis) :
    FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}) ⊕ σ → ℕ :=
  Sum.elim (fun P => (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
    (fun _ => 0)

theorem actual_marked_row_overlap_zero {σ : Type*} [Fintype σ]
    {m f z : Eis} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hmLam : λ₀∣m) (hm2 : (2:Eis)∣m)
    (P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})) (i : σ)
    (hPi : S.ideal i=P.val.val) (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=0 := by
  rw [actual_marked_row_fixed_factor D Ψ Q hmLam hm2]
  exact markedCompletedT_free_overlap_zero D.movingIdeal (Q*Ideal.span {(72:Eis)})
    D.movingSupported S P i hPi (D.fixedFactor Ψ Q) W X

def markedCuspSource {ι : Type*} [Fintype ι] (P : PrimeFamily ι)
    (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i)) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  thetaDerivativeScalar⁻¹*∑ t : FixedActiveCuspIndex c P.generator,
    fixedActiveFunctionWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
    (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
      (P.activeControlled hP c G N hN hNp) t).smoothedKernel W X

theorem actual_marked_row_source {σ : Type*} [Fintype σ]
    {m f z : Eis} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hQ : Q≠0)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm : ∀ n, ‖Ψ n‖≤1)
    (hmLam : λ₀∣m) (hm2 : (2:Eis)∣m)
    (hdis : ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}), ∀ i, S.ideal i≠P.val.val)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((markedRowFamily D S Q).ideal i))
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=
    markedCuspSource (markedRowFamily D S Q)
      (joined_free_pairwise D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported S hS hdis)
      (markedRowExponent D Q) markedSumSlots (D.fixedFactor Ψ Q) c hc G N hN hNp W X := by
  have hQ0 : Q*Ideal.span {(72:Eis)}≠0 := by
    apply mul_ne_zero hQ
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  exact (actual_marked_row_eq_joined D S Ψ Q hmLam hm2 W X).trans
    ((markedRowFamily D S Q).marked_source
      (joined_free_pairwise D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported S hS hdis)
      (markedRowExponent D Q) markedSumSlots (D.fixedFactor Ψ Q) (D.fixedFactor_norm Ψ Q hΨnorm)
      (Q*Ideal.span {(72:Eis)}) hQ0 (D.fixedFactor_periodic Ψ Q hΨ) c hc hcQ G N hN hNp
      W hWcompact lo hi hlo hsupp hW X hX)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1540

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedLevel.lean; sha256: 88b690307ece498acc1d940a1bd19dd367081fb3b08192eed6531c4bccc96ecb -/
section Source1541
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma PrimeFamily.level_coprime {ι : Type*} (P : PrimeFamily ι)
    (Q : Ideal Eis) (c : Eis) (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*Q)
    (hQ : ∀ i, IsCoprime Q (P.ideal i)) (i : ι) :
    IsCoprime (Ideal.span {(9:Eis)*c}) (P.ideal i) := by
  have h9 : IsCoprime (Ideal.span {(9:Eis)}) (P.ideal i) := by
    rw [← P.generator_span i]
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (ShortDraftCRT.primary_coprime_nine _ (P.generator_primary i)).symm
  rw [← Ideal.span_singleton_mul_span_singleton,hcQ]
  exact h9.mul_left (h9.mul_left (hQ i))

lemma markedRowFamily_period {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis)
    (hS : ∀ i, IsCoprime (Q*Ideal.span {(72:Eis)}) (S.ideal i))
    (c : Eis) (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)})) :
    ∀ i, IsCoprime (Ideal.span {(9:Eis)*c}) ((markedRowFamily D S Q).ideal i) := by
  apply PrimeFamily.level_coprime _ _ _ hcQ
  intro i
  cases i with
  | inl P => exact freePrimeIndex_coprime _ _ P
  | inr i => exact hS i

lemma markedRowFamily_odd {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis)
    (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2) :
    ∀ i, ringChar (Eis⧸(markedRowFamily D S Q).ideal i)≠2 := by
  intro i
  cases i with
  | inl P => exact (supported_factors_good D.movingIdeal D.movingSupported P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.2
  | inr i => exact hS i

lemma markedRowExponent_lt {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (Q : Ideal Eis) :
    ∀ i : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})⊕σ, markedRowExponent D Q i<6 := by
  intro i
  cases i with
  | inl P => exact Nat.mod_lt _ (by norm_num)
  | inr i => norm_num [markedRowExponent]
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1541

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedFiber.lean; sha256: 55b5399c3106ad00b10be3e26e310d700fde471498dc9f7cda568c2178ea0de5 -/
section Source1542
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [Fintype ι] [Fintype σ]

def joinedInactiveCoefficient (P : PrimeFamily ι) (S : PrimeFamily σ) (j : ι→ℕ) : ι⊕σ→ℂ :=
  Sum.elim (fun i => if j i=0 then 1-(Ideal.absNorm (P.ideal i):ℂ)⁻¹ else 0)
    (fun i => (Ideal.absNorm (S.ideal i):ℂ)⁻¹)

lemma joined_inactive_weight (P : PrimeFamily ι) (S : PrimeFamily σ)
    (hP : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (j : ι→ℕ) (hj : ∀ i, j i<6) (A : Finset (ι⊕σ)) :
    localInactiveWeight (P.sum S).generator (P.sum S).generator_ne_zero
      (mixedPrimeFunction (P.sum S).generator (P.sum S).generator_good
        (Sum.elim j (fun _ => 0)) markedSumSlots) A =
    ∏ i∈(Finset.univ:Finset (ι⊕σ))\A, joinedInactiveCoefficient P S j i := by
  have ho : ∀ i, ringChar (Eis⧸(P.sum S).ideal i)≠2 := by
    intro i
    cases i with
    | inl i => exact hP i
    | inr i => exact hS i
  have hj' : ∀ i : ι⊕σ, Sum.elim j (fun _ => 0) i<6 := by
    intro i
    cases i with
    | inl i => exact hj i
    | inr i => norm_num
  rw [mixed_inactive_weight (P.sum S) ho _ hj']
  apply Finset.prod_congr (by ext i; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro i hi
  cases i <;> simp [markedSumSlots,joinedInactiveCoefficient,PrimeFamily.sum]
  rfl

theorem joined_inactive_three_blocks {α β : Type*} [Fintype α] [Fintype β]
    (P : PrimeFamily ι) (S : PrimeFamily σ)
    (hP : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (j : ι→ℕ) (hj : ∀ i, j i<6) (e : α⊕β≃ι) (he : ∀ a, j (e (Sum.inl a))=1)
    (F : Finset (ι⊕σ)→ℂ) :
    (∑ A : Finset (ι⊕σ),
      localInactiveWeight (P.sum S).generator (P.sum S).generator_ne_zero
        (mixedPrimeFunction (P.sum S).generator (P.sum S).generator_good
          (Sum.elim j (fun _ => 0)) markedSumSlots) A * F A)=
    ∑ B : Finset β, ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset β)\B,
        if j (e (Sum.inr b))=0 then 1-(Ideal.absNorm (P.ideal (e (Sum.inr b))):ℂ)⁻¹ else 0)*
        ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*F (markedActiveSet e B T) := by
  have hz : ∀ a, joinedInactiveCoefficient P S j (Sum.inl (e (Sum.inl a)))=0 := by
    intro a
    simp [joinedInactiveCoefficient,he a]
  have h := inactive_weight_three_blocks e (joinedInactiveCoefficient P S j) hz F
  refine Eq.trans ?_ h
  apply Finset.sum_congr (by ext A; simp only [Finset.mem_univ])
  intro A hA
  congr 1
  exact joined_inactive_weight P S hP hS j hj A
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1542

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalFiber.lean; sha256: 13c5c00fded57a47aef4396b7d9285de457fee7453edca9e2890ab3696ca5c91 -/
section Source1543
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask

theorem original_fiber_inactive_sum (S : PrimeFamily σ)
    (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (H : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ)→ℂ) :
    (∑ A : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ),
      localInactiveWeight ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator
        ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator_ne_zero
        (mixedPrimeFunction ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator
          ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator_good
          (Sum.elim (fun P => (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
            (fun _ => 0)) markedSumSlots) A * H A)=
    ∑ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀), ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀))\B,
        if completedLocalExponent R F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0)*
        ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*H (markedActiveSet E B T) := by
  have hodd : ∀ P : FreePrimeIndex D.movingIdeal Q₀,
      ringChar (Eis⧸(freePrimeFamily D.movingIdeal Q₀ D.movingSupported).ideal P)≠2 := by
    intro P
    exact (supported_factors_good D.movingIdeal D.movingSupported P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.2
  have hres : ∀ a, (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count
      (E (Sum.inl a)).val.val%6=1 := by
    intro a
    exact D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
  have he := joined_inactive_three_blocks (freePrimeFamily D.movingIdeal Q₀ D.movingSupported)
    S hodd hS (fun P => (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
    (fun _ => Nat.mod_lt _ (by norm_num)) E hres H
  refine he.trans ?_
  apply Finset.sum_congr (by ext B; simp only [Finset.mem_univ])
  intro B hB
  apply Finset.sum_congr (by ext T; simp only [Finset.mem_univ])
  intro T hT
  congr 2
  apply Finset.prod_congr (by ext b; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro b hb
  rw [D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)]
  change (if completedLocalExponent R F b.val=0 then
    1-(Ideal.absNorm (E (Sum.inr b)).val.val:ℂ)⁻¹ else 0)=_
  rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)]
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1543

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ActiveDictionary.lean; sha256: d54de412a18c4b0b2407989b37fbe6ed49a35c09ece14bf3983fae4e89e1d57a -/
section Source1544
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CanonicalRowCompletion
noncomputable section
variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype σ]

def disjSumIndexEquiv (B : Finset β) (T : Finset σ) : B⊕T≃B.disjSum T where
  toFun x := match x with
    | Sum.inl b => ⟨Sum.inl b.val,by simp⟩
    | Sum.inr t => ⟨Sum.inr t.val,by simp⟩
  invFun x := match x with
    | ⟨Sum.inl b,hb⟩ => Sum.inl ⟨b,by simpa using hb⟩
    | ⟨Sum.inr t,ht⟩ => Sum.inr ⟨t,by simpa using ht⟩
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨x,hx⟩; cases x <;> rfl

omit [Fintype β] [Fintype σ] in
lemma complete_marked_set (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) :
    completeActiveSet (joinedFiberEquiv e) (B.disjSum T)=markedActiveSet e B T := by
  ext x
  simp only [completeActiveSet,markedActiveSet,Finset.mem_union,Finset.mem_image]

def markedActiveEquiv (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) :
    B⊕(α⊕T)≃markedActiveSet e B T :=
  (((((Equiv.sumAssoc B α T).symm.trans
    (Equiv.sumCongr (Equiv.sumComm B α) (Equiv.refl T))).trans (Equiv.sumAssoc α B T)).trans
    (Equiv.sumCongr (Equiv.refl α) (disjSumIndexEquiv B T))).trans
    (selectedActiveEquiv (joinedFiberEquiv e) (B.disjSum T))).trans
    (Equiv.subtypeEquivRight (fun x => by rw [complete_marked_set e B T]))

lemma markedActiveEquiv_frozen (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (b : B) :
    (markedActiveEquiv e B T (Sum.inl b)).val=Sum.inl (e (Sum.inr b.val)) := rfl
lemma markedActiveEquiv_residual (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (a : α) :
    (markedActiveEquiv e B T (Sum.inr (Sum.inl a))).val=Sum.inl (e (Sum.inl a)) := rfl
lemma markedActiveEquiv_slot (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (t : T) :
    (markedActiveEquiv e B T (Sum.inr (Sum.inr t))).val=Sum.inr t.val := rfl
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1544

/- Original source: OAI/NumberTheory/DirichletL/Reflection/Reindex.lean; sha256: 138ffe0c6131e65f65a876df572a9fd3eeba79ea7a91374b7961c2423cb8183f -/
section Source1545
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators MatrixGroups
open ActualEisensteinCubic CubicEisenstein CompletedGauss CubicJacobiGlobal FiniteGaussPhase ShortDraftCRT
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma cofactor_reindex (p : ι→Eis) (e : κ≃ι) (k : κ) :
    cofactor (fun k => p (e k)) k=cofactor p (e k) := by
  unfold cofactor
  apply Finset.prod_equiv e
  · intro i
    simp only [Finset.mem_erase,Finset.mem_univ,and_true,ne_eq,EmbeddingLike.apply_eq_iff_eq]
  · intro i hi
    rfl

lemma finiteCrossNumerator_reindex (a c l : Eis) (p : ι→Eis) (e : κ≃ι) (h : ι→Eis) :
    finiteCrossNumerator a c l (fun k => p (e k)) (fun k => h (e k))=
      finiteCrossNumerator a c l p h := by
  unfold finiteCrossNumerator
  simp_rw [cofactor_reindex]
  rw [e.prod_comp,e.sum_comp (fun i => h i*cofactor p i)]

def unitFrequencyEquiv (p : ι→Eis) (e : κ≃ι) :
    (∀ k, (Eis⧸Ideal.span {p (e k)})ˣ)≃(∀ i, (Eis⧸Ideal.span {p i})ˣ) :=
  Equiv.piCongrLeft (fun i => (Eis⧸Ideal.span {p i})ˣ) e

omit [Fintype ι] [Fintype κ] in
lemma unitFrequencyEquiv_apply (p : ι→Eis) (e : κ≃ι)
    (v : ∀ k, (Eis⧸Ideal.span {p (e k)})ˣ) (k : κ) :
    unitFrequencyEquiv p e v (e k)=v k := Equiv.piCongrLeft_apply_apply _ _ _ _

omit [Fintype ι] [Fintype κ] in
lemma unitFrequencyEquiv_one (p : ι→Eis) (e : κ≃ι) :
    unitFrequencyEquiv p e (fun _ => 1)=(fun _ => 1) := by
  funext i
  obtain ⟨k,rfl⟩ := e.surjective i
  exact unitFrequencyEquiv_apply p e _ k

def reindexControlled {p : ι→Eis} {N a c : Eis} {mode : Bool}
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    ControlledStratumArithmetic (fun k => p (e k)) N a c mode where
  lift v k := D.lift (unitFrequencyEquiv p e v) (e k)
  lift_period v k := D.lift_period _ _
  lift_residue v k := (D.lift_residue _ _).trans (congrArg Units.val (unitFrequencyEquiv_apply p e v k))
  U := D.U
  w := D.w
  bezout := by simpa only [e.prod_comp] using D.bezout
  sigma k := D.sigma (e k)
  epsilon k := D.epsilon (e k)
  sigma_value k := by simpa only [cofactor_reindex] using D.sigma_value (e k)
  epsilon_value k := by simpa only [cofactor_reindex] using D.epsilon_value (e k)
  matrix v := D.matrix (unitFrequencyEquiv p e v)
  numerator v := by
    rw [D.numerator,finiteCrossNumerator_reindex]
  denominator v := by simpa only [e.prod_comp] using D.denominator (unitFrequencyEquiv p e v)
  matrix_fixed v i j := by
    simpa only [unitFrequencyEquiv_one] using D.matrix_fixed (unitFrequencyEquiv p e v) i j
  conditions v := D.conditions (unitFrequencyEquiv p e v)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1545

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ReindexReflection.lean; sha256: c4f63495ee5b1b52c3c2a193e9a71ffa59f895fa251b7e3356d259d542e4f80a -/
section Source1546
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→Eis} {N a c : Eis} {mode : Bool}

lemma reindexControlled_matrix_one (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).matrix (fun _ => 1)=D.matrix (fun _ => 1) := by
  change D.matrix (unitFrequencyEquiv p e (fun _ => 1))=_
  rw [unitFrequencyEquiv_one]

lemma reindexControlled_fixedFactor (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).fixedFactor=D.fixedFactor := by
  unfold ControlledStratumArithmetic.fixedFactor
  rw [reindexControlled_matrix_one]

lemma reindexControlled_U (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).U=D.U := rfl

def reindexMarks (e : κ≃ι) (S : Finset ι) : Finset κ := Finset.univ.filter (fun k => e k∈S)

omit [Fintype ι] in
lemma mem_reindexMarks (e : κ≃ι) (S : Finset ι) (k : κ) : k∈reindexMarks e S ↔ e k∈S := by
  simp [reindexMarks]

lemma mixedActiveBracket_reindex [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)
    (hp : ∀ i, p i≠0) (hg : ∀ i, λ₀∉Ideal.span {p i})
    (j : ι→ℕ) (S : Finset ι) (k : κ) (x : Eis) :
    mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
      (reindexMarks e S) (reindexControlled D e) k x =mixedActiveBracket hp hg j S D (e k) x := by
  simp only [mixedActiveBracket,mem_reindexMarks]
  rfl

theorem mixedReflectedValue_reindex [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hc : c≠0) (hg : ∀ i, λ₀∉Ideal.span {p i})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (reindexControlled D e) s (fun k => hp (e k)) hc (fun k => hg (e k))
      (fun k => j (e k)) (reindexMarks e S) W X =mixedReflectedValue D s hp hc hg j S W X := by
  have hprod (x : Eis) :
      (∏ k, mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
        (reindexMarks e S) (reindexControlled D e) k x)=∏ i, mixedActiveBracket hp hg j S D i x := by
    simp_rw [mixedActiveBracket_reindex]
    exact e.prod_comp (fun i => mixedActiveBracket hp hg j S D i x)
  simp only [mixedReflectedValue,e.prod_comp p,reindexControlled_fixedFactor,
    reindexControlled_matrix_one,reindexControlled_U,hprod]
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1546

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalDictionary.lean; sha256: 66550407bdfc122958d237d7932d78db4aa5ef8822e09bf2b5e7a41455b24369 -/
section Source1547
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def poolPrimeFamily (R Q Q₀ : Ideal Eis) : PrimeFamily (FreeReflection.pool R Q Q₀) where
  ideal P := P.val
  maximal P := FreeReflection.pool_maximal R Q Q₀ P
  good P := FreeReflection.pool_good R Q Q₀ P

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad

lemma original_active_family_ideal (S : PrimeFamily σ)
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    (((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).restrict
      (markedActiveSet E B T)).ideal (markedActiveEquiv E B T x)=
    (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).ideal x := by
  cases x with
  | inl b =>
    change (E (Sum.inr b.val)).val.val=b.val.val
    exact D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b.val)
  | inr x => cases x with
    | inl a =>
      change (E (Sum.inl a)).val.val=a.val
      exact D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
    | inr t => rfl

lemma original_active_family_generator (S : PrimeFamily σ)
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    (((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).restrict
      (markedActiveSet E B T)).generator (markedActiveEquiv E B T x)=
    (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator x :=
  congrArg primaryPrime (original_active_family_ideal D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T x)

lemma original_active_exponent
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
      (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) (fun _ : σ => 0)
      (markedActiveEquiv E B T x).val =
    Sum.elim (fun b : B => completedLocalExponent R F b.val.val)
      (Sum.elim (fun _ : PrimeIndex K => 1) (fun _ : T => 0)) x := by
  cases x with
  | inl b => exact D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b.val)
  | inr x => cases x with
    | inl a => exact D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
    | inr t => rfl

lemma original_active_marks
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ) :
    reindexMarks (markedActiveEquiv E B T) (activeMarks (markedActiveSet E B T) markedSumSlots)=
    Finset.univ.filter (fun x : B⊕(PrimeIndex K⊕T) => match x with
      | Sum.inr (Sum.inr _) => True | _ => False) := by
  ext x
  simp only [mem_reindexMarks,mem_activeMarks,Finset.mem_filter,Finset.mem_univ,true_and]
  cases x with
  | inl b => simp [markedActiveEquiv_frozen,markedSumSlots]
  | inr x => cases x with
    | inl a => simp [markedActiveEquiv_residual,markedSumSlots]
    | inr t => simp [markedActiveEquiv_slot,markedSumSlots]
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1547

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalTransport.lean; sha256: 1e35080845e1e6c15cace7958478617b8d33e216b165fe8496d71bc6cba33842 -/
section Source1548
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def castControlled {ι : Type*} [Fintype ι] {p q : ι→Eis} {N a c : Eis} {mode : Bool}
    (h : p=q) (D : ControlledStratumArithmetic p N a c mode) :
    ControlledStratumArithmetic q N a c mode := h ▸ D

lemma mixedReflectedValue_cast {ι : Type*} [Fintype ι] {p q : ι→Eis} {N a c : Eis} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (h : p=q) (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hq : ∀ i, q i≠0) (hc : c≠0)
    (hgp : ∀ i, λ₀∉Ideal.span {p i}) (hgq : ∀ i, λ₀∉Ideal.span {q i})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (castControlled h D) s hq hc hgq j S W X=
      mixedReflectedValue D s hp hc hgp j S W X := by
  subst q
  rfl

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ) (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "PS" => PrimeFamily.restrict (PrimeFamily.sum (freePrimeFamily D.movingIdeal Q₀ D.movingSupported) S) (markedActiveSet E B T)
local notation "PF" => PrimeFamily.reflected (PrimeFamily.restrict (poolPrimeFamily R (Ideal.span (Set.singleton m)*F) Q₀) B) K hK (S.restrict T)
local notation "EA" => markedActiveEquiv E B T

lemma original_active_marks_eq_slots :
    reindexMarks EA (activeMarks (markedActiveSet E B T) markedSumSlots)=slotIndices B (PrimeIndex K) T := by
  rw [original_active_marks D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T]
  ext x
  cases x with
  | inl b => simp [slotIndices]
  | inr x => cases x with
    | inl a => simp [slotIndices]
    | inr t => simp [slotIndices]

def originalCanonicalControlled {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PS).generator N a c mode) :
    ControlledStratumArithmetic (PF).generator N a c mode :=
  castControlled (funext (original_active_family_generator D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T))
    (reindexControlled C EA)

theorem original_reflected_source_eq {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PS).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue C s (PS).generator_ne_zero hc (PS).generator_good
      (fun i => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) i.val) (activeMarks (markedActiveSet E B T) markedSumSlots) W X =
    mixedReflectedValue (originalCanonicalControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T C)
      s (PF).generator_ne_zero hc (PF).generator_good
      (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val)) (slotIndices B (PrimeIndex K) T) W X := by
  rw [← mixedReflectedValue_reindex C EA]
  have hj : (fun x => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) (EA x).val)=
      reflectedExponent (fun b : B => completedLocalExponent R F b.val.val) := by
    funext x
    exact original_active_exponent D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T x
  rw [hj,original_active_marks_eq_slots D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T]
  exact (mixedReflectedValue_cast _ (reindexControlled C EA) s _ (PF).generator_ne_zero hc _ (PF).generator_good _ _ W X).symm
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1548

/- Original source: OAI/NumberTheory/DirichletL/Reflection/Pullback.lean; sha256: 6937c2de55f291f6aac3d6dcf957f254d753b918d4457b68a660344ec2098a35 -/
section Source1549
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→Eis} {q : κ→Eis}
    {N a c : Eis} {mode : Bool}

omit [Fintype ι] [Fintype κ] in
lemma pullback_generator_eq (e : κ≃ι) (h : (fun k => p (e k))=q) :
    (fun i => q (e.symm i))=p := by
  rw [← h]
  simp only [Equiv.apply_symm_apply]

def pullbackControlled (e : κ≃ι) (h : (fun k => p (e k))=q)
    (D : ControlledStratumArithmetic q N a c mode) :
    ControlledStratumArithmetic p N a c mode :=
  castControlled (pullback_generator_eq e h) (reindexControlled D e.symm)

lemma reindexMarks_symm (e : κ≃ι) (S : Finset ι) :
    reindexMarks e.symm (reindexMarks e S)=S := by
  ext i
  simp only [mem_reindexMarks,Equiv.apply_symm_apply]

theorem mixedReflectedValue_pullback
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ k, (Ideal.span {q k}).IsMaximal]
    (e : κ≃ι) (h : (fun k => p (e k))=q)
    (D : ControlledStratumArithmetic q N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hq : ∀ k, q k≠0) (hc : c≠0)
    (hgp : ∀ i, λ₀∉Ideal.span {p i}) (hgq : ∀ k, λ₀∉Ideal.span {q k})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (pullbackControlled e h D) s hp hc hgp j S W X=
      mixedReflectedValue D s hq hc hgq (fun k => j (e k)) (reindexMarks e S) W X := by
  unfold pullbackControlled
  rw [mixedReflectedValue_cast _ _ s (fun i => hq (e.symm i)) hp hc
    (fun i => hgq (e.symm i)) hgp]
  have hj : (fun i => j (e (e.symm i)))=j := by funext i; simp only [Equiv.apply_symm_apply]
  have he := mixedReflectedValue_reindex D e.symm s hq hc hgq
    (fun k => j (e k)) (reindexMarks e S) W X
  rw [hj,reindexMarks_symm] at he
  exact he
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1549

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalChosen.lean; sha256: 9f1c9ed448b3234d77fc619b9a69f8ca792cf1725c3c8583c8bdc3b910e1973b -/
section Source1550
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ) (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "PS" => PrimeFamily.restrict (PrimeFamily.sum (freePrimeFamily D.movingIdeal Q₀ D.movingSupported) S) (markedActiveSet E B T)
local notation "PF" => PrimeFamily.reflected (PrimeFamily.restrict (poolPrimeFamily R (Ideal.span (Set.singleton m)*F) Q₀) B) K hK (S.restrict T)
local notation "EA" => markedActiveEquiv E B T

def originalChosenControlled {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PF).generator N a c mode) :
    ControlledStratumArithmetic (PS).generator N a c mode :=
  pullbackControlled EA
    (funext (original_active_family_generator D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T)) C

theorem original_chosen_reflected_source_eq {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PF).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (originalChosenControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T C)
      s (PS).generator_ne_zero hc (PS).generator_good
      (fun i => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) i.val) (activeMarks (markedActiveSet E B T) markedSumSlots) W X =
    mixedReflectedValue C s (PF).generator_ne_zero hc (PF).generator_good
      (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val)) (slotIndices B (PrimeIndex K) T) W X := by
  unfold originalChosenControlled
  rw [mixedReflectedValue_pullback]
  have hj : (fun x => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) (EA x).val)=
      reflectedExponent (fun b : B => completedLocalExponent R F b.val.val) := by
    funext x
    exact original_active_exponent D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T x
  rw [hj,original_active_marks_eq_slots D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T]
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1550

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedDualSource.lean; sha256: d58263776bbde6b2a45fbfed1e869c9df918489702dea8adf115a05c4c9a74aa -/
section Source1551
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
namespace PrimeFamily
variable {ι : Type*} [Fintype ι] (P : PrimeFamily ι)

lemma fixed_active_sum_eq_mixed
    (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i)) (W : ℝ→ℂ) (X : ℝ) :
    (∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        (P.activeControlled hP c G N hN hNp) t).smoothedKernel W X)=
    ∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedSmoothedValue (P.activeControlled hP c G N hN hNp h A) (hN h)
          (P.restrict A).generator_product_primary (G h).primary (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveFunctionWeight,fixedActiveCuspDatum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro A hA
  rw [← active_sum_eq_mixed P j S hP c G N hN hNp h A W X]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  ring

theorem marked_reflected_source
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedReflectedValue (P.activeControlled hP c G N hN hNp h A) (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  rw [P.marked_source hP j S φ hφnorm Q hQ hφperiod c hc hcQ G N hN hNp
    W hWcompact lo hi hlo hsupp hW X hX,
    P.fixed_active_sum_eq_mixed hP j S φ c hc G N hN hNp W X]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  congr 1
  apply mixed_smoothed_eq_reflected
  · intro i k hik
    change IsCoprime (Ideal.span {P.generator i.val}) (Ideal.span {P.generator k.val})
    rw [P.generator_span,P.generator_span]
    exact hP (fun he => hik (Subtype.ext he))
  · intro i
    rw [P.generator_span]
    exact hodd i.val
  · exact fun i => hj i.val
  · exact hlo
  · exact hsupp
  · exact hW
  · exact hX
end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1551

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedChosenSource.lean; sha256: 699a9e3b3c24ef848cf5c8d3bf844311de9273c2b01320cb9764a7c402d74808 -/
section Source1552
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
namespace PrimeFamily
variable {ι : Type*} (P : PrimeFamily ι)

theorem marked_source_of_controlled [Fintype ι]
    (_hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        C t).smoothedKernel W X := by
  let Qall := (Q*Ideal.span {∏ i, P.generator i})*Ideal.span {∏ i∈S, P.generator i}
  have hprod : (∏ i, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hmark : (∏ i∈S, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hQall : Qall≠0 := mul_ne_zero (mul_ne_zero hQ
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hprod))
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hmark)
  let call := ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*Qall)
  have hcall : call≠0 := by
    apply ConcretePrimeRowBridge.idealGenerator_ne_zero
    apply mul_ne_zero _ hQall
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  let : Finite (Eis⧸Ideal.span {call}) := ConcreteTraceCRT.finite_quotient_span hcall
  let : Fintype (Eis⧸Ideal.span {call}) := Fintype.ofFinite _
  have hcallQ : Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall := by
    rw [ConcretePrimeRowBridge.span_idealGenerator]
  exact markedCompletedT_fixed_active_strata P.generator P.generator_ne_zero P.generator_prime
    P.generator_primary P.generator_good j S φ hφnorm Q hφperiod c hc hcQ G N hN
    C call hcall hcallQ W hWcompact lo hi hlo hsupp hW X hX
end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1552

/- Original source: OAI/NumberTheory/DirichletL/Reflection/MarkedChosenDual.lean; sha256: 99e2e2e7f46b0a99c24201056373286ed3f1f18d1458c09f559386ff3decc4a5 -/
section Source1553
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
namespace PrimeFamily
variable {ι : Type*} [Fintype ι] (P : PrimeFamily ι)

lemma fixed_active_sum_eq_mixed_of_controlled
    (_hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode) (W : ℝ→ℂ) (X : ℝ) :
    (∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        C t).smoothedKernel W X)=
    ∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedSmoothedValue (C h A) (hN h)
          (P.restrict A).generator_product_primary (G h).primary (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveFunctionWeight,fixedActiveCuspDatum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro A hA
  simp only [mixedSmoothedValue,Finset.mul_sum]
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  rw [localActiveWeight_restrict]
  have hw : fullLocalFourierWeight (P.restrict A).generator_ne_zero
      (mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
        (fun i => j i.val) (activeMarks A S)) v =
      fullLocalFourierWeight (fun i : A => P.generator_ne_zero i.val)
        (mixedPrimeFunction (fun i : A => P.generator i.val) (fun i => P.generator_good i.val)
          (fun i => j i.val) (activeMarks A S)) v := rfl
  rw [hw]
  dsimp only [activeStratumDatum]
  ring

theorem marked_reflected_source_of_controlled
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedReflectedValue (C h A) (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  rw [P.marked_source_of_controlled hP j S φ hφnorm Q hQ hφperiod c hc hcQ G N hN C
    W hWcompact lo hi hlo hsupp hW X hX,
    P.fixed_active_sum_eq_mixed_of_controlled hP j S φ c hc G N hN C W X]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  congr 1
  apply mixed_smoothed_eq_reflected
  · intro i k hik
    change IsCoprime (Ideal.span {P.generator i.val}) (Ideal.span {P.generator k.val})
    rw [P.generator_span,P.generator_span]
    exact hP (fun he => hik (Subtype.ext he))
  · intro i
    rw [P.generator_span]
    exact hodd i.val
  · exact fun i => hj i.val
  · exact hlo
  · exact hsupp
  · exact hW
  · exact hX
end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1553

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SourceSelection.lean; sha256: 61f6a6dc8169428a5c19179ea86389fc625e72a79f2269da3d30137b6a7381ae -/
section Source1554
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CanonicalRowCompletion
noncomputable section

def sourceDependentExtension {X Y : Type*} {D : Y→Type*}
    (f : X→Y) (C : ∀ x, D (f x)) (fallback : ∀ y, D y) (y : Y) : D y :=
  if h : ∃ x, f x=y then h.choose_spec ▸ C h.choose else fallback y

lemma sourceDependentExtension_at {X Y : Type*} {D : Y→Type*}
    (f : X→Y) (hinj : Function.Injective f) (C : ∀ x, D (f x))
    (fallback : ∀ y, D y) (x : X) :
    sourceDependentExtension f C fallback (f x)=C x := by
  have h : ∃ z, f z=f x := ⟨x,rfl⟩
  unfold sourceDependentExtension
  rw [dite_eq_left h]
  have he : h.choose=x := hinj h.choose_spec
  have hcast : ∀ (z x : X) (hf : f z=f x), z=x → (hf ▸ C z)=C x := by
    intro z x hf hx
    subst x
    rfl
  exact hcast _ _ h.choose_spec he

variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype σ]

lemma markedActiveSet_injective (e : α⊕β≃γ) :
    Function.Injective (fun q : Finset β×Finset σ => markedActiveSet e q.1 q.2) := by
  intro x y he
  have hh := congrArg (optionalPrimeActive (joinedFiberEquiv e)) he
  dsimp only at hh
  rw [← complete_marked_set,← complete_marked_set,
    optionalPrimeActive_completeActiveSet,optionalPrimeActive_completeActiveSet] at hh
  apply Prod.ext
  · have h := congrArg Finset.toLeft hh
    simpa using h
  · have h := congrArg Finset.toRight hh
    simpa using h

theorem exists_marked_source_selection (e : α⊕β≃γ)
    (D : Finset (γ⊕σ)→Type*) (fallback : ∀ A, D A)
    (C : ∀ B : Finset β, ∀ T : Finset σ, D (markedActiveSet e B T)) :
    ∃ E : ∀ A, D A, ∀ B T, E (markedActiveSet e B T)=C B T := by
  refine ⟨sourceDependentExtension (fun q : Finset β×Finset σ => markedActiveSet e q.1 q.2)
    (fun q => C q.1 q.2) fallback,?_⟩
  intro B T
  exact sourceDependentExtension_at _ (markedActiveSet_injective e) _ _ (B,T)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1554

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SelectedExpansion.lean; sha256: 58cb9c07708eba99ace16f821f322f8e606ca75edca29cd39a98de6239f4c6cb -/
section Source1555
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ)
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "Pall" => PrimeFamily.sum (freePrimeFamily D.movingIdeal Q₀ D.movingSupported) S
local notation "Jall" => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
  Multiset.count (Subtype.val (Subtype.val P)) (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal)%6) (fun _ : σ => 0)

include hR hI hF hm hf hz hbad hcop hpow hmask

private theorem exists_original_controlled_source
    (c : Eis) [Fintype (Eis⧸Ideal.span {c})]
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((Pall).ideal i))
    (hP : Pairwise (Function.onFun IsCoprime (Pall).ideal))
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀),
      ∀ T : Finset σ, ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode) :
    ∀ h : Eis⧸Ideal.span {c}, ∃ CC : ∀ A : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ),
      ControlledStratumArithmetic (fun i : A => (Pall).generator i.val) N (G h).a0 (G h).c0 (G h).mode,
      ∀ B T, CC (markedActiveSet E B T)=
        originalChosenControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T (C h B T) := by
  intro h
  exact exists_marked_source_selection E
    (fun A => ControlledStratumArithmetic (fun i : A => (Pall).generator i.val) N (G h).a0 (G h).c0 (G h).mode)
    ((Pall).activeControlled hP c G N hN hNp h)
    (fun B T => originalChosenControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T (C h B T))

private theorem original_controlled_source_sum
    (hSodd : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    {N a c : Eis} {mode : Bool}
    (C : ∀ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀),
      ∀ T : Finset σ, ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator
        N a c mode)
    (CC : ∀ A : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ),
      ControlledStratumArithmetic (fun i : A => (Pall).generator i.val) N a c mode)
    (hCC : ∀ B T, CC (markedActiveSet E B T)=
      originalChosenControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T (C B T))
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (X : ℝ) :
    (∑ A : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ),
      localInactiveWeight (Pall).generator (Pall).generator_ne_zero
        (mixedPrimeFunction (Pall).generator (Pall).generator_good Jall markedSumSlots) A *
        mixedReflectedValue (CC A) s ((Pall).restrict A).generator_ne_zero hc
          ((Pall).restrict A).generator_good (fun i => Jall i.val)
          (activeMarks A markedSumSlots) W X) =
    ∑ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀), ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀))\B,
        if completedLocalExponent R F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0)*
        ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*
      mixedReflectedValue (C B T) s
        (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator_ne_zero hc
        (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator_good
        (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val))
        (slotIndices B (PrimeIndex K) T) W X := by
  rw [original_fiber_inactive_sum D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S hSodd]
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro T hT
  congr 1
  rw [hCC B T]
  exact original_chosen_reflected_source_eq D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T
    (C B T) s hc W X

theorem original_selected_reflected_expansion
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hSodd : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (hdis : ∀ P : FreePrimeIndex D.movingIdeal Q₀, ∀ i, S.ideal i≠P.val.val)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1) (hQ₀ : Q₀≠0)
    (hφperiod : CanonicalCoefficientClass.FactorsModulo Q₀ φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q₀)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((Pall).ideal i))
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀),
      ∀ T : Finset σ, ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist (Pall).generator (Pall).generator_good Jall markedSumSlots) W X
      (fun A => ∏ i∈markedSumSlots, if Ideal.span {(Pall).generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀), ∑ T : Finset σ,
        ((∏ b∈(Finset.univ:Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀))\B,
          if completedLocalExponent R F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0)*
          ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*
        mixedReflectedValue (C h B T) (G h).shape
          (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator_ne_zero
          (G h).denominator_ne_zero
          (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator_good
          (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val))
          (slotIndices B (PrimeIndex K) T) W X := by
  have hP : Pairwise (Function.onFun IsCoprime (Pall).ideal) :=
    joined_free_pairwise D.movingIdeal Q₀ D.movingSupported S hS hdis
  have hodd : ∀ i, ringChar (Eis⧸(Pall).ideal i)≠2 := by
    intro i
    cases i with
    | inl P => exact (supported_factors_good D.movingIdeal D.movingSupported P.val.val
        (Multiset.mem_toFinset.mp P.val.property)).2.2
    | inr t => exact hSodd t
  have hj : ∀ i, Jall i<6 := by
    intro i
    cases i with
    | inl P => exact Nat.mod_lt _ (by norm_num)
    | inr t => norm_num
  have hchoose := exists_original_controlled_source D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    S c G N hN hNp hP C
  choose CC hCC using hchoose
  rw [(Pall).marked_reflected_source_of_controlled hP hodd Jall hj markedSumSlots φ hφnorm Q₀ hQ₀ hφperiod
    c hc hcQ G N hN CC W hWcompact lo hi hlo hsupp hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  exact original_controlled_source_sum D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    S hSodd (C h) (CC h) (hCC h) (G h).shape (G h).denominator_ne_zero W X
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1555

/- Original source: OAI/NumberTheory/DirichletL/Reflection/ActualSelected.lean; sha256: 9504f9ab1fc6802ef7ae01f334bb1079f74624624f284447134724d3f7f2653e -/
section Source1556
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ)
local notation "E" => D.primeFiberEquiv R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "Pall" => PrimeFamily.sum (freePrimeFamily D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported) S
local notation "Jall" => Sum.elim (fun P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}) =>
  Multiset.count (Subtype.val (Subtype.val P)) (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal)%6) (fun _ : σ => 0)

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem actual_marked_selected_reflection
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hSodd : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (hdis : ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}), ∀ i, S.ideal i≠P.val.val)
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n, ‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((Pall).ideal i))
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ, ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict B).reflected K hK (S.restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h *
      ∑ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})), ∑ T : Finset σ,
        ((∏ b∈(Finset.univ:Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})))\B,
          if completedLocalExponent R F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0)*
          ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*
        mixedReflectedValue (C h B T) (G h).shape
          (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict B).reflected K hK (S.restrict T)).generator_ne_zero
          (G h).denominator_ne_zero
          (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict B).reflected K hK (S.restrict T)).generator_good
          (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val))
          (slotIndices B (PrimeIndex K) T) W X := by
  have hQ0 : (Q*Ideal.span {(72:Eis)})≠0 := by
    apply mul_ne_zero hQ
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  exact (actual_marked_row_eq_joined D S Ψ Q hmLam hm2 W X).trans
    (original_selected_reflected_expansion D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask S
      hS hSodd hdis (D.fixedFactor Ψ Q) (D.fixedFactor_norm Ψ Q hΨnorm) hQ0
      (D.fixedFactor_periodic Ψ Q hΨperiod) c hc hcQ G N hN hNp C W hWcompact lo hi hlo hsupp hW X hX)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1556

/- Original source: OAI/NumberTheory/DirichletL/Reflection/OriginalWeights.lean; sha256: eb1d36955dee816d28cd7e9a9df70acddf6a471629464b985452a00c314bd75c -/
section Source1557
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def frozenInactiveWeight (J F Q Q₀ : Ideal Eis) (A : Finset (FreeReflection.pool J Q Q₀)) : ℂ :=
  ∏ b∈(Finset.univ:Finset (FreeReflection.pool J Q Q₀))\A,
    if completedLocalExponent J F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0

lemma one_sub_inverse_norm_le_one (I : Ideal Eis) (hI : I≠0) :
    ‖1-(Ideal.absNorm I:ℂ)⁻¹‖≤1 := by
  have hn : (1:ℝ)≤Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hi : (Ideal.absNorm I:ℝ)⁻¹≤1 := inv_le_one_of_one_le₀ hn
  have he : (1-(Ideal.absNorm I:ℂ)⁻¹)=((1-(Ideal.absNorm I:ℝ)⁻¹):ℝ) := by push_cast;rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  have hp : 0≤(Ideal.absNorm I:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  linarith

lemma frozenInactiveWeight_norm (J F Q Q₀ : Ideal Eis) (A : Finset (FreeReflection.pool J Q Q₀)) :
    ‖frozenInactiveWeight J F Q Q₀ A‖≤1 := by
  unfold frozenInactiveWeight
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro b hb
    exact norm_nonneg _
  · intro b hb
    split_ifs
    · exact one_sub_inverse_norm_le_one b.val
        (NeZero.ne ((poolPrimeFamily J Q Q₀).ideal b))
    · simp

lemma original_fourier_frozen_weight_norm {m f z : Eis} (D : GoodMaskRowData m f z)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : ∀ n,‖Ψ n‖≤1)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})] (h : Eis⧸Ideal.span {c})
    (J F Q₀ : Ideal Eis) (A : Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀)) :
    ‖fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*frozenInactiveWeight J F (Ideal.span {m}*F) Q₀ A‖≤1 := by
  rw [norm_mul]
  exact (mul_le_mul (D.fixedCoefficient_norm Ψ Q hΨ c hc h)
    (frozenInactiveWeight_norm J F (Ideal.span {m}*F) Q₀ A) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1557

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SourceSectors.lean; sha256: 3fe059eff8f4f169453ea223860ab13ab7031d98ed324ee22b7d04f39e922684 -/
section Source1558
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

variable {φ σ : Type*} [Fintype φ] [Fintype σ]

theorem exists_fixed_ray_source_arithmetic (F : PrimeFamily φ)
    (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis → PrimeFamily σ)
    (hrows : ∀ K ∈ rows, Admissible K)
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hScop : ∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal))
    (hSN : ∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((S P).ideal i))
    (rowClass slotClass : Eis ⧸ Ideal.span {N^2})
    (hrowClass : ∀ K ∈ rows, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=rowClass)
    (hslotClass : ∀ P ∈ Pset, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator P)=slotClass) :
    ∃ E : ∀ x : SourcePair rows Pset,
      ControlledStratumArithmetic
        (F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val)).generator N a c mode,
      ∀ x0 x, (E x).fixedFactor = (E x0).fixedFactor ∧
        ∀ u m n b, actualCuspColumn (E x) s hc u m n b = actualCuspColumn (E x0) s hc u m n b := by
  obtain ⟨E,κ,A,_,_,hκ,hA⟩ := exists_source_pair_templates F rows Pset S hrows hprod
    N a c mode s hc hN hbase hac hF hNF hrowcop hScop hSN
  refine ⟨E,?_⟩
  intro x0 x
  have he (y : SourcePair rows Pset) :
      separateSector N (primaryGenerator y.val.1.val) (primaryGenerator y.val.2.val) = (rowClass,slotClass) := by
    exact Prod.ext (hrowClass _ y.val.1.property) (hslotClass _ y.val.2.property)
  constructor
  · rw [hκ x,hκ x0,he x,he x0]
  · intro u m n b
    rw [hA x u m n b,hA x0 u m n b,he x,he x0]

end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1558

/- Original source: OAI/NumberTheory/DirichletL/Reflection/SectorData.lean; sha256: 2affed53165ad5e47fb1616a4dc1c105e4747f2d6df72093afbce39b5606bb0c -/
section Source1559
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

structure SectorArithmetic (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows, Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0) where
  referenceIndex : Type (max u v)
  [referenceFintype : Fintype referenceIndex]
  referencePrimes : PrimeFamily referenceIndex
  referenceArithmetic : ControlledStratumArithmetic referencePrimes.generator N a c mode
  completion : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
    ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode
  fixedFactor_eq : ∀ K P hp, (completion K P hp).fixedFactor=referenceArithmetic.fixedFactor
  cuspColumn_eq : ∀ K P hp u m n b,
    actualCuspColumn (completion K P hp) s hc u m n b=actualCuspColumn referenceArithmetic s hc u m n b

attribute [instance] SectorArithmetic.referenceFintype

theorem exists_sector_arithmetic (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows, Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hac : IsCoprime a c) (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K∈rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hprod : ∀ P∈Pset, (∏ i,(S P).ideal i)=P)
    (hScop : ∀ P∈Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal))
    (hSN : ∀ P∈Pset, ∀ i, IsCoprime (Ideal.span {N}) ((S P).ideal i))
    (rowClass slotClass : Eis⧸Ideal.span {N^2})
    (hrowClass : ∀ K∈rows, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=rowClass)
    (hslotClass : ∀ P∈Pset, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator P)=slotClass) :
    Nonempty (SectorArithmetic (N:=N) F rows Pset S hrows s hc) := by
  obtain ⟨E,hE⟩ := exists_fixed_ray_source_arithmetic F rows Pset S hrows hprod N a c mode s hc hN hbase hac
    hF hNF hrowcop hScop hSN rowClass slotClass hrowClass hslotClass
  let D := fun (K : rows) (P : Pset) (hp : IsCoprime K.val P.val) => E ⟨(K,P),hp⟩
  by_cases hnon : Nonempty (SourcePair rows Pset)
  · let x0 : SourcePair rows Pset := Classical.choice hnon
    exact ⟨{
      referenceIndex := φ ⊕ (PrimeIndex x0.val.1.val ⊕ σ)
      referencePrimes := F.reflected x0.val.1.val (hrows x0.val.1.val x0.val.1.property) (S x0.val.2.val)
      referenceArithmetic := E x0
      completion := D
      fixedFactor_eq := fun K P hp => (hE x0 ⟨(K,P),hp⟩).1
      cuspColumn_eq := fun K P hp => (hE x0 ⟨(K,P),hp⟩).2
    }⟩
  · let G0 : PrimeFamily (ULift.{v} φ) := ⟨fun x => F.ideal x.down,fun x => F.maximal x.down,fun x => F.good x.down⟩
    obtain ⟨D0⟩ := G0.exists_controlled N a c mode hc hN hbase hac
      (fun x y hxy => hF (fun h => hxy (ULift.ext x y h))) (fun x => hNF x.down)
    exact ⟨{
      referenceIndex := ULift.{v} φ
      referencePrimes := G0
      referenceArithmetic := D0
      completion := D
      fixedFactor_eq := fun K P hp => (hnon ⟨⟨(K,P),hp⟩⟩).elim
      cuspColumn_eq := fun K P hp => (hnon ⟨⟨(K,P),hp⟩⟩).elim
    }⟩
end
end SevenEighths.InverseReflectedPhase

end OAI

end Source1559
