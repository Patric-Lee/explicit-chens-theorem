import OpenAIGrouped.Unit035
import OpenAIGrouped.Unit012
import OpenAIGrouped.Unit007
import OpenAIGrouped.Unit025
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Descent/Grid.lean; sha256: b42b2f1a674aa2b72632fe7135596c9e447fb3b00f55cf1ef46894bb4291a44c -/
section Source1440
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

section FiniteGrid
variable {M H C A : Type*} [DecidableEq M] [DecidableEq H] [DecidableEq C] [AddCommMonoid A]

def gridCommonSupport (T : Finset ((M × H) × C)) (m : M) : Finset C :=
  (T.filter fun u => u.1.1 = m).image Prod.snd

theorem finite_triple_support_reindex (T : Finset ((M × H) × C))
    (f : (M × H) × C → A) :
    (∑ u ∈ T, f u) = ∑ p ∈ T.image Prod.fst,
      ∑ c ∈ gridCommonSupport T p.1, if (p, c) ∈ T then f (p, c) else 0 := by
  have hp := Finset.sum_fiberwise_of_maps_to
    (s := T) (t := T.image Prod.fst) (g := Prod.fst)
    (fun u hu => Finset.mem_image.mpr ⟨u, hu, rfl⟩) f
  rw [← hp]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun u _ => u.2)
  · intro u hu
    obtain ⟨huT, hup⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huT, congrArg Prod.fst hup⟩, rfl⟩
    · simpa only [← hup, Prod.eta] using huT
  · intro u hu v hv he
    apply Prod.ext
    · exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
    · exact he
  · intro c hc
    have hpc := (Finset.mem_filter.mp hc).2
    exact ⟨(p, c), Finset.mem_filter.mpr ⟨hpc, rfl⟩, rfl⟩
  · intro u hu
    have hup := (Finset.mem_filter.mp hu).2
    simp only [← hup, Prod.eta]

end FiniteGrid

def HybridColumnData.gridIndex (d : HybridColumnData) :
    (Ideal Eis × Ideal Eis) × Ideal Eis := ((d.residualN, d.residualB), d.common)

theorem HybridColumnData.gridIndex_injective_on_square (t : Ideal Eis) :
    Set.InjOn HybridColumnData.gridIndex {d | d.square = t} := by
  intro d hd e he hg
  have hm : d.residualN = e.residualN := congrArg (fun u => u.1.1) hg
  have hh : d.residualB = e.residualB := congrArg (fun u => u.1.2) hg
  have hc : d.common = e.common := congrArg Prod.snd hg
  have ht : d.square = e.square := hd.trans he.symm
  cases d
  cases e
  cases hc
  cases hm
  cases hh
  cases ht
  rfl

def hybridGridSupport (D : Finset HybridColumnData) :
    Finset ((Ideal Eis × Ideal Eis) × Ideal Eis) := D.image HybridColumnData.gridIndex

theorem hybrid_grid_reindex (D : Finset HybridColumnData) (t : Ideal Eis)
    (hD : ∀ d ∈ D, d.square = t) (f : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) :
    (∑ d ∈ D, f d.common d.residualN d.residualB) =
      ∑ p ∈ (hybridGridSupport D).image Prod.fst,
        ∑ c ∈ gridCommonSupport (hybridGridSupport D) p.1,
          if (p, c) ∈ hybridGridSupport D then f c p.1 p.2 else 0 := by
  have he : (∑ d ∈ D, f d.common d.residualN d.residualB) =
      ∑ u ∈ hybridGridSupport D, f u.2 u.1.1 u.1.2 := by
    symm
    apply Finset.sum_image
    intro d hd e he hg
    exact HybridColumnData.gridIndex_injective_on_square t (hD d hd) (hD e he) hg
  rw [he]
  exact finite_triple_support_reindex (hybridGridSupport D) _

theorem gridCommonSupport_origin (D : Finset HybridColumnData) (m c : Ideal Eis)
    (hc : c ∈ gridCommonSupport (hybridGridSupport D) m) :
    ∃ d ∈ D, d.residualN = m ∧ d.common = c := by
  obtain ⟨u, hu, huc⟩ := Finset.mem_image.mp hc
  obtain ⟨huT, hum⟩ := Finset.mem_filter.mp hu
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp huT
  exact ⟨d, hd, hum, huc⟩

end
end SevenEighths.InverseMoment

end OAI

end Source1440

/- Original source: OAI/NumberTheory/DirichletL/Descent/Quotients.lean; sha256: bf02ee0e8e64a55a1574c11f5afcc852ab277b9e5b7c4a13ba49b25e312ca3b9 -/
section Source1441
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def quotientSupport (D : Ideal Eis) (S : Finset (Ideal Eis)) : Finset (Ideal Eis) :=
  (S.filter (fun I => D ∣ I)).image (idealQuotient D)

@[simp] theorem mem_quotientSupport (D J : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) :
    J ∈ quotientSupport D S ↔ D * J ∈ S := by
  constructor
  · intro hJ
    obtain ⟨I, hI, he⟩ := Finset.mem_image.mp hJ
    obtain ⟨hIS, hDI⟩ := Finset.mem_filter.mp hI
    rw [← he, idealQuotient_mul hDI]
    exact hIS
  · intro hJ
    refine Finset.mem_image.mpr ⟨D * J, Finset.mem_filter.mpr ⟨hJ, dvd_mul_right _ _⟩, ?_⟩
    exact mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right D J))

theorem sum_quotientSupport {A : Type*} [AddCommMonoid A]
    (D : Ideal Eis) (S : Finset (Ideal Eis)) (f : Ideal Eis → A) :
    (∑ I ∈ S with D ∣ I, f I) = ∑ J ∈ quotientSupport D S, f (D * J) := by
  rw [quotientSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    rw [idealQuotient_mul (Finset.mem_filter.mp hI).2]
  · intro I hI J hJ he
    exact idealQuotient_injective_on D (Finset.mem_filter.mp hI).2
      (Finset.mem_filter.mp hJ).2 he

theorem quotientSupport_nonzero (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, I ≠ 0)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) : J ≠ 0 := by
  have h := hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)
  exact (mul_ne_zero_iff.mp h).2

theorem quotientSupport_quadratic_admissible (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, CanonicalQuadraticSieve.Admissible I)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    CanonicalQuadraticSieve.Admissible J :=
  admissible_of_dvd (hS (D * J) ((mem_quotientSupport D J hD S).mp hJ))
    (dvd_mul_left _ _)

theorem quotientSupport_cubic_admissible (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, CubicSieve.Admissible I)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    CubicSieve.Admissible J :=
  CubicSieve.cubic_admissible_of_dvd
    (hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)) (dvd_mul_left _ _)

theorem quotientSupport_norm_le (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (N : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ 0) (hS : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ N)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    (Ideal.absNorm J : ℝ) ≤ N := by
  have hDJ := (mem_quotientSupport D J hD S).mp hJ
  have hn : Ideal.absNorm J ≤ Ideal.absNorm (D * J) := by
    apply Nat.le_of_dvd
    · exact Nat.pos_of_ne_zero (fun hz => hS0 _ hDJ (Ideal.absNorm_eq_zero_iff.mp hz))
    · exact map_dvd Ideal.absNorm (dvd_mul_left J D)
  exact (Nat.cast_le.mpr hn).trans (hS _ hDJ)

theorem quotientSupport_shell (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (L : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ 0)
    (hS : ∀ I ∈ S, L ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ 2 * L)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    max 1 (L / (Ideal.absNorm D : ℝ)) ≤ (Ideal.absNorm J : ℝ) ∧
      (Ideal.absNorm J : ℝ) ≤ 2 * max 1 (L / (Ideal.absNorm D : ℝ)) := by
  have hDJ := (mem_quotientSupport D J hD S).mp hJ
  have hnD : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD (Ideal.absNorm_eq_zero_iff.mp hz))
  have hJ0 := quotientSupport_nonzero D hD S hS0 J hJ
  have hnJ : 1 ≤ (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hJ0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs := hS (D * J) hDJ
  simp only [map_mul, Nat.cast_mul] at hs
  constructor
  · refine max_le hnJ ((div_le_iff₀ hnD).mpr ?_)
    simpa only [mul_comm] using hs.1
  · have hj : (Ideal.absNorm J : ℝ) ≤ 2 * (L / (Ideal.absNorm D : ℝ)) := by
      have hj := (le_div_iff₀ hnD).mpr (show
          (Ideal.absNorm J : ℝ) * (Ideal.absNorm D : ℝ) ≤ 2 * L by
        simpa only [mul_comm] using hs.2)
      simpa only [mul_div_assoc] using hj
    exact hj.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))

theorem quotient_hybridCubicCoefficient_energy
    (R r h t : Ideal Eis) (hR : R ≠ 0) (S : Finset (Ideal Eis)) (L : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ 0)
    (hS : ∀ I ∈ S, L ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ I ∈ S, ‖a I‖ ≤ 1) :
    (∑ P ∈ quotientSupport R S, ‖hybridCubicCoefficient R r h t a P‖ ^ 2) ≤ 256 := by
  apply hybridCubicCoefficient_energy R r h t (quotientSupport R S)
    (max 1 (L / (Ideal.absNorm R : ℝ))) (le_max_left _ _)
  · exact quotientSupport_shell R hR S L hS0 hS
  · intro P hP
    exact ha (R * P) ((mem_quotientSupport R P hR S).mp hP)

end
end SevenEighths.InverseMoment

end OAI

end Source1441

/- Original source: OAI/NumberTheory/DirichletL/Descent/DivisorExtraction.lean; sha256: 73153d8ef4c89d147b941e0a0028a96dfb7d2047df60fb60e99b37386bcc620b -/
section Source1442
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem inverseCubicKernel_divisor_overlap_zero (R r P c m : Ideal Eis)
    (hP : primaryGenerator P ≠ 0) (hcm : primaryGenerator (c * m) ≠ 0)
    (hRP : R ∣ P) (hrc : r ∣ c) (hRr : ¬ IsCoprime R r) :
    inverseCubicKernel P (c * m) = 0 := by
  apply inverseCubicKernel_eq_zero_of_not_coprime P (c * m) hP hcm
  intro hcop
  have hPc := hcop.of_isCoprime_of_dvd_right (dvd_mul_right c m)
  exact hRr ((hPc.of_isCoprime_of_dvd_left hRP).of_isCoprime_of_dvd_right hrc)

theorem double_divisor_row_reindex {A : Type*} [AddCommMonoid A]
    (rows : Finset (Ideal Eis)) (hrows : ∀ k ∈ rows, k ≠ 0)
    (R r : Ideal Eis) (hRr : IsCoprime R r) (F : Ideal Eis → A) :
    (∑ k ∈ rows, if (R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k) then F k else 0) =
      ∑ k ∈ quotientSupport (R * r) rows, F ((R * r) * k) := by
  have hsel (k : Ideal Eis) (hk : k ∈ rows) :
      ((R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k)) ↔ R * r ∣ k := by
    rw [Finset.mem_product, mem_idealDivisors (hrows k hk), mem_idealDivisors (hrows k hk)]
    exact ⟨fun h => hRr.mul_dvd h.1 h.2,
      fun h => ⟨dvd_trans (dvd_mul_right R r) h, dvd_trans (dvd_mul_left r R) h⟩⟩
  calc
    _ = ∑ k ∈ rows, if R * r ∣ k then F k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [hsel k hk]
    _ = ∑ k ∈ rows with R * r ∣ k, F k := (Finset.sum_filter _ _).symm
    _ = _ := sum_quotientSupport (R * r) rows F

theorem double_column_divisor_reindex {A : Type*} [AddCommMonoid A]
    (Pset cset : Finset (Ideal Eis)) (R r : Ideal Eis)
    (F : Ideal Eis → Ideal Eis → A) :
    (∑ P ∈ Pset, ∑ c ∈ cset, if R ∣ P ∧ r ∣ c then F P c else 0) =
      ∑ P ∈ quotientSupport R Pset, ∑ c ∈ quotientSupport r cset, F (R * P) (r * c) := by
  calc
    _ = ∑ P ∈ Pset with R ∣ P, ∑ c ∈ cset with r ∣ c, F P c := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro P hP
      by_cases hd : R ∣ P
      · simp only [hd, true_and, ite_true]
      · simp [hd]
    _ = ∑ P ∈ quotientSupport R Pset, ∑ c ∈ cset with r ∣ c, F (R * P) c :=
      sum_quotientSupport R Pset (fun P => ∑ c ∈ cset with r ∣ c, F P c)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P hP
      exact sum_quotientSupport r cset (F (R * P))

end
end SevenEighths.InverseMoment

end OAI

end Source1442

/- Original source: OAI/NumberTheory/DirichletL/Descent/ExtractedGrid.lean; sha256: 9d4a315439681c79615e9a44da2d3710c762c70c0429555bced3bdc09a46b767 -/
section Source1443
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "Grid" => Finset ((Ideal Eis × Ideal Eis) × Ideal Eis)

def quotientGridSupport (r : Ideal Eis) (T : Grid) : Grid :=
  (T.filter fun u => r ∣ u.2).image fun u => (u.1, idealQuotient r u.2)

@[simp] theorem mem_quotientGridSupport (r : Ideal Eis) (hr : r ≠ 0)
    (T : Grid) (p : Ideal Eis × Ideal Eis) (c : Ideal Eis) :
    (p, c) ∈ quotientGridSupport r T ↔ (p, r * c) ∈ T := by
  constructor
  · intro hu
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hu
    obtain ⟨huT, hru⟩ := Finset.mem_filter.mp hu
    have hp : u.1 = p := congrArg Prod.fst he
    have hc : idealQuotient r u.2 = c := congrArg Prod.snd he
    have hec : r * c = u.2 := by rw [← hc, idealQuotient_mul hru]
    simpa only [← hp, hec, Prod.eta] using huT
  · intro hu
    refine Finset.mem_image.mpr ⟨(p, r * c), Finset.mem_filter.mpr ⟨hu, dvd_mul_right _ _⟩, ?_⟩
    refine Prod.ext (show p = p from rfl) ?_
    exact mul_left_cancel₀ hr (idealQuotient_mul (dvd_mul_right r c))

theorem sum_quotientGridSupport {A : Type*} [AddCommMonoid A]
    (r : Ideal Eis) (T : Grid) (f : (Ideal Eis × Ideal Eis) × Ideal Eis → A) :
    (∑ u ∈ T, if r ∣ u.2 then f u else 0) =
      ∑ u ∈ quotientGridSupport r T, f (u.1, r * u.2) := by
  rw [← Finset.sum_filter, quotientGridSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [idealQuotient_mul (Finset.mem_filter.mp hu).2]
  · intro u hu v hv he
    apply Prod.ext
    · simpa only using congrArg Prod.fst he
    · exact idealQuotient_injective_on r (Finset.mem_filter.mp hu).2
        (Finset.mem_filter.mp hv).2 (congrArg Prod.snd he)

theorem quotientGridSupport_origin (r : Ideal Eis) (hr : r ≠ 0)
    (D : Finset HybridColumnData) (p : Ideal Eis × Ideal Eis) (c : Ideal Eis)
    (hu : (p, c) ∈ quotientGridSupport r (hybridGridSupport D)) :
    ∃ d ∈ D, (d.residualN, d.residualB) = p ∧ d.common = r * c := by
  have hm := (mem_quotientGridSupport r hr (hybridGridSupport D) p c).mp hu
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hm
  exact ⟨d, hd, congrArg Prod.fst he, congrArg Prod.snd he⟩

theorem quotientGridCommonSupport_origin (r : Ideal Eis) (hr : r ≠ 0)
    (D : Finset HybridColumnData) (m c : Ideal Eis)
    (hc : c ∈ gridCommonSupport (quotientGridSupport r (hybridGridSupport D)) m) :
    ∃ d ∈ D, d.residualN = m ∧ d.common = r * c := by
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hc
  obtain ⟨huQ, hum⟩ := Finset.mem_filter.mp hu
  obtain ⟨d, hd, hp, hdc⟩ := quotientGridSupport_origin r hr D u.1 u.2 huQ
  refine ⟨d, hd, (congrArg Prod.fst hp).trans hum, ?_⟩
  simpa only [he] using hdc

def extractedGridCoefficient (T : Grid) (R t : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (c m h : Ideal Eis) : ℂ :=
  if ((m, h), c) ∈ T then beta c m h * (if IsCoprime R (h * t) then 1 else 0) else 0

theorem extractedGridCoefficient_norm_le_one (T : Grid) (R t : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (hb : ∀ u ∈ T, ‖beta u.2 u.1.1 u.1.2‖ ≤ 1)
    (c m h : Ideal Eis) : ‖extractedGridCoefficient T R t beta c m h‖ ≤ 1 := by
  unfold extractedGridCoefficient
  split_ifs with hu hcop
  · simpa using hb ((m, h), c) hu
  · simp
  · simp

def gridDivisorHybridBlock (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) : ℂ :=
  ∑ u ∈ T, if r ∣ u.2 then ∑ P ∈ Pset, if R ∣ P then
    a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta u.2 u.1.1 u.1.2 *
      (quadraticRow k (primaryGenerator (u.1.1 * u.1.2)) * inverseCubicKernel P (u.2 * u.1.1)) *
        (if IsCoprime P (u.1.2 * t) then 1 else 0)
    else 0 else 0

theorem gridDivisorHybridBlock_eq_zero_of_quotientGrid_empty
    (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) (hQ : quotientGridSupport r T = ∅) :
    gridDivisorHybridBlock T Pset a beta t k R r = 0 := by
  unfold gridDivisorHybridBlock
  rw [sum_quotientGridSupport, hQ]
  exact Finset.sum_empty

theorem gridDivisorHybridBlock_extract
    (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) (hR : R ≠ 0) (hr : r ≠ 0)
    (hk : Admissible ((R * r) * k))
    (hP : ∀ P ∈ Pset, CubicSieve.Admissible P) :
    gridDivisorHybridBlock T Pset a beta t ((R * r) * k) R r =
      (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
        ∑ p ∈ (quotientGridSupport r T).image Prod.fst,
          quadraticRow k (primaryGenerator (p.1 * p.2)) *
            ∑ c ∈ gridCommonSupport (quotientGridSupport r T) p.1,
              hybridColumnCoefficient R r (extractedGridCoefficient T R t beta) c p.1 p.2 *
                ∑ P ∈ quotientSupport R Pset,
                  hybridCubicCoefficient R r p.2 t a P * inverseCubicKernel P (c * p.1) := by
  have hmask (P h : Ideal Eis) :
      (if IsCoprime (R * P) (h * t) then (1 : ℂ) else 0) =
      (if IsCoprime R (h * t) then 1 else 0) *
        (if IsCoprime P (h * t) then 1 else 0) := by
    simp only [IsCoprime.mul_left_iff]
    split_ifs <;> simp_all
  unfold gridDivisorHybridBlock
  rw [sum_quotientGridSupport]
  have hinner (u : (Ideal Eis × Ideal Eis) × Ideal Eis) :
      (∑ P ∈ Pset, if R ∣ P then
        a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta (r * u.2) u.1.1 u.1.2 *
          (quadraticRow ((R * r) * k) (primaryGenerator (u.1.1 * u.1.2)) *
            inverseCubicKernel P ((r * u.2) * u.1.1)) *
              (if IsCoprime P (u.1.2 * t) then 1 else 0) else 0) =
      ∑ P ∈ quotientSupport R Pset,
        a (R * P) / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) * beta (r * u.2) u.1.1 u.1.2 *
          (quadraticRow ((R * r) * k) (primaryGenerator (u.1.1 * u.1.2)) *
            inverseCubicKernel (R * P) ((r * u.2) * u.1.1)) *
              (if IsCoprime (R * P) (u.1.2 * t) then 1 else 0) := by
    rw [← Finset.sum_filter]
    exact sum_quotientSupport R Pset _
  simp_rw [hinner]
  rw [finite_triple_support_reindex]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hu : (p, c) ∈ quotientGridSupport r T
  · have huc := (mem_quotientGridSupport r hr T p c).mp hu
    simp only [hu, ite_true]
    apply Finset.sum_congr rfl
    intro P hPP
    have hpgen := (quotientSupport_cubic_admissible R hR Pset hP P hPP).2
    have hid := hybrid_extracted_block_identity R r k P c p.1 p.2 t hk hpgen a
      (extractedGridCoefficient T R t beta)
    simp only [extractedGridCoefficient, huc, ite_true] at hid
    rw [hmask]
    calc
      _ = a (R * P) / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) *
          (beta (r * c) p.1 p.2 * (if IsCoprime R (p.2 * t) then 1 else 0)) *
          (quadraticRow ((R * r) * k) (primaryGenerator (p.1 * p.2)) *
            inverseCubicKernel (R * P) ((r * c) * p.1)) *
          (if IsCoprime P (p.2 * t) then 1 else 0) := by ring
      _ = _ := by rw [hid]; ring
  · have huc : (p, r * c) ∉ T := (mem_quotientGridSupport r hr T p c).not.mp hu
    simp [hu, hybridColumnCoefficient, extractedGridCoefficient, huc]

end
end SevenEighths.InverseMoment

end OAI

end Source1443

/- Original source: OAI/NumberTheory/DirichletL/Descent/Quadratic.lean; sha256: e0da7cdbebfd3fb86babc8c5d3547865e4bce2cd3b03897373c0b4aec485be8e -/
section Source1444
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_family_quadratic_hybrid_orientation :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    ∀ {m n : Type*} [Fintype m] [Fintype n],
    ∀ (rows : m → Ideal Eis) (cols : n → Ideal Eis),
      Function.Injective rows → Function.Injective cols →
      (∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M) →
      (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
    ∀ a : n → ℂ,
      (∑ i, ‖∑ j, quadraticRow (rows i) (primaryGenerator (cols j)) * a j‖ ^ 2) ≤
        C * (M * N) ^ ε * (M + N) * ∑ j, ‖a j‖ ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨C, hC, ?_⟩
  intro M N hM hN m n _ _ rows cols hr hc hrows hcols a
  let B : Matrix n m ℂ := fun j i => quadraticRow (rows i) (primaryGenerator (cols j))
  have hB : ‖FiniteSieveOperator.operator B‖ ^ 2 ≤ sieveNorm N M :=
    family_squared_norm_le cols rows hc hr N M hcols hrows
  have hBT : B.conjTranspose =
      (fun i j => quadraticRow (rows i) (primaryGenerator (cols j))) := by
    ext i j
    exact canonical_quadraticRow_star (rows i) (hrows i).1 _
  have he := FiniteSieveOperator.energy_bound B.conjTranspose a
  rw [FiniteSieveOperator.operator_conjTranspose_norm, hBT] at he
  have henergy : 0 ≤ ∑ j, ‖a j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply he.trans
  calc
    _ ≤ sieveNorm N M * ∑ j, ‖a j‖ ^ 2 := mul_le_mul_of_nonneg_right hB henergy
    _ ≤ (C * (N * M) ^ ε * (N + M)) * ∑ j, ‖a j‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hsharp N M hN hM) henergy
    _ = _ := by rw [mul_comm N M, add_comm N M]

theorem finite_squarefree_quadratic_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows cols : Finset (Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ J ∈ cols, Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ X) →
    ∀ a : Ideal Eis → ℂ,
      (∑ k ∈ rows, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2) ≤
        C * (K * X) ^ ε * (K + X) * ∑ J ∈ cols, ‖a J‖ ^ 2 := by
  obtain ⟨C, hC, hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨4 * C, by positivity, ?_⟩
  intro K X hK hX rows cols hrows hcols a
  have hf := squarefree_all_column_energy (fun J : cols => J.val) Subtype.val_injective X K
    (fun J => hcols J.val J.property) (fun J => a J.val)
  have hi (k : idealRange K) :
      (∑ J : cols, quadraticRow k.val (primaryGenerator J.val) * a J.val) =
        ∑ J ∈ cols, quadraticRow k.val (primaryGenerator J) * a J :=
    Finset.sum_coe_sort cols (fun J => quadraticRow k.val (primaryGenerator J) * a J)
  simp_rw [hi] at hf
  rw [Finset.sum_coe_sort (idealRange K)
    (fun k => ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2),
    Finset.sum_coe_sort cols (fun J => ‖a J‖ ^ 2)] at hf
  have hr : rows ⊆ idealRange K := fun k hk => mem_idealRange.mpr (hrows k hk)
  have he : (∑ k ∈ rows, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2) ≤
      ∑ k ∈ idealRange K, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hr (by intro k _ _; exact sq_nonneg _)
  apply (he.trans hf).trans
  calc
    _ ≤ 4 * (C * (X * K) ^ ε * (X + K)) * ∑ J ∈ cols, ‖a J‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (hsharp X K hX hK) (by norm_num)
    _ = _ := by rw [mul_comm X K, add_comm X K]; ring

theorem quadratic_squarefree_product_column_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ a : Ideal Eis × Ideal Eis → ℂ,
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (p.1 * p.2)) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Cq, hCq, hquad⟩ := finite_squarefree_quadratic_energy (ε / 2) hhalf
  obtain ⟨Cd, hCd, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) hhalf
  refine ⟨Cq * Cd, mul_pos hCq hCd, ?_⟩
  intro K X hK hX rows pairs hrows hpairs a
  let target := pairs.image (fun p => p.1 * p.2)
  have ht (J : Ideal Eis) (hJ : J ∈ target) :
      Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ X := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hJ
    exact hpairs p hp
  have hfiber (J : Ideal Eis) (hJ : J ∈ target) :
      ((pairs.filter (fun p => p.1 * p.2 = J)).card : ℝ) ≤ Cd * X ^ (ε / 2) := by
    apply (Nat.cast_le.mpr (product_fiber_card pairs J (ht J hJ).1.ne_zero)).trans
    exact (hdiv J (ht J hJ).1.ne_zero).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (ht J hJ).2 hhalf.le) hCd.le)
  have he := column_fiber_sieve rows pairs target (fun p => p.1 * p.2)
    (fun k J => quadraticRow k (primaryGenerator J)) a
    (Cq * (K * X) ^ (ε / 2) * (K + X)) (Cd * X ^ (ε / 2)) (by positivity)
    (fun p hp => Finset.mem_image_of_mem _ hp) hfiber
    (hquad K X hK hX rows target hrows ht)
  apply he.trans
  have hKX : 0 < K * X := mul_pos (by linarith) (by linarith)
  have hpow : (K * X) ^ (ε / 2) * X ^ (ε / 2) ≤ (K * X) ^ ε := by
    calc
      _ ≤ (K * X) ^ (ε / 2) * (K * X) ^ (ε / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hKX.le _)
        exact Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith) hK) hhalf.le
      _ = _ := by rw [← Real.rpow_add hKX]; congr 1 ; ring
  calc
    _ = (Cq * Cd) * ((K * X) ^ (ε / 2) * X ^ (ε / 2)) * (K + X) *
        ∑ p ∈ pairs, ‖a p‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem quadratic_product_column_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Admissible (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ a : Ideal Eis × Ideal Eis → ℂ,
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (p.1 * p.2)) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Cq, hCq, hquadratic⟩ := finite_family_quadratic_hybrid_orientation (ε / 2) hhalf
  obtain ⟨Cd, hCd, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) hhalf
  refine ⟨Cq * Cd, mul_pos hCq hCd, ?_⟩
  intro K X hK hX rows pairs hrows hpairs a
  let target := pairs.image (fun p => p.1 * p.2)
  have ht (J : Ideal Eis) (hJ : J ∈ target) :
      Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ X := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hJ
    exact hpairs p hp
  have hquad (f : Ideal Eis → ℂ) :
      (∑ k ∈ rows, ‖∑ J ∈ target, quadraticRow k (primaryGenerator J) * f J‖ ^ 2) ≤
        (Cq * (K * X) ^ (ε / 2) * (K + X)) * ∑ J ∈ target, ‖f J‖ ^ 2 := by
    have he := hquadratic K X hK hX
      (fun k : rows => k.val) (fun J : target => J.val)
      Subtype.val_injective Subtype.val_injective
      (fun k => hrows k.val k.property) (fun J => ht J.val J.property)
      (fun J => f J.val)
    have hi (k : rows) :
        (∑ J : target, quadraticRow k.val (primaryGenerator J.val) * f J.val) =
        ∑ J ∈ target, quadraticRow k.val (primaryGenerator J) * f J :=
      Finset.sum_coe_sort target (fun J => quadraticRow k.val (primaryGenerator J) * f J)
    simp_rw [hi] at he
    rw [Finset.sum_coe_sort rows
      (fun k => ‖∑ J ∈ target, quadraticRow k (primaryGenerator J) * f J‖ ^ 2),
      Finset.sum_coe_sort target (fun J => ‖f J‖ ^ 2)] at he
    exact he
  have hfiber (J : Ideal Eis) (hJ : J ∈ target) :
      ((pairs.filter (fun p => p.1 * p.2 = J)).card : ℝ) ≤ Cd * X ^ (ε / 2) := by
    apply (Nat.cast_le.mpr (CanonicalQuadraticSieve.product_fiber_card pairs J (ht J hJ).1.1)).trans
    exact (hdiv J (ht J hJ).1.1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (ht J hJ).2 hhalf.le) hCd.le)
  have he := column_fiber_sieve rows pairs target (fun p => p.1 * p.2)
    (fun k J => quadraticRow k (primaryGenerator J)) a
    (Cq * (K * X) ^ (ε / 2) * (K + X)) (Cd * X ^ (ε / 2)) (by positivity)
    (fun p hp => Finset.mem_image_of_mem _ hp) hfiber hquad
  apply he.trans
  have hKX : 0 < K * X := mul_pos (by linarith) (by linarith)
  have hpow : (K * X) ^ (ε / 2) * X ^ (ε / 2) ≤ (K * X) ^ ε := by
    calc
      _ ≤ (K * X) ^ (ε / 2) * (K * X) ^ (ε / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hKX.le _)
        exact Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith) hK) hhalf.le
      _ = _ := by rw [← Real.rpow_add hKX]; congr 1 ; ring
  calc
    _ = (Cq * Cd) * ((K * X) ^ (ε / 2) * X ^ (ε / 2)) * (K + X) *
        ∑ p ∈ pairs, ‖a p‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem quadratic_fixed_factor_energy
    (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis))
    (hrows : ∀ k ∈ rows, Admissible k) (B : Ideal Eis)
    (a : Ideal Eis × Ideal Eis → ℂ) :
    (∑ k ∈ rows, ‖∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
    ∑ k ∈ rows, ‖∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (p.1 * p.2)) * a p‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  have he : (∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p) =
      quadraticRow k (primaryGenerator B) * ∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (p.1 * p.2)) * a p := by
    simp only [primaryGenerator_mul,
      canonical_quadraticRow_argument_mul k (hrows k hk), Finset.mul_sum, mul_assoc]
  rw [he]
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one k _)

theorem quadratic_product_column_energy_fixed_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Admissible (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B : Ideal Eis) (a : Ideal Eis × Ideal Eis → ℂ),
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := quadratic_product_column_energy ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B a
  exact (quadratic_fixed_factor_energy rows pairs (fun k hk => (hrows k hk).1) B a).trans
    (hb K X hK hX rows pairs hrows hpairs a)

theorem quadratic_squarefree_product_energy_fixed_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B : Ideal Eis) (a : Ideal Eis × Ideal Eis → ℂ),
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := quadratic_squarefree_product_column_energy ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B a
  exact (quadratic_fixed_factor_energy rows pairs (fun k hk => (hrows k hk).1) B a).trans
    (hb K X hK hX rows pairs hrows hpairs a)

end
end SevenEighths.InverseMoment

end OAI

end Source1444

/- Original source: OAI/NumberTheory/DirichletL/Descent/HybridReduction.lean; sha256: 585f951d5aff0641257a0853399a168ae8a1b5e75dcea71f0ed65557a2dcee64 -/
section Source1445
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_inverse_cubic_energy
    (Jset Pset : Finset (Ideal Eis)) (N L : ℝ)
    (hJ : ∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N)
    (hP : ∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L)
    (a : Ideal Eis → ℂ) :
    (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2) ≤
      CubicSieve.sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  let A : Matrix Jset Pset ℂ := fun J P => CubicSieve.idealKernel P.val J.val
  have hnorm : CubicSieve.squaredNorm (fun J P => star (A J P)) =
      CubicSieve.squaredNorm A :=
    congrArg (fun z : ℝ => z ^ 2) (CubicSieve.operator_conjugate_norm A)
  have hfamily : CubicSieve.squaredNorm A ≤ CubicSieve.sieveNorm N L :=
    CubicSieve.family_squared_norm_le
      (fun J : Jset => J.val) (fun P : Pset => P.val)
      Subtype.val_injective Subtype.val_injective N L
      (fun J => hJ J.val J.property) (fun P => hP P.val P.property)
  have he := CubicSieve.energy_le_squaredNorm (fun J P => star (A J P)) (fun P => a P.val)
  rw [hnorm] at he
  have he' := he.trans (mul_le_mul_of_nonneg_right hfamily
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hinner (J : Jset) :
      (∑ P : Pset, star (A J P) * a P.val) =
        ∑ P ∈ Pset, a P * inverseCubicKernel P J.val := by
    simp only [A, inverseCubicKernel, CubicSieve.idealKernel, mul_comm]
    exact Finset.sum_coe_sort Pset
      (fun P => a P * star (ConcreteTraceCRT.eisEmbedding
        (CubicJacobiGlobal.idealSymbol P (primaryGenerator J.val))))
  simp_rw [hinner] at he'
  rw [Finset.sum_coe_sort Jset
    (fun J => ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2),
    Finset.sum_coe_sort Pset (fun P => ‖a P‖ ^ 2)] at he'
  exact he'

theorem hybrid_quadratic_reduction (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B mBad : Ideal Eis) (cset : Ideal Eis → Finset (Ideal Eis))
      (Pset : Finset (Ideal Eis)) (coef : Ideal Eis → Ideal Eis → ℂ)
      (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (Cbound : ℝ),
      (∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) *
          (∑ c ∈ cset p.1, beta c p.1 p.2 *
            (∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))))‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * Cbound *
        ∑ p ∈ pairs, ∑ c ∈ cset p.1,
          ‖∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))‖ ^ 2 := by
  obtain ⟨C, hC, hquadratic⟩ := quadratic_squarefree_product_energy_fixed_factor ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B mBad cset Pset coef beta Cbound hcount hbeta
  let F (p : Ideal Eis × Ideal Eis) (c : Ideal Eis) :=
    ∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))
  have he := hquadratic K X hK hX rows pairs hrows hpairs B
    (fun p => ∑ c ∈ cset p.1, beta c p.1 p.2 * F p c)
  apply he.trans
  have hlocal (p : Ideal Eis × Ideal Eis) (hp : p ∈ pairs) :
      ‖∑ c ∈ cset p.1, beta c p.1 p.2 * F p c‖ ^ 2 ≤
        Cbound * ∑ c ∈ cset p.1, ‖F p c‖ ^ 2 := by
    exact (bounded_finset_coefficient_sum_sq (cset p.1)
      (fun c => beta c p.1 p.2) (F p) (hbeta p hp)).trans
        (mul_le_mul_of_nonneg_right (hcount p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  calc
    _ ≤ C * (K * X) ^ ε * (K + X) *
        ∑ p ∈ pairs, Cbound * ∑ c ∈ cset p.1, ‖F p c‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlocal)
      positivity
    _ = _ := by rw [← Finset.mul_sum]; simp only [F]; ring

theorem cubic_product_row_bound_of_sieve (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℝ, 1 ≤ N →
    ∀ (pairs : Finset (Ideal Eis × Ideal Eis)) (Jset Pset : Finset (Ideal Eis))
      (mBad : Ideal Eis) (S : ℝ),
      (∀ p ∈ pairs, p.2 * (mBad * p.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ a : Ideal Eis → ℂ,
        (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2) ≤
          S * ∑ P ∈ Pset, ‖a P‖ ^ 2) →
      ∀ a : Ideal Eis → ℂ,
        (∑ p ∈ pairs, ‖∑ P ∈ Pset,
          a P * inverseCubicKernel P (p.2 * (mBad * p.1))‖ ^ 2) ≤
          D * N ^ ε * S * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  obtain ⟨D, hD, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨D, hD, ?_⟩
  intro N hN pairs Jset Pset mBad S hmap hJset hcubic a
  let E (J : Ideal Eis) := ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2
  have hfiber (J : Ideal Eis) (hJ : J ∈ Jset) :
      (∑ _p ∈ pairs with _p.2 * (mBad * _p.1) = J, (1 : ℝ)) ≤ D * N ^ ε := by
    have hJ0 := (hJset J hJ).1.1.ne_zero
    have hc : ((pairs.filter (fun p => p.2 * (mBad * p.1) = J)).card : ℝ) ≤
        ((IdealMobiusDivisorSum.idealDivisors J).card : ℝ) :=
      Nat.cast_le.mpr (scaled_product_fiber_card pairs mBad J hJ0)
    have hd := (hdiv J hJ0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hJset J hJ).2 hε.le) hD.le)
    exact (by simpa using hc :
      (∑ _p ∈ pairs with _p.2 * (mBad * _p.1) = J, (1 : ℝ)) ≤
        ((IdealMobiusDivisorSum.idealDivisors J).card : ℝ)).trans hd
  have hf := fiber_energy_bound pairs Jset (fun p => p.2 * (mBad * p.1))
    (fun _ => 1) (fun _ => D * N ^ ε) E hmap (fun _ _ => sq_nonneg _) hfiber
  simp only [one_mul, ← Finset.mul_sum] at hf
  apply hf.trans
  calc
    _ ≤ (D * N ^ ε) * (S * ∑ P ∈ Pset, ‖a P‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hcubic a) (by positivity)
    _ = _ := by ring

theorem cubic_product_row_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N L : ℝ, 1 ≤ N →
    ∀ (pairs : Finset (Ideal Eis × Ideal Eis)) (Jset Pset : Finset (Ideal Eis))
      (mBad : Ideal Eis),
      (∀ p ∈ pairs, p.2 * (mBad * p.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      ∀ a : Ideal Eis → ℂ,
        (∑ p ∈ pairs, ‖∑ P ∈ Pset,
          a P * inverseCubicKernel P (p.2 * (mBad * p.1))‖ ^ 2) ≤
          D * N ^ ε * CubicSieve.sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  obtain ⟨D, hD, hb⟩ := cubic_product_row_bound_of_sieve ε hε
  refine ⟨D, hD, ?_⟩
  intro N L hN pairs Jset Pset mBad hmap hJ hP a
  exact hb N hN pairs Jset Pset mBad (CubicSieve.sieveNorm N L) hmap hJ
    (finite_inverse_cubic_energy Jset Pset N L hJ hP) a

theorem hybrid_fixed_block_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X N L : ℝ, 1 ≤ K → 1 ≤ X → 1 ≤ N →
    ∀ (rows : Finset (Ideal Eis)) (pairs cubicPairs : Finset (Ideal Eis × Ideal Eis))
      (Hset Jset Pset : Finset (Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B mBad : Ideal Eis) (cset : Ideal Eis → Finset (Ideal Eis))
      (coef : Ideal Eis → Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
      (Cbound Ebound : ℝ), 0 ≤ Cbound →
      (∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1) →
      (∀ p ∈ pairs, p.2 ∈ Hset) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ cubicPairs) →
      (∀ u ∈ cubicPairs, u.2 * (mBad * u.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      (∀ h ∈ Hset, (∑ P ∈ Pset, ‖coef h P‖ ^ 2) ≤ Ebound) →
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) *
          (∑ c ∈ cset p.1, beta c p.1 p.2 *
            (∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))))‖ ^ 2) ≤
      C * (K * X * N) ^ ε * (K + X) * Cbound * (Hset.card : ℝ) *
        CubicSieve.sieveNorm N L * Ebound := by
  obtain ⟨Cq, hCq, hquad⟩ := hybrid_quadratic_reduction ε hε
  obtain ⟨D, hD, hcube⟩ := cubic_product_row_sieve_norm ε hε
  refine ⟨Cq * D, mul_pos hCq hD, ?_⟩
  intro K X N L hK hX hN rows pairs cubicPairs Hset Jset Pset hrows hpairs
    B mBad cset coef beta Cbound Ebound hCbound hcount hbeta hH hmc hmap hJ hP hcoef
  let E (h m c : Ideal Eis) := ‖∑ P ∈ Pset,
    coef h P * inverseCubicKernel P (c * (mBad * m))‖ ^ 2
  have hnorm : 0 ≤ CubicSieve.sieveNorm N L := sq_nonneg _
  have he := hquad K X hK hX rows pairs hrows hpairs B mBad cset Pset coef beta
    Cbound hcount hbeta
  have hpos := positive_triple_enlarge pairs cset Hset cubicPairs E hH hmc
    (fun _ _ _ => sq_nonneg _)
  have htotal : (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) ≤
      (Hset.card : ℝ) * (D * N ^ ε * CubicSieve.sieveNorm N L * Ebound) := by
    apply hpos.trans
    calc
      _ ≤ ∑ _h ∈ Hset, D * N ^ ε * CubicSieve.sieveNorm N L * Ebound := by
        apply Finset.sum_le_sum
        intro h hh
        apply (hcube N L hN cubicPairs Jset Pset mBad hmap hJ hP (coef h)).trans
        exact mul_le_mul_of_nonneg_left (hcoef h hh)
          (mul_nonneg (mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)) hnorm)
      _ = _ := by simp
  apply he.trans
  calc
    _ ≤ (Cq * (K * X) ^ ε * (K + X) * Cbound) *
        ((Hset.card : ℝ) * (D * N ^ ε * CubicSieve.sieveNorm N L * Ebound)) := by
      apply mul_le_mul_of_nonneg_left htotal
      positivity
    _ = _ := by
      rw [Real.mul_rpow (show 0 ≤ K * X by positivity) (show 0 ≤ N by linarith)]
      ring

end
end SevenEighths.InverseMoment

end OAI

end Source1445

/- Original source: OAI/NumberTheory/DirichletL/Descent/OriginalBlock.lean; sha256: cbae7f5606c2599793d32efd9e1269005dcc4d090c36c2eea075f0a4de23f456 -/
section Source1446
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_original_quotient_block (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X N L A H : ℝ,
      1 ≤ K → 1 ≤ X → 1 ≤ N → 1 ≤ A → 1 ≤ H →
    ∀ (R r t : Ideal Eis), R ≠ 0 → r ≠ 0 →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis))
      (cset : Ideal Eis → Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧
        L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧
        (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
      (∀ p ∈ pairs, p.2 ≠ 0 ∧ (Ideal.absNorm p.2 : ℝ) ≤ H) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1,
        c ≠ 0 ∧ (Ideal.absNorm c : ℝ) ≤ A ∧ (r * c) * p.1 ∈ nset) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta (r * c) p.1 p.2‖ ≤ 1) →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖(Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
          (∑ p ∈ pairs, quadraticRow k (primaryGenerator (p.1 * p.2)) *
            (∑ c ∈ cset p.1, hybridColumnCoefficient R r beta c p.1 p.2 *
              (∑ P ∈ quotientSupport R Pset,
                hybridCubicCoefficient R r p.2 t a P * inverseCubicKernel P (c * p.1))))‖ ^ 2) ≤
      C * (K * X * N) ^ ε * (K + X) * A * H /
        (Ideal.absNorm R : ℝ) * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C, hC, hblock⟩ := hybrid_fixed_block_sieve_norm ε hε
  refine ⟨C * (128 * 128 * 256), by positivity, ?_⟩
  intro K X N L A H hK hX hN hA hH R r t hR hr rows nset Pset pairs cset a beta
    hrows hn hP ha hpairs hhs hcs hbeta
  let Hset := pairs.image Prod.snd
  let mc := (pairs.image Prod.fst).biUnion fun m => (cset m).image fun c => (m, c)
  have hRr : R * r ≠ 0 := mul_ne_zero hR hr
  have hn0 : ∀ n ∈ nset, n ≠ 0 := fun n hn' => (hn n hn').1.1.ne_zero
  have hP0 : ∀ P ∈ Pset, P ≠ 0 := fun P hP' => (hP P hP').1.1.ne_zero
  have hHcount : (Hset.card : ℝ) ≤ 128 * H := by
    apply DescentFiberCost.finite_ideal_count_real Hset H hH
    · intro h hh
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
      exact (hhs p hp).1
    · intro h hh
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
      exact (hhs p hp).2
  have hcCount : ∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ 128 * A := by
    intro p hp
    exact DescentFiberCost.finite_ideal_count_real (cset p.1) A hA
      (fun c hc => (hcs p hp c hc).1) (fun c hc => (hcs p hp c hc).2.1)
  have hmc : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc := by
    intro p hp c hc
    exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
  have hmap : ∀ u ∈ mc, u.2 * (1 * u.1) ∈ quotientSupport r nset := by
    intro u hu
    obtain ⟨m, hm, cu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp cu
    apply (mem_quotientSupport r (c * (1 * p.1)) hr nset).mpr
    simpa only [one_mul, mul_assoc] using (hcs p hp c hc).2.2
  have he := hblock K X N (2 * L) hK hX hN
    (quotientSupport (R * r) rows) pairs mc Hset (quotientSupport r nset)
    (quotientSupport R Pset)
    (fun k hk => ⟨quotientSupport_quadratic_admissible (R * r) hRr rows
        (fun k hk => (hrows k hk).1) k hk,
      quotientSupport_norm_le (R * r) hRr rows K
        (fun k hk => (hrows k hk).1.1) (fun k hk => (hrows k hk).2) k hk⟩)
    hpairs 1 1 cset (fun h => hybridCubicCoefficient R r h t a)
    (hybridColumnCoefficient R r beta) (128 * A) 256 (by positivity) hcCount
    (fun p hp c hc => hybridColumnCoefficient_norm_le_one R r c p.1 p.2 beta (hbeta p hp c hc))
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) hmc hmap
    (fun J hJ => ⟨quotientSupport_cubic_admissible r hr nset (fun n hn' => (hn n hn').1) J hJ,
      quotientSupport_norm_le r hr nset N hn0 (fun n hn' => (hn n hn').2) J hJ⟩)
    (fun P hP' => ⟨quotientSupport_cubic_admissible R hR Pset (fun P hP' => (hP P hP').1) P hP',
      quotientSupport_norm_le R hR Pset (2 * L) hP0 (fun P hP' => (hP P hP').2.2) P hP'⟩)
    (fun h _ => quotient_hybridCubicCoefficient_energy R r h t hR Pset L hP0
      (fun P hP' => (hP P hP').2) a ha)
  simp only [one_mul] at he
  have hsqrt : ‖(Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹‖ ^ 2 =
      (Ideal.absNorm R : ℝ)⁻¹ := by
    rw [norm_inv, inv_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
  simp_rw [norm_mul, mul_pow, hsqrt]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Nat.cast_nonneg _))).trans
  calc
    _ ≤ (Ideal.absNorm R : ℝ)⁻¹ *
      (C * (K * X * N) ^ ε * (K + X) * (128 * A) * (128 * H) *
        CubicSieve.sieveNorm N (2 * L) * 256) := by
      gcongr
      exact sq_nonneg _
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI

end Source1446

/- Original source: OAI/NumberTheory/DirichletL/Descent/DyadicBlock.lean; sha256: acc030a4fa3d2b04e2747bc51d981c1b4a6e372390aa1cea7e2676f7b8d8c9eb -/
section Source1447
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_extracted_dyadic_block_nonempty (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L C T : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (R r t : Ideal Eis), R ≠ 0 → r ≠ 0 → T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (D : Finset HybridColumnData)
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (quotientGridSupport r (hybridGridSupport D)).Nonempty →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₀ * (K * (N * B) * N) ^ ε * (K + N * B) * B /
        ((Ideal.absNorm R : ℝ) * (Ideal.absNorm r : ℝ) * T ^ 2) *
          CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C₁, hC₁, hblock⟩ := hybrid_original_quotient_block ε hε
  refine ⟨2 * C₁, by positivity, ?_⟩
  intro K N B L C T hK hN hB hC hT R r t hR hr ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta hQ
  let Q := quotientGridSupport r (hybridGridSupport D)
  let X := N * B / (C ^ 2 * T ^ 2)
  let A := 2 * C / (Ideal.absNorm r : ℝ)
  let H := B / (C * T ^ 2)
  have hC0 : 0 < C := by linarith
  have hT0 : 0 < T := by linarith
  have hnr : 0 < (Ideal.absNorm r : ℝ) := QuadraticMainBoundary.norm_pos hr
  have hnorm (d : HybridColumnData) (hd : d ∈ D) :
      (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
      (Ideal.absNorm d.residualB : ℝ) ≤ H ∧
      (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ X := by
    have hd' := hD d hd
    apply d.residual_norm_bounds N B C T (by linarith) (by linarith) hC0 hT0
      (hn _ hd'.2.2.2.1).2 hd'.2.2.2.2 hd'.2.1
    simpa only [hd'.1] using ht
  have hcBound (d : HybridColumnData) (hd : d ∈ D) (c : Ideal Eis)
      (hdc : d.common = r * c) : c ≠ 0 ∧ (Ideal.absNorm c : ℝ) ≤ A := by
    have hcz : c ≠ 0 := by
      intro hz
      apply d.common_ne_zero
      simp [hdc, hz]
    refine ⟨hcz, (le_div_iff₀ hnr).mpr ?_⟩
    have hdcN := (hD d hd).2.2.1
    rw [hdc, map_mul, Nat.cast_mul] at hdcN
    simpa only [mul_comm] using hdcN
  have hpair (p : Ideal Eis × Ideal Eis) (hp : p ∈ Q.image Prod.fst) :
      Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X ∧
      p.2 ≠ 0 ∧ (Ideal.absNorm p.2 : ℝ) ≤ H := by
    obtain ⟨u, hu, hup⟩ := Finset.mem_image.mp hp
    obtain ⟨d, hd, he, hdc⟩ := quotientGridSupport_origin r hr D u.1 u.2 hu
    have he' : (d.residualN, d.residualB) = p := he.trans hup
    have hm := congrArg Prod.fst he'
    have hh := congrArg Prod.snd he'
    have hdB : d.residualB ≠ 0 :=
      ne_zero_of_dvd_ne_zero d.g_squarefree.ne_zero (dvd_mul_left _ _)
    exact ⟨by simpa only [← hm, ← hh] using d.residual_product_squarefree,
      by simpa only [← hm, ← hh] using (hnorm d hd).2.2,
      by simpa only [← hh] using hdB,
      by simpa only [← hh] using (hnorm d hd).2.1⟩
  have hcset (p : Ideal Eis × Ideal Eis) (hp : p ∈ Q.image Prod.fst)
      (c : Ideal Eis) (hc : c ∈ gridCommonSupport Q p.1) :
      c ≠ 0 ∧ (Ideal.absNorm c : ℝ) ≤ A ∧ (r * c) * p.1 ∈ nset := by
    obtain ⟨d, hd, hm, hdc⟩ := quotientGridCommonSupport_origin r hr D p.1 c hc
    have hc' := hcBound d hd c hdc
    exact ⟨hc'.1, hc'.2, by simpa only [hdc, hm] using (hD d hd).2.2.2.1⟩
  obtain ⟨u₀, hu₀⟩ := hQ
  have hp₀ : u₀.1 ∈ Q.image Prod.fst := Finset.mem_image.mpr ⟨u₀, hu₀, rfl⟩
  have hc₀ : u₀.2 ∈ gridCommonSupport Q u₀.1.1 :=
    Finset.mem_image.mpr ⟨u₀, Finset.mem_filter.mpr ⟨hu₀, rfl⟩, rfl⟩
  have hX : 1 ≤ X :=
    (QuadraticMainBoundary.norm_one_le (hpair u₀.1 hp₀).1.ne_zero).trans (hpair u₀.1 hp₀).2.1
  have hH : 1 ≤ H :=
    (QuadraticMainBoundary.norm_one_le (hpair u₀.1 hp₀).2.2.1).trans (hpair u₀.1 hp₀).2.2.2
  have hA : 1 ≤ A :=
    (QuadraticMainBoundary.norm_one_le (hcset u₀.1 hp₀ u₀.2 hc₀).1).trans
      (hcset u₀.1 hp₀ u₀.2 hc₀).2.1
  have hbGrid : ∀ u ∈ hybridGridSupport D, ‖beta u.2 u.1.1 u.1.2‖ ≤ 1 := by
    intro u hu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
    exact hbeta d hd
  have he := hblock K X N L A H hK hX hN hA hH R r t hR hr rows nset Pset
    (Q.image Prod.fst) (gridCommonSupport Q) a
    (extractedGridCoefficient (hybridGridSupport D) R t beta)
    hrows hn hP ha (fun p hp => ⟨(hpair p hp).1, (hpair p hp).2.1⟩)
    (fun p hp => (hpair p hp).2.2) hcset
    (fun p _ c _ => extractedGridCoefficient_norm_le_one _ R t beta hbGrid (r * c) p.1 p.2)
  have hrow (k : Ideal Eis) (hk : k ∈ quotientSupport (R * r) rows) :=
    gridDivisorHybridBlock_extract (hybridGridSupport D) Pset a beta t k R r hR hr
      (hrows _ ((mem_quotientSupport (R * r) k (mul_ne_zero hR hr) rows).mp hk)).1
      (fun P hP' => (hP P hP').1)
  have he' : (∑ k ∈ quotientSupport (R * r) rows,
      ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₁ * (K * X * N) ^ ε * (K + X) * A * H /
        (Ideal.absNorm R : ℝ) * CubicSieve.sieveNorm N (2 * L) := by
    calc
      _ = _ := Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hrow k hk))
      _ ≤ _ := he
  have hXupper : X ≤ N * B := by
    apply div_le_self (by positivity : 0 ≤ N * B)
    have hC2 : 1 ≤ C ^ 2 := one_le_pow₀ hC
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
    exact one_le_mul_of_one_le_of_one_le hC2 hT2
  apply he'.trans
  calc
    _ ≤ C₁ * (K * (N * B) * N) ^ ε * (K + N * B) * A * H /
        (Ideal.absNorm R : ℝ) * CubicSieve.sieveNorm N (2 * L) := by
      have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
      gcongr
    _ = _ := by
      dsimp only [A, H]
      field_simp

theorem hybrid_extracted_dyadic_block (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L C T : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (R r t : Ideal Eis), R ≠ 0 → r ≠ 0 → T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (D : Finset HybridColumnData)
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₀ * (K * (N * B) * N) ^ ε * (K + N * B) * B /
        ((Ideal.absNorm R : ℝ) * (Ideal.absNorm r : ℝ) * T ^ 2) *
          CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C₀, hC₀, he⟩ := hybrid_extracted_dyadic_block_nonempty ε hε
  refine ⟨C₀, hC₀, ?_⟩
  intro K N B L C T hK hN hB hC hT R r t hR hr ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta
  by_cases hQ : (quotientGridSupport r (hybridGridSupport D)).Nonempty
  · exact he K N B L C T hK hN hB hC hT R r t hR hr ht
      rows nset Pset D a beta hrows hn hP ha hD hbeta hQ
  · have hQ' := Finset.not_nonempty_iff_eq_empty.mp hQ
    simp only [gridDivisorHybridBlock_eq_zero_of_quotientGrid_empty _ _ _ _ _ _ _ _ hQ',
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero]
    have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
    positivity

end
end SevenEighths.InverseMoment

end OAI

end Source1447

/- Original source: OAI/NumberTheory/DirichletL/Descent/MaskedGrid.lean; sha256: 669b686445b5f3fe31f35616165458e24a74a6741f6e26faa68e289d59eceab5 -/
section Source1448
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum UniqueFactorizationMonoid
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "Grid" => Finset ((Ideal Eis × Ideal Eis) × Ideal Eis)

def maskedGridHybridRow (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k : Ideal Eis) : ℂ :=
  ∑ u ∈ T, ∑ P ∈ Pset, (if IsCoprime k (P * u.2) then 1 else 0) *
    (a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta u.2 u.1.1 u.1.2 *
      (quadraticRow k (primaryGenerator (u.1.1 * u.1.2)) * inverseCubicKernel P (u.2 * u.1.1)) *
        (if IsCoprime P (u.1.2 * t) then 1 else 0))

theorem maskedGridHybridRow_mobius (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k : Ideal Eis) (hk : k ≠ 0) :
    maskedGridHybridRow T Pset a beta t k =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        ((moebius D.1 : ℂ) * (moebius D.2 : ℂ)) *
          gridDivisorHybridBlock T Pset a beta t k D.1 D.2 := by
  have hm (P c : Ideal Eis) :
      (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        if D.1 ∣ P ∧ D.2 ∣ c then (moebius D.1 : ℂ) * (moebius D.2 : ℂ) else 0 := by
    rw [hybrid_double_mask_mobius k P c hk, Finset.sum_product]
  unfold maskedGridHybridRow
  simp_rw [hm, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  unfold gridDivisorHybridBlock
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hrc : D.2 ∣ u.2
  · simp only [hrc, ite_true, and_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hRP : D.1 ∣ P <;> simp [hRP]
  · simp [hrc]

theorem gridDivisorHybridBlock_zero_of_not_coprime
    (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) (hRr : ¬ IsCoprime R r)
    (hP : ∀ P ∈ Pset, primaryGenerator P ≠ 0)
    (hT : ∀ u ∈ T, primaryGenerator (u.2 * u.1.1) ≠ 0) :
    gridDivisorHybridBlock T Pset a beta t k R r = 0 := by
  unfold gridDivisorHybridBlock
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hrc : r ∣ u.2
  · simp only [hrc, ite_true]
    apply Finset.sum_eq_zero
    intro P hPP
    by_cases hRP : R ∣ P
    · simp only [hRP, ite_true]
      rw [inverseCubicKernel_divisor_overlap_zero R r P u.2 u.1.1
        (hP P hPP) (hT u hu) hRP hrc hRr]
      simp
    · simp only [hRP, ite_false]
  · simp only [hrc, ite_false]

theorem maskedGridHybridRow_divisor_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
    ∀ (rows : Finset (Ideal Eis)) (T : Grid) (Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (t : Ideal Eis),
      (∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∑ k ∈ rows, ‖maskedGridHybridRow T Pset a beta t k‖ ^ 2) ≤
        C * K ^ ε *
          ∑ D ∈ rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)),
            ∑ k ∈ rows, if D ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
              ‖gridDivisorHybridBlock T Pset a beta t k D.1 D.2‖ ^ 2 else 0 := by
  obtain ⟨C, hC, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨C ^ 2, pow_pos hC 2, ?_⟩
  intro K hK rows T Pset a beta t hrows
  have he (k : Ideal Eis) (hk : k ∈ rows) :=
    maskedGridHybridRow_mobius T Pset a beta t k (hrows k hk).1
  simp_rw [Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (he k hk))]
  apply finite_expansion_energy rows
    (rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)))
    (fun k => (idealDivisors k) ×ˢ (idealDivisors k))
    (fun _ D => (moebius D.1 : ℂ) * (moebius D.2 : ℂ))
    (fun k D => gridDivisorHybridBlock T Pset a beta t k D.1 D.2) (C ^ 2 * K ^ ε)
  · intro k hk D hD
    exact Finset.mem_biUnion.mpr ⟨k, hk, hD⟩
  · intro k hk D hD
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul
        (QuadraticInitialBound.norm_ideal_moebius_le_one D.1)
        (QuadraticInitialBound.norm_ideal_moebius_le_one D.2) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · intro k hk
    have hd := (hdiv k (hrows k hk).1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hrows k hk).2 (by positivity)) hC.le)
    calc
      _ = ((idealDivisors k).card : ℝ) ^ 2 := by simp [Finset.card_product, pow_two]
      _ ≤ (C * K ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
      _ = C ^ 2 * K ^ ε := by
        rw [mul_pow, pow_two (K ^ (ε / 2)), ← Real.rpow_add (by linarith : 0 < K)]
        congr 1
        congr 1
        ring

end
end SevenEighths.InverseMoment

end OAI

end Source1448

/- Original source: OAI/NumberTheory/DirichletL/Descent/DivisorSum.lean; sha256: 62b93afc6c8154ae4a145b20d6ca7b1c04fe9a592210d8b29d3d629ec4c4aa92 -/
section Source1449
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def hybridDivisorPool (rows : Finset (Ideal Eis)) : Finset (Ideal Eis) :=
  rows.biUnion idealDivisors

def hybridDivisorPairPool (rows : Finset (Ideal Eis)) : Finset (Ideal Eis × Ideal Eis) :=
  rows.biUnion fun k => (idealDivisors k) ×ˢ (idealDivisors k)

theorem hybridDivisorPool_bounds (rows : Finset (Ideal Eis)) (K : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K)
    (D : Ideal Eis) (hD : D ∈ hybridDivisorPool rows) :
    D ≠ 0 ∧ (Ideal.absNorm D : ℝ) ≤ K := by
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  have hdiv := (mem_idealDivisors (hrows k hk).1).mp hDk
  exact ⟨ne_zero_of_dvd_ne_zero (hrows k hk).1 hdiv,
    (QuadraticMainBoundary.norm_le_of_dvd (hrows k hk).1 hdiv).trans (hrows k hk).2⟩

theorem hybridDivisorPairPool_subset (rows : Finset (Ideal Eis)) :
    hybridDivisorPairPool rows ⊆ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows) := by
  intro D hD
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  exact Finset.mem_product.mpr
    ⟨Finset.mem_biUnion.mpr ⟨k, hk, (Finset.mem_product.mp hDk).1⟩,
      Finset.mem_biUnion.mpr ⟨k, hk, (Finset.mem_product.mp hDk).2⟩⟩

theorem hybrid_divisor_pair_inverse_norm_sum
    (rows : Finset (Ideal Eis)) (K : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) :
    (∑ D ∈ hybridDivisorPairPool rows,
      1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ))) ≤
      (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2 := by
  have hb := hybridDivisorPool_bounds rows K hrows
  have hsum := finite_inverse_norm_sum (hybridDivisorPool rows) K
    (fun D hD => (hb D hD).1) (fun D hD => (hb D hD).2)
  calc
    _ ≤ ∑ D ∈ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows),
        1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (hybridDivisorPairPool_subset rows)
      intro D hD hn
      positivity
    _ = (∑ D ∈ hybridDivisorPool rows, 1 / (Ideal.absNorm D : ℝ)) ^ 2 := by
      rw [Finset.sum_product, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro R hR
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hsum 2

end
end SevenEighths.InverseMoment

end OAI

end Source1449

/- Original source: OAI/NumberTheory/DirichletL/Descent/FixedSquare.lean; sha256: 2c51ab31e4c177e19974ccb257bdf0f9d5a29bef4f199261c7370ac44f23694e -/
section Source1450
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_fixed_square_grid_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L C T : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (t : Ideal Eis), T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (D : Finset HybridColumnData)
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (∑ k ∈ rows, ‖maskedGridHybridRow (hybridGridSupport D) Pset a beta t k‖ ^ 2) ≤
      C₀ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B / T ^ 2 *
        CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2 := by
  obtain ⟨C₁, hC₁, hblock⟩ := hybrid_extracted_dyadic_block ε hε
  obtain ⟨C₂, hC₂, hmask⟩ := maskedGridHybridRow_divisor_energy ε hε
  refine ⟨C₁ * C₂ * 256 ^ 2, by positivity, ?_⟩
  intro K N B L C T hK hN hB hC hT t ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta
  have hr0 : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K :=
    fun k hk => ⟨(hrows k hk).1.1, (hrows k hk).2⟩
  let E := C₁ * (K * (N * B) * N) ^ ε * (K + N * B) * B / T ^ 2 *
    CubicSieve.sieveNorm N (2 * L)
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hTprim : ∀ u ∈ hybridGridSupport D, primaryGenerator (u.2 * u.1.1) ≠ 0 := by
    intro u hu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
    exact (hn _ (hD d hd).2.2.2.1).1.2
  have hterm (v : Ideal Eis × Ideal Eis) (hv : v ∈ hybridDivisorPairPool rows) :
      (∑ k ∈ rows, if v ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t k v.1 v.2‖ ^ 2 else 0) ≤
      E * (1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ))) := by
    have hp := Finset.mem_product.mp (hybridDivisorPairPool_subset rows hv)
    have hR := (hybridDivisorPool_bounds rows K hr0 v.1 hp.1).1
    have hr := (hybridDivisorPool_bounds rows K hr0 v.2 hp.2).1
    by_cases hcop : IsCoprime v.1 v.2
    · rw [double_divisor_row_reindex rows (fun k hk => (hr0 k hk).1) v.1 v.2 hcop]
      have he := hblock K N B L C T hK hN hB hC hT v.1 v.2 t hR hr ht
        rows nset Pset D a beta hrows hn hP ha hD hbeta
      convert he using 1
      dsimp only [E]
      field_simp
    · simp only [gridDivisorHybridBlock_zero_of_not_coprime _ _ _ _ _ _ _ _ hcop
          (fun P hPP => (hP P hPP).1.2) hTprim,
        norm_zero, zero_pow (by norm_num : 2 ≠ 0), ite_self, Finset.sum_const_zero]
      exact mul_nonneg hE (by positivity)
  have he := hmask K hK rows (hybridGridSupport D) Pset a beta t hr0
  have hsum : (∑ v ∈ hybridDivisorPairPool rows,
      ∑ k ∈ rows, if v ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t k v.1 v.2‖ ^ 2 else 0) ≤
      E * (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ v ∈ hybridDivisorPairPool rows,
          E * (1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ))) :=
        Finset.sum_le_sum hterm
      _ = E * ∑ v ∈ hybridDivisorPairPool rows,
          1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hybrid_divisor_pair_inverse_norm_sum rows K hr0) hE
  apply he.trans
  calc
    _ ≤ C₂ * K ^ ε * (E * (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp only [E]; ring

end
end SevenEighths.InverseMoment

end OAI

end Source1450

/- Original source: OAI/NumberTheory/DirichletL/Descent/SourceHybrid.lean; sha256: ac0fabf6238766c0b426e7987abd0f5af2bf9fc3b601e06fb418a6aefd1d5469 -/
section Source1451
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def sourceGridCoefficient (beta : Ideal Eis → Ideal Eis → ℂ)
    (t c m h : Ideal Eis) : ℂ := beta (c * m) ((c * h) * t ^ 2)

theorem reconstructed_fixed_square_grid
    (D : Finset HybridColumnData) (t : Ideal Eis) (hD : ∀ d ∈ D, d.square = t)
    (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) :
    (∑ d ∈ D, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d) =
      (if IsCoprime k t then 1 else 0) *
        maskedGridHybridRow (hybridGridSupport D) Pset a (sourceGridCoefficient beta t) t k := by
  unfold maskedGridHybridRow hybridGridSupport
  rw [Finset.sum_image]
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro P hP
    simp only [reconstructedHybridTerm, HybridColumnData.gridIndex,
      sourceGridCoefficient, hD d hd]
    ac_rfl
  · intro d hd e he hg
    exact HybridColumnData.gridIndex_injective_on_square t (hD d hd) (hD e he) hg

theorem reconstructed_fixed_square_energy_le
    (D : Finset HybridColumnData) (t : Ideal Eis) (hD : ∀ d ∈ D, d.square = t)
    (rows Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) :
    (∑ k ∈ rows, ‖∑ d ∈ D, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d‖ ^ 2) ≤
      ∑ k ∈ rows,
        ‖maskedGridHybridRow (hybridGridSupport D) Pset a (sourceGridCoefficient beta t) t k‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  rw [reconstructed_fixed_square_grid D t hD Pset a beta k]
  by_cases hkt : IsCoprime k t
  · simp only [hkt, ite_true, one_mul, le_refl]
  · simp only [hkt, ite_false, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact sq_nonneg _

theorem finite_double_row_energy {I J : Type*} [Fintype I] [Fintype J]
    (rows : Finset (Ideal Eis)) (F : I → J → Ideal Eis → ℂ) (E : ℝ) (_hE : 0 ≤ E)
    (hF : ∀ i j, (∑ k ∈ rows, ‖F i j k‖ ^ 2) ≤ E) :
    (∑ k ∈ rows, ‖∑ i, ∑ j, F i j k‖ ^ 2) ≤
      ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) ^ 2 * E := by
  have hk (k : Ideal Eis) :
      ‖∑ i, ∑ j, F i j k‖ ^ 2 ≤
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
          ∑ i, ∑ j, ‖F i j k‖ ^ 2 := by
    simpa only [one_mul, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul] using
      bounded_coefficient_sum_sq (fun _ : I × J => 1) (fun u => F u.1 u.2 k) (by simp)
  calc
    _ ≤ ∑ k ∈ rows, ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
        ∑ i, ∑ j, ‖F i j k‖ ^ 2 := Finset.sum_le_sum (fun k _ => hk k)
    _ = ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
        ∑ i, ∑ j, ∑ k ∈ rows, ‖F i j k‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ ≤ ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) * ∑ _i : I, ∑ _j : J, E := by
      gcongr with i hi j hj
      exact hF i j
    _ = _ := by simp; ring

theorem supportedHybridRow_energy_log (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows : Finset (Ideal Eis)) (S : Finset (Ideal Eis × Ideal Eis))
      (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ S, Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ p ∈ S, ‖beta p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖supportedHybridRow S Pset a beta k‖ ^ 2) ≤
      C₀ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B *
        CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2 *
          (columnDyadicLength N + 1 : ℝ) ^ 2 * (columnDyadicLength B + 1 : ℝ) ^ 2 := by
  obtain ⟨C₁, hC₁, hfixed⟩ := hybrid_fixed_square_grid_energy ε hε
  refine ⟨256 ^ 2 * C₁, by positivity, ?_⟩
  intro K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  let nset := S.image Prod.fst
  let E := C₁ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B *
    CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2
  let F (j : Fin (columnDyadicLength B + 1)) (i : Fin (columnDyadicLength N + 1))
      (k : Ideal Eis) : ℂ :=
    ∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
      ∑ d ∈ hybridCommonBlock S N i t, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hnset : ∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨⟨(hS p hp).1, (hS p hp).2.1⟩, (hS p hp).2.2.2.1⟩
  have hBsup : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B := fun p hp => (hS p hp).2.2.2.2
  have hlen : ∀ p ∈ S, (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B :=
    fun p hp => (hS p hp).2.2.2
  have hlabel (j : Fin (columnDyadicLength B + 1))
      (i : Fin (columnDyadicLength N + 1)) :
      (∑ k ∈ rows, ‖F j i k‖ ^ 2) ≤ 256 ^ 2 * E := by
    let Td := divisorDyadicScale j.val
    have hTd : 0 < Td := by dsimp only [Td]; linarith [divisorDyadicScale_ge_one j.val]
    have htEnergy (t : Ideal Eis) (ht : t ∈ divisorDyadicBin (hybridSquarePool S) B j) :
        (∑ k ∈ rows, ‖∑ d ∈ hybridCommonBlock S N i t,
          ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d‖ ^ 2) ≤ E / Td ^ 2 := by
      let D := hybridCommonBlock S N i t
      have hD (d : HybridColumnData) (hd : d ∈ D) :
          d.square = t ∧ divisorDyadicScale i.val ≤ (Ideal.absNorm d.common : ℝ) ∧
          (Ideal.absNorm d.common : ℝ) ≤ 2 * divisorDyadicScale i.val ∧
          d.common * d.residualN ∈ nset ∧
          (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B := by
        obtain ⟨hdS, hdt, hdi⟩ := Finset.mem_filter.mp hd
        have hdorig := (mem_hybridColumnSupport S d).mp hdS
        have hb := hybridCommonBlock_bounds S N B (by linarith) (by linarith) hlen i j t ht d hd
        exact ⟨hdt, hb.1, hb.2.1, Finset.mem_image.mpr ⟨d.reconstruct, hdorig, rfl⟩,
          hBsup d.reconstruct hdorig⟩
      have hβ : ∀ d ∈ D, ‖sourceGridCoefficient beta t d.common d.residualN d.residualB‖ ≤ 1 := by
        intro d hd
        have hdo := (mem_hybridColumnSupport S d).mp (Finset.mem_filter.mp hd).1
        simpa only [sourceGridCoefficient, ← (hD d hd).1, HybridColumnData.reconstruct] using
          hbeta d.reconstruct hdo
      have hfix := hfixed K N B L (divisorDyadicScale i.val) Td hK hN hB
        (divisorDyadicScale_ge_one i.val) (divisorDyadicScale_ge_one j.val) t
        (divisorDyadicBin_bounds (hybridSquarePool S) B (hybridSquarePool_bounds S B hBsup) j t ht).1
        rows nset Pset D a (sourceGridCoefficient beta t) hrows hnset hP ha hD hβ
      apply (reconstructed_fixed_square_energy_le D t (fun d hd => (hD d hd).1) rows Pset a beta).trans
      convert hfix using 1 ; dsimp only [E] ; ring
    have he := hybrid_square_dyad_energy S B hBsup j rows
      (fun t k => ∑ d ∈ hybridCommonBlock S N i t,
        ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d)
      (E / Td ^ 2) (div_nonneg hE (sq_nonneg _)) htEnergy
    calc
      _ ≤ (256 * Td) ^ 2 * (E / Td ^ 2) := he
      _ = 256 ^ 2 * E := by field_simp
  have hrow (k : Ideal Eis) (hk : k ∈ rows) :
      supportedHybridRow S Pset a beta k = ∑ j, ∑ i, F j i k := by
    rw [supportedHybridRow_reconstruct S Pset
      (fun p hp => ⟨(hS p hp).1,
        primaryGenerator_ne_zero_ideal p.2 (hS p hp).2.2.1,
        (hS p hp).2.1, (hS p hp).2.2.1⟩)
      (fun P hPP => (hP P hPP).1.2) a beta k (hrows k hk).1]
    exact hybrid_dyadic_reindex S N B _
  calc
    _ = ∑ k ∈ rows, ‖∑ j, ∑ i, F j i k‖ ^ 2 :=
      Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hrow k hk))
    _ ≤ ((Fintype.card (Fin (columnDyadicLength B + 1)) : ℝ) *
        (Fintype.card (Fin (columnDyadicLength N + 1)) : ℝ)) ^ 2 * (256 ^ 2 * E) :=
      finite_double_row_energy rows F (256 ^ 2 * E) (by positivity) hlabel
    _ = _ := by simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, E]; ring

end
end SevenEighths.InverseMoment

end OAI

end Source1451

/- Original source: OAI/NumberTheory/DirichletL/Descent/HybridBound.lean; sha256: e11e3939ce1dc7d7ed14407cdd3462c9d8554a681cdb38d73eae7a57f803a99c -/
section Source1452
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

private theorem hybrid_log_cost_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
      K ^ (ε / 9) * (K * (N * B) * N) ^ (ε / 9) *
        (columnDyadicLength K + 1 : ℝ) ^ 2 * (columnDyadicLength N + 1 : ℝ) ^ 2 *
          (columnDyadicLength B + 1 : ℝ) ^ 2 ≤ C * (K * N * B) ^ ε := by
  let δ := ε / 9
  let A := 2 + 1 / (δ * Real.log 2)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A ^ 6, pow_pos hA 6, ?_⟩
  intro K N B hK hN hB
  let Q := K * N * B
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hK hN) hB
  have hQ0 : 0 < Q := by linarith
  have hKQ : K ≤ Q :=
    (le_mul_of_one_le_right (by linarith : 0 ≤ K) hN).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ K * N) hB)
  have hNQ : N ≤ Q :=
    (le_mul_of_one_le_left (by linarith : 0 ≤ N) hK).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ K * N) hB)
  have hBQ : B ≤ Q := le_mul_of_one_le_left (by linarith)
    (one_le_mul_of_one_le_of_one_le hK hN)
  have hquad : K * (N * B) * N ≤ Q ^ 2 := by
    calc
      _ = Q * N := by dsimp only [Q]; ring
      _ ≤ Q * Q := mul_le_mul_of_nonneg_left hNQ hQ0.le
      _ = _ := by ring
  have hlog (Y : ℝ) (hY : 1 ≤ Y) (hYQ : Y ≤ Q) :
      (columnDyadicLength Y + 1 : ℝ) ≤ A * Q ^ δ := by
    exact (columnDyadicLength_small_power δ hδ Y hY).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hYQ hδ.le) hA.le)
  have hpow2 : (Q ^ 2) ^ δ = (Q ^ δ) ^ 2 := by
    rw [← Real.rpow_natCast_mul hQ0.le 2 δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    congr 1
    ring
  have hpow9 : (Q ^ δ) ^ 9 = Q ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    congr 1
    dsimp only [δ]
    ring
  calc
    _ ≤ Q ^ δ * (Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 := by
      have hbase := Real.rpow_le_rpow (by positivity : 0 ≤ K * (N * B) * N) hquad hδ.le
      rw [hpow2] at hbase
      gcongr
      · exact hlog K hK hKQ
      · exact hlog N hN hNQ
      · exact hlog B hB hBQ
    _ = A ^ 6 * (Q ^ δ) ^ 9 := by ring
    _ = _ := by rw [hpow9]

theorem supportedHybridRow_energy_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows : Finset (Ideal Eis)) (S : Finset (Ideal Eis × Ideal Eis))
      (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ S, Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ p ∈ S, ‖beta p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖supportedHybridRow S Pset a beta k‖ ^ 2) ≤
      C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C₀, hC₀, he⟩ := supportedHybridRow_energy_log (ε / 9) (by positivity)
  obtain ⟨C₁, hC₁, hlogs⟩ := hybrid_log_cost_bound ε hε
  refine ⟨C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  intro K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  have hb := he K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  apply hb.trans
  calc
    _ = C₀ * (K ^ (ε / 9) * (K * (N * B) * N) ^ (ε / 9) *
        (columnDyadicLength K + 1 : ℝ) ^ 2 * (columnDyadicLength N + 1 : ℝ) ^ 2 *
          (columnDyadicLength B + 1 : ℝ) ^ 2) *
        (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by ring
    _ ≤ C₀ * (C₁ * (K * N * B) ^ ε) * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hlogs K N B hK hN hB) hC₀.le)
            (by positivity)) (by linarith)) hs
    _ = _ := by ring

theorem hybridRow_energy_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows nset bset Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖hybridRow Pset nset bset a beta k‖ ^ 2) ≤
      C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C, hC, he⟩ := supportedHybridRow_energy_sieve_norm ε hε
  refine ⟨C, hC, ?_⟩
  intro K N B L hK hN hB rows nset bset Pset a beta hrows hn hb hP ha hbeta
  have hprod : ∀ p ∈ nset ×ˢ bset,
      Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B := by
    intro p hp
    obtain ⟨hpn, hpb⟩ := Finset.mem_product.mp hp
    exact ⟨(hn p.1 hpn).1.1, (hn p.1 hpn).1.2, (hb p.2 hpb).1,
      (hn p.1 hpn).2, (hb p.2 hpb).2⟩
  have hh := he K N B L hK hN hB rows (nset ×ˢ bset) Pset a beta hrows hprod hP ha
    (fun p hp => hbeta p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2)
  simpa only [supportedHybridRow_product] using hh

end
end SevenEighths.InverseMoment

end OAI

end Source1452

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/FullNorm.lean; sha256: 8d1cce620d9a82caeb4b7a2dfeb6e278a2f51029e3bad43656c64f8a35bbd38a -/
section Source1453
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def elementRange (M : ℝ) : Finset O :=
  (ShortDraftLatticeCount.rowNormBall ⌊M⌋₊).filter
    (fun z => z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)

lemma mem_elementRange (M : ℝ) (z : O) :
    z ∈ elementRange M ↔ z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    apply ShortDraftLatticeCount.mem_rowNormBall_of_qNat_le
    rw [ActualEisensteinCubic.qNat_eq_absNorm_span]
    exact Nat.le_floor h.2

def elementMatrix (M N : ℝ) : Matrix (elementRange M) (idealRange N) ℂ :=
  fun z J => cubicRow J.val z.val

def elementSieveNorm (M N : ℝ) : ℝ := squaredNorm (elementMatrix M N)

lemma elementSieveNorm_nonneg (M N : ℝ) : 0 ≤ elementSieveNorm M N := squaredNorm_nonneg _

theorem element_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => cubicRow (cols j) (rows i)) ≤ elementSieveNorm M N := by
  let r : m → elementRange M := fun i => ⟨rows i, (mem_elementRange M (rows i)).mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (elementMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma sieveNorm_le_elementSieveNorm (M N : ℝ) : sieveNorm M N ≤ elementSieveNorm M N := by
  apply element_family_squared_norm_le
    (fun I : idealRange M => primaryGenerator I.val) (fun J : idealRange N => J.val)
  · intro I J he
    exact Subtype.ext (primaryGenerator_inj_on_cubic_admissible
      (mem_idealRange.mp I.property).1 (mem_idealRange.mp J.property).1 he)
  · exact Subtype.val_injective
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1.2, by
      rw [(primaryGenerator_spec I.val (mem_idealRange.mp I.property).1.2).1]
      exact (mem_idealRange.mp I.property).2⟩
  · intro J
    exact mem_idealRange.mp J.property

lemma elementSieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    elementSieveNorm M N ≤ elementSieveNorm M' N' := by
  apply element_family_squared_norm_le (fun z : elementRange M => z.val)
    (fun I : idealRange N => I.val) Subtype.val_injective Subtype.val_injective
  · intro z
    exact ⟨((mem_elementRange M z.val).mp z.property).1,
      ((mem_elementRange M z.val).mp z.property).2.trans hM⟩
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1, (mem_idealRange.mp I.property).2.trans hN⟩

theorem element_coprime_bilinear_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (hN : 0 ≤ N)
    (rows : m → O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (a b : n → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
      star (cubicRow (cols j) (rows i) * a j) * (cubicRow (cols k) (rows i) * b k) else 0‖) ^ 2 ≤
      (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) *
      (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * ∑ j, ‖b j‖ ^ 2) := by
  have hb := IdealCoprimeBilinearSieve.ideal_coprime_bilinear_operator_bound ε hε cols cols
    (fun j => primaryGenerator_ne_zero_ideal _ (hcols j).1.2)
    (fun j => primaryGenerator_ne_zero_ideal _ (hcols j).1.2)
    N N hN hN (fun j => (hcols j).2) (fun j => (hcols j).2)
    (fun i j => cubicRow (cols j) (rows i)) (fun i j => cubicRow (cols j) (rows i)) a b
  have hn := element_family_squared_norm_le rows cols hr hc M N hrows hcols
  have hfac : 0 ≤ IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε :=
    mul_nonneg (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le (Real.rpow_nonneg hN _)
  apply hb.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hfac) (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hfac) (by positivity)
  · positivity
  · exact mul_nonneg (mul_nonneg (elementSieveNorm_nonneg _ _) hfac) (by positivity)

theorem elementSieveNorm_initial (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    elementSieveNorm M N ≤ QuadraticInitialBound.initialSieveConstant * (M + (⌈N⌉₊ : ℝ) ^ 2) := by
  let F := idealRange N
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  have hFp : ∀ I ∈ F, I ≠ ⊥ := fun I hI => primaryGenerator_ne_zero_ideal I (hF I hI).2
  have hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P :=
    fun I hI P hP => (primaryPrime_spec P
      (primaryPrime_factor_ne_zero I P (hF I hI).2 hP)).2.1
  have hnat : 1 ≤ ⌈N⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ ⌈N⌉₊ := by
    intro I hI
    exact Nat.cast_le.mp ((mem_idealRange.mp hI).2.trans (Nat.le_ceil N))
  have hR : ∀ z ∈ elementRange M, ‖eisEmbedding z‖ ^ 2 ≤ M := by
    intro z hz
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact ((mem_elementRange M z).mp hz).2
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · have hc := (QuadraticInitialBound.initialSieveConstant_pos).le
    positivity
  intro a
  let aext (I : Ideal O) : ℂ := if h : I ∈ F then a ⟨I, h⟩ else 0
  have hinner (z : O) :
      (∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 2) =
        ∑ J : F, cubicRow J.val z * a J := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J hJ
    change aext J.val * (idealSexticRow F hFp hFg J.val z) ^ 2 =
      eisEmbedding (CubicJacobiGlobal.idealSymbol J.val z) * a J
    rw [idealSymbol_eq_idealSexticRow_sq F hFp hFg J.val J.property (hF J.val J.property).1 z]
    simp only [aext, dite_eq_left J.property]
    exact mul_comm _ _
  have he := ideal_initial_cubic_sieve F hFp hFg
    (fun I hI => (hF I hI).1) ⌈N⌉₊ hnat hnorm aext M hM (elementRange M) hR
  have hea : (∑ I ∈ F, ‖aext I‖ ^ 2) = ∑ J : F, ‖a J‖ ^ 2 := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J hJ
    simp only [aext, dite_eq_left J.property]
    rfl
  simp_rw [hinner] at he
  rw [hea, ← Finset.sum_coe_sort] at he
  exact he

end
end SevenEighths.CubicSieve

end OAI

end Source1453

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/ExtractionOptimization.lean; sha256: dfa2eba96b842eb6fae28dd9f16a37cfb1e879c0a2b888bf29c7f8705b209081 -/
section Source1454
namespace OAI

namespace SevenEighths.CubicSieve
noncomputable section

lemma cube_scale_power (M T a : ℝ) (hT : 0 < T) (hTM : T ≤ M) (ha : (1/3 : ℝ) ≤ a) :
    (M/T)^(1/3 : ℝ) * T^a ≤ M^a := by
  have hM : 0 < M := hT.trans_le hTM
  have hbase : 1 ≤ M/T := (one_le_div hT).mpr hTM
  calc
    _ ≤ (M/T)^a * T^a := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hbase ha) (Real.rpow_nonneg hT.le _)
    _ = M^a := by
      rw [Real.div_rpow hM.le hT.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hT a).ne']

lemma extracted_monomial_le (W U T a : ℝ) (hW : 1 ≤ W) (hU : 0 ≤ U)
    (hWT : W^2*U ≤ T) (ha : (1/2 : ℝ) ≤ a) : W*U^a ≤ T^a := by
  have hW0 : 0 ≤ W := by linarith
  have hw : W ≤ (W^2)^a := by
    rw [← Real.rpow_natCast_mul hW0]
    conv_lhs => rw [← Real.rpow_one W]
    exact Real.rpow_le_rpow_of_exponent_le hW (by norm_num; linarith)
  calc
    _ ≤ (W^2)^a * U^a := mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hU _)
    _ = (W^2*U)^a := (Real.mul_rpow (sq_nonneg _) hU).symm
    _ ≤ T^a := Real.rpow_le_rpow (mul_nonneg (sq_nonneg _) hU) hWT (by linarith)

lemma extracted_linear_le (W T : ℝ) (hW : 0 ≤ W) (hWT : W^3 ≤ T) :
    W ≤ T^(1/3 : ℝ) := by
  have hh := Real.rpow_le_rpow (pow_nonneg hW 3) hWT (by norm_num : (0 : ℝ) ≤ 1/3)
  rw [← Real.rpow_natCast_mul hW] at hh
  norm_num at hh
  exact hh

lemma extraction_selected_shape (M N W U T ξ : ℝ) (hN : 0 ≤ N)
    (hW : 1 ≤ W) (hU : 0 ≤ U) (hT : 0 < T) (hTM : T ≤ M)
    (hWT : W^2*U ≤ T) (hWcube : W^3 ≤ T) (hξ : 1 ≤ ξ) :
    (M/T)^(1/3 : ℝ) * W * (U^ξ + N + (U*N)^(2/3 : ℝ)) ≤
      M^ξ + M^(1/3 : ℝ)*N + (M*N)^(2/3 : ℝ) := by
  have hM0 : 0 < M := hT.trans_le hTM
  have hH : 0 ≤ (M/T)^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hp : (M/T)^(1/3 : ℝ)*W*U^ξ ≤ M^ξ := by
    calc
      _ = (M/T)^(1/3 : ℝ)*(W*U^ξ) := by ring
      _ ≤ (M/T)^(1/3 : ℝ)*T^ξ := mul_le_mul_of_nonneg_left
        (extracted_monomial_le W U T ξ hW hU hWT (by linarith)) hH
      _ ≤ _ := cube_scale_power M T ξ hT hTM (by linarith)
  have hn : (M/T)^(1/3 : ℝ)*W*N ≤ M^(1/3 : ℝ)*N := by
    apply mul_le_mul_of_nonneg_right _ hN
    calc
      _ ≤ (M/T)^(1/3 : ℝ)*T^(1/3 : ℝ) := mul_le_mul_of_nonneg_left
        (extracted_linear_le W T (by linarith) hWcube) hH
      _ ≤ _ := cube_scale_power M T (1/3) hT hTM le_rfl
  have hc : (M/T)^(1/3 : ℝ)*W*(U*N)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
    rw [Real.mul_rpow hU hN, Real.mul_rpow (hT.le.trans hTM) hN]
    calc
      _ = ((M/T)^(1/3 : ℝ)*(W*U^(2/3 : ℝ)))*N^(2/3 : ℝ) := by ring
      _ ≤ ((M/T)^(1/3 : ℝ)*T^(2/3 : ℝ))*N^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (extracted_monomial_le W U T (2/3) hW hU hWT (by norm_num)) hH)
          (Real.rpow_nonneg hN _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (cube_scale_power M T (2/3) hT hTM (by norm_num))
        (Real.rpow_nonneg hN _)
  nlinarith

theorem extraction_min_shape (M N X Y ξ : ℝ) (hN : 0 ≤ N)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X*Y^2 ≤ M) (hξ : 1 ≤ ξ) :
    (M/(X*Y^2))^(1/3 : ℝ) *
      min (Y*(X^ξ + N + (X*N)^(2/3 : ℝ))) (X*(Y^ξ + N + (Y*N)^(2/3 : ℝ))) ≤
      M^ξ + M^(1/3 : ℝ)*N + (M*N)^(2/3 : ℝ) := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hT : 0 < X*Y^2 := by positivity
  have hM0 : 0 < M := hT.trans_le hXY
  have hH : 0 ≤ (M/(X*Y^2))^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  by_cases hyx : Y ≤ X
  · apply (mul_le_mul_of_nonneg_left (min_le_left _ _) hH).trans
    rw [← mul_assoc]
    exact extraction_selected_shape M N Y X (X*Y^2) ξ hN hY hX0.le hT hXY
      (by nlinarith) (by nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (sq_nonneg Y)]) hξ
  · have hxy : X ≤ Y := (lt_of_not_ge hyx).le
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hH).trans
    rw [← mul_assoc]
    exact extraction_selected_shape M N X Y (X*Y^2) ξ hN hX hY0.le hT hXY
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg hX0.le hY0.le)])
      (by nlinarith [sq_le_sq₀ hX0.le hY0.le |>.mpr hxy]) hξ

lemma cubic_cross_shape_absorb (M N ξ : ℝ) (hM : 1 ≤ M) (hN : 0 ≤ N)
    (hξ : (4/3 : ℝ) ≤ ξ) :
    (M*N)^(2/3 : ℝ) ≤ M^(1/3 : ℝ)*N + M^ξ := by
  have hM0 : 0 < M := by linarith
  have hfirst : 0 ≤ M^(1/3 : ℝ)*N := mul_nonneg (Real.rpow_nonneg hM0.le _) hN
  have hsecond : 0 ≤ M^ξ := Real.rpow_nonneg hM0.le _
  by_cases hMN : M ≤ N
  · have hN0 : 0 < N := hM0.trans_le hMN
    have hh := Real.rpow_le_rpow hM0.le hMN (by norm_num : (0 : ℝ) ≤ 1/3)
    have hm : M^(2/3 : ℝ) = M^(1/3 : ℝ)*M^(1/3 : ℝ) := by
      rw [← Real.rpow_add hM0]
      congr 1
      ring
    have hn : N^(1/3 : ℝ)*N^(2/3 : ℝ) = N := by
      rw [← Real.rpow_add hN0]
      norm_num
    apply le_trans _ (le_add_of_nonneg_right hsecond)
    rw [Real.mul_rpow hM0.le hN, hm]
    calc
      _ ≤ (M^(1/3 : ℝ)*N^(1/3 : ℝ))*N^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hM0.le _))
          (Real.rpow_nonneg hN _)
      _ = _ := by rw [mul_assoc, hn]
  · have hNM : N ≤ M := (lt_of_not_ge hMN).le
    apply le_trans _ (le_add_of_nonneg_left hfirst)
    calc
      _ ≤ (M*M)^(2/3 : ℝ) := Real.rpow_le_rpow (mul_nonneg hM0.le hN)
        (mul_le_mul_of_nonneg_left hNM hM0.le) (by norm_num)
      _ = M^(4/3 : ℝ) := by
        rw [Real.mul_rpow hM0.le hM0.le, ← Real.rpow_add hM0]
        congr 1
        ring
      _ ≤ M^ξ := Real.rpow_le_rpow_of_exponent_le hM hξ

theorem extraction_min_two_power (M N X Y ξ : ℝ) (hM : 1 ≤ M) (hN : 0 ≤ N)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X*Y^2 ≤ M) (hξ : (4/3 : ℝ) ≤ ξ) :
    (M/(X*Y^2))^(1/3 : ℝ) *
      min (Y*(X^ξ + N + (X*N)^(2/3 : ℝ))) (X*(Y^ξ + N + (Y*N)^(2/3 : ℝ))) ≤
      2*(M^(1/3 : ℝ)*N + M^ξ) := by
  have hh := extraction_min_shape M N X Y ξ hN hX hY hXY (by linarith)
  have hc := cubic_cross_shape_absorb M N ξ hM hN hξ
  linarith

end
end SevenEighths.CubicSieve

end OAI

end Source1454

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Growth.lean; sha256: 654b7b398f93506f226b090076229e01bee83e2fa99c2dd484324f4a46b1fe42 -/
section Source1455
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

def HasCubicExponent (ξ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C*(M*N)^ε*(M + N^ξ + (M*N)^(2/3 : ℝ))

theorem hasCubicExponent_initial : HasCubicExponent 2 := by
  intro ε hε
  let C := QuadraticInitialBound.initialSieveConstant
  have hC : 0 < C := QuadraticInitialBound.initialSieveConstant_pos
  refine ⟨4*C, by positivity, ?_⟩
  intro M N hM hN
  have hN0 : 0 ≤ N := by linarith
  have hceil : (⌈N⌉₊ : ℝ) ≤ 2*N := by
    have hh := Nat.ceil_lt_add_one hN0
    linarith
  have hn : (⌈N⌉₊ : ℝ)^2 ≤ 4*N^2 := by nlinarith [sq_nonneg ((⌈N⌉₊ : ℝ) - 2*N)]
  have hp : 1 ≤ (M*N)^ε := Real.one_le_rpow (by nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sub_nonneg.mpr hN)]) hε.le
  have hx : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ C*(M+(⌈N⌉₊ : ℝ)^2) := sieveNorm_initial M N hM hN
    _ ≤ 4*C*(M + N^(2 : ℝ) + (M*N)^(2/3 : ℝ)) := by
      rw [Real.rpow_two]
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hn), mul_nonneg hC.le hx]
    _ ≤ _ := by
      have hs : 0 ≤ M + N^(2 : ℝ) + (M*N)^(2/3 : ℝ) := by positivity
      nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 4*C) hs) (sub_nonneg.mpr hp)]

lemma HasCubicExponent.swapped {ξ : ℝ} (h : HasCubicExponent ξ)
    (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
        sieveNorm M N ≤ C*(M*N)^ε*(M^ξ + N + (M*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := h ε hε
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  rw [sieveNorm_reciprocity]
  simpa only [mul_comm, add_comm, add_left_comm, add_assoc] using hb N M hN hM

lemma HasCubicExponent.doubled {ξ : ℝ} (h : HasCubicExponent ξ)
    (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
      ∀ X N : ℝ, 1 ≤ X → 1 ≤ N →
        sieveNorm (2*X) N ≤ C*(X*N)^ε*(X^ξ + N + (X*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := h.swapped ε hε
  let A : ℝ := 1 + (2:ℝ)^ξ + (2:ℝ)^(2/3 : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨C*(2:ℝ)^ε*A, by positivity, ?_⟩
  intro X N hX hN
  have hX0 : 0 ≤ X := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hxξ := Real.rpow_nonneg hX0 ξ
  have hcross := Real.rpow_nonneg (mul_nonneg hX0 hN0) (2/3 : ℝ)
  have hshape : (2*X)^ξ + N + ((2*X)*N)^(2/3 : ℝ) ≤
      A*(X^ξ+N+(X*N)^(2/3 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hX0]
    rw [show (2*X)*N = 2*(X*N) by ring, Real.mul_rpow (by norm_num) (mul_nonneg hX0 hN0)]
    dsimp only [A]
    nlinarith [mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) ξ) hN0,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) ξ) hcross,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (2/3 : ℝ)) hN0,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (2/3 : ℝ)) hxξ]
  calc
    _ ≤ C*((2*X)*N)^ε*((2*X)^ξ+N+((2*X)*N)^(2/3 : ℝ)) := hb (2*X) N (by linarith) hN
    _ ≤ C*((2*X)*N)^ε*(A*(X^ξ+N+(X*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hshape (by positivity)
    _ = _ := by
      rw [show (2*X)*N = 2*(X*N) by ring, Real.mul_rpow (by norm_num) (mul_nonneg hX0 hN0)]
      ring

end
end SevenEighths.CubicSieve

end OAI

end Source1455

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/B2Growth.lean; sha256: 97a3c26debeef5cd76b79c55745d531359237b549310abe3588888faf35d9be7 -/
section Source1456
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem elementSieveNorm_two_power_log (ξ ε A M N : ℝ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hB1 : ∀ X : ℝ, 1 ≤ X → sieveNorm (2*X) N ≤
      A*(X*N)^ε*(X^ξ + N + (X*N)^(2/3 : ℝ))) :
    elementSieveNorm M N ≤ (384*128^2 : ℝ) * A *
      (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 *
      (M*N)^ε * (M^(1/3 : ℝ)*N + M^ξ) := by
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let R := elementRange M
  have hRne : R.Nonempty := by
    refine ⟨1, ?_⟩
    rw [mem_elementRange]
    refine ⟨one_ne_zero, ?_⟩
    simpa using hM
  have hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M :=
    fun z hz => (mem_elementRange M z).mp hz
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · positivity
  intro a
  obtain ⟨X,Y,hX,hY,hXY,he⟩ := full_element_dyadic_extraction R hRne M N hR
    (fun j : idealRange N => j.val) Subtype.val_injective
    (fun j => mem_idealRange.mp j.property) a
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hXM : X ≤ M := by nlinarith [sq_nonneg (Y-1)]
  have hYM : Y ≤ M := by nlinarith [sq_nonneg (Y-1)]
  let B := A*(M*N)^ε
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (U : ℝ) (hU : 1 ≤ U) (hUM : U ≤ M) :
      sieveNorm (2*U) N ≤ B*(U^ξ+N+(U*N)^(2/3 : ℝ)) := by
    apply (hB1 U hU).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_right hUM hN0.le) hε) hA
  have hmin : min (Y*sieveNorm (2*X) N) (X*sieveNorm (2*Y) N) ≤
      B*min (Y*(X^ξ+N+(X*N)^(2/3 : ℝ))) (X*(Y^ξ+N+(Y*N)^(2/3 : ℝ))) := by
    rw [mul_min_of_nonneg _ _ hB]
    apply min_le_min
    · convert mul_le_mul_of_nonneg_left (hb X hX hXM) hY0.le using 1; ring
    · convert mul_le_mul_of_nonneg_left (hb Y hY hYM) hX0.le using 1; ring
  have hopt := extraction_min_two_power M N X Y ξ hM hN0.le hX hY hXY hξ
  have hH : 0 ≤ (M/(X*Y^2))^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hi (z : O) : (∑ j : idealRange N, a j * elementCharacter j.val (mem_idealRange.mp j.property).1.2 z) =
      ∑ j : idealRange N, cubicRow j.val z * a j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  simp_rw [hi] at he
  have hE : 0 ≤ ∑ j : idealRange N, ‖a j‖^2 := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmin (show 0 ≤ (192*128^2 : ℝ)*
      (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*(M/(X*Y^2))^(1/3 : ℝ) by positivity)) hE
  have hbnd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hopt (show 0 ≤ (192*128^2 : ℝ)*
      (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*B by positivity)) hE
  have he' := he.trans hh
  rw [← Finset.sum_coe_sort] at he'
  change (∑ z : elementRange M, ‖∑ j : idealRange N, cubicRow j.val z.val * a j‖^2) ≤ _
  apply he'.trans
  convert hbnd using 1 <;> dsimp only [B] <;> ring

theorem HasCubicExponent.full_element_bound {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      elementSieveNorm M N ≤ C*(M*N)^ε*(M^(1/3 : ℝ)*N + M^ξ) := by
  obtain ⟨A,hA,hb⟩ := h.doubled (ε/2) (by positivity)
  let D : ℝ := 2 + 1/((ε/4)*Real.log 2)
  have hD : 0 < D := by
    dsimp [D]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨(384*128^2 : ℝ)*A*D^2, by positivity, ?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hlog := CanonicalQuadraticSieve.columnDyadicLength_small_power (ε/4) (by positivity) M hM
  have hLP : (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 ≤ D^2*M^(ε/2) := by
    have hh := pow_le_pow_left₀ (by positivity) hlog 2
    rw [mul_pow, ← Real.rpow_mul_natCast hM0.le] at hh
    have he : (ε/4)*(2:ℕ) = ε/2 := by push_cast; ring
    rw [he] at hh
    exact hh
  have hMP : M^(ε/2) ≤ (M*N)^(ε/2) := Real.rpow_le_rpow hM0.le
    (by nlinarith) (by positivity)
  have hprod : (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 * (M*N)^(ε/2) ≤
      D^2*(M*N)^ε := by
    calc
      _ ≤ (D^2*M^(ε/2))*(M*N)^(ε/2) :=
        mul_le_mul_of_nonneg_right hLP (Real.rpow_nonneg (by positivity) _)
      _ ≤ (D^2*(M*N)^(ε/2))*(M*N)^(ε/2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMP (sq_nonneg _))
          (Real.rpow_nonneg (by positivity) _)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add (mul_pos hM0 hN0)]
        congr 2
        ring
  have he := elementSieveNorm_two_power_log ξ (ε/2) A M N hξ (by positivity) hA.le hM hN
    (fun X hX => hb X N hX hN)
  calc
    _ ≤ (384*128^2 : ℝ)*A*
        (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 *
        (M*N)^(ε/2)*(M^(1/3 : ℝ)*N+M^ξ) := he
    _ = ((384*128^2 : ℝ)*A)*
        ((CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*(M*N)^(ε/2))*
        (M^(1/3 : ℝ)*N+M^ξ) := by ring
    _ ≤ ((384*128^2 : ℝ)*A)*(D^2*(M*N)^ε)*(M^(1/3 : ℝ)*N+M^ξ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by positivity)) (by positivity)
    _ = _ := by ring

end
end SevenEighths.CubicSieve

end OAI

end Source1456

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/PairPrimes.lean; sha256: c578314264a9e34af6857d1eff0ded7fad7607e29d46d7981b594eb2765e1ce5 -/
section Source1457
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def pairPrime (I J : Ideal O) : PrimeIndex I ⊕ PrimeIndex J → Ideal O :=
  Sum.elim Subtype.val Subtype.val

instance pairPrime_maximal (I J : Ideal O) (P : PrimeIndex I ⊕ PrimeIndex J) :
    (pairPrime I J P).IsMaximal := by
  cases P <;> exact primeIndexMaximal _ _

lemma pairPrime_good (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (P : PrimeIndex I ⊕ PrimeIndex J) : goodLambda ∉ pairPrime I J P := by
  cases P with
  | inl P => exact primeIndex_good I hI.2 P
  | inr P => exact primeIndex_good J hJ.2 P

lemma pairPrime_coprime (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) : Pairwise (Function.onFun IsCoprime (pairPrime I J)) := by
  have cross (P : PrimeIndex I) (Q : PrimeIndex J) : IsCoprime P.val Q.val := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup (primeIndex_le I (primaryGenerator_ne_zero_ideal I hI.2) P)
      (primeIndex_le J (primaryGenerator_ne_zero_ideal J hJ.2) Q)
  intro P Q hPQ
  cases P with
  | inl P => cases Q with
    | inl Q =>
      exact CanonicalRowCompletion.primeIndex_pairwise_coprime I (fun he => hPQ (congrArg Sum.inl he))
    | inr Q => exact cross P Q
  | inr P => cases Q with
    | inl Q => exact (cross Q P).symm
    | inr Q =>
      exact CanonicalRowCompletion.primeIndex_pairwise_coprime J (fun he => hPQ (congrArg Sum.inr he))

lemma pairPrime_product (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    (∏ P, pairPrime I J P) = I * J := by
  rw [Fintype.prod_sum_type]
  exact congrArg₂ (· * ·) (primeIndex_product I hI) (primeIndex_product J hJ)

def pairExponent (I J : Ideal O) : PrimeIndex I ⊕ PrimeIndex J → ℕ :=
  Sum.elim (fun _ => 4) (fun _ => 2)

lemma pairExponent_nonprincipal (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (P : PrimeIndex I ⊕ PrimeIndex J) :
    actualSextic (pairPrime I J P) (pairPrime_good I J hI hJ P) ^ pairExponent I J P ≠ 1 := by
  cases P with
  | inl P => exact cubicExponent_nonprincipal P.val (primeIndex_good I hI.2 P) true
  | inr P => exact cubicExponent_nonprincipal P.val (primeIndex_good J hJ.2 P) false

lemma primeIndex_cubic_row (I : Ideal O) (hI : Admissible I) (z : O) :
    finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 2) z =
      cubicRow I z := by
  exact (CompletedGauss.cubicRow_mk I hI.2 z).symm.trans
    (CubicEisenstein.cubicRow_eq_idealSymbol I hI.2 hI.1 z)

lemma primeIndex_conjugate_cubic_row (I : Ideal O) (hI : Admissible I) (z : O) :
    finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z =
      star (cubicRow I z) := by
  have he : finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z =
      (finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 2) z) ^ 2 := by
    simp only [finiteSexticRow, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro P hP
    rw [MulChar.pow_apply' _ (by decide : (4 : ℕ) ≠ 0),
      MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), ← pow_mul]
  rw [he, primeIndex_cubic_row I hI, cubicRow_square_eq_star]

lemma pairPrime_row (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (z : O) :
    finiteSexticRow (pairPrime I J) (pairPrime_good I J hI hJ) (pairExponent I J) z =
      star (cubicRow I z) * cubicRow J z := by
  unfold finiteSexticRow
  rw [Fintype.prod_sum_type]
  change finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z *
    finiteSexticRow (fun P : PrimeIndex J => P.val) (primeIndex_good J hJ.2) (fun _ => 2) z = _
  rw [primeIndex_conjugate_cubic_row I hI, primeIndex_cubic_row J hJ]

lemma pairPrime_modulus (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    Ideal.span {primaryGenerator I * primaryGenerator J} = ∏ P, pairPrime I J P := by
  rw [pairPrime_product I J hI hJ, ← Ideal.span_singleton_mul_span_singleton,
    (primaryGenerator_spec I hI.2).1, (primaryGenerator_spec J hJ.2).1]

end
end SevenEighths.CubicSieve

end OAI

end Source1457

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/PairPoisson.lean; sha256: da0eeb6163c2d1b8e8b0cc9dc787fbda1331efc6550b43503eaf9566b97f3db6 -/
section Source1458
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def pairPrincipalRow (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) : O ⧸ Ideal.span {primaryGenerator I * primaryGenerator J} → ℂ :=
  principalSexticRow (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
    (pairPrime_good I J hI hJ) (pairExponent I J) (primaryGenerator I * primaryGenerator J)
    (pairPrime_modulus I J hI hJ)

lemma pairPrincipalRow_mk (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (z : O) :
    pairPrincipalRow I J hI hJ hcop (Ideal.Quotient.mk _ z) =
      star (cubicRow I z) * cubicRow J z := by
  unfold pairPrincipalRow
  rw [principalSexticRow_mk (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
    (pairPrime_good I J hI hJ) (pairExponent I J) _ (pairPrime_modulus I J hI hJ) z,
    pairPrime_row I J hI hJ]

lemma pairPrincipalGauss_eq (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    principalNormalizedGauss (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
      (pairPrime_good I J hI hJ) (pairExponent I J)
      (primaryGenerator I * primaryGenerator J) (pairPrime_modulus I J hI hJ)
      (mul_ne_zero hI.2 hJ.2) = cubicPairGauss I J hI hJ := by
  let a := primaryGenerator I
  let b := primaryGenerator J
  let : Finite (O ⧸ Ideal.span {a * b}) := finite_quotient_span (mul_ne_zero hI.2 hJ.2)
  let : Fintype (O ⧸ Ideal.span {a * b}) := Fintype.ofFinite _
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := finite_quotient_product hI.2 hJ.2
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span hI.2
  let e : (O ⧸ Ideal.span {a * b}) ≃+* (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm
  have hnorm : (‖eisEmbedding (a * b)‖ : ℂ) = (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ) := by
    rw [map_mul, norm_mul, Complex.ofReal_mul]
  dsimp only [principalNormalizedGauss, cubicPairGauss]
  rw [hnorm]
  congr 1
  rw [← Equiv.sum_comp e.toEquiv]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  change pairPrincipalRow I J hI hJ hcop (Ideal.Quotient.mk _ z) * _ = _
  rw [pairPrincipalRow_mk]
  simp only [e, a, b, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, Ideal.quotEquivOfEq_mk, Ideal.Quotient.factor_mk]
  rw [← MulChar.star_apply', principalCubicCharacter_mk I hI, principalCubicCharacter_mk J hJ]
  congr 1

lemma pairPrincipalGauss_separation (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    principalNormalizedGauss (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
      (pairPrime_good I J hI hJ) (pairExponent I J)
      (primaryGenerator I * primaryGenerator J) (pairPrime_modulus I J hI hJ)
      (mul_ne_zero hI.2 hJ.2) = star (gaussTwo I hI.2) * gaussTwo J hJ.2 := by
  rw [pairPrincipalGauss_eq I J hI hJ hcop, cubicPairGauss_separation I J hI hJ hcop]

theorem cubic_pair_poisson (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, (star (cubicRow I z) * cubicRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ((M : ℂ) * (star (gaussTwo I hI.2) * gaussTwo J hJ.2) /
        (‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ : ℂ)) *
      ∑' h : O, (cubicRow I h * star (cubicRow J h)) *
        paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 /
          ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ ^ 2) := by
  let c := primaryGenerator I * primaryGenerator J
  have hc0 : c ≠ 0 := mul_ne_zero hI.2 hJ.2
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (pairPrime_modulus I J hI hJ)
  let : Fintype (O ⧸ ∏ P, pairPrime I J P) := Fintype.ofEquiv (O ⧸ Ideal.span {c}) e.toEquiv
  let (P : PrimeIndex I ⊕ PrimeIndex J) : Fintype (O ⧸ pairPrime I J P) := Fintype.ofFinite _
  let row := pairPrincipalRow I J hI hJ hcop
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0
  let G := ∑ r : O ⧸ Ideal.span {c}, row r * ψ r
  have ht (h : O) :
      (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
        (cubicRow I h * star (cubicRow J h)) * G := by
    have hh := canonical_principal_gauss_transform_of_nontrivial (pairPrime I J)
      (pairPrime_coprime I J hI hJ hcop) (pairPrime_good I J hI hJ) (pairExponent I J)
      (pairExponent_nonprincipal I J hI hJ) c (pairPrime_modulus I J hI hJ) ψ
      (Ideal.Quotient.mk (Ideal.span {c}) h)
    change (∑ r, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
      star (row (Ideal.Quotient.mk (Ideal.span {c}) h)) * G at hh
    change (∑ r, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
      star (pairPrincipalRow I J hI hJ hcop (Ideal.Quotient.mk _ h)) * G at hh
    rw [pairPrincipalRow_mk I J hI hJ hcop h, star_mul, star_star,
      mul_comm (star (cubicRow J h)) (cubicRow I h)] at hh
    exact hh
  have hp := actual_radial_paper_poisson_trace W M hM c hc0 row
  change (∑' z : O, row (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
      (M / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [ht] at hp
  have hsum : (∑' h : O, ((cubicRow I h * star (cubicRow J h)) * G) *
      paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) =
      G * ∑' h : O, (cubicRow I h * star (cubicRow J h)) *
        paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    ring
  rw [hsum] at hp
  have hrow (z : O) : row (Ideal.Quotient.mk (Ideal.span {c}) z) =
      star (cubicRow I z) * cubicRow J z :=
    pairPrincipalRow_mk I J hI hJ hcop z
  simp_rw [hrow] at hp
  rw [hp]
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc0))
  have hGauss := pairPrincipalGauss_separation I J hI hJ hcop
  change G / (‖eisEmbedding c‖ : ℂ) = star (gaussTwo I hI.2) * gaussTwo J hJ.2 at hGauss
  have hG := (div_eq_iff hn).mp hGauss
  change ((M / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * (G * _) = _
  rw [← mul_assoc]
  congr 1
  change ((M / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * G =
    (M : ℂ) * (star (gaussTwo I hI.2) * gaussTwo J hJ.2) / (‖eisEmbedding c‖ : ℂ)
  rw [hG]
  push_cast
  field_simp [hn]

end
end SevenEighths.CubicSieve

end OAI

end Source1458

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/KernelTransfer.lean; sha256: f0beb52c5781983439681fccdf524055eb6919ccf643fb0750a06be7e7ea2ae0 -/
section Source1459
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson FourierBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem cubic_radial_kernel_transfer (W : 𝓢(ℝ, ℂ)) (Lr Lc : ℝ)
    (hLr : 0 ≤ Lr) (hLc : 0 ≤ Lc) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hN : 0 ≤ N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
        (_hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a b : n → ℂ) (E : ℝ) (_hE : 0 ≤ E)
        (_ha : (∑ j, ‖a j‖ ^ 2) ≤ E) (_hb : (∑ j, ‖b j‖ ^ 2) ≤ E)
        (x : m → ℝ) (y : n → ℝ) (_hx : ∀ i, |x i| ≤ Lr) (_hy : ∀ j, |y j| ≤ Lc),
        (1 + R) ^ A *
          (∑ i, ‖∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
            star (cubicRow (cols j) (rows i) * a j) *
              (cubicRow (cols k) (rows i) * b k) else 0) *
            paperRadialFourier W (R * Real.exp (x i + (y j + y k)))‖) ≤
          C * (elementSieveNorm M N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) := by
  obtain ⟨C, hC, htransfer⟩ := QuadraticKernelTransfer.radial_matrix_kernel_transfer
    W Lr (2 * Lc) hLr (by positivity) A
  refine ⟨C, hC, ?_⟩
  intro R hR m n _ _ _ _ ε hε M N hN rows cols hr hc hrows hcols a b E hE ha hb x y hx hy
  let c : m → n × n → ℂ := fun i p => if IsCoprime (cols p.1) (cols p.2) then
    star (cubicRow (cols p.1) (rows i) * a p.1) *
      (cubicRow (cols p.2) (rows i) * b p.2) else 0
  let H := elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E
  have hfac : 0 ≤ elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) :=
    mul_nonneg (elementSieveNorm_nonneg _ _)
      (mul_nonneg (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le (Real.rpow_nonneg hN _))
  have hH : 0 ≤ H := mul_nonneg hfac hE
  have hyy (p : n × n) : |y p.1 + y p.2| ≤ 2 * Lc :=
    (abs_add_le _ _).trans (by linarith [hy p.1, hy p.2])
  have hphase (t : ℝ) : (∑ i, ‖∑ p : n × n, c i p * logPhase t (y p.1 + y p.2)‖) ≤ H := by
    let aTwist : n → ℂ := fun j => a j * star (logPhase t (y j))
    let bTwist : n → ℂ := fun j => b j * logPhase t (y j)
    have ha' : (∑ j, ‖aTwist j‖ ^ 2) ≤ E := by simpa only [aTwist, norm_mul, norm_star, logPhase_norm, mul_one] using ha
    have hb' : (∑ j, ‖bTwist j‖ ^ 2) ≤ E := by simpa only [bTwist, norm_mul, logPhase_norm, mul_one] using hb
    have he (i : m) : (∑ p : n × n, c i p * logPhase t (y p.1 + y p.2)) =
        ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
          star (cubicRow (cols j) (rows i) * aTwist j) *
            (cubicRow (cols k) (rows i) * bTwist k) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [c, aTwist, bTwist]
      split_ifs
      · rw [logPhase_add]
        simp only [star_mul, star_star]
        ring
      · simp only [zero_mul]
    simp_rw [he]
    have hbil := element_coprime_bilinear_bound ε hε M N hN rows cols hr hc hrows hcols aTwist bTwist
    apply (sq_le_sq₀ (by positivity) hH).mp
    apply hbil.trans
    calc
      _ ≤ (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) *
          (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ha' hfac) (mul_le_mul_of_nonneg_left hb' hfac)
          (by positivity) hH
      _ = H ^ 2 := by ring
  have ht := htransfer R hR c x (fun p : n × n => y p.1 + y p.2) H hH hx hyy hphase
  simpa only [Fintype.sum_prod_type, c, H] using ht

end
end SevenEighths.CubicSieve

end OAI

end Source1459

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/FrequencyShell.lean; sha256: de8ae9dca7149524a97b04fccf8a1d06e32375801bd9c9f72dffc2b31b30f343 -/
section Source1460
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson FourierBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma log_shell_ratio (K q : ℝ) (hK : 0 < K) (hq : K / 2 ≤ q ∧ q ≤ K) :
    |Real.log (q / K)| ≤ 4 := by
  apply CanonicalQuadraticSieve.middleRatio_log_bound
  constructor
  · apply (le_div_iff₀ hK).mpr
    linarith [hq.1]
  · apply (div_le_iff₀ hK).mpr
    linarith [hq.2]

lemma log_inverse_shell_ratio (N q : ℝ) (hN : 0 < N) (hq : N / 2 ≤ q ∧ q ≤ N) :
    |Real.log (N / q)| ≤ 4 := by
  have hq0 : 0 < q := by linarith [hq.1]
  apply CanonicalQuadraticSieve.middleRatio_log_bound
  constructor
  · apply (le_div_iff₀ hq0).mpr
    linarith [hq.2]
  · apply (div_le_iff₀ hq0).mpr
    linarith [hq.1]

lemma radial_product_log_identity (M K N q u v : ℝ)
    (hK : 0 < K) (hN : 0 < N) (hq : 0 < q) (hu : 0 < u) (hv : 0 < v) :
    (M * K / N ^ 2) * Real.exp (Real.log (q / K) + (Real.log (N / u) + Real.log (N / v))) =
      M * q / (u * v) := by
  rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hq hK),
    Real.exp_log (div_pos hN hu), Real.exp_log (div_pos hN hv)]
  field_simp

theorem cubic_frequency_shell_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M K N : ℝ) (_hM : 0 < M) (_hK : 0 < K) (_hN : 0 < N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, K / 2 ≤ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ∧
          (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ K)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a b : n → ℂ) (E : ℝ) (_hE : 0 ≤ E)
        (_ha : (∑ j, ‖a j‖ ^ 2) ≤ E) (_hb : (∑ j, ‖b j‖ ^ 2) ≤ E),
        (1 + M * K / N ^ 2) ^ A *
          (∑ i, ‖∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
            star (cubicRow (cols j) (rows i) * a j) *
              (cubicRow (cols k) (rows i) * b k) else 0) *
            paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {rows i}) : ℝ) /
              ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)))‖) ≤
          C * (elementSieveNorm K N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) := by
  obtain ⟨C, hC, ht⟩ := cubic_radial_kernel_transfer W 4 4 (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n _ _ _ _ ε hε M K N hM hK hN rows cols hr hc hrows hcols a b E hE ha hb
  have hq (i : m) : 0 < (Ideal.absNorm (Ideal.span {rows i}) : ℝ) := by linarith [(hrows i).1]
  have hn (j : n) : 0 < (Ideal.absNorm (cols j) : ℝ) := by linarith [(hcols j).2.1]
  have hr0 (i : m) : rows i ≠ 0 := by
    intro hz
    simpa [hz] using hq i
  have hp := ht (M * K / N ^ 2) (by positivity) ε hε K N hN.le rows cols hr hc
    (fun i => ⟨hr0 i, (hrows i).2⟩) (fun j => ⟨(hcols j).1, (hcols j).2.2⟩)
    a b E hE ha hb
    (fun i => Real.log ((Ideal.absNorm (Ideal.span {rows i}) : ℝ) / K))
    (fun j => Real.log (N / (Ideal.absNorm (cols j) : ℝ)))
    (fun i => log_shell_ratio K _ hK (hrows i))
    (fun j => log_inverse_shell_ratio N _ hN (hcols j).2)
  simp_rw [radial_product_log_identity M K N _ _ _ hK hN (hq _) (hn _) (hn _)] at hp
  exact hp

end
end SevenEighths.CubicSieve

end OAI

end Source1460

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/DualCoefficients.lean; sha256: 9098098b1fd48a13cfef622ac16d8ebcee34317be121df73a8394d67cb6274bc -/
section Source1461
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicDualCoefficient {n : Type*} (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (j : n) : ℂ :=
  star (a j * gaussTwo (cols j) (hc j).2) / (‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ)

lemma cubicDualCoefficient_norm_sq {n : Type*}
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ) (j : n) :
    ‖cubicDualCoefficient cols hc a j‖ ^ 2 = ‖a j‖ ^ 2 / (Ideal.absNorm (cols j) : ℝ) := by
  simp only [cubicDualCoefficient, norm_div, norm_star, norm_mul, gaussTwo_norm_one _ (hc j),
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_pow,
    primaryGenerator_norm_sq _ (hc j).2]

lemma cubicDualCoefficient_energy {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (N : ℝ) (hN : 0 < N) (hcols : ∀ j, N / 2 ≤ (Ideal.absNorm (cols j) : ℝ)) :
    (∑ j, ‖cubicDualCoefficient cols hc a j‖ ^ 2) ≤ (2 / N) * ∑ j, ‖a j‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [cubicDualCoefficient_norm_sq]
  calc
    _ ≤ ‖a j‖ ^ 2 / (N / 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (hcols j)
    _ = _ := by field_simp

def cubicDualRow {n : Type*} [Fintype n] (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (h : O) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
      ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ))) *
      (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
      paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) else 0

lemma cubicDualRow_eq_gram {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (h : O) :
    cubicDualRow cols hc a W M h =
      ∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
        star (cubicRow (cols j) h * cubicDualCoefficient cols hc a j) *
          (cubicRow (cols k) h * cubicDualCoefficient cols hc a k) else 0) *
        paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
          ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) := by
  unfold cubicDualRow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [isCoprime_comm (x := cols k) (y := cols j)]
  by_cases hcop : IsCoprime (cols j) (cols k)
  · rw [ite_eq_left hcop, ite_eq_left hcop]
    have hscale : (Ideal.absNorm (cols k) : ℝ) * (Ideal.absNorm (cols j) : ℝ) =
        (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) := mul_comm _ _
    rw [hscale]
    congr 1
    simp only [cubicDualCoefficient, star_mul, star_div₀, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring
  · simp only [ite_eq_right hcop, zero_mul]

lemma cubicRow_zero_of_ne_one (I : Ideal O) (hI : Admissible I) (hI1 : I ≠ 1) :
    cubicRow I 0 = 0 := by
  have hI_top : I ≠ ⊤ := by simpa only [Ideal.one_eq_top] using hI1
  have hcop : ¬ IsCoprime I (Ideal.span {(0 : O)}) := by
    simpa only [Ideal.isCoprime_iff_sup_eq, Ideal.span_singleton_zero, sup_bot_eq] using hI_top
  have h := idealSymbol_cube_mask I 0 hI.2
  rw [ite_eq_right hcop] at h
  exact eq_zero_of_pow_eq_zero h

end
end SevenEighths.CubicSieve

end OAI

end Source1461

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Smoothed.lean; sha256: 50251dd04a95bd29fc630eb0eb867a22fe21651152bff69d164b01c9af77a4aa -/
section Source1462
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicRow_norm_le_one (I : Ideal O) (hI : Admissible I) (z : O) : ‖cubicRow I z‖ ≤ 1 :=
  elementCharacter_norm_le_one I hI.2 z

lemma cubic_pair_fourier_summable (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    Summable (fun h : O => (cubicRow I h * star (cubicRow J h)) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) _
    (paperRadialFourier_lattice_summable_norm W t ht)
  intro h
  simp only [norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right (cubicRow_norm_le_one I hI h) (norm_nonneg _)).trans
      (by simpa only [one_mul] using cubicRow_norm_le_one J hJ h))
    (norm_nonneg _)).trans_eq (one_mul _)

def cubicSmoothedCoprime {n : Type*} [Fintype n] (cols : n → Ideal O)
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j) * a k * ∑' z : O, (star (cubicRow (cols j) z) * cubicRow (cols k) z) *
      W (‖eisEmbedding z‖ ^ 2 / M) else 0

lemma pair_modulus_norm_sq (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by
  rw [map_mul, norm_mul, mul_pow, primaryGenerator_norm_sq I hI.2, primaryGenerator_norm_sq J hJ.2]

lemma cubicDualRow_summable {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (cubicDualRow cols hc a W M) := by
  apply summable_sum
  intro j hj
  apply summable_sum
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · simp only [ite_eq_left hcop]
    have hjN : 0 < (Ideal.absNorm (cols j) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc j).2))
    have hkN : 0 < (Ideal.absNorm (cols k) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc k).2))
    have hs := (cubic_pair_fourier_summable (cols j) (cols k) (hc j) (hc k) W
      (M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) (by positivity)).mul_left
      (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
        ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ)))
    convert hs using 1
    ext z
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    rw [show M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) *
      (Ideal.absNorm (Ideal.span {z}) : ℝ) = M * (Ideal.absNorm (Ideal.span {z}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) by ring]
    try simp only [mul_assoc]
  · simp only [ite_eq_right hcop]
    exact summable_zero

lemma cubicDualRow_tsum {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' h : O, cubicDualRow cols hc a W M h) =
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ))) *
          ∑' h : O, (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
            paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
              ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) else 0 := by
  have hs (j k : n) : Summable (fun h : O => (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
      paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)))) := by
    have hjN : 0 < (Ideal.absNorm (cols j) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc j).2))
    have hkN : 0 < (Ideal.absNorm (cols k) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc k).2))
    convert cubic_pair_fourier_summable (cols j) (cols k) (hc j) (hc k) W
      (M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) (by positivity) using 1
    ext z
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    rw [show M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) *
      (Ideal.absNorm (Ideal.span {z}) : ℝ) = M * (Ideal.absNorm (Ideal.span {z}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) by ring]
    try simp only [mul_assoc]
  unfold cubicDualRow
  rw [Summable.tsum_finsetSum (fun j hj => summable_sum (fun k hk => by
    split_ifs
    · simpa only [mul_assoc] using (hs j k).mul_left
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ)))
    · exact summable_zero))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Summable.tsum_finsetSum (fun k hk => by
    split_ifs
    · simpa only [mul_assoc] using (hs j k).mul_left
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ)))
    · exact summable_zero)]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp only [tsum_zero, mul_assoc, tsum_mul_left]

theorem cubicSmoothedCoprime_poisson {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    cubicSmoothedCoprime cols a W M =
      (M : ℂ) * ∑' h : O, cubicDualRow cols hc a W M h := by
  rw [cubicDualRow_tsum cols hc a W M hM]
  unfold cubicSmoothedCoprime
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · rw [ite_eq_left hcop, ite_eq_left hcop, cubic_pair_poisson _ _ (hc j) (hc k) hcop W M hM]
    rw [pair_modulus_norm_sq _ _ (hc j) (hc k)]
    simp_rw [eisEmbedding_norm_sq_eq_absNorm_span]
    rw [map_mul, norm_mul, Complex.ofReal_mul]
    ring
  · simp only [ite_eq_right hcop, mul_zero]

end
end SevenEighths.CubicSieve

end OAI

end Source1462

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Mobius.lean; sha256: fb8d436edc1a4c03e20c6c4bf613bc075b4bef3d81b5e4e012fb2747dbf62392 -/
section Source1463
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve (idealQuotient totalQuotient gcdPool)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def elementQuotient (d z : O) : O := if h : d ∣ z then h.choose else 0

lemma elementQuotient_mul (d z : O) (h : d ∣ z) : d * elementQuotient d z = z := by
  rw [elementQuotient, dite_eq_left h]
  exact h.choose_spec.symm

lemma elementQuotient_injective (d : O) : Set.InjOn (elementQuotient d) {z | d ∣ z} := by
  intro x hx y hy he
  rw [← elementQuotient_mul d x hx, ← elementQuotient_mul d y hy, he]

def dividedRows (R : Finset O) (d : O) : Finset O :=
  (R.filter (fun z => d ∣ z)).image (elementQuotient d)

lemma sum_divisible_rows (R : Finset O) (d : O) (f : O → ℂ) :
    (∑ z ∈ R, if d ∣ z then f z else 0) =
      ∑ w ∈ dividedRows R d, f (d * w) := by
  rw [← Finset.sum_filter]
  unfold dividedRows
  have hinj : Set.InjOn (elementQuotient d) (↑(R.filter (fun z => d ∣ z)) : Set O) := by
    intro x hx y hy he
    exact elementQuotient_injective d (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 he
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro z hz
  rw [elementQuotient_mul d z (Finset.mem_filter.mp hz).2]

lemma dividedRows_ne_zero (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0) (d : O)
    (w : O) (hw : w ∈ dividedRows R d) : w ≠ 0 := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
  intro he
  have h := elementQuotient_mul d z (Finset.mem_filter.mp hz).2
  rw [he, mul_zero] at h
  exact hR z (Finset.mem_filter.mp hz).1 h.symm

lemma dividedRows_norm_le (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (d : O) (hd : d ≠ 0) (w : O) (hw : w ∈ dividedRows R d) :
    (Ideal.absNorm (Ideal.span {w}) : ℝ) ≤ M / (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
  have hdN : 0 < (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hd))
  apply (le_div_iff₀ hdN).mpr
  calc
    _ = (Ideal.absNorm (Ideal.span {d * elementQuotient d z}) : ℝ) := by
      rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul, mul_comm]
    _ = (Ideal.absNorm (Ideal.span {z}) : ℝ) := by
      rw [elementQuotient_mul d z (Finset.mem_filter.mp hz).2]
    _ ≤ M := hR z (Finset.mem_filter.mp hz).1

lemma cubicRow_mul_argument (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x y : O) :
    cubicRow I (x * y) = cubicRow I x * cubicRow I y := by
  exact (elementCharacter I hI).map_mul x y

lemma totalQuotient_cubic_admissible (D I : Ideal O) (hI : Admissible I) :
    Admissible (totalQuotient D I) := by
  by_cases h : D ∣ I
  · rw [totalQuotient, ite_eq_left h]
    exact cubic_admissible_quotient hI h
  · rw [totalQuotient, ite_eq_right h]
    exact ⟨squarefree_one, by rw [primaryGenerator_one]; exact one_ne_zero⟩

def descendedCoefficient {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (d : O) (j : n) : ℂ :=
  cubicRow (totalQuotient D (cols j)) d * (if D ∣ cols j then a j else 0)

def residualGram {n : Type*} [Fintype n] (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
    star (cubicRow (totalQuotient D (cols j)) z * a j) *
      (cubicRow (totalQuotient D (cols k)) z * a k) else 0

lemma residualGram_rescale {n : Type*} [Fintype n] (D : Ideal O) (cols : n → Ideal O)
    (hcols : ∀ j, Admissible (cols j)) (a : n → ℂ) (d w : O) :
    residualGram D cols (fun j => if D ∣ cols j then a j else 0) (d * w) =
      residualGram D cols (descendedCoefficient D cols a d) w := by
  unfold residualGram
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs
  · rw [cubicRow_mul_argument _ (totalQuotient_cubic_admissible D _ (hcols j)).2,
      cubicRow_mul_argument _ (totalQuotient_cubic_admissible D _ (hcols k)).2]
    simp only [descendedCoefficient, star_mul]
    ring
  · rfl

lemma ideal_dvd_span_iff_generator (E : Ideal O) (z : O) :
    E ∣ Ideal.span {z} ↔ idealGenerator E ∣ z := by
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have he : (z ∈ Ideal.span {idealGenerator E}) ↔ idealGenerator E ∣ z :=
    Ideal.mem_span_singleton
  rwa [span_idealGenerator] at he

lemma sum_dividedRows_residualGram_rescale {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (a : n → ℂ) (R : Finset O) (w : O → ℂ) (d : O) :
    (∑ z ∈ dividedRows R d,
      w (d * z) * residualGram D cols (fun j => if D ∣ cols j then a j else 0) (d * z)) =
      ∑ z ∈ dividedRows R d,
        w (d * z) * residualGram D cols (descendedCoefficient D cols a d) z := by
  apply Finset.sum_congr rfl
  intro z _
  rw [residualGram_rescale D cols hcols a]

theorem cubic_gcd_mobius_descent {n : Type*} [Fintype n]
    (D : Ideal O) (hD : primaryGenerator D ≠ 0)
    (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (a : n → ℂ) (R : Finset O) (w : O → ℂ) :
    (∑ z ∈ R, w z * ∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          ∑ z ∈ dividedRows R (idealGenerator E),
            w (idealGenerator E * z) *
              residualGram D cols (descendedCoefficient D cols a (idealGenerator E)) z := by
  let b : n → ℂ := fun j => if D ∣ cols j then a j else 0
  have ht (z : O) : (∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      (star (cubicRow D z) * cubicRow D z) * residualGram D cols b z := by
    simp only [cubicGcdTerm_eq_quotient D (primaryGenerator_ne_zero_ideal D hD),
      residualGram, b, Finset.mul_sum]
  calc
    _ = ∑ z ∈ R, ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          (if idealGenerator E ∣ z then w z * residualGram D cols b z else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [ht, cubicRow_common_mobius D hD, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      rw [ideal_dvd_span_iff_generator]
      split_ifs <;> ring
    _ = ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          ∑ z ∈ R, if idealGenerator E ∣ z then w z * residualGram D cols b z else 0 := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [sum_divisible_rows]
      exact congrArg ((UniqueFactorizationMonoid.moebius E : ℂ) * ·)
        (sum_dividedRows_residualGram_rescale D cols hcols a R w (idealGenerator E))

end
end SevenEighths.CubicSieve

end OAI

end Source1463

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/DescentEnergy.lean; sha256: cf5044c572ab37adb4ba419e4963f8e570a190fbf06bcf23136e6d6645ad2c09 -/
section Source1464
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve IdealMobiusDivisorSum DivisorBlockCauchy
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma descendedCoefficient_norm_le {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (a : n → ℂ) (d : O) (j : n) :
    ‖descendedCoefficient D cols a d j‖ ≤ ‖if D ∣ cols j then a j else 0‖ := by
  unfold descendedCoefficient
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right
    (elementCharacter_norm_le_one _ (totalQuotient_cubic_admissible D _ (hc j)).2 d)
    (norm_nonneg _)).trans_eq (one_mul _)

theorem descended_energy_small_power {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (N : ℝ) (hN0 : 0 ≤ N)
    (hN : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ D ∈ columnDivisorPool cols, ∑ E ∈ idealDivisors D,
      ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) ≤
        (divisorConstant ε hε * N^ε)^2 * ∑ j, ‖a j‖^2 := by
  have hc0 (j : n) : cols j ≠ 0 := primaryGenerator_ne_zero_ideal _ (hc j).2
  let B := divisorConstant ε hε * N^ε
  have hB : 0 ≤ B := mul_nonneg (divisorConstant_pos ε hε).le (Real.rpow_nonneg hN0 _)
  have hcard (D : Ideal O) (hD : D ∈ columnDivisorPool cols) :
      ((idealDivisors D).card : ℝ) ≤ B := by
    have hd := columnDivisorPool_norm_bounds cols hc0 N hN D hD
    have hd0 : D ≠ 0 := by
      intro he
      have hh := hd.1
      norm_num [he] at hh
    exact ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 D hd0).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hd.2 hε.le)
        (divisorConstant_pos ε hε).le)
  calc
    _ ≤ ∑ D ∈ columnDivisorPool cols, B * ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
      apply Finset.sum_le_sum
      intro D hD
      calc
        _ ≤ ∑ E ∈ idealDivisors D, ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
          apply Finset.sum_le_sum
          intro E hE
          exact Finset.sum_le_sum (fun j hj => pow_le_pow_left₀ (norm_nonneg _)
            (descendedCoefficient_norm_le D cols hc a (idealGenerator E) j) 2)
        _ = ((idealDivisors D).card : ℝ) * ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD) (by positivity)
    _ = B * (∑ D ∈ columnDivisorPool cols, ∑ j, ‖if D ∣ cols j then a j else 0‖^2) := by
      rw [Finset.mul_sum]
    _ ≤ B * (B * ∑ j, ‖a j‖^2) := mul_le_mul_of_nonneg_left
      (divisor_mask_energy_small_power ε hε _ cols hc0 N hN a) hB
    _ = _ := by dsimp [B]; ring

end
end SevenEighths.CubicSieve

end OAI

end Source1464

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/CompactDescent.lean; sha256: ed67b145108a15338ce90560e9d25c6a5199fc54f4176c7a0f3b117343c02c66 -/
section Source1465
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve IdealMobiusDivisorSum SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma majorant_radial_summable (P : O → ℂ) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => rowMajorant (‖eisEmbedding z‖^2 / M) * P z) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall M) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside M hM z hz, zero_mul]

lemma majorant_rescale (d z : O) (_hd : d ≠ 0) (M : ℝ) :
    rowMajorant (‖eisEmbedding (d*z)‖^2 / M) =
      rowMajorant (‖eisEmbedding z‖^2 / (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) := by
  rw [map_mul, norm_mul, mul_pow, eisEmbedding_norm_sq_eq_absNorm_span d]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

lemma dividedMajorant_tsum (P : O → ℂ) (d : O) (hd : d ≠ 0)
    (M : ℝ) (hM : 0 < M) :
    (∑ z ∈ dividedRows (rowMajorantBall M) d,
      rowMajorant (‖eisEmbedding (d*z)‖^2 / M) * P z) =
      ∑' z : O, rowMajorant (‖eisEmbedding z‖^2 /
        (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) * P z := by
  symm
  rw [← show (fun z : O => rowMajorant (‖eisEmbedding (d*z)‖^2 / M) * P z) =
      (fun z : O => rowMajorant (‖eisEmbedding z‖^2 /
        (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) * P z) by
          funext z; rw [majorant_rescale d z hd M]]
  apply tsum_eq_sum
  intro z hz
  have hout : d*z ∉ rowMajorantBall M := by
    intro hin
    apply hz
    apply Finset.mem_image.mpr
    refine ⟨d*z, Finset.mem_filter.mpr ⟨hin, dvd_mul_right d z⟩, ?_⟩
    apply mul_left_cancel₀ hd
    exact elementQuotient_mul d (d*z) (dvd_mul_right d z)
  rw [rowMajorant_zero_outside M hM (d*z) hout, zero_mul]

lemma majorant_coprime_tsum {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowMajorant (‖eisEmbedding z‖^2 / M) *
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0) =
      cubicSmoothedCoprime cols a rowMajorant M := by
  have hs (j k : n) := majorant_radial_summable
    (fun z => if IsCoprime (cols j) (cols k) then
      star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0) M hM
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun j hj => summable_sum (fun k hk => hs j k))]
  unfold cubicSmoothedCoprime
  apply Finset.sum_congr rfl
  intro j hj
  rw [Summable.tsum_finsetSum (fun k hk => hs j k)]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · simp only [ite_eq_left hcop]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro z
    simp only [star_mul]
    ring
  · simp only [ite_eq_right hcop, mul_zero, tsum_zero]

lemma compact_gcd_mobius_descent {n : Type*} [Fintype n]
    (D : Ideal O) (hD : primaryGenerator D ≠ 0)
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (M : ℝ) (hM : 0 < M) :
    (∑ z ∈ rowMajorantBall M, rowMajorant (‖eisEmbedding z‖^2 / M) *
      ∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      ∑ E ∈ idealDivisors D, (UniqueFactorizationMonoid.moebius E : ℂ) *
        cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (idealGenerator E)) rowMajorant
          (M / (Ideal.absNorm E : ℝ)) := by
  rw [cubic_gcd_mobius_descent D hD cols hc a]
  apply Finset.sum_congr rfl
  intro E hE
  have hE0 : E ≠ 0 := by
    intro he
    have hh := (mem_idealDivisors (primaryGenerator_ne_zero_ideal D hD)).mp hE
    rw [he, zero_dvd_iff] at hh
    exact primaryGenerator_ne_zero_ideal D hD hh
  have hgen := idealGenerator_ne_zero E hE0
  congr 1
  rw [dividedMajorant_tsum _ _ hgen M hM, span_idealGenerator]
  apply majorant_coprime_tsum
  have hNE : 0 < (Ideal.absNorm E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
  exact div_pos hM hNE

lemma gcdPool_cubic_admissible {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (D : Ideal O) (hD : D ∈ gcdPool cols) : Admissible D := by
  obtain ⟨⟨j,k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  exact cubic_admissible_of_dvd (hc j) (gcd_dvd_left _ _)

lemma gcdPool_subset_columnDivisorPool {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, cols j ≠ 0) :
    gcdPool cols ⊆ columnDivisorPool cols := by
  intro D hD
  obtain ⟨⟨j,k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  exact mem_columnDivisorPool_of_dvd cols hc j _ (gcd_dvd_left _ _)

theorem finite_energy_le_compact_descendants {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (R : Finset O) (M : ℝ) (hM : 0 < M)
    (hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M) :
    (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
      ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        ‖cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (idealGenerator E)) rowMajorant
          (M / (Ideal.absNorm E : ℝ))‖ := by
  have hs := finite_row_energy_le_rowMajorant
    (fun z => ∑ j, cubicRow (cols j) z * a j) R M hM hR
  apply hs.trans
  apply (Complex.re_le_norm _).trans
  rw [rowMajorant_tsum_eq_sum _ M hM,
    cubic_weighted_energy_eq_gcd_blocks (rowMajorantBall M) _ cols a]
  have he (D : Ideal O) (hD : D ∈ gcdPool cols) :=
    compact_gcd_mobius_descent D (gcdPool_cubic_admissible cols hc D hD).2 cols hc a M hM
  calc
    _ ≤ ∑ D ∈ gcdPool cols,
        ‖∑ z ∈ rowMajorantBall M, rowMajorant (‖eisEmbedding z‖^2 / M) *
          ∑ j, ∑ k, cubicGcdTerm D cols a z j k‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro D hD
      rw [he D hD]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro E hE
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (QuadraticInitialBound.norm_ideal_moebius_le_one E)
        (norm_nonneg _)).trans_eq (one_mul _)

end
end SevenEighths.CubicSieve

end OAI

end Source1465

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/QuotientColumns.lean; sha256: a360f895d7c4b5f67b2a0c7eaa22cecb9a7c08b5346f15a392111c0eefae3583 -/
section Source1466
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma finite_sum_restrict {n A : Type*} [Fintype n] [AddCommMonoid A]
    (p : n → Prop) (f : n → A) (hf : ∀ j, ¬p j → f j = 0) :
    (∑ j, f j) = ∑ j : {j // p j}, f j.val := by
  have h := Fintype.sum_subtype_add_sum_subtype p f
  have hz : (∑ j : {j // ¬p j}, f j.val) = 0 :=
    Finset.sum_eq_zero (fun j hj => hf j.val j.property)
  rw [hz, add_zero] at h
  exact h.symm

lemma cubicSmoothedCoprime_restrict {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (p : n → Prop)
    (ha : ∀ j, ¬p j → a j = 0) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicSmoothedCoprime cols a W M =
      cubicSmoothedCoprime (fun j : {j // p j} => cols j.val) (fun j => a j.val) W M := by
  unfold cubicSmoothedCoprime
  rw [finite_sum_restrict p _ (by
    intro j hj
    simp [ha j hj])]
  apply Finset.sum_congr rfl
  intro j hj
  exact finite_sum_restrict p _ (by
    intro k hk
    simp [ha k hk])

def quotientColumn {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (j : {j // D ∣ cols j}) : Ideal O := idealQuotient D (cols j.val)

def quotientCoefficient {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (d : O) (j : {j // D ∣ cols j}) : ℂ :=
  cubicRow (quotientColumn D cols j) d * a j.val

lemma quotientColumn_injective {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : Function.Injective cols) : Function.Injective (quotientColumn D cols) := by
  intro j k he
  exact Subtype.ext (hc (idealQuotient_injective_on D j.property k.property he))

lemma quotientColumn_admissible {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (j : {j // D ∣ cols j}) :
    Admissible (quotientColumn D cols j) := cubic_admissible_quotient (hc j.val) j.property

lemma cubic_quotient_in_shell {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (N : ℝ)
    (hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (j : {j // D ∣ cols j}) :
    (N / (Ideal.absNorm D : ℝ))/2 ≤ (Ideal.absNorm (quotientColumn D cols j) : ℝ) ∧
      (Ideal.absNorm (quotientColumn D cols j) : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero (primaryGenerator_ne_zero_ideal _ (hc j.val).2) j.property
  have hDN : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
  have he : (Ideal.absNorm (quotientColumn D cols j) : ℝ) * (Ideal.absNorm D : ℝ) =
      (Ideal.absNorm (cols j.val) : ℝ) := by
    rw [mul_comm, ← Nat.cast_mul, ← map_mul, quotientColumn, idealQuotient_mul j.property]
  refine ⟨?_, idealQuotient_norm_le hD0 j.property N (hcols j.val).2⟩
  have hh : (N/2) / (Ideal.absNorm D : ℝ) ≤ (Ideal.absNorm (quotientColumn D cols j) : ℝ) := by
    apply (div_le_iff₀ hDN).mpr
    rw [he]
    exact (hcols j.val).1
  convert hh using 1; ring

lemma compact_descendant_restrict {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (d : O)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
      (descendedCoefficient D cols a d) W M =
    cubicSmoothedCoprime (quotientColumn D cols) (quotientCoefficient D cols a d) W M := by
  rw [cubicSmoothedCoprime_restrict _ _ (fun j => D ∣ cols j) (by
    intro j hj
    simp only [descendedCoefficient, ite_eq_right hj, mul_zero])]
  have hc : (fun j : {j // D ∣ cols j} => totalQuotient D (cols j.val)) = quotientColumn D cols := by
    funext j
    simp only [totalQuotient, ite_eq_left j.property, quotientColumn]
  have ha : (fun j : {j // D ∣ cols j} => descendedCoefficient D cols a d j.val) =
      quotientCoefficient D cols a d := by
    funext j
    simp only [descendedCoefficient, totalQuotient, ite_eq_left j.property, quotientCoefficient, quotientColumn]
  rw [hc, ha]

lemma quotientCoefficient_energy {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (d : O) :
    (∑ j : {j // D ∣ cols j}, ‖quotientCoefficient D cols a d j‖^2) =
      ∑ j, ‖descendedCoefficient D cols a d j‖^2 := by
  rw [finite_sum_restrict (fun j => D ∣ cols j) _ (by
    intro j hj
    simp only [descendedCoefficient, ite_eq_right hj, mul_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [quotientCoefficient, quotientColumn, descendedCoefficient, totalQuotient, ite_eq_left j.property]

end
end SevenEighths.CubicSieve

end OAI

end Source1466

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/DualShell.lean; sha256: 849de0df95e2ec9a75b7955888d76d290cb1aa89885ee0dec7e9f101a977de13 -/
section Source1467
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicDualRow_zero {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hunit : ∀ j, cols j ≠ 1) (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicDualRow cols hc a W M 0 = 0 := by
  unfold cubicDualRow
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro k hk
  rw [cubicRow_zero_of_ne_one _ (hc j) (hunit j)]
  simp

theorem cubic_dual_shell_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M K N : ℝ) (_hM : 0 < M) (_hK : 0 < K) (_hN : 0 < N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, K / 2 ≤ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ∧
          (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ K)
        (hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ),
        (1 + M * K / N ^ 2) ^ A *
          (∑ i, ‖cubicDualRow cols (fun j => (hcols j).1) a W M (rows i)‖) ≤
          C * (elementSieveNorm K N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) *
              ((2 / N) * ∑ j, ‖a j‖ ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := cubic_frequency_shell_bound W A
  refine ⟨C, hC, ?_⟩
  intro m n _ _ _ _ ε hε M K N hM hK hN rows cols hr hc hrows hcols a
  have he := cubicDualCoefficient_energy cols (fun j => (hcols j).1) a N hN
    (fun j => (hcols j).2.1)
  have h := hb ε hε M K N hM hK hN rows cols hr hc hrows hcols
    (cubicDualCoefficient cols (fun j => (hcols j).1) a)
    (cubicDualCoefficient cols (fun j => (hcols j).1) a)
    ((2 / N) * ∑ j, ‖a j‖ ^ 2) (by positivity) he he
  simpa only [cubicDualRow_eq_gram] using h

end
end SevenEighths.CubicSieve

end OAI

end Source1467

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/FrequencyDyads.lean; sha256: c243dc6a62ac7f8b54b949b8a867dc41f0f2a54ac1285408deed0a4e8c700e0d -/
section Source1468
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def frequencyDyad (j : ℕ) : Finset O :=
  (elementRange ((2 : ℝ)^j)).filter (fun h => Nat.clog 2 (Ideal.absNorm (Ideal.span {h})) = j)

lemma mem_frequencyDyad (h : O) (j : ℕ) :
    h ∈ frequencyDyad j ↔ h ≠ 0 ∧ Nat.clog 2 (Ideal.absNorm (Ideal.span {h})) = j := by
  simp only [frequencyDyad, Finset.mem_filter, mem_elementRange]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hh, hj⟩
    refine ⟨⟨hh, ?_⟩, hj⟩
    have hu := Nat.le_pow_clog (by norm_num : 1 < 2) (Ideal.absNorm (Ideal.span {h}))
    rw [hj] at hu
    exact_mod_cast hu

lemma frequencyDyad_bounds (j : ℕ) (h : O) (hh : h ∈ frequencyDyad j) :
    h ≠ 0 ∧ (2 : ℝ)^j / 2 ≤ (Ideal.absNorm (Ideal.span {h}) : ℝ) ∧
      (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ (2 : ℝ)^j := by
  obtain ⟨hn, hj⟩ := (mem_frequencyDyad h j).mp hh
  have hnorm : Ideal.absNorm (Ideal.span {h}) ≠ 0 := by
    exact Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hn)
  have hu := Nat.le_pow_clog (by norm_num : 1 < 2) (Ideal.absNorm (Ideal.span {h}))
  have hl := two_pow_clog_le_double _ (Nat.one_le_iff_ne_zero.mpr hnorm)
  rw [hj] at hu hl
  refine ⟨hn, ?_, by exact_mod_cast hu⟩
  have hr : (2 : ℝ)^j ≤ 2 * (Ideal.absNorm (Ideal.span {h}) : ℝ) := by exact_mod_cast hl
  linarith

def frequencyDyadicEquiv : {h : O // h ≠ 0} ≃ Σ j : ℕ, frequencyDyad j where
  toFun h := ⟨Nat.clog 2 (Ideal.absNorm (Ideal.span {h.val})),
    ⟨h.val, (mem_frequencyDyad _ _).mpr ⟨h.property, rfl⟩⟩⟩
  invFun h := ⟨h.2.val, ((mem_frequencyDyad _ _).mp h.2.property).1⟩
  left_inv h := by cases h; rfl
  right_inv h := by
    rcases h with ⟨j, h, hh⟩
    have hj := ((mem_frequencyDyad h j).mp hh).2
    dsimp only
    subst j
    rfl

theorem tsum_frequencyDyads (f : O → ℂ) (hf : Summable f) (hzero : f 0 = 0) :
    (∑' h : O, f h) = ∑' j : ℕ, ∑ h : frequencyDyad j, f h.val := by
  have he : (∑' h : O, f h) = ∑' h : {h : O // h ≠ 0}, f h.val := by
    symm
    exact tsum_subtype_eq_of_support_subset (fun h hh => by
      change h ≠ 0
      intro hz
      exact hh (hz ▸ hzero))
  rw [he]
  let g := (fun h : {h : O // h ≠ 0} => f h.val) ∘ frequencyDyadicEquiv.symm
  have hg : Summable g := frequencyDyadicEquiv.symm.summable_iff.mpr (hf.subtype _)
  calc
    _ = ∑' h, g h := (frequencyDyadicEquiv.symm.tsum_eq _).symm
    _ = ∑' j, ∑' h, g ⟨j,h⟩ := Summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable) hg
    _ = _ := by
      apply tsum_congr
      intro j
      rw [tsum_fintype]
      rfl

theorem tsum_frequencyDyads_with_zero (f : O → ℂ) (hf : Summable f) :
    (∑' h : O, f h) = f 0 + ∑' j : ℕ, ∑ h : frequencyDyad j, f h.val := by
  have he : (∑' h : O, f h) = f 0 + ∑' h : {h : O // h ≠ 0}, f h.val := by
    have hs := (hf.sum_add_tsum_compl (s := {0})).symm
    have hset : ((↑({0} : Finset O) : Set O)ᶜ) = {h : O | h ≠ 0} := by
      ext h
      simp
    rw [hset] at hs
    simpa only [Finset.sum_singleton, Set.coe_ofPred] using hs
  rw [he]
  congr 1
  let g := (fun h : {h : O // h ≠ 0} => f h.val) ∘ frequencyDyadicEquiv.symm
  have hg : Summable g := frequencyDyadicEquiv.symm.summable_iff.mpr (hf.subtype _)
  calc
    _ = ∑' h, g h := (frequencyDyadicEquiv.symm.tsum_eq _).symm
    _ = ∑' j, ∑' h, g ⟨j,h⟩ := Summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable) hg
    _ = _ := by
      apply tsum_congr
      intro j
      rw [tsum_fintype]
      rfl

end
end SevenEighths.CubicSieve

end OAI

end Source1468

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Majorant.lean; sha256: a8e52271c9e058808b50fc4a162ee79ccf958465a08be04b541fa6701e0dfe75 -/
section Source1469
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

def frequencyMajorant (M N : ℝ) (j : ℕ) : ℝ :=
  elementSieveNorm ((2 : ℝ)^j) N / (1 + M * (2 : ℝ)^j / N^2)^3

lemma frequencyMajorant_nonneg (M N : ℝ) (hM : 0 ≤ M) (j : ℕ) :
    0 ≤ frequencyMajorant M N j := by
  unfold frequencyMajorant
  exact div_nonneg (elementSieveNorm_nonneg _ _) (by positivity)

lemma frequencyMajorant_geometric (M N : ℝ) (hM : 0 < M) (hN : 1 ≤ N) (j : ℕ) :
    frequencyMajorant M N j ≤
      (QuadraticInitialBound.initialSieveConstant * (1 + (⌈N⌉₊ : ℝ)^2) /
        (M / N^2)^3) * ((1 / 4 : ℝ)^j) := by
  let K : ℝ := (2 : ℝ)^j
  let c : ℝ := M / N^2
  let Q : ℝ := (⌈N⌉₊ : ℝ)^2
  let C : ℝ := QuadraticInitialBound.initialSieveConstant
  have hK : 1 ≤ K := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hK0 : 0 < K := by positivity
  have hN0 : 0 < N := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hQ : 0 ≤ Q := sq_nonneg _
  have hC : 0 ≤ C := QuadraticInitialBound.initialSieveConstant_pos.le
  have hi : elementSieveNorm K N ≤ C * (1 + Q) * K := by
    apply (elementSieveNorm_initial K N hK hN).trans
    dsimp only [C, Q]
    nlinarith [mul_nonneg hC (mul_nonneg hQ (sub_nonneg.mpr hK))]
  have hden : (c*K)^3 ≤ (1+c*K)^3 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hgeom : (K^2)⁻¹ = (1/4 : ℝ)^j := by
    dsimp only [K]
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, ← inv_pow]
    norm_num
  change elementSieveNorm K N / (1 + M*K/N^2)^3 ≤ _
  rw [show M*K/N^2 = c*K by dsimp [c]; ring]
  calc
    _ ≤ (C*(1+Q)*K) / (1+c*K)^3 := div_le_div_of_nonneg_right hi (by positivity)
    _ ≤ (C*(1+Q)*K) / (c*K)^3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = (C*(1+Q)/c^3) * (K^2)⁻¹ := by field_simp
    _ = _ := by rw [hgeom]

theorem frequencyMajorant_summable (M N : ℝ) (hM : 0 < M) (hN : 1 ≤ N) :
    Summable (frequencyMajorant M N) := by
  have hg : Summable (fun j : ℕ => (1/4 : ℝ)^j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact (hg.mul_left _).of_nonneg_of_le
    (frequencyMajorant_nonneg M N hM.le) (frequencyMajorant_geometric M N hM hN)

end
end SevenEighths.CubicSieve

end OAI

end Source1469

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/ZeroMode.lean; sha256: 0817a88225176c95c707937a6efafa77342effe02778c3ad0f55db5423c2f508 -/
section Source1470
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

@[simp] lemma cubicRow_one (z : O) : cubicRow 1 z = 1 := by
  simp only [cubicRow, CubicJacobiGlobal.idealSymbol_one, map_one]

theorem cubicDualRow_zero_bound {n : Type*} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hinj : Function.Injective cols) (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M N : ℝ)
    (hN : 0 < N) (hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ)) :
    ‖cubicDualRow cols hc a W M 0‖ ≤
      ((2/N) * ∑ j, ‖a j‖^2) * ‖paperRadialFourier W 0‖ := by
  by_cases hu : ∃ j, cols j = 1
  · obtain ⟨j₀, hj₀⟩ := hu
    have ho (j : n) (hj : j ≠ j₀) : cols j ≠ 1 := by
      intro he
      exact hj (hinj (he.trans hj₀.symm))
    have he : cubicDualRow cols hc a W M 0 =
        (star (cubicDualCoefficient cols hc a j₀) * cubicDualCoefficient cols hc a j₀) *
          paperRadialFourier W 0 := by
      rw [cubicDualRow_eq_gram]
      rw [Finset.sum_eq_single j₀]
      · rw [Finset.sum_eq_single j₀]
        · simp only [hj₀, cubicRow_one, one_mul, Ideal.span_singleton_zero,
            Ideal.absNorm_bot, Nat.cast_zero, mul_zero, zero_div, ite_eq_left isCoprime_one_left]
        · intro k hk hkj
          rw [cubicRow_zero_of_ne_one _ (hc k) (ho k hkj)]
          simp
        · simp
      · intro j hj hjj
        rw [cubicRow_zero_of_ne_one _ (hc j) (ho j hjj)]
        simp
      · simp
    rw [he, norm_mul, norm_mul, norm_star, ← pow_two]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (Finset.single_le_sum (fun j hj => sq_nonneg ‖cubicDualCoefficient cols hc a j‖)
      (Finset.mem_univ j₀)).trans (cubicDualCoefficient_energy cols hc a N hN hcols)
  · have hz : ∀ j, cols j ≠ 1 := fun j hj => hu ⟨j,hj⟩
    rw [cubicDualRow_zero cols hc hz a W M, norm_zero]
    positivity

end
end SevenEighths.CubicSieve

end OAI

end Source1470

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/Recurrence.lean; sha256: 620bf78be18220b14a53a23d9c7acfb05fe4b63ce080772b11396de4c53e1edd -/
section Source1471
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem cubic_smoothed_frequency_recurrence (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M) (_hN : 1 ≤ N)
        (cols : n → Ideal O) (_hc : Function.Injective cols)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (_hunit : ∀ j, cols j ≠ 1) (a : n → ℂ),
        ‖cubicSmoothedCoprime cols a W M‖ ≤
          M * (C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
            ((2 / N) * ∑ j, ‖a j‖^2) * ∑' l : ℕ, frequencyMajorant M N l) := by
  obtain ⟨C, hC, hshell⟩ := cubic_dual_shell_bound W 3
  refine ⟨C, hC, ?_⟩
  intro n _ _ ε hε M N hM hN cols hc hcols hunit a
  have hN0 : 0 < N := by linarith
  let f : O → ℂ := cubicDualRow cols (fun j => (hcols j).1) a W M
  let B : ℝ := C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
    ((2 / N) * ∑ j, ‖a j‖^2)
  have hf : Summable f := cubicDualRow_summable cols (fun j => (hcols j).1) a W M hM
  have hf0 : f 0 = 0 := cubicDualRow_zero cols (fun j => (hcols j).1) hunit a W M
  have hblock (l : ℕ) : ‖∑ h : frequencyDyad l, f h.val‖ ≤ B * frequencyMajorant M N l := by
    have hp := hshell ε hε M ((2 : ℝ)^l) N hM (by positivity) hN0
      (fun h : frequencyDyad l => h.val) cols Subtype.val_injective hc
      (fun h => (frequencyDyad_bounds l h.val h.property).2) hcols a
    have hd : 0 < (1 + M * (2 : ℝ)^l / N^2)^3 := by positivity
    have hs : (∑ h : frequencyDyad l, ‖f h.val‖) ≤ B * frequencyMajorant M N l := by
      have he : B * frequencyMajorant M N l =
          (C * (elementSieveNorm ((2 : ℝ)^l) N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
              ((2 / N) * ∑ j, ‖a j‖^2))) / (1 + M * (2 : ℝ)^l / N^2)^3 := by
        dsimp only [B, frequencyMajorant]
        ring
      rw [he]
      apply (le_div_iff₀ hd).mpr
      simpa only [mul_comm] using hp
    exact (norm_sum_le _ _).trans hs
  have hg : Summable (fun l => B * frequencyMajorant M N l) :=
    (frequencyMajorant_summable M N hM hN).mul_left B
  have hb := (hg.of_norm_bounded hblock).hasSum.norm_le_of_bounded hg.hasSum hblock
  rw [tsum_mul_left] at hb
  rw [cubicSmoothedCoprime_poisson cols (fun j => (hcols j).1) a W M hM, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  change M * ‖∑' h : O, f h‖ ≤ _
  rw [tsum_frequencyDyads f hf hf0]
  exact mul_le_mul_of_nonneg_left hb hM.le

theorem cubic_smoothed_frequency_recurrence_all (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M) (_hN : 1 ≤ N)
        (cols : n → Ideal O) (_hc : Function.Injective cols)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a : n → ℂ),
        ‖cubicSmoothedCoprime cols a W M‖ ≤
          M * (((2 / N) * ∑ j, ‖a j‖^2) * ‖paperRadialFourier W 0‖ + C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
            ((2 / N) * ∑ j, ‖a j‖^2) * ∑' l : ℕ, frequencyMajorant M N l) := by
  obtain ⟨C, hC, hshell⟩ := cubic_dual_shell_bound W 3
  refine ⟨C, hC, ?_⟩
  intro n _ _ ε hε M N hM hN cols hc hcols a
  have hN0 : 0 < N := by linarith
  let f : O → ℂ := cubicDualRow cols (fun j => (hcols j).1) a W M
  let B : ℝ := C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
    ((2 / N) * ∑ j, ‖a j‖^2)
  have hf : Summable f := cubicDualRow_summable cols (fun j => (hcols j).1) a W M hM
  have hblock (l : ℕ) : ‖∑ h : frequencyDyad l, f h.val‖ ≤ B * frequencyMajorant M N l := by
    have hp := hshell ε hε M ((2 : ℝ)^l) N hM (by positivity) hN0
      (fun h : frequencyDyad l => h.val) cols Subtype.val_injective hc
      (fun h => (frequencyDyad_bounds l h.val h.property).2) hcols a
    have hd : 0 < (1 + M * (2 : ℝ)^l / N^2)^3 := by positivity
    have hs : (∑ h : frequencyDyad l, ‖f h.val‖) ≤ B * frequencyMajorant M N l := by
      have he : B * frequencyMajorant M N l =
          (C * (elementSieveNorm ((2 : ℝ)^l) N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
              ((2 / N) * ∑ j, ‖a j‖^2))) / (1 + M * (2 : ℝ)^l / N^2)^3 := by
        dsimp only [B, frequencyMajorant]
        ring
      rw [he]
      apply (le_div_iff₀ hd).mpr
      simpa only [mul_comm] using hp
    exact (norm_sum_le _ _).trans hs
  have hg : Summable (fun l => B * frequencyMajorant M N l) :=
    (frequencyMajorant_summable M N hM hN).mul_left B
  have hb := (hg.of_norm_bounded hblock).hasSum.norm_le_of_bounded hg.hasSum hblock
  rw [tsum_mul_left] at hb
  rw [cubicSmoothedCoprime_poisson cols (fun j => (hcols j).1) a W M hM, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  change M * ‖∑' h : O, f h‖ ≤ _
  rw [tsum_frequencyDyads_with_zero f hf]
  apply mul_le_mul_of_nonneg_left _ hM.le
  exact (norm_add_le _ _).trans (add_le_add
    (cubicDualRow_zero_bound cols (fun j => (hcols j).1) hc a W M N hN0
      (fun j => (hcols j).2.1)) hb)

end
end SevenEighths.CubicSieve

end OAI

end Source1471

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/CommonFactorBound.lean; sha256: ea0779180b6d3f6f7bbb834d351c8d490b563a7f6f1d71a09a8b33778699499d -/
section Source1472
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve IdealMobiusDivisorSum SecondPassArithmetic EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def frequencyCost (C ε : ℝ) (hε : 0 < ε) (M N : ℝ) : ℝ :=
  M * (2/N) * (‖paperRadialFourier rowMajorant 0‖ +
    C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
      ∑' l : ℕ, frequencyMajorant M N l)

theorem cubic_common_factor_frequency_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M)
        (cols : n → Ideal O) (_hinj : Function.Injective cols)
        (_hc : ∀ j, Admissible (cols j))
        (_hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a : n → ℂ) (R : Finset O)
        (_hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M),
        (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
          ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
            frequencyCost C ε hε (M / (Ideal.absNorm E : ℝ)) (N / (Ideal.absNorm D : ℝ)) *
              ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2 := by
  obtain ⟨C,hC,hrec⟩ := cubic_smoothed_frequency_recurrence_all rowMajorant
  refine ⟨C,hC,?_⟩
  intro n _ _ ε hε M N hM cols hinj hc hcols a R hR
  apply (finite_energy_le_compact_descendants cols hc a R M hM hR).trans
  apply Finset.sum_le_sum
  intro D hD
  have hc0 (j : n) : cols j ≠ 0 := primaryGenerator_ne_zero_ideal _ (hc j).2
  have hDcol := gcdPool_subset_columnDivisorPool cols hc0 hD
  have hDN := columnDivisorPool_norm_bounds cols hc0 N (fun j => (hcols j).2) D hDcol
  have hD0 := gcdPool_ne_zero cols hc0 D hD
  have hDN0 : 0 < (Ideal.absNorm D : ℝ) := by linarith [hDN.1]
  have hNshort : 1 ≤ N / (Ideal.absNorm D : ℝ) := (one_le_div hDN0).mpr hDN.2
  apply Finset.sum_le_sum
  intro E hE
  have hEdiv := (mem_idealDivisors hD0).mp hE
  have hE0 : E ≠ 0 := ne_zero_of_dvd_ne_zero hD0 hEdiv
  have hEN : 0 < (Ideal.absNorm E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
  rw [compact_descendant_restrict]
  have hh := hrec ε hε (M / (Ideal.absNorm E : ℝ)) (N / (Ideal.absNorm D : ℝ))
    (div_pos hM hEN) hNshort (quotientColumn D cols) (quotientColumn_injective D cols hinj)
    (fun j => ⟨quotientColumn_admissible D cols hc j, cubic_quotient_in_shell D cols hc N hcols j⟩)
    (quotientCoefficient D cols a (idealGenerator E))
  rw [quotientCoefficient_energy] at hh
  convert hh using 1
  dsimp only [frequencyCost]
  ring

theorem common_factor_uniform_cost {n : Type*} [Fintype n]
    (C ε U M N : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hN : 0 ≤ N)
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hnorm : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ)
    (hcost : ∀ D ∈ gcdPool cols, ∀ E ∈ idealDivisors D,
      frequencyCost C ε hε (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) ≤ U) :
    (∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
      frequencyCost C ε hε (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) *
        ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) ≤
      U*(DivisorBlockCauchy.divisorConstant ε hε*N^ε)^2*∑ j, ‖a j‖^2 := by
  have he := descended_energy_small_power ε hε cols hc N hN hnorm a
  have hsub := gcdPool_subset_columnDivisorPool cols
    (fun j => primaryGenerator_ne_zero_ideal _ (hc j).2)
  calc
    _ ≤ ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        U * ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2 := by
      apply Finset.sum_le_sum
      intro D hD
      apply Finset.sum_le_sum
      intro E hE
      exact mul_le_mul_of_nonneg_right (hcost D hD E hE) (by positivity)
    _ = U*(∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) := by
      simp only [Finset.mul_sum]
    _ ≤ U*(∑ D ∈ columnDivisorPool cols, ∑ E ∈ idealDivisors D,
        ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) := by
      apply mul_le_mul_of_nonneg_left _ hU
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun D hD hnot => by positivity)
    _ ≤ U*((DivisorBlockCauchy.divisorConstant ε hε*N^ε)^2*∑ j, ‖a j‖^2) :=
      mul_le_mul_of_nonneg_left he hU
    _ = _ := by ring

end
end SevenEighths.CubicSieve

end OAI

end Source1472

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/DescendantBounds.lean; sha256: 9f9ad8e2180a6e50339d7596d792adfdb34e25c33b99c9eaed2658d1ff232a69 -/
section Source1473
namespace OAI

namespace SevenEighths.CubicSieve
noncomputable section

lemma descendant_cross_le (M N D E : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) :
    ((M/E)*(N/D))^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact mul_le_mul (div_le_self hM hE) (div_le_self hN hD) (by positivity) hM

lemma descendant_asymmetric_le (M N D E ξ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hED : E ≤ D) (hξ : 1 ≤ ξ) :
    (M/E)^(1-ξ)*(N/D)^(2*ξ-1) ≤ M^(1-ξ)*N^(2*ξ-1) := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hp : E^(ξ-1) ≤ D^(2*ξ-1) :=
    (Real.rpow_le_rpow hE0.le hED (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hD (by linarith))
  have hr : E^(ξ-1)/D^(2*ξ-1) ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hD0 _)).mpr hp
  have he : E^(1-ξ) = (E^(ξ-1))⁻¹ := by
    rw [← Real.rpow_neg hE0.le]
    congr 1
    ring
  calc
    _ = (M^(1-ξ)*N^(2*ξ-1))*(E^(ξ-1)/D^(2*ξ-1)) := by
      rw [Real.div_rpow hM.le hE0.le, Real.div_rpow hN.le hD0.le, he]
      simp only [div_eq_mul_inv, inv_inv]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hr

lemma descendant_loss_le (M N D E δ ε : ℝ) (hM : 1 ≤ M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hED : E ≤ D) (hDN : D ≤ N)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    (M/E)^(-δ)*(N/D)^(3*δ+ε) ≤ N^(4*δ+ε) := by
  have hM0 : 0 < M := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hEM : E/M ≤ N := (div_le_self hE0.le hM).trans (hED.trans hDN)
  have hfirst : (M/E)^(-δ) ≤ N^δ := by
    rw [Real.rpow_neg (div_pos hM0 hE0).le, ← Real.inv_rpow (div_pos hM0 hE0).le, inv_div]
    exact Real.rpow_le_rpow (by positivity) hEM hδ
  have hsecond : (N/D)^(3*δ+ε) ≤ N^(3*δ+ε) :=
    Real.rpow_le_rpow (by positivity) (div_le_self hN.le hD) (by positivity)
  calc
    _ ≤ N^δ*N^(3*δ+ε) := mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hN]
      congr 1
      ring

lemma descendant_unit_scale_le (M N D E : ℝ) (hM : 0 ≤ M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hDN : D ≤ N) :
    (M/E)*(2/(N/D)) ≤ 2*M := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hY : 1 ≤ N/D := (one_le_div hD0).mpr hDN
  have hr : 2/(N/D) ≤ 2 := div_le_self (by norm_num) hY
  calc
    _ ≤ M*2 := mul_le_mul (div_le_self hM hE) hr (by positivity) hM
    _ = _ := mul_comm _ _

end
end SevenEighths.CubicSieve

end OAI

end Source1473

/- Original source: OAI/NumberTheory/DirichletL/CubicDyadicDecay.lean; sha256: 1a6ab6ccc62d7bd902ea5728dcf49d01093595ebf908875f34a0163378ad4293 -/
section Source1474
namespace OAI

namespace SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section

def decayConstant (α : ℝ) : ℝ :=
  (2 : ℝ)^α / ((2 : ℝ)^α - 1) + (1 - (2 : ℝ)^(α - 3))⁻¹

lemma dyadic_rpow (α : ℝ) (j : ℕ) :
    ((2 : ℝ)^j)^α = ((2 : ℝ)^α)^j := by
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm,
    Real.rpow_mul_natCast (by norm_num)]

lemma decay_le_low (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤ ((2 : ℝ)^α)^j := by
  rw [← dyadic_rpow]
  exact div_le_self (by positivity) (one_le_pow₀ (by
    have : 0 ≤ t * (2 : ℝ)^j := by positivity
    linarith))

lemma decay_le_high (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α - 3))^j := by
  have hk : 0 < (2 : ℝ)^j := by positivity
  calc
    _ ≤ ((2 : ℝ)^j)^α / (t * (2 : ℝ)^j)^3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) (by linarith) 3)
    _ = _ := by
      rw [← dyadic_rpow, Real.rpow_sub hk, Real.rpow_neg ht.le, mul_pow]
      simp only [Real.rpow_ofNat]
      ring

lemma decay_summable (t α : ℝ) (ht : 0 < t) (hα : α < 3) :
    Summable (fun j : ℕ => ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) := by
  have hr : (2 : ℝ)^(α - 3) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact ((summable_geometric_of_lt_one (by positivity) hr).mul_left (t^(-3 : ℝ))).of_nonneg_of_le
    (fun j => by positivity) (decay_le_high t α ht)

lemma decayConstant_pos (α : ℝ) (hα : 0 < α) (hα3 : α < 3) :
    0 < decayConstant α := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α - 3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold decayConstant
  positivity

lemma geometric_prefix_le (q : ℝ) (hq : 1 < q) (k : ℕ) :
    (∑ j ∈ Finset.range k, q^j) ≤ q^k / (q - 1) := by
  rw [geom_sum_eq (ne_of_gt hq)]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

lemma decay_tail_le (t α : ℝ) (ht : 0 < t) (hα3 : α < 3) (k : ℕ) :
    (∑' j : ℕ, ((2 : ℝ)^(j+k))^α / (1 + t * (2 : ℝ)^(j+k))^3) ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k * (1 - (2 : ℝ)^(α-3))⁻¹ := by
  have hr0 : 0 ≤ (2 : ℝ)^(α-3) := by positivity
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs := summable_geometric_of_lt_one hr0 hr
  calc
    _ ≤ ∑' j : ℕ, t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^(j+k) := by
      apply (decay_summable t α ht hα3).comp_injective (add_left_injective k) |>.tsum_le_tsum
        (fun j => decay_le_high t α ht (j+k))
      exact (hs.comp_injective (add_left_injective k)).mul_left _
    _ = _ := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr]
      ring

theorem dyadic_decay_bound (t α : ℝ) (ht : 0 < t) (hα : 0 < α) (hα3 : α < 3) :
    (∑' j : ℕ, ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
      decayConstant α * t^(-α) := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < (1 - (2 : ℝ)^(α-3))⁻¹ := inv_pos.mpr (by linarith)
  by_cases ht1 : 1 ≤ t
  · have hp : t^(-3 : ℝ) ≤ t^(-α) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    have hh := decay_tail_le t α ht hα3 0
    simp only [Nat.add_zero, pow_zero, mul_one] at hh
    apply hh.trans
    unfold decayConstant
    nlinarith [mul_nonneg (div_nonneg (by positivity : 0 ≤ (2 : ℝ)^α)
      (by linarith : 0 ≤ (2 : ℝ)^α - 1)) (by positivity : 0 ≤ t^(-α)),
      mul_le_mul_of_nonneg_right hp hden.le]
  · have hit : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr (le_of_not_ge ht1)
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hit (by norm_num : (1 : ℝ) < 2)
    let k := n+1
    have hk0 : 0 < (2 : ℝ)^k := by positivity
    have hk : t⁻¹ ≤ (2 : ℝ)^k := le_of_lt hn'
    have hk' : (2 : ℝ)^k ≤ 2*t⁻¹ := by
      dsimp [k]
      rw [pow_succ]
      nlinarith
    have hlow : (∑ j ∈ Finset.range k,
        ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
        (2 : ℝ)^α / ((2 : ℝ)^α - 1) * t^(-α) := by
      calc
        _ ≤ ∑ j ∈ Finset.range k, ((2 : ℝ)^α)^j :=
          Finset.sum_le_sum (fun j hj => decay_le_low t α ht j)
        _ ≤ ((2 : ℝ)^α)^k / ((2 : ℝ)^α - 1) := geometric_prefix_le _ hq k
        _ ≤ (2*t⁻¹)^α / ((2 : ℝ)^α - 1) := by
          rw [← dyadic_rpow]
          exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hk0.le hk' hα.le)
            (by linarith)
        _ = _ := by
          rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr ht.le),
            ← Real.rpow_neg_eq_inv_rpow]
          ring
    have hhigh : t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k ≤ t^(-α) := by
      rw [← dyadic_rpow]
      calc
        _ ≤ t^(-3 : ℝ) * (t⁻¹)^(α-3) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (inv_pos.mpr ht)
            hk (by linarith)) (by positivity)
        _ = _ := by
          rw [← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_add ht]
          congr 1
          ring
    rw [← (decay_summable t α ht hα3).sum_add_tsum_nat_add k]
    have htail := (decay_tail_le t α ht hα3 k).trans
      (mul_le_mul_of_nonneg_right hhigh hden.le)
    unfold decayConstant
    nlinarith

theorem two_power_majorant (B : ℝ → ℝ) (C P Q t α β : ℝ)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (ht : 0 < t)
    (hα : 0 < α) (hα3 : α < 3) (hβ : 0 < β) (hβ3 : β < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ C * (P*K^α + Q*K^β)) :
    Summable (fun j : ℕ => B ((2 : ℝ)^j) / (1 + t*(2 : ℝ)^j)^3) ∧
    (∑' j : ℕ, B ((2 : ℝ)^j) / (1 + t*(2 : ℝ)^j)^3) ≤
      C * (P*decayConstant α*t^(-α) + Q*decayConstant β*t^(-β)) := by
  let f (γ : ℝ) (j : ℕ) := ((2 : ℝ)^j)^γ / (1+t*(2 : ℝ)^j)^3
  have hsα : Summable (f α) := decay_summable t α ht hα3
  have hsβ : Summable (f β) := decay_summable t β ht hβ3
  have hs : Summable (fun j => C*(P*f α j+Q*f β j)) :=
    ((hsα.mul_left P).add (hsβ.mul_left Q)).mul_left C
  have hle (j : ℕ) : B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3 ≤
      C*(P*f α j+Q*f β j) := by
    have hi := div_le_div_of_nonneg_right (hB ((2 : ℝ)^j)
      (one_le_pow₀ (by norm_num))) (by positivity : 0 ≤ (1+t*(2 : ℝ)^j)^3)
    dsimp [f]
    convert hi using 1
    ring
  have hsum := hs.of_nonneg_of_le
    (fun j => div_nonneg (hB0 _ (one_le_pow₀ (by norm_num))) (by positivity)) hle
  refine ⟨hsum, (hsum.tsum_le_tsum hle hs).trans ?_⟩
  rw [tsum_mul_left, (hsα.mul_left P).tsum_add (hsβ.mul_left Q), tsum_mul_left,
    tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ hC
  have h₁ := mul_le_mul_of_nonneg_left (dyadic_decay_bound t α ht hα hα3) hP
  have h₂ := mul_le_mul_of_nonneg_left (dyadic_decay_bound t β ht hβ hβ3) hQ
  dsimp [f] at *
  nlinarith

theorem sieve_growth_majorant (B : ℝ → ℝ) (A N t δ ξ : ℝ)
    (hA : 0 ≤ A) (hN : 0 < N) (ht : 0 < t)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    Summable (fun j : ℕ => B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ∧
    (∑' j : ℕ, B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ≤
      A*N^δ * (N*decayConstant (1/3+δ)*t^(-(1/3+δ)) +
        decayConstant (ξ+δ)*t^(-(ξ+δ))) := by
  have hh := two_power_majorant B (A*N^δ) N 1 t (1/3+δ) (ξ+δ)
    (by positivity) hN.le (by norm_num) ht hα hα3 hβ hβ3 hB0
  simp only [one_mul] at hh
  apply hh
  intro K hK
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  apply (hB K hK).trans_eq
  rw [Real.mul_rpow hK0.le hN.le, Real.rpow_add hK0, Real.rpow_add hK0]
  ring

lemma poisson_scale_identity (M N α : ℝ) (hM : 0 < M) (hN : 0 < N) :
    M/N * (M/N^2)^(-α) = M^(1-α) * N^(2*α-1) := by
  rw [Real.div_rpow hM.le (sq_nonneg N), Real.rpow_neg hM.le,
    Real.rpow_neg (sq_nonneg N), div_inv_eq_mul,
    ← Real.rpow_natCast_mul hN.le 2 α, Real.rpow_sub hM,
    Real.rpow_sub hN, Real.rpow_one, Real.rpow_one]
  norm_num
  ring

lemma poisson_small_power_identity (M N δ β : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^δ * (M/N) * (M/N^2)^(-(β+δ)) =
      N^(3*δ)*M^(-δ)*M^(1-β)*N^(2*β-1) := by
  rw [mul_assoc, poisson_scale_identity M N (β+δ) hM hN]
  calc
    _ = M^(1-(β+δ)) * (N^δ*N^(2*(β+δ)-1)) := by ring
    _ = M^(-δ+(1-β)) * N^(3*δ+(2*β-1)) := by
      rw [← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring
    _ = _ := by rw [Real.rpow_add hM, Real.rpow_add hN]; ring

theorem sieve_poisson_bound (B : ℝ → ℝ) (A M N δ ξ : ℝ)
    (hA : 0 ≤ A) (hM : 0 < M) (hN : 0 < N)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    (M/N) * (∑' j : ℕ, B ((2 : ℝ)^j) / (1+M*(2 : ℝ)^j/N^2)^3) ≤
      A*N^(3*δ)*M^(-δ) *
        (decayConstant (1/3+δ)*(M*N)^(2/3 : ℝ) +
          decayConstant (ξ+δ)*M^(1-ξ)*N^(2*ξ-1)) := by
  have ht : 0 < M/N^2 := by positivity
  have hh := (sieve_growth_majorant B A N (M/N^2) δ ξ hA hN ht
    hα hα3 hβ hβ3 hB0 hB).2
  have hden : (fun j : ℕ => B ((2 : ℝ)^j)/(1+(M/N^2)*(2 : ℝ)^j)^3) =
      (fun j : ℕ => B ((2 : ℝ)^j)/(1+M*(2 : ℝ)^j/N^2)^3) := by
    funext j
    congr 2
    ring
  rw [hden] at hh
  apply (mul_le_mul_of_nonneg_left hh (div_pos hM hN).le).trans_eq
  have hid₁ := poisson_small_power_identity M N δ (1/3) hM hN
  have hid₂ := poisson_small_power_identity M N δ ξ hM hN
  have hmix : N * M^(1-(1/3 : ℝ)) * N^(2*(1/3 : ℝ)-1) =
      (M*N)^(2/3 : ℝ) := by
    norm_num
    rw [Real.mul_rpow hM.le hN.le]
    have hn' : N * N^(- (1/3 : ℝ)) = N^(2/3 : ℝ) := by
      calc
        _ = N^(1 : ℝ) * N^(-(1/3 : ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hN]; norm_num
    nlinarith [congrArg (fun x => M^(2/3 : ℝ)*x) hn']
  calc
    _ = A*N*decayConstant (1/3+δ)*(N^δ*(M/N)*(M/N^2)^(-(1/3+δ))) +
        A*decayConstant (ξ+δ)*(N^δ*(M/N)*(M/N^2)^(-(ξ+δ))) := by ring
    _ = _ := by
      rw [hid₁, hid₂]
      have he := congrArg (fun x => A*N^(3*δ)*M^(-δ)*decayConstant (1/3+δ)*x) hmix
      nlinarith [he]

lemma descent_factor_le_one (e d u v : ℝ) (he : 1 ≤ e) (hed : e ≤ d)
    (hv : v ≤ 0) (huv : u+v ≤ 0) : e^u*d^v ≤ 1 := by
  have hd : 1 ≤ d := he.trans hed
  by_cases hu : 0 ≤ u
  · calc
      _ ≤ d^u*d^v := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by linarith) hed hu) (by positivity)
      _ = d^(u+v) := (Real.rpow_add (by linarith : 0 < d) u v).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hd huv
  · exact (mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos he (le_of_not_ge hu))
      (Real.rpow_le_one_of_one_le_of_nonpos hd hv) (by positivity) (by norm_num)).trans_eq
      (one_mul 1)

lemma monomial_descendant_le (M N e d u v : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hv : 0 ≤ v) (huv : 0 ≤ u+v) :
    (M/e)^u*(N/d)^v ≤ M^u*N^v := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  have hg := descent_factor_le_one e d (-u) (-v) he hed (by linarith) (by linarith)
  calc
    _ = (M^u*N^v)*(e^(-u)*d^(-v)) := by
      rw [Real.div_rpow hM.le he0.le, Real.div_rpow hN.le hd0.le,
        Real.rpow_neg he0.le, Real.rpow_neg hd0.le]
      ring
    _ ≤ (M^u*N^v)*1 := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := mul_one _

lemma mixed_monomial_identity (M N δ : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^(3*δ)*M^(-δ)*(M*N)^(2/3 : ℝ) =
      M^(2/3-δ)*N^(2/3+3*δ) := by
  rw [Real.mul_rpow hM.le hN.le]
  calc
    _ = (M^(-δ)*M^(2/3 : ℝ))*(N^(3*δ)*N^(2/3 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring

lemma secondary_monomial_identity (M N δ ξ : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^(3*δ)*M^(-δ)*M^(1-ξ)*N^(2*ξ-1) =
      M^(1-ξ-δ)*N^(2*ξ-1+3*δ) := by
  calc
    _ = (M^(-δ)*M^(1-ξ))*(N^(3*δ)*N^(2*ξ-1)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring

lemma mixed_descendant_le (M N e d δ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 ≤ δ) :
    (N/d)^(3*δ)*(M/e)^(-δ)*((M/e)*(N/d))^(2/3 : ℝ) ≤
      N^(3*δ)*M^(-δ)*(M*N)^(2/3 : ℝ) := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  rw [mixed_monomial_identity (M/e) (N/d) δ (div_pos hM he0) (div_pos hN hd0),
    mixed_monomial_identity M N δ hM hN]
  exact monomial_descendant_le M N e d (2/3-δ) (2/3+3*δ) hM hN he hed
    (by linarith) (by linarith)

lemma secondary_descendant_le (M N e d δ ξ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) :
    (N/d)^(3*δ)*(M/e)^(-δ)*(M/e)^(1-ξ)*(N/d)^(2*ξ-1) ≤
      N^(3*δ)*M^(-δ)*M^(1-ξ)*N^(2*ξ-1) := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  rw [secondary_monomial_identity (M/e) (N/d) δ ξ (div_pos hM he0) (div_pos hN hd0),
    secondary_monomial_identity M N δ ξ hM hN]
  exact monomial_descendant_le M N e d (1-ξ-δ) (2*ξ-1+3*δ) hM hN he hed
    (by linarith) (by linarith)

theorem poisson_envelope_descendant_le (M N e d δ ξ P Q : ℝ)
    (hM : 0 < M) (hN : 0 < N) (he : 1 ≤ e) (hed : e ≤ d)
    (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (N/d)^(3*δ)*(M/e)^(-δ) *
        (P*((M/e)*(N/d))^(2/3 : ℝ) + Q*(M/e)^(1-ξ)*(N/d)^(2*ξ-1)) ≤
      N^(3*δ)*M^(-δ) * (P*(M*N)^(2/3 : ℝ)+Q*M^(1-ξ)*N^(2*ξ-1)) := by
  have hm := mul_le_mul_of_nonneg_left (mixed_descendant_le M N e d δ hM hN he hed hδ) hP
  have hs := mul_le_mul_of_nonneg_left
    (secondary_descendant_le M N e d δ ξ hM hN he hed hδ hξ) hQ
  nlinarith [hm, hs]

end
end SevenEighths.CubicDyadicDecay

end OAI

end Source1474

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/CostGrowth.lean; sha256: c886a50d9fe2a6d66f9615df6aeadab8efd774d5afe2489296fa91091a5cb5d2 -/
section Source1475
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open SecondPassArithmetic EisensteinSchwartzPoisson SevenEighths.CubicDyadicDecay
noncomputable section

theorem HasCubicExponent.frequencyCost_bound {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1/2) :
    ∃ A : ℝ, 0 < A ∧ ∀ C ε : ℝ, 0 ≤ C → ∀ hε : 0 < ε,
      ∀ X Y : ℝ, 0 < X → 1 ≤ Y →
        frequencyCost C ε hε X Y ≤
          (X*(2/Y))*‖paperRadialFourier rowMajorant 0‖ +
          (2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A) * Y^ε *
            (Y^(3*δ)*X^(-δ) * (decayConstant (1/3+δ)*(X*Y)^(2/3 : ℝ) +
              decayConstant (ξ+δ)*X^(1-ξ)*Y^(2*ξ-1))) := by
  obtain ⟨A,hA,hb⟩ := h.full_element_bound hξ δ hδ
  refine ⟨A,hA,?_⟩
  intro C ε hC hε X Y hX hY
  have hY0 : 0 < Y := by linarith
  have hs := sieve_poisson_bound (fun K => elementSieveNorm K Y) A X Y δ ξ hA.le hX hY0
    (by linarith) (by linarith) (by linarith) (by linarith)
    (fun K hK => elementSieveNorm_nonneg K Y)
    (fun K hK => by simpa only [mul_comm Y (K^(1/3 : ℝ))] using hb K Y hK hY)
  have hfac : 0 ≤ 2*C*IdealCoprimeSieveOperator.supportConstant ε hε*Y^ε := by
    have hp := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
    positivity
  have hh := mul_le_mul_of_nonneg_left hs hfac
  have he := add_le_add_left hh ((X*(2/Y))*‖paperRadialFourier rowMajorant 0‖)
  convert he using 1 <;> try dsimp only [frequencyCost, frequencyMajorant]
  all_goals ring

theorem frequencyCost_descendant_of_bound (C ε A δ ξ M N d e : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) (hα3 : 1/3+δ < 3) (hβ3 : ξ+δ < 3)
    (hM : 0 < M) (hN : 0 < N) (he : 1 ≤ e) (hed : e ≤ d) (hdN : d ≤ N)
    (hb : frequencyCost C ε hε (M/e) (N/d) ≤
      ((M/e)*(2/(N/d)))*‖paperRadialFourier rowMajorant 0‖ +
      (2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A)*(N/d)^ε*
        ((N/d)^(3*δ)*(M/e)^(-δ) *
          (decayConstant (1/3+δ)*((M/e)*(N/d))^(2/3 : ℝ) +
            decayConstant (ξ+δ)*(M/e)^(1-ξ)*(N/d)^(2*ξ-1)))) :
    frequencyCost C ε hε (M/e) (N/d) ≤
      2*M*‖paperRadialFourier rowMajorant 0‖ +
      (2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A)*N^ε*
        (N^(3*δ)*M^(-δ) *
          (decayConstant (1/3+δ)*(M*N)^(2/3 : ℝ) +
            decayConstant (ξ+δ)*M^(1-ξ)*N^(2*ξ-1))) := by
  have hd : 1 ≤ d := he.trans hed
  have hd0 : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have hp := (decayConstant_pos (1/3+δ) (by linarith) hα3).le
  have hq := (decayConstant_pos (ξ+δ) (by linarith) hβ3).le
  have henv := poisson_envelope_descendant_le M N e d δ ξ
    (decayConstant (1/3+δ)) (decayConstant (ξ+δ)) hM hN he hed hδ hξ hp hq
  have hny : (N/d)^ε ≤ N^ε := Real.rpow_le_rpow (by positivity) (div_le_self hN.le hd) hε.le
  have hfac : 0 ≤ 2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A := by
    have hp := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
    positivity
  apply hb.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (descendant_unit_scale_le M N d e hM.le hN hd he hdN) (norm_nonneg _)
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hny hfac
    · exact henv
    · positivity
    · positivity

lemma poisson_envelope_absorb (M N δ ε ξ H Z P Q : ℝ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hH : 0 ≤ H) (hZ : 0 ≤ Z) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    2*M*Z + H*N^ε*(N^(3*δ)*M^(-δ)*
      (P*(M*N)^(2/3 : ℝ)+Q*M^(1-ξ)*N^(2*ξ-1))) ≤
        (2*Z+H*(P+Q))*N^(3*δ+ε)*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let X := (M*N)^(2/3 : ℝ)
  let Y := M^(1-ξ)*N^(2*ξ-1)
  let S := M+X+Y
  have hX : 0 ≤ X := Real.rpow_nonneg (by positivity) _
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hshape : P*X+Q*Y ≤ (P+Q)*S := by
    dsimp only [S]
    nlinarith [mul_nonneg hP hM0.le, mul_nonneg hQ hM0.le, mul_nonneg hP hY, mul_nonneg hQ hX]
  have hsmall : M^(-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM (by linarith)
  have hloss : 1 ≤ N^(3*δ+ε) := Real.one_le_rpow hN (by positivity)
  have hunit : 2*M*Z ≤ 2*Z*N^(3*δ+ε)*S := by
    have hmS : M ≤ S := by dsimp [S]; linarith
    calc
      _ = 2*Z*M := by ring
      _ ≤ 2*Z*S := mul_le_mul_of_nonneg_left hmS (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2*Z) hS) (sub_nonneg.mpr hloss)]
  have htail : H*N^ε*(N^(3*δ)*M^(-δ)*(P*X+Q*Y)) ≤
      H*(P+Q)*N^(3*δ+ε)*S := by
    have hs : M^(-δ)*(P*X+Q*Y) ≤ (P+Q)*S :=
      (mul_le_of_le_one_left (by positivity) hsmall).trans hshape
    have hpow : N^ε*N^(3*δ) = N^(3*δ+ε) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    calc
      _ = H*(N^ε*N^(3*δ))*(M^(-δ)*(P*X+Q*Y)) := by ring
      _ ≤ H*(N^ε*N^(3*δ))*((P+Q)*S) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [hpow]; ring
  have hh := add_le_add hunit htail
  convert hh using 1 <;> dsimp only [S,X,Y] <;> ring

end
end SevenEighths.CubicSieve

end OAI

end Source1475

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/ColumnShells.lean; sha256: 548e6cde808710858f52098eed599df78e9688313f1ff44acda510a8bb6841b5 -/
section Source1476
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve FiniteSieveRestriction
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicColumnLabel {n : Type*} (cols : n → Ideal O) (N : ℝ) (j : n) :
    Fin (columnDyadicLength N + 1) := divisorDyadicLabel N (cols j)

abbrev CubicColumnShell {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (l : Fin (columnDyadicLength N + 1)) := {j : n // cubicColumnLabel cols N j = l}

lemma cubicColumnShell_bounds {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (hc : ∀ j, Admissible (cols j)) (hn : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (l : Fin (columnDyadicLength N + 1)) (j : CubicColumnShell cols N l) :
    (2 : ℝ)^l.val/2 ≤ (Ideal.absNorm (cols j.val) : ℝ) ∧
      (Ideal.absNorm (cols j.val) : ℝ) ≤ (2 : ℝ)^l.val := by
  have hp : 1 ≤ (Ideal.absNorm (cols j.val) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (primaryGenerator_ne_zero_ideal _ (hc j.val).2))
  have hb := divisorDyadicLabel_bounds N (cols j.val) hp (hn j.val)
  have hj := j.property
  change divisorDyadicLabel N (cols j.val) = l at hj
  rw [hj] at hb
  exact ⟨hb.1.le,hb.2⟩

lemma cubicColumnShell_scale_le {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (hc : ∀ j, Admissible (cols j)) (hn : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (l : Fin (columnDyadicLength N + 1)) (j : CubicColumnShell cols N l) :
    (2 : ℝ)^l.val ≤ 2*N := by
  have hh := (cubicColumnShell_bounds cols N hc hn l j).1
  linarith [hn j.val]

lemma cubicColumnShell_energy {n : Type*} [Fintype n]
    (cols : n → Ideal O) (N : ℝ) (a : n → ℂ) :
    (∑ l : Fin (columnDyadicLength N + 1), ∑ j : CubicColumnShell cols N l, ‖a j.val‖^2) =
      ∑ j, ‖a j‖^2 := Fintype.sum_fiberwise (cubicColumnLabel cols N) (fun j => ‖a j‖^2)

theorem cubic_energy_column_shells {n : Type*} [Fintype n]
    (cols : n → Ideal O) (N : ℝ) (a : n → ℂ) (R : Finset O) :
    (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
      (columnDyadicLength N + 1 : ℝ) *
        ∑ l : Fin (columnDyadicLength N + 1), ∑ z ∈ R,
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z * a j.val‖^2 := by
  have hp (z : O) : ‖∑ j, cubicRow (cols j) z*a j‖^2 ≤
      (columnDyadicLength N + 1 : ℝ)*∑ l : Fin (columnDyadicLength N + 1),
        ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2 := by
    rw [← Fintype.sum_fiberwise (cubicColumnLabel cols N) (fun j => cubicRow (cols j) z*a j)]
    calc
      _ ≤ (∑ l : Fin (columnDyadicLength N + 1),
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by
        simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
          Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
          (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ))
            (fun l : Fin (columnDyadicLength N + 1) =>
              ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖))
  calc
    _ ≤ ∑ z ∈ R, (columnDyadicLength N + 1 : ℝ)*
        ∑ l : Fin (columnDyadicLength N + 1),
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2 :=
      Finset.sum_le_sum (fun z hz => hp z)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end
end SevenEighths.CubicSieve

end OAI

end Source1476

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/AnnularImprovement.lean; sha256: adfd504afcb3c6cdb6f879852deec4144830db166c09951b704098c0fbf45dc0 -/
section Source1477
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open IdealMobiusDivisorSum SecondPassArithmetic EisensteinSchwartzPoisson
open SevenEighths.CubicDyadicDecay
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem HasCubicExponent.annular_improved {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ < 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : Type} [Fintype n] [DecidableEq n]
      (M N : ℝ), 1 ≤ M → 1 ≤ N → ∀ (cols : n → Ideal O), Function.Injective cols →
      (∀ j, Admissible (cols j)) →
      (∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
      ∀ (a : n → ℂ) (R : Finset O),
        (∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M) →
        (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z*a j‖^2) ≤
          K*N^(6*θ)*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1))*∑ j, ‖a j‖^2 := by
  obtain ⟨C,hC,hcf⟩ := cubic_common_factor_frequency_bound
  obtain ⟨A,hA,hfb⟩ := h.frequencyCost_bound hξ hξ2 θ hθ hθsmall
  let Z := ‖paperRadialFourier rowMajorant 0‖
  let P := decayConstant (1/3+θ)
  let Q := decayConstant (ξ+θ)
  let H := 2*C*IdealCoprimeSieveOperator.supportConstant θ hθ*A
  let V := 1+2*Z+H*(P+Q)
  let Dv := DivisorBlockCauchy.divisorConstant θ hθ
  have hZ : 0 ≤ Z := norm_nonneg _
  have hP : 0 ≤ P := (decayConstant_pos _ (by linarith) (by linarith)).le
  have hQ : 0 ≤ Q := (decayConstant_pos _ (by linarith) (by linarith)).le
  have hH : 0 ≤ H := by
    dsimp [H]
    have hs := (IdealCoprimeSieveOperator.supportConstant_pos θ hθ).le
    positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hDv : 0 < Dv := DivisorBlockCauchy.divisorConstant_pos θ hθ
  refine ⟨V*Dv^2, by positivity, ?_⟩
  intro n _ _ M N hM hN cols hinj hc hcols a R hR
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let S := M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let U := V*N^(4*θ)*S
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hcost (D : Ideal O) (hD : D ∈ gcdPool cols) (E : Ideal O) (hE : E ∈ idealDivisors D) :
      frequencyCost C θ hθ (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) ≤ U := by
    have hc0 (j : n) : cols j ≠ 0 := primaryGenerator_ne_zero_ideal _ (hc j).2
    have hD0 := gcdPool_ne_zero cols hc0 D hD
    have hDE := (mem_idealDivisors hD0).mp hE
    have hE0 : E ≠ 0 := ne_zero_of_dvd_ne_zero hD0 hDE
    have he1 : 1 ≤ (Ideal.absNorm E : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
    have hed : (Ideal.absNorm E : ℝ) ≤ (Ideal.absNorm D : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0))
        (map_dvd Ideal.absNorm hDE)
    have hdN := (columnDivisorPool_norm_bounds cols hc0 N (fun j => (hcols j).2) D
      (gcdPool_subset_columnDivisorPool cols hc0 hD)).2
    have hd0 : 0 < (Ideal.absNorm D : ℝ) := by linarith
    have he0 : 0 < (Ideal.absNorm E : ℝ) := by linarith
    have hh := hfb C θ hC hθ (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ))
      (div_pos hM0 he0) ((one_le_div hd0).mpr hdN)
    have hd := frequencyCost_descendant_of_bound C θ A θ ξ M N
      (Ideal.absNorm D) (Ideal.absNorm E) hC hθ hA.le hθ.le (by linarith)
      (by linarith) (by linarith) hM0 hN0 he1 hed hdN hh
    have hb := poisson_envelope_absorb M N θ θ ξ H Z P Q hM hN hθ.le hθ.le hH hZ hP hQ
    have hx : 3*θ+θ = 4*θ := by ring
    rw [hx] at hb
    apply (hd.trans hb).trans
    change (2*Z+H*(P+Q))*N^(4*θ)*S ≤ V*N^(4*θ)*S
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [V]; linarith) (Real.rpow_nonneg hN0.le _)) hS
  have henergy := (hcf θ hθ M N hM0 cols hinj hc hcols a R hR).trans
    (common_factor_uniform_cost C θ U M N hθ hU hN0.le cols hc (fun j => (hcols j).2) a hcost)
  have hp : N^(4*θ)*(N^θ)^2 = N^(6*θ) := by
    rw [← Real.rpow_mul_natCast hN0.le, ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  calc
    _ ≤ U*(Dv*N^θ)^2*∑ j, ‖a j‖^2 := henergy
    _ = (V*Dv^2)*(N^(4*θ)*(N^θ)^2)*S*∑ j, ‖a j‖^2 := by dsimp [U]; ring
    _ = _ := by rw [hp]

end
end SevenEighths.CubicSieve

end OAI

end Source1477

/- Original source: OAI/NumberTheory/DirichletL/CubicSieve/FullImprovement.lean; sha256: 2c2d5e9aea4a02dd94d8b5063859d201baec675e241e481ebd718ba3049d47df -/
section Source1478
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalQuadraticSieve (columnDyadicLength)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma improved_shape_shell (M N Y ξ : ℝ) (hM : 0 < M) (hN : 0 < N) (hY : 0 ≤ Y)
    (hYN : Y ≤ 2*N) (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2) :
    M+(M*Y)^(2/3 : ℝ)+M^(1-ξ)*Y^(2*ξ-1) ≤
      8*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  have hp : (2:ℝ)^(2/3 : ℝ) ≤ 8 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (by norm_num : (2/3 : ℝ)≤3)
    norm_num at hh ⊢
    exact hh
  have hq : (2:ℝ)^(2*ξ-1) ≤ 8 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 2*ξ-1 ≤ 3 by linarith)
    norm_num at hh
    exact hh
  have hcross := Real.rpow_le_rpow (mul_nonneg hM.le hY)
    (mul_le_mul_of_nonneg_left hYN hM.le) (by norm_num : (0:ℝ)≤2/3)
  have hsec := Real.rpow_le_rpow hY hYN (show 0 ≤ 2*ξ-1 by linarith)
  rw [show M*(2*N) = 2*(M*N) by ring, Real.mul_rpow (by norm_num) (mul_pos hM hN).le] at hcross
  rw [Real.mul_rpow (by norm_num) hN.le] at hsec
  have hx := (hcross.trans (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (mul_pos hM hN).le _)))
  have hy := mul_le_mul_of_nonneg_left
    (hsec.trans (mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hN.le _)))
      (Real.rpow_nonneg hM.le (1-ξ))
  nlinarith

lemma improved_loss_shell (N Y θ : ℝ) (hN : 0 ≤ N) (hY : 0 ≤ Y) (hYN : Y ≤ 2*N)
    (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1/2) : Y^(6*θ) ≤ 8*N^(6*θ) := by
  have hh := Real.rpow_le_rpow hY hYN (show 0 ≤ 6*θ by positivity)
  rw [Real.mul_rpow (by norm_num) hN] at hh
  have hp : (2:ℝ)^(6*θ) ≤ 8 := by
    have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 6*θ ≤ 3 by linarith)
    norm_num at he
    exact he
  exact hh.trans (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hN _))

theorem HasCubicExponent.full_improved {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      elementSieveNorm M N ≤ C*N^(7*θ)*
        (M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  obtain ⟨K,hK,hb⟩ := h.annular_improved hξ hξ2 θ hθ hθsmall
  let D : ℝ := 2+1/(θ*Real.log 2)
  have hD : 0 < D := by
    dsimp [D]
    have := Real.log_pos (by norm_num : (1:ℝ)<2)
    positivity
  refine ⟨64*K*D, by positivity, ?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let cols : idealRange N → Ideal O := fun j => j.val
  have hc (j : idealRange N) : Admissible (cols j) := (mem_idealRange.mp j.property).1
  have hn (j : idealRange N) : (Ideal.absNorm (cols j) : ℝ) ≤ N := (mem_idealRange.mp j.property).2
  let R := elementRange M
  have hR (z : O) (hz : z ∈ R) : (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M :=
    ((mem_elementRange M z).mp hz).2
  let S := M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · positivity
  intro a
  have hsector (l : Fin (columnDyadicLength N + 1)) :
      (∑ z ∈ R, ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2) ≤
        (64*K*N^(6*θ)*S)*∑ j : CubicColumnShell cols N l, ‖a j.val‖^2 := by
    by_cases hne : Nonempty (CubicColumnShell cols N l)
    · obtain ⟨j₀⟩ := hne
      have hYN := cubicColumnShell_scale_le cols N hc hn l j₀
      have hY1 : 1 ≤ (2:ℝ)^l.val := one_le_pow₀ (by norm_num)
      have hs := hb M ((2:ℝ)^l.val) hM hY1
        (fun j : CubicColumnShell cols N l => cols j.val)
        (fun j k he => Subtype.ext (Subtype.ext he)) (fun j => hc j.val)
        (fun j => cubicColumnShell_bounds cols N hc hn l j)
        (fun j => a j.val) R hR
      have hl := improved_loss_shell N ((2:ℝ)^l.val) θ hN0.le (by positivity) hYN hθ.le hθsmall.le
      have ht := improved_shape_shell M N ((2:ℝ)^l.val) ξ hM0 hN0 (by positivity) hYN
        (by linarith) hξ2
      apply hs.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hl hK.le) ht (by positivity) (by positivity)
      convert hh using 1; dsimp only [S]; ring
    · let : IsEmpty (CubicColumnShell cols N l) := not_nonempty_iff.mp hne
      simp
  have hsum := cubic_energy_column_shells cols N a R
  have hle := Finset.sum_le_sum (s := Finset.univ) (fun l hl => hsector l)
  rw [← Finset.mul_sum, cubicColumnShell_energy cols N a] at hle
  have he := hsum.trans (mul_le_mul_of_nonneg_left hle (by positivity))
  have hlog := CanonicalQuadraticSieve.columnDyadicLength_small_power θ hθ N hN
  have he' := he.trans (mul_le_mul_of_nonneg_right hlog
    (show 0 ≤ (64*K*N^(6*θ)*S)*∑ j, ‖a j‖^2 by positivity))
  have hp : N^θ*N^(6*θ) = N^(7*θ) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  rw [← Finset.sum_coe_sort] at he'
  change (∑ z : elementRange M, ‖∑ j : idealRange N, cubicRow j.val z.val*a j‖^2) ≤ _
  apply he'.trans_eq
  calc
    _ = (64*K*D)*(N^θ*N^(6*θ))*S*∑ j, ‖a j‖^2 := by dsimp [D]; ring
    _ = _ := by rw [hp]

end
end SevenEighths.CubicSieve

end OAI

end Source1478

/- Original source: OAI/NumberTheory/DirichletL/HeathBrownIteration.lean; sha256: 4a8f3bf7c261b5322473146b07968a3762951df575659e95f03ec0f37a6d784c -/
section Source1479
namespace OAI

namespace SevenEighths.HeathBrownIteration

noncomputable section

def step (x : ℝ) : ℝ := (6 * x - 4) / (3 * x - 1)

theorem step_sub (x : ℝ) (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 = 2 * (x - 4 / 3) / (3 * x - 1) := by
  have hd : 3 * x - 1 ≠ 0 := by linarith
  apply (eq_div_iff hd).mpr
  unfold step
  rw [sub_mul, div_mul_cancel₀ _ hd]
  ring

theorem step_gt {x : ℝ} (hx : (4 / 3 : ℝ) < x) :
    (4 / 3 : ℝ) < step x := by
  have h := step_sub x hx.le
  have hp : 0 < 2 * (x - 4 / 3) / (3 * x - 1) :=
    div_pos (mul_pos (by norm_num) (sub_pos.mpr hx)) (by linarith)
  linarith

theorem step_error_le {x : ℝ} (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 ≤ (2 / 3 : ℝ) * (x - 4 / 3) := by
  rw [step_sub x hx]
  apply (div_le_iff₀ (by linarith : 0 < 3 * x - 1)).mpr
  nlinarith [sq_nonneg (x - 4 / 3)]

theorem step_lt {x : ℝ} (hx : (4 / 3 : ℝ) < x) : step x < x := by
  have h := step_error_le hx.le
  linarith

def exponent : ℕ → ℝ
  | 0 => 2
  | n + 1 => step (exponent n)

theorem exponent_bounds (n : ℕ) :
    (4 / 3 : ℝ) < exponent n ∧ exponent n ≤ 2 := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    exact ⟨step_gt ih.1, (step_lt ih.1).le.trans ih.2⟩

theorem exponent_error_le (n : ℕ) :
    exponent n - 4 / 3 ≤ (2 / 3 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    calc
      exponent (n + 1) - 4 / 3 ≤ (2 / 3 : ℝ) * (exponent n - 4 / 3) :=
        step_error_le (exponent_bounds n).1.le
      _ ≤ (2 / 3 : ℝ) * (2 / 3 : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 / 3 : ℝ) ^ (n + 1 + 1) := by rw [pow_succ]; ring

theorem exists_exponent_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, exponent n < 4 / 3 + ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 / 3 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have hp : (2 / 3 : ℝ) ^ (n + 1) ≤ (2 / 3 : ℝ) ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) (by norm_num)
  have he := exponent_error_le n
  linarith

theorem finite_improvement {P : ℝ → Prop} (hstart : P 2)
    (himprove : ∀ x : ℝ, (4 / 3 : ℝ) < x → x ≤ 2 → P x → P (step x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, (4 / 3 : ℝ) < x ∧ x ≤ 2 ∧ x < 4 / 3 + ε ∧ P x := by
  have hp (n : ℕ) : P (exponent n) := by
    induction n with
    | zero => exact hstart
    | succ n ih => exact himprove _ (exponent_bounds n).1 (exponent_bounds n).2 ih
  obtain ⟨n, hn⟩ := exists_exponent_lt hε
  exact ⟨exponent n, (exponent_bounds n).1, (exponent_bounds n).2, hn, hp n⟩

end

end SevenEighths.HeathBrownIteration

end OAI

end Source1479
