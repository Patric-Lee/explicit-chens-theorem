import OpenAIGrouped.Unit057
import OpenAIGrouped.Unit037
import OpenAIGrouped.Unit007
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OpenAIGrouped.Unit018
import Mathlib.MeasureTheory.Integral.Pi
import OpenAIGrouped.Unit012

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialQuotientGeometry.lean; sha256: f489172179aa8f2e876fc8a0b56da6db8e18ccbeb645384ce4094ca62e53e454 -/
section Source2320
namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalQuadraticSieve
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialQuotientGeometry

local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)

def sourceWeight {J : ℕ} (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (Z B θ : ℝ) (x : Source (ι:=ι) J) : ℂ :=
  A x * ψC ((Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Z^B) *
    ψd ((Ideal.absNorm (sourceIdeal p x.divisor) : ℝ)/Z^θ)

def retained {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ) : Finset (Source (ι:=ι) J) :=
  S.filter (fun x => sourceWeight p A ψC ψd Z B θ x ≠ 0)

def quotientSet {J : ℕ} (S : Finset (Source (ι:=ι) J)) : Finset (Ideal Eis) :=
  S.image (fun x => sourceIdeal p (x.common\x.divisor))

omit [DecidableEq ι] in
theorem retained_sum {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ)
    (F : Source (ι:=ι) J → ℂ) :
    (∑ x ∈ S, sourceWeight p A ψC ψd Z B θ x * F x) =
      ∑ x ∈ retained p S A ψC ψd Z B θ, sourceWeight p A ψC ψd Z B θ x * F x := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x hx hn
  have hz : sourceWeight p A ψC ψd Z B θ x = 0 := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨hx,h⟩)
  simp [hz]

omit [DecidableEq ι] in

theorem retained_phase_independent {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ)
    (phase : Source (ι:=ι) J → ℂ) (hp : ∀ x ∈ S, phase x ≠ 0) :
    S.filter (fun x => sourceWeight p A ψC ψd Z B θ x * phase x ≠ 0) =
      retained p S A ψC ψd Z B θ := by
  ext x
  simp only [Finset.mem_filter, retained, mul_ne_zero_iff]
  constructor
  · rintro ⟨hx,hw,_⟩
    exact ⟨hx,hw⟩
  · rintro ⟨hx,hw⟩
    exact ⟨hx,hw,hp x hx⟩

variable (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotientSet_nonzero {J : ℕ} (S : Finset (Source (ι:=ι) J)) :
    ∀ t ∈ quotientSet p S, t ≠ 0 := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  exact sourceIdeal_ne_zero p hp _

include hp in

theorem quotientSet_eq_initial {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (u : Eisˣ) (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) :
    initialQuotientSet (S.image (fun x => toTuple p (sectorSource u x))) = quotientSet p S := by
  rw [initialQuotientSet, Finset.image_image]
  apply Finset.image_congr
  intro x hx
  change idealQuotient (sourceIdeal p x.divisor) (sourceIdeal p x.common) = _
  exact source_quotient p hp x.common x.divisor (hdiv x hx)

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotient_norm_eq {J : ℕ} (x : Source (ι:=ι) J) (hdiv : x.divisor ⊆ x.common) :
    (Ideal.absNorm (sourceIdeal p (x.common\x.divisor)) : ℝ) =
      (Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Ideal.absNorm (sourceIdeal p x.divisor) := by
  have he : sourceIdeal p x.divisor * sourceIdeal p (x.common\x.divisor) = sourceIdeal p x.common := by
    rw [←sourceIdeal_union p x.divisor (x.common\x.divisor) Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hdiv]
  have hn := congrArg (fun I : Ideal Eis => (Ideal.absNorm I : ℝ)) he
  simp only [map_mul,Nat.cast_mul] at hn
  have hd : (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _)
  apply (eq_div_iff hd).mpr
  simpa only [mul_comm] using hn

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in

theorem retained_norm_windows {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ : ℝ) (hZ : 0 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    {x : Source (ι:=ι) J} (hx : x ∈ retained p S A ψC ψd Z B θ) :
    (Ideal.absNorm (sourceIdeal p x.common) : ℝ) ≤ bC*Z^B ∧
      ad*Z^θ ≤ (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) := by
  have hn := (Finset.mem_filter.mp hx).2
  have hnC : ψC ((Ideal.absNorm (sourceIdeal p x.common) : ℝ)/Z^B) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
  have hnd : ψd ((Ideal.absNorm (sourceIdeal p x.divisor) : ℝ)/Z^θ) ≠ 0 :=
    (mul_ne_zero_iff.mp hn).2
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hC hnC).2,
    (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hd hnd).1⟩

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_quotient_bound {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 0 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) :
    ∀ t ∈ quotientSet p (retained p S A ψC ψd Z B θ),
      (Ideal.absNorm t : ℝ) ≤ Z^(B-θ+2*η) := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  have hw := retained_norm_windows p S A ψC ψd aC bC ad bd Z B θ hZ hC hd hx
  rw [quotient_norm_eq p hp x (hdiv x (Finset.mem_filter.mp hx).1)]
  have hc : (Ideal.absNorm (sourceIdeal p x.common) : ℝ) ≤ Z^(B+η) := by
    apply (hw.1.trans (mul_le_mul_of_nonneg_right hCup (Real.rpow_pos_of_pos hZ _).le)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  have he : Z^(θ-η) ≤ (Ideal.absNorm (sourceIdeal p x.divisor) : ℝ) := by
    apply le_trans _ hw.2
    calc
      _ = Z^(-η)*Z^θ := by rw [←Real.rpow_add hZ]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdlo (Real.rpow_pos_of_pos hZ _).le
  calc
    _ ≤ Z^(B+η)/Z^(θ-η) := div_le_div₀ (by positivity) hc (Real.rpow_pos_of_pos hZ _) he
    _ = _ := by rw [←Real.rpow_sub hZ]; congr 1; ring

theorem endpoint_threshold (bC ad : ℝ) (had : 0 < ad) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧ bC ≤ Z^η ∧ Z^(-η) ≤ ad := by
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop bC),
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop ad⁻¹)] with Z hZ hC hd
  refine ⟨hZ,hC,?_⟩
  rw [Real.rpow_neg (zero_lt_one.trans hZ).le]
  exact (inv_le_comm₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) had).mpr hd

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotientSet_empty_iff {J : ℕ} (S : Finset (Source (ι:=ι) J)) :
    quotientSet p S = ∅ ↔ S = ∅ := Finset.image_eq_empty

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_empty_sum {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ) (Z B θ : ℝ)
    (h : quotientSet p (retained p S A ψC ψd Z B θ) = ∅)
    (F : Source (ι:=ι) J → ℂ) :
    (∑ x ∈ S, sourceWeight p A ψC ψd Z B θ x * F x) = 0 := by
  rw [retained_sum p S A ψC ψd Z B θ F, (quotientSet_empty_iff p _).mp h]
  simp

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem nonempty_radius {J : ℕ} (S : Finset (Source (ι:=ι) J)) (Z P η : ℝ)
    (hZ : 1 < Z) (hne : (quotientSet p S).Nonempty)
    (hnorm : ∀ t ∈ quotientSet p S, (Ideal.absNorm t : ℝ) ≤ Z^(P+2*η)) :
    1 ≤ Z^(P+2*η) ∧ 0 ≤ P+2*η := by
  obtain ⟨t,ht⟩ := hne
  have ht0 := quotientSet_nonzero p hp S t ht
  have hn : (1:ℝ) ≤ Ideal.absNorm t := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ht0)
  have hh := hn.trans (hnorm t ht)
  refine ⟨hh,?_⟩
  exact (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero] using hh)

def normalizedMass (J : ℕ) (T : Finset (Ideal Eis)) (H : ℝ) : ℝ :=
  H⁻¹ * ∑ t ∈ T, ((idealDivisors t).card : ℝ)^J

theorem normalized_mass_bound (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (Ideal Eis)) (H : ℝ), 0 < H →
      (∀ t ∈ T, t ≠ 0) → (∀ t ∈ T, (Ideal.absNorm t : ℝ) ≤ H) →
      normalizedMass J T H ≤ C*H^ε := by
  obtain ⟨C,hC,hb⟩ := ideal_divisor_power_small J ε hε
  refine ⟨128*C,by positivity,?_⟩
  intro T H hH hz hn
  rcases T.eq_empty_or_nonempty with he|⟨t,ht⟩
  · subst T
    simp only [normalizedMass,Finset.sum_empty,mul_zero]
    positivity
  have hH1 : 1 ≤ H := by
    have ht1 : (1:ℝ) ≤ Ideal.absNorm t := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hz t ht))
    exact ht1.trans (hn t ht)
  have hw : ∀ t ∈ T, ((idealDivisors t).card : ℝ)^J ≤ C*H^ε := by
    intro t ht
    exact (hb t (hz t ht)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hn t ht) hε.le) hC.le)
  have hs : (∑ t ∈ T, ((idealDivisors t).card : ℝ)^J) ≤ (128*H)*(C*H^ε) := by
    calc
      _ ≤ ∑ _t ∈ T, C*H^ε := Finset.sum_le_sum hw
      _ = (T.card:ℝ)*(C*H^ε) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (DescentFiberCost.finite_ideal_count_real T H hH1 hz hn) (by positivity)
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hH.le)).trans_eq
  field_simp

theorem retained_normalized_mass (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → Eis)
      (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (S : Finset (Source (ι:=ι) J)) (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
      (aC bC ad bd Z B θ η : ℝ), 0 < Z →
      Function.support ψC ⊆ Set.Icc aC bC → Function.support ψd ⊆ Set.Icc ad bd →
      bC ≤ Z^η → Z^(-η) ≤ ad → (∀ x ∈ S, x.divisor ⊆ x.common) →
      Z^(-(B-θ+2*η)) *
        (∑ t ∈ quotientSet p (retained p S A ψC ψd Z B θ), ((idealDivisors t).card : ℝ)^J) ≤
        C*Z^((B-θ+2*η)*ε) := by
  obtain ⟨C,hC,hb⟩ := normalized_mass_bound J ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ S A ψC ψd aC bC ad bd Z B θ η hZ hCw hdw hCup hdlo hdiv
  have h := hb (quotientSet p (retained p S A ψC ψd Z B θ)) (Z^(B-θ+2*η))
    (Real.rpow_pos_of_pos hZ _) (quotientSet_nonzero p hp _)
    (retained_quotient_bound p hp S A ψC ψd aC bC ad bd Z B θ η hZ hCw hdw hCup hdlo hdiv)
  simpa only [normalizedMass,←Real.rpow_neg hZ.le,←Real.rpow_mul hZ.le] using h

theorem retained_normalized_mass_pi (J : ℕ) (U π : ℝ) (hU : 0 ≤ U) (hπ : 0 < π) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → Eis)
      (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (S : Finset (Source (ι:=ι) J)) (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
      (aC bC ad bd Z B θ η : ℝ), 1 ≤ Z →
      Function.support ψC ⊆ Set.Icc aC bC → Function.support ψd ⊆ Set.Icc ad bd →
      bC ≤ Z^η → Z^(-η) ≤ ad → (∀ x ∈ S, x.divisor ⊆ x.common) → B-θ+2*η ≤ U →
      Z^(-(B-θ+2*η)) *
        (∑ t ∈ quotientSet p (retained p S A ψC ψd Z B θ), ((idealDivisors t).card : ℝ)^J) ≤ C*Z^π := by
  have hε : 0 < π/(U+1) := div_pos hπ (by linarith)
  obtain ⟨C,hC,hb⟩ := retained_normalized_mass J (π/(U+1)) hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ S A ψC ψd aC bC ad bd Z B θ η hZ hCw hdw hCup hdlo hdiv hcap
  apply (hb p hp S A ψC ψd aC bC ad bd Z B θ η (zero_lt_one.trans_le hZ)
    hCw hdw hCup hdlo hdiv).trans
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ ?_) hC.le
  apply (mul_le_mul_of_nonneg_right hcap hε.le).trans
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by linarith : 0 < U+1)).mpr
  nlinarith

theorem radical_norm_le (I : Ideal Eis) (hI : I ≠ 0) :
    (Ideal.absNorm I.radical : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (Ideal.absNorm_dvd_absNorm_of_le Ideal.le_radical)

theorem radical_product_bound (t j : Ideal Eis) (ht : t ≠ 0) (hj : j ≠ 0)
    (Z P G η : ℝ) (hZ : 0 < Z)
    (hnt : (Ideal.absNorm t : ℝ) ≤ Z^(P+2*η))
    (hnj : (Ideal.absNorm j : ℝ) ≤ Z^(G+η)) :
    (Ideal.absNorm (t*j).radical : ℝ) ≤ Z^(P+G+3*η) := by
  apply (radical_norm_le (t*j) (mul_ne_zero ht hj)).trans
  simp only [map_mul,Nat.cast_mul]
  calc
    _ ≤ Z^(P+2*η)*Z^(G+η) := mul_le_mul hnt hnj (by positivity) (by positivity)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring

def assignedCenter {σ : Type*} (slots : Finset σ) (z : σ → ℝ) : ℝ := ∑ i ∈ slots, z i

theorem assigned_register {σ : Type*} [DecidableEq σ]
    (all assigned : Finset σ) (ha : assigned ⊆ all) (z : σ → ℝ)
    (hz : ∀ i ∈ all, 0 ≤ z i) :
    0 ≤ assignedCenter assigned z ∧ 0 ≤ assignedCenter (all\assigned) z ∧
      assignedCenter all z - assignedCenter assigned z = assignedCenter (all\assigned) z := by
  refine ⟨Finset.sum_nonneg (fun i hi => hz i (ha hi)),
    Finset.sum_nonneg (fun i hi => hz i (Finset.mem_sdiff.mp hi).1),?_⟩
  unfold assignedCenter
  have h := Finset.sum_sdiff ha (f := z)
  linarith

def assignedElement {σ : Type*} (slots : Finset σ) (q : σ → Eis) : Eis := ∏ i ∈ slots, q i

theorem assigned_norm_bound {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ) (Z : ℝ) (hZ : 0 < Z)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0) :
    (Ideal.absNorm (Ideal.span {assignedElement slots q}) : ℝ) ≤
      (∏ i ∈ slots, b i)*Z^(assignedCenter slots z) := by
  have hb : ∀ i ∈ slots, (Ideal.absNorm (Ideal.span {q i}) : ℝ) ≤ b i*Z^(z i) := by
    intro i hi
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp (hW i hi (hret i hi)).2
  have hp := Finset.prod_le_prod₀ (fun i _ => (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {q i})))) hb
  simpa only [assignedElement,FiniteGaussPhase.span_finset_prod,map_prod,Nat.cast_prod,
    Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hZ,assignedCenter] using hp

theorem assigned_norm_power {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ) (Z η : ℝ) (hZ : 0 < Z)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ slots, b i) ≤ Z^η) :
    (Ideal.absNorm (Ideal.span {assignedElement slots q}) : ℝ) ≤
      Z^(assignedCenter slots z+η) := by
  apply (assigned_norm_bound slots q z a b W Z hZ hW hret).trans
  calc
    _ ≤ Z^η*Z^(assignedCenter slots z) := mul_le_mul_of_nonneg_right hthreshold (by positivity)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring

include hp in

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_assigned_puncture_bound {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 0 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hq : ∀ i ∈ slots, q i ≠ 0)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ slots, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (retained p S A ψC ψd Z B θ)) :
    (Ideal.absNorm (t*Ideal.span {assignedElement slots q}).radical : ℝ) ≤
      Z^((B-θ)+assignedCenter slots z+3*η) := by
  apply radical_product_bound t (Ideal.span {assignedElement slots q})
    (quotientSet_nonzero p hp _ t ht)
    (Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr hq))
    Z (B-θ) (assignedCenter slots z) η hZ
  · exact retained_quotient_bound p hp S A ψC ψd aC bC ad bd Z B θ η
      hZ hC hd hCup hdlo hdiv t ht
  · exact assigned_norm_power slots q z a b W Z η hZ hW hret hthreshold

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem span_source_puncture {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (hpr : ∀ i, λ₀^2 ∣ p i-1) (j : Eis)
    {t : Ideal Eis} (ht : t ∈ quotientSet p S) :
    Ideal.span {j*primaryGenerator t} = t*Ideal.span {j} := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  rw [sourceIdeal_gen p hp hpr]
  simp only [sourceIdeal,Ideal.span_singleton_mul_span_singleton,mul_comm]

def punctureLength (Z : ℝ) (t : Ideal Eis) (j : Eis) : ℝ :=
  Real.log (Ideal.absNorm (Ideal.span {j*primaryGenerator t}).radical : ℝ)/Real.log Z

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_puncture_length_bound {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, λ₀^2 ∣ p i-1)
    {σ : Type*} (slots : Finset σ) (q : σ → Eis)
    (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hq : ∀ i ∈ slots, q i ≠ 0)
    (hW : ∀ i ∈ slots, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ slots, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ slots, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (retained p S A ψC ψd Z B θ)) :
    punctureLength Z t (assignedElement slots q) ≤ (B-θ)+assignedCenter slots z+3*η := by
  have hz := zero_lt_one.trans hZ
  have hbound := retained_assigned_puncture_bound p hp S A ψC ψd aC bC ad bd Z B θ η
    hz hC hd hCup hdlo hdiv slots q z a b W hq hW hret hthreshold ht
  unfold punctureLength
  rw [span_source_puncture p hp _ hpr _ ht]
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  have htn : t*Ideal.span {assignedElement slots q} ≠ 0 := mul_ne_zero
    (quotientSet_nonzero p hp _ t ht)
    (Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr hq))
  have hrn : (t*Ideal.span {assignedElement slots q}).radical ≠ 0 := by
    intro he
    apply htn
    apply le_bot_iff.mp
    simpa only [he,Ideal.zero_eq_bot] using (Ideal.le_radical :
      t*Ideal.span {assignedElement slots q} ≤ (t*Ideal.span {assignedElement slots q}).radical)
  have hpos : (0:ℝ) < Ideal.absNorm (t*Ideal.span {assignedElement slots q}).radical := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hrn)
  have hlog := Real.log_le_log hpos hbound
  simpa only [Real.log_rpow hz] using hlog

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_initial_margins {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, λ₀^2 ∣ p i-1)
    {σ : Type*} [DecidableEq σ] (all assigned : Finset σ) (ha : assigned ⊆ all)
    (q : σ → Eis) (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hz : ∀ i ∈ all, 0 ≤ z i) (hq : ∀ i ∈ assigned, q i ≠ 0)
    (hW : ∀ i ∈ assigned, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ assigned, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ assigned, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (retained p S A ψC ψd Z B θ))
    (m r δ τ c₁ c₂ : ℝ)
    (h₁ : r+2*assignedCenter all z ≤ m-c₁)
    (h₂ : 2*r+8*assignedCenter all z ≤ 3*m-c₂) :
    c₁+δ-9*η-τ ≤
      initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ -
      initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ -
      punctureLength Z t (assignedElement assigned q) - assignedCenter (all\assigned) z ∧
    c₂+4*δ-22*η-3*τ ≤
      4*initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ -
      3*initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ -
      6*assignedCenter (all\assigned) z := by
  have hr := assigned_register all assigned ha z hz
  have hP := (nonempty_radius p hp (retained p S A ψC ψd Z B θ) Z (B-θ) η hZ ⟨t,ht⟩
    (retained_quotient_bound p hp S A ψC ψd aC bC ad bd Z B θ η
      (zero_lt_one.trans hZ) hC hd hCup hdlo hdiv)).2
  have hQ := retained_puncture_length_bound p hp S A ψC ψd aC bC ad bd Z B θ η
    hZ hC hd hCup hdlo hdiv hpr assigned q z a b W hq hW hret hthreshold ht
  simpa only [hr.2.2] using initial_margins_sharp (delta:=δ) (tau:=τ)
    h₁ h₂ hr.1 (by linarith : -2*η ≤ B-θ) hQ

theorem all_endpoint_threshold {σ : Type*} (slots : Finset σ) (b : σ → ℝ)
    (bC ad η : ℝ) (had : 0 < ad) (hη : 0 < η) :
    ∀ᶠ Z : ℝ in Filter.atTop,
      1 < Z ∧ bC ≤ Z^η ∧ Z^(-η) ≤ ad ∧ (∏ i ∈ slots, b i) ≤ Z^η := by
  filter_upwards [endpoint_threshold bC ad had η hη,
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop (∏ i ∈ slots,b i))]
      with Z h hprod
  exact ⟨h.1,h.2.1,h.2.2,hprod⟩

include hp in

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_nonempty_radius {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hne : (quotientSet p (retained p S A ψC ψd Z B θ)).Nonempty) :
    1 ≤ Z^((B-θ)+2*η) ∧ 0 ≤ (B-θ)+2*η :=
  nonempty_radius p hp (retained p S A ψC ψd Z B θ) Z (B-θ) η hZ hne
    (retained_quotient_bound p hp S A ψC ψd aC bC ad bd Z B θ η
      (zero_lt_one.trans hZ) hC hd hCup hdlo hdiv)

omit [∀ i, (Ideal.span {p i}).IsMaximal] in

theorem assigned_cutoffs_of_term {J : ℕ} (lists : Fin J → Finset ι)
    (a : Fin J → ι → ℂ) (W : Fin J → ℝ → ℂ) (z : Fin J → ℝ)
    (Z : ℝ) (outer : Finset ι) (assigned : Fin J → ι)
    (hterm : assignedTerm lists
      (fun i x => a i x * W i ((Ideal.absNorm (Ideal.span {p x}) : ℝ)/Z^(z i)))
      outer assigned ≠ 0) :
    ∀ i, assigned i ∈ lists i ∧ assigned i ∈ outer ∧
      W i ((Ideal.absNorm (Ideal.span {p (assigned i)}) : ℝ)/Z^(z i)) ≠ 0 := by
  intro i
  have hi := assignedTerm_source lists _ outer assigned hterm i
  have hn := Finset.prod_ne_zero_iff.mp hterm i (Finset.mem_univ i)
  simp only [hi] at hn
  exact ⟨hi.1,hi.2,(mul_ne_zero_iff.mp hn).2⟩

omit [∀ i, (Ideal.span {p i}).IsMaximal] in

theorem retained_assigned_term {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (lists : Fin J → Finset ι) (a : Fin J → ι → ℂ)
    (ψC ψd : ℝ → ℂ) (Z B θ : ℝ) {x : Source (ι:=ι) J}
    (hx : x ∈ retained p S
      (fun y => A y * assignedTerm lists a (y.common∪y.overlap) y.assigned) ψC ψd Z B θ) :
    assignedTerm lists a (x.common∪x.overlap) x.assigned ≠ 0 := by
  have hn := (Finset.mem_filter.mp hx).2
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1).2

end SevenEighths.InverseInitialQuotientGeometry

end

end OAI

end Source2320

/- Original source: OAI/NumberTheory/DirichletL/Descent/DescentProfiles.lean; sha256: af9dc28056c60ef7c8ead58d9717c8f1416ceb5a497771e38a26db0e64f44343 -/
section Source2321
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

lemma schwartz_logPhase_inversion (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    g x = ∫ t : ℝ, logPhase t x * (𝓕 g) t := by
  convert schwartz_log_inversion g x using 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  simp only [logPhase, Real.inner_apply]
  congr 1
  push_cast
  ring

theorem descent_profile_identity {ι : Type*} [Fintype ι]
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak : ι → ℝ)
    (R : ℝ) (b : 𝓢(ℝ, ℂ))
    (he : ∀ y : ι → ℝ,
      (∏ i, V i (y i)) * paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t : ℝ, (∏ i, V i (y i) * logPhase t (ak i * y i)) * b t) :
    ∀ y : ι → ℝ,
      (∏ i, V i (y i)) * g₁ (∑ i, a₁ i * y i) * g₂ (∑ i, a₂ i * y i) *
        paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 g₁) (𝓕 g₂) b (t₁, t₂, t₃) *
          (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
            logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i)) := by
  intro y
  let P : ℂ := ∏ i, V i (y i)
  let x₁ : ℝ := ∑ i, a₁ i * y i
  let x₂ : ℝ := ∑ i, a₂ i * y i
  let xk : ℝ := ∑ i, ak i * y i
  have hphase (t : ℝ) (a : ι → ℝ) :
      (∏ i, logPhase t (a i * y i)) = logPhase t (∑ i, a i * y i) :=
    (logPhase_sum Finset.univ t (fun i => a i * y i)).symm
  have hk' : P * paperRadialFourier W (R * Real.exp xk) =
      ∫ t : ℝ, P * logPhase t xk * b t := by
    simpa only [Finset.prod_mul_distrib, hphase, P, xk] using he y
  have hprod (t₁ t₂ t₃ : ℝ) :
      (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
        logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i)) =
      P * logPhase t₁ x₁ * logPhase t₂ x₂ * logPhase t₃ xk := by
    simp only [Finset.prod_mul_distrib, hphase, P, x₁, x₂, xk]
  simp only [hprod, tripleCoefficient]
  have hinner (t₁ t₂ : ℝ) :
      (∫ t₃ : ℝ, (𝓕 g₁) t₁ * ((𝓕 g₂) t₂ * b t₃) *
        (P * logPhase t₁ x₁ * logPhase t₂ x₂ * logPhase t₃ xk)) =
      ((𝓕 g₁) t₁ * (𝓕 g₂) t₂ * logPhase t₁ x₁ * logPhase t₂ x₂) *
        (P * paperRadialFourier W (R * Real.exp xk)) := by
    rw [hk', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t₃
    ring
  simp_rw [hinner]
  have hmid (t₁ : ℝ) :
      (∫ t₂ : ℝ, ((𝓕 g₁) t₁ * (𝓕 g₂) t₂ * logPhase t₁ x₁ * logPhase t₂ x₂) *
        (P * paperRadialFourier W (R * Real.exp xk))) =
      (logPhase t₁ x₁ * (𝓕 g₁) t₁) * g₂ x₂ *
        (P * paperRadialFourier W (R * Real.exp xk)) := by
    rw [schwartz_logPhase_inversion g₂ x₂, ← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with t₂
    ring
  simp_rw [hmid]
  rw [integral_mul_const, integral_mul_const, ← schwartz_logPhase_inversion]
  dsimp only [P, x₁, x₂, xk]
  ring

theorem descent_profile_separation {ι : Type*} [Fintype ι]
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * g₁ (∑ i, a₁ i * y i) * g₂ (∑ i, a₂ i * y i) *
          paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient (𝓕 g₁) (𝓕 g₂) b (t₁, t₂, t₃) *
            (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
              logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  obtain ⟨C, hC, hk⟩ := paperRadialFourier_log_separation_envelope W V ak M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, he, hi, hb, hp⟩ := hk R hR
  refine ⟨b, ?_, hi, hb, hp⟩
  exact descent_profile_identity g₁ g₂ W V a₁ a₂ ak R b he

theorem tripleCoefficient_weighted_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : Frequency =>
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖) := by
  have hi (b : 𝓢(ℝ, ℂ)) : Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖b t‖) := by
    have he : (𝓕 (𝓕⁻ b) : 𝓢(ℝ, ℂ)) = b := by simp
    simpa only [he] using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J
  convert (hi b₁).mul_prod ((hi b₂).mul_prod (hi b₃)) using 1
  funext t
  simp only [tripleCoefficient, norm_mul]
  ring

theorem tripleCoefficient_weighted_integral (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ t : Frequency,
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖) =
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₁ t‖) *
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₂ t‖) *
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₃ t‖) := by
  have he (t : Frequency) :
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖ =
      ((1 + ‖t.1‖)^J * ‖b₁ t.1‖) *
        (((1 + ‖t.2.1‖)^J * ‖b₂ t.2.1‖) * ((1 + ‖t.2.2‖)^J * ‖b₃ t.2.2‖)) := by
    simp only [tripleCoefficient, norm_mul]
    ring
  simp_rw [he]
  simp only [Measure.volume_eq_prod]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => (1 + ‖t‖)^J * ‖b₁ t‖)
    (fun t : ℝ × ℝ => ((1 + ‖t.1‖)^J * ‖b₂ t.1‖) * ((1 + ‖t.2‖)^J * ‖b₃ t.2‖))]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => (1 + ‖t‖)^J * ‖b₂ t‖) (fun t : ℝ => (1 + ‖t‖)^J * ‖b₃ t‖)]
  ring

theorem source_descent_profile_separation {ι : Type*} [Fintype ι]
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, a₁ i * y i)) *
          W₂ (Real.exp (∑ i, a₂ i * y i)) * paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient b₁ b₂ b₃ (t₁, t₂, t₃) *
            (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
              logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ≤ C := by
  let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
  let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
  obtain ⟨C, hC, hsep⟩ := descent_profile_separation g₁ g₂ Φ V a₁ a₂ ak M hM hV A J
  let I₁ := ∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 g₁) t‖
  let I₂ := ∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 g₂) t‖
  have hI₁ : 0 ≤ I₁ := integral_nonneg (fun t => by positivity)
  have hI₂ : 0 ≤ I₂ := integral_nonneg (fun t => by positivity)
  refine ⟨𝓕 g₁, 𝓕 g₂, I₁ * I₂ * C, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, heq, hi, hb, hp⟩ := hsep R hR
  refine ⟨b₃, ?_, tripleCoefficient_weighted_integrable _ _ _ J, ?_⟩
  · simpa only [g₁, g₂, CubicReflectionKernel.logSchwartz_apply] using heq
  · rw [tripleCoefficient_weighted_integral]
    have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg hI₁ hI₂)
    convert hh using 1 ; dsimp only [I₁, I₂] ; ring

end
end SevenEighths.InverseMoment

end OAI

end Source2321

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActualProfiles.lean; sha256: e18456e2afe7c61db5c483b64351251c7b7c2c6911dd70bae523115e26506fc4 -/
section Source2322
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

def inverseNormWindow (V : ℝ → ℂ) (y : ℝ) : ℂ := V y / (Real.exp y : ℂ)
def inverseRootWindow (V : ℝ → ℂ) (y : ℝ) : ℂ := V y / (Real.sqrt (Real.exp y) : ℂ)

def firstRootWindows (V : Fin 9 → ℝ → ℂ) : Fin 9 → ℝ → ℂ :=
  ![V 0, V 1, V 2, inverseNormWindow (V 3), inverseRootWindow (V 4),
    inverseNormWindow (V 5), V 6, inverseRootWindow (V 7), inverseRootWindow (V 8)]

def firstLeftSlope : Fin 9 → ℝ := ![1, 0, 1, 0, 0, 1, 0, 1, 0]
def firstRightSlope : Fin 9 → ℝ := ![0, 1, 1, 0, 0, 1, 0, 0, 1]
def firstKernelSlope : Fin 9 → ℝ := ![0, 0, 0, -1, -1, -2, 1, -1, -1]

def secondRootWindows (V : Fin 6 → ℝ → ℂ) : Fin 6 → ℝ → ℂ :=
  ![V 0, inverseNormWindow (V 1), inverseNormWindow (V 2), V 3,
    inverseRootWindow (V 4), inverseRootWindow (V 5)]

def secondLeftSlope : Fin 6 → ℝ := ![1, 0, 1, 0, 1, 0]
def secondRightSlope : Fin 6 → ℝ := ![1, 0, 1, 0, 0, 1]
def secondKernelSlope : Fin 6 → ℝ := ![0, -1, -2, 1, -1, -1]

def firstPoissonProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 9 → ℝ → ℂ) (R : ℝ) (y : Fin 9 → ℝ) : ℂ :=
  (∏ i, firstRootWindows V i (y i)) *
    W₁ (Real.exp (∑ i, firstLeftSlope i * y i)) *
    W₂ (Real.exp (∑ i, firstRightSlope i * y i)) *
    paperRadialFourier Φ (R * Real.exp (∑ i, firstKernelSlope i * y i))

def secondPoissonProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (∏ i, secondRootWindows V i (y i)) *
    W₁ (Real.exp (∑ i, secondLeftSlope i * y i)) *
    W₂ (Real.exp (∑ i, secondRightSlope i * y i)) *
    paperRadialFourier Φ (R * Real.exp (∑ i, secondKernelSlope i * y i))

def profileMode {ι : Type*} [Fintype ι] (V : ι → ℝ → ℂ)
    (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ) (t : Frequency) : ℂ :=
  ∏ i, V i (y i) * logPhase t.1 (a₁ i * y i) *
    logPhase t.2.1 (a₂ i * y i) * logPhase t.2.2 (ak i * y i)

theorem first_profile_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (M : Fin 9 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ V R y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient b₁ b₂ b₃ (t₁, t₂, t₃) *
            profileMode (firstRootWindows V) firstLeftSlope firstRightSlope firstKernelSlope y (t₁,t₂,t₃)) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ≤ C := by
  have hU : ∀ i y, firstRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hV _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  exact source_descent_profile_separation W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ
    (firstRootWindows V) firstLeftSlope firstRightSlope firstKernelSlope M hM hU A J

theorem second_profile_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 6 → ℝ, secondPoissonProfile W₁ W₂ Φ V R y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient b₁ b₂ b₃ (t₁, t₂, t₃) *
            profileMode (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope y (t₁,t₂,t₃)) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ≤ C := by
  have hU : ∀ i y, secondRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hV _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  exact source_descent_profile_separation W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ
    (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope M hM hU A J

end
end SevenEighths.InverseMoment

end OAI

end Source2322

/- Original source: OAI/NumberTheory/DirichletL/Descent/DescentHeight.lean; sha256: 3c10c23604c0e175c64f3cb796130de3db7fdfcd2a650e4fe8129e77f2f92976 -/
section Source2323
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
noncomputable section

theorem frequencyTwist_fourier_moment (J : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 (frequencyTwist g θ)) t‖) ≤
        C * (1 + ‖θ‖)^(J + (volume : Measure ℝ).integrablePower) := by
  let K := J + (volume : Measure ℝ).integrablePower
  let D := twistSourceBound g K
  have hD : 0 ≤ D := twistSourceBound_nonneg g K
  let C := (2 : ℝ)^J * (coefficientMomentBound 0 D + coefficientMomentBound J D)
  have hC : 0 ≤ C := mul_nonneg (by positivity) (add_nonneg
    (coefficientMomentBound_nonneg 0 D hD) (coefficientMomentBound_nonneg J D hD))
  refine ⟨C, hC, ?_⟩
  intro θ
  let H := (1 + ‖θ‖)^K
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hs : ∀ i ≤ K,
      (SchwartzMap.seminorm ℝ 0 i) (frequencyTwist g θ) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) (frequencyTwist g θ) ≤ D * H := by
    intro i hi
    exact (source_le_profileSourceBound (frequencyTwist g θ) K i hi).trans
      (profileSourceBound_frequencyTwist g θ K)
  have hh := uniform_fourier_one_plus_moment (frequencyTwist g θ) J 1 (D * H)
    (by norm_num) (mul_nonneg hD hH) (fun i hi => by simpa only [one_mul] using hs i hi)
  have hlin (j : ℕ) : coefficientMomentBound j (D * H) = coefficientMomentBound j D * H := by
    unfold coefficientMomentBound
    ring
  simpa only [one_mul, hlin, add_mul, C, H, K, mul_assoc, mul_add] using hh

theorem twisted_descent_profile_separation {ι : Type*} [Fintype ι]
    (g₁ g₂ Φ : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ θ₁ θ₂ : ℝ,
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * frequencyTwist g₁ θ₁ (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ₂ (∑ i, a₂ i * y i) *
          paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ (t₁,t₂,t₃) *
            (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
              logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ t‖) ≤
        C * (1 + ‖θ₁‖)^(J + (volume : Measure ℝ).integrablePower) *
          (1 + ‖θ₂‖)^(J + (volume : Measure ℝ).integrablePower) := by
  obtain ⟨Ck, hCk, hk⟩ := paperRadialFourier_log_separation_envelope Φ V ak M hM hV A J
  obtain ⟨C₁, hC₁, h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂, hC₂, h₂⟩ := frequencyTwist_fourier_moment J g₂
  refine ⟨C₁ * C₂ * Ck, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, he, hi, hb, hp⟩ := hk R hR
  refine ⟨b₃, ?_⟩
  intro θ₁ θ₂
  refine ⟨descent_profile_identity _ _ Φ V a₁ a₂ ak R b₃ he,
    tripleCoefficient_weighted_integrable _ _ _ J, ?_⟩
  rw [tripleCoefficient_weighted_integral]
  have hh := mul_le_mul (mul_le_mul (h₁ θ₁) (h₂ θ₂)
    (integral_nonneg (fun t => by positivity)) (by positivity)) hb
    (by positivity : 0 ≤ (1 + R)^A * ∫ t : ℝ, (1 + ‖t‖)^J * ‖b₃ t‖) (by positivity)
  convert hh using 1 <;> ring

end
end SevenEighths.InverseMoment

end OAI

end Source2323

/- Original source: OAI/NumberTheory/DirichletL/Inversion/ClippingProfiles.lean; sha256: 1da4c69d0ea7e310feeeed905e208f1eb62f87284a2ca24c321dfe7244f81c43 -/
section Source2324
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
namespace SevenEighths.InverseClippingProfiles

def logWindow (v : ℝ → ℂ) (L ρ : ℝ) (y : ℝ) : ℂ := v ((y + ρ) / L)

def rootedWindow (v : ℝ → ℂ) (L ρ a H : ℝ) (y : ℝ) : ℂ :=
  (Real.exp (a * y - H * L) : ℂ) * logWindow v L ρ y

lemma logWindow_contDiff (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (L ρ : ℝ) :
    ContDiff ℝ ∞ (logWindow v L ρ) := by
  exact hv.comp ((contDiff_id.add contDiff_const).div_const L)

lemma rootedWindow_contDiff (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (L ρ a H : ℝ) :
    ContDiff ℝ ∞ (rootedWindow v L ρ a H) := by
  apply ContDiff.mul _ (logWindow_contDiff v hv L ρ)
  exact Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

lemma logWindow_iteratedDeriv (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v)
    (L ρ : ℝ) (n : ℕ) :
    iteratedDeriv n (logWindow v L ρ) =
      fun y => (L⁻¹)^n • iteratedDeriv n v ((y + ρ) / L) := by
  have h : (logWindow v L ρ) =
      fun y => (fun z => v (L⁻¹ * z)) (y + ρ) := by
    funext y
    simp only [logWindow, div_eq_mul_inv, mul_comm]
  rw [h, iteratedDeriv_comp_add_const n (fun z => v (L⁻¹ * z)) ρ,
    iteratedDeriv_comp_const_smul (hv.of_le (by simp))]
  simp only [div_eq_mul_inv, mul_comm]

lemma expAffine_iteratedDeriv (a b : ℝ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => (Real.exp (a * y + b) : ℂ)) =
      fun y => (a : ℂ)^n * (Real.exp (a * y + b) : ℂ) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h := (((hasDerivAt_id y).const_mul a).add_const b).exp
    have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt y h).const_mul ((a : ℂ)^n)
    simp only [Function.comp_def, id_eq, Complex.ofRealCLM_apply] at hc
    rw [hc.deriv]
    simp only [mul_one, Complex.ofReal_mul, pow_succ]
    ring

lemma logWindow_support (v : ℝ → ℂ) (M B L ρ : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    Function.support (logWindow v L ρ) ⊆ Set.Icc (-(M+B)*L) ((M+B)*L) := by
  intro y hy
  have hy' := hv hy
  change -M ≤ (y+ρ)/L ∧ (y+ρ)/L ≤ M at hy'
  have hl := (le_div_iff₀ hL).mp hy'.1
  have hu := (div_le_iff₀ hL).mp hy'.2
  have hr := abs_le.mp hρ
  constructor <;> nlinarith

lemma rootedWindow_compact (v : ℝ → ℂ) (M B L ρ a H : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    HasCompactSupport (rootedWindow v L ρ a H) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro y hy
  apply logWindow_support v M B L ρ hL hρ hv
  exact (mul_ne_zero_iff.mp hy).2

def rootSchwartz (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  (rootedWindow_compact v M B L ρ a H hL hρ hv).toSchwartzMap
    (rootedWindow_contDiff v (v.smooth ⊤) L ρ a H)

@[simp] lemma rootSchwartz_apply (v : 𝓢(ℝ, ℂ)) (M B L ρ a H y : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    rootSchwartz v M B L ρ a H hL hρ hv y = rootedWindow v L ρ a H y := rfl

lemma derivative_support (v : 𝓢(ℝ, ℂ)) (M : ℝ)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (n : ℕ) :
    Function.support (iteratedDeriv n v) ⊆ Set.Icc (-M) M :=
  (subset_tsupport _).trans
    ((CompactProfileFamily.tsupport_iteratedDeriv_subset v n).trans
      (closure_minimal hv isClosed_Icc))

lemma root_exp_le_one (a H M B L ρ y : ℝ)
    (hL : 0 ≤ L) (hρ : |ρ| ≤ B*L) (hy : |(y+ρ)/L| ≤ M)
    (hL0 : L ≠ 0) (hH : |a| *(M+B) ≤ H) :
    Real.exp (a*y-H*L) ≤ 1 := by
  have hs : |y| ≤ (M+B)*L := by
    have h := (abs_le.mp hy)
    have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    have h1 := (le_div_iff₀ hLp).mp h.1
    have h2 := (div_le_iff₀ hLp).mp h.2
    have hr := abs_le.mp hρ
    apply abs_le.mpr
    constructor <;> nlinarith
  have ha := le_abs_self (a*y)
  rw [abs_mul] at ha
  have hh := mul_le_mul_of_nonneg_left hs (abs_nonneg a)
  have hb := mul_le_mul_of_nonneg_right hH hL
  apply Real.exp_le_one_iff.mpr
  nlinarith

lemma expAffine_iteratedFDeriv_norm (a b y : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x : ℝ => (Real.exp (a*x+b) : ℂ)) y‖ =
      |a|^n * Real.exp (a*y+b) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, expAffine_iteratedDeriv]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem rootSchwartz_seminorm (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n)
        (rootSchwartz v M B L ρ a H (by linarith) hρ hv) ≤
      ((M+B)*L)^k * (2:ℝ)^n * (1+|a|)^n * derivativeSeminormSum v 0 n := by
  have hLp : 0 < L := by linarith
  have hC : 0 ≤ ((M+B)*L)^k * (2:ℝ)^n * (1+|a|)^n *
      derivativeSeminormSum v 0 n := by
    apply mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
  apply SchwartzMap.seminorm_le_bound ℝ k n _ hC
  intro y
  have hbase (j : ℕ) (hj : j ≤ n) :
      ‖y‖^k * Real.exp (a*y-H*L) *
          ‖iteratedFDeriv ℝ j (logWindow v L ρ) y‖ ≤
        ((M+B)*L)^k * derivativeSeminormSum v 0 n := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logWindow_iteratedDeriv v (v.smooth ⊤)]
    by_cases hz : iteratedDeriv j v ((y+ρ)/L) = 0
    · simp only [hz, smul_zero, norm_zero, mul_zero]
      exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
    have harg := derivative_support v M hv j hz
    have hy : |(y+ρ)/L| ≤ M := abs_le.mpr harg
    have he := root_exp_le_one a H M B L ρ y hLp.le hρ hy (ne_of_gt hLp) hH
    have hx : ‖y‖ ≤ (M+B)*L := by
      have ht := logWindow_support (iteratedDeriv j v) M B L ρ hLp hρ
        (derivative_support v M hv j) hz
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor <;> linarith [ht.1, ht.2]
    have hd : ‖iteratedDeriv j v ((y+ρ)/L)‖ ≤ derivativeSeminormSum v 0 n := by
      have hh := (SchwartzMap.le_seminorm ℝ 0 j v ((y+ρ)/L)).trans
        (seminorm_le_derivativeSeminormSum v 0 n j hj)
      simpa only [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hh
    have hi : ‖L⁻¹‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (inv_nonneg.mpr hLp.le)]
      exact inv_le_one_of_one_le₀ hL
    have hs : ‖(L⁻¹)^j • iteratedDeriv j v ((y+ρ)/L)‖ ≤
        derivativeSeminormSum v 0 n := by
      rw [norm_smul, norm_pow]
      calc
        _ ≤ 1 * ‖iteratedDeriv j v ((y+ρ)/L)‖ := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hi
        _ ≤ _ := by simpa using hd
    calc
      _ ≤ ((M+B)*L)^k * 1 * derivativeSeminormSum v 0 n := by gcongr
      _ = _ := by ring
  have he : ContDiff ℝ ∞ (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))
  have hh := norm_iteratedFDeriv_mul_le he (logWindow_contDiff v (v.smooth ⊤) L ρ)
    y (n := n) (by exact_mod_cast le_top)
  change ‖y‖^k * ‖iteratedFDeriv ℝ n (rootedWindow v L ρ a H) y‖ ≤ _
  unfold rootedWindow
  calc
    _ ≤ ‖y‖^k * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) y‖ *
        ‖iteratedFDeriv ℝ (n-i) (logWindow v L ρ) y‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * |a|^i *
        (‖y‖^k * Real.exp (a*y-H*L) *
          ‖iteratedFDeriv ℝ (n-i) (logWindow v L ρ) y‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) =
        (fun x : ℝ => (Real.exp (a*x+(-H*L)) : ℂ)) by ext x; congr 2; ring]
      rw [expAffine_iteratedFDeriv_norm]
      rw [show a*y+(-H*L) = a*y-H*L by ring]
      ring
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * (1+|a|)^n *
        (((M+B)*L)^k * derivativeSeminormSum v 0 n) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp : |a|^i ≤ (1+|a|)^n := by
        calc
          _ ≤ (1+|a|)^i := by gcongr; linarith [abs_nonneg a]
          _ ≤ _ := pow_le_pow_right₀ (by linarith [abs_nonneg a])
            (Finset.mem_range_succ_iff.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity))
        (hbase (n-i) (Nat.sub_le _ _)) (by positivity) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring

def rootDerivativeBound (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (2:ℝ)^i * (1+|a|)^i * derivativeSeminormSum v 0 i

def twistedDerivativeBound (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) : ℝ :=
  (2:ℝ)^n * (1+2*Real.pi)^n * rootDerivativeBound v a n

lemma rootDerivativeBound_nonneg (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) :
    0 ≤ rootDerivativeBound v a n := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)

lemma twistedDerivativeBound_nonneg (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) :
    0 ≤ twistedDerivativeBound v a n :=
  mul_nonneg (by positivity) (rootDerivativeBound_nonneg _ _ _)

lemma rootSchwartz_derivativeSum (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    derivativeSeminormSum (rootSchwartz v M B L ρ a H (by linarith) hρ hv) k n ≤
      ((M+B)*L)^k * rootDerivativeBound v a n := by
  unfold derivativeSeminormSum rootDerivativeBound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  convert rootSchwartz_seminorm v M B L ρ a H hM hB hL hρ hv hH k i using 1
  ring

theorem rooted_twist_seminorm (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n)
      (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) ≤
      (M+B)^k * twistedDerivativeBound v a n * L^k * (1+‖θ‖)^n := by
  have hb := frequencyTwist_seminorm_polynomial
    (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ k n
  have hd := rootSchwartz_derivativeSum v M B L ρ a H hM hB hL hρ hv hH k n
  calc
    _ ≤ ((2:ℝ)^n * (1+2*Real.pi)^n *
        derivativeSeminormSum (rootSchwartz v M B L ρ a H (by linarith) hρ hv) k n) *
        (1+‖θ‖)^n := hb
    _ ≤ ((2:ℝ)^n * (1+2*Real.pi)^n *
        (((M+B)*L)^k * rootDerivativeBound v a n)) * (1+‖θ‖)^n := by gcongr
    _ = _ := by unfold twistedDerivativeBound; rw [mul_pow]; ring

def momentOrder (J : ℕ) : ℕ := J + (volume : Measure ℝ).integrablePower

def windowSourceBound (v : 𝓢(ℝ, ℂ)) (M B a : ℝ) (J : ℕ) : ℝ :=
  (1+(M+B)^(volume : Measure ℝ).integrablePower) *
    ∑ i ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a i

lemma windowSourceBound_nonneg (v : 𝓢(ℝ, ℂ)) (M B a : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (J : ℕ) : 0 ≤ windowSourceBound v M B a J := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun _ _ => twistedDerivativeBound_nonneg _ _ _)

theorem rooted_twist_moment_sources (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (J i : ℕ) (hi : i ≤ momentOrder J) :
    (SchwartzMap.seminorm ℝ 0 i)
        (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i)
        (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) ≤
      windowSourceBound v M B a J * L^(volume : Measure ℝ).integrablePower *
        (1+‖θ‖)^(momentOrder J) := by
  let p := (volume : Measure ℝ).integrablePower
  have h0 := rooted_twist_seminorm v M B L ρ a H θ hM hB hL hρ hv hH 0 i
  have hp := rooted_twist_seminorm v M B L ρ a H θ hM hB hL hρ hv hH p i
  simp only [pow_zero, one_mul, mul_one] at h0
  have hs : twistedDerivativeBound v a i ≤
      ∑ j ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a j := by
    apply Finset.single_le_sum (fun j _ => twistedDerivativeBound_nonneg v a j)
    exact Finset.mem_range_succ_iff.mpr hi
  have hl : 1 ≤ L^p := one_le_pow₀ hL
  have ht : (1+‖θ‖)^i ≤ (1+‖θ‖)^(momentOrder J) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg θ]) hi
  have hc := twistedDerivativeBound_nonneg v a i
  have hsum : 0 ≤ ∑ j ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a j :=
    Finset.sum_nonneg (fun _ _ => twistedDerivativeBound_nonneg _ _ _)
  calc
    _ ≤ twistedDerivativeBound v a i * (1+‖θ‖)^i +
        (M+B)^p * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := add_le_add h0 hp
    _ ≤ twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i +
        (M+B)^p * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := by gcongr; nlinarith
    _ = (1+(M+B)^p) * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := by ring
    _ ≤ _ := by unfold windowSourceBound; gcongr

lemma coefficientMomentBound_mul (J : ℕ) (C D : ℝ) :
    coefficientMomentBound J (C*D) = coefficientMomentBound J C * D := by
  unfold coefficientMomentBound
  ring

theorem rooted_twist_fourier_moment (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H) (J : ℕ) :
    (∫ t : ℝ, (1+‖t‖)^J *
      ‖(𝓕 (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ)) t‖) ≤
      ((2:ℝ)^J * (coefficientMomentBound 0 (windowSourceBound v M B a J) +
        coefficientMomentBound J (windowSourceBound v M B a J))) *
      L^(volume : Measure ℝ).integrablePower * (1+‖θ‖)^(momentOrder J) := by
  have hc := windowSourceBound_nonneg v M B a hM hB J
  have h := uniform_fourier_one_plus_moment
    (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) J 1
    (windowSourceBound v M B a J * L^(volume : Measure ℝ).integrablePower *
      (1+‖θ‖)^(momentOrder J)) (by norm_num) (by positivity)
    (by
      intro i hi
      simpa using (rooted_twist_moment_sources v M B L ρ a H θ
        hM hB hL hρ hv hH J i hi))
  simp only [one_mul, coefficientMomentBound_mul] at h
  convert h using 1
  ring

theorem child_log_window_parameters (η Z δ : ℝ) (_hη : 0 ≤ η)
    (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hδu : δ ≤ 6*η) :
    0 ≤ δ*Real.log Z ∧ |δ*Real.log Z| ≤ 6*(η*Real.log Z) := by
  have hz : 0 ≤ Real.log Z := Real.log_nonneg hZ
  constructor
  · positivity
  · rw [abs_of_nonneg (by positivity : 0 ≤ δ*Real.log Z)]
    nlinarith [mul_le_mul_of_nonneg_right hδu hz]

theorem clipping_ratio_of_column_witness (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hwitness : w (q / Z^N) ≠ 0) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  have hz : 0 < Z := by linarith
  have hn : 0 ≤ max 0 N-N := sub_nonneg.mpr (le_max_right _ _)
  refine ⟨Real.one_le_rpow hZ.le hn, ?_⟩
  by_cases hN : 0 ≤ N
  · simpa [max_eq_right hN] using hb
  · have hN' : N ≤ 0 := le_of_lt (lt_of_not_ge hN)
    rw [max_eq_left hN', zero_sub, Real.rpow_neg hz.le]
    have hsupport := (hw hwitness).2
    calc
      _ = 1 / Z^N := (one_div _).symm
      _ ≤ q / Z^N := div_le_div_of_nonneg_right hq (Real.rpow_nonneg hz.le _)
      _ ≤ b := hsupport

theorem clipped_positive_support (w : ℝ → ℂ) (a b c : ℝ)
    (ha : 0 < a) (hc : 1 ≤ c) (hcb : c ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) :
    Function.support (fun y => w (c*y)) ⊆ Set.Icc (a/b) b := by
  intro y hy
  have hs := hw hy
  have hcp : 0 < c := by linarith
  have hbp : 0 < b := lt_of_lt_of_le hcp hcb
  have hyp : 0 < y := by nlinarith [hs.1]
  constructor
  · apply (div_le_iff₀ hbp).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcb hyp.le, hs.1]
  · nlinarith [hs.2]

theorem clipped_log_source (w : ℝ → ℂ) (c y : ℝ) (hc : 0 < c) :
    w (c*Real.exp y) = (fun s => w (Real.exp s)) (y+Real.log c) := by
  change w (c*Real.exp y) = w (Real.exp (y+Real.log c))
  rw [Real.exp_add, Real.exp_log hc]
  congr 1
  ring

open InverseMoment

def firstRootExponent (y : Fin 9 → ℝ) : ℝ :=
  -y 3-y 4/2-y 5-(y 7+y 8)/2

def secondRootExponent (y : Fin 6 → ℝ) : ℝ :=
  -y 1-y 2-(y 4+y 5)/2

theorem first_root_coupled_identity (y : Fin 9 → ℝ) :
    firstRootExponent y = -y 3-y 4/2+(y 0+y 1)/2+y 2 -
      ((∑ i, firstLeftSlope i*y i)+(∑ i, firstRightSlope i*y i))/2 := by
  simp [firstRootExponent, firstLeftSlope, firstRightSlope, Fin.sum_univ_succ]
  ring

theorem second_root_coupled_identity (y : Fin 6 → ℝ) :
    secondRootExponent y = -y 1+y 0 -
      ((∑ i, secondLeftSlope i*y i)+(∑ i, secondRightSlope i*y i))/2 := by
  simp [secondRootExponent, secondLeftSlope, secondRightSlope, Fin.sum_univ_succ]
  ring

theorem first_root_budget (y : Fin 9 → ℝ) (L : ℝ)
    (h0 : |y 0| ≤ L) (h1 : |y 1| ≤ L) (h2 : |y 2| ≤ L)
    (h3 : |y 3| ≤ L) (h4 : |y 4| ≤ L)
    (hl : |∑ i, firstLeftSlope i*y i| ≤ L)
    (hr : |∑ i, firstRightSlope i*y i| ≤ L) :
    firstRootExponent y ≤ (9/2:ℝ)*L := by
  rw [first_root_coupled_identity]
  rcases abs_le.mp h0 with ⟨_, h0⟩
  rcases abs_le.mp h1 with ⟨_, h1⟩
  rcases abs_le.mp h2 with ⟨_, h2⟩
  rcases abs_le.mp h3 with ⟨h3, _⟩
  rcases abs_le.mp h4 with ⟨h4, _⟩
  rcases abs_le.mp hl with ⟨hl, _⟩
  rcases abs_le.mp hr with ⟨hr, _⟩
  linarith

theorem second_root_budget (y : Fin 6 → ℝ) (L : ℝ)
    (h0 : |y 0| ≤ L) (h1 : |y 1| ≤ L)
    (hl : |∑ i, secondLeftSlope i*y i| ≤ 4*L)
    (hr : |∑ i, secondRightSlope i*y i| ≤ 4*L) :
    secondRootExponent y ≤ 6*L := by
  rw [second_root_coupled_identity]
  rcases abs_le.mp h0 with ⟨_, h0⟩
  rcases abs_le.mp h1 with ⟨h1, _⟩
  rcases abs_le.mp hl with ⟨hl, _⟩
  rcases abs_le.mp hr with ⟨hr, _⟩
  linarith

def firstRootSlope : Fin 9 → ℝ := ![0,0,0,-1,-(1/2),-1,0,-(1/2),-(1/2)]
def secondRootSlope : Fin 6 → ℝ := ![0,-1,-1,0,-(1/2),-(1/2)]

lemma inverseNormWindow_exp (V : ℝ → ℂ) (y : ℝ) :
    inverseNormWindow V y = (Real.exp (-y) : ℂ)*V y := by
  simp only [inverseNormWindow, Real.exp_neg, Complex.ofReal_inv, div_eq_mul_inv]
  ring

lemma inverseRootWindow_exp (V : ℝ → ℂ) (y : ℝ) :
    inverseRootWindow V y = (Real.exp (-(y/2)) : ℂ)*V y := by
  rw [inverseRootWindow, ← Real.exp_half, Real.exp_neg, Complex.ofReal_inv]
  ring

theorem firstRootWindows_exp (V : Fin 9 → ℝ → ℂ) (i : Fin 9) (y : ℝ) :
    firstRootWindows V i y = (Real.exp (firstRootSlope i*y) : ℂ)*V i y := by
  fin_cases i <;> simp [firstRootWindows, firstRootSlope, inverseNormWindow_exp,
    inverseRootWindow_exp, neg_mul]
  all_goals left; congr 1; ring

theorem secondRootWindows_exp (V : Fin 6 → ℝ → ℂ) (i : Fin 6) (y : ℝ) :
    secondRootWindows V i y = (Real.exp (secondRootSlope i*y) : ℂ)*V i y := by
  fin_cases i <;> simp [secondRootWindows, secondRootSlope, inverseNormWindow_exp,
    inverseRootWindow_exp, neg_mul]
  all_goals left; congr 1; ring

theorem firstRootWindows_prod (V : Fin 9 → ℝ → ℂ) (y : Fin 9 → ℝ) :
    (∏ i, firstRootWindows V i (y i)) =
      (Real.exp (firstRootExponent y) : ℂ) * ∏ i, V i (y i) := by
  simp_rw [firstRootWindows_exp]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [firstRootSlope, firstRootExponent, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num
  ring

theorem secondRootWindows_prod (V : Fin 6 → ℝ → ℂ) (y : Fin 6 → ℝ) :
    (∏ i, secondRootWindows V i (y i)) =
      (Real.exp (secondRootExponent y) : ℂ) * ∏ i, V i (y i) := by
  simp_rw [secondRootWindows_exp]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [secondRootSlope, secondRootExponent, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num
  ring

theorem first_profile_normalized_identity (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 9 → ℝ → ℂ) (R L : ℝ) (y : Fin 9 → ℝ) :
    (Real.exp (-(9/2:ℝ)*L) : ℂ)*firstPoissonProfile W₁ W₂ Φ V R y =
      (Real.exp (firstRootExponent y-(9/2:ℝ)*L) : ℂ) *
      (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, firstLeftSlope i*y i)) *
      W₂ (Real.exp (∑ i, firstRightSlope i*y i)) *
      EisensteinSchwartzPoisson.paperRadialFourier Φ
        (R*Real.exp (∑ i, firstKernelSlope i*y i)) := by
  rw [firstPoissonProfile, firstRootWindows_prod]
  simp only [Real.exp_sub, div_eq_mul_inv, neg_mul, Real.exp_neg,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem second_profile_normalized_identity (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) :
    (Real.exp (-6*L) : ℂ)*secondPoissonProfile W₁ W₂ Φ V R y =
      (Real.exp (secondRootExponent y-6*L) : ℂ) *
      (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, secondLeftSlope i*y i)) *
      W₂ (Real.exp (∑ i, secondRightSlope i*y i)) *
      EisensteinSchwartzPoisson.paperRadialFourier Φ
        (R*Real.exp (∑ i, secondKernelSlope i*y i)) := by
  rw [secondPoissonProfile, secondRootWindows_prod]
  simp only [Real.exp_sub, div_eq_mul_inv, neg_mul, Real.exp_neg,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem fourier_phase_shift (f : ℝ → ℂ) (θ t : ℝ) :
    (𝓕 (fun y => logPhase θ y * f y)) t = (𝓕 f) (t-θ) := by
  simp only [Real.fourier_eq', logPhase, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translate (f : ℝ → ℂ) (ρ t : ℝ) :
    (𝓕 (fun y => f (y+ρ))) t = logPhase t ρ * (𝓕 f) t := by
  have h := congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℝ) (innerₗ ℝ) f ρ) t
  change _ = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t at h
  have h' : (𝓕 (fun y => f (y+ρ))) t = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t := by
    simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, Function.comp_def, innerₗ_apply_apply] using h
  rw [h']
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, logPhase]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translated_twist (f : ℝ → ℂ) (ρ θ t : ℝ) :
    (𝓕 (fun y => logPhase θ y * f (y+ρ))) t =
      logPhase (t-θ) ρ * (𝓕 f) (t-θ) := by
  rw [fourier_phase_shift, fourier_translate]

theorem norm_fourier_translated_twist (f : ℝ → ℂ) (ρ θ t : ℝ) :
    ‖(𝓕 (fun y => logPhase θ y * f (y+ρ))) t‖ = ‖(𝓕 f) (t-θ)‖ := by
  rw [fourier_translated_twist, norm_mul, logPhase_norm, one_mul]

theorem rooted_family_fourier_joint_measurable (v : 𝓢(ℝ, ℂ)) (a H : ℝ) :
    StronglyMeasurable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
      (𝓕 (fun y => logPhase p.1.2.2 y * rootedWindow v p.1.1 p.1.2.1 a H y)) p.2) := by
  apply InverseKernelSourceUniform.fourier_joint_stronglyMeasurable
    (fun q : ℝ × ℝ × ℝ => fun y => logPhase q.2.2 y * rootedWindow v q.1 q.2.1 a H y)
  apply Measurable.stronglyMeasurable
  change Measurable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
    logPhase p.1.2.2 p.2 * ((Real.exp (a*p.2-H*p.1.1) : ℂ) *
      v ((p.2+p.1.2.1)/p.1.1)))
  have hp : Measurable (fun p : (ℝ × ℝ × ℝ) × ℝ => logPhase p.1.2.2 p.2) := by
    unfold logPhase
    fun_prop
  exact hp.mul ((show Measurable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
    (Real.exp (a*p.2-H*p.1.1) : ℂ)) by fun_prop).mul
      (v.continuous.measurable.comp (by fun_prop)))

def childWindowDensity (v : 𝓢(ℝ, ℂ)) (η Z δ θ t : ℝ) : ℂ :=
  (𝓕 (fun y => logPhase θ y * v ((y+δ*Real.log Z)/(η*Real.log Z)))) t

def windowMomentConstant (v : 𝓢(ℝ, ℂ)) (M B a : ℝ) (J : ℕ) : ℝ :=
  (2:ℝ)^J * (coefficientMomentBound 0 (windowSourceBound v M B a J) +
    coefficientMomentBound J (windowSourceBound v M B a J))

theorem childWindowDensity_moment (v : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 ≤ M)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (J : ℕ)
    (η Z δ θ : ℝ) (hη : 0 ≤ η) (hZ : 1 ≤ Z)
    (hL : 1 ≤ η*Real.log Z) (hδ : 0 ≤ δ) (hδu : δ ≤ 6*η) :
    Integrable (fun t : ℝ => (1+‖t‖)^J * ‖childWindowDensity v η Z δ θ t‖) ∧
    (∫ t : ℝ, (1+‖t‖)^J * ‖childWindowDensity v η Z δ θ t‖) ≤
      windowMomentConstant v M 6 0 J * (η*Real.log Z)^(volume : Measure ℝ).integrablePower *
        (1+‖θ‖)^(momentOrder J) := by
  have hρ := (child_log_window_parameters η Z δ hη hZ hδ hδu).2
  let g := frequencyTwist (rootSchwartz v M 6 (η*Real.log Z) (δ*Real.log Z) 0 0
    (by linarith) hρ hv) θ
  have he (t : ℝ) : childWindowDensity v η Z δ θ t = (𝓕 g) t := by
    rw [congrFun (SchwartzMap.fourier_coe g) t]
    unfold childWindowDensity
    have hg : (g : ℝ → ℂ) = fun y =>
        logPhase θ y * v ((y+δ*Real.log Z)/(η*Real.log Z)) := by
      funext y
      simp [g, frequencyTwist_apply, rootSchwartz_apply, rootedWindow, logWindow]
    rw [hg]
  simp_rw [he]
  refine ⟨AnalyticBridge.schwartz_fourier_one_plus_integrable g J, ?_⟩
  exact rooted_twist_fourier_moment v M 6 (η*Real.log Z) (δ*Real.log Z) 0 0 θ
    hM (by norm_num) hL hρ hv (by simp) J

theorem retained_clipped_column (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hwitness : w (q/Z^N) ≠ 0) :
    let c := Z^(max 0 N-N)
    1 ≤ c ∧ c ≤ b ∧
    Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b ∧
    ∀ θ t : ℝ,
      (𝓕 (fun y => logPhase θ y * w (c*Real.exp y))) t =
        logPhase (t-θ) (Real.log c) * (𝓕 (fun y => w (Real.exp y))) (t-θ) := by
  dsimp only
  have hc := clipping_ratio_of_column_witness w Z N q a b hZ hq hb hw hwitness
  refine ⟨hc.1, hc.2, clipped_positive_support w a b _ ha hc.1 hc.2 hw, ?_⟩
  intro θ t
  have he : (fun y => logPhase θ y * w (Z^(max 0 N-N)*Real.exp y)) =
      (fun y => logPhase θ y * (fun s => w (Real.exp s)) (y+Real.log (Z^(max 0 N-N)))) := by
    ext y
    rw [clipped_log_source w _ y (by linarith)]
  rw [he]
  exact fourier_translated_twist (fun s => w (Real.exp s)) (Real.log (Z^(max 0 N-N))) θ t

theorem translated_twist_moment_uniform (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ θ : ℝ,
      Integrable (fun t : ℝ => (1+‖t‖)^J *
        ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖) ≤
        C*(1+‖θ‖)^(momentOrder J) := by
  obtain ⟨C, hC, hb⟩ := InverseMoment.frequencyTwist_fourier_moment J g
  refine ⟨C, hC, ?_⟩
  intro ρ θ
  have he (t : ℝ) : ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖ =
      ‖(𝓕 (frequencyTwist g θ)) t‖ := by
    rw [norm_fourier_translated_twist, congrFun (SchwartzMap.fourier_coe _) t]
    have hf : (frequencyTwist g θ : ℝ → ℂ) = fun y => logPhase θ y * g y := by
      funext y
      exact frequencyTwist_apply g θ y
    rw [hf, fourier_phase_shift]
  simp_rw [he]
  exact ⟨AnalyticBridge.schwartz_fourier_one_plus_integrable _ _, hb θ⟩

theorem eventually_log_scale_pow_le (C η π : ℝ) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hπ : 0 < π) (k : ℕ) :
    ∀ᶠ Z : ℝ in Filter.atTop, C*(η*Real.log Z)^k ≤ Z^π := by
  have h := (_root_.isLittleO_log_rpow_rpow_atTop (k:ℝ) hπ).const_mul_left (C*η^k)
  filter_upwards [h.bound (by norm_num : (0:ℝ) < 1),
    Filter.eventually_ge_atTop (1:ℝ)] with Z hZ hZ1
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  have hz : 0 ≤ Z := by linarith
  rw [Real.rpow_natCast, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.rpow_nonneg hz π), one_mul] at hZ
  convert hZ using 1
  ring

def firstBalancedSlope : Fin 9 → ℝ := ![1/2,1/2,1,-1,-(1/2),0,0,0,0]
def secondBalancedSlope : Fin 6 → ℝ := ![1,-1,0,0,0,0]

theorem first_root_normalization_split (y : Fin 9 → ℝ) (L : ℝ) :
    Real.exp (firstRootExponent y-(9/2:ℝ)*L) =
      (∏ i, Real.exp (firstBalancedSlope i*y i-|firstBalancedSlope i| *L)) *
      Real.exp (-(∑ i, firstLeftSlope i*y i)/2-L/2) *
      Real.exp (-(∑ i, firstRightSlope i*y i)/2-L/2) := by
  rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [firstRootExponent, firstBalancedSlope, firstLeftSlope, firstRightSlope,
    Fin.sum_univ_succ]
  ring

theorem second_root_normalization_split (y : Fin 6 → ℝ) (L : ℝ) :
    Real.exp (secondRootExponent y-6*L) =
      (∏ i, Real.exp (secondBalancedSlope i*y i-|secondBalancedSlope i| *L)) *
      Real.exp (-(∑ i, secondLeftSlope i*y i)/2-2*L) *
      Real.exp (-(∑ i, secondRightSlope i*y i)/2-2*L) := by
  rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [secondRootExponent, secondBalancedSlope, secondLeftSlope, secondRightSlope,
    Fin.sum_univ_succ]
  ring

end SevenEighths.InverseClippingProfiles

end

end OAI

end Source2324

/- Original source: OAI/NumberTheory/DirichletL/Descent/WindowFourier.lean; sha256: 615b7d415c0e5e29f3544f24a15c3a45dc65165e5103012f012438ec3bc4a9ed -/
section Source2325
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

variable {ι : Type*} [Fintype ι]

def coordinateDensity (g : ι → 𝓢(ℝ, ℂ)) (t : ι → ℝ) : ℂ :=
  ∏ i, (𝓕 (g i)) (t i)

def coordinatePhase (t y : ι → ℝ) : ℂ := ∏ i, logPhase (t i) (y i)

theorem coordinate_fourier_inversion (g : ι → 𝓢(ℝ, ℂ)) (y : ι → ℝ) :
    (∏ i, g i (y i)) = ∫ t : ι → ℝ, coordinateDensity g t * coordinatePhase t y := by
  simp only [coordinateDensity, coordinatePhase, ← Finset.prod_mul_distrib]
  have hp := integral_fintype_prod_volume_eq_prod (E := fun _ : ι => ℝ)
    (fun (i : ι) (t : ℝ) => (𝓕 (g i) : 𝓢(ℝ, ℂ)) t * logPhase t (y i))
  rw [hp]
  apply Finset.prod_congr rfl
  intro i hi
  simpa only [mul_comm] using schwartz_logPhase_inversion (g i) (y i)

theorem coordinate_density_weighted_integrable (g : ι → 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ι → ℝ => (∏ i, (1 + ‖t i‖)^J) * ‖coordinateDensity g t‖) := by
  have hi (i : ι) := AnalyticBridge.schwartz_fourier_one_plus_integrable (g i) J
  convert Integrable.fintype_prod hi using 1
  funext t
  simp only [coordinateDensity, norm_prod, Finset.prod_mul_distrib]

theorem coordinate_density_weighted_integral (g : ι → 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ t : ι → ℝ, (∏ i, (1 + ‖t i‖)^J) * ‖coordinateDensity g t‖) =
      ∏ i, ∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 (g i)) t‖ := by
  simp only [coordinateDensity, norm_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_volume_eq_prod (E := fun _ : ι => ℝ)
    (fun i t => (1 + ‖t‖)^J * ‖(𝓕 (g i)) t‖)

def pureProfileMode (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ)
    (t : Frequency) (u : ι → ℝ) : ℂ :=
  ∏ i, logPhase (u i) (y i) * logPhase t.1 (a₁ i * y i) *
    logPhase t.2.1 (a₂ i * y i) * logPhase t.2.2 (ak i * y i)

theorem profileMode_coordinate_separation (g : ι → 𝓢(ℝ, ℂ))
    (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ) (t : Frequency) :
    profileMode (fun i => g i) a₁ a₂ ak y t =
      ∫ u : ι → ℝ, coordinateDensity g u * pureProfileMode a₁ a₂ ak y t u := by
  simp only [profileMode, pureProfileMode, Finset.prod_mul_distrib]
  simp only [← mul_assoc]
  rw [integral_mul_const, integral_mul_const, integral_mul_const]
  have he := coordinate_fourier_inversion g y
  simp only [coordinatePhase] at he
  rw [← he]

 theorem pureProfileMode_norm (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ)
    (t : Frequency) (u : ι → ℝ) : ‖pureProfileMode a₁ a₂ ak y t u‖ = 1 := by
  simp [pureProfileMode, norm_prod,  logPhase_norm]

def fullProfileDensity (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (p : Frequency × (ι → ℝ)) : ℂ :=
  tripleCoefficient b₁ b₂ b₃ p.1 * coordinateDensity g p.2

def tripleHeight (J : ℕ) (t : Frequency) : ℝ :=
  (1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J

def coordinateHeight (J : ℕ) (u : ι → ℝ) : ℝ := ∏ i, (1 + ‖u i‖)^J

theorem fullProfileDensity_weighted_integrable (g : ι → 𝓢(ℝ, ℂ))
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun p : Frequency × (ι → ℝ) =>
      tripleHeight J p.1 * coordinateHeight J p.2 * ‖fullProfileDensity g b₁ b₂ b₃ p‖) := by
  convert (tripleCoefficient_weighted_integrable b₁ b₂ b₃ J).mul_prod
    (coordinate_density_weighted_integrable g J) using 1
  funext p
  simp only [tripleHeight, coordinateHeight, fullProfileDensity, norm_mul]
  ring

theorem fullProfileDensity_weighted_integral (g : ι → 𝓢(ℝ, ℂ))
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ p : Frequency × (ι → ℝ),
      tripleHeight J p.1 * coordinateHeight J p.2 * ‖fullProfileDensity g b₁ b₂ b₃ p‖) =
      (∫ t : Frequency, tripleHeight J t * ‖tripleCoefficient b₁ b₂ b₃ t‖) *
      (∏ i, ∫ u : ℝ, (1 + ‖u‖)^J * ‖(𝓕 (g i)) u‖) := by
  have he (p : Frequency × (ι → ℝ)) :
      tripleHeight J p.1 * coordinateHeight J p.2 * ‖fullProfileDensity g b₁ b₂ b₃ p‖ =
        (tripleHeight J p.1 * ‖tripleCoefficient b₁ b₂ b₃ p.1‖) *
        (coordinateHeight J p.2 * ‖coordinateDensity g p.2‖) := by
    simp only [fullProfileDensity, norm_mul]
    ring
  simp_rw [he]
  simp only [Measure.volume_eq_prod]
  rw [integral_prod_mul (fun t : Frequency => tripleHeight J t * ‖tripleCoefficient b₁ b₂ b₃ t‖)
    (fun u : ι → ℝ => coordinateHeight J u * ‖coordinateDensity g u‖)]
  simp only [coordinateHeight]
  rw [coordinate_density_weighted_integral g J]

theorem profile_integral_coordinate_absorption (g : ι → 𝓢(ℝ, ℂ))
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (a₁ a₂ ak y : ι → ℝ) :
    (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) *
        profileMode (fun i => g i) a₁ a₂ ak y (t₁,t₂,t₃)) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : ι → ℝ,
      fullProfileDensity g b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
        pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u := by
  apply integral_congr_ae
  filter_upwards with t₁
  apply integral_congr_ae
  filter_upwards with t₂
  apply integral_congr_ae
  filter_upwards with t₃
  rw [profileMode_coordinate_separation, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [fullProfileDensity]
  ring

def profileHeight (a₁ a₂ ak : ι → ℝ) (t : Frequency) (u : ι → ℝ) (i : ι) : ℝ :=
  u i + a₁ i * t.1 + a₂ i * t.2.1 + ak i * t.2.2

lemma logPhase_scaled_coordinate (t a y : ℝ) : logPhase t (a*y) = logPhase (a*t) y := by
  unfold logPhase
  congr 1
  push_cast
  ring

theorem pureProfileMode_height (a₁ a₂ ak y : ι → ℝ) (t : Frequency) (u : ι → ℝ) :
    pureProfileMode a₁ a₂ ak y t u = ∏ i, logPhase (profileHeight a₁ a₂ ak t u i) (y i) := by
  apply Finset.prod_congr rfl
  intro i hi
  simp only [profileHeight, logPhase_add_frequency, logPhase_scaled_coordinate]

end
end SevenEighths.InverseMoment

end OAI

end Source2325

/- Original source: OAI/NumberTheory/DirichletL/Descent/RootWindows.lean; sha256: 971384242537e44b41713306cdadeed7c60d75b0d2706e519ff60d8a336b980d -/
section Source2326
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

theorem inverseNormWindow_contDiff (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (inverseNormWindow V) := by
  unfold inverseNormWindow
  have hn : ∀ y : ℝ, (Real.exp y : ℂ) ≠ 0 := by
    intro y
    exact_mod_cast Real.exp_ne_zero y
  simpa only [div_eq_mul_inv, Pi.inv_apply, Function.comp_apply, Complex.ofRealCLM_apply] using
    hV.mul ((Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).inv hn)

theorem inverseRootWindow_contDiff (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (inverseRootWindow V) := by
  unfold inverseRootWindow
  have hs : ContDiff ℝ ∞ (fun y : ℝ => Real.sqrt (Real.exp y)) :=
    Real.contDiff_exp.sqrt Real.exp_ne_zero
  have hn : ∀ y : ℝ, (Real.sqrt (Real.exp y) : ℂ) ≠ 0 := by
    intro y
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (Real.exp_pos y))
  simpa only [div_eq_mul_inv, Pi.inv_apply, Function.comp_apply, Complex.ofRealCLM_apply] using
    hV.mul ((Complex.ofRealCLM.contDiff.comp hs).inv hn)

theorem inverseNormWindow_compact (V : ℝ → ℂ) (hV : HasCompactSupport V) :
    HasCompactSupport (inverseNormWindow V) := by
  apply hV.mono
  intro y hy
  exact (div_ne_zero_iff.mp hy).1

theorem inverseRootWindow_compact (V : ℝ → ℂ) (hV : HasCompactSupport V) :
    HasCompactSupport (inverseRootWindow V) := by
  apply hV.mono
  intro y hy
  exact (div_ne_zero_iff.mp hy).1

theorem firstRootWindows_smooth_compact (V : Fin 9 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i)) :
    ∀ i, ContDiff ℝ ∞ (firstRootWindows V i) ∧ HasCompactSupport (firstRootWindows V i) := by
  intro i
  fin_cases i <;> first
    | exact ⟨hV _, hS _⟩
    | exact ⟨inverseNormWindow_contDiff _ (hV _), inverseNormWindow_compact _ (hS _)⟩
    | exact ⟨inverseRootWindow_contDiff _ (hV _), inverseRootWindow_compact _ (hS _)⟩

theorem secondRootWindows_smooth_compact (V : Fin 6 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i)) :
    ∀ i, ContDiff ℝ ∞ (secondRootWindows V i) ∧ HasCompactSupport (secondRootWindows V i) := by
  intro i
  fin_cases i <;> first
    | exact ⟨hV _, hS _⟩
    | exact ⟨inverseNormWindow_contDiff _ (hV _), inverseNormWindow_compact _ (hS _)⟩
    | exact ⟨inverseRootWindow_contDiff _ (hV _), inverseRootWindow_compact _ (hS _)⟩

end
end SevenEighths.InverseMoment

end OAI

end Source2326

/- Original source: OAI/NumberTheory/DirichletL/Descent/FullProfile.lean; sha256: 5a655ad3986219a6de60099bd72b644f66a407dc15d21628d79b99bbd5e00810 -/
section Source2327
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

def rootSchwartz {ι : Type*} (U : ι → ℝ → ℂ)
    (hU : ∀ i, ContDiff ℝ ∞ (U i)) (hS : ∀ i, HasCompactSupport (U i))
    (i : ι) : 𝓢(ℝ, ℂ) := (hS i).toSchwartzMap (hU i)

@[simp] theorem rootSchwartz_apply {ι : Type*} (U : ι → ℝ → ℂ)
    (hU : ∀ i, ContDiff ℝ ∞ (U i)) (hS : ∀ i, HasCompactSupport (U i))
    (i : ι) (y : ℝ) : rootSchwartz U hU hS i y = U i y := rfl

theorem full_source_profile_common_measure {ι : Type*} [Fintype ι]
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (U : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hU : ∀ i, ContDiff ℝ ∞ (U i)) (hS : ∀ i, HasCompactSupport (U i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, U i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ i, U i (y i)) * W₁ (Real.exp (∑ i, a₁ i * y i)) *
          W₂ (Real.exp (∑ i, a₂ i * y i)) *
          paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : ι → ℝ,
          fullProfileDensity (rootSchwartz U hU hS) b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight a₁ a₂ ak (t₁,t₂,t₃) u i) (y i))) ∧
      Integrable (fun p : Frequency × (ι → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (rootSchwartz U hU hS) b₁ b₂ b₃ p‖) ∧
      (1 + R)^A * (∫ p : Frequency × (ι → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (rootSchwartz U hU hS) b₁ b₂ b₃ p‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hsep⟩ := source_descent_profile_separation
    W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ U a₁ a₂ ak M hM hbox A J
  let g := rootSchwartz U hU hS
  let D : ℝ := ∏ i, ∫ u : ℝ, (1 + ‖u‖)^J * ‖(𝓕 (g i)) u‖
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i hi => integral_nonneg (fun u => by positivity))
  refine ⟨b₁,b₂,C*D,mul_nonneg hC hD, ?_⟩
  intro R hR
  obtain ⟨b₃,he,hi,hb⟩ := hsep R hR
  refine ⟨b₃,?_,fullProfileDensity_weighted_integrable g b₁ b₂ b₃ J,?_⟩
  · intro y
    rw [he y]
    have habs := profile_integral_coordinate_absorption g b₁ b₂ b₃ a₁ a₂ ak y
    simpa only [g, profileMode, rootSchwartz_apply, pureProfileMode_height] using habs
  · rw [fullProfileDensity_weighted_integral]
    change (1+R)^A * ((∫ t : Frequency, tripleHeight J t * ‖tripleCoefficient b₁ b₂ b₃ t‖) * D) ≤ C*D
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hb hD

def firstRootSchwartz (V : Fin 9 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i)) :
    Fin 9 → 𝓢(ℝ, ℂ) :=
  rootSchwartz (firstRootWindows V)
    (fun i => (firstRootWindows_smooth_compact V hV hS i).1)
    (fun i => (firstRootWindows_smooth_compact V hV hS i).2)

theorem first_full_profile_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (M : Fin 9 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ V R y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 9 → ℝ,
          fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope
              (t₁,t₂,t₃) u i) (y i))) ∧
      Integrable (fun p : Frequency × (Fin 9 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + R)^A * (∫ p : Frequency × (Fin 9 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  have hb : ∀ i y, firstRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  exact full_source_profile_common_measure W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ
    (firstRootWindows V) firstLeftSlope firstRightSlope firstKernelSlope M
    (fun i => (firstRootWindows_smooth_compact V hV hS i).1)
    (fun i => (firstRootWindows_smooth_compact V hV hS i).2) hM hb A J

def secondRootSchwartz (V : Fin 6 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i)) :
    Fin 6 → 𝓢(ℝ, ℂ) :=
  rootSchwartz (secondRootWindows V)
    (fun i => (secondRootWindows_smooth_compact V hV hS i).1)
    (fun i => (secondRootWindows_smooth_compact V hV hS i).2)

theorem second_full_profile_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 6 → ℝ, secondPoissonProfile W₁ W₂ Φ V R y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
          fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope
              (t₁,t₂,t₃) u i) (y i))) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + R)^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  have hb : ∀ i y, secondRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  exact full_source_profile_common_measure W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ
    (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope M
    (fun i => (secondRootWindows_smooth_compact V hV hS i).1)
    (fun i => (secondRootWindows_smooth_compact V hV hS i).2) hM hb A J

end
end SevenEighths.InverseMoment

end OAI

end Source2327

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondProfileIdentity.lean; sha256: 851d9ba10ac7e31a261133abc29153b2ea01826ca57e2d4d49d3d6db22d5b75b -/
section Source2328
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondNormProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (q : Fin 6 → ℝ) : ℂ :=
  (∏ i, V i (Real.log (q i))) * W₁ (q 0*q 2*q 4) * W₂ (q 0*q 2*q 5) *
    paperRadialFourier Φ (R*q 3/(q 1*(q 2)^2*q 4*q 5)) /
      ((q 1:ℂ)*(q 2:ℂ)*(Real.sqrt (q 4):ℂ)*(Real.sqrt (q 5):ℂ))

lemma secondPoissonProfile_log (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    secondPoissonProfile W₁ W₂ Φ V R (fun i => Real.log (q i)) =
      secondNormProfile W₁ W₂ Φ V R q := by
  have hleft : (∑ i, secondLeftSlope i * Real.log (q i)) =
      Real.log (q 0)+Real.log (q 2)+Real.log (q 4) := by
    simp [Fin.sum_univ_succ,secondLeftSlope]; ring
  have hright : (∑ i, secondRightSlope i * Real.log (q i)) =
      Real.log (q 0)+Real.log (q 2)+Real.log (q 5) := by
    simp [Fin.sum_univ_succ,secondRightSlope]; ring
  have hker : (∑ i, secondKernelSlope i * Real.log (q i)) =
      Real.log (q 3) - (Real.log (q 1)+Real.log (q 2)+Real.log (q 2)+Real.log (q 4)+Real.log (q 5)) := by
    simp [Fin.sum_univ_succ,secondKernelSlope]; ring
  unfold secondPoissonProfile secondNormProfile
  rw [hleft,hright,hker]
  simp only [Real.exp_add,Real.exp_sub,Real.exp_log (hq _)]
  have hk : R * (q 3/(q 1*q 2*q 2*q 4*q 5)) = R*q 3/(q 1*(q 2)^2*q 4*q 5) := by ring
  rw [hk]
  simp only [Fin.prod_univ_succ,secondRootWindows,inverseNormWindow,inverseRootWindow,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.isValue,Real.exp_log (hq _),Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,  Fin.val_mk]
  norm_num
  ring

theorem secondSourcePairKernel_profile {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
    (G V N M : Finset ι) (hVN : Disjoint V N) (hVM : Disjoint V M)
    (e k : Eis) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    (‖eisEmbedding e‖^2 : ℂ)⁻¹ * secondSourcePairKernel p e k
      (fun U => W₁ (primeProductNorm p G * primeProductNorm p U))
      (fun U => W₂ (primeProductNorm p G * primeProductNorm p U)) Φ Y (V ∪ N) (V ∪ M) =
    secondNormProfile (fun x => star (W₁ x)) W₂ Φ (fun _ _ => 1) Y
      ![primeProductNorm p G, ‖eisEmbedding e‖^2, primeProductNorm p V,
        ‖eisEmbedding k‖^2, primeProductNorm p N, primeProductNorm p M] := by
  have hs (S : Finset ι) : ‖eisEmbedding (∏ i ∈ S, p i)‖ = Real.sqrt (primeProductNorm p S) := by
    simp only [primeProductNorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hV : 0 ≤ primeProductNorm p V := (primeProductNorm_pos p hp V).le
  have hroots : Real.sqrt (primeProductNorm p V*primeProductNorm p N) *
      Real.sqrt (primeProductNorm p V*primeProductNorm p M) =
      primeProductNorm p V * Real.sqrt (primeProductNorm p N) * Real.sqrt (primeProductNorm p M) := by
    rw [Real.sqrt_mul hV, Real.sqrt_mul hV]
    calc
      _ = (Real.sqrt (primeProductNorm p V))^2 * Real.sqrt (primeProductNorm p N) * Real.sqrt (primeProductNorm p M) := by ring
      _ = _ := by rw [Real.sq_sqrt hV]
  unfold secondSourcePairKernel secondNormProfile
  simp only [hs,primeProductNorm_union p V N hVN,primeProductNorm_union p V M hVM,
    Matrix.cons_val_zero,  Fin.isValue, Finset.prod_const_one, one_mul]
  have harg : Y * ‖eisEmbedding k‖^2 /
      (‖eisEmbedding e‖^2 * (primeProductNorm p V*primeProductNorm p N *
        (primeProductNorm p V*primeProductNorm p M))) =
      Y * ‖eisEmbedding k‖^2 / (‖eisEmbedding e‖^2 * (primeProductNorm p V)^2 *
        primeProductNorm p N * primeProductNorm p M) := by ring
  rw [harg]
  rw [← Complex.ofReal_mul, hroots]
  push_cast
  ring_nf

theorem secondNormProfile_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (G₀ E₀ V₀ K₀ X₀ Y : ℝ)
    (_hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        secondNormProfile W₁ W₂ Φ (fun _ _ => 1)
          (Y*K₀/(E₀*V₀^2*X₀^2))
          ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] := by
  have hleft : (q 0/G₀)*(q 2/V₀)*(q 4/X₀) = q 0*q 2*q 4/(G₀*V₀*X₀) := by ring
  have hright : (q 0/G₀)*(q 2/V₀)*(q 5/X₀) = q 0*q 2*q 5/(G₀*V₀*X₀) := by ring
  have harg : (Y*K₀/(E₀*V₀^2*X₀^2))*(q 3/K₀)/
      ((q 1/E₀)*(q 2/V₀)^2*(q 4/X₀)*(q 5/X₀)) =
      Y*q 3/(q 1*(q 2)^2*q 4*q 5) := by
    field_simp
  have hroot : Real.sqrt (q 4/X₀)*Real.sqrt (q 5/X₀) =
      Real.sqrt (q 4)*Real.sqrt (q 5)/X₀ := by
    rw [Real.sqrt_div (hq 4).le,Real.sqrt_div (hq 5).le]
    rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hX.le]
  have hc0 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (0:Fin 6) = q 0/G₀ := rfl
  have hc1 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (1:Fin 6) = q 1/E₀ := rfl
  have hc2 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (2:Fin 6) = q 2/V₀ := rfl
  have hc3 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (3:Fin 6) = q 3/K₀ := rfl
  have hc4 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (4:Fin 6) = q 4/X₀ := rfl
  have hc5 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (5:Fin 6) = q 5/X₀ := rfl
  unfold secondNormProfile
  simp only [Finset.prod_const_one,one_mul,hc0,hc1,hc2,hc3,hc4,hc5]
  rw [hleft,hright,harg]
  have hrootC : (Real.sqrt (q 4/X₀):ℂ)*(Real.sqrt (q 5/X₀):ℂ) =
      (Real.sqrt (q 4):ℂ)*(Real.sqrt (q 5):ℂ)/(X₀:ℂ) := by exact_mod_cast hroot
  rw [show (↑(q 1/E₀):ℂ)*↑(q 2/V₀)*↑(Real.sqrt (q 4/X₀))*↑(Real.sqrt (q 5/X₀)) =
      (↑(q 1/E₀):ℂ)*↑(q 2/V₀)*(↑(Real.sqrt (q 4/X₀))*↑(Real.sqrt (q 5/X₀))) from by ring,
    hrootC]
  have hEc : (E₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hE.ne'
  have hVc : (V₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV.ne'
  have hXc : (X₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  push_cast
  field_simp [hEc,hVc,hXc]

end
end SevenEighths.InverseMoment

end OAI

end Source2328

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondKernelMeasure.lean; sha256: a3d61f0ab7bf02f4f2547042535d1b22ca5f316915e962867ffa9fde7fa1cb17 -/
section Source2329
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

def secondRelativeNorm (q : Fin 6 → ℝ) (G E V K X : ℝ) : Fin 6 → ℝ :=
  ![q 0/G,q 1/E,q 2/V,q 3/K,q 4/X,q 5/X]

def secondRelativeLog (q : Fin 6 → ℝ) (G E V K X : ℝ) (i : Fin 6) : ℝ :=
  Real.log (secondRelativeNorm q G E V K X i)

lemma secondRelativeNorm_pos (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (G E V K X : ℝ) (hG : 0 < G) (hE : 0 < E) (hV : 0 < V) (hK : 0 < K) (hX : 0 < X) :
    ∀ i, 0 < secondRelativeNorm q G E V K X i := by
  intro i
  fin_cases i
  · exact div_pos (hq 0) hG
  · exact div_pos (hq 1) hE
  · exact div_pos (hq 2) hV
  · exact div_pos (hq 3) hK
  · exact div_pos (hq 4) hX
  · exact div_pos (hq 5) hX

lemma secondNormProfile_eq_full_of_windows (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hV : ∀ i, V i (Real.log (q i)) = 1) :
    secondNormProfile W₁ W₂ Φ (fun _ _ => 1) R q =
      secondPoissonProfile W₁ W₂ Φ V R (fun i => Real.log (q i)) := by
  rw [secondPoissonProfile_log W₁ W₂ Φ V R q hq]
  simp only [secondNormProfile, hV, Finset.prod_const_one]

theorem second_norm_kernel_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ G₀ E₀ V₀ K₀ X₀ Y : ℝ,
      0 < G₀ → 0 < E₀ → 0 < V₀ → 0 < K₀ → 0 < X₀ → 0 < Y →
      ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ (q : Fin 6 → ℝ), (∀ i, 0 < q i) →
        (∀ i, V i (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i) = 1) →
        secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
          (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
          ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
            ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
              fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
                (∏ i, logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope
                  (t₁,t₂,t₃) u i) (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i))) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + Y*K₀/(E₀*V₀^2*X₀^2))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hsep⟩ := second_full_profile_common_measure
    W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  obtain ⟨b₃,he,hi,hbound⟩ := hsep (Y*K₀/(E₀*V₀^2*X₀^2)) (by positivity)
  refine ⟨b₃,?_,hi,hbound⟩
  intro q hq hcut
  rw [secondNormProfile_nominal W₁ W₂ Φ G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX q hq]
  change ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * secondNormProfile W₁ W₂ Φ (fun _ _ => 1)
      (Y*K₀/(E₀*V₀^2*X₀^2)) (secondRelativeNorm q G₀ E₀ V₀ K₀ X₀) = _
  rw [secondNormProfile_eq_full_of_windows W₁ W₂ Φ V _ _
    (secondRelativeNorm_pos q hq G₀ E₀ V₀ K₀ X₀ hG hE hV₀ hK hX) hcut, he]
  rfl

end
end SevenEighths.InverseMoment

end OAI

end Source2329

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondFreshMeasure.lean; sha256: 792bf00639acc85dbbc41c5f1f32970785459bcb8ecba3fb0c16cd6843def8f0 -/
section Source2330
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

theorem second_fresh_kernel_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ G₀ E₀ V₀ K₀ X₀ Y : ℝ,
      0 < G₀ → 0 < E₀ → 0 < V₀ → 0 < K₀ → 0 < X₀ → 0 < Y →
      ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ (ω₁ ω₂ : ℝ → ℂ) (q : Fin 6 → ℝ), (∀ i, 0 < q i) →
        (W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) ≠ 0 → ω₁ (q 4/X₀) = 1) →
        (W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) ≠ 0 → ω₂ (q 5/X₀) = 1) →
        (ω₁ (q 4/X₀) ≠ 0 → ω₂ (q 5/X₀) ≠ 0 →
          ∀ i, V i (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i) = 1) →
        secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
          (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
          ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * (ω₁ (q 4/X₀)*ω₂ (q 5/X₀)) *
            ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
              fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
                (∏ i, logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope
                  (t₁,t₂,t₃) u i) (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i))) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + Y*K₀/(E₀*V₀^2*X₀^2))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hsep⟩ := second_norm_kernel_common_measure
    W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  obtain ⟨b₃,he,hi,hbound⟩ := hsep G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  refine ⟨b₃,?_,hi,hbound⟩
  intro ω₁ ω₂ q hq hω₁ hω₂ hcut
  by_cases hw₁ : ω₁ (q 4/X₀) = 0
  · have hW : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      have hh := hω₁ hn
      rw [hw₁] at hh
      exact zero_ne_one hh
    simp only [secondNormProfile,hW,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : ω₂ (q 5/X₀) = 0
  · have hW : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      have hh := hω₂ hn
      rw [hw₂] at hh
      exact zero_ne_one hh
    simp only [secondNormProfile,hW,hw₂,mul_zero,zero_mul,zero_div]
  have hm : secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
    (ω₁ (q 4/X₀)*ω₂ (q 5/X₀)) *
      secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
        (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q := by
    by_cases h1 : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [hω₁ h1,hω₂ h2,one_mul]
  rw [hm,he q hq (hcut hw₁ hw₂)]
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2330

/- Original source: OAI/NumberTheory/DirichletL/Descent/ProfileIntegral.lean; sha256: f6e1b2cea8d2a3d33353bf559704acd23ee02873dbb34f3a56f91e7b94e3e745 -/
section Source2331
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma full_density_integrable (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) :
    Integrable (fullProfileDensity g b₁ b₂ b₃) := by
  have hc : Continuous (fullProfileDensity g b₁ b₂ b₃) := by
    unfold fullProfileDensity coordinateDensity tripleCoefficient
    fun_prop
  apply (integrable_norm_iff hc.aestronglyMeasurable).mp
  simpa only [tripleHeight,coordinateHeight,pow_zero,Finset.prod_const_one,mul_one,one_mul] using
    fullProfileDensity_weighted_integrable g b₁ b₂ b₃ 0

lemma full_density_mode_integrable (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (a₁ a₂ ak y : ι → ℝ) :
    Integrable (fun p : Frequency × (ι → ℝ) => fullProfileDensity g b₁ b₂ b₃ p *
      pureProfileMode a₁ a₂ ak y p.1 p.2) := by
  have hc : Continuous (fun p : Frequency × (ι → ℝ) => pureProfileMode a₁ a₂ ak y p.1 p.2) := by
    unfold pureProfileMode logPhase
    fun_prop
  exact (full_density_integrable g b₁ b₂ b₃).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => (pureProfileMode_norm a₁ a₂ ak y p.1 p.2).le))

theorem full_density_mode_fubini (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (a₁ a₂ ak y : ι → ℝ) :
    (∫ p : Frequency × (ι → ℝ), fullProfileDensity g b₁ b₂ b₃ p *
      pureProfileMode a₁ a₂ ak y p.1 p.2) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : ι → ℝ,
      fullProfileDensity g b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
        pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u := by
  let f : Frequency × (ι → ℝ) → ℂ := fun p => fullProfileDensity g b₁ b₂ b₃ p *
    pureProfileMode a₁ a₂ ak y p.1 p.2
  have hf : Integrable f (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using full_density_mode_integrable g b₁ b₂ b₃ a₁ a₂ ak y
  change (∫ p, f p) = _
  rw [Measure.volume_eq_prod, integral_prod _ hf]
  have ht : Integrable (fun t : Frequency => ∫ u, f (t,u)) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hf.integral_prod_left
  rw [Measure.volume_eq_prod, integral_prod _ ht]
  apply integral_congr_ae
  filter_upwards [ht.prod_right_ae] with t₁ ht₁
  simpa only [Measure.volume_eq_prod] using integral_prod (fun t : ℝ×ℝ => ∫ u, f ((t₁,t.1,t.2),u)) ht₁

theorem full_density_finite_sum {κ : Type*} (s : Finset κ)
    (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) (a₁ a₂ ak : ι → ℝ)
    (c : κ → ℂ) (y : κ → ι → ℝ) :
    (∑ k ∈ s, c k * ∫ p : Frequency × (ι → ℝ), fullProfileDensity g b₁ b₂ b₃ p *
      pureProfileMode a₁ a₂ ak (y k) p.1 p.2) =
    ∫ p : Frequency × (ι → ℝ), fullProfileDensity g b₁ b₂ b₃ p *
      ∑ k ∈ s, c k * pureProfileMode a₁ a₂ ak (y k) p.1 p.2 := by
  simp only [← integral_const_mul]
  rw [← integral_finsetSum s (fun k hk =>
    (full_density_mode_integrable g b₁ b₂ b₃ a₁ a₂ ak (y k)).const_mul (c k))]
  apply integral_congr_ae
  filter_upwards with p
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2331

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialProfile.lean; sha256: 446ac4ecee7755bceae9cc60b5ea239a8ca521b2db50256d80c5c5b71f994945 -/
section Source2332
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment

namespace SevenEighths.InverseInitialProfile

def clippedTwist (g : 𝓢(ℝ, ℂ)) (c θ : ℝ) : 𝓢(ℝ, ℂ) :=
  frequencyTwist (SchwartzMap.compSubConstCLM ℂ (-Real.log c) g) θ

@[simp] theorem clippedTwist_apply (g : 𝓢(ℝ, ℂ)) (c θ y : ℝ) :
    clippedTwist g c θ y = logPhase θ y * g (y + Real.log c) := by
  simp [clippedTwist]

def sourceDensity (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) : ℂ :=
  logPhase (t-θ) (Real.log c) * (𝓕 g) (t-θ)

theorem fourier_clippedTwist (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) :
    (𝓕 (clippedTwist g c θ)) t = sourceDensity g c θ t := by
  rw [SchwartzMap.fourier_coe]
  have he : (clippedTwist g c θ : ℝ → ℂ) =
      fun y => logPhase θ y * g (y + Real.log c) := by ext y; simp
  rw [he, InverseClippingProfiles.fourier_translated_twist]
  rfl

theorem sourceDensity_joint_measurable (g : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ℝ => sourceDensity g p.1.1 p.1.2 p.2) := by
  unfold sourceDensity logPhase
  apply Measurable.stronglyMeasurable
  apply Measurable.mul
  · exact Complex.continuous_exp.measurable.comp (by fun_prop)
  · exact (𝓕 g : 𝓢(ℝ, ℂ)).continuous.measurable.comp (by fun_prop)

theorem sourceDensity_norm (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) :
    ‖sourceDensity g c θ t‖ = ‖(𝓕 g) (t-θ)‖ := by
  simp [sourceDensity, logPhase_norm]

theorem sourceDensity_moment_uniform (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c θ : ℝ,
      Integrable (fun t : ℝ => (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
        C*(1+‖θ‖)^(InverseClippingProfiles.momentOrder J) := by
  obtain ⟨C, hC, hb⟩ := InverseClippingProfiles.translated_twist_moment_uniform g J
  refine ⟨C, hC, ?_⟩
  intro c θ
  simpa only [InverseClippingProfiles.fourier_translated_twist, sourceDensity,
    SchwartzMap.fourier_coe] using hb (Real.log c) θ

def clippedSource (W : ℝ → ℂ) (c θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x) * W (c*x)

theorem clipped_log_source (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c : ℝ} (hc : 0 < c) (θ y : ℝ) :
    clippedTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) c θ y =
      clippedSource W c θ (Real.exp y) := by
  simp only [clippedTwist_apply, CubicReflectionKernel.logSchwartz_apply,
    clippedSource, Real.log_exp, Real.exp_add, Real.exp_log hc]
  rw [mul_comm (Real.exp y) c]

def rootExponent (y : Fin 6 → ℝ) : ℝ := -y 1-y 2-(y 4+y 5)/2

theorem root_coupled_identity (y : Fin 6 → ℝ) :
    rootExponent y = -y 1+y 0-((y 0+y 2+y 4)+(y 0+y 2+y 5))/2 := by
  unfold rootExponent
  ring

theorem root_budget (y : Fin 6 → ℝ) (L : ℝ)
    (hd : |y 1| ≤ L) (hC : |y 0| ≤ L)
    (hc₁ : |y 0+y 2+y 4| ≤ L) (hc₂ : |y 0+y 2+y 5| ≤ L) :
    rootExponent y ≤ 3*L := by
  rw [root_coupled_identity]
  have hd' := (abs_le.mp hd).1
  have hC' := (abs_le.mp hC).2
  have h1 := (abs_le.mp hc₁).1
  have h2 := (abs_le.mp hc₂).1
  linarith

def normalizedProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (Real.exp (-3*L) : ℂ) * secondPoissonProfile W₁ W₂ Φ V R y

theorem normalizedProfile_exact (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) :
    normalizedProfile W₁ W₂ Φ V R L y =
      (Real.exp (rootExponent y-3*L) : ℂ) * (∏ i, V i (y i)) *
      W₁ (Real.exp (y 0+y 2+y 4)) * W₂ (Real.exp (y 0+y 2+y 5)) *
      paperRadialFourier Φ (R*Real.exp (y 3-y 1-2*y 2-y 4-y 5)) := by
  unfold normalizedProfile secondPoissonProfile
  rw [InverseClippingProfiles.secondRootWindows_prod]
  have hleft : (∑ i, secondLeftSlope i*y i) = y 0+y 2+y 4 := by
    simp [secondLeftSlope, Fin.sum_univ_succ]
    ring
  have hright : (∑ i, secondRightSlope i*y i) = y 0+y 2+y 5 := by
    simp [secondRightSlope, Fin.sum_univ_succ]
    ring
  have hker : (∑ i, secondKernelSlope i*y i) = y 3-y 1-2*y 2-y 4-y 5 := by
    simp [secondKernelSlope, Fin.sum_univ_succ]
    ring
  rw [hleft, hright, hker]
  change (Real.exp (-3*L) : ℂ) * (((Real.exp (rootExponent y) : ℂ)*_)*_*_*_) = _
  rw [show Real.exp (rootExponent y-3*L) = Real.exp (-3*L)*Real.exp (rootExponent y) by
    rw [← Real.exp_add]; congr 1; ring, Complex.ofReal_mul]
  ring

def familyDensity (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Frequency × (Fin 6 → ℝ)) : ℂ :=
  (Real.exp (-3*L) : ℂ) * fullProfileDensity g
    (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

theorem familyDensity_formula (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Frequency × (Fin 6 → ℝ)) :
    familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p =
      (Real.exp (-3*L) : ℂ) *
        (sourceDensity g₁ c₁ θ₁ p.1.1 *
          (sourceDensity g₂ c₂ θ₂ p.1.2.1 * b₃ p.1.2.2)) * coordinateDensity g p.2 := by
  simp only [familyDensity, fullProfileDensity, tripleCoefficient, fourier_clippedTwist]
  ring

theorem familyDensity_weighted_integrable
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) := by
  convert (InverseMoment.fullProfileDensity_weighted_integrable g
    (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ J).const_mul
      (Real.exp (-3*L)) using 1
  funext p
  simp only [familyDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  ring

theorem familyDensity_weighted_integral
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Frequency × (Fin 6 → ℝ),
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) =
    Real.exp (-3*L) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
      ∏ i, ∫ u : ℝ, (1+‖u‖)^J * ‖(𝓕 (g i)) u‖ := by
  have he (p : Frequency × (Fin 6 → ℝ)) :
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖ =
      Real.exp (-3*L) * (tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖fullProfileDensity g (𝓕 (clippedTwist g₁ c₁ θ₁))
          (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p‖) := by
    simp only [familyDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    ring
  simp_rw [he]
  rw [integral_const_mul, InverseMoment.fullProfileDensity_weighted_integral]
  simp only [tripleHeight]
  rw [tripleCoefficient_weighted_integral]
  simp only [fourier_clippedTwist]
  ring

def logFamilyProfile (g₁ g₂ : 𝓢(ℝ, ℂ)) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (Real.exp (-3*L) : ℂ) *
    ((∏ i, secondRootWindows V i (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, secondLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, secondRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)))

theorem family_common_measure
    (g₁ g₂ Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ c₁ c₂ θ₁ θ₂ L : ℝ, 0 ≤ L →
      (∀ y : Fin 6 → ℝ,
        logFamilyProfile g₁ g₂ Φ V c₁ c₂ θ₁ θ₂ R L y =
          ∫ p : Frequency × (Fin 6 → ℝ),
            familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p *
              pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C * ((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  have hb : ∀ i y, secondRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  obtain ⟨C₃, hC₃, hsep⟩ := paperRadialFourier_log_separation_envelope
    Φ (secondRootWindows V) secondKernelSlope M hM hb A J
  obtain ⟨C₁, hC₁, h₁⟩ := sourceDensity_moment_uniform g₁ J
  obtain ⟨C₂, hC₂, h₂⟩ := sourceDensity_moment_uniform g₂ J
  let D : ℝ := ∏ i, ∫ u : ℝ, (1+‖u‖)^J *
    ‖(𝓕 (secondRootSchwartz V hV hS i)) u‖
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i _ => integral_nonneg (fun u => by positivity))
  refine ⟨C₁*C₂*C₃*D, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, he, _, hm, _⟩ := hsep R hR
  refine ⟨b₃, ?_⟩
  intro c₁ c₂ θ₁ θ₂ L hL
  refine ⟨?_, familyDensity_weighted_integrable _ _ _ _ _ _ _ _ _ _, ?_⟩
  · intro y
    have hid := descent_profile_identity (clippedTwist g₁ c₁ θ₁) (clippedTwist g₂ c₂ θ₂)
      Φ (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope R b₃ he y
    have habs := profile_integral_coordinate_absorption (secondRootSchwartz V hV hS)
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃
      secondLeftSlope secondRightSlope secondKernelSlope y
    have hid' : logFamilyProfile g₁ g₂ Φ V c₁ c₂ θ₁ θ₂ R L y =
        (Real.exp (-3*L) : ℂ) *
          ∫ p : Frequency × (Fin 6 → ℝ),
            fullProfileDensity (secondRootSchwartz V hV hS)
              (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p *
              pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2 := by
      unfold logFamilyProfile
      rw [hid]
      congr 1
      rw [full_density_mode_fubini]
      simpa only [profileMode, secondRootSchwartz, rootSchwartz_apply] using habs
    rw [hid', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    unfold familyDensity
    ring
  · rw [familyDensity_weighted_integral]
    have h1 := (h₁ c₁ θ₁).2
    have h2 := (h₂ c₂ θ₂).2
    have h12 := mul_le_mul h1 h2 (integral_nonneg (fun _ => by positivity))
      (mul_nonneg hC₁ (by positivity))
    have hm0 : 0 ≤ (1+R)^A * ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖ := by positivity
    have h123 := mul_le_mul h12 hm hm0 (by positivity)
    have h123D := mul_le_mul_of_nonneg_right h123 hD
    have hnorm : Real.exp (-3*L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have heq : (1+R)^A * (Real.exp (-3*L) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) * D) =
      Real.exp (-3*L) * (((∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖)) *
        ((1+R)^A * ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) * D) := by ring
    change (1+R)^A * (_ * _ * _ * _ * D) ≤ _
    rw [heq]
    exact (mul_le_mul_of_nonneg_left h123D (Real.exp_pos _).le).trans
      ((mul_le_of_le_one_left (by positivity) hnorm).trans_eq (by ring))

theorem sourceDensity_moment_seminorm (g : 𝓢(ℝ, ℂ)) (M b : ℝ)
    (hM : 0 ≤ M) (hb : 1 ≤ b) (hg : Function.support g ⊆ Set.Icc (-M) M)
    (J : ℕ) {c : ℝ} (hc : 1 ≤ c) (hcb : c ≤ b) (θ : ℝ) :
    (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
      InverseClippingProfiles.windowMomentConstant g M (Real.log b) 0 J *
        (1+‖θ‖)^(InverseClippingProfiles.momentOrder J) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hlog : |Real.log c| ≤ Real.log b * 1 := by
    rw [mul_one, abs_of_nonneg (Real.log_nonneg hc)]
    exact Real.log_le_log hc0 hcb
  have he : clippedTwist g c θ = frequencyTwist
      (InverseClippingProfiles.rootSchwartz g M (Real.log b) 1 (Real.log c) 0 0
        zero_lt_one hlog hg) θ := by
    ext y
    simp [InverseClippingProfiles.rootSchwartz_apply,
      InverseClippingProfiles.rootedWindow, InverseClippingProfiles.logWindow]
  have hm := InverseClippingProfiles.rooted_twist_fourier_moment g M (Real.log b)
    1 (Real.log c) 0 0 θ hM (Real.log_nonneg hb) le_rfl hlog hg (by simp) J
  simp_rw [← fourier_clippedTwist, he]
  simpa only [InverseClippingProfiles.windowMomentConstant, one_pow, mul_one] using hm

theorem clippedSource_conjugate (W : ℝ → ℂ) (c θ x : ℝ) :
    star (clippedSource W c θ x) = clippedSource (fun x => star (W x)) c (-θ) x := by
  simp only [clippedSource, star_mul, SecondPassIntegration.logPhase_conjugate]
  ring

theorem familyDensity_joint_measurable
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) (L : ℝ) :
    StronglyMeasurable (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × (Frequency × (Fin 6 → ℝ)) =>
      familyDensity g g₁ g₂ b₃ z.1.1.1 z.1.2.1 z.1.1.2 z.1.2.2 L z.2) := by
  simp_rw [familyDensity_formula]
  apply Measurable.stronglyMeasurable
  unfold sourceDensity coordinateDensity logPhase
  have h1 : Measurable ((𝓕 g₁ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := (𝓕 g₁ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h2 : Measurable ((𝓕 g₂ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := (𝓕 g₂ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h3 : Measurable (b₃ : ℝ → ℂ) := b₃.continuous.measurable
  have hu (i : Fin 6) : Measurable ((𝓕 (g i) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
    (𝓕 (g i) : 𝓢(ℝ, ℂ)).continuous.measurable
  have hexp : Measurable Complex.exp := Complex.continuous_exp.measurable
  fun_prop

theorem fresh_cutoff_one (W w : ℝ → ℂ) (a b bclip A₀ B₀ A₂ B₂ : ℝ)
    (_ha : 0 < a) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂) (hclip : 1 ≤ bclip)
    (hW : Function.support W ⊆ Set.Icc a b)
    (hω : ∀ x ∈ Set.Icc (a/(bclip*B₀*B₂)) (b/(A₀*A₂)), w x = 1)
    {c u v x : ℝ} (hc : 1 ≤ c) (hcb : c ≤ bclip)
    (hu : u ∈ Set.Icc A₀ B₀) (hv : v ∈ Set.Icc A₂ B₂) (hx : 0 < x)
    (hs : W (c*(u*v*x)) ≠ 0) : w x = 1 := by
  have hu0 : 0 < u := hA₀.trans_le hu.1
  have hv0 : 0 < v := hA₂.trans_le hv.1
  have hB₀ : 0 < B₀ := hu0.trans_le hu.2
  have hB₂ : 0 < B₂ := hv0.trans_le hv.2
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hs' := hW hs
  have hlo : A₀*A₂ ≤ c*(u*v) := by
    have hprod := mul_le_mul hu.1 hv.1 hA₂.le hu0.le
    exact hprod.trans (le_mul_of_one_le_left (mul_nonneg hu0.le hv0.le) hc)
  have hhi : c*(u*v) ≤ bclip*B₀*B₂ := by
    have hprod := mul_le_mul hu.2 hv.2 hv0.le hB₀.le
    exact (mul_le_mul hcb hprod (mul_nonneg hu0.le hv0.le)
      (zero_lt_one.trans_le hclip).le).trans_eq (by ring)
  apply hω x
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < bclip*B₀*B₂)).mpr
    have hh := mul_le_mul_of_nonneg_right hhi hx.le
    nlinarith [hs'.1]
  · apply (le_div_iff₀ (mul_pos hA₀ hA₂)).mpr
    have hh := mul_le_mul_of_nonneg_right hlo hx.le
    nlinarith [hs'.2]

def columnCenter (D B v : ℝ) : ℝ := D-B-v
def prefactorCenter (m D B θ : ℝ) : ℝ := m-2*D+B-θ
def radialCenter (m H θ D B : ℝ) : ℝ := m+H-θ-2*(D-B)

theorem original_column_scale {Z : ℝ} (hZ : 0 < Z) (D B v : ℝ) :
    Z^B * Z^v * Z^(columnCenter D B v) = Z^D := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  unfold columnCenter
  ring

theorem initial_prefactor_scale {Z : ℝ} (hZ : 0 < Z) (D B v m θ : ℝ) :
    Z^(-D) * Z^m / (Z^θ * Z^v * Z^(columnCenter D B v)) =
      Z^(prefactorCenter m D B θ) := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_sub hZ]
  congr 1
  unfold columnCenter prefactorCenter
  ring

theorem initial_radial_scale {Z : ℝ} (hZ : 0 < Z) (D B v m θ H : ℝ) :
    Z^m * Z^H / (Z^θ * (Z^v)^2 * (Z^(columnCenter D B v))^2) =
      Z^(radialCenter m H θ D B) := by
  simp only [pow_two]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_sub hZ]
  congr 1
  unfold columnCenter radialCenter
  ring

theorem initial_normalization_scalar {Z : ℝ} (hZ : 0 < Z) (κ η : ℝ) :
    Z^(κ+3*η) * Real.exp (-3*(η*Real.log Z)) = Z^κ := by
  have he : Real.exp (-3*(η*Real.log Z)) = Z^(-3*η) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  rw [he, ← Real.rpow_add hZ]
  congr 1
  ring

def physicalKernel (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (Z D m : ℝ) (q : Fin 6 → ℝ) : ℂ :=
  ((Z^(-D)*Z^m/(q 1*q 2*Real.sqrt (q 4*q 5)) : ℝ) : ℂ) *
    W₁ (q 0*q 2*q 4/Z^D) * W₂ (q 0*q 2*q 5/Z^D) *
      paperRadialFourier Φ (Z^m*q 3/(q 1*(q 2)^2*q 4*q 5))

theorem physicalKernel_eq_secondNorm (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (Z D m : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    physicalKernel W₁ W₂ Φ Z D m q =
      ((Z^(-D)*Z^m : ℝ) : ℂ) *
        secondNormProfile (fun x => W₁ (x/Z^D)) (fun x => W₂ (x/Z^D))
          Φ (fun _ _ => 1) (Z^m) q := by
  unfold physicalKernel secondNormProfile
  rw [Real.sqrt_mul (hq 4).le]
  simp only [Finset.prod_const_one, one_mul, Complex.ofReal_div, Complex.ofReal_mul]
  ring

theorem physicalKernel_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    {Z : ℝ} (hZ : 0 < Z) (D B v m θ H : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(prefactorCenter m D B θ) : ℝ) *
        secondNormProfile W₁ W₂ Φ (fun _ _ => 1) (Z^(radialCenter m H θ D B))
          (secondRelativeNorm q (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v))) := by
  have hn := secondNormProfile_nominal W₁ W₂ Φ
    (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v)) (Z^m)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) q hq
  rw [original_column_scale hZ D B v, initial_radial_scale hZ D B v m θ H] at hn
  rw [physicalKernel_eq_secondNorm W₁ W₂ Φ Z D m q hq, hn]
  change ((Z^(-D)*Z^m : ℝ) : ℂ) *
      (((Z^θ*Z^v*Z^(columnCenter D B v) : ℝ) : ℂ)⁻¹ * _) = _
  rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    ← div_eq_mul_inv, initial_prefactor_scale hZ D B v m θ]
  rfl

theorem normalizedProfile_eq_family (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (θ₁ θ₂ R L : ℝ)
    (y : Fin 6 → ℝ) :
    normalizedProfile (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ V R L y =
      logFamilyProfile (CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁)
        (CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂)
        Φ V c₁ c₂ θ₁ θ₂ R L y := by
  unfold normalizedProfile logFamilyProfile secondPoissonProfile
  rw [clipped_log_source W₁ a b ha hs₁ hW₁ hc₁,
    clipped_log_source W₂ a b ha hs₂ hW₂ hc₂]

theorem fresh_profile_restore (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (x : Fin 6 → ℝ) (hx : ∀ i, 0 < x i)
    (hw₁ : W₁ (x 0*x 2*x 4) ≠ 0 → w₁ (x 4) = 1)
    (hw₂ : W₂ (x 0*x 2*x 5) ≠ 0 → w₂ (x 5) = 1)
    (hV : w₁ (x 4) ≠ 0 → w₂ (x 5) ≠ 0 → ∀ i, V i (Real.log (x i)) = 1) :
    (Real.exp (-3*L) : ℂ) * secondNormProfile W₁ W₂ Φ (fun _ _ => 1) R x =
      (w₁ (x 4)*w₂ (x 5)) * normalizedProfile W₁ W₂ Φ V R L (fun i => Real.log (x i)) := by
  unfold normalizedProfile
  rw [secondPoissonProfile_log W₁ W₂ Φ V R x hx]
  by_cases h1 : W₁ (x 0*x 2*x 4) = 0
  · simp only [secondNormProfile, h1, mul_zero, zero_mul, zero_div]
  by_cases h2 : W₂ (x 0*x 2*x 5) = 0
  · simp only [secondNormProfile, h2, mul_zero, zero_mul, zero_div]
  have hv := hV (by rw [hw₁ h1]; exact one_ne_zero) (by rw [hw₂ h2]; exact one_ne_zero)
  simp only [secondNormProfile, hv, hw₁ h1, hw₂ h2, Finset.prod_const_one, one_mul]

def relativeNorm (q : Fin 6 → ℝ) (Z D B v θ H : ℝ) : Fin 6 → ℝ :=
  secondRelativeNorm q (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v))

def relativeLog (q : Fin 6 → ℝ) (Z D B v θ H : ℝ) (i : Fin 6) : ℝ :=
  Real.log (relativeNorm q Z D B v θ H i)

theorem relativeNorm_pos (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    {Z : ℝ} (hZ : 0 < Z) (D B v θ H : ℝ) :
    ∀ i, 0 < relativeNorm q Z D B v θ H i :=
  secondRelativeNorm_pos q hq _ _ _ _ _
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _)

theorem initial_kernel_restore (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (D B v m θ H η : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hw₁ : W₁ (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
      relativeNorm q Z D B v θ H 4) ≠ 0 → w₁ (relativeNorm q Z D B v θ H 4) = 1)
    (hw₂ : W₂ (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
      relativeNorm q Z D B v θ H 5) ≠ 0 → w₂ (relativeNorm q Z D B v θ H 5) = 1)
    (hV : w₁ (relativeNorm q Z D B v θ H 4) ≠ 0 →
      w₂ (relativeNorm q Z D B v θ H 5) ≠ 0 → ∀ i, V i (relativeLog q Z D B v θ H i) = 1) :
    physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(prefactorCenter m D B θ + 3*η) : ℝ) *
        (w₁ (relativeNorm q Z D B v θ H 4)*w₂ (relativeNorm q Z D B v θ H 5)) *
        normalizedProfile W₁ W₂ Φ V (Z^(radialCenter m H θ D B))
          (η*Real.log Z) (relativeLog q Z D B v θ H) := by
  rw [physicalKernel_nominal W₁ W₂ Φ hZ D B v m θ H q hq]
  have hs := fresh_profile_restore W₁ W₂ w₁ w₂ Φ V (Z^(radialCenter m H θ D B))
    (η*Real.log Z) (relativeNorm q Z D B v θ H)
    (relativeNorm_pos q hq hZ D B v θ H) hw₁ hw₂ hV
  have hn : ((Z^(prefactorCenter m D B θ) : ℝ) : ℂ) =
      (Z^(prefactorCenter m D B θ+3*η) : ℝ) * (Real.exp (-3*(η*Real.log Z)) : ℂ) := by
    rw [← Complex.ofReal_mul, initial_normalization_scalar hZ]
  rw [show relativeLog q Z D B v θ H =
    (fun i => Real.log (relativeNorm q Z D B v θ H i)) by rfl]
  rw [hn, mul_assoc]
  simpa only [mul_assoc, relativeNorm] using congrArg
    (fun z : ℂ => (Z^(prefactorCenter m D B θ+3*η) : ℝ) * z) hs

def PhysicalIdentityAt (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ) : Prop :=
  ∀ (w₁ w₂ : ℝ → ℂ) (q : Fin 6 → ℝ), (∀ i, 0 < q i) →
    (clippedSource W₁ c₁ θ₁
      (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
        relativeNorm q Z D B v θ H 4) ≠ 0 → w₁ (relativeNorm q Z D B v θ H 4) = 1) →
    (clippedSource W₂ c₂ θ₂
      (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
        relativeNorm q Z D B v θ H 5) ≠ 0 → w₂ (relativeNorm q Z D B v θ H 5) = 1) →
    (w₁ (relativeNorm q Z D B v θ H 4) ≠ 0 →
      w₂ (relativeNorm q Z D B v θ H 5) ≠ 0 →
      ∀ i, V i (relativeLog q Z D B v θ H i) = 1) →
    physicalKernel (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m q =
      (Z^(prefactorCenter m D B θ + 3*η) : ℝ) *
        (w₁ (relativeNorm q Z D B v θ H 4)*w₂ (relativeNorm q Z D B v θ H 5)) *
        ∫ p : Frequency × (Fin 6 → ℝ),
          familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (relativeLog q Z D B v θ H) p.1 p.2

theorem initial_physical_family_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    let g := secondRootSchwartz V hV hS
    let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
    let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z D B v m θ H η : ℝ, 0 < Z → 0 ≤ η*Real.log Z →
      ∃ b₃ : 𝓢(ℝ, ℂ), ∀ c₁ c₂ θ₁ θ₂ : ℝ, 0 < c₁ → 0 < c₂ →
      PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂ ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p‖) ∧
      (1+Z^(radialCenter m H θ D B))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p‖) ≤
        C * ((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C, hC, hsep⟩ := family_common_measure
    (CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁)
    (CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂)
    Φ V M hV hS hM hbox A J
  refine ⟨C, hC, ?_⟩
  intro Z D B v m θ H η hZ hL
  obtain ⟨b₃, hb₃⟩ := hsep (Z^(radialCenter m H θ D B)) (Real.rpow_pos_of_pos hZ _)
  refine ⟨b₃, ?_⟩
  intro c₁ c₂ θ₁ θ₂ hc₁ hc₂
  obtain ⟨he, hi, hbound⟩ := hb₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) hL
  refine ⟨?_, hi, hbound⟩
  intro w₁ w₂ q hq hw₁ hw₂ hcut
  rw [initial_kernel_restore _ _ w₁ w₂ Φ V hZ D B v m θ H η q hq hw₁ hw₂ hcut,
    normalizedProfile_eq_family W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V hc₁ hc₂, he]

theorem fresh_cutoff_one_clippedSource (W w : ℝ → ℂ) (a b bclip A₀ B₀ A₂ B₂ : ℝ)
    (ha : 0 < a) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂) (hclip : 1 ≤ bclip)
    (hW : Function.support W ⊆ Set.Icc a b)
    (hw : ∀ x ∈ Set.Icc (a/(bclip*B₀*B₂)) (b/(A₀*A₂)), w x = 1)
    {c u v x : ℝ} (hc : 1 ≤ c) (hcb : c ≤ bclip)
    (hu : u ∈ Set.Icc A₀ B₀) (hv : v ∈ Set.Icc A₂ B₂) (hx : 0 < x)
    (θ : ℝ) (hs : clippedSource W c θ (u*v*x) ≠ 0) : w x = 1 := by
  exact fresh_cutoff_one W w a b bclip A₀ B₀ A₂ B₂ ha hA₀ hA₂ hclip hW hw
    hc hcb hu hv hx (mul_ne_zero_iff.mp hs).2

theorem clipped_column_ratio {Z : ℝ} (hZ : 0 < Z) (N q : ℝ) :
    q / Z^N = Z^(max 0 N-N) * (q / Z^(max 0 N)) := by
  rw [Real.rpow_sub hZ]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hZ N),
    ne_of_gt (Real.rpow_pos_of_pos hZ (max 0 N))]

theorem clipped_column_source_identity (w : ℝ → ℂ) {Z q : ℝ}
    (hZ : 0 < Z) (hq : 0 < q) (N θ : ℝ) :
    logPhase θ (Real.log (q/Z^N)) * w (q/Z^N) =
      logPhase θ (Real.log (Z^(max 0 N-N))) *
        clippedSource w (Z^(max 0 N-N)) θ (q/Z^(max 0 N)) := by
  rw [clipped_column_ratio hZ N q]
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hZ _))
    (ne_of_gt (div_pos hq (Real.rpow_pos_of_pos hZ _))), logPhase_add]
  unfold clippedSource
  ring

theorem retained_initial_clipping (w : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) (hs : ContDiff ℝ ∞ w) (J : ℕ) :
    let g := CubicReflectionKernel.logSchwartz w a b ha hw hs
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z N q : ℝ, 1 < Z → 1 ≤ q → w (q/Z^N) ≠ 0 →
      let c := Z^(max 0 N-N)
      1 ≤ c ∧ c ≤ b ∧
      Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b ∧
      (∀ θ : ℝ, logPhase θ (Real.log (q/Z^N)) * w (q/Z^N) =
        logPhase θ (Real.log c) * clippedSource w c θ (q/Z^(max 0 N))) ∧
      (∀ θ : ℝ, Integrable (fun t : ℝ => (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ∧
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
          C*(1+‖θ‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C, hC, hbound⟩ := sourceDensity_moment_uniform
    (CubicReflectionKernel.logSchwartz w a b ha hw hs) J
  refine ⟨C, hC, ?_⟩
  intro Z N q hZ hq hwitness
  obtain ⟨hc, hcb, hsupport, _⟩ := InverseClippingProfiles.retained_clipped_column
    w Z N q a b hZ hq ha hb hw hwitness
  refine ⟨hc, hcb, hsupport, ?_, fun θ => hbound _ θ⟩
  exact fun θ => clipped_column_source_identity w (zero_lt_one.trans hZ)
    (zero_lt_one.trans_le hq) N θ

end SevenEighths.InverseInitialProfile

end

end OAI

end Source2332

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondWholeKernel.lean; sha256: 6c2d3e6ad9bbcb6c9cd43fae79bff063e3f09d58f90fb8b833e3dc6c21871c77 -/
section Source2333
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma secondSourcePairKernel_mark_factors {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (A₁ A₂ : Finset ι) (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (S T : Finset ι) :
    secondSourcePairKernel p e k
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U)*H₁ U)
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U)*H₂ U) W Y S T =
      star (primeMark slots₁ lists₁ a₁ (A₁ ∪ S)) * primeMark slots₂ lists₂ a₂ (A₂ ∪ T) *
        secondSourcePairKernel p e k H₁ H₂ W Y S T := by
  simp only [secondSourcePairKernel,star_mul]
  ring

theorem secondChildKernelPair_whole_profile {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F G V A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    (‖eisEmbedding e‖^2 : ℂ)⁻¹ * secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂
      m r c d e k (-k)
      (secondSourcePairKernel p e k
        (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U)*W₁ (primeProductNorm p G*primeProductNorm p U))
        (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U)*W₂ (primeProductNorm p G*primeProductNorm p U)) Φ Y) =
    ∑ N ∈ (F \ V).powerset, ∑ M ∈ (F \ V).powerset,
      (star (secondChildColumn p hp hcop hg Ψ₁ (m*r) (c*e*∏ i ∈ V,p i)
        (d*e*k) (fun _ => 1) N) *
        secondChildColumn p hp hcop hg Ψ₂ (m*r) (c*e*∏ i ∈ V,p i)
          (d*e*(-k)) (fun _ => 1) M) *
      (star (primeMark slots₁ lists₁ a₁ (A₁ ∪ (V ∪ N))) *
        primeMark slots₂ lists₂ a₂ (A₂ ∪ (V ∪ M))) *
      secondNormProfile (fun x => star (W₁ x)) W₂ Φ (fun _ _ => 1) Y
        ![primeProductNorm p G,‖eisEmbedding e‖^2,primeProductNorm p V,
          ‖eisEmbedding k‖^2,primeProductNorm p N,primeProductNorm p M] := by
  unfold secondChildKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hVM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  rw [secondSourcePairKernel_mark_factors]
  have hp := secondSourcePairKernel_profile p hp G V N M hVN hVM e k W₁ W₂ Φ Y
  rw [← hp]
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2333

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondFiniteMeasure.lean; sha256: e3542085e053ab7442c9d93aa55bf8989e40c39142ccb70211de0dc67804ebe6 -/
section Source2334
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

universe u

theorem second_finite_source_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ G₀ E₀ V₀ K₀ X₀ Y : ℝ,
      0 < G₀ → 0 < E₀ → 0 < V₀ → 0 < K₀ → 0 < X₀ → 0 < Y →
      ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ {κ : Type u} (source : Finset κ) (c : κ → ℂ) (q : κ → Fin 6 → ℝ),
        (∀ x ∈ source, ∀ i, 0 < q x i) →
        (∀ x ∈ source, ∀ i, V i (secondRelativeLog (q x) G₀ E₀ V₀ K₀ X₀ i) = 1) →
        (∑ x ∈ source, c x * secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
          (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (q x)) =
          ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
            ∫ p : Frequency × (Fin 6 → ℝ),
              fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p *
                ∑ x ∈ source, c x * pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
                  (secondRelativeLog (q x) G₀ E₀ V₀ K₀ X₀) p.1 p.2) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + Y*K₀/(E₀*V₀^2*X₀^2))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hsep⟩ := second_norm_kernel_common_measure
    W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  obtain ⟨b₃,he,hi,hbound⟩ := hsep G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  refine ⟨b₃,?_,hi,hbound⟩
  intro κ source c q hq hcut
  have hpoint (x : κ) (hx : x ∈ source) :
      secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
        (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (q x) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ p : Frequency × (Fin 6 → ℝ),
        fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (q x) G₀ E₀ V₀ K₀ X₀) p.1 p.2 := by
    rw [he (q x) (hq x hx) (hcut x hx),full_density_mode_fubini]
    simp only [pureProfileMode_height]
  calc
    _ = ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∑ x ∈ source, c x *
        ∫ p : Frequency × (Fin 6 → ℝ),
          fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (secondRelativeLog (q x) G₀ E₀ V₀ K₀ X₀) p.1 p.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hpoint x hx]
      ring
    _ = _ := by rw [full_density_finite_sum]

end
end SevenEighths.InverseMoment

end OAI

end Source2334

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActualSecondProfile.lean; sha256: aa838143347c734cffd2353518fd77a7df4ed0dbbef22c67ca9af0fac8d93243 -/
section Source2335
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

structure SecondProfileData (ι : Type*) where
  common : Finset ι
  overlap : Finset ι
  extractedLeft : Finset ι
  extractedRight : Finset ι
  rayLeft : Eis →* ℂ
  rayRight : Eis →* ℂ
  puncture : Eis
  quotient : Eis
  oldLabel : Eis
  oldDivisor : Eis
  divisor : Eis
  frequency : Eis

def secondActualNorms {ι : Type*} (p : ι → Eis) (x : SecondProfileData ι)
    (N M : Finset ι) : Fin 6 → ℝ :=
  ![primeProductNorm p x.common, ‖eisEmbedding x.divisor‖^2,
    primeProductNorm p x.overlap, ‖eisEmbedding x.frequency‖^2,
    primeProductNorm p N, primeProductNorm p M]

lemma secondActualNorms_pos {ι : Type*} (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
    (x : SecondProfileData ι) (he : x.divisor ≠ 0) (hk : x.frequency ≠ 0) (N M : Finset ι) :
    ∀ i, 0 < secondActualNorms p x N M i := by
  intro i
  fin_cases i
  · exact primeProductNorm_pos p hp x.common
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero he))
  · exact primeProductNorm_pos p hp x.overlap
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hk))
  · exact primeProductNorm_pos p hp N
  · exact primeProductNorm_pos p hp M

def secondActualCoefficient {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (N M : Finset ι) : ℂ :=
  star (secondChildColumn p hp hcop hg x.rayLeft (x.puncture*x.quotient)
    (x.oldLabel*x.divisor*∏ i ∈ x.overlap,p i) (x.oldDivisor*x.divisor*x.frequency) (fun _ => 1) N) *
  secondChildColumn p hp hcop hg x.rayRight (x.puncture*x.quotient)
    (x.oldLabel*x.divisor*∏ i ∈ x.overlap,p i) (x.oldDivisor*x.divisor*(-x.frequency)) (fun _ => 1) M *
  (star (primeMark slots₁ lists₁ a₁ (x.extractedLeft ∪ (x.overlap ∪ N))) *
    primeMark slots₂ lists₂ a₂ (x.extractedRight ∪ (x.overlap ∪ M)))

def actualSecondProfileRow {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) : ℂ :=
  (‖eisEmbedding x.divisor‖^2 : ℂ)⁻¹ *
  secondChildKernelPair p hp hcop hg F x.overlap x.rayLeft x.rayRight x.puncture x.quotient
    x.oldLabel x.oldDivisor x.divisor x.frequency (-x.frequency)
    (secondSourcePairKernel p x.divisor x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ (x.extractedLeft ∪ U)*
        W₁ (primeProductNorm p x.common*primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (x.extractedRight ∪ U)*
        W₂ (primeProductNorm p x.common*primeProductNorm p U/X)) Φ Y)

theorem actualSecondProfileRow_eq_whole {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    actualSecondProfileRow p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X =
      ∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
        secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
          secondNormProfile (fun z => star (W₁ (z/X))) (fun z => W₂ (z/X)) Φ (fun _ _ => 1) Y
            (secondActualNorms p x N M) :=
  secondChildKernelPair_whole_profile p hp hcop hg F x.common x.overlap x.extractedLeft x.extractedRight
    x.rayLeft x.rayRight x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ (fun z => W₁ (z/X)) (fun z => W₂ (z/X)) Φ Y

end
end SevenEighths.InverseMoment

end OAI

end Source2335

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActualSecondMeasure.lean; sha256: a9cb39dba2c21bd8490158ef67c422ce40c77c2359c25738e104da80ab182163 -/
section Source2336
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondProfileIndices {κ ι : Type*} [DecidableEq ι]
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) :
    Finset (Σ _ : κ, Finset ι × Finset ι) :=
  source.sigma (fun j => (F \ (x j).overlap).powerset ×ˢ (F \ (x j).overlap).powerset)

lemma mem_secondProfileIndices {κ ι : Type*} [DecidableEq ι]
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι)
    (j : Σ _ : κ, Finset ι × Finset ι) : j ∈ secondProfileIndices source F x ↔
      j.1 ∈ source ∧ j.2.1 ∈ (F \ (x j.1).overlap).powerset ∧
        j.2.2 ∈ (F \ (x j.1).overlap).powerset := by
  simp only [secondProfileIndices,Finset.mem_sigma,Finset.mem_product]

theorem actualSecondProfileRows_eq_indexed {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X) =
    ∑ j ∈ secondProfileIndices source F x,
      (w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
      secondNormProfile (fun z => star (W₁ (z/X))) (fun z => W₂ (z/X)) Φ (fun _ _ => 1) Y
        (secondActualNorms p (x j.1) j.2.1 j.2.2) := by
  simp only [actualSecondProfileRow_eq_whole,secondProfileIndices,Finset.sum_sigma,
    Finset.sum_product,Finset.mul_sum,mul_assoc]

theorem actualSecondProfileRows_integral {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (g : Fin 6 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
          fullProfileDensity g b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope
              (t₁,t₂,t₃) u i) (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2)
                G₀ E₀ V₀ K₀ X₀ i))) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        fullProfileDensity g b₁ b₂ b₃ v *
          ∑ j ∈ secondProfileIndices source F x,
            (w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
              slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
  rw [actualSecondProfileRows_eq_indexed]
  rw [← full_density_finite_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj, full_density_mode_fubini]
  simp only [pureProfileMode_height]
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2336

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActualSecondUniform.lean; sha256: cf6dae9b7698a05a69e32188dcb4a1f088acaa1e578c01cb2429dbfd682a2d69 -/
section Source2337
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v w

def ActualSecondCommonMeasureAt (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (hV : ∀ i, ContDiff ℝ ∞ (V i))
    (hS : ∀ i, HasCompactSupport (V i))
    (G₀ E₀ V₀ K₀ X₀ Y : ℝ) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) : Prop :=
  ∀ {κ : Type u} {ι : Type v} {σ : Type w} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (weight : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ),
    (∀ j ∈ source, (x j).divisor ≠ 0 ∧ (x j).frequency ≠ 0) →
    (∀ j ∈ secondProfileIndices source F x, ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1) →
    (∑ j ∈ source, weight j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ z : Frequency × (Fin 6 → ℝ),
        fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ z *
          ∑ j ∈ secondProfileIndices source F x,
            (weight j.1 * secondActualCoefficient p hp hcop hg (x j.1)
              slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) z.1 z.2

theorem actual_second_uniform_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ G₀ E₀ V₀ K₀ X₀ Y : ℝ,
      0 < G₀ → 0 < E₀ → 0 < V₀ → 0 < K₀ → 0 < X₀ → 0 < Y →
      ∃ b₃ : 𝓢(ℝ, ℂ),
      ActualSecondCommonMeasureAt.{u,v,w} W₁ W₂ Φ V hV hS G₀ E₀ V₀ K₀ X₀ Y b₁ b₂ b₃ ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + Y*K₀/(E₀*V₀^2*X₀^2))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  have hstar : ContDiff ℝ ∞ (fun t => star (W₁ t)) := Complex.conjCLE.contDiff.comp hW₁
  have hsstar : Function.support (fun t => star (W₁ t)) ⊆ Set.Icc a b := by
    intro t ht
    apply hs₁
    simpa only [Function.mem_support,star_ne_zero] using ht
  obtain ⟨b₁,b₂,C,hC,hsep⟩ := second_norm_kernel_common_measure
    (fun t => star (W₁ t)) W₂ a b ha hsstar hs₂ hstar hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  obtain ⟨b₃,he,hi,hbound⟩ := hsep G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  refine ⟨b₃,?_,hi,hbound⟩
  intro κ ι σ _ _ p hp _ hcop hg source F x weight slots₁ slots₂ lists₁ lists₂ a₁ a₂ hn hcut
  apply actualSecondProfileRows_integral p hp hcop hg source F x weight
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y G₀ E₀ V₀ K₀ X₀
    (secondRootSchwartz V hV hS) b₁ b₂ b₃
  intro j hj
  have hj0 := (mem_secondProfileIndices source F x j).mp hj
  exact he (secondActualNorms p (x j.1) j.2.1 j.2.2)
    (secondActualNorms_pos p hp (x j.1) (hn j.1 hj0.1).1 (hn j.1 hj0.1).2 j.2.1 j.2.2)
    (hcut j hj)

end
end SevenEighths.InverseMoment

end OAI

end Source2337

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondPass.lean; sha256: e72d0f63218c83bceb47cc97079dc9cf00b874f8f0bb6008b91a4a6a7cff96ef -/
section Source2338
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq σ] in
theorem marked_input_smoothed_second_poisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (F A : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : Eis, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖inputConjugateRow p hg F Ψ m c d
        (fun U => H U * primeMark slots lists a (A ∪ U)) z‖ ^ 2 : ℝ)) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then overlapPairWeight p hg Ψ m c d
          (fun U => H U * primeMark slots lists a (A ∪ U)) G U V *
          maskedSecondDual p hg hp hinj G U V W Y else 0 :=
  inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ m c d _ W Y hY

def canonicalMarkedSplit (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ V) *
    finiteCanonicalMarkedRow p hp hcop hg F Ψ (m * r)
      (c * e * ∏ i ∈ V, p i) (d * e * k)
      (slots \ J) (fun i => lists i \ A) a W (X / primeProductNorm p V)

theorem secondActualPair_marked_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (F A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U) * W₁ (primeProductNorm p U / X₁))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U) * W₂ (primeProductNorm p U / X₂)) =
      ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z, V) *
        star (canonicalMarkedSplit p hp hcop hg F V A₁ (secondRayMinus Ψ₁ z)
          m r c d e k slots₁ lists₁ a₁ W₁ X₁) *
        canonicalMarkedSplit p hp hcop hg F V A₂ (secondRayPlus Ψ₂ z)
          m r c d e (-k) slots₂ lists₂ a₂ W₂ X₂ := by
  rw [secondActualPair_eq_children p hp hcop hg hinj hc hpr]
  simp only [secondChildSum_marked_fixed_pool, canonicalMarkedSplit]

end
end SevenEighths.InverseMoment

end OAI

end Source2338

/- Original source: OAI/NumberTheory/DirichletL/Descent/FreshWindows.lean; sha256: 8707fe7459c41fa07770c526028fab106fc4921dbe680d00d29594e2f46eee9e -/
section Source2339
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem fresh_ratio_of_source_support (W : ℝ → ℂ) (a b g₀ g₁ v₀ v₁ g v n : ℝ)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hg₀ : 0 < g₀) (hv₀ : 0 < v₀) (hg : g ∈ Set.Icc g₀ g₁)
    (hv : v ∈ Set.Icc v₀ v₁) (hn : 0 ≤ n) (hw : W (g*v*n) ≠ 0) :
    n ∈ Set.Icc (a/(g₁*v₁)) (b/(g₀*v₀)) := by
  have hgp : 0 < g := hg₀.trans_le hg.1
  have hvp : 0 < v := hv₀.trans_le hv.1
  have hghi : 0 < g₁ := hgp.trans_le hg.2
  have hvhi : 0 < v₁ := hvp.trans_le hv.2
  have hsource := hs hw
  constructor
  · apply (div_le_iff₀ (mul_pos hghi hvhi)).mpr
    calc
      a ≤ g*v*n := hsource.1
      _ ≤ (g₁*v₁)*n := mul_le_mul_of_nonneg_right
        (mul_le_mul hg.2 hv.2 hvp.le hghi.le) hn
      _ = _ := by ring
  · apply (le_div_iff₀ (mul_pos hg₀ hv₀)).mpr
    calc
      _ = (g₀*v₀)*n := by ring
      _ ≤ g*v*n := mul_le_mul_of_nonneg_right
        (mul_le_mul hg.1 hv.1 hv₀.le hgp.le) hn
      _ ≤ b := hsource.2

theorem fresh_window_eq_one (W ω : ℝ → ℂ) (a b g₀ g₁ v₀ v₁ g v n : ℝ)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hg₀ : 0 < g₀) (hv₀ : 0 < v₀) (hg : g ∈ Set.Icc g₀ g₁)
    (hv : v ∈ Set.Icc v₀ v₁) (hn : 0 ≤ n)
    (hω : ∀ n ∈ Set.Icc (a/(g₁*v₁)) (b/(g₀*v₀)), ω n = 1)
    (hw : W (g*v*n) ≠ 0) : ω n = 1 :=
  hω n (fresh_ratio_of_source_support W a b g₀ g₁ v₀ v₁ g v n hs hg₀ hv₀ hg hv hn hw)

theorem secondChildKernelPair_insert_fresh {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F V : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k₁ k₂ : Eis)
    (K : Finset ι → Finset ι → ℂ) (ω₁ ω₂ : Finset ι → ℂ)
    (hω : ∀ N ∈ (F \ V).powerset, ∀ M ∈ (F \ V).powerset,
      K (V ∪ N) (V ∪ M) ≠ 0 → ω₁ (V ∪ N) = 1 ∧ ω₂ (V ∪ M) = 1) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (fun S T => star (ω₁ S)*ω₂ T*K S T) := by
  unfold secondChildKernelPair
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  by_cases hK : K (V ∪ N) (V ∪ M) = 0
  · simp only [hK,mul_zero]
  · obtain ⟨h1,h2⟩ := hω N hN M hM hK
    simp only [h1,h2,star_one,one_mul]

theorem secondChildKernelPair_separated_marked {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F V A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k₁ k₂ : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (fun S T => star (primeMark slots₁ lists₁ a₁ (A₁ ∪ S)*W₁ (primeProductNorm p S/X₁)) *
        (primeMark slots₂ lists₂ a₂ (A₂ ∪ T)*W₂ (primeProductNorm p T/X₂))) =
      star (canonicalMarkedSplit p hp hcop hg F V A₁ Ψ₁ m r c d e k₁ slots₁ lists₁ a₁ W₁ X₁) *
        canonicalMarkedSplit p hp hcop hg F V A₂ Ψ₂ m r c d e k₂ slots₂ lists₂ a₂ W₂ X₂ := by
  have hs (Ψ : Eis →* ℂ) (A : Finset ι) (k : Eis) (slots : Finset σ)
      (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :=
    secondChildSum_marked_fixed_pool p hp hcop hg F V A Ψ m r c d e k slots lists a W X
  unfold canonicalMarkedSplit
  rw [← hs Ψ₁ A₁ k₁ slots₁ lists₁ a₁ W₁ X₁, ← hs Ψ₂ A₂ k₂ slots₂ lists₂ a₂ W₂ X₂]
  unfold secondChildKernelPair secondChildSum
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  simp only [secondChildColumn,star_mul,mul_one]
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2339

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondSeparatedColumns.lean; sha256: 404792d499c4c84f7ba86188afcdf0f1c89dfa665917d7254bc9183d210a10c7 -/
section Source2340
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondOuterPhase (h y : Fin 6 → ℝ) : ℂ :=
  logPhase (h 0) (y 0) * logPhase (h 1) (y 1) *
    logPhase (h 2) (y 2) * logPhase (h 3) (y 3)

def childLogTest (ω : ℝ → ℂ) (h : ℝ) (y : ℝ) : ℂ :=
  ω y * logPhase h (Real.log y)

lemma second_mode_split (y : Fin 6 → ℝ) (t : Frequency) (u : Fin 6 → ℝ) :
    pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t u =
      secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u) y *
        logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 4) (y 4) *
        logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 5) (y 5) := by
  rw [pureProfileMode_height]
  simp only [Fin.prod_univ_succ, secondOuterPhase]
  simp only [Fin.succ,  Fin.val_mk]
  norm_num
  ring

lemma secondOuterPhase_norm (h y : Fin 6 → ℝ) : ‖secondOuterPhase h y‖ = 1 := by
  simp only [secondOuterPhase,norm_mul,logPhase_norm,mul_one]

lemma second_fresh_scale {ι : Type*} [DecidableEq ι] (p : ι → Eis)
    (hp : ∀ i, p i ≠ 0) (V N : Finset ι) (hVN : Disjoint V N) (X : ℝ) :
    primeProductNorm p (V ∪ N)/(primeProductNorm p V*X) = primeProductNorm p N/X := by
  rw [primeProductNorm_union p V N hVN]
  field_simp [(primeProductNorm_pos p hp V).ne']

theorem actual_second_columns_separated {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (X : ℝ) (h₁ h₂ : ℝ) :
    (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
      secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
        (star (ω₁ (primeProductNorm p N/X)) * ω₂ (primeProductNorm p M/X)) *
        logPhase h₁ (Real.log (primeProductNorm p N/X)) *
        logPhase h₂ (Real.log (primeProductNorm p M/X))) =
    star (canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedLeft x.rayLeft
      x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
      slots₁ lists₁ a₁ (childLogTest ω₁ (-h₁)) (primeProductNorm p x.overlap*X)) *
      canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedRight x.rayRight
      x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor (-x.frequency)
      slots₂ lists₂ a₂ (childLogTest ω₂ h₂) (primeProductNorm p x.overlap*X) := by
  rw [← secondChildKernelPair_separated_marked]
  unfold secondChildKernelPair
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint x.overlap N := by
    apply Finset.disjoint_left.mpr
    intro i hi hiN
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 hi
  have hVM : Disjoint x.overlap M := by
    apply Finset.disjoint_left.mpr
    intro i hi hiM
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hM) hiM)).2 hi
  dsimp only
  rw [second_fresh_scale p hp x.overlap N hVN,second_fresh_scale p hp x.overlap M hVM]
  simp only [secondActualCoefficient,childLogTest,secondChildColumn,
    star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,mul_one]
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2340

/- Original source: OAI/NumberTheory/DirichletL/Inversion/AmbientProfileTower.lean; sha256: b37c1388089d04d55a03d1674eb3a8c090f9e93a523a9cbeba0af1a926bc8ed5 -/
section Source2341
namespace OAI

namespace SevenEighths.InverseAmbientProfileTower
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open SevenEighths.InverseMoment
noncomputable section

theorem frequencyTwist_fourier_joint_stronglyMeasurable (g : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : ℝ × ℝ => (𝓕 (frequencyTwist g p.1)) p.2) := by
  have hf : StronglyMeasurable
      (fun p : ℝ × ℝ => frequencyTwist g p.1 p.2) := by
    simp only [frequencyTwist_apply]
    apply Continuous.stronglyMeasurable
    unfold logPhase
    fun_prop
  exact InverseKernelSourceUniform.fourier_joint_stronglyMeasurable
    (fun θ => (frequencyTwist g θ : ℝ → ℂ)) hf

theorem logSource_fourier_joint_stronglyMeasurable
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    StronglyMeasurable (fun p : ℝ × ℝ =>
      (𝓕 (frequencyTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) p.1)) p.2) :=
  frequencyTwist_fourier_joint_stronglyMeasurable _

theorem twistedTriple_joint_stronglyMeasurable (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × Frequency =>
      tripleCoefficient (𝓕 (frequencyTwist g₁ p.1.1))
        (𝓕 (frequencyTwist g₂ p.1.2)) b₃ p.2) := by
  unfold tripleCoefficient
  exact ((frequencyTwist_fourier_joint_stronglyMeasurable g₁).comp_measurable
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).mul
      (((frequencyTwist_fourier_joint_stronglyMeasurable g₂).comp_measurable
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))).mul
      (b₃.continuous.stronglyMeasurable.comp_measurable
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))

abbrev Ambient (ι : Type*) := Frequency × (ι → ℝ)

def ambientWeight {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) : ℝ :=
  ((1 + ‖p.1.1‖)^J * (1 + ‖p.1.2.1‖)^J * (1 + ‖p.1.2.2‖)^J) *
    ∏ i, (1 + ‖p.2 i‖)^J

theorem ambientWeight_eq_pow {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) :
    ambientWeight J p = (ambientWeight 1 p)^J := by
  simp [ambientWeight, mul_pow, Finset.prod_pow]

theorem ambientWeight_one_le {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) :
    1 ≤ ambientWeight J p := by
  unfold ambientWeight
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg p.1.1]))
        (one_le_pow₀ (by linarith [norm_nonneg p.1.2.1])))
        (one_le_pow₀ (by linarith [norm_nonneg p.1.2.2])))
    (Finset.one_le_prod₀ (fun i _ => one_le_pow₀ (by linarith [norm_nonneg (p.2 i)])))

theorem ambientWeight_add {ι : Type*} [Fintype ι] (J K : ℕ) (p : Ambient ι) :
    ambientWeight (J + K) p = ambientWeight J p * ambientWeight K p := by
  rw [ambientWeight_eq_pow (J+K), ambientWeight_eq_pow J, ambientWeight_eq_pow K, pow_add]

def inheritedLeft {ι : Type*} (i : ι) (p : Ambient ι) : ℝ :=
  p.2 i + p.1.1 - p.1.2.2

def inheritedRight {ι : Type*} (i : ι) (p : Ambient ι) : ℝ :=
  -(p.2 i + p.1.2.1 - p.1.2.2)

private theorem one_add_norm_add_le (x y : ℝ) :
    1 + ‖x + y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
  have h := norm_add_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  nlinarith [mul_nonneg hx hy]

private theorem coordinate_factor_le {ι : Type*} [Fintype ι]
    (i : ι) (u : ι → ℝ) :
    1 + ‖u i‖ ≤ ∏ j, (1 + ‖u j‖) :=
  by
  have hm (j : ι) : max (1 + ‖u j‖) 1 = 1 + ‖u j‖ :=
    max_eq_left (by linarith [norm_nonneg (u j)])
  simpa only [hm] using
    Finset.le_prod_max_one (Finset.mem_univ i) (fun j => 1 + ‖u j‖)

theorem inheritedLeft_bound {ι : Type*} [Fintype ι] (i : ι) (p : Ambient ι) :
    1 + ‖inheritedLeft i p‖ ≤ ambientWeight 1 p := by
  have h := (one_add_norm_add_le (p.2 i + p.1.1) (-p.1.2.2)).trans
    (mul_le_mul_of_nonneg_right (one_add_norm_add_le (p.2 i) p.1.1) (by positivity))
  simp only [norm_neg, ← sub_eq_add_neg] at h
  have hc := coordinate_factor_le i p.2
  have ht : (1 + ‖p.1.1‖) * (1 + ‖p.1.2.2‖) ≤
      (1 + ‖p.1.1‖) * (1 + ‖p.1.2.1‖) * (1 + ‖p.1.2.2‖) := by
    nlinarith [norm_nonneg p.1.1, norm_nonneg p.1.2.1, norm_nonneg p.1.2.2,
      mul_nonneg (mul_nonneg (show 0 ≤ 1 + ‖p.1.1‖ by positivity)
        (norm_nonneg p.1.2.1)) (show 0 ≤ 1 + ‖p.1.2.2‖ by positivity)]
  have hh := mul_le_mul hc ht (by positivity)
    (Finset.prod_nonneg (fun j _ => by positivity))
  change _ ≤ (∏ j, (1 + ‖p.2 j‖)) * _ at hh
  exact h.trans (by simpa [ambientWeight, inheritedLeft, mul_comm, mul_left_comm, mul_assoc] using hh)

theorem inheritedRight_bound {ι : Type*} [Fintype ι] (i : ι) (p : Ambient ι) :
    1 + ‖inheritedRight i p‖ ≤ ambientWeight 1 p := by
  have h := inheritedLeft_bound i ((p.1.2.1, p.1.1, p.1.2.2), p.2)
  change 1 + ‖-(p.2 i + p.1.2.1 - p.1.2.2)‖ ≤ _
  rw [norm_neg]
  simpa [inheritedLeft, ambientWeight, mul_comm, mul_left_comm, mul_assoc] using h

theorem inherited_pair_weight_bound {ι : Type*} [Fintype ι]
    (i j : ι) (J K : ℕ) (p : Ambient ι) :
    ambientWeight J p * ((1 + ‖inheritedLeft i p‖)^K *
      (1 + ‖inheritedRight j p‖)^K) ≤ ambientWeight (J + 2*K) p := by
  have h₁ := pow_le_pow_left₀ (by positivity) (inheritedLeft_bound i p) K
  have h₂ := pow_le_pow_left₀ (by positivity) (inheritedRight_bound j p) K
  have hh := mul_le_mul h₁ h₂ (by positivity)
    (pow_nonneg (le_trans zero_le_one (ambientWeight_one_le 1 p)) K)
  rw [← pow_add] at hh
  rw [ambientWeight_add, ambientWeight_eq_pow (2*K)]
  exact mul_le_mul_of_nonneg_left (by simpa [two_mul] using hh)
    (le_trans zero_le_one (ambientWeight_one_le J p))

theorem ambientWeight_continuous {ι : Type*} [Fintype ι] (J : ℕ) :
    Continuous (ambientWeight (ι := ι) J) := by
  unfold ambientWeight
  fun_prop

theorem inheritedLeft_continuous {ι : Type*} (i : ι) :
    Continuous (inheritedLeft i) := by unfold inheritedLeft; fun_prop

theorem inheritedRight_continuous {ι : Type*} (i : ι) :
    Continuous (inheritedRight i) := by unfold inheritedRight; fun_prop

private theorem inheritedParameter_measurable {ι κ : Type*} (i j : ι) :
    Measurable (fun z : Ambient ι × Ambient κ =>
      ((inheritedLeft i z.1,inheritedRight j z.1),z.2)) := by
  unfold inheritedLeft inheritedRight
  fun_prop

private theorem conditional_tower_integrable
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (J K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (B : Ambient ι → ℂ) (hB : StronglyMeasurable B)
    (D : Ambient ι → Ambient κ → ℂ)
    (hD : StronglyMeasurable (Function.uncurry D))
    (hi : ∀ p, Integrable (fun q => ambientWeight J q * ‖D p q‖))
    (hb : ∀ p, (∫ q, ambientWeight J q * ‖D p q‖) ≤
      C * ((1 + ‖inheritedLeft i p‖)^K * (1 + ‖inheritedRight j p‖)^K))
    (houter : Integrable (fun p => ambientWeight (J+2*K) p * ‖B p‖)) :
    Integrable (fun z : Ambient ι × Ambient κ =>
      ambientWeight J z.1 * ambientWeight J z.2 * ‖B z.1 * D z.1 z.2‖) := by
  let f : Ambient ι × Ambient κ → ℝ := fun z =>
    ambientWeight J z.1 * ambientWeight J z.2 * ‖B z.1 * D z.1 z.2‖
  have hf_nonneg (z) : 0 ≤ f z := by
    dsimp only [f]
    exact mul_nonneg (mul_nonneg
      (le_trans zero_le_one (ambientWeight_one_le J z.1))
      (le_trans zero_le_one (ambientWeight_one_le J z.2))) (norm_nonneg _)
  have hsm : StronglyMeasurable f :=
    (((ambientWeight_continuous J).comp continuous_fst).stronglyMeasurable.mul
      ((ambientWeight_continuous J).comp continuous_snd).stronglyMeasurable).mul
        ((hB.comp_measurable measurable_fst).mul hD).norm
  apply (integrable_prod_iff hsm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun p => by
      convert (hi p).const_mul (ambientWeight J p * ‖B p‖) using 1
      funext q; dsimp only [f]; rw [norm_mul]; ring)
  · apply (houter.const_mul C).mono' (hsm.norm.integral_prod_right').aestronglyMeasurable
    filter_upwards with p
    have he : (∫ q, ‖f (p,q)‖) =
        ambientWeight J p * ‖B p‖ * (∫ q, ambientWeight J q * ‖D p q‖) := by
      simp_rw [Real.norm_of_nonneg (hf_nonneg _)]
      have heq (q) : f (p,q) =
          (ambientWeight J p * ‖B p‖) * (ambientWeight J q * ‖D p q‖) := by
        dsimp only [f]; rw [norm_mul]; ring
      simp_rw [heq]
      exact integral_const_mul _ _
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), he]
    calc
      _ ≤ ambientWeight J p * ‖B p‖ *
          (C * ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) :=
        mul_le_mul_of_nonneg_left (hb p)
          (mul_nonneg (le_trans zero_le_one (ambientWeight_one_le J p)) (norm_nonneg _))
      _ = (C * ‖B p‖) * (ambientWeight J p *
          ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) := by ring
      _ ≤ (C * ‖B p‖) * ambientWeight (J+2*K) p :=
        mul_le_mul_of_nonneg_left (inherited_pair_weight_bound i j J K p)
          (mul_nonneg hC (norm_nonneg _))
      _ = C * (ambientWeight (J+2*K) p * ‖B p‖) := by ring

private theorem conditional_tower_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (J K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (B : Ambient ι → ℂ) (hB : StronglyMeasurable B)
    (D : Ambient ι → Ambient κ → ℂ)
    (hD : StronglyMeasurable (Function.uncurry D))
    (hi : ∀ p, Integrable (fun q => ambientWeight J q * ‖D p q‖))
    (hb : ∀ p, (∫ q, ambientWeight J q * ‖D p q‖) ≤
      C * ((1 + ‖inheritedLeft i p‖)^K * (1 + ‖inheritedRight j p‖)^K))
    (houter : Integrable (fun p => ambientWeight (J+2*K) p * ‖B p‖)) :
    (∫ z : Ambient ι × Ambient κ,
      ambientWeight J z.1 * ambientWeight J z.2 * ‖B z.1 * D z.1 z.2‖) ≤
      C * (∫ p, ambientWeight (J+2*K) p * ‖B p‖) := by
  have hprod := conditional_tower_integrable i j J K C hC B hB D hD hi hb houter
  rw [Measure.volume_eq_prod, integral_prod _ hprod, ← integral_const_mul]
  apply integral_mono hprod.integral_prod_left (houter.const_mul C)
  intro p
  have he (q) : ambientWeight J p * ambientWeight J q * ‖B p * D p q‖ =
      (ambientWeight J p * ‖B p‖) * (ambientWeight J q * ‖D p q‖) := by
    rw [norm_mul]; ring
  simp_rw [he]
  rw [integral_const_mul]
  calc
    _ ≤ ambientWeight J p * ‖B p‖ *
        (C * ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) :=
      mul_le_mul_of_nonneg_left (hb p)
        (mul_nonneg (le_trans zero_le_one (ambientWeight_one_le J p)) (norm_nonneg _))
    _ = (C * ‖B p‖) * (ambientWeight J p *
        ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) := by ring
    _ ≤ (C * ‖B p‖) * ambientWeight (J+2*K) p :=
      mul_le_mul_of_nonneg_left (inherited_pair_weight_bound i j J K p)
        (mul_nonneg hC (norm_nonneg _))
    _ = C * (ambientWeight (J+2*K) p * ‖B p‖) := by ring

theorem integrable_density_test {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D F : Ambient ι × Ambient κ → ℂ)
    (hD : StronglyMeasurable D) (hF : StronglyMeasurable F) (J : ℕ)
    (hi : Integrable (fun z => ambientWeight J z.1 * ambientWeight J z.2 * ‖D z‖))
    (hFbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    Integrable (fun z => D z * F z) := by
  apply hi.mono' (hD.mul hF).aestronglyMeasurable
  filter_upwards with z
  change ‖D z * F z‖ ≤ _
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hFbound z) (norm_nonneg _)

theorem density_test_fubini {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D F : Ambient ι × Ambient κ → ℂ)
    (hD : StronglyMeasurable D) (hF : StronglyMeasurable F) (J : ℕ)
    (hi : Integrable (fun z => ambientWeight J z.1 * ambientWeight J z.2 * ‖D z‖))
    (hFbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    (∫ z, D z * F z) = ∫ p, ∫ q, D (p,q) * F (p,q) := by
  have h := integrable_density_test D F hD hF J hi hFbound
  simpa only [Measure.volume_eq_prod] using integral_prod (fun z => D z * F z) h

def twistedFullDensity {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (θ : ℝ × ℝ) (p : Ambient ι) : ℂ :=
  fullProfileDensity g (𝓕 (frequencyTwist g₁ θ.1))
    (𝓕 (frequencyTwist g₂ θ.2)) b₃ p

theorem fullProfileDensity_continuous {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) :
    Continuous (fullProfileDensity g b₁ b₂ b₃) := by
  unfold fullProfileDensity tripleCoefficient coordinateDensity
  fun_prop

theorem twistedFullDensity_joint_stronglyMeasurable {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × Ambient ι =>
      twistedFullDensity g g₁ g₂ b₃ p.1 p.2) := by
  unfold twistedFullDensity fullProfileDensity
  apply StronglyMeasurable.mul
  · have hm : Measurable (fun p : (ℝ × ℝ) × Ambient ι => (p.1,p.2.1)) := by fun_prop
    simpa only [Function.comp_def] using
      (twistedTriple_joint_stronglyMeasurable g₁ g₂ b₃).comp_measurable hm
  · apply Continuous.stronglyMeasurable
    unfold coordinateDensity
    fun_prop

theorem fullProfileDensity_weighted_integrable {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun p : Ambient ι =>
      ambientWeight J p * ‖fullProfileDensity g b₁ b₂ b₃ p‖) := by
  convert (tripleCoefficient_weighted_integrable b₁ b₂ b₃ J).mul_prod
    (coordinate_density_weighted_integrable g J) using 1
  funext p
  simp only [ambientWeight, fullProfileDensity, norm_mul]
  ring

theorem fullProfileDensity_weighted_integral {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ p : Ambient ι, ambientWeight J p * ‖fullProfileDensity g b₁ b₂ b₃ p‖) =
      (∫ t : Frequency,
        ((1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) *
      (∫ u : ι → ℝ, (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖) := by
  have he (p : Ambient ι) :
      ambientWeight J p * ‖fullProfileDensity g b₁ b₂ b₃ p‖ =
      (((1+‖p.1.1‖)^J * (1+‖p.1.2.1‖)^J * (1+‖p.1.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ p.1‖) *
      ((∏ i, (1+‖p.2 i‖)^J) * ‖coordinateDensity g p.2‖) := by
    simp only [ambientWeight, fullProfileDensity, norm_mul]; ring
  simp_rw [he, Measure.volume_eq_prod]
  exact integral_prod_mul
    (fun t : Frequency => ((1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) *
      ‖tripleCoefficient b₁ b₂ b₃ t‖)
    (fun u : ι → ℝ => (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖)

def towerMomentOrder (J : ℕ) : ℕ := J + 2*(J + (volume : Measure ℝ).integrablePower)

theorem twistedFullDensity_moment {ι : Type*} [Fintype ι]
    (J : ℕ) (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ × ℝ,
      (∫ p : Ambient ι, ambientWeight J p * ‖twistedFullDensity g g₁ g₂ b₃ θ p‖) ≤
      C * ((1+‖θ.1‖)^(J + (volume : Measure ℝ).integrablePower) *
        (1+‖θ.2‖)^(J + (volume : Measure ℝ).integrablePower)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂, hC₂, h₂⟩ := frequencyTwist_fourier_moment J g₂
  let M := ∫ u : ι → ℝ, (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖
  let B := ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖
  have hM : 0 ≤ M := integral_nonneg (fun _ => by positivity)
  have hB : 0 ≤ B := integral_nonneg (fun _ => by positivity)
  refine ⟨C₁*C₂*B*M, by positivity, ?_⟩
  intro θ
  unfold twistedFullDensity
  rw [fullProfileDensity_weighted_integral,
    tripleCoefficient_weighted_integral]
  have hh := mul_le_mul (h₁ θ.1) (h₂ θ.2)
    (integral_nonneg (fun _ => by positivity)) (by positivity)
  have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hB) hM
  convert hh' using 1
  ring

def towerDensity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (z : Ambient ι × Ambient κ) : ℂ :=
  fullProfileDensity outer b₁ b₂ b₃ z.1 *
    twistedFullDensity inner g₁ g₂ c₃
      (inheritedLeft i z.1, inheritedRight j z.1) z.2

theorem towerDensity_joint_stronglyMeasurable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃) := by
  unfold towerDensity
  apply StronglyMeasurable.mul
  · exact ((fullProfileDensity_continuous outer b₁ b₂ b₃).comp continuous_fst).stronglyMeasurable
  · simpa only [Function.comp_def] using
      (twistedFullDensity_joint_stronglyMeasurable inner g₁ g₂ c₃).comp_measurable
        (inheritedParameter_measurable i j)

theorem towerDensity_weighted {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : ℕ) (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
      Integrable (fun z : Ambient ι × Ambient κ =>
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ∧
      (∫ z : Ambient ι × Ambient κ,
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ≤
        C * (∫ p : Ambient ι, ambientWeight (towerMomentOrder J) p *
          ‖fullProfileDensity outer b₁ b₂ b₃ p‖) := by
  obtain ⟨C,hC,hb⟩ := twistedFullDensity_moment J inner g₁ g₂ c₃
  refine ⟨C,hC,?_⟩
  intro i j outer b₁ b₂ b₃
  let D : Ambient ι → Ambient κ → ℂ := fun p q =>
    twistedFullDensity inner g₁ g₂ c₃ (inheritedLeft i p, inheritedRight j p) q
  have hD : StronglyMeasurable (Function.uncurry D) := by
    simpa only [Function.comp_def, Function.uncurry_def, D] using
      (twistedFullDensity_joint_stronglyMeasurable inner g₁ g₂ c₃).comp_measurable
        (inheritedParameter_measurable i j)
  have hi (p : Ambient ι) : Integrable (fun q => ambientWeight J q * ‖D p q‖) :=
    fullProfileDensity_weighted_integrable inner
      (𝓕 (frequencyTwist g₁ (inheritedLeft i p)))
      (𝓕 (frequencyTwist g₂ (inheritedRight j p))) c₃ J
  have hout := fullProfileDensity_weighted_integrable outer b₁ b₂ b₃ (towerMomentOrder J)
  have hB := (fullProfileDensity_continuous outer b₁ b₂ b₃).stronglyMeasurable
  exact ⟨conditional_tower_integrable i j J _ C hC _ hB D hD hi
      (fun p => hb (inheritedLeft i p,inheritedRight j p)) hout,
    conditional_tower_bound i j J _ C hC _ hB D hD hi
      (fun p => hb (inheritedLeft i p,inheritedRight j p)) hout⟩

theorem towerDensity_fubini {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (F : Ambient ι × Ambient κ → ℂ) (hF : StronglyMeasurable F) (J : ℕ)
    (hFbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    (∫ z, towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z * F z) =
      ∫ p, ∫ q, towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ (p,q) * F (p,q) := by
  obtain ⟨C,hC,h⟩ := towerDensity_weighted (ι := ι) J inner g₁ g₂ c₃
  exact density_test_fubini _ F
    (towerDensity_joint_stronglyMeasurable i j outer b₁ b₂ b₃ inner g₁ g₂ c₃)
    hF J (h i j outer b₁ b₂ b₃).1 hFbound

theorem first_inherited_left_eq (p : Ambient (Fin 9)) :
    inheritedLeft 7 p = profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 7 := by
  simp [inheritedLeft, profileHeight, firstLeftSlope, firstRightSlope, firstKernelSlope]
  ring

theorem first_inherited_right_eq (p : Ambient (Fin 9)) :
    inheritedRight 8 p = -profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 8 := by
  simp [inheritedRight, profileHeight, firstLeftSlope, firstRightSlope, firstKernelSlope]
  ring

theorem second_inherited_left_eq (p : Ambient (Fin 6)) :
    inheritedLeft 4 p = profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 4 := by
  simp [inheritedLeft, profileHeight, secondLeftSlope, secondRightSlope, secondKernelSlope]
  ring

theorem second_inherited_right_eq (p : Ambient (Fin 6)) :
    inheritedRight 5 p = -profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 5 := by
  simp [inheritedRight, profileHeight, secondLeftSlope, secondRightSlope, secondKernelSlope]
  ring

theorem twistedFullDensity_uniform_separation {κ : Type*} [Fintype κ]
    (g : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (a₁ a₂ ak M : κ → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hbox : ∀ i y, g i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ c₃ : 𝓢(ℝ, ℂ),
      (∀ (θ : ℝ × ℝ) (y : κ → ℝ),
        (∏ i, g i (y i)) * frequencyTwist g₁ θ.1 (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ.2 (∑ i, a₂ i * y i) *
          EisensteinSchwartzPoisson.paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : κ → ℝ,
          twistedFullDensity g g₁ g₂ c₃ θ ((t₁,t₂,t₃),u) *
            pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u) ∧
      (∀ θ : ℝ × ℝ,
        (1+R)^A * (∫ p : Ambient κ,
          ambientWeight J p * ‖twistedFullDensity g g₁ g₂ c₃ θ p‖) ≤
        C * ((1+‖θ.1‖)^(J + (volume : Measure ℝ).integrablePower) *
          (1+‖θ.2‖)^(J + (volume : Measure ℝ).integrablePower))) := by
  obtain ⟨C,hC,hs⟩ := twisted_descent_profile_separation
    g₁ g₂ Φ (fun i => g i) a₁ a₂ ak M hM hbox A J
  let G := ∫ u : κ → ℝ, (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖
  have hG : 0 ≤ G := integral_nonneg (fun _ => by positivity)
  refine ⟨C*G,mul_nonneg hC hG,?_⟩
  intro R hR
  obtain ⟨c₃,hc⟩ := hs R hR
  refine ⟨c₃,?_,?_⟩
  · intro θ y
    rw [(hc θ.1 θ.2).1 y]
    exact profile_integral_coordinate_absorption g
      (𝓕 (frequencyTwist g₁ θ.1)) (𝓕 (frequencyTwist g₂ θ.2)) c₃ a₁ a₂ ak y
  · intro θ
    unfold twistedFullDensity
    rw [fullProfileDensity_weighted_integral]
    have hh := mul_le_mul_of_nonneg_right (hc θ.1 θ.2).2.2 hG
    convert hh using 1 <;> ring

theorem fullProfile_tower_uniform {ι κ : Type*} [Fintype ι] [Fintype κ]
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (a₁ a₂ ak M : κ → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hbox : ∀ i y, inner i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ c₃ : 𝓢(ℝ, ℂ),
      (∀ (θ : ℝ × ℝ) (y : κ → ℝ),
        (∏ i, inner i (y i)) * frequencyTwist g₁ θ.1 (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ.2 (∑ i, a₂ i * y i) *
          EisensteinSchwartzPoisson.paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : κ → ℝ,
          twistedFullDensity inner g₁ g₂ c₃ θ ((t₁,t₂,t₃),u) *
            pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u) ∧
      (∀ (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
        Integrable (fun z : Ambient ι × Ambient κ =>
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ∧
        (1+R)^A * (∫ z : Ambient ι × Ambient κ,
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ≤
          C * (∫ p : Ambient ι, ambientWeight (towerMomentOrder J) p *
            ‖fullProfileDensity outer b₁ b₂ b₃ p‖)) := by
  obtain ⟨C,hC,hs⟩ := twistedFullDensity_uniform_separation inner g₁ g₂ Φ a₁ a₂ ak M hM hbox A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨c₃,he,hb⟩ := hs R hR
  refine ⟨c₃,he,?_⟩
  intro i j outer b₁ b₂ b₃
  have hRpow : 0 < (1+R)^A := pow_pos (by linarith) A
  let D : Ambient ι → Ambient κ → ℂ := fun p q =>
    twistedFullDensity inner g₁ g₂ c₃ (inheritedLeft i p,inheritedRight j p) q
  have hD : StronglyMeasurable (Function.uncurry D) := by
    simpa only [Function.comp_def, Function.uncurry_def, D] using
      (twistedFullDensity_joint_stronglyMeasurable inner g₁ g₂ c₃).comp_measurable
        (inheritedParameter_measurable i j)
  have hi (p : Ambient ι) : Integrable (fun q => ambientWeight J q * ‖D p q‖) :=
    fullProfileDensity_weighted_integrable inner
      (𝓕 (frequencyTwist g₁ (inheritedLeft i p)))
      (𝓕 (frequencyTwist g₂ (inheritedRight j p))) c₃ J
  have hb' (p : Ambient ι) : (∫ q, ambientWeight J q * ‖D p q‖) ≤
      (C/(1+R)^A) * ((1+‖inheritedLeft i p‖)^(J + (volume : Measure ℝ).integrablePower) *
        (1+‖inheritedRight j p‖)^(J + (volume : Measure ℝ).integrablePower)) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hRpow).mpr
    simpa only [mul_comm] using hb (inheritedLeft i p,inheritedRight j p)
  have hout := fullProfileDensity_weighted_integrable outer b₁ b₂ b₃ (towerMomentOrder J)
  have hB := (fullProfileDensity_continuous outer b₁ b₂ b₃).stronglyMeasurable
  have hi' := conditional_tower_integrable i j J _ (C/(1+R)^A)
    (div_nonneg hC hRpow.le) _ hB D hD hi hb' hout
  have hb'' := conditional_tower_bound i j J _ (C/(1+R)^A)
    (div_nonneg hC hRpow.le) _ hB D hD hi hb' hout
  refine ⟨hi',?_⟩
  have hh := mul_le_mul_of_nonneg_left hb'' hRpow.le
  have hcancel (x : ℝ) : (1+R)^A * (C/(1+R)^A*x) = C*x := by
    field_simp [ne_of_gt hRpow]
  rw [hcancel] at hh
  simpa only [towerDensity, D, towerMomentOrder] using hh

def twistedPositiveSource (W : ℝ → ℂ) (θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x) * W x

theorem first_second_profile_tower
    (W₁ W₂ U₁ U₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsW₁ : Function.support W₁ ⊆ Set.Icc a b) (hsW₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hsU₁ : Function.support U₁ ⊆ Set.Icc a b) (hsU₂ : Function.support U₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (hU₁ : ContDiff ℝ ∞ U₁) (hU₂ : ContDiff ℝ ∞ U₂)
    (Φ Ψ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (T : Fin 6 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hVS : ∀ i, HasCompactSupport (V i))
    (hT : ∀ i, ContDiff ℝ ∞ (T i)) (hTS : ∀ i, HasCompactSupport (T i))
    (MV : Fin 9 → ℝ) (MT : Fin 6 → ℝ)
    (hMV : ∀ i, 0 ≤ MV i) (hMT : ∀ i, 0 ≤ MT i)
    (hVbox : ∀ i y, V i y ≠ 0 → |y| ≤ MV i)
    (hTbox : ∀ i y, T i y ≠ 0 → |y| ≤ MT i) (A₁ A₂ J : ℕ) :
    let G := firstRootSchwartz V hV hVS
    let H := secondRootSchwartz T hT hTS
    let g₁ := CubicReflectionKernel.logSchwartz U₁ a b ha hsU₁ hU₁
    let g₂ := CubicReflectionKernel.logSchwartz U₂ a b ha hsU₂ hU₂
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 < R₁ → 0 < R₂ → ∃ b₃ c₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ V R₁ y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 9 → ℝ,
          fullProfileDensity G b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope
              (t₁,t₂,t₃) u i) (y i))) ∧
      (∀ (θ : ℝ × ℝ) (y : Fin 6 → ℝ),
        secondPoissonProfile (twistedPositiveSource U₁ θ.1)
          (twistedPositiveSource U₂ θ.2) Ψ T R₂ y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
          twistedFullDensity H g₁ g₂ c₃ θ ((t₁,t₂,t₃),u) *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y (t₁,t₂,t₃) u) ∧
      Integrable (fun z : Ambient (Fin 9) × Ambient (Fin 6) =>
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖towerDensity 7 8 G b₁ b₂ b₃ H g₁ g₂ c₃ z‖) ∧
      (1+R₁)^A₁ * (1+R₂)^A₂ *
        (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖towerDensity 7 8 G b₁ b₂ b₃ H g₁ g₂ c₃ z‖) ≤ C := by
  dsimp only
  let G := firstRootSchwartz V hV hVS
  let H := secondRootSchwartz T hT hTS
  let g₁ := CubicReflectionKernel.logSchwartz U₁ a b ha hsU₁ hU₁
  let g₂ := CubicReflectionKernel.logSchwartz U₂ a b ha hsU₂ hU₂
  obtain ⟨b₁,b₂,C₁,hC₁,hfirst⟩ := first_full_profile_common_measure
    W₁ W₂ a b ha hsW₁ hsW₂ hW₁ hW₂ Φ V MV hV hVS hMV hVbox A₁ (towerMomentOrder J)
  have hbox : ∀ i y, H i y ≠ 0 → |y| ≤ MT i := by
    intro i y hy
    change secondRootWindows T i y ≠ 0 at hy
    fin_cases i <;> apply hTbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  obtain ⟨C₂,hC₂,hsecond⟩ := fullProfile_tower_uniform (ι := Fin 9)
    H g₁ g₂ Ψ secondLeftSlope secondRightSlope secondKernelSlope MT hMT hbox A₂ J
  refine ⟨b₁,b₂,C₂*C₁,mul_nonneg hC₂ hC₁,?_⟩
  intro R₁ R₂ hR₁ hR₂
  obtain ⟨b₃,he₁,hi₁,hb₁⟩ := hfirst R₁ hR₁
  obtain ⟨c₃,he₂,htower⟩ := hsecond R₂ hR₂
  have ht := htower 7 8 G b₁ b₂ b₃
  refine ⟨b₃,c₃,he₁,?_,ht.1,?_⟩
  · intro θ y
    simpa only [secondPoissonProfile, twistedPositiveSource, Real.log_exp,
      frequencyTwist_apply, g₁, g₂, CubicReflectionKernel.logSchwartz_apply,
      H, secondRootSchwartz, rootSchwartz_apply] using he₂ θ y
  · have hh := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ (1+R₁)^A₁ by positivity)
    have hh' := mul_le_mul_of_nonneg_left hb₁ hC₂
    calc
      _ = (1+R₁)^A₁ * ((1+R₂)^A₂ *
          (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
            ambientWeight J z.1 * ambientWeight J z.2 *
              ‖towerDensity 7 8 G b₁ b₂ b₃ H g₁ g₂ c₃ z‖)) := by ring
      _ ≤ (1+R₁)^A₁ * (C₂ * (∫ p : Ambient (Fin 9),
          ambientWeight (towerMomentOrder J) p * ‖fullProfileDensity G b₁ b₂ b₃ p‖)) := hh
      _ ≤ C₂*C₁ := by
        simpa only [ambientWeight, tripleHeight, coordinateHeight, G, mul_assoc,
          mul_left_comm, mul_comm] using hh'

end
end SevenEighths.InverseAmbientProfileTower

end OAI

end Source2341

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialClippedColumns.lean; sha256: 1ece818208c68fc5d43e20cc861e985cfbd068ac579a6630ec2661254ddf23ce -/
section Source2342
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open SevenEighths.InverseMoment
namespace SevenEighths.InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

def clippedTest (w : ℝ → ℂ) (c h : ℝ) : ℝ → ℂ :=
  childLogTest (fun x => w (c*x)) h

theorem clippedTest_eq_source (w : ℝ → ℂ) (c h x : ℝ) :
    clippedTest w c h x = InverseInitialProfile.clippedSource w c h x := by
  unfold clippedTest childLogTest InverseInitialProfile.clippedSource
  ring

theorem child_test_clipping (w : ℝ → ℂ) {Z q : ℝ} (hZ : 0 < Z) (hq : 0 < q)
    (N h : ℝ) :
    childLogTest w h (q/Z^N) = logPhase h (Real.log (Z^(max 0 N-N))) *
      clippedTest w (Z^(max 0 N-N)) h (q/Z^(max 0 N)) := by
  rw [clippedTest_eq_source]
  simpa only [childLogTest,mul_comm] using
    InverseInitialProfile.clipped_column_source_identity w hZ hq N h

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def freshColumns (pool : Finset ι) (w : ℝ → ℂ) (X : ℝ) : Finset (Finset ι) :=
  pool.powerset.filter (fun U => w (primeProductNorm p U/X) ≠ 0)

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem mem_freshColumns (pool : Finset ι) (w : ℝ → ℂ) (X : ℝ) (U : Finset ι) :
    U ∈ freshColumns p pool w X ↔ U ⊆ pool ∧ w (primeProductNorm p U/X) ≠ 0 := by
  simp [freshColumns]

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_clipping_range (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  obtain ⟨U,hU⟩ := hn
  exact InverseClippingProfiles.clipping_ratio_of_column_witness w Z N
    (primeProductNorm p U) a b hZ (primeProductNorm_ge_one p hp U) hb hw
    ((mem_freshColumns p pool w (Z^N) U).mp hU).2

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_initial_clipping_shift (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N η : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty)
    (hthreshold : Real.log b ≤ 3*η*Real.log Z) :
    0 ≤ max 0 N-N ∧ max 0 N-N ≤ 3*η := by
  have hc := freshColumns_clipping_range p hp pool w a b Z N hZ hb hw hn
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hz _) hc.2
  rw [Real.log_rpow hz] at hl
  refine ⟨sub_nonneg.mpr (le_max_right _ _), ?_⟩
  exact (mul_le_mul_iff_left₀ (Real.log_pos hZ)).mp (hl.trans hthreshold)

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem clippedTest_support_of_freshColumns (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N h : ℝ) (ha : 0 < a) (hb : 1 ≤ b) (hZ : 1 < Z)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty) :
    Function.support (clippedTest w (Z^(max 0 N-N)) h) ⊆ Set.Icc (a/b) b := by
  obtain ⟨hc,hcb⟩ := freshColumns_clipping_range p hp pool w a b Z N hZ hb hw hn
  have hs := InverseClippingProfiles.clipped_positive_support w a b _ ha hc hcb hw
  intro x hx
  exact hs (mul_ne_zero_iff.mp hx).1

theorem canonical_row_zero_of_freshColumns_empty
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) (X h : ℝ) (he : freshColumns p pool w X = ∅) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) X = 0 := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_eq_zero
  intro U hU
  have hw : w (primeProductNorm p U/X) = 0 := by
    by_contra hw
    have hu : U ∈ freshColumns p pool w X := Finset.mem_filter.mpr ⟨hU,hw⟩
    rw [he] at hu
    exact Finset.notMem_empty U hu
  simp only [secondChildColumn,childLogTest,hw,zero_mul,mul_zero]

theorem canonical_row_nonzero_freshColumns
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) (X h : ℝ)
    (hn : finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) X ≠ 0) : (freshColumns p pool w X).Nonempty := by
  by_contra he
  exact hn (canonical_row_zero_of_freshColumns_empty p hp hcop hg pool Ψ m f k
    slots lists a w X h (Finset.not_nonempty_iff_eq_empty.mp he))

theorem canonical_row_clipping
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N) =
      logPhase h (Real.log (Z^(max 0 N-N))) *
        finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
          (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [secondChildColumn]
  rw [child_test_clipping w hZ (primeProductNorm_pos p hp U) N h]
  ring

theorem canonical_row_clipping_norm
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N)‖ =
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N))‖ := by
  rw [canonical_row_clipping p hp hcop hg pool Ψ m f k slots lists a w hZ N h,
    norm_mul,logPhase_norm,one_mul]

def columnEnergy (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator f) k
      slots lists a W X‖^2

theorem columnEnergy_clipping
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest w h) (Z^N) =
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) := by
  unfold columnEnergy
  simp_rw [canonical_row_clipping_norm p hp hcop hg pool Ψ m _ _ slots lists a w hZ N h]

theorem canonical_pair_clipping
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (w₁ w₂ : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (N h₁ h₂ : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
      (childLogTest w₁ h₁) (Z^N) *
    star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
      (childLogTest w₂ (-h₂)) (Z^N)) =
    logPhase (h₁+h₂) (Real.log (Z^(max 0 N-N))) *
      (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
        (clippedTest w₁ (Z^(max 0 N-N)) h₁) (Z^(max 0 N)) *
      star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
        (clippedTest w₂ (Z^(max 0 N-N)) (-h₂)) (Z^(max 0 N)))) := by
  rw [canonical_row_clipping p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁ w₁ hZ,
    canonical_row_clipping p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂ w₂ hZ]
  simp only [star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,
    logPhase_add_frequency]
  ring

theorem canonical_pair_clipping_left_conjugate
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (w₁ w₂ : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (N h₁ h₂ : ℝ) :
    star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
      (childLogTest w₁ (-h₁)) (Z^N)) *
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
      (childLogTest w₂ h₂) (Z^N) =
    logPhase (h₁+h₂) (Real.log (Z^(max 0 N-N))) *
      (star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
        (clippedTest w₁ (Z^(max 0 N-N)) (-h₁)) (Z^(max 0 N))) *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
        (clippedTest w₂ (Z^(max 0 N-N)) h₂) (Z^(max 0 N))) := by
  rw [canonical_row_clipping p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁ w₁ hZ,
    canonical_row_clipping p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂ w₂ hZ]
  simp only [star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,
    logPhase_add_frequency]
  ring

def normalizedColumnEnergy (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X Z F : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖((Z^(-F/2) : ℝ) : ℂ) *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator f) k
        slots lists a W X‖^2

theorem columnEnergy_normalization
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X : ℝ) {Z : ℝ} (hZ : 0 < Z) (F : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X =
      Z^F * normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a
        labels rows D W X Z F := by
  have hr : Z^F * (Z^(-F/2))^2 = 1 := by
    rw [← Real.rpow_mul_natCast hZ.le, ← Real.rpow_add hZ]
    rw [show F+(-F/2)*(2:ℕ) = 0 by ring, Real.rpow_zero]
  unfold columnEnergy normalizedColumnEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [← mul_assoc, mul_comm (Z^F) (D f), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hZ _),mul_pow,← mul_assoc,hr,one_mul]

theorem initial_columnEnergy_clipping_normalized
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N V h : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest w h) (Z^N) =
      Z^(max 0 N+V) * normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a
        labels rows D (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) Z (max 0 N+V) := by
  rw [columnEnergy_clipping p hp hcop hg pool Ψ m slots lists a labels rows D w hZ N h]
  exact columnEnergy_normalization p hp hcop hg pool Ψ m slots lists a labels rows D
    _ _ hZ _

end Arithmetic

def leftHeight (z : Frequency × (Fin 6 → ℝ)) : ℝ := z.2 4+z.1.1-z.1.2.2
def rightHeight (z : Frequency × (Fin 6 → ℝ)) : ℝ := z.2 5+z.1.2.1-z.1.2.2

theorem leftHeight_eq (z : Frequency × (Fin 6 → ℝ)) :
    leftHeight z = profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2 4 := by
  simp [leftHeight,profileHeight,secondLeftSlope,secondRightSlope,secondKernelSlope]
  ring

theorem rightHeight_eq (z : Frequency × (Fin 6 → ℝ)) :
    rightHeight z = profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2 5 := by
  simp [rightHeight,profileHeight,secondLeftSlope,secondRightSlope,secondKernelSlope]
  ring

def clippingPhase (c : ℝ) (z : Frequency × (Fin 6 → ℝ)) : ℂ :=
  logPhase (leftHeight z+rightHeight z) (Real.log c)

theorem clippingPhase_norm (c : ℝ) (z : Frequency × (Fin 6 → ℝ)) :
    ‖clippingPhase c z‖ = 1 := logPhase_norm _ _

theorem clippingPhase_continuous (c : ℝ) : Continuous (clippingPhase c) := by
  unfold clippingPhase leftHeight rightHeight logPhase
  fun_prop

theorem fresh_pair_mode_clipping (w₁ w₂ : ℝ → ℂ)
    {Z q₁ q₂ : ℝ} (hZ : 0 < Z) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (N : ℝ) (y : Fin 6 → ℝ) (z : Frequency × (Fin 6 → ℝ))
    (hy₁ : y 4 = Real.log (q₁/Z^N)) (hy₂ : y 5 = Real.log (q₂/Z^N)) :
    (w₁ (q₁/Z^N)*star (w₂ (q₂/Z^N))) *
      pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y z.1 z.2 =
    secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) y *
      clippingPhase (Z^(max 0 N-N)) z *
      (clippedTest w₁ (Z^(max 0 N-N)) (leftHeight z) (q₁/Z^(max 0 N)) *
      star (clippedTest w₂ (Z^(max 0 N-N)) (-rightHeight z) (q₂/Z^(max 0 N)))) := by
  rw [second_mode_split,← leftHeight_eq,← rightHeight_eq,hy₁,hy₂]
  have h1 := child_test_clipping w₁ hZ hq₁ N (leftHeight z)
  have h2 := child_test_clipping w₂ hZ hq₂ N (-rightHeight z)
  calc
    _ = secondOuterPhase
        (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) y *
        (childLogTest w₁ (leftHeight z) (q₁/Z^N) *
          star (childLogTest w₂ (-rightHeight z) (q₂/Z^N))) := by
      simp only [childLogTest,star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg]
      ring
    _ = _ := by
      rw [h1,h2]
      simp only [clippingPhase,star_mul,SecondPassIntegration.logPhase_conjugate,
        neg_neg,logPhase_add_frequency]
      ring

theorem child_height_moment_bound (K : ℕ) (z : Frequency × (Fin 6 → ℝ)) :
    (1+‖leftHeight z‖)^K * (1+‖rightHeight z‖)^K ≤
      tripleHeight (2*K) z.1 * coordinateHeight (2*K) z.2 := by
  have hh := InverseAmbientProfileTower.inherited_pair_weight_bound 4 5 0 K z
  simpa only [InverseAmbientProfileTower.ambientWeight,
    InverseAmbientProfileTower.inheritedLeft,InverseAmbientProfileTower.inheritedRight,
    leftHeight,rightHeight,norm_neg,pow_zero,Finset.prod_const_one,
    mul_one,one_mul,zero_add,tripleHeight,coordinateHeight] using hh

def outerCutoff (ψ : Fin 4 → ℝ → ℂ) (x : Fin 6 → ℝ) : ℂ :=
  ψ 0 (x 0)*ψ 1 (x 1)*ψ 2 (x 2)*ψ 3 (x 3)

def retainedCutoffs (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ) : Fin 6 → ℝ → ℂ :=
  ![ψ 0,ψ 1,ψ 2,ψ 3,w₁,w₂]

theorem retainedCutoffs_nonzero (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ)
    (x : Fin 6 → ℝ) (ho : outerCutoff ψ x ≠ 0)
    (h₁ : w₁ (x 4) ≠ 0) (h₂ : w₂ (x 5) ≠ 0) :
    ∀ i, retainedCutoffs ψ w₁ w₂ i (x i) ≠ 0 := by
  have h := mul_ne_zero_iff.mp ho
  have h' := mul_ne_zero_iff.mp h.1
  have h'' := mul_ne_zero_iff.mp h'.1
  intro i
  fin_cases i <;> simp only [retainedCutoffs]
  · exact h''.1
  · exact h''.2
  · exact h'.2
  · exact h.2
  · exact h₁
  · exact h₂

theorem larger_windows_one (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ)
    (Ω : Fin 6 → ℝ → ℂ)
    (hΩ : ∀ i x, retainedCutoffs ψ w₁ w₂ i x ≠ 0 → Ω i x = 1)
    (x : Fin 6 → ℝ) (hx : ∀ i, 0 < x i) (ho : outerCutoff ψ x ≠ 0)
    (h₁ : w₁ (x 4) ≠ 0) (h₂ : w₂ (x 5) ≠ 0) :
    ∀ i, Ω i (Real.exp (Real.log (x i))) = 1 := by
  intro i
  rw [Real.exp_log (hx i)]
  exact hΩ i (x i) (retainedCutoffs_nonzero ψ w₁ w₂ x ho h₁ h₂ i)

theorem retained_physical_kernel_restore
    (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (ψ : Fin 4 → ℝ → ℂ) (Ω : Fin 6 → ℝ → ℂ)
    (a b A₀ B₀ A₂ B₂ : ℝ) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂)
    (hW₁ : Function.support W₁ ⊆ Set.Icc a b)
    (hW₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hψ₀ : ∀ x, ψ 0 x ≠ 0 → x ∈ Set.Icc A₀ B₀)
    (hψ₂ : ∀ x, ψ 2 x ≠ 0 → x ∈ Set.Icc A₂ B₂)
    (hw₁ : ∀ x ∈ Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)), w₁ x = 1)
    (hw₂ : ∀ x ∈ Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)), w₂ x = 1)
    (hΩ : ∀ i x, retainedCutoffs ψ w₁ w₂ i x ≠ 0 → Ω i x = 1)
    {Z : ℝ} (hZ : 0 < Z) (D B v m θ H η : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    let x := InverseInitialProfile.relativeNorm q Z D B v θ H
    outerCutoff ψ x * InverseInitialProfile.physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(InverseInitialProfile.prefactorCenter m D B θ+3*η) : ℝ) *
        outerCutoff ψ x * (w₁ (x 4)*w₂ (x 5)) *
        InverseInitialProfile.normalizedProfile W₁ W₂ Φ (fun i y => Ω i (Real.exp y))
          (Z^(InverseInitialProfile.radialCenter m H θ D B)) (η*Real.log Z)
          (InverseInitialProfile.relativeLog q Z D B v θ H) := by
  dsimp only
  let x := InverseInitialProfile.relativeNorm q Z D B v θ H
  have hx : ∀ i, 0 < x i := InverseInitialProfile.relativeNorm_pos q hq hZ D B v θ H
  by_cases ho : outerCutoff ψ x = 0
  · change outerCutoff ψ x * _ = _ * outerCutoff ψ x * _ * _
    simp only [ho,zero_mul,mul_zero]
  have hc : ψ 0 (x 0) ≠ 0 := ((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ho).1).1 |> mul_ne_zero_iff.mp).1
  have hs : ψ 2 (x 2) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ho).1).2
  have h1 : W₁ (x 0*x 2*x 4) ≠ 0 → w₁ (x 4) = 1 :=
    fresh_window_eq_one W₁ w₁ a b A₀ B₀ A₂ B₂ (x 0) (x 2) (x 4)
      hW₁ hA₀ hA₂ (hψ₀ _ hc) (hψ₂ _ hs) (hx 4).le hw₁
  have h2 : W₂ (x 0*x 2*x 5) ≠ 0 → w₂ (x 5) = 1 :=
    fresh_window_eq_one W₂ w₂ a b A₀ B₀ A₂ B₂ (x 0) (x 2) (x 5)
      hW₂ hA₀ hA₂ (hψ₀ _ hc) (hψ₂ _ hs) (hx 5).le hw₂
  have hcut : w₁ (x 4) ≠ 0 → w₂ (x 5) ≠ 0 →
      ∀ i, Ω i (Real.exp (InverseInitialProfile.relativeLog q Z D B v θ H i)) = 1 := by
    intro hleft hright
    exact larger_windows_one ψ w₁ w₂ Ω hΩ x hx ho hleft hright
  have he := InverseInitialProfile.initial_kernel_restore W₁ W₂ w₁ w₂ Φ
    (fun i y => Ω i (Real.exp y)) hZ D B v m θ H η q hq h1 h2 hcut
  rw [he]
  ring

end SevenEighths.InverseInitialClippedColumns

end

end OAI

end Source2342

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCaller.lean; sha256: 7581b5e2f24d608089bfbc916db0558a2b14fe8e48eacd9ac8d5bfd8b16b3ca8 -/
section Source2343
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
namespace SevenEighths.InverseInitialEnergyCaller
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_sector_energy {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (lists : Fin J → Finset ι) (a : Fin J → ι → ℂ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hterm : ∀ x ∈ S, assignedTerm lists a (x.common ∪ x.overlap) x.assigned ≠ 0)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (F : InitialChild → ℂ) :
    (∑ x ∈ S, ‖F (initialChild (toTuple p (sectorSource u x)))‖^2) ≤
      ∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) *
          ∑ k ∈ rows, ‖F (t,f,k)‖^2 := by
  let T := S.image (fun x => toTuple p (sectorSource u x))
  have hvalid : ∀ y ∈ T, InitialSourceValid y := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact actual_source_valid p hp hpr (sectorSource u x) (hdiv x hx) lists a (hterm x hx)
  have hc : ∀ y ∈ T, (initialChild y).2.1 ∈ labels ∧ (initialChild y).2.2 ∈ rows := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hchild x hx
  have he := initial_energy_projection T hvalid labels rows hlabels hc
    (fun _ => 1) (fun _ _ => le_rfl) F
  simp only [one_mul] at he
  rw [show initialQuotientSet T = quotientSet p S from
    quotientSet_eq_initial p hp S u hdiv] at he
  have hs : (∑ y ∈ T, ‖F (initialChild y)‖^2) =
      ∑ x ∈ S, ‖F (initialChild (toTuple p (sectorSource u x)))‖^2 := by
    exact Finset.sum_image (fun x _ y _ he => sectorSource_injective u (toTuple_injective p hinj he))
  rw [hs] at he
  exact he

include hp in

theorem actual_sector_signed_pair {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (lists : Fin J → Finset ι) (a : Fin J → ι → ℂ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hterm : ∀ x ∈ S, assignedTerm lists a (x.common ∪ x.overlap) x.assigned ≠ 0)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (c : Source (ι:=ι) J → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hc : ∀ x ∈ S, ‖c x‖ ≤ A) (F G : InitialChild → ℂ) :
    ‖∑ x ∈ S, c x * star (F (initialChild (toTuple p (sectorSource u x)))) *
        G (initialChild (toTuple p (sectorSource u x)))‖ ≤
      A * (Real.sqrt (∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) * ∑ k ∈ rows, ‖F (t,f,k)‖^2) *
        Real.sqrt (∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) * ∑ k ∈ rows, ‖G (t,f,k)‖^2)) := by
  let child := fun x : Source (ι:=ι) J => initialChild (toTuple p (sectorSource u x))
  have hF := actual_sector_energy p hp hinj hpr S u lists a hdiv hterm labels rows hlabels hchild F
  have hG := actual_sector_energy p hp hinj hpr S u lists a hdiv hterm labels rows hlabels hchild G
  calc
    _ ≤ ∑ x ∈ S, ‖c x * star (F (child x)) * G (child x)‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ S, A * (‖F (child x)‖ * ‖G (child x)‖) := by
      apply Finset.sum_le_sum
      intro x hx
      simp only [norm_mul, norm_star]
      nlinarith [mul_le_mul_of_nonneg_right (hc x hx)
        (mul_nonneg (norm_nonneg (F (child x))) (norm_nonneg (G (child x))))]
    _ = A * ∑ x ∈ S, ‖F (child x)‖ * ‖G (child x)‖ := by rw [Finset.mul_sum]
    _ ≤ A * (Real.sqrt (∑ x ∈ S, ‖F (child x)‖^2) *
        Real.sqrt (∑ x ∈ S, ‖G (child x)‖^2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt S _ _) hA
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA

end SevenEighths.InverseInitialEnergyCaller

end

end OAI

end Source2343

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerCanonical.lean; sha256: fbba842e7eec4b6f3bec1bd627a76de55f2faaf814578165f7f7b85a85ddc7a6 -/
section Source2344
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
namespace SevenEighths.InverseInitialEnergyCallerCanonical
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def child (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (c : InitialChild) : ℂ :=
  finiteCanonicalMarkedRow p hp hcop hg pool Ψ (j*primaryGenerator c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a W X

omit [DecidableEq σ] in
theorem energy_eq_normalized (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (J : ℕ) (T : Finset (Ideal Eis))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    {Z : ℝ} (hZ : 0<Z) (F : ℝ) :
    (∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      ∑ f ∈ labels, ((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k ∈ rows, ‖child p hp hcop hg pool Ψ j slots lists a W X (t,f,k)‖^2) =
    Z^F * ∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      normalizedColumnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t)
        slots lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X Z F := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  change ((idealDivisors t).card:ℝ)^J *
    columnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t) slots lists a
      labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X = _
  rw [columnEnergy_normalization p hp hcop hg pool Ψ (j*primaryGenerator t)
    slots lists a labels rows _ W X hZ F]
  ring

omit [DecidableEq σ] in
theorem energy_le_moment (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (J : ℕ) (T : Finset (Ideal Eis))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    {Z : ℝ} (hZ : 0<Z) (F B : ℝ)
    (hmoment : ∀ t ∈ T,
      normalizedColumnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t)
        slots lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X Z F ≤ B) :
    (∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      ∑ f ∈ labels, ((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k ∈ rows, ‖child p hp hcop hg pool Ψ j slots lists a W X (t,f,k)‖^2) ≤
    (Z^F * ∑ t ∈ T, ((idealDivisors t).card:ℝ)^J) * B := by
  rw [energy_eq_normalized p hp hcop hg pool Ψ j slots lists a W X J T labels rows hZ F,
    mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZ.le _)
  exact Finset.sum_le_sum fun t ht =>
    mul_le_mul_of_nonneg_left (hmoment t ht) (by positivity)

theorem sqrt_pair_mass (M B₁ B₂ : ℝ) (hM : 0≤M) :
    Real.sqrt (M*B₁)*Real.sqrt (M*B₂) = M*(Real.sqrt B₁*Real.sqrt B₂) := by
  rw [Real.sqrt_mul hM,Real.sqrt_mul hM]
  calc
    _ = (Real.sqrt M*Real.sqrt M)*(Real.sqrt B₁*Real.sqrt B₂) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hM]

omit [DecidableEq σ] in
theorem signed_canonical_pair_moment {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (assignedLists : Fin J → Finset ι) (assignedCoeff : Fin J → ι → ℂ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hterm : ∀ x ∈ S, assignedTerm assignedLists assignedCoeff
      (x.common ∪ x.overlap) x.assigned ≠ 0)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (c : Source (ι:=ι) J → ℂ) (A : ℝ) (hA : 0≤A)
    (hc : ∀ x ∈ S, ‖c x‖≤A)
    (pool : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (j : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    {Z : ℝ} (hZ : 0<Z) (F B : ℝ) (hB : 0≤B)
    (hmoment₁ : ∀ t ∈ quotientSet p S,
      normalizedColumnEnergy p hp hcop hg pool Ψ₁ (j*primaryGenerator t)
        slots₁ lists₁ a₁ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W₁ X₁ Z F ≤ B)
    (hmoment₂ : ∀ t ∈ quotientSet p S,
      normalizedColumnEnergy p hp hcop hg pool Ψ₂ (j*primaryGenerator t)
        slots₂ lists₂ a₂ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W₂ X₂ Z F ≤ B) :
    ‖∑ x ∈ S, c x *
      star (child p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁
        (initialChild (toTuple p (sectorSource u x)))) *
      child p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂
        (initialChild (toTuple p (sectorSource u x)))‖ ≤
      A * (Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J) * B := by
  have h₁ := energy_le_moment p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁
    J (quotientSet p S) labels rows hZ F B hmoment₁
  have h₂ := energy_le_moment p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂
    J (quotientSet p S) labels rows hZ F B hmoment₂
  apply (InverseInitialEnergyCaller.actual_sector_signed_pair p hp hinj hpr S u
    assignedLists assignedCoeff hdiv hterm labels rows hlabels hchild c A hA hc
    (child p hp hcop hg pool Ψ₁ j slots₁ lists₁ a₁ W₁ X₁)
    (child p hp hcop hg pool Ψ₂ j slots₂ lists₂ a₂ W₂ X₂)).trans
  calc
    _ ≤ A * (Real.sqrt ((Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J)*B) *
        Real.sqrt ((Z^F * ∑ t ∈ quotientSet p S, ((idealDivisors t).card:ℝ)^J)*B)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt h₁)
        (Real.sqrt_le_sqrt h₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA
    _ = _ := by
      rw [Real.mul_self_sqrt (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _)
        (Finset.sum_nonneg fun t ht=>by positivity)) hB)]
      ring

end SevenEighths.InverseInitialEnergyCallerCanonical

end

end OAI

end Source2344

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerFamily.lean; sha256: 713cb717e69c8288b8ad26d80a02ceab00ac6dd820498adb934f8ea975c472a7 -/
section Source2345
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialEnergyCallerFamily
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem common_killed (G E V : Finset ι) (_hE : E⊆G) (j d t : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∀ i∈G,(j*t)*(d*∏ k∈V,p k)∈Ideal.span {p i} := by
  intro i hi
  by_cases hiE : i∈E
  · have he : d∈Ideal.span {p i} := by
      apply (Ideal.dvd_iff_le.mp (source_prime_dvd p E i hiE))
      rw [←hd]
      exact Ideal.subset_span (Set.mem_singleton d)
    have hh := (Ideal.span {p i}).mul_mem_left ((j*t)*(∏ k∈V,p k)) he
    convert hh using 1 ; ring
  · have hit : i∈G\E := Finset.mem_sdiff.mpr ⟨hi,hiE⟩
    have he : t∈Ideal.span {p i} := by
      apply (Ideal.dvd_iff_le.mp (source_prime_dvd p (G\E) i hit))
      rw [←ht]
      exact Ideal.subset_span (Set.mem_singleton t)
    have hh := (Ideal.span {p i}).mul_mem_left (j*(d*∏ k∈V,p k)) he
    convert hh using 1 ; ring

theorem marked_child_original_lists (F G E V : Finset ι) (hE : E⊆G)
    (Ψ : Eis →* ℂ) (j d t h : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E))
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    (∑ N∈(F\V).powerset,
      secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>primeMark slots lists a (G∪V∪U)*W (primeProductNorm p (V∪U)/X)) N) =
    ∑ J∈slots.powerset,primeMark J lists a (G∪V)*
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (slots\J) lists a W (X/primeProductNorm p V) := by
  rw [initial_marked_child p hp hcop hg F V G Ψ j t d h slots lists a W X]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteCanonicalMarkedRow_restore_lists p hp hcop hg F G Ψ (j*t)
    (d*∏ i∈V,p i) (d*h) (slots\J) lists a W (X/primeProductNorm p V)
    (common_killed p G E V hE j d t hd ht)]

omit [DecidableEq σ] in
theorem normalized_child_uniform
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (G E V : Finset ι) (d t : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∃ u : Eisˣ, d=(u:Eis)*primaryGenerator (sourceIdeal p E) ∧
      ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis)
        (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ),
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*primaryGenerator (sourceIdeal p (G\E)))
        (primaryGenerator (sourceIdeal p E*sourceIdeal p V))
        (primaryGenerator (sourceIdeal p E)*((u:Eis)^5*h)) slots lists a W X := by
  have hgen : primaryGenerator (sourceIdeal p E)≠0 := by
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  obtain ⟨u,hu⟩ := generator_eq_unit_primary (sourceIdeal p E) d hd hgen
  refine ⟨u,hu,?_⟩
  intro F Ψ j h slots lists a W X
  obtain ⟨v,hv,hcol⟩ := initial_poisson_child_normalized p hp hcop hg hpr G E V Ψ j d t h hd ht
  have huv : v=u := by
    apply Units.val_injective
    exact mul_right_cancel₀ hgen (hv.symm.trans hu)
  subst v
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro N hN
  exact hcol _ N

theorem fresh_initial_split_fixed_family
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (G E V : Finset ι) (hE : E⊆G) (d t : Eis)
    (hd : Ideal.span {d}=sourceIdeal p E) (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∃ u : Eisˣ, d=(u:Eis)*primaryGenerator (sourceIdeal p E) ∧
      ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis)
        (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ),
      (∑ N∈(F\V).powerset,
        secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
          (fun U=>primeMark slots lists a (G∪V∪U)*W (primeProductNorm p U/X)) N) =
      ∑ J∈slots.powerset,primeMark J lists a (G∪V)*
        finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*primaryGenerator (sourceIdeal p (G\E)))
          (primaryGenerator (sourceIdeal p E*sourceIdeal p V))
          (primaryGenerator (sourceIdeal p E)*((u:Eis)^5*h)) (slots\J) lists a W X := by
  obtain ⟨u,hu,hnorm⟩ := normalized_child_uniform p hp hcop hg hpr G E V d t hd ht (σ:=σ)
  refine ⟨u,hu,?_⟩
  intro F Ψ j h slots lists a W X
  have hV : primeProductNorm p V≠0 := (primeProductNorm_pos p hp V).ne'
  have hx : primeProductNorm p V*X/primeProductNorm p V=X := by
    field_simp
  have he := marked_child_original_lists p hp hcop hg F G E V hE Ψ j d t h hd ht
    slots lists a W (primeProductNorm p V*X)
  rw [hx] at he
  calc
    _ = ∑ N∈(F\V).powerset,
        secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
          (fun U=>primeMark slots lists a (G∪V∪U)*
            W (primeProductNorm p (V∪U)/(primeProductNorm p V*X))) N := by
      apply Finset.sum_congr rfl
      intro N hN
      have hdN : Disjoint V N := Finset.disjoint_left.mpr (by
        intro i hiV hiN
        exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hiN)).2 hiV)
      simp only [secondChildColumn]
      rw [primeProductNorm_union p V N hdN]
      rw [mul_div_mul_left _ _ hV]
    _ = _ := by
      rw [he]
      apply Finset.sum_congr rfl
      intro J hJ
      rw [hnorm F Ψ j h (slots\J) lists a W X]

end SevenEighths.InverseInitialEnergyCallerFamily

end

end OAI

end Source2345

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialOverlap.lean; sha256: 3e08d000494a74ed90649cd77b5dd0da496f419588f1dbde00ba4bb42eb18c33 -/
section Source2346
namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum
open UniqueFactorizationMonoid

namespace SevenEighths.InverseInitialOverlap

abbrev O := ActualEisensteinCubic.O

def residual (P j : Ideal O) : Ideal O := idealQuotient j P

def column (P j n : Ideal O) : Ideal O := idealQuotient j n * residual P j

def reconstruct (P j c : Ideal O) : Ideal O := j * idealQuotient (residual P j) c

def original (S : Finset (Ideal O)) (P j : Ideal O) : Finset (Ideal O) :=
  S.filter fun n => Squarefree n ∧ gcd n P = j

def columns (S : Finset (Ideal O)) (P j : Ideal O) : Finset (Ideal O) :=
  (original S P j).image (column P j)

theorem mem_original {S : Finset (Ideal O)} {P j n : Ideal O} :
    n ∈ original S P j ↔ n ∈ S ∧ Squarefree n ∧ gcd n P = j := by
  simp only [original, Finset.mem_filter]

theorem residual_mul {P j : Ideal O} (hj : j ∣ P) : j * residual P j = P :=
  idealQuotient_mul hj

theorem residual_squarefree {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) :
    Squarefree (residual P j) :=
  hP.squarefree_of_dvd (idealQuotient_dvd hj)

theorem quotient_mul_cancel {D H : Ideal O} (hD : D ≠ 0) :
    idealQuotient D (D * H) = H :=
  mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right D H))

theorem column_properties {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hn : Squarefree n) (hg : gcd n P = j) :
    Squarefree (column P j n) ∧ IsCoprime (column P j n) j ∧
      residual P j ∣ column P j n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hHP : IsCoprime (idealQuotient j n) P := by
    rw [← hg]
    exact squarefree_quotient_gcd_coprime n P hn
  have hHj := hHP.mono (dvd_refl _) hj
  have hHP0 := hHP.mono (dvd_refl _) (idealQuotient_dvd hj)
  have hJP0 : IsCoprime j (residual P j) :=
    ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (j * residual P j) by rw [residual_mul hj]; exact hP)).1
  refine ⟨squarefree_mul_iff.mpr ⟨hHP0.isRelPrime,
    hn.squarefree_of_dvd (idealQuotient_dvd hjn), residual_squarefree hP hj⟩,
    hHj.mul_left hJP0.symm, dvd_mul_left _ _⟩

theorem reconstruct_column {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hg : gcd n P = j) : reconstruct P j (column P j n) = n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hP0 := (residual_squarefree hP hj).ne_zero
  unfold reconstruct column
  rw [mul_comm (idealQuotient j n), quotient_mul_cancel hP0, idealQuotient_mul hjn]

theorem reconstruct_properties {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hc : Squarefree c) (hcj : IsCoprime c j) (hPc : residual P j ∣ c) :
    Squarefree (reconstruct P j c) ∧ gcd (reconstruct P j c) P = j := by
  let H := idealQuotient (residual P j) c
  have hHc : H ∣ c := idealQuotient_dvd hPc
  have hHj : IsCoprime H j := hcj.mono hHc (dvd_refl _)
  have hHP0 : IsCoprime H (residual P j) :=
    (ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (residual P j * H) by rw [idealQuotient_mul hPc]; exact hc)).1).symm
  have hHP : IsCoprime H P := by
    rw [← residual_mul hj]
    exact hHj.mul_right hHP0
  exact ⟨squarefree_mul_iff.mpr ⟨hHj.symm.isRelPrime,
    hP.squarefree_of_dvd hj, hc.squarefree_of_dvd hHc⟩,
    gcd_mul_of_coprime_divisor j H P hj hHP⟩

theorem column_reconstruct {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) : column P j (reconstruct P j c) = c := by
  have hj0 : j ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero hj
  unfold column reconstruct
  rw [quotient_mul_cancel hj0, mul_comm, idealQuotient_mul hPc]

theorem mem_columns {S : Finset (Ideal O)} {P j c : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) :
    c ∈ columns S P j ↔ Squarefree c ∧ IsCoprime c j ∧
      residual P j ∣ c ∧ reconstruct P j c ∈ S := by
  constructor
  · intro hc
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hnS, hn, hg⟩ := mem_original.mp hn
    obtain ⟨hcs, hcj, hPc⟩ := column_properties hP hj hn hg
    exact ⟨hcs, hcj, hPc, by rwa [reconstruct_column hP hj hg]⟩
  · rintro ⟨hc, hcj, hPc, hnS⟩
    obtain ⟨hn, hg⟩ := reconstruct_properties hP hj hc hcj hPc
    exact Finset.mem_image.mpr ⟨reconstruct P j c,
      mem_original.mpr ⟨hnS, hn, hg⟩, column_reconstruct hP hj hPc⟩

theorem column_injOn (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) :
    Set.InjOn (column P j) (original S P j) := by
  intro n hn m hm he
  have hn' := reconstruct_column hP hj (mem_original.mp hn).2.2
  have hm' := reconstruct_column hP hj (mem_original.mp hm).2.2
  rw [← hn', ← hm', he]

def overlapEquiv (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) : original S P j ≃ columns S P j where
  toFun n := ⟨column P j n, Finset.mem_image.mpr ⟨n, n.property, rfl⟩⟩
  invFun c := ⟨reconstruct P j c, by
    obtain ⟨hc, hcj, hPc, hnS⟩ := (mem_columns hP hj).mp c.property
    exact mem_original.mpr ⟨hnS, reconstruct_properties hP hj hc hcj hPc⟩⟩
  left_inv n := Subtype.ext (reconstruct_column hP hj (mem_original.mp n.property).2.2)
  right_inv c := Subtype.ext (column_reconstruct hP hj
    ((mem_columns hP hj).mp c.property).2.2.1)

theorem reconstruct_mul_residual {P j c : Ideal O} (hPc : residual P j ∣ c) :
    reconstruct P j c * residual P j = j * c := by
  unfold reconstruct
  rw [mul_assoc, mul_comm (idealQuotient _ _), idealQuotient_mul hPc]

theorem norm_reconstruct {P j c : Ideal O} (hPc : residual P j ∣ c) :
    Ideal.absNorm (reconstruct P j c) * Ideal.absNorm (residual P j) =
      Ideal.absNorm j * Ideal.absNorm c := by
  simpa only [map_mul] using congrArg Ideal.absNorm (reconstruct_mul_residual hPc)

theorem cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) (X : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / X =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c /
        ((Ideal.absNorm (residual P j) : ℝ) * X) := by
  have h0 : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hn : (Ideal.absNorm (reconstruct P j c) : ℝ) =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c / Ideal.absNorm (residual P j) := by
    apply (eq_div_iff h0).mpr
    exact_mod_cast norm_reconstruct hPc
  rw [hn, div_div]

theorem columns_filter (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (mask : Ideal O → Prop) [DecidablePred mask] :
    columns (S.filter mask) P j =
      (columns S P j).filter fun c => mask (reconstruct P j c) := by
  ext c
  simp only [mem_columns hP hj, Finset.mem_filter]
  tauto

theorem sum_reconstruct (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (F : Ideal O → ℂ) :
    (∑ n ∈ original S P j, F n) =
      ∑ c ∈ columns S P j, F (reconstruct P j c) := by
  rw [columns, Finset.sum_image (column_injOn S hP hj)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [reconstruct_column hP hj (mem_original.mp hn).2.2]

theorem coefficient_identity (ψ : Ideal O →* ℂ) {P j n : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (hn : Squarefree n) (hg : gcd n P = j) :
    (moebius n : ℂ) * ψ n * ψ P =
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2 *
        ((moebius (column P j n) : ℂ) * ψ (column P j n)) := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hH : IsCoprime (idealQuotient j n) P := by
    rw [← hg]
    exact squarefree_quotient_gcd_coprime n P hn
  have h := InverseMoment.moebius_character_overlap ψ
    (hH.mono (dvd_refl _) hj).symm.isRelPrime
    (hH.mono (dvd_refl _) (idealQuotient_dvd hj)).isRelPrime
    (residual_squarefree hP hj)
  rw [idealQuotient_mul hjn, idealQuotient_mul hj] at h
  change (moebius n : ℂ) * ψ n * ψ P = _
  rw [h]
  unfold column residual
  ring

theorem polynomial_fixed_overlap (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (ψ : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    (∑ n ∈ original S P j,
      (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / X)) =
    ((moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2) *
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
          ((Ideal.absNorm (residual P j) : ℝ) * X)) := by
  rw [sum_reconstruct S hP hj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨hcs, hcj, hPc, _⟩ := (mem_columns hP hj).mp hc
  obtain ⟨hn, hg⟩ := reconstruct_properties hP hj hcs hcj hPc
  rw [coefficient_identity ψ hP hj hn hg, column_reconstruct hP hj hPc,
    cutoff_argument hP hj hPc]
  ring

theorem sum_original_partition (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (F : Ideal O → ℂ) :
    (∑ n ∈ S.filter Squarefree, F n) =
      ∑ j ∈ idealDivisors P, ∑ n ∈ original S P j, F n := by
  have hmap : ∀ n ∈ S.filter Squarefree, gcd n P ∈ idealDivisors P := by
    intro n _
    exact (mem_idealDivisors hP.ne_zero).mpr (GCDMonoid.gcd_dvd_right _ _)
  have h := Finset.sum_fiberwise_of_maps_to hmap F
  simpa only [original, Finset.filter_filter] using h.symm

theorem polynomial_all_overlaps (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    (∑ n ∈ S.filter Squarefree,
      (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / X)) =
    ∑ j ∈ idealDivisors P,
      ((moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
            ((Ideal.absNorm (residual P j) : ℝ) * X)) := by
  rw [sum_original_partition S hP]
  apply Finset.sum_congr rfl
  intro j hj
  exact polynomial_fixed_overlap S hP ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W X

theorem scaled_cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / Z ^ r =
      (((Ideal.absNorm j : ℝ) / Z ^ G) *
        ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
        ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G)) := by
  have hnorm : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hscale : Z ^ G * Z ^ (r + z - 2 * G) = Z ^ r * Z ^ (z - G) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    ring
  rw [cutoff_argument hP hj hPc]
  rw [div_mul_div_comm, div_div_eq_mul_div]
  field_simp [hnorm, (Real.rpow_pos_of_pos hZ r).ne',
    (Real.rpow_pos_of_pos hZ G).ne',
    (Real.rpow_pos_of_pos hZ (r + z - 2 * G)).ne',
    (Real.rpow_pos_of_pos hZ (z - G)).ne']
  linear_combination ((Ideal.absNorm j : ℝ) * Ideal.absNorm c) * hscale

theorem normalization_split {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    Z ^ (-(r + z) / 2) = Z ^ (-G) * Z ^ (-(r + z - 2 * G) / 2) := by
  rw [← Real.rpow_add hZ]
  congr 1
  ring

theorem normalized_polynomial_fixed_overlap (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (ψ : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ original S P j,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
      (Z ^ (-G) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G) / 2) : ℝ) *
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((((Ideal.absNorm j : ℝ) / Z ^ G) *
          ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
          ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G))) := by
  rw [polynomial_fixed_overlap S hP hj ψ a W, normalization_split hZ r z G,
    Complex.ofReal_mul]
  have hs : (∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
          ((Ideal.absNorm (residual P j) : ℝ) * Z ^ r))) =
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((((Ideal.absNorm j : ℝ) / Z ^ G) *
          ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
          ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G))) := by
    apply Finset.sum_congr rfl
    intro c hc
    have hPc := ((mem_columns hP hj).mp hc).2.2.1
    rw [← cutoff_argument hP hj hPc, scaled_cutoff_argument hP hj hPc hZ]
  rw [hs]
  ring

theorem normalized_polynomial_all_overlaps (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal O → ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ S.filter Squarefree,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    ∑ j ∈ idealDivisors P,
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
        (Z ^ (-G j) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G j) / 2) : ℝ) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((((Ideal.absNorm j : ℝ) / Z ^ G j) *
            ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G j))) /
            ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G j))) := by
  rw [sum_original_partition S hP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact normalized_polynomial_fixed_overlap S hP
    ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W hZ r z (G j)

theorem sum_moebius_filter (S : Finset (Ideal O)) (F : Ideal O → ℂ) :
    (∑ n ∈ S, (moebius n : ℂ) * F n) =
      ∑ n ∈ S.filter Squarefree, (moebius n : ℂ) * F n := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnf
  have hns : ¬ Squarefree n := fun h => hnf (Finset.mem_filter.mpr ⟨hn, h⟩)
  simp only [moebius_of_not_squarefree hns, Int.cast_zero, zero_mul]

theorem original_normalized_polynomial (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal O → ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ S,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    ∑ j ∈ idealDivisors P,
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
        (Z ^ (-G j) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G j) / 2) : ℝ) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((((Ideal.absNorm j : ℝ) / Z ^ G j) *
            ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G j))) /
            ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G j))) := by
  have hf := sum_moebius_filter S (fun n =>
    ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r))
  simp only [← mul_assoc] at hf
  rw [hf]
  exact normalized_polynomial_all_overlaps S hP ψ a W hZ r z G

theorem overlap_coefficient_norm_le {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (ψ : Ideal O →* ℂ) (hψ : ‖ψ j‖ ≤ 1) :
    ‖(moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2‖ ≤ 1 := by
  have hjSF := hP.squarefree_of_dvd hj
  have hresSF := residual_squarefree hP hj
  simpa [norm_mul, hjSF.moebius_eq, hresSF.moebius_eq] using
    InverseMoment.overlap_scalar_norm_le hψ

end SevenEighths.InverseInitialOverlap

end

end OAI

end Source2346

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialPoissonBridge.lean; sha256: 1fa14960d39536579bb725bd657b9017e53d9a95af3e0ae6d2eab8cd895af660 -/
section Source2347
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialPoissonBridge
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge ConcreteTraceCRT EisensteinSchwartzPoisson
open UniqueFactorizationMonoid InverseInitialOverlap
local notation "Eis" => ActualEisensteinCubic.O

def rowPolynomial (F : Finset (Ideal Eis)) (A : Ideal Eis → ℂ) (u : Eis) : ℂ :=
  ∑ I ∈ F, A I * idealRowHom u I

lemma pool_positive (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I) :
    ∀ I ∈ F, I ≠ 0 := fun I hI => (hF I hI).1

lemma pool_good (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I) :
    ∀ I ∈ F, ∀ Q ∈ normalizedFactors I, goodLambda ∉ Q :=
  fun I hI Q hQ => ((hF I hI).2.2 Q hQ).1

lemma pool_char (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I)
    (q : primePool F) : ringChar (Eis ⧸ q.val) ≠ 2 := by
  obtain ⟨I,hI,hq⟩ := mem_primePool_iff.mp q.property
  exact ((hF I hI).2.2 q.val hq).2

theorem idealRowHom_eq_idealSexticRow
    (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I)
    {I : Ideal Eis} (hI : I ∈ F) (u : Eis) :
    idealRowHom u I = idealSexticRow F (pool_positive F hF) (pool_good F hF) I u := by
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  conv_lhs => rw [← idealSupport_product_eq F hI (hF I hI).2.1]
  rw [map_prod]
  change (∏ q ∈ idealSupport F I, idealRowHom u q.val) =
    ∏ q ∈ idealSupport F I, CompletedGauss.actualSextic q.val (primePool_good F (pool_good F hF) q)
      (Ideal.Quotient.mk q.val u)
  apply Finset.prod_congr rfl
  intro q hq
  exact idealRowHom_prime u q.val (primePool_good F (pool_good F hF) q)

theorem rowPolynomial_eq_finite (F : Finset (Ideal Eis))
    (hF : ∀ I ∈ F, Admissible I) (A : Ideal Eis → ℂ) (u : Eis) :
    rowPolynomial F A u = ∑ I ∈ F, A I *
      idealSexticRow F (pool_positive F hF) (pool_good F hF) I u := by
  apply Finset.sum_congr rfl
  intro I hI
  rw [idealRowHom_eq_idealSexticRow F hF hI]

theorem rowPolynomial_smoothed_summable (F : Finset (Ideal Eis))
    (hF : ∀ I ∈ F, Admissible I) (A : Ideal Eis → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y) *
      (‖rowPolynomial F A u‖^2 : ℝ)) := by
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  simpa only [rowPolynomial_eq_finite F hF A,idealSexticRow] using
    finiteSquarefreeRow_smoothed_mean_square_summable
      (fun q : primePool F => q.val) (primePool_good F (pool_good F hF))
      F (idealSupport F) A Φ Y hY

theorem rowPolynomial_smoothed_expand (F : Finset (Ideal Eis))
    (hF : ∀ I ∈ F, Admissible I) (A : Ideal Eis → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y) * (‖rowPolynomial F A u‖^2 : ℝ)) =
      ∑ I ∈ F, ∑ J ∈ F, (star (A I)*A J) *
        ∑' u : Eis, (star (idealRowHom u I)*idealRowHom u J)*Φ (‖eisEmbedding u‖^2/Y) := by
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  have he := finiteSquarefreeRow_smoothed_mean_square_expand
    (fun q : primePool F => q.val) (primePool_good F (pool_good F hF))
    F (idealSupport F) A Φ Y hY
  simp_rw [rowPolynomial_eq_finite F hF A]
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp_rw [idealRowHom_eq_idealSexticRow F hF hI, idealRowHom_eq_idealSexticRow F hF hJ]
  rfl

theorem rowPolynomial_smoothed_poisson (F : Finset (Ideal Eis))
    (hF : ∀ I ∈ F, Admissible I) (A : Ideal Eis → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y) * (‖rowPolynomial F A u‖^2 : ℝ)) =
      ∑ I ∈ F, ∑ J ∈ F, (star (A I)*A J) *
        idealPairPoissonKernel F (pool_positive F hF) (pool_good F hF) I J Φ Y := by
  rw [rowPolynomial_smoothed_expand F hF A Φ Y hY]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  simp_rw [idealRowHom_eq_idealSexticRow F hF hI, idealRowHom_eq_idealSexticRow F hF hJ]
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  exact finiteSquarefreeRow_pair_radial_poisson
    (fun q : primePool F => q.val) Subtype.val_injective
    (primePool_good F (pool_good F hF)) (pool_char F hF)
    (idealSupport F I) (idealSupport F J) Φ Y hY

theorem indexed_smoothed_poisson {β : Type*} (C : Finset β)
    (L : β → Ideal Eis) (hL : ∀ c ∈ C, Admissible (L c)) (A : β → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let F := C.image L
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact hL c hc
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y) *
      (‖∑ c ∈ C, A c * idealRowHom u (L c)‖^2 : ℝ)) =
      ∑ c ∈ C, ∑ d ∈ C, (star (A c)*A d) *
        idealPairPoissonKernel F (pool_positive F hF) (pool_good F hF) (L c) (L d) Φ Y := by
  intro F hF
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  have he (u : Eis) : (∑ c ∈ C, A c*idealRowHom u (L c)) =
      ∑ c ∈ C, A c*idealSexticRow F (pool_positive F hF) (pool_good F hF) (L c) u := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [idealRowHom_eq_idealSexticRow F hF (Finset.mem_image.mpr ⟨c,hc,rfl⟩)]
  simp_rw [he]
  simp only [idealSexticRow]
  rw [finiteSquarefreeRow_smoothed_mean_square_expand
    (fun q : primePool F => q.val) (primePool_good F (pool_good F hF))
    C (fun c => idealSupport F (L c)) A Φ Y hY]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  exact finiteSquarefreeRow_pair_radial_poisson
    (fun q : primePool F => q.val) Subtype.val_injective
    (primePool_good F (pool_good F hF)) (pool_char F hF)
    (idealSupport F (L c)) (idealSupport F (L d)) Φ Y hY

theorem indexed_conjugate_smoothed_poisson {β : Type*} (C : Finset β)
    (L : β → Ideal Eis) (hL : ∀ c ∈ C, Admissible (L c)) (A : β → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let F := C.image L
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact hL c hc
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y) *
      (‖∑ c ∈ C, A c * star (idealRowHom u (L c))‖^2 : ℝ)) =
      ∑ c ∈ C, ∑ d ∈ C, (A c*star (A d)) *
        idealPairPoissonKernel F (pool_positive F hF) (pool_good F hF) (L c) (L d) Φ Y := by
  intro F hF
  have he (u : Eis) : (∑ c ∈ C, A c * star (idealRowHom u (L c))) =
      star (∑ c ∈ C, star (A c) * idealRowHom u (L c)) := by
    simp only [star_sum,star_mul,star_star,mul_comm]
  simp_rw [he,norm_star]
  simpa only [star_star] using indexed_smoothed_poisson C L hL (fun c => star (A c)) Φ Y hY

theorem indexed_smoothed_summable {β : Type*} (C : Finset β)
    (L : β → Ideal Eis) (hL : ∀ c ∈ C, Admissible (L c)) (A : β → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y) *
      (‖∑ c ∈ C, A c * idealRowHom u (L c)‖^2 : ℝ)) := by
  let F := C.image L
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
    exact hL c hc
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  have he (u : Eis) : (∑ c ∈ C, A c*idealRowHom u (L c)) =
      ∑ c ∈ C, A c*idealSexticRow F (pool_positive F hF) (pool_good F hF) (L c) u := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [idealRowHom_eq_idealSexticRow F hF (Finset.mem_image.mpr ⟨c,hc,rfl⟩)]
  simpa only [he,idealSexticRow] using finiteSquarefreeRow_smoothed_mean_square_summable
    (fun q : primePool F => q.val) (primePool_good F (pool_good F hF))
    C (fun c => idealSupport F (L c)) A Φ Y hY

theorem supported_of_dvd {I J : Ideal Eis} (hI : Supported I) (hJI : J ∣ I) : Supported J := by
  obtain ⟨K,rfl⟩ := hJI
  exact (supported_mul_iff J K).mp hI |>.1

theorem columns_admissible (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n)
    {c : Ideal Eis} (hc : c ∈ columns S P j) : Admissible c := by
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hnS,hns,hg⟩ := mem_original.mp hn
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hs := (supported_mul_iff (idealQuotient j n) (residual P j)).mpr
    ⟨supported_of_dvd (hS n hnS hns) (idealQuotient_dvd hjn),
     supported_of_dvd (admissible_supported hP) (idealQuotient_dvd hj)⟩
  exact ⟨hs.1,(column_properties hP.2.1 hj hns hg).1,hs.2⟩

theorem masked_columns_admissible (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n)
    {c : Ideal Eis} (hc : c ∈ columns S P j) : Admissible (j*c) := by
  have hjA := admissible_of_dvd hP hj
  have hcA := columns_admissible S hP hj hS hc
  have hs := (supported_mul_iff j c).mpr ⟨admissible_supported hjA,admissible_supported hcA⟩
  exact ⟨hs.1,squarefree_mul_iff.mpr
    ⟨((mem_columns hP.2.1 hj).mp hc).2.1.symm.isRelPrime,hjA.2.1,hcA.2.1⟩,hs.2⟩

theorem norm_idealRowHom_four_eq_two (I : Ideal Eis) (hI : Admissible I) (u : Eis) :
    ‖idealRowHom u I‖^4 = ‖idealRowHom u I‖^2 := by
  let F : Finset (Ideal Eis) := {I}
  have hF : ∀ J ∈ F, Admissible J := by
    intro J hJ
    have he : J=I := Finset.mem_singleton.mp hJ
    simpa only [he] using hI
  rw [idealRowHom_eq_idealSexticRow F hF (Finset.mem_singleton_self I)]
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  have he := congrArg norm (finiteSquarefreeRow_self_pair
    (fun q : primePool F => q.val) (primePool_good F (pool_good F hF)) (idealSupport F I) u)
  simp only [norm_mul,norm_star,←pow_two] at he
  change ‖idealSexticRow F (pool_positive F hF) (pool_good F hF) I u‖^2 = _ at he
  have hp : ∀ x : ℝ, x^4=(x^2)^2 := by intro x; ring
  rw [hp,he]
  unfold rowCoprimeMask
  split_ifs <;> norm_num

def heckeIdealCharacter (η : Ideal Eis →* ℂ) (u : Eis) : Ideal Eis →* ℂ :=
  η * (idealRowHom u).toMonoidHom

theorem heckeIdealCharacter_apply (η : Ideal Eis →* ℂ) (u : Eis) (I : Ideal Eis) :
    heckeIdealCharacter η u I = η I * idealRowHom u I := rfl

def originalFixedPolynomial (S : Finset (Ideal Eis)) (P j : Ideal Eis)
    (η : Ideal Eis →* ℂ) (a : Ideal Eis → ℂ) (W : ℝ → ℂ)
    (Z r z : ℝ) (u : Eis) : ℂ :=
  (Z^(-(r+z)/2) : ℝ) * ∑ n ∈ original S P j,
    (moebius n : ℂ) * heckeIdealCharacter η u n * heckeIdealCharacter η u P *
      a n * W ((Ideal.absNorm n : ℝ)/Z^r)

def overlapResidualCoefficient (P j : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (c : Ideal Eis) : ℂ :=
  (moebius c : ℂ) * η c * a (reconstruct P j c) *
    W ((((Ideal.absNorm j : ℝ)/Z^G)*((Ideal.absNorm c : ℝ)/Z^(r+z-2*G))) /
      ((Ideal.absNorm (residual P j) : ℝ)/Z^(z-G)))

def overlapPrefactor (P j : Ideal Eis) (η : Ideal Eis →* ℂ) (Z r z G : ℝ) : ℂ :=
  (moebius j : ℂ)*(moebius (residual P j) : ℂ)*(Z^(-G) : ℝ)*η j^2*
    (Z^(-(r+z-2*G)/2) : ℝ)

theorem originalFixedPolynomial_eq (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j ∣ P) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) (u : Eis) :
    originalFixedPolynomial S P j η a W Z r z u =
      overlapPrefactor P j η Z r z G * (idealRowHom u j)^2 *
        rowPolynomial (columns S P j) (overlapResidualCoefficient P j η a W Z r z G) u := by
  have he := normalized_polynomial_fixed_overlap S hP hj (heckeIdealCharacter η u) a W hZ r z G
  change originalFixedPolynomial S P j η a W Z r z u = _ at he
  rw [he]
  simp only [heckeIdealCharacter_apply,
    rowPolynomial,overlapPrefactor,overlapResidualCoefficient,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem maskedResidual_eq (S : Finset (Ideal Eis)) (P j : Ideal Eis)
    (A : Ideal Eis → ℂ) (u : Eis) :
    (∑ c ∈ columns S P j, A c*idealRowHom u (j*c)) =
      idealRowHom u j * rowPolynomial (columns S P j) A u := by
  simp only [map_mul,rowPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

lemma norm_sq_square_factor (r s : ℂ) (h : ‖r‖^4=‖r‖^2) :
    ‖r^2*s‖^2=‖r*s‖^2 := by
  calc
    _ = ‖r‖^4*‖s‖^2 := by simp only [norm_mul,norm_pow]; ring
    _ = ‖r*s‖^2 := by rw [h,norm_mul,mul_pow]

theorem originalFixedPolynomial_norm_sq (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j ∣ P) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) (u : Eis) :
    ‖originalFixedPolynomial S P j η a W Z r z u‖^2 =
      ‖overlapPrefactor P j η Z r z G‖^2 *
        ‖∑ c ∈ columns S P j, overlapResidualCoefficient P j η a W Z r z G c *
          idealRowHom u (j*c)‖^2 := by
  rw [originalFixedPolynomial_eq S hP.2.1 hj η a W hZ r z G,
    maskedResidual_eq,mul_assoc,norm_mul,mul_pow]
  congr 1
  exact norm_sq_square_factor _ _ (norm_idealRowHom_four_eq_two j (admissible_of_dvd hP hj) u)

theorem norm_overlapPrefactor_sq {P j : Ideal Eis} (hP : Squarefree P) (hj : j ∣ P)
    (η : Ideal Eis →* ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    ‖overlapPrefactor P j η Z r z G‖^2 =
      Z^(-2*G-(r+z-2*G))*‖η j‖^4 := by
  have hjn : ‖(moebius j : ℂ)‖=1 := by simp [(hP.squarefree_of_dvd hj).moebius_eq]
  have hpn : ‖(moebius (residual P j) : ℂ)‖=1 := by simp [(residual_squarefree hP hj).moebius_eq]
  simp only [overlapPrefactor,norm_mul,norm_pow,hjn,hpn,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ (-G)),
    abs_of_pos (Real.rpow_pos_of_pos hZ (-(r+z-2*G)/2))]
  have hs : (Z^(-G))^2*(Z^(-(r+z-2*G)/2))^2=Z^(-2*G-(r+z-2*G)) := by
    rw [←Real.rpow_natCast,←Real.rpow_natCast,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,
      ←Real.rpow_add hZ]
    congr 1
    norm_num
    ring
  calc
    _ = ((Z^(-G))^2*(Z^(-(r+z-2*G)/2))^2)*‖η j‖^4 := by ring
    _ = _ := by rw [hs]

theorem original_fixed_overlap_smoothed_poisson
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let C := columns S P j
    let F := C.image (fun c => j*c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact masked_columns_admissible S hP hj hS hc
    let A := overlapResidualCoefficient P j η a W Z r z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y)*
      (‖originalFixedPolynomial S P j η a W Z r z u‖^2 : ℝ)) =
      ((Z^(-2*G-(r+z-2*G))*‖η j‖^4 : ℝ) : ℂ) *
        ∑ c ∈ C, ∑ d ∈ C, (star (A c)*A d) *
          idealPairPoissonKernel F (pool_positive F hF) (pool_good F hF) (j*c) (j*d) Φ Y := by
  intro C F hF A
  have he := indexed_smoothed_poisson C (fun c => j*c)
    (fun c hc => masked_columns_admissible S hP hj hS hc) A Φ Y hY
  calc
    _ = ∑' u : Eis, ((Z^(-2*G-(r+z-2*G))*‖η j‖^4 : ℝ) : ℂ) *
        (Φ (‖eisEmbedding u‖^2/Y) * (‖∑ c ∈ C, A c*idealRowHom u (j*c)‖^2 : ℝ)) := by
      apply tsum_congr
      intro u
      rw [originalFixedPolynomial_norm_sq S hP hj η a W hZ r z G,
        norm_overlapPrefactor_sq hP.2.1 hj η hZ r z G,Complex.ofReal_mul]
      ring
    _ = _ := by rw [tsum_mul_left,he]

theorem original_fixed_overlap_smoothed_poisson_zero_split
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let C := columns S P j
    let F := C.image (fun c => j*c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact masked_columns_admissible S hP hj hS hc
    let A := overlapResidualCoefficient P j η a W Z r z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y)*
      (‖originalFixedPolynomial S P j η a W Z r z u‖^2 : ℝ)) =
      ((Z^(-2*G-(r+z-2*G))*‖η j‖^4 : ℝ) : ℂ) *
        ∑ c ∈ C, ∑ d ∈ C, (star (A c)*A d) *
          (idealPairPoissonZeroMode F (pool_positive F hF) (pool_good F hF) (j*c) (j*d) Φ Y +
           idealPairPoissonNonzeroMode F (pool_positive F hF) (pool_good F hF) (j*c) (j*d) Φ Y) := by
  intro C F hF A
  rw [original_fixed_overlap_smoothed_poisson S hP hj hS η a W hZ r z G Φ Y hY]
  simp_rw [idealPairPoissonKernel_zero_split _ _ _ _ _ _ _ hY]
  rfl

def residualNormalizedPolynomial (S : Finset (Ideal Eis)) (P j : Ideal Eis)
    (η : Ideal Eis →* ℂ) (a : Ideal Eis → ℂ) (W : ℝ → ℂ)
    (Z r z G : ℝ) (u : Eis) : ℂ :=
  (Z^(-(r+z-2*G)/2) : ℝ) * ∑ c ∈ columns S P j,
    overlapResidualCoefficient P j η a W Z r z G c * star (idealRowHom u c)

lemma norm_rpow_half_sq {Z : ℝ} (hZ : 0 < Z) (D : ℝ) :
    ‖((Z^(-D/2) : ℝ) : ℂ)‖^2=Z^(-D) := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),
    ←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  congr 1
  norm_num

theorem residual_normalized_smoothed_poisson
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let C := columns S P j
    let F := C.image (fun c => c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact columns_admissible S hP hj hS hc
    let A := overlapResidualCoefficient P j η a W Z r z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) =
      (Z^(-(r+z-2*G)) : ℝ) *
        ∑ c ∈ C, ∑ d ∈ C, (A c*star (A d)) *
          idealPairPoissonKernel F (pool_positive F hF) (pool_good F hF) c d Φ Y := by
  intro C F hF A
  have he := indexed_conjugate_smoothed_poisson C (fun c => c)
    (fun c hc => columns_admissible S hP hj hS hc) A Φ Y hY
  calc
    _ = ∑' u : Eis, (Z^(-(r+z-2*G)) : ℝ) *
        (Φ (‖eisEmbedding u‖^2/Y) * (‖∑ c ∈ C, A c*star (idealRowHom u c)‖^2 : ℝ)) := by
      apply tsum_congr
      intro u
      rw [residualNormalizedPolynomial,norm_mul,mul_pow,norm_rpow_half_sq hZ,Complex.ofReal_mul]
      ring
    _ = _ := by rw [tsum_mul_left,he]

theorem residual_normalized_smoothed_poisson_zero_split
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let C := columns S P j
    let F := C.image (fun c => c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact columns_admissible S hP hj hS hc
    let A := overlapResidualCoefficient P j η a W Z r z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) =
      (Z^(-(r+z-2*G)) : ℝ) *
        ∑ c ∈ C, ∑ d ∈ C, (A c*star (A d)) *
          (idealPairPoissonZeroMode F (pool_positive F hF) (pool_good F hF) c d Φ Y +
           idealPairPoissonNonzeroMode F (pool_positive F hF) (pool_good F hF) c d Φ Y) := by
  intro C F hF A
  rw [residual_normalized_smoothed_poisson S hP hj hS η a W hZ r z G Φ Y hY]
  simp_rw [idealPairPoissonKernel_zero_split _ _ _ _ _ _ _ hY]
  rfl

theorem original_fixed_overlap_smoothed_summable
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y)*
      (‖originalFixedPolynomial S P j η a W Z r z u‖^2 : ℝ)) := by
  have hs := (indexed_smoothed_summable (columns S P j) (fun c => j*c)
    (fun c hc => masked_columns_admissible S hP hj hS hc)
    (overlapResidualCoefficient P j η a W Z r z G) Φ Y hY).mul_left
      ((‖overlapPrefactor P j η Z r z G‖^2 : ℝ) : ℂ)
  apply hs.congr
  intro u
  rw [originalFixedPolynomial_norm_sq S hP hj η a W hZ r z G,Complex.ofReal_mul]
  ring

theorem original_normalized_polynomial_hecke_rows
    (S : Finset (Ideal Eis)) {P : Ideal Eis} (hP : Squarefree P)
    (η : Ideal Eis →* ℂ) (a : Ideal Eis → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal Eis → ℝ) (u : Eis) :
    (Z^(-(r+z)/2) : ℝ) * (∑ n ∈ S,
      (moebius n : ℂ)*heckeIdealCharacter η u n*heckeIdealCharacter η u P*
        a n*W ((Ideal.absNorm n : ℝ)/Z^r)) =
      ∑ j ∈ IdealMobiusDivisorSum.idealDivisors P,
        overlapPrefactor P j η Z r z (G j) * (idealRowHom u j)^2 *
          rowPolynomial (columns S P j)
            (overlapResidualCoefficient P j η a W Z r z (G j)) u := by
  rw [original_normalized_polynomial S hP (heckeIdealCharacter η u) a W hZ r z G]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [heckeIdealCharacter_apply,rowPolynomial,overlapPrefactor,
    overlapResidualCoefficient,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem indexed_conjugate_smoothed_summable {β : Type*} (C : Finset β)
    (L : β → Ideal Eis) (hL : ∀ c ∈ C, Admissible (L c)) (A : β → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y) *
      (‖∑ c ∈ C, A c * star (idealRowHom u (L c))‖^2 : ℝ)) := by
  have he (u : Eis) : (∑ c ∈ C, A c * star (idealRowHom u (L c))) =
      star (∑ c ∈ C, star (A c) * idealRowHom u (L c)) := by
    simp only [star_sum,star_mul,star_star,mul_comm]
  simpa only [he,norm_star] using
    indexed_smoothed_summable C L hL (fun c => star (A c)) Φ Y hY

theorem residual_normalized_smoothed_summable
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) := by
  have hs := (indexed_conjugate_smoothed_summable (columns S P j) (fun c => c)
    (fun c hc => columns_admissible S hP hj hS hc)
    (overlapResidualCoefficient P j η a W Z r z G) Φ Y hY).mul_left
      ((Z^(-(r+z-2*G)) : ℝ) : ℂ)
  apply hs.congr
  intro u
  rw [residualNormalizedPolynomial,norm_mul,mul_pow,norm_rpow_half_sq hZ,Complex.ofReal_mul]
  ring

end SevenEighths.InverseInitialPoissonBridge

end

end OAI

end Source2347

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialKernelBridge.lean; sha256: 2f1dbd2141754f9c738c42be6f85e26a9ad99ed913d18faac09325882184fe89 -/
section Source2348
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open EisensteinSchwartzPoisson UniqueFactorizationMonoid CanonicalQuadraticSieve
open SevenEighths.InverseInitialPoissonBridge SevenEighths.InverseInitialOverlap
open SevenEighths.InverseInitialProfile
namespace SevenEighths.InverseInitialKernelBridge

local notation "Eis" => ActualEisensteinCubic.O
local notation "N" => fun I : Ideal Eis => (Ideal.absNorm I : ℝ)
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal Eis)
  [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
  (hg : ∀ i, goodLambda ∉ P i)

def pairRow (S T : Finset ι) (h : Eis) : ℂ :=
  finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T) h

def pairGauss (S T : Finset ι) : ℂ :=
  canonicalNormalizedGauss (activePrimes P S T)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val) (activeExponent S T)

def pairCoordinates (S T E : Finset ι) (h : Eis) : Fin 6 → ℝ :=
  ![N (∏ i ∈ S∩T,P i), N (∏ i ∈ E,P i), 1, ‖eisEmbedding h‖^2,
    N (∏ i ∈ S\T,P i), N (∏ i ∈ T\S,P i)]

omit [∀ i, (P i).IsMaximal] in
theorem common_left_product (S T : Finset ι) :
    (∏ i ∈ S∩T,P i)*(∏ i ∈ S\T,P i) = ∏ i ∈ S,P i := by
  rw [mul_comm,←Finset.prod_union (Finset.disjoint_sdiff_inter S T),Finset.sdiff_union_inter]

omit [∀ i, (P i).IsMaximal] in
theorem common_right_product (S T : Finset ι) :
    (∏ i ∈ S∩T,P i)*(∏ i ∈ T\S,P i) = ∏ i ∈ T,P i := by
  simpa only [Finset.inter_comm] using common_left_product P T S

omit [∀ i, (P i).IsMaximal] in
theorem conductor_norm (S T : Finset ι) :
    ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ =
      Real.sqrt (N (∏ i ∈ S\T,P i)*N (∏ i ∈ T\S,P i)) := by
  have hn := activePrimeModulus_norm_sq P S T
  have hd : Disjoint (S\T) (T\S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  simp only [activeSupport,Finset.prod_union hd,map_mul,Nat.cast_mul] at hn
  rw [←hn,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  rfl

def pairArithmetic (S T E : Finset ι) (h : Eis) : ℂ :=
  pairGauss P hinj hg S T * (moebius (∏ i ∈ E,P i) : ℂ) *
    pairRow P hg S T (primeSubsetGenerator P E) * star (pairRow P hg S T h)

def pairMode (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (h : Eis) : ℂ :=
  ((Y : ℂ)*pairGauss P hinj hg S T /
    (‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ : ℂ)) *
    (((moebius (∏ i ∈ E,P i) : ℂ)*pairRow P hg S T (primeSubsetGenerator P E) /
      (‖eisEmbedding (primeSubsetGenerator P E)‖^2 : ℝ)) *
      (star (pairRow P hg S T h)*paperRadialFourier Φ
        (Y*‖eisEmbedding h‖^2/(‖eisEmbedding (primeSubsetGenerator P E)‖^2 *
          ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖^2))))

theorem pairKernel_eq_modes (S T : Finset ι) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    squarefreePairPoissonKernel P hinj hg S T Φ Y =
      ∑ E ∈ (S∩T).powerset, ∑' h : Eis, pairMode P hinj hg S T E Φ Y h := by
  simp only [squarefreePairPoissonKernel,pairMode,pairGauss,pairRow,
    tsum_mul_left,Finset.mul_sum]

private theorem physicalKernel_vector (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z D m q₀ q₁ q₂ q₃ q₄ q₅ : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m ![q₀,q₁,q₂,q₃,q₄,q₅] =
      ((Z^(-D)*Z^m/(q₁*q₂*Real.sqrt (q₄*q₅)) : ℝ) : ℂ)*
        W₁ (q₀*q₂*q₄/Z^D)*W₂ (q₀*q₂*q₅/Z^D)*
          paperRadialFourier Φ (Z^m*q₃/(q₁*q₂^2*q₄*q₅)) := rfl

theorem pairMode_physical (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ))
    (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) (h : Eis) :
    (Z^(-D) : ℝ)*W₁ (N (∏ i ∈ S,P i)/Z^D)*W₂ (N (∏ i ∈ T,P i)/Z^D)*
      pairMode P hinj hg S T E Φ (Z^m) h =
    pairArithmetic P hinj hg S T E h *
      physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E h) := by
  have hs := congrArg N (common_left_product P S T)
  have ht := congrArg N (common_right_product P S T)
  simp only [map_mul,Nat.cast_mul] at hs ht
  have hc := conductor_norm P S T
  have hc2 := congrArg (fun x : ℝ => x^2) hc
  rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] at hc2
  unfold pairMode pairArithmetic pairCoordinates
  rw [physicalKernel_vector]
  simp only [mul_one,one_pow,primeSubsetGenerator_norm_sq,hc2]
  rw [hc,hs,ht]
  push_cast
  ring_nf

theorem pairKernel_physical (S T : Finset ι) (Φ : 𝓢(ℝ,ℂ))
    (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) :
    (Z^(-D) : ℝ)*W₁ (N (∏ i ∈ S,P i)/Z^D)*W₂ (N (∏ i ∈ T,P i)/Z^D)*
      squarefreePairPoissonKernel P hinj hg S T Φ (Z^m) =
    ∑ E ∈ (S∩T).powerset, ∑' h : Eis,
      pairArithmetic P hinj hg S T E h *
        physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E h) := by
  rw [pairKernel_eq_modes]
  simp only [Finset.mul_sum,←tsum_mul_left]
  apply Finset.sum_congr rfl
  intro E hE
  apply tsum_congr
  intro h
  exact pairMode_physical P hinj hg S T E Φ W₁ W₂ Z D m h

def idealPhysicalPair (F : Finset (Ideal Eis)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ Q ∈ normalizedFactors I, goodLambda ∉ Q)
    (I J : Ideal Eis) (Φ : 𝓢(ℝ,ℂ)) (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) : ℂ := by
  letI : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F hFpos
  exact ∑ E ∈ (idealSupport F I ∩ idealSupport F J).powerset, ∑' h : Eis,
    pairArithmetic (fun q : primePool F => q.val) Subtype.val_injective
      (primePool_good F hFgood) (idealSupport F I) (idealSupport F J) E h *
      physicalKernel W₁ W₂ Φ Z D m
        (pairCoordinates (fun q : primePool F => q.val) (idealSupport F I) (idealSupport F J) E h)

theorem ideal_conductor_norm_sq (F : Finset (Ideal Eis)) {I J : Ideal Eis}
    (hI : I ∈ F) (hJ : J ∈ F) (hsI : Squarefree I) (hsJ : Squarefree J) :
    ‖eisEmbedding (finitePrimeModulus (activePrimes (fun q : primePool F => q.val)
      (idealSupport F I) (idealSupport F J)))‖^2 *
        (N (primeSubsetProduct F (idealSupport F I∩idealSupport F J)))^2 = N I*N J :=
  idealPairPoisson_conductor_norm_sq F hI hJ hsI hsJ

theorem idealPairKernel_physical (F : Finset (Ideal Eis)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ Q ∈ normalizedFactors I, goodLambda ∉ Q)
    {I J : Ideal Eis} (hI : I ∈ F) (hJ : J ∈ F) (hsI : Squarefree I) (hsJ : Squarefree J)
    (Φ : 𝓢(ℝ,ℂ)) (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) :
    (Z^(-D) : ℝ)*W₁ (N I/Z^D)*W₂ (N J/Z^D)*
      idealPairPoissonKernel F hFpos hFgood I J Φ (Z^m) =
      idealPhysicalPair F hFpos hFgood I J Φ W₁ W₂ Z D m := by
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F hFpos
  simpa only [idealPairPoissonKernel,idealPhysicalPair,
    idealSupport_product_eq F hI hsI,idealSupport_product_eq F hJ hsJ] using
    pairKernel_physical (fun q : primePool F => q.val) Subtype.val_injective
      (primePool_good F hFgood) (idealSupport F I) (idealSupport F J) Φ W₁ W₂ Z D m

def bareOverlapCoefficient (P j : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (c : Ideal Eis) : ℂ :=
  (moebius c : ℂ)*η c*a (reconstruct P j c)

def maskedOverlapWindow (P j : Ideal Eis) (W : ℝ → ℂ) (Z z G : ℝ) (x : ℝ) : ℂ :=
  W ((x/Z^G)/((N (residual P j))/Z^(z-G)))

def residualOverlapWindow (P j : Ideal Eis) (W : ℝ → ℂ) (Z z G : ℝ) (x : ℝ) : ℂ :=
  W (((N j/Z^G)*x)/((N (residual P j))/Z^(z-G)))

theorem overlapCoefficient_masked (P j c : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) :
    overlapResidualCoefficient P j η a W Z r z G c =
      bareOverlapCoefficient P j η a c *
        maskedOverlapWindow P j W Z z G (N (j*c)/Z^(r+z-2*G)) := by
  unfold overlapResidualCoefficient bareOverlapCoefficient maskedOverlapWindow
  simp only [map_mul,Nat.cast_mul]
  congr 2
  ring_nf

theorem overlapCoefficient_residual (P j c : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) :
    overlapResidualCoefficient P j η a W Z r z G c =
      bareOverlapCoefficient P j η a c *
        residualOverlapWindow P j W Z z G (N c/Z^(r+z-2*G)) := rfl

theorem original_fixed_overlap_physical
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G m : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) :
    let C := columns S P j
    let F := C.image (fun c => j*c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact masked_columns_admissible S hP hj hS hc
    let b := bareOverlapCoefficient P j η a
    let V := maskedOverlapWindow P j W Z z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖originalFixedPolynomial S P j η a W Z r z u‖^2 : ℝ)) =
      ((Z^(-2*G)*‖η j‖^4 : ℝ) : ℂ)*
        ∑ c ∈ C, ∑ d ∈ C, (star (b c)*b d)*
          idealPhysicalPair F (pool_positive F hF) (pool_good F hF) (j*c) (j*d)
            Φ (fun x => star (V x)) V Z (r+z-2*G) m := by
  intro C F hF b V
  rw [original_fixed_overlap_smoothed_poisson S hP hj hS η a W hZ r z G Φ
    (Z^m) (Real.rpow_pos_of_pos hZ m)]
  have he : Z^(-2*G-(r+z-2*G)) = Z^(-2*G)*Z^(-(r+z-2*G)) := by
    rw [←Real.rpow_add hZ]
    congr 1
  rw [he]
  simp only [Complex.ofReal_mul]
  rw [show ((Z^(-2*G):ℝ):ℂ)*((Z^(-(r+z-2*G)):ℝ):ℂ)*↑(‖η j‖^4) =
    (((Z^(-2*G):ℝ):ℂ)*↑(‖η j‖^4))*((Z^(-(r+z-2*G)):ℝ):ℂ) from by ring_nf,mul_assoc]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  have hcF : j*c ∈ F := Finset.mem_image.mpr ⟨c,hc,rfl⟩
  have hdF : j*d ∈ F := Finset.mem_image.mpr ⟨d,hd,rfl⟩
  have hker := idealPairKernel_physical F (pool_positive F hF) (pool_good F hF)
    hcF hdF (hF _ hcF).2.1 (hF _ hdF).2.1 Φ (fun x => star (V x)) V Z (r+z-2*G) m
  rw [overlapCoefficient_masked,overlapCoefficient_masked]
  simp only [star_mul]
  dsimp only [b,V,F,C] at hker ⊢
  rw [←hker]
  ring_nf

theorem residual_normalized_physical
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G m : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) :
    let C := columns S P j
    let F := C.image (fun c => c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact columns_admissible S hP hj hS hc
    let b := bareOverlapCoefficient P j η a
    let V := residualOverlapWindow P j W Z z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) =
        ∑ c ∈ C, ∑ d ∈ C, (b c*star (b d))*
          idealPhysicalPair F (pool_positive F hF) (pool_good F hF) c d
            Φ V (fun x => star (V x)) Z (r+z-2*G) m := by
  intro C F hF b V
  rw [residual_normalized_smoothed_poisson S hP hj hS η a W hZ r z G Φ
    (Z^m) (Real.rpow_pos_of_pos hZ m)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  have hcF : c ∈ F := Finset.mem_image.mpr ⟨c,hc,rfl⟩
  have hdF : d ∈ F := Finset.mem_image.mpr ⟨d,hd,rfl⟩
  have hker := idealPairKernel_physical F (pool_positive F hF) (pool_good F hF)
    hcF hdF (hF _ hcF).2.1 (hF _ hdF).2.1 Φ V (fun x => star (V x)) Z (r+z-2*G) m
  rw [overlapCoefficient_residual,overlapCoefficient_residual]
  simp only [star_mul]
  dsimp only [b,V,F,C] at hker ⊢
  rw [←hker]
  ring_nf

def physicalCoordinates (C d s n₁ n₂ : Ideal Eis) (h : Eis) : Fin 6 → ℝ :=
  ![N C,N d,N s,‖eisEmbedding h‖^2,N n₁,N n₂]

theorem physicalCoordinates_pos (C d s n₁ n₂ : Ideal Eis) (h : Eis)
    (hC : C ≠ 0) (hd : d ≠ 0) (hs : s ≠ 0) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (hh : h ≠ 0) :
    ∀ i, 0 < physicalCoordinates C d s n₁ n₂ h i := by
  have hp (I : Ideal Eis) (hI : I ≠ 0) : 0 < N I := by
    change 0 < (Ideal.absNorm I : ℝ)
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  intro i
  fin_cases i
  · exact hp C hC
  · exact hp d hd
  · exact hp s hs
  · exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh))
  · exact hp n₁ h₁
  · exact hp n₂ h₂

theorem physicalKernel_common_factor (C d s n₁ n₂ : Ideal Eis) (h : Eis)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d 1 (s*n₁) (s*n₂) h) =
      physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d s n₁ n₂ h) := by
  have hroot : Real.sqrt ((N s*N n₁)*(N s*N n₂)) = N s*Real.sqrt (N n₁*N n₂) := by
    rw [show (N s*N n₁)*(N s*N n₂) = (N s)^2*(N n₁*N n₂) from by ring_nf,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  unfold physicalCoordinates
  rw [physicalKernel_vector,physicalKernel_vector]
  simp only [map_one,Nat.cast_one,map_mul,Nat.cast_mul,mul_one,one_pow]
  rw [hroot]
  have hl : N C*(N s*N n₁)/Z^D = N C*N s*N n₁/Z^D := by ring_nf
  have hr : N C*(N s*N n₂)/Z^D = N C*N s*N n₂/Z^D := by ring_nf
  have hk : Z^m*‖eisEmbedding h‖^2/(N d*(N s*N n₁)*(N s*N n₂)) =
      Z^m*‖eisEmbedding h‖^2/(N d*(N s)^2*N n₁*N n₂) := by ring_nf
  rw [hl,hr,hk]
  push_cast
  ring_nf

omit [∀ i, (P i).IsMaximal] in

theorem pairCoordinates_eq (S T E : Finset ι) (h : Eis) :
    pairCoordinates P S T E h = physicalCoordinates
      (∏ i ∈ S∩T,P i) (∏ i ∈ E,P i) 1 (∏ i ∈ S\T,P i) (∏ i ∈ T\S,P i) h := by
  simp only [pairCoordinates,physicalCoordinates,map_one,Nat.cast_one]

theorem pairArithmetic_residual_rows (S T E : Finset ι) (h : Eis) :
    pairArithmetic P hinj hg S T E h =
      pairGauss P hinj hg S T * (moebius (∏ i ∈ E,P i) : ℂ) *
        (star (finiteSquarefreeRow P hg (S\T) (primeSubsetGenerator P E)) *
          finiteSquarefreeRow P hg (T\S) (primeSubsetGenerator P E)) *
        (finiteSquarefreeRow P hg (S\T) h * star (finiteSquarefreeRow P hg (T\S) h)) := by
  have he (u : Eis) : pairRow P hg S T u =
      star (finiteSquarefreeRow P hg (S\T) u)*finiteSquarefreeRow P hg (T\S) u :=
    finiteSexticRow_activeSupport P hg S T u
  simp only [pairArithmetic,he,star_mul,star_star]
  ring_nf

theorem pairMode_summable (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (pairMode P hinj hg S T E Φ Y) := by
  let den := ‖eisEmbedding (primeSubsetGenerator P E)‖^2 *
    ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖^2
  have hd : 0 < den := mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E))))
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero _))))
  have hs := activeRow_paperFourier_summable P hg S T Φ (Y/den) (div_pos hY hd)
  have he (h : Eis) : (Y/den)*‖eisEmbedding h‖^2 = Y*‖eisEmbedding h‖^2/den := by ring_nf
  simp_rw [he] at hs
  exact (hs.mul_left _).mul_left _

theorem pairMode_zero_split (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' h : Eis, pairMode P hinj hg S T E Φ Y h) =
      pairMode P hinj hg S T E Φ Y 0 +
        ∑' h : Eis, if h=0 then 0 else pairMode P hinj hg S T E Φ Y h :=
  (pairMode_summable P hinj hg S T E Φ Y hY).tsum_eq_add_tsum_ite 0

theorem physicalMode_zero_split (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ))
    (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) (hZ : 0 < Z) :
    (∑' h : Eis, pairArithmetic P hinj hg S T E h *
      physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E h)) =
      pairArithmetic P hinj hg S T E 0 *
        physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E 0) +
      ∑' h : Eis, if h=0 then 0 else pairArithmetic P hinj hg S T E h *
        physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E h) := by
  have hs := (pairMode_summable P hinj hg S T E Φ (Z^m) (Real.rpow_pos_of_pos hZ m)).mul_left
    (((Z^(-D):ℝ):ℂ)*W₁ (N (∏ i ∈ S,P i)/Z^D)*W₂ (N (∏ i ∈ T,P i)/Z^D))
  have he := (funext fun h => pairMode_physical P hinj hg S T E Φ W₁ W₂ Z D m h)
  rw [he] at hs
  exact hs.tsum_eq_add_tsum_ite 0

open InverseInitialArithmetic SecondPassArithmetic

theorem common_extracted_physical_mode
    (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i,goodLambda∉Ideal.span {p i})
    (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ₁ Ψ₂ : Eis →* ℂ)
    (j t d h : Eis) (H₁ H₂ : Finset ι → ℂ) (V N₁ N₂ : Finset ι)
    (h₁ : Disjoint V N₁) (h₂ : Disjoint V N₂)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) :
    star (initialColumn p hp hcop hgood Ψ₁ j (d*t) d h H₁ (V∪N₁)) *
      initialColumn p hp hcop hgood Ψ₂ j (d*t) d h H₂ (V∪N₂) *
      physicalKernel W₁ W₂ Φ Z D m
        (physicalCoordinates (Ideal.span {d*t}) (Ideal.span {d}) 1
          (sourceIdeal p (V∪N₁)) (sourceIdeal p (V∪N₂)) h) =
    (star (initialColumn p hp hcop hgood Ψ₁ j (d*t) d h (fun _=>1) V) *
      initialColumn p hp hcop hgood Ψ₂ j (d*t) d h (fun _=>1) V) *
      star (secondChildColumn p hp hcop hgood Ψ₁ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>H₁ (V∪U)) N₁) *
      secondChildColumn p hp hcop hgood Ψ₂ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>H₂ (V∪U)) N₂ *
      physicalKernel W₁ W₂ Φ Z D m
        (physicalCoordinates (Ideal.span {d*t}) (Ideal.span {d}) (sourceIdeal p V)
          (sourceIdeal p N₁) (sourceIdeal p N₂) h) := by
  rw [initial_common_extraction p hp hcop hgood hpr Ψ₁ j t d h H₁ V N₁ h₁,
    initial_common_extraction p hp hcop hgood hpr Ψ₂ j t d h H₂ V N₂ h₂,
    sourceIdeal_union p V N₁ h₁,sourceIdeal_union p V N₂ h₂,
    physicalKernel_common_factor]
  simp only [star_mul]
  ring_nf

omit [∀ i, (P i).IsMaximal] in

theorem pairDivisor_dvd_common (S T E : Finset ι) (hE : E ∈ (S∩T).powerset) :
    (∏ i ∈ E,P i) ∣ (∏ i ∈ S∩T,P i) :=
  Finset.prod_dvd_prod_of_subset E (S∩T) P (Finset.mem_powerset.mp hE)

omit [DecidableEq ι] [∀ i, (P i).IsMaximal] in
theorem pairDivisor_span (E : Finset ι) :
    Ideal.span {primeSubsetGenerator P E} = ∏ i ∈ E,P i :=
  span_idealGenerator _

theorem physicalCoordinates_frequency_ideal (C d s n₁ n₂ : Ideal Eis) (h : Eis) :
    physicalCoordinates C d s n₁ n₂ h =
      ![N C,N d,N s,N (Ideal.span {h}),N n₁,N n₂] := by
  simp only [physicalCoordinates,eisEmbedding_norm_sq_eq_absNorm_span]

end SevenEighths.InverseInitialKernelBridge

end

end OAI

end Source2348

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialRayAttachment.lean; sha256: 280bdb9a66a3446782d24f5d4b7e196bf4b682b64ce58ffa7da3a4df1abe37f0 -/
section Source2349
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialRayAttachment
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open FirstCauchyArithmetic SecondPassArithmetic ConcreteTraceCRT EisensteinSchwartzPoisson
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialArithmetic InverseInitialProfile
local notation "O" => ActualEisensteinCubic.O

def elementCharacter (η : Ideal O →* ℂ) : O →* ℂ where
  toFun x := η (Ideal.span {x})
  map_one' := by rw [Ideal.span_singleton_one, ←Ideal.one_eq_top, map_one]
  map_mul' x y := by rw [←Ideal.span_singleton_mul_span_singleton,map_mul]

theorem elementCharacter_product {ι : Type*} (η : Ideal O →* ℂ)
    (p : ι → O) (A : Finset ι) :
    elementCharacter η (∏ i ∈ A,p i) = η (∏ i ∈ A,Ideal.span {p i}) := by
  change η (Ideal.span {∏ i ∈ A,p i}) = _
  rw [FiniteGaussPhase.span_finset_prod]

def reconstructedSelector (S : Finset (Ideal O)) (P j : Ideal O)
    (a : Ideal O → ℂ) (A : Finset (primePool (columns S P j))) : ℂ :=
  if (∏ i ∈ A,i.val) ∈ columns S P j then a (reconstruct P j (∏ i ∈ A,i.val)) else 0

theorem poolPrimary_injective (F : Finset (Ideal O)) (hF : ∀ I ∈ F,Admissible I) :
    Function.Injective (fun i : primePool F => Ideal.span {poolPrimary F i}) := by
  intro i k he
  change Ideal.span {poolPrimary F i} = Ideal.span {poolPrimary F k} at he
  rw [poolPrimary_span F hF,poolPrimary_span F hF] at he
  exact Subtype.ext he

theorem poolPrimary_primary (F : Finset (Ideal O)) (hF : ∀ I ∈ F,Admissible I)
    (i : primePool F) : goodLambda^2 ∣ poolPrimary F i-1 :=
  (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2

theorem selected_mask (F : Finset (Ideal O)) (j : Ideal O) (hj : Admissible j)
    (A : Finset (primePool F)) (hcop : IsCoprime (∏ i ∈ A,i.val) j) :
    rowCoprimeMask (fun i : primePool F => i.val) A (primaryGenerator j)=1 := by
  have hspan := (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1
  unfold rowCoprimeMask
  split_ifs with h
  · obtain ⟨i,hi,hm⟩ := h
    have hd : i.val ∣ ∏ k ∈ A,k.val := Finset.dvd_prod_of_mem _ hi
    have hjd : i.val ∣ j := by
      rw [Ideal.dvd_iff_le,←hspan]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have hp : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
    exact False.elim (hp.not_isUnit (hcop.isRelPrime hd hjd))
  · rfl

theorem selected_conjugate_row (F : Finset (Ideal O))
    (hF : ∀ I ∈ F,Admissible I) (j : Ideal O) (hj : Admissible j)
    (hcop : ∀ I ∈ F,IsCoprime I j) (η : Ideal O →* ℂ) (H : Ideal O → ℂ) (u : O) :
    let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    (∑ I ∈ F,(moebius I : ℂ)*η I*H I*star (idealRowHom u I)) =
      inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A => if (∏ i ∈ A,i.val)∈F then H (∏ i ∈ A,i.val) else 0) u := by
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) =
      (fun i : primePool F => i.val) := funext (poolPrimary_span F hF)
  dsimp only
  rw [InitialMeanSquare.sum_selected_ideals F (fun I hI => (hF I hI).2.1)]
  erw [initial_input_row]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [elementCharacter_product]
  simp only [he]
  by_cases hAF : (∏ i ∈ A,i.val)∈F
  · simp only [hAF,ite_true]
    rw [selected_mask F j hj A (hcop _ hAF),mul_one]
    rw [idealRowHom_eq_idealSexticRow F hF hAF]
    simp only [supportMobius,idealSexticRow,InitialMeanSquare.pool_support_product]
    ring
  · simp only [hAF,ite_false,mul_zero,zero_mul]

theorem residual_eq_input (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    (Z r z G : ℝ) (u : O) :
    let F := columns S P j
    let hF : ∀ I ∈ F,Admissible I := fun I hI => columns_admissible S hP hj hS hI
    let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    residualNormalizedPolynomial S P j η a W Z r z G u =
      (Z^(-(r+z-2*G)/2) : ℝ)*
        inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ
          (elementCharacter η) (primaryGenerator j) 1 1
          (fun A => reconstructedSelector S P j a A *
            residualOverlapWindow P j W Z z G
              ((Ideal.absNorm (∏ i ∈ A,i.val) : ℝ)/Z^(r+z-2*G))) u := by
  intro F hF
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  unfold residualNormalizedPolynomial
  congr 1
  have hc : ∀ I ∈ F,IsCoprime I j := fun I hI => ((mem_columns hP.2.1 hj).mp hI).2.1
  have ht := selected_conjugate_row F hF j (admissible_of_dvd hP hj) hc η
    (fun I => a (reconstruct P j I)*residualOverlapWindow P j W Z z G
      ((Ideal.absNorm I : ℝ)/Z^(r+z-2*G))) u
  convert ht using 1
  · apply Finset.sum_congr rfl
    intro I hI
    rw [overlapCoefficient_residual]
    unfold bareOverlapCoefficient
    ring
  · congr 1
    funext A
    unfold reconstructedSelector
    dsimp only [F]
    split_ifs <;> simp only [zero_mul]

section RayModes
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})
open FirstPassCubeLabels (primeProductNorm primeProductNorm_union)

def initialTest (σ : Finset ι → ℂ) (V : ℝ → ℂ) (Z D : ℝ) (A : Finset ι) : ℂ :=
  σ A*V (primeProductNorm p A/Z^D)

def initialBeta (Ψ : O →* ℂ) (j : O) (G : Finset ι) : ℂ :=
  (‖Ψ (∏ i ∈ G,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) G j‖^2 : ℝ)

theorem initial_overlap_weight (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι → ℂ) (V : ℝ → ℂ) (Z D : ℝ) (G U T : Finset ι) :
    overlapPairWeight p hg Ψ j 1 1 (initialTest p σ V Z D) G U T =
      initialBeta p Ψ j G *
        star (supportMobius (fun i => Ideal.span {p i}) U *
          secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) U) *
        (supportMobius (fun i => Ideal.span {p i}) T *
          secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) T) *
        star (V (primeProductNorm p (G∪U)/Z^D))*V (primeProductNorm p (G∪T)/Z^D) := by
  have hrow (A : Finset ι) :
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A 1 = 1 :=
    finiteSquarefreeRow_one _ hg A
  simp only [overlapPairWeight,secondInputCoefficient,initialBeta,initialTest,
    hrow,one_pow,mul_one,star_mul]
  ring

theorem initial_pair_rays
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j e h : O) (σ : Finset ι → ℂ)
    (G U T : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T) (hUT : Disjoint U T) :
    star (supportMobius (fun i => Ideal.span {p i}) U *
      secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) U) *
      (supportMobius (fun i => Ideal.span {p i}) T *
        secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) T) *
      activeGaussRowFactor p hp hinj hg T U e h =
    ∑ ρ : SecondRayIndex,secondRayCoefficient ρ *
      star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i ∈ G,p i) e h
        (fun A => σ (G∪A)) U) *
      initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i ∈ G,p i) e (-h)
        (fun A => σ (G∪A)) T := by
  have hm (A : Finset ι) (hAG : Disjoint A G) :
      secondInputCoefficient p hg Ψ (j*∏ i ∈ G,p i) 1 1 (fun A => σ (G∪A)) A =
        secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) A := by
    erw [secondInputCoefficient_fixed_mask,commonProduct_mask p hg hinj]
    simp only [hAG,ite_true,one_mul]
  have he := second_gauss_ray_expansion p hp hcop hg hinj hc hpr Ψ Ψ
    (j*∏ i ∈ G,p i) 1 1 e h (fun A => σ (G∪A)) (fun A => σ (G∪A)) U T hUT
  rw [hm U hGU.symm,hm T hGT.symm] at he
  simpa only [Fintype.sum_prod_type,secondRayCoefficient,secondRayMinus,secondRayPlus,
    initialColumn_eq_secondPre] using he

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem initial_product_kernel (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (G U T E : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T)
    (hUT : Disjoint U T) (h : O) :
    physicalKernel (fun x => star (V x)) V Φ Z D m
      (physicalCoordinates (sourceIdeal p G) (sourceIdeal p E) 1
        (sourceIdeal p U) (sourceIdeal p T) h) =
    ((Z^(-D) : ℝ) : ℂ)*star (V (primeProductNorm p (G∪U)/Z^D))*
      V (primeProductNorm p (G∪T)/Z^D)*
      ((Z^m : ℝ) : ℂ)/(‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖ : ℂ) *
      (1/(‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 : ℝ)) *
      paperRadialFourier Φ (Z^m*‖eisEmbedding h‖^2/
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
          ‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖^2)) := by
  have hn := active_norm_sq_disjoint p U T hUT
  have hr : Real.sqrt (primeProductNorm p U*primeProductNorm p T) =
      ‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖ := by
    rw [←hn,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have he : (Ideal.absNorm (sourceIdeal p E) : ℝ) =
      ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 := by
    rw [primeSubsetGenerator_norm_sq,sourceIdeal,FiniteGaussPhase.span_finset_prod]
  have hnorm (A : Finset ι) : (Ideal.absNorm (sourceIdeal p A) : ℝ)=primeProductNorm p A :=
    (eisEmbedding_norm_sq_eq_absNorm_span _).symm
  unfold physicalKernel physicalCoordinates
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    hnorm,map_one,Nat.cast_one,mul_one,one_pow]
  rw [hr,←hnorm E,he,hn]
  rw [primeProductNorm_union p G U hGU,primeProductNorm_union p G T hGT]
  push_cast
  ring_nf

def initialPhysicalMode (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) (G U T E : Finset ι) (h : O) : ℂ :=
  initialBeta p Ψ j G * (moebius (sourceIdeal p E) : ℂ) *
    (∑ ρ : SecondRayIndex,secondRayCoefficient ρ *
      star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i ∈ G,p i)
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) h (fun A => σ (G∪A)) U) *
      initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i ∈ G,p i)
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) (-h) (fun A => σ (G∪A)) T) *
    physicalKernel (fun x => star (V x)) V Φ Z D m
      (physicalCoordinates (sourceIdeal p G) (sourceIdeal p E) 1
        (sourceIdeal p U) (sourceIdeal p T) h)

theorem normalized_overlap_mode
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) (G U T E : Finset ι)
    (hGU : Disjoint G U) (hGT : Disjoint G T) (hUT : Disjoint U T) (h : O) :
    ((Z^(-D) : ℝ) : ℂ)*
      overlapPairWeight p hg Ψ j 1 1 (initialTest p σ V Z D) G U T *
      (((Z^m : ℝ) : ℂ)/(‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖ : ℂ)) *
      ((moebius (∏ i ∈ E,Ideal.span {p i}) : ℂ)/
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 : ℝ)) *
      (paperRadialFourier Φ (Z^m*‖eisEmbedding h‖^2/
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
          ‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖^2)) *
        activeGaussRowFactor p hp hinj hg T U
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E) h) =
      initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h := by
  rw [initial_overlap_weight]
  unfold initialPhysicalMode
  rw [←initial_pair_rays p hp hcop hg hinj hc hpr Ψ j _ h σ G U T hGU hGT hUT,
    initial_product_kernel p V Φ Z D m G U T E hGU hGT hUT h]
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  ring

theorem initial_input_physical
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (F : Finset ι) (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) {Z : ℝ} (hZ : 0<Z) (D m : ℝ) :
    (∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖((Z^(-D/2) : ℝ) : ℂ)*inputConjugateRow p hg F Ψ j 1 1
        (initialTest p σ V Z D) u‖^2 : ℝ)) =
    ∑ G ∈ F.powerset,∑ U ∈ (F\G).powerset,∑ T ∈ (F\G).powerset,
      if Disjoint U T then ∑ E ∈ G.powerset,∑' h : O,
        initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h else 0 := by
  have hn := norm_rpow_half_sq hZ D
  simp only [norm_mul,mul_pow,hn,Complex.ofReal_mul]
  have hs : (∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (((Z^(-D) : ℝ) : ℂ)*(‖inputConjugateRow p hg F Ψ j 1 1
        (initialTest p σ V Z D) u‖^2 : ℝ))) =
      ((Z^(-D) : ℝ) : ℂ)*(∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
        (‖inputConjugateRow p hg F Ψ j 1 1 (initialTest p σ V Z D) u‖^2 : ℝ)) := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro u
    ring
  rw [hs,inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ j 1 1
    (initialTest p σ V Z D) Φ (Z^m) (Real.rpow_pos_of_pos hZ m)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hUT : Disjoint U T
  · simp only [hUT,ite_true]
    have hGU : Disjoint G U := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
    have hGT : Disjoint G T := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hT) disjoint_sdiff_self_right
    unfold maskedSecondDual
    simp only [Finset.mul_sum,←tsum_mul_left]
    apply Finset.sum_congr rfl
    intro E hE
    apply tsum_congr
    intro h
    convert normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ V Φ
      Z D m G U T E hGU hGT hUT h using 1
    ring
  · simp only [hUT,ite_false,mul_zero]

theorem initialPhysicalMode_summable
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) {Z : ℝ} (hZ : 0<Z) (D m : ℝ)
    (G U T E : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T)
    (hUT : Disjoint U T) :
    Summable (initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E) := by
  have hs := secondPairRadialMode_summable p hp hg hinj U T
    (primeSubsetGenerator (fun i => Ideal.span {p i}) E) (primeSubsetGenerator_ne_zero _ _)
    Φ (Z^m) (Real.rpow_pos_of_pos hZ m)
  have hs' := (hs.mul_left ((moebius (∏ i ∈ E,Ideal.span {p i}) : ℂ)/
    (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 : ℝ))).mul_left
    (((Z^(-D) : ℝ) : ℂ)*overlapPairWeight p hg Ψ j 1 1 (initialTest p σ V Z D) G U T)
  apply hs'.congr
  intro h
  rw [←normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ V Φ
    Z D m G U T E hGU hGT hUT h]
  unfold secondPairRadialMode
  ring

theorem initialPhysicalMode_zero_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) {Z : ℝ} (hZ : 0<Z) (D m : ℝ)
    (G U T E : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T)
    (hUT : Disjoint U T) :
    (∑' h : O,initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h) =
      initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E 0 +
      ∑' h : O,if h=0 then 0 else
        initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h :=
  (initialPhysicalMode_summable p hp hcop hg hinj hc hpr Ψ j σ V Φ hZ D m
    G U T E hGU hGT hUT).tsum_eq_add_tsum_ite 0

end RayModes

theorem poolPrimary_norm (F : Finset (Ideal O)) (hF : ∀ I ∈ F,Admissible I)
    (A : Finset (primePool F)) :
    FirstPassCubeLabels.primeProductNorm (poolPrimary F) A = (Ideal.absNorm (∏ i ∈ A,i.val) : ℝ) := by
  unfold FirstPassCubeLabels.primeProductNorm
  rw [eisEmbedding_norm_sq_eq_absNorm_span,FiniteGaussPhase.span_finset_prod]
  simp only [poolPrimary_span F hF]

theorem reconstructedSelector_support (S : Finset (Ideal O)) (P j : Ideal O)
    (a : Ideal O → ℂ) (A : Finset (primePool (columns S P j)))
    (hA : reconstructedSelector S P j a A≠0) : (∏ i ∈ A,i.val)∈columns S P j := by
  by_contra h
  exact hA (by simp only [reconstructedSelector,h,ite_false])

theorem reconstructedSelector_original (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j∣P) (a : Ideal O → ℂ)
    (A : Finset (primePool (columns S P j)))
    (hA : reconstructedSelector S P j a A≠0) :
    Squarefree (∏ i ∈ A,i.val) ∧ IsCoprime (∏ i ∈ A,i.val) j ∧
      residual P j ∣ (∏ i ∈ A,i.val) ∧ reconstruct P j (∏ i ∈ A,i.val)∈S :=
  (mem_columns hP hj).mp (reconstructedSelector_support S P j a A hA)

theorem reconstructedSelector_empty (S : Finset (Ideal O)) (P j : Ideal O)
    (a : Ideal O → ℂ) (h : columns S P j=∅) (A : Finset (primePool (columns S P j))) :
    reconstructedSelector S P j a A=0 := by simp only [reconstructedSelector,h,Finset.notMem_empty,ite_false]

theorem residual_empty (S : Finset (Ideal O)) (P j : Ideal O)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ)
    (h : columns S P j=∅) (u : O) :
    residualNormalizedPolynomial S P j η a W Z r z G u=0 := by
  simp only [residualNormalizedPolynomial,h,Finset.sum_empty,mul_zero]

theorem residual_eq_initialTest (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P)
    (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (u : O) :
    let F := columns S P j
    let hF : ∀ I∈F,Admissible I := fun I hI => columns_admissible S hP hj hS hI
    letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    residualNormalizedPolynomial S P j η a W Z r z G u =
      ((Z^(-(r+z-2*G)/2) : ℝ) : ℂ)*inputConjugateRow (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ (elementCharacter η) (primaryGenerator j) 1 1
        (initialTest (poolPrimary F) (reconstructedSelector S P j a)
          (residualOverlapWindow P j W Z z G) Z (r+z-2*G)) u := by
  intro F hF
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  rw [residual_eq_input S hP hj hS η a W Z r z G u]
  congr 2
  funext A
  simp only [initialTest,poolPrimary_norm F hF]
  rfl

theorem residual_initial_physical_rays (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P)
    (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G m : ℝ) (Φ : 𝓢(ℝ,ℂ)) :
    let F := columns S P j
    let hF : ∀ I∈F,Admissible I := fun I hI => columns_admissible S hP hj hS hI
    letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    (∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) =
    ∑ C ∈ (Finset.univ : Finset (primePool F)).powerset,
      ∑ U ∈ (Finset.univ\C).powerset,∑ T ∈ (Finset.univ\C).powerset,
        if Disjoint U T then ∑ E ∈ C.powerset,∑' h : O,
          initialPhysicalMode (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) (elementCharacter η) (primaryGenerator j)
            (reconstructedSelector S P j a) (residualOverlapWindow P j W Z z G)
            Φ Z (r+z-2*G) m C U T E h else 0 := by
  intro F hF
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  simp_rw [residual_eq_initialTest S hP hj hS η a W Z r z G]
  exact initial_input_physical (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_injective F hF)
    (poolPrimary_odd F hF) (poolPrimary_primary F hF) Finset.univ (elementCharacter η)
    (primaryGenerator j) (reconstructedSelector S P j a) (residualOverlapWindow P j W Z z G)
    Φ hZ (r+z-2*G) m

theorem idealPair_product_transport (F : Finset (Ideal O))
    (hF : ∀ I∈F,Admissible I) (I J : Ideal O) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealPairPoissonKernel F (pool_positive F hF) (pool_good F hF) I J Φ Y =
      GaussGeneratorTransport.squarefreePairProductPoissonKernel (poolPrimary F)
        (poolPrimary_ne_zero F hF) (poolPrimary_injective F hF) (poolPrimary_good F hF)
        (idealSupport F I) (idealSupport F J) Φ Y := by
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) =
      (fun i : primePool F => i.val) := funext (poolPrimary_span F hF)
  have ht := GaussGeneratorTransport.squarefreePairPoissonKernel_eq_product
    (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_injective F hF)
    (poolPrimary_good F hF) (idealSupport F I) (idealSupport F J) Φ Y
  simpa only [he,idealPairPoissonKernel] using ht

end SevenEighths.InverseInitialRayAttachment

end

end OAI

end Source2349

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialConjugateEnergy.lean; sha256: 430517db2b929aa1b0e67a2195daa2ea06e0b8baa0cfafeb7f7b97ec6c1f758b -/
section Source2350
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialConjugateEnergy
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss ConcreteTraceCRT
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialRayAttachment
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def conjugateIdealCharacter (η : Ideal O →* ℂ) : Ideal O →* ℂ where
  toFun I := star (η I)
  map_one' := by rw [map_one,star_one]
  map_mul' I J := by simp [map_mul]

@[simp] theorem conjugateIdealCharacter_apply (η : Ideal O →* ℂ) (I : Ideal O) :
    conjugateIdealCharacter η I = star (η I) := rfl

theorem reconstructedSelector_conjugate (S : Finset (Ideal O)) (P j : Ideal O)
    (a : Ideal O → ℂ) (A : Finset (primePool (columns S P j))) :
    reconstructedSelector S P j (fun I => star (a I)) A =
      star (reconstructedSelector S P j a A) := by
  unfold reconstructedSelector
  split_ifs <;> simp

theorem overlapResidualCoefficient_conjugate (P j : Ideal O) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (c : Ideal O) :
    overlapResidualCoefficient P j (conjugateIdealCharacter η)
        (fun I => star (a I)) (fun x => star (W x)) Z r z G c =
      star (overlapResidualCoefficient P j η a W Z r z G c) := by
  simp [overlapResidualCoefficient, star_mul, mul_comm, mul_left_comm, mul_assoc]

def conjugatedResidual (S : Finset (Ideal O)) (P j : Ideal O) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (u : O) : ℂ :=
  residualNormalizedPolynomial S P j (conjugateIdealCharacter η)
    (fun I => star (a I)) (fun x => star (W x)) Z r z G u

theorem star_conjugatedResidual (S : Finset (Ideal O)) (P j : Ideal O)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    (Z r z G : ℝ) (u : O) :
    star (conjugatedResidual S P j η a W Z r z G u) =
      (Z^(-(r+z-2*G)/2) : ℝ) *
        rowPolynomial (columns S P j) (overlapResidualCoefficient P j η a W Z r z G) u := by
  unfold conjugatedResidual residualNormalizedPolynomial
  simp_rw [overlapResidualCoefficient_conjugate]
  simp [rowPolynomial, mul_comm]

theorem originalFixedPolynomial_eq_conjugatedResidual (S : Finset (Ideal O))
    {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (u : O) :
    originalFixedPolynomial S P j η a W Z r z u =
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) * (Z^(-G) : ℝ) *
        η j^2 * (idealRowHom u j)^2 * star (conjugatedResidual S P j η a W Z r z G u) := by
  rw [originalFixedPolynomial_eq S hP hj η a W hZ r z G,
    star_conjugatedResidual]
  unfold overlapPrefactor
  ring

theorem originalFixedPolynomial_norm_sq_conjugatedResidual (S : Finset (Ideal O))
    {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (u : O) :
    ‖originalFixedPolynomial S P j η a W Z r z u‖^2 =
      Z^(-2*G) * ‖η j‖^4 * ‖idealRowHom u j‖^4 *
        ‖conjugatedResidual S P j η a W Z r z G u‖^2 := by
  rw [originalFixedPolynomial_eq_conjugatedResidual S hP hj η a W hZ r z G]
  have hjn : ‖(moebius j : ℂ)‖=1 := by simp [(hP.squarefree_of_dvd hj).moebius_eq]
  have hpn : ‖(moebius (residual P j) : ℂ)‖=1 := by simp [(residual_squarefree hP hj).moebius_eq]
  have hp : (Z^(-G))^2=Z^(-2*G) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    ring
  simp only [norm_mul,norm_pow,norm_star,hjn,hpn,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ (-G)),mul_pow]
  rw [hp]
  ring

theorem admissible_row_four_le_one (I : Ideal O) (hI : Admissible I) (u : O) :
    ‖idealRowHom u I‖^4 ≤ 1 := by
  have he := norm_idealRowHom_four_eq_two I hI u
  have hs : 0≤‖idealRowHom u I‖^2 := sq_nonneg _
  have ht : ‖idealRowHom u I‖^4=(‖idealRowHom u I‖^2)^2 := by ring
  rw [ht] at he ⊢
  nlinarith

theorem originalFixedPolynomial_norm_sq_le (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j ∣ P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z) (r z G : ℝ) (u : O) :
    ‖originalFixedPolynomial S P j η a W Z r z u‖^2 ≤
      Z^(-2*G) * ‖η j‖^4 * ‖conjugatedResidual S P j η a W Z r z G u‖^2 := by
  rw [originalFixedPolynomial_norm_sq_conjugatedResidual S hP.2.1 hj η a W hZ r z G]
  have hm := admissible_row_four_le_one j (admissible_of_dvd hP hj) u
  have hz := (Real.rpow_pos_of_pos hZ (-2*G)).le
  nlinarith [mul_nonneg hz (pow_nonneg (norm_nonneg (η j)) 4),
    mul_nonneg (mul_nonneg hz (pow_nonneg (norm_nonneg (η j)) 4))
      (sq_nonneg ‖conjugatedResidual S P j η a W Z r z G u‖)]

theorem finite_weighted_triangle {α β : Type*} (J : Finset α) (R : Finset β)
    (w : β → ℝ) (hw : ∀ u,0≤w u) (F : α → β → ℂ) :
    (∑ u ∈ R,w u * ‖∑ j ∈ J,F j u‖^2) ≤
      (∑ j ∈ J,Real.sqrt (∑ u ∈ R,w u*‖F j u‖^2))^2 := by
  let v (j : α) : EuclideanSpace ℂ R :=
    WithLp.toLp 2 (fun u => (Real.sqrt (w u) : ℂ)*F j u)
  have hv (j : α) : ‖v j‖^2=∑ u ∈ R,w u*‖F j u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [v,norm_mul,mul_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hw _)]
    exact Finset.sum_coe_sort R (fun u => w u*‖F j u‖^2)
  have hsum : ‖∑ j ∈ J,v j‖^2=∑ u ∈ R,w u*‖∑ j ∈ J,F j u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [WithLp.ofLp_sum,Finset.sum_apply,v,←Finset.mul_sum,norm_mul,mul_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hw _)]
    exact Finset.sum_coe_sort R (fun u => w u*‖∑ j ∈ J,F j u‖^2)
  have hs := norm_sum_le J v
  have hn (j : α) : ‖v j‖=Real.sqrt (∑ u ∈ R,w u*‖F j u‖^2) := by
    rw [←hv,Real.sqrt_sq (norm_nonneg _)]
  have hh := pow_le_pow_left₀ (norm_nonneg _) hs 2
  simpa only [hsum,hn] using hh

theorem weighted_overlap_triangle {α β : Type*} (J : Finset α)
    (w : β → ℝ) (hw : ∀ u,0≤w u) (F : α → β → ℂ)
    (hs : ∀ j∈J,Summable (fun u => w u*‖F j u‖^2)) :
    Summable (fun u => w u*‖∑ j∈J,F j u‖^2) ∧
      (∑' u,w u*‖∑ j∈J,F j u‖^2) ≤
        (∑ j∈J,Real.sqrt (∑' u,w u*‖F j u‖^2))^2 := by
  have hn (u : β) : 0≤w u*‖∑ j∈J,F j u‖^2 := mul_nonneg (hw u) (sq_nonneg _)
  have hb (R : Finset β) : (∑ u∈R,w u*‖∑ j∈J,F j u‖^2) ≤
      (∑ j∈J,Real.sqrt (∑' u,w u*‖F j u‖^2))^2 := by
    refine (finite_weighted_triangle J R w hw F).trans ?_
    apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))
    apply Finset.sum_le_sum
    intro j hj
    apply Real.sqrt_le_sqrt
    exact (hs j hj).sum_le_tsum R (fun u _ => mul_nonneg (hw u) (sq_nonneg _))
  exact ⟨summable_of_sum_le hn hb,Real.tsum_le_of_sum_le hn hb⟩

def radialWeight (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (u : O) : ℝ :=
  (Φ (‖eisEmbedding u‖^2/Y)).re

def smoothedEnergy (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (f : O → ℂ) : ℝ :=
  ∑' u,radialWeight Φ Y u*‖f u‖^2

theorem radialWeight_nonneg (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re)
    {Y : ℝ} (hY : 0<Y) (u : O) : 0≤radialWeight Φ Y u :=
  hΦ _ (div_nonneg (sq_nonneg _) hY.le)

theorem smoothedEnergy_nonneg (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re)
    {Y : ℝ} (hY : 0<Y) (f : O → ℂ) : 0≤smoothedEnergy Φ Y f :=
  tsum_nonneg (fun u => mul_nonneg (radialWeight_nonneg Φ hΦ hY u) (sq_nonneg _))

theorem original_energy_summable (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) {Y : ℝ} (hY : 0<Y) :
    Summable (fun u => radialWeight Φ Y u*‖originalFixedPolynomial S P j η a W Z r z u‖^2) := by
  have hs := original_fixed_overlap_smoothed_summable S hP hj hS η a W hZ r z G Φ Y hY
  simpa only [radialWeight,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero] using (Complex.hasSum_re hs.hasSum).summable

theorem conjugatedResidual_energy_summable (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) {Y : ℝ} (hY : 0<Y) :
    Summable (fun u => radialWeight Φ Y u*‖conjugatedResidual S P j η a W Z r z G u‖^2) := by
  have hs := residual_normalized_smoothed_summable S hP hj hS (conjugateIdealCharacter η)
    (fun I => star (a I)) (fun x => star (W x)) hZ r z G Φ Y hY
  simpa only [radialWeight,conjugatedResidual,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] using (Complex.hasSum_re hs.hasSum).summable

theorem original_smoothed_mask_identity (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j∣P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    smoothedEnergy Φ Y (originalFixedPolynomial S P j η a W Z r z) =
      Z^(-2*G)*‖η j‖^4 * ∑' u,radialWeight Φ Y u*‖idealRowHom u j‖^4*
        ‖conjugatedResidual S P j η a W Z r z G u‖^2 := by
  unfold smoothedEnergy
  rw [←tsum_mul_left]
  apply tsum_congr
  intro u
  rw [originalFixedPolynomial_norm_sq_conjugatedResidual S hP hj η a W hZ r z G]
  ring

theorem original_smoothed_contraction (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re)
    {Y : ℝ} (hY : 0<Y) :
    smoothedEnergy Φ Y (originalFixedPolynomial S P j η a W Z r z) ≤
      Z^(-2*G)*‖η j‖^4 * smoothedEnergy Φ Y (conjugatedResidual S P j η a W Z r z G) := by
  unfold smoothedEnergy
  rw [←tsum_mul_left]
  apply (original_energy_summable S hP hj hS η a W hZ r z G Φ hY).tsum_le_tsum _
    ((conjugatedResidual_energy_summable S hP hj hS η a W hZ r z G Φ hY).mul_left _)
  intro u
  have hh := mul_le_mul_of_nonneg_left
    (originalFixedPolynomial_norm_sq_le S hP hj η a W hZ r z G u)
    (radialWeight_nonneg Φ hΦ hY u)
  convert hh using 1
  ring

theorem sqrt_overlap_prefactor {Z : ℝ} (hZ : 0<Z) (G : ℝ) (ηj : ℂ) (E : ℝ) :
    Real.sqrt (Z^(-2*G)*‖ηj‖^4*E) = Z^(-G)*‖ηj‖^2*Real.sqrt E := by
  have hz : (Z^(-G))^2=Z^(-2*G) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    ring
  have hp : Z^(-2*G)*‖ηj‖^4=(Z^(-G)*‖ηj‖^2)^2 := by
    rw [mul_pow,hz]
    ring
  rw [hp,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]

def originalTotalPolynomial (S : Finset (Ideal O)) (P : Ideal O) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z : ℝ) (u : O) : ℂ :=
  (Z^(-(r+z)/2) : ℝ) * ∑ n∈S,(moebius n : ℂ)*heckeIdealCharacter η u n*
    heckeIdealCharacter η u P*a n*W ((Ideal.absNorm n : ℝ)/Z^r)

theorem originalTotalPolynomial_eq_sectors (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z : ℝ) (G : Ideal O → ℝ) (u : O) :
    originalTotalPolynomial S P η a W Z r z u =
      ∑ j∈idealDivisors P,originalFixedPolynomial S P j η a W Z r z u := by
  unfold originalTotalPolynomial
  rw [original_normalized_polynomial_hecke_rows S hP η a W hZ r z G]
  apply Finset.sum_congr rfl
  intro j hj
  exact (originalFixedPolynomial_eq S hP ((mem_idealDivisors hP.ne_zero).mp hj)
    η a W hZ r z (G j) u).symm

theorem original_smoothed_overlap_triangle (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Admissible P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z : ℝ) (G : Ideal O → ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) {Y : ℝ} (hY : 0<Y) :
    Summable (fun u => radialWeight Φ Y u*‖originalTotalPolynomial S P η a W Z r z u‖^2) ∧
    Real.sqrt (smoothedEnergy Φ Y (originalTotalPolynomial S P η a W Z r z)) ≤
      ∑ j∈idealDivisors P,Z^(-G j)*‖η j‖^2*
        Real.sqrt (smoothedEnergy Φ Y (conjugatedResidual S P j η a W Z r z (G j))) := by
  have hjd (j : Ideal O) (hj : j∈idealDivisors P) : j∣P := (mem_idealDivisors hP.1).mp hj
  have hs := weighted_overlap_triangle (idealDivisors P) (radialWeight Φ Y)
    (radialWeight_nonneg Φ hΦ hY) (fun j => originalFixedPolynomial S P j η a W Z r z)
    (fun j hj => original_energy_summable S hP (hjd j hj) hS η a W hZ r z (G j) Φ hY)
  simp_rw [←originalTotalPolynomial_eq_sectors S hP.2.1 η a W hZ r z G] at hs
  refine ⟨hs.1,?_⟩
  have hb := Real.sqrt_le_sqrt hs.2
  rw [Real.sqrt_sq (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))] at hb
  refine hb.trans (Finset.sum_le_sum (fun j hj => ?_))
  have hc := Real.sqrt_le_sqrt (original_smoothed_contraction S hP (hjd j hj) hS
    η a W hZ r z (G j) Φ hΦ hY)
  rwa [sqrt_overlap_prefactor hZ] at hc

theorem real_smoothed_sum_eq (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → (Φ x).im=0) {Y : ℝ} (hY : 0<Y) (f : O → ℂ) :
    (∑' u : O,Φ (‖eisEmbedding u‖^2/Y)*(‖f u‖^2 : ℝ)) =
      (smoothedEnergy Φ Y f : ℂ) := by
  unfold smoothedEnergy
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro u
  have he : Φ (‖eisEmbedding u‖^2/Y) = (radialWeight Φ Y u : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hΦ _ (div_nonneg (sq_nonneg _) hY.le)
  rw [he,Complex.ofReal_mul]

theorem original_smoothed_overlap_bound (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Admissible P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z : ℝ) (G : Ideal O → ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) {Y : ℝ} (hY : 0<Y) :
    smoothedEnergy Φ Y (originalTotalPolynomial S P η a W Z r z) ≤
      (∑ j∈idealDivisors P,Z^(-G j)*‖η j‖^2*
        Real.sqrt (smoothedEnergy Φ Y (conjugatedResidual S P j η a W Z r z (G j))))^2 := by
  have ht := (original_smoothed_overlap_triangle S hP hS η a W hZ r z G Φ hΦ hY).2
  have hb := pow_le_pow_left₀ (Real.sqrt_nonneg _) ht 2
  rwa [Real.sq_sqrt (smoothedEnergy_nonneg Φ hΦ hY _)] at hb

def conjugatePhysicalSum (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    (Z r z G m : ℝ) (Φ : 𝓢(ℝ,ℂ)) : ℂ :=
  let F := columns S P j
  let hF : ∀ I∈F,Admissible I := fun I hI => columns_admissible S hP hj hS hI
  letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  ∑ C ∈ (Finset.univ : Finset (primePool F)).powerset,
    ∑ U ∈ (Finset.univ\C).powerset,∑ T ∈ (Finset.univ\C).powerset,
      if Disjoint U T then ∑ E ∈ C.powerset,∑' h : O,
        initialPhysicalMode (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
          (poolPrimary_good F hF) (elementCharacter (conjugateIdealCharacter η)) (primaryGenerator j)
          (reconstructedSelector S P j (fun I => star (a I)))
          (InverseInitialKernelBridge.residualOverlapWindow P j (fun x => star (W x)) Z z G)
          Φ Z (r+z-2*G) m C U T E h else 0

theorem conjugatedResidual_physical (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z G m : ℝ) (Φ : 𝓢(ℝ,ℂ)) :
    (∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖conjugatedResidual S P j η a W Z r z G u‖^2 : ℝ)) =
      conjugatePhysicalSum S hP hj hS η a W Z r z G m Φ := by
  exact residual_initial_physical_rays S hP hj hS (conjugateIdealCharacter η)
    (fun I => star (a I)) (fun x => star (W x)) hZ r z G m Φ

theorem conjugatedResidual_energy_physical (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z G m : ℝ) (Φ : 𝓢(ℝ,ℂ)) :
    smoothedEnergy Φ (Z^m) (conjugatedResidual S P j η a W Z r z G) =
      (conjugatePhysicalSum S hP hj hS η a W Z r z G m Φ).re := by
  have hs := residual_normalized_smoothed_summable S hP hj hS (conjugateIdealCharacter η)
    (fun I => star (a I)) (fun x => star (W x)) hZ r z G Φ (Z^m) (Real.rpow_pos_of_pos hZ m)
  have he := congrArg Complex.re (conjugatedResidual_physical S hP hj hS η a W hZ r z G m Φ)
  change Summable (fun u : O => Φ (‖eisEmbedding u‖^2/Z^m)*
    (‖conjugatedResidual S P j η a W Z r z G u‖^2 : ℝ)) at hs
  rw [Complex.re_tsum hs] at he
  simpa only [smoothedEnergy,radialWeight,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] using he

theorem original_fixed_physical_contraction (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z G m : ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) :
    smoothedEnergy Φ (Z^m) (originalFixedPolynomial S P j η a W Z r z) ≤
      Z^(-2*G)*‖η j‖^4*(conjugatePhysicalSum S hP hj hS η a W Z r z G m Φ).re := by
  rw [←conjugatedResidual_energy_physical S hP hj hS η a W hZ r z G m Φ]
  exact original_smoothed_contraction S hP hj hS η a W hZ r z G Φ hΦ
    (Real.rpow_pos_of_pos hZ m)

theorem original_physical_overlap_triangle (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Admissible P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z m : ℝ) (G : Ideal O → ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) :
    Real.sqrt (smoothedEnergy Φ (Z^m) (originalTotalPolynomial S P η a W Z r z)) ≤
      ∑ j : idealDivisors P,Z^(-G j)*‖η j‖^2*
        Real.sqrt ((conjugatePhysicalSum S hP ((mem_idealDivisors hP.1).mp j.property)
          hS η a W Z r z (G j) m Φ).re) := by
  have ht := (original_smoothed_overlap_triangle S hP hS η a W hZ r z G Φ hΦ
    (Real.rpow_pos_of_pos hZ m)).2
  rw [←Finset.sum_coe_sort] at ht
  convert ht using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [conjugatedResidual_energy_physical S hP ((mem_idealDivisors hP.1).mp j.property)
    hS η a W hZ r z (G j) m Φ]

theorem original_smoothed_overlap_cauchy (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Admissible P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z : ℝ) (G : Ideal O → ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) {Y : ℝ} (hY : 0<Y) :
    smoothedEnergy Φ Y (originalTotalPolynomial S P η a W Z r z) ≤
      (∑ j∈idealDivisors P,Z^(-G j)*‖η j‖^2) *
        ∑ j∈idealDivisors P,Z^(-G j)*‖η j‖^2*
          smoothedEnergy Φ Y (conjugatedResidual S P j η a W Z r z (G j)) := by
  refine (original_smoothed_overlap_bound S hP hS η a W hZ r z G Φ hΦ hY).trans ?_
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro j _
    exact mul_nonneg (Real.rpow_nonneg hZ.le _) (sq_nonneg _)
  · intro j _
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _) (sq_nonneg _))
      (smoothedEnergy_nonneg Φ hΦ hY _)
  · intro j _
    rw [mul_pow,Real.sq_sqrt (smoothedEnergy_nonneg Φ hΦ hY _)]
    nlinarith

theorem original_complex_physical_overlap_bound (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Admissible P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z m : ℝ) (G : Ideal O → ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) (hΦreal : ∀ x : ℝ,0≤x → (Φ x).im=0) :
    ‖∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖originalTotalPolynomial S P η a W Z r z u‖^2 : ℝ)‖ ≤
      (∑ j : idealDivisors P,Z^(-G j)*‖η j‖^2*
        Real.sqrt ((conjugatePhysicalSum S hP ((mem_idealDivisors hP.1).mp j.property)
          hS η a W Z r z (G j) m Φ).re))^2 := by
  have hY := Real.rpow_pos_of_pos hZ m
  rw [real_smoothed_sum_eq Φ hΦreal hY,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (smoothedEnergy_nonneg Φ hΦ hY _)]
  have ht := original_physical_overlap_triangle S hP hS η a W hZ r z m G Φ hΦ
  have hb := pow_le_pow_left₀ (Real.sqrt_nonneg _) ht 2
  rwa [Real.sq_sqrt (smoothedEnergy_nonneg Φ hΦ hY _)] at hb

end SevenEighths.InverseInitialConjugateEnergy

end

end OAI

end Source2350

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialPhysicalMeasure.lean; sha256: f8c30dfe6e3c01cb7c26f0cae5b1c0016e57abe0f3e12765bf12c81c251bb009 -/
section Source2351
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

namespace SevenEighths.InverseInitialPhysicalMeasure
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialRayAttachment
open InverseInitialKernelBridge InverseInitialProfile InverseInitialClippedColumns
open MeasureTheory FourierBridge JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

@[ext] structure Point (ι : Type*) where
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  left : Finset ι
  right : Finset ι
  frequency : O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})

def divisor (x : Point ι) : O := primeSubsetGenerator (fun i=>Ideal.span {p i}) x.divisor

def quotient (x : Point ι) : O := primaryGenerator (sourceIdeal p (x.common\x.divisor))

def coordinates (x : Point ι) : Fin 6 → ℝ :=
  physicalCoordinates (sourceIdeal p x.common) (sourceIdeal p x.divisor)
    (sourceIdeal p x.overlap) (sourceIdeal p x.left) (sourceIdeal p x.right) x.frequency

structure Valid (x : Point ι) : Prop where
  divisor_subset : x.divisor⊆x.common
  overlap_left : Disjoint x.overlap x.left
  overlap_right : Disjoint x.overlap x.right
  frequency_nonzero : x.frequency≠0

include hp in
omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem coordinates_pos (x : Point ι) (hx : Valid x) : ∀ i,0<coordinates p x i :=
  physicalCoordinates_pos _ _ _ _ _ _ (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _) hx.frequency_nonzero

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem divisor_span (x : Point ι) : Ideal.span {divisor p x}=sourceIdeal p x.divisor := by
  simpa only [divisor,sourceIdeal,FiniteGaussPhase.span_finset_prod] using
    pairDivisor_span (fun i=>Ideal.span {p i}) x.divisor

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem quotient_span (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) :
    Ideal.span {quotient p x}=sourceIdeal p (x.common\x.divisor) := by
  rw [quotient,sourceIdeal_gen p hp hpr]
  rfl

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem common_span (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) (hx : Valid x) :
    Ideal.span {divisor p x*quotient p x}=sourceIdeal p x.common := by
  rw [←Ideal.span_singleton_mul_span_singleton,divisor_span p,quotient_span p hp hpr,
    ←sourceIdeal_union p _ _ (Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hx.divisor_subset]

include hp in
def unitSector (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) : Oˣ :=
  Classical.choose (generator_eq_unit_primary (sourceIdeal p x.divisor) (divisor p x)
    (divisor_span p x) (by rw [sourceIdeal_gen p hp hpr]; exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem unitSector_spec (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) :
    divisor p x=(unitSector p hp hpr x:O)*primaryGenerator (sourceIdeal p x.divisor) :=
  Classical.choose_spec (generator_eq_unit_primary (sourceIdeal p x.divisor) (divisor p x)
    (divisor_span p x) (by rw [sourceIdeal_gen p hp hpr]; exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

theorem child_normalized (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι)
    (Ψ : O →* ℂ) (j h : O) (H : Finset ι→ℂ) (N : Finset ι) :
    secondChildColumn p hp hcop hg Ψ (j*quotient p x)
      (divisor p x*∏ i∈x.overlap,p i) (divisor p x*h) H N =
    secondChildColumn p hp hcop hg Ψ (j*quotient p x)
      (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
      (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h)) H N := by
  obtain ⟨u,hu,he⟩ := initial_poisson_child_normalized p hp hcop hg hpr
    x.common x.divisor x.overlap Ψ j (divisor p x) (quotient p x) h
    (divisor_span p x) (quotient_span p hp hpr x)
  have hgen : primaryGenerator (sourceIdeal p x.divisor)≠0 := by
    rw [sourceIdeal_gen p hp hpr];exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hu' : u=unitSector p hp hpr x := Units.val_injective
    (mul_right_cancel₀ hgen (hu.symm.trans (unitSector_spec p hp hpr x)))
  simpa only [hu',quotient] using he H N

include hp hcop hg in
theorem column_extraction (hpr : ∀ i,goodLambda^2∣p i-1)
    (x : Point ι) (hx : Valid x) (Ψ : O →* ℂ) (j h : O)
    (σ : Finset ι→ℂ) (N : Finset ι) (hN : Disjoint x.overlap N) :
    initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h
      (fun A=>σ (x.common∪A)) (x.overlap∪N) =
      initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h (fun _=>1) x.overlap *
      secondChildColumn p hp hcop hg Ψ (j*quotient p x)
        (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
        (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h))
        (fun A=>σ (x.common∪(x.overlap∪A))) N := by
  have hm (A : Finset ι) :
      rowCoprimeMask (fun i=>Ideal.span {p i}) A (j*∏ i∈x.common,p i)=
      rowCoprimeMask (fun i=>Ideal.span {p i}) A (j*(divisor p x*quotient p x)) :=
    rowCoprimeMask_mul_eq_of_span_eq _ A j (common_span p hp hpr x hx).symm
  have hc (H : Finset ι→ℂ) (A : Finset ι) :
      initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h H A =
      initialColumn p hp hcop hg Ψ j (divisor p x*quotient p x) (divisor p x) h H A := by
    simp only [initialColumn,hm]
  rw [hc,initial_common_extraction p hp hcop hg hpr Ψ j (quotient p x) (divisor p x) h _ _ _ hN,
    ←hc,child_normalized p hp hcop hg hpr]

def outerCoefficient (Ψ : O →* ℂ) (j : O) (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius (fun i=>Ideal.span {p i}) x.overlap * secondRayCoefficient ρ *
    star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
      (divisor p x) x.frequency (fun _=>1) x.overlap) *
    initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
      (divisor p x) (-x.frequency) (fun _=>1) x.overlap

def canonicalColumn (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ) (x : Point ι) (h : O)
    (H : Finset ι→ℂ) (N : Finset ι) : ℂ :=
  secondChildColumn p hp hcop hg Ψ (j*quotient p x)
    (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
    (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h))
    (fun A=>σ (x.common∪(x.overlap∪A))*H A) N

def physicalTerm (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  (initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius (fun i=>Ideal.span {p i}) x.overlap * secondRayCoefficient ρ) *
  star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) x.frequency (fun A=>σ (x.common∪A)) (x.overlap∪x.left)) *
  initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=>σ (x.common∪A)) (x.overlap∪x.right) *
  physicalKernel W₁ W₂ Φ Z D m
    (physicalCoordinates (sourceIdeal p x.common) (sourceIdeal p x.divisor) 1
      (sourceIdeal p (x.overlap∪x.left)) (sourceIdeal p (x.overlap∪x.right)) x.frequency)

include hp hcop hg in
theorem physicalTerm_extracted (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (x : Point ι) (hx : Valid x) (ρ : SecondRayIndex) :
    physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ =
      outerCoefficient p hp hcop hg Ψ j x ρ *
      star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j σ x x.frequency (fun _=>1) x.left) *
      canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j σ x (-x.frequency) (fun _=>1) x.right *
      physicalKernel W₁ W₂ Φ Z D m (coordinates p x) := by
  unfold physicalTerm
  rw [column_extraction p hp hcop hg hpr x hx _ _ _ σ _ hx.overlap_left,
    column_extraction p hp hcop hg hpr x hx _ _ _ σ _ hx.overlap_right,
    sourceIdeal_union p _ _ hx.overlap_left,sourceIdeal_union p _ _ hx.overlap_right,
    physicalKernel_common_factor]
  simp only [canonicalColumn,mul_one,star_mul,outerCoefficient,coordinates]
  ring

def barePair (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι→ℂ) (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  outerCoefficient p hp hcop hg Ψ j x ρ *
    star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j σ x x.frequency (fun _=>1) x.left) *
    canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j σ x (-x.frequency) (fun _=>1) x.right

def columnRatio (N : Finset ι) (Z D B v : ℝ) : ℝ :=
  (Ideal.absNorm (sourceIdeal p N):ℝ)/Z^(columnCenter D B v)

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem relative_column_left (x : Point ι) (Z D B v θ H : ℝ) :
    relativeNorm (coordinates p x) Z D B v θ H 4=columnRatio p x.left Z D B v := rfl

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem relative_column_right (x : Point ι) (Z D B v θ H : ℝ) :
    relativeNorm (coordinates p x) Z D B v θ H 5=columnRatio p x.right Z D B v := rfl

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem columnRatio_actual (N : Finset ι) (Z D B v : ℝ) :
    columnRatio p N Z D B v=primeProductNorm p N/Z^(columnCenter D B v) := by
  unfold columnRatio sourceIdeal primeProductNorm
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]

def canonicalPairMode (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι→ℂ) (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (x : Point ι) (ρ : SecondRayIndex) (z : Frequency × (Fin 6→ℝ)) : ℂ :=
  let height :=  profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
  outerCoefficient p hp hcop hg Ψ j x ρ *
    secondOuterPhase height (relativeLog (coordinates p x) Z D B v θ H) *
    star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j σ x x.frequency
      (fun A=>childLogTest ω₁ (-height 4) (columnRatio p A Z D B v)) x.left) *
    canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j σ x (-x.frequency)
      (fun A=>childLogTest ω₂ (height 5) (columnRatio p A Z D B v)) x.right

theorem canonical_pair_mode (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι→ℂ) (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (x : Point ι) (ρ : SecondRayIndex) (z : Frequency × (Fin 6→ℝ)) :
    barePair p hp hcop hg hpr Ψ j σ x ρ *
      (star (ω₁ (columnRatio p x.left Z D B v))*ω₂ (columnRatio p x.right Z D B v)) *
      pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
        (relativeLog (coordinates p x) Z D B v θ H) z.1 z.2 =
      canonicalPairMode p hp hcop hg hpr Ψ j σ ω₁ ω₂ Z D B v θ H x ρ z := by
  rw [second_mode_split]
  simp only [canonicalPairMode,barePair,canonicalColumn,secondChildColumn,childLogTest,
    star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,relativeLog,
    relative_column_left,relative_column_right,mul_one]
  ring

theorem family_density_finite_sum {κ : Type*} (s : Finset κ)
    (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ)) (c₁ c₂ θ₁ θ₂ L : ℝ)
    (c : κ→ℂ) (y : κ→Fin 6→ℝ) :
    (∑ k∈s,c k*∫ z : Frequency × (Fin 6→ℝ),
      familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y k) z.1 z.2) =
    ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z *
      ∑ k∈s,c k*pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y k) z.1 z.2 := by
  simp only [familyDensity,mul_assoc,integral_const_mul]
  have he := full_density_finite_sum s g (𝓕 (clippedTwist g₁ c₁ θ₁))
    (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ secondLeftSlope secondRightSlope secondKernelSlope c y
  calc
    _ = (Real.exp (-3*L):ℂ)*∑ k∈s,c k*∫ z : Frequency × (Fin 6→ℝ),
        fullProfileDensity g (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ z *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y k) z.1 z.2 := by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro k hk;ring
    _ = _ := by rw [he]

def physicalBlock (source : Finset (Point ι)) (w : Point ι→ℂ)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) : ℂ :=
  ∑ x∈source,∑ ρ : SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ

def canonicalBlock (hpr : ∀ i,goodLambda^2∣p i-1)
    (source : Finset (Point ι)) (w : Point ι→ℂ) (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ) (z : Frequency × (Fin 6→ℝ)) : ℂ :=
  ∑ x∈source,∑ ρ : SecondRayIndex,w x*canonicalPairMode p hp hcop hg hpr Ψ j σ ω₁ ω₂ Z D B v θ H x ρ z

theorem physicalBlock_integral
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6→ℝ→ℂ)
    (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ)
    (hid : PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂)
    (source : Finset (Point ι)) (hs : ∀ x∈source,Valid x)
    (w : Point ι→ℂ) (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ) (ω₁ ω₂ : ℝ→ℂ)
    (hω₁ : ∀ x∈source,clippedSource W₁ c₁ θ₁
      (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
        relativeNorm (coordinates p x) Z D B v θ H 4)≠0 → star (ω₁ (columnRatio p x.left Z D B v))=1)
    (hω₂ : ∀ x∈source,clippedSource W₂ c₂ θ₂
      (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
        relativeNorm (coordinates p x) Z D B v θ H 5)≠0 → ω₂ (columnRatio p x.right Z D B v)=1)
    (hcut : ∀ x∈source,star (ω₁ (columnRatio p x.left Z D B v))≠0 →
      ω₂ (columnRatio p x.right Z D B v)≠0 → ∀ i,V i (relativeLog (coordinates p x) Z D B v θ H i)=1) :
    physicalBlock p hp hcop hg source w Ψ j σ (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
      (Z^(prefactorCenter m D B θ+3*η):ℝ)*
      ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
        canonicalBlock p hp hcop hg hpr source w Ψ j σ ω₁ ω₂ Z D B v θ H z := by
  let S := source ×ˢ (Finset.univ : Finset SecondRayIndex)
  let c := fun a : Point ι × SecondRayIndex => w a.1*barePair p hp hcop hg hpr Ψ j σ a.1 a.2 *
    (star (ω₁ (columnRatio p a.1.left Z D B v))*ω₂ (columnRatio p a.1.right Z D B v))
  let y := fun a : Point ι × SecondRayIndex => relativeLog (coordinates p a.1) Z D B v θ H
  have he := family_density_finite_sum S g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) c y
  have hpnt (x : Point ι) (hx : x∈source) (ρ : SecondRayIndex) :
      w x*physicalTerm p hp hcop hg Ψ j σ (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m x ρ =
      (Z^(prefactorCenter m D B θ+3*η):ℝ)*c (x,ρ)*
        ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y (x,ρ)) z.1 z.2 := by
    rw [physicalTerm_extracted p hp hcop hg hpr Ψ j σ _ _ Φ Z D m x (hs x hx) ρ]
    rw [hid (fun r=>star (ω₁ r)) ω₂ (coordinates p x) (coordinates_pos p hp x (hs x hx))
      (hω₁ x hx) (hω₂ x hx) (hcut x hx)]
    dsimp only [c,y,barePair]
    rw [relative_column_left,relative_column_right]
    ring
  have hsumeq : physicalBlock p hp hcop hg source w Ψ j σ
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
      (Z^(prefactorCenter m D B θ+3*η):ℝ)*
        ∑ a∈S,c a*∫ z : Frequency × (Fin 6→ℝ),
          familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y a) z.1 z.2 := by
    simp only [physicalBlock,S,Finset.sum_product,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [hpnt x hx ρ]
    ring
  rw [hsumeq,he]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  simp only [S,Finset.sum_product,canonicalBlock,c,y]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mul_assoc (w x),mul_assoc (w x),canonical_pair_mode]

theorem original_ray_common_insertion
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F G E : Finset ι) (h : O) (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) :
    (∑ U∈F.powerset,∑ T∈F.powerset,if Disjoint U T then
      initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E h else 0) =
    ∑ V∈F.powerset,∑ N₁∈(F\V).powerset,∑ N₂∈(F\V).powerset,
      ∑ ρ : SecondRayIndex,physicalTerm p hp hcop hg Ψ j σ (fun x=>star (W x)) W Φ Z D m
        ⟨G,E,V,N₁,N₂,h⟩ ρ := by
  rw [CoprimeMobiusExtension.double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro V hV
  rw [←prime_product_moebius (fun i=>Ideal.span {p i})
    (fun i=>Ideal.prime_of_isPrime (NeZero.ne _) inferInstance) hinj V]
  simp only [Finset.mul_sum,initialPhysicalMode,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro N₁ hN₁
  apply Finset.sum_congr rfl
  intro N₂ hN₂
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [physicalTerm,divisor,supportMobius]
  ring

theorem physicalBlock_zero (source : Finset (Point ι)) (w : Point ι→ℂ)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (hw : ∀ x∈source,w x=0) : physicalBlock p hp hcop hg source w Ψ j σ W₁ W₂ Φ Z D m=0 := by
  unfold physicalBlock
  apply Finset.sum_eq_zero
  intro x hx
  simp only [hw x hx,zero_mul,Finset.sum_const_zero]

include hp in
omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem child_test_clipping (w₀ : ℝ→ℂ) {Z : ℝ} (hZ : 0<Z)
    (N t : ℝ) (A : Finset ι) :
    childLogTest w₀ t ((Ideal.absNorm (sourceIdeal p A):ℝ)/Z^N) =
      logPhase t ((max 0 N-N)*Real.log Z) *
        clippedTest w₀ (Z^(max 0 N-N)) t
          ((Ideal.absNorm (sourceIdeal p A):ℝ)/Z^(max 0 N)) := by
  rw [clippedTest_eq_source]
  simpa only [childLogTest,Real.log_rpow hZ,mul_comm] using
    clipped_column_source_identity w₀ hZ
      (QuadraticMainBoundary.norm_pos (sourceIdeal_ne_zero p hp A)) N t

def BlockSupport (source : Finset (Point ι)) (W₁ W₂ ω₁ ω₂ : ℝ→ℂ)
    (V : Fin 6→ℝ→ℂ) (Z D B v θ H c₁ c₂ θ₁ θ₂ : ℝ) : Prop :=
  (∀ x∈source,clippedSource W₁ c₁ θ₁
    (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
      relativeNorm (coordinates p x) Z D B v θ H 4)≠0 → star (ω₁ (columnRatio p x.left Z D B v))=1) ∧
  (∀ x∈source,clippedSource W₂ c₂ θ₂
    (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
      relativeNorm (coordinates p x) Z D B v θ H 5)≠0 → ω₂ (columnRatio p x.right Z D B v)=1) ∧
  (∀ x∈source,star (ω₁ (columnRatio p x.left Z D B v))≠0 →
    ω₂ (columnRatio p x.right Z D B v)≠0 → ∀ i,V i (relativeLog (coordinates p x) Z D B v θ H i)=1)

theorem actual_initial_block_common_measure
    (W₁ W₂ : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6→ℝ→ℂ) (M : Fin 6→ℝ)
    (hV : ∀ i,ContDiff ℝ ∞ (V i)) (hS : ∀ i,HasCompactSupport (V i))
    (hM : ∀ i,0≤M i) (hbox : ∀ i y,V i y≠0 → |y|≤M i) (A J : ℕ) :
    let g := secondRootSchwartz V hV hS
    let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
    let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
    ∃ C : ℝ,0≤C ∧ ∀ Z D B v m θ H η : ℝ,0<Z → 0≤η*Real.log Z →
      ∃ b₃ : 𝓢(ℝ,ℂ),∀ c₁ c₂ θ₁ θ₂ : ℝ,0<c₁ → 0<c₂ →
      (∀ {κ : Type*} [DecidableEq κ] (p : κ→O) (hp : ∀ i,p i≠0)
        [∀ i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
        (hg : ∀ i,goodLambda∉Ideal.span {p i}) (hpr : ∀ i,goodLambda^2∣p i-1)
        (source : Finset (Point κ)) (_hs : ∀ x∈source,Valid x)
        (w : Point κ→ℂ) (Ψ : O →* ℂ) (j : O) (σ : Finset κ→ℂ) (ω₁ ω₂ : ℝ→ℂ),
        BlockSupport p source W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂ →
        physicalBlock p hp hcop hg source w Ψ j σ
          (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
          (Z^(prefactorCenter m D B θ+3*η):ℝ)*
            ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
              canonicalBlock p hp hcop hg hpr source w Ψ j σ ω₁ ω₂ Z D B v θ H z) ∧
      Integrable (fun z : Frequency × (Fin 6→ℝ)=>tripleHeight J z.1*coordinateHeight J z.2*
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z‖) ∧
      (1+Z^(radialCenter m H θ D B))^A *
        (∫ z : Frequency × (Fin 6→ℝ),tripleHeight J z.1*coordinateHeight J z.2*
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z‖) ≤
        C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J*(1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) := by
  dsimp only
  obtain ⟨C,hC,hfamily⟩ := initial_physical_family_common_measure
    W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨C,hC,?_⟩
  intro Z D B v m θ H η hZ hL
  obtain ⟨b₃,hb₃⟩ := hfamily Z D B v m θ H η hZ hL
  refine ⟨b₃,?_⟩
  intro c₁ c₂ θ₁ θ₂ hc₁ hc₂
  obtain ⟨hid,hi,hb⟩ := hb₃ c₁ c₂ θ₁ θ₂ hc₁ hc₂
  refine ⟨?_,hi,hb⟩
  intro κ _ p hp _ hcop hg hpr source hs w Ψ j σ ω₁ ω₂ hsupport
  exact physicalBlock_integral p hp hcop hg hpr W₁ W₂ Φ V _ _ _ b₃
    Z D B v m θ H η c₁ c₂ θ₁ θ₂ hid source hs w Ψ j σ ω₁ ω₂
    hsupport.1 hsupport.2.1 hsupport.2.2

open InverseInitialOverlap InverseInitialPoissonBridge CanonicalQuadraticSieve

def overlapDilation (P j : Ideal O) (Z z G : ℝ) : ℝ :=
  ((Ideal.absNorm j:ℝ)/Z^G)/((Ideal.absNorm (residual P j):ℝ)/Z^(z-G))

theorem residualWindow_eq_clipped (P j : Ideal O) (W : ℝ→ℂ) (Z z G : ℝ) :
    residualOverlapWindow P j W Z z G=clippedSource W (overlapDilation P j Z z G) 0 := by
  funext x
  simp only [residualOverlapWindow,clippedSource,logPhase,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,overlapDilation]
  congr 1
  ring

theorem overlapDilation_pos {P j : Ideal O} (hP : Admissible P) (hj : j∣P)
    {Z : ℝ} (hZ : 0<Z) (z G : ℝ) : 0<overlapDilation P j Z z G := by
  exact div_pos (div_pos (QuadraticMainBoundary.norm_pos (admissible_of_dvd hP hj).2.1.ne_zero)
      (Real.rpow_pos_of_pos hZ _))
    (div_pos (QuadraticMainBoundary.norm_pos (residual_squarefree hP.2.1 hj).ne_zero)
      (Real.rpow_pos_of_pos hZ _))

theorem clippedSource_zero_star (W : ℝ→ℂ) (c : ℝ) :
    (fun x=>star (clippedSource W c 0 x))=clippedSource (fun x=>star (W x)) c 0 := by
  funext x
  simp [clippedSource,logPhase]

def originalBlock (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z r z G m : ℝ) (source : Finset (Point (primePool (columns S P j))))
    (w : Point (primePool (columns S P j))→ℂ) : ℂ :=
  let F := columns S P j
  let hF : ∀ I∈F,Admissible I := fun I hI=>columns_admissible S hP hj hS hI
  letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  physicalBlock (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) source w (elementCharacter η) (primaryGenerator j)
    (reconstructedSelector S P j a) (fun x=>star (residualOverlapWindow P j W Z z G x))
    (residualOverlapWindow P j W Z z G) Φ Z (r+z-2*G) m

theorem originalBlock_integral
    (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6→ℝ→ℂ) (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (Z r z G B v m θ H ε : ℝ)
    (hid : PhysicalIdentityAt (fun x=>star (W x)) W Φ V g g₁ g₂ b₃
      Z (r+z-2*G) B v m θ H ε (overlapDilation P j Z z G) (overlapDilation P j Z z G) 0 0)
    (source : Finset (Point (primePool (columns S P j)))) (hs : ∀ x∈source,Valid x)
    (w : Point (primePool (columns S P j))→ℂ) (ω₁ ω₂ : ℝ→ℂ)
    (hcut : BlockSupport (poolPrimary (columns S P j)) source (fun x=>star (W x)) W ω₁ ω₂ V
      Z (r+z-2*G) B v θ H (overlapDilation P j Z z G) (overlapDilation P j Z z G) 0 0) :
    let F := columns S P j
    let hF : ∀ I∈F,Admissible I := fun I hI=>columns_admissible S hP hj hS hI
    letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    originalBlock S hP hj hS η a W Φ Z r z G m source w =
      (Z^(prefactorCenter m (r+z-2*G) B θ+3*ε):ℝ)*
        ∫ q : Frequency × (Fin 6→ℝ),
          familyDensity g g₁ g₂ b₃ (overlapDilation P j Z z G) (overlapDilation P j Z z G)
            0 0 (ε*Real.log Z) q *
          canonicalBlock (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) (poolPrimary_primary F hF) source w (elementCharacter η)
            (primaryGenerator j) (reconstructedSelector S P j a) ω₁ ω₂ Z (r+z-2*G) B v θ H q := by
  intro F hF
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  unfold originalBlock
  rw [residualWindow_eq_clipped,clippedSource_zero_star]
  exact physicalBlock_integral (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) (poolPrimary_primary F hF) _ _ Φ V g g₁ g₂ b₃
    Z (r+z-2*G) B v m θ H ε _ _ 0 0 hid source hs w (elementCharacter η)
    (primaryGenerator j) (reconstructedSelector S P j a) ω₁ ω₂ hcut.1 hcut.2.1 hcut.2.2

end SevenEighths.InverseInitialPhysicalMeasure

end

end OAI

end Source2351

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerModes.lean; sha256: 0cc5a9225d8e6dd2d579daf5c55f04fd9b58ab23ff005b18abbd11abea14e819 -/
section Source2352
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialPhysicalMeasure SevenEighths.InverseInitialKernelBridge
open SevenEighths.InverseInitialEnergyCallerFamily SevenEighths.InverseInitialProfile
namespace SevenEighths.InverseInitialEnergyCallerModes
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonicalColumn_marked_sum
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x : Point ι) (hE : x.divisor⊆x.common)
    (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (Z D B v : ℝ) :
    (∑ N∈(F\x.overlap).powerset,
      canonicalColumn p hp hcop hg hpr Ψ j (primeMark slots lists a) x h
        (fun A=>W (columnRatio p A Z D B v)) N) =
      ∑ J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
        finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*quotient p x)
          (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
          (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:Eis)^5*h))
          (slots\J) lists a W (Z^(columnCenter D B v)) := by
  have hgen (A : Finset ι) : primaryGenerator (sourceIdeal p A)≠0 := by
    rw [sourceIdeal_gen p hp hpr A]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hd : Ideal.span {primaryGenerator (sourceIdeal p x.divisor)}=sourceIdeal p x.divisor :=
    (primaryGenerator_spec _ (hgen _)).1
  have ht : Ideal.span {quotient p x}=sourceIdeal p (x.common\x.divisor) :=
    (primaryGenerator_spec _ (hgen _)).1
  obtain ⟨u,hu,hsplit⟩ := fresh_initial_split_fixed_family p hp hcop hg hpr
    x.common x.divisor x.overlap hE (primaryGenerator (sourceIdeal p x.divisor))
    (quotient p x) hd ht (σ:=σ)
  have hu1 : u=1 := by
    apply Units.val_injective
    apply mul_right_cancel₀ (hgen x.divisor)
    simpa only [Units.val_one,one_mul] using hu.symm
  subst u
  have he := hsplit F Ψ j ((unitSector p hp hpr x:Eis)^5*h) slots lists a W
    (Z^(columnCenter D B v))
  simp only [Units.val_one,one_pow,one_mul] at he
  convert he using 1
  · apply Finset.sum_congr rfl
    intro N hN
    simp only [canonicalColumn,primaryGenerator_mul,sourceIdeal_gen p hp hpr x.overlap,
      secondChildColumn,columnRatio_actual,Finset.union_assoc]
  · rfl

def sourcePoint (x : Source (ι:=ι) 0) (N M : Finset ι) : Point ι where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  left := N
  right := M
  frequency := x.frequency

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourcePoint_outer_phase (x : Source (ι:=ι) 0) (N M : Finset ι)
    (height : Fin 6→ℝ) (Z D B v θ H : ℝ) :
    secondOuterPhase height (relativeLog (coordinates p (sourcePoint x N M)) Z D B v θ H) =
    secondOuterPhase height (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H) := by
  have hc₀ : coordinates p (sourcePoint x N M) 0=coordinates p (sourcePoint x ∅ ∅) 0 := by
    simp [coordinates,physicalCoordinates,sourcePoint]
  have hc₁ : coordinates p (sourcePoint x N M) 1=coordinates p (sourcePoint x ∅ ∅) 1 := by
    simp [coordinates,physicalCoordinates,sourcePoint]
  have hc₂ : coordinates p (sourcePoint x N M) 2=coordinates p (sourcePoint x ∅ ∅) 2 := by
    simp [coordinates,physicalCoordinates,sourcePoint]
  have hc₃ : coordinates p (sourcePoint x N M) 3=coordinates p (sourcePoint x ∅ ∅) 3 := by
    simp [coordinates,physicalCoordinates,sourcePoint]
  simp [secondOuterPhase,relativeLog,relativeNorm,secondRelativeNorm,hc₀,hc₁,hc₂,hc₃]

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem sourcePoint_unitSector
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x : Source (ι:=ι) 0) (N M : Finset ι) :
    unitSector p hp hpr (sourcePoint x N M)=unitSector p hp hpr (sourcePoint x ∅ ∅) := by
  have hgen : primaryGenerator (sourceIdeal p x.divisor)≠0 := by
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  apply Units.val_injective
  apply mul_right_cancel₀ hgen
  exact (unitSector_spec p hp hpr (sourcePoint x N M)).symm.trans
    (unitSector_spec p hp hpr (sourcePoint x ∅ ∅))

def markedModeColumn (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (j h : Eis) (x : Source (ι:=ι) 0)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (Z D B v : ℝ) : ℂ :=
  ∑ J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
    finiteCanonicalMarkedRow p hp hcop hg F Ψ
      (j*quotient p (sourcePoint x ∅ ∅))
      (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
      (primaryGenerator (sourceIdeal p x.divisor)*
        ((unitSector p hp hpr (sourcePoint x ∅ ∅):Eis)^5*h))
      (slots\J) lists a W (Z^(columnCenter D B v))

theorem canonicalPairMode_rectangle
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x : Source (ι:=ι) 0) (hE : x.divisor⊆x.common)
    (F : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ) (ρ : SecondRayIndex)
    (z : JointLogSeparation.Frequency × (Fin 6→ℝ)) :
    let height := profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
    (∑ N∈(F\x.overlap).powerset,∑ M∈(F\x.overlap).powerset,
      canonicalPairMode p hp hcop hg hpr Ψ j (primeMark slots lists a) ω₁ ω₂
        Z D B v θ H (sourcePoint x N M) ρ z) =
    (outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ *
      secondOuterPhase height (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H)) *
    (star (markedModeColumn p hp hcop hg hpr F (secondRayMinus Ψ ρ) j x.frequency x
        slots lists a (childLogTest ω₁ (-height 4)) Z D B v) *
      markedModeColumn p hp hcop hg hpr F (secondRayPlus Ψ ρ) j (-x.frequency) x
        slots lists a (childLogTest ω₂ (height 5)) Z D B v) := by
  dsimp only
  let x₀ := sourcePoint x ∅ ∅
  have hpoint (N M : Finset ι) :
      canonicalPairMode p hp hcop hg hpr Ψ j (primeMark slots lists a) ω₁ ω₂
        Z D B v θ H (sourcePoint x N M) ρ z =
      (outerCoefficient p hp hcop hg Ψ j x₀ ρ *
        secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2)
          (relativeLog (coordinates p x₀) Z D B v θ H)) *
      star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j (primeMark slots lists a) x₀ x.frequency
        (fun A=>childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4)
          (columnRatio p A Z D B v)) N) *
      canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j (primeMark slots lists a) x₀ (-x.frequency)
        (fun A=>childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5)
          (columnRatio p A Z D B v)) M := by
    unfold InverseInitialPhysicalMeasure.canonicalPairMode
    dsimp only
    rw [sourcePoint_outer_phase p x N M
      (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) Z D B v θ H]
    simp only [canonicalColumn]
    simp only [sourcePoint_unitSector p hp hpr x N M]
    simp only [outerCoefficient,sourcePoint,divisor,quotient,x₀]
  simp_rw [hpoint,←Finset.mul_sum]
  rw [←Finset.sum_mul,←Finset.mul_sum,←star_sum]
  have hleft := canonicalColumn_marked_sum p hp hcop hg hpr x₀ hE F (secondRayMinus Ψ ρ) j x.frequency
      slots lists a (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4)) Z D B v
  have hright := canonicalColumn_marked_sum p hp hcop hg hpr x₀ hE F (secondRayPlus Ψ ρ) j (-x.frequency)
      slots lists a (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5)) Z D B v
  dsimp only [x₀,sourcePoint] at hleft hright ⊢
  rw [hleft,hright]
  simp only [markedModeColumn,sourcePoint]
  ring

end SevenEighths.InverseInitialEnergyCallerModes

end

end OAI

end Source2352

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerSource.lean; sha256: 5671d3acdf2899bfb4af5e3730662e0802138434c8936a1f8c4729251bf15182 -/
section Source2353
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open SevenEighths.InverseMoment SevenEighths.InverseInitialProfile
open SevenEighths.InverseInitialArithmetic SevenEighths.InverseInitialPhysicalMeasure
open SevenEighths.InverseInitialEnergyCallerModes
namespace SevenEighths.InverseInitialEnergyCallerSource
variable {ι : Type*} [DecidableEq ι]

def erasePoint (x : Point ι) : Source (ι:=ι) 0 where
  common := x.common
  divisor := x.divisor
  overlap := x.overlap
  frequency := x.frequency
  assigned := Fin.elim0

omit [DecidableEq ι] in
@[simp] theorem erase_sourcePoint (x : Source (ι:=ι) 0) (N M : Finset ι) :
    erasePoint (sourcePoint x N M)=x := by
  apply Source.ext <;> try rfl
  funext i
  exact Fin.elim0 i

omit [DecidableEq ι] in
theorem point_pair_injective (x : Source (ι:=ι) 0) :
    Function.Injective (fun q : Finset ι × Finset ι=>sourcePoint x q.1 q.2) := by
  intro q r h
  exact Prod.ext (congrArg Point.left h) (congrArg Point.right h)

def rectangle (F : Finset ι) (x : Source (ι:=ι) 0) : Finset (Point ι) :=
  ((F\x.overlap).powerset ×ˢ (F\x.overlap).powerset).image
    (fun q=>sourcePoint x q.1 q.2)

def pointSource (F : Finset ι) (S : Finset (Source (ι:=ι) 0)) : Finset (Point ι) :=
  S.biUnion (rectangle F)

theorem rectangles_disjoint (F : Finset ι) {x y : Source (ι:=ι) 0} (hne : x≠y) :
    Disjoint (rectangle F x) (rectangle F y) := by
  apply Finset.disjoint_left.mpr
  intro z hz₁ hz₂
  obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hz₁
  obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hz₂
  have he := congrArg erasePoint (hea.trans heb.symm)
  simp only [erase_sourcePoint] at he
  exact hne he

theorem pointSource_sum {A : Type*} [AddCommMonoid A]
    (F : Finset ι) (S : Finset (Source (ι:=ι) 0)) (f : Point ι→A) :
    (∑ x∈pointSource F S,f x) =
      ∑ y∈S,∑ N∈(F\y.overlap).powerset,∑ M∈(F\y.overlap).powerset,
        f (sourcePoint y N M) := by
  rw [pointSource,Finset.sum_biUnion (fun x hx y hy hne=>rectangles_disjoint F hne)]
  apply Finset.sum_congr rfl
  intro y hy
  rw [rectangle,Finset.sum_image (fun x _ z _ he=>point_pair_injective y he),Finset.sum_product]

theorem pointSource_valid (F : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hdiv : ∀ x∈S,x.divisor⊆x.common)
    (hfreq : ∀ x∈S,x.frequency≠0) : ∀ y∈pointSource F S,Valid y := by
  intro y hy
  obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hy
  have hd (U : Finset ι) (hU : U∈(F\x.overlap).powerset) : Disjoint x.overlap U := by
    apply Finset.disjoint_left.mpr
    intro i hi hiU
    exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hU hiU)).2 hi
  exact ⟨hdiv x hx,hd N (Finset.mem_product.mp hNM).1,
    hd M (Finset.mem_product.mp hNM).2,hfreq x hx⟩

variable {σ : Type*} [DecidableEq σ]
  (p : ι→ActualEisensteinCubic.O) (hp : ∀ i,p i≠0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def rowMode (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (j : ActualEisensteinCubic.O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (x : Source (ι:=ι) 0) (ρ : SecondRayIndex)
    (z : JointLogSeparation.Frequency × (Fin 6→ℝ)) : ℂ :=
  let height := profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
  (outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ *
    secondOuterPhase height (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H)) *
  (star (markedModeColumn p hp hcop hg hpr F (secondRayMinus Ψ ρ) j x.frequency x
      slots lists a (childLogTest ω₁ (-height 4)) Z D B v) *
    markedModeColumn p hp hcop hg hpr F (secondRayPlus Ψ ρ) j (-x.frequency) x
      slots lists a (childLogTest ω₂ (height 5)) Z D B v)

theorem canonicalBlock_rows
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hE : ∀ x∈S,x.divisor⊆x.common) (w : Source (ι:=ι) 0→ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (j : ActualEisensteinCubic.O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (z : JointLogSeparation.Frequency × (Fin 6→ℝ)) :
    canonicalBlock p hp hcop hg hpr (pointSource F S) (w ∘ erasePoint) Ψ j
      (primeMark slots lists a) ω₁ ω₂ Z D B v θ H z =
      ∑ x∈S,∑ ρ : SecondRayIndex,w x*rowMode p hp hcop hg hpr F Ψ j
        slots lists a ω₁ ω₂ Z D B v θ H x ρ z := by
  unfold canonicalBlock
  rw [pointSource_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Function.comp_apply,erase_sourcePoint]
  calc
    _ = ∑ N∈(F\x.overlap).powerset,∑ ρ : SecondRayIndex,∑ M∈(F\x.overlap).powerset,
        w x*InverseInitialPhysicalMeasure.canonicalPairMode p hp hcop hg hpr Ψ j
          (primeMark slots lists a) ω₁ ω₂ Z D B v θ H (sourcePoint x N M) ρ z := by
      apply Finset.sum_congr rfl
      intro N hN
      exact Finset.sum_comm
    _ = ∑ ρ : SecondRayIndex,∑ N∈(F\x.overlap).powerset,∑ M∈(F\x.overlap).powerset,
        w x*InverseInitialPhysicalMeasure.canonicalPairMode p hp hcop hg hpr Ψ j
          (primeMark slots lists a) ω₁ ω₂ Z D B v θ H (sourcePoint x N M) ρ z := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      simp_rw [←Finset.mul_sum]
      rw [canonicalPairMode_rectangle p hp hcop hg hpr x (hE x hx) F Ψ j
        slots lists a ω₁ ω₂ Z D B v θ H ρ z]
      rfl

theorem physicalBlock_rectangular_common_measure
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6→ℝ→ℂ)
    (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ)
    (hid : PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂)
    (F : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hE : ∀ x∈S,x.divisor⊆x.common) (hf : ∀ x∈S,x.frequency≠0)
    (w : Source (ι:=ι) 0→ℂ) (Ψ : ActualEisensteinCubic.O →* ℂ) (j : ActualEisensteinCubic.O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (ω₁ ω₂ : ℝ→ℂ)
    (hsupport : BlockSupport p (pointSource F S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂) :
    physicalBlock p hp hcop hg (pointSource F S) (w ∘ erasePoint) Ψ j (primeMark slots lists a)
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
    (Z^(prefactorCenter m D B θ+3*η):ℝ)*
      ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
        (∑ x∈S,∑ ρ : SecondRayIndex,w x*rowMode p hp hcop hg hpr F Ψ j
          slots lists a ω₁ ω₂ Z D B v θ H x ρ z) := by
  rw [physicalBlock_integral p hp hcop hg hpr W₁ W₂ Φ V g g₁ g₂ b₃
    Z D B v m θ H η c₁ c₂ θ₁ θ₂ hid (pointSource F S) (pointSource_valid F S hE hf)
    (w ∘ erasePoint) Ψ j (primeMark slots lists a) ω₁ ω₂
    hsupport.1 hsupport.2.1 hsupport.2.2]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [canonicalBlock_rows p hp hcop hg hpr F S hE w Ψ j slots lists a ω₁ ω₂ Z D B v θ H z]

end SevenEighths.InverseInitialEnergyCallerSource

end

end OAI

end Source2353

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondFreshAssembly.lean; sha256: b8350b05562cf133bb6e6044bf828a182e87097eff8dc387a019024f6c149933 -/
section Source2354
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondSeparatedPair (F : Finset ι) (x : SecondProfileData ι)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (v : Frequency × (Fin 6 → ℝ)) : ℂ :=
  let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope v.1 v.2
  secondOuterPhase h
    (secondRelativeLog (secondActualNorms p x ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
  star (canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedLeft x.rayLeft
    x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
    slots₁ lists₁ a₁ (childLogTest ω₁ (-h 4)) (primeProductNorm p x.overlap*X₀)) *
  canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedRight x.rayRight
    x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor (-x.frequency)
    slots₂ lists₂ a₂ (childLogTest ω₂ (h 5)) (primeProductNorm p x.overlap*X₀)

theorem actual_second_full_mode_columns (F : Finset ι) (x : SecondProfileData ι)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (v : Frequency × (Fin 6 → ℝ)) :
    (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
      secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
        (star (ω₁ (primeProductNorm p N/X₀)) * ω₂ (primeProductNorm p M/X₀)) *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
          (secondRelativeLog (secondActualNorms p x N M) G₀ E₀ V₀ K₀ X₀) v.1 v.2) =
      secondSeparatedPair p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope v.1 v.2
  let O := secondOuterPhase h (secondRelativeLog (secondActualNorms p x ∅ ∅) G₀ E₀ V₀ K₀ X₀)
  calc
    _ = O * (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
        secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
          (star (ω₁ (primeProductNorm p N/X₀)) * ω₂ (primeProductNorm p M/X₀)) *
          logPhase (h 4) (Real.log (primeProductNorm p N/X₀)) *
          logPhase (h 5) (Real.log (primeProductNorm p M/X₀))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro M hM
      have hm : pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
          (secondRelativeLog (secondActualNorms p x N M) G₀ E₀ V₀ K₀ X₀) v.1 v.2 =
          O * logPhase (h 4) (Real.log (primeProductNorm p N/X₀)) *
            logPhase (h 5) (Real.log (primeProductNorm p M/X₀)) := by
        rw [second_mode_split]
        simp [secondOuterPhase,secondRelativeLog,secondRelativeNorm,secondActualNorms,O,h]
      rw [hm]
      ring
    _ = _ := by
      rw [actual_second_columns_separated]
      simp only [secondSeparatedPair,h,O,mul_assoc]

theorem actualSecondFreshRows_integral {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (g : Fin 6 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), fullProfileDensity g b₁ b₂ b₃ v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        fullProfileDensity g b₁ b₂ b₃ v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  rw [actualSecondProfileRows_eq_indexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← full_density_finite_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj]
  ring

end
end SevenEighths.InverseMoment

end OAI

end Source2354

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondGenerator.lean; sha256: 5961388c09167b0b6c5a01fc08ea44454db70fcb14bb60634bd8f001f6d50391 -/
section Source2355
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondUnitFrequency (u v : Eisˣ) (k : Eis) : Eis := ((u^4*v:Eisˣ):Eis)*k

lemma secondUnitFrequency_injective (u v : Eisˣ) : Function.Injective (secondUnitFrequency u v) := by
  intro a b hab
  exact mul_left_cancel₀ (Units.ne_zero (u^4*v)) hab

lemma secondUnitFrequency_norm (u v : Eisˣ) (k : Eis) :
    ‖ConcreteTraceCRT.eisEmbedding (secondUnitFrequency u v k)‖ =
      ‖ConcreteTraceCRT.eisEmbedding k‖ :=
  GaussGeneratorTransport.norm_eisEmbedding_unit_mul (u^4*v) k

lemma secondUnitFrequency_neg (u v : Eisˣ) (k : Eis) :
    secondUnitFrequency u v (-k) = -secondUnitFrequency u v k := by
  simp only [secondUnitFrequency,mul_neg]

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondCanonical_generator_transport
    (F : Finset ι) (Ψ : Eis →* ℂ) (m label d e k : Eis)
    (L D E : Ideal Eis) (u v : Eisˣ)
    (hl : label = (u:Eis)*primaryGenerator L)
    (hd : d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E))
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m label (d*e*k) slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m (primaryGenerator L)
        (primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k) slots lists a W X := by
  rw [hl,finiteCanonicalMarkedRow_label_transfer,hd]
  congr 1
  unfold secondUnitFrequency
  change (u:Eis)^4*((v:Eis)*(primaryGenerator D*primaryGenerator E)*k) =
    primaryGenerator D*primaryGenerator E*(((u:Eis)^4*(v:Eis))*k)
  ring

theorem secondCanonical_row_norm (D E : Ideal Eis) (u v : Eisˣ) (d e k : Eis)
    (hd : d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E)) :
    ‖ConcreteTraceCRT.eisEmbedding
      (primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k)‖ =
      ‖ConcreteTraceCRT.eisEmbedding (d*e*k)‖ := by
  rw [hd]
  have hl : primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k =
      ((u^4*v:Eisˣ):Eis)*(primaryGenerator D*primaryGenerator E*k) := by
    unfold secondUnitFrequency
    ring
  rw [hl,GaussGeneratorTransport.norm_eisEmbedding_unit_mul]
  have hr : (v:Eis)*(primaryGenerator D*primaryGenerator E)*k =
      (v:Eis)*(primaryGenerator D*primaryGenerator E*k) := by ring
  rw [hr,GaussGeneratorTransport.norm_eisEmbedding_unit_mul]

theorem exists_second_generator_sectors (label d e : Eis) (L D E : Ideal Eis)
    (hl : Ideal.span {label} = L) (hd : Ideal.span {d} = D) (he : Ideal.span {e} = E)
    (hL : primaryGenerator L ≠ 0) (hD : primaryGenerator D ≠ 0) (hE : primaryGenerator E ≠ 0) :
    ∃ u v : Eisˣ, label = (u:Eis)*primaryGenerator L ∧
      d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E) := by
  obtain ⟨u,hu⟩ := generator_eq_unit_primary L label hl hL
  have hspan : Ideal.span {d*e} = D*E := by
    rw [← Ideal.span_singleton_mul_span_singleton,hd,he]
  obtain ⟨v,hv⟩ := generator_eq_unit_primary (D*E) (d*e) hspan
    (by rw [primaryGenerator_mul]; exact mul_ne_zero hD hE)
  exact ⟨u,v,hu,by simpa only [primaryGenerator_mul] using hv⟩

end
end SevenEighths.InverseMoment

end OAI

end Source2355

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondSourceTuples.lean; sha256: 94f77b8ccfe1da4b313ab4f6db3ab39f974e004eb031ae98e636102a81df050c -/
section Source2356
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero sourceIdeal_union sourceIdeal_injective sourcePrime source_prime_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

@[ext] structure SecondOriginalSource (ι : Type*) (Jo Jn : ℕ) where
  q0 : Ideal Eis
  quotient : Ideal Eis
  J : Ideal Eis
  C : Ideal Eis
  s : Ideal Eis
  b1 : Ideal Eis
  A1 : Ideal Eis
  A2 : Ideal Eis
  dK : Ideal Eis
  J2 : Ideal Eis
  b2 : Ideal Eis
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal
  newAssigned : Fin Jn → ι

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def originalSecondTuple {Jo Jn : ℕ} (u v : Eisˣ) (x : SecondOriginalSource ι Jo Jn) : SecondTuple Jo Jn where
  outer := ⟨x.q0,x.quotient,sourceIdeal p (x.common \ x.divisor)⟩
  core := ![x.J,x.C,sourceIdeal p x.divisor,x.s,x.b1,x.A1,x.A2,x.dK]
  commonResidual := sourceIdeal p x.overlap
  cubeResidual := x.J2
  secondCube := x.b2
  extractedCommon := sourceIdeal p x.common
  frequency := secondUnitFrequency u v x.frequency
  oldAssigned := x.oldAssigned
  newAssigned := fun i => sourcePrime p (x.newAssigned i)

structure SecondOriginalValid {Jo Jn : ℕ} (x : SecondOriginalSource ι Jo Jn) : Prop where
  j_split : x.s*x.J2 = x.J
  b_split : x.b1*x.b2 = x.q0^2*x.J2^2*x.s
  a1 : x.A1 ∣ (x.b1*x.b2).radical
  a2 : x.A2 ∣ (x.b1*x.b2).radical
  first_divisor : x.dK ∣ x.C*(x.b1*x.b2).radical
  first_generator : primaryGenerator x.dK ≠ 0
  second_subset : x.divisor ⊆ x.common
  old_support : ∀ i, (x.oldAssigned i).val ∣ x.q0*x.J*x.C*x.quotient
  new_support : ∀ i, x.newAssigned i ∈ x.common ∪ x.overlap

theorem originalSecondTuple_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    {Jo Jn : ℕ} (u v : Eisˣ) (x : SecondOriginalSource ι Jo Jn) (hx : SecondOriginalValid x) :
    Valid (originalSecondTuple p u v x)
      (secondChild (originalSecondTuple p u v x)).1
      (secondChild (originalSecondTuple p u v x)).2.1
      (secondChild (originalSecondTuple p u v x)).2.2 := by
  have hproduct : sourceIdeal p x.divisor * sourceIdeal p (x.common \ x.divisor) =
      sourceIdeal p x.common := by
    rw [←sourceIdeal_union p x.divisor (x.common \ x.divisor)
      (Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi)),
      Finset.union_sdiff_of_subset hx.second_subset]
  refine ⟨rfl,rfl,hx.j_split,hx.b_split,hx.a1,hx.a2,hx.first_divisor,?_,hx.first_generator,?_,rfl,?_,?_⟩
  · exact hproduct
  · change primaryGenerator (sourceIdeal p x.divisor) ≠ 0
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  · intro i
    apply (hx.old_support i).trans
    change x.q0*x.J*x.C*x.quotient ∣
      x.q0*(x.J*x.C*sourceIdeal p x.divisor*sourceIdeal p x.overlap)*x.quotient
    refine ⟨sourceIdeal p x.divisor*sourceIdeal p x.overlap,?_⟩
    ring
  · intro i
    change (sourcePrime p (x.newAssigned i)).val ∣
      (x.J*x.C*sourceIdeal p x.divisor*sourceIdeal p x.overlap)*sourceIdeal p (x.common \ x.divisor)
    have hslot : (sourcePrime p (x.newAssigned i)).val ∣
        sourceIdeal p x.common*sourceIdeal p x.overlap := by
      rcases Finset.mem_union.mp (hx.new_support i) with hi|hi
      · exact dvd_mul_of_dvd_left (source_prime_dvd p x.common _ hi) _
      · exact dvd_mul_of_dvd_right (source_prime_dvd p x.overlap _ hi) _
    apply hslot.trans
    refine ⟨x.J*x.C,?_⟩
    rw [←hproduct]
    ring

theorem originalSecondTuple_injective
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) :
    Function.Injective (originalSecondTuple (Jo:=Jo) (Jn:=Jn) p u v) := by
  intro x y hxy
  have hi := sourceIdeal_injective p hinj
  have hcore (i : Fin 8) := congrArg (fun z : SecondTuple Jo Jn => z.core i) hxy
  apply SecondOriginalSource.ext
  · exact congrArg (fun z : SecondTuple Jo Jn => z.outer.q0) hxy
  · exact congrArg (fun z : SecondTuple Jo Jn => z.outer.quotient) hxy
  · exact hcore 0
  · exact hcore 1
  · exact hcore 3
  · exact hcore 4
  · exact hcore 5
  · exact hcore 6
  · exact hcore 7
  · exact congrArg SecondTuple.cubeResidual hxy
  · exact congrArg SecondTuple.secondCube hxy
  · exact hi (congrArg SecondTuple.extractedCommon hxy)
  · exact hi (hcore 2)
  · exact hi (congrArg SecondTuple.commonResidual hxy)
  · exact secondUnitFrequency_injective u v (congrArg SecondTuple.frequency hxy)
  · exact congrArg SecondTuple.oldAssigned hxy
  · funext i
    apply hinj
    exact congrArg (fun z : SecondTuple Jo Jn => (z.newAssigned i).val) hxy

theorem original_second_source_fiber_bound (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (SecondOriginalSource ι Jo Jn))
    (hs : ∀ x ∈ source, SecondOriginalValid x)
    (γ : OuterTriple) (f : Ideal Eis) (k : Eis)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    (source.filter (fun x => secondChild (originalSecondTuple p u v x) = (γ,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(9+4*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.q0).card^(5+2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.quotient).card^(2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.residual).card^(2*K) := by
  classical
  let S := source.filter (fun x => secondChild (originalSecondTuple p u v x) = (γ,f,k))
  have hv : ∀ y ∈ S.image (originalSecondTuple p u v), Valid y γ f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,he⟩ := Finset.mem_filter.mp hx
    have hh := originalSecondTuple_valid p hp hpr u v x (hs x hxs)
    simpa only [he] using hh
  have hb := valid_tuple_card_le_slot_cap (S.image (originalSecondTuple p u v))
    γ f k hf hq ht hr hv K ho hn
  rw [Finset.card_image_of_injective S (originalSecondTuple_injective p hinj u v)] at hb
  exact hb

theorem originalSecondTuple_row_norm {Jo Jn : ℕ} (u v : Eisˣ)
    (x : SecondOriginalSource ι Jo Jn) (d e : Eis)
    (hde : d*e = (v:Eis)*(primaryGenerator x.dK*primaryGenerator (sourceIdeal p x.divisor))) :
    ‖ConcreteTraceCRT.eisEmbedding (secondChild (originalSecondTuple p u v x)).2.2‖ =
      ‖ConcreteTraceCRT.eisEmbedding (d*e*x.frequency)‖ := by
  exact secondCanonical_row_norm x.dK (sourceIdeal p x.divisor) u v d e x.frequency hde

end
end SevenEighths.InverseMoment

end OAI

end Source2356

/- Original source: OAI/NumberTheory/DirichletL/Descent/CubeSource.lean; sha256: e5154ae07a363fa1a4c6b33510e57ae854ef21ebfa30d3936f639cdabaf27450 -/
section Source2357
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero sourceIdeal_union sourceIdeal_injective sourcePrime source_prime_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

lemma sourceIdeal_isRadical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (S : Finset ι) :
    (sourceIdeal p S).IsRadical := by
  change (Ideal.span {∏ i ∈ S,p i}).IsRadical
  rw [FiniteGaussPhase.span_finset_prod]
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact fun _ _ => by simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Ideal.mul_eq_inf_of_isCoprime]
    · exact (inferInstance : (Ideal.span {p a}).IsPrime).isRadical.inf ih
    · apply IsCoprime.prod_right
      intro b hb
      exact hcop (fun he => ha (he.symm ▸ hb))

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma cubeRadical_span_dvd_product (B : Finset ι) (v : ι → ℕ)
    (hv : ∀ i ∈ B, 0 < v i) :
    sourceIdeal p B ∣ Ideal.span {primeProduct p B v} := by
  apply span_dvd_of_element_dvd
  change (∏ i ∈ B,p i) ∣ primeProduct p B v
  unfold primeProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  exact dvd_pow_self _ (Nat.ne_of_gt (hv i hi))

theorem cubeSupport_dvd_radical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    sourceIdeal p B ∣
      (Ideal.span {primeProduct p B v₁}*Ideal.span {primeProduct p B v₂}).radical := by
  apply Ideal.dvd_iff_le.mpr
  apply (sourceIdeal_isRadical p hcop B).radical_le_iff.mpr
  apply Ideal.dvd_iff_le.mp
  rw [Ideal.span_singleton_mul_span_singleton,←primeProduct_add]
  exact cubeRadical_span_dvd_product p B _ hv

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma aLabel_dvd_cubeSupport (B : Finset ι) (ε : ι → Bool) :
    Ideal.span {aLabel p B ε} ∣ sourceIdeal p B := by
  apply span_dvd_of_element_dvd
  unfold aLabel primeProduct
  change (∏ i ∈ B,p i^bit (ε i)) ∣ ∏ i ∈ B,p i
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  cases hh : ε i <;> simp [bit]

theorem firstMask_dvd_cube_radical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (B C D : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v₁ v₂ : ι → ℕ) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    sourceIdeal p D ∣ sourceIdeal p C *
      (Ideal.span {primeProduct p B v₁}*Ideal.span {primeProduct p B v₂}).radical := by
  have hd := InverseInitialArithmetic.sourceIdeal_dvd p D (C∪B) hD
  rw [sourceIdeal_union p C B hCB] at hd
  exact hd.trans (mul_dvd_mul_left _ (cubeSupport_dvd_radical p hcop B v₁ v₂ hv))

def cubeSecondSource {Jo Jn : ℕ} (B C D G E V : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι) :
    SecondOriginalSource ι Jo Jn where
  q0 := Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  quotient := t
  J := Ideal.span {jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  C := sourceIdeal p C
  s := Ideal.span {squarefreeLabel p B (fun i => v₁ i+v₂ i)}
  b1 := Ideal.span {primeProduct p B v₁}
  A1 := Ideal.span {aLabel p B ε₁}
  A2 := Ideal.span {aLabel p B ε₂}
  dK := sourceIdeal p D
  J2 := Ideal.span {j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  b2 := Ideal.span {primeProduct p B v₂}
  common := G
  divisor := E
  overlap := V
  frequency := k
  oldAssigned := oldAssigned
  newAssigned := newAssigned

theorem cubeSecondSource_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (B C D G E V : Finset ι) (hCB : Disjoint C B)
    (hD : D ⊆ C∪B) (hE : E ⊆ G)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι)
    (hold : ∀ i, (oldAssigned i).val ∣
      Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂} *
      Ideal.span {jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂} * sourceIdeal p C * t)
    (hnew : ∀ i, newAssigned i ∈ G∪V) :
    SecondOriginalValid (cubeSecondSource p B C D G E V v₁ v₂ ε₁ ε₂ t k oldAssigned newAssigned) := by
  constructor
  · change Ideal.span {squarefreeLabel p B (fun i => v₁ i+v₂ i)} *
        Ideal.span {j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂} = _
    rw [Ideal.span_singleton_mul_span_singleton,←jLabel_eq_squarefree_mul_j2]
    rfl
  · have hb := congrArg (fun a : Eis => (Ideal.span {a} : Ideal Eis))
      (cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv)
    simpa only [cubeSecondSource,pow_two,←Ideal.span_singleton_mul_span_singleton] using hb
  · exact (aLabel_dvd_cubeSupport p B ε₁).trans (cubeSupport_dvd_radical p hcop B v₁ v₂ hv)
  · exact (aLabel_dvd_cubeSupport p B ε₂).trans (cubeSupport_dvd_radical p hcop B v₁ v₂ hv)
  · exact firstMask_dvd_cube_radical p hcop B C D hCB hD v₁ v₂ hv
  · change primaryGenerator (sourceIdeal p D) ≠ 0
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  · exact hE
  · exact hold
  · exact hnew

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem oldSlot_dvd_reconstructed_support
    (B C : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (P t : Ideal Eis)
    (hP : P ∣ sourceIdeal p B*sourceIdeal p C*t) :
    P ∣ Ideal.span {b0Label p B v ε₁ ε₂}*
      Ideal.span {jLabel p B v ε₁ ε₂}*sourceIdeal p C*t := by
  have hb := span_dvd_of_element_dvd (cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv)
  change sourceIdeal p B ∣ Ideal.span {jLabel p B v ε₁ ε₂*b0Label p B v ε₁ ε₂} at hb
  rw [←Ideal.span_singleton_mul_span_singleton,mul_comm (Ideal.span {jLabel p B v ε₁ ε₂})] at hb
  exact hP.trans (mul_dvd_mul_right (mul_dvd_mul_right hb _) _)

theorem cubeSecondSource_valid_original_slots (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (B C D G E V : Finset ι) (hCB : Disjoint C B)
    (hD : D ⊆ C∪B) (hE : E ⊆ G)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι)
    (hold : ∀ i, (oldAssigned i).val ∣ sourceIdeal p B*sourceIdeal p C*t)
    (hnew : ∀ i, newAssigned i ∈ G∪V) :
    SecondOriginalValid (cubeSecondSource p B C D G E V v₁ v₂ ε₁ ε₂ t k oldAssigned newAssigned) :=
  cubeSecondSource_valid p hp hpr hcop B C D G E V hCB hD hE v₁ v₂ ε₁ ε₂ hv t k
    oldAssigned newAssigned
    (fun i => oldSlot_dvd_reconstructed_support p B C _ ε₁ ε₂ hv _ t (hold i)) hnew

end
end SevenEighths.InverseMoment

end OAI

end Source2357

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondSourceEncoding.lean; sha256: 942fc0fa022ee005d084f787b993689f4f775ae0b259cba5016b4deec7c7d662 -/
section Source2358
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_injective)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

@[ext] structure MarkedSecondSource (ι : Type*) (Jo Jn : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  second : SecondExpansionData ι
  quotient : Ideal Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal
  newAssigned : Fin Jn → ι

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def markedSecondOriginal {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : SecondOriginalSource ι Jo Jn :=
  cubeSecondSource p x.cube.support x.firstCommon x.firstDivisor
    x.second.sourceCommon x.second.divisor x.second.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.quotient x.second.frequency x.oldAssigned x.newAssigned

theorem markedSecondOriginal_injOn (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) {Jo Jn : ℕ} :
    Set.InjOn (markedSecondOriginal (Jo:=Jo) (Jn:=Jn) p) {x | x.cube.Admissible} := by
  intro x hx y hy hxy
  have hc : x.cube = y.cube := by
    apply cubeDivisorKey_injective_on_product p hp hinj hx hy
    · simpa only [markedSecondOriginal,cubeSecondSource,cubeProductIdeal] using
        congrArg (fun z : SecondOriginalSource ι Jo Jn => z.b1*z.b2) hxy
    · funext i
      fin_cases i
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.b1 hxy
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.A1 hxy
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.A2 hxy
  apply MarkedSecondSource.ext hc
  · exact sourceIdeal_injective p hinj (congrArg SecondOriginalSource.C hxy)
  · exact sourceIdeal_injective p hinj (congrArg SecondOriginalSource.dK hxy)
  · apply SecondExpansionData.ext
    · exact congrArg SecondOriginalSource.common hxy
    · exact congrArg SecondOriginalSource.divisor hxy
    · exact congrArg SecondOriginalSource.overlap hxy
    · exact congrArg SecondOriginalSource.frequency hxy
  · exact congrArg SecondOriginalSource.quotient hxy
  · exact congrArg SecondOriginalSource.oldAssigned hxy
  · exact congrArg SecondOriginalSource.newAssigned hxy

theorem markedSecondTuple_injOn (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) {Jo Jn : ℕ} (u v : Eisˣ) :
    Set.InjOn (fun x : MarkedSecondSource ι Jo Jn => originalSecondTuple p u v (markedSecondOriginal p x))
      {x | x.cube.Admissible} := by
  intro x hx y hy he
  exact markedSecondOriginal_injOn p hp hinj hx hy
    (originalSecondTuple_injective p hinj u v he)

theorem markedSecondOriginal_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (hold : ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient)
    (hnew : ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap) :
    SecondOriginalValid (markedSecondOriginal p x) :=
  cubeSecondSource_valid_original_slots p hp hpr hcop x.cube.support x.firstCommon x.firstDivisor
    x.second.sourceCommon x.second.divisor x.second.overlap hCB hD hE
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit x.cube.support_pos
    x.quotient x.second.frequency x.oldAssigned x.newAssigned hold hnew

theorem actual_marked_second_source_fiber (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (ha : ∀ x ∈ source, x.cube.Admissible)
    (hCB : ∀ x ∈ source, Disjoint x.firstCommon x.cube.support)
    (hD : ∀ x ∈ source, x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : ∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon)
    (hold : ∀ x ∈ source, ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient)
    (hnew : ∀ x ∈ source, ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap)
    (γ : OuterTriple) (f : Ideal Eis) (k : Eis)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    (source.filter (fun x => secondChild (originalSecondTuple p u v (markedSecondOriginal p x)) = (γ,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(9+4*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.q0).card^(5+2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.quotient).card^(2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.residual).card^(2*K) := by
  classical
  let encode := fun x : MarkedSecondSource ι Jo Jn => originalSecondTuple p u v (markedSecondOriginal p x)
  let S := source.filter (fun x => secondChild (encode x) = (γ,f,k))
  have hvalid : ∀ x ∈ source,
      Valid (encode x) (secondChild (encode x)).1 (secondChild (encode x)).2.1 (secondChild (encode x)).2.2 := by
    intro x hx
    exact originalSecondTuple_valid p hp hpr u v (markedSecondOriginal p x)
      (markedSecondOriginal_valid p hp hpr hcop x (hCB x hx) (hD x hx) (hE x hx) (hold x hx) (hnew x hx))
  have hv : ∀ y ∈ S.image encode, Valid y γ f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,he⟩ := Finset.mem_filter.mp hx
    simpa only [he] using hvalid x hxs
  have hi : Set.InjOn encode (S : Set (MarkedSecondSource ι Jo Jn)) := by
    intro x hx y hy he
    exact markedSecondTuple_injOn p hp hinj u v
      (ha x (Finset.mem_filter.mp hx).1) (ha y (Finset.mem_filter.mp hy).1) he
  have hb := valid_tuple_card_le_slot_cap (S.image encode) γ f k hf hq ht hr hv K ho hn
  rw [Finset.card_image_iff.mpr hi] at hb
  exact hb

end
end SevenEighths.InverseMoment

end OAI

end Source2358

/- Original source: OAI/NumberTheory/DirichletL/Descent/SecondCauchy.lean; sha256: 75b77ad9dda6c5186e52d326d3ff7f1af97f1d57858ef745acab14a4936be3c5 -/
section Source2359
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open SevenEighths.InverseSecondFibers IdealMobiusDivisorSum CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondLabelEnergy (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : ℝ :=
  ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(9+4*K) *
    ∑ k ∈ rows, ‖F (γ,f,k)‖^2

lemma secondLabelEnergy_nonneg (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : 0 ≤ secondLabelEnergy K labels rows F γ := by
  unfold secondLabelEnergy; positivity

theorem second_weighted_count {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild x).2.1 ∈ labels ∧ (secondChild x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℂ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ originalSource source oldLists newLists keep,
      w x * F (secondChild x) * star (G (secondChild x))‖ ≤
      Real.sqrt (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  have hF := second_energy_projection source oldLists newLists keep hvalid labels rows hf houter hchild
    K ho hn (fun x => ‖w x‖) hw F
  have hG := second_energy_projection source oldLists newLists keep hvalid labels rows hf houter hchild
    K ho hn (fun x => ‖w x‖) hw G
  apply (DescentWeightedCauchy.weighted_cauchy (originalSource source oldLists newLists keep)
    w (F ∘ secondChild) (G ∘ secondChild)).trans
  exact mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem second_weighted_count_of_child_bound {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild x).2.1 ∈ labels ∧ (secondChild x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℂ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows F γ ≤ E)
    (hG : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows G γ ≤ E) :
    ‖∑ x ∈ originalSource source oldLists newLists keep,
      w x * F (secondChild x) * star (G (secondChild x))‖ ≤
      E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ := by
  have hb (P : SecondChild → ℂ)
      (hP : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows P γ ≤ E) :
      (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows P γ) ≤
      E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ hγ
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hP γ hγ) (tripleDivisorWeight_nonneg K γ)
  apply (second_weighted_count source oldLists newLists keep hvalid labels rows hf houter hchild K ho hn w hw F G).trans
  calc
    _ ≤ Real.sqrt (E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ) *
      Real.sqrt (E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ) :=
      mul_le_mul (Real.sqrt_le_sqrt (hb F hF)) (Real.sqrt_le_sqrt (hb G hG))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (mul_nonneg hE (Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ)))

def secondCanonicalPolynomial {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : OuterTriple → Eis →* ℂ) (puncture : OuterTriple → Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) : ℂ :=
  finiteCanonicalMarkedRow p hp hcop hg pool (Ψ c.1) (puncture c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a (W c.1) X

theorem secondCanonicalPolynomial_actual_columns {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : OuterTriple → Eis →* ℂ) (puncture : OuterTriple → Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) :
    secondCanonicalPolynomial p hp hcop hg pool Ψ puncture slots lists a W X c =
      ∑ U ∈ pool.powerset,
        columnWeight (CanonicalRowCompletion.rowTwist (Ψ c.1) (puncture c.1)
          (primaryGenerator c.2.1) c.2.2) (Ideal.span {∏ i ∈ U, p i}) *
        (primeMark slots lists a U * W c.1 (FirstPassCubeLabels.primeProductNorm p U / X)) :=
  finiteCanonicalMarkedRow_actual_columns p hp hcop hg hpr pool (Ψ c.1) (puncture c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a (W c.1) X

end
end SevenEighths.InverseMoment

end OAI

end Source2359
