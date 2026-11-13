import OpenAIGrouped.Unit032
import OpenAIGrouped.Unit009
import OpenAIGrouped.Unit017
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import OpenAIGrouped.Unit027
import OpenAIGrouped.Unit044
import OpenAIGrouped.Unit031
import OpenAIGrouped.Unit033
import OpenAIGrouped.Unit011
import Mathlib.Analysis.Analytic.IsolatedZeros
import OpenAIGrouped.Unit015
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit030
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Detector/FiniteProductX.lean; sha256: 4ae6793522fbe8bd7fe4c14647461dc1f032e4e2a93d4697437ecfe4b372d7d7 -/
section Source1800
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace SevenEighths.ProbeFiniteProductX
open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeFiniteProductBounds
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma marked_differentiableAt_x (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun x => idealMarkedClosed η P x w z) x := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hr := coordR_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) z
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  have hk := coordK_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) w
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => localMultiplier η P x w z) {x : ℂ | 7/8 < x.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramifiedClosed_analytic_x (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 w z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx.le hz
  have hm := marked_differentiableAt_x η P x w z hQ hx.le hz
  have hcc : DifferentiableAt ℂ (fun x => idealClosedCorrection η P x w z) x :=
    (hc x hx).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx.le hw hz
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => selectedMultiplier η T x w z) {x : ℂ | 7/8 < x.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_x η S hS P (hT P hp) w z hw hz)

theorem slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => slotMultiplier η J T b x w z) {x : ℂ | 7/8 < x.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_x η S hS P (hT j hj P hp) w z hw hz)

theorem window_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (W : ι → ℝ → ℂ) (scale : ι → ℝ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => windowMultiplier η J T W scale x w z) {x : ℂ | 7/8 < x.re} :=
  slot_analytic_x η S hS J T _ hT w z hw hz

theorem combined_selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * selectedMultiplier η T x w z)
      {x : ℂ | 7/8 < x.re} :=
  (globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (selected_analytic_x η S hS T hT w z hw hz)

theorem combined_slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {x : ℂ | 7/8 < x.re} :=
  (globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (slot_analytic_x η S hS J T b hT w z hw hz)

def continuedSourceMultiplier {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z) * (Z:ℂ)^(x+z-1) * (Y:ℂ)^(w-1) *
    Complex.exp ((x+z-1)^2) *
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z * mellin W1 w *
      HeckeReciprocal.reciprocal (η.excludePrimes S hS) x *
      globalClosedCorrection η S x w z * slotMultiplier η J T b x w z

theorem continued_source_analytic_x {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | max (7/8 : ℝ) HeckeZeroSupremum.beta < x.re} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hx' : (7/8 : ℝ)<x.re := lt_of_le_of_lt (le_max_left _ _) hx
  have hβ : HeckeZeroSupremum.beta<x.re := lt_of_le_of_lt (le_max_right _ _) hx
  have hH := (globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  have hR := HeckeReciprocal.reciprocal_differentiableAt (η.excludePrimes S hS.prime) hβ
  apply DifferentiableAt.differentiableWithinAt
  unfold continuedSourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx0 : x≠0) (hx1 : x≠1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z x w z =
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) x
        (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z := by
  simp only [continuedSourceMultiplier,sourceMultiplier,
    HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,div_eq_mul_inv]

theorem continued_source_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a : ℝ) (w z : ℂ) :
    (fun t : ℝ => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z ((a:ℂ)+t*I) w z)
      =ᵐ[volume] (fun t : ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
        ((a:ℂ)+t*I) (globalClosedCorrection η S ((a:ℂ)+t*I))
          (slotMultiplier η J T b ((a:ℂ)+t*I)) w z) := by
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply continued_source_eq_raw
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem source_analytic_x_off_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) x
      (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z)
      {x : ℂ | max (7/8 : ℝ) HeckeZeroSupremum.beta < x.re ∧ x≠1} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _
    ((Complex.isOpen_re_gt _).inter (isClosed_singleton.isOpen_compl))
  intro x hx
  have hx' : (7/8 : ℝ)<x.re := lt_of_le_of_lt (le_max_left _ _) hx.1
  have hβ : HeckeZeroSupremum.beta<x.re := lt_of_le_of_lt (le_max_right _ _) hx.1
  have hx0 : x≠0 := by intro h; simp only [h,zero_re] at hx'; norm_num at hx'
  have hL := LFunction_differentiableAt (η.excludePrimes S hS.prime) hx0 (Or.inl hx.2)
  have hLn := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime) hβ (Or.inl hx.2)
  have hH := (globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  apply DifferentiableAt.differentiableWithinAt
  unfold sourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_differentiable_strip {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) {a c : ℝ}
    (ha : 7/8<a) (hβ : HeckeZeroSupremum.beta<a) :
    DifferentiableOn ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | a≤x.re ∧ x.re≤c} := by
  apply (continued_source_analytic_x η S hS J T b hT W0 W1 X Y Z hZ w z hw hz).differentiableOn.mono
  intro x hx
  exact lt_of_lt_of_le (max_lt ha hβ) hx.1

theorem continued_source_principal_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (w z : ℂ)
    (hχ : (η.excludePrimes S hS).residue=1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z 1 w z=0 := by
  simp only [continuedSourceMultiplier,HeckeReciprocal.reciprocal_principal_one _ hχ,mul_zero,zero_mul]

end SevenEighths.ProbeFiniteProductX
end

end OAI

end Source1800

/- Original source: OAI/NumberTheory/DirichletL/Detector/PrincipalContours.lean; sha256: fefc1bbcb8eaab512a8d3b92bc2e374852333de8b8bee0ff43945fd0b8d9db8b -/
section Source1801
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalContours
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O
local instance : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable

@[fun_prop] lemma measurable_const_cpow {α : Type*} [MeasurableSpace α] (Q : ℝ) (hQ : 0<Q)
    (f : α → ℂ) (hf : Measurable f) : Measurable (fun x => (Q:ℂ)^f x) := by
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact ((differentiable_id.const_cpow (Or.inl hn)).continuous.measurable).comp hf

lemma ideal_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => idealClosedCorrection η P (x t) (w t) (z t)) := by
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealClosedCorrection unramifiedClosed continuedCorrection markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma global_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (S : Finset Id) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => globalClosedCorrection η S (x t) (w t) (z t)) := by
  unfold globalClosedCorrection
  exact Measurable.tprod (fun P => ideal_correction_measurable η P.val x w z hx hw hz)

lemma local_multiplier_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => localMultiplier η P (x t) (w t) (z t)) := by
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  have hc := ideal_correction_measurable η P x w z hx hw hz
  unfold localMultiplier compensatedReplacement idealMarkedClosed markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma slot_multiplier_measurable {α ι : Type*} [MeasurableSpace α]
    (η : Character) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (x w z : α → ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => slotMultiplier η J T b (x t) (w t) (z t)) := by
  unfold slotMultiplier
  apply Finset.measurable_prod
  intro j hj
  apply Finset.measurable_sum
  intro P hP
  exact measurable_const.mul (local_multiplier_measurable η P x w z hx hw hz)

def zBoxAmplitude (M : Id) (Bz : ℝ) : ℝ :=
  36*max 6 (6*Bz+1)*principalConstant M

lemma zBoxAmplitude_nonneg (M : Id) [NeZero M] (Bz : ℝ) : 0≤zBoxAmplitude M Bz := by
  unfold zBoxAmplitude
  exact mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) (le_max_left _ _)))
    (principalConstant_pos M).le

lemma fixed_principal_z_box_growth (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖≤zBoxAmplitude M Bz*height t^3 := by
  have hb := principal_poleRemoved_growth (fixedPrincipal M) rfl
    (show (19/20 : ℝ)≤(6*((ξ:ℂ)+t*I) : ℂ).re by simp; linarith [hξ.1])
  have hn : ‖6*((ξ:ℂ)+t*I)+1‖≤max 6 (6*Bz+1)*height t := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    have hm : (6:ℝ)≤max 6 (6*Bz+1) := le_max_left _ _
    have hm' : 6*ξ+1≤max 6 (6*Bz+1) := (by linarith [hξ.2] : 6*ξ+1≤6*Bz+1).trans (le_max_right _ _)
    simp only [add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,I_re,I_im,
      mul_zero,sub_zero,add_zero,zero_add,mul_one,one_re,one_im]
    norm_num only [show (6:ℂ).re=6 by norm_num,show (6:ℂ).im=0 by norm_num,zero_mul,sub_zero,add_zero]
    rw [abs_of_pos (by linarith [hξ.1] : 0<6*ξ+1),abs_mul]
    norm_num
    unfold height
    nlinarith [mul_le_mul_of_nonneg_right hm (abs_nonneg t)]
  have hi : |(6*((ξ:ℂ)+t*I) : ℂ).im|=6*|t| := by simp [abs_mul]
  have ht : (3+6*|t|)^2≤36*height t^2 := by
    have hh : 3+6*|t|≤6*height t := by unfold height; linarith
    have hp := pow_le_pow_left₀ (by positivity : 0≤3+6*|t|) hh 2
    simpa only [mul_pow,show (6:ℝ)^2=36 by norm_num] using hp
  have hC := (principalConstant_pos M).le
  have hmax : 0≤max (6:ℝ) (6*Bz+1) := le_trans (by norm_num) (le_max_left _ _)
  have hh := (height_pos t).le
  rw [hi] at hb
  calc
    _ ≤ principalConstant M*‖6*((ξ:ℂ)+t*I)+1‖*(3+6*|t|)^2 := hb
    _ ≤ principalConstant M*(max 6 (6*Bz+1)*height t)*(36*height t^2) := by
      gcongr
    _ = _ := by unfold zBoxAmplitude; ring

lemma LFunction_eq_pole_quotient (χ : Character) {s : ℂ} (h0 : s≠0) (h1 : s≠1) :
    LFunction χ s=HeckeOrigin.poleRemoved χ s/(s-1) := by
  rw [HeckeOrigin.poleRemoved_eq χ h0 h1]
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr h1)).symm

lemma LFunction_vertical_continuous (χ : Character) (a : ℝ) (ha0 : a≠0) (ha1 : a≠1) :
    Continuous (fun t : ℝ => LFunction χ ((a:ℂ)+t*I)) := by
  have h0 (t : ℝ) : (a:ℂ)+t*I≠0 := by intro h; exact ha0 (by simpa using congrArg Complex.re h)
  have h1 (t : ℝ) : (a:ℂ)+t*I≠1 := by intro h; exact ha1 (by simpa using congrArg Complex.re h)
  have hc := ((HeckeOrigin.poleRemoved_entire χ).continuous.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I))).div
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I-1)) (fun t => sub_ne_zero.mpr (h1 t))
  exact hc.congr (fun t => (LFunction_eq_pole_quotient χ (h0 t) (h1 t)).symm)

lemma reciprocal_vertical_continuous (χ : Character) (a : ℝ) (ha : HeckeZeroSupremum.beta<a) :
    Continuous (fun t : ℝ => HeckeReciprocal.reciprocal χ ((a:ℂ)+t*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (HeckeReciprocal.reciprocal_differentiableAt χ (by simpa using ha)).continuousAt.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I)).continuousAt

lemma LFunction_norm_le_of_poleRemoved (χ : Character) (s : ℂ) (h0 : s≠0) (h1 : s≠1)
    (A δ : ℝ) (hδ : 0<δ) (hd : δ≤‖s-1‖) (hA : ‖HeckeOrigin.poleRemoved χ s‖≤A) :
    ‖LFunction χ s‖≤A/δ := by
  apply (le_div_iff₀ hδ).mpr
  calc
    _ ≤ ‖LFunction χ s‖*‖s-1‖ := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = ‖HeckeOrigin.poleRemoved χ s‖ := by rw [HeckeOrigin.poleRemoved_eq χ h0 h1,norm_mul]; ring
    _ ≤ A := hA

lemma fixed_principal_w_bound (M : Id) [NeZero M] {cw υ : ℝ} (hcw : 1<cw)
    (hυ : υ∈Icc (19/20 : ℝ) cw) (hυ1 : υ≠1) (t : ℝ) :
    ‖LFunction (fixedPrincipal M) ((υ:ℂ)+t*I)‖≤
      (wAmplitude M cw/|υ-1|)*height t^3 := by
  have h0 : (υ:ℂ)+t*I≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hυ.1]
  have h1 : (υ:ℂ)+t*I≠1 := by intro h; exact hυ1 (by simpa using congrArg Complex.re h)
  have hδ : 0 < |υ-1| := abs_pos.mpr (sub_ne_zero.mpr hυ1)
  have h := LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ
    (pole_distance_vertical 1 υ t) (fixed_principal_w_growth M hcw hυ t)
  convert h using 1
  ring

lemma fixed_principal_z_bound (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) (hξ1 : 6*ξ≠1) :
    ‖LFunction (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖≤
      (zBoxAmplitude M Bz/|6*ξ-1|)*height t^3 := by
  have h0 : (6*((ξ:ℂ)+t*I) : ℂ)≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hξ.1]
  have h1 : (6*((ξ:ℂ)+t*I) : ℂ)≠1 := by intro h; exact hξ1 (by simpa using congrArg Complex.re h)
  have hd : |6*ξ-1|≤‖6*((ξ:ℂ)+t*I)-1‖ := by
    simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+t*I)-1)
  have hδ : 0 < |6*ξ-1| := abs_pos.mpr (sub_ne_zero.mpr hξ1)
  have h := LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ hd
    (fixed_principal_z_box_growth M Bz ξ t hξ)
  convert h using 1
  ring

def arithmeticMultiplier {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (X Y Z : ℝ) (s w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*(Y:ℂ)^(w-1)*
    HeckeReciprocal.reciprocal (η.excludePrimes S hS) s *
    (globalClosedCorrection η S s w z*slotMultiplier η J T b s w z)*
    LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w

lemma arithmetic_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    arithmeticMultiplier η S hS J T b X Y Z s w z*profile W0 W1 s w z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z *
        LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w := by
  unfold arithmeticMultiplier profile continuedSourceMultiplier
  ring

lemma arithmetic_onLines_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : HeckeZeroSupremum.beta<a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) (hυ0 : υ≠0) (hυ1 : υ≠1) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hH := global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (LFunction_vertical_continuous (fixedSourcePrincipal S hS) υ hυ0 hυ1).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.2))
  have hZL := (LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
    (mul_ne_zero (by norm_num) hξ0) hξ1).measurable.comp
      (by fun_prop : Measurable (fun p : HeightSpace => 6*p.1.2))
  have hZL' : Measurable (fun p : HeightSpace => LFunction (fixedSourcePrincipal S hS)
      (6*((ξ:ℂ)+p.1.2*I))) := by
    convert hZL using 1
    funext p
    congr 1
    push_cast
    ring
  unfold arithmeticMultiplier
  fun_prop (disch := aesop)

def boxScale (X Y Z a Bs Bz cw : ℝ) : ℝ :=
  scaleBound X (1/2-Bz) (1/2-33/200) * scaleBound Z (a+33/200-1) (Bs+Bz-1) *
    scaleBound Y (19/20-1) (cw-1)

lemma boxScale_pos (X Y Z a Bs Bz cw : ℝ) : 0<boxScale X Y Z a Bs Bz cw := by
  unfold boxScale
  exact mul_pos (mul_pos (scaleBound_pos _ _ _) (scaleBound_pos _ _ _)) (scaleBound_pos _ _ _)

def arithmeticAmplitude {ι : Type*} (S : Finset Id) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (X Y Z a Bs Bz cw C δw δz : ℝ) : ℝ :=
  boxScale X Y Z a Bs Bz cw * C * ((3/2)*slotBound J T b Bs Bz) *
    (zBoxAmplitude (∏P∈S,P) Bz/δz) * (wAmplitude (∏P∈S,P) cw/δw)

lemma height_le_joint_s (t v u : ℝ) : height t≤jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg v,abs_nonneg u]
lemma height_le_joint_z (t v u : ℝ) : height v≤jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg u]
lemma height_le_joint_w (t v u : ℝ) : height u≤jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg v]

lemma arithmetic_onLines_bound_of_gaps {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (δw δz : ℝ) (hdw : 0<δw) (hdz : 0<δz)
    (hC : 0≤C) (hR : ∀s : ℂ, a≤s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤C*(1+|s.im|^2))
    (p : HeightSpace)
    (hwgap : δw≤‖((υ:ℂ)+p.2*I)-1‖) (hzgap : δz≤‖6*((ξ:ℂ)+p.1.2*I)-1‖) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hx := cpow_le_scaleBound hX (1/2-((ξ:ℂ)+p.1.2*I))
    (show (1/2-((ξ:ℂ)+p.1.2*I) : ℂ).re∈Icc (1/2-Bz) (1/2-33/200) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero]
      norm_num only [show (1/2:ℂ).re=1/2 by norm_num]
      constructor <;> linarith [hξ.1,hξ.2])
  have hz := cpow_le_scaleBound hZ (((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)
    (show ((((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1) : ℂ).re∈Icc (a+33/200-1) (Bs+Bz-1) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero,one_re]; constructor <;> linarith [hσ.1,hσ.2,hξ.1,hξ.2])
  have hy := cpow_le_scaleBound hY (((υ:ℂ)+p.2*I)-1)
    (show (((υ:ℂ)+p.2*I)-1 : ℂ).re∈Icc (19/20-1) (cw-1) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero,one_re]; constructor <;> linarith [hυ.1,hυ.2])
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)‖≤C*height p.1.1^2 := by
    apply (hR _ (by simpa using hσ.1)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg p.1.1]
  have hh := combined_slot_bound η S hS.tail J T b hT ((σ:ℂ)+p.1.1*I)
    ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) Bs Bz
    (by simpa using And.intro (ha.trans hσ.1) hσ.2) (by simpa using hυ.1) (by simpa using hξ)
  have hw0 : (υ:ℂ)+p.2*I≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hυ.1]
  have hw1 : (υ:ℂ)+p.2*I≠1 := by
    intro h; rw [h,sub_self,norm_zero] at hwgap; linarith
  have hz0 : (6*((ξ:ℂ)+p.1.2*I) : ℂ)≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hξ.1]
  have hz1 : (6*((ξ:ℂ)+p.1.2*I) : ℂ)≠1 := by
    intro h; rw [h,sub_self,norm_zero] at hzgap; linarith
  have hlz0 := LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hz0 hz1 _ _ hdz hzgap
    (fixed_principal_z_box_growth (∏P∈S,P) Bz ξ p.1.2 hξ)
  have hlw0 := LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hw0 hw1 _ _ hdw hwgap
    (fixed_principal_w_growth (∏P∈S,P) hcw hυ p.2)
  have hlz : ‖LFunction (fixedPrincipal (∏P∈S,P)) (6*((ξ:ℂ)+p.1.2*I))‖≤
      (zBoxAmplitude (∏P∈S,P) Bz/δz)*height p.1.2^3 := by convert hlz0 using 1; ring
  have hlw : ‖LFunction (fixedPrincipal (∏P∈S,P)) ((υ:ℂ)+p.2*I)‖≤
      (wAmplitude (∏P∈S,P) cw/δw)*height p.2^3 := by convert hlw0 using 1; ring
  have hp1 := (height_pos p.1.1).le
  have hp2 := (height_pos p.1.2).le
  have hp3 := (height_pos p.2).le
  have hpJ := (jointHeight_pos p.1.1 p.1.2 p.2).le
  have hsX := (scaleBound_pos X (1/2-Bz) (1/2-33/200)).le
  have hsY := (scaleBound_pos Y (19/20-1) (cw-1)).le
  have hsZ := (scaleBound_pos Z (a+33/200-1) (Bs+Bz-1)).le
  have hHB := mul_nonneg (by norm_num : (0:ℝ)≤3/2) (slotBound_nonneg J T b Bs Bz)
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏P∈S,P) Bz) hdz.le
  have hAW := div_nonneg (wAmplitude_pos (∏P∈S,P) hcw).le hdw.le
  calc
    _ = ‖(X:ℂ)^(1/2-((ξ:ℂ)+p.1.2*I))‖ *
        ‖(Z:ℂ)^(((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)‖ *
        ‖(Y:ℂ)^(((υ:ℂ)+p.2*I)-1)‖ *
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)‖ *
        ‖globalClosedCorrection η S ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
          slotMultiplier η J T b ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ := by
      simp only [arithmeticMultiplier,norm_mul]
    _ ≤ scaleBound X (1/2-Bz) (1/2-33/200)*scaleBound Z (a+33/200-1) (Bs+Bz-1)*
        scaleBound Y (19/20-1) (cw-1)*(C*height p.1.1^2)*((3/2)*slotBound J T b Bs Bz)*
        ((zBoxAmplitude (∏P∈S,P) Bz/δz)*height p.1.2^3)*
        ((wAmplitude (∏P∈S,P) cw/δw)*height p.2^3) := by
      gcongr <;> first | positivity | exact hlz | exact hlw
    _ ≤ scaleBound X (1/2-Bz) (1/2-33/200)*scaleBound Z (a+33/200-1) (Bs+Bz-1)*
        scaleBound Y (19/20-1) (cw-1)*(C*jointHeight p.1.1 p.1.2 p.2^2)*((3/2)*slotBound J T b Bs Bz)*
        ((zBoxAmplitude (∏P∈S,P) Bz/δz)*jointHeight p.1.1 p.1.2 p.2^3)*
        ((wAmplitude (∏P∈S,P) cw/δw)*jointHeight p.1.1 p.1.2 p.2^3) := by
      gcongr <;> first | positivity | exact height_le_joint_s _ _ _ | exact height_le_joint_z _ _ _ | exact height_le_joint_w _ _ _
    _ = _ := by unfold arithmeticAmplitude boxScale; ring

lemma arithmetic_onLines_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1)
    (hC : 0≤C) (hR : ∀s : ℂ, a≤s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤C*(1+|s.im|^2))
    (p : HeightSpace) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1| *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  apply arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ |υ-1| |6*ξ-1| (abs_pos.mpr (sub_ne_zero.mpr hυ1))
    (abs_pos.mpr (sub_ne_zero.mpr hξ1)) hC hR p
  · exact pole_distance_vertical 1 υ p.2
  · simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)

theorem continued_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ υ
    (by linarith) (fun p : HeightSpace => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I))
    (arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
      (by linarith) hξ1 (by linarith [hυ.1]) hυ1).aestronglyMeasurable
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|) 8
    (arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
      ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR)
  apply hi.congr
  exact Eventually.of_forall (fun p => arithmetic_profile_eq_source η S hS.prime J T b W0 W1 X Y Z _ _ _)

lemma outer_height_ne_zero_ae : ∀ᵐp : HeightSpace ∂heightMeasure, p.1.1≠0 := by
  have hh : ∀ᵐp : ℝ×ℝ ∂volume.prod volume, p.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  exact Measure.quasiMeasurePreserving_fst.ae hh

lemma continued_joint_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    (fun p : HeightSpace => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) =ᵐ[heightMeasure]
    (fun p : HeightSpace => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
      ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
      (slotMultiplier η J T b ((a:ℂ)+p.1.1*I)) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  filter_upwards [outer_height_ne_zero_ae] with p hp
  apply continued_source_eq_raw
  · intro h; exact hp (by simpa using congrArg Complex.im h)
  · intro h; exact hp (by simpa using congrArg Complex.im h)

theorem source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  apply (continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1).congr
  filter_upwards [continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ] with p hp
  rw [hp]

theorem source_joint_fubini {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
    ((∫p, F p ∂heightMeasure)=∫t : ℝ,∫v : ℝ,∫u : ℝ,F ((t,v),u)) ∧
    ((∫p, F p ∂heightMeasure)=∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((t,v),u)) := by
  dsimp only
  have hi := source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  constructor
  · rw [integral_prod _ hi]
    exact integral_prod _ hi.integral_prod_left
  · rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu

lemma arithmeticAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (X Y Z a Bs Bz cw C δw δz : ℝ) (hcw : 1<cw) (hC : 0≤C) (hw : 0≤δw) (hz : 0≤δz) :
    0≤arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hbox := (boxScale_pos X Y Z a Bs Bz cw).le
  have hb := slotBound_nonneg J T b Bs Bz
  have hza := zBoxAmplitude_nonneg (∏P∈S,P) Bz
  have hwa := (wAmplitude_pos (∏P∈S,P) hcw).le
  unfold arithmeticAmplitude
  positivity

theorem continued_source_slices {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) (N : ℕ) :
    ∃ C K : ℝ, 0≤C ∧ 0<K ∧ ∀axis : SliceAxis,∀R : ℝ,
      let F := fun p : HeightSpace =>
        continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
          ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume)≤
        arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1| *K/height R^N := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ υ υ (by linarith) 8 N
  refine ⟨C,K,hC,hK,?_⟩
  intro axis R
  let G : HeightSpace → ℂ := fun p => arithmeticMultiplier η S hS.prime J T b X Y Z
    ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)
  have hm := arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
    (by linarith) hξ1 (by linarith [hυ.1]) hυ1
  have hbound := arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
    ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR
  have hh := hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩ axis R
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|)
    (arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a a ξ cw C _ _ hcw hC (abs_nonneg _) (abs_nonneg _))
    (fun q => G (sliceMap axis R q)) ((hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable)
    (fun q => hbound (sliceMap axis R q))
  simpa only [G,onLines,arithmetic_profile_eq_source] using hh

theorem source_w_leftover_outer_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    Integrable (fun v : ℝ => verticalIntegral (19/20) (fun w =>
      K w ((1/6+e:ℝ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime)
        (6*((1/6+e:ℝ)+v*I))*LFunction (fixedSourcePrincipal S hS.prime) w)) := by
  obtain ⟨C,K,hC,hK,hslice⟩ := continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z a (1/6+e) (19/20) 3 hX hY hZ ha hβ
    (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num) 0
  have hi := (hslice .s t).1
  have hs0 : (a:ℂ)+t*I≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have hpair : Integrable (fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I))
        ((19/20:ℝ)+q.2*I) ((1/6+e:ℝ)+q.1*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((1/6+e:ℝ)+q.1*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((19/20:ℝ)+q.2*I)) (volume.prod volume) := by
    simpa only [sliceMap,continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ hs0 hs1] using hi
  simpa only [verticalIntegral] using hpair.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem source_z_boundary_any {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0⊆Icc a0 b0) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s : ℂ) (hs : 7/8≤s.re) (hη : LFunction (η.excludePrimes S hS.prime) s≠0)
    {e : ℝ} (he : 0<e) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)) (33/200) (1/6+e) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 (∏P∈S,P)
    X Y Z hX hZ (η.excludePrimes S hS.prime) s hη
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) (AL := zBoxAmplitude (∏P∈S,P) (1/6+e))
    he (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _))
    (zBoxAmplitude_nonneg _ _) 0 3
  · exact (combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)<z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using combined_slot_bound η S hS.tail J T b hT s
      1 ((x:ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)
  · intro x hx t _
    exact fixed_principal_z_box_growth (∏P∈S,P) (1/6+e) x t hx

theorem source_ordered_at_height {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (he : 0<e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) =
    verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) +
    HeckeReciprocal.regularizedL π 1*verticalIntegral (33/200) (fun z => K 1 z*LFunction π (6*z)) +
    (HeckeReciprocal.regularizedL π 1)^2/6*K 1 (1/6) := by
  dsimp only
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hs : (7/8 : ℝ)≤(((a:ℂ)+t*I) : ℂ).re := by simpa using ha
  have hη := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime)
    (show HeckeZeroSupremum.beta<(((a:ℂ)+t*I) : ℂ).re by simpa using hβ) (Or.inl hs1)
  have hzb := source_z_boundary_any η S hS J T b hT W0 W1 a0 b0 ha0 hW0 X Y Z hX hZ
    ((a:ℂ)+t*I) hs hη he
  apply source_ordered_double_shift (fixedSourcePrincipal S hS.prime) _ hcw he
  · intro z hz
    apply (source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith)).mono
    intro w hw
    change (9/10 : ℝ)<w.re
    linarith [hw.1]
  · intro z hz
    have hh := ProbeFiniteProductBounds.source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏P∈S,P) X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith) hη hcw
    convert boundary_mul_const _ _ _ hh (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
    funext w
    dsimp only [fixedSourcePrincipal,fixedPrincipal]
    ring
  · apply (source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
      ((a:ℂ)+t*I) 1 hs (by norm_num)).mono
    intro z hz
    change (4/25 : ℝ)<z.re
    linarith [hz.1]
  · exact hzb
  · exact source_w_leftover_outer_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e t hX hY hZ ha hβ he hs1

theorem source_ordered_ae {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (he : 0<e) :
    ∀ᵐt : ℝ, let s : ℂ := (a:ℂ)+t*I
      let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s)
      let π := fixedSourcePrincipal S hS.prime
      verticalIntegral (1/6+e) (fun z => verticalIntegral cw
        (fun w => K w z*LFunction π (6*z)*LFunction π w)) =
      verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => K w z*LFunction π (6*z)*LFunction π w)) +
      HeckeReciprocal.regularizedL π 1*verticalIntegral (33/200) (fun z => K 1 z*LFunction π (6*z)) +
      (HeckeReciprocal.regularizedL π 1)^2/6*K 1 (1/6) := by
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply source_ordered_at_height η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e t cw hX hY hZ ha hβ hcw he
  intro h
  exact ht (by simpa using congrArg Complex.im h)

def residueArithmetic {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (X Z : ℝ) (s z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*HeckeReciprocal.reciprocal (η.excludePrimes S hS) s *
    (globalClosedCorrection η S s 1 z*slotMultiplier η J T b s 1 z)*
    LFunction (fixedSourcePrincipal S hS) (6*z)

lemma residue_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s z : ℂ) :
    residueArithmetic η S hS J T b X Z s z*profile W0 W1 s 1 z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s 1 z *
        LFunction (fixedSourcePrincipal S hS) (6*z) := by
  unfold residueArithmetic profile continuedSourceMultiplier
  simp only [sub_self,Complex.cpow_zero,mul_one]
  ring

lemma residue_arithmetic_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (X Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (hβ : HeckeZeroSupremum.beta<a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) :
    Measurable (fun q : ℝ×ℝ => residueArithmetic η S hS J T b X Z
      ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) := by
  have hH := global_correction_measurable η S (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := slot_multiplier_measurable η J T b (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (reciprocal_vertical_continuous (η.excludePrimes S hS) a hβ).measurable.comp
    (by fun_prop : Measurable (fun q : ℝ×ℝ => q.1))
  have hL := (LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
    (mul_ne_zero (by norm_num) hξ0) hξ1).measurable.comp
      (by fun_prop : Measurable (fun q : ℝ×ℝ => 6*q.2))
  have hL' : Measurable (fun q : ℝ×ℝ => LFunction (fixedSourcePrincipal S hS)
      (6*((ξ:ℂ)+q.2*I))) := by
    convert hL using 1
    funext q
    congr 1
    push_cast
    ring
  unfold residueArithmetic
  fun_prop (disch := aesop)

def residueAmplitude {ι : Type*} (S : Finset Id) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ) (X Z a ξ C : ℝ) : ℝ :=
  X^(1/2-ξ)*Z^(a+ξ-1)*C*((3/2)*slotBound J T b a ξ)*
    (zBoxAmplitude (∏P∈S,P) ξ/|6*ξ-1|)

lemma residue_arithmetic_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Z a ξ C : ℝ) (hX : 0<X) (hZ : 0<Z) (ha : 7/8≤a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1)
    (hC : 0≤C) (hR : ∀s : ℂ,a≤s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤C*(1+|s.im|^2))
    (q : ℝ×ℝ) :
    ‖residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)‖≤
      residueAmplitude S J T b X Z a ξ C*jointHeight q.1 q.2 0^5 := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)‖≤C*height q.1^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg q.1]
  have hh := combined_slot_bound η S hS.tail J T b hT ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I) a ξ
    (by simpa using ha) (by norm_num) (by simpa using hξ)
  have hL := fixed_principal_z_bound (∏P∈S,P) ξ ξ q.2 ⟨hξ,le_rfl⟩ hξ1
  have hX0 := (Real.rpow_pos_of_pos hX (1/2-ξ)).le
  have hZ0 := (Real.rpow_pos_of_pos hZ (a+ξ-1)).le
  have hHB := mul_nonneg (by norm_num : (0:ℝ)≤3/2) (slotBound_nonneg J T b a ξ)
  have hA := div_nonneg (zBoxAmplitude_nonneg (∏P∈S,P) ξ) (abs_nonneg (6*ξ-1))
  have hq1 := (height_pos q.1).le
  have hq2 := (height_pos q.2).le
  have hqJ := (jointHeight_pos q.1 q.2 0).le
  calc
    _ = X^(1/2-ξ)*Z^(a+ξ-1)*
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)‖ *
        ‖globalClosedCorrection η S ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
          slotMultiplier η J T b ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ := by
      simp only [residueArithmetic,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
        Complex.norm_cpow_eq_rpow_re_of_pos hZ]
      norm_num
    _ ≤ X^(1/2-ξ)*Z^(a+ξ-1)*(C*height q.1^2)*((3/2)*slotBound J T b a ξ)*
        ((zBoxAmplitude (∏P∈S,P) ξ/|6*ξ-1|)*height q.2^3) := by
      gcongr
      first | positivity | exact hL
    _ ≤ X^(1/2-ξ)*Z^(a+ξ-1)*(C*jointHeight q.1 q.2 0^2)*((3/2)*slotBound J T b a ξ)*
        ((zBoxAmplitude (∏P∈S,P) ξ/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr <;> first | positivity | exact height_le_joint_s _ _ _ | exact height_le_joint_z _ _ _
    _ = _ := by unfold residueAmplitude; ring

lemma residueAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ) (X Z a ξ C : ℝ)
    (hX : 0≤X) (hZ : 0≤Z) (hC : 0≤C) : 0≤residueAmplitude S J T b X Z a ξ C := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hb := slotBound_nonneg J T b a ξ
  have hza := zBoxAmplitude_nonneg (∏P∈S,P) ξ
  unfold residueAmplitude
  positivity

theorem continued_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) 5 0
  have hm := residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith) hξ1
  have hb := residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hh := (hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ 1 ⟨le_rfl,le_rfl⟩ .w 0
    (residueAmplitude S J T b X Z a ξ C)
    (residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC)
    (fun q : ℝ×ℝ => residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I))
    hm.aestronglyMeasurable hb).1
  apply hh.congr
  apply Eventually.of_forall
  intro q
  simpa only [sliceMap,onLines,ofReal_one,ofReal_zero,zero_mul,add_zero] using
    residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)

theorem residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
      1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  apply (continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1).congr
  have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  filter_upwards [hh] with q hq
  have h0 : (a:ℂ)+q.1*I≠0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+q.1*I≠1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  rw [continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem source_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) w z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w))) := by
  have hi := source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  simpa only [verticalIntegral,integral_const_mul,mul_assoc] using
    (hi.integral_prod_left.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))).const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem residue_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) 1 z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z))) := by
  have hi := residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  simpa only [verticalIntegral] using hi.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem source_ordered_outer {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (he : 0<e) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) =
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) +
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))) +
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  let R := HeckeReciprocal.regularizedL π 1
  let A := fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral cw
    (fun w => K s w z*LFunction π (6*z)*LFunction π w))
  let B := fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
    (fun w => K s w z*LFunction π (6*z)*LFunction π w))
  let D := fun s => R*verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))
  let E := fun s => R^2/6*K s 1 (1/6)
  have hA : Integrable (fun t : ℝ => A ((a:ℂ)+t*I)) :=
    source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) cw cw hX hY hZ ha hβ (by linarith) hcw ⟨by linarith,le_rfl⟩
      (by linarith) (ne_of_gt hcw)
  have hB : Integrable (fun t : ℝ => B ((a:ℂ)+t*I)) :=
    source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) (19/20) cw hX hY hZ ha hβ (by linarith) hcw ⟨le_rfl,by linarith⟩
      (by linarith) (by norm_num)
  have hD : Integrable (fun t : ℝ => D ((a:ℂ)+t*I)) :=
    (residue_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (33/200) hX hZ ha hβ le_rfl (by norm_num)).const_mul R
  have hp : ∀ᵐt : ℝ,A ((a:ℂ)+t*I)=B ((a:ℂ)+t*I)+D ((a:ℂ)+t*I)+E ((a:ℂ)+t*I) :=
    source_ordered_ae η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e cw hX hY hZ ha hβ hcw he
  have hE : Integrable (fun t : ℝ => E ((a:ℂ)+t*I)) := by
    apply ((hA.sub hB).sub hD).congr
    filter_upwards [hp] with t ht
    change A ((a:ℂ)+t*I)-B ((a:ℂ)+t*I)-D ((a:ℂ)+t*I)=E ((a:ℂ)+t*I)
    rw [ht]
    ring
  have heq : verticalIntegral a A=verticalIntegral a (fun s => B s+D s+E s) := by
    unfold verticalIntegral
    congr 1
    exact integral_congr_ae hp
  rw [verticalIntegral_add a _ _ (hB.add hD) hE,verticalIntegral_add a _ _ hB hD] at heq
  change verticalIntegral a A=verticalIntegral a B+R*verticalIntegral a _+R^2/6*verticalIntegral a _
  rw [heq]
  simp only [D,E,verticalIntegral,integral_const_mul]
  ring

theorem source_initial_ordered {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) =
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) +
    R*verticalIntegral 3 (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))) +
    R^2/6*verticalIntegral 3 (fun s => K s 1 (1/6)) := by
  simpa only [show (1/6+11/6:ℝ)=2 by norm_num] using
    source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z 3 (11/6) 3 hX hY hZ (by norm_num)
      (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num) (by norm_num)

theorem source_uniform_joint_tails {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      6*ξ≠1→υ≠1→∀R : ℝ,0≤R→
      (∫p : HeightSpace in outsideBox R,
        ‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)
          (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
          ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
          LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
          LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ∂heightMeasure) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1| * K/(1+R)^N := by
  obtain ⟨K,hK,hk⟩ := profile_uniform_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8 N
  obtain ⟨K0,hK0,hm⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ hξ1 hυ1 R hR0
  let A := arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1|
  have hA : 0≤A := arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a Bs Bz cw C _ _ hcw hC
    (abs_nonneg _) (abs_nonneg _)
  have hi := source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z σ ξ υ cw hX hY hZ (ha.trans hσ.1) (hβ.trans_le hσ.1) hξ.1 hcw hυ hξ1 hυ1
  have hmi := (hm σ hσ ξ hξ υ hυ).1
  have hbound := arithmetic_onLines_bound η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ hξ1 hυ1 hC hR
  have hdom : ∀ᵐp : HeightSpace ∂heightMeasure,
      ‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ≤
      A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖) := by
    filter_upwards [continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z σ ξ υ] with p hp
    rw [←hp,←arithmetic_profile_eq_source]
    rw [norm_mul]
    simpa only [mul_assoc,A,onLines] using mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg (onLines W0 W1 σ ξ υ p))
  calc
    _ ≤ ∫p : HeightSpace in outsideBox R,
        A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖) ∂heightMeasure :=
      integral_mono_ae hi.norm.integrableOn (hmi.const_mul A).integrableOn (ae_restrict_of_ae hdom)
    _ = A*(∫p : HeightSpace in outsideBox R,
        jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure) := integral_const_mul _ _
    _ ≤ A*(K/(1+R)^N) := mul_le_mul_of_nonneg_left (hk σ hσ ξ hξ υ hυ R hR0) hA
    _ = _ := by dsimp [A]; ring

lemma LFunction_measurable (χ : Character) : Measurable (LFunction χ) := by
  classical
  have hm := ((HeckeOrigin.poleRemoved_entire χ).continuous.measurable).div
    (measurable_id.sub_const (1:ℂ))
  have h1 : Measurable (fun s : ℂ => if s=1 then LFunction χ 1 else HeckeOrigin.poleRemoved χ s/(s-1)) :=
    Measurable.ite (measurableSet_singleton (1:ℂ))
    (measurable_const : Measurable (fun _ : ℂ => LFunction χ 1)) hm
  have h0 : Measurable (fun s : ℂ => if s=0 then LFunction χ 0 else
      if s=1 then LFunction χ 1 else HeckeOrigin.poleRemoved χ s/(s-1)) :=
    Measurable.ite (measurableSet_singleton (0:ℂ))
    (measurable_const : Measurable (fun _ : ℂ => LFunction χ 0)) h1
  convert h0 using 1
  funext s
  split_ifs with hs0 hs1
  · subst s; rfl
  · subst s; rfl
  · exact LFunction_eq_pole_quotient χ hs0 hs1

lemma arithmetic_onLines_measurable_all {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : HeckeZeroSupremum.beta<a) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hH := global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p : HeightSpace => (υ:ℂ)+p.2*I))
  have hZL := (LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p : HeightSpace => 6*((ξ:ℂ)+p.1.2*I)))
  unfold arithmeticMultiplier
  fun_prop (disch := aesop)

def joinWGap (axis : SliceAxis) (υ : ℝ) : ℝ := if axis=.w then 1 else |υ-1|
def joinZGap (axis : SliceAxis) (ξ : ℝ) : ℝ := if axis=.z then 6 else |6*ξ-1|

lemma joinWGap_pos (axis : SliceAxis) (υ : ℝ) (hυ : axis≠.w→υ≠1) : 0<joinWGap axis υ := by
  unfold joinWGap
  split_ifs with h
  · norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr (hυ h))
lemma joinZGap_pos (axis : SliceAxis) (ξ : ℝ) (hξ : axis≠.z→6*ξ≠1) : 0<joinZGap axis ξ := by
  unfold joinZGap
  split_ifs with h
  · norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr (hξ h))

lemma slice_w_gap (axis : SliceAxis) (R υ : ℝ) (hR : 1≤|R|) (q : ℝ×ℝ) :
    joinWGap axis υ≤‖((υ:ℂ)+(sliceMap axis R q).2*I)-1‖ := by
  cases axis
  · simpa [joinWGap,sliceMap] using pole_distance_vertical 1 υ q.2
  · simpa [joinWGap,sliceMap] using pole_distance_vertical 1 υ q.2
  · simpa [joinWGap,sliceMap] using hR.trans (pole_distance_horizontal 1 υ R)
lemma slice_z_gap (axis : SliceAxis) (R ξ : ℝ) (hR : 1≤|R|) (q : ℝ×ℝ) :
    joinZGap axis ξ≤‖6*((ξ:ℂ)+(sliceMap axis R q).1.2*I)-1‖ := by
  cases axis
  · simpa [joinZGap,sliceMap] using Complex.abs_re_le_norm (6*((ξ:ℂ)+q.1*I)-1)
  · have hi : 6*|R|≤‖6*((ξ:ℂ)+R*I)-1‖ := by
      simpa [abs_mul] using Complex.abs_im_le_norm (6*((ξ:ℂ)+R*I)-1)
    simpa [joinZGap,sliceMap] using (by linarith : (6:ℝ)≤6*|R|).trans hi
  · simpa [joinZGap,sliceMap] using Complex.abs_re_le_norm (6*((ξ:ℂ)+q.2*I)-1)

theorem source_uniform_high_slices {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      ∀axis : SliceAxis, (axis≠.w→υ≠1)→(axis≠.z→6*ξ≠1)→∀R : ℝ,1≤|R|→
      let F := fun p : HeightSpace => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ) * K/height R^N := by
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR0
  have hm := arithmetic_onLines_measurable_all η S hS.prime J T b X Y Z σ ξ υ hX hY hZ (hβ.trans_le hσ.1)
  have hb (q : ℝ×ℝ) := arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C
    hX hY hZ ha hσ hξ hcw hυ (joinWGap axis υ) (joinZGap axis ξ)
    (joinWGap_pos axis υ hυ1) (joinZGap_pos axis ξ hξ1) hC hR (sliceMap axis R q)
    (slice_w_gap axis R υ hR0 q) (slice_z_gap axis R ξ hR0 q)
  have hh := hk σ hσ ξ hξ υ hυ axis R
    (arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ))
    (arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a Bs Bz cw C _ _ hcw hC
      (joinWGap_pos axis υ hυ1).le (joinZGap_pos axis ξ hξ1).le)
    (fun q : ℝ×ℝ => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((σ:ℂ)+(sliceMap axis R q).1.1*I) ((υ:ℂ)+(sliceMap axis R q).2*I)
      ((ξ:ℂ)+(sliceMap axis R q).1.2*I))
    (hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable hb
  simpa only [onLines,arithmetic_profile_eq_source] using hh

theorem residue_uniform_moments {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξ : ℝ) (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a)
    (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Z→
      ∃C : ℝ,0≤C ∧
      let F := fun q : ℝ×ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
          (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
          1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
      Integrable (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N*‖F q‖) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)≤residueAmplitude S J T b X Z a ξ C*K := by
  obtain ⟨K,hK,hk⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) (5+N) 0
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  let A := residueAmplitude S J T b X Z a ξ C
  have hA : 0≤A := residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC
  let F : ℝ×ℝ → ℂ := fun q => residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) *
    onLines W0 W1 a ξ 1 (sliceMap .w 0 q)
  have hm := residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith) hξ1
  have hFc : AEStronglyMeasurable F (volume.prod volume) := hm.aestronglyMeasurable.mul
    (((onLines_continuous W0 W1 a1 b1 ha1 hW1 a ξ 1 (by linarith)).comp
      (sliceMap_continuous .w 0)).aestronglyMeasurable)
  have hb := residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hmom := hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ 1 ⟨le_rfl,le_rfl⟩ .w 0
  have hdom (q : ℝ×ℝ) : jointHeight q.1 q.2 0^N*‖F q‖≤
      A*(jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖) := by
    dsimp only [F]
    rw [norm_mul]
    calc
      _ ≤ jointHeight q.1 q.2 0^N * ((A*jointHeight q.1 q.2 0^5)*
          ‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hb q) (norm_nonneg _))
          (pow_nonneg (jointHeight_pos _ _ _).le _)
      _ = _ := by rw [pow_add]; ring
  have hi : Integrable (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N*‖F q‖) (volume.prod volume) := by
    apply (hmom.1.const_mul A).mono'
    · exact (by unfold jointHeight; fun_prop : Continuous (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N)).aestronglyMeasurable.mul hFc.norm
    · apply Eventually.of_forall
      intro q
      simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)),sliceMap] using hdom q
  have hn : (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)≤A*K := by
    calc
      _ ≤ ∫q : ℝ×ℝ,A*(jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖)
          ∂volume.prod volume := integral_mono hi (hmom.1.const_mul A) hdom
      _ = A*(∫q : ℝ×ℝ,jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖
          ∂volume.prod volume) := integral_const_mul _ _
      _ ≤ A*K := mul_le_mul_of_nonneg_left (by simpa only [sliceMap,pow_zero,div_one] using hmom.2) hA
  have heq : F =ᵐ[volume.prod volume] (fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
        (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) := by
    have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    filter_upwards [hh] with q hq
    have h0 : (a:ℂ)+q.1*I≠0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
    have h1 : (a:ℂ)+q.1*I≠1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
    dsimp only [F,onLines,sliceMap]
    simp only [ofReal_one,ofReal_zero,zero_mul,add_zero]
    rw [residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z,
      continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
  have hweight : (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N)=ᵐ[volume.prod volume]
      (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N) := Eventually.of_forall (fun _ => rfl)
  have heqw := hweight.mul (heq.fun_comp (fun z : ℂ => ‖z‖))
  exact ⟨hi.congr heqw, (integral_congr_ae heqw).symm.trans_le hn⟩

def residueOutside (R : ℝ) : Set (ℝ×ℝ) := {q | R < |q.1| ∨ R < |q.2|}
lemma residueOutside_measurable (R : ℝ) : MeasurableSet (residueOutside R) := by
  unfold residueOutside
  measurability

theorem residue_uniform_tails {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξ : ℝ) (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a)
    (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Z→
      ∃C : ℝ,0≤C ∧ ∀R : ℝ,0≤R→
      let F := fun q : ℝ×ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
          (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
          1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
      (∫q : ℝ×ℝ in residueOutside R,‖F q‖ ∂volume.prod volume)≤
        residueAmplitude S J T b X Z a ξ C*K/(1+R)^N := by
  obtain ⟨K,hK,hk⟩ := residue_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hZ
  obtain ⟨C,hC,hi,hb⟩ := hk η S hS J T b hT X Y Z hX hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  let F := fun q : ℝ×ℝ =>
    sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
      (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
      1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
  have hF := residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  have hdom (q : ℝ×ℝ) (hq : q∈residueOutside R) :
      ‖F q‖≤jointHeight q.1 q.2 0^N*‖F q‖/(1+R)^N := by
    have hh : 1+R≤jointHeight q.1 q.2 0 := by
      rcases hq with h|h <;> unfold jointHeight <;> simp only [abs_zero,add_zero] <;>
        linarith [abs_nonneg q.1,abs_nonneg q.2]
    have hp := pow_le_pow_left₀ (by linarith : 0≤1+R) hh N
    apply (le_div_iff₀ (pow_pos (by linarith : 0<1+R) N)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (norm_nonneg (F q))
  change (∫q : ℝ×ℝ in residueOutside R,‖F q‖ ∂volume.prod volume)≤_
  calc
    _ ≤ ∫q : ℝ×ℝ in residueOutside R,jointHeight q.1 q.2 0^N*‖F q‖/(1+R)^N
        ∂volume.prod volume := setIntegral_mono_on hF.norm.integrableOn (hi.div_const _).integrableOn
          (residueOutside_measurable R) hdom
    _ = (∫q : ℝ×ℝ in residueOutside R,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)/(1+R)^N := integral_div _ _
    _ ≤ (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)/(1+R)^N := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact setIntegral_le_integral hi (Eventually.of_forall (fun q =>
        mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)))
    _ ≤ _ := div_le_div_of_nonneg_right hb (by positivity)

lemma continued_high_slice_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ ξ υ : ℝ)
    (axis : SliceAxis) (R : ℝ) (hR : R≠0) :
    (fun q : ℝ×ℝ => let p := sliceMap axis R q
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS) ((υ:ℂ)+p.2*I)) =ᵐ[volume.prod volume]
    (fun q : ℝ×ℝ => let p := sliceMap axis R q
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) ((σ:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS) ((υ:ℂ)+p.2*I)) := by
  have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,(sliceMap axis R q).1.1≠0 := by
    cases axis
    · exact Eventually.of_forall (fun _ => hR)
    · exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    · exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  filter_upwards [hh] with q hq
  have h0 : (σ:ℂ)+(sliceMap axis R q).1.1*I≠0 := by
    intro h; exact hq (by simpa using congrArg Complex.im h)
  have h1 : (σ:ℂ)+(sliceMap axis R q).1.1*I≠1 := by
    intro h; exact hq (by simpa using congrArg Complex.im h)
  dsimp only
  rw [continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

lemma source_axis_gaps {e : ℝ} (he : 0<e) :
    |(19/20:ℝ)-1|=1/20 ∧ |6*(1/6+e)-1|=6*e ∧ |6*(33/200:ℝ)-1|=1/100 := by
  constructor
  · norm_num
  constructor
  · rw [show 6*(1/6+e)-1=6*e by ring,abs_of_pos (by positivity)]
  · norm_num

theorem raw_source_uniform_high_slices {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      ∀axis : SliceAxis, (axis≠.w→υ≠1)→(axis≠.z→6*ξ≠1)→∀R : ℝ,1≤|R|→
      let F := fun p : HeightSpace => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((σ:ℂ)+p.1.1*I) (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I))
        (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I)) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ) * K/height R^N := by
  obtain ⟨K,hK,hk⟩ := source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs Bz cw ha hβ hcw N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have hh := hc σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have heq := continued_high_slice_ae_raw η S hS.prime J T b W0 W1 X Y Z σ ξ υ axis R
    (by intro h; norm_num [h] at hR)
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

end SevenEighths.ProbePrincipalContours
end

end OAI

end Source1801

/- Original source: OAI/NumberTheory/DirichletL/Detector/PrincipalTransport.lean; sha256: 99dd35d116ce437bcb9fcb40abd411240684b570c6eb8a88ebd594f60df65870 -/
section Source1802
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalTransport
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma gaussianMoment_tendsto (n : ℕ) : Tendsto (gaussianMoment n) atTop (𝓝 0) := by
  have hb (t : ℝ) : gaussianMoment n t ≤ (2:ℝ)^(n-1)*Continuation.polynomialGaussian n t := by
    have h := add_pow_le (by norm_num : (0:ℝ)≤1) (abs_nonneg t) n
    unfold gaussianMoment height Continuation.polynomialGaussian
    calc
      _ ≤ ((2:ℝ)^(n-1)*(1^n+|t|^n))*Real.exp (-(t^2)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := by simp only [one_pow]; ring
  exact squeeze_zero (gaussianMoment_nonneg n) hb
    (by simpa using (Continuation.polynomialGaussian_tendsto n).const_mul ((2:ℝ)^(n-1)))

lemma gaussianMoment_even (n : ℕ) (t : ℝ) : gaussianMoment n (-t)=gaussianMoment n t := by
  simp [gaussianMoment,height]

lemma gaussianMoment_tendsto_bot (n : ℕ) : Tendsto (gaussianMoment n) atBot (𝓝 0) := by
  have h := (gaussianMoment_tendsto n).comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def,gaussianMoment_even] using h

lemma shifted_gaussian_integrable (n : ℕ) (v : ℝ) :
    Integrable (fun t : ℝ => gaussianMoment n (t+v)) := by
  exact (measurePreserving_add_right volume v).integrable_comp_of_integrable (gaussianMoment_integrable n)

lemma shifted_gaussian_top (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (t+v)) atTop (𝓝 0) :=
  (gaussianMoment_tendsto n).comp (tendsto_atTop_add_const_right _ v tendsto_id)

lemma shifted_gaussian_bottom (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (-t+v)) atTop (𝓝 0) :=
by
  convert shifted_gaussian_top n (-v) using 1
  funext t
  rw [←gaussianMoment_even n (t + -v)]
  congr 1
  ring

theorem verticalIntegral_eq_of_shifted_gaussian (F : ℂ → ℂ) {a c A : ℝ}
    (n : ℕ) (v : ℝ) (hac : a≤c)
    (hF : DifferentiableOn ℂ F {s : ℂ | a≤s.re ∧ s.re≤c})
    (hb : ∀σ∈Icc a c,∀t : ℝ,‖F ((σ:ℂ)+t*I)‖≤A*gaussianMoment n (t+v)) :
    verticalIntegral a F=verticalIntegral c F := by
  have hc (σ : ℝ) (hσ : σ∈Icc a c) : Continuous (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    hF.continuousOn.comp_continuous (by fun_prop) (by intro t; simpa using hσ)
  have hi (σ : ℝ) (hσ : σ∈Icc a c) : Integrable (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    ((shifted_gaussian_integrable n v).const_mul A).mono' (hc σ hσ).aestronglyMeasurable
      (Eventually.of_forall (hb σ hσ))
  have hj (T : ℝ) : ‖∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)‖≤A*gaussianMoment n (T+v)*|c-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    exact hb σ (by simpa [uIcc_of_le hac] using uIoc_subset_uIcc hσ) T
  have ht : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hj
      (by simpa using ((shifted_gaussian_top n v).const_mul A).mul_const |c-a|)
  have hbot : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+(-T)*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun T => by simpa only [Complex.ofReal_neg] using hj (-T))
      (by simpa using ((shifted_gaussian_bottom n v).const_mul A).mul_const |c-a|)
  unfold verticalIntegral
  congr 1
  exact Continuation.vertical_integral_eq_of_horizontal_vanish F hac hF
    (hi a ⟨le_rfl,hac⟩) (hi c ⟨hac,le_rfl⟩) hbot ht

theorem principal_box_majorant {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξlo : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξlo : 1/6<ξlo) :
    ∃ A : ℝ,0≤A ∧ ∀σ∈Icc a 3,∀ξ∈Icc ξlo 2,∀p : HeightSpace,
      ‖continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2*I)‖≤A*jointEnvelope 8 p := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hd⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 ξlo 2
    (by linarith) 10
  obtain ⟨E,hE,he⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) 3 3 10
  let A := arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
  let B := realGaussianBound a 3 ξlo 2*2^8*D*E
  have hA : 0≤A := arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
    (by norm_num) hC (by norm_num) (by linarith)
  have hB : 0≤B := by dsimp [B]; have := (realGaussianBound_pos a 3 ξlo 2).le; positivity
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro σ hσ ξ hξ p
  have hξ' : ξ∈Icc (33/200 : ℝ) 2 := ⟨by linarith [hξ.1],hξ.2⟩
  have hw : (2:ℝ)≤‖((3:ℂ)+p.2*I)-1‖ := by
    convert pole_distance_vertical 1 3 p.2 using 1; norm_num
  have hz : 6*ξlo-1≤‖6*((ξ:ℂ)+p.1.2*I)-1‖ := by
    have h := Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)
    have hh : 0≤6*ξ-1 := by linarith [hξ.1]
    simp only [sub_re,mul_re,ofReal_re,ofReal_im,add_re,I_re,I_im,mul_zero,
      zero_mul,sub_zero,add_zero,one_re] at h
    norm_num only [show (6:ℂ).re=6 by norm_num,show (6:ℂ).im=0 by norm_num,zero_mul,sub_zero] at h
    rw [abs_of_nonneg hh] at h
    exact le_trans (by linarith [hξ.1]) h
  have hb := arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a 3 2 3 σ ξ 3 C
    hX hY hZ ha hσ hξ' (by norm_num) (by norm_num) 2 (6*ξlo-1)
    (by norm_num) (by linarith) hC hR p hw hz
  have hp := profile_moment_majorant W0 W1 8 hσ hξ hD.le hE.le (hd ξ hξ)
    (he 3 ⟨le_rfl,le_rfl⟩) p
  rw [←arithmetic_profile_eq_source,norm_mul]
  calc
    _ ≤ (A*jointHeight p.1.1 p.1.2 p.2^8)*‖profile W0 W1
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ 3 p‖) := by
      simp only [onLines,ofReal_ofNat]; ring
    _ ≤ A*(B*jointEnvelope 8 p) := mul_le_mul_of_nonneg_left hp hA
    _ = _ := by ring

theorem continued_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a)
    (hξ : 1/6<ξ) (hξ2 : ξ≤2) (v u : ℝ) :
    verticalIntegral a (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 3 (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  obtain ⟨A,hA,hb⟩ := principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha.le hβ hξ
  have hh := continued_source_differentiable_strip η S hS J T b hT W0 W1 X Y Z hZ
    ((3:ℂ)+u*I) ((ξ:ℂ)+v*I) (by norm_num) (by simpa using (show (4/25:ℝ)≤ξ by linarith)) ha hβ
    (c:=3)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 v ha3
    ((hh.mul_const _).mul_const _) (A:=A*cauchy v*cauchy u)
  intro σ hσ t
  have h := hb σ hσ ξ ⟨le_rfl,hξ2⟩ ((t,v),u)
  simpa only [jointEnvelope,Prod.fst,Prod.snd,mul_assoc,mul_left_comm,mul_comm] using h

lemma continued_source_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s w : ℂ) (hs : 7/8≤s.re) (hw : 9/10≤w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)
      {z : ℂ | 4/25<z.re} := by
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25<z.re} := (ProbeRadialMellin.radial_mellin_differentiable W0).mono
        (by intro z hz; change 0<z.re; change (4/25:ℝ)<z.re at hz; linarith)
  have hH := (combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hnX : (X:ℂ)≠0 := by exact_mod_cast hX.ne'
  have hnZ : (Z:ℂ)≠0 := by exact_mod_cast hZ.ne'
  have he : (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)=
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w*HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s)*
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*
        (globalClosedCorrection η S s w z*slotMultiplier η J T b s w z)) := by
    funext z; unfold continuedSourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hnX | exact Or.inl hnZ)

lemma continued_principal_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s w : ℂ) (hs : 7/8≤s.re) (hw : 9/10≤w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w)
      {z : ℂ | 1/6<z.re} := by
  have hK := continued_source_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s w hs hw
  apply ((hK.mono (by intro z hz; change (4/25:ℝ)<z.re; change (1/6:ℝ)<z.re at hz; linarith)).mul ?_).mul_const
  intro z hz
  have h0 : (6*z:ℂ)≠0 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)<z.re at hz; linarith
  have h1 : (6*z:ℂ)≠1 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)<z.re at hz; linarith
  exact ((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) h0 (Or.inl h1)).comp z
    (differentiableAt_id.const_mul 6)).differentiableWithinAt

theorem continued_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a)
    (hξ : 1/6<ξ) (hξ2 : ξ≤2) (t u : ℝ) :
    verticalIntegral ξ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 2 (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  obtain ⟨A,hA,hb⟩ := principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha hβ hξ
  have hh := continued_principal_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
    ((a:ℂ)+t*I) ((3:ℂ)+u*I) (by simpa using ha) (by norm_num)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 t hξ2
    (hh.mono (by intro z hz; change (1/6:ℝ)<z.re; exact hξ.trans_le hz.1)) (A:=A*cauchy u)
  intro ζ hζ v
  have h := hb a ⟨le_rfl,ha3⟩ ζ hζ ((t,v),u)
  calc
    _ ≤ A*(gaussianMoment 8 (t+v)*cauchy v*cauchy u) := h
    _ ≤ A*(gaussianMoment 8 (t+v)*1*cauchy u) := by
      have hgu := gaussianMoment_nonneg 8 (t+v)
      have hcu := cauchy_nonneg u
      gcongr
      exact cauchy_le_one v
    _ = _ := by rw [add_comm t v]; ring

lemma verticalIntegral_swap (F : ℂ → ℂ → ℂ) (a b : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ => F ((a:ℂ)+q.1*I) ((b:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun z => verticalIntegral b (F z))=
      verticalIntegral b (fun w => verticalIntegral a (fun z => F z w)) := by
  simp only [verticalIntegral,integral_const_mul]
  congr 2
  exact integral_integral_swap (f:=fun t u : ℝ => F ((a:ℂ)+t*I) ((b:ℂ)+u*I)) hi

lemma verticalIntegral_triple_reverse (F : ℂ → ℂ → ℂ → ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace => F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w => F s w z)))=
      verticalIntegral υ (fun w => verticalIntegral ξ (fun z => verticalIntegral a (fun s => F s w z))) := by
  have h1 := integral_prod _ hi
  have h2 := integral_prod _ hi.integral_prod_left
  have h3 := integral_prod_symm _ hi
  have h4 : (∫u : ℝ,∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume)=
      ∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) := by
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu
  have he := h2.symm.trans (h1.symm.trans (h3.trans h4))
  simp only [verticalIntegral,integral_const_mul]
  congr 3

lemma verticalIntegral_congr_line (F G : ℂ → ℂ) (a : ℝ)
    (h : ∀t : ℝ,F ((a:ℂ)+t*I)=G ((a:ℂ)+t*I)) : verticalIntegral a F=verticalIntegral a G := by
  unfold verticalIntegral
  congr 1
  exact integral_congr_ae (Eventually.of_forall h)

theorem continued_triple_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (hξ : 1/6<ξ) (hξ2 : ξ≤2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral 3 (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  have hiA := continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha.le hβ (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  have hi3 := continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 ξ 3 3 hX hY hZ (by norm_num) (hβ.trans_le ha3) (by linarith)
    (by norm_num) (by norm_num) (by linarith) (by norm_num)
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  rw [verticalIntegral_triple_reverse F a ξ 3 hiA,verticalIntegral_triple_reverse F 3 ξ 3 hi3]
  apply verticalIntegral_congr_line
  intro u
  apply verticalIntegral_congr_line
  intro v
  exact continued_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 v u

theorem continued_triple_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (hξ : 1/6<ξ) (hξ2 : ξ≤2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral a (fun s => verticalIntegral 2 (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  obtain ⟨Cξ,Kξ,hCξ,hKξ,hξi⟩ := continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha hβ (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num) 0
  obtain ⟨C2,K2,hC2,hK2,h2i⟩ := continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 3 3 hX hY hZ ha hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  apply verticalIntegral_congr_line
  intro t
  have hiξ := (hξi .s t).1
  have hi2 := (h2i .s t).1
  rw [verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) ξ 3 hiξ,
    verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) 2 3 hi2]
  apply verticalIntegral_congr_line
  intro u
  exact continued_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 t u

lemma continued_triple_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w)))=
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w))) := by
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  have h0 : (a:ℂ)+t*I≠0 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+t*I≠1 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  simp_rw [continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem source_initial_placement {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e≤11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
  dsimp only
  rw [←continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z 3 2 3,
    ←continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z a (1/6+e) 3]
  have hx := continued_triple_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 hX hY hZ ha ha3 hβ (by norm_num) le_rfl
  have hz := continued_triple_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a (1/6+e) hX hY hZ ha.le ha3 hβ (by linarith) (by linarith)
  exact hx.symm.trans hz.symm

theorem source_initial_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e≤11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))+
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z)))+
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  exact (source_initial_placement η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2).trans
    (source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e 3 hX hY hZ ha.le hβ (by norm_num) he)

lemma continued_principal_measurable (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    {ι : Type*} (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (x w z : ℝ×(ℝ×ℝ) → ℂ) (hx : Continuous x) (hw : Continuous w) (hz : Continuous z)
    (hβ : ∀p,HeckeZeroSupremum.beta<(x p).re) (hz0 : ∀p,0<(z p).re) :
    Measurable (fun p => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z (x p) (w p) (z p)*
      LFunction (fixedSourcePrincipal S hS) (6*z p)*LFunction (fixedSourcePrincipal S hS) (w p)) := by
  have hH := global_correction_measurable η S x w z hx.measurable hw.measurable hz.measurable
  have hB := slot_multiplier_measurable η J T b x w z hx.measurable hw.measurable hz.measurable
  have hR : Continuous (fun p => HeckeReciprocal.reciprocal (η.excludePrimes S hS) (x p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (HeckeReciprocal.reciprocal_differentiableAt _ (hβ p)).continuousAt.comp hx.continuousAt
  have hM0 : Continuous (fun p => mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) (z p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (ProbeRadialMellin.radial_mellin_analytic W0 _ (hz0 p)).continuousAt.comp hz.continuousAt
  have hM1 := (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1
    (W1.smooth ⊤)).continuous.comp hw
  have hL6 := (LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p => 6*z p))
  have hLw := (LFunction_measurable (fixedSourcePrincipal S hS)).comp hw.measurable
  have hm0 := hM0.measurable
  have hm1 := hM1.measurable
  have hmr := hR.measurable
  have hmx := hx.measurable
  have hmw := hw.measurable
  have hmz := hz.measurable
  unfold continuedSourceMultiplier
  fun_prop (disch := aesop)

lemma strip_integrable_of_uniform_slices (F : ℝ×(ℝ×ℝ) → ℂ) (l r D : ℝ)
    (hlr : l≤r) (hm : AEStronglyMeasurable F ((volume.restrict (Icc l r)).prod (volume.prod volume)))
    (hs : ∀σ∈Icc l r,Integrable (fun q => F (σ,q)) (volume.prod volume))
    (hb : ∀σ∈Icc l r,(∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume)≤D) :
    Integrable F ((volume.restrict (Icc l r)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc l r)).prod (volume.prod volume))≤(r-l)*D := by
  have hm' := hm.norm.integral_prod_right'
  have hb' : ∀ᵐσ : ℝ ∂volume.restrict (Icc l r),
      ‖∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume‖≤D := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hb σ hσ
  have hi' : Integrable (fun σ : ℝ => ∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume)
      (volume.restrict (Icc l r)) :=
    (integrableOn_const (s:=Icc l r) (C:=D) (hs:=by simp [Real.volume_Icc])).mono' hm' hb'
  have hi : Integrable F ((volume.restrict (Icc l r)).prod (volume.prod volume)) := by
    apply (integrable_prod_iff hm).mpr
    refine ⟨?_,hi'⟩
    filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
    exact hs σ hσ
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi.norm]
  calc
    _ ≤ ∫σ : ℝ in Icc l r,D := integral_mono_ae hi' (integrableOn_const (hs:=by simp [Real.volume_Icc])) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
      exact hb σ hσ)
    _ = _ := by simp [sub_nonneg.mpr hlr,mul_comm]

theorem uniform_high_x_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : 7/8≤a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a)
    (hξlo : 1/6<ξlo) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀ξ∈Icc ξlo 2,∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((p.1:ℂ)+R*I) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.2.1*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc a 3)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc a 3)).prod (volume.prod volume))≤
      (3-a)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 |6*ξ-1| *K/height R^N) := by
  obtain ⟨K,hK,hk⟩ := source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a 3 2 3 ha hβ (by norm_num) N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro ξ hξ R hR
  dsimp only
  let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
    ((p.1:ℂ)+R*I) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
    LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.2.1*I))*
    LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
  have hcut := continued_principal_measurable η S hS.prime J T b W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
    (fun p : ℝ×(ℝ×ℝ) => ((max a p.1:ℝ):ℂ)+R*I)
    (fun p : ℝ×(ℝ×ℝ) => (3:ℂ)+p.2.2*I)
    (fun p : ℝ×(ℝ×ℝ) => (ξ:ℂ)+p.2.1*I) (by fun_prop) (by fun_prop) (by fun_prop)
    (by intro p; simpa using hβ.trans_le (le_max_left a p.1))
    (by intro p; simpa using (show (0:ℝ)<ξ by linarith [hξ.1]))
  have hm : AEStronglyMeasurable F ((volume.restrict (Icc a 3)).prod (volume.prod volume)) := by
    apply hcut.aestronglyMeasurable.congr
    have hh : ∀ᵐp : ℝ×(ℝ×ℝ) ∂(volume.restrict (Icc a 3)).prod (volume.prod volume),p.1∈Icc a 3 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hh] with p hp
    dsimp [F]
    rw [max_eq_right hp.1]
  have hh (σ : ℝ) (hσ : σ∈Icc a 3) := hc σ hσ ξ ⟨by linarith [hξ.1],hξ.2⟩
    3 (by norm_num) .s (by intro _; norm_num) (by intro _; linarith [hξ.1]) R hR
  have hs (σ : ℝ) (hσ : σ∈Icc a 3) : Integrable (fun q => F (σ,q)) (volume.prod volume) := by
    simpa only [F,sliceMap,ofReal_ofNat] using (hh σ hσ).1
  have hb (σ : ℝ) (hσ : σ∈Icc a 3) : (∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume)≤
      arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 |6*ξ-1| *K/height R^N := by
    have ht := (hh σ hσ).2
    norm_num [joinWGap,joinZGap,sliceMap] at ht
    simpa only [F,norm_mul] using ht
  exact strip_integrable_of_uniform_slices F a 3 _ ha3 hm hs hb

theorem uniform_high_z_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : 7/8≤a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a)
    (hξlo : 1/6<ξlo) (hξ2 : ξlo≤2) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((a:ℂ)+p.2.1*I) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((p.1:ℂ)+R*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc ξlo 2)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume))≤
      (2-ξlo)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 6*K/height R^N) := by
  obtain ⟨K,hK,hk⟩ := source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a 3 2 3 ha hβ (by norm_num) N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  dsimp only
  let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
    ((a:ℂ)+p.2.1*I) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
    LFunction (fixedSourcePrincipal S hS.prime) (6*((p.1:ℂ)+R*I))*
    LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
  have hcut := continued_principal_measurable η S hS.prime J T b W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
    (fun p : ℝ×(ℝ×ℝ) => (a:ℂ)+p.2.1*I)
    (fun p : ℝ×(ℝ×ℝ) => (3:ℂ)+p.2.2*I)
    (fun p : ℝ×(ℝ×ℝ) => ((max ξlo p.1:ℝ):ℂ)+R*I) (by fun_prop) (by fun_prop) (by fun_prop)
    (by intro p; simpa using hβ)
    (by intro p; simpa using (show (0:ℝ)<max ξlo p.1 by linarith [le_max_left ξlo p.1]))
  have hm : AEStronglyMeasurable F ((volume.restrict (Icc ξlo 2)).prod (volume.prod volume)) := by
    apply hcut.aestronglyMeasurable.congr
    have hh : ∀ᵐp : ℝ×(ℝ×ℝ) ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume),p.1∈Icc ξlo 2 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hh] with p hp
    dsimp [F]
    rw [max_eq_right hp.1]
  have hh (ξ : ℝ) (hξ : ξ∈Icc ξlo 2) := hc a ⟨le_rfl,ha3⟩ ξ ⟨by linarith [hξ.1],hξ.2⟩
    3 (by norm_num) .z (by intro _; norm_num) (by simp) R hR
  have hs (ξ : ℝ) (hξ : ξ∈Icc ξlo 2) : Integrable (fun q => F (ξ,q)) (volume.prod volume) := by
    simpa only [F,sliceMap,ofReal_ofNat] using (hh ξ hξ).1
  have hb (ξ : ℝ) (hξ : ξ∈Icc ξlo 2) : (∫q : ℝ×ℝ,‖F (ξ,q)‖ ∂volume.prod volume)≤
      arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 6*K/height R^N := by
    have ht := (hh ξ hξ).2
    norm_num [joinWGap,joinZGap,sliceMap] at ht
    simpa only [F,norm_mul] using ht
  exact strip_integrable_of_uniform_slices F ξlo 2 _ hξ2 hm hs hb

lemma high_x_join_ae_raw {ι : Type*} (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ R : ℝ) (hR : R≠0) :
    (fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
      ((p.1:ℂ)+R*I) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.2.1*I))*
      LFunction (fixedSourcePrincipal S hS) ((3:ℂ)+p.2.2*I))
      =ᵐ[(volume.restrict (Icc a 3)).prod (volume.prod volume)]
    (fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) ((p.1:ℂ)+R*I)
      (globalClosedCorrection η S ((p.1:ℂ)+R*I)) (slotMultiplier η J T b ((p.1:ℂ)+R*I))
      ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.2.1*I))*
      LFunction (fixedSourcePrincipal S hS) ((3:ℂ)+p.2.2*I)) := by
  apply Eventually.of_forall
  intro p
  have h0 : (p.1:ℂ)+R*I≠0 := by intro h; exact hR (by simpa using congrArg Complex.im h)
  have h1 : (p.1:ℂ)+R*I≠1 := by intro h; exact hR (by simpa using congrArg Complex.im h)
  dsimp only
  rw [continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

lemma high_z_join_ae_raw {ι : Type*} (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξlo R : ℝ) :
    (fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
      ((a:ℂ)+p.2.1*I) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
      LFunction (fixedSourcePrincipal S hS) (6*((p.1:ℂ)+R*I))*
      LFunction (fixedSourcePrincipal S hS) ((3:ℂ)+p.2.2*I))
      =ᵐ[(volume.restrict (Icc ξlo 2)).prod (volume.prod volume)]
    (fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) ((a:ℂ)+p.2.1*I)
      (globalClosedCorrection η S ((a:ℂ)+p.2.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.2.1*I))
      ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
      LFunction (fixedSourcePrincipal S hS) (6*((p.1:ℂ)+R*I))*
      LFunction (fixedSourcePrincipal S hS) ((3:ℂ)+p.2.2*I)) := by
  have hh : ∀ᵐp : ℝ×(ℝ×ℝ) ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume),p.2.1≠0 :=
    Measure.quasiMeasurePreserving_snd.ae
      (Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ)))
  filter_upwards [hh] with p hp
  have h0 : (a:ℂ)+p.2.1*I≠0 := by intro h; exact hp (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+p.2.1*I≠1 := by intro h; exact hp (by simpa using congrArg Complex.im h)
  rw [continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem raw_uniform_high_x_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : 7/8≤a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a)
    (hξlo : 1/6<ξlo) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀ξ∈Icc ξlo 2,∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((p.1:ℂ)+R*I)
        (globalClosedCorrection η S ((p.1:ℂ)+R*I)) (slotMultiplier η J T b ((p.1:ℂ)+R*I)) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.2.1*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc a 3)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc a 3)).prod (volume.prod volume))≤
      (3-a)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 |6*ξ-1| *K/height R^N) := by
  obtain ⟨K,hK,hk⟩ := uniform_high_x_joins W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a ξlo ha ha3 hβ hξlo N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro ξ hξ R hR
  have hh := hc ξ hξ R hR
  have heq := high_x_join_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ R
    (by intro h; norm_num [h] at hR)
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

theorem raw_uniform_high_z_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : 7/8≤a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a)
    (hξlo : 1/6<ξlo) (hξ2 : ξlo≤2) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.2.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.2.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.2.1*I)) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((p.1:ℂ)+R*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc ξlo 2)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume))≤
      (2-ξlo)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 6*K/height R^N) := by
  obtain ⟨K,hK,hk⟩ := uniform_high_z_joins W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a ξlo ha ha3 hβ hξlo hξ2 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  have hh := hc R hR
  have heq := high_z_join_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξlo R
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

theorem source_initial_joint_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e≤11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (((1/(2*Real.pi):ℝ):ℂ)^3)*(∫p : HeightSpace,
      K ((3:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((2:ℂ)+p.1.2*I)*
        LFunction π (6*((2:ℂ)+p.1.2*I))*LFunction π ((3:ℂ)+p.2*I) ∂heightMeasure)=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))+
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z)))+
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  have hh := source_initial_ordered_at_a η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2
  have hf := (source_joint_fubini η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 2 3 3 hX hY hZ (by norm_num) (hβ.trans_le ha3) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  have hi : (((1/(2*Real.pi):ℝ):ℂ)^3)*(∫p : HeightSpace,
      K ((3:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((2:ℂ)+p.1.2*I)*
        LFunction π (6*((2:ℂ)+p.1.2*I))*LFunction π ((3:ℂ)+p.2*I) ∂heightMeasure)=
      verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
        (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
    dsimp [K,π]
    simp only [ofReal_ofNat] at hf
    rw [hf]
    simp only [verticalIntegral,integral_const_mul,ofReal_ofNat]
    ring
  exact hi.trans hh

end SevenEighths.ProbePrincipalTransport
end

end OAI

end Source1802

/- Original source: OAI/NumberTheory/DirichletL/Detector/PrincipalPhysical.lean; sha256: 4949ca006c113bf0aaa35143561f9d8d9ef9ee8905a0041c40ecc30f5e3180c2 -/
section Source1803
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds CanonicalQuadraticSieve
open PrincipalMellinResidues ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal HeckeFamily.O

lemma slotMultiplier_as_tuples {K : ℕ} (η : Character) (T : Fin K→Finset PrimeIdeal)
    (b : Fin K→PrimeIdeal→ℂ) (s w z : ℂ) :
    slotMultiplier η Finset.univ T b s w z=
      ∑P : (∀i,T i),(∏i,b i (P i).val)*
        slotMultiplier η Finset.univ (fun i=>{(P i).val}) (fun _ _=>1) s w z := by
  simp only [slotMultiplier,Finset.sum_singleton,one_mul]
  simp_rw [←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun i (p : T i)=>b i p.val*localMultiplier η p.val s w z)]
  congr 1
  funext i
  exact (Finset.sum_coe_sort (T i) (fun p=>b i p*localMultiplier η p s w z)).symm

def principalPoolKernel {K : ℕ} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset PrimeIdeal) (b : Fin K→PrimeIdeal→ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) : ℂ :=
  sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s) w z *
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w

lemma principalPoolKernel_as_tuples {K : ℕ} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset PrimeIdeal) (b : Fin K→PrimeIdeal→ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    principalPoolKernel η S hS T b W0 W1 X Y Z s w z=
      ∑P : (∀i,T i),(∏i,b i (P i).val)*
        principalPoolKernel η S hS (fun i=>{(P i).val}) (fun _ _=>1) W0 W1 X Y Z s w z := by
  unfold principalPoolKernel sourceMultiplier
  rw [slotMultiplier_as_tuples]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P hP
  ring

theorem principal_physical_pool_initial {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
        principalPoolKernel η S hS T b W0 W1 X Y Z
          ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I) ∂heightMeasure := by
  let F (P : ∀i,T i) (t : HeightSpace) :=
    principalPoolKernel η S hS (fun i=>{(P i).val}) (fun _ _=>1) W0 W1 X Y Z
      ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I)
  have hF (P : ∀i,T i) : Integrable (F P) heightMeasure := by
    apply source_joint_integrable η S hS Finset.univ (fun i=>{(P i).val}) (fun _ _=>1)
      (by intro i hi p hp;simp only [Finset.mem_singleton] at hp;subst p;exact hT i _ (P i).property)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z 3 2 3 3 hX hY hZ
      (by norm_num) (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp_rw [principalPoolKernel_as_tuples η S hS T b W0 W1 X Y Z]
  rw [integral_finsetSum Finset.univ (fun P _=>(hF P).const_mul (∏i,b i (P i).val)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [principalRowIntegral_eq_sourceMultiplier η S hS (fun i=>(P i).val) (hdis P)
    (fun i=>hT i _ (P i).property) W0 W1 X Y Z,integral_const_mul]
  dsimp only [F,principalPoolKernel]
  ring

theorem principal_physical_pool_ordered {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e≤11/6) :
    let F := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => F s w z*LFunction π (6*z)*LFunction π w)))+
      R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => F s 1 z*LFunction π (6*z)))+
      R^2/6*verticalIntegral a (fun s => F s 1 (1/6)) := by
  dsimp only
  rw [principal_physical_pool_initial η S hS T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact ProbePrincipalTransport.source_initial_joint_ordered_at_a η S hS Finset.univ T b
    (fun i _ p hp=>hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2

lemma finitePhysicalRows_principal {K : ℕ} (S : Finset Id) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset PrimeIdeal) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    ProbeHighRowFamily.finitePhysicalRows S hmax η {principalFreeRow} T W Yp W0 W1 X Y Z=
      ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z := by
  simp only [ProbeHighRowFamily.finitePhysicalRows,Finset.sum_singleton,rowIntegral_principal]

theorem compensatedPhysicalProbe_principal_pool_split {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
      (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      ProbeHighRowFamily.finitePhysicalRows S hmax η {principalFreeRow} T W Yp W0 W1 X Y Z+
      ∑'u : HeckeInverseAmplification.FreeRow,if u=principalFreeRow then 0 else
        ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
          rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u := by
  have hSne : S.Nonempty := (by simp [fixedBadPrimes] : fixedBadPrimes.Nonempty).mono hS.bad
  rw [compensatedPhysicalProbe_eq_canonical_rows η S hmax hS.prime hS.bad hSne T hT W Yp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  have hs (P : ∀i,T i) : Summable (fun u : HeckeInverseAmplification.FreeRow=>
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) :=
    (rowIntegral_summable η S _ _ (fun i=>supported_primaryGenerator_ne_zero _ (hT i _ (P i).property))
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).mul_left _
  rw [(summable_sum (s:=Finset.univ) (fun P _=>hs P)).tsum_eq_add_tsum_ite principalFreeRow]
  simp only [ProbeHighRowFamily.finitePhysicalRows,Finset.sum_singleton]

end SevenEighths.ProbePrincipalPhysical
end

end OAI

end Source1803

/- Original source: OAI/NumberTheory/DirichletL/Detector/PrincipalRemainderBounds.lean; sha256: de3b03a6fc50f24fe83e865fe2c6895c9d2900e1989ed611cc1780465102424f -/
section Source1804
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalRemainderBounds
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma active_prime_sum_bound (T : Finset PrimeIdeal) (W : ℝ→ℝ)
    (c d B P ξ : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hP : 0<P)
    (hthreshold : 480≤c*P) (hξ : ξ≤1)
    (hW : ∀x,0≤W x ∧ W x≤B) (hsupp : Function.support W⊆Icc c d) :
    (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))
      ≤(128*d*B*c^(ξ-1))*P^ξ := by
  let A := T.filter (fun p=>W ((Ideal.absNorm p.val:ℝ)/P)≠0)
  have hA (p : PrimeIdeal) (hp : p∈A) :
      c*P≤(Ideal.absNorm p.val:ℝ) ∧ (Ideal.absNorm p.val:ℝ)≤d*P := by
    have h := hsupp (Finset.mem_filter.mp hp).2
    exact ⟨(le_div_iff₀ hP).mp h.1,(div_le_iff₀ hP).mp h.2⟩
  have he : (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))=
      ∑p∈A,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hw : W ((Ideal.absNorm p.val:ℝ)/P)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hp,hh⟩)
    simp [hw]
  have hcount : (A.card:ℝ)≤128*(d*P) := by
    have h := DescentFiberCost.finite_ideal_count_real (A.image Subtype.val) (d*P)
      (by nlinarith) (by
        intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact p.property.ne_zero)
      (by intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact (hA p hp).2)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using h
  have hp (p : PrimeIdeal) (hp : p∈A) : (Ideal.absNorm p.val:ℝ)^(ξ-1)≤c^(ξ-1)*P^(ξ-1) := by
    rw [←Real.mul_rpow hc.le hP.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hc hP) (hA p hp).1 (by linarith)
  rw [he]
  calc
    _≤∑_p∈A,B*(c^(ξ-1)*P^(ξ-1)) := Finset.sum_le_sum (fun p hpA=>
      mul_le_mul (hW _).2 (hp p hpA) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hB)
    _=(A.card:ℝ)*(B*(c^(ξ-1)*P^(ξ-1))) := by simp
    _≤(128*(d*P))*(B*(c^(ξ-1)*P^(ξ-1))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _=(128*d*B*c^(ξ-1))*P^ξ := by
      have heP : P*P^(ξ-1)=P^ξ := by
        calc
          _=P^(1:ℝ)*P^(ξ-1) := by rw [Real.rpow_one]
          _=P^ξ := by rw [←Real.rpow_add hP];congr 1;ring
      calc
        _=(128*d*B*c^(ξ-1))*(P*P^(ξ-1)) := by ring
        _=_ := by rw [heP]

def slotConstant {ι : Type*} (J : Finset ι) (c d B ξ : ℝ) : ℝ :=
  (3/2)*∏_j∈J,(1+1440*(480:ℝ)^(-(7/8:ℝ)))*(128*d*B*c^(ξ-1))

lemma slotConstant_nonneg {ι : Type*} (J : Finset ι) {c d B ξ : ℝ}
    (hc : 0<c) (hd : c≤d) (hB : 0≤B) : 0≤slotConstant J c d B ξ := by
  have hd0 : 0≤d := hc.le.trans hd
  unfold slotConstant
  apply mul_nonneg (by norm_num)
  exact Finset.prod_nonneg (fun _ _=>by positivity)

theorem window_sharp_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hξ : ξ≤1)
    (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤W j x ∧ W j x≤B)
    (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
    (P : ι→ℝ) (hP : ∀j∈J,0<P j)
    (hthreshold : ∀j∈J,480≤c*P j)
    (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j)
    (T : ι→Finset PrimeIdeal) (s w z : ℂ)
    (hs : 7/8≤s.re) (hw : 19/20≤w.re) (hz : z.re=ξ) (hzlo : 33/200≤ξ) :
    ‖globalClosedCorrection η S s w z *
      windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z‖≤
      slotConstant J c d B ξ * ∏j∈J,(P j)^ξ := by
  let A (j : ι) := (T j).filter (fun p=>W j ((Ideal.absNorm p.val:ℝ)/P j)≠0)
  have hA (j : ι) (hj : j∈J) (p : PrimeIdeal) (hp : p∈A j) : c*P j≤(Ideal.absNorm p.val:ℝ) :=
    (le_div_iff₀ (hP j hj)).mp ((hsupp j hj) (Finset.mem_filter.mp hp).2).1
  have he : windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z =
      slotMultiplier η J A (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) s w z := by
    unfold windowMultiplier slotMultiplier
    apply Finset.prod_congr rfl
    intro j hj
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hh : W j ((Ideal.absNorm p.val:ℝ)/P j)=0 := by
      by_contra h; exact hn (Finset.mem_filter.mpr ⟨hp,h⟩)
    simp [hh]
  rw [he]
  have h := combined_slot_bound_sharp η S hS J A
    (fun j p=>W j ((Ideal.absNorm p.val:ℝ)/P j)) 480 (by norm_num)
    (fun j hj p _=>(hW j hj _).1)
    (fun j hj p hp=>(hthreshold j hj).trans (hA j hj p hp))
    (fun j hj p hp=>PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero
      (PrincipalSignalComparison.prime_coprime_of_norm_gt η p (by
        exact_mod_cast (hmod j hj).trans_le (hA j hj p hp)))) s w z hs hw (by rw [hz];exact hzlo)
  apply h.trans
  simp only [hz]
  calc
    _≤(3/2)*∏j∈J,(1+1440*(480:ℝ)^(-(7/8:ℝ)))*((128*d*B*c^(ξ-1))*(P j)^ξ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.prod_le_prod₀
      · intro j hj; apply mul_nonneg (by positivity);exact Finset.sum_nonneg (fun p _=>by
          exact mul_nonneg (hW j hj _).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · intro j hj
        exact mul_le_mul_of_nonneg_left (active_prime_sum_bound (A j) (W j) c d B (P j) ξ
          hc hd hB (hP j hj) (hthreshold j hj) hξ (hW j hj) (hsupp j hj)) (by positivity)
    _=_ := by simp only [slotConstant,←mul_assoc,Finset.prod_mul_distrib]

def scalePower (X Y Z a ξ υ : ℝ) : ℝ :=
  X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)

lemma scalePower_nonneg {X Y Z a ξ υ : ℝ} (hX : 0≤X) (hY : 0≤Y) (hZ : 0≤Z) :
    0≤scalePower X Y Z a ξ υ := by unfold scalePower;positivity

section Pointwise
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B ξ : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hξ : ξ≤1)
  (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤W j x ∧ W j x≤B)
  (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
  (P : ι→ℝ) (hP : ∀j∈J,0<P j) (hthreshold : ∀j∈J,480≤c*P j)
  (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) (T : ι→Finset PrimeIdeal)
  (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
  (ha : 7/8≤a) (hυ : 19/20≤υ) (hzlo : 33/200≤ξ) (hC : 0≤C)
  (hR : ∀s : ℂ,a≤s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤C*(1+|s.im|^2))

include hc hd hB hξ hW hsupp hP hthreshold hmod hX hY hZ ha hυ hzlo hC hR

lemma continued_source_sharp_pointwise (t v u : ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)‖ ≤
    scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight t v u^2*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
  have hslot := window_sharp_bound η S hS.tail J c d B ξ hc hd hB hξ W hW hsupp
    P hP hthreshold hmod T ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)
    (by simpa using ha) (by simpa using hυ) (by simp) hzlo
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)‖≤C*jointHeight t v u^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    have hh := height_le_joint_s t v u
    have hh0 := height_pos t
    unfold height jointHeight at *
    nlinarith [abs_nonneg t,abs_nonneg v,abs_nonneg u]
  have hx : ‖(X:ℂ)^(1/2-((ξ:ℂ)+v*I))‖=X^(1/2-ξ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX];congr 1;simp
  have hz : ‖(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)‖=Z^(a+ξ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ];congr 1;simp
  have hy : ‖(Y:ℂ)^(((υ:ℂ)+u*I)-1)‖=Y^(υ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY];congr 1;simp
  have he : continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) =
      (X:ℂ)^(1/2-((ξ:ℂ)+v*I))*(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)*
      (Y:ℂ)^(((υ:ℂ)+u*I)-1)*HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)*
      (globalClosedCorrection η S ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)*
        windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I))*
      onLines W0 W1 a ξ υ ((t,v),u) := by
    unfold continuedSourceMultiplier windowMultiplier onLines profile;ring
  rw [he,norm_mul,norm_mul,norm_mul,norm_mul,norm_mul,hx,hz,hy]
  calc
    _≤X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)*(C*jointHeight t v u^2)*
      (slotConstant J c d B ξ*(∏j∈J,(P j)^ξ))*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
      gcongr
    _=_ := by unfold scalePower;ring

lemma full_sharp_pointwise (hυhi : υ≤2) (hυ1 : υ≠1) (hξ1 : 6*ξ≠1) (p : HeightSpace) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ≤
    (C*slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*
      (wAmplitude (∏q∈S,q) 2/|υ-1|)) *
      (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))*
      (jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a υ C hX hY hZ ha hυ hzlo hC hR p.1.1 p.1.2 p.2
  have hlz := fixed_principal_z_bound (∏q∈S,q) 1 ξ p.1.2 ⟨hzlo,hξ⟩ hξ1
  have hlw := fixed_principal_w_bound (∏q∈S,q) (by norm_num : (1:ℝ)<2) ⟨hυ,hυhi⟩ hυ1 p.2
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏q∈S,q) 1) (abs_nonneg (6*ξ-1))
  have hAW := div_nonneg (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le (abs_nonneg (υ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
  have ht := (height_pos p.1.1).le
  have hv := (height_pos p.1.2).le
  have hu := (height_pos p.2).le
  have hj := (jointHeight_pos p.1.1 p.1.2 p.2).le
  rw [norm_mul,norm_mul]
  calc
    _≤(scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*height p.1.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*height p.2^3) := by
      gcongr <;> first | positivity | exact h0 | exact hlz | exact hlw
    _≤(scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*jointHeight p.1.1 p.1.2 p.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*jointHeight p.1.1 p.1.2 p.2^3) := by
      have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
      gcongr <;> first | positivity | exact height_le_joint_z _ _ _ | exact height_le_joint_w _ _ _
    _=_ := by ring

omit hυ in
lemma residue_sharp_pointwise (hξ1 : 6*ξ≠1) (q : ℝ×ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ≤
    (C*slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)) *
      (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ))*
      (jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a 1 C hX hY hZ ha (by norm_num) hzlo hC hR q.1 q.2 0
  simp only [ofReal_one,ofReal_zero,zero_mul,add_zero] at h0
  have hlz := fixed_principal_z_bound (∏p∈S,p) 1 ξ q.2 ⟨hzlo,hξ⟩ hξ1
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏p∈S,p) 1) (abs_nonneg (6*ξ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=1) hX.le hY.le hZ.le
  have hv := (height_pos q.2).le
  rw [norm_mul]
  calc
    _≤(scalePower X Y Z a ξ 1*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*height q.2^3) := by
      gcongr ; first | positivity | exact h0 | exact hlz
    _≤(scalePower X Y Z a ξ 1*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr ; first | positivity | exact height_le_joint_z _ _ _
    _=_ := by ring
end Pointwise

lemma vertical_triple_eq_joint (F : ℂ→ℂ→ℂ→ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace=>F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s=>verticalIntegral ξ (fun z=>verticalIntegral υ (fun w=>F s w z))) =
    (((1/(2*Real.pi):ℝ):ℂ))^3*
      ∫p : HeightSpace,F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) ∂heightMeasure := by
  rw [integral_prod _ hi,integral_prod _ hi.integral_prod_left]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma vertical_pair_eq_joint (F : ℂ→ℂ→ℂ) (a ξ : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ=>F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun s=>verticalIntegral ξ (fun z=>F s z)) =
    (((1/(2*Real.pi):ℝ):ℂ))^2*
      ∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume := by
  rw [integral_prod _ hi]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma normalizer_norm_pos : 0<‖(((1/(2*Real.pi):ℝ):ℂ))‖ := by
  apply norm_pos_iff.mpr
  exact_mod_cast (one_div_ne_zero (mul_ne_zero (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero))

section Uniform
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
  (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
  (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
  (a ξ : ℝ) (ha : a∈Icc (7/8:ℝ) 2) (hβ : HeckeZeroSupremum.beta<a)
  (hξ : ξ∈Icc (33/200:ℝ) 1) (hξ1 : 6*ξ≠1)
include hc hd hB ha0 ha1 hW0 hW1 ha hβ hξ hξ1

theorem full_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480≤c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
    Integrable F heightMeasure ∧
      (∫p,‖F p‖ ∂heightMeasure)≤K/(|6*ξ-1| *|υ-1|)*
        (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (7/8) 2 (33/200) 1 (19/20) 2 (by norm_num) 8
  let K := C*slotConstant J c d B ξ*zBoxAmplitude (∏q∈S,q) 1*wAmplitude (∏q∈S,q) 2*D
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := zBoxAmplitude_nonneg (∏q∈S,q) 1
  have hWA := (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le
  have hK : 0≤K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ 2 hX hY hZ ha.1 hβ hξ.1 (by norm_num) hυ hξ1 hυ1
  have hae := continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ
  have hae' := (hae.mul (EventuallyEq.rfl (f:=fun p : HeightSpace=>
    LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))))).mul
    (EventuallyEq.rfl (f:=fun p : HeightSpace=>LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)))
  refine ⟨hi.congr hae',?_⟩
  refine (integral_congr_ae (hae'.fun_comp norm)).symm.le.trans ?_
  let A := C*slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*(wAmplitude (∏q∈S,q) 2/|υ-1|)
  let E := scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)
  have hA : 0≤A := by dsimp [A];positivity
  have hE : 0≤E := mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ υ hυ
  calc
    _≤∫p : HeightSpace,A*E*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) ∂heightMeasure := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro p
      exact full_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a υ C hX hY hZ ha.1 hυ.1 hξ.1 hC hR hυ.2 hυ1 hξ1 p
    _=A*E*(∫p : HeightSpace,jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖ ∂heightMeasure) := integral_const_mul _ _
    _≤A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/(|6*ξ-1| *|υ-1|)*E := by dsimp [A,K];simp only [div_eq_mul_inv,mul_inv_rev];ring
    _≤(K+1)/(|6*ξ-1| *|υ-1|)*E := by gcongr;linarith

theorem residue_scale_bound :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480≤c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let F := fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
        (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
    Integrable F (volume.prod volume) ∧
      (∫q,‖F q‖ ∂volume.prod volume)≤K/|6*ξ-1| *
        (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (7/8) 2 (33/200) 1 1 1 (by norm_num) 5 0
  let K := C*slotConstant J c d B ξ*zBoxAmplitude (∏p∈S,p) 1*D
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := zBoxAmplitude_nonneg (∏p∈S,p) 1
  have hK : 0≤K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha.1 hβ hξ.1 hξ1
  have hae : (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) =ᵐ[volume.prod volume]
    (fun q : ℝ×ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I))
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I)) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) := by
    have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    filter_upwards [hh] with q hq
    have h0 : (a:ℂ)+q.1*I≠0 := by intro h;exact hq (by simpa using congrArg Complex.im h)
    have h1 : (a:ℂ)+q.1*I≠1 := by intro h;exact hq (by simpa using congrArg Complex.im h)
    rw [continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
    rfl
  refine ⟨hi.congr hae,?_⟩
  refine (integral_congr_ae (hae.fun_comp norm)).symm.le.trans ?_
  let A := C*slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)
  let E := scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)
  have hA : 0≤A := by dsimp [A];positivity
  have hE : 0≤E := mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ 1 ⟨le_rfl,le_rfl⟩ .w 0
  simp only [sliceMap,pow_zero,div_one] at hp
  calc
    _≤∫q : ℝ×ℝ,A*E*(jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) ∂volume.prod volume := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro q
      exact residue_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a C hX hY hZ ha.1 hξ.1 hC hR hξ1 q
    _=A*E*(∫q : ℝ×ℝ,jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖ ∂volume.prod volume) := integral_const_mul _ _
    _≤A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/|6*ξ-1| *E := by dsimp [A,K];ring
    _≤(K+1)/|6*ξ-1| *E := by gcongr;linarith

theorem full_vertical_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480≤c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let K0 := fun s=>sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖verticalIntegral a (fun s=>verticalIntegral ξ (fun z=>verticalIntegral υ
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      K/(|6*ξ-1| *|υ-1|)*(scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := full_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 υ hυ hυ1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^3
  have hk : 0<k := pow_pos normalizer_norm_pos _
  refine ⟨k*K,mul_pos hk hK,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [vertical_triple_eq_joint _ a ξ υ hh.1,norm_mul,norm_pow]
  calc
    _≤k*(∫p : HeightSpace,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le
    _≤k*(K/(|6*ξ-1| *|υ-1|)*(scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))) :=
      mul_le_mul_of_nonneg_left hh.2 hk.le
    _=_ := by ring

theorem residue_vertical_scale_bound :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480≤c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let K0 := fun s=>sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral ξ
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤
      K/|6*ξ-1| *(scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := residue_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1
  let R := HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^2
  have hk : 0<k := pow_pos normalizer_norm_pos _
  refine ⟨(1+‖R‖)*k*K,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [vertical_pair_eq_joint _ a ξ hh.1,norm_mul,norm_mul,norm_pow]
  calc
    _≤(1+‖R‖)*(k*(∫q : ℝ×ℝ,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ∂volume.prod volume)) := by
      apply mul_le_mul (by dsimp [R];linarith [norm_nonneg (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)])
        (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le) (by positivity) (by positivity)
    _≤(1+‖R‖)*(k*(K/|6*ξ-1| *(scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)))) := by
      gcongr;exact hh.2
    _=_ := by ring
end Uniform

theorem ordered_remainders_scale_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (7/8:ℝ) 2) (hβ : HeckeZeroSupremum.beta<a)
    (he : 0<e) (hehi : e≤5/6) :
    ∃C : ℝ,0<C ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480≤c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let K0 := fun s=>sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=>verticalIntegral (1/6+e) (fun z=>verticalIntegral (19/20)
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*(scalePower X Y Z a (1/6+e) (19/20)*(∏j∈J,(P j)^(1/6+e)))) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral (33/200)
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤
      C*(scalePower X Y Z a (33/200) 1*(∏j∈J,(P j)^(33/200:ℝ)))) := by
  obtain ⟨A,hA,hfirst⟩ := full_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (1/6+e) ha hβ ⟨by linarith,by linarith⟩ (by linarith)
    (19/20) (by norm_num) (by norm_num)
  obtain ⟨D,hD,hsecond⟩ := residue_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (33/200) ha hβ (by norm_num) (by norm_num)
  refine ⟨(10/3)*A+100*D,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hf := hfirst W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  have hg := hsecond W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hf hg
  have hegap : |6*((1/6:ℝ)+e)-1|=6*e := by rw [abs_of_pos (by linarith)];ring
  rw [hegap] at hf
  norm_num only [show |(19/20:ℝ)-1|=1/20 by norm_num] at hf
  norm_num only [show |6*(33/200:ℝ)-1|=1/100 by norm_num] at hg
  have hm (ξ : ℝ) : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  constructor
  · apply hf.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    have heq : A/(6*e*(1/20))=((10/3)*A)/e := by field_simp;ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ he.le
    nlinarith
  · apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    norm_num
    linarith

lemma source_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=1/6) (Z a ξ υ : ℝ) (hZ : 0<Z) :
    scalePower (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a ξ υ *
      (∏j∈J,(Z^(ell j))^ξ) =
    Z^(a-11/16+(13/16)*(ξ-1/6)+(23/48)*(υ-1)) := by
  have hp : (∏j∈J,(Z^(ell j))^ξ)=Z^((1/6)*ξ) := by
    simp only [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul,hell]
  rw [hp,scalePower,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma source_w_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=1/6) (Z a e : ℝ) (hZ : 0<Z) :
    scalePower (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a (1/6+e) (19/20) *
      (∏j∈J,(Z^(ell j))^(1/6+e)) = Z^(a-11/16+(13/16)*e-23/960) := by
  rw [source_scale_identity J ell hell Z a (1/6+e) (19/20) hZ]
  congr 1;ring

lemma source_z_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=1/6) (Z a : ℝ) (hZ : 0<Z) :
    scalePower (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a (33/200) 1 *
      (∏j∈J,(Z^(ell j))^(33/200:ℝ)) = Z^(a-11/16-13/9600) := by
  rw [source_scale_identity J ell hell Z a (33/200) 1 hZ]
  congr 1;ring

lemma eventual_annulus_threshold {ι : Type*} (η : Character) (J : Finset ι)
    (c : ℝ) (hc : 0<c) (ell : ι→ℝ) (hell : ∀j∈J,0<ell j) :
    ∃Z0 : ℝ,1≤Z0 ∧ ∀Z : ℝ,Z0≤Z→∀j∈J,
      480≤c*Z^(ell j) ∧ (Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j) := by
  have hh : ∀ᶠZ : ℝ in atTop,∀j∈J,
      480≤c*Z^(ell j) ∧ (Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j) := by
    apply (Filter.eventually_all_finset J).mpr
    intro j hj
    have ht := (tendsto_rpow_atTop (hell j hj)).const_mul_atTop hc
    exact (ht.eventually (eventually_ge_atTop 480)).and
      (ht.eventually (eventually_gt_atTop (Ideal.absNorm η.modulus:ℝ)))
  obtain ⟨Z0,hZ0⟩ := eventually_atTop.mp hh
  refine ⟨max 1 Z0,le_max_left _ _,?_⟩
  intro Z hZ
  exact hZ0 Z ((le_max_right _ _).trans hZ)

theorem source_remainders_power_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (7/8:ℝ) 2) (hβ : HeckeZeroSupremum.beta<a)
    (he : 0<e) (hehi : e≤5/6) :
    ∃C : ℝ,0<C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=1/6) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,0<Z→
    (∀j∈J,480≤c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    let K0 := fun s=>sourceMultiplier W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=>verticalIntegral (1/6+e) (fun z=>verticalIntegral (19/20)
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(a-11/16+(13/16)*e-23/960)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral (33/200)
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤C*Z^(a-11/16-13/9600)) := by
  obtain ⟨C,hC,hbound⟩ := ordered_remainders_scale_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a e ha hβ he hehi
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound W hW hsupp (fun j=>Z^(ell j)) (fun _ _=>Real.rpow_pos_of_pos hZ _)
    hthreshold hmod T hT (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ
  dsimp only at hh
  rw [source_w_scale_identity J ell hell Z a e hZ,source_z_scale_identity J ell hell Z a hZ] at hh
  exact hh

lemma source_w_strict_exponent (β e : ℝ) (he : e≤1/1000) :
    (β+e)-11/16+(13/16)*e-23/960≤β-11/16-17/48000 := by linarith

lemma source_z_strict_exponent (β e : ℝ) (he : e≤1/1000) :
    (β+e)-11/16-13/9600≤β-11/16-17/48000 := by linarith

theorem source_remainders_strict_saving {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e≤1/1000)
    (ha : HeckeZeroSupremum.beta+e∈Icc (7/8:ℝ) 2) :
    ∃C : ℝ,0<C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=1/6) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,1≤Z→
    (∀j∈J,480≤c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    let K0 := fun s=>sourceMultiplier W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=>verticalIntegral (1/6+e)
      (fun z=>verticalIntegral (19/20) (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral (HeckeZeroSupremum.beta+e)
      (fun s=>verticalIntegral (33/200) (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤
      C*Z^(HeckeZeroSupremum.beta-11/16-17/48000)) := by
  obtain ⟨C,hC,hbound⟩ := source_remainders_power_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta+e) e ha (by linarith) he (by linarith)
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound ell hell W hW hsupp T hT Z (by linarith) hthreshold hmod
  dsimp only at hh
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_w_strict_exponent HeckeZeroSupremum.beta e hehi))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_z_strict_exponent HeckeZeroSupremum.beta e hehi)) hC.le)

end SevenEighths.ProbePrincipalRemainderBounds

end

end OAI

end Source1804

/- Original source: OAI/NumberTheory/DirichletL/Detector/PrincipalPhysicalRemainder.lean; sha256: 0082454b3750c828a2b43fd72a631d790f3e323f336cf3596fa74525801cb922 -/
section Source1805
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal HeckeFamily.O

theorem physical_principal_residue_remainder {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e≤1/1000)
    (ha : 7/8<HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ell : Fin K→ℝ,(∑j,ell j)=1/6 → ∀W : Fin K→ℝ→ℝ,
    (∀j x,0≤W j x ∧ W j x≤B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1≤Z → (∀j,480≤c*Z^(ell j)) → (∀j,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)-
      sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta+e) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := ProbePrincipalRemainderBounds.source_remainders_strict_saving η S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le,ha2⟩
  refine ⟨2*C,by positivity,?_⟩
  intro ell hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0<Z := by linarith
  have hb := hbound ell hell W (fun j _=>hW j) (fun j _=>hsupp j) T (fun j _ p hp=>hT j p hp)
    Z hZ (fun j _=>hthreshold j) (fun j _=>hmod j)
  dsimp only at hb
  have heq := principal_physical_pool_ordered η S hS T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(ell j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith) (by linarith) he (by linarith)
  dsimp only at heq
  have hres (F : ℂ→ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6*
        verticalIntegral (HeckeZeroSupremum.beta+e) F=
      verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=>fixedPrincipalResidue (∏p∈S,p)^2/6*F s) := by
    rw [verticalIntegral,verticalIntegral,integral_const_mul]
    dsimp only [fixedPrincipalResidue,fixedPrincipal,fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres,add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _≤(2*C)/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000)
  apply hn.trans
  have hCe : C≤C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0≤Z^(HeckeZeroSupremum.beta-11/16-17/48000) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring
  rw [htwo]
  nlinarith
end SevenEighths.ProbePrincipalPhysical
end

end OAI

end Source1805

/- Original source: OAI/NumberTheory/DirichletL/Detector/RayPoolThresholds.lean; sha256: 0411f3084260288d0de442bb3f9cf17c55c90ea44e1506f0a5877ddbb8f9fe4d -/
section Source1806
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PrincipalSignalComparison ProbePrincipalResidueActual
local notation "Id" => Ideal HeckeFamily.O

theorem power_pool_thresholds {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (η : Character) (c d ellMin : ℝ)
    (hc : 0<c) (hd : c≤d) (hmin : 0<ellMin)
    (ell : ι→ℝ) (hell : ∀j,ellMin≤ell j) :
    ∀ᶠZ : ℝ in atTop,
      1≤Z ∧ 480≤c*Z^ellMin ∧ 1440*(c*Z^ellMin)^(-(7/8:ℝ))≤1 ∧
      (∀j,480≤c*Z^(ell j) ∧ (η.modulus.absNorm:ℝ)<c*Z^(ell j)) ∧
      (∀j,∀P∈pool C S c d (Z^(ell j)),
        c*Z^ellMin≤(P.val.absNorm:ℝ) ∧ IsCoprime P.val η.modulus ∧ P.val∉S) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop hc
  have hs : Tendsto (fun Z : ℝ=>1440*(c*Z^ellMin)^(-(7/8:ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7/8)).comp ht).const_mul (1440:ℝ)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop (480:ℝ)),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ)),
    hs.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with Z hZ h480 hmod hsmall
  have hZ0 : 0<Z := by linarith
  have hmono (j : ι) : c*Z^ellMin≤c*Z^(ell j) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) hc.le
  refine ⟨hZ,h480,hsmall.le,fun j=>⟨h480.trans (hmono j),hmod.trans_le (hmono j)⟩,?_⟩
  intro j P hP
  have hp := pool_norm_bounds C S hc.le hd (Real.rpow_pos_of_pos hZ0 _) P hP
  have hn : c*Z^ellMin<(P.val.absNorm:ℝ) := (hmono j).trans_lt (by simpa only [mul_comm] using hp.1)
  exact ⟨hn.le,prime_coprime_of_norm_gt η P (hmod.trans hn),(mem_pool C S c d _ P).mp hP |>.2.2.2⟩

variable (M : Id) [NeZero M]
local instance : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
include hH

theorem power_ray_mass_and_normalizer {ι : Type*} [Fintype ι]
    (S : Finset Id) (W : ι→ℝ→ℝ) (c d : ℝ) (hc : 0<c) (hd : c≤d)
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hp : ∀j,tsupport (W j)⊆Set.Ioi 0) (hW0 : ∀j y,0≤W j y) (hne : ∀j,W j≠0)
    (ell : ι→ℝ) (hell : ∀j,0<ell j) (eps : ℝ) (heps : 0<eps) :
    ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      (∀j,0<slotMass T (residueWeights W (fun j=>Z^(ell j))) j) ∧
      |(Probe.principalScalar Finset.univ Z (∑j,ell j)
        (slotMass T (residueWeights W (fun j=>Z^(ell j)))))⁻¹|≤Z^eps := by
  have hm : ∀ᶠZ : ℝ in atTop,∀j,0<slotMass
      (fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j)))
      (residueWeights W (fun j=>Z^(ell j))) j := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_rpow_atTop (hell j)).eventually
      (ray_pool_mass_eventually_positive M H hH S (W j) c d hc hd (hsupp j)
        (hW j) (hcompact j) (hp j) (hW0 j) (hne j))
  have hi := ProbeRayNormalization.ray_principalScalar_inverse_subpower M H hH Finset.univ S W
    (fun _=>c) (fun _=>d) ell (fun _ _=>hc) (fun _ _=>hd) (fun j _=>hsupp j)
    (fun j _=>hW j) (fun j _=>hcompact j) (fun j _=>hp j) (fun j _=>hW0 j) (fun j _=>hne j)
    (fun j _=>hell j) eps heps
  filter_upwards [hm,hi] with Z hmass hinv
  exact ⟨hmass,hinv⟩
end SevenEighths.ProbeRaySlots
end

end OAI

end Source1806

/- Original source: OAI/NumberTheory/DirichletL/Detector/PrincipalNormalized.lean; sha256: b98009f4e73427d1ed7fc1d35e124f085f10082e481e0031222f40e3436de397 -/
section Source1807
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter
namespace SevenEighths.ProbePrincipalNormalized
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

lemma normalized_error (A R F N : ℂ) (c d v : ℝ)
    (hc : 0≤c) (hA : ‖A-R‖≤c) (hN : ‖N⁻¹‖≤v)
    (hR : ‖R/N-F‖≤d) : ‖A/N-F‖≤c*v+d := by
  calc
    _ = ‖(A-R)*N⁻¹+(R/N-F)‖ := by congr 1; simp only [div_eq_mul_inv];ring
    _ ≤ ‖(A-R)*N⁻¹‖+‖R/N-F‖ := norm_add_le _ _
    _ ≤ c*v+d := by rw [norm_mul];gcongr

theorem actual_ray_principal_comparison {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hmin : 0<ellMin)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hdis : Function.Injective ell)
    (hsum : (∑j,ell j)=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0<e) (hehi : e≤1/1000) (hnu : 0<nu)
    (ha : 7/8<HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
      C*(Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+
        Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0,hC0,hrem⟩ := ProbePrincipalPhysical.physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K:=K)
  obtain ⟨D,hD,hres⟩ := normalized_actual_window_residue S hS η ha ha2 (by linarith) (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏p∈S,p)
  let C := C0/e*‖cs⁻¹‖+D*c^(-(7/8:ℝ))+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin ell hell,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y=>(hWbounds j y).1) hne ell (fun j=>hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _=>c) (fun _=>d) ell (fun _=>hc) (fun _=>hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ,h480,hsmall,hslot,hpool⟩
  have hZ0 : 0<Z := by linarith
  let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
  let normer := cs*(Probe.principalScalar Finset.univ Z (1/6)
    (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j=>Z^(ell j)) (c*Z^ellMin) (Z^(23/48:ℝ)) Z h480 hsmall
    (fun j _ p _=>(hWbounds j _).1) (fun j _ p hp=>(hpool j p hp).1)
    (fun j _ p hp=>(hpool j p hp).2.1) (fun j _=>hmass.1 j) hZ
  dsimp only at hr ⊢
  refine ⟨hr.1,?_⟩
  have hraw := hrem ell hsum W hWbounds (fun j=>Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp=>(hpool j p hp).2.2) htuple Z hZ (fun j=>(hslot j).1) (fun j=>(hslot j).2)
  have hinv : ‖normer⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    dsimp only [normer]
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,norm_real]
    simpa only [hsum,Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hh := normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2.2
  have hpw : (c*Z^ellMin)^(-(7/8:ℝ))=c^(-(7/8:ℝ))*Z^(-(7/8:ℝ)*ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _),←Real.rpow_mul hZ0.le]
    congr 2;ring
  have heq1 : (C0/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000))*(‖cs⁻¹‖*Z^nu)=
      (C0/e*‖cs⁻¹‖)*Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu) := by
    rw [Real.rpow_add hZ0];ring
  have heq2 : D*Z^(HeckeZeroSupremum.beta+e-11/16)*(c*Z^ellMin)^(-(7/8:ℝ))=
      (D*c^(-(7/8:ℝ)))*Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin) := by
    rw [hpw]
    rw [show HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin=
      (HeckeZeroSupremum.beta+e-11/16)+(-(7/8:ℝ)*ellMin) by ring,Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1,heq2]
  have h1 : C0/e*‖cs⁻¹‖≤C := by
    dsimp [C]
    have : 0≤D*c^(-(7/8:ℝ)) := by positivity
    linarith
  have h2 : D*c^(-(7/8:ℝ))≤C := by
    dsimp [C]
    have : 0≤C0/e*‖cs⁻¹‖ := by positivity
    linarith
  calc
    _ ≤ C*Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+
        C*Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin) := by gcongr
    _ = _ := by ring
end SevenEighths.ProbePrincipalNormalized
end

end OAI

end Source1807

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CubeNormalizer.lean; sha256: d57811850ecae40246f331be0fe5bf0ce0aca3cd0ab9e27f980d28907046529b -/
section Source1808
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison
open PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem actual_ray_normalizer_inverse {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0<c) (hcb : c≤b)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hellsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c b) (hp : ∀j y,0≤W j y) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧ ‖normer⁻¹‖≤C*Z^nu := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let cs := sourceResidueConstant W0 W1 (∏P∈S,P)
  refine ⟨‖cs⁻¹‖+1,by positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply Set.Subset.trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy
    exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_ray_mass_and_normalizer M H hH S W c b hc hcb hsupp hW hcompact hpos hp hne ell hell nu hnu,
    eventually_gt_atTop (0:ℝ)] with Z hmass hZ
  dsimp only
  refine ⟨ProbePrincipalNormalizer.signed_source_normalizer_ne_zero (∏P∈S,P)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 Finset.univ
    (fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
    (residueWeights W (fun j=>Z^(ell j))) Z (1/6) hZ (fun j _=>hmass.1 j),?_⟩
  have hb : ‖(sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (1/6)
        (slotMass (fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
          (residueWeights W (fun j=>Z^(ell j)))) : ℂ))⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,Complex.norm_real]
    simpa only [hellsum,Real.norm_eq_abs,mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ.le _))

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1808

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowNormalized.lean; sha256: 0c6c90b0ffd370ef8a1b0bcf8b39d92950e45248d448ff0360e2be607faaade0 -/
section Source1809
namespace OAI

noncomputable section
open scoped Classical ContDiff
open Filter
namespace SevenEighths.ProbePhysical
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem original_normalized_compensatedPhysicalProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer‖≤
        C*Z^(3/16+loss) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin K) : Function.support (WC j)⊆Set.Icc a b := by
    intro y hy
    apply Set.Ioo_subset_Icc_self (hsupp j _)
    intro hz
    exact hy (by dsimp [WC];rw [hz];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hW1' : Function.support W1⊆Set.Icc a1 (max b1 (a1+1)) := by
    intro y hy
    exact ⟨(hW1 hy).1,(hW1 hy).2.trans (le_max_left _ _)⟩
  have hab1 : a1<max b1 (a1+1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨Cn,hCn,hnorm⟩ := ProbeHighRowFamily.actual_ray_normalizer_inverse M H hH S hS a b ha hab
    ell hell hsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 (loss/2) (by positivity)
  intro η
  obtain ⟨Cp,hCp,hprobe⟩ := original_ray_compensatedPhysicalProbe_low_loss S hS hmax ell
    (fun j=>(hell j).le) hinj hsum.le (RayQuotient.identityClass M H) a b B (loss/2)
    ha hab (by positivity) WC hWC hWCB W0 W1 a0 b0 a1 (max b1 (a1+1))
    (SchwartzMap.seminorm ℝ 0 0 W0) (SchwartzMap.seminorm ℝ 0 0 W1)
    ha0 ha1 hab1 (by positivity) (by positivity) hW0 hW1' (W0.smooth (⊤ : ℕ∞)) (W1.smooth (⊤ : ℕ∞))
    (SchwartzMap.norm_le_seminorm ℝ W0) (SchwartzMap.norm_le_seminorm ℝ W1) η
  refine ⟨Cp*Cn,by positivity,?_⟩
  filter_upwards [hprobe,hnorm,eventually_gt_atTop (0:ℝ)] with Z hp hn hZ
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  rw [div_eq_mul_inv,norm_mul]
  calc
    _≤(Cp*Z^(3/16+loss/2))*(Cn*Z^(loss/2)) :=
      mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)
    _=(Cp*Cn)*Z^(3/16+loss) := by
      rw [mul_mul_mul_comm,←Real.rpow_add hZ]
      congr 2
      ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1809

/- Original source: OAI/NumberTheory/DirichletL/Hecke/SignalIdentity.lean; sha256: b62af8a2ae114e91f46d872392ccbd130c48b5bde2c8aeef073bcf9b831c8e1b -/
section Source1810
namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology Classical
namespace SevenEighths.HeckeSignal
open HeckeFamily Continuation

private theorem line_tendsto_punctured :
    Tendsto (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) (𝓝[≠] 0) (𝓝[≠] (2 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Continuous (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) := by fun_prop
    simpa using (h.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hy (by nlinarith [Real.pi_pos])

theorem signalMellin_eq_amplitude (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (c a : ℝ) (ha : a < 2)
    (htop : signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    signalMellin (signal χ H c) c s = amplitude χ H s := by
  have hF := signalMellin_analytic (signal χ H c) a c
    (signal_locallyIntegrable χ H hH hb c) htop (signal_rapidDecayAtZero χ H hH hb c)
  have hFa : AnalyticOnNhd ℂ (signalMellin (signal χ H c) c) {z : ℂ | max a 1 < z.re} :=
    hF.mono (fun _ hz => (le_max_left a 1).trans_lt hz)
  have hA : AnalyticOnNhd ℂ (amplitude χ H) {z : ℂ | max a 1 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).2
    intro z hz
    have hq := quotient_differentiableAt χ H hH ((le_max_right a 1).trans_lt hz)
    exact ((((differentiable_id.sub_const (5/6 : ℂ)).pow 2).cexp.differentiableAt).mul hq).differentiableWithinAt
  apply hFa.eqOn_of_preconnected_of_frequently_eq hA (convex_halfSpace_re_gt _).isPreconnected
    (z₀ := (2 : ℂ)) (by simpa using max_lt ha (by norm_num : (1 : ℝ) < 2)) _ hs
  apply line_tendsto_punctured.frequently
  exact Filter.Frequently.of_forall (fun y => signalMellin_eq_amplitude_on_line χ H hH hb c a ha htop y)

theorem poleRemoved_mul_signalMellin (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (c a : ℝ) (ha : a < 2)
    (htop : signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    HeckeOrigin.poleRemoved χ s * signalMellin (signal χ H c) c s =
      (s-1) * gaussianMultiplier H s := by
  have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
  rw [HeckeOrigin.poleRemoved_eq χ h0 h1, signalMellin_eq_amplitude χ H hH hb c a ha htop hs]
  unfold amplitude quotient gaussianMultiplier
  rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
  have hn := LFunction_ne_zero_of_one_lt_re χ hs1
  field_simp

def targetRegularizer (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then s-1 else 1

def regularL (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then HeckeOrigin.poleRemoved χ s else LFunction χ s

theorem targetRegularizer_entire (χ : Character) : Differentiable ℂ (targetRegularizer χ) := by
  by_cases h : χ.residue = 1
  · have he : targetRegularizer χ = fun z : ℂ => z-1 := by funext z; simp [targetRegularizer, h]
    rw [he]
    exact differentiable_id.sub_const 1
  · have he : targetRegularizer χ = fun _ : ℂ => (1 : ℂ) := by funext z; simp [targetRegularizer, h]
    rw [he]
    exact differentiable_const 1

theorem regularL_entire (χ : Character) : Differentiable ℂ (regularL χ) := by
  by_cases h : χ.residue = 1
  · have he : regularL χ = HeckeOrigin.poleRemoved χ := by funext z; simp [regularL, h]
    rw [he]
    exact HeckeOrigin.poleRemoved_entire χ
  · have he : regularL χ = LFunction χ := by funext z; simp [regularL, h]
    rw [he]
    exact LFunction_entire_nonprincipal χ h

theorem regularL_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    regularL χ s = targetRegularizer χ s * LFunction χ s := by
  by_cases h : χ.residue = 1
  · simp only [regularL, targetRegularizer, h, ite_true]
    exact HeckeOrigin.poleRemoved_eq χ h0 (hpole.resolve_right (not_not.mpr h))
  · simp [regularL, targetRegularizer, h]

theorem targetRegularizer_ne_zero (χ : Character) {s : ℂ}
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : targetRegularizer χ s ≠ 0 := by
  by_cases h : χ.residue = 1
  · simpa only [targetRegularizer, h, ite_true, sub_ne_zero] using
      hpole.resolve_right (not_not.mpr h)
  · simp [targetRegularizer, h]

theorem nonzero_of_probe_bounds (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ)
    (β ω σ c : ℝ) (hβ : β ≤ 1) (hω0 : 0 < ω) (hω : ω < β-7/8) (hσ : 0 < σ)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (hJ : J =O[atTop] (fun x : ℝ => x^(7/8+c+ω)))
    (herror : (fun x => J x - signal χ H c x) =O[atTop]
      (fun x : ℝ => x^(β+c-σ)))
    {ρ : ℂ} (hρ : β - Supremum.continuationMargin β ω σ < ρ.re)
    (hpole : ρ ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ ρ ≠ 0 := by
  let a := β - Supremum.continuationMargin β ω σ
  have ha2 : a < 2 := by
    have hp := Supremum.continuationMargin_pos hω hσ
    dsimp [a]
    linarith
  have htop : signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
    have h := common_signal_bound_with_margin J (signal χ H c) β ω σ c hJ herror
    convert h using 1; dsimp [a]; ring_nf
  have hHd := hH.differentiableOn
  apply nonzero_of_common_signal β ω σ c hω0 (LFunction χ) (regularL χ)
    (targetRegularizer χ) H J (signal χ H c)
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr (regularL_entire χ)).mono (Set.subset_univ _))
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr (targetRegularizer_entire χ)).mono (Set.subset_univ _))
    hH hb (signal_locallyIntegrable χ H hHd hb c) (signal_rapidDecayAtZero χ H hHd hb c)
    hJ herror _ hρ _ (targetRegularizer_ne_zero χ hpole)
  · intro s hs
    have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
    rw [regularL_eq χ h0 (Or.inl h1), signalMellin_eq_amplitude χ H hHd hb c a ha2 htop hs]
    unfold amplitude quotient gaussianMultiplier
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
    have hn := LFunction_ne_zero_of_one_lt_re χ hs1
    field_simp
  · apply regularL_eq χ _ hpole
    intro h
    have hbound := Supremum.continuation_boundary_gt (β := β) (σ := σ) hω0
    rw [h] at hρ
    norm_num at hρ
    linarith

end SevenEighths.HeckeSignal

end

end OAI

end Source1810

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimitiveSupremum.lean; sha256: d049c74d13211d7bb59aabaaa8f84275c861b68b08305dab8306dbc2c97e2b26 -/
section Source1811
namespace OAI

noncomputable section
namespace SevenEighths.HeckePrimitiveSupremum
open HeckeFamily HeckeZeroSupremum

def primitiveZeroRealParts : Set ℝ :=
  {x | ∃ (χ : Character) (s : ℂ), FiniteFourier.IsPrimitiveOnIdeals χ.residue ∧
    (1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧
    LFunction χ s = 0 ∧ s.re = x}

def primitiveSetWithSentinel : Set ℝ := insert (1 / 2) primitiveZeroRealParts

theorem primitiveSet_subset : primitiveSetWithSentinel ⊆ zeroSetWithSentinel := by
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact Set.mem_insert _ _
  · obtain ⟨χ, s, _, hhalf, _, hpole, hz, rfl⟩ := hx
    exact Set.mem_insert_of_mem _ ⟨χ, s, by linarith, hpole, hz, rfl⟩

theorem primitiveSet_bddAbove : BddAbove primitiveSetWithSentinel :=
  zeroSet_bddAbove.mono primitiveSet_subset

theorem primitiveSet_nonempty : primitiveSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem beta_eq_primitive_supremum : beta = sSup primitiveSetWithSentinel := by
  apply le_antisymm
  · apply csSup_le zeroSet_nonempty
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact le_csSup primitiveSet_bddAbove (Set.mem_insert _ _)
    · by_cases hhalf : (1 / 2 : ℝ) ≤ x
      · obtain ⟨χ, s, hpos, hpole, hz, rfl⟩ := hx
        obtain ⟨ψ, hp, hpoleψ, hzψ⟩ :=
          HeckeFiniteDeletion.exists_primitive_zero χ hpos hpole hz
        apply le_csSup primitiveSet_bddAbove
        exact Set.mem_insert_of_mem _ ⟨ψ, s, hp, hhalf,
          zeroRealParts_le_one ⟨χ, s, hpos, hpole, hz, rfl⟩, hpoleψ, hzψ, rfl⟩
      · exact (le_of_not_ge hhalf).trans
          (le_csSup primitiveSet_bddAbove (Set.mem_insert _ _))
  · exact csSup_le_csSup zeroSet_bddAbove primitiveSet_nonempty primitiveSet_subset

theorem exists_primitive_zero_near_beta {ε : ℝ} (hε : 0 < ε)
    (hsmall : (1 / 2 : ℝ) ≤ beta - ε) :
    ∃ (χ : Character) (s : ℂ), FiniteFourier.IsPrimitiveOnIdeals χ.residue ∧
      (1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧
      LFunction χ s = 0 ∧ beta - ε < s.re := by
  rw [beta_eq_primitive_supremum] at hsmall ⊢
  obtain ⟨x, hx, hlt⟩ := Supremum.exists_gt_supremum_sub_of_insert
    primitiveSet_bddAbove hε hsmall
  obtain ⟨χ, s, hp, hhalf, hone, hpole, hz, rfl⟩ := hx
  exact ⟨χ, s, hp, hhalf, hone, hpole, hz, hlt⟩

end SevenEighths.HeckePrimitiveSupremum

end

end OAI

end Source1811

/- Original source: OAI/NumberTheory/DirichletL/Hecke/Dirichlet.lean; sha256: 8b33d23c18ec5b85a13043aa775841389903247645fc00536cc2b3286332ff7d -/
section Source1812
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDirichlet
open HeckeFamily

variable {q : ℕ}

def modulus (q : ℕ) : Ideal O := Ideal.span {(q : O)}

theorem modulus_ne_bot [NeZero q] : modulus q ≠ ⊥ := by
  simpa only [modulus, ne_eq, Ideal.span_singleton_eq_bot] using
    (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : O) ≠ 0)

theorem quotient_modulus_zero : (q : O ⧸ modulus q) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (modulus q))]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem norm_span_dvd (z : O) :
    z ∣ (Ideal.absNorm (Ideal.span {z}) : O) := by
  have h : (Ideal.absNorm (Ideal.span {z}) : ℤ) =
      ShortDraftLatticeCount.q (ActualEisensteinCoordinates.coords z) := by
    rw [← ActualEisensteinCubic.qNat_eq_absNorm_span]
    exact Int.toNat_of_nonneg (ShortDraftLatticeCount.qO_nonneg z)
  rw [← Int.cast_natCast, h]
  exact ⟨_, ActualEisensteinCubic.coordinate_norm_eq_mul_conjO z⟩

theorem quotient_unit_of_norm_unit (z : O)
    (hz : IsUnit (Ideal.absNorm (Ideal.span {z}) : ZMod q)) :
    IsUnit (Ideal.Quotient.mk (modulus q) z) := by
  have hc := (ZMod.isUnit_iff_coprime _ _).mp hz
  have hi : IsCoprime (Ideal.absNorm (Ideal.span {z}) : O ⧸ modulus q) (q : O ⧸ modulus q) := by
    simpa only [map_natCast] using hc.isCoprime.map (Int.castRingHom (O ⧸ modulus q))
  rw [quotient_modulus_zero, isCoprime_zero_right] at hi
  obtain ⟨w, hw⟩ := norm_span_dvd z
  have hn : (Ideal.absNorm (Ideal.span {z}) : O ⧸ modulus q) =
      Ideal.Quotient.mk (modulus q) z * Ideal.Quotient.mk (modulus q) w := by
    rw [← map_mul, ← hw, map_natCast]
  rw [hn] at hi
  exact isUnit_of_mul_isUnit_left hi

def residue (χ : DirichletCharacter ℂ q) : MulChar (O ⧸ modulus q) ℂ where
  toFun x := Quotient.liftOn' x (InitialMeanSquare.normCharacter χ) (by
    intro a b hab
    exact CanonicalCoefficientClass.normCharacter_factorsModulo χ a b
      ((modulus q).quotientRel_def.mp hab))
  map_one' := (InitialMeanSquare.normCharacter χ).map_one
  map_mul' x y := by
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    exact (InitialMeanSquare.normCharacter χ).map_mul a b
  map_nonunit' x hx := by
    refine Quotient.inductionOn' x (fun z hz => ?_) hx
    change χ (Ideal.absNorm (Ideal.span {z})) = 0
    apply MulChar.map_nonunit
    exact fun h => hz (quotient_unit_of_norm_unit z h)

@[simp] theorem residue_mk (χ : DirichletCharacter ℂ q) (z : O) :
    residue χ (Ideal.Quotient.mk (modulus q) z) = χ (Ideal.absNorm (Ideal.span {z})) := rfl

theorem residue_unit_trivial (χ : DirichletCharacter ℂ q) (u : Oˣ) :
    residue χ (Ideal.Quotient.mk (modulus q) (u : O)) = 1 := by
  rw [residue_mk, Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top]
  simp

variable [NeZero q]

def character (χ : DirichletCharacter ℂ q) : Character :=
  Character.ofResidue (modulus q) modulus_ne_bot (residue χ) (residue_unit_trivial χ)

@[simp] theorem elementCoeff_character (χ : DirichletCharacter ℂ q) (z : O) :
    elementCoeff (character χ) z = χ (Ideal.absNorm (Ideal.span {z})) := rfl

theorem idealCoeff_character (χ : DirichletCharacter ℂ q) (I : Ideal O) (hI : I ≠ 0) :
    idealCoeff (character χ) I = χ (Ideal.absNorm I) := by
  rw [← ConcretePrimeRowBridge.span_idealGenerator I]
  rw [idealCoeff_span _ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),
    elementCoeff_character, ConcretePrimeRowBridge.span_idealGenerator]

theorem moebius_idealCoeff_character (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    (UniqueFactorizationMonoid.moebius I : ℂ) * idealCoeff (character χ) I =
      ShortDraftHeckeBridge.baseChangeWeight χ I := by
  by_cases hI : I = 0
  · subst I
    unfold ShortDraftHeckeBridge.baseChangeWeight
    rw [UniqueFactorizationMonoid.moebius_zero]
    simp
  · rw [idealCoeff_character χ I hI]
    rfl

theorem inverseSeries_eq_pairInverse_LSeries (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    IdealEuler.inverseSeries (idealCoeff (character χ)) s =
      LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ (ShortDraftHeckeBridge.baseChangeChar χ)) s := by
  rw [IdealEuler.inverseSeries]
  have ht (I : Ideal O) : (UniqueFactorizationMonoid.moebius I : ℂ) *
      IdealEuler.weighted (idealCoeff (character χ)) s I =
      ShortDraftHeckeBridge.baseChangeWeight χ I * CubicEisenstein.fullIdealWeight s I := by
    change (UniqueFactorizationMonoid.moebius I : ℂ) *
      (idealCoeff (character χ) I * CubicEisenstein.fullIdealWeight s I) = _
    rw [← mul_assoc, moebius_idealCoeff_character]
  simp_rw [ht]
  rw [SmoothMobiusCorrection.idealDirichlet_eq_LSeries _
    (ConcretePrimeRowBridge.baseChangeWeight_norm_le_one χ) s hs]
  exact ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse χ
    (ShortDraftHeckeBridge.baseChangeChar χ) _
    (ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff χ) s

theorem LFunction_eq_dirichlet_product_right (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LFunction (character χ) s = χ.LFunction s *
      (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s := by
  have hH := inverseSeries_mul_LFunction (character χ) hs
  have hD := ShortDraftHeckeBridge.pair_inverse_euler_identity χ
    (ShortDraftHeckeBridge.baseChangeChar χ) s hs
  rw [inverseSeries_eq_pairInverse_LSeries χ hs] at hH
  have hne : LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ
      (ShortDraftHeckeBridge.baseChangeChar χ)) s ≠ 0 := by
    intro h
    rw [h, zero_mul] at hH
    exact zero_ne_one hH
  apply mul_left_cancel₀ hne
  rw [hH, mul_comm, hD]

theorem LFunction_eq_dirichlet_product (χ : DirichletCharacter ℂ q)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LFunction (character χ) s = χ.LFunction s *
      (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s := by
  let U : Set ℂ := {0,1}ᶜ
  have hU : IsOpen U := (Set.toFinite ({0,1} : Set ℂ)).isClosed.isOpen_compl
  have hpc : IsPreconnected U :=
    ((Set.toFinite ({0,1} : Set ℂ)).countable.isConnected_compl_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)).isPreconnected
  have hmem : s ∈ U := by simp [U, h0, h1]
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (f := LFunction (character χ))
    (g := fun z => χ.LFunction z * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction z)
    _ _ hpc htwo _ hmem
  · apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hz' : z ≠ 0 ∧ z ≠ 1 := by simpa [U] using hz
    exact (LFunction_differentiableAt _ hz'.1 (Or.inl hz'.2)).differentiableWithinAt
  · apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hz' : z ≠ 1 := by simp only [U, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hz; exact hz.2
    exact ((χ.differentiableAt_LFunction z (Or.inl hz')).mul
      ((ShortDraftHeckeBridge.baseChangeChar χ).differentiableAt_LFunction z
        (Or.inl hz'))).differentiableWithinAt
  · filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact LFunction_eq_dirichlet_product_right χ hz

theorem dirichlet_seven_eighths_of_hecke
    (hH : ∀ (η : Character) (s : ℂ), (7/8 : ℝ) < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8 : ℝ) < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h := hH (character χ) s hs (Or.inl hs1)
  rw [LFunction_eq_dirichlet_product χ hs0 hs1] at h
  exact (mul_ne_zero_iff.mp h).1

theorem zeta_seven_eighths_of_hecke
    (hH : ∀ (η : Character) (s : ℂ), (7/8 : ℝ) < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    (s : ℂ) (hs : (7/8 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := dirichlet_seven_eighths_of_hecke hH (1 : DirichletCharacter ℂ 1) s hs
    (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

end SevenEighths.HeckeDirichlet

end

end OAI

end Source1812

/- Original source: OAI/NumberTheory/DirichletL/Hecke/CommonProbe.lean; sha256: db523b6b84d2464b34837d864e6d2811903e6085c2862eda85e1c8e2c7b839d4 -/
section Source1813
namespace OAI

noncomputable section
open Filter Asymptotics
open scoped Classical
namespace SevenEighths.HeckeCommonProbe
open HeckeFamily HeckeZeroSupremum

def PrimitiveContract (ω σ : ℝ) : Prop :=
  ∀ η : Character, FiniteFourier.IsPrimitiveOnIdeals η.residue →
    ∃ (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ),
      (∀ I, idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff η I else 0) ∧
      AnalyticOnNhd ℂ H {s : ℂ | 7/8 < s.re} ∧
      (∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2) ∧
      J =O[atTop] (fun x : ℝ => x^(3/16+ω)) ∧
      (fun x => J x - HeckeSignal.signal χ H (-11/16) x) =O[atTop]
        (fun x : ℝ => x^(beta-11/16-σ))

def UniformCommonProbe : Prop :=
  7/8 < beta → ∃ ω σ : ℝ,
    0 < ω ∧ ω < beta-7/8 ∧ 0 < σ ∧ PrimitiveContract ω σ

theorem beta_le_seven_eighths (h : UniformCommonProbe) : beta ≤ 7/8 := by
  by_contra hn
  obtain ⟨ω, σ, hω0, hω, hσ, hcontract⟩ := h (lt_of_not_ge hn)
  have hmargin := Supremum.continuationMargin_pos hω hσ
  have hboundary := Supremum.continuation_boundary_gt (β := beta) (σ := σ) hω0
  obtain ⟨η, ρ, hp, hhalf, _, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin (by linarith)
  obtain ⟨χ, H, J, hmask, hH, hb, hJ, herr⟩ := hcontract η hp
  have hχpole : ρ ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr (fun hc => hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ : LFunction χ ρ = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask (by linarith) hχpole,
      hz, zero_mul]
  apply (HeckeSignal.nonzero_of_probe_bounds χ H J beta ω σ (-11/16)
    beta_le_one hω0 hω hσ hH hb ?_ ?_ hnear hχpole) hzχ
  · convert hJ using 1; ring_nf
  · convert herr using 1; ring_nf

theorem hecke_ne_zero_of_common_probe (h : UniformCommonProbe)
    (χ : Character) (s : ℂ) (hs : (7/8 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  exact LFunction_ne_zero_of_beta_lt χ ((beta_le_seven_eighths h).trans_lt hs) hpole

theorem dirichlet_of_common_probe (h : UniformCommonProbe) (q : ℕ) (hq : q ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8 : ℝ) < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 := by
  let : NeZero q := ⟨hq⟩
  exact HeckeDirichlet.dirichlet_seven_eighths_of_hecke
    (hecke_ne_zero_of_common_probe h) χ s hs hexc

theorem zeta_of_common_probe (h : UniformCommonProbe) (s : ℂ)
    (hs : (7/8 : ℝ) < s.re) : riemannZeta s ≠ 0 :=
  HeckeDirichlet.zeta_seven_eighths_of_hecke (hecke_ne_zero_of_common_probe h) s hs

end SevenEighths.HeckeCommonProbe

end

end OAI

end Source1813

/- Original source: OAI/NumberTheory/DirichletL/Detector/FinalAssemblySource.lean; sha256: 32d7255e4de3d6709dc2e06d61c52651beca2f34658536a89b5719ec2719ec91 -/
section Source1814
namespace OAI

noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

def normalizedProbe {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (ell : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ) : ℂ :=
  let Yp := fun j=>Z^(ell j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j=>canonicalSlotSupport (T j)) (fun j y=>(W j y:ℂ)) Yp
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ))

lemma isBigO_rpow_of_eventual_norm_bound (f : ℝ→ℂ) (r : ℝ)
    (h : ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,‖f Z‖≤C*Z^r) :
    f=O[atTop](fun Z : ℝ=>Z^r) := by
  obtain ⟨C,hC,hb⟩ := h
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with Z hb hZ
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hZ r)] using hb

theorem normalizedProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,normalizedProbe M H S hmax ell a b W W0 W1 η=O[atTop](fun Z : ℝ=>Z^(3/16+loss)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  obtain ⟨C,hC,hb⟩ := original_normalized_compensatedPhysicalProbe_low M H hH S hS hmax
    a b B loss ha hab hloss ell hell hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  apply isBigO_rpow_of_eventual_norm_bound
  exact ⟨C,hC,hb.mono (fun Z h=>h.2)⟩

theorem actual_source_analytic (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) :
    (∀I,idealCoeff (η.excludePrimes S hS.prime) I=
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ|7/8<s.re} ∧
    (∀s : ℂ,7/8<s.re→‖sourceCorrection η S s-1‖≤1/2) := by
  exact ⟨excludePrimes_mask η S hS.prime,
    (sourceCorrection_differentiable η S hS).analyticOnNhd (Complex.isOpen_re_gt _),
    sourceCorrection_bound η S hS⟩

end SevenEighths.ProbeFinalAssembly
end

end OAI

end Source1814

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorDynamicSelection.lean; sha256: 46cd5eddb45bff5314458f1ea249763136afd25d24482772b6fc68f0f04ea3ee -/
section Source1815
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorDynamicSelection
open HeckeFamily HeckeDetectorWitnessRows

theorem actual_witness_family (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ), i≤I → 51/100<a → a≤1 →
        (∀ u, HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u, a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
          Nonempty (∀ u,Witness (χ u) (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := exists_from_maximum dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  exact ⟨fun u => Classical.choice (hZ₀ Z hZ d hd hd' (χ u) (hχ u) a i hi ha ha'
    (hnext u) (hcurrent u) (hQ u) tstar ht ht')⟩

def fiber {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U)) : Finset Row :=
  rows.filter (fun u => (w u).label=label ∧ (w u).left=J ∧ (w u).right=K)

theorem card_eq_sum_fibers {Row Label : Type*} [Fintype Label]
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i) :
    rows.card=∑ label : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
      (fiber rows χ U a ε tstar T allowance i w label J K).card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
    (f:=fun u => ((w u).label,(w u).left,(w u).right))
    (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,Prod.mk.injEq,fiber] using hh

end SevenEighths.HeckeDetectorDynamicSelection

end

end OAI

end Source1815

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorFiberPartition.lean; sha256: b79c31ccef2cfbbd8ffe03b6757ccbe69318f6ee0dbe7ae880f76161ef669173 -/
section Source1816
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorFiberPartition
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

abbrev BinLabel {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ) :=
  slots → ↥(HeckePrimeAmplitudeBins.labels cap mesh)

def amplitudeLabel {Row Slot : Type*} (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ) (u : Row) : BinLabel slots cap mesh :=
  fun s => ⟨HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s),
    HeckePrimeAmplitudeBins.amplitude_mem_labels _ _ _ _ hm⟩

def fiber {Row Label Slot : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) (bin : BinLabel slots ((2*a-1)/2) mesh)
    (label : Label) (J K : Fin (dyadicLength U)) : Finset Row :=
  rows.filter (fun u => amplitudeLabel slots U ((2*a-1)/2) mesh hm widths physical u=bin ∧
    (w u).label=label ∧ (w u).left=J ∧ (w u).right=K)

theorem card_eq_sum_fibers {Row Label Slot : Type*} [Fintype Label]
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) :
    rows.card=∑ bin : BinLabel slots ((2*a-1)/2) mesh, ∑ label : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        (fiber rows χ U a ε tstar T allowance i w slots mesh hm widths physical bin label J K).card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
    (f:=fun u => (amplitudeLabel slots U ((2*a-1)/2) mesh hm widths physical u,
      (w u).label,(w u).left,(w u).right)) (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,Prod.mk.injEq,fiber] using hh

def binValue {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (bin : BinLabel slots cap mesh) (s : Slot) : ℝ :=
  if hs : s∈slots then (bin ⟨s,hs⟩).val else 0

theorem fixed_bin {Row Label Slot : Type*}
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) (bin : BinLabel slots ((2*a-1)/2) mesh)
    (label : Label) (J K : Fin (dyadicLength U)) (u : Row)
    (hu : u∈fiber rows χ U a ε tstar T allowance i w slots mesh hm widths physical bin label J K)
    (s : Slot) (hs : s∈slots) :
    HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) mesh (physical u s)=
      binValue slots ((2*a-1)/2) mesh bin s := by
  have he := (Finset.mem_filter.mp hu).2.1
  have hv := congrArg (fun f : BinLabel slots ((2*a-1)/2) mesh => (f ⟨s,hs⟩).val) he
  simpa only [amplitudeLabel,binValue,dite_eq_left hs] using hv

def toFiber (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) {Label Slot : Type*}
    (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (hrow : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U)
    (data : Label→RowData) (reverse : Label→Bool)
    (hcoeff : ∀ u∈rows,∀ j,∀ I : Ideal O,idealCoeff (χ u j) I=
      if reverse j then starRingEnd ℂ (idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
      else idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hmesh : 0≤mesh) (hbw : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwmesh : ∀ s∈slots,widths s≤mesh)
    (hsupply : 7/37≤∑ s∈slots,widths s)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (label : Label)
    (J K : Fin (dyadicLength U))
    (hne : (fiber rows χ U a ε tstar T allowance i w slots binWidth hbw widths
      (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K).Nonempty) :
    Fiber M H Label Slot U a ε tstar T allowance i where
  rows := fiber rows χ U a ε tstar T allowance i w slots binWidth hbw widths
    (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K
  nonempty := hne
  family := χ
  witness := w
  label := label
  left := J
  right := K
  fixed_label := fun _u hu => (Finset.mem_filter.mp hu).2.2.1
  fixed_left := fun _u hu => (Finset.mem_filter.mp hu).2.2.2.1
  fixed_right := fun _u hu => (Finset.mem_filter.mp hu).2.2.2.2
  row_norm := fun u hu => hrow u (Finset.mem_filter.mp hu).1
  rowData := data label
  reverse := reverse label
  row_coeff := fun u hu => hcoeff u (Finset.mem_filter.mp hu).1 label
  slots := slots
  profile := profile
  upper := upper
  widths := widths
  external := external
  bin := binValue slots ((2*a-1)/2) binWidth bin
  mesh := mesh
  binWidth := binWidth
  mesh_nonneg := hmesh
  binWidth_pos := hbw
  widths_pos := hw
  widths_mesh := hwmesh
  supply := hsupply
  fixed_bin := fun u hu s hs => fixed_bin rows χ U a ε tstar T allowance i w slots binWidth hbw widths
    (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K u hu s hs

end SevenEighths.HeckeDetectorFiberPartition

end

end OAI

end Source1816

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorBatch.lean; sha256: bd7bf9bedfe6b8c8bfa7584b5bd2455238663bb29dec0d51516847068e4e2c04 -/
section Source1817
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorBatch
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorFiberPartition
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

structure Batch (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) (Label Slot : Type*)
    (U a ε tstar T allowance : ℝ) (i : ℕ) where
  rows : Finset FreeRow
  family : FreeRow→Label→Character
  witness : ∀ u,SupportedWitness (family u) U a ε tstar T allowance i
  row_norm : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U
  data : Label→RowData
  reverse : Label→Bool
  row_coeff : ∀ u∈rows,∀ j,∀ I : Ideal O,idealCoeff (family u j) I=
    if reverse j then starRingEnd ℂ (idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
    else idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I
  slots : Finset Slot
  profile : Slot→ℝ→ℂ
  upper : Slot→ℝ
  widths : Slot→ℝ
  external : Slot→ℂ
  mesh : ℝ
  binWidth : ℝ
  mesh_nonneg : 0≤mesh
  binWidth_pos : 0<binWidth
  widths_pos : ∀ s∈slots,0<widths s
  widths_mesh : ∀ s∈slots,widths s≤mesh
  supply : 7/37≤∑ s∈slots,widths s

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

abbrev Batch.Bin (B : Batch M H Label Slot U a ε tstar T allowance i) :=
  BinLabel B.slots ((2*a-1)/2) B.binWidth

def Batch.fiberRows (B : Batch M H Label Slot U a ε tstar T allowance i)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U)) : Finset FreeRow :=
  fiber B.rows B.family U a ε tstar T allowance i B.witness B.slots B.binWidth B.binWidth_pos B.widths
    (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U) bin j J K

def Batch.fiber (B : Batch M H Label Slot U a ε tstar T allowance i)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows bin j J K).Nonempty) : Fiber M H Label Slot U a ε tstar T allowance i :=
  toFiber M H B.rows B.family U a ε tstar T allowance i B.witness B.row_norm B.data B.reverse
    B.row_coeff B.slots B.profile B.upper B.widths B.external B.mesh B.binWidth B.mesh_nonneg
    B.binWidth_pos B.widths_pos B.widths_mesh B.supply bin j J K hne

def Batch.q (B : Batch M H Label Slot U a ε tstar T allowance i) (bin : B.Bin) : ℝ :=
  weightedMean B.slots B.widths (binValue B.slots ((2*a-1)/2) B.binWidth bin)

theorem Batch.card_eq_sum_fibers [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i) :
    B.rows.card=∑ bin : B.Bin, ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
      (B.fiberRows bin j J K).card :=
  HeckeDetectorFiberPartition.card_eq_sum_fibers B.rows B.family U a ε tstar T allowance i B.witness
    B.slots B.binWidth B.binWidth_pos B.widths
    (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U)

theorem Batch.card_bound [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i)
    (C : ℝ) (exponent : B.Bin→ℝ) (hC : 0≤C) (hU : 0<U)
    (hfiber : ∀ bin j J K,∀ hne : (B.fiberRows bin j J K).Nonempty,
      ((B.fiber bin j J K hne).rows.card : ℝ)≤C*U^(exponent bin)) :
    (B.rows.card : ℝ)≤(Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2*C*
      ∑ bin : B.Bin,U^(exponent bin) := by
  have he : (B.rows.card : ℝ)=∑ bin : B.Bin, ∑ j : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        ((B.fiberRows bin j J K).card : ℝ) := by exact_mod_cast B.card_eq_sum_fibers
  rw [he]
  calc
    _ ≤ ∑ bin : B.Bin, ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        C*U^(exponent bin) := by
      apply Finset.sum_le_sum
      intro bin _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro J _
      apply Finset.sum_le_sum
      intro K _
      by_cases hn : (B.fiberRows bin j J K).Nonempty
      · exact hfiber bin j J K hn
      · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
        simp only [Finset.card_empty,Nat.cast_zero]
        exact mul_nonneg hC (Real.rpow_nonneg hU.le _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      simp_rw [←mul_assoc]
      rw [←Finset.mul_sum]
      ring

end SevenEighths.HeckeDetectorBatch

end

end OAI

end Source1817

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorRawBranches.lean; sha256: 696bbacc691905ef06aa8934946185ae5d158907a93167d08005bd5da4ad3a4c -/
section Source1818
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorInverseFiberCount HeckeDetectorPlainFiberCount HeckeDetectorNoSlotPlainCount
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem Fiber.lengths (F : Fiber M H Label Slot U a ε tstar T allowance i) (hU : 1<U) :
    tstar-F.r-ε≤F.m ∧ F.r≤tstar+ε ∧ F.m≤1/2+75*ε ∧ tstar-1/2-76*ε≤F.r ∧ 0≤F.m :=
  fiber_lengths F.rows F.nonempty F.family U a ε tstar T allowance i hU F.witness
    F.left F.right F.fixed_left F.fixed_right

theorem Fiber.inverse_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F Δ c κ C height εm)
    (hU : 1<U) (ha : 1/2≤a) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (z : ℝ) (hz : 0≤z) (hz' : z≤7/37) (hcap1 : F.r+2*z<1) (hcap2 : 2*F.r+8*z<3) :
    (F.rows.card : ℝ)≤(12*(1+height)*C)*U^(1-(2*a-1)*F.r-2*F.q*z+2*ε+(2*a-1)*F.mesh+εm) := by
  exact inverse_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans F.supply) F.fixed_bin hC hh hf hcap1 hcap2 moments.inverse_marked

theorem Fiber.plain_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F Δ c κ C height εm)
    (hU : 1<U) (ha : 1/2≤a) (hΔ : 0≤Δ) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (z : ℝ) (hz : 0≤z) (hz' : z≤7/37) (hcap : 2*F.m+6*(3/4+2*Δ)*z≤1) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*U^(1-2*(2*a-1)*F.m-2*F.q*z+4*ε+(2*a-1)*F.mesh+εm) := by
  exact plain_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z (3/4+2*Δ) εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans F.supply) F.fixed_bin (by linarith) hC hh hf hcap moments.plain_marked

theorem Fiber.plain_unmarked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F Δ c κ C height εm)
    (hU : 1<U) (ha : 0≤a) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*U^(max 1 (2*F.m)-2*(2*a-1)*F.m+4*ε+εm) := by
  exact no_slot_plain_count F.rows F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    εm C height hC hh hf moments.plain_unmarked

def fiberConstant (C height K : ℝ) : ℝ := (192*(1+height)*C)*max 1 K

theorem fiberConstant_bounds (C height K : ℝ) (hC : 0≤C) (hh : 0≤height) (hK : 0≤K) :
    0≤fiberConstant C height K ∧ 192*(1+height)*C≤fiberConstant C height K ∧
      12*(1+height)*C≤fiberConstant C height K ∧
      12*(1+height)*(C*K)≤fiberConstant C height K := by
  have h1 : 0≤192*(1+height)*C := by positivity
  have h2 : 12*(1+height)*C≤192*(1+height)*C := by nlinarith
  have hbig : 192*(1+height)*C≤fiberConstant C height K :=
    le_mul_of_one_le_right h1 (le_max_left _ _)
  refine ⟨h1.trans hbig,hbig,h2.trans hbig,?_⟩
  calc
    _ = (12*(1+height)*C)*K := by ring
    _ ≤ (192*(1+height)*C)*max 1 K := mul_le_mul h2 (le_max_right _ _) hK h1

end SevenEighths.HeckeDetectorRawFiber

end

end OAI

end Source1818

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorCountFromMoments.lean; sha256: 5d29e2f64e2e52ac5beb54a873684c5ea7fb32511280e8d53fd4b378ac014149 -/
section Source1819
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorCountFromMoments
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBranchBudget
open HeckeDetectorRowCount

theorem count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε tstar T allowance Δ ν C height : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      1≤tstar → tstar≤3/2 → 0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      Moments F Δ c κ C height εm →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(max (shortExponent (2*a-1) (F.q/(2*a-1)) tstar) (longExponent (2*a-1) tstar)+
          Δ/4+159*ε+εm+F.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε tstar T allowance Δ ν C height i hU ha hδcap hε hεsmall ht ht' hΔ hΔ' hν hC hh hf
    Label Slot F moments
  let δ := 2*a-1
  let x := F.q/δ
  have hδ : 0<δ := by dsimp [δ]; linarith
  have ha' : 1/2≤a := by linarith
  have hδ1 : δ≤1 := by dsimp [δ]; linarith
  obtain ⟨hq0,hqδ⟩ := F.mean_bounds ha'
  have hx : 0≤x := div_nonneg hq0 hδ.le
  have hx' : x≤1/2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
  have hqx : δ*x=F.q := by dsimp [x]; field_simp
  have hgeom := F.lengths hU
  have hr0 : 0≤F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r≤2 := by linarith [hgeom.2.1]
  have hUp : 0<U := zero_lt_one.trans hU
  obtain ⟨hconst,hconstP,hconstI,hconstI0⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have promote (C' p q : ℝ) (hC' : C'≤fiberConstant C height K₀)
      (hb : (F.rows.card : ℝ)≤C'*U^p) (hpq : p≤q) :
      (F.rows.card : ℝ)≤fiberConstant C height K₀*U^q := by
    exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
  have hi0 := hamp F.rows F.family a ε tstar T allowance i hU ha'
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.inverse_raw
  have hI0 : (F.rows.card : ℝ)≤fiberConstant C height K₀*
      U^(max 1 ((1+5*F.r)/6)-δ*F.r+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstI0 hi0
    exact no_slot_inverse_loss F.r δ ε εm F.mesh ν hε F.mesh_nonneg hν.le
  have hp0 := F.plain_unmarked_count moments hU (by linarith) hC hh hf
  have hP0 : (F.rows.card : ℝ)≤fiberConstant C height K₀*
      U^(1-2*δ*F.m+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstP hp0
    exact no_slot_plain_loss F.m δ ε εm F.mesh ν hε hgeom.2.2.1 F.mesh_nonneg hν.le
  have hI : 23/37≤F.r → F.r<1 → ν<(1-F.r)/2 →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(inverseExponent δ x F.r+commonLoss ε εm F.mesh ν) := by
    intro hr hr1 hv
    obtain ⟨hz,hz',hcap1,hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
    have hb := F.inverse_marked_count moments hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
    apply promote _ _ _ hconstI hb
    have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    rwa [hqx] at hl
  have hP : F.r≤crossing x tstar → F.m<1/2 → ν<(1-2*F.m)/(9/2+12*Δ) →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(1-2*δ*F.m-2*(δ*x)*(1-2*F.m)/(9/2+12*Δ)+commonLoss ε εm F.mesh ν) := by
    intro hr hm hv
    obtain ⟨hz,hz',hcap⟩ := plain_requested_capacity Δ x tstar F.r F.m ε ν hΔ hx hx' ht ht'
      hr hgeom.1 (by linarith) hν.le hv
    have hb := F.plain_marked_count moments hU ha' hΔ hC hh hf
      ((1-2*F.m)/(9/2+12*Δ)-ν) hz hz' hcap
    apply promote _ _ _ hconstP hb
    have hl := plain_marked_loss F.m δ x Δ ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    simpa only [hqx] using hl
  have hc' := count_bound_of_source_branches (F.rows.card : ℝ) (fiberConstant C height K₀) U δ x Δ
    tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le hδcap hx hx' hΔ hΔ'
    ht ht' hν.le hε hgeom.1 hgeom.2.1 hI0 hP0 hI hP
  convert hc' using 1; congr 2
  unfold commonLoss
  ring

end SevenEighths.HeckeDetectorCountFromMoments

end

end OAI

end Source1819

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorBatchCount.lean; sha256: b910426b7dfc442a1e5af94ec153debe617d8c7592d59e4f4b61e1142832b71d -/
section Source1820
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorBatchCount
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows HeckeDetectorRowCount

theorem batch_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε tstar T allowance Δ ν C height : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      1≤tstar → tstar≤3/2 → 0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i),
      (∀ bin j J K,∀ hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2* fiberConstant C height K₀*
        ∑ bin : B.Bin,U^(max (shortExponent (2*a-1) (B.q bin/(2*a-1)) tstar)
          (longExponent (2*a-1) tstar)+Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := HeckeDetectorCountFromMoments.count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε tstar T allowance Δ ν C height i hU ha hδcap hε hεsmall ht ht' hΔ hΔ' hν hC hh hf
    Label Slot _ B moments
  apply B.card_bound (fiberConstant C height K₀) _
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU)
  intro bin j J K hne
  exact hcount a ε tstar T allowance Δ ν C height i hU ha hδcap hε hεsmall ht ht' hΔ hΔ' hν hC hh hf
    (B.fiber bin j J K hne) (moments bin j J K hne)

end SevenEighths.HeckeDetectorBatchCount

end

end OAI

end Source1820

/- Original source: OAI/NumberTheory/DirichletL/Endpoint.lean; sha256: 155fffbc6da45d459f2f9eada01f51dbae6b961ae8a456e603c59b13efe9baa5 -/
section Source1821
namespace OAI

namespace SevenEighths.Endpoint

noncomputable section

def denominator (y : ℝ) : ℝ := (37 + 34 * y) / 18

def primeWeight (y : ℝ) : ℝ := (7 + 18 * y + 8 * y ^ 2) / 9

def balanceDenominator (δ y : ℝ) : ℝ :=
  (5 / 6 - δ) * denominator y + δ * primeWeight y

def certificateWeight (y : ℝ) : ℝ := 51 + 41 * y

def balancedCutoff (δ y : ℝ) : ℝ :=
  1 + δ * primeWeight y / (2 * balanceDenominator δ y)

def balancedRowCount (δ y : ℝ) : ℝ :=
  1 - 5 / 6 + (5 / 6 - δ) * balancedCutoff δ y

def balancedExponent (δ y : ℝ) : ℝ :=
  -(1 / 48) + (2 / 3) * δ + δ * (1 / 2 - y) / 6 -
    (13 / 16) * (1 - balancedRowCount δ y)

theorem denominator_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    7 / 9 ≤ denominator y ∧ denominator y ≤ 3 := by
  dsimp [denominator]
  constructor <;> linarith

theorem primeWeight_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    7 / 9 ≤ primeWeight y ∧ primeWeight y ≤ 2 := by
  have hs := sq_nonneg y
  have ht := mul_nonneg hy0 (sub_nonneg.mpr hy1)
  dsimp [primeWeight]
  constructor <;> nlinarith

theorem balanceDenominator_bounds {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    35 / 54 ≤ balanceDenominator δ y ∧ balanceDenominator δ y ≤ 5 / 2 := by
  obtain ⟨hd0, hd1⟩ := denominator_bounds hy0 hy1
  obtain ⟨hp0, hp1⟩ := primeWeight_bounds hy0 hy1
  have ha : 0 ≤ 5 / 6 - δ := sub_nonneg.mpr hδ1
  have hl1 := mul_le_mul_of_nonneg_left hd0 ha
  have hl2 := mul_le_mul_of_nonneg_left hp0 hδ0
  have hu1 := mul_le_mul_of_nonneg_left hd1 ha
  have hu2 := mul_le_mul_of_nonneg_left (le_trans hp1 (by norm_num : (2 : ℝ) ≤ 3)) hδ0
  dsimp [balanceDenominator]
  constructor <;> nlinarith

theorem endpoint_identity (δ y : ℝ) (hJ : balanceDenominator δ y ≠ 0) :
    10368 * certificateWeight y * balanceDenominator δ y * (-balancedExponent δ y) =
      (3 + 5 * y) * ((4 * certificateWeight y * δ - 79) ^ 2 + 49) +
      4 * y * (4 * certificateWeight y * δ *
        ((1 + 3 * y) * (15 + 32 * y) * δ + 9 - 13 * y) + 265 + 3485 * y) := by
  unfold balancedExponent balancedRowCount balancedCutoff
  field_simp
  simp only [balanceDenominator, denominator, primeWeight, certificateWeight]
  ring

theorem balanced_endpoint_margin {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    (49 : ℝ) / 440640 ≤ -balancedExponent δ y := by
  obtain ⟨hJlo, hJhi⟩ := balanceDenominator_bounds hδ0 hδ1 hy0 hy1
  have hJpos : 0 < balanceDenominator δ y := by linarith
  have hvpos : 0 < certificateWeight y := by dsimp [certificateWeight]; linarith
  have hinner : 0 ≤ (1 + 3 * y) * (15 + 32 * y) * δ + 9 - 13 * y := by
    have hp : 0 ≤ (1 + 3 * y) * (15 + 32 * y) * δ := by positivity
    linarith
  have hrest : 0 ≤ 4 * y * (4 * certificateWeight y * δ *
      ((1 + 3 * y) * (15 + 32 * y) * δ + 9 - 13 * y) + 265 + 3485 * y) := by
    positivity
  have hsq : 0 ≤ (3 + 5 * y) * (4 * certificateWeight y * δ - 79) ^ 2 := by
    positivity
  have hid := endpoint_identity δ y (ne_of_gt hJpos)
  have hcert : 49 * (3 + 5 * y) ≤
      10368 * certificateWeight y * balanceDenominator δ y * (-balancedExponent δ y) := by
    nlinarith only [hid, hrest, hsq]
  have hvhi : certificateWeight y ≤ 17 * (3 + 5 * y) := by
    dsimp [certificateWeight]
    linarith
  have hscaled : 49 * certificateWeight y ≤
      176256 * certificateWeight y * balanceDenominator δ y * (-balancedExponent δ y) := by
    nlinarith only [hcert, hvhi]
  have hcancel : 49 ≤ 176256 * balanceDenominator δ y * (-balancedExponent δ y) := by
    nlinarith only [hscaled, hvpos]
  have hEpos : 0 < -balancedExponent δ y := by
    by_contra hn
    have hn' : -balancedExponent δ y ≤ 0 := le_of_not_gt hn
    have hp := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hJpos) hn'
    nlinarith only [hcancel, hp]
  have hup := mul_le_mul_of_nonneg_right hJhi (le_of_lt hEpos)
  nlinarith only [hcancel, hup]

theorem balanced_endpoint_strict {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    balancedExponent δ y < -(1 / 10000 : ℝ) := by
  have h := balanced_endpoint_margin hδ0 hδ1 hy0 hy1
  norm_num at *
  linarith

end

end SevenEighths.Endpoint

end OAI

end Source1821

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorRowCountEndpoint.lean; sha256: 79717dfc44a31432e01eba2992f2e136589659929168f4f33a70df4b2caef875 -/
section Source1822
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

lemma denominator_endpoint (x : ℝ) : denominator x=Endpoint.denominator (1/2-x) := by
  unfold denominator Endpoint.denominator
  ring

lemma primeWeight_endpoint (x : ℝ) : primeWeight x=Endpoint.primeWeight (1/2-x) := by
  unfold primeWeight Endpoint.primeWeight
  ring

theorem balanced_cutoff_bounds {δ x : ℝ} (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) :
    1≤Endpoint.balancedCutoff δ (1/2-x) ∧ Endpoint.balancedCutoff δ (1/2-x)≤3/2 := by
  have hy : 0≤1/2-x := by linarith
  have hy' : 1/2-x≤1/2 := by linarith
  have hd := Endpoint.denominator_bounds hy hy'
  have hp := Endpoint.primeWeight_bounds hy hy'
  have hJ := Endpoint.balanceDenominator_bounds hδ hδ' hy hy'
  have hJp : 0<Endpoint.balanceDenominator δ (1/2-x) := by linarith [hJ.1]
  unfold Endpoint.balancedCutoff
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hδ (by linarith [hp.1])) (by positivity))
  · have hnum : δ*Endpoint.primeWeight (1/2-x)≤Endpoint.balanceDenominator δ (1/2-x) := by
      unfold Endpoint.balanceDenominator
      have hh := mul_nonneg (sub_nonneg.mpr hδ') (show 0≤Endpoint.denominator (1/2-x) by linarith [hd.1])
      linarith
    have hh : δ*Endpoint.primeWeight (1/2-x)/(2*Endpoint.balanceDenominator δ (1/2-x))≤1/2 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith

theorem balanced_count_identity {δ x : ℝ} (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) :
    max (shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x)))
        (longExponent δ (Endpoint.balancedCutoff δ (1/2-x))) =
      Endpoint.balancedRowCount δ (1/2-x) := by
  have hy : 0≤1/2-x := by linarith
  have hy' : 1/2-x≤1/2 := by linarith
  have hDb : 0<Endpoint.denominator (1/2-x) := by
    have hh := Endpoint.denominator_bounds hy hy'
    linarith [hh.1]
  have hJb : 0<Endpoint.balanceDenominator δ (1/2-x) := by
    have hh := Endpoint.balanceDenominator_bounds hδ hδ' hy hy'
    linarith [hh.1]
  have hl : longExponent δ (Endpoint.balancedCutoff δ (1/2-x))=
      Endpoint.balancedRowCount δ (1/2-x) := by
    unfold longExponent Endpoint.balancedRowCount
    ring
  have hs : shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x))=
      Endpoint.balancedRowCount δ (1/2-x) := by
    unfold shortExponent
    rw [denominator_endpoint,primeWeight_endpoint]
    unfold Endpoint.balancedRowCount Endpoint.balancedCutoff
    generalize hDd : Endpoint.denominator (1/2-x) = D at *
    generalize hPd : Endpoint.primeWeight (1/2-x) = P at *
    generalize hJd : Endpoint.balanceDenominator δ (1/2-x) = J at *
    have hJdef : J=(5/6-δ)*D+δ*P := by
      rw [←hJd, Endpoint.balanceDenominator, hDd, hPd]
    have hD : D ≠ 0 := hDb.ne'
    have hJ : J ≠ 0 := hJb.ne'
    field_simp [hD,hJ]
    rw [hJdef]
    ring
  rw [hl,hs,max_self]

theorem high_bin_count {B C U δ r ε γ : ℝ}
    (hC : 0≤C) (hU : 1≤U) (hδ : 5/6≤δ) (hδ' : δ≤1)
    (hγ : 0≤γ) (hr : 1-γ≤r)
    (hI : B≤C*U^(max 1 ((1+5*r)/6)-δ*r+ε)) :
    B≤C*U^(1-δ+ε+γ) := by
  apply hI.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  by_cases hr1 : 1≤r
  · rw [max_eq_right (show 1≤(1+5*r)/6 by linarith)]
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hδ) (sub_nonneg.mpr hr1)
    nlinarith
  · rw [max_eq_left (show (1+5*r)/6≤1 by linarith)]
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤δ by linarith)
    have hh' := mul_le_mul_of_nonneg_right hδ' hγ
    nlinarith

theorem high_bin_endpoint {δ q R loss : ℝ} (_hδ : 5/6≤δ)
    (hq : q≤δ/2) (hR : R≤1-δ+loss) :
    -(1/48 : ℝ)+(2/3)*δ+q/6-(13/16)*(1-R)≤
      -1/48-δ/16+(13/16)*loss := by
  linarith

theorem balanced_endpoint_with_loss {δ x R loss : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤5/6) (hx : 0≤x) (hx' : x≤1/2)
    (hR : R≤max (shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x)))
      (longExponent δ (Endpoint.balancedCutoff δ (1/2-x)))+loss) :
    -(1/48 : ℝ)+(2/3)*δ+(δ*x)/6-(13/16)*(1-R)≤
      -49/440640+(13/16)*loss := by
  rw [balanced_count_identity hδ hδ' hx hx'] at hR
  have hh := Endpoint.balanced_endpoint_margin hδ hδ'
    (show 0≤1/2-x by linarith) (show 1/2-x≤1/2 by linarith)
  unfold Endpoint.balancedExponent at hh
  nlinarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI

end Source1822

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorAdaptiveCutoff.lean; sha256: 494cc048ad3438976fcab45b364e3c2828e51cdaee3aa2eac00268119514f92a -/
section Source1823
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorAdaptiveCutoff
open HeckeFamily HeckeDetectorSupportedWitness HeckeDetectorRowCount

def cutoff (δ q : ℝ) : ℝ :=
  if δ≤5/6 then Endpoint.balancedCutoff δ (1/2-min (1/2) (max 0 (q/δ))) else 3/2

theorem cutoff_bounds (δ q : ℝ) (hδ : 0≤δ) : 1≤cutoff δ q ∧ cutoff δ q≤3/2 := by
  unfold cutoff
  split_ifs with hd
  · exact balanced_cutoff_bounds hδ hd (le_min (by norm_num) (le_max_left _ _)) (min_le_left _ _)
  · norm_num

theorem cutoff_eq_balanced (δ q : ℝ) (hδ : 0<δ) (hd : δ≤5/6)
    (hq : 0≤q) (hq' : q≤δ/2) :
    cutoff δ q=Endpoint.balancedCutoff δ (1/2-q/δ) := by
  have hx : 0≤q/δ := div_nonneg hq hδ.le
  have hx' : q/δ≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  simp only [cutoff,ite_eq_left hd,max_eq_right hx,min_eq_right hx']

theorem cutoff_eq_high (δ q : ℝ) (hδ : 5/6<δ) : cutoff δ q=3/2 := by
  simp only [cutoff,ite_eq_right (not_le_of_gt hδ)]

theorem actual_adaptive_witnesses (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ,∀ Z : ℝ,Z₀≤Z → ∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀ u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) → ∀ q : Row→ℝ,
          Nonempty (∀ u,SupportedWitness (χ u) (Z^d) a ε (cutoff (2*a-1) (q u))
            (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := actual_supported_witness_family dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label _ χ hχ a i hi ha ha' hnext hcurrent hQ q
  have hδ : 0≤2*a-1 := by linarith
  exact ⟨fun u => (Classical.choice (hZ₀ Z hZ d hd hd' χ hχ a i hi ha ha'
    hnext hcurrent hQ (cutoff (2*a-1) (q u))
      (cutoff_bounds (2*a-1) (q u) hδ).1 (cutoff_bounds (2*a-1) (q u) hδ).2)) u⟩

end SevenEighths.HeckeDetectorAdaptiveCutoff

end

end OAI

end Source1823

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorAmplitudeFirst.lean; sha256: d787f9d44bd8e3840aac72c2e26cd133cf0bc2e631fce7229c9e4f0623c7ca12 -/
section Source1824
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorAmplitudeFirst
open HeckeFamily HeckeDetectorSupportedWitness HeckeDetectorFiberPartition
open HeckeDetectorPhysicalSelection HeckeDetectorAdaptiveCutoff

def amplitudeRows {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots cap mesh) : Finset Row :=
  rows.filter (fun u => amplitudeLabel slots U cap mesh hm widths physical u=bin)

def rowMean {Row Slot : Type*} (slots : Finset Slot) (U cap mesh : ℝ)
    (widths : Slot→ℝ) (physical : Row→Slot→ℂ) (u : Row) : ℝ :=
  weightedMean slots widths (fun s => HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s))

def classMean {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (widths : Slot→ℝ) (bin : BinLabel slots cap mesh) : ℝ :=
  weightedMean slots widths (binValue slots cap mesh bin)

theorem rowMean_eq {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots cap mesh) (u : Row)
    (hu : u∈amplitudeRows rows slots U cap mesh hm widths physical bin) :
    rowMean slots U cap mesh widths physical u=classMean slots cap mesh widths bin := by
  have he := (Finset.mem_filter.mp hu).2
  unfold rowMean classMean weightedMean
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hv := congrArg (fun f : BinLabel slots cap mesh => (f ⟨s,hs⟩).val) he
  have hval : HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s)=
      binValue slots cap mesh bin s := by
    simpa only [amplitudeLabel,binValue,dite_eq_left hs] using hv
  exact congrArg (fun x => widths s*x) hval

theorem classMean_bounds {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U δ mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots (δ/2) mesh) (hδ : 0≤δ)
    (hw : ∀ s∈slots,0≤widths s) (hsupply : 0<∑ s∈slots,widths s)
    (hne : (amplitudeRows rows slots U (δ/2) mesh hm widths physical bin).Nonempty) :
    0≤classMean slots (δ/2) mesh widths bin ∧ classMean slots (δ/2) mesh widths bin≤δ/2 := by
  obtain ⟨u,hu⟩ := hne
  rw [←rowMean_eq rows slots U (δ/2) mesh hm widths physical bin u hu]
  apply weightedMean_bounds slots widths _ δ hw hsupply
  intro s hs
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

def recut {Label : Type*} {χ : Label→Character} {U a ε t t' T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ U a ε t T allowance i) (he : t=t') :
    SupportedWitness χ U a ε t' T allowance i := he ▸ w

theorem recut_values {Label : Type*} {χ : Label→Character} {U a ε t t' T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ U a ε t T allowance i) (he : t=t') :
    (recut w he).label=w.label ∧ (recut w he).zero=w.zero ∧
    (recut w he).left=w.left ∧ (recut w he).right=w.right ∧
    (recut w he).nu=w.nu ∧ (recut w he).r=w.r ∧ (recut w he).m=w.m := by
  cases he
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def classWitness {Row Label Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (U a ε T allowance mesh : ℝ) (i : ℕ) (hm : 0<mesh)
    (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (w : ∀ u : rows,SupportedWitness (χ u) U a ε
      (cutoff (2*a-1) (rowMean slots U ((2*a-1)/2) mesh widths physical u)) T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) mesh)
    (u : amplitudeRows rows slots U ((2*a-1)/2) mesh hm widths physical bin) :
    SupportedWitness (χ u) U a ε
      (cutoff (2*a-1) (classMean slots ((2*a-1)/2) mesh widths bin)) T allowance i :=
  recut (w ⟨u.val,(Finset.mem_filter.mp u.property).1⟩)
    (congrArg (cutoff (2*a-1))
      (rowMean_eq rows slots U ((2*a-1)/2) mesh hm widths physical bin u.val u.property))

theorem card_eq_sum_amplitudeRows {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ) :
    rows.card=∑ bin : BinLabel slots cap mesh,(amplitudeRows rows slots U cap mesh hm widths physical bin).card := by
  exact Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
    (f:=amplitudeLabel slots U cap mesh hm widths physical) (by intro u hu; exact Finset.mem_univ _)

end SevenEighths.HeckeDetectorAmplitudeFirst

end

end OAI

end Source1824

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorClassBudget.lean; sha256: 5e6a0ec5c45c2204143d2a224f460e629de2038e958141fff469f09b8214e655 -/
section Source1825
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.HeckeDetectorClassBudget
open HeckeDetectorFiberPartition HeckeDetectorWitnessRows

def alphabetBound (mesh : ℝ) : ℕ := 2+(⌈(1/2 : ℝ)/mesh⌉+1 : ℤ).toNat

theorem labels_card_le (cap mesh : ℝ) (hcap : cap≤1/2) (hm : 0<mesh) :
    (HeckePrimeAmplitudeBins.labels cap mesh).card≤alphabetBound mesh := by
  have hceil : ⌈cap/mesh⌉≤⌈(1/2 : ℝ)/mesh⌉ :=
    Int.ceil_mono (div_le_div_of_nonneg_right hcap hm.le)
  have hsub : Finset.Icc (0 : ℤ) ⌈cap/mesh⌉ ⊆ Finset.Icc (0 : ℤ) ⌈(1/2 : ℝ)/mesh⌉ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans hceil⟩
  have h1 := Finset.card_insert_le (0 : ℝ)
    (insert cap ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ))))
  have h2 := Finset.card_insert_le cap
    ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ)))
  have h3 := Finset.card_image_le (s:=Finset.Icc (0 : ℤ) ⌈cap/mesh⌉)
    (f:=fun n : ℤ => mesh*(n : ℝ))
  have h4 := Finset.card_le_card hsub
  simp only [Int.card_Icc,sub_zero] at h4 h3
  unfold HeckePrimeAmplitudeBins.labels alphabetBound
  omega

theorem bin_card_le {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (hcap : cap≤1/2) (hm : 0<mesh) :
    Fintype.card (BinLabel slots cap mesh)≤(alphabetBound mesh)^slots.card := by
  simpa only [BinLabel,Fintype.card_fun,Fintype.card_coe] using
    Nat.pow_le_pow_left (labels_card_le cap mesh hcap hm) slots.card

theorem dyadic_cost_eventually (η : ℝ) (hη : 0<η) :
    ∃ K : ℝ,0≤K ∧ ∀ᶠ U : ℝ in atTop,(dyadicLength U : ℝ)^2≤K*U^η := by
  let K := 625/(Real.log 2)^2
  have hK : 0≤K := by positivity
  have hlog := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hη).bound (by norm_num : (0 : ℝ)<1)
  refine ⟨K,hK,?_⟩
  filter_upwards [hlog,eventually_ge_atTop (2 : ℝ)] with U hlog hU
  have hUp : 0<U := by linarith
  have hs : (Real.log U)^2≤U^η := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log U)),
      abs_of_nonneg (Real.rpow_nonneg hUp.le _),one_mul] using hlog
  have hd := HeckeDetectorBudget.source_pair_count_bound U hU
  calc
    (dyadicLength U : ℝ)^2 ≤ 625*(Real.logb 2 U)^2 := hd
    _ = K*(Real.log U)^2 := by unfold K Real.logb; ring
    _ ≤ K*U^η := mul_le_mul_of_nonneg_left hs hK

end SevenEighths.HeckeDetectorClassBudget

end

end OAI

end Source1825

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorFixedAmplitudeCount.lean; sha256: baabf13565f77b3ae8bde6808c3ccab92d91499c967c05e474d00fb02768a447 -/
section Source1826
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorFixedAmplitudeCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

lemma fiber_mean_eq (B : Batch M H Label Slot U a ε tstar T allowance i) (q : ℝ)
    (hq : ∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
      (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows bin j J K).Nonempty) : (B.fiber bin j J K hne).q=q := by
  let u := hne.choose
  have hu : u ∈ B.fiberRows bin j J K := hne.choose_spec
  have huR : u∈B.rows := (Finset.mem_filter.mp hu).1
  rw [←hq u huR]
  unfold Fiber.q rowMean weightedMean
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  exact congrArg (fun g=>B.widths s*g) ((B.fiber bin j J K hne).fixed_bin u hu s hs).symm

lemma batch_mean_bounds (B : Batch M H Label Slot U a ε tstar T allowance i)
    (hne : B.rows.Nonempty) (ha : 1/2≤a) (q : ℝ)
    (hq : ∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
      (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) :
    0≤q ∧ q≤(2*a-1)/2 := by
  obtain ⟨u,hu⟩ := hne
  rw [←hq u hu]
  apply weightedMean_bounds B.slots B.widths _ (2*a-1)
    (fun s hs=>(B.widths_pos s hs).le) (by linarith [B.supply])
  intro s hs
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

theorem fixed_amplitude_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε tstar T allowance Δ ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      1≤tstar → tstar≤3/2 → 0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i),
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(max (shortExponent (2*a-1) (q/(2*a-1)) tstar) (longExponent (2*a-1) tstar)+
          Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := HeckeDetectorCountFromMoments.count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε tstar T allowance Δ ν C height q i hU ha hd hε hε' ht ht' hΔ hΔ' hν hC hh hf Label Slot _ B hq moments
  have hb := B.card_bound (fiberConstant C height K₀)
    (fun _=>max (shortExponent (2*a-1) (q/(2*a-1)) tstar) (longExponent (2*a-1) tstar)+
      Δ/4+159*ε+εm+B.mesh+7*ν)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hne
      have hc' := hcount a ε tstar T allowance Δ ν C height i hU ha hd hε hε' ht ht' hΔ hΔ' hν hC hh hf
        (B.fiber bin j J K hne) (moments bin j J K hne)
      rw [fiber_mean_eq B q hq bin j J K hne] at hc'
      exact hc')
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
end SevenEighths.HeckeDetectorFixedAmplitudeCount

end

end OAI

end Source1826

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorHighCount.lean; sha256: 38232c049a7d7440e58f4900c79e971e42a64ba46dcf3a6f35bbfade355f98b6 -/
section Source1827
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorHighCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorRowCount

theorem high_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height : ℝ) (i : ℕ),
      1<U → 5/6≤2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} (F : Fiber M H Label Slot U a ε (3/2) T allowance i),
      Moments F Δ c κ C height εm →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε T allowance Δ C height i hU ha ha' hε hεsmall hC hh hf Label Slot F moments
  have hgeom := F.lengths hU
  have hr0 : 0≤F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r≤2 := by linarith [hgeom.2.1]
  obtain ⟨hconst,_,_,hconstI⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have hi := hamp F.rows F.family a ε (3/2) T allowance i hU (by linarith)
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.inverse_raw
  have hb : (F.rows.card : ℝ)≤fiberConstant C height K₀*
      U^(max 1 ((1+5*F.r)/6)-(2*a-1)*F.r+(2*ε+εm)) := by
    apply hi.trans
    convert mul_le_mul_of_nonneg_right hconstI
      (Real.rpow_nonneg (zero_lt_one.trans hU).le
        (max 1 ((1+5*F.r)/6)-(2*a-1)*F.r+2*ε+εm)) using 1 <;> congr 2; ring
  have hout := high_bin_count hconst hU.le ha (show 2*a-1≤1 by linarith)
    (show 0≤76*ε by positivity) (show 1-76*ε≤F.r by linarith [hgeom.2.2.2.1]) hb
  convert hout using 1; congr 2; ring

end SevenEighths.HeckeDetectorHighCount

end

end OAI

end Source1827

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorHighBatchCount.lean; sha256: e89b70a440ff42d51af62ab0b5ecee37c2009fa4acf59a828adca8b5d762733b -/
section Source1828
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorHighBatchCount
open HeckeDetectorBatch
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorRowCount

theorem high_batch_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height : ℝ) (i : ℕ),
      1<U → 5/6≤2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (3/2) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := HeckeDetectorHighCount.high_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ C height i hU ha ha' hε hε' hC hh hf Label Slot _ B moments
  have hb := B.card_bound (fiberConstant C height K₀) (fun _=>1-(2*a-1)+78*ε+εm)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hne
      exact hcount a ε T allowance Δ C height i hU ha ha' hε hε' hC hh hf
        (B.fiber bin j J K hne) (moments bin j J K hne))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
end SevenEighths.HeckeDetectorHighBatchCount

end

end OAI

end Source1828

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CubeCalibration.lean; sha256: badf6f3e00ef5de00c14ce06e14e4d71dc1fdc5ba6dcc105fb8a032b0496073e -/
section Source1829
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma centralCubeIntegral_calibration_zero {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=0 := by
  simp [centralCubeIntegral,continuedRowOnLines,continuedPhysicalRowKernel,hc]

lemma cubeWeightedRow_calibration_zero {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z a e H : ℝ) :
    cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H=0 := by
  funext t
  simp [cubeWeightedRow,weightedRowOnLines,calibratedTupleValue,hc]

theorem finiteCentralCubeRows_filter_calibration {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e : ℝ) (a H : FreeRow→ℝ) :
    finiteCentralCubeRows S hS hmax η (R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0))
      T hT W Yp W0 W1 X Y Z e a H=
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H := by
  unfold finiteCentralCubeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp [hc,centralCubeIntegral_calibration_zero S hS hmax _ _ η u hc]
  · simp [hc]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1829

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CubeBinPartition.lean; sha256: f8df56cd7678abc578b9b4b92e18009b6f57793ad81b7e69ba47a588615df618 -/
section Source1830
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (i k : ℕ) : Finset FreeRow :=
  R.filter (fun u=>idx u=i ∧ grid u=k)

@[simp] lemma mem_cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (i k : ℕ) (u : FreeRow) :
    u∈cubeBinRows R idx grid i k ↔ u∈R ∧ idx u=i ∧ grid u=k := by simp [cubeBinRows]

lemma sum_cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u≤n ∧ grid u≤m) (f : FreeRow→ℂ) :
    (∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),∑u∈cubeBinRows R idx grid i k,f u)=∑u∈R,f u := by
  have hm : ∀u∈R,(idx u,grid u)∈(Finset.range (n+1)).product (Finset.range (m+1)) := by
    intro u hu
    simpa only [Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range] using
      And.intro (Nat.lt_succ_of_le (hlabel u hu).1) (Nat.lt_succ_of_le (hlabel u hu).2)
  have hs := Finset.sum_fiberwise_of_maps_to hm f
  simpa only [Finset.product_eq_sprod,Finset.sum_product,Prod.mk.injEq,cubeBinRows] using hs

theorem finiteCentralCubeRows_bin_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B : ℝ) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u≤n ∧ grid u≤m) :
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*B)=
    ∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),
      finiteCentralCubeRows S hS hmax η (cubeBinRows R idx grid i k) T hT W Yp W0 W1 X Y Z e
        (fun _=>51/100+e*k) (fun _=>(3*i+1:ℕ)*B) := by
  unfold finiteCentralCubeRows
  rw [←sum_cubeBinRows R idx grid n m hlabel]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro u hu
  rcases (mem_cubeBinRows R idx grid i k u).mp hu with ⟨hu,hi,hk⟩
  simp only [hi,hk]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1830

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/CubeCommonProfile.lean; sha256: 949febab3c7afb9e6cbcf316464e3a76e5b10075d1de0e9ee60c63ffd2e6e9e7 -/
section Source1831
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def cubeArithmeticSum {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (a e : ℝ) (t : HeightSpace) : ℂ :=
  ∑u∈R,frequencyWeight ((17/50:ℂ)+t.1.2*Complex.I) ⟨u.val,u.property.1⟩*
    ∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hT i _ (P i).property) W Yp
      (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      ((17/50:ℂ)+t.1.2*Complex.I)

theorem cube_sum_eq_common_profile {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) (t : HeightSpace) :
    (∑u∈R,∑P:(∀i,T i),cubeWeightedRow S hS hmax (fun i=>(P i).val)
      (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z a e H t)=
    {v : HeightSpace | (|v.1.1|≤H ∧ |v.2|≤H) ∧ |v.1.2|≤H}.indicator
      (fun v=>sourceMellinWeight W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+v.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+v.2*Complex.I)
        ((17/50:ℂ)+v.1.2*Complex.I)*cubeArithmeticSum S hS hmax η R T hT W Yp a e v) t := by
  by_cases ht : (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H
  · simp [cubeWeightedRow,ht,weightedRowOnLines,cubeArithmeticSum,
      Finset.mul_sum,mul_assoc]
  · simp [cubeWeightedRow,ht]

theorem cube_common_profile_integral {K : ℕ} {ι : Type*} [Fintype ι]
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1' : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}.indicator
      (fun t=>sourceMellinWeight W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
        ((17/50:ℂ)+t.1.2*Complex.I)*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
    Integrable F heightMeasure ∧
      finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,F t ∂heightMeasure) := by
  have hh := finiteCentralCubeRows_eq_integral e he he' S hS hmax hfirst η R hR T hT
    (fun _=>a) (fun _=>B) (fun _=>H) (fun _=>i) ψ
    (fun u hu=>⟨ha,ha1,hB,hH,hbin u hu⟩) W Yp W0 W1 a0 b0 a1 b1 ha0 ha1' hW0 hW1 X Y Z hX hY hZ
  dsimp only at hh ⊢
  simpa only [cube_sum_eq_common_profile] using hh

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1831

/- Original source: OAI/NumberTheory/DirichletL/Detector/CentralCubeNorm.lean; sha256: ff41bad5e590181d0cb346745f56f6a32f69cfe9f018f0d5a72baec8261dedd2 -/
section Source1832
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma cubeArithmeticSum_norm {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (a e : ℝ) (t : HeightSpace)
    (A : FreeRow→ℝ)
    (hA : ∀u∈R,‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
      (fun j=>hT j _ (P j).property) W Yp
      (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      ((17/50:ℂ)+t.1.2*Complex.I)‖≤A u) :
    ‖cubeArithmeticSum S hS hmax η R T hT W Yp a e t‖≤
      ∑u∈R,rowNorm u^(-(17/50:ℝ))*A u := by
  unfold cubeArithmeticSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu=>?_)
  rw [norm_mul,frequencyWeight_ideal_norm]
  have hz : (((17/50:ℂ)+t.1.2*Complex.I).re:ℝ)=17/50 := by simp
  rw [hz]
  exact mul_le_mul_of_nonneg_left (hA u hu) (Real.rpow_nonneg (by positivity) _)

theorem actual_common_cube_norm (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀{K : ℕ} {ι : Type*} [Fintype ι]
      (e a B H : ℝ) (i : ℕ),0<e → e<1/1000 → 51/100≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
    ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal),
    FirstTail (4*e) S → ∀(η : Character) (R : Finset FreeRow), (∀u∈R,u.val≠1) →
    ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
      (ψ : FreeRow→ι→Character),
      (∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e) →
    ∀(W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (X Y Z : ℝ),0<X → 0<Y → 0<Z →
    ∀A : FreeRow→ℝ,(∀u∈R,0≤A u) →
      (∀t : HeightSpace,(|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H → ∀u∈R,
        ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=>hT j _ (P j).property) W Yp
          (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
          ((17/50:ℂ)+t.1.2*Complex.I)‖≤A u) →
      ‖finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)‖≤
        C*(X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e))*
          (∑u∈R,rowNorm u^(-(17/50:ℝ))*A u) := by
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    0 2 (17/50) (17/50) (-1) 1 (by norm_num) 0
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)^3‖*D,mul_pos (norm_pos_iff.mpr (by
    apply pow_ne_zero
    exact_mod_cast (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))) hD,?_⟩
  intro K ι _ e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR T hT ψ hbin W Yp X Y Z hX hY hZ A hA hb
  let E : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  let V : HeightSpace→ℂ := fun t=>sourceMellinWeight W0 W1 X Y Z
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
    ((17/50:ℂ)+t.1.2*Complex.I)
  let F := E.indicator (fun t=>V t*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
  let mass : ℝ := ∑u∈R,rowNorm u^(-(17/50:ℝ))*A u
  have hm : 0≤mass := Finset.sum_nonneg fun u hu=>mul_nonneg (Real.rpow_nonneg (by unfold rowNorm;positivity) _) (hA u hu)
  let scale : ℝ := X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e)
  have hs : 0≤scale := by dsimp [scale];positivity
  have hv (t : HeightSpace) : ‖V t‖=scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ := by
    have hxre : (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I).re=a+16*e := by simp
    have hwre : (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I).re=1-a-6*e := by simp
    have hzre : ((17/50:ℂ)+t.1.2*Complex.I).re=17/50 := by simp
    dsimp [V]
    rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ,hxre,hwre,hzre]
    have hs0 : X^(1/2-(17/50:ℝ))*Z^((a+16*e)+17/50-1)*Y^((1-a-6*e)-1)=scale := by
      rw [show (1/2-17/50:ℝ)=4/25 by norm_num,
        show (a+16*e)+17/50-1=a+16*e-33/50 by ring,
        show (1-a-6*e)-1=-a-6*e by ring]
    rw [hs0]
    simp [onLines]
  have hp := hprofile (a+16*e) (by constructor <;> linarith) (17/50) ⟨le_rfl,le_rfl⟩
    (1-a-6*e) (by constructor <;> linarith)
  simp only [pow_zero,one_mul] at hp
  have hg : Integrable (fun t=>scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass) heightMeasure :=
    (hp.1.const_mul scale).mul_const mass
  have hf := cube_common_profile_integral e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR
    T hT ψ hbin W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  change Integrable F heightMeasure ∧ _ at hf
  have hb' (t : HeightSpace) : ‖F t‖≤scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass := by
    by_cases ht : t∈E
    · dsimp only [F]
      rw [Set.indicator_of_mem ht,norm_mul,hv]
      exact mul_le_mul_of_nonneg_left (cubeArithmeticSum_norm S hS hmax η R T hT W Yp a e t A (hb t ht)) (by positivity)
    · dsimp only [F]
      rw [Set.indicator_of_notMem ht,norm_zero]
      positivity
  rw [hf.2,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(∫t,scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (integral_mono hf.1.norm hg hb')) (norm_nonneg _)
    _ = ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*(∫t,‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ ∂heightMeasure)*mass) := by
      rw [integral_mul_const,integral_const_mul]
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*D*mass) := by gcongr;exact hp.2
    _ = _ := by dsimp [scale,mass];ring

theorem actual_common_cube_aggregate_norm (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀{K : ℕ} {ι : Type*} [Fintype ι]
      (e a B H : ℝ) (i : ℕ),0<e → e<1/1000 → 51/100≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
    ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal),
    FirstTail (4*e) S → ∀(η : Character) (R : Finset FreeRow), (∀u∈R,u.val≠1) →
    ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
      (ψ : FreeRow→ι→Character),
      (∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e) →
    ∀(W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (X Y Z : ℝ),0<X → 0<Y → 0<Z →
    ∀A : ℝ,0≤A →
      (∀t : HeightSpace,(|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H →
        ‖cubeArithmeticSum S hS hmax η R T hT W Yp a e t‖≤A) →
      ‖finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)‖≤
        C*(X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e))*
          A := by
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    0 2 (17/50) (17/50) (-1) 1 (by norm_num) 0
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)^3‖*D,mul_pos (norm_pos_iff.mpr (by
    apply pow_ne_zero
    exact_mod_cast (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))) hD,?_⟩
  intro K ι _ e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR T hT ψ hbin W Yp X Y Z hX hY hZ A hA hb
  let E : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  let V : HeightSpace→ℂ := fun t=>sourceMellinWeight W0 W1 X Y Z
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
    ((17/50:ℂ)+t.1.2*Complex.I)
  let F := E.indicator (fun t=>V t*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
  let mass : ℝ := A
  have hm : 0≤mass := hA
  let scale : ℝ := X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e)
  have hs : 0≤scale := by dsimp [scale];positivity
  have hv (t : HeightSpace) : ‖V t‖=scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ := by
    have hxre : (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I).re=a+16*e := by simp
    have hwre : (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I).re=1-a-6*e := by simp
    have hzre : ((17/50:ℂ)+t.1.2*Complex.I).re=17/50 := by simp
    dsimp [V]
    rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ,hxre,hwre,hzre]
    have hs0 : X^(1/2-(17/50:ℝ))*Z^((a+16*e)+17/50-1)*Y^((1-a-6*e)-1)=scale := by
      rw [show (1/2-17/50:ℝ)=4/25 by norm_num,
        show (a+16*e)+17/50-1=a+16*e-33/50 by ring,
        show (1-a-6*e)-1=-a-6*e by ring]
    rw [hs0]
    simp [onLines]
  have hp := hprofile (a+16*e) (by constructor <;> linarith) (17/50) ⟨le_rfl,le_rfl⟩
    (1-a-6*e) (by constructor <;> linarith)
  simp only [pow_zero,one_mul] at hp
  have hg : Integrable (fun t=>scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass) heightMeasure :=
    (hp.1.const_mul scale).mul_const mass
  have hf := cube_common_profile_integral e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR
    T hT ψ hbin W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  change Integrable F heightMeasure ∧ _ at hf
  have hb' (t : HeightSpace) : ‖F t‖≤scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass := by
    by_cases ht : t∈E
    · dsimp only [F]
      rw [Set.indicator_of_mem ht,norm_mul,hv]
      exact mul_le_mul_of_nonneg_left (hb t ht) (by positivity)
    · dsimp only [F]
      rw [Set.indicator_of_notMem ht,norm_zero]
      positivity
  rw [hf.2,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(∫t,scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (integral_mono hf.1.norm hg hb')) (norm_nonneg _)
    _ = ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*(∫t,‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ ∂heightMeasure)*mass) := by
      rw [integral_mul_const,integral_const_mul]
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*D*mass) := by gcongr;exact hp.2
    _ = _ := by dsimp [scale,mass];ring
end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1832

/- Original source: OAI/NumberTheory/DirichletL/Detector/CentralExponent.lean; sha256: c138e38592cb202bbc4c13021d65378163c77988ebda575a2af39c6961b92a83 -/
section Source1833
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeCentralExponent

def sourceExponent (a d R q : ℝ) : ℝ :=
  (17/48)*(1/2-17/50)+a+17/50-1-a*(23/48)-d*(17/50)+d*R+
    d*(a-1/2)+(1/6)*(17/50-1/2+q)

def relativeExponent (δ d R q : ℝ) : ℝ :=
  -1/48+(2/3)*δ+q/6-(13/16)*(1-R)+(d-13/16)*(R+δ/2-17/50)

lemma original_exponent_identity (a d R q : ℝ) :
    sourceExponent a d R q=3/16+relativeExponent (2*a-1) d R q := by
  unfold sourceExponent relativeExponent
  ring

lemma frequency_slope_bounds (δ R : ℝ) (_hδ : 0≤δ) (hδ1 : δ≤1)
    (hRlo : 1-δ≤R) (hRhi : R≤139/96) :
    4/25≤R+δ/2-17/50 ∧ R+δ/2-17/50≤2 := by
  constructor <;> linarith

lemma relative_extend (δ d R q ζ : ℝ) (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    relativeExponent δ d R q≤relativeExponent δ (13/16) R q+2*ζ := by
  have hh := mul_le_mul_of_nonneg_right (show d-13/16≤ζ by linarith) hslo
  have hh' := mul_le_mul_of_nonneg_left hshi hζ
  unfold relativeExponent
  nlinarith

lemma balanced_source_margin (δ x R Δ loss ζ d : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤5/6) (hx : 0≤x) (hx1 : x≤1/2)
    (hR : R≤Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    sourceExponent ((1+δ)/2) d R (δ*x)-(3/16+Δ)≤
      -49/440640-(51/64)*Δ+(13/16)*loss+2*ζ := by
  have hb := Endpoint.balanced_endpoint_margin hδ hδ1
    (show 0≤1/2-x by linarith) (show 1/2-x≤1/2 by linarith)
  have he := relative_extend δ d R (δ*x) ζ hζ hd hslo hshi
  rw [original_exponent_identity]
  have hid : 2*((1+δ)/2)-1=δ := by ring
  rw [hid]
  unfold Endpoint.balancedExponent at hb
  unfold relativeExponent at he ⊢
  nlinarith

lemma high_source_margin (δ R q Δ loss ζ d : ℝ)
    (hq : q≤δ/2) (hR : R≤1-δ+loss)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    sourceExponent ((1+δ)/2) d R q-(3/16+Δ)≤
      -1/48-δ/16-Δ+(13/16)*loss+2*ζ := by
  have he := relative_extend δ d R q ζ hζ hd hslo hshi
  rw [original_exponent_identity]
  have hid : 2*((1+δ)/2)-1=δ := by ring
  rw [hid]
  unfold relativeExponent at he ⊢
  nlinarith

lemma floor_source_margin (q Δ ζ d : ℝ) (hq : q≤1/100)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ) :
    sourceExponent (51/100) d 1 q-(3/16+Δ)≤-7/1200-Δ+2*ζ := by
  have he := relative_extend (1/50) d 1 q ζ hζ hd (by norm_num) (by norm_num)
  rw [original_exponent_identity]
  norm_num only at *
  unfold relativeExponent at he ⊢
  nlinarith

lemma intermediate_source_margin (δ q Δ d : ℝ) (_hδ : 0≤δ) (hδ1 : δ≤5/6)
    (hq : q≤δ/2) (hd : d≤1/2) :
    sourceExponent ((1+δ)/2) d (76/75-(2/3)*δ) q-(3/16+Δ)≤-49/14400-Δ := by
  have hs : 0≤(76/75-(2/3)*δ)+δ/2-17/50 := by linarith
  have hm := mul_le_mul_of_nonneg_right hd hs
  unfold sourceExponent
  nlinarith

def realLoss (N : ℕ) (d e eps heightLoss mesh : ℝ) : ℝ :=
  (105/8)*e+12*d*e+d*eps*(N+8)+heightLoss+mesh/6

lemma realLoss_bound (N : ℕ) (d e eps heightLoss mesh : ℝ)
    (hd : d≤1) (he : 0≤e) (heps : 0≤eps) :
    realLoss N d e eps heightLoss mesh≤26*e+(N+8)*eps+heightLoss+mesh/6 := by
  have h1 := mul_le_mul_of_nonneg_right hd he
  have h2 := mul_le_mul_of_nonneg_right hd (show 0≤eps*(N+8) by positivity)
  unfold realLoss
  nlinarith

lemma physical_scale_identity (Z a e : ℝ) (hZ : 0<Z) :
    (Z^(17/48:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(23/48:ℝ))^(-a-6*e)=
      Z^((25/48)*a-181/300+(105/8)*e) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring
end SevenEighths.ProbeCentralExponent

end

end OAI

end Source1833

/- Original source: OAI/NumberTheory/DirichletL/Detector/CentralDyadicWeight.lean; sha256: 731176a3f226ff14ad0eea1ab1f73c8cd8c81d870dd6672676298e1abcdd0f22 -/
section Source1834
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

lemma dyadic_weighted_rows_card (α r C U B : ℝ) (hC : 0≤C) (hU : 0<U)
    (R : Finset FreeRow) (hcard : (R.card:ℝ)≤B)
    (hR : ∀u∈R,U≤rowNorm u ∧ rowNorm u≤2*U)
    (F : FreeRow→ℝ) (hF : ∀u∈R,F u≤C*rowNorm u^α)
    (z : ℂ) (hz : z.re=r) :
    (∑u∈R,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u)≤
      B*C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r) := by
  have hA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 (α-r) (by norm_num)
  calc
    _ ≤ ∑u∈R,C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r) := by
      apply Finset.sum_le_sum
      intro u hu
      have hN : 0<rowNorm u := hU.trans_le (hR u hu).1
      rw [frequencyWeight_ideal_norm,hz]
      change rowNorm u^(-r)*F u≤_
      calc
        _ ≤ rowNorm u^(-r)*(C*rowNorm u^α) :=
          mul_le_mul_of_nonneg_left (hF u hu) (Real.rpow_nonneg hN.le _)
        _ = C*rowNorm u^(α-r) := by
          rw [show α-r=(-r)+α by ring,Real.rpow_add hN]; ring
        _ ≤ _ := by
          have hb := ProbeSelectedPrimeSums.annular_rpow 1 2 U (rowNorm u) (α-r)
            (by norm_num) (by norm_num) hU (by simpa using (hR u hu).1) (hR u hu).2
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC
    _ = (R.card:ℝ)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r)) := by simp
    _ ≤ B*(C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

lemma annular_power_uniform (p pmax : ℝ) (hp : p≤pmax) :
    ProbeSelectedPrimeSums.annularPower 1 2 p≤max 1 ((2:ℝ)^pmax) := by
  unfold ProbeSelectedPrimeSums.annularPower
  rw [Real.one_rpow]
  exact max_le_max le_rfl (Real.rpow_le_rpow_of_exponent_le (by norm_num) hp)

def mixedSourceExponent (a v d R q : ℝ) : ℝ :=
  ProbeCentralExponent.sourceExponent a v R q+(d-v)*R

lemma mixed_physical_exponent (Z a v d R q e eps loss mesh : ℝ) (N : ℕ)
    (hZ : 0<Z) :
    ((Z^(17/48:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(23/48:ℝ))^(-a-6*e))*
      ((Z^d)^R*(Z^v)^(a-1/2+12*e+eps*(N+8)-17/50)*Z^(-2/75+q/6+mesh/6+loss))=
    Z^(mixedSourceExponent a v d R q+ProbeCentralExponent.realLoss N v e eps loss mesh) := by
  rw [ProbeCentralExponent.physical_scale_identity Z a e hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  unfold mixedSourceExponent ProbeCentralExponent.sourceExponent ProbeCentralExponent.realLoss
  ring

lemma mixed_source_slack (a v d R q μ Rmax : ℝ)
    (hR : 0≤R) (hRmax : R≤Rmax) (hμ : 0≤μ) (hd : d-v≤μ) :
    mixedSourceExponent a v d R q≤ProbeCentralExponent.sourceExponent a v R q+μ*Rmax := by
  have h1 := mul_le_mul_of_nonneg_right hd hR
  have h2 := mul_le_mul_of_nonneg_left hRmax hμ
  unfold mixedSourceExponent
  linarith

lemma dyad_conductor_margin (Z v margin : ℝ) (hZ : 0<Z) (hmargin : 2≤Z^margin)
    (R : Finset FreeRow) (hR : ∀u∈R,rowNorm u≤2*Z^v) :
    ∀u∈R,rowNorm u≤Z^((v+2*margin)-margin) := by
  intro u hu
  calc
    rowNorm u≤2*Z^v := hR u hu
    _ ≤ Z^margin*Z^v := mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring
end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1834

/- Original source: OAI/NumberTheory/DirichletL/Detector/CentralMixedMargins.lean; sha256: 635ed51704661906d6c751bed052cfbacde4d5d9207179be65d328877f7d034d -/
section Source1835
namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeDetectorRowCount ProbeCentralExponent

lemma balanced_count_range (δ x Δ loss : ℝ) (hδ : 0≤δ) (hd : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8)
    (hl : 0≤loss) (hl' : loss≤1/32) :
    let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
    1-δ≤R ∧ R≤3/2 := by
  have ht := balanced_cutoff_bounds hδ hd hx hx'
  have hp0 := mul_nonneg (show 0≤5/6-δ by linarith) (show 0≤Endpoint.balancedCutoff δ (1/2-x)-1 by linarith)
  have hp1 := mul_le_mul_of_nonneg_left ht.2 (show 0≤5/6-δ by linarith)
  dsimp only
  unfold Endpoint.balancedRowCount
  constructor <;> nlinarith

lemma balanced_mixed_margin (δ x Δ loss ζ μ v d : ℝ)
    (hδ : 0≤δ) (hd : δ≤5/6) (hx : 0≤x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hl : 0≤loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ) :
    let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
    mixedSourceExponent ((1+δ)/2) v d R (δ*x)-(3/16+Δ)≤
      -49/440640-(51/64)*Δ+(13/16)*loss+2*ζ+(3/2)*μ := by
  dsimp only
  let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
  have hr := balanced_count_range δ x Δ loss hδ hd hx hx' hΔ hΔ' hl hl'
  have hlo : 0≤R+δ/2-17/50 := by dsimp [R]; linarith [hr.1]
  have hhi : R+δ/2-17/50≤2 := by dsimp [R]; linarith [hr.2]
  have hm := balanced_source_margin δ x R Δ loss ζ v hδ hd hx hx' le_rfl hζ hv hlo hhi
  have hs := mixed_source_slack ((1+δ)/2) v d R (δ*x) μ (3/2)
    (by dsimp [R];linarith [hr.1]) hr.2 hμ hdv
  linarith

lemma high_mixed_margin (δ q Δ loss ζ μ v d : ℝ)
    (hδ : 5/6≤δ) (hd : δ≤1) (hq : q≤δ/2)
    (hl : 0≤loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ) :
    mixedSourceExponent ((1+δ)/2) v d (1-δ+loss) q-(3/16+Δ)≤
      -1/48-δ/16-Δ+(13/16)*loss+2*ζ+μ := by
  have hlo : 0≤(1-δ+loss)+δ/2-17/50 := by linarith
  have hhi : (1-δ+loss)+δ/2-17/50≤2 := by linarith
  have hm := high_source_margin δ (1-δ+loss) q Δ loss ζ v hq le_rfl hζ hv hlo hhi
  have hs := mixed_source_slack ((1+δ)/2) v d (1-δ+loss) q μ 1
    (by linarith) (by linarith) hμ hdv
  linarith

lemma balanced_mixed_saving (δ x Δ loss ζ μ v d other saving : ℝ)
    (hδ : 0≤δ) (hd : δ≤5/6) (hx : 0≤x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hl : 0≤loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ)
    (hbudget : (13/16)*loss+2*ζ+(3/2)*μ+other+saving≤49/440640) :
    mixedSourceExponent ((1+δ)/2) v d
      (Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss) (δ*x)+other≤3/16+Δ-saving := by
  have hm := balanced_mixed_margin δ x Δ loss ζ μ v d hδ hd hx hx' hΔ hΔ' hl hl' hζ hv hμ hdv
  linarith
end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1835

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/NonfloorCount.lean; sha256: a52ccf6c3e635d3305336b6ede7b6b82271c0b8606178e410be3110e632734af -/
section Source1836
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff

theorem balanced_adaptive_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+
          Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    HeckeDetectorFixedAmplitudeCount.fixed_amplitude_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ ν C height q i hU ha hd hε hε' hΔ hΔ' hν hC hh hf Label Slot _ B hne hq hmom
  have hδ : 0<2*a-1 := by linarith
  have hqb := HeckeDetectorFixedAmplitudeCount.batch_mean_bounds B hne (by linarith) q hq
  have hx : 0≤q/(2*a-1) := div_nonneg hqb.1 hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
  have ht := cutoff_bounds (2*a-1) q hδ.le
  have hc' := hcount a ε (cutoff (2*a-1) q) T allowance Δ ν C height q i
    hU ha hd hε hε' ht.1 ht.2 hΔ hΔ' hν hC hh hf B hq hmom
  have he : max (shortExponent (2*a-1) (q/(2*a-1)) (cutoff (2*a-1) q))
      (longExponent (2*a-1) (cutoff (2*a-1) q)) =
      Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1)) := by
    rw [cutoff_eq_balanced (2*a-1) q hδ hd hqb.1 hqb.2]
    exact HeckeDetectorRowCount.balanced_count_identity hδ.le hd hx hx'
  rw [he] at hc'
  exact hc'

theorem high_adaptive_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height q : ℝ) (i : ℕ),
      1<U → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    HeckeDetectorHighBatchCount.high_batch_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ C height q i hU ha ha' hε hε' hC hh hf
  rw [cutoff_eq_high (2*a-1) q ha]
  exact hcount a ε T allowance Δ C height i hU ha.le ha' hε hε' hC hh hf

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1836

/- Original source: OAI/NumberTheory/DirichletL/Detector/FinalAssemblyCountParameters.lean; sha256: 88b1a01167a672f116f0285f9384ed5c888cc456a55da7dbc71c90498632a968 -/
section Source1837
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff
open ProbeHighRowFamily

structure CountParameters (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  cB : ℝ
  kB : ℝ
  cH : ℝ
  kH : ℝ
  cB_pos : 0<cB
  cB_one : cB≤1
  kB_pos : 0<kB
  cH_pos : 0<cH
  cH_one : cH≤1
  kH_pos : 0<kH
  balanced : ∃K₀ : ℝ,0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ cB kB C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+
          Δ/4+159*ε+εm+B.mesh+7*ν)
  high : ∃K₀ : ℝ,0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height q : ℝ) (i : ℕ),
      1<U → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ cH kH C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm)

theorem exists_count_parameters
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    Nonempty (CountParameters M H εm) := by
  obtain ⟨cB,kB,KB,hcB,hcB1,hkB,hKB,hbalanced⟩ := balanced_adaptive_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨cH,kH,KH,hcH,hcH1,hkH,hKH,hhigh⟩ := high_adaptive_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨cB,kB,cH,kH,hcB,hcB1,hkB,hcH,hcH1,hkH,⟨KB,hKB,hbalanced⟩,⟨KH,hKH,hhigh⟩⟩⟩

end SevenEighths.ProbeFinalAssembly

end

end OAI

end Source1837

/- Original source: OAI/NumberTheory/DirichletL/Detector/FinalAssemblyData.lean; sha256: 40177414737797476aa62242da6bbe91bd42c505887517be6d1ab19a6cef1628 -/
section Source1838
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
local notation "O" => HeckeFamily.O

structure SourceData {Δ : ℝ} (D : HighData Δ) where
  S : Finset (Ideal O)
  exclusions : SourceExclusions S
  maximal : ∀P∈S,P.IsMaximal
  first : FirstTail (4*D.e) S
  w : ℝ→ℝ
  W : SchwartzMap ℝ ℂ
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  support : Function.support w⊆Set.Ioo 1 2
  positive_support : tsupport w⊆Set.Ioi 0
  bounded : ∀x,0≤w x ∧ w x≤1
  nonzero : w≠0
  complex_eq : ∀x,W x=(w x:ℂ)
  complex_nonzero : W≠0
  complex_support : Function.support W⊆Set.Icc 1 2
  real : ∀x,(W x).im=0
  nonnegative : ∀x,0≤(W x).re

theorem exists_source_data {Δ : ℝ} (D : HighData Δ) : Nonempty (SourceData D) := by
  obtain ⟨S,_,hS,hfirst,hmax⟩ := exists_fixed_source D.e D.e_pos ∅ (by simp)
  obtain ⟨w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩ := exists_fixed_probe_window
  exact ⟨⟨S,hS,hmax,hfirst,w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩⟩

def SourceData.modulus {Δ : ℝ} {D : HighData Δ} (F : SourceData D) : Ideal O := ∏P∈F.S,P

instance {Δ : ℝ} {D : HighData Δ} (F : SourceData D) : NeZero F.modulus :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

instance {Δ : ℝ} {D : HighData Δ} (F : SourceData D) : Finite (O ⧸ F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

theorem source_count_parameters {Δ : ℝ} {D : HighData Δ} (F : SourceData D) :
    Nonempty (CountParameters F.modulus ⊤ D.t) := by
  exact exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x=>(F.bounded x).1) F.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) F.support (fun x=>(F.bounded x).2) D.t D.t_pos

def SourceData.probe {Δ : ℝ} {D : HighData Δ} (F : SourceData D) (η : Character) : ℝ→ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  normalizedProbe F.modulus ⊤ F.S F.maximal D.ell 1 2 (fun _=>F.w) F.W F.W η

theorem SourceData.probe_low {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (loss : ℝ) (hloss : 0<loss) (η : Character) :
    F.probe η=O[atTop](fun Z : ℝ=>Z^(3/16+loss)) := by
  exact normalizedProbe_low F.modulus ⊤ le_top F.S F.exclusions F.maximal 1 2 1 loss
    (by norm_num) (by norm_num) hloss D.ell (fun j=>(D.slots_bounds j).1) D.slots_injective D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero η

end SevenEighths.ProbeFinalAssembly

end

end OAI

end Source1838

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceBatch.lean; sha256: bcabe2864432eeaa7817d5a7481164b2ddb0e856c8b8cf0fde37c6c870b53783 -/
section Source1839
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentDetectorDictionary
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open ProbeHighRowFamily HeckeDetectorDyadicProfiles CenteredMomentPrimeSlot HeckeDetectorRowwisePolynomial
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem eventually_source_batch_plain_sectors {N : ℕ}
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (hM : M=∏P∈S,P)
    (η : Character) (ell : Fin N→ℝ) (hell : ∀s,0<ell s)
    (W : Fin N→ℝ→ℂ) (hW : ∀s,Function.support (W s)⊆Set.Ici 1) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,d≠0→∀a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N) (Z^d) a ε tstar T allowance i,
      B.data=sourceMomentData M H hH S hS η→B.widths=(fun s=>ell s/d)→B.profile=W→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀selected : Finset (Fin N),∀j k : ℕ,∀σ t : ℝ,
      let F:=B.fiber bin label J K hne
      let η₀:=sourceMomentBase M H hH S hS η label
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) ((Z^d)^F.m) σ t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) ((Z^d)^F.m) σ t*
          F.physicalProduct selected u‖^2)≤
        ∑θ : selected→RayQuotient.Characters M H,‖averageWeight (ι:=selected) M H‖*
          ∑u∈F.rows,‖fiberSector hH F η₀ selected j k σ t θ u‖^2 := by
  have hMm : M≤Ideal.span {rowMaskElement} := by
    rw [hM]
    exact source_product_le_rowMask S hbad
  filter_upwards [eventually_source_slots_coprime M H hH S hS η ell hell 1 (by norm_num),
    eventually_gt_atTop (0:ℝ)] with Z hz hZ
  intro d hd a ε tstar T allowance i B hdata hwidth hprofile bin label J K hne selected j k σ t
  dsimp only
  convert fiber_plain_sector_energy hH (B.fiber bin label J K hne)
    (sourceMomentBase M H hH S hS η label) ?_ hMm (Real.rpow_pos_of_pos hZ _) selected j k σ t ?_ using 1
  · congr 2 ; apply Subsingleton.elim
  · change B.data label=momentData (sourceMomentBase M H hH S hS η label)
    rw [hdata,sourceMomentData_base]
  · intro s hs P hP hp
    change P∈primePool M H (B.upper s) ((Z^d)^(B.widths s)) at hP
    change B.profile s ((P.absNorm:ℝ)/((Z^d)^(B.widths s)))≠0 at hp
    rw [hwidth] at hP
    rw [hwidth,hprofile] at hp
    exact hz label s d hd (W s) (B.upper s) (hW s) P hP hp

theorem sourceData_batch_gate {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,d≠0→∀a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i,
      B.data=sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η→
      B.widths=(fun s=>D.ell s/d)→B.profile=(fun _ y=>(F.w y:ℂ))→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀selected : Finset (Fin D.N),∀j k : ℕ,∀σ t : ℝ,
      let Bf:=B.fiber bin label J K hne
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      (∑u∈Bf.rows,‖polynomial (Bf.family u Bf.label) false ((logProfile^[j]) positiveAnnular) ((Z^d)^Bf.m) σ t*
        polynomial (Bf.family u Bf.label) false ((logProfile^[k]) positiveAnnular) ((Z^d)^Bf.m) σ t*
          Bf.physicalProduct selected u‖^2)≤
        ∑θ : selected→RayQuotient.Characters F.modulus ⊤,‖averageWeight (ι:=selected) F.modulus ⊤‖*
          ∑u∈Bf.rows,‖fiberSector le_top Bf η₀ selected j k σ t θ u‖^2 := by
  apply eventually_source_batch_plain_sectors F.modulus ⊤ le_top F.S F.exclusions.prime
    F.exclusions.bad rfl η D.ell (fun s=>(D.slots_bounds s).1) (fun _ y=>(F.w y:ℂ))
  intro s y hy
  have hn : F.w y≠0 := by
    intro h
    apply hy
    simp only [h,Complex.ofReal_zero]
  exact (F.support hn).1.le

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1839
