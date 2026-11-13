import OpenAIGrouped.Unit006
import OpenAIGrouped.Unit000
import OpenAIGrouped.Unit001
import OpenAIGrouped.Unit002
import OpenAIGrouped.Unit003
import OpenAIGrouped.Unit004
import OpenAIGrouped.Unit005
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Basic.NNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Cusp/WeylRepresentatives.lean; sha256: 2560ef95fb63e72eadc02177074749614e2949d4142126e3fa8e3ce6641d2b15 -/
section Source280
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

namespace ShortDraftCusp
open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicKubota CubicEisenstein ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def A3WeylCusp (u : Eis) : SL(2,Eis) :=
  ⟨!![u,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma A3_ramified_relative_matrix (M : SL(2,Eis)) (u : Eis) :
    ((M*(lowerCuspMatrix u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) =
      !![M 0 0-u*M 0 1,M 0 1;M 1 0-u*M 1 1,M 1 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerCuspMatrix,Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma A3_unramified_relative_matrix (M : SL(2,Eis)) (u : Eis) :
    ((M*(A3WeylCusp u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) =
      !![-M 0 1,M 0 0+u*M 0 1;-M 1 1,M 1 0+u*M 1 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A3WeylCusp,Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma A3_principal_mem_levelThree (M : SL(2,Eis))
    (ha : (3:Eis)∣M 0 0-1) (hb : (3:Eis)∣M 0 1)
    (hc : (3:Eis)∣M 1 0) (hd : (3:Eis)∣M 1 1-1) : M∈levelThree := by
  apply (mem_levelThree_iff_entries M).mpr
  intro i j
  fin_cases i <;> fin_cases j <;> simpa using (by assumption)

lemma A3_ramified_mem_levelThree (M : SL(2,Eis)) (u : Eis)
    (ha : (3:Eis)∣M 0 0-1) (hb : (3:Eis)∣M 0 1)
    (hc : (3:Eis)∣M 1 0-u) (hd : (3:Eis)∣M 1 1-1) :
    M*(lowerCuspMatrix u)⁻¹∈levelThree := by
  apply (mem_levelThree_iff_entries _).mpr
  intro i j
  rw [A3_ramified_relative_matrix]
  fin_cases i <;> fin_cases j
  · convert dvd_sub ha (dvd_mul_of_dvd_right hb u) using 1 ; simp ; ring
  · simpa using hb
  · convert dvd_sub hc (dvd_mul_of_dvd_right hd u) using 1 ; simp ; ring
  · simpa using hd

lemma A3_unramified_mem_levelThree (M : SL(2,Eis)) (u : Eis)
    (ha : (3:Eis)∣M 0 0-u) (hb : (3:Eis)∣M 0 1+1)
    (hc : (3:Eis)∣M 1 0-1) (hd : (3:Eis)∣M 1 1) :
    M*(A3WeylCusp u)⁻¹∈levelThree := by
  apply (mem_levelThree_iff_entries _).mpr
  intro i j
  rw [A3_unramified_relative_matrix]
  fin_cases i <;> fin_cases j
  · convert dvd_neg.mpr hb using 1 ; simp ; ring
  · convert dvd_add ha (dvd_mul_of_dvd_right hb u) using 1 ; simp ; ring
  · simpa using dvd_neg.mpr hd
  · convert dvd_add hc (dvd_mul_of_dvd_right hd u) using 1 ; simp ; ring

end

open ActualEisensteinCubic CubicKubota CubicEisenstein ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma A3_principal_character (M : SL(2,Eis)) (hM : M∈levelThree)
    (c0 r : Eis) (hC : M 1 0=c0*r) (hr : lambda^2∣r-1) :
    complexCharacter ⟨M,hM⟩ =
      eisEmbedding (symbol c0 (M 0 0))*eisEmbedding (symbol (M 0 0) r) := by
  change eisEmbedding (symbol (M 1 0) (M 0 0))=_
  rw [hC,A3_principal_global _ _ _ (levelThree_primary ⟨M,hM⟩) hr,map_mul]

lemma A3_ramified_literal_character (M : SL(2,Eis)) (u : Eis)
    (hM : M*(lowerCuspMatrix u)⁻¹∈levelThree) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,hM⟩ =
      eisEmbedding (symbol (M 1 0-u*M 1 1) (M 0 0-u*M 0 1)) := by
  change eisEmbedding (symbol
    (((M*(lowerCuspMatrix u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 1 0)
    (((M*(lowerCuspMatrix u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 0 0))=_
  rw [A3_ramified_relative_matrix]
  rfl

lemma A3_unramified_literal_character (M : SL(2,Eis)) (u : Eis)
    (hM : M*(A3WeylCusp u)⁻¹∈levelThree) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,hM⟩ =
      eisEmbedding (symbol (-M 1 1) (-M 0 1)) := by
  change eisEmbedding (symbol
    (((M*(A3WeylCusp u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 1 0)
    (((M*(A3WeylCusp u)⁻¹ : SL(2,Eis)) : Matrix (Fin 2) (Fin 2) Eis) 0 0))=_
  rw [A3_unramified_relative_matrix]
  rfl

theorem A3_ramified_character (M : SL(2,Eis)) (u c0 r : Eis)
    (ha : (3:Eis)∣M 0 0-1) (hb : (3:Eis)∣M 0 1)
    (hc : (3:Eis)∣M 1 0-u) (hd : (3:Eis)∣M 1 1-1)
    (hC : M 1 0=u*(c0*r)) (hr : lambda^2∣r-1) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,
      A3_ramified_mem_levelThree M u ha hb hc hd⟩ =
      eisEmbedding (symbol (-u) (M 0 0-u*M 0 1)*symbol c0 (M 0 0))*
        eisEmbedding (symbol (M 0 0) r) := by
  have hA : lambda^2∣(M 0 0-u*M 0 1)-1 := by
    apply lambda_sq_dvd_three.trans
    convert dvd_sub ha (dvd_mul_of_dvd_right hb u) using 1 ; ring
  have hdet : M 0 0*M 1 1-M 0 1*(u*(c0*r))=1 := by
    rw [←hC]
    simpa only [Matrix.det_fin_two] using M.property
  rw [A3_ramified_literal_character,hC,
    A3_ramified_global_factor _ _ _ _ _ _ hdet
      (lambda_sq_dvd_three.trans ha) hA hr,map_mul]

theorem A3_unramified_character (M : SL(2,Eis)) (u c0 r : Eis)
    (ha : (3:Eis)∣M 0 0-u) (hb : (3:Eis)∣M 0 1+1)
    (hc : (3:Eis)∣M 1 0-1) (hd : (3:Eis)∣M 1 1)
    (hC : M 1 0=c0*r) (h9 : (9:Eis)∣M 0 0*M 1 1) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,
      A3_unramified_mem_levelThree M u ha hb hc hd⟩ =
      eisEmbedding (symbol (M 0 0) c0)*eisEmbedding (symbol (M 0 0) r) := by
  have hb' : lambda^2∣(-M 0 1)-1 := by
    apply lambda_sq_dvd_three.trans
    convert dvd_neg.mpr hb using 1 ; ring
  have hc' : lambda^2∣c0*r-1 := by
    rw [←hC]
    exact lambda_sq_dvd_three.trans hc
  have hdet : M 0 0*M 1 1-M 0 1*(c0*r)=1 := by
    rw [←hC]
    simpa only [Matrix.det_fin_two] using M.property
  rw [A3_unramified_literal_character,
    A3_unramified_global_factor _ _ _ _ _ hdet hb' hc' h9,map_mul]

end ShortDraftCusp

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedCuspArrayIndex_ne_zero (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    fixedCuspArrayIndex u m I J≠0 :=
  mul_ne_zero (mul_ne_zero (ramifiedElement_ne_zero u m) hI) (pow_ne_zero _ hJ)

lemma fixedCuspArrayIndex_norm_sq (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    ‖eisEmbedding (fixedCuspArrayIndex u m I J)‖^2=
      (3:ℝ)^m*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  have hr:‖eisEmbedding (u.val*lambda^m)‖^2=(3:ℝ)^m := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ramifiedElement_absNorm,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _=‖eisEmbedding (u.val*lambda^m)‖^2*‖eisEmbedding (primaryGenerator I)‖^2*
      (‖eisEmbedding (primaryGenerator J)‖^2)^3 := by
        simp only [fixedCuspArrayIndex,map_mul,map_pow,norm_mul,norm_pow]
        ring
    _=_ := by rw [hr,primaryGenerator_norm_sq I hI,primaryGenerator_norm_sq J hJ]

lemma fixedCuspArrayIndex_norm (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    ‖eisEmbedding (fixedCuspArrayIndex u m I J)‖=
      Real.sqrt ((3:ℝ)^m*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3) := by
  rw [←fixedCuspArrayIndex_norm_sq u m I J hI hJ,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]

lemma fixedCuspArrayWeight_div_norm (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    fixedCuspArrayWeight m J/‖eisEmbedding (fixedCuspArrayIndex u m I J)‖=
      1/((3:ℝ)^((m:ℝ)/3)*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hn:0<(Ideal.absNorm I:ℝ) := by
    rw [←primaryGenerator_norm_sq I hI]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hI))
  have hb:0<(Ideal.absNorm J:ℝ) := by
    rw [←primaryGenerator_norm_sq J hJ]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hJ))
  rw [fixedCuspArrayWeight,fixedCuspArrayIndex_norm u m I J hI hJ]
  simpa only [Real.rpow_natCast] using cusp_coefficient_normalization (m:ℝ)
    (Ideal.absNorm I:ℝ) (Ideal.absNorm J:ℝ) hn hb

theorem fixedConjugateCuspArray_div_norm (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayEligible I J) :
    star ((sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J))/
      (‖eisEmbedding (fixedCuspArrayIndex u m I J)‖:ℂ)=
    (fixedCuspCoefficientBound:ℂ)*fixedConjugateCuspArray j u m I J/
      (((3:ℝ)^((m:ℝ)/3)*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ):ℝ):ℂ) := by
  rw [fixedConjugateCuspArray_reconstruct j u m I J h]
  calc
    _=(fixedCuspCoefficientBound:ℂ)*fixedConjugateCuspArray j u m I J*
      ((fixedCuspArrayWeight m J/‖eisEmbedding (fixedCuspArrayIndex u m I J)‖:ℝ):ℂ) := by
        push_cast
        ring
    _=_ := by
      rw [fixedCuspArrayWeight_div_norm u m I J h.2.1 h.2.2]
      push_cast
      ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

section
open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaFullFrequency_eq_fixedCuspArrayIndex (p:ThetaFullIndex) :
    thetaFullFrequency p=fixedCuspArrayIndex p.1 p.2.1 p.2.2.1.val p.2.2.2.val := rfl

lemma sourceCuspRadialLength_full_index (p:ThetaFullIndex) :
    sourceCuspRadialLength (thetaFullFrequency p)=
      (3:ℝ)^p.2.1*(Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3 := by
  rw [sourceCuspRadialLength,ite_eq_right (thetaFullFrequency_ne_zero p),thetaFullFrequency_eq_fixedCuspArrayIndex]
  exact fixedCuspArrayIndex_norm_sq p.1 p.2.1 p.2.2.1.val p.2.2.2.val
    p.2.2.1.property.2 p.2.2.2.property

lemma thetaRamifiedScale_eq (m:ℕ) :
    ramifiedScale 1 completedRamifiedStep m=(3:ℝ)^((m:ℝ)/3) := by
  unfold ramifiedScale completedRamifiedStep
  rw [one_mul,←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

lemma thetaRamifiedScale_cube (m:ℕ) :
    (ramifiedScale 1 completedRamifiedStep m)^3=(3:ℝ)^m := by
  rw [thetaRamifiedScale_eq,←Real.rpow_mul_natCast (by norm_num)]
  norm_num only [Nat.cast_ofNat]
  rw [show ((m:ℝ)/3)*(3:ℝ)=m by ring,Real.rpow_natCast]

lemma sourceCusp_full_index_kernel_argument (p:ThetaFullIndex) (j:Fin 3) (Q X:ℝ) :
    X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale j)^2*Q^2)=
      (X/(27*(sourceCuspScale j)^2*Q^2))*(ramifiedScale 1 completedRamifiedStep p.2.1)^3*
        (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3 := by
  rw [sourceCuspRadialLength_full_index,thetaRamifiedScale_cube]
  ring

def sourceFrequencyAngle (h:Eis) : ℂ := eisEmbedding h/(‖eisEmbedding h‖:ℂ)

lemma sourceFrequencyAngle_norm (h:Eis) (hh:h≠0) : ‖sourceFrequencyAngle h‖=1 := by
  rw [sourceFrequencyAngle,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hh))

lemma sourceCuspRadialCoefficient_angle (j:Fin 3) (z:ℂ) (h:Eis) (hh:h≠0) :
    sourceCuspRadialCoefficient j z h=
      ((-2*Real.pi*Complex.I*thetaFrequencyScale)/(sourceCuspScale j:ℂ)^2)*
        sourceFrequencyAngle h*
        (star ((sourceCuspCoefficients j).value h)/(‖eisEmbedding h‖:ℂ))*
        ShortDraftTrace.breveE (-cuspFrequency h*(z/(sourceCuspScale j:ℂ))) := by
  have hn:(‖eisEmbedding h‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hh))
  have hs:(sourceCuspScale j:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne'
  rw [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,sourceCuspRadialLength,ite_eq_right hh]
  rw [cuspFrequency_eq_thetaFrequencyScale]
  unfold sourceFrequencyAngle
  push_cast
  field_simp [hn,hs]

def fixedRadialCoefficientScalar : ℂ :=
  (-2*Real.pi*Complex.I)*thetaFrequencyScale*(fixedCuspCoefficientBound:ℂ)

theorem sourceCuspRadialCoefficient_fixed_array
    (j:Fin 3) (z:ℂ) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) (h:fixedCuspArrayEligible I J) :
    sourceCuspRadialCoefficient j z (fixedCuspArrayIndex u m I J)=
      (fixedRadialCoefficientScalar/(sourceCuspScale j:ℂ)^2)*
        (fixedConjugateCuspArray j u m I J*
          sourceFrequencyAngle (fixedCuspArrayIndex u m I J)*
          ShortDraftTrace.breveE (-cuspFrequency (fixedCuspArrayIndex u m I J)*
            (z/(sourceCuspScale j:ℂ))))/
        ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm I:ℝ)*
          (Ideal.absNorm J:ℝ):ℝ):ℂ) := by
  rw [sourceCuspRadialCoefficient_angle _ _ _
    (fixedCuspArrayIndex_ne_zero u m I J h.2.1 h.2.2),
    fixedConjugateCuspArray_div_norm j u m I J h,thetaRamifiedScale_eq]
  unfold fixedRadialCoefficientScalar
  push_cast
  ring

end

open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaFullIndex_denominator_pos (p:ThetaFullIndex) :
    0<ramifiedScale 1 completedRamifiedStep p.2.1*
      Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ) := by
  have hI:0<(Ideal.absNorm p.2.2.1.val:ℝ):=by
    rw [←primaryGenerator_norm_sq _ p.2.2.1.property.2]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero p.2.2.1.property.2))
  have hJ:0<(Ideal.absNorm p.2.2.2.val:ℝ):=by
    rw [←primaryGenerator_norm_sq _ p.2.2.2.property]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero p.2.2.2.property))
  rw [thetaRamifiedScale_eq]
  positivity

lemma SourceCuspDatum.smoothed_unit_phase_norm (d:SourceCuspDatum) :
    ‖d.multiplier*(d.heightScale:ℂ)‖=1 := by
  rw [norm_mul,d.multiplier_norm,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos d.heightScale_pos,inv_mul_cancel₀ d.heightScale_pos.ne']

theorem SourceCuspDatum.smoothedFullCoefficient_normalization (d:SourceCuspDatum) (p:ThetaFullIndex) :
    (d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
      sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)=
    (fixedRadialCoefficientScalar*(d.multiplier*(d.heightScale:ℂ)))*
      (fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
        sourceFrequencyAngle (thetaFullFrequency p)*
        ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
          (d.dualPoint/(sourceCuspScale d.index:ℂ))))/
      ((ramifiedScale 1 completedRamifiedStep p.2.1*
        Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ) := by
  have hs:(sourceCuspScale d.index:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos _).ne'
  have hn:((ramifiedScale 1 completedRamifiedStep p.2.1*
      Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (thetaFullIndex_denominator_pos p).ne'
  simp only [thetaFullFrequency_eq_fixedCuspArrayIndex]
  rw [sourceCuspRadialCoefficient_fixed_array _ _ _ _ _ _
    ⟨p.2.2.1.property.1,p.2.2.1.property.2,p.2.2.2.property⟩]
  field_simp [hs,hn]

lemma SourceCuspDatum.smoothedFullCoefficient_norm_le (d:SourceCuspDatum) (p:ThetaFullIndex) :
    ‖(d.multiplier*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
      sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)‖≤
    ‖fixedRadialCoefficientScalar‖/
      (ramifiedScale 1 completedRamifiedStep p.2.1*
        Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)) := by
  have ha:‖fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      sourceFrequencyAngle (thetaFullFrequency p)*
      ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
        (d.dualPoint/(sourceCuspScale d.index:ℂ)))‖≤1:=by
    rw [norm_mul,norm_mul,sourceFrequencyAngle_norm _ (thetaFullFrequency_ne_zero p),breveE_norm,mul_one,mul_one]
    exact fixedConjugateCuspArray_norm_le_one _ _ _ _ _
  rw [d.smoothedFullCoefficient_normalization,norm_div,norm_mul,norm_mul,
    d.smoothed_unit_phase_norm,mul_one,Complex.norm_real,Real.norm_of_nonneg (thetaFullIndex_denominator_pos p).le]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right (norm_nonneg _) ha) (thetaFullIndex_denominator_pos p).le

theorem SourceCuspDatum.smoothedKernel_fixed_array (d:SourceCuspDatum) (W:ℝ→ℂ) (X:ℝ) :
    d.smoothedKernel W X=(fixedRadialCoefficientScalar*(d.multiplier*(d.heightScale:ℂ)))*
      ∑'p:ThetaFullIndex,
        ((fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
          sourceFrequencyAngle (thetaFullFrequency p)*
          ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
            (d.dualPoint/(sourceCuspScale d.index:ℂ))))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale d.index)^2*d.heightScale^2))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3) := by
  rw [d.smoothedKernel_full_index,←tsum_mul_left,←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [←mul_assoc,d.smoothedFullCoefficient_normalization,sourceCusp_full_index_kernel_argument]
  ring

end CubicEisenstein

open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticAllOddCRT
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

theorem idealRowHom_congr_mod (I:Ideal Eis) (x y:Eis) (hxy:x-y∈I) :
    idealRowHom x I=idealRowHom y I := by
  by_cases hI:I=0
  · subst I
    simp only [map_zero]
  change (if I=0 then 0 else _)=(if I=0 then 0 else _)
  rw [ite_eq_right hI,ite_eq_right hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  have hle:I≤P:=((Ideal.mem_normalizedFactors_iff hI).mp hP).2
  unfold localRowValue
  split_ifs with hp
  · let:P.IsMaximal:=hp.1
    congr 1
    exact Ideal.Quotient.eq.mpr (hle hxy)
  · rfl

lemma sexticReciprocityPhase_congr_right (a x y:Eis) (hxy:(4:Eis)∣x-y) :
    sexticReciprocityPhase a x=sexticReciprocityPhase a y := by
  unfold sexticReciprocityPhase
  rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub x y hxy]

lemma sexticReciprocityPhase_norm (a x:Eis) : ‖sexticReciprocityPhase a x‖≤1 := by
  unfold sexticReciprocityPhase quadraticRaySign
  split_ifs <;> norm_num

def reciprocalRow (a:Eis) (ha:Supported (Ideal.span {a})) : Eis→*ℂ where
  toFun n:=sexticReciprocityPhase a n*idealRowHom n (Ideal.span {a})
  map_one' := by rw [sexticReciprocityPhase_one_right a ha,idealRowHom_one_supported _ ha,one_mul]
  map_mul' x y := by
    rw [sexticReciprocityPhase_mul_right,idealRowHom_argument_mul]
    ring

lemma reciprocalRow_norm (a:Eis) (ha:Supported (Ideal.span {a})) (n:Eis) :
    ‖reciprocalRow a ha n‖≤1 := by
  change ‖sexticReciprocityPhase a n*idealRowHom n (Ideal.span {a})‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (sexticReciprocityPhase_norm a n)).trans (idealRowHom_norm _ _)

lemma reciprocalRow_periodic (a:Eis) (ha:Supported (Ideal.span {a})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(4:Eis)}*Ideal.span {a}) (reciprocalRow a ha) := by
  intro x y hxy
  change sexticReciprocityPhase a x*idealRowHom x (Ideal.span {a})=
    sexticReciprocityPhase a y*idealRowHom y (Ideal.span {a})
  rw [sexticReciprocityPhase_congr_right a x y
    (Ideal.mem_span_singleton.mp (Ideal.mul_le_left hxy)),
    idealRowHom_congr_mod _ x y (Ideal.mul_le_right hxy)]

lemma reciprocalRow_eq_idealRowHom (a n:Eis)
    (ha:Supported (Ideal.span {a})) (hn:Supported (Ideal.span {n}))
    (hpa:lambda^2∣a-1) (hpn:lambda^2∣n-1) :
    reciprocalRow a ha n=idealRowHom a (Ideal.span {n}) := by
  have h:=idealRowHom_primary_reciprocity n a hpn hpa hn ha
  have hs:sexticReciprocityPhase n a=sexticReciprocityPhase a n := by
    exact congrArg (fun z:ℤ=>(z:ℂ)) (quadraticRaySign_symm _ _)
  change sexticReciprocityPhase a n*idealRowHom n (Ideal.span {a})=_
  rw [hs] at h
  exact h.symm

end CanonicalRowCompletion

namespace CubicEisenstein
open scoped Classical BigOperators MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

def amplitude (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  fixedConjugateCuspArray s.index u m I J*
    sourceFrequencyAngle (fixedCuspArrayIndex u m I J)*
    ShortDraftTrace.breveE (-cuspFrequency (fixedCuspArrayIndex u m I J)*
      eisEmbedding (s.upper 0 0*s.upper 0 1)/(sourceCuspScale s.index:ℂ))

lemma amplitude_norm (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ‖s.amplitude u m I J‖≤1 := by
  by_cases he:fixedCuspArrayEligible I J
  · rw [amplitude,norm_mul,norm_mul,breveE_norm,
      sourceFrequencyAngle_norm _ (fixedCuspArrayIndex_ne_zero u m I J he.2.1 he.2.2),mul_one,mul_one]
    exact fixedConjugateCuspArray_norm_le_one _ _ _ _ _
  · simp only [amplitude,fixedConjugateCuspArray,
      fixedCuspArray_zero_of_ineligible _ _ _ _ _ he,star_zero,zero_mul,norm_zero]
    norm_num

theorem smoothedKernel_fixed_shape (g:levelTwo) (hc:((g:SL(2,Eis))*H) 1 0≠0)
    (W:ℝ→ℂ) (X:ℝ) :
    (s.datum g hc).smoothedKernel W X=
      (fixedRadialCoefficientScalar*((s.datum g hc).multiplier*
        (‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^2:ℝ)))*
      ∑'p:ThetaFullIndex,
        ((s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
          ShortDraftTrace.breveE (cuspFrequency (thetaFullFrequency p)*
            eisEmbedding (s.upper 0 0)^2*
            (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding (((g:SL(2,Eis))*H) 1 0))/
            (sourceCuspScale s.index:ℂ)))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale s.index)^2*‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^4))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3) := by
  rw [(s.datum g hc).smoothedKernel_fixed_array,s.datum_heightScale]
  have hi:(s.datum g hc).index=s.index:=rfl
  simp only [hi,←pow_mul,show (2:ℕ)*2=4 by norm_num]
  congr 1
  apply tsum_congr
  intro p
  have hp:=s.datum_additive_phase g hc (cuspFrequency (thetaFullFrequency p))
    (sourceCuspScale s.index:ℂ)
  rw [show -cuspFrequency (thetaFullFrequency p)*
      ((s.datum g hc).dualPoint/(sourceCuspScale s.index:ℂ))=
      -cuspFrequency (thetaFullFrequency p)*(s.datum g hc).dualPoint/(sourceCuspScale s.index:ℂ) by ring,hp]
  unfold amplitude
  rw [←thetaFullFrequency_eq_fixedCuspArrayIndex]
  ring

lemma smoothed_row_factor (g:levelTwo) (hc:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g hc).multiplier*((s.datum g hc).heightScale:ℂ)=
      -star (levelTwoComplexCharacter g)*
        (star (levelTwoComplexCharacter s.gamma)*eisEmbedding (s.upper 0 0)^2)*
        ((‖eisEmbedding (((g:SL(2,Eis))*H) 1 0)‖^2:ℝ):ℂ)/
        eisEmbedding (((g:SL(2,Eis))*H) 1 0)^2 := by
  rw [s.datum_multiplier,s.datum_heightScale]
  push_cast
  ring

end FixedCuspShape
end CubicEisenstein

open scoped BigOperators Classical Matrix MatrixGroups

namespace ShortDraftCRT
variable {R:Type*} [CommRing R]

lemma exists_controlled_inverse (B c a:R) (ha:IsCoprime a (B*c)) :
    ∃d0:R,B*c∣a*d0-1 := by
  obtain ⟨x,y,hxy⟩:=ha
  refine ⟨x,-y,?_⟩
  linear_combination hxy

lemma exists_controlled_zero_inverse (B c a:R)
    (hBc:IsCoprime B c) (hac:IsCoprime a c) :
    ∃d0:R,B∣d0 ∧ c∣a*d0-1 := by
  obtain ⟨x,y,hxy⟩:=hac.mul_left hBc
  refine ⟨B*x,⟨x,rfl⟩,-y,?_⟩
  linear_combination hxy

variable [IsDomain R]

lemma fixed_completion_upper_right_dvd (B M c r a d0 b d:R)
    (hc:c≠0) (hBM:B∣M) (hr:IsCoprime r (M*c))
    (hinv:B*c∣a*d0-1) (hdet:a*d-b*(c*r)=1) (hd:M*c∣d-d0) : B∣b := by
  have hBcM:B*c∣M*c:=mul_dvd_mul_right hBM c
  have hadd:B*c∣a*(d-d0):=dvd_mul_of_dvd_right (hBcM.trans hd) a
  have hfull:B*c∣a*d-1:=by
    convert dvd_add hadd hinv using 1 ; ring
  have hmul:B*c∣c*(b*r):=by
    convert hfull using 1
    linear_combination -hdet
  rw [mul_comm B c] at hmul
  have hbr:B∣b*r:=(mul_dvd_mul_iff_left hc).mp hmul
  have hBr:IsCoprime B r:=hr.of_mul_right_left.symm.of_isCoprime_of_dvd_left hBM
  exact hBr.dvd_of_dvd_mul_right hbr

theorem exists_fixed_completion_upper_right (B M c r a d0:R)
    (hc:c≠0) (hBM:B∣M) (hr:IsCoprime r (M*c)) (har:IsCoprime a r)
    (hinv:B*c∣a*d0-1) :
    ∃b d:R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ B∣b := by
  obtain ⟨b,d,hdet,hd⟩:=exists_fixed_completion M c r a d0
    ((dvd_mul_left c B).trans hinv) hr har
  exact ⟨b,d,hdet,hd,fixed_completion_upper_right_dvd B M c r a d0 b d hc hBM hr hinv hdet hd⟩

omit [IsDomain R] in
theorem exists_fixed_completion_lower_right (B M c r a d0:R)
    (hBM:B∣M) (hr:IsCoprime r (M*c)) (har:IsCoprime a r)
    (hzero:B∣d0) (hinv:c∣a*d0-1) :
    ∃b d:R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ B∣d ∧ B∣a*d ∧ B∣b*(c*r)+1 := by
  obtain ⟨b,d,hdet,hd⟩:=exists_fixed_completion M c r a d0 hinv hr har
  have hdd:B∣d-d0:=(hBM.trans (dvd_mul_right M c)).trans hd
  have hBd:B∣d:=by
    convert dvd_add hdd hzero using 1 ; ring
  have hBad:B∣a*d:=dvd_mul_of_dvd_right hBd a
  refine ⟨b,d,hdet,hd,hBd,hBad,?_⟩
  convert hBad using 1
  linear_combination -hdet

theorem controlled_completion_matrix_congr (M c r r0 a a0 b b0 d d0 inverse:R)
    (hc:c≠0) (hr:IsCoprime M r)
    (hdet:a*d-b*(c*r)=1) (hdet0:a0*d0-b0*(c*r0)=1)
    (ha:M*c∣a-a0) (hd:M*c∣d-inverse) (hd0:M*c∣d0-inverse)
    (hrr:M∣r-r0) :
    (!![a,b;c*r,d]:Matrix (Fin 2) (Fin 2) R).map (Ideal.Quotient.mk (Ideal.span {M}))=
      (!![a0,b0;c*r0,d0]:Matrix (Fin 2) (Fin 2) R).map (Ideal.Quotient.mk (Ideal.span {M})) := by
  apply fixed_completion_matrix_congr M c r r0 a a0 b b0 d d0 hc hr hdet hdet0 ha _ hrr
  convert dvd_sub hd hd0 using 1 ; ring

end ShortDraftCRT

end

end OAI

end Source280

/- Original source: OAI/NumberTheory/DirichletL/ChineseRemainder/PrimaryCompletions.lean; sha256: 7f110a463e288c602fac99699d938f3744bbe198cf282e8b4ff67b5343e794bc -/
section Source281
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

namespace ShortDraftCRT
open scoped BigOperators Classical Matrix MatrixGroups

section
open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primary_coprime_nine (a:Eis) (ha:lambda^2∣a-1) : IsCoprime a (9:Eis) := by
  have h3:=primary_coprime_three a ha
  simpa only [show (3:Eis)*3=9 by norm_num] using h3.mul_right h3

lemma nine_coprime_of_not_lambda_dvd (c:Eis) (hc:¬lambda∣c) : IsCoprime (9:Eis) c := by
  have hL:IsCoprime lambda c:=
    PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr hc
  have h3:IsCoprime (3:Eis) c:=(hL.mul_left hL).of_isCoprime_of_dvd_left
    (by simpa only [pow_two] using three_dvd_lambda_sq)
  simpa only [show (3:Eis)*3=9 by norm_num] using h3.mul_left h3

lemma primary_numerator_controlled_inverse (c a:Eis)
    (ha:lambda^2∣a-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)*c∣a*d0-1 :=
  exists_controlled_inverse 9 c a ((primary_coprime_nine a ha).mul_right hac)

lemma completion_primary_lower_right (a b c d:Eis)
    (hdet:a*d-b*c=1) (ha:(3:Eis)∣a-1) (hb:(3:Eis)∣b) : (3:Eis)∣d-1 := by
  have had:(3:Eis)∣a*d-1:=by
    convert dvd_mul_of_dvd_left hb c using 1
    linear_combination hdet
  convert dvd_sub had (dvd_mul_of_dvd_left ha d) using 1 ; ring

lemma completion_negative_upper_right (a b c d:Eis)
    (hdet:a*d-b*c=1) (hc:(3:Eis)∣c-1) (hd:(3:Eis)∣d) : (3:Eis)∣b+1 := by
  have hbc:(3:Eis)∣b*c+1:=by
    convert dvd_mul_of_dvd_right hd a using 1
    linear_combination -hdet
  convert dvd_sub hbc (dvd_mul_of_dvd_right hc b) using 1 ; ring

theorem exists_primary_numerator_completion (M c a:Eis)
    (hc:c≠0) (h9M:(9:Eis)∣M) (ha:lambda^2∣a-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)*c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃b d:Eis,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ (9:Eis)∣b ∧
        (3:Eis)∣d-1 ∧ (3:Eis)∣c*r-c := by
  obtain ⟨d0,hd0⟩:=primary_numerator_controlled_inverse c a ha hac
  refine ⟨d0,hd0,?_⟩
  intro r hr har hprimary
  obtain ⟨b,d,hdet,hd,hb⟩:=exists_fixed_completion_upper_right 9 M c r a d0 hc h9M hr har hd0
  refine ⟨b,d,hdet,hd,hb,completion_primary_lower_right a b (c*r) d hdet
    (three_dvd_primary_sub_one a ha) ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hb),?_⟩
  convert dvd_mul_of_dvd_right (three_dvd_primary_sub_one r hprimary) c using 1 ; ring

theorem exists_unramified_denominator_completion (M c a:Eis)
    (h9M:(9:Eis)∣M) (hc:¬lambda∣c) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)∣d0 ∧ c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→
      ∃b d:Eis,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ (9:Eis)∣d ∧
        (9:Eis)∣a*d ∧ (9:Eis)∣b*(c*r)+1 := by
  obtain ⟨d0,hzero,hinv⟩:=exists_controlled_zero_inverse 9 c a
    (nine_coprime_of_not_lambda_dvd c hc) hac
  exact ⟨d0,hzero,hinv,fun r hr har=>exists_fixed_completion_lower_right 9 M c r a d0
    h9M hr har hzero hinv⟩

theorem exists_primary_denominator_completion (M c a:Eis)
    (h9M:(9:Eis)∣M) (hc:lambda^2∣c-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)∣d0 ∧ c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃b d:Eis,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ (9:Eis)∣d ∧
        (9:Eis)∣a*d ∧ (9:Eis)∣b*(c*r)+1 ∧ (3:Eis)∣b+1 ∧ (3:Eis)∣c*r-1 := by
  have hcl:¬lambda∣c:=by
    intro hd
    have hcL:IsCoprime lambda c:=
      (primary_coprime_three c hc).symm.of_isCoprime_of_dvd_left
        ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three)
    exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (hcL.isUnit_of_dvd hd)
  obtain ⟨d0,hzero,hinv,hcomp⟩:=exists_unramified_denominator_completion M c a h9M hcl hac
  refine ⟨d0,hzero,hinv,?_⟩
  intro r hr har hpr
  obtain ⟨b,d,hdet,hd,hBd,had,hbc⟩:=hcomp r hr har
  have hc3:(3:Eis)∣c*r-1:=three_dvd_primary_sub_one _ (primary_mul c r hc hpr)
  exact ⟨b,d,hdet,hd,hBd,had,hbc,completion_negative_upper_right a b (c*r) d hdet hc3
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hBd),hc3⟩

end

section
variable {R:Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
lemma controlled_inverse_sector (B M c a a0 d0:R)
    (hBM:B∣M) (ha:M*c∣a-a0) (hinv:B*c∣a0*d0-1) : B*c∣a*d0-1 := by
  have hdiff:=dvd_mul_of_dvd_left ((mul_dvd_mul_right hBM c).trans ha) d0
  convert dvd_add hdiff hinv using 1 ; ring

theorem exists_fixed_matrix_completion_controlled
    (B N M c a0 r0 b0 d0 bResidue dResidue:R)
    (hc:c≠0) (hBM:B∣M) (hNM:N∣M)
    (hdet0:a0*d0-b0*(c*r0)=1)
    (hb0:B∣b0-bResidue) (hd0:N∣d0-dResidue) :
    ∀a r:R,M*c∣a-a0→M∣r-r0→IsCoprime r (M*c)→IsCoprime a r→
      ∃b d:R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ B∣b-bResidue ∧ N∣d-dResidue ∧
        (!![a,b;c*r,d]:Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M}))=
        (!![a0,b0;c*r0,d0]:Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M})) := by
  intro a r ha hrr hr har
  obtain ⟨b,d,hdet,hd,hmat⟩:=exists_fixed_matrix_completion M c a0 r0 d0 b0 hc hdet0
    a r ha hrr hr har
  have hbd:B∣b-b0:=hBM.trans (fixed_completion_congr M c r r0 a a0 b b0 d d0 hc
    hr.of_mul_right_left.symm hdet hdet0 ha hd hrr)
  have hdd:N∣d-d0:=(hNM.trans (dvd_mul_right M c)).trans hd
  refine ⟨b,d,hdet,hd,?_,?_,hmat⟩
  · convert dvd_add hbd hb0 using 1 ; ring
  · convert dvd_add hdd hd0 using 1 ; ring

end

section
open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal CubicKubota ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O

def controlledCompletionMatrix (a b c d:Eis) (hdet:a*d-b*c=1) : SL(2,Eis) :=
  ⟨!![a,b;c,d],by simpa [Matrix.det_fin_two] using hdet⟩

theorem exists_primary_numerator_matrix (M c a:Eis)
    (hc:c≠0) (h9M:(9:Eis)∣M) (ha:lambda^2∣a-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)*c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃g:SL(2,Eis),g 0 0=a ∧ g 1 0=c*r ∧ M*c∣g 1 1-d0 ∧
        (9:Eis)∣g 0 1 ∧ (3:Eis)∣g 0 0-1 ∧ (3:Eis)∣g 1 1-1 ∧ (3:Eis)∣g 1 0-c := by
  obtain ⟨d0,hd0,hcomp⟩:=exists_primary_numerator_completion M c a hc h9M ha hac
  refine ⟨d0,hd0,?_⟩
  intro r hr har hpr
  obtain ⟨b,d,hdet,hd,hb,hd3,hc3⟩:=hcomp r hr har hpr
  exact ⟨controlledCompletionMatrix a b (c*r) d hdet,rfl,rfl,hd,hb,
    three_dvd_primary_sub_one a ha,hd3,hc3⟩

theorem exists_primary_denominator_matrix (M c a:Eis)
    (h9M:(9:Eis)∣M) (hc:lambda^2∣c-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)∣d0 ∧ c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃g:SL(2,Eis),g 0 0=a ∧ g 1 0=c*r ∧ M*c∣g 1 1-d0 ∧
        (9:Eis)∣g 1 1 ∧ (9:Eis)∣g 0 0*g 1 1 ∧
        (9:Eis)∣g 0 1*g 1 0+1 ∧ (3:Eis)∣g 0 1+1 ∧ (3:Eis)∣g 1 0-1 := by
  obtain ⟨d0,hzero,hinv,hcomp⟩:=exists_primary_denominator_completion M c a h9M hc hac
  refine ⟨d0,hzero,hinv,?_⟩
  intro r hr har hpr
  obtain ⟨b,d,hdet,hd,hBd,had,hbc,hb3,hc3⟩:=hcomp r hr har hpr
  exact ⟨controlledCompletionMatrix a b (c*r) d hdet,rfl,rfl,hd,hBd,had,hbc,hb3,hc3⟩

lemma controlled_primary_principal (g:SL(2,Eis)) (c:Eis)
    (ha:(3:Eis)∣g 0 0-1) (hb:(9:Eis)∣g 0 1)
    (hc:(3:Eis)∣g 1 0-c) (hc0:(3:Eis)∣c) (hd:(3:Eis)∣g 1 1-1) :
    g∈levelThree := by
  apply A3_principal_mem_levelThree g ha
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hb) _ hd
  convert dvd_add hc hc0 using 1 ; ring

lemma controlled_primary_ramified (g:SL(2,Eis)) (c u:Eis)
    (ha:(3:Eis)∣g 0 0-1) (hb:(9:Eis)∣g 0 1)
    (hc:(3:Eis)∣g 1 0-c) (hcu:(3:Eis)∣c-u) (hd:(3:Eis)∣g 1 1-1) :
    g*(lowerCuspMatrix u)⁻¹∈levelThree := by
  apply A3_ramified_mem_levelThree g u ha
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hb) _ hd
  convert dvd_add hc hcu using 1 ; ring

lemma controlled_denominator_unramified (g:SL(2,Eis)) (u:Eis)
    (ha:(3:Eis)∣g 0 0-u) (hb:(3:Eis)∣g 0 1+1)
    (hc:(3:Eis)∣g 1 0-1) (hd:(9:Eis)∣g 1 1) :
    g*(A3WeylCusp u)⁻¹∈levelThree :=
  A3_unramified_mem_levelThree g u ha hb hc ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hd)

end

open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem exists_primary_numerator_sector_completions {ι Q:Type*}
    (M c:Eis) (hc:c≠0) (h9M:(9:Eis)∣M)
    (sector:ι→Q) (a r:ι→Eis)
    (haPrimary:∀i,lambda^2∣a i-1) (hrPrimary:∀i,lambda^2∣r i-1)
    (hcop:∀i,IsCoprime (a i) (c*r i)) (hr:∀i,IsCoprime (r i) (M*c))
    (ha:∀i j,sector i=sector j→M*c∣a i-a j)
    (hrr:∀i j,sector i=sector j→M∣r i-r j) :
    ∃(b d:ι→Eis) (C:Q→Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M})),
      (∀i,a i*d i-b i*(c*r i)=1) ∧ (∀i,(9:Eis)∣b i) ∧ (∀i,(3:Eis)∣d i-1) ∧
      ∀i,(!![a i,b i;c*r i,d i]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M}))=C (sector i) := by
  have h3M:(3:Eis)∣M:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9M
  have hlocal (q:Q) :
      ∃C:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M}),
      ∀i,sector i=q→∃b d:Eis,a i*d-b*(c*r i)=1 ∧ (9:Eis)∣b ∧ (3:Eis)∣d-1 ∧
        (!![a i,b;c*r i,d]:Matrix (Fin 2) (Fin 2) Eis).map
          (Ideal.Quotient.mk (Ideal.span {M}))=C := by
    by_cases hq:∃j,sector j=q
    · obtain ⟨j,hj⟩:=hq
      obtain ⟨inverse,_,hcompletion⟩:=exists_primary_numerator_completion M c (a j) hc h9M
        (haPrimary j) (hcop j).of_mul_right_left
      obtain ⟨b0,d0,hdet0,_,hb0,hd0,_⟩:=hcompletion (r j) (hr j)
        (hcop j).of_mul_right_right (hrPrimary j)
      refine ⟨(!![a j,b0;c*r j,d0]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M})),?_⟩
      intro i hi
      have hs:sector i=sector j:=hi.trans hj.symm
      obtain ⟨b,d,hdet,_,hb,hd,hmat⟩:=exists_fixed_matrix_completion_controlled
        9 3 M c (a j) (r j) b0 d0 0 1 hc h9M h3M hdet0 (by simpa using hb0) hd0
        (a i) (r i) (ha i j hs) (hrr i j hs) (hr i) (hcop i).of_mul_right_right
      exact ⟨b,d,hdet,by simpa using hb,hd,hmat⟩
    · refine ⟨0,?_⟩
      intro i hi
      exact False.elim (hq ⟨i,hi⟩)
  choose C hC using hlocal
  have hi (i:ι):=hC (sector i) i rfl
  choose b d hdet hb hd hmat using hi
  exact ⟨b,d,C,hdet,hb,hd,hmat⟩

theorem exists_primary_denominator_sector_completions {ι Q:Type*}
    (M c:Eis) (h9M:(9:Eis)∣M) (hcPrimary:lambda^2∣c-1)
    (sector:ι→Q) (a r:ι→Eis) (hrPrimary:∀i,lambda^2∣r i-1)
    (hcop:∀i,IsCoprime (a i) (c*r i)) (hr:∀i,IsCoprime (r i) (M*c))
    (ha:∀i j,sector i=sector j→M*c∣a i-a j)
    (hrr:∀i j,sector i=sector j→M∣r i-r j) :
    ∃(b d:ι→Eis) (C:Q→Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M})),
      (∀i,a i*d i-b i*(c*r i)=1) ∧ (∀i,(3:Eis)∣b i+1) ∧ (∀i,(9:Eis)∣d i) ∧
      ∀i,(!![a i,b i;c*r i,d i]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M}))=C (sector i) := by
  have hc:c≠0:=primary_ne_zero c hcPrimary
  have h3M:(3:Eis)∣M:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9M
  have hlocal (q:Q) :
      ∃C:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M}),
      ∀i,sector i=q→∃b d:Eis,a i*d-b*(c*r i)=1 ∧ (3:Eis)∣b+1 ∧ (9:Eis)∣d ∧
        (!![a i,b;c*r i,d]:Matrix (Fin 2) (Fin 2) Eis).map
          (Ideal.Quotient.mk (Ideal.span {M}))=C := by
    by_cases hq:∃j,sector j=q
    · obtain ⟨j,hj⟩:=hq
      obtain ⟨inverse,_,_,hcompletion⟩:=exists_primary_denominator_completion M c (a j)
        h9M hcPrimary (hcop j).of_mul_right_left
      obtain ⟨b0,d0,hdet0,_,hd0,_,_,hb0,_⟩:=hcompletion (r j) (hr j)
        (hcop j).of_mul_right_right (hrPrimary j)
      refine ⟨(!![a j,b0;c*r j,d0]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M})),?_⟩
      intro i hi
      have hs:sector i=sector j:=hi.trans hj.symm
      obtain ⟨b,d,hdet,_,hb,hd,hmat⟩:=exists_fixed_matrix_completion_controlled
        3 9 M c (a j) (r j) b0 d0 (-1) 0 hc h3M h9M hdet0
        (by simpa using hb0) (by simpa using hd0)
        (a i) (r i) (ha i j hs) (hrr i j hs) (hr i) (hcop i).of_mul_right_right
      exact ⟨b,d,hdet,by simpa using hb,by simpa using hd,hmat⟩
    · refine ⟨0,?_⟩
      intro i hi
      exact False.elim (hq ⟨i,hi⟩)
  choose C hC using hlocal
  have hi (i:ι):=hC (sector i) i rfl
  choose b d hdet hb hd hmat using hi
  exact ⟨b,d,C,hdet,hb,hd,hmat⟩

end ShortDraftCRT

namespace CubicEisenstein
open scoped Classical BigOperators ContDiff MatrixGroups

open CompletedGauss CompletedDyadic

theorem sum_smoothedKernel_common_cusp {ι:Type*} [Fintype ι]
    (d:ι→SourceCuspDatum) (w:ι→ℂ) (j:Fin 3) (Q:ℝ)
    (hj:∀i,(d i).index=j) (hQ:∀i,(d i).heightScale=Q)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑i,w i*(d i).smoothedKernel W X)=fixedRadialCoefficientScalar*
      ∑'p:ThetaFullIndex,
        ((fixedConjugateCuspArray j p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
          sourceFrequencyAngle (thetaFullFrequency p))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          (X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale j)^2*Q^2))*
        (∑i,w i*((d i).multiplier*(Q:ℂ))*
          ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
            ((d i).dualPoint/(sourceCuspScale j:ℂ)))) := by
  let F:ι→ThetaFullIndex→ℂ:=fun i p=>w i*
    ((d i).multiplier*((d i).heightScale:ℂ)*(sourceCuspScale (d i).index:ℂ)^2)*
    (sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p)*
      CubicReflectionKernel.paperKernel (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency p)/
          (27*(sourceCuspScale (d i).index)^2*(d i).heightScale^2)))
  have hs (i:ι):Summable (F i):=by
    exact ((d i).smoothedKernel_full_index_norm_summable W a b ha hsupp hW X hX).of_norm.mul_left _
  have he (i:ι):w i*(d i).smoothedKernel W X=∑'p,F i p := by
    rw [(d i).smoothedKernel_full_index]
    simp only [F,tsum_mul_left]
    ring
  simp_rw [he]
  rw [←Summable.tsum_finsetSum (fun i _=>hs i),←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hn:=(d i).smoothedFullCoefficient_normalization p
  dsimp only [F]
  calc
    _=w i*(((d i).multiplier*((d i).heightScale:ℂ)*(sourceCuspScale (d i).index:ℂ)^2)*
      sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p))*
      CubicReflectionKernel.paperKernel (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency p)/
          (27*(sourceCuspScale (d i).index)^2*(d i).heightScale^2)):=by ring
    _=_:=by rw [hn,hj i,hQ i]; ring

end CubicEisenstein

open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def coprimalityMask (m:Eis) : Eis→*ℂ where
  toFun n:=if IsCoprime m n then 1 else 0
  map_one' := by simp only [isCoprime_one_right,ite_true]
  map_mul' x y := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hx:IsCoprime m x <;> by_cases hy:IsCoprime m y <;> simp [hx,hy]

lemma coprimalityMask_norm (m n:Eis) : ‖coprimalityMask m n‖≤1 := by
  change ‖if IsCoprime m n then (1:ℂ) else 0‖≤1
  split_ifs <;> norm_num

lemma isCoprime_congr_mod (m x y:Eis) (hxy:m∣x-y) : IsCoprime m x↔IsCoprime m y := by
  obtain ⟨z,hz⟩:=hxy
  constructor
  · rintro ⟨r,s,hrs⟩
    refine ⟨r+s*z,s,?_⟩
    linear_combination hrs-s*hz
  · rintro ⟨r,s,hrs⟩
    refine ⟨r-s*z,s,?_⟩
    linear_combination hrs+s*hz

lemma coprimalityMask_periodic (m:Eis) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {m}) (coprimalityMask m) := by
  intro x y hxy
  change (if IsCoprime m x then (1:ℂ) else 0)=(if IsCoprime m y then 1 else 0)
  rw [isCoprime_congr_mod m x y (Ideal.mem_span_singleton.mp hxy)]

lemma idealRowHom_prime_sixth_mask (m:Eis) (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P) :
    idealRowHom (m^6) P=if IsCoprime P (Ideal.span {m}) then 1 else 0 := by
  rw [idealRowHom_prime _ P hg]
  have hm:=canonicalSextic_sixth_power_mask P hg m
  rw [hm]
  rw [SixthPowerAverage.prime_coprime_span_iff]
  by_cases hm:m∈P <;> simp [hm]

theorem idealRowHom_sixth_mask (m:Eis) (I:Ideal Eis) (hI:Supported I) :
    idealRowHom (m^6) I=if IsCoprime I (Ideal.span {m}) then 1 else 0 := by
  have hprod (s:Multiset (Ideal Eis))
      (hs:∀P∈s,P.IsMaximal ∧ lambda∉P) :
      idealRowHom (m^6) s.prod=if IsCoprime s.prod (Ideal.span {m}) then 1 else 0 := by
    induction s using Multiset.induction_on with
    | empty =>
      change idealRowHom (m^6) 1=if IsCoprime (1:Ideal Eis) (Ideal.span {m}) then 1 else 0
      simp only [map_one,isCoprime_one_left,ite_true]
    | @cons P s ih =>
      have hp:=hs P (Multiset.mem_cons_self _ _)
      let:P.IsMaximal:=hp.1
      have ht:∀R∈s,R.IsMaximal ∧ lambda∉R:=fun R hR=>hs R (Multiset.mem_cons_of_mem hR)
      rw [Multiset.prod_cons,map_mul,idealRowHom_prime_sixth_mask m P hp.2,ih ht,
        IsCoprime.mul_left_iff]
      by_cases hP:IsCoprime P (Ideal.span {m}) <;>
        by_cases hS:IsCoprime s.prod (Ideal.span {m}) <;> simp [hP,hS]
  have h:=hprod (normalizedFactors I) (fun P hP=>
    ⟨(supported_factors_good I hI P hP).1,(supported_factors_good I hI P hP).2.1⟩)
  rwa [Ideal.prod_normalizedFactors_eq_self hI.1] at h

lemma idealRowHom_sixth_eq_mask (m n:Eis) (hn:Supported (Ideal.span {n})) :
    idealRowHom (m^6) (Ideal.span {n})=coprimalityMask m n := by
  rw [idealRowHom_sixth_mask m _ hn,Ideal.isCoprime_span_singleton_iff]
  change (if IsCoprime n m then (1:ℂ) else 0)=(if IsCoprime m n then 1 else 0)
  rw [isCoprime_comm]

lemma rowTwist_extract_sixth_mask (Ψ:Eis→*ℂ) (m f z n:Eis)
    (hn:Supported (Ideal.span {n})) :
    rowTwist Ψ m f z n=Ψ n*coprimalityMask m n*
      idealRowHom (f^4*z) (Ideal.span {n}) := by
  change Ψ n*idealRowHom (m^6*f^4*z) (Ideal.span {n})=_
  rw [show m^6*f^4*z=m^6*(f^4*z) by ring,idealRowHom_argument_mul,
    idealRowHom_sixth_eq_mask m n hn]
  ring

end CanonicalRowCompletion

open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp

section
open ActualEisensteinCubic CubicKubota CubicEisenstein ConcreteTraceCRT CubicJacobiGlobal
open CompletedGauss CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O

theorem embedded_symbol_product {ι : Type*} [Fintype ι]
    (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (a : Eis) :
    eisEmbedding (symbol a (∏i,p i))=
      ∏i,(actualSextic (Ideal.span {p i}) (hg i) (Ideal.Quotient.mk _ a))^2 := by
  change eisEmbedding (idealSymbol (Ideal.span {∏i,p i}) a)=_
  rw [←idealRowHom_square,idealRowHom_product p hg Finset.univ a]
  simp only [ActualEisensteinCubic.finiteSquarefreeRow,actualSextic,Finset.prod_pow]

theorem conjugate_symbol_product {ι : Type*} [Fintype ι]
    (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (a : Eis) :
    star (eisEmbedding (symbol a (∏i,p i)))=
      ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        (Ideal.Quotient.mk _ a) := by
  rw [embedded_symbol_product p hg a,star_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [star_pow,MulChar.star_apply',MulChar.pow_apply' _ (by decide : (2:ℕ)≠0)]

theorem conjugate_symbol_product_frequency {ι : Type*} [Fintype ι]
    (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (a : Eis)
    (σ : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i : Eis⧸Ideal.span {p i})*h i) :
    star (eisEmbedding (symbol a (∏i,p i)))=
      ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        ((σ i : Eis⧸Ideal.span {p i})*h i) := by
  rw [conjugate_symbol_product p hg a]
  simp only [ha]

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_field_inverse {F : Type*} [Field F] (a d B : F) (σ ε : Fˣ) (h x : F)
    (had : a*d=1) (ha : a=(σ:F)*h) (hε : B*(σ:F)*(ε:F)=-1) :
    h≠0 ∧ -d*B⁻¹*x=((ε:F)*x)*h⁻¹ := by
  have hh : h≠0 := by
    intro hz
    rw [ha,hz,mul_zero,zero_mul] at had
    exact zero_ne_one had
  have hB : B≠0 := by
    intro hz
    rw [hz,zero_mul,zero_mul] at hε
    exact neg_ne_zero.mpr (one_ne_zero : (1:F)≠0) hε.symm
  have hd : d=((σ:F)*h)⁻¹ := eq_inv_of_mul_eq_one_right (ha ▸ had)
  have he : (ε:F)=-(B*(σ:F))⁻¹ := by
    have heq : (B*(σ:F))*(-(ε:F))=1 := by linear_combination -hε
    exact neg_eq_iff_eq_neg.mp (eq_inv_of_mul_eq_one_right heq)
  refine ⟨hh,?_⟩
  rw [hd,he]
  field_simp

noncomputable local instance A4quotientField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance A4quotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

lemma A4_active_local {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (a b c0 d : Eis) (hdet : a*d-b*(c0*∏i,p i)=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (x : Eis) (i : ι) :
    h i≠0 ∧
      -(Ideal.Quotient.mk (Ideal.span {p i}) d)*
        (Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i))⁻¹*
        Ideal.Quotient.mk (Ideal.span {p i}) x =
      ((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk (Ideal.span {p i}) x)*(h i)⁻¹ := by
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (∏k,p k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
      (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
  have had : Ideal.Quotient.mk (Ideal.span {p i}) a*
      Ideal.Quotient.mk (Ideal.span {p i}) d=1 := by
    have he := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hdet
    simpa only [map_sub,map_mul,map_one,hz,mul_zero,sub_zero] using he
  exact A4_field_inverse _ _ _ (σ i) (ε i) (h i) _ had (ha i) (hε i)

lemma A4_complement_inverse {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (c0 U w : Eis) (hbez : U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (i : ι) (v t : Eis) (hlocal : t*p i+v*cofactor p i=1) :
    (Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i))⁻¹=
      Ideal.Quotient.mk (Ideal.span {p i}) (w*v) := by
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (∏k,p k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
      (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
  have hp0 : Ideal.Quotient.mk (Ideal.span {p i}) (p i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hw := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hbez
  have hv := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hlocal
  simp only [map_add,map_mul,map_pow,map_one,hz,mul_zero,zero_add] at hw
  simp only [map_add,map_mul,map_one,hp0,mul_zero,zero_add] at hv
  symm
  apply eq_inv_of_mul_eq_one_right
  simp only [map_mul,map_pow]
  calc
    _ = ((Ideal.Quotient.mk _ ramifiedTraceLambda)^3*Ideal.Quotient.mk _ w*
        Ideal.Quotient.mk _ c0)*(Ideal.Quotient.mk _ v*Ideal.Quotient.mk _ (cofactor p i)) := by ring
    _ = 1 := by rw [hw,hv,mul_one]

end ShortDraftCusp

end

end OAI

end Source281

/- Original source: OAI/NumberTheory/DirichletL/Cusp/ResiduePhases.lean; sha256: fd5db4ed279545cf88cb848bd498275c8d24dc8f3d158190db1cda1ecb52f718 -/
section Source282
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

namespace ShortDraftCusp
open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_bad_modulus_ne_zero (c0:Eis) (hc0:c0≠0) : ramifiedTraceLambda^3*c0≠0 := by
  apply mul_ne_zero _ hc0
  apply pow_ne_zero
  intro hz
  have he:=ramifiedEmbedding_traceLambda
  rw [hz,map_zero] at he
  exact eisLam_ne_zero he.symm

def A4BadPhase (c0:Eis) (hc0:c0≠0) (d U x:Eis) : ℂ :=
  quotientTrace (ramifiedTraceLambda^3*c0) (A4_bad_modulus_ne_zero c0 hc0)
    (Ideal.Quotient.mk _ (-d*U*x))

lemma A4BadPhase_eq (c0:Eis) (hc0:c0≠0) (d U x:Eis) :
    A4BadPhase c0 hc0 d U x =
      ShortDraftTrace.breveE (-(eisEmbedding d*eisEmbedding U*(eisEmbedding x/eisLam^4))/eisEmbedding c0) := by
  change ShortDraftTrace.breveE
    (eisEmbedding (-d*U*x)/(eisEmbedding (ramifiedTraceLambda^3*c0)*eisLam))=_
  simp only [map_mul,map_pow,map_neg,ramifiedEmbedding_traceLambda]
  congr 1
  field_simp [eisLam_ne_zero,eisEmbedding_ne_zero hc0]

noncomputable local instance A4phaseField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance A4phaseFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem A4_phase_product {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (a b c0 d U w x:Eis) (hc0:c0≠0)
    (hdet:a*d-b*(c0*∏i,p i)=1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1) :
    ShortDraftTrace.breveE (-(eisEmbedding d*(eisEmbedding x/eisLam^4))/
      (eisEmbedding c0*eisEmbedding (∏i,p i))) =
    A4BadPhase c0 hc0 d U x *
      ∏i,quotientTrace (p i) (hp i)
        (((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ x)*(h i)⁻¹) := by
  let hr : (∏i,p i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hs:=ShortDraftCRT.normalized_crt_pair eisEmbedding ShortDraftTrace.breveE
    ramifiedTraceLambda c0 (∏i,p i) d x U w
    (by simpa only [ramifiedEmbedding_traceLambda] using eisLam_ne_zero)
    (eisEmbedding_ne_zero hc0) (eisEmbedding_ne_zero hr) hbez
  simp only [ramifiedEmbedding_traceLambda] at hs
  rw [hs,←A4BadPhase_eq c0 hc0 d U x]
  congr 1
  have he : ShortDraftTrace.breveE (eisEmbedding (-d*w*x)/(eisLam*eisEmbedding (∏i,p i)))=
      quotientTrace (∏i,p i) hr (Ideal.Quotient.mk _ (-d*w*x)) := by
    simp only [quotientTrace,eisTraceModChar,traceModChar_mk]
    congr 1
    rw [mul_comm eisLam]
  rw [he,addChar_finite_crt_factor (fun i=>Eis⧸Ideal.span {p i})
    (productElementCRT p hcop)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [productElementCRT_mk]
  obtain ⟨t,v,hlocal⟩:=bezout_of_principal_coprime (cofactor_coprime p hcop i)
  have hc:=coordinate_trace_character p hp hcop i t v hlocal
  change coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
    (quotientTrace (∏i,p i) hr) i (Ideal.Quotient.mk _ (-d*w*x))=_
  change coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
    (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates (∏i,p i) hr) i
    (Ideal.Quotient.mk _ (-d*w*x))=_
  rw [hc]
  change quotientTrace (p i) (hp i)
    (Ideal.Quotient.mk _ v*Ideal.Quotient.mk _ (-d*w*x))=_
  apply congrArg (quotientTrace (p i) (hp i))
  have hinv:=A4_complement_inverse p c0 U w hbez i v t hlocal
  have hphase:=(A4_active_local p a b c0 d hdet σ ε h ha hε x i).2
  rw [hinv] at hphase
  convert hphase using 1 ; simp only [map_mul,map_neg] ; ring

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance A4frequencyField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance A4frequencyFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem A3_A4_frequency_product {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (a b c0 d U w x:Eis) (hc0:c0≠0)
    (hdet:a*d-b*(c0*∏i,p i)=1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1) :
    star (eisEmbedding (CubicJacobiGlobal.symbol a (∏i,p i)))*
      ShortDraftTrace.breveE (-(eisEmbedding d*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i))) =
    A4BadPhase c0 hc0 d U x *
      ∏i,frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (σ i) (ε i) (Ideal.Quotient.mk _ x) (h i) := by
  rw [conjugate_symbol_product_frequency p hg a σ h ha,
    A4_phase_product p hp hcop a b c0 d U w x hc0 hdet hbez σ ε h ha hε]
  calc
    _ = A4BadPhase c0 hc0 d U x *
      ((∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        ((σ i:Eis⧸Ideal.span {p i})*h i))*
       ∏i,quotientTrace (p i) (hp i)
        (((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ x)*(h i)⁻¹)) := by ring
    _ = _ := by
      congr 1
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      have hn:=(A4_active_local p a b c0 d hdet σ ε h ha hε x i).1
      simp only [frequencyMultiplier,ite_eq_right hn]

lemma A4BadPhase_eq_of_residue (c0:Eis) (hc0:c0≠0) (d U d' U' x:Eis)
    (hres:ramifiedTraceLambda^3*c0∣d*U-d'*U') :
    A4BadPhase c0 hc0 d U x=A4BadPhase c0 hc0 d' U' x := by
  unfold A4BadPhase
  congr 1
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have hd:=dvd_mul_of_dvd_left hres (-x)
  convert hd using 1 ; ring

lemma A4BadPhase_norm (c0:Eis) (hc0:c0≠0) (d U x:Eis) :
    ‖A4BadPhase c0 hc0 d U x‖=1 := by
  rw [A4BadPhase_eq]
  exact breveE_norm _

end ShortDraftCusp

open scoped BigOperators Classical

namespace IdealGaussCRT
open CubicEisenstein

lemma finiteAdditiveFourierCoeff_mulShift {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R→ℂ) (k h : R) :
    finiteAdditiveFourierCoeff (ψ.mulShift k) φ h=
      finiteAdditiveFourierCoeff ψ φ (k*h) := by
  unfold finiteAdditiveFourierCoeff
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [AddChar.mulShift_apply]
  congr 2
  ring

theorem finite_fourier_weighted_shift_crt {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e : T≃+*∀i,R i)
    (ψ : AddChar T ℂ) (ψi : ∀i,AddChar (R i) ℂ) (k : ∀i,(R i)ˣ)
    (hψ : ∀i,coordinateAddChar R e ψ i=(ψi i).mulShift (k i:R i))
    (φ κ : ∀i,R i→ℂ) :
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun x=>∏i,φ i (e x i)) h *
      ∏i,κ i ((k i:R i)*e h i))=
      ∏i,∑h:R i,finiteAdditiveFourierCoeff (ψi i) (φ i) h*κ i h := by
  rw [finite_fourier_weighted_crt R e ψ φ (fun i h=>κ i ((k i:R i)*h))]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [hψ,finiteAdditiveFourierCoeff_mulShift]
  exact Equiv.sum_comp (k i).mulLeft
    (fun h:R i=>finiteAdditiveFourierCoeff (ψi i) (φ i) h*κ i h)

theorem finiteAdditiveFourierCoeff_pair {T R S : Type*}
    [CommRing T] [CommRing R] [CommRing S]
    [Fintype T] [Fintype R] [Fintype S]
    (e : T≃+*R×S) (ψ : AddChar T ℂ) (φ : R→ℂ) (f : S→ℂ) (h : T) :
    finiteAdditiveFourierCoeff ψ (fun t=>φ (e t).1*f (e t).2) h=
      finiteAdditiveFourierCoeff (leftAddChar e ψ) φ (e h).1 *
      finiteAdditiveFourierCoeff (rightAddChar e ψ) f (e h).2 := by
  have hs : (∑x:T,(φ (e x).1*f (e x).2)*ψ (-h*x))=
      (∑x:R,φ x*leftAddChar e ψ (-(e h).1*x))*
        (∑y:S,f y*rightAddChar e ψ (-(e h).2*y)) := by
    calc
      _ = ∑x:T,(φ (e x).1*leftAddChar e ψ (-(e h).1*(e x).1))*
          (f (e x).2*rightAddChar e ψ (-(e h).2*(e x).2)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [addChar_crt_factor e ψ (-h*x)]
        simp only [map_mul,map_neg,Prod.fst_mul,Prod.snd_mul,Prod.fst_neg,Prod.snd_neg]
        ring
      _ = ∑x:R×S,(φ x.1*leftAddChar e ψ (-(e h).1*x.1))*
          (f x.2*rightAddChar e ψ (-(e h).2*x.2)) :=
        Equiv.sum_comp e.toEquiv (fun x:R×S=>(φ x.1*leftAddChar e ψ (-(e h).1*x.1))*
          (f x.2*rightAddChar e ψ (-(e h).2*x.2)))
      _ = _ := by rw [Fintype.sum_prod_type,Finset.sum_mul_sum]
  have hc : (Fintype.card T:ℂ)=(Fintype.card R:ℂ)*(Fintype.card S:ℂ) := by
    rw [Fintype.card_congr e.toEquiv,Fintype.card_prod,Nat.cast_mul]
  simp only [finiteAdditiveFourierCoeff,hs,hc]
  ring

end IdealGaussCRT

namespace LocalReflectionBrackets
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance canonicalShiftField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance canonicalShiftFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem canonical_finite_reflection_shifted_crt {ι T : Type*} [Fintype ι]
    [CommRing T] [Fintype T]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (e : T≃+*∀i,Eis⧸P i) (ψ : AddChar T ℂ)
    (ψi : ∀i,AddChar (Eis⧸P i) ℂ) (hψi : ∀i,(ψi i).IsPrimitive)
    (k : ∀i,(Eis⧸P i)ˣ)
    (hshift : ∀i,coordinateAddChar (fun i=>Eis⧸P i) e ψ i=(ψi i).mulShift (k i:Eis⧸P i))
    (hg : ∀i,lambda∉P i) (hchar : ∀i,ringChar (Eis⧸P i)≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6) (σ ε : ∀i,(Eis⧸P i)ˣ) (x : ∀i,Eis⧸P i) :
    let χ := fun i=>actualSextic (P i) (hg i)
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) ((k i:Eis⧸P i)*e h i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  let χ := fun i=>actualSextic (P i) (hg i)
  let f := fun i=>frequencyRow (χ i) (ψi i) (j i) (σ i) (ε i) (x i)
  have hsum : (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) ((k i:Eis⧸P i)*e h i))=
      ∑h:∀i,Eis⧸P i,∏i,f i (h i) := by
    rw [finite_fourier_weighted_shift_crt (fun i=>Eis⧸P i) e ψ ψi k hshift
      (fun i t=>(χ i^j i) t) (fun i=>frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i))]
    exact Fintype.prod_sum f
  have hactive (i : ι) : (∑h:(Eis⧸P i)ˣ,f i h)=
      (((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i) := by
    exact canonical_frequencyRow_units (P i) (hg i) (hchar i) (ψi i)
      (hψi i) (j i) (hj i) (σ i) (ε i) (x i)
  have hzero (i : ι) : f i 0=if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0 := by
    exact canonical_frequencyRow_zero (P i) (hg i) (hchar i) (ψi i) (j i) (hj i) (σ i) (ε i) (x i)
  change (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) ((k i:Eis⧸P i)*e h i))=_
  rw [hsum,FixedRayActiveSet.product_sum_by_active_set (fun i=>Eis⧸P i) f]
  simp only [hactive,hzero]
  rfl

end LocalReflectionBrackets

namespace FiniteGaussPhase

section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem exists_product_trace_shifts {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) :
    ∃k : ∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∀i,Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*(k i:Eis⧸Ideal.span {p i})=1) ∧
      ∀i,coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
        (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
          (quotientTrace (p i) (hp i)).mulShift (k i:Eis⧸Ideal.span {p i}) := by
  have hone (i : ι) : ∃k : (Eis⧸Ideal.span {p i})ˣ,
      Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*(k:Eis⧸Ideal.span {p i})=1 ∧
      coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
        (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
          (quotientTrace (p i) (hp i)).mulShift (k:Eis⧸Ideal.span {p i}) := by
    obtain ⟨u,v,hbez⟩:=bezout_of_principal_coprime (cofactor_coprime p hcop i)
    have hv : Ideal.Quotient.mk (Ideal.span {p i}) v*
        Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)=1 := by
      simpa only [mul_comm] using bezout_inverse_left hbez
    refine ⟨Units.mkOfMulEqOne _ _ hv,?_,?_⟩
    · simpa only [Units.val_mkOfMulEqOne,mul_comm] using hv
    · exact coordinate_trace_character p hp hcop i u v hbez
  choose k hki hkψ using hone
  exact ⟨k,hki,hkψ⟩

noncomputable def productTraceShift {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) :
    ∀i,(Eis⧸Ideal.span {p i})ˣ :=
  (exists_product_trace_shifts p hp hcop).choose

lemma productTraceShift_inverse {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*
      (productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})=1 :=
  (exists_product_trace_shifts p hp hcop).choose_spec.1 i

lemma productTraceShift_character {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) (i:ι) :
    coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
        (quotientTrace (p i) (hp i)).mulShift
          (productTraceShift p hp hcop i:Eis⧸Ideal.span {p i}) :=
  (exists_product_trace_shifts p hp hcop).choose_spec.2 i

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem product_trace_fourier_factor {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    [Fintype (Eis⧸Ideal.span {∏i,p i})] [∀i,Fintype (Eis⧸Ideal.span {p i})]
    (φ : ∀i,(Eis⧸Ideal.span {p i})→ℂ) (H:Eis⧸Ideal.span {∏i,p i}) :
    finiteAdditiveFourierCoeff
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))
      (fun t=>∏i,φ i (productElementCRT p hcop t i)) H=
    ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (φ i)
      ((productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i) := by
  rw [finiteAdditiveFourierCoeff_crt]
  apply Finset.prod_congr rfl
  intro i hi
  rw [productTraceShift_character,finiteAdditiveFourierCoeff_mulShift]

theorem product_trace_fourier_weighted {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    [Fintype (Eis⧸Ideal.span {∏i,p i})] [∀i,Fintype (Eis⧸Ideal.span {p i})]
    (φ κ : ∀i,(Eis⧸Ideal.span {p i})→ℂ) :
    (∑H:Eis⧸Ideal.span {∏i,p i},finiteAdditiveFourierCoeff
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))
      (fun t=>∏i,φ i (productElementCRT p hcop t i)) H *
      ∏i,κ i ((productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i))=
    ∏i,∑h:Eis⧸Ideal.span {p i},finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (φ i) h*κ i h := by
  exact finite_fourier_weighted_shift_crt (fun i=>Eis⧸Ideal.span {p i})
    (productElementCRT p hcop) _ (fun i=>quotientTrace (p i) (hp i))
    (productTraceShift p hp hcop) (productTraceShift_character p hp hcop) φ κ

end FiniteGaussPhase

namespace LocalReflectionBrackets
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance productReflectionField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance productReflectionFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem canonical_product_reflection_crt {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (hchar : ∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (x : ∀i,Eis⧸Ideal.span {p i})
    [Fintype (Eis⧸Ideal.span {∏i,p i})] :
    let χ := fun i=>actualSextic (Ideal.span {p i}) (hg i)
    let ψ := quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
    let ψi := fun i=>quotientTrace (p i) (hp i)
    (∑H:Eis⧸Ideal.span {∏i,p i},finiteAdditiveFourierCoeff ψ
      (principalSexticRow (fun i=>Ideal.span {p i}) hcop hg j (∏i,p i)
        (span_finset_prod Finset.univ p)) H *
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i)
        ((productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸Ideal.span {p i}):ℂ)⁻¹ else 0) := by
  let e:=productElementCRT p hcop
  have hrow : principalSexticRow (fun i=>Ideal.span {p i}) hcop hg j (∏i,p i)
      (span_finset_prod Finset.univ p)=
      fun t=>∏i,(actualSextic (Ideal.span {p i}) (hg i)^j i) (e t i) := by
    funext t
    rfl
  dsimp only
  rw [hrow]
  exact canonical_finite_reflection_shifted_crt (fun i=>Ideal.span {p i}) e _
    (fun i=>quotientTrace (p i) (hp i))
    (fun i=>GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i))
    (productTraceShift p hp hcop) (productTraceShift_character p hp hcop)
    hg hchar j hj σ ε x

end LocalReflectionBrackets

open scoped Classical BigOperators

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem A4BadPhase_strong_sector (M c0 r r0 d d0 U U0 x:Eis) (hc0:c0≠0)
    (hM:ramifiedTraceLambda^3∣M) (hc:c0∣M)
    (hr:M^2∣r-r0) (hd:M*c0∣d-d0)
    (hcop:IsCoprime (ramifiedTraceLambda^3*c0) r)
    (hU:ramifiedTraceLambda^3*c0∣U*r-1)
    (hU0:ramifiedTraceLambda^3*c0∣U0*r0-1) :
    A4BadPhase c0 hc0 d U x=A4BadPhase c0 hc0 d0 U0 x := by
  obtain ⟨hrr,hdd⟩:=ShortDraftCRT.strong_sector_additive_congruences
    M ramifiedTraceLambda c0 r r0 d d0 hM hc hr hd
  apply A4BadPhase_eq_of_residue
  have he:=ShortDraftCRT.inverse_weight_residue_congr
    (ramifiedTraceLambda^3*c0) r r0 U U0 d d0 hcop hrr hU hU0 hdd
  have hn:=dvd_neg.mpr he
  convert hn using 1 ; ring

def A4PhaseFromResidue (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}) (x:Eis) : ℂ :=
  quotientTrace (ramifiedTraceLambda^3*c0) (A4_bad_modulus_ne_zero c0 hc0)
    (v*Ideal.Quotient.mk _ x)

lemma A4BadPhase_as_fixed_residue (c0:Eis) (hc0:c0≠0) (d U:Eis) :
    A4BadPhase c0 hc0 d U=
      A4PhaseFromResidue c0 hc0 (Ideal.Quotient.mk _ (-d*U)) := by
  funext x
  simp only [A4BadPhase,A4PhaseFromResidue,map_mul]

lemma A4PhaseFromResidue_range (c0:Eis) (hc0:c0≠0) :
    (Set.range (A4PhaseFromResidue c0 hc0)).Finite ∧
      (Set.range (A4PhaseFromResidue c0 hc0)).ncard≤
        Ideal.absNorm (Ideal.span {ramifiedTraceLambda^3*c0}) := by
  let:Finite (Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}):=
    finite_quotient_span (A4_bad_modulus_ne_zero c0 hc0)
  refine ⟨Set.finite_range _,?_⟩
  have h:=Set.ncard_image_le (s:=Set.univ) (f:=A4PhaseFromResidue c0 hc0)
  simpa only [Set.image_univ,Set.ncard_univ,Ideal.absNorm_apply,Submodule.cardQuot_apply] using h

end ShortDraftCusp

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

variable (Ψ Φ:Eis→*ℂ) (h:∀n:Eis,lambda^2∣n-1→Ψ n=Φ n)
include h

lemma columnWeight_congr_primary (I:Ideal Eis) : columnWeight Ψ I=columnWeight Φ I := by
  by_cases hi:primaryGenerator I=0
  · simp only [columnWeight,squarefreeGaussCoefficient,hi,ne_eq,not_true_eq_false,and_false,
      dite_false,zero_mul]
  · rw [columnWeight,columnWeight,h _ (primaryGenerator_spec I hi).2]

lemma cubeWeight_congr_primary (I:Ideal Eis) : cubeWeight Ψ I=cubeWeight Φ I := by
  change star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*Ψ (primaryGenerator I)^3/
      (Ideal.absNorm I:ℂ)=star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*Φ (primaryGenerator I)^3/
      (Ideal.absNorm I:ℂ)
  by_cases hi:primaryGenerator I=0
  · simp only [hi,FiniteGaussPhase.angularFactor,map_zero,norm_zero,Complex.ofReal_zero,
      div_zero,star_zero,zero_pow (by decide : (3:ℕ)≠0),zero_mul,zero_div]
  · rw [h _ (primaryGenerator_spec I hi).2]

theorem completedT_congr_primary (W:ℝ→ℂ) (X:ℝ) : completedT Ψ W X=completedT Φ W X := by
  unfold completedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [summand,summand,columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]

lemma completedMellinCoefficient_congr_primary (p:CompletedMellinIndex) :
    completedMellinCoefficient Ψ p=completedMellinCoefficient Φ p := by
  unfold completedMellinCoefficient
  rw [columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]

theorem completedBesselProfile_congr_primary (q:ℝ) :
    completedBesselProfile Ψ q=completedBesselProfile Φ q := by
  have he:completedMellinCoefficient Ψ=completedMellinCoefficient Φ:=
    funext (completedMellinCoefficient_congr_primary Ψ Φ h)
  simp only [completedBesselProfile,he]

end CompletedGauss

namespace CubicEisenstein
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O
lemma fixedThetaTwist_congr_primary (Ψ Φ:Eis→*ℂ)
    (h:∀n:Eis,lambda^2∣n-1→Ψ n=Φ n) : fixedThetaTwist Ψ=fixedThetaTwist Φ := by
  funext n
  by_cases hn:lambda^2∣n-1
  · rw [fixedThetaTwist_primary Ψ n hn,fixedThetaTwist_primary Φ n hn,h n hn]
  · rw [fixedThetaTwist_not_primary Ψ n hn,fixedThetaTwist_not_primary Φ n hn]
end CubicEisenstein

open scoped Classical BigOperators

namespace ShortDraftCRT
open ActualEisensteinCubic FiniteGaussPhase ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

def finiteCrossNumerator (a c l:Eis) (p h:ι→Eis) : Eis :=
  a*(∏i,p i)+l^2*c*∑i,h i*cofactor p i

lemma prime_dvd_other_cofactor (p:ι→Eis) {i k:ι} (hik:i≠k) : p i∣cofactor p k := by
  exact Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨hik,Finset.mem_univ i⟩)

lemma finiteCrossNumerator_local (a c l:Eis) (p h:ι→Eis) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (finiteCrossNumerator a c l p h)=
      Ideal.Quotient.mk (Ideal.span {p i}) (l^2*c*cofactor p i)*
        Ideal.Quotient.mk (Ideal.span {p i}) (h i) := by
  let q:=Ideal.Quotient.mk (Ideal.span {p i})
  have hz:q (∏k,p k)=0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨cofactor p i, (prime_mul_cofactor p i).symm⟩
  have hs:(∑k,q (h k)*q (cofactor p k))=q (h i)*q (cofactor p i) := by
    apply Finset.sum_eq_single i
    · intro k hk hki
      have hk0:q (cofactor p k)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr (prime_dvd_other_cofactor p hki.symm))
      rw [hk0,mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  change q (finiteCrossNumerator a c l p h)=q (l^2*c*cofactor p i)*q (h i)
  simp only [finiteCrossNumerator,map_add,map_mul,map_sum,map_pow,hz,mul_zero,zero_add,hs]
  ring

lemma finiteCrossNumerator_fixed (N a c l:Eis) (p h:ι→Eis)
    (hh:∀i,N∣h i) : N∣finiteCrossNumerator a c l p h-a*(∏i,p i) := by
  have hs:N∣∑i,h i*cofactor p i:=Finset.dvd_sum (fun i _=>dvd_mul_of_dvd_left (hh i) _)
  convert dvd_mul_of_dvd_right hs (l^2*c) using 1 ; simp [finiteCrossNumerator]

lemma finiteCrossNumerator_fixed_sector {κ:Type*} [Fintype κ]
    (M a c l:Eis) (p h:ι→Eis) (p0 h0:κ→Eis)
    (hc:c∣M) (hh:∀i,M^2∣h i) (hh0:∀i,M^2∣h0 i)
    (hr:M^2∣(∏i,p i)-(∏i,p0 i)) :
    M*c∣finiteCrossNumerator a c l p h-finiteCrossNumerator a c l p0 h0 := by
  have hmc:M*c∣M^2:=by simpa only [pow_two] using mul_dvd_mul_left M hc
  apply hmc.trans
  have h1:=finiteCrossNumerator_fixed (M^2) a c l p h hh
  have h0:=finiteCrossNumerator_fixed (M^2) a c l p0 h0 hh0
  have h2:=dvd_mul_of_dvd_right hr a
  convert dvd_sub (dvd_add h1 h2) h0 using 1 ; ring

lemma finiteCrossNumerator_coprime (a c l:Eis) (p h:ι→Eis)
    (hbase:IsCoprime a c) (hpair:Pairwise (Function.onFun IsCoprime p))
    (hc:∀i,IsCoprime c (p i)) (hl:∀i,IsCoprime l (p i))
    (hh:∀i,IsCoprime (h i) (p i)) :
    IsCoprime (finiteCrossNumerator a c l p h) (c*∏i,p i) := by
  have hmodc:c∣finiteCrossNumerator a c l p h-a*(∏i,p i):=by
    refine ⟨l^2*(∑i,h i*cofactor p i),?_⟩
    unfold finiteCrossNumerator
    ring
  have hcR:IsCoprime c (∏i,p i):=IsCoprime.prod_right (fun i _=>hc i)
  have hca:IsCoprime c (finiteCrossNumerator a c l p h):=
    (CanonicalRowCompletion.isCoprime_congr_mod c _ _ hmodc).mpr (hbase.symm.mul_right hcR)
  apply hca.symm.mul_right
  apply IsCoprime.prod_right
  intro i hi
  have hcof:IsCoprime (p i) (cofactor p i):=
    IsCoprime.prod_right (fun k hk=>hpair (Ne.symm (Finset.mem_erase.mp hk).1))
  have hterm:IsCoprime (p i) (l^2*c*cofactor p i*h i):=
    (((hl i).symm.pow_right : IsCoprime (p i) (l^2)).mul_right (hc i).symm).mul_right hcof |>.mul_right (hh i).symm
  have he:=finiteCrossNumerator_local a c l p h i
  rw [←map_mul] at he
  have hd:p i∣finiteCrossNumerator a c l p h-l^2*c*cofactor p i*h i:=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  exact ((CanonicalRowCompletion.isCoprime_congr_mod (p i) _ _ hd).mpr hterm).symm

end ShortDraftCRT

end

end OAI

end Source282

/- Original source: OAI/NumberTheory/DirichletL/ChineseRemainder/FrequencyLifts.lean; sha256: 782092da365c7773ff6a804a76c04ee2f4b6d8fd033158b43929f14094c5f250 -/
section Source283
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

open scoped Classical BigOperators

namespace ShortDraftCRT
open ActualEisensteinCubic FiniteGaussPhase ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

omit [Fintype ι] in
theorem exists_strong_unit_frequency_lifts (M:Eis) (p:ι→Eis)
    (hM:∀i,IsCoprime M (p i)) (x:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    ∃h:ι→Eis,(∀i,M^2∣h i) ∧
      (∀i,Ideal.Quotient.mk (Ideal.span {p i}) (h i)=(x i:Eis⧸Ideal.span {p i})) ∧
      ∀i,IsCoprime (h i) (p i) := by
  have hx (i:ι) := exists_frequency_lift (M^2) (p i)
    (Quotient.out (x i:Eis⧸Ideal.span {p i})) (hM i).pow_left
  choose h hh hd using hx
  have he (i:ι):Ideal.Quotient.mk (Ideal.span {p i}) (h i)=(x i:Eis⧸Ideal.span {p i}) := by
    calc
      _=Ideal.Quotient.mk (Ideal.span {p i}) (Quotient.out (x i:Eis⧸Ideal.span {p i})) :=
        Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (hd i))
      _=x i:=Ideal.Quotient.mk_out _
  refine ⟨h,hh,he,?_⟩
  intro i
  apply IsCoprime.symm
  apply (isUnit_quotient_span_iff (p i) (h i)).mp
  rw [he]
  exact (x i).isUnit

theorem finiteCrossNumerator_fraction (a c l:Eis) (p h:ι→Eis)
    (hc:c≠0) (hp:∀i,p i≠0) :
    eisEmbedding (finiteCrossNumerator a c l p h)/eisEmbedding (c*∏i,p i)=
      eisEmbedding a/eisEmbedding c+eisEmbedding l^2*
        ∑i,eisEmbedding (h i)/eisEmbedding (p i) := by
  have hR:(∏i,p i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hcC:=eisEmbedding_ne_zero hc
  have hRC:=eisEmbedding_ne_zero hR
  have hs:eisEmbedding (∑i,h i*cofactor p i)/eisEmbedding (∏i,p i)=
      ∑i,eisEmbedding (h i)/eisEmbedding (p i) := by
    rw [map_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hpi:=eisEmbedding_ne_zero (hp i)
    have hr:eisEmbedding (p i)*eisEmbedding (cofactor p i)=eisEmbedding (∏i,p i) := by
      rw [←map_mul,prime_mul_cofactor]
    rw [map_mul]
    apply (div_eq_div_iff hRC hpi).mpr
    linear_combination eisEmbedding (h i)*hr
  simp only [finiteCrossNumerator,map_add,map_mul,map_pow]
  rw [←hs]
  field_simp [hcC,hRC]

end ShortDraftCRT

open scoped BigOperators Classical

namespace IdealGaussCRT
open CubicEisenstein

theorem finite_fourier_sum_reindex {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e:T≃+*∀i,R i)
    (ψ:AddChar T ℂ) (ψi:∀i,AddChar (R i) ℂ) (k:∀i,(R i)ˣ)
    (hψ:∀i,coordinateAddChar R e ψ i=(ψi i).mulShift (k i:R i))
    (φ:∀i,R i→ℂ) (weight:(∀i,R i)→ℂ) :
    (∑H:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,φ i (e t i)) H*
      weight (fun i=>(k i:R i)*e H i))=
    ∑h:∀i,R i,(∏i,finiteAdditiveFourierCoeff (ψi i) (φ i) (h i))*weight h := by
  let E:T≃(∀i,R i):=e.toEquiv.trans (Equiv.piCongrRight (fun i=>(k i).mulLeft))
  have hc (H:T) : finiteAdditiveFourierCoeff ψ (fun t=>∏i,φ i (e t i)) H=
      ∏i,finiteAdditiveFourierCoeff (ψi i) (φ i) ((k i:R i)*e H i) := by
    rw [finiteAdditiveFourierCoeff_crt]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hψ,finiteAdditiveFourierCoeff_mulShift]
  simp only [hc]
  exact Equiv.sum_comp E
    (fun h:∀i,R i=>(∏i,finiteAdditiveFourierCoeff (ψi i) (φ i) (h i))*weight h)

end IdealGaussCRT

namespace FiniteGaussPhase
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem product_trace_fourier_sum_reindex {ι : Type*} [Fintype ι]
    (p:ι→Eis) (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    [Fintype (Eis⧸Ideal.span {∏i,p i})] [∀i,Fintype (Eis⧸Ideal.span {p i})]
    (φ:∀i,(Eis⧸Ideal.span {p i})→ℂ)
    (weight:(∀i,Eis⧸Ideal.span {p i})→ℂ) :
    (∑H:Eis⧸Ideal.span {∏i,p i},finiteAdditiveFourierCoeff
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))
      (fun t=>∏i,φ i (productElementCRT p hcop t i)) H*
      weight (fun i=>(productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i))=
    ∑h:∀i,Eis⧸Ideal.span {p i},
      (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (φ i) (h i))*weight h := by
  exact finite_fourier_sum_reindex (fun i=>Eis⧸Ideal.span {p i})
    (productElementCRT p hcop) _ (fun i=>quotientTrace (p i) (hp i))
    (productTraceShift p hp hcop) (productTraceShift_character p hp hcop) φ weight

end FiniteGaussPhase

namespace FixedRayActiveSet

lemma sum_nonzero_ite {F : Type*} [Field F] [Fintype F] (f:F→ℂ) :
    (∑x:F,if x≠0 then f x else 0)=∑u:Fˣ,f (u:F) := by
  calc
    _ = ∑x∈(Finset.univ:Finset F).filter (fun x=>x≠0),f x := by rw [Finset.sum_filter]
    _ = ∑x:{x:F//x≠0},f x := by
      apply Finset.sum_subtype
      intro x
      simp
    _ = _ := (Equiv.sum_comp unitsEquivNeZero (fun x:{x:F//x≠0}=>f x)).symm

def activeStratum {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)] (A:Finset ι) :
    Finset (∀i,F i) := Finset.univ.filter (fun h=>∀i,h i≠0↔i∈A)

theorem sum_active_stratum {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (A:Finset ι) (f:∀i,F i→ℂ) :
    (∑h∈activeStratum F A,∏i,f i (h i))=
      (∏i∈A,∑u:(F i)ˣ,f i (u:F i))*
        (∏i∈(Finset.univ:Finset ι)\A,f i 0) := by
  classical
  let g:=fun i (x:F i)=>if (x≠0↔i∈A) then f i x else 0
  have hs : (∑h∈activeStratum F A,∏i,f i (h i))=
      ∏i,∑x:F i,g i x := by
    rw [activeStratum,Finset.sum_filter]
    calc
      _ = ∑h:∀i,F i,∏i,g i (h i) := by
        apply Finset.sum_congr rfl
        intro h hh
        exact (Fintype.prod_ite_zero (p:=fun i=>h i≠0↔i∈A) (f:=fun i=>f i (h i))).symm
      _ = _ := (Fintype.prod_sum g).symm
  have hg (i:ι) : (∑x:F i,g i x)=if i∈A then ∑u:(F i)ˣ,f i (u:F i) else f i 0 := by
    by_cases hi:i∈A
    · simpa only [g,hi,iff_true,ite_true] using sum_nonzero_ite (f i)
    · simp [g,hi]
  rw [hs]
  simp only [hg,Finset.prod_ite]
  have ha : (Finset.univ:Finset ι).filter (fun i=>i∈A)=A := by ext i;simp
  have hn : (Finset.univ:Finset ι).filter (fun i=>i∉A)=(Finset.univ:Finset ι)\A := by ext i;simp
  rw [ha,hn]

theorem sum_by_active_strata {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (weight:(∀i,F i)→ℂ) :
    (∑h:∀i,F i,weight h)=
      ∑A∈(Finset.univ:Finset ι).powerset,∑h∈activeStratum F A,weight h := by
  classical
  symm
  simp only [activeStratum,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  let A:Finset ι:=Finset.univ.filter (fun i=>h i≠0)
  have he : ∀i,h i≠0↔i∈A := by intro i;simp [A]
  rw [Finset.sum_eq_single A]
  · simp only [he,implies_true,ite_true]
  · intro B hB hBA
    have hbad : ¬(∀i,h i≠0↔i∈B) := by
      intro hgood
      apply hBA
      ext i
      simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and] using (hgood i).symm
    simp only [hbad,ite_false]
  · intro hnot
    exact (hnot (Finset.mem_powerset.mpr (Finset.filter_subset _ _))).elim

end FixedRayActiveSet

namespace LocalReflectionBrackets
open ActualEisensteinCubic CubicEisenstein CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance stratumField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance stratumFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem canonical_active_stratum {ι : Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (hchar:∀i,ringChar (Eis⧸P i)≠2)
    (ψ:∀i,AddChar (Eis⧸P i) ℂ) (hψ:∀i,(ψ i).IsPrimitive)
    (A:Finset ι) (j:ι→ℕ) (hj:∀i,j i<6)
    (σ ε:∀i,(Eis⧸P i)ˣ) (x:∀i,Eis⧸P i) :
    (∑h∈FixedRayActiveSet.activeStratum (fun i=>Eis⧸P i) A,
      ∏i,frequencyRow (actualSextic (P i) (hg i)) (ψ i) (j i) (σ i) (ε i) (x i) (h i))=
    (∏i∈A,(((actualSextic (P i) (hg i))⁻¹)^2) (σ i)*
      phase (actualSextic (P i) (hg i)) (ψ i) (j i) (ε i)*
      bracket (actualSextic (P i) (hg i)) (j i) (x i))*
    (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  rw [FixedRayActiveSet.sum_active_stratum]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact canonical_frequencyRow_units (P i) (hg i) (hchar i) (ψ i) (hψ i) (j i) (hj i) (σ i) (ε i) (x i)
  · apply Finset.prod_congr rfl
    intro i hi
    exact canonical_frequencyRow_zero (P i) (hg i) (hchar i) (ψ i) (j i) (hj i) (σ i) (ε i) (x i)

end LocalReflectionBrackets

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedTraceLambda_dvd_of_lambda_dvd (h:Eis) (hh:lambda∣h) :
    ramifiedTraceLambda∣h := by
  obtain ⟨q,hq⟩:=hh
  refine ⟨(paperLambdaUnit⁻¹:Eisˣ)*q,?_⟩
  change h=paperLambda*((paperLambdaUnit⁻¹:Eisˣ)*q)
  rw [paperLambda_eq,hq]
  have hu : (paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)=1 := by
    simpa only [Units.val_mul,Units.val_one] using
      congrArg (fun v:Eisˣ=>(v:Eis)) (mul_inv_cancel paperLambdaUnit)
  calc
    _=(paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)*(lambda*q) := by rw [hu,one_mul]
    _=_ := by ring

def paperLambdaQuotient (h:Eis) : Eis :=
  if hh:ramifiedTraceLambda∣h then hh.choose else 0

lemma paperLambdaQuotient_mul (h:Eis) (hh:ramifiedTraceLambda∣h) :
    ramifiedTraceLambda*paperLambdaQuotient h=h := by
  simp only [paperLambdaQuotient,dite_eq_left hh]
  exact hh.choose_spec.symm

lemma sourceCuspCoefficients_ramified_divisibility (j:Fin 3) (hj:j≠0) (h:Eis)
    (hh:(sourceCuspCoefficients j).value h≠0) : ramifiedTraceLambda∣h := by
  apply ramifiedTraceLambda_dvd_of_lambda_dvd
  fin_cases j
  · exact (hj rfl).elim
  · exact (ramifiedBesselValue_exact_lambda_valuation false h hh).1
  · exact (ramifiedBesselValue_exact_lambda_valuation true h hh).1

def sourceCuspPhaseNumerator (j:Fin 3) (u h:Eis) : Eis :=
  if j=0 then ramifiedTraceLambda*u^2*h else -u^2*paperLambdaQuotient h

lemma sourceCuspPhaseNumerator_embedding (j:Fin 3) (u h:Eis)
    (hh:(sourceCuspCoefficients j).value h≠0) :
    eisEmbedding (sourceCuspPhaseNumerator j u h)=
      -eisLam^4*cuspFrequency h*(eisEmbedding u)^2/(sourceCuspScale j:ℂ) := by
  by_cases hj:j=0
  · subst j
    simp only [sourceCuspPhaseNumerator,ite_true,map_mul,map_pow,
      ramifiedEmbedding_traceLambda,cuspFrequency,sourceCuspScale]
    norm_num only [Matrix.cons_val_zero,Complex.ofReal_one,div_one]
    field_simp [eisLam_ne_zero]
    linear_combination (eisEmbedding h*(eisEmbedding u)^2)*TraceLambdaPhase.eisLam_sq
  · have hdiv:=sourceCuspCoefficients_ramified_divisibility j hj h hh
    have hprod:=congrArg eisEmbedding (paperLambdaQuotient_mul h hdiv)
    have hscale:sourceCuspScale j=3 := by fin_cases j <;> simp_all [sourceCuspScale]
    have hfour:eisLam^4=(9:ℂ) := by
      calc
        eisLam^4=(eisLam^2)^2:=by ring
        _=9:=by rw [TraceLambdaPhase.eisLam_sq];norm_num
    rw [sourceCuspPhaseNumerator,ite_eq_right hj]
    simp only [map_mul,map_neg,map_pow]
    rw [cuspFrequency,hscale,←hprod,map_mul,ramifiedEmbedding_traceLambda,hfour]
    norm_num only [Complex.ofReal_ofNat]
    field_simp [eisLam_ne_zero]
    ; ring

lemma sourceCuspPhaseNumerator_phase (j:Fin 3) (u h c d:Eis) (hc:c≠0)
    (hh:(sourceCuspCoefficients j).value h≠0) :
    ShortDraftTrace.breveE (cuspFrequency h*(eisEmbedding u)^2*
      (eisEmbedding d/eisEmbedding c)/(sourceCuspScale j:ℂ))=
    ShortDraftTrace.breveE (-(eisEmbedding d*
      (eisEmbedding (sourceCuspPhaseNumerator j u h)/eisLam^4))/eisEmbedding c) := by
  rw [sourceCuspPhaseNumerator_embedding j u h hh]
  congr 1
  field_simp [eisLam_ne_zero,eisEmbedding_ne_zero hc,
    Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne']

end CubicEisenstein

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve QuadraticAllOddCRT
open ConcreteTraceCRT UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def cubicTwoSupplement : Eis→*ℂ where
  toFun n:=(actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal n)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]

def quadraticTwoSupplement : Eis→*ℂ :=
  InitialMeanSquare.normCharacter (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))

def twoSupplement : Eis→*ℂ := cubicTwoSupplement^2*quadraticTwoSupplement

lemma cubicTwoSupplement_norm (n:Eis) : ‖cubicTwoSupplement n‖≤1 := by
  change ‖(actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2)
    (Ideal.Quotient.mk cubicTwoIdeal n)‖≤1
  exact FiniteRayExpansion.norm_char_le_one _ _

lemma twoSupplement_norm (n:Eis) : ‖twoSupplement n‖≤1 := by
  change ‖cubicTwoSupplement n^2*quadraticTwoSupplement n‖≤1
  rw [norm_mul,norm_pow]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    _).trans (InitialMeanSquare.normCharacter_norm_le_one _ n)
  exact pow_le_one₀ (norm_nonneg _) (cubicTwoSupplement_norm n)

lemma cubicTwoSupplement_periodic (x y:Eis) (hxy:x-y∈Ideal.span {(8:Eis)}) :
    cubicTwoSupplement x=cubicTwoSupplement y := by
  have h2:x-y∈cubicTwoIdeal:=by
    obtain ⟨k,hk⟩:=Ideal.mem_span_singleton.mp hxy
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-4*k,?_⟩
    change x-y=(-2:Eis)*(-4*k)
    rw [hk]
    ring
  change (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal x)=
    (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal y)
  rw [Ideal.Quotient.eq.mpr h2]

lemma twoSupplement_periodic :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(8:Eis)}) twoSupplement := by
  intro x y hxy
  change cubicTwoSupplement x^2*quadraticTwoSupplement x=
    cubicTwoSupplement y^2*quadraticTwoSupplement y
  rw [cubicTwoSupplement_periodic x y hxy]
  congr 1
  exact CanonicalCoefficientClass.normCharacter_factorsModulo _ x y hxy

lemma idealRowHom_two_prime (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hs:Supported (Ideal.span {p})) :
    idealRowHom (2:Eis) (Ideal.span {p})=twoSupplement p := by
  let:(Ideal.span {p}).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  obtain ⟨hg,hc⟩:=supported_prime_data p hp hs
  have h2:idealRowHom (2:Eis) (Ideal.span {p})^2=cubicTwoSupplement p:=by
    rw [idealRowHom_prime _ _ hg]
    have he:=canonicalSextic_four_eq_fixed_two (Ideal.span {p}) hg p rfl hprimary
    have hfour:Ideal.Quotient.mk (Ideal.span {p}) (4:Eis)=
      (Ideal.Quotient.mk (Ideal.span {p}) (2:Eis))^2:=by norm_num [map_ofNat]
    rw [hfour,map_pow] at he
    change (actualSextic (Ideal.span {p}) hg) (Ideal.Quotient.mk _ 2)^2=
      (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal p)
    rw [canonicalSextic_pow_two]
    exact he
  have h3:idealRowHom (2:Eis) (Ideal.span {p})^3=quadraticTwoSupplement p:=by
    rw [idealRowHom_prime _ _ hg,←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
    change ((quadraticChar (Eis⧸Ideal.span {p}) (Ideal.Quotient.mk _ (2:Eis)):ℤ):ℂ)=_
    simp only [map_ofNat]
    rw [quadraticChar_two hc]
    have hn:Ideal.absNorm (Ideal.span {p})=Fintype.card (Eis⧸Ideal.span {p}):=by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    change ((ZMod.χ₈ (Fintype.card (Eis⧸Ideal.span {p})):ℤ):ℂ)=
      ((ZMod.χ₈ (Ideal.absNorm (Ideal.span {p})):ℤ):ℂ)
    rw [hn]
  have hn2:(2:Eis)∉Ideal.span {p}:=by
    intro hz
    have he: (2:Eis⧸Ideal.span {p})=0:=by
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hz
    exact Ring.two_ne_zero hc he
  have h6:idealRowHom (2:Eis) (Ideal.span {p})^6=1:=by
    rw [idealRowHom_prime _ _ hg]
    have he:=canonicalSextic_sixth_power_mask (Ideal.span {p}) hg (2:Eis)
    change actualSextic _ hg (Ideal.Quotient.mk _ ((2:Eis)^6))=_ at he
    simpa only [map_pow,ite_eq_right hn2] using he
  calc
    _=idealRowHom (2:Eis) (Ideal.span {p})*idealRowHom (2:Eis) (Ideal.span {p})^6:=by rw [h6,mul_one]
    _=idealRowHom (2:Eis) (Ideal.span {p})^3*(idealRowHom (2:Eis) (Ideal.span {p})^2)^2:=by ring
    _=twoSupplement p:=by
      rw [h2,h3]
      change quadraticTwoSupplement p*cubicTwoSupplement p^2=cubicTwoSupplement p^2*quadraticTwoSupplement p
      ring

theorem idealRowHom_two_formula (n:Eis) (hn:lambda^2∣n-1)
    (hs:Supported (Ideal.span {n})) :
    idealRowHom (2:Eis) (Ideal.span {n})=twoSupplement n := by
  have hn0:n≠0:=by intro hz;apply hs.1;simp [hz]
  obtain ⟨s,hprod,hfactors⟩:=exists_primary_prime_factorization n hn0 hn
  rw [←hprod] at hs ⊢
  clear hprod hn hn0 n
  induction s using Multiset.induction_on with
  | empty=>simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one]
  | @cons p s ih=>
    have hp:=hfactors p (Multiset.mem_cons_self _ _)
    have htail:∀q∈s,Prime q ∧ lambda^2∣q-1:=fun q hq=>hfactors q (Multiset.mem_cons_of_mem hq)
    have hsplit:Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}):=by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hs
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,
      idealRowHom_two_prime p hp.1 hp.2 hsplit.1,ih hsplit.2 htail,map_mul]

end

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def supportedIdealRow (a:Eis) : Eis→*ℂ where
  toFun n:=if Supported (Ideal.span {n}) then idealRowHom a (Ideal.span {n}) else 0
  map_one' := by
    have hs:Supported (1:Ideal Eis):=⟨one_ne_zero,by
      intro P hP
      rw [normalizedFactors_one] at hP
      exact False.elim (Multiset.notMem_zero P hP)⟩
    rw [show Ideal.span {(1:Eis)}=(1:Ideal Eis) by simp only [Ideal.span_singleton_one,Ideal.one_eq_top],
      ite_eq_left hs,map_one]
  map_mul' x y := by
    rw [←Ideal.span_singleton_mul_span_singleton,supported_mul_iff,map_mul]
    by_cases hx:Supported (Ideal.span {x}) <;> by_cases hy:Supported (Ideal.span {y}) <;> simp [hx,hy]

lemma supportedIdealRow_norm (a n:Eis) : ‖supportedIdealRow a n‖≤1 := by
  change ‖if _ then _ else _‖≤_
  split_ifs
  · exact idealRowHom_norm _ _
  · simp

lemma exists_supported_primary_unit (x:Eis) (hx:Supported (Ideal.span {x})) :
    ∃u:Eisˣ,lambda^2∣u.val*x-1 := by
  have hg:=supported_primaryGenerator_ne_zero (Ideal.span {x}) hx
  have hp:=primaryGenerator_spec (Ideal.span {x}) hg
  have ha:Associated x (primaryGenerator (Ideal.span {x})):=
    Ideal.span_singleton_eq_span_singleton.mp hp.1.symm
  obtain ⟨u,hu⟩:=ha
  refine ⟨u,?_⟩
  have he:u.val*x=primaryGenerator (Ideal.span {x}):=by simpa only [mul_comm] using hu
  rw [he]
  exact hp.2

theorem supportedIdealRow_lambda_periodic :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(36:Eis)}) (supportedIdealRow lambda) := by
  intro x y hxy
  have hs:=CanonicalUnitEuler.supported_span_congruent_mod_thirty_six x y hxy
  change (if Supported (Ideal.span {x}) then _ else 0)=
    (if Supported (Ideal.span {y}) then _ else 0)
  by_cases hx:Supported (Ideal.span {x})
  · have hy:=hs.mp hx
    rw [ite_eq_left hx,ite_eq_left hy]
    obtain ⟨u,hux⟩:=exists_supported_primary_unit x hx
    have h36:(36:Eis)∣u.val*x-u.val*y:=by
      convert dvd_mul_of_dvd_right (Ideal.mem_span_singleton.mp hxy) u.val using 1 ; ring
    have hl:lambda^2∣u.val*x-u.val*y:=
      lambda_sq_dvd_three.trans ((show (3:Eis)∣36 from ⟨12,by norm_num⟩).trans h36)
    have huy:lambda^2∣u.val*y-1:=by
      convert dvd_sub hux hl using 1 ; ring
    have hsp (z:Eis) : Ideal.span {u.val*z}=Ideal.span {z}:=
      Ideal.span_singleton_mul_left_unit u.isUnit z
    have he:=idealRowHom_lambda_mod_thirty_six (u.val*x) (u.val*y) hux huy
      (by rwa [hsp]) (by rwa [hsp]) h36
    simpa only [hsp] using he
  · rw [ite_eq_right hx,ite_eq_right (fun hy=>hx (hs.mpr hy))]

lemma supportedIdealRow_lambda_primary (n:Eis) (hs:Supported (Ideal.span {n})) :
    supportedIdealRow lambda n=idealRowHom lambda (Ideal.span {n}) := by
  change (if Supported (Ideal.span {n}) then _ else _)=_
  rw [ite_eq_left hs]

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma negative_two_prime : Prime (-2:Eis) :=
  (Ideal.span_singleton_prime (by norm_num : (-2:Eis)≠0)).mp
    (show (Ideal.span {(-2:Eis)}).IsPrime from cubicTwoIdeal_isMaximal.isPrime)

theorem exists_supported_numerator_factorization (x:Eis) (hx:x≠0) :
    ∃u:Eisˣ,∃a b:ℕ,∃r:Eis,Supported (Ideal.span {r}) ∧ lambda^2∣r-1 ∧
      x=u.val*lambda^a*(2:Eis)^b*r := by
  obtain ⟨n,u,a,hn,hxform⟩:=CubicEisenstein.exists_primary_unit_lambda_factor x hx
  have hn0:n≠0:=by
    intro hz
    exact hx (by rw [hxform,hz,zero_mul])
  obtain ⟨r,hr,hrnot⟩:=(FiniteMultiplicity.of_prime_left negative_two_prime hn0).exists_eq_pow_mul_and_not_dvd
  let b:ℕ:=multiplicity (-2:Eis) n
  change n=(-2:Eis)^b*r at hr
  have hp:lambda^2∣(-2:Eis)^b-1:=neg_two_primary.trans (sub_one_dvd_pow_sub_one (-2:Eis) b)
  have hprimary:lambda^2∣r-1:=by
    have hh:=dvd_sub hn (dvd_mul_of_dvd_left hp r)
    have he:n-1-(((-2:Eis)^b-1)*r)=r-1:=by rw [hr];ring
    rwa [he] at hh
  have hnot2:¬(2:Eis)∣r:=by
    intro h2
    exact hrnot (by simpa only [neg_dvd] using h2)
  have hnotlambda:¬lambda∣r:=by
    intro hLam
    have hsub:lambda∣r-1:=(dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hprimary
    have hone:lambda∣(1:Eis):=by
      convert dvd_sub hLam hsub using 1 ; ring
    exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (isUnit_of_dvd_one hone)
  let v:Eisˣ:=u*(-1:Eisˣ)^b
  refine ⟨v,a,b,r,(supported_span_iff r).mpr ⟨hnotlambda,hnot2⟩,hprimary,?_⟩
  have hp2:(-2:Eis)^b=(-1:Eis)^b*(2:Eis)^b:=by
    rw [show (-2:Eis)=(-1)*2 by ring,mul_pow]
  rw [hxform,hr,hp2]
  dsimp only [v]
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,Units.coe_neg_one]
  ring

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

lemma idealRowHom_argument_pow (a:Eis) (k:ℕ) (I:Ideal Eis) (hI:Supported I) :
    idealRowHom (a^k) I=(idealRowHom a I)^k := by
  induction k with
  | zero => simpa only [pow_zero] using idealRowHom_one_supported I hI
  | succ k ih => rw [pow_succ,idealRowHom_argument_mul,ih,pow_succ]

def reciprocityPhaseMonoid (r:Eis) (hr:Supported (Ideal.span {r})) : Eis→*ℂ where
  toFun n:=sexticReciprocityPhase r n
  map_one' := sexticReciprocityPhase_one_right r hr
  map_mul' := sexticReciprocityPhase_mul_right r

def numeratorBadTwist (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) : Eis→*ℂ :=
  unitSupplement u * supportedIdealRow lambda^a * twoSupplement^b * reciprocityPhaseMonoid r hr

lemma numeratorBadTwist_norm (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (n:Eis) : ‖numeratorBadTwist u a b r hr n‖≤1 := by
  change ‖((unitSupplement u n * (supportedIdealRow lambda n)^a) * (twoSupplement n)^b) *
    sexticReciprocityPhase r n‖≤1
  simp only [norm_mul,norm_pow]
  have hu:=unitSupplement_norm u n
  have ha:‖supportedIdealRow lambda n‖^a≤1:=
    pow_le_one₀ (norm_nonneg _) (supportedIdealRow_norm lambda n)
  have hb:‖twoSupplement n‖^b≤1:=
    pow_le_one₀ (norm_nonneg _) (twoSupplement_norm n)
  have hrn:=sexticReciprocityPhase_norm r n
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _)
    ((mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) hu).trans ha)).trans hb)).trans hrn

lemma numeratorBadTwist_periodic (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(72:Eis)}) (numeratorBadTwist u a b r hr) := by
  intro x y hxy
  have h72:(72:Eis)∣x-y:=Ideal.mem_span_singleton.mp hxy
  have h36:x-y∈(Ideal.span {(36:Eis)}:Ideal Eis):=
    Ideal.mem_span_singleton.mpr ((show (36:Eis)∣72 from ⟨2,by norm_num⟩).trans h72)
  have h8:x-y∈(Ideal.span {(8:Eis)}:Ideal Eis):=
    Ideal.mem_span_singleton.mpr ((show (8:Eis)∣72 from ⟨9,by norm_num⟩).trans h72)
  have h4:(4:Eis)∣x-y:=(show (4:Eis)∣72 from ⟨18,by norm_num⟩).trans h72
  change ((unitSupplement u x * (supportedIdealRow lambda x)^a) * (twoSupplement x)^b) *
      sexticReciprocityPhase r x =
    ((unitSupplement u y * (supportedIdealRow lambda y)^a) * (twoSupplement y)^b) *
      sexticReciprocityPhase r y
  rw [unitSupplement_periodic u x y h36,supportedIdealRow_lambda_periodic x y h36,
    twoSupplement_periodic x y h8,sexticReciprocityPhase_congr_right r x y h4]

def movingNumeratorRow (r:Eis) (hr:Supported (Ideal.span {r})) : Eis→*ℂ where
  toFun n:=idealRowHom n (Ideal.span {r})
  map_one' := idealRowHom_one_supported _ hr
  map_mul' a b := idealRowHom_argument_mul a b _

lemma movingNumeratorRow_norm (r:Eis) (hr:Supported (Ideal.span {r})) (n:Eis) :
    ‖movingNumeratorRow r hr n‖≤1 := idealRowHom_norm n _

lemma movingNumeratorRow_periodic (r:Eis) (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {r}) (movingNumeratorRow r hr) :=
  idealRowHom_congr_mod _

theorem idealRowHom_factor_numerator (u:Eisˣ) (a b:ℕ) (r n:Eis)
    (hr:Supported (Ideal.span {r})) (hpr:lambda^2∣r-1)
    (hn:Supported (Ideal.span {n})) (hpn:lambda^2∣n-1) :
    idealRowHom (u.val*lambda^a*(2:Eis)^b*r) (Ideal.span {n})=
      numeratorBadTwist u a b r hr n * movingNumeratorRow r hr n := by
  have hu:unitSupplement u n=idealRowHom u.val (Ideal.span {n}):=by
    change (if Supported (Ideal.span {n}) then _ else 0)=_
    rw [ite_eq_left hn]
  have hrec:=reciprocalRow_eq_idealRowHom r n hr hn hpr hpn
  change sexticReciprocityPhase r n*idealRowHom n (Ideal.span {r})=
    idealRowHom r (Ideal.span {n}) at hrec
  change _=(((unitSupplement u n * (supportedIdealRow lambda n)^a) * (twoSupplement n)^b) *
    sexticReciprocityPhase r n)*idealRowHom n (Ideal.span {r})
  rw [idealRowHom_argument_mul,idealRowHom_argument_mul,idealRowHom_argument_mul,
    idealRowHom_argument_pow _ _ _ hn,idealRowHom_argument_pow _ _ _ hn,
    hu,supportedIdealRow_lambda_primary n hn,←idealRowHom_two_formula n hpn hn,←hrec]
  ring

end CanonicalRowCompletion

end

end OAI

end Source283

/- Original source: OAI/NumberTheory/DirichletL/RowCompletion/PeriodicRows.lean; sha256: 7306d53cc2364f05c53923d9db94cac9f28ab1a754fa0130c49b813dc69e7c8f -/
section Source284
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
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

lemma numeratorBadTwist_zero_of_not_supported (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (n:Eis) (hn:¬Supported (Ideal.span {n})) :
    numeratorBadTwist u a b r hr n=0 := by
  have hu:unitSupplement u n=0:=by
    change (if Supported (Ideal.span {n}) then _ else 0)=0
    rw [ite_eq_right hn]
  change ((unitSupplement u n * (supportedIdealRow lambda n)^a) * (twoSupplement n)^b) *
    sexticReciprocityPhase r n=0
  rw [hu,zero_mul,zero_mul,zero_mul]

lemma rowTwist_zero_of_not_supported (Ψ:Eis→*ℂ) (m f z n:Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (hn:¬Supported (Ideal.span {n})) :
    rowTwist Ψ m f z n=0 := by
  have hu:unitSupplement (1:Eisˣ) n=0:=by
    change (if Supported (Ideal.span {n}) then _ else 0)=0
    rw [ite_eq_right hn]
  have h:=congrArg (fun T:Eis→*ℂ=>T n) (rowTwist_unitSupplement Ψ m f z (1:Eisˣ) hmLam hm2)
  change rowTwist Ψ m f ((1:Eisˣ).val*z) n=unitSupplement (1:Eisˣ) n*rowTwist Ψ m f z n at h
  simpa only [Units.val_one,one_mul,hu,zero_mul] using h

def actualPeriodicRow (Ψ:Eis→*ℂ) (m:Eis) (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) : Eis→*ℂ :=
  Ψ * coprimalityMask m * numeratorBadTwist u a b r hr * movingNumeratorRow r hr

lemma actualPeriodicRow_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (m:Eis) (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) (n:Eis) :
    ‖actualPeriodicRow Ψ m u a b r hr n‖≤1 := by
  change ‖((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n‖≤1
  simp only [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
    (hΨ n)).trans (coprimalityMask_norm m n))).trans (numeratorBadTwist_norm u a b r hr n))).trans
    (movingNumeratorRow_norm r hr n)

lemma actualPeriodicRow_periodic (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (m:Eis) (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo
      (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})
      (actualPeriodicRow Ψ m u a b r hr) := by
  intro x y hxy
  have hQ:x-y∈Q:=Ideal.mul_le_left (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hm:x-y∈Ideal.span {m}:=Ideal.mul_le_right (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have h72:x-y∈Ideal.span {(72:Eis)}:=Ideal.mul_le_right (Ideal.mul_le_left hxy)
  have hrxy:x-y∈Ideal.span {r}:=Ideal.mul_le_right hxy
  change ((Ψ x*coprimalityMask m x)*numeratorBadTwist u a b r hr x)*movingNumeratorRow r hr x=
    ((Ψ y*coprimalityMask m y)*numeratorBadTwist u a b r hr y)*movingNumeratorRow r hr y
  rw [hΨ x y hQ,coprimalityMask_periodic m x y hm,numeratorBadTwist_periodic u a b r hr x y h72,
    movingNumeratorRow_periodic r hr x y hrxy]

theorem rowTwist_eq_actualPeriodicRow_primary (Ψ:Eis→*ℂ) (m f z:Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (hpr:lambda^2∣r-1)
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=actualPeriodicRow Ψ m u a b r hr n := by
  by_cases hn:Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask Ψ m f z n hn,hx,
      idealRowHom_factor_numerator u a b r n hr hpr hn hpn]
    change _=((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n
    ring
  · rw [rowTwist_zero_of_not_supported Ψ m f z n hmLam hm2 hn]
    change 0=((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n
    rw [numeratorBadTwist_zero_of_not_supported u a b r hr n hn,mul_zero,zero_mul]

theorem exists_actual_periodic_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hQ:Q≠0) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(u:Eisˣ)(a b:ℕ)(r:Eis)(hr:Supported (Ideal.span {r})),
      lambda^2∣r-1 ∧ f^4*z=u.val*lambda^a*(2:Eis)^b*r ∧
      (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})≠0 ∧
      CanonicalCoefficientClass.FactorsModulo
        (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})
        (actualPeriodicRow Ψ m u a b r hr) ∧
      (∀n,‖actualPeriodicRow Ψ m u a b r hr n‖≤1) ∧
      (∀n,lambda^2∣n-1 → rowTwist Ψ m f z n=actualPeriodicRow Ψ m u a b r hr n) := by
  obtain ⟨u,a,b,r,hr,hpr,hx⟩:=exists_supported_numerator_factorization (f^4*z)
    (mul_ne_zero (pow_ne_zero _ hf) hz)
  refine ⟨u,a,b,r,hr,hpr,hx,?_,actualPeriodicRow_periodic Ψ Q hΨ m u a b r hr,
    actualPeriodicRow_norm Ψ hΨnorm m u a b r hr,?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hQ (by
      simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hm))
      (by simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot];norm_num)) hr.1
  · exact fun n hpn=>rowTwist_eq_actualPeriodicRow_primary Ψ m f z hmLam hm2 u a b r hr hpr hx n hpn

end CanonicalRowCompletion

namespace CompletedGauss

section
open ActualEisensteinCubic IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def completedReflectionPool (I Q:Ideal Eis) : Finset (Ideal Eis) :=
  (primeSupport (I*Q)).filter (fun P=>lambda∉P ∧ ringChar (Eis⧸P)≠2 ∧ ¬P∣rowResidualPart I Q)

lemma mem_completedReflectionPool (I Q P:Ideal Eis) (hI:I≠0) (hQ:Q≠0) :
    P∈completedReflectionPool I Q ↔
      Prime P ∧ P∣I*Q ∧ lambda∉P ∧ ringChar (Eis⧸P)≠2 ∧ ¬P∣rowResidualPart I Q := by
  simp only [completedReflectionPool,Finset.mem_filter,primeSupport,Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff (mul_ne_zero hI hQ)]
  aesop

lemma completedReflectionPool_maximal (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    P.val.IsMaximal := by
  have hm: P.val∈normalizedFactors (I*Q):=
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp P.property).1
  have hp:=prime_of_normalized_factor P.val hm
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

lemma completedReflectionPool_good (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    lambda∉P.val := (Finset.mem_filter.mp P.property).2.1

lemma completedReflectionPool_odd (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    ringChar (Eis⧸P.val)≠2 := (Finset.mem_filter.mp P.property).2.2.1

lemma completedReflectionPool_nonresidual (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    ¬P.val∣rowResidualPart I Q := (Finset.mem_filter.mp P.property).2.2.2

lemma completedReflectionPool_divides (I Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (P:completedReflectionPool I Q) : P.val∣I*Q :=
  ((mem_completedReflectionPool I Q P.val hI hQ).mp P.property).2.1

lemma completedReflectionPool_coprime (I Q:Ideal Eis) :
    Pairwise (fun P R:completedReflectionPool I Q=>IsCoprime P.val R.val) := by
  let (P:completedReflectionPool I Q):P.val.IsMaximal:=completedReflectionPool_maximal I Q P
  intro P R hPR
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPR)

theorem completedReflectionPool_eq_on_fiber (I J Q:Ideal Eis)
    (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q) :
    completedReflectionPool I Q=completedReflectionPool J Q := by
  ext P
  rw [mem_completedReflectionPool I Q P hI hQ,mem_completedReflectionPool J Q P hJ hQ]
  constructor
  · rintro ⟨hP,hdiv,hgood,hodd,hres⟩
    obtain ⟨hdivJ,hresJ,_⟩:=nonresidual_prime_transport I J 1 Q P hI hJ hP hA hT hdiv hres
    exact ⟨hP,hdivJ,hgood,hodd,hresJ⟩
  · rintro ⟨hP,hdiv,hgood,hodd,hres⟩
    obtain ⟨hdivI,hresI,_⟩:=nonresidual_prime_transport J I 1 Q P hJ hI hP hA.symm hT.symm hdiv hres
    exact ⟨hP,hdivI,hgood,hodd,hresI⟩

lemma completedReflectionPool_exponent_eq (I J F Q:Ideal Eis)
    (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q)
    (P:completedReflectionPool I Q) :
    completedLocalExponent I F P.val=completedLocalExponent J F P.val := by
  rcases (mem_completedReflectionPool I Q P.val hI hQ).mp P.property with
    ⟨hP,hdiv,_,_,hres⟩
  exact (nonresidual_prime_transport I J F Q P.val hI hJ hP hA hT hdiv hres).2.2

theorem completedBranchScale_eq_on_fiber {ι:Type*} [Fintype ι]
    (K X:ℝ) (I J F Q:Ideal Eis) (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q)
    (P:ι→Ideal Eis) (hP:∀i,P i∈completedReflectionPool I Q) (e:ι→Fin 3) :
    completedBranchScale K X I F Q P e=completedBranchScale K X J F Q P e := by
  have hj:(fun i=>completedLocalExponent I F (P i))=(fun i=>completedLocalExponent J F (P i)):=by
    funext i
    exact completedReflectionPool_exponent_eq I J F Q hI hJ hQ hA hT ⟨P i,hP i⟩
  simp only [completedBranchScale,completedResidualScale_eq_on_fiber K I J Q hA hT,hj]

end

section

def reflectionSixActive (e:Fin 6) : Prop := 3≤e.val

def reflectionSixLabel (e:Fin 6) : Fin 3 := ⟨e.val%3,Nat.mod_lt _ (by decide)⟩

def reflectionSixValid {ι:Type*} (e:ι→Fin 6) : Prop :=
  ∀i,e i=0 ∨ reflectionSixActive (e i)

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def encodeReflectionSix (x:ΣA:Finset ι,A→Fin 3) : ι→Fin 6 := fun i=>
  if h:i∈x.1 then ⟨3+(x.2 ⟨i,h⟩).val,by have ht:=(x.2 ⟨i,h⟩).isLt; omega⟩ else 0

def reflectionSixSupport (e:ι→Fin 6) : Finset ι :=
  Finset.univ.filter (fun i=>reflectionSixActive (e i))

def decodeReflectionSix (e:ι→Fin 6) : ΣA:Finset ι,A→Fin 3 :=
  ⟨reflectionSixSupport e,fun i=>reflectionSixLabel (e i.val)⟩

omit [Fintype ι] in
lemma reflectionSixActive_encode (x:ΣA:Finset ι,A→Fin 3) (i:ι) :
    reflectionSixActive (encodeReflectionSix x i) ↔ i∈x.1 := by
  by_cases hi:i∈x.1
  · simp [encodeReflectionSix,hi,reflectionSixActive]
  · simp [encodeReflectionSix,hi,reflectionSixActive]

omit [Fintype ι] in
lemma encodeReflectionSix_valid (x:ΣA:Finset ι,A→Fin 3) :
    reflectionSixValid (encodeReflectionSix x) := by
  intro i
  by_cases hi:i∈x.1
  · exact Or.inr ((reflectionSixActive_encode x i).mpr hi)
  · left
    simp [encodeReflectionSix,hi]

lemma reflectionSixSupport_encode (x:ΣA:Finset ι,A→Fin 3) :
    reflectionSixSupport (encodeReflectionSix x)=x.1 := by
  ext i
  simp only [reflectionSixSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    reflectionSixActive_encode]

lemma encodeReflectionSix_injective :
    Function.Injective (encodeReflectionSix (ι:=ι)) := by
  intro x y hxy
  have hsets:x.1=y.1:=by
    rw [←reflectionSixSupport_encode x,←reflectionSixSupport_encode y,hxy]
  rcases x with ⟨A,e⟩
  rcases y with ⟨B,f⟩
  dsimp only at hsets
  subst B
  congr 1
  funext i
  have he:=congrFun hxy i.val
  simp only [encodeReflectionSix,dite_eq_left i.property] at he
  apply Fin.ext
  have hv:=congrArg Fin.val he
  exact Nat.add_left_cancel hv

lemma encode_decodeReflectionSix (e:ι→Fin 6) (he:reflectionSixValid e) :
    encodeReflectionSix (decodeReflectionSix e)=e := by
  funext i
  by_cases hi:reflectionSixActive (e i)
  · have him:i∈reflectionSixSupport e:=by simp [reflectionSixSupport,hi]
    dsimp only [encodeReflectionSix, decodeReflectionSix]
    rw [dite_eq_left him]
    apply Fin.ext
    change 3 + (e i).val % 3 = (e i).val
    have hl:=(e i).isLt
    dsimp only [reflectionSixActive] at hi
    omega
  · have him:i∉reflectionSixSupport e:=by simp [reflectionSixSupport,hi]
    have hz:e i=0:=(he i).resolve_right hi
    simp [encodeReflectionSix,decodeReflectionSix,him,hz]

lemma decode_encodeReflectionSix (x:ΣA:Finset ι,A→Fin 3) :
    decodeReflectionSix (encodeReflectionSix x)=x :=
  encodeReflectionSix_injective (encode_decodeReflectionSix _ (encodeReflectionSix_valid x))

def reflectionSixEquiv : (ΣA:Finset ι,A→Fin 3) ≃ {e:ι→Fin 6 // reflectionSixValid e} where
  toFun x:=⟨encodeReflectionSix x,encodeReflectionSix_valid x⟩
  invFun e:=decodeReflectionSix e.val
  left_inv:=decode_encodeReflectionSix
  right_inv e:=Subtype.ext (encode_decodeReflectionSix e.val e.property)

theorem sum_active_exceptional_eq_six {V:Type*} [AddCommMonoid V]
    (F:∀A:Finset ι,(A→Fin 3)→V) :
    (∑A:Finset ι,∑e:A→Fin 3,F A e)=
      ∑e:ι→Fin 6,if reflectionSixValid e then
        F (decodeReflectionSix e).1 (decodeReflectionSix e).2 else 0 := by
  have he:=Equiv.sum_comp (reflectionSixEquiv (ι:=ι))
    (fun e:{e:ι→Fin 6 // reflectionSixValid e}=>
      F (decodeReflectionSix e.val).1 (decodeReflectionSix e.val).2)
  have hs:(∑x:ΣA:Finset ι,A→Fin 3,F x.1 x.2)=
      ∑e:{e:ι→Fin 6 // reflectionSixValid e},F (decodeReflectionSix e.val).1 (decodeReflectionSix e.val).2 := by
    calc
      _=∑x:ΣA:Finset ι,A→Fin 3,
          F (decodeReflectionSix (encodeReflectionSix x)).1
            (decodeReflectionSix (encodeReflectionSix x)).2 := by
        apply Finset.sum_congr rfl
        intro x _
        exact (congrArg (fun y:ΣA:Finset ι,A→Fin 3=>F y.1 y.2)
          (decode_encodeReflectionSix x)).symm
      _=_ := he
  rw [Fintype.sum_sigma] at hs
  rw [hs,←Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter reflectionSixValid)
    (by simp) (fun e:ι→Fin 6=>F (decodeReflectionSix e).1 (decodeReflectionSix e).2)).symm

end
section

open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance reflectionWeightField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P
noncomputable local instance reflectionWeightFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def reflectionStratumWeight (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (A:Finset ι) : ℂ :=
  (∏i∈A,(((actualSextic (P i) (hg i))⁻¹)^2) (σ A i)*
    phase (actualSextic (P i) (hg i)) (ψ A i) (j i) (ε A i))*
  (∏i∈(Finset.univ:Finset ι)\A,zeroFourierCoefficient (actualSextic (P i) (hg i)) (j i))

lemma reflectionStratumWeight_norm_le_one (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (hc:∀i,ringChar (Eis⧸P i)≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ) (hψ:∀A i,(ψ A i).IsPrimitive)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (A:Finset ι) :
    ‖reflectionStratumWeight P hg j ψ σ ε A‖≤1 := by
  have hactive (i:ι) : ‖(((actualSextic (P i) (hg i))⁻¹)^2) (σ A i)*
      phase (actualSextic (P i) (hg i)) (ψ A i) (j i) (ε A i)‖=1 := by
    rw [norm_mul,FiniteRayExpansion.norm_char_unit]
    simpa only [one_mul,actualSextic] using canonical_phase_norm (P i) (hg i) (hc i)
      (ψ A i) (hψ A i) (j i) (hj i) (ε A i)
  have hinactive (i:ι) : ‖zeroFourierCoefficient (actualSextic (P i) (hg i)) (j i)‖≤1 := by
    by_cases hi:j i=0
    · rw [hi]
      exact zeroFourierCoefficient_zero_norm_le_one _
    · have he:=canonical_zeroFourierCoefficient (P i) (hg i) (hc i) (j i) (hj i)
      have hz:zeroFourierCoefficient (actualSextic (P i) (hg i)) (j i)=0 := by
        simpa only [actualSextic,ite_eq_right hi] using he
      rw [hz]
      simp
  rw [reflectionStratumWeight,norm_mul,norm_prod,norm_prod]
  simp only [hactive,Finset.prod_const_one,one_mul]
  exact Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i _=>hinactive i)

def reflectionSixWeight (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (e:ι→Fin 6) : ℂ :=
  if reflectionSixValid e then reflectionStratumWeight P hg j ψ σ ε (reflectionSixSupport e) else 0

lemma reflectionSixWeight_norm_le_one (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (hc:∀i,ringChar (Eis⧸P i)≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ) (hψ:∀A i,(ψ A i).IsPrimitive)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (e:ι→Fin 6) :
    ‖reflectionSixWeight P hg j ψ σ ε e‖≤1 := by
  unfold reflectionSixWeight
  split_ifs
  · exact reflectionStratumWeight_norm_le_one P hg hc j hj ψ hψ σ ε _
  · simp

theorem sum_reflectionStratumWeight_eq_six (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ)
    (G:∀A:Finset ι,(A→Fin 3)→ℂ) :
    (∑A:Finset ι,∑e:A→Fin 3,reflectionStratumWeight P hg j ψ σ ε A*G A e)=
      ∑e:ι→Fin 6,reflectionSixWeight P hg j ψ σ ε e*
        G (decodeReflectionSix e).1 (decodeReflectionSix e).2 := by
  rw [sum_active_exceptional_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e <;> simp [reflectionSixWeight,he,decodeReflectionSix]

theorem stratum_weighted_brackets_eq_branches (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (A:Finset ι) (n b:Eis) :
    reflectionStratumWeight P hg j ψ σ ε A*
      (∏i:A,bracket (actualSextic (P i.val) (hg i.val)) (j i.val)
        (Ideal.Quotient.mk (P i.val) (n*b^3)))=
    ∑e:A→Fin 3,reflectionStratumWeight P hg j ψ σ ε A*
      reflectedBranch (fun i:A=>P i.val) (fun i=>hg i.val) (fun i=>j i.val) e n b := by
  rw [prod_bracket_eq_full_branches,Finset.mul_sum]
  apply Finset.sum_congr
  · ext e
    simp
  · intro e _
    rfl

theorem sum_reflectionSixWeight_unpad (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (G:(ι→Fin 6)→ℂ) :
    (∑e:ι→Fin 6,reflectionSixWeight P hg j ψ σ ε e*G e)=
      ∑A:Finset ι,∑e:A→Fin 3,reflectionStratumWeight P hg j ψ σ ε A*
        G (encodeReflectionSix ⟨A,e⟩) := by
  rw [sum_reflectionStratumWeight_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e
  · rw [encode_decodeReflectionSix e he]
  · simp only [reflectionSixWeight,ite_eq_right he,zero_mul]

end
section

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def reflectionChoiceValue (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6)
    (P:Ideal Eis) : Fin 6 :=
  if h:P∈completedReflectionPool I Q then e ⟨P,h⟩ else 0

def reflectionActivePool (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6) : Finset (Ideal Eis) :=
  (completedReflectionPool I Q).filter (fun P=>reflectionSixActive (reflectionChoiceValue I Q e P))

lemma reflectionActivePool_subset (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6) :
    reflectionActivePool I Q e⊆completedReflectionPool I Q := Finset.filter_subset _ _

lemma mem_reflectionActivePool (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6)
    (P:completedReflectionPool I Q) :
    P.val∈reflectionActivePool I Q e ↔ reflectionSixActive (e P) := by
  rw [reflectionActivePool, Finset.mem_filter]
  simp only [P.property, true_and]
  rw [reflectionChoiceValue, dite_eq_left P.property]

lemma reflectionActivePool_encode (I Q:Ideal Eis)
    (A:Finset (completedReflectionPool I Q)) (e:A→Fin 3) :
    reflectionActivePool I Q (encodeReflectionSix ⟨A,e⟩)=A.image Subtype.val := by
  ext P
  constructor
  · intro hP
    let p:completedReflectionPool I Q:=⟨P,reflectionActivePool_subset I Q _ hP⟩
    have hp:p∈A:=(reflectionSixActive_encode ⟨A,e⟩ p).mp
      ((mem_reflectionActivePool I Q _ p).mp hP)
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  · intro hP
    obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hP
    exact (mem_reflectionActivePool I Q _ p).mpr ((reflectionSixActive_encode ⟨A,e⟩ p).mpr hp)

def reflectionActiveLabel (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6)
    (P:reflectionActivePool I Q e) : Fin 3 :=
  reflectionSixLabel (e ⟨P.val,reflectionActivePool_subset I Q e P.property⟩)

def sixReflectedBranch (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6)
    (amplitude:ℕ→Ideal Eis→Ideal Eis→ℂ) (hamp:∀m n b,‖amplitude m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q where
  levelScale:=levelScale
  levelScale_pos:=hlevel
  levelScale_le:=hbound
  primes:=reflectionActivePool I Q e
  maximal:=fun P=>completedReflectionPool_maximal I Q ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
  good:=fun P=>completedReflectionPool_good I Q ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
  coprime:=by
    intro P R hPR
    let : P.val.IsMaximal:=completedReflectionPool_maximal I Q ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
    let : R.val.IsMaximal:=completedReflectionPool_maximal I Q ⟨R.val,reflectionActivePool_subset I Q e R.property⟩
    exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPR)
  divides:=fun P=>completedReflectionPool_divides I Q hI hQ ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
  nonresidual:=fun P=>completedReflectionPool_nonresidual I Q ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
  label:=reflectionActiveLabel I Q e
  nColumns:=fun i=>dualIdealDyad i.2.2
  bColumns:=fun i=>dualIdealDyad i.2.1
  nBounds:=fun i n hn=>dualIdealDyad_bounds i.2.2 n hn
  bBounds:=fun i b hb=>dualIdealDyad_bounds i.2.1 b hb
  amplitude:=fun i=>amplitude i.1
  amplitude_bound:=fun i n _ b _=>hamp i.1 n b
  rowPhase:=fun i=>rowPhase i.1
  rowPhase_bound:=fun i k=>hrow i.1 k

def sixFixedCuspBranch (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q :=
  (sixReflectedBranch I F Q hI hQ K levelBound levelScale hlevel hbound e
    (fixedConjugateCuspArray cusp u) (fixedConjugateCuspArray_norm_le_one cusp u) rowPhase hrow).withExtractedFixedCuspArray cusp u rowPhase hrow

lemma sixFixedCuspBranch_primes (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    (sixFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u rowPhase hrow).primes=
      reflectionActivePool I Q e := rfl

lemma sixFixedCuspBranch_scale (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K X levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    let d:=sixFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u rowPhase hrow
    completedBranchScale K (X/d.levelScale) I F Q (fun P:d.primes=>P.val) d.label=
      completedBranchScale K (X/levelScale) I F Q
        (fun P:reflectionActivePool I Q e=>P.val) (reflectionActiveLabel I Q e) := rfl

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
local instance poolMaximal (I Q:Ideal Eis) (P:completedReflectionPool I Q) : P.val.IsMaximal :=
  completedReflectionPool_maximal I Q P
noncomputable local instance poolField (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Field (Eis⧸P.val) :=
  Ideal.Quotient.field P.val
noncomputable local instance poolFintype (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Fintype (Eis⧸P.val) :=
  Fintype.ofFinite _

def reflectionInactiveStratumWeight (I F Q:Ideal Eis) (A:Finset (completedReflectionPool I Q)) : ℂ :=
  ∏P∈(Finset.univ:Finset (completedReflectionPool I Q))\A,
    zeroFourierCoefficient (actualSextic P.val (completedReflectionPool_good I Q P))
      (completedLocalExponent I F P.val)

lemma reflectionInactiveStratumWeight_norm_le_one (I F Q:Ideal Eis)
    (A:Finset (completedReflectionPool I Q)) : ‖reflectionInactiveStratumWeight I F Q A‖≤1 := by
  rw [reflectionInactiveStratumWeight,norm_prod]
  apply Finset.prod_le_one₀ (fun _ _=>norm_nonneg _)
  intro P _
  by_cases hj:completedLocalExponent I F P.val=0
  · rw [hj]
    exact zeroFourierCoefficient_zero_norm_le_one _
  · have he:=canonical_zeroFourierCoefficient P.val (completedReflectionPool_good I Q P)
      (completedReflectionPool_odd I Q P) (completedLocalExponent I F P.val)
      (Nat.mod_lt _ (by decide : 0<6))
    have hz:zeroFourierCoefficient (actualSextic P.val (completedReflectionPool_good I Q P))
        (completedLocalExponent I F P.val)=0 := by
      simpa only [actualSextic,ite_eq_right hj] using he
    rw [hz]
    simp

def reflectionSixInactiveWeight (I F Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6) : ℂ :=
  if reflectionSixValid e then reflectionInactiveStratumWeight I F Q (reflectionSixSupport e) else 0

lemma reflectionSixInactiveWeight_norm_le_one (I F Q:Ideal Eis)
    (e:completedReflectionPool I Q→Fin 6) : ‖reflectionSixInactiveWeight I F Q e‖≤1 := by
  unfold reflectionSixInactiveWeight
  split_ifs
  · exact reflectionInactiveStratumWeight_norm_le_one I F Q _
  · simp

lemma sum_reflectionSixInactiveWeight_unpad (I F Q:Ideal Eis)
    (G:(completedReflectionPool I Q→Fin 6)→ℂ) :
    (∑e:completedReflectionPool I Q→Fin 6,reflectionSixInactiveWeight I F Q e*G e)=
      ∑A:Finset (completedReflectionPool I Q),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q A*G (encodeReflectionSix ⟨A,e⟩) := by
  rw [sum_active_exceptional_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e
  · rw [ite_eq_left he,encode_decodeReflectionSix e he]
    simp only [reflectionSixInactiveWeight,ite_eq_left he,decodeReflectionSix]
  · simp only [ite_eq_right he,reflectionSixInactiveWeight,zero_mul]

abbrev SixReflectionIndex (rays:ℕ) (I Q:Ideal Eis) :=
  Fin rays×(completedReflectionPool I Q→Fin 6)

def sixFixedCuspFiber (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) : ReflectedFiberData rays levelBound K I F Q where
  pool:=completedReflectionPool I Q
  maximal:=completedReflectionPool_maximal I Q
  divides:=completedReflectionPool_divides I Q hI hQ
  branch:=fun x=>sixFixedCuspBranch I F Q hI hQ K levelBound (levelScale x) (hlevel x) (hlevelBound x)
    x.2 (cusp x) (unit x) (rowPhase x) (hrow x)
  weight:=fun x=>rayWeight x*reflectionSixInactiveWeight I F Q x.2
  weight_bound:=by
    intro x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hray x)).trans (reflectionSixInactiveWeight_norm_le_one I F Q x.2)

theorem sixFixedCuspFiber_value (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=sixFixedCuspFiber rays I F Q hI hQ K levelBound levelScale hlevel hlevelBound
      cusp unit rayWeight hray rowPhase hrow
    d.value W X ρ q k=
      ∑t:Fin rays,∑A:Finset (completedReflectionPool I Q),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q A*rayWeight (t,encodeReflectionSix ⟨A,e⟩)*
          (d.branch (t,encodeReflectionSix ⟨A,e⟩)).value W X ρ q k := by
  dsimp only
  rw [ReflectedFiberData.value,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _=∑e:completedReflectionPool I Q→Fin 6,reflectionSixInactiveWeight I F Q e*
      (rayWeight (t,e)*(sixFixedCuspBranch I F Q hI hQ K levelBound (levelScale (t,e))
        (hlevel (t,e)) (hlevelBound (t,e)) e (cusp (t,e)) (unit (t,e))
        (rowPhase (t,e)) (hrow (t,e))).value W X ρ q k) := by
          apply Finset.sum_congr rfl
          intro e _
          dsimp only [sixFixedCuspFiber]
          ring
    _=_ := by
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [sixFixedCuspFiber]
      exact (mul_assoc _ _ _).symm

end CompletedGauss

end

end OAI

end Source284

/- Original source: OAI/NumberTheory/DirichletL/GaussSum/ReflectionPool.lean; sha256: d212ab20bb18930de6c970385f93156c267b17e0606593de376ba68f9a6d535a -/
section Source285
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

namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
local instance poolMaximalCount (I Q:Ideal Eis) (P:completedReflectionPool I Q) : P.val.IsMaximal :=
  completedReflectionPool_maximal I Q P
noncomputable local instance poolFieldCount (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Field (Eis⧸P.val) :=
  Ideal.Quotient.field P.val
noncomputable local instance poolFintypeCount (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Fintype (Eis⧸P.val) :=
  Fintype.ofFinite _

lemma reflectionSixInactiveWeight_support (I F Q:Ideal Eis)
    (e:completedReflectionPool I Q→Fin 6) (hne:reflectionSixInactiveWeight I F Q e≠0)
    (P:completedReflectionPool I Q) (hj:completedLocalExponent I F P.val≠0) :
    reflectionSixActive (e P) := by
  have he:reflectionSixValid e:=by
    by_contra he
    exact hne (by simp [reflectionSixInactiveWeight,he])
  have hprod:reflectionInactiveStratumWeight I F Q (reflectionSixSupport e)≠0:=by
    simpa only [reflectionSixInactiveWeight,ite_eq_left he] using hne
  by_contra hP
  have hm:P∈(Finset.univ:Finset (completedReflectionPool I Q))\reflectionSixSupport e:=by
    simp [reflectionSixSupport,hP]
  have hp:zeroFourierCoefficient (actualSextic P.val (completedReflectionPool_good I Q P))
      (completedLocalExponent I F P.val)≠0:=
    (Finset.prod_ne_zero_iff.mp hprod) P hm
  have hz:=canonical_zeroFourierCoefficient P.val (completedReflectionPool_good I Q P)
    (completedReflectionPool_odd I Q P) (completedLocalExponent I F P.val)
    (Nat.mod_lt _ (by decide : 0<6))
  apply hp
  simpa only [actualSextic,ite_eq_right hj] using hz

lemma sixReflectionIndex_card (rays:ℕ) (I Q:Ideal Eis) :
    Fintype.card (SixReflectionIndex rays I Q)=rays*6^(completedReflectionPool I Q).card := by
  simp [SixReflectionIndex]

theorem completedReflectionPool_count_small_power (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀I Q:Ideal Eis,I≠0→Q≠0→
      (6:ℝ)^(2*(completedReflectionPool I Q).card)≤
        C*((Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ))^ε := by
  obtain ⟨C,hC,hbound⟩:=completed_branch_count_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro I Q hI hQ
  have h:=hbound (I*Q) (mul_ne_zero hI hQ)
    (fun P:completedReflectionPool I Q=>P.val) Subtype.val_injective
    (completedReflectionPool_divides I Q hI hQ)
  simpa only [Fintype.card_coe,map_mul,Nat.cast_mul] using h

end CompletedGauss

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma actualSextic_sixth_one (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P) :
    actualSextic P hg^6=1 := by
  apply MulChar.ext
  intro t
  obtain ⟨n,hn⟩:=Ideal.Quotient.mk_surjective (t:Eis⧸P)
  have hnot:n∉P:=by
    intro hm
    have ht:(t:Eis⧸P)=0:=by rw [←hn];exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
    exact t.ne_zero ht
  have h:=canonicalSextic_sixth_power_mask P hg n
  change actualSextic P hg (Ideal.Quotient.mk P (n^6))=_ at h
  rw [map_pow,map_pow,ite_eq_right hnot] at h
  rw [MulChar.pow_apply_coe,MulChar.one_apply_coe,←hn]
  exact h

lemma actualSextic_power_mod_six (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P)
    (k:ℕ) (hk:k≠0) (n:Eis) :
    actualSextic P hg (Ideal.Quotient.mk P n)^k=
      (actualSextic P hg^(k%6)) (Ideal.Quotient.mk P n) := by
  rw [←MulChar.pow_apply' _ hk,pow_eq_pow_mod _ (actualSextic_sixth_one P hg)]

lemma idealRowHom_eq_prime_count_product (I:Ideal Eis) (hI:Supported I) (n:Eis) :
    idealRowHom n I=∏P:PrimeIndex I,
      (actualSextic P.val ((supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1) ^
        ((normalizedFactors I).count P.val%6)) (Ideal.Quotient.mk P.val n) := by
  have he:I=∏P:PrimeIndex I,P.val^((normalizedFactors I).count P.val):=by
    change I=∏P:(normalizedFactors I).toFinset,P.val^((normalizedFactors I).count P.val)
    exact ((Ideal.prod_normalizedFactors_eq_self hI.1).symm.trans (Finset.prod_multiset_count _)).trans
      (Finset.prod_coe_sort (normalizedFactors I).toFinset (fun P=>P^((normalizedFactors I).count P))).symm
  calc
    idealRowHom n I = idealRowHom n (∏P:PrimeIndex I,P.val^((normalizedFactors I).count P.val)) :=
      congrArg (idealRowHom n) he
    _ = ∏P:PrimeIndex I,idealRowHom n P.val ^ ((normalizedFactors I).count P.val) := by
      simp only [map_prod,map_pow]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro P hP
      rw [idealRowHom_prime n P.val
        ((supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1)]
      exact actualSextic_power_mod_six P.val _ _
        (Nat.ne_of_gt (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property))) n

lemma primeIndex_pairwise_coprime (I:Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (fun P:PrimeIndex I=>P.val)) := by
  intro P Q hPQ
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPQ (Subtype.ext he))

theorem idealRowHom_eq_principalSexticRow (I:Ideal Eis) (hI:Supported I) (n:Eis) :
    idealRowHom n I=
      principalSexticRow (fun P:PrimeIndex I=>P.val) (primeIndex_pairwise_coprime I)
        (fun P=>(supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1)
        (fun P=>(normalizedFactors I).count P.val%6)
        (finitePrimeModulus (fun P:PrimeIndex I=>P.val))
        (span_finitePrimeModulus _)
        (Ideal.Quotient.mk _ n) := by
  rw [principalSexticRow_mk]
  exact idealRowHom_eq_prime_count_product I hI n

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

lemma coprimalityMask_good_part (u:Eisˣ) (a b:ℕ) (r n:Eis)
    (hn:Supported (Ideal.span {n})) :
    coprimalityMask (u.val*lambda^a*(2:Eis)^b*r) n=coprimalityMask r n := by
  have hl:IsCoprime lambda n:=
    PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr ((supported_span_iff n).mp hn).1
  have hneg2:IsCoprime (-2:Eis) n:=negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff n).mp hn).2)
  have h2:IsCoprime (2:Eis) n:=hneg2.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  have hu:IsCoprime u.val n:=⟨(u⁻¹).val,0,by simp⟩
  have hla:IsCoprime (lambda^a) n:=hl.pow_left
  have h2b:IsCoprime ((2:Eis)^b) n:=h2.pow_left
  change (if IsCoprime (u.val*lambda^a*(2:Eis)^b*r) n then (1:ℂ) else 0)=_
  rw [IsCoprime.mul_left_iff,IsCoprime.mul_left_iff,IsCoprime.mul_left_iff]
  simp only [hu,hla,h2b,true_and]
  rfl

lemma idealRowHom_sixth_denominator_mask (r n:Eis) (hr:Supported (Ideal.span {r})) :
    idealRowHom n ((Ideal.span {r})^6)=coprimalityMask r n := by
  rw [map_pow,←idealRowHom_argument_pow n 6 _ hr,idealRowHom_sixth_eq_mask n r hr]
  change (if IsCoprime n r then (1:ℂ) else 0)=(if IsCoprime r n then 1 else 0)
  rw [isCoprime_comm]

lemma mask_times_good_row (m:Eis) (um:Eisˣ) (am bm:ℕ) (g r n:Eis)
    (hg:Supported (Ideal.span {g})) (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (hn:Supported (Ideal.span {n})) :
    coprimalityMask m n*idealRowHom n (Ideal.span {r})=
      idealRowHom n ((Ideal.span {g})^6*Ideal.span {r}) := by
  rw [hm,coprimalityMask_good_part um am bm g n hn,map_mul,
    idealRowHom_sixth_denominator_mask g n hg]

theorem rowTwist_eq_fixed_times_good_row_primary
    (Ψ:Eis→*ℂ) (m f z:Eis) (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hpr:lambda^2∣r-1) (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=(Ψ*numeratorBadTwist u a b r hr) n *
      idealRowHom n ((Ideal.span {g})^6*Ideal.span {r}) := by
  rw [rowTwist_eq_actualPeriodicRow_primary Ψ m f z hmLam hm2 u a b r hr hpr hx n hpn]
  by_cases hn:Supported (Ideal.span {n})
  · change ((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*idealRowHom n (Ideal.span {r})=
      (Ψ n*numeratorBadTwist u a b r hr n)*_
    rw [show ((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*idealRowHom n (Ideal.span {r})=
      (Ψ n*numeratorBadTwist u a b r hr n)*(coprimalityMask m n*idealRowHom n (Ideal.span {r})) by ring,
      mask_times_good_row m um am bm g r n hg hm hn]
  · change ((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*_=
      (Ψ n*numeratorBadTwist u a b r hr n)*_
    rw [numeratorBadTwist_zero_of_not_supported u a b r hr n hn]
    simp only [mul_zero,zero_mul]

lemma fixedNumeratorTwist_periodic (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)})
      (Ψ*numeratorBadTwist u a b r hr) := by
  intro x y hxy
  change Ψ x*numeratorBadTwist u a b r hr x=Ψ y*numeratorBadTwist u a b r hr y
  rw [hΨ x y (Ideal.mul_le_left hxy),numeratorBadTwist_periodic u a b r hr x y (Ideal.mul_le_right hxy)]

theorem exists_fixed_twist_principal_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      (∀n,lambda^2∣n-1 → rowTwist Ψ m f z n=φ n *
        principalSexticRow (fun P:PrimeIndex I=>P.val) (primeIndex_pairwise_coprime I)
          (fun P=>(supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1)
          (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val%6)
          (finitePrimeModulus (fun P:PrimeIndex I=>P.val)) (span_finitePrimeModulus _)
          (Ideal.Quotient.mk _ n)) := by
  obtain ⟨um,am,bm,g,hg,hpg,hmf⟩:=exists_supported_numerator_factorization m hm
  obtain ⟨u,a,b,r,hr,hpr,hxf⟩:=exists_supported_numerator_factorization (f^4*z)
    (mul_ne_zero (pow_ne_zero _ hf) hz)
  let I:Ideal Eis:=(Ideal.span {g})^6*Ideal.span {r}
  have hI:Supported I:=by
    change Supported ((Ideal.span {g})^6*Ideal.span {r})
    rw [supported_mul_iff]
    exact ⟨supported_pow hg 6,hr⟩
  refine ⟨I,hI,Ψ*numeratorBadTwist u a b r hr,
    fixedNumeratorTwist_periodic Ψ Q hΨ u a b r hr,?_,?_⟩
  · intro n
    change ‖Ψ n*numeratorBadTwist u a b r hr n‖≤1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hΨnorm n)).trans (numeratorBadTwist_norm u a b r hr n)
  · intro n hpn
    rw [←idealRowHom_eq_principalSexticRow I hI n]
    exact rowTwist_eq_fixed_times_good_row_primary Ψ m f z hmLam hm2 um am bm g hg hmf
      u a b r hr hpr hxf n hpn

theorem rowTwist_completedT_eq_periodic (Ψ:Eis→*ℂ) (m f z:Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (hpr:lambda^2∣r-1)
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) (W:ℝ→ℂ) (X:ℝ) :
    completedT (rowTwist Ψ m f z) W X=completedT (actualPeriodicRow Ψ m u a b r hr) W X :=
  completedT_congr_primary _ _
    (rowTwist_eq_actualPeriodicRow_primary Ψ m f z hmLam hm2 u a b r hr hpr hx) W X

end CanonicalRowCompletion

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance A4unitsField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P

theorem exists_A4_local_units {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (c0 U w:Eis) (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1) :
    ∃σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∀i,(σ i:Eis⧸Ideal.span {p i})=
        Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i)) ∧
      ∀i,Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
        (σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1 := by
  have hone (i:ι) : ∃σ ε:(Eis⧸Ideal.span {p i})ˣ,
      (σ:Eis⧸Ideal.span {p i})=Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i) ∧
      Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
        (σ:Eis⧸Ideal.span {p i})*(ε:Eis⧸Ideal.span {p i})=-1 := by
    let q:=Ideal.Quotient.mk (Ideal.span {p i})
    have hz:q (∏k,p k)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
    have hb:q (ramifiedTraceLambda^3*c0)*q w=1 := by
      have he:=congrArg q hbez
      simp only [map_add,map_mul,map_pow,map_one,hz,mul_zero,zero_add] at he
      simpa only [map_mul,map_pow,mul_assoc,mul_comm,mul_left_comm] using he
    have hb0:q (ramifiedTraceLambda^3*c0)≠0 := by
      intro he
      rw [he,zero_mul] at hb
      exact zero_ne_one hb
    have hc0:q (cofactor p i)≠0 := by
      intro he
      have hi:=productTraceShift_inverse p hp hcop i
      change q (cofactor p i)*_=1 at hi
      rw [he,zero_mul] at hi
      exact zero_ne_one hi
    have hB:q (ramifiedTraceLambda^3*c0*cofactor p i)≠0 := by
      rw [map_mul]
      exact mul_ne_zero hb0 hc0
    have hS:q (ramifiedTraceLambda^2*c0*cofactor p i)≠0 := by
      intro he
      apply hB
      calc
        _=q ramifiedTraceLambda*q (ramifiedTraceLambda^2*c0*cofactor p i) := by
          simp only [map_mul,map_pow]
          ring
        _=0:=by rw [he,mul_zero]
    let σ:(Eis⧸Ideal.span {p i})ˣ:=Units.mk0 _ hS
    let B:(Eis⧸Ideal.span {p i})ˣ:=Units.mk0 _ hB
    refine ⟨σ,-(B*σ)⁻¹,rfl,?_⟩
    have hcancel:=congrArg (fun u:(Eis⧸Ideal.span {p i})ˣ=>(u:Eis⧸Ideal.span {p i}))
      (mul_inv_cancel (B*σ))
    simpa only [B,Units.val_mk0,Units.val_mul,Units.val_one,Units.val_neg,mul_neg] using congrArg Neg.neg hcancel
  choose σ ε hσ hε using hone
  exact ⟨σ,ε,hσ,hε⟩

end ShortDraftCusp

section
open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss CubicKubota CubicJacobiGlobal LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance principalStratumField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance principalStratumFintype (P:Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem principal_stratum_multiplier {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (c0 U w x:Eis) (hc0:c0≠0) (hr:lambda^2∣(∏i,p i)-1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (g:(∀i,(Eis⧸Ideal.span {p i})ˣ)→levelThree)
    (hC:∀v,(g v:SL(2,Eis)) 1 0=c0*∏i,p i)
    (hA:∀v,(9:Eis)*c0∣(g v:SL(2,Eis)) 0 0-(g (fun _=>1):SL(2,Eis)) 0 0)
    (hD:∀v,ramifiedTraceLambda^3*c0∣(g v:SL(2,Eis)) 1 1-(g (fun _=>1):SL(2,Eis)) 1 1)
    (σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ)
    (hfreq:∀v i,Ideal.Quotient.mk (Ideal.span {p i}) ((g v:SL(2,Eis)) 0 0)=
      (σ i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}))
    (hε:∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (j:ι→ℕ) (hj:∀i,j i<6) :
    (∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
        (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i))*
      star (complexCharacter (g v))*
      ShortDraftTrace.breveE (-(eisEmbedding ((g v:SL(2,Eis)) 1 1)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))) =
    (star (eisEmbedding (symbol c0 ((g (fun _=>1):SL(2,Eis)) 0 0)))*
      A4BadPhase c0 hc0 ((g (fun _=>1):SL(2,Eis)) 1 1) U x)*
    ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (σ i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (ε i)*
      bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x) := by
  let a0:=(g (fun _=>1):SL(2,Eis)) 0 0
  let d0:=(g (fun _=>1):SL(2,Eis)) 1 1
  let C:=star (eisEmbedding (symbol c0 a0))*A4BadPhase c0 hc0 d0 U x
  let f:=fun i (v:(Eis⧸Ideal.span {p i})ˣ)=>frequencyRow
    (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i)
    (σ i) (ε i) (Ideal.Quotient.mk _ x) v
  have hpoint (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
      star (complexCharacter (g v))*
      ShortDraftTrace.breveE (-(eisEmbedding ((g v:SL(2,Eis)) 1 1)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))=
      C*∏i,frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (σ i) (ε i) (Ideal.Quotient.mk _ x) (v i) := by
    have hbad:A4BadPhase c0 hc0 ((g v:SL(2,Eis)) 1 1) U x=A4BadPhase c0 hc0 d0 U x := by
      apply A4BadPhase_eq_of_residue
      convert dvd_mul_of_dvd_left (hD v) U using 1 ; ring
    have hfixed:symbol c0 ((g v:SL(2,Eis)) 0 0)=symbol c0 a0 :=
      A3_fixed_factor_congr 9 c0 _ _ (dvd_refl _) (levelThree_primary (g v))
        (levelThree_primary (g (fun _=>1))) (hA v)
    have hdet:(g v:SL(2,Eis)) 0 0*(g v:SL(2,Eis)) 1 1-
        (g v:SL(2,Eis)) 0 1*(c0*∏i,p i)=1 := by
      rw [←hC v]
      simpa only [Matrix.det_fin_two] using (g v:SL(2,Eis)).property
    have hlocal:=A3_A4_frequency_product p hp hcop hg
      ((g v:SL(2,Eis)) 0 0) ((g v:SL(2,Eis)) 0 1) c0 ((g v:SL(2,Eis)) 1 1)
      U w x hc0 hdet hbez σ ε (fun i=>(v i:Eis⧸Ideal.span {p i})) (hfreq v) hε
    rw [A3_principal_character (g v) (g v).property c0 (∏i,p i) (hC v) hr,hfixed,star_mul]
    calc
      _=star (eisEmbedding (symbol c0 a0))*
          (star (eisEmbedding (symbol ((g v:SL(2,Eis)) 0 0) (∏i,p i)))*
            ShortDraftTrace.breveE (-(eisEmbedding ((g v:SL(2,Eis)) 1 1)*(eisEmbedding x/eisLam^4))/
              (eisEmbedding c0*eisEmbedding (∏i,p i)))) := by ring
      _=_ := by rw [hlocal,hbad];dsimp only [C];ring
  calc
    _=C*∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,∏i,f i (v i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [mul_assoc, hpoint]
      simp only [f,frequencyRow,Finset.prod_mul_distrib]
      ring
    _=C*∏i,∑v:(Eis⧸Ideal.span {p i})ˣ,f i v := by rw [Fintype.prod_sum]
    _=_ := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact canonical_frequencyRow_units (Ideal.span {p i}) (hg i) (hchar i)
        (quotientTrace (p i) (hp i))
        (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) (j i) (hj i) (σ i) (ε i) _

end ShortDraftCusp

namespace CubicEisenstein
open ActualEisensteinCubic CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma cuspRepresentative_zero_eq_one : cuspRepresentative 0=(1:SL(2,Eis)) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspRepresentative,cuspParameter,lowerCuspMatrix]

def principalCuspDatum (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) : SourceCuspDatum where
  gamma:=sourceLevelInclusion g
  index:=0
  lower_ne_zero:=by
    change (integralComplexMatrix (g:SL(2,Eis))*integralComplexMatrix (cuspRepresentative 0)) 1 0≠0
    rw [cuspRepresentative_zero_eq_one,map_one,mul_one,integralComplexMatrix_apply]
    exact eisEmbedding_ne_zero hc

lemma principalCuspDatum_matrix (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) :
    (principalCuspDatum g hc).matrix=integralComplexMatrix (g:SL(2,Eis)) := by
  change integralComplexMatrix (g:SL(2,Eis))*integralComplexMatrix (cuspRepresentative 0)=_
  rw [cuspRepresentative_zero_eq_one,map_one,mul_one]

lemma principalCuspDatum_height (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) :
    (principalCuspDatum g hc).heightScale=‖eisEmbedding ((g:SL(2,Eis)) 1 0)‖^2 := by
  rw [SourceCuspDatum.heightScale,principalCuspDatum_matrix,integralComplexMatrix_apply]

lemma principalCuspDatum_dual (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) :
    (principalCuspDatum g hc).dualPoint=
      -eisEmbedding ((g:SL(2,Eis)) 1 1)/eisEmbedding ((g:SL(2,Eis)) 1 0) := by
  rw [SourceCuspDatum.dualPoint,principalCuspDatum_matrix]
  rfl

lemma principalCuspDatum_multiplier (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) :
    (principalCuspDatum g hc).multiplier=
      -star (complexCharacter g)/(eisEmbedding ((g:SL(2,Eis)) 1 0))^2 := by
  rw [SourceCuspDatum.multiplier,principalCuspDatum_matrix,integralComplexMatrix_apply]
  change -star (levelTwoComplexCharacter (sourceLevelInclusion g))/_=_
  rw [sourceLevelInclusion_character]

lemma infinity_phaseNumerator_embedding (h:Eis) :
    eisEmbedding (ramifiedTraceLambda*h)=-eisLam^4*cuspFrequency h := by
  rw [map_mul,ramifiedEmbedding_traceLambda,cuspFrequency]
  field_simp [eisLam_ne_zero]
  linear_combination eisEmbedding h*TraceLambdaPhase.eisLam_sq

lemma principalCuspDatum_phase (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) (h:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency h*(principalCuspDatum g hc).dualPoint)=
      ShortDraftTrace.breveE (-(eisEmbedding ((g:SL(2,Eis)) 1 1)*
        (eisEmbedding (ramifiedTraceLambda*h)/eisLam^4))/eisEmbedding ((g:SL(2,Eis)) 1 0)) := by
  rw [principalCuspDatum_dual,infinity_phaseNumerator_embedding]
  congr 1
  field_simp [eisLam_ne_zero,eisEmbedding_ne_zero hc]

end CubicEisenstein
end

namespace CubicEisenstein
open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic
open CubicKubota CubicJacobiGlobal ShortDraftCusp LocalReflectionBrackets FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance smoothingField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance smoothingFintype (P:Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem principal_stratum_smoothed {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (c0 U w:Eis) (hc0:c0≠0) (hr:lambda^2∣(∏i,p i)-1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (g:(∀i,(Eis⧸Ideal.span {p i})ˣ)→levelThree)
    (hC:∀v,(g v:SL(2,Eis)) 1 0=c0*∏i,p i)
    (hA:∀v,(9:Eis)*c0∣(g v:SL(2,Eis)) 0 0-(g (fun _=>1):SL(2,Eis)) 0 0)
    (hD:∀v,ramifiedTraceLambda^3*c0∣(g v:SL(2,Eis)) 1 1-(g (fun _=>1):SL(2,Eis)) 1 1)
    (σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ)
    (hfreq:∀v i,Ideal.Quotient.mk (Ideal.span {p i}) ((g v:SL(2,Eis)) 0 0)=
      (σ i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}))
    (hε:∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    let c:=c0*∏i,p i
    let Q:ℝ:=‖eisEmbedding c‖^2
    let hc:∀v,(g v:SL(2,Eis)) 1 0≠0:=fun v=>by
      rw [hC v];exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
    let weight:=fun v:∀i,(Eis⧸Ideal.span {p i})ˣ=>
      ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
        (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i)
    (∑v,weight v*(principalCuspDatum (g v) (hc v)).smoothedKernel W X)=
    fixedRadialCoefficientScalar*∑'t:ThetaFullIndex,
      ((fixedConjugateCuspArray 0 t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
        sourceFrequencyAngle (thetaFullFrequency t))/
        ((ramifiedScale 1 completedRamifiedStep t.2.1*
          Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      CubicReflectionKernel.paperKernel (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency t)/(27*Q^2))*
      (-(Q:ℂ)/(eisEmbedding c)^2*
        ((star (eisEmbedding (symbol c0 ((g (fun _=>1):SL(2,Eis)) 0 0)))*
          A4BadPhase c0 hc0 ((g (fun _=>1):SL(2,Eis)) 1 1) U (ramifiedTraceLambda*thetaFullFrequency t))*
        ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (σ i)*
          phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (ε i)*
          bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
            (Ideal.Quotient.mk _ (ramifiedTraceLambda*thetaFullFrequency t)))) := by
  dsimp only
  let c:=c0*∏i,p i
  let Q:ℝ:=‖eisEmbedding c‖^2
  have hc:∀v,(g v:SL(2,Eis)) 1 0≠0:=fun v=>by
    rw [hC v];exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  let d:=fun v:∀i,(Eis⧸Ideal.span {p i})ˣ=>principalCuspDatum (g v) (hc v)
  let weight:=fun v:∀i,(Eis⧸Ideal.span {p i})ˣ=>
    ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
      (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i)
  have hheight:∀v,(d v).heightScale=Q:=by
    intro v
    rw [principalCuspDatum_height,hC v]
  have hcol:=sum_smoothedKernel_common_cusp d weight 0 Q (fun _=>rfl) hheight
    W lo hi hlo hsupp hW X hX
  change (∑v,weight v*(d v).smoothedKernel W X)=_
  rw [hcol]
  congr 1
  apply tsum_congr
  intro t
  simp only [sourceCuspScale,Matrix.cons_val_zero,Complex.ofReal_one,div_one,one_pow,mul_one]
  congr 1
  let x:=ramifiedTraceLambda*thetaFullFrequency t
  have hlocal:=principal_stratum_multiplier p hp hcop hg hchar c0 U w x hc0 hr hbez
    g hC hA hD σ ε hfreq hε j hj
  calc
    _=(-(Q:ℂ)/(eisEmbedding c)^2)*
        ∑v,weight v*star (complexCharacter (g v))*
          ShortDraftTrace.breveE (-(eisEmbedding ((g v:SL(2,Eis)) 1 1)*(eisEmbedding x/eisLam^4))/
            (eisEmbedding c0*eisEmbedding (∏i,p i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      change weight v*((principalCuspDatum (g v) (hc v)).multiplier*(Q:ℂ))*
        ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency t)*(principalCuspDatum (g v) (hc v)).dualPoint)=_
      rw [principalCuspDatum_multiplier,principalCuspDatum_phase,hC v,map_mul]
      dsimp only [c,x]
      rw [map_mul]
      ring
    _=_:=by rw [hlocal]

end CubicEisenstein

open scoped Classical BigOperators MatrixGroups

namespace ShortDraftCRT
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT PrimaryIdealUnitReindex
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_primary_unit_multiple (x:Eis) (hx:¬lambda∣x) :
    ∃u:Eisˣ,lambda^2∣u.val*x-1 := by
  have hg:primaryGenerator (Ideal.span {x})≠0:=primaryGenerator_span_ne_zero_iff x |>.mpr hx
  have hspec:=primaryGenerator_spec (Ideal.span {x}) hg
  have ha:Associated x (primaryGenerator (Ideal.span {x})):=
    Ideal.span_singleton_eq_span_singleton.mp hspec.1.symm
  obtain ⟨u,hu⟩:=ha
  refine ⟨u,?_⟩
  rw [mul_comm,hu]
  exact hspec.2

lemma normalize_coprime_pair (a c:Eis) (hcop:IsCoprime a c) :
    ∃u:Eisˣ,IsCoprime (u.val*a) (u.val*c) ∧
      (lambda∣u.val*c→lambda^2∣u.val*a-1) ∧
      (¬lambda∣u.val*c→lambda^2∣u.val*c-1) := by
  have hunit (u:Eisˣ):IsCoprime (u.val*a) (u.val*c) := by
    obtain ⟨r,s,hrs⟩:=hcop
    refine ⟨r*(↑u⁻¹:Eis),s*(↑u⁻¹:Eis),?_⟩
    calc
      _=((↑u⁻¹:Eis)*u.val)*(r*a+s*c):=by ring
      _=1:=by rw [Units.inv_mul,hrs,mul_one]
  have hd (u:Eisˣ):lambda∣u.val*c↔lambda∣c := by
    constructor
    · intro h
      have hh:=dvd_mul_of_dvd_right h (↑u⁻¹:Eis)
      simpa only [←mul_assoc,Units.inv_mul,one_mul] using hh
    · intro h
      exact dvd_mul_of_dvd_right h u.val
  by_cases hc:lambda∣c
  · have ha:¬lambda∣a:=fun h=>lambda_prime_actual.not_isUnit (hcop.isUnit_of_dvd' h hc)
    obtain ⟨u,hu⟩:=exists_primary_unit_multiple a ha
    exact ⟨u,hunit u,fun _=>hu,fun hn=>False.elim (hn ((hd u).mpr hc))⟩
  · obtain ⟨u,hu⟩:=exists_primary_unit_multiple c hc
    exact ⟨u,hunit u,fun h=>False.elim (hc ((hd u).mp h)),fun _=>hu⟩

theorem exists_normalized_rational_cusp (a c:Eis) (hc:c≠0) :
    ∃a0 c0:Eis,c0≠0 ∧ c0∣c ∧ IsCoprime a0 c0 ∧
      eisEmbedding a0/eisEmbedding c0=eisEmbedding a/eisEmbedding c ∧
      (lambda∣c0→lambda^2∣a0-1) ∧ (¬lambda∣c0→lambda^2∣c0-1) := by
  let d:Eis:=IsBezout.gcd a c
  obtain ⟨a',ha⟩:=IsBezout.gcd_dvd_left a c
  obtain ⟨c',hc'⟩:=IsBezout.gcd_dvd_right a c
  change a=d*a' at ha
  change c=d*c' at hc'
  have hd:d≠0:=by intro hz; exact hc (by rw [hc',hz,zero_mul])
  have hcp:c'≠0:=by intro hz; exact hc (by rw [hc',hz,mul_zero])
  obtain ⟨r,s,hrs⟩:=IsBezout.gcd_eq_sum a c
  have hred:IsCoprime a' c':=by
    refine ⟨r,s,?_⟩
    apply mul_left_cancel₀ hd
    change d*(r*a'+s*c')=d*1
    calc
      _=r*a+s*c:=by rw [ha,hc'];ring
      _=d:=hrs
      _=_:=by ring
  obtain ⟨u,hu,hua,huc⟩:=normalize_coprime_pair a' c' hred
  refine ⟨u.val*a',u.val*c',mul_ne_zero u.ne_zero hcp,?_,hu,?_,hua,huc⟩
  · refine ⟨d*(↑u⁻¹:Eis),?_⟩
    rw [hc']
    calc
      d*c'=((u.val*(↑u⁻¹:Eis))*d)*c':=by rw [Units.mul_inv,one_mul]
      _=_:=by ring
  · rw [ha,hc',map_mul,map_mul,map_mul,map_mul]
    have he:=eisEmbedding_ne_zero hd
    have hf:=eisEmbedding_ne_zero hcp
    have hu0:=eisEmbedding_ne_zero u.ne_zero
    field_simp

end ShortDraftCRT

end

end OAI

end Source285

/- Original source: OAI/NumberTheory/DirichletL/Eisenstein/FixedConductor.lean; sha256: f644f63b1e9d735658f616059dffaab6bc22d4323ad79edcb2ab73d8a9cfe467 -/
section Source286
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

open scoped Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

lemma divisor_principal_norm_le (c0 c:Eis) (hc:c≠0) (hdiv:c0∣c) :
    (Ideal.absNorm (Ideal.span {c0}):ℝ)≤(Ideal.absNorm (Ideal.span {c}):ℝ) := by
  have hp:0<Ideal.absNorm (Ideal.span {c}):=Nat.pos_of_ne_zero (by
    intro hz
    exact hc (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hd:Ideal.absNorm (Ideal.span {c0})∣Ideal.absNorm (Ideal.span {c}) := by
    obtain ⟨d,hd⟩:=hdiv
    rw [hd,←Ideal.span_singleton_mul_span_singleton,map_mul]
    exact dvd_mul_right _ _
  exact_mod_cast Nat.le_of_dvd hp hd

def fixedCuspLevelBound (c:Eis) : ℝ :=
  243*(Ideal.absNorm (Ideal.span {c}):ℝ)^2

def fixedCuspLevelScale (j:Fin 3) (c0:Eis) : ℝ :=
  27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0}):ℝ)^2

lemma fixedCuspLevelBound_ge_one (c:Eis) (hc:c≠0) : 1≤fixedCuspLevelBound c := by
  have hp:1≤Ideal.absNorm (Ideal.span {c}):=Nat.one_le_iff_ne_zero.mpr (by
    intro hz
    exact hc (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hr:(1:ℝ)≤(Ideal.absNorm (Ideal.span {c}):ℝ):=by exact_mod_cast hp
  unfold fixedCuspLevelBound
  nlinarith

lemma fixedCuspLevelScale_pos (j:Fin 3) (c0:Eis) (hc0:c0≠0) : 0<fixedCuspLevelScale j c0 := by
  have hp:0<Ideal.absNorm (Ideal.span {c0}):=Nat.pos_of_ne_zero (by
    intro hz
    exact hc0 (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hr:(0:ℝ)<(Ideal.absNorm (Ideal.span {c0}):ℝ):=by exact_mod_cast hp
  have hs:=sourceCuspScale_pos j
  unfold fixedCuspLevelScale
  positivity

lemma fixedCuspLevelScale_le (j:Fin 3) (c0 c:Eis) (hc:c≠0) (hdiv:c0∣c) :
    fixedCuspLevelScale j c0≤fixedCuspLevelBound c := by
  have hd:=divisor_principal_norm_le c0 c hc hdiv
  have hs:(sourceCuspScale j)^2≤9:=by fin_cases j <;> norm_num [sourceCuspScale]
  unfold fixedCuspLevelScale fixedCuspLevelBound
  calc
    27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0}):ℝ)^2≤
      27*9*(Ideal.absNorm (Ideal.span {c}):ℝ)^2:=by gcongr
    _=_:=by ring

end

section
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_traceLambda_pow_four : ramifiedTraceLambda^4=(9:Eis) := by
  apply eisEmbedding_injective
  rw [map_pow,map_ofNat,ramifiedEmbedding_traceLambda]
  calc
    _=(eisLam^2)^2:=by ring
    _=9:=by rw [TraceLambdaPhase.eisLam_sq];norm_num

structure PrincipalStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) (N a0 c0:Eis) where
  lift : (∀i,(Eis⧸Ideal.span {p i})ˣ)→ι→Eis
  lift_period : ∀v i,N^2∣lift v i
  lift_residue : ∀v i,Ideal.Quotient.mk (Ideal.span {p i}) (lift v i)=(v i:Eis⧸Ideal.span {p i})
  U : Eis
  w : Eis
  bezout : U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1
  sigma : ∀i,(Eis⧸Ideal.span {p i})ˣ
  epsilon : ∀i,(Eis⧸Ideal.span {p i})ˣ
  sigma_value : ∀i,(sigma i:Eis⧸Ideal.span {p i})=
    Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i)
  epsilon_value : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
    (sigma i:Eis⧸Ideal.span {p i})*(epsilon i:Eis⧸Ideal.span {p i})=-1
  gamma : (∀i,(Eis⧸Ideal.span {p i})ˣ)→levelThree
  numerator : ∀v,(gamma v:SL(2,Eis)) 0 0=finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  denominator : ∀v,(gamma v:SL(2,Eis)) 1 0=c0*∏i,p i
  numerator_fixed : ∀v,(9:Eis)*c0∣(gamma v:SL(2,Eis)) 0 0-(gamma (fun _=>1):SL(2,Eis)) 0 0
  inverse_fixed : ∀v,ramifiedTraceLambda^3*c0∣(gamma v:SL(2,Eis)) 1 1-(gamma (fun _=>1):SL(2,Eis)) 1 1

theorem exists_principalStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (N a0 c0:Eis) (hc0:c0≠0) (hc3:(3:Eis)∣c0)
    (hN:(9:Eis)*c0∣N) (ha0:lambda^2∣a0-1) (hac:IsCoprime a0 c0)
    (hNp:∀i,IsCoprime N (p i)) :
    Nonempty (PrincipalStratumArithmetic p N a0 c0) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have hcN:c0∣N:=(dvd_mul_left c0 9).trans hN
  have hD9:ramifiedTraceLambda^3*c0∣(9:Eis)*c0 := by
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [←A4_traceLambda_pow_four]
    ring
  have hDN:ramifiedTraceLambda^3*c0∣N:=hD9.trans hN
  have hl9:ramifiedTraceLambda∣(9:Eis) := by
    rw [←A4_traceLambda_pow_four]
    exact dvd_pow_self _ (by decide)
  have hlN:ramifiedTraceLambda∣N:=hl9.trans h9N
  have hstdN:lambda^2∣N:=lambda_sq_dvd_three.trans
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N)
  let r:Eis:=∏i,p i
  have hr:lambda^2∣r-1:=primary_finset_product Finset.univ p (fun i _=>hprimary i)
  have hNr:IsCoprime N r:=IsCoprime.prod_right (fun i _=>hNp i)
  have hrNc:IsCoprime r (N*c0):=hNr.symm.mul_right
    (hNr.symm.of_isCoprime_of_dvd_right hcN)
  obtain ⟨U,w,huw⟩:=hNr.symm.of_isCoprime_of_dvd_right hDN
  have hbez:U*r+(ramifiedTraceLambda^3*w)*c0=1 := by
    linear_combination huw
  obtain ⟨σ,ε,hσ,hε⟩:=exists_A4_local_units p hp hcop c0 U w hbez
  have hlf (v:∀i,(Eis⧸Ideal.span {p i})ˣ):=
    exists_strong_unit_frequency_lifts N p hNp v
  choose lift hlift hres hlcop using hlf
  let a:=fun v=>finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  have hap:∀v,lambda^2∣a v-1 := by
    intro v
    have hfixed:N∣a v-a0*r:=finiteCrossNumerator_fixed N a0 c0 ramifiedTraceLambda p (lift v)
      (fun i=>(dvd_pow_self N (by decide : (2:ℕ)≠0)).trans (hlift v i))
    have hbase:=primary_mul a0 r ha0 hr
    convert dvd_add (hstdN.trans hfixed) hbase using 1 ; ring
  have hpairs:Pairwise (Function.onFun IsCoprime p):=by
    intro i k hik
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hik)
  have hacop:∀v,IsCoprime (a v) (c0*r) := by
    intro v
    exact finiteCrossNumerator_coprime a0 c0 ramifiedTraceLambda p (lift v) hac hpairs
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hcN)
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hlN) (hlcop v)
  obtain ⟨b,d,C,hdet,hb,hd,hmat⟩:=exists_primary_numerator_sector_completions
    N c0 hc0 h9N (fun (_:∀i,(Eis⧸Ideal.span {p i})ˣ)=>()) a (fun _=>r)
    hap (fun _=>hr) hacop (fun _=>hrNc)
    (fun v z _=>finiteCrossNumerator_fixed_sector N a0 c0 ramifiedTraceLambda p (lift v)
      p (lift z) hcN (hlift v) (hlift z) (by simp))
    (fun _ _ _=>by simp)
  let mat:=fun v=>controlledCompletionMatrix (a v) (b v) (c0*r) (d v) (hdet v)
  have hm:∀v,mat v∈levelThree:=by
    intro v
    apply A3_principal_mem_levelThree (mat v)
    · exact three_dvd_primary_sub_one (a v) (hap v)
    · exact (show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans (hb v)
    · exact dvd_mul_of_dvd_left hc3 r
    · exact hd v
  let gamma:=fun v=>(⟨mat v,hm v⟩:levelThree)
  have hentry (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i j:Fin 2):
      N∣(mat v) i j-(mat (fun _=>1)) i j := by
    have he:=congrArg (fun T:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {N})=>T i j)
      ((hmat v).trans (hmat (fun _=>1)).symm)
    change Ideal.Quotient.mk (Ideal.span {N}) ((mat v) i j)=
      Ideal.Quotient.mk (Ideal.span {N}) ((mat (fun _=>1)) i j) at he
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  exact ⟨{
    lift := lift
    lift_period := hlift
    lift_residue := hres
    U := U
    w := w
    bezout := hbez
    sigma := σ
    epsilon := ε
    sigma_value := hσ
    epsilon_value := hε
    gamma := gamma
    numerator := fun _=>rfl
    denominator := fun _=>rfl
    numerator_fixed := fun v=>hN.trans (hentry v 0 0)
    inverse_fixed := fun v=>hDN.trans (hentry v 1 1)
  }⟩

lemma PrincipalStratumArithmetic.frequency_congruence {ι:Type*} [Fintype ι]
    {p:ι→Eis} {N a0 c0:Eis} (D:PrincipalStratumArithmetic p N a0 c0)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) ((D.gamma v:SL(2,Eis)) 0 0)=
      (D.sigma i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}) := by
  rw [D.numerator,finiteCrossNumerator_local,D.sigma_value,D.lift_residue]

end

open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic
open CubicKubota CubicJacobiGlobal ShortDraftCusp LocalReflectionBrackets FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
namespace PrincipalStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis}

noncomputable def datum (D:PrincipalStratumArithmetic p N a0 c0)
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : SourceCuspDatum :=
  principalCuspDatum (D.gamma v) (by
    rw [D.denominator];exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

lemma datum_point (D:PrincipalStratumArithmetic p N a0 c0)
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.datum hp hc0 v).point=eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i) := by
  rw [SourceCuspDatum.point,datum,principalCuspDatum_matrix,
    integralComplexMatrix_apply,integralComplexMatrix_apply,D.numerator,D.denominator]
  simpa only [ramifiedEmbedding_traceLambda] using
    ShortDraftCRT.finiteCrossNumerator_fraction a0 c0 ramifiedTraceLambda p (D.lift v) hc0 hp

noncomputable def smoothedValue (D:PrincipalStratumArithmetic p N a0 c0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0) (hc0:c0≠0)
    (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
    (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
      (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i))*
    (D.datum hp hc0 v).smoothedKernel W X

noncomputable def reflectedValue (D:PrincipalStratumArithmetic p N a0 c0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0) (hc0:c0≠0)
    (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Field (Eis⧸Ideal.span {p i}):=Ideal.Quotient.field _
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  let c:=c0*∏i,p i
  let Q:ℝ:=‖eisEmbedding c‖^2
  exact fixedRadialCoefficientScalar*∑'t:ThetaFullIndex,
    ((fixedConjugateCuspArray 0 t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
      sourceFrequencyAngle (thetaFullFrequency t))/
      ((ramifiedScale 1 completedRamifiedStep t.2.1*
        Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
    CubicReflectionKernel.paperKernel (Vstar W)
      (X*sourceCuspRadialLength (thetaFullFrequency t)/(27*Q^2))*
    (-(Q:ℂ)/(eisEmbedding c)^2*
      ((star (eisEmbedding (symbol c0 ((D.gamma (fun _=>1):SL(2,Eis)) 0 0)))*
        A4BadPhase c0 hc0 ((D.gamma (fun _=>1):SL(2,Eis)) 1 1) D.U (ramifiedTraceLambda*thetaFullFrequency t))*
      ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
        phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)*
        bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk _ (ramifiedTraceLambda*thetaFullFrequency t))))

theorem smoothed_eq_reflected (D:PrincipalStratumArithmetic p N a0 c0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0) (hc0:c0≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hr:lambda^2∣(∏i,p i)-1) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.smoothedValue hp hc0 hg j W X=D.reflectedValue hp hc0 hg j W X := by
  simpa only [smoothedValue,reflectedValue,datum] using
    principal_stratum_smoothed p hp hcop hg hchar c0 D.U D.w hc0 hr D.bezout
      D.gamma D.denominator D.numerator_fixed D.inverse_fixed D.sigma D.epsilon
      D.frequency_congruence D.epsilon_value j hj W lo hi hlo hsupp hW X hX

end PrincipalStratumArithmetic

theorem exists_constructed_principal_reflection {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (N a0 c0:Eis) (hc0:c0≠0) (hc3:(3:Eis)∣c0)
    (hN:(9:Eis)*c0∣N) (ha0:lambda^2∣a0-1) (hac:IsCoprime a0 c0)
    (hNp:∀i,IsCoprime N (p i)) :
    ∃D:PrincipalStratumArithmetic p N a0 c0,
      ∀j:ι→ℕ,(∀i,j i<6)→∀(W:ℝ→ℂ)(lo hi:ℝ),0<lo→
        Function.support W⊆Set.Icc lo hi→ContDiff ℝ ∞ W→∀X:ℝ,0<X→
        D.smoothedValue hp hc0 hg j W X=D.reflectedValue hp hc0 hg j W X := by
  obtain ⟨D⟩:=exists_principalStratumArithmetic p hp hcop hprimary N a0 c0 hc0 hc3 hN ha0 hac hNp
  refine ⟨D,?_⟩
  intro j hj W lo hi hlo hsupp hW X hX
  exact D.smoothed_eq_reflected hp hc0 hcop hg hchar
    (primary_finset_product Finset.univ p (fun i _=>hprimary i)) j hj W lo hi hlo hsupp hW X hX

end CubicEisenstein

open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

abbrev BasePrimeIndex (I Q:Ideal Eis) := {P:PrimeIndex I // Q≤P.val}
abbrev FreePrimeIndex (I Q:Ideal Eis) := {P:PrimeIndex I // ¬Q≤P.val}

def basePrimeRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) : Eis→*ℂ where
  toFun n:=∏P:BasePrimeIndex I Q,
    (actualSextic P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp only [map_one,Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

def freePrimeRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) : Eis→*ℂ where
  toFun n:=∏P:FreePrimeIndex I Q,
    (actualSextic P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp only [map_one,Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

lemma basePrimeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    ‖basePrimeRow I hI Q n‖≤1 := by
  change ‖∏P:BasePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

lemma freePrimeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    ‖freePrimeRow I hI Q n‖≤1 := by
  change ‖∏P:FreePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

lemma basePrimeRow_periodic (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) :
    CanonicalCoefficientClass.FactorsModulo Q (basePrimeRow I hI Q) := by
  intro x y hxy
  change (∏P:BasePrimeIndex I Q,_)=∏P:BasePrimeIndex I Q,_
  apply Finset.prod_congr rfl
  intro P hP
  have he:Ideal.Quotient.mk P.val.val x=Ideal.Quotient.mk P.val.val y:=
    Ideal.Quotient.eq.mpr (P.property hxy)
  rw [he]

lemma idealRowHom_fixed_conductor_split (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    idealRowHom n I=basePrimeRow I hI Q n*freePrimeRow I hI Q n := by
  rw [idealRowHom_eq_prime_count_product I hI n]
  exact (Fintype.prod_subtype_mul_prod_subtype (fun P:PrimeIndex I=>Q≤P.val)
    (fun P:PrimeIndex I=>(actualSextic P.val ((supported_factors_good I hI P.val
      (Multiset.mem_toFinset.mp P.property)).2.1)^((normalizedFactors I).count P.val%6))
      (Ideal.Quotient.mk P.val n))).symm

lemma freePrimeIndex_pairwise_coprime (I Q:Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (fun P:FreePrimeIndex I Q=>P.val.val)) := by
  intro P R hPR
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPR (Subtype.ext (Subtype.ext he)))

lemma freePrimeIndex_coprime (I Q:Ideal Eis) (P:FreePrimeIndex I Q) :
    IsCoprime Q P.val.val := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra ht
  have he:P.val.val=Q⊔P.val.val:=
    (show P.val.val.IsMaximal from inferInstance).eq_of_le ht le_sup_right
  exact P.property (le_sup_left.trans he.symm.le)

lemma freePrimeProduct_coprime (I Q:Ideal Eis) :
    IsCoprime Q (∏P:FreePrimeIndex I Q,P.val.val) :=
  IsCoprime.prod_right (fun P _=>freePrimeIndex_coprime I Q P)

lemma freePrimeRow_eq_principalSexticRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    freePrimeRow I hI Q n=
      principalSexticRow (fun P:FreePrimeIndex I Q=>P.val.val) (freePrimeIndex_pairwise_coprime I Q)
        (fun P=>(supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1)
        (fun P=>(normalizedFactors I).count P.val.val%6)
        (finitePrimeModulus (fun P:FreePrimeIndex I Q=>P.val.val))
        (span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [principalSexticRow_mk]
  rfl

theorem fixed_conductor_absorb_shared_primes (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (hφn:∀n,‖φ n‖≤1) :
    CanonicalCoefficientClass.FactorsModulo Q (φ*basePrimeRow I hI Q) ∧
    (∀n,‖(φ*basePrimeRow I hI Q) n‖≤1) ∧
    IsCoprime Q (∏P:FreePrimeIndex I Q,P.val.val) ∧
    (∀n,φ n*idealRowHom n I=(φ*basePrimeRow I hI Q) n*freePrimeRow I hI Q n) := by
  refine ⟨?_,?_,freePrimeProduct_coprime I Q,?_⟩
  · intro x y hxy
    change φ x*basePrimeRow I hI Q x=φ y*basePrimeRow I hI Q y
    rw [hφ x y hxy,basePrimeRow_periodic I hI Q x y hxy]
  · intro n
    change ‖φ n*basePrimeRow I hI Q n‖≤1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hφn n)).trans (basePrimeRow_norm I hI Q n)
  · intro n
    rw [idealRowHom_fixed_conductor_split I hI Q n]
    exact (mul_assoc _ _ _).symm

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma freePrimeRow_periodic (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) :
    CanonicalCoefficientClass.FactorsModulo (∏P:FreePrimeIndex I Q,P.val.val) (freePrimeRow I hI Q) := by
  intro x y hxy
  change (∏P:FreePrimeIndex I Q,_)=∏P:FreePrimeIndex I Q,_
  apply Finset.prod_congr rfl
  intro P hP
  have hm:x-y∈P.val.val:=
    (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ P))) hxy
  rw [Ideal.Quotient.eq.mpr hm]

lemma fixedFreeRow_periodic (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) :
    CanonicalCoefficientClass.FactorsModulo (Q*(∏P:FreePrimeIndex I Q,P.val.val))
      (φ*freePrimeRow I hI Q) := by
  intro x y hxy
  change φ x*freePrimeRow I hI Q x=φ y*freePrimeRow I hI Q y
  rw [hφ x y (Ideal.mul_le_left hxy),freePrimeRow_periodic I hI Q x y (Ideal.mul_le_right hxy)]

lemma fixedFreeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis)
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (n:Eis) : ‖(φ*freePrimeRow I hI Q) n‖≤1 := by
  change ‖φ n*freePrimeRow I hI Q n‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hφ n)).trans (freePrimeRow_norm I hI Q n)

theorem exists_actual_coprime_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (∀n,lambda^2∣n-1 → rowTwist Ψ m f z n=φ n*freePrimeRow I hI (Q*Ideal.span {(72:Eis)}) n) := by
  obtain ⟨I,hI,φ,hφ,hφn,hrow⟩:=exists_fixed_twist_principal_row Ψ Q hΨ hΨnorm m f z hm hf hz hmLam hm2
  obtain ⟨hperiod,hnorm,hcop,hprod⟩:=fixed_conductor_absorb_shared_primes I hI _ φ hφ hφn
  refine ⟨I,hI,φ*basePrimeRow I hI _,hperiod,hnorm,hcop,?_⟩
  intro n hpn
  rw [hrow n hpn,←idealRowHom_eq_principalSexticRow I hI n,hprod n]

theorem exists_actual_coprime_completed_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hQ:Q≠0) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (Q*Ideal.span {(72:Eis)}*(∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val))≠0 ∧
      CanonicalCoefficientClass.FactorsModulo
        (Q*Ideal.span {(72:Eis)}*(∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val))
        (φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) ∧
      (∀n,‖(φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) n‖≤1) ∧
      (∀W X,completedT (rowTwist Ψ m f z) W X=
        completedT (φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) W X) := by
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hrow⟩:=exists_actual_coprime_row Ψ Q hΨ hΨnorm m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,hcop,?_,fixedFreeRow_periodic I hI _ φ hφ,
    fixedFreeRow_norm I hI _ φ hφn,?_⟩
  · apply mul_ne_zero
    · apply mul_ne_zero hQ
      simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
      norm_num
    · exact finite_prime_product_ne_bot (fun P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)})=>P.val.val)
  · intro W X
    exact completedT_congr_primary _ _ hrow W X

def fixedQuotientValue (Q:Ideal Eis) (φ:Eis→*ℂ) (x:Eis⧸Q) : ℂ := φ (Quotient.out x)

lemma fixedQuotientValue_mk (Q:Ideal Eis) (φ:Eis→*ℂ)
    (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (n:Eis) :
    fixedQuotientValue Q φ (Ideal.Quotient.mk Q n)=φ n :=
  hφ _ _ (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out _))

lemma fixedQuotientValue_norm (Q:Ideal Eis) (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (x:Eis⧸Q) :
    ‖fixedQuotientValue Q φ x‖≤1 := hφ _

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge
local notation "Eis" => ActualEisensteinCubic.O

def goodMaskMovingIdeal (g r:Eis) : Ideal Eis := (Ideal.span {g})^6*Ideal.span {r}

lemma goodMaskMovingIdeal_supported (g r:Eis)
    (hg:Supported (Ideal.span {g})) (hr:Supported (Ideal.span {r})) :
    Supported (goodMaskMovingIdeal g r) := by
  exact (supported_mul_iff _ _).mpr ⟨supported_pow hg 6,hr⟩

lemma good_odd_prime_two_not_mem (P:Ideal Eis) [P.IsMaximal]
    (hodd:ringChar (Eis⧸P)≠2) : (2:Eis)∉P := by
  intro ht
  have he:=maximal_ideal_eq_span_of_mem P inferInstance (2:Eis) twoIdeal_maximal ht
  exact hodd (he ▸ twoIdeal_characteristic)

lemma count_span_eq_zero_of_not_mem (P:Ideal Eis) (x:Eis) (hx:x∉P) :
    (normalizedFactors (Ideal.span {x})).count P=0 := by
  apply Multiset.count_eq_zero.mpr
  intro hm
  have h0:(Ideal.span {x}:Ideal Eis)≠0:=by
    apply Ideal.span_singleton_eq_bot.not.mpr
    intro he
    exact hx (he ▸ P.zero_mem)
  exact hx (Ideal.dvd_span_singleton.mp
    ((UniqueFactorizationMonoid.mem_normalizedFactors_iff h0).mp hm).2)

lemma good_factor_count (P:Ideal Eis) [P.IsMaximal]
    (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    (normalizedFactors (Ideal.span {u.val*lambda^a*(2:Eis)^b*r})).count P=
      (normalizedFactors (Ideal.span {r})).count P := by
  have hl:(Ideal.span {lambda}:Ideal Eis)≠0:=
    Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  have ht:(Ideal.span {(2:Eis)}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hcl:=count_span_eq_zero_of_not_mem P lambda hgood
  have hct:=count_span_eq_zero_of_not_mem P 2 (good_odd_prime_two_not_mem P hodd)
  rw [show u.val*lambda^a*(2:Eis)^b*r=u.val*(lambda^a*(2:Eis)^b*r) by ring,
    Ideal.span_singleton_mul_left_unit u.isUnit,
    ←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
    ←Ideal.span_singleton_pow,←Ideal.span_singleton_pow,
    normalizedFactors_mul (mul_ne_zero (pow_ne_zero _ hl) (pow_ne_zero _ ht)) hr.1,
    normalizedFactors_mul (pow_ne_zero _ hl) (pow_ne_zero _ ht)]
  simp only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul,hcl,hct,mul_zero,zero_add]

theorem goodMaskMovingIdeal_count (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P=
      6*(normalizedFactors (Ideal.span {m})).count P+
        4*(normalizedFactors F).count P+(normalizedFactors I).count P := by
  have hmc:(normalizedFactors (Ideal.span {m})).count P=(normalizedFactors (Ideal.span {g})).count P:=by
    rw [hm]
    exact good_factor_count P hgood hodd um am bm g hg
  have hrc:(normalizedFactors (Ideal.span {r})).count P=
      4*(normalizedFactors F).count P+(normalizedFactors I).count P:=by
    have hh:=good_factor_count P hgood hodd u a b r hr
    rw [←hx,←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow,hf,hz,
      normalizedFactors_mul (pow_ne_zero 4 hF) hI] at hh
    simpa only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul] using hh.symm
  rw [goodMaskMovingIdeal,normalizedFactors_mul (pow_ne_zero 6 hg.1) hr.1]
  simp only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul,←hmc,hrc]
  omega

lemma squarefree_prime_count_indicator (F P:Ideal Eis) (hF:Squarefree F) (hP:Prime P) :
    (normalizedFactors F).count P=if P∣F then 1 else 0 := by
  have hle:=Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors hF.ne_zero).mp hF) P
  by_cases hPF:P∣F
  · rw [ite_eq_left hPF]
    have hp:=Multiset.count_pos.mpr
      ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hF.ne_zero).mpr ⟨hP,hPF⟩)
    omega
  · rw [ite_eq_right hPF]
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact hPF ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hF.ne_zero).mp hm).2

theorem goodMaskMovingIdeal_exponent (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P%6=completedLocalExponent I F P := by
  rw [goodMaskMovingIdeal_count I F hI hF.ne_zero m f z hf hz um am bm g hg hm u a b r hr hx P hgood hodd,
    squarefree_prime_count_indicator F P hF (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance)]
  unfold completedLocalExponent
  omega

theorem goodMaskMovingIdeal_generator_exponent (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m:Eis) (v:Eisˣ)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:(idealGenerator F)^4*(v.val*idealGenerator I)=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P%6=completedLocalExponent I F P := by
  exact goodMaskMovingIdeal_exponent I F hI hF m (idealGenerator F) (v.val*idealGenerator I)
    (span_idealGenerator F) (by rw [Ideal.span_singleton_mul_left_unit v.isUnit,span_idealGenerator])
    um am bm g hg hm u a b r hr hx P hgood hodd

end CanonicalRowCompletion

end

end OAI

end Source286

/- Original source: OAI/NumberTheory/DirichletL/RowCompletion/FixedCuspBranches.lean; sha256: b8aefff6f7ce990f97b7695b1f7f147ea53fb7de98846fd5f459cd18b44053cb -/
section Source287
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
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge
local notation "Eis" => ActualEisensteinCubic.O

lemma prime_dvd_iff_factor_count_pos (P A:Ideal Eis) (hP:Prime P) (hA:A≠0) :
    P∣A ↔ 0<(normalizedFactors A).count P := by
  simp only [Multiset.count_pos,UniqueFactorizationMonoid.mem_normalizedFactors_iff hA,hP,true_and]

theorem goodMaskMovingIdeal_dvd_iff (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    P∣goodMaskMovingIdeal g r ↔ P∣I*(Ideal.span {m}*F) := by
  have hP:Prime P:=Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  have hmI:(Ideal.span {m}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr hm0
  rw [prime_dvd_iff_factor_count_pos P _ hP (goodMaskMovingIdeal_supported g r hg hr).1,
    prime_dvd_iff_factor_count_pos P _ hP (mul_ne_zero hI (mul_ne_zero hmI hF)),
    goodMaskMovingIdeal_count I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P hgood hodd,
    normalizedFactors_mul hI (mul_ne_zero hmI hF),normalizedFactors_mul hmI hF]
  simp only [Multiset.count_add]
  omega

theorem goodMaskMovingIdeal_primeSupport (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    IdealMobiusDivisorSum.primeSupport (goodMaskMovingIdeal g r)=
      (IdealMobiusDivisorSum.primeSupport (I*(Ideal.span {m}*F))).filter
        (fun P=>lambda∉P ∧ ringChar (Eis⧸P)≠2) := by
  have hs:=goodMaskMovingIdeal_supported g r hg hr
  have hmI:(Ideal.span {m}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr hm0
  have hprod:=mul_ne_zero hI (mul_ne_zero hmI hF)
  ext P
  simp only [IdealMobiusDivisorSum.primeSupport,Finset.mem_filter,Multiset.mem_toFinset]
  constructor
  · intro hP
    obtain ⟨hmax,hgood,hodd⟩:=supported_factors_good _ hs P hP
    let:P.IsMaximal:=hmax
    have hp:Prime P:=prime_of_normalized_factor P hP
    have hd: P∣goodMaskMovingIdeal g r:=
      ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hs.1).mp hP).2
    exact ⟨(UniqueFactorizationMonoid.mem_normalizedFactors_iff hprod).mpr ⟨hp,
      (goodMaskMovingIdeal_dvd_iff I F hI hF m f z hm0 hf hz um am bm g hg hm
        u a b r hr hx P hgood hodd).mp hd⟩,hgood,hodd⟩
  · rintro ⟨hP,hgood,hodd⟩
    have hp:Prime P:=prime_of_normalized_factor P hP
    let:P.IsMaximal:=(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hd:=((UniqueFactorizationMonoid.mem_normalizedFactors_iff hprod).mp hP).2
    exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hs.1).mpr ⟨hp,
      (goodMaskMovingIdeal_dvd_iff I F hI hF m f z hm0 hf hz um am bm g hg hm
        u a b r hr hx P hgood hodd).mpr hd⟩

def goodMaskNonresidualPool (I F:Ideal Eis) (m g r:Eis) : Finset (Ideal Eis) :=
  (IdealMobiusDivisorSum.primeSupport (goodMaskMovingIdeal g r)).filter
    (fun P=>¬P∣rowResidualPart I (Ideal.span {m}*F))

theorem goodMaskNonresidualPool_eq (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    goodMaskNonresidualPool I F m g r=completedReflectionPool I (Ideal.span {m}*F) := by
  rw [goodMaskNonresidualPool,
    goodMaskMovingIdeal_primeSupport I F hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx]
  ext P
  simp only [Finset.mem_filter,completedReflectionPool]
  tauto

theorem goodMaskNonresidualPool_eq_on_fiber (I J F:Ideal Eis)
    (hI:I≠0) (hJ:J≠0) (hF:F≠0) (m f z w:Eis) (hm0:m≠0)
    (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I) (hw:Ideal.span {w}=J)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (u':Eisˣ) (a' b':ℕ) (r':Eis) (hr':Supported (Ideal.span {r'}))
    (hx':f^4*w=u'.val*lambda^a'*(2:Eis)^b'*r')
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I (Ideal.span {m}*F)=rowMaskPart J (Ideal.span {m}*F)) :
    goodMaskNonresidualPool I F m g r=goodMaskNonresidualPool J F m g r' := by
  rw [goodMaskNonresidualPool_eq I F hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx,
    goodMaskNonresidualPool_eq J F hJ hF m f w hm0 hf hw um am bm g hg hm u' a' b' r' hr' hx']
  exact completedReflectionPool_eq_on_fiber I J (Ideal.span {m}*F) hI hJ
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF) hA hT

theorem goodMaskNonresidualPool_free_eq (I F Q0:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    (goodMaskNonresidualPool I F m g r).filter (fun P=>¬Q0≤P)=
      (completedReflectionPool I (Ideal.span {m}*F)).filter (fun P=>¬Q0≤P) := by
  rw [goodMaskNonresidualPool_eq I F hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx]

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

theorem goodMaskMovingIdeal_principal_row (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) (n:Eis) :
    idealRowHom n (goodMaskMovingIdeal g r)=
      principalSexticRow (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val)
        (primeIndex_pairwise_coprime (goodMaskMovingIdeal g r))
        (fun P=>(supported_factors_good _ (goodMaskMovingIdeal_supported g r hg hr)
          P.val (Multiset.mem_toFinset.mp P.property)).2.1)
        (fun P=>completedLocalExponent I F P.val)
        (finitePrimeModulus (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val))
        (span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [idealRowHom_eq_principalSexticRow _ (goodMaskMovingIdeal_supported g r hg hr)]
  have he:(fun P:PrimeIndex (goodMaskMovingIdeal g r)=>(normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6)=
      (fun P=>completedLocalExponent I F P.val):=by
    funext P
    have hdata:=supported_factors_good _ (goodMaskMovingIdeal_supported g r hg hr)
      P.val (Multiset.mem_toFinset.mp P.property)
    exact goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm
      u a b r hr hx P.val hdata.2.1 hdata.2.2
  rw [he]

theorem rowTwist_eq_computed_principal_row
    (Ψ:Eis→*ℂ) (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hpr:lambda^2∣r-1) (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=(Ψ*numeratorBadTwist u a b r hr) n *
      principalSexticRow (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val)
        (primeIndex_pairwise_coprime (goodMaskMovingIdeal g r))
        (fun P=>(supported_factors_good _ (goodMaskMovingIdeal_supported g r hg hr)
          P.val (Multiset.mem_toFinset.mp P.property)).2.1)
        (fun P=>completedLocalExponent I F P.val)
        (finitePrimeModulus (fun P:PrimeIndex (goodMaskMovingIdeal g r)=>P.val))
        (span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [rowTwist_eq_fixed_times_good_row_primary Ψ m f z hmLam hm2 um am bm g hg hm
    u a b r hr hpr hx n hpn]
  change _*idealRowHom n (goodMaskMovingIdeal g r)=_
  rw [goodMaskMovingIdeal_principal_row I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx n]

theorem goodMaskMovingIdeal_exponent_eq_on_fiber
    (I J F:Ideal Eis) (hI:I≠0) (hJ:J≠0) (hF:Squarefree F)
    (m f z w:Eis) (hm0:m≠0)
    (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I) (hw:Ideal.span {w}=J)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (u':Eisˣ) (a' b':ℕ) (r':Eis) (hr':Supported (Ideal.span {r'}))
    (hx':f^4*w=u'.val*lambda^a'*(2:Eis)^b'*r')
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I (Ideal.span {m}*F)=rowMaskPart J (Ideal.span {m}*F))
    (P:completedReflectionPool I (Ideal.span {m}*F)) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6=
      (normalizedFactors (goodMaskMovingIdeal g r')).count P.val%6 := by
  let:P.val.IsMaximal:=completedReflectionPool_maximal I (Ideal.span {m}*F) P
  have hgood:=completedReflectionPool_good I (Ideal.span {m}*F) P
  have hodd:=completedReflectionPool_odd I (Ideal.span {m}*F) P
  rw [goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P.val hgood hodd,
    goodMaskMovingIdeal_exponent J F hJ hF m f w hf hw um am bm g hg hm u' a' b' r' hr' hx' P.val hgood hodd]
  exact completedReflectionPool_exponent_eq I J F (Ideal.span {m}*F) hI hJ
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hA hT P

end CanonicalRowCompletion

namespace CubicEisenstein

section
open scoped Classical BigOperators MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

lemma amplitude_source_nonzero (p:ThetaFullIndex)
    (hp:s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val≠0) :
    (sourceCuspCoefficients s.index).value (thetaFullFrequency p)≠0 := by
  intro hz
  apply hp
  have hz':(sourceCuspCoefficients s.index).value
      (fixedCuspArrayIndex p.1 p.2.1 p.2.2.1.val p.2.2.2.val)=0:=by
    simpa only [thetaFullFrequency_eq_fixedCuspArrayIndex] using hz
  simp only [amplitude,fixedConjugateCuspArray,fixedCuspArray,hz',zero_div,ite_self,
    star_zero,zero_mul]

lemma amplitude_integral_phase (p:ThetaFullIndex) (c d:Eis) (hc:c≠0) :
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      ShortDraftTrace.breveE (cuspFrequency (thetaFullFrequency p)*eisEmbedding (s.upper 0 0)^2*
        (eisEmbedding d/eisEmbedding c)/(sourceCuspScale s.index:ℂ)) =
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      ShortDraftTrace.breveE (-(eisEmbedding d*
        (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
          eisEmbedding c) := by
  by_cases hp:s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val=0
  · rw [hp,zero_mul,zero_mul]
  · rw [sourceCuspPhaseNumerator_phase s.index (s.upper 0 0) (thetaFullFrequency p) c d hc
      (s.amplitude_source_nonzero p hp)]

lemma datum_integral_phase (g:levelTwo) (c:Eis) (hc:c≠0)
    (hg:((g:SL(2,Eis))*H) 1 0=c) (p:ThetaFullIndex) :
    (fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      sourceFrequencyAngle (thetaFullFrequency p))*
      ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
        ((s.datum g (by rwa [hg])).dualPoint/(sourceCuspScale s.index:ℂ))) =
    s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
      ShortDraftTrace.breveE (-(eisEmbedding (((g:SL(2,Eis))*H) 1 1)*
        (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
          eisEmbedding c) := by
  have hphase:=s.datum_additive_phase g (by rwa [hg])
    (cuspFrequency (thetaFullFrequency p)) (sourceCuspScale s.index:ℂ)
  simp only [hg] at hphase
  calc
    _=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
        ShortDraftTrace.breveE (cuspFrequency (thetaFullFrequency p)*eisEmbedding (s.upper 0 0)^2*
          (eisEmbedding (((g:SL(2,Eis))*H) 1 1)/eisEmbedding c)/(sourceCuspScale s.index:ℂ)) := by
      rw [show -cuspFrequency (thetaFullFrequency p)*
          ((s.datum g (by rwa [hg])).dualPoint/(sourceCuspScale s.index:ℂ))=
        -cuspFrequency (thetaFullFrequency p)*(s.datum g (by rwa [hg])).dualPoint/
          (sourceCuspScale s.index:ℂ) by ring,hphase]
      unfold amplitude
      rw [←thetaFullFrequency_eq_fixedCuspArrayIndex]
      ring
    _=_:=s.amplitude_integral_phase p c _ hc

def stratumShapeFactor (c:Eis) : ℂ :=
  -star (levelTwoComplexCharacter s.gamma)*eisEmbedding (s.upper 0 0)^2*
    ((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ)/eisEmbedding c^2

lemma datum_common_row_factor (g:levelTwo) (c:Eis) (hc:c≠0)
    (hg:((g:SL(2,Eis))*H) 1 0=c) :
    (s.datum g (by rwa [hg])).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ)=
      s.stratumShapeFactor c*star (levelTwoComplexCharacter g) := by
  have hm:=s.smoothed_row_factor g (by rwa [hg])
  simp only [s.datum_heightScale,hg,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at hm
  rw [hm]
  unfold stratumShapeFactor
  ring

end FixedCuspShape
end

open scoped Classical BigOperators ContDiff MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

theorem sum_smoothedKernel_integral_phase {ι:Type*} [Fintype ι]
    (g:ι→levelTwo) (c:Eis) (hc:c≠0) (hC:∀v,((g v:SL(2,Eis))*H) 1 0=c)
    (w:ι→ℂ) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑v,w v*(s.datum (g v) (by rw [hC v];exact hc)).smoothedKernel W X)=
      fixedRadialCoefficientScalar*s.stratumShapeFactor c*
      ∑'p:ThetaFullIndex,
        (s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val /
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)*
        (∑v,w v*star (levelTwoComplexCharacter (g v))*
          ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
            (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/
              eisEmbedding c)) := by
  let d:ι→SourceCuspDatum:=fun v=>s.datum (g v) (by rw [hC v];exact hc)
  have hindex:∀v,(d v).index=s.index:=fun _=>rfl
  have hheight:∀v,(d v).heightScale=(Ideal.absNorm (Ideal.span {c}):ℝ):=by
    intro v
    dsimp only [d]
    rw [s.datum_heightScale,hC v,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  have he:=sum_smoothedKernel_common_cusp d w s.index (Ideal.absNorm (Ideal.span {c}):ℝ)
    hindex hheight W a b ha hsupp hW X hX
  rw [he]
  conv_rhs => rw [mul_assoc]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*z)
  rw [←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [sourceCusp_full_index_kernel_argument p s.index (Ideal.absNorm (Ideal.span {c}):ℝ) X]
  let A:ℂ:=fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
    sourceFrequencyAngle (thetaFullFrequency p)
  let B:ℂ:=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val
  let lengthScale:ι→ℂ:=fun v=>w v*((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
    ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*((d v).dualPoint/(sourceCuspScale s.index:ℂ)))
  let R:ι→ℂ:=fun v=>w v*star (levelTwoComplexCharacter (g v))*
    ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
      (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/eisEmbedding c)
  have hs:A*(∑v,lengthScale v)=s.stratumShapeFactor c*B*(∑v,R v):=by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [lengthScale,R]
    calc
      _=w v*(((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
          (A*ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
            ((d v).dualPoint/(sourceCuspScale s.index:ℂ))))):=by ring
      _=w v*((s.stratumShapeFactor c*star (levelTwoComplexCharacter (g v)))*
          (B*ShortDraftTrace.breveE (-(eisEmbedding (((g v:SL(2,Eis))*H) 1 1)*
            (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/eisLam^4))/eisEmbedding c))):=by
        rw [s.datum_common_row_factor (g v) c hc (hC v),s.datum_integral_phase (g v) c hc (hC v) p]
      _=_:=by ring
  let D:ℂ:=((ramifiedScale 1 completedRamifiedStep p.2.1*
    Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ)
  let K:ℂ:=CubicReflectionKernel.paperKernel (Vstar W)
    ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
      (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)
  change A/D*K*(∑v,lengthScale v)=s.stratumShapeFactor c*(B/D*K*(∑v,R v))
  calc
    _=(A*(∑v,lengthScale v))/D*K:=by ring
    _=(s.stratumShapeFactor c*B*(∑v,R v))/D*K:=by rw [hs]
    _=_:=by ring

lemma stratumShapeFactor_norm (c:Eis) (hc:c≠0) : ‖s.stratumShapeFactor c‖=1 := by
  have hu:‖eisEmbedding (s.upper 0 0)‖=1:=by
    rcases s.upper_unit with ⟨u,hu⟩
    rw [←hu]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit u
  have hn:‖eisEmbedding c‖^2≠0:=pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc))
  rw [stratumShapeFactor,norm_div,norm_mul,norm_mul,norm_neg,norm_star,
    norm_levelTwoComplexCharacter,norm_pow,hu,one_pow,one_mul,one_mul,norm_pow,
    Complex.norm_real,Real.norm_of_nonneg (Nat.cast_nonneg _),
    ←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  exact div_self hn

end FixedCuspShape
end CubicEisenstein

open scoped BigOperators Classical ContDiff

namespace CompletedGauss

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def fixedCuspArrayWithPhase (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) : ℂ :=
  phaseArray m n b*fixedConjugateCuspArray cusp u m n b

lemma fixedCuspArrayWithPhase_norm_le_one (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (m:ℕ) (n b:Ideal Eis) : ‖fixedCuspArrayWithPhase cusp u phaseArray m n b‖≤1 := by
  rw [fixedCuspArrayWithPhase,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (hphase m n b)).trans (fixedConjugateCuspArray_norm_le_one cusp u m n b)

lemma fixedCuspArrayWithPhase_zero (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis)
    (h:¬fixedCuspArrayEligible n b) : fixedCuspArrayWithPhase cusp u phaseArray m n b=0 := by
  simp only [fixedCuspArrayWithPhase,fixedConjugateCuspArray,
    fixedCuspArray_zero_of_ineligible _ _ _ _ _ h,star_zero,mul_zero]

namespace ReflectedBranchData

def extractedFixedCuspArrayWithPhase {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase cusp u phaseArray m
    (reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1*n)
    (reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2*b)

lemma extractedFixedCuspArrayWithPhase_norm_le_one {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (m:ℕ) (n b:Ideal Eis) : ‖d.extractedFixedCuspArrayWithPhase cusp u phaseArray m n b‖≤1 :=
  fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase m _ _

lemma extractedFixedCuspArrayWithPhase_eq {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) :
    d.extractedFixedCuspArrayWithPhase cusp u phaseArray m n b=
      phaseArray m
        (reflectionExtractedDivisor (fun p:d.primes=>p.val)
          (fun p=>completedLocalExponent I F p.val) d.label 1*n)
        (reflectionExtractedDivisor (fun p:d.primes=>p.val)
          (fun p=>completedLocalExponent I F p.val) d.label 2*b)*
      d.extractedFixedCuspArray cusp u m n b := rfl

lemma extractedFixedCuspArrayWithPhase_zero {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis)
    (h:¬fixedCuspArrayEligible
      (reflectionExtractedDivisor (fun p:d.primes=>p.val)
        (fun p=>completedLocalExponent I F p.val) d.label 1*n)
      (reflectionExtractedDivisor (fun p:d.primes=>p.val)
        (fun p=>completedLocalExponent I F p.val) d.label 2*b)) :
    d.extractedFixedCuspArrayWithPhase cusp u phaseArray m n b=0 :=
  fixedCuspArrayWithPhase_zero cusp u phaseArray m _ _ h

def withExtractedFixedCuspArrayWithPhase {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) : ReflectedBranchData levelBound K I F Q :=
  d.withCanonicalCuspArray (d.extractedFixedCuspArrayWithPhase cusp u phaseArray)
    (fun m n b=>d.extractedFixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase m n.val b.val)
    rowPhase hrow

lemma withExtractedFixedCuspArrayWithPhase_amplitude {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1) (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    (d.withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow).amplitude i n b=
      d.extractedFixedCuspArrayWithPhase cusp u phaseArray i.1 n b := rfl

theorem withExtractedFixedCuspArrayWithPhase_value {levelBound K:ℝ} {I F Q:Ideal Eis}
    (d:ReflectedBranchData levelBound K I F Q) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hsupp:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    (d.withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow).value W X ρ q k=
      d.rawValue (d.extractedFixedCuspArrayWithPhase cusp u phaseArray) rowPhase W X ρ q k :=
  d.withCanonicalCuspArray_value (d.extractedFixedCuspArrayWithPhase cusp u phaseArray)
    (fun m n b=>d.extractedFixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase m n.val b.val)
    rowPhase hrow W a b ha hsupp hW X ρ q hX hρ hq hK k hk

end ReflectedBranchData
end
section

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def sixPhaseFixedCuspBranch (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q :=
  (sixReflectedBranch I F Q hI hQ K levelBound levelScale hlevel hbound e
    (fixedCuspArrayWithPhase cusp u phaseArray)
    (fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase) rowPhase hrow).withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow

lemma sixPhaseFixedCuspBranch_primes (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    (sixPhaseFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow).primes=reflectionActivePool I Q e := rfl

lemma sixPhaseFixedCuspBranch_amplitude (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    let d:=sixPhaseFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    let D:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1
    let E:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2
    d.amplitude i n b=phaseArray i.1 (D*n) (E*b)*fixedConjugateCuspArray cusp u i.1 (D*n) (E*b) := rfl

lemma sixPhaseFixedCuspBranch_scale (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K X levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    let d:=sixPhaseFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    completedBranchScale K (X/d.levelScale) I F Q (fun P:d.primes=>P.val) d.label=
      completedBranchScale K (X/levelScale) I F Q
        (fun P:reflectionActivePool I Q e=>P.val) (reflectionActiveLabel I Q e) := rfl

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def sixPhaseFixedCuspFiber (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) : ReflectedFiberData rays levelBound K I F Q where
  pool:=completedReflectionPool I Q
  maximal:=completedReflectionPool_maximal I Q
  divides:=completedReflectionPool_divides I Q hI hQ
  branch:=fun x=>sixPhaseFixedCuspBranch I F Q hI hQ K levelBound (levelScale x) (hlevel x) (hlevelBound x)
    x.2 (cusp x) (unit x) (phaseArray x) (hphase x) (rowPhase x) (hrow x)
  weight:=fun x=>rayWeight x*reflectionSixInactiveWeight I F Q x.2
  weight_bound:=by
    intro x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hray x)).trans (reflectionSixInactiveWeight_norm_le_one I F Q x.2)

theorem sixPhaseFixedCuspFiber_value (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=sixPhaseFixedCuspFiber rays I F Q hI hQ K levelBound levelScale hlevel hlevelBound
      cusp unit phaseArray hphase rayWeight hray rowPhase hrow
    d.value W X ρ q k=
      ∑t:Fin rays,∑A:Finset (completedReflectionPool I Q),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q A*rayWeight (t,encodeReflectionSix ⟨A,e⟩)*
          (d.branch (t,encodeReflectionSix ⟨A,e⟩)).value W X ρ q k := by
  dsimp only
  rw [ReflectedFiberData.value,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _=∑e:completedReflectionPool I Q→Fin 6,reflectionSixInactiveWeight I F Q e*
      (rayWeight (t,e)*(sixPhaseFixedCuspBranch I F Q hI hQ K levelBound (levelScale (t,e))
        (hlevel (t,e)) (hlevelBound (t,e)) e (cusp (t,e)) (unit (t,e))
        (phaseArray (t,e)) (hphase (t,e)) (rowPhase (t,e)) (hrow (t,e))).value W X ρ q k) := by
          apply Finset.sum_congr rfl
          intro e _
          dsimp only [sixPhaseFixedCuspFiber]
          ring
    _=_ := by
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [sixPhaseFixedCuspFiber]
      exact (mul_assoc _ _ _).symm

end CompletedGauss

end

end OAI

end Source287

/- Original source: OAI/NumberTheory/DirichletL/Cusp/StaticReflectionPhases.lean; sha256: 0cf6e362b173a959bf7e5f2e980e29149e29ce36032fdf92f317d91135850161 -/
section Source288
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

section
open scoped BigOperators Classical MatrixGroups

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A4PhaseFromResidue_norm (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}) (x:Eis) :
    ‖A4PhaseFromResidue c0 hc0 v x‖=1 := by
  let:Finite (Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}):=
    finite_quotient_span (A4_bad_modulus_ne_zero c0 hc0)
  unfold A4PhaseFromResidue
  exact AddChar.norm_apply _ _
end ShortDraftCusp

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss ShortDraftCusp ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceFrequencyAngle_norm_le_one (h:Eis) : ‖sourceFrequencyAngle h‖≤1 := by
  by_cases hh:h=0
  · simp only [hh,sourceFrequencyAngle,map_zero,norm_zero,Complex.ofReal_zero,div_zero]
    norm_num
  · exact (sourceFrequencyAngle_norm h hh).le

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

def reflectionStaticPhase (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) : ℂ :=
  sourceFrequencyAngle (fixedCuspArrayIndex u m I J)*
    ShortDraftTrace.breveE (-cuspFrequency (fixedCuspArrayIndex u m I J)*
      eisEmbedding (s.upper 0 0*s.upper 0 1)/(sourceCuspScale s.index:ℂ))*
    A4PhaseFromResidue c0 hc0 v (dualNumerator m I J)

lemma reflectionStaticPhase_norm_le_one (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) : ‖s.reflectionStaticPhase c0 hc0 v dualNumerator u m I J‖≤1 := by
  simp only [reflectionStaticPhase,norm_mul,breveE_norm,A4PhaseFromResidue_norm,mul_one]
  exact sourceFrequencyAngle_norm_le_one _

lemma fixedCuspArrayWithPhase_reflectionStaticPhase (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) :
    fixedCuspArrayWithPhase s.index u (s.reflectionStaticPhase c0 hc0 v dualNumerator u) m I J=
      s.amplitude u m I J*A4PhaseFromResidue c0 hc0 v (dualNumerator m I J) := by
  unfold fixedCuspArrayWithPhase reflectionStaticPhase amplitude
  ring

end FixedCuspShape
end CubicEisenstein
end

open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalCoefficientClass
local notation "Eis" => ActualEisensteinCubic.O

def reflectionConductor (q:ℕ) : Eis := (2592*q:ℕ)

def reflectionExcludedPrimes (q:ℕ) : Finset (Ideal Eis) :=
  gcdMaskPrimes (Ideal.span {reflectionConductor q})

lemma reflectionConductor_ne_zero (q:ℕ) (hq:q≠0) : reflectionConductor q≠0 := by
  unfold reflectionConductor
  exact_mod_cast Nat.mul_ne_zero (by decide : 2592≠0) hq

lemma reflectionConductor_ideal (q:ℕ) :
    Ideal.span {reflectionConductor q}=
      Ideal.span {(9:Eis)}*(fixedBaseConductor q*Ideal.span {(72:Eis)}) := by
  rw [fixedBaseConductor_principal,Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_mul_span_singleton]
  congr 1
  unfold reflectionConductor
  push_cast
  ring_nf

lemma reflectionExcludedPrimes_bad (q:ℕ) :
    fixedBadPrimes⊆reflectionExcludedPrimes q := Finset.subset_union_left

lemma reflectionExcludedPrimes_prime (q:ℕ) (P:Ideal Eis)
    (hP:P∈reflectionExcludedPrimes q) : Prime P := by
  let:P.IsMaximal:=gcdMaskPrimes_maximal _ ⟨P,hP⟩
  exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance

lemma reflectionConductor_prime_mem (q:ℕ) (hq:q≠0) (P:Ideal Eis)
    (hP:Prime P) (hd:P∣Ideal.span {reflectionConductor q}) :
    P∈reflectionExcludedPrimes q := by
  apply Finset.mem_union_right
  apply Multiset.mem_toFinset.mpr
  apply (Ideal.mem_normalizedFactors_iff (Ideal.span_singleton_eq_bot.not.mpr
    (reflectionConductor_ne_zero q hq))).mpr
  exact ⟨Ideal.isPrime_of_prime hP,Ideal.dvd_iff_le.mp hd⟩

lemma reflectionExcludedGenerator_ne_zero (q:ℕ) :
    excludedGenerator (reflectionExcludedPrimes q)≠0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  exact Finset.prod_ne_zero_iff.mpr (fun P hP=>(reflectionExcludedPrimes_prime q P hP).ne_zero)

lemma reflectionExcludedGenerator_bad (q:ℕ) :
    lambda∣excludedGenerator (reflectionExcludedPrimes q) ∧
      (2:Eis)∣excludedGenerator (reflectionExcludedPrimes q) := by
  constructor
  · apply Ideal.mem_span_singleton.mp
    exact excludedGenerator_mem _ (reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes]))
  · apply Ideal.mem_span_singleton.mp
    exact excludedGenerator_mem _ (reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes]))

lemma reflectionConductor_coprime_of_not_excluded (q:ℕ) (hq:q≠0)
    (P:Ideal Eis) [P.IsMaximal] (hP:P∉reflectionExcludedPrimes q) :
    IsCoprime (Ideal.span {reflectionConductor q}) P := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra ht
  have he:P=Ideal.span {reflectionConductor q}⊔P:=
    (show P.IsMaximal from inferInstance).eq_of_le ht le_sup_right
  exact hP (reflectionConductor_prime_mem q hq P
    (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance)
    (Ideal.dvd_iff_le.mpr (le_sup_left.trans he.symm.le)))

lemma reflectionConductor_coprime_primary (q:ℕ) (hq:q≠0)
    (p:Eis) [(Ideal.span {p}).IsMaximal]
    (hp:Ideal.span {p}∉reflectionExcludedPrimes q) :
    IsCoprime (reflectionConductor q) p :=
  (Ideal.isCoprime_span_singleton_iff _ _).mp
    (reflectionConductor_coprime_of_not_excluded q hq _ hp)

lemma reflectionLevelBound_ge_one (q:ℕ) (hq:q≠0) :
    1≤CubicEisenstein.fixedCuspLevelBound (reflectionConductor q) :=
  CubicEisenstein.fixedCuspLevelBound_ge_one _ (reflectionConductor_ne_zero q hq)

end CanonicalRowCompletion

open scoped BigOperators Classical

namespace CompletedGauss
open ActualEisensteinCubic UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma prime_dvd_rowResidualPart_iff (I Q P:Ideal Eis) (hP:Prime P) :
    P∣rowResidualPart I Q ↔ P∈normalizedFactors (rowSimplePart I) ∧ ¬P∣Q := by
  have hm:=UniqueFactorizationMonoid.mem_normalizedFactors_iff
    (squarefreeResidualPart_ne_zero (rowSimplePart I) Q) (p:=P)
  simp only [hP,true_and] at hm
  change P∣squarefreeResidualPart (rowSimplePart I) Q ↔ _
  rw [←hm]
  simp only [normalizedFactors_squarefreeResidualPart,Multiset.mem_filter]

lemma rowResidualPart_prime_fixed_mask (I Q Q0 P:Ideal Eis)
    (hP:Prime P) (hfree:¬Q0≤P) :
    P∣rowResidualPart I (Q0*Q) ↔ P∣rowResidualPart I Q := by
  have hnd:¬P∣Q0:=by simpa only [Ideal.dvd_iff_le] using hfree
  rw [prime_dvd_rowResidualPart_iff I (Q0*Q) P hP,
    prime_dvd_rowResidualPart_iff I Q P hP,hP.dvd_mul]
  simp only [hnd,false_or]

theorem completedReflectionPool_fixed_mask_filter (I Q Q0:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hQ0:Q0≠0) :
    (completedReflectionPool I (Q0*Q)).filter (fun P=>¬Q0≤P)=
      (completedReflectionPool I Q).filter (fun P=>¬Q0≤P) := by
  ext P
  simp only [Finset.mem_filter,mem_completedReflectionPool I (Q0*Q) P hI (mul_ne_zero hQ0 hQ),
    mem_completedReflectionPool I Q P hI hQ]
  by_cases hP:Prime P
  · by_cases hfree:¬Q0≤P
    · have hnd:¬P∣Q0:=by simpa only [Ideal.dvd_iff_le] using hfree
      have hdiv:P∣I*(Q0*Q) ↔ P∣I*Q:=by
        rw [hP.dvd_mul,hP.dvd_mul,hP.dvd_mul]
        simp only [hnd,false_or]
      rw [hdiv,rowResidualPart_prime_fixed_mask I Q Q0 P hP hfree]
    · simp only [hfree,and_false]
  · simp only [hP,false_and]

end CompletedGauss

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

theorem goodMaskNonresidualPool_full_mask (I F Q0:Ideal Eis)
    (hI:I≠0) (hF:F≠0) (hQ0:Q0≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    (goodMaskNonresidualPool I F m g r).filter (fun P=>¬Q0≤P)=
      (completedReflectionPool I (Q0*(Ideal.span {m}*F))).filter (fun P=>¬Q0≤P) := by
  rw [completedReflectionPool_fixed_mask_filter I (Ideal.span {m}*F) Q0 hI
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF) hQ0]
  exact goodMaskNonresidualPool_free_eq I F Q0 hI hF m f z hm0 hf hz
    um am bm g hg hm u a b r hr hx

end CanonicalRowCompletion

open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp

section
open ActualEisensteinCubic CubicEisenstein CubicKubota CubicJacobiGlobal ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem A3_ramified_character_of_relative_level (M:SL(2,Eis)) (u q r:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree)
    (ha:lambda^2∣M 0 0-1) (hr:lambda^2∣r-1) (hC:M 1 0=(u*q)*r) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩=
      eisEmbedding (symbol (-u) (M 0 0-u*M 0 1)*symbol q (M 0 0))*
        eisEmbedding (symbol (M 0 0) r) := by
  have hA:=levelThree_primary ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩
  change lambda^2∣(((M*(lowerCuspMatrix u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hA
  rw [A3_ramified_relative_matrix] at hA
  have hdet:M 0 0*M 1 1-M 0 1*(u*(q*r))=1 := by
    have hd:=M.property
    simp only [Matrix.det_fin_two,hC] at hd
    linear_combination hd
  rw [A3_ramified_literal_character,hC,show (u*q)*r=u*(q*r) by ring,
    A3_ramified_global_factor _ _ _ _ _ _ hdet ha hA hr,map_mul]

theorem A3_unramified_character_of_relative_level (M:SL(2,Eis)) (u c0 r:Eis)
    (hG:M*(A3WeylCusp u)⁻¹∈levelThree)
    (hc:lambda^2∣M 1 0-1) (h9:(9:Eis)∣M 0 0*M 1 1) (hC:M 1 0=c0*r) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,hG⟩=
      eisEmbedding (symbol (M 0 0) c0)*eisEmbedding (symbol (M 0 0) r) := by
  have hb:=levelThree_primary ⟨M*(A3WeylCusp u)⁻¹,hG⟩
  change lambda^2∣(((M*(A3WeylCusp u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hb
  rw [A3_unramified_relative_matrix] at hb
  have hdet:M 0 0*M 1 1-M 0 1*(c0*r)=1 := by
    simpa only [Matrix.det_fin_two,hC] using M.property
  rw [hC] at hc
  rw [A3_unramified_literal_character,A3_unramified_global_factor _ _ _ _ _ hdet hb hc h9,map_mul]

end

section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss CubicKubota CubicJacobiGlobal LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance stratumMultiplierField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance stratumMultiplierFintype (P:Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem stratum_multiplier_of_cubic_factor {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (c0 U w x d0:Eis) (hc0:c0≠0)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (a b d:(∀i,(Eis⧸Ideal.span {p i})ˣ)→Eis)
    (κ:(∀i,(Eis⧸Ideal.span {p i})ˣ)→ℂ) (κ0:ℂ)
    (hκ:∀v,κ v=κ0*eisEmbedding (symbol (a v) (∏i,p i)))
    (hdet:∀v,a v*d v-b v*(c0*∏i,p i)=1)
    (hD:∀v,ramifiedTraceLambda^3*c0∣d v-d0)
    (σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ)
    (hfreq:∀v i,Ideal.Quotient.mk (Ideal.span {p i}) (a v)=
      (σ i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}))
    (hε:∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (j:ι→ℕ) (hj:∀i,j i<6) :
    (∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
        (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i))*
      star (κ v)*ShortDraftTrace.breveE (-(eisEmbedding (d v)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))) =
    (star κ0*A4BadPhase c0 hc0 d0 U x)*
    ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (σ i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (ε i)*
      bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x) := by
  let C:=star κ0*A4BadPhase c0 hc0 d0 U x
  let f:=fun i (v:(Eis⧸Ideal.span {p i})ˣ)=>frequencyRow
    (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i)
    (σ i) (ε i) (Ideal.Quotient.mk _ x) v
  have hpoint (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
      star (κ v)*ShortDraftTrace.breveE (-(eisEmbedding (d v)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))=
      C*∏i,frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (σ i) (ε i) (Ideal.Quotient.mk _ x) (v i) := by
    have hbad:A4BadPhase c0 hc0 (d v) U x=A4BadPhase c0 hc0 d0 U x := by
      apply A4BadPhase_eq_of_residue
      convert dvd_mul_of_dvd_left (hD v) U using 1 ; ring
    have hlocal:=A3_A4_frequency_product p hp hcop hg (a v) (b v) c0 (d v)
      U w x hc0 (hdet v) hbez σ ε (fun i=>(v i:Eis⧸Ideal.span {p i})) (hfreq v) hε
    rw [hκ,star_mul]
    calc
      _=star κ0*(star (eisEmbedding (symbol (a v) (∏i,p i)))*
        ShortDraftTrace.breveE (-(eisEmbedding (d v)*(eisEmbedding x/eisLam^4))/
          (eisEmbedding c0*eisEmbedding (∏i,p i)))) := by ring
      _=_ := by rw [hlocal,hbad];dsimp only [C];ring
  calc
    _=C*∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,∏i,f i (v i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [mul_assoc,hpoint]
      simp only [f,frequencyRow,Finset.prod_mul_distrib]
      ring
    _=C*∏i,∑v:(Eis⧸Ideal.span {p i})ˣ,f i v := by rw [Fintype.prod_sum]
    _=_ := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact canonical_frequencyRow_units (Ideal.span {p i}) (hg i) (hchar i)
        (quotientTrace (p i) (hp i))
        (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) (j i) (hj i) (σ i) (ε i) _

end

open ActualEisensteinCubic CubicEisenstein CubicKubota CubicJacobiGlobal ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A3_ramified_relative_primary (M:SL(2,Eis)) (u:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree) :
    lambda^2∣(M 0 0-u*M 0 1)-1 := by
  have hA:=levelThree_primary ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩
  change lambda^2∣(((M*(lowerCuspMatrix u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hA
  rw [A3_ramified_relative_matrix] at hA
  exact hA

theorem A3_ramified_fixed_sector_character (M M0:SL(2,Eis)) (N u q r:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree)
    (hG0:M0*(lowerCuspMatrix u)⁻¹∈levelThree)
    (ha:lambda^2∣M 0 0-1) (ha0:lambda^2∣M0 0 0-1)
    (hr:lambda^2∣r-1) (hC:M 1 0=(u*q)*r)
    (h9N:(9:Eis)∣N) (hqN:q∣N) (huN:u∣N)
    (hA:N∣M 0 0-M0 0 0) (hB:N∣M 0 1-M0 0 1) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩=
      eisEmbedding (symbol (-u) (M0 0 0-u*M0 0 1)*symbol q (M0 0 0))*
        eisEmbedding (symbol (M 0 0) r) := by
  rw [A3_ramified_character_of_relative_level M u q r hG ha hr hC]
  rw [A3_ramified_fixed_factor_congr N q u (M 0 0) (M0 0 0) (M 0 1) (M0 0 1)
    h9N hqN huN ha ha0 (A3_ramified_relative_primary M u hG)
    (A3_ramified_relative_primary M0 u hG0) hA hB]

theorem A3_unramified_fixed_sector_character (M M0:SL(2,Eis)) (u c0 r:Eis)
    (hG:M*(A3WeylCusp u)⁻¹∈levelThree)
    (hc:lambda^2∣M 1 0-1) (h9:(9:Eis)∣M 0 0*M 1 1) (hC:M 1 0=c0*r)
    (hA:c0∣M 0 0-M0 0 0) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,hG⟩=
      eisEmbedding (symbol (M0 0 0) c0)*eisEmbedding (symbol (M 0 0) r) := by
  rw [A3_unramified_character_of_relative_level M u c0 r hG hc h9 hC,
    symbol_congr hA]

end ShortDraftCusp

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

structure ControlledStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) (N a0 c0:Eis) (numeratorMode:Bool) where
  lift : (∀i,(Eis⧸Ideal.span {p i})ˣ)→ι→Eis
  lift_period : ∀v i,N^2∣lift v i
  lift_residue : ∀v i,Ideal.Quotient.mk (Ideal.span {p i}) (lift v i)=(v i:Eis⧸Ideal.span {p i})
  U : Eis
  w : Eis
  bezout : U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1
  sigma : ∀i,(Eis⧸Ideal.span {p i})ˣ
  epsilon : ∀i,(Eis⧸Ideal.span {p i})ˣ
  sigma_value : ∀i,(sigma i:Eis⧸Ideal.span {p i})=
    Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i)
  epsilon_value : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
    (sigma i:Eis⧸Ideal.span {p i})*(epsilon i:Eis⧸Ideal.span {p i})=-1
  matrix : (∀i,(Eis⧸Ideal.span {p i})ˣ)→SL(2,Eis)
  numerator : ∀v,matrix v 0 0=finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  denominator : ∀v,matrix v 1 0=c0*∏i,p i
  matrix_fixed : ∀v i j,N∣matrix v i j-matrix (fun _=>1) i j
  conditions : ∀v,if numeratorMode then
    (9:Eis)∣matrix v 0 1 ∧ (3:Eis)∣matrix v 1 1-1
    else (3:Eis)∣matrix v 0 1+1 ∧ (9:Eis)∣matrix v 1 1

theorem exists_controlledStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (N a0 c0:Eis) (hc0:c0≠0) (hN:(9:Eis)*c0∣N)
    (mode:Bool) (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hac:IsCoprime a0 c0) (hNp:∀i,IsCoprime N (p i)) :
    Nonempty (ControlledStratumArithmetic p N a0 c0 mode) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have hcN:c0∣N:=(dvd_mul_left c0 9).trans hN
  have hD9:ramifiedTraceLambda^3*c0∣(9:Eis)*c0 := by
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [←A4_traceLambda_pow_four]
    ring
  have hDN:ramifiedTraceLambda^3*c0∣N:=hD9.trans hN
  have hl9:ramifiedTraceLambda∣(9:Eis) := by
    rw [←A4_traceLambda_pow_four]
    exact dvd_pow_self _ (by decide)
  have hlN:ramifiedTraceLambda∣N:=hl9.trans h9N
  have hstdN:lambda^2∣N:=lambda_sq_dvd_three.trans
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N)
  let r:Eis:=∏i,p i
  have hr:lambda^2∣r-1:=primary_finset_product Finset.univ p (fun i _=>hprimary i)
  have hNr:IsCoprime N r:=IsCoprime.prod_right (fun i _=>hNp i)
  have hrNc:IsCoprime r (N*c0):=hNr.symm.mul_right
    (hNr.symm.of_isCoprime_of_dvd_right hcN)
  obtain ⟨U,w,huw⟩:=hNr.symm.of_isCoprime_of_dvd_right hDN
  have hbez:U*r+(ramifiedTraceLambda^3*w)*c0=1 := by linear_combination huw
  obtain ⟨σ,ε,hσ,hε⟩:=exists_A4_local_units p hp hcop c0 U w hbez
  have hlf (v:∀i,(Eis⧸Ideal.span {p i})ˣ):=exists_strong_unit_frequency_lifts N p hNp v
  choose lift hlift hres hlcop using hlf
  let a:=fun v=>finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  have hap (ha0:lambda^2∣a0-1):∀v,lambda^2∣a v-1 := by
    intro v
    have hfixed:N∣a v-a0*r:=finiteCrossNumerator_fixed N a0 c0 ramifiedTraceLambda p (lift v)
      (fun i=>(dvd_pow_self N (by decide : (2:ℕ)≠0)).trans (hlift v i))
    have hbas:=primary_mul a0 r ha0 hr
    convert dvd_add (hstdN.trans hfixed) hbas using 1 ; ring
  have hpairs:Pairwise (Function.onFun IsCoprime p):=by
    intro i k hik
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hik)
  have hacop:∀v,IsCoprime (a v) (c0*r) := by
    intro v
    exact finiteCrossNumerator_coprime a0 c0 ramifiedTraceLambda p (lift v) hac hpairs
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hcN)
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hlN) (hlcop v)
  have hfixed:∀v z,(fun (_:∀i,(Eis⧸Ideal.span {p i})ˣ)=>()) v=()→N*c0∣a v-a z := by
    intro v z _
    exact finiteCrossNumerator_fixed_sector N a0 c0 ramifiedTraceLambda p (lift v)
      p (lift z) hcN (hlift v) (hlift z) (by simp)
  have hcompletes:∃(b d:(∀i,(Eis⧸Ideal.span {p i})ˣ)→Eis)
      (C:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {N})),
      (∀v,a v*d v-b v*(c0*r)=1) ∧
      (∀v,if mode then (9:Eis)∣b v ∧ (3:Eis)∣d v-1 else (3:Eis)∣b v+1 ∧ (9:Eis)∣d v) ∧
      ∀v,(!![a v,b v;c0*r,d v]:Matrix (Fin 2) (Fin 2) Eis).map (Ideal.Quotient.mk (Ideal.span {N}))=C := by
    cases mode
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩:=exists_primary_denominator_sector_completions N c0 h9N hbase
        (fun (_:∀i,(Eis⧸Ideal.span {p i})ˣ)=>()) a (fun _=>r)
        (fun _=>hr) hacop (fun _=>hrNc) (fun v z _=>hfixed v z rfl) (fun _ _ _=>by simp)
      exact ⟨b,d,C (),hd,fun v=>⟨hb v,hz v⟩,hm⟩
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩:=exists_primary_numerator_sector_completions N c0 hc0 h9N
        (fun (_:∀i,(Eis⧸Ideal.span {p i})ˣ)=>()) a (fun _=>r)
        (hap hbase) (fun _=>hr) hacop (fun _=>hrNc)
        (fun v z _=>hfixed v z rfl) (fun _ _ _=>by simp)
      exact ⟨b,d,C (),hd,fun v=>⟨hb v,hz v⟩,hm⟩
  obtain ⟨b,d,C,hdet,hconditions,hmat⟩:=hcompletes
  let mat:=fun v=>controlledCompletionMatrix (a v) (b v) (c0*r) (d v) (hdet v)
  have hentry (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i j:Fin 2):
      N∣(mat v) i j-(mat (fun _=>1)) i j := by
    have he:=congrArg (fun T:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {N})=>T i j)
      ((hmat v).trans (hmat (fun _=>1)).symm)
    change Ideal.Quotient.mk (Ideal.span {N}) ((mat v) i j)=
      Ideal.Quotient.mk (Ideal.span {N}) ((mat (fun _=>1)) i j) at he
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  exact ⟨{
    lift := lift
    lift_period := hlift
    lift_residue := hres
    U := U
    w := w
    bezout := hbez
    sigma := σ
    epsilon := ε
    sigma_value := hσ
    epsilon_value := hε
    matrix := mat
    numerator := fun _=>rfl
    denominator := fun _=>rfl
    matrix_fixed := hentry
    conditions := hconditions
  }⟩

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

lemma frequency_congruence (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (D.matrix v 0 0)=
      (D.sigma i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}) := by
  rw [D.numerator,finiteCrossNumerator_local,D.sigma_value,D.lift_residue]

lemma numerator_congruence (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    N∣D.matrix v 0 0-a0*∏i,p i := by
  rw [D.numerator]
  exact finiteCrossNumerator_fixed N a0 c0 ramifiedTraceLambda p (D.lift v)
    (fun i=>(dvd_pow_self N (by decide : (2:ℕ)≠0)).trans (D.lift_period v i))

lemma numerator_mod_three (D:ControlledStratumArithmetic p N a0 c0 mode)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : (3:Eis)∣D.matrix v 0 0-a0 := by
  have hprod:=three_dvd_primary_sub_one (∏i,p i) hr
  convert dvd_add (h3N.trans (D.numerator_congruence v))
    (dvd_mul_of_dvd_right hprod a0) using 1 ; ring

lemma numerator_primary (D:ControlledStratumArithmetic p N a0 c0 mode)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1) (ha:lambda^2∣a0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : lambda^2∣D.matrix v 0 0-1 := by
  convert dvd_add (lambda_sq_dvd_three.trans (D.numerator_mod_three h3N hr v)) ha using 1 ; ring

lemma denominator_primary (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hr:lambda^2∣(∏i,p i)-1) (hc:lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : lambda^2∣D.matrix v 1 0-1 := by
  rw [D.denominator]
  exact primary_mul c0 (∏i,p i) hc hr

lemma ramified_relative (D:ControlledStratumArithmetic p N a0 c0 true)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1) (ha:lambda^2∣a0-1)
    (u:Eis) (hcu:(3:Eis)∣c0-u) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v*(lowerCuspMatrix u)⁻¹∈levelThree := by
  have hcond := D.conditions v
  simp only [ ↓reduceIte] at hcond
  apply A3_ramified_mem_levelThree
  · exact three_dvd_primary_sub_one _ (D.numerator_primary h3N hr ha v)
  · exact (show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hcond.1
  · rw [D.denominator]
    have hprod:=three_dvd_primary_sub_one (∏i,p i) hr
    convert dvd_add (dvd_mul_of_dvd_right hprod c0) hcu using 1 ; ring
  · exact hcond.2

lemma unramified_relative (D:ControlledStratumArithmetic p N a0 c0 false)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1) (hc:lambda^2∣c0-1)
    (u:Eis) (hau:(3:Eis)∣a0-u) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v*(A3WeylCusp u)⁻¹∈levelThree := by
  have hcond := D.conditions v
  simp only [Bool.false_eq_true, ↓reduceIte] at hcond
  apply A3_unramified_mem_levelThree
  · convert dvd_add (D.numerator_mod_three h3N hr v) hau using 1 ; ring
  · exact hcond.1
  · exact three_dvd_primary_sub_one _ (D.denominator_primary hr hc v)
  · exact (show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hcond.2

lemma inverse_fixed (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    ramifiedTraceLambda^3*c0∣D.matrix v 1 1-D.matrix (fun _=>1) 1 1 := by
  have hD9:ramifiedTraceLambda^3*c0∣(9:Eis)*c0 := by
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [←A4_traceLambda_pow_four]
    ring
  exact (hD9.trans hN).trans (D.matrix_fixed v 1 1)

lemma determinant (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v 0 0*D.matrix v 1 1-D.matrix v 0 1*(c0*∏i,p i)=1 := by
  simpa only [Matrix.det_fin_two,D.denominator] using (D.matrix v).property

def ramifiedFixedFactor (D:ControlledStratumArithmetic p N a0 c0 true) (u q:Eis) : ℂ :=
  eisEmbedding (symbol (-u) (D.matrix (fun _=>1) 0 0-u*D.matrix (fun _=>1) 0 1)*
    symbol q (D.matrix (fun _=>1) 0 0))

def unramifiedFixedFactor (D:ControlledStratumArithmetic p N a0 c0 false) : ℂ :=
  eisEmbedding (symbol (D.matrix (fun _=>1) 0 0) c0)

theorem ramified_character (D:ControlledStratumArithmetic p N a0 c0 true)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1) (ha:lambda^2∣a0-1)
    (u q:Eis) (hc0:c0=u*q) (hcu:(3:Eis)∣c0-u)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    complexCharacter ⟨D.matrix v*(lowerCuspMatrix u)⁻¹,
      D.ramified_relative ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
        ((dvd_mul_right 9 c0).trans hN)) hr ha u hcu v⟩=
      D.ramifiedFixedFactor u q*eisEmbedding (symbol (D.matrix v 0 0) (∏i,p i)) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N
  have hcN:c0∣N:=(dvd_mul_left c0 9).trans hN
  exact A3_ramified_fixed_sector_character (D.matrix v) (D.matrix (fun _=>1)) N u q (∏i,p i)
    (D.ramified_relative h3N hr ha u hcu v) (D.ramified_relative h3N hr ha u hcu (fun _=>1))
    (D.numerator_primary h3N hr ha v) (D.numerator_primary h3N hr ha (fun _=>1)) hr
    (by rw [D.denominator,hc0]) h9N
    ((hc0 ▸ dvd_mul_left q u).trans hcN) ((hc0 ▸ dvd_mul_right u q).trans hcN)
    (D.matrix_fixed v 0 0) (D.matrix_fixed v 0 1)

theorem unramified_character (D:ControlledStratumArithmetic p N a0 c0 false)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1) (hc:lambda^2∣c0-1)
    (u:Eis) (hau:(3:Eis)∣a0-u) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    complexCharacter ⟨D.matrix v*(A3WeylCusp u)⁻¹,
      D.unramified_relative ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
        ((dvd_mul_right 9 c0).trans hN)) hr hc u hau v⟩=
      D.unramifiedFixedFactor*eisEmbedding (symbol (D.matrix v 0 0) (∏i,p i)) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N
  have hcond:=D.conditions v
  simp only [Bool.false_eq_true, ↓reduceIte] at hcond
  exact A3_unramified_fixed_sector_character (D.matrix v) (D.matrix (fun _=>1)) u c0 (∏i,p i)
    (D.unramified_relative h3N hr hc u hau v) (D.denominator_primary hr hc v)
    (dvd_mul_of_dvd_right hcond.2 _) (D.denominator v)
    (((dvd_mul_left c0 9).trans hN).trans (D.matrix_fixed v 0 0))

end ControlledStratumArithmetic
end CubicEisenstein

end

end OAI

end Source288

/- Original source: OAI/NumberTheory/DirichletL/Eisenstein/FixedFrequencyExpansion.lean; sha256: 147b6a869c1a68f126f68b8430b9446d7bccd34402ef2deb51d6352f3b0f200a -/
section Source289
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
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

def fixedCusp (a0 c0:Eis) (mode:Bool) : SL(2,Eis) :=
  if mode then lowerCuspMatrix c0 else A3WeylCusp a0

lemma relative (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v*(fixedCusp a0 c0 mode)⁻¹∈levelThree := by
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
    ((dvd_mul_right 9 c0).trans hN)
  cases mode
  · exact D.unramified_relative h3N hr hbase a0 (by simp) v
  · exact D.ramified_relative h3N hr hbase c0 (by simp) v

def relativeGamma (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : levelThree :=
  ⟨D.matrix v*(fixedCusp a0 c0 mode)⁻¹,D.relative hN hr hbase v⟩

lemma relativeGamma_mul (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.relativeGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode=D.matrix v := by
  exact inv_mul_cancel_right (D.matrix v) (fixedCusp a0 c0 mode)

def fixedFactor (D:ControlledStratumArithmetic p N a0 c0 mode) : ℂ :=
  if mode then
    eisEmbedding (symbol (-c0) (D.matrix (fun _=>1) 0 0-c0*D.matrix (fun _=>1) 0 1)*
      symbol 1 (D.matrix (fun _=>1) 0 0))
  else eisEmbedding (symbol (D.matrix (fun _=>1) 0 0) c0)

theorem relative_character (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    complexCharacter (D.relativeGamma hN hr hbase v)=
      D.fixedFactor*eisEmbedding (symbol (D.matrix v 0 0) (∏i,p i)) := by
  cases mode
  · simpa only [relativeGamma,fixedCusp,fixedFactor,Bool.false_eq_true,↓reduceIte,
      unramifiedFixedFactor] using D.unramified_character hN hr hbase a0 (by simp) v
  · simpa only [relativeGamma,fixedCusp,fixedFactor,Bool.true_eq,↓reduceIte,
      ramifiedFixedFactor] using D.ramified_character hN hr hbase c0 1 (by simp) (by simp) v

theorem fixedFactor_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1) : ‖D.fixedFactor‖=1 := by
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
    ((dvd_mul_right 9 c0).trans hN)
  cases mode
  · exact norm_A3_unramified_fixed_factor _ _ _ _ _ (D.determinant (fun _=>1)) hbase
  · apply norm_A3_ramified_fixed_factor _ _ 1 (∏i,p i) _ c0
    · simpa only [one_mul] using D.determinant (fun _=>1)
    · exact D.numerator_primary h3N hr hbase (fun _=>1)
    · exact A3_ramified_relative_primary (D.matrix (fun _=>1)) c0
        (D.ramified_relative h3N hr hbase c0 (by simp) (fun _=>1))

noncomputable def fourierWeight [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
    (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i)

noncomputable def multiplierSum (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
    fourierWeight hp hg j v*star (complexCharacter (D.relativeGamma hN hr hbase v))*
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))

noncomputable def bracketProduct (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) : ℂ := by
  letI (i:ι):Field (Eis⧸Ideal.span {p i}):=Ideal.Quotient.field _
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)*
    bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x)

theorem multiplierSum_eq (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hp:∀i,p i≠0) (hc0:c0≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j:ι→ℕ) (hj:∀i,j i<6) (x:Eis) :
    D.multiplierSum hN hr hbase hp hg j x=
      (star D.fixedFactor*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U x)*
        D.bracketProduct hp hg j x := by
  exact stratum_multiplier_of_cubic_factor p hp hcop hg hchar c0 D.U D.w x
    (D.matrix (fun _=>1) 1 1) hc0 D.bezout
    (fun v=>D.matrix v 0 0) (fun v=>D.matrix v 0 1) (fun v=>D.matrix v 1 1)
    (fun v=>complexCharacter (D.relativeGamma hN hr hbase v)) D.fixedFactor
    (D.relative_character hN hr hbase) D.determinant (D.inverse_fixed hN)
    D.sigma D.epsilon D.frequency_congruence D.epsilon_value j hj

end ControlledStratumArithmetic
end

section
open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

def sourceGamma (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : levelTwo :=
  sourceLevelInclusion (D.relativeGamma hN hr hbase v)

lemma sourceGamma_mul (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.sourceGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode=D.matrix v :=
  D.relativeGamma_mul hN hr hbase v

lemma sourceGamma_character (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    levelTwoComplexCharacter (D.sourceGamma hN hr hbase v)=
      complexCharacter (D.relativeGamma hN hr hbase v) :=
  sourceLevelInclusion_character _

def datum (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : SourceCuspDatum :=
  s.datum (D.sourceGamma hN hr hbase v) (by
    rw [D.sourceGamma_mul,D.denominator]
    exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

lemma datum_point (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.datum hN hr hbase s hp hc0 v).point=eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i) := by
  rw [datum,s.datum_point,D.sourceGamma_mul,D.numerator,D.denominator]
  simpa only [ramifiedEmbedding_traceLambda] using
    finiteCrossNumerator_fraction a0 c0 ramifiedTraceLambda p (D.lift v) hc0 hp

noncomputable def smoothedValue (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,fourierWeight hp hg j v*
    (D.datum hN hr hbase s hp hc0 v).smoothedKernel W X

noncomputable def reflectedValue (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  fixedRadialCoefficientScalar*s.stratumShapeFactor (c0*∏i,p i)*
    ∑'t:ThetaFullIndex,
      (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
        ((ramifiedScale 1 completedRamifiedStep t.2.1*
          Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      CubicReflectionKernel.paperKernel (Vstar W)
        ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c0*∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)*
      ((star D.fixedFactor*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U
        (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))*
          D.bracketProduct hp hg j
            (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))

theorem smoothed_eq_reflected (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.smoothedValue hN hr hbase s hp hc0 hg j W X=D.reflectedValue s hp hc0 hg j W X := by
  let (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  have hc:c0*(∏i,p i)≠0:=mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  have hC:∀v,((D.sourceGamma hN hr hbase v:SL(2,Eis))*fixedCusp a0 c0 mode) 1 0=c0*∏i,p i := by
    intro v
    rw [D.sourceGamma_mul,D.denominator]
  have he:=s.sum_smoothedKernel_integral_phase (D.sourceGamma hN hr hbase) _ hc hC
    (fourierWeight hp hg j) W lo hi hlo hsupp hW X hX
  change D.smoothedValue hN hr hbase s hp hc0 hg j W X=_ at he
  rw [he]
  unfold reflectedValue
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*s.stratumShapeFactor (c0*∏i,p i)*z)
  apply tsum_congr
  intro t
  apply congrArg (fun z:ℂ=>
    (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
      ((ramifiedScale 1 completedRamifiedStep t.2.1*
        Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      CubicReflectionKernel.paperKernel (Vstar W)
        ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c0*∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)*z)
  simpa only [multiplierSum,D.sourceGamma_character,D.sourceGamma_mul,map_mul] using
    D.multiplierSum_eq hN hr hbase hp hc0 hcop hg hchar j hj
      (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))

end ControlledStratumArithmetic

theorem exists_constructed_stratum_reflection {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (N a0 c0:Eis) (hc0:c0≠0) (hN:(9:Eis)*c0∣N)
    (mode:Bool) (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hac:IsCoprime a0 c0) (hNp:∀i,IsCoprime N (p i)) :
    ∃s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode),
      ∃D:ControlledStratumArithmetic p N a0 c0 mode,
      ∀j:ι→ℕ,(∀i,j i<6)→∀(W:ℝ→ℂ)(lo hi:ℝ),0<lo→
        Function.support W⊆Set.Icc lo hi→ContDiff ℝ ∞ W→∀X:ℝ,0<X→
        D.smoothedValue hN (primary_finset_product Finset.univ p (fun i _=>hprimary i))
          hbase s hp hc0 hg j W X=D.reflectedValue s hp hc0 hg j W X := by
  obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)
  obtain ⟨D⟩:=exists_controlledStratumArithmetic p hp hcop hprimary N a0 c0 hc0 hN mode hbase hac hNp
  refine ⟨s,D,?_⟩
  intro j hj W lo hi hlo hsupp hW X hX
  exact D.smoothed_eq_reflected hN _ hbase s hp hc0 hcop hg hchar j hj W lo hi hlo hsupp hW X hX

end

section
open scoped Classical BigOperators MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O

structure FixedFourierGeometry (c:Eis) (h:Eis⧸Ideal.span {c}) where
  a0 : Eis
  c0 : Eis
  denominator_ne_zero : c0≠0
  denominator_dvd : c0∣c
  coprime : IsCoprime a0 c0
  point : eisEmbedding a0/eisEmbedding c0=thetaFourierTranslation c h
  mode : Bool
  primary : if mode then lambda^2∣a0-1 else lambda^2∣c0-1
  shape : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)

lemma exists_fixedFourierGeometry (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) :
    Nonempty (FixedFourierGeometry c h) := by
  obtain ⟨a0,c0,hc0,hdiv,hcop,hpoint,ha,hcp⟩:=
    ShortDraftCRT.exists_normalized_rational_cusp (-3*Quotient.out h) c hc
  have hp:eisEmbedding a0/eisEmbedding c0=thetaFourierTranslation c h := by
    rw [hpoint,thetaFourierTranslation,TraceLambdaPhase.eisLam_sq]
    simp only [map_mul,map_neg,map_ofNat]
  by_cases hl:lambda∣c0
  · obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 true)
    exact ⟨⟨a0,c0,hc0,hdiv,hcop,hp,true,ha hl,s⟩⟩
  · obtain ⟨s⟩:=exists_fixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 false)
    exact ⟨⟨a0,c0,hc0,hdiv,hcop,hp,false,hcp hl,s⟩⟩

def fixedFourierGeometry (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) :
    FixedFourierGeometry c h := Classical.choice (exists_fixedFourierGeometry c hc h)

namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)

abbrev PhaseResidue := Eis⧸Ideal.span {ramifiedTraceLambda^3*G.c0}

instance phaseResidue_finite : Finite G.PhaseResidue :=
  finite_quotient_span (A4_bad_modulus_ne_zero G.c0 G.denominator_ne_zero)

def levelScale : ℝ := fixedCuspLevelScale G.shape.index G.c0

lemma levelScale_pos : 0<G.levelScale :=
  fixedCuspLevelScale_pos G.shape.index G.c0 G.denominator_ne_zero

lemma levelScale_le (hc:c≠0) : G.levelScale≤fixedCuspLevelBound c :=
  fixedCuspLevelScale_le G.shape.index G.c0 c hc G.denominator_dvd

def dualNumerator (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  sourceCuspPhaseNumerator G.shape.index (G.shape.upper 0 0)
    (fixedCuspArrayIndex u m I J)

def staticPhase (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  G.shape.reflectionStaticPhase G.c0 G.denominator_ne_zero v (G.dualNumerator u) u m I J

lemma staticPhase_norm_le_one (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖G.staticPhase v u m I J‖≤1 :=
  G.shape.reflectionStaticPhase_norm_le_one G.c0 G.denominator_ne_zero v _ u m I J

def array (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase G.shape.index u (G.staticPhase v u) m I J

lemma array_norm_le_one (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖G.array v u m I J‖≤1 :=
  fixedCuspArrayWithPhase_norm_le_one G.shape.index u _ (G.staticPhase_norm_le_one v u) m I J

lemma array_eq (v:G.PhaseResidue) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    G.array v u m I J=G.shape.amplitude u m I J*
      A4PhaseFromResidue G.c0 G.denominator_ne_zero v (G.dualNumerator u m I J) :=
  G.shape.fixedCuspArrayWithPhase_reflectionStaticPhase G.c0 G.denominator_ne_zero v _ u m I J

end FixedFourierGeometry

def FixedReflectionRay (c:Eis) (hc:c≠0) :=
  Σh:Eis⧸Ideal.span {c},(fixedFourierGeometry c hc h).PhaseResidue×Eisˣ

instance fixedReflectionRay_finite (c:Eis) (hc:c≠0) : Finite (FixedReflectionRay c hc) := by
  let:Finite (Eis⧸Ideal.span {c}):=finite_quotient_span hc
  let:Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  unfold FixedReflectionRay
  infer_instance

noncomputable instance fixedReflectionRay_fintype (c:Eis) (hc:c≠0) :
    Fintype (FixedReflectionRay c hc) := Fintype.ofFinite _

def fixedReflectionRayCount (c:Eis) (hc:c≠0) : ℕ := Fintype.card (FixedReflectionRay c hc)

def fixedReflectionRayEquiv (c:Eis) (hc:c≠0) :
    FixedReflectionRay c hc≃Fin (fixedReflectionRayCount c hc) := Fintype.equivFin _

lemma fixedReflectionRayCount_subpower (c:Eis) (hc:c≠0) (z:ℂ) (κ:ℝ) (hκ:0≤κ) :
    ∃C:ℝ,0≤C ∧ ∀Z:ℝ,1≤Z→
      (fixedReflectionRayCount c hc:ℝ)^2*‖z‖^2≤C*Z^κ := by
  refine ⟨(fixedReflectionRayCount c hc:ℝ)^2*‖z‖^2,by positivity,?_⟩
  intro Z hZ
  have hz:1≤Z^κ:=Real.one_le_rpow hZ hκ
  exact le_mul_of_one_le_right (by positivity) hz

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem completedT_of_finite_cusp_profiles
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    {ι:Type*} [Fintype ι] (d:ι→SourceCuspDatum) (w:ι→ℂ)
    (hFG:∀v:ℝ,0<v→completedBesselProfile Ψ thetaBesselScale v=
      ∑i,w i*cuspBarProfile cubicSourceConjugateFunction (d i).point v)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=∑i,w i*(d i).smoothedKernel W X := by
  let : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let G:ι→ℝ→ℂ:=fun h=>
    cuspBarProfile cubicSourceConjugateFunction (d h).point
  have hG (h:ι) : ∀s:ℂ,MellinConvergent (G h) s:=
    (d h).cuspBarProfile_mellin_entire.1
  have hF:=completedBesselProfile_mellin_entire_of_periodic Ψ Q hperiod c hc hcQ
  have hVs:=Vstar_support W v0 v1 hWs
  have hV:=Vstar_contDiff W v0 v1 hv0 hWs hW
  let J:ι→ℝ→ℂ:=fun h t=>
    besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I)
  have hi (h:ι) : Integrable (J h):=
    besselSmoothingIntegrand_reflected_integrable (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  have hireal (h:ι) : Integrable (fun t:ℝ=>
      besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X (((-1:ℝ):ℂ)+t*Complex.I)):=by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one,J] using hi h
  have hleft:=besselSmoothingIntegrand_finite_integrable
    (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X (-1)
    (fun h t=>hG h _) hireal
  have hshift:=completedT_mellin_shift Ψ hΨ thetaBesselScale thetaBesselScale_pos hF.1 hF.2
    W v0 v1 hv0 hWs hW X hX (-1) (by norm_num) hleft
  have hline (h:ι) : (1/(2*Real.pi):ℂ)*(∫t:ℝ,J h t)=(d h).smoothedKernel W X:=by
    exact besselSmoothingIntegral_reflected_kernel (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  calc
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand (completedBesselProfile Ψ thetaBesselScale)
          thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I):=by
      simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hshift
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,∑h,w h*J h t:=by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      exact besselSmoothingIntegrand_finite_sum
        (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X _
        (fun h=>hG h _)
    _=∑h,w h*((1/(2*Real.pi):ℂ)*∫t:ℝ,J h t):=by
      rw [integral_finsetSum Finset.univ (fun h _=>(hi h).const_mul (w h)),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [integral_const_mul]
      ring
    _=∑h,w h*(d h).smoothedKernel W X:=by simp_rw [hline]

end CubicEisenstein

open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss
open CubicEisenstein hiding summand
local notation "Eis" => ActualEisensteinCubic.O

def fixedRowFourierPhase (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) (n:Eis) : ℂ :=
  quotientTrace c hc (h*Ideal.Quotient.mk _ n)

def fixedRowFourierCoeff (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (h:Eis⧸Ideal.span {c}) : ℂ :=
  finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedQuotientValue (Ideal.span {c}) φ) h

lemma fixedRowFourierCoeff_norm (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (h:Eis⧸Ideal.span {c}) :
    ‖fixedRowFourierCoeff c hc φ h‖≤1 :=
  finiteAdditiveFourierCoeff_norm _ _ (fixedQuotientValue_norm _ φ hφ) h

lemma fixedRowFourierCoeff_mass (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) :
    (∑h:Eis⧸Ideal.span {c},‖fixedRowFourierCoeff c hc φ h‖)≤
      (Fintype.card (Eis⧸Ideal.span {c}):ℝ) := by
  calc
    _≤∑_h:Eis⧸Ideal.span {c},(1:ℝ):=
      Finset.sum_le_sum (fun h _=>fixedRowFourierCoeff_norm c hc φ hφ h)
    _=_:=by simp

lemma fixedRowFourierPhase_norm (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})] (h:Eis⧸Ideal.span {c}) (n:Eis) :
    ‖fixedRowFourierPhase c hc h n‖=1 := AddChar.norm_apply _ _

lemma fixedRowFourierPhase_translation (c:Eis) (hc:c≠0) (h:Eis⧸Ideal.span {c}) (n:Eis) :
    fixedRowFourierPhase c hc h n=
      ShortDraftTrace.breveE (-cuspFrequency n*thetaFourierTranslation c h) :=
  (thetaFourierTranslation_phase c hc h n).symm

lemma fixedRowFourier_inversion (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo (Ideal.span {c}) φ) (n:Eis) :
    (∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*fixedRowFourierPhase c hc h n)=φ n := by
  rw [show (∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*fixedRowFourierPhase c hc h n)=
      fixedQuotientValue (Ideal.span {c}) φ (Ideal.Quotient.mk _ n) from
    finiteAdditiveFourier_inversion (quotientTrace c hc)
      (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc)
      (fixedQuotientValue (Ideal.span {c}) φ) _]
  exact fixedQuotientValue_mk _ φ hφ n

lemma summand_mul_fixed_twist (φ χ:Eis→*ℂ) (W:ℝ→ℂ) (X:ℝ) (I J:Ideal Eis) :
    summand (φ*χ) W X I J=
      φ (primaryGenerator I*(primaryGenerator J)^3)*summand χ W X I J := by
  have he (η:Eis→*ℂ) : cubeWeight η J=
      star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
        η (primaryGenerator J)^3/(Ideal.absNorm J:ℂ):=rfl
  rw [summand,summand,he,he]
  simp only [columnWeight,MonoidHom.mul_apply,map_mul,map_pow,mul_pow]
  ring

def completedFixedFrequency (χ:Eis→*ℂ) (c:Eis) (hc:c≠0)
    (h:Eis⧸Ideal.span {c}) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  ∑'p:Ideal Eis×Ideal Eis,summand χ W X p.1 p.2*
    fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)

lemma completedFixedFrequency_summable (χ:Eis→*ℂ) (c:Eis) (hc:c≠0)
    (h:Eis⧸Ideal.span {c}) (W:ℝ→ℂ) (hW:HasCompactSupport W) (X:ℝ) (hX:0<X) :
    Summable (fun p:Ideal Eis×Ideal Eis=>summand χ W X p.1 p.2*
      fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support χ W hW X hX).subset
  intro p hp
  exact left_ne_zero_of_mul hp

theorem completedT_fixed_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ χ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo (Ideal.span {c}) φ)
    (W:ℝ→ℂ) (hW:HasCompactSupport W) (X:ℝ) (hX:0<X) :
    completedT (φ*χ) W X=
      ∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*completedFixedFrequency χ c hc h W X := by
  have hp (p:Ideal Eis×Ideal Eis) : summand (φ*χ) W X p.1 p.2=
      ∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*
        (summand χ W X p.1 p.2*
          fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)) := by
    rw [summand_mul_fixed_twist,←fixedRowFourier_inversion c hc φ hφ,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  calc
    completedT (φ*χ) W X=∑'p:Ideal Eis×Ideal Eis,summand (φ*χ) W X p.1 p.2 :=
      (completedT_summable (φ*χ) W hW X hX).tsum_prod.symm
    _=∑'p:Ideal Eis×Ideal Eis,∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*
        (summand χ W X p.1 p.2*
          fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)) :=
      tsum_congr hp
    _=∑h:Eis⧸Ideal.span {c},∑'p:Ideal Eis×Ideal Eis,fixedRowFourierCoeff c hc φ h*
        (summand χ W X p.1 p.2*
          fixedRowFourierPhase c hc h (primaryGenerator p.1*(primaryGenerator p.2)^3)) :=
      Summable.tsum_finsetSum (fun h _=>(completedFixedFrequency_summable χ c hc h W hW X hX).mul_left _)
    _=_:=by simp only [tsum_mul_left,completedFixedFrequency]

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open CubicEisenstein hiding summand
local notation "Eis" => ActualEisensteinCubic.O

theorem actual_completedT_fixed_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hQ:Q≠0)
    (hcQ:Ideal.span {c}≤Q*Ideal.span {(72:Eis)})
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (∀h:Eis⧸Ideal.span {c},‖fixedRowFourierCoeff c hc φ h‖≤1) ∧
      (∀(W:ℝ→ℂ),HasCompactSupport W→∀X:ℝ,0<X→
        completedT (rowTwist Ψ m f z) W X=
          ∑h:Eis⧸Ideal.span {c},fixedRowFourierCoeff c hc φ h*
            completedFixedFrequency (freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) c hc h W X) := by
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hmod,hperiod,hnorm,hT⟩:=
    exists_actual_coprime_completed_row Ψ Q hQ hΨ hΨnorm m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,hcop,fixedRowFourierCoeff_norm c hc φ hφn,?_⟩
  intro W hW X hX
  rw [hT W X]
  exact completedT_fixed_fourier c hc φ _ (fun x y hxy=>hφ x y (hcQ hxy)) W hW X hX

end CanonicalRowCompletion

end

end OAI

end Source289

/- Original source: OAI/NumberTheory/DirichletL/Eisenstein/FixedThetaTwists.lean; sha256: 8aa61529274beb6f42b7584ffe317de37c7649ab99514866dc8eb2a87b96352f -/
section Source290
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

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedThetaTwist_mul (φ χ:Eis→*ℂ) (n:Eis) :
    fixedThetaTwist (φ*χ) n=fixedThetaTwist φ n*χ n := by
  by_cases hn:lambda^2∣n-1
  · rw [fixedThetaTwist_primary _ n hn,fixedThetaTwist_primary _ n hn,MonoidHom.mul_apply]
    ring
  · rw [fixedThetaTwist_not_primary _ n hn,fixedThetaTwist_not_primary _ n hn,zero_mul]

def fixedThetaRowCoeff (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (h:Eis⧸Ideal.span {c}) : ℂ :=
  finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient φ c) h

lemma fixedThetaRowCoeff_norm (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (h:Eis⧸Ideal.span {c}) :
    ‖fixedThetaRowCoeff c hc φ h‖≤1 :=
  finiteAdditiveFourierCoeff_norm _ _ (fixedThetaQuotient_norm_le_one φ hφ c) h

theorem fixedThetaTwist_fixed_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Q:Ideal Eis) (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (φ χ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (n:Eis) :
    fixedThetaTwist (φ*χ) n=
      ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*fixedRowFourierPhase c hc h n*χ n := by
  rw [←Finset.sum_mul,fixedThetaTwist_mul]
  congr 1
  have h:=finiteAdditiveFourier_inversion (quotientTrace c hc)
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) (fixedThetaQuotient φ c)
    (Ideal.Quotient.mk _ n)
  rw [fixedThetaQuotient_mk φ Q hφ c hcQ n] at h
  exact h.symm

theorem fixedThetaTwist_free_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Q:Ideal Eis) (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (I:Ideal Eis) (hI:CanonicalQuadraticSieve.Supported I)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (n:Eis) :
    fixedThetaTwist (φ*freePrimeRow I hI Q) n=
      (∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*fixedRowFourierPhase c hc h n)*
      ActualEisensteinCubic.principalSexticRow (fun P:FreePrimeIndex I Q=>P.val.val)
        (freePrimeIndex_pairwise_coprime I Q)
        (fun P=>(supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1)
        (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6)
        (ActualEisensteinCubic.finitePrimeModulus (fun P:FreePrimeIndex I Q=>P.val.val))
        (ActualEisensteinCubic.span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [fixedThetaTwist_fixed_fourier c hc Q hcQ φ _ hφ n,←Finset.sum_mul,
    freePrimeRow_eq_principalSexticRow I hI Q n]

theorem actual_fixedTheta_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:CanonicalQuadraticSieve.Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (∀h:Eis⧸Ideal.span {c},‖fixedThetaRowCoeff c hc φ h‖≤1) ∧
      (∀n,fixedThetaTwist (rowTwist Ψ m f z) n=
        ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*fixedRowFourierPhase c hc h n*
          freePrimeRow I hI (Q*Ideal.span {(72:Eis)}) n) := by
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hrow⟩:=exists_actual_coprime_row Ψ Q hΨ hΨnorm m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,hcop,fixedThetaRowCoeff_norm c hc φ hφn,?_⟩
  have he:fixedThetaTwist (rowTwist Ψ m f z)=
      fixedThetaTwist (φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})):=
    fixedThetaTwist_congr_primary _ _ hrow
  intro n
  rw [he]
  exact fixedThetaTwist_fixed_fourier c hc _ hcQ φ _ hφ n

end CubicEisenstein

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma admissiblePrimeGood (K:Ideal Eis) (hK:Admissible K) (P:PrimeIndex K) : lambda∉P.val :=
  (hK.2.2 P.val (Multiset.mem_toFinset.mp P.property)).1

theorem quadraticRow_eq_primeIndex (K:Ideal Eis) (hK:Admissible K) (x:Eis) :
    quadraticRow K x=finiteSexticRow (fun P:PrimeIndex K=>P.val)
      (admissiblePrimeGood K hK) (fun _=>3) x := by
  have hs:∀I∈({K}:Finset (Ideal Eis)),Admissible I:=by
    intro I hI
    simpa only [Finset.mem_singleton.mp hI] using hK
  have heq:primePool ({K}:Finset (Ideal Eis))=primeSupport K:=by
    simp [primePool,primeSupport]
  let e:primePool ({K}:Finset (Ideal Eis))≃PrimeIndex K:={
    toFun:=fun P=>⟨P.val,heq ▸ P.property⟩
    invFun:=fun P=>⟨P.val,heq.symm ▸ P.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  rw [quadraticRow_eq_pool {K} hs K (Finset.mem_singleton_self K) x,
    idealSupport_singleton_univ]
  simp only [QuadraticInitialBound.quadraticRow,finiteSquarefreeRow,Finset.prod_pow,
    finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]
  congr 1
  exact Fintype.prod_equiv e _ _ (fun P=>rfl)

theorem completedLocalExponent_residual (I F Q:Ideal Eis) (hFQ:F∣Q)
    (P:PrimeIndex (rowResidualPart I Q)) : completedLocalExponent I F P.val=1 := by
  have h:=rowResidualPart_prime_exponent I Q P.val (Multiset.mem_toFinset.mp P.property)
  have hnot:¬P.val∣F:=fun hd=>h.2.2 (hd.trans hFQ)
  simp only [completedLocalExponent,h.2.1,ite_eq_right hnot,mul_zero,add_zero,Nat.reduceMod]

theorem residual_bracket_eq_quadraticRow (I F Q:Ideal Eis) (hFQ:F∣Q)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (x:Eis) :
    (∏P:PrimeIndex (rowResidualPart I Q),
      bracket (actualSextic P.val
        (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) P))
        (completedLocalExponent I F P.val) (Ideal.Quotient.mk P.val x))=
      quadraticRow (rowResidualPart I Q) x := by
  simp_rw [completedLocalExponent_residual I F Q hFQ,bracket_one_eq_quadratic]
  rw [quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad)]
  simp only [finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]

def residualQuadraticPhase (K:Ideal Eis) (u:Eisˣ) (m:ℕ) (D E:Ideal Eis) : ℂ :=
  quadraticRow K ((u.val*lambda^m)*primaryGenerator (D*E))

lemma residualQuadraticPhase_norm_le_one (K:Ideal Eis) (u:Eisˣ) (m:ℕ) (D E:Ideal Eis) :
    ‖residualQuadraticPhase K u m D E‖≤1 := quadraticRow_norm_le_one _ _

theorem residual_bracket_extracted_columns (I F Q:Ideal Eis) (hFQ:F∣Q)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (u:Eisˣ) (m:ℕ) (D E n b:Ideal Eis) :
    (∏P:PrimeIndex (rowResidualPart I Q),
      bracket (actualSextic P.val
        (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) P))
        (completedLocalExponent I F P.val)
        (Ideal.Quotient.mk P.val
          ((u.val*lambda^m)*primaryGenerator (D*n)*(primaryGenerator (E*b))^3)))=
      residualQuadraticPhase (rowResidualPart I Q) u m D E *
        quadraticRow (rowResidualPart I Q) (primaryGenerator (n*b)) := by
  simp_rw [completedLocalExponent_residual I F Q hFQ]
  rw [residual_bracket_product]
  rw [←quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad),
    ←quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad)]
  simp only [primaryGenerator_mul,residualQuadraticPhase,
    canonical_quadraticRow_argument_mul _ (rowResidualPart_admissible I Q hbad)]
  ring

end

section
open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

def actualResidualModelRow (K:ℝ) (I Q:Ideal Eis) (hI:I≠0)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (hIK:(Ideal.absNorm I:ℝ)≤K) :
    idealRange (completedResidualScale K I Q) := by
  refine ⟨rowResidualPart I Q,mem_idealRange.mpr ⟨rowResidualPart_admissible I Q hbad,?_⟩⟩
  rw [rowResidualPart_norm I Q hI,completedResidualScale]
  exact div_le_div_of_nonneg_right hIK (by positivity)

lemma actualResidualModelRow_val (K:ℝ) (I Q:Ideal Eis) (hI:I≠0)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (hIK:(Ideal.absNorm I:ℝ)≤K) :
    (actualResidualModelRow K I Q hI hbad hIK).val=rowResidualPart I Q := rfl

lemma actualResidualModelRow_shell (K:ℝ) (I Q:Ideal Eis) (hI:I≠0)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (hIK:(Ideal.absNorm I:ℝ)≤K)
    (hlo:K/2≤(Ideal.absNorm I:ℝ)) :
    completedResidualScale K I Q/2≤(Ideal.absNorm (actualResidualModelRow K I Q hI hbad hIK).val:ℝ) := by
  change completedResidualScale K I Q/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ)
  rw [rowResidualPart_norm I Q hI,completedResidualScale]
  have h:=div_le_div_of_nonneg_right hlo
    (show 0≤(Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ) by positivity)
  convert h using 1 ; ring

theorem completedBranchScale_raw_argument {ι:Type*} [Fintype ι]
    (K X c r:ℝ) (I F Q:Ideal Eis) (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (e:ι→Fin 3) (k n b:Ideal Eis) (hK:0<completedResidualScale K I Q)
    (hc:0<c) (hk:k≠0) :
    ((completedBranchScale K (X/c) I F Q P e)⁻¹*
      (completedResidualScale K I Q/(Ideal.absNorm k:ℝ))^2)*r^3*
      (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3=
    X*r^3*
      (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 1*n):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 2*b):ℝ)^3/
      (c*(Ideal.absNorm k:ℝ)^2*(Ideal.absNorm (∏i,P i):ℝ)^2) := by
  have hkN:(Ideal.absNorm k:ℝ)≠0:=by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hk)
  have hpN:(Ideal.absNorm (∏i,P i):ℝ)≠0:=by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun i _=>NeZero.ne (P i))))
  simp only [completedBranchScale,inv_div,map_mul,Nat.cast_mul]
  field_simp [hK.ne',hc.ne',hkN,hpN]

end

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def residualModelRowPhase {K:ℝ} (rowPhase:ℕ→idealRange K→ℂ)
    (u:Eisˣ) (D E:Ideal Eis) (m:ℕ) (k:idealRange K) : ℂ :=
  rowPhase m k*residualQuadraticPhase k.val u m D E

lemma residualModelRowPhase_norm_le_one {K:ℝ} (rowPhase:ℕ→idealRange K→ℂ)
    (hphase:∀m k,‖rowPhase m k‖≤1) (u:Eisˣ) (D E:Ideal Eis) (m:ℕ) (k:idealRange K) :
    ‖residualModelRowPhase rowPhase u D E m k‖≤1 := by
  rw [residualModelRowPhase,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (hphase m k)).trans (residualQuadraticPhase_norm_le_one k.val u m D E)

theorem residual_coefficient_eq_canonical {ι:Type*} [Fintype ι]
    (I F Q:Ideal Eis) (hFQ:F∣Q) (hbad:∀P∈fixedBadPrimes,P∣Q)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (u:Eisˣ)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (rowPhase:ℕ→ℂ) (m:ℕ) (n b:Ideal Eis) :
    let D:=reflectionExtractedDivisor P j e 1
    let E:=reflectionExtractedDivisor P j e 2
    (rowPhase m*(∏p:PrimeIndex (rowResidualPart I Q),
        bracket (actualSextic p.val (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) p))
          (completedLocalExponent I F p.val)
          (Ideal.Quotient.mk p.val ((u.val*lambda^m)*primaryGenerator (D*n)*(primaryGenerator (E*b))^3))) *
      η m (D*n) (E*b)*reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*b)))/
        ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm (D*n):ℝ)*(Ideal.absNorm (E*b):ℝ):ℝ):ℂ)=
      4*canonicalRawBranchCoefficient P hg j e ρ q
        (fun l a c=>η l (D*a) (E*c))
        (fun l=>rowPhase l*residualQuadraticPhase (rowResidualPart I Q) u l D E)
        (rowResidualPart I Q) m n b := by
  dsimp only
  rw [residual_bracket_extracted_columns I F Q hFQ hbad]
  unfold canonicalRawBranchCoefficient reflectedDyadicCoefficient
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring

end CompletedGauss

open scoped Classical BigOperators ContDiff

namespace CompletedGauss.FreeReflection

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def pool (I Q Q0:Ideal Eis) : Finset (Ideal Eis) :=
  (completedReflectionPool I Q).filter (fun P=>¬Q0≤P)

lemma pool_subset (I Q Q0:Ideal Eis) : pool I Q Q0⊆completedReflectionPool I Q :=
  Finset.filter_subset _ _
lemma pool_maximal (I Q Q0:Ideal Eis) (P:pool I Q Q0) : P.val.IsMaximal :=
  completedReflectionPool_maximal I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_good (I Q Q0:Ideal Eis) (P:pool I Q Q0) : lambda∉P.val :=
  completedReflectionPool_good I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_odd (I Q Q0:Ideal Eis) (P:pool I Q Q0) : ringChar (Eis⧸P.val)≠2 :=
  completedReflectionPool_odd I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_divides (I Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (P:pool I Q Q0) : P.val∣I*Q :=
  completedReflectionPool_divides I Q hI hQ ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_nonresidual (I Q Q0:Ideal Eis) (P:pool I Q Q0) : ¬P.val∣rowResidualPart I Q :=
  completedReflectionPool_nonresidual I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_free (I Q Q0:Ideal Eis) (P:pool I Q Q0) : ¬Q0≤P.val :=
  (Finset.mem_filter.mp P.property).2

lemma pool_eq_on_fiber (I J Q Q0:Ideal Eis) (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J) (hT:rowMaskPart I Q=rowMaskPart J Q) :
    pool I Q Q0=pool J Q Q0 := by
  unfold pool
  rw [completedReflectionPool_eq_on_fiber I J Q hI hJ hQ hA hT]

end

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def reflectionChoiceValue (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6)
    (P:Ideal Eis) : Fin 6 :=
  if h:P∈pool I Q Q0 then e ⟨P,h⟩ else 0

def reflectionActivePool (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6) : Finset (Ideal Eis) :=
  (pool I Q Q0).filter (fun P=>reflectionSixActive (reflectionChoiceValue I Q Q0 e P))

lemma reflectionActivePool_subset (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6) :
    reflectionActivePool I Q Q0 e⊆pool I Q Q0 := Finset.filter_subset _ _

lemma mem_reflectionActivePool (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6)
    (P:pool I Q Q0) :
    P.val∈reflectionActivePool I Q Q0 e ↔ reflectionSixActive (e P) := by
  rw [reflectionActivePool, Finset.mem_filter]
  simp only [P.property, true_and]
  rw [reflectionChoiceValue, dite_eq_left P.property]

lemma reflectionActivePool_encode (I Q Q0:Ideal Eis)
    (A:Finset (pool I Q Q0)) (e:A→Fin 3) :
    reflectionActivePool I Q Q0 (encodeReflectionSix ⟨A,e⟩)=A.image Subtype.val := by
  ext P
  constructor
  · intro hP
    let p:pool I Q Q0:=⟨P,reflectionActivePool_subset I Q Q0 _ hP⟩
    have hp:p∈A:=(reflectionSixActive_encode ⟨A,e⟩ p).mp
      ((mem_reflectionActivePool I Q Q0 _ p).mp hP)
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  · intro hP
    obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hP
    exact (mem_reflectionActivePool I Q Q0 _ p).mpr ((reflectionSixActive_encode ⟨A,e⟩ p).mpr hp)

def reflectionActiveLabel (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6)
    (P:reflectionActivePool I Q Q0 e) : Fin 3 :=
  reflectionSixLabel (e ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩)

def sixReflectedBranch (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6)
    (amplitude:ℕ→Ideal Eis→Ideal Eis→ℂ) (hamp:∀m n b,‖amplitude m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q where
  levelScale:=levelScale
  levelScale_pos:=hlevel
  levelScale_le:=hbound
  primes:=reflectionActivePool I Q Q0 e
  maximal:=fun P=>pool_maximal I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  good:=fun P=>pool_good I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  coprime:=by
    intro P R hPR
    let : P.val.IsMaximal:=pool_maximal I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
    let : R.val.IsMaximal:=pool_maximal I Q Q0 ⟨R.val,reflectionActivePool_subset I Q Q0 e R.property⟩
    exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPR)
  divides:=fun P=>pool_divides I Q Q0 hI hQ ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  nonresidual:=fun P=>pool_nonresidual I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  label:=reflectionActiveLabel I Q Q0 e
  nColumns:=fun i=>dualIdealDyad i.2.2
  bColumns:=fun i=>dualIdealDyad i.2.1
  nBounds:=fun i n hn=>dualIdealDyad_bounds i.2.2 n hn
  bBounds:=fun i b hb=>dualIdealDyad_bounds i.2.1 b hb
  amplitude:=fun i=>amplitude i.1
  amplitude_bound:=fun i n _ b _=>hamp i.1 n b
  rowPhase:=fun i=>rowPhase i.1
  rowPhase_bound:=fun i k=>hrow i.1 k

end

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def sixPhaseFixedCuspBranch (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q :=
  (sixReflectedBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e
    (fixedCuspArrayWithPhase cusp u phaseArray)
    (fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase) rowPhase hrow).withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow

lemma sixPhaseFixedCuspBranch_primes (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    (sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow).primes=reflectionActivePool I Q Q0 e := rfl

lemma sixPhaseFixedCuspBranch_amplitude (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    let D:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1
    let E:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2
    d.amplitude i n b=phaseArray i.1 (D*n) (E*b)*fixedConjugateCuspArray cusp u i.1 (D*n) (E*b) := rfl

lemma sixPhaseFixedCuspBranch_scale (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K X levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    completedBranchScale K (X/d.levelScale) I F Q (fun P:d.primes=>P.val) d.label=
      completedBranchScale K (X/levelScale) I F Q
        (fun P:reflectionActivePool I Q Q0 e=>P.val) (reflectionActiveLabel I Q Q0 e) := rfl

end
section

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
local instance poolMaximal (I Q Q0:Ideal Eis) (P:pool I Q Q0) : P.val.IsMaximal :=
  pool_maximal I Q Q0 P
noncomputable local instance poolField (I Q Q0:Ideal Eis) (P:pool I Q Q0) : Field (Eis⧸P.val) :=
  Ideal.Quotient.field P.val
noncomputable local instance poolFintype (I Q Q0:Ideal Eis) (P:pool I Q Q0) : Fintype (Eis⧸P.val) :=
  Fintype.ofFinite _

def reflectionInactiveStratumWeight (I F Q Q0:Ideal Eis) (A:Finset (pool I Q Q0)) : ℂ :=
  ∏P∈(Finset.univ:Finset (pool I Q Q0))\A,
    zeroFourierCoefficient (actualSextic P.val (pool_good I Q Q0 P))
      (completedLocalExponent I F P.val)

lemma reflectionInactiveStratumWeight_norm_le_one (I F Q Q0:Ideal Eis)
    (A:Finset (pool I Q Q0)) : ‖reflectionInactiveStratumWeight I F Q Q0 A‖≤1 := by
  rw [reflectionInactiveStratumWeight,norm_prod]
  apply Finset.prod_le_one₀ (fun _ _=>norm_nonneg _)
  intro P _
  by_cases hj:completedLocalExponent I F P.val=0
  · rw [hj]
    exact zeroFourierCoefficient_zero_norm_le_one _
  · have he:=canonical_zeroFourierCoefficient P.val (pool_good I Q Q0 P)
      (pool_odd I Q Q0 P) (completedLocalExponent I F P.val)
      (Nat.mod_lt _ (by decide : 0<6))
    have hz:zeroFourierCoefficient (actualSextic P.val (pool_good I Q Q0 P))
        (completedLocalExponent I F P.val)=0 := by
      simpa only [actualSextic,ite_eq_right hj] using he
    rw [hz]
    simp

def reflectionSixInactiveWeight (I F Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6) : ℂ :=
  if reflectionSixValid e then reflectionInactiveStratumWeight I F Q Q0 (reflectionSixSupport e) else 0

lemma reflectionSixInactiveWeight_norm_le_one (I F Q Q0:Ideal Eis)
    (e:pool I Q Q0→Fin 6) : ‖reflectionSixInactiveWeight I F Q Q0 e‖≤1 := by
  unfold reflectionSixInactiveWeight
  split_ifs
  · exact reflectionInactiveStratumWeight_norm_le_one I F Q Q0 _
  · simp

lemma sum_reflectionSixInactiveWeight_unpad (I F Q Q0:Ideal Eis)
    (G:(pool I Q Q0→Fin 6)→ℂ) :
    (∑e:pool I Q Q0→Fin 6,reflectionSixInactiveWeight I F Q Q0 e*G e)=
      ∑A:Finset (pool I Q Q0),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q Q0 A*G (encodeReflectionSix ⟨A,e⟩) := by
  rw [sum_active_exceptional_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e
  · rw [ite_eq_left he,encode_decodeReflectionSix e he]
    simp only [reflectionSixInactiveWeight,ite_eq_left he,decodeReflectionSix]
  · simp only [ite_eq_right he,reflectionSixInactiveWeight,zero_mul]

abbrev SixReflectionIndex (rays:ℕ) (I Q Q0:Ideal Eis) :=
  Fin rays×(pool I Q Q0→Fin 6)

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def sixPhaseFixedCuspFiber (rays:ℕ) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q Q0→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q Q0→Fin 3) (unit:SixReflectionIndex rays I Q Q0→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q Q0→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) : ReflectedFiberData rays levelBound K I F Q where
  pool:=pool I Q Q0
  maximal:=pool_maximal I Q Q0
  divides:=pool_divides I Q Q0 hI hQ
  branch:=fun x=>sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound (levelScale x) (hlevel x) (hlevelBound x)
    x.2 (cusp x) (unit x) (phaseArray x) (hphase x) (rowPhase x) (hrow x)
  weight:=fun x=>rayWeight x*reflectionSixInactiveWeight I F Q Q0 x.2
  weight_bound:=by
    intro x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hray x)).trans (reflectionSixInactiveWeight_norm_le_one I F Q Q0 x.2)

theorem sixPhaseFixedCuspFiber_value (rays:ℕ) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q Q0→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q Q0→Fin 3) (unit:SixReflectionIndex rays I Q Q0→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q Q0→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=sixPhaseFixedCuspFiber rays I F Q Q0 hI hQ K levelBound levelScale hlevel hlevelBound
      cusp unit phaseArray hphase rayWeight hray rowPhase hrow
    d.value W X ρ q k=
      ∑t:Fin rays,∑A:Finset (pool I Q Q0),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q Q0 A*rayWeight (t,encodeReflectionSix ⟨A,e⟩)*
          (d.branch (t,encodeReflectionSix ⟨A,e⟩)).value W X ρ q k := by
  dsimp only
  rw [ReflectedFiberData.value,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _=∑e:pool I Q Q0→Fin 6,reflectionSixInactiveWeight I F Q Q0 e*
      (rayWeight (t,e)*(sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound (levelScale (t,e))
        (hlevel (t,e)) (hlevelBound (t,e)) e (cusp (t,e)) (unit (t,e))
        (phaseArray (t,e)) (hphase (t,e)) (rowPhase (t,e)) (hrow (t,e))).value W X ρ q k) := by
          apply Finset.sum_congr rfl
          intro e _
          dsimp only [sixPhaseFixedCuspFiber]
          ring
    _=_ := by
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [sixPhaseFixedCuspFiber]
      exact (mul_assoc _ _ _).symm

end CompletedGauss.FreeReflection

end

end OAI

end Source290

/- Original source: OAI/NumberTheory/DirichletL/GaussSum/FixedRayFibers.lean; sha256: 7c6fa56f60cb842441dafc8e727ee46be05bde1335f59d1104b058ce64421c7c -/
section Source291
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

open scoped Classical BigOperators ContDiff

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

abbrev FixedBranchIndex (c:Eis) (hc:c≠0) (I Q Q0:Ideal Eis) :=
  FixedReflectionRay c hc×(pool I Q Q0→Fin 6)

def fixedRayFiber (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) :
    ReflectedFiberData (fixedReflectionRayCount c hc) (fixedCuspLevelBound c) K I F Q := by
  let R:SixReflectionIndex (fixedReflectionRayCount c hc) I Q Q0→FixedReflectionRay c hc:=
    fun x=>(fixedReflectionRayEquiv c hc).symm x.1
  let G:=fun x=>fixedFourierGeometry c hc (R x).1
  exact sixPhaseFixedCuspFiber (fixedReflectionRayCount c hc) I F Q Q0 hI hQ K
    (fixedCuspLevelBound c) (fun x=>(G x).levelScale)
    (fun x=>(G x).levelScale_pos) (fun x=>(G x).levelScale_le hc)
    (fun x=>(G x).shape.index) (fun x=>(R x).2.2)
    (fun x=>(G x).staticPhase (R x).2.1 (R x).2.2)
    (fun x=>(G x).staticPhase_norm_le_one (R x).2.1 (R x).2.2)
    (fun x=>rayWeight (R x,x.2)) (fun x=>hray (R x,x.2))
    (fun x=>rowPhase (R x,x.2)) (fun x=>hrow (R x,x.2))

lemma fixedRayFiber_pool (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) :
    (fixedRayFiber c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow).pool=pool I Q Q0 := rfl

theorem fixedRayFiber_value (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=fixedRayFiber c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow
    d.value W X ρ q k=
      ∑r:FixedReflectionRay c hc,∑A:Finset (pool I Q Q0),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q Q0 A*rayWeight (r,encodeReflectionSix ⟨A,e⟩)*
          (d.branch (fixedReflectionRayEquiv c hc r,encodeReflectionSix ⟨A,e⟩)).value W X ρ q k := by
  dsimp only
  rw [ReflectedFiberData.value,Fintype.sum_prod_type]
  calc
    _=∑r:FixedReflectionRay c hc,∑e:pool I Q Q0→Fin 6,
        reflectionSixInactiveWeight I F Q Q0 e*
          (rayWeight (r,e)*((fixedRayFiber c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow).branch
            (fixedReflectionRayEquiv c hc r,e)).value W X ρ q k) := by
      apply Fintype.sum_equiv (fixedReflectionRayEquiv c hc).symm
      intro t
      apply Finset.sum_congr rfl
      intro e he
      simp only [Equiv.apply_symm_apply]
      change (rayWeight ((fixedReflectionRayEquiv c hc).symm t,e)*
        reflectionSixInactiveWeight I F Q Q0 e)*_= _
      ring
    _=_:=by
      apply Finset.sum_congr rfl
      intro r hr
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro e he
      exact (mul_assoc _ _ _).symm

end CompletedGauss.FreeReflection

open scoped BigOperators Classical

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def residualArgumentPhase (K:Ideal Eis) (z:Eis) (D E:Ideal Eis) : ℂ :=
  quadraticRow K (z*primaryGenerator (D*E))

lemma residualArgumentPhase_norm_le_one (K:Ideal Eis) (z:Eis) (D E:Ideal Eis) :
    ‖residualArgumentPhase K z D E‖≤1 := quadraticRow_norm_le_one _ _

theorem residual_bracket_extracted_argument (I F Q:Ideal Eis) (hFQ:F∣Q)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (z:Eis) (D E n b:Ideal Eis) :
    (∏P:PrimeIndex (rowResidualPart I Q),
      bracket (actualSextic P.val
        (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) P))
        (completedLocalExponent I F P.val)
        (Ideal.Quotient.mk P.val
          (z*primaryGenerator (D*n)*(primaryGenerator (E*b))^3)))=
      residualArgumentPhase (rowResidualPart I Q) z D E *
        quadraticRow (rowResidualPart I Q) (primaryGenerator (n*b)) := by
  simp_rw [completedLocalExponent_residual I F Q hFQ]
  rw [residual_bracket_product]
  rw [←quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad),
    ←quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad)]
  simp only [primaryGenerator_mul,residualArgumentPhase,
    canonical_quadraticRow_argument_mul _ (rowResidualPart_admissible I Q hbad)]
  ring

def residualArgumentRowPhase {K:ℝ} (rowPhase:ℕ→idealRange K→ℂ)
    (residualArgument:ℕ→Eis) (D E:Ideal Eis) (m:ℕ) (k:idealRange K) : ℂ :=
  rowPhase m k*residualArgumentPhase k.val (residualArgument m) D E

lemma residualArgumentRowPhase_norm_le_one {K:ℝ} (rowPhase:ℕ→idealRange K→ℂ)
    (hphase:∀m k,‖rowPhase m k‖≤1) (residualArgument:ℕ→Eis)
    (D E:Ideal Eis) (m:ℕ) (k:idealRange K) :
    ‖residualArgumentRowPhase rowPhase residualArgument D E m k‖≤1 := by
  rw [residualArgumentRowPhase,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (hphase m k)).trans (residualArgumentPhase_norm_le_one k.val _ D E)

theorem residual_coefficient_eq_canonical_argument {ι:Type*} [Fintype ι]
    (I F Q:Ideal Eis) (hFQ:F∣Q) (hbad:∀P∈fixedBadPrimes,P∣Q)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (residualArgument:ℕ→Eis)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (rowPhase:ℕ→ℂ) (m:ℕ) (n b:Ideal Eis) :
    let D:=reflectionExtractedDivisor P j e 1
    let E:=reflectionExtractedDivisor P j e 2
    (rowPhase m*(∏p:PrimeIndex (rowResidualPart I Q),
        bracket (actualSextic p.val (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) p))
          (completedLocalExponent I F p.val)
          (Ideal.Quotient.mk p.val (residualArgument m*primaryGenerator (D*n)*(primaryGenerator (E*b))^3))) *
      η m (D*n) (E*b)*reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*b)))/
        ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm (D*n):ℝ)*(Ideal.absNorm (E*b):ℝ):ℝ):ℂ)=
      4*canonicalRawBranchCoefficient P hg j e ρ q
        (fun l a c=>η l (D*a) (E*c))
        (fun l=>rowPhase l*residualArgumentPhase (rowResidualPart I Q) (residualArgument l) D E)
        (rowResidualPart I Q) m n b := by
  dsimp only
  rw [residual_bracket_extracted_argument I F Q hFQ hbad]
  unfold canonicalRawBranchCoefficient reflectedDyadicCoefficient
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring

end

section
open ActualEisensteinCubic CubicEisenstein LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma reflectedBranch_local_support {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (n b:Eis) (hne:reflectedBranch P hg j e n b≠0) :
    (∀i,j i=4 → e i=1 → n∈P i) ∧
    (∀i,j i=4 → e i=2 → n∉P i ∧ b∈P i) := by
  have hi (i:ι):reflectedLocalPiece (P i) (hg i) (j i) (e i) n b≠0:=
    (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  constructor
  · intro i hj he
    by_contra hn
    exact hi i (by simp [reflectedLocalPiece,hj,exceptionalPiece,he,hn])
  · intro i hj he
    by_contra hn
    exact hi i (by simp [reflectedLocalPiece,hj,exceptionalPiece,he,hn])

lemma reflectionExtractedDivisor_dvd_of_local {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hcop:Pairwise (fun i k=>IsCoprime (P i) (P k)))
    (j:ι→ℕ) (e:ι→Fin 3) (v:Fin 3) (A:Ideal Eis)
    (hA:∀i,(j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) → P i∣A) :
    reflectionExtractedDivisor P j e v∣A := by
  unfold reflectionExtractedDivisor
  apply Fintype.prod_dvd_of_coprime
  · intro i k hik
    change IsCoprime (reflectionExtractedPrime (P i) (j i) (e i) v)
      (reflectionExtractedPrime (P k) (j k) (e k) v)
    unfold reflectionExtractedPrime
    by_cases hi:(j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0)
    · rw [ite_eq_left hi]
      by_cases hk:(j k=4 ∧ e k=v) ∨ (j k=0 ∧ v=0)
      · rw [ite_eq_left hk]
        exact hcop hik
      · rw [ite_eq_right hk]
        exact isCoprime_one_right
    · rw [ite_eq_right hi]
      exact isCoprime_one_left
  · intro i
    unfold reflectionExtractedPrime
    split_ifs with hi
    · exact hA i hi
    · exact one_dvd _

theorem reflectedBranch_extracted_divisibility {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (hcop:Pairwise (fun i k=>IsCoprime (P i) (P k)))
    (j:ι→ℕ) (e:ι→Fin 3) (n b:Eis) (hne:reflectedBranch P hg j e n b≠0) :
    reflectionExtractedDivisor P j e 1∣Ideal.span {n} ∧
    reflectionExtractedDivisor P j e 2∣Ideal.span {b} ∧
    (∀i,j i=4 → e i=2 → n∉P i) := by
  have hs:=reflectedBranch_local_support P hg j e n b hne
  refine ⟨reflectionExtractedDivisor_dvd_of_local P hcop j e 1 _ ?_,
    reflectionExtractedDivisor_dvd_of_local P hcop j e 2 _ ?_,fun i hj he=>(hs.2 i hj he).1⟩
  · intro i hi
    have h:j i=4 ∧ e i=1:=by simpa using hi
    exact Ideal.dvd_span_singleton.mpr (hs.1 i h.1 h.2)
  · intro i hi
    have h:j i=4 ∧ e i=2:=by simpa using hi
    exact Ideal.dvd_span_singleton.mpr (hs.2 i h.1 h.2).2

def fixedCuspBranchNumerator {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase cusp u phaseArray m n b *
    reflectedBranch P hg j e (primaryGenerator n) (primaryGenerator b)

theorem fixedCuspBranchNumerator_support {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (hcop:Pairwise (fun i k=>IsCoprime (P i) (P k)))
    (j:ι→ℕ) (e:ι→Fin 3) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (n b:Ideal Eis)
    (hne:fixedCuspBranchNumerator P hg j e cusp u phaseArray m n b≠0) :
    reflectionExtractedDivisor P j e 1∣n ∧ reflectionExtractedDivisor P j e 2∣b ∧
    (∀i,j i=4 → e i=2 → primaryGenerator n∉P i) := by
  have hn:(fixedCuspArrayWithPhase cusp u phaseArray m n b)≠0:=
    (mul_ne_zero_iff.mp hne).1
  have he:fixedCuspArrayEligible n b:=by
    by_contra he
    exact hn (fixedCuspArrayWithPhase_zero cusp u phaseArray m n b he)
  have hb:reflectedBranch P hg j e (primaryGenerator n) (primaryGenerator b)≠0:=
    (mul_ne_zero_iff.mp hne).2
  have hs:=reflectedBranch_extracted_divisibility P hg hcop j e _ _ hb
  rwa [(primaryGenerator_spec n he.2.1).1,(primaryGenerator_spec b he.2.2).1] at hs

end

open ActualEisensteinCubic CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

def nonzeroDualDilation (D E:Ideal Eis) (hD:D≠0) (hE:E≠0)
    (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℕ×NonzeroDualIdeal×NonzeroDualIdeal :=
  (x.1,⟨D*x.2.1.val,mul_ne_zero hD x.2.1.property⟩,
    ⟨E*x.2.2.val,mul_ne_zero hE x.2.2.property⟩)

lemma nonzeroDualDilation_injective (D E:Ideal Eis) (hD:D≠0) (hE:E≠0) :
    Function.Injective (nonzeroDualDilation D E hD hE) := by
  intro x y h
  apply Prod.ext
  · have ht:=congrArg (fun t:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>t.1) h
    exact ht
  · apply Prod.ext
    · apply Subtype.ext
      exact mul_left_cancel₀ hD (congrArg (fun t:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>t.2.1.val) h)
    · apply Subtype.ext
      exact mul_left_cancel₀ hE (congrArg (fun t:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>t.2.2.val) h)

theorem tsum_nonzeroDualDilation (D E:Ideal Eis) (hD:D≠0) (hE:E≠0)
    (f:(ℕ×NonzeroDualIdeal×NonzeroDualIdeal)→ℂ)
    (hsupport:∀x,f x≠0 → D∣x.2.1.val ∧ E∣x.2.2.val) :
    (∑'x,f x)=∑'x,f (nonzeroDualDilation D E hD hE x) := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun x:Function.support (fun y=>f (nonzeroDualDilation D E hD hE y))=>
      nonzeroDualDilation D E hD hE x.val)
  · exact (nonzeroDualDilation_injective D E hD hE).comp Subtype.val_injective
  · intro x hx
    obtain ⟨hn,hb⟩:=hsupport x hx
    obtain ⟨n,hn⟩:=hn
    obtain ⟨b,hb⟩:=hb
    have hn0:n≠0:=by
      intro hz
      apply x.2.1.property
      rw [hn,hz,mul_zero]
    have hb0:b≠0:=by
      intro hz
      apply x.2.2.property
      rw [hb,hz,mul_zero]
    let y:ℕ×NonzeroDualIdeal×NonzeroDualIdeal:=(x.1,⟨n,hn0⟩,⟨b,hb0⟩)
    have hy:nonzeroDualDilation D E hD hE y=x:=by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact Subtype.ext hn.symm
        · exact Subtype.ext hb.symm
    refine ⟨⟨y,?_⟩,hy⟩
    change f (nonzeroDualDilation D E hD hE y)≠0
    rwa [hy]
  · intro x
    rfl

theorem fixedCuspBranch_tsum_extract {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (hcop:Pairwise (fun i k=>IsCoprime (P i) (P k)))
    (j:ι→ℕ) (e:ι→Fin 3) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ)
    (kernel:(ℕ×NonzeroDualIdeal×NonzeroDualIdeal)→ℂ) :
    let D:=reflectionExtractedDivisor P j e 1
    let E:=reflectionExtractedDivisor P j e 2
    let hD:=reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e 1
    let hE:=reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e 2
    (∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      fixedCuspBranchNumerator P hg j e cusp u phaseArray x.1 x.2.1.val x.2.2.val*kernel x)=
    ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      fixedCuspBranchNumerator P hg j e cusp u phaseArray x.1 (D*x.2.1.val) (E*x.2.2.val)*
        kernel (nonzeroDualDilation D E hD hE x) := by
  dsimp only
  apply tsum_nonzeroDualDilation
  intro x hx
  have hcoeff:fixedCuspBranchNumerator P hg j e cusp u phaseArray x.1 x.2.1.val x.2.2.val≠0:=
    (mul_ne_zero_iff.mp hx).1
  have hs:=fixedCuspBranchNumerator_support P hg hcop j e cusp u phaseArray x.1 x.2.1.val x.2.2.val hcoeff
  exact ⟨hs.1,hs.2.1⟩

end CompletedGauss

open scoped BigOperators Classical MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic CompletedGauss CubicKubota CubicJacobiGlobal ConcreteTraceCRT
open LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedConjugateCuspArray_nonzero (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedConjugateCuspArray j u m I J≠0) :
    fixedCuspArrayEligible I J ∧
      (sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0 := by
  have helig:fixedCuspArrayEligible I J:=by
    by_contra he
    apply h
    simp only [fixedConjugateCuspArray,fixedCuspArray,ite_eq_right he,star_zero]
  refine ⟨helig,?_⟩
  intro hz
  apply h
  simp only [fixedConjugateCuspArray,fixedCuspArray,ite_eq_left helig,hz,zero_div,star_zero]

lemma fixedCusp_ramified_index_pos (j:Fin 3) (hj:j≠0) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J)
    (h:(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0) : 0<m := by
  apply Nat.pos_of_ne_zero
  intro hm
  have hp:lambda∣ramifiedTraceLambda:=by
    change lambda∣paperLambda
    rw [paperLambda_eq]
    exact dvd_mul_left lambda _
  have hd:=hp.trans (sourceCuspCoefficients_ramified_divisibility j hj _ h)
  simp only [fixedCuspArrayIndex,hm,pow_zero,mul_one] at hd
  have hu:IsCoprime lambda (u:Eis):=⟨0,(↑u⁻¹:Eis),by simp⟩
  have hni:IsCoprime lambda (primaryGenerator I):=coprime_of_dvd_sub_one lambda _
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec I helig.2.1).2)
  have hnj:IsCoprime lambda (primaryGenerator J):=coprime_of_dvd_sub_one lambda _
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec J helig.2.2).2)
  exact residue_lambda_prime.not_isUnit (((hu.mul_right hni).mul_right hnj.pow_right).isUnit_of_dvd hd)

def sourcePhaseUnit (j:Fin 3) (w u:Eisˣ) : Eisˣ :=
  if j=0 then paperLambdaUnit*w^2*u else -(w^2*u*paperLambdaUnit⁻¹)

def sourcePhaseExponent (j:Fin 3) (m:ℕ) : ℕ :=
  if j=0 then m+1 else m-1

lemma paperLambdaQuotient_succ (u:Eisˣ) (m:ℕ) (n b:Eis) :
    paperLambdaQuotient ((u.val*lambda^(m+1))*n*b^3)=
      (paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3 := by
  have hp:ramifiedTraceLambda*((paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3)=
      (u.val*lambda^(m+1))*n*b^3 := by
    change paperLambda*((paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3)=_
    rw [paperLambda_eq,pow_succ]
    have hi:(paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)=1:=by simp
    calc
      _=((paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ))*(u.val*lambda^m*lambda*n*b^3):=by ring
      _=_:=by rw [hi,one_mul];ring
  have hd:ramifiedTraceLambda∣(u.val*lambda^(m+1))*n*b^3:=⟨_,hp.symm⟩
  have hn:ramifiedTraceLambda≠0:=by
    intro hz
    have he:=ramifiedEmbedding_traceLambda
    rw [hz,map_zero] at he
    exact eisLam_ne_zero he.symm
  apply mul_left_cancel₀ hn
  rw [paperLambdaQuotient_mul _ hd,hp]

theorem sourceCuspPhaseNumerator_columns (j:Fin 3) (w u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J)
    (h:(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0) :
    sourceCuspPhaseNumerator j w.val (fixedCuspArrayIndex u m I J)=
      ((sourcePhaseUnit j w u).val*lambda^(sourcePhaseExponent j m))*
        (primaryGenerator I*(primaryGenerator J)^3) := by
  by_cases hj:j=0
  · subst j
    simp only [sourceCuspPhaseNumerator,sourcePhaseUnit,sourcePhaseExponent,ite_true,
      fixedCuspArrayIndex,Units.val_mul,Units.val_pow_eq_pow_val]
    change paperLambda*w.val^2*((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)=_
    rw [paperLambda_eq,pow_succ]
    ring
  · have hm:=fixedCusp_ramified_index_pos j hj u m I J helig h
    cases m with
    | zero => omega
    | succ m =>
      simp only [sourceCuspPhaseNumerator,sourcePhaseUnit,sourcePhaseExponent,ite_eq_right hj,
        fixedCuspArrayIndex,Nat.succ_sub_succ_eq_sub,Nat.sub_zero,Units.val_neg,Units.val_mul,
        Units.val_pow_eq_pow_val]
      rw [paperLambdaQuotient_succ]
      ring

theorem fixedCuspArray_phase_brackets {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i) (exponent:ι→ℕ)
    (j:Fin 3) (w u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    fixedConjugateCuspArray j u m I J*
      (∏i,bracket (actualSextic (P i) (hg i)) (exponent i)
        (Ideal.Quotient.mk (P i) (sourceCuspPhaseNumerator j w.val (fixedCuspArrayIndex u m I J))))=
    fixedConjugateCuspArray j u m I J*
      ramifiedBranchPhase P hg exponent (sourcePhaseUnit j w u) (sourcePhaseExponent j m)*
      ∑e:ι→Fin 3,reflectedBranch P hg exponent e (primaryGenerator I) (primaryGenerator J) := by
  by_cases hz:fixedConjugateCuspArray j u m I J=0
  · rw [hz,zero_mul,zero_mul,zero_mul]
  · obtain ⟨he,hh⟩:=fixedConjugateCuspArray_nonzero j u m I J hz
    rw [sourceCuspPhaseNumerator_columns j w u m I J he hh,
      ramified_bracket_full_expansion]
    ring

end

open ActualEisensteinCubic CompletedGauss CompletedDyadic CubicKubota CubicJacobiGlobal ConcreteTraceCRT
open LocalReflectionBrackets ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

def phaseUpperUnit : Eisˣ := s.upper_unit.unit

lemma phaseUpperUnit_val : (s.phaseUpperUnit:Eis)=s.upper 0 0 := s.upper_unit.unit_spec

def modelDualNumerator (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : Eis :=
  sourceCuspPhaseNumerator s.index (s.upper 0 0) (fixedCuspArrayIndex u m I J)

theorem model_array_brackets {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (c0:Eis) (hc0:c0≠0) (d U:Eis) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    (s.amplitude u m I J*A4BadPhase c0 hc0 d U (s.modelDualNumerator u m I J))*
      (∏i,bracket (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))=
    ramifiedBranchPhase P hg j (sourcePhaseUnit s.index s.phaseUpperUnit u)
      (sourcePhaseExponent s.index m)*
      ∑e:ι→Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-d*U)) (s.modelDualNumerator u) u) m I J*
        reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J) := by
  let φ:=s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-d*U)) (s.modelDualNumerator u) u
  have hA:φ m I J*fixedConjugateCuspArray s.index u m I J=
      s.amplitude u m I J*A4BadPhase c0 hc0 d U (s.modelDualNumerator u m I J) := by
    rw [A4BadPhase_as_fixed_residue]
    exact s.fixedCuspArrayWithPhase_reflectionStaticPhase c0 hc0 _ _ u m I J
  have hbr:=fixedCuspArray_phase_brackets P hg j s.index s.phaseUpperUnit u m I J
  rw [s.phaseUpperUnit_val] at hbr
  change fixedConjugateCuspArray s.index u m I J*
    (∏i,bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))=_ at hbr
  rw [←hA]
  calc
    _=φ m I J*(fixedConjugateCuspArray s.index u m I J*
      (∏i,bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))) := by ring
    _=φ m I J*(fixedConjugateCuspArray s.index u m I J*
      ramifiedBranchPhase P hg j (sourcePhaseUnit s.index s.phaseUpperUnit u)
        (sourcePhaseExponent s.index m)*
        ∑e:ι→Fin 3,reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J)) := by rw [hbr]
    _=_ := by
      simp only [fixedCuspArrayWithPhase]
      rw [←Finset.mul_sum]
      dsimp only [φ]
      ring

end FixedCuspShape

namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
noncomputable local instance coefficientField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P
noncomputable local instance coefficientFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

def activePhase (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) : ℂ :=
  ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)

lemma activePhase_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6) :
    ‖D.activePhase hp hg j‖=1 := by
  rw [activePhase,norm_prod]
  have he (i:ι):‖(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)‖=1 := by
    rw [norm_mul,FiniteRayExpansion.norm_char_unit,one_mul]
    exact canonical_phase_norm (Ideal.span {p i}) (hg i) (hchar i) (quotientTrace (p i) (hp i))
      (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) (j i) (hj i) (D.epsilon i)
  simp only [he,Finset.prod_const_one]

lemma bracketProduct_eq (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) :
    D.bracketProduct hp hg j x=D.activePhase hp hg j*
      ∏i,bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x) := by
  exact Finset.prod_mul_distrib

def modelRowPhase (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (u:Eisˣ) (m:ℕ) : ℂ :=
  star D.fixedFactor*D.activePhase hp hg j*
    ramifiedBranchPhase (fun i=>Ideal.span {p i}) hg j
      (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)

theorem modelRowPhase_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (u:Eisˣ) (m:ℕ) : ‖D.modelRowPhase s hp hg j u m‖=1 := by
  rw [modelRowPhase,norm_mul,norm_mul,norm_star,D.fixedFactor_norm hN hr hbase,
    D.activePhase_norm hp hg hchar j hj,ramifiedBranchPhase_norm,one_mul,one_mul]

theorem model_coefficient (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    s.amplitude u m I J*
      (star D.fixedFactor*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U (s.modelDualNumerator u m I J))*
      D.bracketProduct hp hg j (s.modelDualNumerator u m I J)=
    D.modelRowPhase s hp hg j u m*
      ∑e:ι→Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U))
            (s.modelDualNumerator u) u) m I J*
        reflectedBranch (fun i=>Ideal.span {p i}) hg j e (primaryGenerator I) (primaryGenerator J) := by
  rw [D.bracketProduct_eq]
  have he:=s.model_array_brackets (fun i=>Ideal.span {p i}) hg j c0 hc0
    (D.matrix (fun _=>1) 1 1) D.U u m I J
  calc
    _=(star D.fixedFactor*D.activePhase hp hg j)*
      ((s.amplitude u m I J*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U (s.modelDualNumerator u m I J))*
        (∏i,bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk _ (s.modelDualNumerator u m I J)))) := by ring
    _=_ := by rw [he];dsimp only [modelRowPhase];ring

end ControlledStratumArithmetic

lemma fixed_stratum_kernel_scale (j:Fin 3) (c0 r:Eis) :
    27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0*r}):ℝ)^2=
      fixedCuspLevelScale j c0*(Ideal.absNorm (Ideal.span {r}):ℝ)^2 := by
  rw [←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul,mul_pow,fixedCuspLevelScale]
  ring

end CubicEisenstein

end

end OAI

end Source291

/- Original source: OAI/NumberTheory/DirichletL/Eisenstein/ReflectionFibers.lean; sha256: d585663bd9772292150668fb218adfe3ba055a71f229a6e374f9de01a0058049 -/
section Source292
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
open scoped BigOperators Classical ContDiff MatrixGroups

open ActualEisensteinCubic CompletedGauss CompletedDyadic CubicKubota CubicJacobiGlobal ConcreteTraceCRT
open LocalReflectionBrackets ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

lemma stratum_model_coefficient (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    G.shape.amplitude u m I J*
      (star D.fixedFactor*A4BadPhase G.c0 G.denominator_ne_zero (D.matrix (fun _=>1) 1 1) D.U
        (G.dualNumerator u m I J))*D.bracketProduct hp hg j (G.dualNumerator u m I J)=
    D.modelRowPhase G.shape hp hg j u m*
      ∑e:ι→Fin 3,G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u m I J*
        reflectedBranch (fun i=>Ideal.span {p i}) hg j e (primaryGenerator I) (primaryGenerator J) :=
  D.model_coefficient G.shape hp G.denominator_ne_zero hg j u m I J

theorem reflectedValue_eq_model_series (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) :
    D.reflectedValue G.shape hp G.denominator_ne_zero hg j W X=
    fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
      ∑'t:ThetaFullIndex,
        (D.modelRowPhase G.shape hp hg j t.1 t.2.1*
          ∑e:ι→Fin 3,
            G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U))
              t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
            reflectedBranch (fun i=>Ideal.span {p i}) hg j e
              (primaryGenerator t.2.2.1.val) (primaryGenerator t.2.2.2.val)) /
          ((ramifiedScale 1 completedRamifiedStep t.2.1*
            Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ)*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
            (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
            (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3) := by
  unfold ControlledStratumArithmetic.reflectedValue
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  apply tsum_congr
  intro t
  rw [fixed_stratum_kernel_scale]
  have he:=G.stratum_model_coefficient D hp hg j t.1 t.2.1 t.2.2.1.val t.2.2.2.val
  have hx:sourceCuspPhaseNumerator G.shape.index (G.shape.upper 0 0) (thetaFullFrequency t)=
      G.dualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val := by
    rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
    rfl
  rw [hx]
  let denominator:ℂ:=((ramifiedScale 1 completedRamifiedStep t.2.1*
    Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ)
  let kernel:ℂ:=CubicReflectionKernel.paperKernel (Vstar W)
    ((X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
      (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)
  change _/denominator*kernel*_=_/denominator*kernel
  calc
    _=(G.shape.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
      (star D.fixedFactor*A4BadPhase G.c0 G.denominator_ne_zero (D.matrix (fun _=>1) 1 1) D.U
        (G.dualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val))*
      D.bracketProduct hp hg j (G.dualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val))/denominator*kernel := by ring
    _=_:=by rw [he]

end FixedFourierGeometry
end

open ActualEisensteinCubic CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

abbrev CuspIdealIndex := Eisˣ×ℕ×NonzeroDualIdeal×NonzeroDualIdeal

def thetaFullToIdealIndex (t:ThetaFullIndex) : CuspIdealIndex :=
  (t.1,t.2.1,primaryCubePairToMellinIndex t.2.2)

lemma thetaFullToIdealIndex_injective : Function.Injective thetaFullToIdealIndex := by
  intro t v h
  apply Prod.ext
  · exact congrArg (fun x:CuspIdealIndex=>x.1) h
  · apply Prod.ext
    · exact congrArg (fun x:CuspIdealIndex=>x.2.1) h
    · apply primaryCubePairToMellinIndex_injective
      exact congrArg (fun x:CuspIdealIndex=>x.2.2) h

lemma fixedCuspArrayWithPhase_eligible (j:Fin 3) (u:Eisˣ)
    (φ:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayWithPhase j u φ m I J≠0) : fixedCuspArrayEligible I J := by
  by_contra he
  exact h (fixedCuspArrayWithPhase_zero j u φ m I J he)

theorem fixedCuspArrayWithPhase_tsum_primary_pairs (j:Fin 3) (u:Eisˣ)
    (φ:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (w:CompletedMellinIndex→ℂ) :
    (∑'t:CompletedMellinIndex,fixedCuspArrayWithPhase j u φ m t.1.val t.2.val*w t)=
    ∑'t:ThetaPrimaryCubePair,fixedCuspArrayWithPhase j u φ m t.1.val t.2.val*
      w (primaryCubePairToMellinIndex t) := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun t=>primaryCubePairToMellinIndex t.val)
  · exact primaryCubePairToMellinIndex_injective.comp Subtype.val_injective
  · intro t ht
    change fixedCuspArrayWithPhase j u φ m t.1.val t.2.val*w t≠0 at ht
    have ha:fixedCuspArrayWithPhase j u φ m t.1.val t.2.val≠0:=by
      intro hz
      exact ht (by rw [hz,zero_mul])
    obtain ⟨hs,hI,hJ⟩:=fixedCuspArrayWithPhase_eligible j u φ m t.1.val t.2.val ha
    let v:ThetaPrimaryCubePair:=(⟨t.1.val,hs,hI⟩,⟨t.2.val,hJ⟩)
    have hv:primaryCubePairToMellinIndex v=t:=Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
    refine ⟨⟨v,?_⟩,hv⟩
    change fixedCuspArrayWithPhase j u φ m (primaryCubePairToMellinIndex v).1.val
      (primaryCubePairToMellinIndex v).2.val*w (primaryCubePairToMellinIndex v)≠0
    rwa [hv]
  · intro t
    rfl

theorem fixedCuspArrayWithPhase_tsum_full_index
    (j:Eisˣ→Fin 3) (φ:Eisˣ→ℕ→Ideal Eis→Ideal Eis→ℂ) (w:CuspIdealIndex→ℂ) :
    (∑'t:CuspIdealIndex,fixedCuspArrayWithPhase (j t.1) t.1 (φ t.1)
      t.2.1 t.2.2.1.val t.2.2.2.val*w t)=
    ∑'t:ThetaFullIndex,fixedCuspArrayWithPhase (j t.1) t.1 (φ t.1)
      t.2.1 t.2.2.1.val t.2.2.2.val*w (thetaFullToIdealIndex t) := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun t=>thetaFullToIdealIndex t.val)
  · exact thetaFullToIdealIndex_injective.comp Subtype.val_injective
  · intro t ht
    change fixedCuspArrayWithPhase (j t.1) t.1 (φ t.1) t.2.1 t.2.2.1.val t.2.2.2.val*w t≠0 at ht
    have ha:fixedCuspArrayWithPhase (j t.1) t.1 (φ t.1) t.2.1 t.2.2.1.val t.2.2.2.val≠0:=by
      intro hz
      exact ht (by rw [hz,zero_mul])
    obtain ⟨hs,hI,hJ⟩:=fixedCuspArrayWithPhase_eligible _ _ _ _ _ _ ha
    let v:ThetaFullIndex:=(t.1,t.2.1,⟨t.2.2.1.val,hs,hI⟩,⟨t.2.2.2.val,hJ⟩)
    have hv:thetaFullToIdealIndex v=t:=
      Prod.ext rfl (Prod.ext rfl (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)))
    refine ⟨⟨v,?_⟩,hv⟩
    change fixedCuspArrayWithPhase (j (thetaFullToIdealIndex v).1) (thetaFullToIdealIndex v).1
      (φ (thetaFullToIdealIndex v).1) (thetaFullToIdealIndex v).2.1
      (thetaFullToIdealIndex v).2.2.1.val (thetaFullToIdealIndex v).2.2.2.val*
      w (thetaFullToIdealIndex v)≠0
    rwa [hv]
  · intro t
    rfl

end CubicEisenstein

open scoped Classical BigOperators

namespace CompletedGauss
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def mandatoryActiveEquiv (R:Finset ι) :
    {A:Finset ι // R⊆A}≃Finset {i:ι // i∉R} where
  toFun A:=A.val.subtype (fun i=>i∉R)
  invFun B:=⟨R∪B.image Subtype.val,Finset.subset_union_left⟩
  left_inv A:=by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_union,Finset.mem_image,Finset.mem_subtype]
    constructor
    · rintro (hi|⟨j,hj,rfl⟩)
      · exact A.property hi
      · exact hj
    · intro hi
      by_cases hr:i∈R
      · exact Or.inl hr
      · exact Or.inr ⟨⟨i,hr⟩,hi,rfl⟩
  right_inv B:=by
    ext i
    simp only [Finset.mem_subtype,Finset.mem_union,Finset.mem_image]
    constructor
    · rintro (hi|⟨j,hj,hji⟩)
      · exact False.elim (i.property hi)
      · have he:j=i:=Subtype.ext hji
        simpa only [he] using hj
    · intro hi
      exact Or.inr ⟨i,hi,rfl⟩

lemma sum_mandatory_active {V:Type*} [AddCommMonoid V]
    (R:Finset ι) (F:Finset ι→V) (hz:∀A,¬R⊆A→F A=0) :
    (∑A:Finset ι,F A)=
      ∑B:Finset {i:ι // i∉R},F (R∪B.image Subtype.val) := by
  calc
    _=∑A:Finset ι,if R⊆A then F A else 0:=by
      apply Finset.sum_congr rfl
      intro A hA
      by_cases h:R⊆A
      · simp only [ite_eq_left h]
      · simp only [ite_eq_right h,hz A h]
    _=∑A:{A:Finset ι // R⊆A},F A.val:=by
      rw [←Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (fun A:Finset ι=>R⊆A)) (by simp) F
    _=_:=by
      apply Fintype.sum_equiv (mandatoryActiveEquiv R)
      intro A
      exact congrArg F (congrArg Subtype.val ((mandatoryActiveEquiv R).left_inv A)).symm

theorem inactive_weight_mandatory_active (R:Finset ι) (z:ι→ℂ)
    (hz:∀i∈R,z i=0) (F:Finset ι→ℂ) :
    (∑A:Finset ι,(∏i∈(Finset.univ:Finset ι)\A,z i)*F A)=
      ∑B:Finset {i:ι // i∉R},
        (∏i∈(Finset.univ:Finset ι)\(R∪B.image Subtype.val),z i)*
          F (R∪B.image Subtype.val) := by
  apply sum_mandatory_active R
  intro A hA
  have hex:∃i∈R,i∉A:=by
    by_contra! hn
    exact hA hn
  obtain ⟨i,hi,hni⟩:=hex
  have hm:i∈(Finset.univ:Finset ι)\A:=by simp [hni]
  rw [Finset.prod_eq_zero hm (hz i hi),zero_mul]

lemma inactive_product_complement (R:Finset ι) (z:ι→ℂ)
    (B:Finset {i:ι // i∉R}) :
    (∏i∈(Finset.univ:Finset ι)\(R∪B.image Subtype.val),z i)=
      ∏i∈(Finset.univ:Finset {i:ι // i∉R})\B,z i.val := by
  symm
  apply Finset.prod_bij (fun i _=>i.val)
  · intro i hi
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and] at hi ⊢
    intro hmem
    rcases Finset.mem_union.mp hmem with hr|hb
    · exact i.property hr
    · obtain ⟨j,hj,hji⟩:=Finset.mem_image.mp hb
      exact hi ((Subtype.ext hji) ▸ hj)
  · intro i hi j hj he
    exact Subtype.ext he
  · intro i hi
    have hnot:i∉R∪B.image Subtype.val:=(Finset.mem_sdiff.mp hi).2
    have hr:i∉R:=fun h=>hnot (Finset.mem_union_left _ h)
    refine ⟨⟨i,hr⟩,?_,rfl⟩
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
    intro hb
    exact hnot (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨i,hr⟩,hb,rfl⟩))
  · intro i hi
    rfl

theorem inactive_weight_optional_active (R:Finset ι) (z:ι→ℂ)
    (hz:∀i∈R,z i=0) (F:Finset ι→ℂ) :
    (∑A:Finset ι,(∏i∈(Finset.univ:Finset ι)\A,z i)*F A)=
      ∑B:Finset {i:ι // i∉R},
        (∏i∈(Finset.univ:Finset {i:ι // i∉R})\B,z i.val)*
          F (R∪B.image Subtype.val) := by
  rw [inactive_weight_mandatory_active R z hz F]
  apply Finset.sum_congr rfl
  intro B hB
  rw [inactive_product_complement]

end CompletedGauss

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum
local notation "Eis" => ActualEisensteinCubic.O

lemma excluded_prime_dvd_row_mask (q:ℕ) (m:Eis) (F P:Ideal Eis)
    (hP:P∈reflectionExcludedPrimes q) :
    P∣Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F := by
  apply dvd_mul_of_dvd_left
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.span_le.mpr
  exact Set.singleton_subset_iff.mpr (P.mul_mem_left m (excludedGenerator_mem _ hP))

lemma residual_prime_not_excluded (q:ℕ) (m:Eis) (F I P:Ideal Eis) (hP:Prime P)
    (hres:P∣rowResidualPart I (Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F)) :
    P∉reflectionExcludedPrimes q := by
  intro hmem
  have hn:¬P∣Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F:=
    ((prime_dvd_rowResidualPart_iff _ _ P hP).mp hres).2
  exact hn (excluded_prime_dvd_row_mask q m F P hmem)

lemma residual_coprime_fixed_conductor (q:ℕ) (hq:q≠0) (m:Eis) (F I:Ideal Eis) :
    IsCoprime (Ideal.span {reflectionConductor q})
      (rowResidualPart I (Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F)) := by
  let Q:=Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))
    (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp
  apply Finset.disjoint_left.mpr
  intro P hfixed hres
  have hp:Prime P:=support_prime hfixed
  have hd:P∣Ideal.span {reflectionConductor q}:=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hfixed)
  have hr:P∣rowResidualPart I Q:=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hres)
  exact residual_prime_not_excluded q m F I P hp hr (reflectionConductor_prime_mem q hq P hp hd)

end CanonicalRowCompletion

open scoped BigOperators Classical

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

def representativeRowFiber (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) : Finset (Ideal Eis) :=
  completedRowFiber rows Q (rowPowerfulPart I) (rowMaskPart I Q)

def reconstructFiberRow (I Q k:Ideal Eis) : Ideal Eis :=
  rowPowerfulPart I*rowMaskPart I Q*k

lemma reconstructFiberRow_ne_zero (I Q k:Ideal Eis) (hk:k≠0) : reconstructFiberRow I Q k≠0 :=
  mul_ne_zero (mul_ne_zero (rowPowerfulPart_ne_zero I)
    (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)) hk

lemma reconstructFiberRow_of_original (rows:Finset (Ideal Eis)) (I Q J:Ideal Eis)
    (hJ:J∈representativeRowFiber rows I Q) (hJ0:J≠0) :
    reconstructFiberRow I Q (rowResidualPart J Q)=J := by
  obtain ⟨_,hA,hT⟩:=Finset.mem_filter.mp hJ
  rw [reconstructFiberRow,←hA,←hT]
  exact row_powerful_mask_residual_product J Q hJ0

lemma residual_reconstructFiberRow (rows:Finset (Ideal Eis)) (I Q k:Ideal Eis)
    (hk:k≠0) (hmem:reconstructFiberRow I Q k∈representativeRowFiber rows I Q) :
    rowResidualPart (reconstructFiberRow I Q k) Q=k := by
  have he:=reconstructFiberRow_of_original rows I Q _ hmem (reconstructFiberRow_ne_zero I Q k hk)
  exact mul_left_cancel₀ (mul_ne_zero (rowPowerfulPart_ne_zero I)
    (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)) he

lemma representativeRowFiber_injective (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (hrows:∀J∈rows,J≠0) :
    Set.InjOn (fun J=>rowResidualPart J Q) (representativeRowFiber rows I Q) :=
  rowResidualPart_injective_on_fiber rows Q (rowPowerfulPart I) (rowMaskPart I Q) hrows

def fiberResidualIndex (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (J:representativeRowFiber rows I Q) : idealRange (completedResidualScale K I Q) :=
  ⟨rowResidualPart J.val Q,completedRowFiber_residual_range rows Q
    (rowPowerfulPart I) (rowMaskPart I Q) hbad K hrows J.val J.property⟩

lemma fiberResidualIndex_injective (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K) :
    Function.Injective (fiberResidualIndex rows I Q K hbad hrows) := by
  intro J lengthScale he
  apply Subtype.ext
  apply representativeRowFiber_injective rows I Q (fun J hJ=>(hrows J hJ).1) J.property lengthScale.property
  exact congrArg Subtype.val he

def extendFiberRowScalar {α:Type*} (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (k:idealRange (completedResidualScale K I Q)) : ℂ :=
  if h:reconstructFiberRow I Q k.val∈representativeRowFiber rows I Q then
    scalar a ⟨reconstructFiberRow I Q k.val,h⟩ else 0

lemma extendFiberRowScalar_norm_le_one {α:Type*} (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (hscalar:∀a J,‖scalar a J‖≤1)
    (a:α) (k:idealRange (completedResidualScale K I Q)) :
    ‖extendFiberRowScalar rows I Q K scalar a k‖≤1 := by
  unfold extendFiberRowScalar
  split_ifs
  · exact hscalar _ _
  · simp

lemma extendFiberRowScalar_zero {α:Type*} (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (k:idealRange (completedResidualScale K I Q))
    (hk:reconstructFiberRow I Q k.val∉representativeRowFiber rows I Q) :
    extendFiberRowScalar rows I Q K scalar a k=0 := by
  simp only [extendFiberRowScalar,dite_eq_right hk]

lemma extendFiberRowScalar_at_original {α:Type*} (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (J:representativeRowFiber rows I Q) :
    extendFiberRowScalar rows I Q K scalar a (fiberResidualIndex rows I Q K hbad hrows J)=scalar a J := by
  have hJ0:J.val≠0:=(hrows J.val (Finset.mem_filter.mp J.property).1).1
  have he:=reconstructFiberRow_of_original rows I Q J.val J.property hJ0
  simp only [extendFiberRowScalar,fiberResidualIndex,he,dite_eq_left J.property]

def extendSelectedFiberRowScalar {α τ:Type*} [DecidableEq τ]
    (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (t:τ) (a:α)
    (k:idealRange (completedResidualScale K I Q)) : ℂ :=
  extendFiberRowScalar rows I Q K (fun a J=>if selector a J=t then scalar a J else 0) a k

lemma extendSelectedFiberRowScalar_norm_le_one {α τ:Type*} [DecidableEq τ]
    (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (hscalar:∀a J,‖scalar a J‖≤1)
    (t:τ) (a:α) (k:idealRange (completedResidualScale K I Q)) :
    ‖extendSelectedFiberRowScalar rows I Q K selector scalar t a k‖≤1 := by
  apply extendFiberRowScalar_norm_le_one
  intro a J
  split_ifs
  · exact hscalar a J
  · simp

lemma extendSelectedFiberRowScalar_at_original {α τ:Type*} [DecidableEq τ]
    (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (t:τ) (a:α)
    (J:representativeRowFiber rows I Q) :
    extendSelectedFiberRowScalar rows I Q K selector scalar t a
      (fiberResidualIndex rows I Q K hbad hrows J)=
        if selector a J=t then scalar a J else 0 :=
  extendFiberRowScalar_at_original rows I Q K hbad hrows _ a J

lemma sum_extendSelectedFiberRowScalar {α τ:Type*} [Fintype τ] [DecidableEq τ]
    (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (k:idealRange (completedResidualScale K I Q)) :
    (∑t:τ,extendSelectedFiberRowScalar rows I Q K selector scalar t a k)=
      extendFiberRowScalar rows I Q K scalar a k := by
  by_cases hk:reconstructFiberRow I Q k.val∈representativeRowFiber rows I Q
  · simp [extendSelectedFiberRowScalar,extendFiberRowScalar,hk]
  · simp only [extendSelectedFiberRowScalar,extendFiberRowScalar,dite_eq_right hk,Finset.sum_const_zero]

end

open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

theorem reconstructFiberRow_valid_iff (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (k:idealRange (completedResidualScale K I Q)) :
    reconstructFiberRow I Q k.val∈representativeRowFiber rows I Q ↔
      ∃J:representativeRowFiber rows I Q,fiberResidualIndex rows I Q K hbad hrows J=k := by
  constructor
  · intro hk
    refine ⟨⟨reconstructFiberRow I Q k.val,hk⟩,?_⟩
    apply Subtype.ext
    exact residual_reconstructFiberRow rows I Q k.val (mem_idealRange.mp k.property).1.1 hk
  · rintro ⟨J,rfl⟩
    have hJ0:J.val≠0:=(hrows J.val (Finset.mem_filter.mp J.property).1).1
    change reconstructFiberRow I Q (rowResidualPart J.val Q)∈representativeRowFiber rows I Q
    rw [reconstructFiberRow_of_original rows I Q J.val J.property hJ0]
    exact J.property

lemma representativeFiber_parts (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (J:representativeRowFiber rows I Q) :
    rowPowerfulPart J.val=rowPowerfulPart I ∧ rowMaskPart J.val Q=rowMaskPart I Q :=
  (Finset.mem_filter.mp J.property).2

lemma representativeFiber_pool (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q) :
    completedReflectionPool J.val Q=completedReflectionPool I Q := by
  have hs:=representativeFiber_parts rows I Q J
  exact completedReflectionPool_eq_on_fiber J.val I Q
    (hrows J.val (Finset.mem_filter.mp J.property).1) hI hQ hs.1 hs.2

lemma representativeFiber_filtered_pool (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q) (free:Ideal Eis → Prop) [DecidablePred free] :
    (completedReflectionPool J.val Q).filter free=(completedReflectionPool I Q).filter free := by
  rw [representativeFiber_pool rows I Q hI hQ hrows J]

lemma representativeFiber_exponent (rows:Finset (Ideal Eis)) (I F Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q) (P:completedReflectionPool I Q) :
    completedLocalExponent J.val F P.val=completedLocalExponent I F P.val := by
  have hs:=representativeFiber_parts rows I Q J
  exact (completedReflectionPool_exponent_eq I J.val F Q hI
    (hrows J.val (Finset.mem_filter.mp J.property).1) hQ hs.1.symm hs.2.symm P).symm

lemma representativeFiber_extractedDivisor {ι:Type*} [Fintype ι]
    (rows:Finset (Ideal Eis)) (I F Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q)
    (P:ι → Ideal Eis) (hP:∀i,P i∈completedReflectionPool I Q) (e:ι → Fin 3) (v:Fin 3) :
    reflectionExtractedDivisor P (fun i=>completedLocalExponent J.val F (P i)) e v=
      reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e v := by
  have he:(fun i=>completedLocalExponent J.val F (P i))=
      (fun i=>completedLocalExponent I F (P i)):=by
    funext i
    exact representativeFiber_exponent rows I F Q hI hQ hrows J ⟨P i,hP i⟩
  rw [he]

lemma representativeFiber_residualScale (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (J:representativeRowFiber rows I Q) (K:ℝ) :
    completedResidualScale K J.val Q=completedResidualScale K I Q := by
  have hs:=representativeFiber_parts rows I Q J
  exact completedResidualScale_eq_on_fiber K J.val I Q hs.1 hs.2

lemma representativeFiber_branchScale {ι:Type*} [Fintype ι]
    (rows:Finset (Ideal Eis)) (I F Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q)
    (P:ι → Ideal Eis) (hP:∀i,P i∈completedReflectionPool I Q) (e:ι → Fin 3) (K X:ℝ) :
    completedBranchScale K X J.val F Q P e=completedBranchScale K X I F Q P e := by
  have hs:=representativeFiber_parts rows I Q J
  exact (completedBranchScale_eq_on_fiber K X I J.val F Q hI
    (hrows J.val (Finset.mem_filter.mp J.property).1) hQ hs.1.symm hs.2.symm P hP e).symm

end CompletedGauss

open scoped Classical BigOperators

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

def fixedRayFiberFromRows (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1) :
    ReflectedFiberData (fixedReflectionRayCount c hc) (fixedCuspLevelBound c) K I F Q :=
  fixedRayFiber c hc I F Q Q0 hI hQ K (fun _=>1) (by intro x;simp)
    (fun x m=>extendFiberRowScalar rows I Q K scalar (x,m))
    (fun x m=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar (x,m))

lemma fixedRayFiberFromRows_rowPhase (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (J:representativeRowFiber rows I Q) (r:FixedReflectionRay c hc)
    (e:pool I Q Q0→Fin 6) (i:ℕ×ℕ×ℕ) :
    ((fixedRayFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).branch
      (fixedReflectionRayEquiv c hc r,e)).rowPhase i
        (fiberResidualIndex rows I Q K hbad hrows J)=scalar ((r,e),i.1) J := by
  change extendFiberRowScalar rows I Q K scalar
    ((((fixedReflectionRayEquiv c hc).symm (fixedReflectionRayEquiv c hc r)),e),i.1)
    (fiberResidualIndex rows I Q K hbad hrows J)=_
  rw [Equiv.symm_apply_apply]
  exact extendFiberRowScalar_at_original rows I Q K hbad hrows scalar ((r,e),i.1) J

lemma fixedRayFiberFromRows_weight (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (r:FixedReflectionRay c hc) (e:pool I Q Q0→Fin 6) :
    (fixedRayFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).weight
      (fixedReflectionRayEquiv c hc r,e)=reflectionSixInactiveWeight I F Q Q0 e := by
  change 1*reflectionSixInactiveWeight I F Q Q0 e=_
  exact one_mul _

end CompletedGauss.FreeReflection

end

end OAI

end Source292

/- Original source: OAI/NumberTheory/DirichletL/RowCompletion/ControlledPrimeStrata.lean; sha256: 569a971442b37e2f6d7e8ea50a978c07c6196393349a75d229dbe6c47370f550 -/
section Source293
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
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def freePrimaryPrime (I Q:Ideal Eis) (P:FreePrimeIndex I Q) : Eis := primaryPrime P.val.val

lemma freePrimaryPrime_ne_zero (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    freePrimaryPrime I Q P≠0 :=
  primaryPrime_ne_zero P.val.val
    (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

lemma freePrimaryPrime_span (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    Ideal.span {freePrimaryPrime I Q P}=P.val.val :=
  (primaryPrime_spec P.val.val (freePrimaryPrime_ne_zero I Q hI P)).2.2.1

lemma freePrimaryPrime_primary (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    lambda^2∣freePrimaryPrime I Q P-1 :=
  (primaryPrime_spec P.val.val (freePrimaryPrime_ne_zero I Q hI P)).2.2.2

lemma freePrimaryPrime_maximal (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    (Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal := by
  rw [freePrimaryPrime_span I Q hI P]
  infer_instance

lemma freePrimaryPrime_good (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    lambda∉(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis) := by
  rw [freePrimaryPrime_span I Q hI P]
  exact (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

lemma freePrimaryPrime_odd (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    ringChar (Eis⧸Ideal.span {freePrimaryPrime I Q P})≠2 := by
  rw [freePrimaryPrime_span I Q hI P]
  exact (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.2

lemma freePrimaryPrime_injective (I Q:Ideal Eis) (hI:Supported I) :
    Function.Injective (freePrimaryPrime I Q) := by
  intro P R he
  have hh:=congrArg (fun x:Eis=>(Ideal.span {x}:Ideal Eis)) he
  rw [freePrimaryPrime_span I Q hI P,freePrimaryPrime_span I Q hI R] at hh
  exact Subtype.ext (Subtype.ext hh)

lemma freePrimaryPrime_coprime (I Q:Ideal Eis) (hI:Supported I) :
    Pairwise (fun P R:FreePrimeIndex I Q =>
      IsCoprime (Ideal.span {freePrimaryPrime I Q P}:Ideal Eis) (Ideal.span {freePrimaryPrime I Q R})) := by
  intro P R hPR
  rw [freePrimaryPrime_span I Q hI P,freePrimaryPrime_span I Q hI R]
  exact freePrimeIndex_pairwise_coprime I Q hPR

lemma freePrimaryPrime_coprime_fixed (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    IsCoprime Q (Ideal.span {freePrimaryPrime I Q P}:Ideal Eis) := by
  rw [freePrimaryPrime_span I Q hI P]
  exact freePrimeIndex_coprime I Q P

lemma freePrimaryPrime_product_span (I Q:Ideal Eis) (hI:Supported I) :
    Ideal.span {∏P:FreePrimeIndex I Q,freePrimaryPrime I Q P}=
      ∏P:FreePrimeIndex I Q,P.val.val := by
  rw [FiniteGaussPhase.span_finset_prod]
  apply Finset.prod_congr rfl
  intro P _
  exact freePrimaryPrime_span I Q hI P

lemma freePrimaryPrime_product_coprime_fixed (I Q:Ideal Eis) (hI:Supported I) :
    IsCoprime Q (Ideal.span {∏P:FreePrimeIndex I Q,freePrimaryPrime I Q P}:Ideal Eis) := by
  rw [freePrimaryPrime_product_span I Q hI]
  exact freePrimeProduct_coprime I Q

lemma actualSextic_power_transport (P R:Ideal Eis) [P.IsMaximal] [R.IsMaximal]
    (hP:lambda∉P) (hR:lambda∉R) (he:P=R) (j:ℕ) (n:Eis) :
    (actualSextic P hP^j) (Ideal.Quotient.mk P n)=
      (actualSextic R hR^j) (Ideal.Quotient.mk R n) := by
  subst R
  rfl

theorem freePrimeRow_eq_primary_family (I Q:Ideal Eis) (hI:Supported I) (n:Eis) :
    letI : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
      freePrimaryPrime_maximal I Q hI
    freePrimeRow I hI Q n=
      finiteSexticRow (fun P:FreePrimeIndex I Q=>Ideal.span {freePrimaryPrime I Q P})
        (freePrimaryPrime_good I Q hI)
        (fun P=>(normalizedFactors I).count P.val.val%6) n := by
  let : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal I Q hI
  unfold freePrimeRow finiteSexticRow
  apply Finset.prod_congr rfl
  intro P _
  exact actualSextic_power_transport _ _ _ _ (freePrimaryPrime_span I Q hI P).symm _ n

end CanonicalRowCompletion

namespace FixedRayActiveSet

theorem fourier_inversion_by_active_set {ι:Type*} [Fintype ι]
    (F:ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (ψ:∀i,AddChar (F i) ℂ) (hψ:∀i,(ψ i).IsPrimitive)
    (φ:∀i,F i→ℂ) (x:∀i,F i) :
    (∏i,φ i (x i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0)*
        (∑v:∀i:A,(F i.val)ˣ,
          (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
            (∏i:A,ψ i.val ((v i:F i.val)*x i.val))) := by
  let f:=fun i (a:F i)=>CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) a*ψ i (a*x i)
  have he: (∑h:∀i,F i,∏i,f i (h i))=∏i,φ i (x i):=by
    rw [←Fintype.prod_sum]
    apply Finset.prod_congr rfl
    intro i hi
    exact CubicEisenstein.finiteAdditiveFourier_inversion (ψ i) (hψ i) (φ i) (x i)
  rw [←he,sum_by_active_strata]
  apply Finset.sum_congr rfl
  intro A hA
  rw [sum_active_stratum]
  have hz:(∏i∈(Finset.univ:Finset ι)\A,f i 0)=
      ∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0:=by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [f,zero_mul,AddChar.map_zero_eq_one,mul_one]
  rw [hz,mul_comm]
  congr 1
  rw [show (∑v:∀i:A,(F i.val)ˣ,
      (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
        (∏i:A,ψ i.val ((v i:F i.val)*x i.val)))=
      ∑v:∀i:A,(F i.val)ˣ,∏i:A,f i.val (v i) by
    apply Finset.sum_congr rfl
    intro v hv
    exact (Finset.prod_mul_distrib).symm]
  calc
    _=∏i:A,∑u:(F i.val)ˣ,f i.val (u:F i.val):=
      (Finset.prod_coe_sort A (fun i=>∑u:(F i)ˣ,f i (u:F i))).symm
    _=_:=Fintype.prod_sum (fun (i:A) (u:(F i.val)ˣ)=>f i.val (u:F i.val))

end FixedRayActiveSet

open scoped BigOperators Classical ContDiff

namespace CubicEisenstein

section
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem completedBesselProfile_of_finite_cusp_multiplier
    (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    {ι:Type*} [Fintype ι] (d:ι→SourceCuspDatum) (w:ι→ℂ)
    (hmult:∀n:Eis,(∑i,w i*ShortDraftTrace.breveE (-cuspFrequency n*(d i).point))=fixedThetaTwist Ψ n)
    (v:ℝ) (hv:0<v) :
    completedBesselProfile Ψ thetaBesselScale v=
      thetaDerivativeScalar⁻¹*∑i,w i*cuspBarProfile cubicSourceConjugateFunction (d i).point v := by
  have hf:=finiteConjugateSource_wirtingerBar (fun i=>(d i).point) w v hv 0
  simp only [hmult] at hf
  have hcseries:=traceTwistedConjugateSource_wirtingerBar c hc (fixedThetaQuotient Ψ c) v hv 0
  simp only [fixedThetaQuotient_mk Ψ Q hperiod c hcQ] at hcseries
  have he:(∑i,w i*cuspBarProfile cubicSourceConjugateFunction (d i).point v)=
      thetaDerivativeScalar*completedBesselProfile Ψ thetaBesselScale v:=by
    rw [←finiteConjugateSource_wirtingerBar_sum (fun i=>(d i).point) w v hv]
    calc
      _=horizontalWirtingerBar (traceTwistedConjugateSource c hc (fixedThetaQuotient Ψ c) v hv) 0:=
        hf.trans hcseries.symm
      _=_:=thetaTwistedSource_wirtingerBar_eq_completedBesselProfile Ψ Q hperiod c hc hcQ v hv
  rw [he,←mul_assoc,inv_mul_cancel₀ thetaDerivativeScalar_ne_zero,one_mul]

theorem completedT_of_finite_cusp_multiplier
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    {ι:Type*} [Fintype ι] (d:ι→SourceCuspDatum) (w:ι→ℂ)
    (hmult:∀n:Eis,(∑i,w i*ShortDraftTrace.breveE (-cuspFrequency n*(d i).point))=fixedThetaTwist Ψ n)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*∑i,w i*(d i).smoothedKernel W X := by
  have hFG (v:ℝ) (hv:0<v) : completedBesselProfile Ψ thetaBesselScale v=
      ∑i,(thetaDerivativeScalar⁻¹*w i)*cuspBarProfile cubicSourceConjugateFunction (d i).point v:=by
    rw [completedBesselProfile_of_finite_cusp_multiplier Ψ Q hperiod c hc hcQ d w hmult v hv,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [completedT_of_finite_cusp_profiles Ψ hΨ Q hperiod c hc hcQ d
    (fun i=>thetaDerivativeScalar⁻¹*w i) hFG W lo hi hlo hsupp hW X hX,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end

open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma theta_lifted_phase (c:Eis) (hc:c≠0) (lift n:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency n*(eisLam^2*eisEmbedding lift/eisEmbedding c))=
      quotientTrace c hc (Ideal.Quotient.mk _ lift*Ideal.Quotient.mk _ n) := by
  rw [←map_mul]
  simp only [quotientTrace,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  congr 1
  unfold cuspFrequency
  rw [map_mul]
  have hc0:=eisEmbedding_ne_zero hc
  have hl:=eisLam_ne_zero
  field_simp
  linear_combination -(eisEmbedding n*eisEmbedding lift)*TraceLambdaPhase.eisLam_sq

lemma breveE_finset_sum {ι:Type*} (s:Finset ι) (z:ι→ℂ) :
    ShortDraftTrace.breveE (∑i∈s,z i)=∏i∈s,ShortDraftTrace.breveE (z i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty,AddChar.map_zero_eq_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,AddChar.map_add_eq_mul,ih]

lemma ControlledStratumArithmetic.datum_fourier_phase {ι:Type*} [Fintype ι]
    {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
    (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (n:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency n*(D.datum hN hr hbase s hp hc0 v).point)=
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        ∏i,quotientTrace (p i) (hp i) ((v i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ n) := by
  rw [D.datum_point]
  have he:-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i))=
      -cuspFrequency n*(eisEmbedding a0/eisEmbedding c0)+
        ∑i,-cuspFrequency n*(eisLam^2*eisEmbedding (D.lift v i)/eisEmbedding (p i)):=by
    simp only [Finset.mul_sum,neg_mul,mul_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he,AddChar.map_add_eq_mul,breveE_finset_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [theta_lifted_phase,D.lift_residue]

end CubicEisenstein

open scoped BigOperators Classical ContDiff

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def unextractedCuspCoefficient {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  σ m*η m I J*reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J)/
    ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ):ℝ):ℂ)

lemma unextractedCuspCoefficient_norm {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (hρ:0<ρ) (hq:1≤q)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (hη:∀m I J,‖η m I J‖≤1) (hσ:∀m,‖σ m‖≤1)
    (m:ℕ) (I J:NonzeroDualIdeal) :
    ‖unextractedCuspCoefficient P hg j e ρ q η σ m I.val J.val‖≤
      (Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
        Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
        Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ))/ρ := by
  let C:ℝ:=Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
    Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
    Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)
  have hC:0≤C:=by dsimp only [C];positivity
  have hr:0<ramifiedScale ρ q m:=ramifiedScale_pos ρ q hρ (lt_of_lt_of_le zero_lt_one hq) m
  have hn:1≤(Ideal.absNorm I.val:ℝ):=norm_at_least_one I.val I.property
  have hb:1≤(Ideal.absNorm J.val:ℝ):=norm_at_least_one J.val J.property
  have hs:1≤Real.sqrt (Ideal.absNorm I.val:ℝ):=by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    simpa using hn
  have hd:ρ≤ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ) := by
    calc
      ρ≤ramifiedScale ρ q m:=le_mul_of_one_le_right hρ.le (one_le_pow₀ hq)
      _≤ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I.val:ℝ):=le_mul_of_one_le_right hr.le hs
      _≤_:=le_mul_of_one_le_right (by positivity) hb
  have hp:‖σ m‖*‖η m I.val J.val‖≤1:=(mul_le_of_le_one_left (norm_nonneg _)
    (hσ m)).trans (hη m I.val J.val)
  have hh:‖σ m‖*‖η m I.val J.val‖*
      ‖reflectedBranch P hg j e (primaryGenerator I.val) (primaryGenerator J.val)‖≤C := by
    have ht:=mul_le_mul hp (reflectedBranch_norm_bound P hg j e (primaryGenerator I.val) (primaryGenerator J.val))
      (norm_nonneg _) zero_le_one
    simpa only [one_mul] using ht
  rw [unextractedCuspCoefficient,norm_div,norm_mul,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  exact (div_le_div_of_nonneg_right hh (by positivity)).trans
    (div_le_div_of_nonneg_left hC hρ hd)

theorem unextractedCuspCoefficient_summable {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (hρ:0<ρ) (hq:1<q)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (hη:∀m I J,‖η m I J‖≤1) (hσ:∀m,‖σ m‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (scale:ℝ) (hscale:0<scale) :
    Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ‖rawDualKernelTerm (Vstar W) scale ρ q (unextractedCuspCoefficient P hg j e ρ q η σ) x‖) := by
  apply rawDualKernelTerm_summable_norm (Vstar W) a b ha (Vstar_support W a b hsupp)
    (Vstar_contDiff W a b ha hsupp hW) scale ρ q
    ((Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ))/ρ)
    hscale hρ hq (by positivity)
  exact unextractedCuspCoefficient_norm P hg j e ρ q hρ hq.le η σ hη hσ

end CompletedGauss

namespace CubicEisenstein

section
open ActualEisensteinCubic CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

def stratumBranchTerm (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (u:Eisˣ) (e:ι→Fin 3) (W:ℝ→ℂ) (X:ℝ)
    (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℂ :=
  rawDualKernelTerm (Vstar W) (X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))
    1 completedRamifiedStep
    (unextractedCuspCoefficient (fun i=>Ideal.span {p i}) hg j e 1 completedRamifiedStep
      (G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u)
      (D.modelRowPhase G.shape hp hg j u)) x

theorem stratumBranchTerm_summable (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (u:Eisˣ) (e:ι→Fin 3) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hsupp:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>‖G.stratumBranchTerm D hp hg j u e W X x‖) := by
  have hn:0<(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz=>
      (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
        (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hlevel:=G.levelScale_pos
  apply unextractedCuspCoefficient_summable (fun i=>Ideal.span {p i}) hg j e 1 completedRamifiedStep
    (by norm_num) completedRamifiedStep_gt_one _ _ (G.array_norm_le_one _ u)
    (fun m=>(D.modelRowPhase_norm hN hr G.primary G.shape hp hg hchar j hj u m).le)
    W a b ha hsupp hW _ (by positivity)

theorem stratumBranchTerm_fubini (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑'t:CuspIdealIndex,∑e:ι→Fin 3,G.stratumBranchTerm D hp hg j t.1 e W X t.2)=
      ∑'u:Eisˣ,∑e:ι→Fin 3,∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
        G.stratumBranchTerm D hp hg j u e W X x := by
  let:Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  have hs:=G.stratumBranchTerm_summable D hN hr hp hg hchar j hj
    (W:=W) (a:=a) (b:=b) (ha:=ha) (hsupp:=hsupp) (hW:=hW) (X:=X) (hX:=hX)
  have hu (u:Eisˣ):Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ‖∑e:ι→Fin 3,G.stratumBranchTerm D hp hg j u e W X x‖) := by
    have hb:Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ∑e:ι→Fin 3,‖G.stratumBranchTerm D hp hg j u e W X x‖) :=
      (hasSum_sum (fun e _=>(hs u e).hasSum)).summable
    exact hb.of_nonneg_of_le (fun _=>norm_nonneg _) (fun _=>norm_sum_le _ _)
  have hall:Summable (fun t:CuspIdealIndex=>
      ‖∑e:ι→Fin 3,G.stratumBranchTerm D hp hg j t.1 e W X t.2‖) :=
    (summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr ⟨hu,Summable.of_finite⟩
  rw [hall.of_norm.tsum_prod]
  apply tsum_congr
  intro u
  exact Summable.tsum_finsetSum (fun e _=>(hs u e).of_norm)

end FixedFourierGeometry
end

open ActualEisensteinCubic CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

theorem reflectedValue_eq_branch_sums (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.reflectedValue G.shape hp G.denominator_ne_zero hg j W X=
      fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
        ∑'u:Eisˣ,∑e:ι→Fin 3,∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
          G.stratumBranchTerm D hp hg j u e W X x := by
  rw [G.reflectedValue_eq_model_series]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  rw [←G.stratumBranchTerm_fubini D hN hr hp hg hchar j hj W a b ha hsupp hW X hX]
  let v:G.PhaseResidue:=Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)
  let weight:CuspIdealIndex→ℂ:=fun t=>
    D.modelRowPhase G.shape hp hg j t.1 t.2.1*
      (∑e:ι→Fin 3,reflectedBranch (fun i=>Ideal.span {p i}) hg j e
        (primaryGenerator t.2.2.1.val) (primaryGenerator t.2.2.2.val)) /
      ((ramifiedScale 1 completedRamifiedStep t.2.1*
        Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ)*
      CubicReflectionKernel.paperKernel (Vstar W)
        ((X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)
  calc
    _=∑'t:ThetaFullIndex,G.array v t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
      weight (thetaFullToIdealIndex t) := by
        apply tsum_congr
        intro t
        dsimp only [weight,thetaFullToIdealIndex,primaryCubePairToMellinIndex]
        rw [←Finset.mul_sum]
        ring
    _=∑'t:CuspIdealIndex,G.array v t.1 t.2.1 t.2.2.1.val t.2.2.2.val*weight t :=
      (fixedCuspArrayWithPhase_tsum_full_index (fun _=>G.shape.index) (G.staticPhase v) weight).symm
    _=_ := by
      apply tsum_congr
      intro t
      dsimp only [weight,stratumBranchTerm,rawDualKernelTerm,unextractedCuspCoefficient]
      simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e he
      dsimp only [v,ramifiedScale]
      ring

theorem stratumBranchTerm_tsum_extract (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hcop:Pairwise (fun i k=>IsCoprime (Ideal.span {p i}) (Ideal.span {p k})))
    (j:ι→ℕ) (e:ι→Fin 3) (u:Eisˣ) (W:ℝ→ℂ) (X:ℝ) :
    let A:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 1
    let B:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 2
    let hA:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 1
    let hB:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 2
    (∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,G.stratumBranchTerm D hp hg j u e W X x)=
      ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
        G.stratumBranchTerm D hp hg j u e W X (nonzeroDualDilation A B hA hB x) := by
  dsimp only
  apply tsum_nonzeroDualDilation
  intro x hx
  dsimp only [stratumBranchTerm,rawDualKernelTerm,unextractedCuspCoefficient] at hx
  have hnum:= (div_ne_zero_iff.mp (mul_ne_zero_iff.mp hx).1).1
  have hpair:G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u x.1 x.2.1.val x.2.2.val*
      reflectedBranch (fun i=>Ideal.span {p i}) hg j e
        (primaryGenerator x.2.1.val) (primaryGenerator x.2.2.val)≠0 :=
    mul_ne_zero (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnum).1).2 (mul_ne_zero_iff.mp hnum).2
  have hs:=fixedCuspBranchNumerator_support (fun i=>Ideal.span {p i}) hg hcop j e
    G.shape.index u (G.staticPhase (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u)
    x.1 x.2.1.val x.2.2.val hpair
  exact ⟨hs.1,hs.2.1⟩

theorem smoothedValue_eq_extracted_branch_sums
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0)
    (hcop:Pairwise (fun i k=>IsCoprime (Ideal.span {p i}) (Ideal.span {p k})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.smoothedValue hN hr G.primary G.shape hp G.denominator_ne_zero hg j W X=
      fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
        ∑'u:Eisˣ,∑e:ι→Fin 3,
          let A:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 1
          let B:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 2
          let hA:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 1
          let hB:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 2
          ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
            G.stratumBranchTerm D hp hg j u e W X (nonzeroDualDilation A B hA hB x) := by
  rw [D.smoothed_eq_reflected hN hr G.primary G.shape hp G.denominator_ne_zero hcop hg hchar
    j hj W a b ha hsupp hW X hX,
    G.reflectedValue_eq_branch_sums D hN hr hp hg hchar j hj W a b ha hsupp hW X hX]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro e he
  exact G.stratumBranchTerm_tsum_extract D hp hg hcop j e u W X

end FixedFourierGeometry
end CubicEisenstein

open scoped BigOperators Classical

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma freePrimaryPrime_coprime_completion (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (P:FreePrimeIndex I Q) : IsCoprime ((9:Eis)*c) (freePrimaryPrime I Q P) := by
  have h9:IsCoprime (9:Eis) (freePrimaryPrime I Q P):=
    (ShortDraftCRT.primary_coprime_nine _ (freePrimaryPrime_primary I Q hI P)).symm
  have h9ideal:IsCoprime (Ideal.span {(9:Eis)}:Ideal Eis)
      (Ideal.span {freePrimaryPrime I Q P}):=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr h9
  have hcideal:IsCoprime (Ideal.span {c}:Ideal Eis)
      (Ideal.span {freePrimaryPrime I Q P}):=by
    rw [hcQ]
    exact h9ideal.mul_left (freePrimaryPrime_coprime_fixed I Q hI P)
  exact h9.mul_left ((Ideal.isCoprime_span_singleton_iff _ _).mp hcideal)

theorem exists_freePrimary_controlled_stratum (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex I Q)) :
    Nonempty (ControlledStratumArithmetic
      (fun i:A=>freePrimaryPrime I Q i.val) ((9:Eis)*c) G.a0 G.c0 G.mode) := by
  let : ∀i:A,(Ideal.span {freePrimaryPrime I Q i.val}:Ideal Eis).IsMaximal:=
    fun i=>freePrimaryPrime_maximal I Q hI i.val
  apply exists_controlledStratumArithmetic
    (fun i:A=>freePrimaryPrime I Q i.val)
    (fun i=>freePrimaryPrime_ne_zero I Q hI i.val)
  · intro i j hij
    exact freePrimaryPrime_coprime I Q hI (fun he=>hij (Subtype.ext he))
  · exact fun i=>freePrimaryPrime_primary I Q hI i.val
  · exact G.denominator_ne_zero
  · exact mul_dvd_mul_left 9 G.denominator_dvd
  · exact G.primary
  · exact G.coprime
  · exact fun i=>freePrimaryPrime_coprime_completion I Q hI c hcQ i.val

noncomputable def freePrimaryControlledStratum (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex I Q)) :
    ControlledStratumArithmetic
      (fun i:A=>freePrimaryPrime I Q i.val) ((9:Eis)*c) G.a0 G.c0 G.mode :=
  Classical.choice (exists_freePrimary_controlled_stratum I Q hI c hcQ h G A)

end CanonicalRowCompletion

end

end OAI

end Source293

/- Original source: OAI/NumberTheory/DirichletL/RowCompletion/FreePrimePools.lean; sha256: a73b10feb302f5de02b6e463a0494a2c39739d011114999119b18639ac8cad30 -/
section Source294
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

section
open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def freePrimePool (lengthScale Q0:Ideal Eis) : Finset (Ideal Eis) :=
  (CompletedGauss.primeSupport lengthScale).filter (fun P=>¬Q0≤P)

lemma mem_freePrimePool (lengthScale Q0 P:Ideal Eis) :
    P∈freePrimePool lengthScale Q0 ↔ P∈CompletedGauss.primeSupport lengthScale ∧ ¬Q0≤P := by
  simp only [freePrimePool,Finset.mem_filter]

lemma residual_nonresidual_disjoint (I Q Q0:Ideal Eis) :
    Disjoint (CompletedGauss.primeSupport (rowResidualPart I Q)) (FreeReflection.pool I Q Q0) := by
  apply Finset.disjoint_left.mpr
  intro P hP ht
  exact FreeReflection.pool_nonresidual I Q Q0 ⟨P,ht⟩
    (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))

theorem freePrimePool_eq_residual_union (lengthScale I Q Q0:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hcop:IsCoprime Q0 (rowResidualPart I Q))
    (hs:CompletedGauss.primeSupport lengthScale=
      (CompletedGauss.primeSupport (I*Q)).filter
        (fun P=>lambda∉P ∧ ringChar (Eis⧸P)≠2)) :
    freePrimePool lengthScale Q0=
      CompletedGauss.primeSupport (rowResidualPart I Q) ∪ FreeReflection.pool I Q Q0 := by
  have hk:=rowResidualPart_admissible I Q hbad
  ext P
  constructor
  · intro hP
    obtain ⟨hL,hfree⟩:=Finset.mem_filter.mp hP
    rw [hs] at hL
    obtain ⟨hprod,hgood,hodd⟩:=Finset.mem_filter.mp hL
    have hp:Prime P:=prime_of_normalized_factor P (Multiset.mem_toFinset.mp hprod)
    by_cases hr:P∣rowResidualPart I Q
    · exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
        ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hk.1).mpr ⟨hp,hr⟩))
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_filter.mpr ⟨hprod,hgood,hodd,hr⟩,hfree⟩
  · intro hP
    rcases Finset.mem_union.mp hP with hr|ht
    · have hfactor:=Multiset.mem_toFinset.mp hr
      have hp:Prime P:=prime_of_normalized_factor P hfactor
      have hrow:=rowResidualPart_prime_exponent I Q P hfactor
      have hgood:=hk.2.2 P hfactor
      have hfree:¬Q0≤P:=by
        intro hQP
        exact hp.not_isUnit (hcop.isUnit_of_dvd'
          (Ideal.dvd_iff_le.mpr hQP) (dvd_of_mem_normalizedFactors hfactor))
      apply Finset.mem_filter.mpr
      refine ⟨?_,hfree⟩
      rw [hs]
      apply Finset.mem_filter.mpr
      exact ⟨Multiset.mem_toFinset.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (mul_ne_zero hI hQ)).mpr
        ⟨hp,dvd_mul_of_dvd_left (dvd_of_mem_normalizedFactors hrow.1) Q⟩),hgood⟩
    · obtain ⟨hpool,hfree⟩:=Finset.mem_filter.mp ht
      obtain ⟨hprod,hgood,hodd,_⟩:=Finset.mem_filter.mp hpool
      apply Finset.mem_filter.mpr
      refine ⟨?_,hfree⟩
      rw [hs]
      exact Finset.mem_filter.mpr ⟨hprod,hgood,hodd⟩

def primeUnionToFree (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T) :
    PrimeIndex k ⊕ T → FreePrimeIndex lengthScale Q0 := fun P=>by
  have hm:(Sum.elim Subtype.val Subtype.val P)∈freePrimePool lengthScale Q0:=by
    rw [hs]
    cases P with
    | inl P=>exact Finset.mem_union_left _ P.property
    | inr P=>exact Finset.mem_union_right _ P.property
  exact ⟨⟨Sum.elim Subtype.val Subtype.val P,(Finset.mem_filter.mp hm).1⟩,
    (Finset.mem_filter.mp hm).2⟩

lemma primeUnionToFree_val (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T) (P:PrimeIndex k⊕T) :
    (primeUnionToFree lengthScale Q0 k T hs P).val.val=Sum.elim Subtype.val Subtype.val P := rfl

lemma primeUnionToFree_bijective (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T)
    (hd:Disjoint (CompletedGauss.primeSupport k) T) :
    Function.Bijective (primeUnionToFree lengthScale Q0 k T hs) := by
  constructor
  · intro P R he
    have hv:=congrArg (fun S:FreePrimeIndex lengthScale Q0=>S.val.val) he
    change Sum.elim Subtype.val Subtype.val P=Sum.elim Subtype.val Subtype.val R at hv
    cases P with
    | inl P=>cases R with
      | inl R=>exact congrArg Sum.inl (Subtype.ext hv)
      | inr R=>
        change P.val=R.val at hv
        exact (Finset.disjoint_left.mp hd P.property (hv.symm ▸ R.property)).elim
    | inr P=>cases R with
      | inl R=>
        change P.val=R.val at hv
        exact (Finset.disjoint_left.mp hd R.property (hv ▸ P.property)).elim
      | inr R=>exact congrArg Sum.inr (Subtype.ext hv)
  · intro P
    have hm:P.val.val∈CompletedGauss.primeSupport k∪T:=by
      rw [←hs]
      exact Finset.mem_filter.mpr ⟨P.val.property,P.property⟩
    rcases Finset.mem_union.mp hm with hl|hr
    · exact ⟨Sum.inl ⟨P.val.val,hl⟩,Subtype.ext (Subtype.ext rfl)⟩
    · exact ⟨Sum.inr ⟨P.val.val,hr⟩,Subtype.ext (Subtype.ext rfl)⟩

noncomputable def primeUnionEquiv (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T)
    (hd:Disjoint (CompletedGauss.primeSupport k) T) :
    PrimeIndex k⊕T ≃ FreePrimeIndex lengthScale Q0 :=
  Equiv.ofBijective (primeUnionToFree lengthScale Q0 k T hs) (primeUnionToFree_bijective lengthScale Q0 k T hs hd)

lemma primeUnionEquiv_val (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T)
    (hd:Disjoint (CompletedGauss.primeSupport k) T) (P:PrimeIndex k⊕T) :
    (primeUnionEquiv lengthScale Q0 k T hs hd P).val.val=Sum.elim Subtype.val Subtype.val P := rfl

theorem prod_freePrimeIndex_eq {M:Type*} [CommMonoid M]
    (lengthScale Q0 k:Ideal Eis) (T:Finset (Ideal Eis))
    (hs:freePrimePool lengthScale Q0=CompletedGauss.primeSupport k∪T)
    (hd:Disjoint (CompletedGauss.primeSupport k) T) (f:Ideal Eis → M) :
    (∏P:FreePrimeIndex lengthScale Q0,f P.val.val)=(∏P:PrimeIndex k,f P.val)*(∏P:T,f P.val) := by
  calc
    _=(∏P:PrimeIndex k⊕T,f (Sum.elim Subtype.val Subtype.val P)):=
      (Fintype.prod_equiv (primeUnionEquiv lengthScale Q0 k T hs hd) _ _ (fun P=>rfl)).symm
    _=_:=Fintype.prod_sum_type _

end

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

variable (I F Q0:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))

include I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop

theorem goodMaskFreePrimePool :
    freePrimePool (goodMaskMovingIdeal g r) Q0=
      CompletedGauss.primeSupport (rowResidualPart I (Ideal.span {m}*F)) ∪
        FreeReflection.pool I (Ideal.span {m}*F) Q0 := by
  apply freePrimePool_eq_residual_union _ _ _ _ hI
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hbad hcop
  exact goodMaskMovingIdeal_primeSupport I F hI hF.ne_zero m f z hm0 hf hz
    um am bm g hg hm u a b r hr hx

noncomputable def goodMaskFreePrimeEquiv :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool I (Ideal.span {m}*F) Q0 ≃
      FreePrimeIndex (goodMaskMovingIdeal g r) Q0 :=
  primeUnionEquiv _ _ _ _
    (goodMaskFreePrimePool I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop)
    (residual_nonresidual_disjoint I (Ideal.span {m}*F) Q0)

lemma goodMaskFreePrimeEquiv_val
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool I (Ideal.span {m}*F) Q0) :
    (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop P).val.val=
      Sum.elim Subtype.val Subtype.val P := rfl

lemma goodMaskFreePrimeEquiv_residual_exponent
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop
        (Sum.inl P)).val.val%6=1 := by
  change (normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6=1
  have hp:=(rowResidualPart_admissible I (Ideal.span {m}*F) hbad).2.2
    P.val (Multiset.mem_toFinset.mp P.property)
  rw [goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P.val hp.1 hp.2]
  exact completedLocalExponent_residual I F _ (dvd_mul_left F (Ideal.span {m})) P

lemma goodMaskFreePrimeEquiv_nonresidual_exponent
    (P:FreeReflection.pool I (Ideal.span {m}*F) Q0) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop
        (Sum.inr P)).val.val%6=completedLocalExponent I F P.val := by
  change (normalizedFactors (goodMaskMovingIdeal g r)).count P.val%6=completedLocalExponent I F P.val
  let:P.val.IsMaximal:=FreeReflection.pool_maximal I (Ideal.span {m}*F) Q0 P
  exact goodMaskMovingIdeal_exponent I F hI hF m f z hf hz um am bm g hg hm u a b r hr hx P.val
    (FreeReflection.pool_good I (Ideal.span {m}*F) Q0 P)
    (FreeReflection.pool_odd I (Ideal.span {m}*F) Q0 P)

theorem goodMaskFreePrimeEquiv_exponent
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool I (Ideal.span {m}*F) Q0) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop P).val.val%6=
      Sum.elim (fun _=>1) (fun R=>completedLocalExponent I F R.val) P := by
  cases P with
  | inl P=>
    exact goodMaskFreePrimeEquiv_residual_exponent I F Q0 hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop P
  | inr P=>
    exact goodMaskFreePrimeEquiv_nonresidual_exponent I F Q0 hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop P

end

section

variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def optionalPrimeActive (e:α⊕β ≃ γ) (A:Finset γ) : Finset β :=
  Finset.univ.filter (fun b=>e (Sum.inr b)∈A)

omit [Fintype α] [Fintype γ] in
lemma mem_optionalPrimeActive (e:α⊕β ≃ γ) (A:Finset γ) (b:β) :
    b∈optionalPrimeActive e A ↔ e (Sum.inr b)∈A := by
  simp only [optionalPrimeActive,Finset.mem_filter,Finset.mem_univ,true_and]

def activePrimeUnionMap (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : α⊕optionalPrimeActive e A → A :=
  Sum.elim (fun a=>⟨e (Sum.inl a),hA a⟩)
    (fun b=>⟨e (Sum.inr b.val),(mem_optionalPrimeActive e A b.val).mp b.property⟩)

omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionMap_bijective (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : Function.Bijective (activePrimeUnionMap e A hA) := by
  constructor
  · intro x y hxy
    have hv:=congrArg Subtype.val hxy
    cases x with
    | inl x=>cases y with
      | inl y=>exact congrArg Sum.inl (Sum.inl.inj (e.injective hv))
      | inr y=>cases e.injective hv
    | inr x=>cases y with
      | inl y=>cases e.injective hv
      | inr y=>exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj (e.injective hv)))
  · intro a
    obtain ⟨x,hx⟩:=e.surjective a.val
    cases x with
    | inl x=>exact ⟨Sum.inl x,Subtype.ext hx⟩
    | inr x=>
      have hm:x∈optionalPrimeActive e A:=(mem_optionalPrimeActive e A x).mpr (hx.symm ▸ a.property)
      exact ⟨Sum.inr ⟨x,hm⟩,Subtype.ext hx⟩

noncomputable def activePrimeUnionEquiv (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) : α⊕optionalPrimeActive e A ≃ A :=
  Equiv.ofBijective (activePrimeUnionMap e A hA) (activePrimeUnionMap_bijective e A hA)

omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionEquiv_inl (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) (a:α) :
    (activePrimeUnionEquiv e A hA (Sum.inl a)).val=e (Sum.inl a) := rfl

omit [Fintype α] [Fintype γ] in
lemma activePrimeUnionEquiv_inr (e:α⊕β ≃ γ) (A:Finset γ)
    (hA:∀a:α,e (Sum.inl a)∈A) (b:optionalPrimeActive e A) :
    (activePrimeUnionEquiv e A hA (Sum.inr b)).val=e (Sum.inr b.val) := rfl

omit [Fintype γ] in
theorem prod_activePrimeUnionEquiv {M:Type*} [CommMonoid M]
    (e:α⊕β ≃ γ) (A:Finset γ) (hA:∀a:α,e (Sum.inl a)∈A) (f:A → M) :
    (∏a:A,f a)=
      (∏a:α,f (activePrimeUnionEquiv e A hA (Sum.inl a)))*
        (∏b:optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA (Sum.inr b))) := by
  calc
    _=(∏x:α⊕optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA x)):=
      (Fintype.prod_equiv (activePrimeUnionEquiv e A hA) _ _ (fun _=>rfl)).symm
    _=_:=Fintype.prod_sum_type _

omit [Fintype γ] in
theorem sum_activePrimeUnionEquiv {M:Type*} [AddCommMonoid M]
    (e:α⊕β ≃ γ) (A:Finset γ) (hA:∀a:α,e (Sum.inl a)∈A) (f:A → M) :
    (∑a:A,f a)=
      (∑a:α,f (activePrimeUnionEquiv e A hA (Sum.inl a)))+
        (∑b:optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA (Sum.inr b))) := by
  calc
    _=(∑x:α⊕optionalPrimeActive e A,f (activePrimeUnionEquiv e A hA x)):=
      (Fintype.sum_equiv (activePrimeUnionEquiv e A hA) _ _ (fun _=>rfl)).symm
    _=_:=Fintype.sum_sum_type _

theorem sum_prime_active_sets {M:Type*} [AddCommMonoid M]
    (e:α⊕β ≃ γ) (f:Finset γ → M) :
    (∑A:Finset γ,f A)=∑A:Finset (α⊕β),f (A.map e.toEmbedding) := by
  exact (Fintype.sum_equiv e.finsetCongr _ _ (fun _=>rfl)).symm

end

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def nonresidualPoolEquiv (R I Q Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R Q=rowMaskPart I Q) :
    FreeReflection.pool R Q Q0 ≃ FreeReflection.pool I Q Q0 := by
  have he:=FreeReflection.pool_eq_on_fiber R I Q Q0 hR hI hQ hA hT
  exact {
    toFun:=fun P=>⟨P.val,he ▸ P.property⟩
    invFun:=fun P=>⟨P.val,he.symm ▸ P.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }

lemma nonresidualPoolEquiv_val (R I Q Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart R=rowPowerfulPart I) (hT:rowMaskPart R Q=rowMaskPart I Q)
    (P:FreeReflection.pool R Q Q0) :
    (nonresidualPoolEquiv R I Q Q0 hR hI hQ hA hT P).val=P.val := rfl

lemma nonresidualPoolEquiv_exponent (R I F Q Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart R=rowPowerfulPart I) (hT:rowMaskPart R Q=rowMaskPart I Q)
    (P:FreeReflection.pool R Q Q0) :
    completedLocalExponent I F (nonresidualPoolEquiv R I Q Q0 hR hI hQ hA hT P).val=
      completedLocalExponent R F P.val :=
  (completedReflectionPool_exponent_eq R I F Q hR hI hQ hA hT
    ⟨P.val,FreeReflection.pool_subset R Q Q0 P.property⟩).symm

variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
include R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop hA hT

noncomputable def goodMaskFreePrimeFiberEquiv :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0 ≃
      FreePrimeIndex (goodMaskMovingIdeal g r) Q0 :=
  (Equiv.sumCongr (Equiv.refl _)
    (nonresidualPoolEquiv R I (Ideal.span {m}*F) Q0 hR hI
      (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hA hT)).trans
    (goodMaskFreePrimeEquiv I F Q0 hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop)

lemma goodMaskFreePrimeFiberEquiv_val
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (goodMaskFreePrimeFiberEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
      hbad hcop hA hT P).val.val=Sum.elim Subtype.val Subtype.val P := by
  cases P <;> rfl

theorem goodMaskFreePrimeFiberEquiv_exponent
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskFreePrimeFiberEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
        hbad hcop hA hT P).val.val%6=
      Sum.elim (fun _=>1) (fun S=>completedLocalExponent R F S.val) P := by
  cases P with
  | inl P=>
    exact goodMaskFreePrimeEquiv_residual_exponent I F Q0 hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop P
  | inr P=>
    exact (goodMaskFreePrimeEquiv_nonresidual_exponent I F Q0 hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop
      (nonresidualPoolEquiv R I (Ideal.span {m}*F) Q0 hR hI
        (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hA hT P)).trans
      (nonresidualPoolEquiv_exponent R I F (Ideal.span {m}*F) Q0 hR hI
        (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF.ne_zero) hA hT P)

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

section
variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
include R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop hA hT

local notation "splitIndex" => (goodMaskFreePrimeFiberEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx hbad hcop hA hT)

noncomputable def goodMaskActivePrimeEquiv
    (A:Finset (FreePrimeIndex (goodMaskMovingIdeal g r) Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A) :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ optionalPrimeActive splitIndex A ≃ A :=
  activePrimeUnionEquiv splitIndex A hactive

lemma goodMaskActivePrimeEquiv_residual_val
    (A:Finset (FreePrimeIndex (goodMaskMovingIdeal g r) Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A)
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) :
    (goodMaskActivePrimeEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
      hbad hcop hA hT A hactive (Sum.inl P)).val.val.val=P.val := rfl

lemma goodMaskActivePrimeEquiv_nonresidual_val
    (A:Finset (FreePrimeIndex (goodMaskMovingIdeal g r) Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A)
    (P:optionalPrimeActive splitIndex A) :
    (goodMaskActivePrimeEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
      hbad hcop hA hT A hactive (Sum.inr P)).val.val.val=P.val.val := rfl

theorem goodMaskActivePrimeEquiv_exponent
    (A:Finset (FreePrimeIndex (goodMaskMovingIdeal g r) Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A)
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ optionalPrimeActive splitIndex A) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count
      (goodMaskActivePrimeEquiv R I F Q0 hR hI hF m f z hm0 hf hz um am bm g hg hm u a b r hr hx
        hbad hcop hA hT A hactive P).val.val.val%6=
      Sum.elim (fun _=>1) (fun S=>completedLocalExponent R F S.val.val) P := by
  cases P with
  | inl P=>
    exact goodMaskFreePrimeFiberEquiv_exponent R I F Q0 hR hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop hA hT (Sum.inl P)
  | inr P=>
    exact goodMaskFreePrimeFiberEquiv_exponent R I F Q0 hR hI hF m f z hm0 hf hz
      um am bm g hg hm u a b r hr hx hbad hcop hA hT (Sum.inr P.val)

end

lemma reflection_row_mask_bad (q:ℕ) (m:Eis) (F:Ideal Eis) :
    ∀P∈fixedBadPrimes,P∣Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F := by
  intro P hP
  exact excluded_prime_dvd_row_mask q m F P (reflectionExcludedPrimes_bad q hP)

lemma residual_coprime_free_base (q:ℕ) (hq:q≠0) (m:Eis) (F I:Ideal Eis) :
    IsCoprime (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)})
      (rowResidualPart I (Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F)) := by
  have hc:=residual_coprime_fixed_conductor q hq m F I
  rw [reflectionConductor_ideal] at hc
  exact hc.of_isCoprime_of_dvd_left (dvd_mul_left _ (Ideal.span {(9:Eis)}))

end CanonicalRowCompletion

local instance (priority := 2000) residualLabelDecidableEq (A B:Type*) : DecidableEq (A⊕B) :=
  Classical.decEq _
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
variable {α β:Type*} [Fintype α] [Fintype β]

def residualZeroLabel (e:β→Fin 3) : α⊕β→Fin 3 := Sum.elim (fun _=>0) e

theorem sum_labels_drop_residual (f:(α⊕β→Fin 3)→ℂ)
    (hzero:∀e,(∃i:α,e (Sum.inl i)≠0)→f e=0) :
    (∑e:α⊕β→Fin 3,f e)=∑e:β→Fin 3,f (residualZeroLabel e) := by
  rw [←(Equiv.sumArrowEquivProdArrow α β (Fin 3)).symm.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_eq_single (fun _ : α=>0)]
  · rfl
  · intro d hd hn
    apply hzero
    have hx:∃i:α,d i≠0:=by
      by_contra h
      push Not at h
      exact hn (funext h)
    obtain ⟨i,hi⟩:=hx
    exact ⟨i,hi⟩
  · simp

lemma reflectedBranch_residual_label_zero
    (P:α⊕β→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:α⊕β→Fin 3) (hbad:∃i:α,e (Sum.inl i)≠0) (n b:Eis) :
    reflectedBranch P hg j e n b=0 := by
  obtain ⟨i,hi⟩:=hbad
  unfold reflectedBranch
  apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl i))
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,ite_eq_right hi]

lemma reflectionExtractedDivisor_drop_residual
    (P:α⊕β→Ideal Eis) (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:α⊕β→Fin 3) (v:Fin 3) :
    reflectionExtractedDivisor P j e v=
      reflectionExtractedDivisor (fun i:β=>P (Sum.inr i)) (fun i=>j (Sum.inr i))
        (fun i=>e (Sum.inr i)) v := by
  simp only [reflectionExtractedDivisor,Fintype.prod_sum_type]
  have hz:(∏i:α,reflectionExtractedPrime (P (Sum.inl i)) (j (Sum.inl i)) (e (Sum.inl i)) v)=1 := by
    simp only [hj,reflectionExtractedPrime,show (1:ℕ)≠4 by decide,show (1:ℕ)≠0 by decide,
      false_and,false_or,ite_false,Finset.prod_const_one]
  rw [hz,one_mul]

lemma reflectedBranch_drop_residual
    (P:α⊕β→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:α⊕β→ℕ) (hj:∀i:α,j (Sum.inl i)=1)
    (e:β→Fin 3) (n b:Eis) :
    reflectedBranch P hg j (residualZeroLabel e) n b=
      (∏i:α,bracket (actualSextic (P (Sum.inl i)) (hg (Sum.inl i))) 1
        (Ideal.Quotient.mk _ (n*b^3)))*
      reflectedBranch (fun i:β=>P (Sum.inr i)) (fun i=>hg (Sum.inr i))
        (fun i=>j (Sum.inr i)) e n b := by
  simp only [reflectedBranch,Fintype.prod_sum_type,residualZeroLabel,Sum.elim_inl,Sum.elim_inr]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,ite_true]

end CompletedGauss
end

open scoped BigOperators Classical

local instance (priority := 2000) residualEquivDecidableEq (A B:Type*) : DecidableEq (A⊕B) :=
  Classical.decEq _
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
variable {α β ι:Type*} [Fintype α] [Fintype β] [Fintype ι]

def residualLabelVia (E:α⊕β≃ι) (e:β→Fin 3) : ι→Fin 3 :=
  residualZeroLabel e ∘ E.symm

omit [Fintype α] [Fintype β] [Fintype ι] in
lemma residualLabelVia_apply (E:α⊕β≃ι) (e:β→Fin 3) (i:α⊕β) :
    residualLabelVia E e (E i)=residualZeroLabel e i := by
  simp only [residualLabelVia,Function.comp_apply,Equiv.symm_apply_apply]

theorem sum_labels_drop_residual_equiv (E:α⊕β≃ι) (f:(ι→Fin 3)→ℂ)
    (hzero:∀e,(∃i:α,e (E (Sum.inl i))≠0)→f e=0) :
    (∑e:ι→Fin 3,f e)=∑e:β→Fin 3,f (residualLabelVia E e) := by
  let e:=Equiv.arrowCongr E (Equiv.refl (Fin 3))
  rw [←e.sum_comp f]
  apply sum_labels_drop_residual
  intro l hl
  apply hzero
  obtain ⟨i,hi⟩:=hl
  refine ⟨i,?_⟩
  simpa only [e,Equiv.arrowCongr_apply,Function.comp_apply,Equiv.refl_apply,Equiv.symm_apply_apply] using hi

omit [Fintype α] [Fintype β] in
lemma reflectedBranch_residual_zero_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:ι→Fin 3) (hbad:∃i:α,e (E (Sum.inl i))≠0) (n b:Eis) :
    reflectedBranch P hg j e n b=0 := by
  obtain ⟨i,hi⟩:=hbad
  unfold reflectedBranch
  apply Finset.prod_eq_zero (Finset.mem_univ (E (Sum.inl i)))
  simp only [reflectedLocalPiece,hj,show (1:ℕ)≠4 by decide,ite_false,ite_eq_right hi]

lemma reflectionExtractedDivisor_drop_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:β→Fin 3) (v:Fin 3) :
    reflectionExtractedDivisor P j (residualLabelVia E e) v=
      reflectionExtractedDivisor (fun i:β=>P (E (Sum.inr i))) (fun i=>j (E (Sum.inr i))) e v := by
  calc
    _=reflectionExtractedDivisor (fun i=>P (E i)) (fun i=>j (E i)) (residualZeroLabel e) v := by
      unfold reflectionExtractedDivisor
      rw [←E.prod_comp]
      apply Finset.prod_congr rfl
      intro i hi
      rw [residualLabelVia_apply]
    _=_:=reflectionExtractedDivisor_drop_residual _ _ hj _ _

lemma reflectedBranch_drop_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1)
    (e:β→Fin 3) (n b:Eis) :
    reflectedBranch P hg j (residualLabelVia E e) n b=
      (∏i:α,bracket (actualSextic (P (E (Sum.inl i))) (hg (E (Sum.inl i)))) 1
        (Ideal.Quotient.mk _ (n*b^3)))*
      reflectedBranch (fun i:β=>P (E (Sum.inr i))) (fun i=>hg (E (Sum.inr i)))
        (fun i=>j (E (Sum.inr i))) e n b := by
  calc
    _=reflectedBranch (fun i=>P (E i)) (fun i=>hg (E i)) (fun i=>j (E i)) (residualZeroLabel e) n b := by
      unfold reflectedBranch
      rw [←E.prod_comp]
      apply Finset.prod_congr rfl
      intro i hi
      rw [residualLabelVia_apply]
    _=_:=reflectedBranch_drop_residual _ _ _ hj _ _ _

end CompletedGauss

end

end OAI

end Source294

/- Original source: OAI/NumberTheory/DirichletL/GaussSum/ResidualEquivalence.lean; sha256: c0e0c97ca9636fce2aa1ada1fa884e3d69efd251f7e5482751b3f9541998c9b5 -/
section Source295
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

open scoped BigOperators Classical ContDiff

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable {α β ι:Type*} [Fintype α] [Fintype β] [Fintype ι]

lemma nonzeroDualDilation_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1) (e:β→Fin 3)
    (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
    nonzeroDualDilation
      (reflectionExtractedDivisor P j (residualLabelVia E e) 1)
      (reflectionExtractedDivisor P j (residualLabelVia E e) 2)
      (reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) j _ 1)
      (reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) j _ 2) x=
    nonzeroDualDilation
      (reflectionExtractedDivisor (fun i:β=>P (E (Sum.inr i))) (fun i=>j (E (Sum.inr i))) e 1)
      (reflectionExtractedDivisor (fun i:β=>P (E (Sum.inr i))) (fun i=>j (E (Sum.inr i))) e 2)
      (reflectionExtractedDivisor_ne_zero _ (fun _i=>NeZero.ne _) _ _ 1)
      (reflectionExtractedDivisor_ne_zero _ (fun _i=>NeZero.ne _) _ _ 2) x := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> apply Subtype.ext <;>
      simp only [nonzeroDualDilation,reflectionExtractedDivisor_drop_residual_equiv E P j hj]

lemma unextractedCuspCoefficient_residual_equiv (E:α⊕β≃ι)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (hj:∀i:α,j (E (Sum.inl i))=1) (e:β→Fin 3)
    (ρ q:ℝ) (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ) (m:ℕ) (I J:Ideal Eis) :
    unextractedCuspCoefficient P hg j (residualLabelVia E e) ρ q η σ m I J=
      (σ m*(∏i:α,LocalReflectionBrackets.bracket (actualSextic (P (E (Sum.inl i))) (hg (E (Sum.inl i)))) 1
        (Ideal.Quotient.mk _ (primaryGenerator I*(primaryGenerator J)^3)))*
        η m I J*reflectedBranch (fun i:β=>P (E (Sum.inr i))) (fun i=>hg (E (Sum.inr i)))
          (fun i=>j (E (Sum.inr i))) e (primaryGenerator I) (primaryGenerator J))/
        ((CompletedDyadic.ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ):ℝ):ℂ) := by
  rw [unextractedCuspCoefficient,reflectedBranch_drop_residual_equiv E P hg j hj]
  ring

end CompletedGauss

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {α β ι:Type*} [Fintype α] [Fintype β] [Fintype ι] {p:ι→Eis} {N:Eis}

omit [Fintype α] [Fintype β] in
lemma stratumBranchTerm_residual_zero_equiv (E:α⊕β≃ι)
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (hres:∀i:α,j (E (Sum.inl i))=1)
    (u:Eisˣ) (e:ι→Fin 3) (hbad:∃i:α,e (E (Sum.inl i))≠0)
    (W:ℝ→ℂ) (X:ℝ) (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
    G.stratumBranchTerm D hp hg j u e W X x=0 := by
  dsimp only [stratumBranchTerm,rawDualKernelTerm,unextractedCuspCoefficient]
  rw [reflectedBranch_residual_zero_equiv E _ hg j hres e hbad,mul_zero,zero_div,zero_mul]

theorem smoothedValue_eq_nonresidual_equiv (E:α⊕β≃ι)
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0)
    (hcop:Pairwise (fun i k=>IsCoprime (Ideal.span {p i}) (Ideal.span {p k})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j:ι→ℕ) (hj:∀i,j i<6) (hres:∀i:α,j (E (Sum.inl i))=1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.smoothedValue hN hr G.primary G.shape hp G.denominator_ne_zero hg j W X=
      fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
        ∑'u:Eisˣ,∑e:β→Fin 3,
          let P:β→Ideal Eis:=fun i=>Ideal.span {p (E (Sum.inr i))}
          let jβ:β→ℕ:=fun i=>j (E (Sum.inr i))
          let A:=reflectionExtractedDivisor P jβ e 1
          let B:=reflectionExtractedDivisor P jβ e 2
          let hA:=reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) jβ e 1
          let hB:=reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) jβ e 2
          ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
            G.stratumBranchTerm D hp hg j u (residualLabelVia E e) W X (nonzeroDualDilation A B hA hB x) := by
  rw [G.smoothedValue_eq_extracted_branch_sums D hN hr hp hcop hg hchar j hj W a b ha hsupp hW X hX]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  apply tsum_congr
  intro u
  let f:(ι→Fin 3)→ℂ:=fun e=>
    ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      G.stratumBranchTerm D hp hg j u e W X
        (nonzeroDualDilation
          (reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 1)
          (reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 2)
          (reflectionExtractedDivisor_ne_zero _ (fun i=>NeZero.ne _) j e 1)
          (reflectionExtractedDivisor_ne_zero _ (fun i=>NeZero.ne _) j e 2) x)
  change (∑e,f e)=_
  have hz:∀e,(∃i:α,e (E (Sum.inl i))≠0)→f e=0 := by
    intro e he
    calc
      f e=∑'(_x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal),(0:ℂ) := by
        apply tsum_congr
        intro x
        exact G.stratumBranchTerm_residual_zero_equiv E D hp hg j hres u e he W X _
      _=0:=tsum_zero
  rw [sum_labels_drop_residual_equiv E f hz]
  apply Finset.sum_congr rfl
  intro e he
  dsimp only [f]
  apply tsum_congr
  intro x
  rw [nonzeroDualDilation_residual_equiv E _ j hres]

end FixedFourierGeometry
end CubicEisenstein

open scoped BigOperators Classical MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

noncomputable local instance primeQuotientFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

def primeInactiveFourierWeight {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (A:Finset ι) : ℂ :=
  ∏i∈(Finset.univ:Finset ι)\A,
    finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
      (fun x=>(actualSextic (Ideal.span {p i}) (hg i)^j i) x) 0

lemma primeRow_fourier_by_active {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (n:Eis) :
    finiteSexticRow (fun i=>Ideal.span {p i}) hg j n=
    ∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
      ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
        ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val)
          (fun i:A=>hp i.val) (fun i:A=>hg i.val) (fun i=>j i.val) v*
        ∏i:A,quotientTrace (p i.val) (hp i.val) ((v i:Eis⧸Ideal.span {p i.val})*Ideal.Quotient.mk (Ideal.span {p i.val}) n) := by
  let (i:ι) : Field (Eis⧸Ideal.span {p i}) := Ideal.Quotient.field _
  have hpow:(Finset.univ:Finset ι).powerset=(Finset.univ:Finset (Finset ι)):=by
    ext A
    simp only [Finset.mem_powerset,Finset.subset_univ,Finset.mem_univ]
  have hFourier:=FixedRayActiveSet.fourier_inversion_by_active_set
    (fun i=>Eis⧸Ideal.span {p i})
    (fun i=>quotientTrace (p i) (hp i))
    (fun i=>GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i))
    (fun i x=>(actualSextic (Ideal.span {p i}) (hg i)^j i) x)
    (fun i=>Ideal.Quotient.mk (Ideal.span {p i}) n)
  simpa only [hpow,finiteSexticRow,primeInactiveFourierWeight,
    ControlledStratumArithmetic.fourierWeight] using hFourier

def activeStratumDatum {ι:Type*} [Fintype ι]
    (p:ι→Eis) (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)
    {N a0 c0:Eis} {mode:Bool}
    (D:∀A:Finset ι,ControlledStratumArithmetic (fun i:A=>p i.val) N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hc0:c0≠0)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (A:Finset ι) (v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ) : SourceCuspDatum :=
  (D A).datum hN (primary_finset_product Finset.univ (fun i:A=>p i.val)
    (fun i _=>hprimary i.val)) hbase s (fun i=>hp i.val) hc0 v

theorem activeStratum_fourier_multiplier {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)
    (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    {N a0 c0:Eis} {mode:Bool}
    (D:∀A:Finset ι,ControlledStratumArithmetic (fun i:A=>p i.val) N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hc0:c0≠0)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)) (n:Eis) :
    (∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
      ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
        ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val) (fun i:A=>hp i.val) (fun i:A=>hg i.val)
          (fun i=>j i.val) v*
        ShortDraftTrace.breveE (-cuspFrequency n*
          (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point))=
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        finiteSexticRow (fun i=>Ideal.span {p i}) hg j n := by
  have hlocal (A:Finset ι) (v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ) :
      ShortDraftTrace.breveE (-cuspFrequency n*
        (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point)=
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        ∏i:A,quotientTrace (p i.val) (hp i.val) ((v i:Eis⧸Ideal.span {p i.val})*Ideal.Quotient.mk (Ideal.span {p i.val}) n) :=
    (D A).datum_fourier_phase hN
      (primary_finset_product Finset.univ (fun i:A=>p i.val) (fun i _=>hprimary i.val))
      hbase s (fun i=>hp i.val) hc0 v n
  calc
    _=∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
        ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
          ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val)
            (fun i:A=>hp i.val) (fun i:A=>hg i.val) (fun i=>j i.val) v*
          (ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
            ∏i:A,quotientTrace (p i.val) (hp i.val) ((v i:Eis⧸Ideal.span {p i.val})*Ideal.Quotient.mk (Ideal.span {p i.val}) n)):=by
      apply Finset.sum_congr rfl
      intro A hA
      apply congrArg (fun z:ℂ=>primeInactiveFourierWeight p hp hg j A*z)
      apply Finset.sum_congr rfl
      intro v hv
      exact congrArg (fun z:ℂ=>ControlledStratumArithmetic.fourierWeight
        (p:=fun i:A=>p i.val) (fun i:A=>hp i.val) (fun i:A=>hg i.val)
        (fun i=>j i.val) v*z) (hlocal A v)
    _=ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        (∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
          ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
            ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val)
              (fun i:A=>hp i.val) (fun i:A=>hg i.val) (fun i=>j i.val) v*
            ∏i:A,quotientTrace (p i.val) (hp i.val) ((v i:Eis⧸Ideal.span {p i.val})*Ideal.Quotient.mk (Ideal.span {p i.val}) n)):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _=_:=congrArg (fun z:ℂ=>
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*z)
      (primeRow_fourier_by_active p hp hg j n).symm

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota CubicJacobiGlobal
open CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O

noncomputable local instance fixedActiveQuotientFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

abbrev FixedActiveCuspIndex {ι:Type*} (c:Eis) (p:ι→Eis) :=
  Σ_h:Eis⧸Ideal.span {c},ΣA:Finset ι,∀i:A,(Eis⧸Ideal.span {p i.val})ˣ

variable {ι:Type*} [Fintype ι] (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)
variable (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
variable (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
variable (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h) (N:Eis)
variable (hN:∀h,(9:Eis)*(G h).c0∣N)
variable (D:∀h:Eis⧸Ideal.span {c},∀A:Finset ι,
  ControlledStratumArithmetic (fun i:A=>p i.val) N (G h).a0 (G h).c0 (G h).mode)

def fixedActiveCuspDatum (t:FixedActiveCuspIndex c p) : SourceCuspDatum :=
  activeStratumDatum p hp hprimary (D t.1) (hN t.1) (G t.1).denominator_ne_zero
    (G t.1).primary (G t.1).shape t.2.1 t.2.2

def fixedActiveCuspWeight (φ:Eis→*ℂ) (t:FixedActiveCuspIndex c p) : ℂ :=
  fixedThetaRowCoeff c hc φ t.1*primeInactiveFourierWeight p hp hg j t.2.1*
    ControlledStratumArithmetic.fourierWeight (p:=fun i:t.2.1=>p i.val)
      (fun i:t.2.1=>hp i.val) (fun i:t.2.1=>hg i.val) (fun i=>j i.val) t.2.2

theorem fixedActiveCusp_fourier_multiplier (Q:Ideal Eis)
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (φ χ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ)
    (hχ:∀n,χ n=finiteSexticRow (fun i=>Ideal.span {p i}) hg j n) (n:Eis) :
    (∑t:FixedActiveCuspIndex c p,fixedActiveCuspWeight p hp hg j c hc φ t*
      ShortDraftTrace.breveE (-cuspFrequency n*
        (fixedActiveCuspDatum p hp hprimary c G N hN D t).point))=
      fixedThetaTwist (φ*χ) n := by
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveCuspWeight,fixedActiveCuspDatum]
  rw [fixedThetaTwist_fixed_fourier c hc Q hcQ φ χ hφ n]
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _=fixedThetaRowCoeff c hc φ h*
        (∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
          ∑v:∀i:A,(Eis⧸Ideal.span {p i.val})ˣ,
            ControlledStratumArithmetic.fourierWeight (p:=fun i:A=>p i.val) (fun i:A=>hp i.val) (fun i:A=>hg i.val)
              (fun i=>j i.val) v*
            ShortDraftTrace.breveE (-cuspFrequency n*
              (activeStratumDatum p hp hprimary (D h) (hN h) (G h).denominator_ne_zero
                (G h).primary (G h).shape A v).point)):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _=fixedThetaRowCoeff c hc φ h*
        (ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding (G h).a0/eisEmbedding (G h).c0))*
          finiteSexticRow (fun i=>Ideal.span {p i}) hg j n):=by
      rw [activeStratum_fourier_multiplier p hp hprimary hg j (D h) (hN h)
        (G h).denominator_ne_zero (G h).primary (G h).shape n]
    _=fixedThetaRowCoeff c hc φ h*fixedRowFourierPhase c hc h n*χ n:=by
      rw [(G h).point,←hχ n, fixedRowFourierPhase_translation]
      ring

theorem completedT_fixed_active_strata (Q:Ideal Eis)
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (φ χ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ)
    (hχ:∀n,χ n=finiteSexticRow (fun i=>Ideal.span {p i}) hg j n)
    (hφχ:∀n,‖(φ*χ) n‖≤1) (Qall:Ideal Eis)
    (hperiod:CanonicalCoefficientClass.FactorsModulo Qall (φ*χ))
    (call:Eis) (hcall:call≠0) [Fintype (Eis⧸Ideal.span {call})]
    (hcallQ:Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (φ*χ) W X=thetaDerivativeScalar⁻¹*
      ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*
        ∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
          (D h A).smoothedValue (hN h)
            (primary_finset_product Finset.univ (fun i:A=>p i.val) (fun i _=>hprimary i.val))
            (G h).primary (G h).shape (fun i=>hp i.val) (G h).denominator_ne_zero
            (fun i=>hg i.val) (fun i=>j i.val) W X := by
  rw [completedT_of_finite_cusp_multiplier (φ*χ) hφχ Qall hperiod call hcall hcallQ
    (fixedActiveCuspDatum p hp hprimary c G N hN D)
    (fixedActiveCuspWeight p hp hg j c hc φ)
    (fixedActiveCusp_fourier_multiplier p hp hprimary hg j c hc G N hN D Q hcQ φ χ hφ hχ)
    W lo hi hlo hsupp hW X hX]
  congr 1
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveCuspWeight,fixedActiveCuspDatum,
    ControlledStratumArithmetic.smoothedValue,activeStratumDatum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  ring

end CubicEisenstein

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def actualControlledSource (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (φ:Eis→*ℂ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal I Q hI
  exact thetaDerivativeScalar⁻¹*
    ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*
      ∑A:Finset (FreePrimeIndex I Q),
        primeInactiveFourierWeight (freePrimaryPrime I Q) (freePrimaryPrime_ne_zero I Q hI)
          (freePrimaryPrime_good I Q hI)
          (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6) A*
        (freePrimaryControlledStratum I Q hI c hcQ h (G h) A).smoothedValue
          (mul_dvd_mul_left 9 (G h).denominator_dvd)
          (primary_finset_product Finset.univ (fun P:A=>freePrimaryPrime I Q P.val)
            (fun P _=>freePrimaryPrime_primary I Q hI P.val))
          (G h).primary (G h).shape (fun P=>freePrimaryPrime_ne_zero I Q hI P.val)
          (G h).denominator_ne_zero (fun P=>freePrimaryPrime_good I Q hI P.val)
          (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val.val%6) W X

theorem fixedFree_completedT_eq_actualControlledSource (I Q:Ideal Eis) (hI:Supported I)
    (hQ:Q≠0) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (hφn:∀n,‖φ n‖≤1)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (φ*freePrimeRow I hI Q) W X=actualControlledSource I Q hI c hc hcQ G φ W X := by
  let : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal I Q hI
  let Qall:Ideal Eis:=Q*(∏P:FreePrimeIndex I Q,P.val.val)
  have hQall:Qall≠0:=mul_ne_zero hQ
    (finite_prime_product_ne_bot (fun P:FreePrimeIndex I Q=>P.val.val))
  let call:=ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*Qall)
  have hcall:call≠0:=by
    apply ConcretePrimeRowBridge.idealGenerator_ne_zero
    apply mul_ne_zero _ hQall
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  let : Finite (Eis⧸Ideal.span {call}):=ConcreteTraceCRT.finite_quotient_span hcall
  let : Fintype (Eis⧸Ideal.span {call}):=Fintype.ofFinite _
  have hcallQ:Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall:=by
    rw [ConcretePrimeRowBridge.span_idealGenerator]
  exact completedT_fixed_active_strata (freePrimaryPrime I Q) (freePrimaryPrime_ne_zero I Q hI)
    (freePrimaryPrime_primary I Q hI) (freePrimaryPrime_good I Q hI)
    (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6)
    c hc G (9*c) (fun h=>mul_dvd_mul_left 9 (G h).denominator_dvd)
    (fun h A=>freePrimaryControlledStratum I Q hI c hcQ h (G h) A)
    Q hcQ.le φ (freePrimeRow I hI Q) hφ (freePrimeRow_eq_primary_family I Q hI)
    (fixedFreeRow_norm I hI Q φ hφn) Qall (fixedFreeRow_periodic I hI Q φ hφ)
    call hcall hcallQ W lo hi hlo hsupp hW X hX

theorem rowTwist_completedT_eq_actualControlledSource
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Q:Ideal Eis) (hQ:Q≠0)
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (Ψ:Eis→*ℂ) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      (∀h:Eis⧸Ideal.span {c},‖fixedThetaRowCoeff c hc φ h‖≤1) ∧
      ∀(W:ℝ→ℂ)(lo hi:ℝ),0<lo→Function.support W⊆Set.Icc lo hi→ContDiff ℝ ∞ W→
        ∀X:ℝ,0<X→completedT (rowTwist Ψ m f z) W X=
          actualControlledSource I (Q*Ideal.span {(72:Eis)}) hI c hc hcQ G φ W X := by
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hmod,hperiod,hnorm,hT⟩:=
    exists_actual_coprime_completed_row Ψ Q hQ hΨ hΨnorm m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,fixedThetaRowCoeff_norm c hc φ hφn,?_⟩
  intro W lo hi hlo hsupp hW X hX
  rw [hT W X]
  apply fixedFree_completedT_eq_actualControlledSource I _ hI _ c hc hcQ G φ hφ hφn W lo hi hlo hsupp hW X hX
  apply mul_ne_zero hQ
  simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
  norm_num

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

structure GoodMaskRowData (m f z:Eis) where
  maskUnit:Eisˣ
  maskLambda:ℕ
  maskTwo:ℕ
  maskGood:Eis
  maskSupported:Supported (Ideal.span {maskGood})
  maskPrimary:lambda^2∣maskGood-1
  maskFactor:m=maskUnit.val*lambda^maskLambda*(2:Eis)^maskTwo*maskGood
  numeratorUnit:Eisˣ
  numeratorLambda:ℕ
  numeratorTwo:ℕ
  numeratorGood:Eis
  numeratorSupported:Supported (Ideal.span {numeratorGood})
  numeratorPrimary:lambda^2∣numeratorGood-1
  numeratorFactor:f^4*z=numeratorUnit.val*lambda^numeratorLambda*(2:Eis)^numeratorTwo*numeratorGood

theorem exists_goodMaskRowData (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) :
    Nonempty (GoodMaskRowData m f z) := by
  obtain ⟨um,am,bm,g,hg,hpg,hmf⟩:=exists_supported_numerator_factorization m hm
  obtain ⟨u,a,b,r,hr,hpr,hxf⟩:=exists_supported_numerator_factorization (f^4*z)
    (mul_ne_zero (pow_ne_zero _ hf) hz)
  exact ⟨⟨um,am,bm,g,hg,hpg,hmf,u,a,b,r,hr,hpr,hxf⟩⟩

noncomputable def goodMaskRowData (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) :
    GoodMaskRowData m f z := Classical.choice (exists_goodMaskRowData m f z hm hf hz)

namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)

def movingIdeal : Ideal Eis := goodMaskMovingIdeal D.maskGood D.numeratorGood

lemma movingSupported : Supported D.movingIdeal :=
  goodMaskMovingIdeal_supported D.maskGood D.numeratorGood D.maskSupported D.numeratorSupported

def fixedFactor (Ψ:Eis→*ℂ) (Q:Ideal Eis) : Eis→*ℂ :=
  (Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
    D.numeratorSupported)*basePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)})

lemma numeratorFactor_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (n:Eis) :
    ‖(Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
      D.numeratorSupported) n‖≤1 := by
  change ‖Ψ n*numeratorBadTwist _ _ _ _ _ n‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΨ n)).trans (numeratorBadTwist_norm _ _ _ _ _ n)

lemma fixedFactor_periodic (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) :
    CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) (D.fixedFactor Ψ Q) := by
  have hn:=fixedNumeratorTwist_periodic Ψ Q hΨ D.numeratorUnit D.numeratorLambda
    D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change (Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
    D.numeratorSupported) x*basePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)}) x=
    (Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
    D.numeratorSupported) y*basePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)}) y
  rw [hn x y hxy,basePrimeRow_periodic D.movingIdeal D.movingSupported _ x y hxy]

lemma fixedFactor_norm (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hΨ:∀n,‖Ψ n‖≤1) (n:Eis) :
    ‖D.fixedFactor Ψ Q n‖≤1 := by
  change ‖((Ψ*numeratorBadTwist _ _ _ _ _) n)*(basePrimeRow _ _ _ n)‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (D.numeratorFactor_norm Ψ hΨ n)).trans (basePrimeRow_norm _ _ _ n)

theorem row_primary (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=D.fixedFactor Ψ Q n*
      freePrimeRow D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)}) n := by
  rw [rowTwist_eq_fixed_times_good_row_primary Ψ m f z hmLam hm2
    D.maskUnit D.maskLambda D.maskTwo D.maskGood D.maskSupported D.maskFactor
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn]
  change (Ψ*numeratorBadTwist _ _ _ _ _) n*idealRowHom n D.movingIdeal= _
  rw [idealRowHom_fixed_conductor_split D.movingIdeal D.movingSupported (Q*Ideal.span {(72:Eis)}) n]
  simp only [fixedFactor,MonoidHom.mul_apply]
  ring

theorem completedT_eq_fixedFactor (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (W:ℝ→ℂ) (X:ℝ) :
    completedT (rowTwist Ψ m f z) W X=
      completedT (D.fixedFactor Ψ Q*freePrimeRow D.movingIdeal D.movingSupported
        (Q*Ideal.span {(72:Eis)})) W X :=
  completedT_congr_primary _ _ (D.row_primary Ψ Q hmLam hm2) W X

lemma fixedCoefficient_norm (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hΨ:∀n,‖Ψ n‖≤1)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})] (h:Eis⧸Ideal.span {c}) :
    ‖fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h‖≤1 :=
  fixedThetaRowCoeff_norm c hc _ (D.fixedFactor_norm Ψ Q hΨ) h

end GoodMaskRowData

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O
namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)
variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (hm:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
include R I F Q0 hR hI hF hm hf hz hbad hcop hA hT

noncomputable def primeFiberEquiv :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0 ≃
      FreePrimeIndex D.movingIdeal Q0 :=
  goodMaskFreePrimeFiberEquiv R I F Q0 hR hI hF m f z hm hf hz
    D.maskUnit D.maskLambda D.maskTwo D.maskGood D.maskSupported D.maskFactor
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorFactor hbad hcop hA hT

lemma primeFiberEquiv_val
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT P).val.val=
      Sum.elim Subtype.val Subtype.val P := by
  cases P <;> rfl

lemma primeFiberEquiv_exponent
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ FreeReflection.pool R (Ideal.span {m}*F) Q0) :
    (normalizedFactors D.movingIdeal).count
      (D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT P).val.val%6=
      Sum.elim (fun _=>1) (fun S=>completedLocalExponent R F S.val) P :=
  goodMaskFreePrimeFiberEquiv_exponent R I F Q0 hR hI hF m f z hm hf hz
    D.maskUnit D.maskLambda D.maskTwo D.maskGood D.maskSupported D.maskFactor
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorFactor hbad hcop hA hT P

local notation "splitIndex" => D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT

noncomputable def activePrimeEquiv (A:Finset (FreePrimeIndex D.movingIdeal Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A) :
    PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ optionalPrimeActive splitIndex A ≃ A :=
  activePrimeUnionEquiv splitIndex A hactive

lemma activePrimeEquiv_exponent (A:Finset (FreePrimeIndex D.movingIdeal Q0))
    (hactive:∀P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)),splitIndex (Sum.inl P)∈A)
    (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F)) ⊕ optionalPrimeActive splitIndex A) :
    (normalizedFactors D.movingIdeal).count
      (D.activePrimeEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT A hactive P).val.val.val%6=
      Sum.elim (fun _=>1) (fun S=>completedLocalExponent R F S.val.val) P := by
  cases P with
  | inl P=>exact D.primeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inl P)
  | inr P=>exact D.primeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inr P.val)

end GoodMaskRowData

noncomputable def fiberGoodMaskRowData (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (m:Eis)
    (hm:m≠0) (hF:F≠0) (hrows:∀I∈rows,I≠0) (u:Eisˣ)
    (I:representativeRowFiber rows R (Ideal.span {m}*F)) :
    GoodMaskRowData m (ConcretePrimeRowBridge.idealGenerator F)
      (u.val*ConcretePrimeRowBridge.idealGenerator I.val) :=
  goodMaskRowData _ _ _ hm (ConcretePrimeRowBridge.idealGenerator_ne_zero F hF)
    (mul_ne_zero u.ne_zero (ConcretePrimeRowBridge.idealGenerator_ne_zero I.val
      (hrows I.val (Finset.mem_filter.mp I.property).1)))

end CanonicalRowCompletion

end

end OAI

end Source295

/- Original source: OAI/NumberTheory/DirichletL/RowCompletion/RowAmplitudes.lean; sha256: 73c29da29926d60ccfbd8ab04305948c11e9d4784b16f5adc385c08695903d07 -/
section Source296
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
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)
variable (Q:Ideal Eis) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})))

abbrev activeStratum :=
  freePrimaryControlledStratum D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported c hcQ h G A

def sourceRowScalar (Ψ:Eis→*ℂ) (u:Eisˣ) (n:ℕ) : ℂ := by
  letI : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported P.val
  exact fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
    G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val)*
    (D.activeStratum Q c hcQ h G A).modelRowPhase G.shape
      (fun P=>freePrimaryPrime_ne_zero D.movingIdeal _ D.movingSupported P.val)
      (fun P=>freePrimaryPrime_good D.movingIdeal _ D.movingSupported P.val)
      (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6) u n

lemma sourceRowScalar_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (u:Eisˣ) (n:ℕ) :
    ‖D.sourceRowScalar Q c hc hcQ h G A Ψ u n‖≤1 := by
  let : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported P.val
  have hp:(G.c0*∏P:A,freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val)≠0:=
    mul_ne_zero G.denominator_ne_zero (Finset.prod_ne_zero_iff.mpr
      (fun P _=>freePrimaryPrime_ne_zero D.movingIdeal _ D.movingSupported P.val))
  have hs:=G.shape.stratumShapeFactor_norm _ hp
  have hr:=(D.activeStratum Q c hcQ h G A).modelRowPhase_norm
    (mul_dvd_mul_left 9 G.denominator_dvd)
    (primary_finset_product Finset.univ
      (fun P:A=>freePrimaryPrime D.movingIdeal (Q*Ideal.span {(72:Eis)}) P.val)
      (fun P _=>freePrimaryPrime_primary D.movingIdeal _ D.movingSupported P.val))
    G.primary G.shape
    (fun P=>freePrimaryPrime_ne_zero D.movingIdeal _ D.movingSupported P.val)
    (fun P=>freePrimaryPrime_good D.movingIdeal _ D.movingSupported P.val)
    (fun P=>freePrimaryPrime_odd D.movingIdeal _ D.movingSupported P.val)
    (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6)
    (fun _=>Nat.mod_lt _ (by decide)) u n
  unfold sourceRowScalar
  rw [norm_mul,norm_mul,hs,hr,mul_one,mul_one]
  exact D.fixedCoefficient_norm Ψ Q hΨ c hc h

def sourceRowResidue : G.PhaseResidue :=
  Ideal.Quotient.mk _ (-((D.activeStratum Q c hcQ h G A).matrix (fun _=>1) 1 1)*
    (D.activeStratum Q c hcQ h G A).U)

def selectedSourceRowScalar (Ψ:Eis→*ℂ) (u:Eisˣ) (n:ℕ)
    (rho:G.PhaseResidue) (k dN dB:Ideal Eis) : ℂ :=
  if rho=D.sourceRowResidue Q c hcQ h G A then
    D.sourceRowScalar Q c hc hcQ h G A Ψ u n*residualArgumentPhase k 1 dN dB else 0

lemma selectedSourceRowScalar_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (u:Eisˣ) (n:ℕ)
    (rho:G.PhaseResidue) (k dN dB:Ideal Eis) :
    ‖D.selectedSourceRowScalar Q c hc hcQ h G A Ψ u n rho k dN dB‖≤1 := by
  unfold selectedSourceRowScalar
  split_ifs
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (D.sourceRowScalar_norm Q c hc hcQ h G A Ψ hΨ u n)).trans (residualArgumentPhase_norm_le_one k 1 dN dB)
  · simp

lemma sum_selectedSourceRowScalar [Fintype G.PhaseResidue]
    (Ψ:Eis→*ℂ) (u:Eisˣ) (n:ℕ) (k dN dB:Ideal Eis) :
    (∑rho:G.PhaseResidue,D.selectedSourceRowScalar Q c hc hcQ h G A Ψ u n rho k dN dB)=
      D.sourceRowScalar Q c hc hcQ h G A Ψ u n*residualArgumentPhase k 1 dN dB := by
  simp only [selectedSourceRowScalar,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end GoodMaskRowData
end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)

theorem completedT_eq_actualControlledSource
    (Q:Ideal Eis) (hQ:Q≠0) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (Ψ:Eis→*ℂ) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist Ψ m f z) W X=
      actualControlledSource D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported
        c hc hcQ G (D.fixedFactor Ψ Q) W X := by
  rw [D.completedT_eq_fixedFactor Ψ Q hmLam hm2 W X]
  apply fixedFree_completedT_eq_actualControlledSource D.movingIdeal _ D.movingSupported _
    c hc hcQ G (D.fixedFactor Ψ Q) (D.fixedFactor_periodic Ψ Q hΨ)
    (D.fixedFactor_norm Ψ Q hΨnorm) W lo hi hlo hsupp hW X hX
  apply mul_ne_zero hQ
  apply Ideal.span_singleton_eq_bot.not.mpr
  norm_num

end GoodMaskRowData
end

variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def residualActivePrimes (e:α⊕β ≃ γ) : Finset γ :=
  Finset.univ.image (fun a:α=>e (Sum.inl a))

omit [Fintype β] [Fintype γ] in
lemma residualActivePrimes_not_inr (e:α⊕β ≃ γ) (b:β) :
    e (Sum.inr b)∉residualActivePrimes e := by
  intro h
  obtain ⟨a,_,ha⟩:=Finset.mem_image.mp h
  cases e.injective ha

def nonresidualComplementMap (e:α⊕β ≃ γ) : β → {g:γ // g∉residualActivePrimes e} :=
  fun b=>⟨e (Sum.inr b),residualActivePrimes_not_inr e b⟩

omit [Fintype β] [Fintype γ] in
lemma nonresidualComplementMap_bijective (e:α⊕β ≃ γ) :
    Function.Bijective (nonresidualComplementMap e) := by
  constructor
  · intro a b hab
    exact Sum.inr.inj (e.injective (congrArg Subtype.val hab))
  · intro g
    obtain ⟨x,hx⟩:=e.surjective g.val
    cases x with
    | inl a=>
      exact (g.property (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,hx⟩)).elim
    | inr b=>exact ⟨b,Subtype.ext hx⟩

noncomputable def nonresidualComplementEquiv (e:α⊕β ≃ γ) :
    β ≃ {g:γ // g∉residualActivePrimes e} :=
  Equiv.ofBijective (nonresidualComplementMap e) (nonresidualComplementMap_bijective e)

omit [Fintype β] [Fintype γ] in
lemma nonresidualComplementEquiv_val (e:α⊕β ≃ γ) (b:β) :
    (nonresidualComplementEquiv e b).val=e (Sum.inr b) := rfl

omit [Fintype β] [Fintype γ] in
lemma complementActive_image (e:α⊕β ≃ γ) (B:Finset β) :
    (B.map (nonresidualComplementEquiv e).toEmbedding).image Subtype.val=
      B.image (fun b=>e (Sum.inr b)) := by
  simp only [Finset.map_eq_image,Finset.image_image,Function.comp_def,
    Equiv.toEmbedding_apply,nonresidualComplementEquiv_val]

lemma inactive_product_nonresidual (e:α⊕β ≃ γ) (z:γ → ℂ) (B:Finset β) :
    (∏g∈(Finset.univ:Finset {g:γ // g∉residualActivePrimes e})\
      B.map (nonresidualComplementEquiv e).toEmbedding,z g.val)=
      ∏b∈(Finset.univ:Finset β)\B,z (e (Sum.inr b)) := by
  symm
  apply Finset.prod_equiv (nonresidualComplementEquiv e)
  · intro b
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_map_equiv,
      Equiv.symm_apply_apply]
  · intro b hb
    rfl

theorem inactive_weight_nonresidual_subsets (e:α⊕β ≃ γ) (z:γ → ℂ)
    (hz:∀a:α,z (e (Sum.inl a))=0) (F:Finset γ → ℂ) :
    (∑A:Finset γ,(∏g∈(Finset.univ:Finset γ)\A,z g)*F A)=
      ∑B:Finset β,(∏b∈(Finset.univ:Finset β)\B,z (e (Sum.inr b)))*
        F (residualActivePrimes e∪B.image (fun b=>e (Sum.inr b))) := by
  have hres:∀g∈residualActivePrimes e,z g=0:=by
    intro g hg
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hg
    exact hz a
  rw [CompletedGauss.inactive_weight_optional_active (residualActivePrimes e) z hres F]
  symm
  apply Fintype.sum_equiv (nonresidualComplementEquiv e).finsetCongr
  intro B
  change _=(∏g∈(Finset.univ:Finset {g:γ // g∉residualActivePrimes e})\
    B.map (nonresidualComplementEquiv e).toEmbedding,z g.val)*
    F (residualActivePrimes e∪(B.map (nonresidualComplementEquiv e).toEmbedding).image Subtype.val)
  rw [inactive_product_nonresidual,complementActive_image]

end CanonicalRowCompletion

open scoped BigOperators Classical ContDiff

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma active_product_residual_equiv {ι β:Type*} [Fintype ι] [Fintype β]
    (I Q:Ideal Eis) (P:ι→Ideal Eis) (R:β→Ideal Eis)
    (E:PrimeIndex (rowResidualPart I Q)⊕β≃ι)
    (hres:∀r,P (E (Sum.inl r))=r.val) (hnonres:∀r,P (E (Sum.inr r))=R r) :
    (∏i,P i)=rowResidualPart I Q*∏i,R i := by
  rw [←E.prod_comp,Fintype.prod_sum_type]
  simp only [hres,hnonres]
  congr 1
  change (∏r:primeSupport (rowResidualPart I Q),r.val)=rowResidualPart I Q
  exact (Finset.prod_coe_sort (primeSupport (rowResidualPart I Q))
      (fun r : Ideal Eis => r)).trans
    (IdealMobiusDivisorSum.squarefree_support_product_self (rowResidualPart_squarefree I Q))

lemma actual_bracket_ideal_congr (P Q:Ideal Eis) [P.IsMaximal] [Q.IsMaximal]
    (hP:lambda∉P) (hQ:lambda∉Q) (hPQ:P=Q) (j:ℕ) (z:Eis) :
    bracket (actualSextic P hP) j (Ideal.Quotient.mk P z)=
      bracket (actualSextic Q hQ) j (Ideal.Quotient.mk Q z) := by
  subst Q
  rfl

theorem residual_equiv_coefficient {ι β:Type*} [Fintype ι] [Fintype β]
    (I F Q:Ideal Eis) (hFQ:F∣Q) (hbad:∀P∈fixedBadPrimes,P∣Q)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (R:β→Ideal Eis) [∀i,(R i).IsMaximal] (hR:∀i,lambda∉R i)
    (E:PrimeIndex (rowResidualPart I Q)⊕β≃ι)
    (hres:∀r,P (E (Sum.inl r))=r.val) (hnonres:∀r,P (E (Sum.inr r))=R r)
    (j:ι→ℕ) (hjres:∀r,j (E (Sum.inl r))=1)
    (hjnonres:∀r,j (E (Sum.inr r))=completedLocalExponent I F (R r))
    (e:β→Fin 3) (ρ q:ℝ) (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (m:ℕ) (n b:Ideal Eis) :
    let A:=reflectionExtractedDivisor R (fun r=>completedLocalExponent I F (R r)) e 1
    let B:=reflectionExtractedDivisor R (fun r=>completedLocalExponent I F (R r)) e 2
    unextractedCuspCoefficient P hg j (residualLabelVia E e) ρ q η σ m (A*n) (B*b)=
      4*canonicalRawBranchCoefficient R hR (fun r=>completedLocalExponent I F (R r)) e ρ q
        (fun l a c=>η l (A*a) (B*c))
        (fun l=>σ l*residualArgumentPhase (rowResidualPart I Q) 1 A B)
        (rowResidualPart I Q) m n b := by
  dsimp only
  rw [unextractedCuspCoefficient,reflectedBranch_drop_residual_equiv E P hg j hjres]
  have hchar (r:PrimeIndex (rowResidualPart I Q)) (z:Eis) :
      bracket (actualSextic (P (E (Sum.inl r))) (hg (E (Sum.inl r)))) 1 (Ideal.Quotient.mk _ z)=
      bracket (actualSextic r.val (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) r))
        (completedLocalExponent I F r.val) (Ideal.Quotient.mk _ z) := by
    rw [completedLocalExponent_residual I F Q hFQ]
    exact actual_bracket_ideal_congr _ _ _ _ (hres r) 1 z
  have hnbranch (a b:Eis):
      reflectedBranch (fun r=>P (E (Sum.inr r))) (fun r=>hg (E (Sum.inr r)))
        (fun r=>j (E (Sum.inr r))) e a b=
      reflectedBranch R hR (fun r=>completedLocalExponent I F (R r)) e a b := by
    unfold reflectedBranch
    apply Finset.prod_congr rfl
    intro r hr
    change reflectedLocalPiece (P (E (Sum.inr r))) _ (j (E (Sum.inr r))) (e r) a b=_
    simp only [hnonres r,hjnonres r]
  simp_rw [hchar]
  rw [hnbranch]
  have ht:=residual_coefficient_eq_canonical_argument I F Q hFQ hbad R hR
    (fun r=>completedLocalExponent I F (R r)) e ρ q (fun _=>1) η σ m n b
  simp only [one_mul] at ht
  convert ht using 1 ; ring

end CompletedGauss

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

theorem stratumBranchTerm_tsum_eq_rawValue
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    {I F Q:Ideal Eis} {levelBound K:ℝ} (d:ReflectedBranchData levelBound K I F Q)
    (hFQ:F∣Q) (hbad:∀P∈fixedBadPrimes,P∣Q) (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q)) (hk:k.val=rowResidualPart I Q)
    (E:PrimeIndex (rowResidualPart I Q)⊕d.primes≃ι)
    (hres:∀r,Ideal.span {p (E (Sum.inl r))}=r.val)
    (hnonres:∀r,Ideal.span {p (E (Sum.inr r))}=r.val)
    (hjres:∀r,j (E (Sum.inl r))=1)
    (hjnonres:∀r,j (E (Sum.inr r))=completedLocalExponent I F r.val)
    (hlevel:d.levelScale=G.levelScale) (u:Eisˣ) (W:ℝ→ℂ) (X:ℝ) :
    letI : ∀r:d.primes,r.val.IsMaximal:=d.maximal
    let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    let hA:=reflectionExtractedDivisor_ne_zero (fun r:d.primes=>r.val) (fun _r=>NeZero.ne _)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let hB:=reflectionExtractedDivisor_ne_zero (fun r:d.primes=>r.val) (fun _r=>NeZero.ne _)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    (∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      G.stratumBranchTerm D hp hg j u (residualLabelVia E d.label) W X (nonzeroDualDilation A B hA hB x))=
      4*d.rawValue
        (fun m n b=>G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u m (A*n) (B*b))
        (fun m k'=>D.modelRowPhase G.shape hp hg j u m*residualArgumentPhase k'.val 1 A B)
        W X 1 completedRamifiedStep k := by
  let : ∀r:d.primes,r.val.IsMaximal:=d.maximal
  dsimp only
  let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
    (fun r=>completedLocalExponent I F r.val) d.label 1
  let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
    (fun r=>completedLocalExponent I F r.val) d.label 2
  let η:=G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u
  let σ:=D.modelRowPhase G.shape hp hg j u
  have hfull:Ideal.span {∏i,p i}=k.val*∏r:d.primes,r.val := by
    rw [FiniteGaussPhase.span_finset_prod,hk]
    exact active_product_residual_equiv I Q (fun i=>Ideal.span {p i})
      (fun r:d.primes=>r.val) E hres hnonres
  have hk0:k.val≠0:=(mem_idealRange.mp k.property).1.1
  unfold ReflectedBranchData.rawValue
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  have hcoef:=residual_equiv_coefficient I F Q hFQ hbad (fun i=>Ideal.span {p i}) hg
    (fun r:d.primes=>r.val) d.good E hres hnonres j hjres hjnonres d.label
    1 completedRamifiedStep η σ x.1 x.2.1.val x.2.2.val
  have harg:
      (X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
        (1*completedRamifiedStep^x.1)^3*(Ideal.absNorm (A*x.2.1.val):ℝ)*
        (Ideal.absNorm (B*x.2.2.val):ℝ)^3=
      ((completedBranchScale K (X/d.levelScale) I F Q (fun r:d.primes=>r.val) d.label)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k.val:ℝ))^2)*
        (1*completedRamifiedStep^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
        (Ideal.absNorm x.2.2.val:ℝ)^3 := by
    rw [hlevel,completedBranchScale_raw_argument K X G.levelScale (1*completedRamifiedStep^x.1)
      I F Q (fun r:d.primes=>r.val) d.label k.val x.2.1.val x.2.2.val hK G.levelScale_pos hk0]
    rw [hfull]
    simp only [map_mul,Nat.cast_mul,mul_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  dsimp only [stratumBranchTerm,nonzeroDualDilation,rawDualKernelTerm]
  change unextractedCuspCoefficient (fun i=>Ideal.span {p i}) hg j (residualLabelVia E d.label)
      1 completedRamifiedStep η σ x.1 (A*x.2.1.val) (B*x.2.2.val)*_=_
  rw [hcoef,harg,hk]
  exact mul_assoc _ _ _

end FixedFourierGeometry
end CubicEisenstein

open scoped Classical BigOperators ContDiff

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass
open ConcretePrimeRowBridge SecondPassArithmetic
local notation "Eis" => ActualEisensteinCubic.O

def HasFixedShellModels (S:Finset (Ideal Eis)) (base:Eis→*ℂ)
    (rays:ℕ) (scale:ℂ) (ρ q level:ℝ) : Prop :=
  ∀ Ψ:Eis→*ℂ,IsBaseRayTwist base Ψ→∀m:Eis,m≠0→
    ∀ F:ℝ,∀f:idealRange F,∀u:Eisˣ,∀ W:ℝ→ℂ,∀a b:ℝ,
      0<a→Function.support W⊆Set.Icc a b→ContDiff ℝ ∞ W→
      ∀K X:ℝ,0<K→0<X→∀rows:Finset (Ideal Eis),
        (∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)→
        HasExactCompletedModels rays rows K X ρ q level f.val
          (Ideal.span {m*excludedGenerator S}*f.val) W
          (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator S) u f) scale

lemma normTwistedSource_contDiff (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (t:ℝ) :
    ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W t) := by
  have he:(CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t:ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t:=by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  rw [←he]
  exact (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t).smooth ⊤

theorem hasCanonicalThetaModels_of_fixed_shell_models
    (S:Finset (Ideal Eis)) (base:Eis→*ℂ) (rays:ℕ) (scale:ℂ) (ρ q level:ℝ)
    (hmodels:HasFixedShellModels S base rays scale ρ q level) :
    HasCanonicalThetaModels S base ρ q level := by
  intro A hA W hs hW κ hκ
  refine ⟨(rays:ℝ)^2*‖scale‖^2,by positivity,?_⟩
  intro Z K X F θ hZ hK hX hF hFZ Ψ hΨ m hm
  dsimp only
  intro hmargin
  refine ⟨rays,scale,?_,?_⟩
  · exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hκ.le)
  · intro u f H hH
    have hH0:H≠0:=((mem_shortCubeRange _ H).mp hH).1
    have hHN:(0:ℝ)<(Ideal.absNorm H:ℝ):=by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hH0)
    have hXH:0<X/(Ideal.absNorm H:ℝ)^3:=by positivity
    have hsTw:Function.support (CompletedHeight.normTwistedSource W θ)⊆
        Set.Icc (Real.exp (-A)) (Real.exp A):=
      (CompletedHeight.normTwistedSource_support W θ).trans hs
    have hTw:=normTwistedSource_contDiff W (Real.exp (-A)) (Real.exp A)
      (Real.exp_pos _) hs hW θ
    let rows:=((firstFrequencyDisk (2*K)).erase 0).image (fun z:Eis=>Ideal.span {z})
    have hrows:∀I∈rows,I≠0:=by
      intro I hI
      obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hI
      exact Ideal.span_singleton_eq_bot.not.mpr (Finset.mem_erase.mp hz).1
    intro j hj
    exact hmodels Ψ hΨ m hm F f u (CompletedHeight.normTwistedSource W θ)
      (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) hsTw hTw
      ((2:ℝ)^j) (X/(Ideal.absNorm H:ℝ)^3) (by positivity) hXH
      (completedRowDyad rows j) (completedRowDyad_bounds rows j hrows)

end CanonicalRowCompletion

open scoped Classical BigOperators

namespace CompletedGauss.ReflectedBranchData
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
variable {levelBound K:ℝ} {I F Q:Ideal Eis}
variable (d:ReflectedBranchData levelBound K I F Q)
variable (η:ℕ→Ideal Eis→Ideal Eis→ℂ)
variable (σ τ:ℕ→idealRange (completedResidualScale K I Q)→ℂ)
variable (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q))

lemma rawValue_congr_phase_at (h:∀m,σ m k=τ m k) :
    d.rawValue η σ W X ρ q k=d.rawValue η τ W X ρ q k := by
  unfold rawValue
  apply tsum_congr
  intro x
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient,h]

lemma rawValue_zero_phase : d.rawValue η (fun _ _=>0) W X ρ q k=0 := by
  unfold rawValue
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient,zero_mul,tsum_zero]

lemma rawValue_mul_phase_at (a:idealRange (completedResidualScale K I Q)→ℂ) :
    d.rawValue η (fun m l=>a l*σ m l) W X ρ q k=a k*d.rawValue η σ W X ρ q k := by
  unfold rawValue
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  unfold rawDualKernelTerm canonicalRawBranchCoefficient
  ring

lemma rawValue_select_phase_at (P:idealRange (completedResidualScale K I Q)→Prop)
    [DecidablePred P] :
    d.rawValue η (fun m l=>if P l then σ m l else 0) W X ρ q k=
      if P k then d.rawValue η σ W X ρ q k else 0 := by
  by_cases hp:P k
  · rw [ite_eq_left hp]
    exact d.rawValue_congr_phase_at η _ σ W X ρ q k (fun m=>ite_eq_left hp)
  · rw [ite_eq_right hp]
    calc
      _=d.rawValue η (fun _ _=>0) W X ρ q k:=
        d.rawValue_congr_phase_at η _ _ W X ρ q k (fun m=>ite_eq_right hp)
      _=0:=d.rawValue_zero_phase η W X ρ q k

end CompletedGauss.ReflectedBranchData

open scoped BigOperators Classical

namespace CanonicalRowCompletion
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]

def completeActiveSet (e:α⊕β ≃ γ) (B:Finset β) : Finset γ :=
  residualActivePrimes e∪B.image (fun b=>e (Sum.inr b))

omit [Fintype β] [Fintype γ] in
lemma completeActiveSet_residual (e:α⊕β ≃ γ) (B:Finset β) (a:α) :
    e (Sum.inl a)∈completeActiveSet e B :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩)

omit [Fintype γ] in
lemma optionalPrimeActive_completeActiveSet (e:α⊕β ≃ γ) (B:Finset β) :
    optionalPrimeActive e (completeActiveSet e B)=B := by
  ext b
  rw [mem_optionalPrimeActive]
  change e (Sum.inr b)∈residualActivePrimes e∪B.image (fun b=>e (Sum.inr b)) ↔ b∈B
  simp only [Finset.mem_union,residualActivePrimes_not_inr,false_or,Finset.mem_image]
  constructor
  · rintro ⟨b',hb',he⟩
    have hb:b'=b:=Sum.inr.inj (e.injective he)
    exact hb ▸ hb'
  · intro hb
    exact ⟨b,hb,rfl⟩

noncomputable def selectedActiveEquiv (e:α⊕β ≃ γ) (B:Finset β) :
    α⊕B ≃ completeActiveSet e B := by
  let t : B ≃ optionalPrimeActive e (completeActiveSet e B):={
    toFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    invFun:=fun b=>⟨b.val,by simpa only [optionalPrimeActive_completeActiveSet] using b.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  exact (Equiv.sumCongr (Equiv.refl _) t).trans
    (activePrimeUnionEquiv e (completeActiveSet e B) (completeActiveSet_residual e B))

omit [Fintype γ] in
lemma selectedActiveEquiv_inl (e:α⊕β ≃ γ) (B:Finset β) (a:α) :
    (selectedActiveEquiv e B (Sum.inl a)).val=e (Sum.inl a) := rfl

omit [Fintype γ] in
lemma selectedActiveEquiv_inr (e:α⊕β ≃ γ) (B:Finset β) (b:B) :
    (selectedActiveEquiv e B (Sum.inr b)).val=e (Sum.inr b.val) := rfl

end CanonicalRowCompletion

open scoped BigOperators Classical

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

def maskElement (q:ℕ) (m:Eis) : Eis := m*excludedGenerator (reflectionExcludedPrimes q)
def maskIdeal (q:ℕ) (m:Eis) (F:Ideal Eis) : Ideal Eis := Ideal.span {maskElement q m}*F
def freeConductor (q:ℕ) : Ideal Eis := CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}
abbrev RowIndex (q:ℕ) (m:Eis) (rows:Finset (Ideal Eis)) (R F:Ideal Eis) :=
  representativeRowFiber rows R (maskIdeal q m F)

lemma maskElement_ne_zero (q:ℕ) (m:Eis) (hm:m≠0) : maskElement q m≠0 :=
  mul_ne_zero hm (reflectionExcludedGenerator_ne_zero q)
lemma maskIdeal_ne_zero (q:ℕ) (m:Eis) (hm:m≠0) (F:Ideal Eis) (hF:F≠0) : maskIdeal q m F≠0 :=
  mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr (maskElement_ne_zero q m hm)) hF
lemma mask_bad (q:ℕ) (m:Eis) (F:Ideal Eis) : ∀P∈fixedBadPrimes,P∣maskIdeal q m F :=
  reflection_row_mask_bad q m F

variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)

noncomputable def data (J:RowIndex q m rows R F) :
    GoodMaskRowData (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val) :=
  fiberGoodMaskRowData rows R F (maskElement q m) (maskElement_ne_zero q m hm) hF.ne_zero hrows v J

noncomputable def splitIndex (J:RowIndex q m rows R F) :
    PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.pool R (maskIdeal q m F) (freeConductor q) ≃
      FreePrimeIndex (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q) := by
  have hJ:J.val≠0:=hrows J.val (Finset.mem_filter.mp J.property).1
  have hz:Ideal.span {v.val*ConcretePrimeRowBridge.idealGenerator J.val}=J.val:=by
    rw [Ideal.span_singleton_mul_left_unit v.isUnit,ConcretePrimeRowBridge.span_idealGenerator]
  have parts:=representativeFiber_parts rows R (maskIdeal q m F) J
  exact (data q m hm rows R F hF hrows v J).primeFiberEquiv R J.val F (freeConductor q)
    hR hJ hF (maskElement_ne_zero q m hm) (ConcretePrimeRowBridge.span_idealGenerator F) hz
    (mask_bad q m F) (residual_coprime_free_base q hq m F J.val) parts.1.symm parts.2.symm

noncomputable def activeSet (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (J:RowIndex q m rows R F) :
    Finset (FreePrimeIndex (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q)) :=
  completeActiveSet (splitIndex q hq m hm rows R F hR hF hrows v J) (reflectionSixSupport e)

def columnDivisor (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (side:Fin 3) : Ideal Eis :=
  reflectionExtractedDivisor
    (fun P:FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e=>P.val)
    (fun P=>completedLocalExponent R F P.val)
    (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e) side

variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

noncomputable def rowScalar (Ψ:Eis→*ℂ)
    (x:FreeReflection.FixedBranchIndex (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      R (maskIdeal q m F) (freeConductor q)) (n:ℕ) (J:RowIndex q m rows R F) : ℂ :=
  (data q m hm rows R F hF hrows v J).selectedSourceRowScalar
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) x.1.1
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) x.1.1)
    (activeSet q hq m hm rows R F hR hF hrows v x.2 J) Ψ x.1.2.2 n x.1.2.1
    (rowResidualPart J.val (maskIdeal q m F))
    (columnDivisor q m R F x.2 1) (columnDivisor q m R F x.2 2)

lemma rowScalar_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (x:FreeReflection.FixedBranchIndex (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      R (maskIdeal q m F) (freeConductor q)) (n:ℕ) (J:RowIndex q m rows R F) :
    ‖rowScalar q hq m hm rows R F hR hF hrows v Ψ x n J‖≤1 := by
  exact (data q m hm rows R F hF hrows v J).selectedSourceRowScalar_norm
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) x.1.1
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) x.1.1)
    (activeSet q hq m hm rows R F hR hF hrows v x.2 J) Ψ hΨ x.1.2.2 n x.1.2.1
    (rowResidualPart J.val (maskIdeal q m F))
    (columnDivisor q m R F x.2 1) (columnDivisor q m R F x.2 2)

noncomputable def reflectedFiber (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) :
    ReflectedFiberData (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      (fixedCuspLevelBound (reflectionConductor q)) K R F (maskIdeal q m F) :=
  FreeReflection.fixedRayFiberFromRows (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    rows R F (maskIdeal q m F) (freeConductor q) hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K
    (fun a J=>rowScalar q hq m hm rows R F hR hF hrows v Ψ a.1 a.2 J)
    (fun a J=>rowScalar_norm q hq m hm rows R F hR hF hrows v Ψ hΨ a.1 a.2 J)

lemma reflectedFiber_rowPhase (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq))
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6) (i:ℕ×ℕ×ℕ) :
    ((reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,e)).rowPhase i
        (fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
          (fun I hI=>⟨hrows I hI,hbound I hI⟩) J)=
      rowScalar q hq m hm rows R F hR hF hrows v Ψ (ray,e) i.1 J := by
  exact FreeReflection.fixedRayFiberFromRows_rowPhase _ _ _ _ _ _ _ _ _ _ _ _
    (mask_bad q m F) (fun I hI=>⟨hrows I hI,hbound I hI⟩) J ray e i

end CanonicalRowCompletion.ActualFiber

end

end OAI

end Source296

/- Original source: OAI/NumberTheory/DirichletL/GaussSum/ActiveReindexing.lean; sha256: 1164b2b1a3cd5ceb019521e6e908fb475d50feee94695759de0021c5446b5a18 -/
section Source297
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

open scoped BigOperators Classical ContDiff

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma active_product_admissible_equiv {ι β:Type*} [Fintype ι] [Fintype β]
    (k:Ideal Eis) (hk:Squarefree k) (P:ι→Ideal Eis) (R:β→Ideal Eis)
    (E:PrimeIndex k⊕β≃ι)
    (hres:∀r,P (E (Sum.inl r))=r.val) (hnonres:∀r,P (E (Sum.inr r))=R r) :
    (∏i,P i)=k*∏i,R i := by
  rw [←E.prod_comp,Fintype.prod_sum_type]
  simp only [hres,hnonres]
  congr 1
  change (∏r:primeSupport k,r.val)=k
  exact (Finset.prod_coe_sort (primeSupport k) (fun r:Ideal Eis=>r)).trans
    (IdealMobiusDivisorSum.squarefree_support_product_self hk)

theorem residual_bracket_extracted_admissible (k:Ideal Eis) (hk:Admissible k)
    (z:Eis) (A B n b:Ideal Eis) :
    (∏P:PrimeIndex k,
      bracket (actualSextic P.val (admissiblePrimeGood k hk P)) 1
        (Ideal.Quotient.mk P.val (z*primaryGenerator (A*n)*(primaryGenerator (B*b))^3)))=
      residualArgumentPhase k z A B*quadraticRow k (primaryGenerator (n*b)) := by
  rw [residual_bracket_product]
  rw [←quadraticRow_eq_primeIndex k hk,←quadraticRow_eq_primeIndex k hk]
  simp only [primaryGenerator_mul,residualArgumentPhase,canonical_quadraticRow_argument_mul k hk]
  ring

theorem residual_coefficient_eq_canonical_admissible {ι:Type*} [Fintype ι]
    (k:Ideal Eis) (hk:Admissible k)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (residualArgument:ℕ→Eis)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (rowPhase:ℕ→ℂ) (m:ℕ) (n b:Ideal Eis) :
    let A:=reflectionExtractedDivisor P j e 1
    let B:=reflectionExtractedDivisor P j e 2
    (rowPhase m*(∏p:PrimeIndex k,
        bracket (actualSextic p.val (admissiblePrimeGood k hk p)) 1
          (Ideal.Quotient.mk p.val (residualArgument m*primaryGenerator (A*n)*(primaryGenerator (B*b))^3))) *
      η m (A*n) (B*b)*reflectedBranch P hg j e (primaryGenerator (A*n)) (primaryGenerator (B*b)))/
        ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm (A*n):ℝ)*(Ideal.absNorm (B*b):ℝ):ℝ):ℂ)=
      4*canonicalRawBranchCoefficient P hg j e ρ q
        (fun l a c=>η l (A*a) (B*c))
        (fun l=>rowPhase l*residualArgumentPhase k (residualArgument l) A B) k m n b := by
  dsimp only
  rw [residual_bracket_extracted_admissible k hk]
  unfold canonicalRawBranchCoefficient reflectedDyadicCoefficient
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring

theorem residual_equiv_coefficient_admissible {ι β:Type*} [Fintype ι] [Fintype β]
    (k:Ideal Eis) (hk:Admissible k)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (R:β→Ideal Eis) [∀i,(R i).IsMaximal] (hR:∀i,lambda∉R i)
    (E:PrimeIndex k⊕β≃ι)
    (hres:∀r,P (E (Sum.inl r))=r.val) (hnonres:∀r,P (E (Sum.inr r))=R r)
    (j:ι→ℕ) (jβ:β→ℕ) (hjres:∀r,j (E (Sum.inl r))=1)
    (hjnonres:∀r,j (E (Sum.inr r))=jβ r)
    (e:β→Fin 3) (ρ q:ℝ) (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (m:ℕ) (n b:Ideal Eis) :
    let A:=reflectionExtractedDivisor R jβ e 1
    let B:=reflectionExtractedDivisor R jβ e 2
    unextractedCuspCoefficient P hg j (residualLabelVia E e) ρ q η σ m (A*n) (B*b)=
      4*canonicalRawBranchCoefficient R hR jβ e ρ q
        (fun l a c=>η l (A*a) (B*c))
        (fun l=>σ l*residualArgumentPhase k 1 A B) k m n b := by
  dsimp only
  rw [unextractedCuspCoefficient,reflectedBranch_drop_residual_equiv E P hg j hjres]
  have hchar (r:PrimeIndex k) (z:Eis) :
      bracket (actualSextic (P (E (Sum.inl r))) (hg (E (Sum.inl r)))) 1 (Ideal.Quotient.mk _ z)=
      bracket (actualSextic r.val (admissiblePrimeGood k hk r)) 1 (Ideal.Quotient.mk _ z) :=
    actual_bracket_ideal_congr _ _ _ _ (hres r) 1 z
  have hnbranch (a b:Eis):
      reflectedBranch (fun r=>P (E (Sum.inr r))) (fun r=>hg (E (Sum.inr r)))
        (fun r=>j (E (Sum.inr r))) e a b=reflectedBranch R hR jβ e a b := by
    unfold reflectedBranch
    apply Finset.prod_congr rfl
    intro r hr
    change reflectedLocalPiece (P (E (Sum.inr r))) _ (j (E (Sum.inr r))) (e r) a b=_
    simp only [hnonres r,hjnonres r]
  simp_rw [hchar]
  rw [hnbranch]
  have ht:=residual_coefficient_eq_canonical_admissible k hk R hR jβ e ρ q (fun _=>1) η σ m n b
  simp only [one_mul] at ht
  convert ht using 1 ; ring

end CompletedGauss

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

theorem stratumBranchTerm_tsum_eq_rawValue_at_row
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    {I F Q:Ideal Eis} {levelBound K:ℝ} (d:ReflectedBranchData levelBound K I F Q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (E:PrimeIndex k.val⊕d.primes≃ι)
    (hres:∀r,Ideal.span {p (E (Sum.inl r))}=r.val)
    (hnonres:∀r,Ideal.span {p (E (Sum.inr r))}=r.val)
    (hjres:∀r,j (E (Sum.inl r))=1)
    (hjnonres:∀r,j (E (Sum.inr r))=completedLocalExponent I F r.val)
    (hlevel:d.levelScale=G.levelScale) (u:Eisˣ) (W:ℝ→ℂ) (X:ℝ) :
    letI : ∀r:d.primes,r.val.IsMaximal:=d.maximal
    let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    let hA:=reflectionExtractedDivisor_ne_zero (fun r:d.primes=>r.val) (fun _r=>NeZero.ne _)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let hB:=reflectionExtractedDivisor_ne_zero (fun r:d.primes=>r.val) (fun _r=>NeZero.ne _)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    (∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      G.stratumBranchTerm D hp hg j u (residualLabelVia E d.label) W X (nonzeroDualDilation A B hA hB x))=
      4*d.rawValue
        (fun m n b=>G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u m (A*n) (B*b))
        (fun m k'=>D.modelRowPhase G.shape hp hg j u m*residualArgumentPhase k'.val 1 A B)
        W X 1 completedRamifiedStep k := by
  let : ∀r:d.primes,r.val.IsMaximal:=d.maximal
  dsimp only
  let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
    (fun r=>completedLocalExponent I F r.val) d.label 1
  let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
    (fun r=>completedLocalExponent I F r.val) d.label 2
  let η:=G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u
  let σ:=D.modelRowPhase G.shape hp hg j u
  have hfull:Ideal.span {∏i,p i}=k.val*∏r:d.primes,r.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact active_product_admissible_equiv k.val (mem_idealRange.mp k.property).1.2.1 (fun i=>Ideal.span {p i})
      (fun r:d.primes=>r.val) E hres hnonres
  have hk0:k.val≠0:=(mem_idealRange.mp k.property).1.1
  unfold ReflectedBranchData.rawValue
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  have hcoef:=residual_equiv_coefficient_admissible k.val (mem_idealRange.mp k.property).1 (fun i=>Ideal.span {p i}) hg
    (fun r:d.primes=>r.val) d.good E hres hnonres j
    (fun r=>completedLocalExponent I F r.val) hjres hjnonres d.label
    1 completedRamifiedStep η σ x.1 x.2.1.val x.2.2.val
  have harg:
      (X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
        (1*completedRamifiedStep^x.1)^3*(Ideal.absNorm (A*x.2.1.val):ℝ)*
        (Ideal.absNorm (B*x.2.2.val):ℝ)^3=
      ((completedBranchScale K (X/d.levelScale) I F Q (fun r:d.primes=>r.val) d.label)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k.val:ℝ))^2)*
        (1*completedRamifiedStep^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
        (Ideal.absNorm x.2.2.val:ℝ)^3 := by
    rw [hlevel,completedBranchScale_raw_argument K X G.levelScale (1*completedRamifiedStep^x.1)
      I F Q (fun r:d.primes=>r.val) d.label k.val x.2.1.val x.2.2.val hK G.levelScale_pos hk0]
    rw [hfull]
    simp only [map_mul,Nat.cast_mul,mul_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  dsimp only [stratumBranchTerm,nonzeroDualDilation,rawDualKernelTerm]
  change unextractedCuspCoefficient (fun i=>Ideal.span {p i}) hg j (residualLabelVia E d.label)
      1 completedRamifiedStep η σ x.1 (A*x.2.1.val) (B*x.2.2.val)*_=_
  rw [hcoef,harg]
  exact mul_assoc _ _ _

end FixedFourierGeometry
end CubicEisenstein

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

theorem sixPhaseFixedCuspBranch_value_eq_rawValue
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound
      e cusp u phaseArray hphase rowPhase hrow
    d.value W X ρ q k=
      d.rawValue (d.extractedFixedCuspArrayWithPhase cusp u phaseArray) rowPhase W X ρ q k := by
  exact (sixReflectedBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e
    (fixedCuspArrayWithPhase cusp u phaseArray)
    (fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase) rowPhase hrow).withExtractedFixedCuspArrayWithPhase_value cusp u phaseArray hphase rowPhase hrow
      W a b ha hsupp hW X ρ q hX hρ hq hK k hk

end CompletedGauss.FreeReflection
namespace CubicEisenstein.FixedFourierGeometry
open ActualEisensteinCubic CompletedGauss CompletedGauss.FreeReflection CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

theorem sixPhaseFixedCuspBranch_value_eq_geometric_rawValue
    {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (hbound:G.levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (v:G.PhaseResidue) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound G.levelScale G.levelScale_pos hbound
      e G.shape.index u (G.staticPhase v u) (G.staticPhase_norm_le_one v u) rowPhase hrow
    let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    d.value W X ρ q k=
      d.rawValue (fun m n b=>G.array v u m (A*n) (B*b)) rowPhase W X ρ q k := by
  exact sixPhaseFixedCuspBranch_value_eq_rawValue I F Q Q0 hI hQ K levelBound
    G.levelScale G.levelScale_pos hbound e G.shape.index u (G.staticPhase v u)
    (G.staticPhase_norm_le_one v u) rowPhase hrow W a b ha hsupp hW X ρ q hX hρ hq hK k hk

end CubicEisenstein.FixedFourierGeometry

open scoped BigOperators Classical

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

def supportActivePoolEquiv (I Q Q0:Ideal Eis) (e:pool I Q Q0 → Fin 6) :
    reflectionSixSupport e ≃ reflectionActivePool I Q Q0 e where
  toFun b:=⟨b.val.val,(mem_reflectionActivePool I Q Q0 e b.val).mpr
    (Finset.mem_filter.mp b.property).2⟩
  invFun P:=⟨⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem_reflectionActivePool I Q Q0 e _).mp P.property⟩⟩
  left_inv _b:=rfl
  right_inv _P:=rfl

lemma supportActivePoolEquiv_val (I Q Q0:Ideal Eis) (e:pool I Q Q0 → Fin 6)
    (b:reflectionSixSupport e) :
    (supportActivePoolEquiv I Q Q0 e b).val=b.val.val := rfl

lemma supportActivePoolEquiv_symm_val (I Q Q0:Ideal Eis) (e:pool I Q Q0 → Fin 6)
    (P:reflectionActivePool I Q Q0 e) :
    ((supportActivePoolEquiv I Q Q0 e).symm P).val.val=P.val := rfl

lemma supportActivePoolEquiv_label (I Q Q0:Ideal Eis) (e:pool I Q Q0 → Fin 6)
    (b:reflectionSixSupport e) :
    reflectionActiveLabel I Q Q0 e (supportActivePoolEquiv I Q Q0 e b)=
      reflectionSixLabel (e b.val) := rfl

def encodedActivePoolEquiv (I Q Q0:Ideal Eis) (B:Finset (pool I Q Q0)) (l:B → Fin 3) :
    B ≃ reflectionActivePool I Q Q0 (encodeReflectionSix ⟨B,l⟩) where
  toFun b:=⟨b.val.val,by
    rw [reflectionActivePool_encode]
    exact Finset.mem_image.mpr ⟨b.val,b.property,rfl⟩⟩
  invFun P:=⟨⟨P.val,reflectionActivePool_subset I Q Q0 _ P.property⟩,by
    have hp:P.val∈B.image Subtype.val:=by
      simpa only [reflectionActivePool_encode] using P.property
    obtain ⟨b,hb,he⟩:=Finset.mem_image.mp hp
    have he':b=⟨P.val,reflectionActivePool_subset I Q Q0 _ P.property⟩:=Subtype.ext he
    exact he' ▸ hb⟩
  left_inv b:=rfl
  right_inv P:=rfl

lemma encodedActivePoolEquiv_val (I Q Q0:Ideal Eis) (B:Finset (pool I Q Q0)) (l:B → Fin 3)
    (b:B) : (encodedActivePoolEquiv I Q Q0 B l b).val=b.val.val := rfl

lemma encodedActivePoolEquiv_label (I Q Q0:Ideal Eis) (B:Finset (pool I Q Q0)) (l:B → Fin 3)
    (b:B) :
    reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,l⟩) (encodedActivePoolEquiv I Q Q0 B l b)=l b := by
  change reflectionSixLabel (encodeReflectionSix ⟨B,l⟩ b.val)=l b
  apply Fin.ext
  simp only [encodeReflectionSix,dite_eq_left b.property,reflectionSixLabel]
  change (3+(l b).val)%3=(l b).val
  have hlt:=(l b).isLt
  omega

lemma encodedActivePoolEquiv_divisor (I F Q Q0:Ideal Eis)
    (B:Finset (pool I Q Q0)) (l:B → Fin 3) (side:Fin 3) :
    reflectionExtractedDivisor
      (fun P:reflectionActivePool I Q Q0 (encodeReflectionSix ⟨B,l⟩)=>P.val)
      (fun P=>completedLocalExponent I F P.val)
      (reflectionActiveLabel I Q Q0 (encodeReflectionSix ⟨B,l⟩)) side=
    reflectionExtractedDivisor (fun b:B=>b.val.val)
      (fun b=>completedLocalExponent I F b.val.val) l side := by
  unfold reflectionExtractedDivisor
  symm
  apply Fintype.prod_equiv (encodedActivePoolEquiv I Q Q0 B l)
  intro b
  rw [encodedActivePoolEquiv_label]
  rfl

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (J:RowIndex q m rows R F)

noncomputable def activeModelPrimeEquiv :
    PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e ≃
        activeSet q hq m hm rows R F hR hF hrows v e J :=
  (Equiv.sumCongr (Equiv.refl _)
    (FreeReflection.supportActivePoolEquiv R (maskIdeal q m F) (freeConductor q) e).symm).trans
    (selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) (reflectionSixSupport e))

lemma splitIndex_prime_val
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕ FreeReflection.pool R (maskIdeal q m F) (freeConductor q)) :
    (splitIndex q hq m hm rows R F hR hF hrows v J P).val.val=
      Sum.elim Subtype.val Subtype.val P := by
  cases P <;> rfl

lemma splitIndex_local_exponent
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕ FreeReflection.pool R (maskIdeal q m F) (freeConductor q)) :
    (UniqueFactorizationMonoid.normalizedFactors (data q m hm rows R F hF hrows v J).movingIdeal).count
      (splitIndex q hq m hm rows R F hR hF hrows v J P).val.val%6=
      Sum.elim (fun _=>1) (fun b=>completedLocalExponent R F b.val) P := by
  unfold splitIndex
  apply GoodMaskRowData.primeFiberEquiv_exponent

lemma activeModelPrimeEquiv_prime_val
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e) :
    (activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J P).val.val.val=
      Sum.elim Subtype.val Subtype.val P := by
  cases P <;> rfl

lemma activeModelPrimeEquiv_span
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e) :
    Ideal.span {freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q)
      (activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J P).val}=
      Sum.elim Subtype.val Subtype.val P := by
  rw [freePrimaryPrime_span _ _ (data q m hm rows R F hF hrows v J).movingSupported]
  exact activeModelPrimeEquiv_prime_val q hq m hm rows R F hR hF hrows v e J P

lemma activeModelPrimeEquiv_exponent
    (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F)) ⊕
      FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e) :
    (UniqueFactorizationMonoid.normalizedFactors (data q m hm rows R F hF hrows v J).movingIdeal).count
      (activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J P).val.val.val%6=
      Sum.elim (fun _=>1) (fun b=>completedLocalExponent R F b.val) P := by
  cases P with
  | inl P=>exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J (Sum.inl P)
  | inr P=>
    exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J
      (Sum.inr ⟨P.val,FreeReflection.reflectionActivePool_subset R (maskIdeal q m F) (freeConductor q) e P.property⟩)

end CanonicalRowCompletion.ActualFiber

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

noncomputable local instance inactiveField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P
noncomputable local instance inactiveFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

lemma finiteAdditiveFourierCoeff_zero {R:Type*} [Field R] [Fintype R]
    (ψ:AddChar R ℂ) (χ:MulChar R ℂ) (j:ℕ) :
    finiteAdditiveFourierCoeff ψ (fun x=>(χ^j) x) 0=zeroFourierCoefficient χ j := by
  simp only [finiteAdditiveFourierCoeff,zeroFourierCoefficient,neg_zero,zero_mul,
    AddChar.map_zero_eq_one,mul_one,div_eq_mul_inv]
  ring

lemma prime_zeroFourier_norm_formula (p:Eis) [(Ideal.span {p}).IsMaximal]
    (hp:p≠0) (hg:lambda∉Ideal.span {p}) (hodd:ringChar (Eis⧸Ideal.span {p})≠2)
    (j:ℕ) (hj:j<6) :
    finiteAdditiveFourierCoeff (quotientTrace p hp)
      (fun x=>(actualSextic (Ideal.span {p}) hg^j) x) 0=
      if j=0 then 1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹ else 0 := by
  rw [finiteAdditiveFourierCoeff_zero]
  have he:=canonical_zeroFourierCoefficient (Ideal.span {p}) hg hodd j hj
  convert he using 1
  exact congrArg (fun n:ℕ=>(if j=0 then 1-(n:ℂ)⁻¹ else 0)) (by rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card])

end CubicEisenstein

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
local instance inactivePoolMaximal (I Q Q0:Ideal Eis) (P:pool I Q Q0) : P.val.IsMaximal:=
  pool_maximal I Q Q0 P
noncomputable local instance inactivePoolField (I Q Q0:Ideal Eis) (P:pool I Q Q0) : Field (Eis⧸P.val):=
  Ideal.Quotient.field P.val
noncomputable local instance inactivePoolFintype (I Q Q0:Ideal Eis) (P:pool I Q Q0) : Fintype (Eis⧸P.val):=
  Fintype.ofFinite _

lemma reflectionInactiveStratumWeight_formula (I F Q Q0:Ideal Eis) (A:Finset (pool I Q Q0)) :
    reflectionInactiveStratumWeight I F Q Q0 A=
      ∏P∈(Finset.univ:Finset (pool I Q Q0))\A,
        if completedLocalExponent I F P.val=0 then 1-(Ideal.absNorm P.val:ℂ)⁻¹ else 0 := by
  unfold reflectionInactiveStratumWeight
  apply Finset.prod_congr (by ext P; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro P hP
  have he:=canonical_zeroFourierCoefficient P.val (pool_good I Q Q0 P) (pool_odd I Q Q0 P)
    (completedLocalExponent I F P.val) (Nat.mod_lt _ (by decide))
  convert he using 1
  exact congrArg (fun n:ℕ=>(if completedLocalExponent I F P.val=0 then 1-(n:ℂ)⁻¹ else 0))
    (by rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card])

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)
variable (R I F Q0:Ideal Eis) (hR:R≠0) (hI:I≠0) (hF:Squarefree F)
    (hm:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (hbad:∀P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (hcop:IsCoprime Q0 (rowResidualPart I (Ideal.span {m}*F)))
    (hA:rowPowerfulPart R=rowPowerfulPart I)
    (hT:rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
include R I F Q0 hR hI hF hm hf hz hbad hcop hA hT

theorem inactive_source_reindex (w:Finset (FreePrimeIndex D.movingIdeal Q0)→ℂ) :
    letI : ∀P:FreePrimeIndex D.movingIdeal Q0,
      (Ideal.span {freePrimaryPrime D.movingIdeal Q0 P}:Ideal Eis).IsMaximal:=
        freePrimaryPrime_maximal D.movingIdeal Q0 D.movingSupported
    let E:=D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT
    (∑A:Finset (FreePrimeIndex D.movingIdeal Q0),
      primeInactiveFourierWeight (freePrimaryPrime D.movingIdeal Q0)
        (freePrimaryPrime_ne_zero D.movingIdeal Q0 D.movingSupported)
        (freePrimaryPrime_good D.movingIdeal Q0 D.movingSupported)
        (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) A*w A)=
      ∑B:Finset (FreeReflection.pool R (Ideal.span {m}*F) Q0),
        FreeReflection.reflectionInactiveStratumWeight R F (Ideal.span {m}*F) Q0 B*
          w (residualActivePrimes E∪B.image (fun P=>E (Sum.inr P))) := by
  let : ∀P:FreePrimeIndex D.movingIdeal Q0,
      (Ideal.span {freePrimaryPrime D.movingIdeal Q0 P}:Ideal Eis).IsMaximal:=
        freePrimaryPrime_maximal D.movingIdeal Q0 D.movingSupported
  dsimp only
  let E:=D.primeFiberEquiv R I F Q0 hR hI hF hm hf hz hbad hcop hA hT
  let Z:FreePrimeIndex D.movingIdeal Q0→ℂ:=fun P=>
    if (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6=0 then
      1-(Ideal.absNorm P.val.val:ℂ)⁻¹ else 0
  have hzero (P:PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) : Z (E (Sum.inl P))=0:=by
    dsimp only [Z]
    rw [D.primeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inl P)]
    norm_num
  have hnonres (P:FreeReflection.pool R (Ideal.span {m}*F) Q0) :
      Z (E (Sum.inr P))=
        if completedLocalExponent R F P.val=0 then 1-(Ideal.absNorm P.val:ℂ)⁻¹ else 0:=by
    dsimp only [Z]
    rw [D.primeFiberEquiv_exponent R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inr P),
      D.primeFiberEquiv_val R I F Q0 hR hI hF hm hf hz hbad hcop hA hT (Sum.inr P)]
    rfl
  have hw (A:Finset (FreePrimeIndex D.movingIdeal Q0)) :
      primeInactiveFourierWeight (freePrimaryPrime D.movingIdeal Q0)
        (freePrimaryPrime_ne_zero D.movingIdeal Q0 D.movingSupported)
        (freePrimaryPrime_good D.movingIdeal Q0 D.movingSupported)
        (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) A=
      ∏P∈(Finset.univ:Finset (FreePrimeIndex D.movingIdeal Q0))\A,Z P:=by
    unfold primeInactiveFourierWeight
    apply Finset.prod_congr (by ext P; simp only [Finset.mem_sdiff,Finset.mem_univ])
    intro P hP
    rw [prime_zeroFourier_norm_formula _ _ _ (freePrimaryPrime_odd D.movingIdeal Q0 D.movingSupported P)
      _ (Nat.mod_lt _ (by decide)),freePrimaryPrime_span D.movingIdeal Q0 D.movingSupported P]
  simp only [hw]
  have he:=inactive_weight_nonresidual_subsets E Z hzero w
  refine Eq.trans ?_ (Eq.trans he ?_)
  · apply Finset.sum_congr (by ext A; simp only [Finset.mem_univ])
    intro A hA
    congr 1
    apply Finset.prod_congr (by ext P; simp only [Finset.mem_sdiff,Finset.mem_univ])
    intro P hP
    rfl
  apply Finset.sum_congr (by ext B; simp only [Finset.mem_univ])
  intro B hB
  congr 1
  · rw [FreeReflection.reflectionInactiveStratumWeight_formula]
    apply Finset.prod_congr (by ext P; simp only [Finset.mem_sdiff,Finset.mem_univ])
    intro P hP
    exact hnonres P
  · apply congrArg w
    ext P
    simp only [E,residualActivePrimes,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]

end GoodMaskRowData
end CanonicalRowCompletion

open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance rayUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _

theorem sum_fixedReflectionRay {M:Type*} [AddCommMonoid M]
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    [∀h:Eis⧸Ideal.span {c},Fintype (fixedFourierGeometry c hc h).PhaseResidue]
    (F:FixedReflectionRay c hc → M) :
    (∑r:FixedReflectionRay c hc,F r)=
      ∑h:Eis⧸Ideal.span {c},∑rho:(fixedFourierGeometry c hc h).PhaseResidue,
        ∑u:Eisˣ,F ⟨h,rho,u⟩ := by
  let e : FixedReflectionRay c hc ≃
      (Σ h : Eis⧸Ideal.span {c}, (fixedFourierGeometry c hc h).PhaseResidue × Eisˣ) :=
    Equiv.refl _
  calc
    _ = ∑ r : (Σ h : Eis⧸Ideal.span {c},
        (fixedFourierGeometry c hc h).PhaseResidue × Eisˣ), F (e.symm r) :=
      Fintype.sum_equiv e _ _ (fun r => congrArg F (e.symm_apply_apply r).symm)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro h hh
      exact Fintype.sum_prod_type _

theorem sum_fixedReflectionRayFin {M:Type*} [AddCommMonoid M]
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    [∀h:Eis⧸Ideal.span {c},Fintype (fixedFourierGeometry c hc h).PhaseResidue]
    (F:Fin (fixedReflectionRayCount c hc) → M) :
    (∑i:Fin (fixedReflectionRayCount c hc),F i)=
      ∑h:Eis⧸Ideal.span {c},∑rho:(fixedFourierGeometry c hc h).PhaseResidue,
        ∑u:Eisˣ,F (fixedReflectionRayEquiv c hc ⟨h,rho,u⟩) := by
  calc
    _=∑r:FixedReflectionRay c hc,F (fixedReflectionRayEquiv c hc r):=
      (Fintype.sum_equiv (fixedReflectionRayEquiv c hc) _ _ (fun _=>rfl)).symm
    _=_:=sum_fixedReflectionRay c hc _

end CubicEisenstein

end

end OAI

end Source297

/- Original source: OAI/NumberTheory/DirichletL/RowCompletion/ReflectedFibers.lean; sha256: c5969d08a8987606011e516173ab97859e045856f9d5755ebddbaa6e95e1a296 -/
section Source298
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

namespace CanonicalRowCompletion.GoodMaskRowData
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

theorem sum_selectedSourceRowScalar_mul {m f z:Eis} (D:GoodMaskRowData m f z)
    (Q:Ideal Eis) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})))
    [Fintype G.PhaseResidue] (Ψ:Eis→*ℂ) (u:Eisˣ) (n:ℕ)
    (k dN dB:Ideal Eis) (weight:G.PhaseResidue → ℂ) :
    (∑rho:G.PhaseResidue,D.selectedSourceRowScalar Q c hc hcQ h G A Ψ u n rho k dN dB*weight rho)=
      (D.sourceRowScalar Q c hc hcQ h G A Ψ u n*residualArgumentPhase k 1 dN dB)*
        weight (D.sourceRowResidue Q c hcQ h G A) := by
  simp only [selectedSourceRowScalar,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end CanonicalRowCompletion.GoodMaskRowData

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance rayUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _

variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
    [Fintype (Eis⧸Ideal.span {reflectionConductor q})]
    [∀h:Eis⧸Ideal.span {reflectionConductor q},
      Fintype (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue]

def rowResidue (h:Eis⧸Ideal.span {reflectionConductor q})
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (J:RowIndex q m rows R F) :
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue :=
  (data q m hm rows R F hF hrows v J).sourceRowResidue
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ideal q) h
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
    (activeSet q hq m hm rows R F hR hF hrows v e J)

def rowAmplitude (Ψ:Eis→*ℂ) (h:Eis⧸Ideal.span {reflectionConductor q}) (u:Eisˣ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (n:ℕ) (J:RowIndex q m rows R F) : ℂ :=
  (data q m hm rows R F hF hrows v J).sourceRowScalar
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) h
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
    (activeSet q hq m hm rows R F hR hF hrows v e J) Ψ u n*
      residualArgumentPhase (rowResidualPart J.val (maskIdeal q m F)) 1
        (columnDivisor q m R F e 1) (columnDivisor q m R F e 2)

omit [∀ h : Eis ⧸ Ideal.span {reflectionConductor q},
  Fintype (fixedFourierGeometry (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) h).PhaseResidue] in
lemma rowScalar_eq_ite (Ψ:Eis→*ℂ)
    (h:Eis⧸Ideal.span {reflectionConductor q}) (u:Eisˣ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (n:ℕ) (J:RowIndex q m rows R F)
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue) :
    rowScalar q hq m hm rows R F hR hF hrows v Ψ (⟨h,rho,u⟩,e) n J=
      if rho=rowResidue q hq m hm rows R F hR hF hrows v h e J then
        rowAmplitude q hq m hm rows R F hR hF hrows v Ψ h u e n J else 0 := rfl

theorem sum_rowScalar_phase_mul (Ψ:Eis→*ℂ)
    (h:Eis⧸Ideal.span {reflectionConductor q}) (u:Eisˣ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (n:ℕ) (J:RowIndex q m rows R F)
    (weight:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue → ℂ) :
    (∑rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue,
      rowScalar q hq m hm rows R F hR hF hrows v Ψ (⟨h,rho,u⟩,e) n J*weight rho)=
      rowAmplitude q hq m hm rows R F hR hF hrows v Ψ h u e n J*
        weight (rowResidue q hq m hm rows R F hR hF hrows v h e J) := by
  exact (data q m hm rows R F hF hrows v J).sum_selectedSourceRowScalar_mul
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) h
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
    (activeSet q hq m hm rows R F hR hF hrows v e J) Ψ u n
    (rowResidualPart J.val (maskIdeal q m F))
    (columnDivisor q m R F e 1) (columnDivisor q m R F e 2) weight

theorem sum_rowScalar_fixedRays (Ψ:Eis→*ℂ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (n:ℕ) (J:RowIndex q m rows R F)
    (weight:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq) → ℂ) :
    (∑ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq),
      rowScalar q hq m hm rows R F hR hF hrows v Ψ (ray,e) n J*weight ray)=
      ∑h:Eis⧸Ideal.span {reflectionConductor q},∑u:Eisˣ,
        rowAmplitude q hq m hm rows R F hR hF hrows v Ψ h u e n J*
          weight ⟨h,rowResidue q hq m hm rows R F hR hF hrows v h e J,u⟩ := by
  rw [sum_fixedReflectionRay]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact sum_rowScalar_phase_mul q hq m hm rows R F hR hF hrows v Ψ h u e n J _

theorem sum_rowScalar_fixedRayFin (Ψ:Eis→*ℂ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (n:ℕ) (J:RowIndex q m rows R F)
    (weight:Fin (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq)) → ℂ) :
    (∑i:Fin (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq)),
      rowScalar q hq m hm rows R F hR hF hrows v Ψ
        ((fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq)).symm i,e)
        n J*weight i)=
      ∑h:Eis⧸Ideal.span {reflectionConductor q},∑u:Eisˣ,
        rowAmplitude q hq m hm rows R F hR hF hrows v Ψ h u e n J*
          weight (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq)
            ⟨h,rowResidue q hq m hm rows R F hR hF hrows v h e J,u⟩) := by
  calc
    _=(∑ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq),
      rowScalar q hq m hm rows R F hR hF hrows v Ψ (ray,e) n J*
        weight (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray)):=by
      symm
      apply Fintype.sum_equiv (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      intro ray
      simp only [Equiv.symm_apply_apply]
    _=_:=sum_rowScalar_fixedRays q hq m hm rows R F hR hF hrows v Ψ e n J _

end CanonicalRowCompletion.ActualFiber

namespace CompletedGauss
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

theorem hasExactCompletedModels_of_representative_identity
    (rays:ℕ) (rows:Finset (Ideal Eis)) (K X ρ q levelBound:ℝ)
    (F Q:Ideal Eis) (W:ℝ→ℂ) (Ψ:Ideal Eis→Eis→*ℂ) (scale:ℂ)
    (model:∀I:Ideal Eis,I∈rows→ReflectedFiberData rays levelBound K I F Q)
    (hmodel:∀(I:Ideal Eis) (hI:I∈rows),∀J∈representativeRowFiber rows I Q,
      completedT (Ψ J) W X=scale*(model I hI).idealValue W X ρ q (rowResidualPart J Q)) :
    HasExactCompletedModels rays rows K X ρ q levelBound F Q W Ψ scale := by
  intro A hA T hT hnonempty
  obtain ⟨I,hI⟩:=hnonempty
  obtain ⟨hIrows,hIA,hIT⟩:=Finset.mem_filter.mp hI
  refine ⟨I,hI,model I hIrows,?_⟩
  intro J hJ
  apply hmodel I hIrows J
  simpa only [representativeRowFiber,hIA,hIT] using hJ

end CompletedGauss

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

noncomputable def sourcePrimeSet (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) :
    Finset (FreePrimeIndex (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q)) :=
  completeActiveSet (splitIndex q hq m hm rows R F hR hF hrows v J) B

omit [Fintype (Eis ⧸ span {reflectionConductor q})] in
lemma sourcePrimeSet_encode (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (e:B→Fin 3) (J:RowIndex q m rows R F) :
    activeSet q hq m hm rows R F hR hF hrows v (encodeReflectionSix ⟨B,e⟩) J=
      sourcePrimeSet q hq m hm rows R F hR hF hrows v B J := by
  unfold activeSet sourcePrimeSet
  rw [reflectionSixSupport_encode]

noncomputable abbrev sourceStratum
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) :=
  (data q m hm rows R F hF hrows v J).activeStratum
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q) (reflectionConductor_ideal q)
    h (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
    (sourcePrimeSet q hq m hm rows R F hR hF hrows v B J)

noncomputable def sourceStratumValue
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  let lengthScale:Ideal Eis:=(data q m hm rows R F hF hrows v J).movingIdeal
  have hL:Supported lengthScale:=(data q m hm rows R F hF hrows v J).movingSupported
  let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  letI : ∀P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
      (Ideal.span {freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ (data q m hm rows R F hF hrows v J).movingSupported P.val
  exact @ControlledStratumArithmetic.smoothedValue A (Finset.Subtype.fintype A)
    _ _ _ _ _ (sourceStratum q hq m hm rows R F hR hF hrows v h B J) _
    (mul_dvd_mul_left 9 G.denominator_dvd)
    (primary_finset_product Finset.univ (fun P:A=>freePrimaryPrime lengthScale (freeConductor q) P.val)
      (fun P _=>freePrimaryPrime_primary lengthScale (freeConductor q) hL P.val))
    G.primary G.shape (fun P=>freePrimaryPrime_ne_zero lengthScale (freeConductor q) hL P.val)
    G.denominator_ne_zero (fun P=>freePrimaryPrime_good lengthScale (freeConductor q) hL P.val)
    (fun P=>(UniqueFactorizationMonoid.normalizedFactors lengthScale).count P.val.val.val%6) W X

private lemma finset_union_image_decidableEq_eq {α β : Type*} (d₁ d₂ : DecidableEq β)
    (t : Finset β) (f : α → β) (s : Finset α) :
    @Union.union (Finset β) (@Finset.instUnion β d₁) t (@Finset.image α β d₁ f s) =
      @Union.union (Finset β) (@Finset.instUnion β d₂) t (@Finset.image α β d₂ f s) := by
  cases Subsingleton.elim d₁ d₂
  rfl

theorem completedT_eq_nonresidual_source
    (Ψ:Eis→*ℂ)
    (hΨ:CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ)
    (hΨnorm:∀n,‖Ψ n‖≤1)
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hsupp:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist Ψ (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
      thetaDerivativeScalar⁻¹*
        ∑h:Eis⧸Ideal.span {reflectionConductor q},
          fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
            ((data q m hm rows R F hF hrows v J).fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
          ∑B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),
            FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
              sourceStratumValue q hq m hm rows R F hR hF hrows v h B J W X := by
  let D:=data q m hm rows R F hF hrows v J
  let : ∀P:FreePrimeIndex D.movingIdeal (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}),
      (Ideal.span {freePrimaryPrime D.movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported
  let (A:Finset (FreePrimeIndex D.movingIdeal (freeConductor q))) :
      ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported P.val
  have hJ:J.val≠0:=hrows J.val (Finset.mem_filter.mp J.property).1
  have hz:Ideal.span {v.val*ConcretePrimeRowBridge.idealGenerator J.val}=J.val:=by
    rw [Ideal.span_singleton_mul_left_unit v.isUnit,ConcretePrimeRowBridge.span_idealGenerator]
  have parts:=representativeFiber_parts rows R (maskIdeal q m F) J
  have hsplit:splitIndex q hq m hm rows R F hR hF hrows v J=
      D.primeFiberEquiv R J.val F (freeConductor q) hR hJ hF (maskElement_ne_zero q m hm)
        (ConcretePrimeRowBridge.span_idealGenerator F) hz (mask_bad q m F)
        (residual_coprime_free_base q hq m F J.val) parts.1.symm parts.2.symm := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    cases x <;> rfl
  have hml:lambda∣maskElement q m:=by
    exact ((reflectionExcludedGenerator_bad q).1).trans (dvd_mul_left _ m)
  have hm2:(2:Eis)∣maskElement q m:=by
    exact ((reflectionExcludedGenerator_bad q).2).trans (dvd_mul_left _ m)
  rw [D.completedT_eq_actualControlledSource (CanonicalCoefficientClass.fixedBaseConductor q)
    (CanonicalCoefficientClass.fixedBaseConductor_ne_zero q hq) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q)
    (fun h=>fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
    Ψ hΨ hΨnorm hml hm2 W lo hi hlo hsupp hW X hX]
  unfold actualControlledSource
  apply congrArg (fun z:ℂ=>thetaDerivativeScalar⁻¹*z)
  apply Finset.sum_congr rfl
  intro h hh
  apply congrArg (fun z:ℂ=>fixedThetaRowCoeff (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*z)
  let weight : Finset (FreePrimeIndex D.movingIdeal (freeConductor q)) → ℂ := fun A =>
    @ControlledStratumArithmetic.smoothedValue A (Finset.Subtype.fintype A)
      _ _ _ _ _ (D.activeStratum (CanonicalCoefficientClass.fixedBaseConductor q)
        (reflectionConductor q) (reflectionConductor_ideal q) h
        (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h) A) _
      (mul_dvd_mul_left 9 (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).denominator_dvd)
      (primary_finset_product Finset.univ (fun P:A=>freePrimaryPrime D.movingIdeal (freeConductor q) P.val)
        (fun P _=>freePrimaryPrime_primary D.movingIdeal (freeConductor q) D.movingSupported P.val))
      (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).primary
      (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).shape
      (fun P=>freePrimaryPrime_ne_zero D.movingIdeal (freeConductor q) D.movingSupported P.val)
      (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).denominator_ne_zero
      (fun P=>freePrimaryPrime_good D.movingIdeal (freeConductor q) D.movingSupported P.val)
      (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6) W X
  convert D.inactive_source_reindex R J.val F (freeConductor q) hR hJ hF
    (maskElement_ne_zero q m hm) (ConcretePrimeRowBridge.span_idealGenerator F) hz
    (mask_bad q m F) (residual_coprime_free_base q hq m F J.val) parts.1.symm parts.2.symm
    weight using 1
  · apply Finset.sum_congr (by ext A; exact iff_of_true (Finset.mem_univ A) (Finset.mem_univ A))
    intro A hA
    rfl
  · apply Finset.sum_congr (by ext B; exact iff_of_true (Finset.mem_univ B) (Finset.mem_univ B))
    intro B hB
    congr 1
    calc
      sourceStratumValue q hq m hm rows R F hR hF hrows v h B J W X=
          weight (sourcePrimeSet q hq m hm rows R F hR hF hrows v B J):=by
        rfl
      _=_:=by
        apply congrArg weight
        rw [sourcePrimeSet, completeActiveSet, hsplit]
        exact finset_union_image_decidableEq_eq _ _ _ _ _

end CanonicalRowCompletion.ActualFiber

open scoped Classical BigOperators ContDiff

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedRayFiber_branch (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (r:FixedReflectionRay c hc) (e:pool I Q Q0→Fin 6) :
    let G:=fixedFourierGeometry c hc r.1
    (fixedRayFiber c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow).branch
      (fixedReflectionRayEquiv c hc r,e)=
      sixPhaseFixedCuspBranch I F Q Q0 hI hQ K (fixedCuspLevelBound c) G.levelScale
        G.levelScale_pos (G.levelScale_le hc) e G.shape.index r.2.2
        (G.staticPhase r.2.1 r.2.2) (G.staticPhase_norm_le_one r.2.1 r.2.2)
        (rowPhase (r,e)) (hrow (r,e)) := by
  let f : FixedReflectionRay c hc → ReflectedBranchData (fixedCuspLevelBound c) K I F Q := fun t =>
    let G:=fixedFourierGeometry c hc t.1
    sixPhaseFixedCuspBranch I F Q Q0 hI hQ K (fixedCuspLevelBound c) G.levelScale
      G.levelScale_pos (G.levelScale_le hc) e G.shape.index t.2.2
      (G.staticPhase t.2.1 t.2.2) (G.staticPhase_norm_le_one t.2.1 t.2.2)
      (rowPhase (t,e)) (hrow (t,e))
  change f ((fixedReflectionRayEquiv c hc).symm ((fixedReflectionRayEquiv c hc) r))=f r
  exact congrArg f ((fixedReflectionRayEquiv c hc).symm_apply_apply r)

theorem fixedRayFiberFromRows_branch_value
    (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ) → representativeRowFiber rows I Q → ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (J:representativeRowFiber rows I Q) (r:FixedReflectionRay c hc)
    (e:pool I Q Q0→Fin 6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (hk:completedResidualScale K I Q/2≤
      (Ideal.absNorm (fiberResidualIndex rows I Q K hbad hrows J).val:ℝ)) :
    let G:=fixedFourierGeometry c hc r.1
    let d:=(fixedRayFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).branch
      (fixedReflectionRayEquiv c hc r,e)
    let A:=reflectionExtractedDivisor (fun P:d.primes=>P.val)
      (fun P=>completedLocalExponent I F P.val) d.label 1
    let B:=reflectionExtractedDivisor (fun P:d.primes=>P.val)
      (fun P=>completedLocalExponent I F P.val) d.label 2
    d.value W X ρ q (fiberResidualIndex rows I Q K hbad hrows J)=
      d.rawValue (fun m n b=>G.array r.2.1 r.2.2 m (A*n) (B*b))
        (fun m _=>scalar ((r,e),m) J) W X ρ q (fiberResidualIndex rows I Q K hbad hrows J) := by
  let G:=fixedFourierGeometry c hc r.1
  let σ:ℕ→idealRange (completedResidualScale K I Q)→ℂ:=
    fun m=>extendFiberRowScalar rows I Q K scalar ((r,e),m)
  have hσ:∀m k,‖σ m k‖≤1:=fun m=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar ((r,e),m)
  have hb:=fixedRayFiber_branch c hc I F Q Q0 hI hQ K (fun _=>1) (by intro x;simp)
    (fun x m=>extendFiberRowScalar rows I Q K scalar (x,m))
    (fun x m=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar (x,m)) r e
  change (fixedRayFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).branch _=_ at hb
  let P (d : ReflectedBranchData (fixedCuspLevelBound c) K I F Q) : Prop :=
    let A := reflectionExtractedDivisor (fun P : d.primes => P.val)
      (fun P => completedLocalExponent I F P.val) d.label 1
    let B := reflectionExtractedDivisor (fun P : d.primes => P.val)
      (fun P => completedLocalExponent I F P.val) d.label 2
    d.value W X ρ q (fiberResidualIndex rows I Q K hbad hrows J) =
      d.rawValue (fun m n b => G.array r.2.1 r.2.2 m (A * n) (B * b))
        (fun m _ => scalar ((r, e), m) J) W X ρ q
        (fiberResidualIndex rows I Q K hbad hrows J)
  apply Eq.mpr (congrArg P hb)
  dsimp only [P]
  rw [G.sixPhaseFixedCuspBranch_value_eq_geometric_rawValue I F Q Q0 hI hQ K
    (fixedCuspLevelBound c) (G.levelScale_le hc) e r.2.1 r.2.2 σ hσ
    W a b ha hsupp hW X ρ q hX hρ hq hK (fiberResidualIndex rows I Q K hbad hrows J) hk]
  apply ReflectedBranchData.rawValue_congr_phase_at
  intro m
  exact extendFiberRowScalar_at_original rows I Q K hbad hrows scalar ((r,e),m) J

end CompletedGauss.FreeReflection

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

omit [Fintype (Eis ⧸ span {reflectionConductor q})] in
lemma columnDivisor_ne_zero
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6) (side:Fin 3) :
    columnDivisor q m R F e side≠0 := by
  let : ∀P:FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e,
      P.val.IsMaximal:=fun P=>FreeReflection.pool_maximal R (maskIdeal q m F) (freeConductor q)
        ⟨P.val,FreeReflection.reflectionActivePool_subset R (maskIdeal q m F) (freeConductor q) e P.property⟩
  exact reflectionExtractedDivisor_ne_zero
    (fun P:FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e=>P.val)
    (fun P=>NeZero.ne P.val) _ _ _

theorem reflectedFiber_branch_exact
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let D:=data q m hm rows R F hF hrows v J
    let A:=activeSet q hq m hm rows R F hR hF hrows v e J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    let S:=D.activeStratum (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
      (reflectionConductor_ideal q) h G A
    let E:=activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J
    letI : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
      fun P=>freePrimaryPrime_maximal _ _ D.movingSupported P.val
    let hp:=fun P:A=>freePrimaryPrime_ne_zero _ _ D.movingSupported P.val
    let hg:=fun P:A=>freePrimaryPrime_good _ _ D.movingSupported P.val
    let j:=fun P:A=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6
    let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
    let d:=(reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,e)
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    let dN:=columnDivisor q m R F e 1
    let dB:=columnDivisor q m R F e 2
    let hdN:=columnDivisor_ne_zero q m R F e 1
    let hdB:=columnDivisor_ne_zero q m R F e 2
    4*d.value W X 1 completedRamifiedStep k=
      if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
        (reflectionConductor_ideal q) h G A then
        fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
          (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
        G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
        ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
          @FixedFourierGeometry.stratumBranchTerm _ _ G A (Finset.Subtype.fintype A) _ _ S _ hp hg j u
            (residualLabelVia E (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e))
            W X (nonzeroDualDilation dN dB hdN hdB x)
      else 0 := by
  let D:=data q m hm rows R F hF hrows v J
  let A:=activeSet q hq m hm rows R F hR hF hrows v e J
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let S:=D.activeStratum (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ideal q) h G A
  let E:=activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J
  let : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ D.movingSupported P.val
  let hp:=fun P:A=>freePrimaryPrime_ne_zero _ _ D.movingSupported P.val
  let hg:=fun P:A=>freePrimaryPrime_good _ _ D.movingSupported P.val
  let j:=fun P:A=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6
  let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
  let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
  let scalar:(FreeReflection.FixedBranchIndex (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      R (maskIdeal q m F) (freeConductor q)×ℕ) → RowIndex q m rows R F → ℂ:=fun a J=>rowScalar q hq m hm rows R F hR hF hrows v Ψ a.1 a.2 J
  have hscalar:∀a J,‖scalar a J‖≤1:=fun a J=>rowScalar_norm q hq m hm rows R F hR hF hrows v Ψ hΨ a.1 a.2 J
  let σ:ℕ→idealRange (completedResidualScale K R (maskIdeal q m F))→ℂ:=
    fun n=>extendFiberRowScalar rows R (maskIdeal q m F) K scalar ((ray,e),n)
  have hσ:∀n k,‖σ n k‖≤1:=fun n=>extendFiberRowScalar_norm_le_one rows R (maskIdeal q m F)
    K scalar hscalar ((ray,e),n)
  let d:=FreeReflection.sixPhaseFixedCuspBranch R F (maskIdeal q m F) (freeConductor q) hR
    (maskIdeal_ne_zero q m hm F hF.ne_zero) K (fixedCuspLevelBound (reflectionConductor q))
    G.levelScale G.levelScale_pos (G.levelScale_le (reflectionConductor_ne_zero q hq))
    e G.shape.index u (G.staticPhase rho u) (G.staticPhase_norm_le_one rho u) σ hσ
  have hb:=FreeReflection.fixedRayFiber_branch (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    R F (maskIdeal q m F) (freeConductor q) hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K
    (fun _=>1) (by intro;simp)
    (fun x n=>extendFiberRowScalar rows R (maskIdeal q m F) K scalar (x,n))
    (fun x n=>extendFiberRowScalar_norm_le_one rows R (maskIdeal q m F) K scalar hscalar (x,n)) ray e
  change (reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
    (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,e)=d at hb
  dsimp only
  rw [hb]
  let dN:=columnDivisor q m R F e 1
  let dB:=columnDivisor q m R F e 2
  let η:=fun n I J=>G.array rho u n (dN*I) (dB*J)
  let τ:=fun n (l:idealRange (completedResidualScale K R (maskIdeal q m F)))=>
    @ControlledStratumArithmetic.modelRowPhase A (Finset.Subtype.fintype A) _ _ _ _ _ S _ G.shape hp hg j u n*residualArgumentPhase l.val 1 dN dB
  let weight:=fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
    G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)
  have hraw:d.value W X 1 completedRamifiedStep k=d.rawValue η σ W X 1 completedRamifiedStep k:=by
    exact G.sixPhaseFixedCuspBranch_value_eq_geometric_rawValue R F (maskIdeal q m F) (freeConductor q)
      hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K (fixedCuspLevelBound (reflectionConductor q))
      (G.levelScale_le (reflectionConductor_ne_zero q hq)) e rho u σ hσ
      W lo hi hlo hsupp hW X 1 completedRamifiedStep hX (by norm_num) completedRamifiedStep_gt_one hK k hk
  rw [hraw]
  have hσrow (n:ℕ):σ n k=rowScalar q hq m hm rows R F hR hF hrows v Ψ (ray,e) n J:=
    extendFiberRowScalar_at_original rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) scalar ((ray,e),n) J
  by_cases hphase:rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q)
    (reflectionConductor q) (reflectionConductor_ideal q) h G A
  · rw [ite_eq_left hphase]
    have hσmatch (n:ℕ):σ n k=weight*τ n k := by
      rw [hσrow]
      change (if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q)
        (reflectionConductor q) (reflectionConductor_ideal q) h G A then
        D.sourceRowScalar (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
          (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) h G A Ψ u n*
            residualArgumentPhase k.val 1 dN dB else 0)=_
      rw [ite_eq_left hphase]
      dsimp only [GoodMaskRowData.sourceRowScalar,weight,τ]
      change (weight*@ControlledStratumArithmetic.modelRowPhase A (Finset.Subtype.fintype A) _ _ _ _ _ S _ G.shape hp hg j u n)*residualArgumentPhase k.val 1 dN dB=
        weight*(@ControlledStratumArithmetic.modelRowPhase A (Finset.Subtype.fintype A) _ _ _ _ _ S _ G.shape hp hg j u n*residualArgumentPhase k.val 1 dN dB)
      exact mul_assoc _ _ _
    rw [d.rawValue_congr_phase_at η σ (fun n l=>weight*τ n l) W X 1 completedRamifiedStep k hσmatch,
      d.rawValue_mul_phase_at η τ W X 1 completedRamifiedStep k (fun _=>weight)]
    have hterm:=@FixedFourierGeometry.stratumBranchTerm_tsum_eq_rawValue_at_row _ _ G A
      (Finset.Subtype.fintype A) _ _ S _ hp hg j _ _ _ _ _ d hK k E
      (fun P=>activeModelPrimeEquiv_span q hq m hm rows R F hR hF hrows v e J (Sum.inl P))
      (fun P=>activeModelPrimeEquiv_span q hq m hm rows R F hR hF hrows v e J (Sum.inr P))
      (fun P=>activeModelPrimeEquiv_exponent q hq m hm rows R F hR hF hrows v e J (Sum.inl P))
      (fun P=>activeModelPrimeEquiv_exponent q hq m hm rows R F hR hF hrows v e J (Sum.inr P)) rfl u W X
    have harr:η=fun n I J=>G.array
        (Ideal.Quotient.mk _ (-(@ControlledStratumArithmetic.matrix A (Finset.Subtype.fintype A) _ _ _ _ _ S (fun _=>1) 1 1)*(@ControlledStratumArithmetic.U A (Finset.Subtype.fintype A) _ _ _ _ _ S))) u n (dN*I) (dB*J):=by
      dsimp only [η]
      rw [hphase]
      rfl
    rw [harr]
    calc
      _=weight*(4*d.rawValue
          (fun n I J=>G.array (Ideal.Quotient.mk _ (-(@ControlledStratumArithmetic.matrix A (Finset.Subtype.fintype A) _ _ _ _ _ S (fun _=>1) 1 1)*(@ControlledStratumArithmetic.U A (Finset.Subtype.fintype A) _ _ _ _ _ S))) u n (dN*I) (dB*J))
          τ W X 1 completedRamifiedStep k):=by ring
      _=_:=congrArg (fun z:ℂ=>weight*z) hterm.symm
  · rw [ite_eq_right hphase]
    have hσzero (n:ℕ):σ n k=0 := by
      rw [hσrow]
      change (if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q)
        (reflectionConductor q) (reflectionConductor_ideal q) h G A then _ else 0)=0
      rw [ite_eq_right hphase]
    rw [d.rawValue_congr_phase_at η σ (fun _ _=>0) W X 1 completedRamifiedStep k hσzero,
      d.rawValue_zero_phase η W X 1 completedRamifiedStep k,mul_zero]

end CanonicalRowCompletion.ActualFiber

open scoped Classical

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CubicEisenstein CanonicalCoefficientClass
local notation "Eis" => ActualEisensteinCubic.O

theorem dirichletTarget_of_reflection_shells
    (hmodels:∀(q₀:ℕ) [NeZero q₀] (χ:DirichletCharacter ℂ q₀),
      ∃(rays:ℕ) (scale:ℂ),
        HasFixedShellModels (reflectionExcludedPrimes q₀) (initialBase χ)
          rays scale 1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q₀))) :
    ShortDraft.DirichletTarget := by
  apply dirichletTarget_of_theta_models
  intro q₀ hq₀ χ
  obtain ⟨rays,scale,hm⟩:=hmodels q₀ χ
  refine ⟨reflectionExcludedPrimes q₀,reflectionExcludedPrimes_bad q₀,
    reflectionExcludedPrimes_prime q₀,1,completedRamifiedStep,
    fixedCuspLevelBound (reflectionConductor q₀),by norm_num,
    completedRamifiedStep_gt_one,reflectionLevelBound_ge_one q₀ (NeZero.ne q₀),?_⟩
  exact hasCanonicalThetaModels_of_fixed_shell_models
    (reflectionExcludedPrimes q₀) (initialBase χ) rays scale 1 completedRamifiedStep
    (fixedCuspLevelBound (reflectionConductor q₀)) hm

end CanonicalRowCompletion

namespace ShortDraft

theorem zeta_nonvanishing_of_dirichletTarget (h:DirichletTarget)
    (s:ℂ) (hs:(23/24:ℝ)<s.re) (hs1:s≠1) : riemannZeta s≠0 := by
  have he:=h 1 (1:DirichletCharacter ℂ 1) s hs (by simp only [true_and]; exact hs1)
  simpa only [DirichletCharacter.LFunction_modOne_eq] using he

end ShortDraft

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

def sourceDivisor (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (l:B→Fin 3) (side:Fin 3) : Ideal Eis :=
  reflectionExtractedDivisor (fun b:B=>b.val.val) (fun b=>completedLocalExponent R F b.val.val) l side

omit [Fintype (Eis ⧸ span {reflectionConductor q})] in
lemma sourceDivisor_ne_zero (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (l:B→Fin 3) (side:Fin 3) : sourceDivisor q m R F B l side≠0 := by
  have hn (b:B):b.val.val≠0:=by
    let : b.val.val.IsMaximal:=FreeReflection.pool_maximal R (maskIdeal q m F) (freeConductor q) b.val
    exact NeZero.ne _
  exact reflectionExtractedDivisor_ne_zero _ hn
    (fun b=>completedLocalExponent R F b.val.val) l side

noncomputable def sourceCompressedTerm
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) (u:Eisˣ) (l:B→Fin 3) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  let lengthScale:Ideal Eis:=(data q m hm rows R F hF hrows v J).movingIdeal
  have hL:Supported lengthScale:=(data q m hm rows R F hF hrows v J).movingSupported
  let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let E:=selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) B
  letI : ∀P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
      (Ideal.span {freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ (data q m hm rows R F hF hrows v J).movingSupported P.val
  exact ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
    @FixedFourierGeometry.stratumBranchTerm _ _ G A (Finset.Subtype.fintype A) _ _
      (sourceStratum q hq m hm rows R F hR hF hrows v h B J) _
      (fun P:A=>freePrimaryPrime_ne_zero lengthScale (freeConductor q) hL P.val)
      (fun P:A=>freePrimaryPrime_good lengthScale (freeConductor q) hL P.val)
      (fun P:A=>(UniqueFactorizationMonoid.normalizedFactors lengthScale).count P.val.val.val%6)
      u (residualLabelVia E l) W X
      (nonzeroDualDilation (sourceDivisor q m R F B l 1) (sourceDivisor q m R F B l 2)
        (sourceDivisor_ne_zero q m R F B l 1) (sourceDivisor_ne_zero q m R F B l 2) x)

end CanonicalRowCompletion.ActualFiber

end

end OAI

end Source298

/- Original source: OAI/NumberTheory/DirichletL/RowCompletion/BranchDecoding.lean; sha256: 61322cab57ec244b17c5d2175464de8a7806d65b1b7c4519bc7f6644d9465cd5 -/
section Source299
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

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma initialOrbit_reflection_inputs {q:ℕ} (χ:DirichletCharacter ℂ q)
    (Ψ:Eis→*ℂ) (hΨ:IsBaseRayTwist (initialBase χ) Ψ) :
    FactorsModulo (fixedBaseConductor q) Ψ ∧ (∀n:Eis,‖Ψ n‖≤1) :=
  ⟨initialOrbit_factorsModulo χ Ψ hΨ,fun n=>hΨ.norm_le (initialBase_norm χ) n⟩

lemma canonicalLabel_squarefree {X:ℝ} (f:idealRange X) : Squarefree f.val :=
  (mem_idealRange.mp f.property).1.2.1

lemma canonicalLabel_generator_ne_zero {X:ℝ} (f:idealRange X) :
    ConcretePrimeRowBridge.idealGenerator f.val≠0 :=
  ConcretePrimeRowBridge.idealGenerator_ne_zero f.val (mem_idealRange.mp f.property).1.1

lemma unitRowFamily_actual {X:ℝ} (f:idealRange X) (Ψ:Eis→*ℂ) (q:ℕ) (m:Eis)
    (u:Eisˣ) (I:Ideal Eis) :
    CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator (reflectionExcludedPrimes q)) u f I=
      rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator f.val)
        (u.val*ConcretePrimeRowBridge.idealGenerator I) := rfl

theorem fixedShellModels_of_actual_fiber_identity
    (q:ℕ) (hq:q≠0) (χ:DirichletCharacter ℂ q) (scale:ℂ)
    [Fintype (Eis⧸Ideal.span {reflectionConductor q})]
    (hidentity:
      ∀(Ψ:Eis→*ℂ),FactorsModulo (fixedBaseConductor q) Ψ→
      ∀hΨnorm:(∀n:Eis,‖Ψ n‖≤1),∀(m:Eis)(hm:m≠0),
      ∀(F:Ideal Eis)(hF:Squarefree F)(u:Eisˣ),∀(W:ℝ→ℂ)(a b:ℝ),
      0<a→Function.support W⊆Set.Icc a b→ContDiff ℝ ∞ W→
      ∀(K X:ℝ),0<K→0<X→∀rows:Finset (Ideal Eis),
      ∀hrows:(∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K),
      ∀(R:Ideal Eis)(hR:R∈rows),∀J:ActualFiber.RowIndex q m rows R F,
        completedT (rowTwist Ψ (ActualFiber.maskElement q m)
          (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
        scale*(ActualFiber.reflectedFiber q hq m hm rows R F (hrows R hR).1 hF
          (fun I hI=>(hrows I hI).1) u K Ψ hΨnorm).idealValue W X 1 completedRamifiedStep
            (rowResidualPart J.val (ActualFiber.maskIdeal q m F))) :
    HasFixedShellModels (reflectionExcludedPrimes q) (initialBase χ)
      (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq)) scale
      1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q)) := by
  intro Ψ hΨ m hm Xlabel f u W a b ha hs hW K X hK hX rows hrows
  obtain ⟨hperiod,hnorm⟩:=initialOrbit_reflection_inputs χ Ψ hΨ
  let models:=fun (R:Ideal Eis) (hR:R∈rows)=>
    ActualFiber.reflectedFiber q hq m hm rows R f.val (hrows R hR).1 (canonicalLabel_squarefree f)
      (fun I hI=>(hrows I hI).1) u K Ψ hnorm
  apply hasExactCompletedModels_of_representative_identity
    (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
    rows K X 1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q)) f.val
    (ActualFiber.maskIdeal q m f.val) W
    (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator (reflectionExcludedPrimes q)) u f)
    scale models
  intro R hR J hJ
  rw [unitRowFamily_actual]
  exact hidentity Ψ hperiod hnorm m hm f.val (canonicalLabel_squarefree f) u W a b ha hs hW
    K X hK hX rows hrows R hR ⟨J,hJ⟩

end

theorem finite_selected_branch_collection
    {H U B:Type*} {R:H→Type*} {E:B→Type*}
    [Fintype H] [Fintype U] [Fintype B]
    [∀h,Fintype (R h)] [∀b,Fintype (E b)]
    (f:(h:H)→R h→U→(b:B)→E b→ℂ)
    (g:H→U→(b:B)→E b→ℂ)
    (chosen:(h:H)→B→R h) (α:H→ℂ) (shape:H→B→ℂ) (w:B→ℂ)
    (hbranch:∀h r u b e,4*f h r u b e=
      if r=chosen h b then α h*shape h b*g h u b e else 0) :
    4*(∑h,∑r:R h,∑u,∑b,w b*∑e:E b,f h r u b e)=
      ∑h,α h*∑b,w b*shape h b*∑u,∑e:E b,g h u b e := by
  have hpoint (h:H) (b:B) :
      4*(∑r:R h,∑u,∑e:E b,f h r u b e)=
        α h*shape h b*(∑u,∑e:E b,g h u b e) := by
    simp_rw [Finset.mul_sum,hbranch]
    calc
      _=∑r:R h,if r=chosen h b then
          α h*shape h b*(∑u,∑e:E b,g h u b e) else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        by_cases he:r=chosen h b
        · simp only [he,ite_true,Finset.mul_sum]
        · simp only [he,ite_false,Finset.sum_const_zero]
      _=_:=by simp [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hswap : (∑r:R h,∑u,∑b,w b*∑e:E b,f h r u b e)=
      ∑b,w b*(∑r:R h,∑u,∑e:E b,f h r u b e) := by
    calc
      _=∑r:R h,∑b,∑u,w b*∑e:E b,f h r u b e := by
        apply Finset.sum_congr rfl
        intro r hr
        exact Finset.sum_comm
      _=∑b,∑r:R h,∑u,w b*∑e:E b,f h r u b e := Finset.sum_comm
      _=_:=by simp_rw [Finset.mul_sum]
  rw [hswap,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    _=w b*(4*(∑r:R h,∑u,∑e:E b,f h r u b e)) := by ring
    _=w b*(α h*shape h b*(∑u,∑e:E b,g h u b e)) := by rw [hpoint]
    _=_:=by ring

end CanonicalRowCompletion

open scoped BigOperators Classical ContDiff

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

theorem fixedRayFiberFromRows_value
    (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=fixedRayFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar
    d.value W X ρ q k=
      ∑r:FixedReflectionRay c hc,∑B:Finset (pool I Q Q0),
        reflectionInactiveStratumWeight I F Q Q0 B*
          ∑l:B→Fin 3,(d.branch (fixedReflectionRayEquiv c hc r,encodeReflectionSix ⟨B,l⟩)).value W X ρ q k := by
  dsimp only
  unfold fixedRayFiberFromRows
  rw [fixedRayFiber_value]
  simp only [mul_one, Finset.mul_sum]

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion.ActualFiber

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_value (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (W:ℝ→ℂ) (X:ℝ) (k:idealRange (completedResidualScale K R (maskIdeal q m F))) :
    let d:=reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ
    d.value W X 1 completedRamifiedStep k=
      ∑r:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq),
        ∑B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),
          FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
            ∑l:B→Fin 3,(d.branch (fixedReflectionRayEquiv (reflectionConductor q)
              (reflectionConductor_ne_zero q hq) r,encodeReflectionSix ⟨B,l⟩)).value W X 1 completedRamifiedStep k := by
  exact FreeReflection.fixedRayFiberFromRows_value (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    rows R F (maskIdeal q m F) (freeConductor q) hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K
    (fun a J=>rowScalar q hq m hm rows R F hR hF hrows v Ψ a.1 a.2 J)
    (fun a J=>rowScalar_norm q hq m hm rows R F hR hF hrows v Ψ hΨ a.1 a.2 J)
    W X 1 completedRamifiedStep k

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

omit [Fintype (Eis ⧸ Ideal.span {reflectionConductor q})] in
theorem sourceStratumValue_eq_compressed
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hsupp:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    sourceStratumValue q hq m hm rows R F hR hF hrows v h B J W X=
      fixedRadialCoefficientScalar*
        (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).shape.stratumShapeFactor
          ((fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).c0*
            ∏P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
              freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q) P.val)*
        ∑'u:Eisˣ,∑l:B→Fin 3,sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X := by
  let lengthScale:Ideal Eis:=(data q m hm rows R F hF hrows v J).movingIdeal
  have hL:Supported lengthScale:=(data q m hm rows R F hF hrows v J).movingSupported
  let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
  let p:A→Eis:=fun P=>freePrimaryPrime lengthScale (freeConductor q) P.val
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let E:=selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) B
  let j:A→ℕ:=fun P=>(UniqueFactorizationMonoid.normalizedFactors lengthScale).count P.val.val.val%6
  let : ∀P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
      (Ideal.span {freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ (data q m hm rows R F hF hrows v J).movingSupported P.val
  have hjres (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F))) : j (E (Sum.inl P))=1:=by
    change (UniqueFactorizationMonoid.normalizedFactors lengthScale).count
      (E (Sum.inl P)).val.val.val%6=1
    rw [selectedActiveEquiv_inl]
    exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J (Sum.inl P)
  have hPB:(fun b:B=>Ideal.span {p (E (Sum.inr b))}:B→Ideal Eis)=(fun b=>b.val.val):=by
    funext b
    rw [show p (E (Sum.inr b))=freePrimaryPrime lengthScale (freeConductor q) (E (Sum.inr b)).val from rfl,
      freePrimaryPrime_span lengthScale (freeConductor q) hL,selectedActiveEquiv_inr]
    exact splitIndex_prime_val q hq m hm rows R F hR hF hrows v J (Sum.inr b.val)
  have hjB:(fun b:B=>j (E (Sum.inr b)))=(fun b=>completedLocalExponent R F b.val.val):=by
    funext b
    change (UniqueFactorizationMonoid.normalizedFactors lengthScale).count
      (E (Sum.inr b)).val.val.val%6=completedLocalExponent R F b.val.val
    rw [selectedActiveEquiv_inr]
    exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J (Sum.inr b.val)
  have hdiv (l:B→Fin 3) (side:Fin 3) :
      reflectionExtractedDivisor (fun b:B=>Ideal.span {p (E (Sum.inr b))})
        (fun b:B=>j (E (Sum.inr b))) l side=sourceDivisor q m R F B l side := by
    rw [hPB,hjB]
    rfl
  have hcop:Pairwise (fun a b:A=>IsCoprime (Ideal.span {p a}) (Ideal.span {p b})):=by
    intro a b hab
    exact freePrimaryPrime_coprime lengthScale (freeConductor q) hL (fun he=>hab (Subtype.ext he))
  have he := @FixedFourierGeometry.smoothedValue_eq_nonresidual_equiv _ _ G
    _ B A _ (Finset.Subtype.fintype B) (Finset.Subtype.fintype A) p _ E
    (sourceStratum q hq m hm rows R F hR hF hrows v h B J)
    (fun P => freePrimaryPrime_maximal lengthScale (freeConductor q) hL P.val)
    (mul_dvd_mul_left 9 G.denominator_dvd)
    (primary_finset_product Finset.univ p (fun P _=>freePrimaryPrime_primary lengthScale (freeConductor q) hL P.val))
    (fun P=>freePrimaryPrime_ne_zero lengthScale (freeConductor q) hL P.val) hcop
    (fun P=>freePrimaryPrime_good lengthScale (freeConductor q) hL P.val)
    (fun P=>freePrimaryPrime_odd lengthScale (freeConductor q) hL P.val) j
    (fun _=>Nat.mod_lt _ (by decide)) hjres W lo hi hlo hsupp hW X hX
  refine he.trans ?_
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏P:A,p P)*z)
  apply tsum_congr
  intro u
  apply Finset.sum_congr (by ext l; simp only [Finset.mem_univ])
  intro l hl
  unfold sourceCompressedTerm
  dsimp only
  apply tsum_congr
  intro x
  congr 1
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun I:Ideal Eis=>I*x.2.1.val) (hdiv l 1)
    · apply Subtype.ext
      exact congrArg (fun I:Ideal Eis=>I*x.2.2.val) (hdiv l 2)

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma one_le_residualScale (q:ℕ) (m:Eis) (rows:Finset (Ideal Eis))
    (R F:Ideal Eis) (K:ℝ)
    (hrows:∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F) :
    1≤completedResidualScale K R (maskIdeal q m F) := by
  have hJ:=hrows J.val (Finset.mem_filter.mp J.property).1
  rw [←representativeFiber_residualScale rows R (maskIdeal q m F) J K]
  exact one_le_completedResidualScale K J.val (maskIdeal q m F) hJ.1 hJ.2.2

lemma residual_shell (q:ℕ) (m:Eis) (rows:Finset (Ideal Eis))
    (R F:Ideal Eis) (K:ℝ)
    (hrows:∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F) :
    0<completedResidualScale K R (maskIdeal q m F) ∧
      completedResidualScale K R (maskIdeal q m F)/2≤
        (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ) := by
  refine ⟨lt_of_lt_of_le zero_lt_one (one_le_residualScale q m rows R F K hrows J),?_⟩
  have hJ:=hrows J.val (Finset.mem_filter.mp J.property).1
  rw [←representativeFiber_residualScale rows R (maskIdeal q m F) J K]
  exact actualResidualModelRow_shell K J.val (maskIdeal q m F) hJ.1
    (mask_bad q m F) hJ.2.2 hJ.2.1

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance sourceUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

noncomputable def sourceShapeFactor
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) : ℂ :=
  (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).shape.stratumShapeFactor
    ((fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).c0*
      ∏P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
        freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q) P.val)

noncomputable def sourceFixedCoefficient
    (Ψ:Eis→*ℂ) (h:Eis⧸Ideal.span {reflectionConductor q})
    (J:RowIndex q m rows R F) : ℂ :=
  fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    ((data q m hm rows R F hF hrows v J).fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h

noncomputable def compressedSourceTotal (Ψ:Eis→*ℂ)
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  ∑h:Eis⧸Ideal.span {reflectionConductor q},
    sourceFixedCoefficient q hq m hm rows R F hF hrows v Ψ h J*
    ∑B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),
      FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
      sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J*
      ∑u:Eisˣ,∑l:B→Fin 3,sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X

theorem completedT_eq_compressedSourceTotal
    (Ψ:Eis→*ℂ)
    (hΨ:CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ)
    (hΨnorm:∀n,‖Ψ n‖≤1)
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hsupp:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist Ψ (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
      (thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar)*
        compressedSourceTotal q hq m hm rows R F hR hF hrows v Ψ J W X := by
  rw [completedT_eq_nonresidual_source q hq m hm rows R F hR hF hrows v Ψ hΨ hΨnorm
    J W lo hi hlo hsupp hW X hX]
  unfold compressedSourceTotal
  rw [mul_assoc]
  apply congrArg (fun z:ℂ=>thetaDerivativeScalar⁻¹*z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [mul_left_comm fixedRadialCoefficientScalar]
  apply congrArg (fun z:ℂ=>sourceFixedCoefficient q hq m hm rows R F hF hrows v Ψ h J*z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [sourceStratumValue_eq_compressed q hq m hm rows R F hR hF hrows v h B J
    W lo hi hlo hsupp hW X hX,tsum_fintype]
  change _=(fixedRadialCoefficientScalar*
    (FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
      sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J*
        ∑u:Eisˣ,∑l:B→Fin 3,sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X))
  dsimp only [sourceShapeFactor]
  ring

end CanonicalRowCompletion.ActualFiber

open scoped Classical BigOperators

namespace CompletedGauss
variable {α β γ ι:Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι]

omit [Fintype α] [Fintype β] [Fintype γ] [Fintype ι] in
lemma residualLabelVia_nonresidual_equiv (E:α⊕β≃ι) (T:β≃γ)
    (l:β→Fin 3) (l':γ→Fin 3) (hl:∀b,l' (T b)=l b) :
    residualLabelVia ((Equiv.sumCongr (Equiv.refl α) T.symm).trans E) l'=
      residualLabelVia E l := by
  let E':=((Equiv.sumCongr (Equiv.refl α) T.symm).trans E)
  funext i
  obtain ⟨a,rfl⟩:=E.surjective i
  cases a with
  | inl a=>
    have he:E (Sum.inl a)=E' (Sum.inl a):=rfl
    calc
      _=residualLabelVia E' l' (E' (Sum.inl a)):=by rw [he]
      _=0:=residualLabelVia_apply E' l' (Sum.inl a)
      _=_:=(residualLabelVia_apply E l (Sum.inl a)).symm
  | inr b=>
    have he:E (Sum.inr b)=E' (Sum.inr (T b)):=by simp [E']
    calc
      _=residualLabelVia E' l' (E' (Sum.inr (T b))):=by rw [he]
      _=l' (T b):=residualLabelVia_apply E' l' (Sum.inr (T b))
      _=l b:=hl b
      _=_:=(residualLabelVia_apply E l (Sum.inr b)).symm

end CompletedGauss

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma activeModelPrimeEquiv_labels
    (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (J:RowIndex q m rows R F) :
    residualLabelVia (activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J)
      (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e)=
    residualLabelVia (selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J)
      (reflectionSixSupport e)) (fun b=>reflectionSixLabel (e b.val)) := by
  exact residualLabelVia_nonresidual_equiv _
    (FreeReflection.supportActivePoolEquiv R (maskIdeal q m F) (freeConductor q) e)
    _ _ (fun _=>rfl)

lemma reflectionSixLabel_encode_at {β:Type*} [Fintype β]
    (B:Finset β) (l:B→Fin 3) (b:B) :
    reflectionSixLabel (encodeReflectionSix ⟨B,l⟩ b.val)=l b := by
  classical
  apply Fin.ext
  simp only [encodeReflectionSix,dite_eq_left b.property,reflectionSixLabel]
  change (3+(l b).val)%3=(l b).val
  have hb:=(l b).isLt
  omega

end CanonicalRowCompletion.ActualFiber

open scoped BigOperators Classical ContDiff

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

lemma supportActivePoolEquiv_divisor (I F Q Q0:Ideal Eis)
    (e:pool I Q Q0 → Fin 6) (side:Fin 3) :
    reflectionExtractedDivisor
      (fun P:reflectionActivePool I Q Q0 e=>P.val)
      (fun P=>completedLocalExponent I F P.val) (reflectionActiveLabel I Q Q0 e) side=
    reflectionExtractedDivisor (fun b:reflectionSixSupport e=>b.val.val)
      (fun b=>completedLocalExponent I F b.val.val) (fun b=>reflectionSixLabel (e b.val)) side := by
  unfold reflectionExtractedDivisor
  symm
  apply Fintype.prod_equiv (supportActivePoolEquiv I Q Q0 e)
  intro b
  rfl

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion.ActualFiber

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_decoded_branch_exact
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let B:=reflectionSixSupport e
    let l:=fun b:B=>reflectionSixLabel (e b.val)
    let D:=data q m hm rows R F hF hrows v J
    let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
    let d:=(reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,
        e)
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    4*d.value W X 1 completedRamifiedStep k=
      if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
        (reflectionConductor_ideal q) h G A then
        fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
          (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
        G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
        sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X
      else 0 := by
  let D:=data q m hm rows R F hF hrows v J
  let A:=activeSet q hq m hm rows R F hR hF hrows v e J
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let S:=D.activeStratum (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ideal q) h G A
  let Em:=activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J
  let Es:=selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) (reflectionSixSupport e)
  let labels:=fun b:reflectionSixSupport e=>reflectionSixLabel (e b.val)
  let : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (CanonicalCoefficientClass.fixedBaseConductor q*
      Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ D.movingSupported P.val
  let hp:=fun P:A=>freePrimaryPrime_ne_zero _ _ D.movingSupported P.val
  let hg:=fun P:A=>freePrimaryPrime_good _ _ D.movingSupported P.val
  let j:=fun P:A=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6
  have ht:=reflectedFiber_branch_exact q hq m hm rows R F hR hF hrows v K Ψ hΨ hbound J h rho u
    e W lo hi hlo hsupp hW X hX hK hk
  refine ht.trans (congrArg (fun z:ℂ=>if rho=D.sourceRowResidue
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q) (reflectionConductor_ideal q)
    h G A then fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
      G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*z
    else 0) ?_)
  unfold sourceCompressedTerm
  apply tsum_congr
  intro x
  have hlabel:residualLabelVia Em (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e)=
      residualLabelVia Es labels:=activeModelPrimeEquiv_labels q hq m hm rows R F hR hF hrows v e J
  have hdiv (side:Fin 3):columnDivisor q m R F e side=
      sourceDivisor q m R F (reflectionSixSupport e) labels side:=
    FreeReflection.supportActivePoolEquiv_divisor R F (maskIdeal q m F) (freeConductor q) e side
  have harg:nonzeroDualDilation (columnDivisor q m R F e 1) (columnDivisor q m R F e 2)
      (columnDivisor_ne_zero q m R F e 1) (columnDivisor_ne_zero q m R F e 2) x=
    nonzeroDualDilation (sourceDivisor q m R F (reflectionSixSupport e) labels 1)
      (sourceDivisor q m R F (reflectionSixSupport e) labels 2)
      (sourceDivisor_ne_zero q m R F (reflectionSixSupport e) labels 1)
      (sourceDivisor_ne_zero q m R F (reflectionSixSupport e) labels 2) x := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> apply Subtype.ext <;> dsimp only [nonzeroDualDilation] <;> rw [hdiv]
  exact congrArg₂ (fun label arg =>
    @FixedFourierGeometry.stratumBranchTerm _ _ G A (Finset.Subtype.fintype A)
      _ _ S _ hp hg j u label W X arg) hlabel harg

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_encoded_branch_exact
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let D:=data q m hm rows R F hF hrows v J
    let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
    let d:=(reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,
        encodeReflectionSix ⟨B,l⟩)
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    4*d.value W X 1 completedRamifiedStep k=
      if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
        (reflectionConductor_ideal q) h G A then
        fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
          (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
        G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
        sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X
      else 0 := by
  let result:(ΣB:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),B→Fin 3) → ℂ := fun x =>
    let D:=data q m hm rows R F hF hrows v J
    let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v x.1 J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
      (reflectionConductor_ideal q) h G A then
      fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
        (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
      G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
      sourceCompressedTerm q hq m hm rows R F hR hF hrows v h x.1 J u x.2 W X
    else 0
  have ht:=reflectedFiber_decoded_branch_exact q hq m hm rows R F hR hF hrows v K Ψ hΨ hbound J h rho u
    (encodeReflectionSix ⟨B,l⟩) W lo hi hlo hsupp hW X hX hK hk
  change _=result (decodeReflectionSix (encodeReflectionSix ⟨B,l⟩)) at ht
  rw [decode_encodeReflectionSix] at ht
  change _=result ⟨B,l⟩
  exact ht

end CanonicalRowCompletion.ActualFiber

end

end OAI

end Source299

/- Original source: OAI/NumberTheory/DirichletL/RowCompletion/ZeroFreeRegion.lean; sha256: 0342d5cd682913d53289281c0bc421a37abaa626845fb4bf1a7288871f3deab8 -/
section Source300
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

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance collectionUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_four_mul_value
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    4*(reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).value
      W X 1 completedRamifiedStep k=
        compressedSourceTotal q hq m hm rows R F hR hF hrows v Ψ J W X := by
  let : ∀h:Eis⧸Ideal.span {reflectionConductor q},
      Fintype (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue :=
    fun h=>Fintype.ofFinite _
  let d:=reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ
  let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
  let f:=fun (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)=>
      (d.branch (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq)
        ⟨h,rho,u⟩,encodeReflectionSix ⟨B,l⟩)).value W X 1 completedRamifiedStep k
  let g:=fun (h:Eis⧸Ideal.span {reflectionConductor q}) (u:Eisˣ)
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)=>
      sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X
  let chosen:=fun (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))=>
      (data q m hm rows R F hF hrows v J).sourceRowResidue
        (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q) (reflectionConductor_ideal q)
        h (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
        (sourcePrimeSet q hq m hm rows R F hR hF hrows v B J)
  let α:=fun h=>sourceFixedCoefficient q hq m hm rows R F hF hrows v Ψ h J
  let shape:=fun h B=>sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J
  let w:=FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q)
  have hbranch:∀h rho u B l,4*f h rho u B l=
      if rho=chosen h B then α h*shape h B*g h u B l else 0 := by
    intro h rho u B l
    exact reflectedFiber_encoded_branch_exact q hq m hm rows R F hR hF hrows v K Ψ hΨ hbound
      J h rho u B l W lo hi hlo hsupp hW X hX hK hk
  have hvalue:d.value W X 1 completedRamifiedStep k=
      ∑h,∑rho,∑u,∑B,w B*∑l,f h rho u B l := by
    rw [reflectedFiber_value q hq m hm rows R F hR hF hrows v K Ψ hΨ W X k]
    exact sum_fixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq) _
  change 4*d.value W X 1 completedRamifiedStep k=_
  rw [hvalue]
  exact finite_selected_branch_collection f g chosen α shape w hbranch

theorem completedT_eq_reflectedFiber_idealValue
    (Ψ:Eis→*ℂ)
    (hΨperiod:CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ)
    (hΨ:∀n,‖Ψ n‖≤1)
    (K:ℝ) (hshell:∀I∈rows,K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist Ψ (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
      (4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar)*
        (reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).idealValue W X 1 completedRamifiedStep
          (rowResidualPart J.val (maskIdeal q m F)) := by
  let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI=>⟨hrows I hI,(hshell I hI).2⟩) J
  have hs:=residual_shell q m rows R F K (fun I hI=>⟨hrows I hI,hshell I hI⟩) J
  have he:=reflectedFiber_four_mul_value q hq m hm rows R F hR hF hrows v K Ψ hΨ
    (fun I hI=>(hshell I hI).2) J W lo hi hlo hsupp hW X hX hs.1 hs.2
  rw [completedT_eq_compressedSourceTotal q hq m hm rows R F hR hF hrows v Ψ hΨperiod hΨ
    J W lo hi hlo hsupp hW X hX,←he]
  have hid:rowResidualPart J.val (maskIdeal q m F)=k.val:=rfl
  rw [hid,ReflectedFiberData.idealValue_at]
  ring

end CanonicalRowCompletion.ActualFiber

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

def actualReflectionScale : ℂ :=
  4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar

theorem actual_fixedShellModels (q:ℕ) (hq:q≠0) (χ:DirichletCharacter ℂ q) :
    HasFixedShellModels (reflectionExcludedPrimes q) (initialBase χ)
      (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      actualReflectionScale 1 completedRamifiedStep
      (fixedCuspLevelBound (reflectionConductor q)) := by
  let : Finite (Eis⧸Ideal.span {reflectionConductor q}) :=
    ConcreteTraceCRT.finite_quotient_span (reflectionConductor_ne_zero q hq)
  let : Fintype (Eis⧸Ideal.span {reflectionConductor q}) := Fintype.ofFinite _
  apply fixedShellModels_of_actual_fiber_identity q hq χ actualReflectionScale
  intro Ψ hperiod hnorm m hm F hF u W a b ha hs hW K X hK hX rows hrows R hR J
  exact ActualFiber.completedT_eq_reflectedFiber_idealValue q hq m hm rows R F
    (hrows R hR).1 hF (fun I hI=>(hrows I hI).1) u Ψ hperiod hnorm K
    (fun I hI=>(hrows I hI).2) J W a b ha hs hW X hX

theorem exists_actual_fixedShellModels (q:ℕ) [NeZero q] (χ:DirichletCharacter ℂ q) :
    ∃(rays:ℕ) (scale:ℂ),
      HasFixedShellModels (reflectionExcludedPrimes q) (initialBase χ)
        rays scale 1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q)) := by
  exact ⟨fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q (NeZero.ne q)),
    actualReflectionScale,actual_fixedShellModels q (NeZero.ne q) χ⟩

end

theorem dirichletTarget_unconditional : ShortDraft.DirichletTarget :=
  dirichletTarget_of_reflection_shells exists_actual_fixedShellModels

end CanonicalRowCompletion

namespace ShortDraft

theorem dirichlet_LFunction_ne_zero (q:ℕ) [NeZero q]
    (χ:DirichletCharacter ℂ q) (s:ℂ)
    (hs:(23/24:ℝ)<s.re) (hpole:¬(χ=1 ∧ s=1)) :
    DirichletCharacter.LFunction χ s≠0 :=
  CanonicalRowCompletion.dirichletTarget_unconditional q χ s hs hpole

theorem riemannZeta_ne_zero_of_re_gt (s:ℂ)
    (hs:(23/24:ℝ)<s.re) (hs1:s≠1) : riemannZeta s≠0 :=
  zeta_nonvanishing_of_dirichletTarget
    CanonicalRowCompletion.dirichletTarget_unconditional s hs hs1

end ShortDraft

end

end OAI

end Source300

/- Original source: OAI/NumberTheory/DirichletL/Foundation.lean; sha256: ebfe6353a647f9e09bce1891343398e49094bc60f72b9b525f1e0fe97ee9e59d -/
section Source301

end Source301

/- Original source: OAI/NumberTheory/DirichletL/Moments/Correlation.lean; sha256: 90d0837fc41a775de40975dae29ff985ceaf4a4b01e7c1f0c078de251addedbe -/
section Source302
namespace OAI

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]

def fourierSum (ψ : AddChar R ℂ) (place : X → R) (f : X → ℂ) (h : R) : ℂ :=
  ∑ x, f x * ψ (h * place x)

def fullCorrelation (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (j : R) : ℂ :=
  ∑ x, ∑ y, if left x - right y = j then f x * star (g y) else 0

omit [Fintype R] in
theorem fullCorrelation_swap (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (j : R) :
    fullCorrelation left right f g j = star (fullCorrelation right left g f (-j)) := by
  classical
  simp only [fullCorrelation, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  have heq : left x - right y = j ↔ right y - left x = -j := by
    constructor <;> intro h <;> linear_combination -h
  by_cases h : left x - right y = j
  · simp [h, heq.mp h, star_mul]
  · simp [h, not_congr heq |>.mp h]

theorem fullCorrelation_fourier (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (left : X → R) (right : Y → R) (f : X → ℂ) (g : Y → ℂ) (j : R) :
    (∑ h : R, fourierSum ψ left f h * star (fourierSum ψ right g h) * ψ (-(h * j))) =
      (Fintype.card R : ℂ) * fullCorrelation left right f g j := by
  classical
  simp only [fourierSum, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have hphase (h : R) (x : X) (y : Y) :
      (f x * ψ (h * left x) * (star (ψ (h * right y)) * star (g y))) * ψ (-(h * j)) =
        (f x * star (g y)) * ψ (h * (left x - right y - j)) := by
    have hs : star (ψ (h * right y)) = ψ (-(h * right y)) := by
      simpa only [← starRingEnd_apply] using (AddChar.map_neg_eq_conj ψ (h * right y)).symm
    rw [hs]
    calc
      _ = (f x * star (g y)) *
          (ψ (h * left x) * ψ (-(h * right y)) * ψ (-(h * j))) := by ring
      _ = _ := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 2
        ring
  simp_rw [hphase, ← Finset.mul_sum, AddChar.sum_mulShift _ hψ]
  simp only [fullCorrelation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : left x - right y = j
  · simp [hxy, mul_comm]
  · simp [sub_ne_zero.mpr hxy, hxy]

section FiniteField
variable {F : Type*} [Field F] [Fintype F]

def shiftCorrelation (χ : MulChar F ℂ) (k : F) : ℂ :=
  ∑ x : F, χ x * star (χ (x - k))

lemma character_mul_star (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) :
    χ a * star (χ a) = 1 := by
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
  exact mul_inv_cancel₀ (χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr ha))

theorem shiftCorrelation_scale (χ : MulChar F ℂ) {k : F} (hk : k ≠ 0) :
    shiftCorrelation χ k = shiftCorrelation χ 1 := by
  unfold shiftCorrelation
  rw [← (Equiv.mulLeft₀ k hk).sum_comp]
  swap
  · simp
  apply Finset.sum_congr rfl
  intro x _
  simp only [Equiv.mulLeft₀_apply]
  rw [show k * x - k = k * (x - 1) by ring, map_mul, map_mul, star_mul]
  calc
    _ = (χ k * star (χ k)) * (χ x * star (χ (x - 1))) := by ring
    _ = _ := by rw [character_mul_star χ hk, one_mul]

theorem shiftCorrelation_one (χ : MulChar F ℂ) :
    shiftCorrelation χ 1 = χ⁻¹ (-1) * jacobiSum χ χ⁻¹ := by
  simp only [shiftCorrelation, jacobiSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [MulChar.star_apply', show x - 1 = (-1) * (1 - x) by ring, map_mul]
  ring

theorem shiftCorrelation_zero (χ : MulChar F ℂ) :
    shiftCorrelation χ 0 = (Fintype.card F : ℂ) - 1 := by
  classical
  simp only [shiftCorrelation, sub_zero, MulChar.star_apply', ← MulChar.mul_apply,
    mul_inv_cancel]
  rw [MulChar.sum_one_eq_card_units, Fintype.card_eq_card_units_add_one (α := F)]
  simp

theorem shiftCorrelation_nonprincipal (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    {k : F} (hk : k ≠ 0) : shiftCorrelation χ k = -1 := by
  rw [shiftCorrelation_scale χ hk, shiftCorrelation_one, jacobiSum_nontrivial_inv hχ,
    mul_neg, ← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero))]

theorem shiftCorrelation_principal {k : F} (hk : k ≠ 0) :
    shiftCorrelation (1 : MulChar F ℂ) k = (Fintype.card F : ℂ) - 2 := by
  rw [shiftCorrelation_scale _ hk, shiftCorrelation_one, inv_one,
    MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero)), one_mul, jacobiSum_one_one]

def localCorrelation (χ : MulChar F ℂ) (n₁ n₂ k : F) : ℂ :=
  fullCorrelation (fun x : F => n₂ * x) (fun y : F => n₁ * y) χ χ k

theorem localCorrelation_eq_shift (χ : MulChar F ℂ) {n₁ n₂ : F}
    (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ n₁ n₂ k = χ (n₁ / n₂) * shiftCorrelation χ (k / n₁) := by
  classical
  have hsolve (x y : F) : n₂ * x - n₁ * y = k ↔ y = (n₂ * x - k) / n₁ := by
    rw [eq_div_iff h₁]
    constructor <;> intro h <;> linear_combination -h
  unfold localCorrelation fullCorrelation
  simp only [hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← (Equiv.mulLeft₀ (n₁ / n₂) (div_ne_zero h₁ h₂)).sum_comp]
  swap
  · simp
  simp only [Equiv.mulLeft₀_apply, shiftCorrelation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul]
  have heq : (n₂ * (n₁ / n₂ * x) - k) / n₁ = x - k / n₁ := by
    field_simp
  rw [heq, mul_assoc]

theorem localCorrelation_units (χ : MulChar F ℂ) {n₁ n₂ : F}
    (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ n₁ n₂ k = χ (n₁ / n₂) *
      (if k = 0 then (Fintype.card F : ℂ) - 1
       else if χ = 1 then (Fintype.card F : ℂ) - 2 else -1) := by
  rw [localCorrelation_eq_shift χ h₁ h₂]
  by_cases hk : k = 0
  · simp [hk, shiftCorrelation_zero]
  · by_cases hχ : χ = 1
    · simp [hk, hχ, shiftCorrelation_principal (div_ne_zero hk h₁)]
    · simp [hk, hχ, shiftCorrelation_nonprincipal χ hχ (div_ne_zero hk h₁)]

lemma character_sum (χ : MulChar F ℂ) :
    (∑ x : F, χ x) = if χ = 1 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    rw [MulChar.sum_one_eq_card_units, Fintype.card_eq_card_units_add_one (α := F)]
    simp
  · simp [hχ, MulChar.sum_eq_zero_of_ne_one hχ]

theorem localCorrelation_first_zero (χ : MulChar F ℂ) {n₂ : F} (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ 0 n₂ k =
      if χ = 1 ∧ k ≠ 0 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  have hsolve (x : F) : n₂ * x = k ↔ x = k / n₂ := by
    rw [eq_div_iff h₂, mul_comm]
  have hsum : localCorrelation χ 0 n₂ k = χ (k / n₂) * star (∑ y : F, χ y) := by
    unfold localCorrelation fullCorrelation
    simp only [zero_mul, sub_zero, hsolve]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.mul_sum, ← star_sum]
  rw [hsum, character_sum]
  by_cases hχ : χ = 1
  · subst χ
    by_cases hk : k = 0
    · simp [hk, MulChar.map_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr (div_ne_zero hk h₂))]
      simp [hk]
  · simp [hχ]

theorem localCorrelation_second_zero (χ : MulChar F ℂ) {n₁ : F} (h₁ : n₁ ≠ 0) (k : F) :
    localCorrelation χ n₁ 0 k =
      if χ = 1 ∧ k ≠ 0 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  have hsolve (y : F) : -(n₁ * y) = k ↔ y = -k / n₁ := by
    rw [eq_div_iff h₁]
    constructor <;> intro h <;> linear_combination -h
  have hsum : localCorrelation χ n₁ 0 k = (∑ x : F, χ x) * star (χ (-k / n₁)) := by
    unfold localCorrelation fullCorrelation
    simp only [zero_mul, zero_sub, hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      ← Finset.sum_mul]
  rw [hsum, character_sum]
  by_cases hχ : χ = 1
  · subst χ
    by_cases hk : k = 0
    · simp [hk, MulChar.map_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr (div_ne_zero (neg_ne_zero.mpr hk) h₁))]
      simp [hk]
  · simp [hχ]

end FiniteField

variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

def reductionMultiplicity (π : A →+* B) : ℕ :=
  (Finset.univ.filter fun x : A => π x = 0).card

theorem sum_reduction (π : A →+* B) (hπ : Function.Surjective π) (f : B → ℂ) :
    (∑ x : A, f (π x)) = (reductionMultiplicity π : ℂ) * ∑ y : B, f y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ π (fun x => f (π x)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = ∑ x : A with π x = y, f y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by
      have hc := AddMonoidHom.card_fiber_eq_of_mem_range π (hπ y) (hπ 0)
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hc]
      rfl

theorem reductionMultiplicity_mul_card (π : A →+* B) (hπ : Function.Surjective π) :
    reductionMultiplicity π * Fintype.card B = Fintype.card A := by
  have h := sum_reduction π hπ (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h.symm

theorem reductionMultiplicity_eq_pow (π : A →+* B) (hπ : Function.Surjective π)
    {P c : ℕ} (hP : 0 < P) (hc : 1 ≤ c)
    (hA : Fintype.card A = P ^ c) (hB : Fintype.card B = P) :
    reductionMultiplicity π = P ^ (c - 1) := by
  apply Nat.eq_of_mul_eq_mul_right hP
  rw [← hB, reductionMultiplicity_mul_card π hπ, hA, hB, ← pow_succ,
    Nat.sub_add_cancel hc]

theorem fullCorrelation_unit_right (u : Aˣ) (v k : A) (f g : A → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => (u : A) * y) f g k =
      ∑ x : A, f x * star (g ((↑u⁻¹ : A) * (v * x - k))) := by
  classical
  have hsolve (x y : A) : v * x - (u : A) * y = k ↔
      y = (↑u⁻¹ : A) * (v * x - k) := by
    constructor
    · intro h
      have heq : v * x - k = (u : A) * y := by linear_combination h
      rw [heq, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
      ring
  simp only [fullCorrelation, hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem fullCorrelation_reduction_unit_right (π : A →+* B)
    (hπ : Function.Surjective π) (u : Aˣ) (v k : A) (f g : B → ℂ) :
    fullCorrelation (fun x : A => v * x) (fun y : A => (u : A) * y)
        (fun x => f (π x)) (fun y => g (π y)) k =
      (reductionMultiplicity π : ℂ) *
        fullCorrelation (fun x : B => π v * x) (fun y : B => π u * y) f g (π k) := by
  rw [fullCorrelation_unit_right]
  have hright := fullCorrelation_unit_right (Units.map π.toMonoidHom u) (π v) (π k) f g
  change fullCorrelation _ (fun y : B => π u * y) _ _ _ = _ at hright
  rw [hright]
  change (∑ x : A, f (π x) * star (g (π ((↑u⁻¹ : A) * (v * x - k))))) =
    (reductionMultiplicity π : ℂ) *
      ∑ x : B, f x * star (g (π (↑u⁻¹ : A) * (π v * x - π k)))
  simpa only [map_mul, map_sub] using
    sum_reduction π hπ (fun x => f x * star (g (π (↑u⁻¹ : A) * (π v * x - π k))))

theorem fullCorrelation_reduction_unit_left (π : A →+* B)
    (hπ : Function.Surjective π) (u : A) (v : Aˣ) (k : A) (f g : B → ℂ) :
    fullCorrelation (fun x : A => (v : A) * x) (fun y : A => u * y)
        (fun x => f (π x)) (fun y => g (π y)) k =
      (reductionMultiplicity π : ℂ) *
        fullCorrelation (fun x : B => π v * x) (fun y : B => π u * y) f g (π k) := by
  rw [fullCorrelation_swap, fullCorrelation_reduction_unit_right π hπ v u (-k) g f]
  rw [fullCorrelation_swap (fun x : B => π v * x) (fun y : B => π u * y) f g (π k)]
  simp only [map_neg, star_mul, star_natCast]
  ring

end
end SevenEighths.CenteredMomentCorrelation

end OAI

end Source302

/- Original source: OAI/NumberTheory/DirichletL/Moments/PrimePower.lean; sha256: bc1c13575d102be643e58ccf58777559f8dacb3529caae27c08fab91218bcc55 -/
section Source303
namespace OAI

open scoped BigOperators Classical
open NumberField
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
local instance : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)

def primePowerReduction (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    (𝓞 K ⧸ P ^ c) →+* (𝓞 K ⧸ P) :=
  Ideal.Quotient.factor (by simpa using Ideal.pow_le_pow_right (I := P) hc)

omit [NumberField K] in
theorem primePowerReduction_surjective (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    Function.Surjective (primePowerReduction P hc) :=
  Ideal.Quotient.factor_surjective _

theorem primePowerReduction_multiplicity (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)] :
    reductionMultiplicity (primePowerReduction P hc) = Ideal.absNorm P ^ (c - 1) := by
  have hcard (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)] :
      Fintype.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  refine reductionMultiplicity_eq_pow _ (primePowerReduction_surjective P hc)
      (P := Ideal.absNorm P) ?_ hc ?_ ?_
  · rw [← hcard P]
    exact Fintype.card_pos
  · rw [hcard, map_pow]
  · exact hcard P

def primePowerCharacter (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) : MulChar (𝓞 K ⧸ P ^ c) ℂ where
  __ := χ.toMonoidHom.comp (primePowerReduction P hc).toMonoidHom
  map_nonunit' := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change χ (Ideal.Quotient.mk P a) = 0
    apply χ.map_nonunit
    intro ha
    exact hx ((Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr ha)

omit [NumberField K] in
@[simp] theorem primePowerCharacter_apply (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) (x : 𝓞 K ⧸ P ^ c) :
    primePowerCharacter P hc χ x = χ (primePowerReduction P hc x) := rfl

section Local
variable (P : Ideal (𝓞 K)) [P.IsMaximal] {c : ℕ} (hc : 1 ≤ c)
variable [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)]
local instance : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P

theorem primePower_localCorrelation (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      localCorrelation (χ ^ c) (primePowerReduction P hc u)
        (primePowerReduction P hc v) (primePowerReduction P hc k) := by
  rw [fullCorrelation_reduction_unit_right _ (primePowerReduction_surjective P hc),
    primePowerReduction_multiplicity, Nat.cast_pow]
  rfl

theorem primePower_localCorrelation_units (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (hχ : orderOf χ = 6) (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c)
    (hv : primePowerReduction P hc v ≠ 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      χ (primePowerReduction P hc u / primePowerReduction P hc v) ^ c *
      (if primePowerReduction P hc k = 0 then (Ideal.absNorm P : ℂ) - 1
       else if 6 ∣ c then (Ideal.absNorm P : ℂ) - 2 else -1) := by
  have hu : primePowerReduction P hc u ≠ 0 :=
    (isUnit_iff_ne_zero.mp (u.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [primePower_localCorrelation, localCorrelation_units _ hu hv,
    MulChar.pow_apply' _ (by omega), hcard, hpow, mul_assoc]
  split_ifs <;> rfl

theorem primePower_localCorrelation_second_zero (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (hχ : orderOf χ = 6) (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c)
    (hv : primePowerReduction P hc v = 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0
       then (Ideal.absNorm P : ℂ) - 1 else 0) := by
  have hu : primePowerReduction P hc u ≠ 0 :=
    (isUnit_iff_ne_zero.mp (u.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [primePower_localCorrelation, hv, localCorrelation_second_zero _ hu, hcard, hpow]
  split_ifs <;> rfl

theorem primePower_localCorrelation_first_zero (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (hχ : orderOf χ = 6) (u : 𝓞 K ⧸ P ^ c) (v : (𝓞 K ⧸ P ^ c)ˣ)
    (k : 𝓞 K ⧸ P ^ c) (hu : primePowerReduction P hc u = 0) :
    fullCorrelation (fun x => (v : 𝓞 K ⧸ P ^ c) * x) (fun y => u * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0
       then (Ideal.absNorm P : ℂ) - 1 else 0) := by
  have hv : primePowerReduction P hc v ≠ 0 :=
    (isUnit_iff_ne_zero.mp (v.isUnit.map (primePowerReduction P hc)))
  have hpow : χ ^ c = 1 ↔ 6 ∣ c := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hcard : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [fullCorrelation_reduction_unit_left _ (primePowerReduction_surjective P hc),
    primePowerReduction_multiplicity, Nat.cast_pow]
  change (Ideal.absNorm P : ℂ) ^ (c - 1) *
      localCorrelation (χ ^ c) (primePowerReduction P hc u)
        (primePowerReduction P hc v) (primePowerReduction P hc k) = _
  rw [hu, localCorrelation_first_zero _ hv, hcard, hpow]
  split_ifs <;> rfl

end Local
end
end SevenEighths.CenteredMomentCorrelation

end OAI

end Source303

/- Original source: OAI/NumberTheory/DirichletL/Moments/CRT.lean; sha256: 870db8546c08aea6d11ffad289fcd0e6c8d2454d29d3cb04a9c1ce269935aa36 -/
section Source304
namespace OAI

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

theorem fullCorrelation_ringEquiv (e : A ≃+* B) (u v k : A) (f g : B → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => f (e x)) (fun y => g (e y)) k =
      fullCorrelation (fun x => e v * x) (fun y => e u * y) f g (e k) := by
  unfold fullCorrelation
  apply Fintype.sum_equiv e.toEquiv
  intro x
  apply Fintype.sum_equiv e.toEquiv
  intro y
  have heq : v * x - u * y = k ↔ e v * e x - e u * e y = e k := by
    rw [← map_mul, ← map_mul, ← map_sub, e.injective.eq_iff]
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, heq]

theorem fullCorrelation_product (u v k : A × B) (f₁ g₁ : A → ℂ) (f₂ g₂ : B → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => f₁ x.1 * f₂ x.2) (fun y => g₁ y.1 * g₂ y.2) k =
      fullCorrelation (fun x => v.1 * x) (fun y => u.1 * y) f₁ g₁ k.1 *
        fullCorrelation (fun x => v.2 * x) (fun y => u.2 * y) f₂ g₂ k.2 := by
  classical
  simp only [fullCorrelation, Fintype.sum_prod_type]
  have hterm (x₁ y₁ : A) (x₂ y₂ : B) :
      (if v * (x₁, x₂) - u * (y₁, y₂) = k
       then (f₁ x₁ * f₂ x₂) * star (g₁ y₁ * g₂ y₂) else 0) =
      (if v.1 * x₁ - u.1 * y₁ = k.1 then f₁ x₁ * star (g₁ y₁) else 0) *
      (if v.2 * x₂ - u.2 * y₂ = k.2 then f₂ x₂ * star (g₂ y₂) else 0) := by
    have heq : v * (x₁, x₂) - u * (y₁, y₂) = k ↔
        v.1 * x₁ - u.1 * y₁ = k.1 ∧ v.2 * x₂ - u.2 * y₂ = k.2 := by
      exact Prod.ext_iff
    by_cases h₁ : v.1 * x₁ - u.1 * y₁ = k.1 <;>
      by_cases h₂ : v.2 * x₂ - u.2 * y₂ = k.2 <;>
      simp [heq, h₁, h₂, star_mul] ; ring
  simp_rw [hterm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x₁ _
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y₁ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x₂ _
  rw [Finset.mul_sum]

theorem fullCorrelation_pi {ι : Type*} [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, Fintype (R i)]
    (u v k : ∀ i, R i) (f g : ∀ i, R i → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)) k =
      ∏ i, fullCorrelation (fun x => v i * x) (fun y => u i * y) (f i) (g i) (k i) := by
  classical
  have hterm (x y : ∀ i, R i) :
      (if v * x - u * y = k then (∏ i, f i (x i)) * star (∏ i, g i (y i)) else 0) =
      ∏ i, if v i * x i - u i * y i = k i then f i (x i) * star (g i (y i)) else 0 := by
    by_cases h : ∀ i, v i * x i - u i * y i = k i
    · have heq : v * x - u * y = k := funext h
      simp only [heq, ite_true, h, star_prod, Finset.prod_mul_distrib]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hne : v * x - u * y ≠ k := fun heq => hi (congrFun heq i)
      rw [ite_eq_right hne]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hi, ite_false]
  simp only [fullCorrelation]
  simp_rw [hterm]
  calc
    _ = ∑ x : ∀ i, R i, ∏ i, ∑ y : R i,
        if v i * x i - u i * y = k i then f i (x i) * star (g i y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum (fun i (y : R i) =>
        if v i * x i - u i * y = k i then f i (x i) * star (g i y) else (0 : ℂ))).symm
    _ = _ := (Fintype.prod_sum (fun i (x : R i) => ∑ y : R i,
      if v i * x - u i * y = k i then f i x * star (g i y) else (0 : ℂ))).symm

theorem fullCorrelation_idealCRT {S ι : Type*} [CommRing S] [Fintype ι]
    (I : ι → Ideal S) (hI : Pairwise (Function.onFun IsCoprime I))
    [Fintype (S ⧸ ⨅ i, I i)] [∀ i, Fintype (S ⧸ I i)]
    (u v k : S ⧸ ⨅ i, I i) (f g : ∀ i, S ⧸ I i → ℂ) :
    let e := Ideal.quotientInfRingEquivPiQuotient I hI
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => ∏ i, f i (e x i)) (fun y => ∏ i, g i (e y i)) k =
      ∏ i, fullCorrelation (fun x => e v i * x) (fun y => e u i * y)
        (f i) (g i) (e k i) := by
  classical
  dsimp only
  rw [fullCorrelation_ringEquiv (Ideal.quotientInfRingEquivPiQuotient I hI) u v k
    (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)), fullCorrelation_pi]

def crtCharacter {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) :
    MulChar S ℂ where
  toFun x := ∏ i, χ i (e x i)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul, Finset.prod_mul_distrib]
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (e x) := fun h => hx ((isUnit_map_iff e x).mp h)
    have hsome : ∃ i, ¬IsUnit (e x i) := by
      by_contra h
      apply hn
      exact Pi.isUnit_iff.mpr (by simpa only [not_exists, not_not] using h)
    obtain ⟨i, hi⟩ := hsome
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((χ i).map_nonunit hi)

@[simp] theorem crtCharacter_apply {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) (x : S) :
    crtCharacter e χ x = ∏ i, χ i (e x i) := rfl

end
end SevenEighths.CenteredMomentCorrelation

end OAI

end Source304

/- Original source: OAI/NumberTheory/DirichletL/Moments/Canonical.lean; sha256: 3f13deefe9d03002173a565be205edab82dfa53f50ff2a66b860b8b4ed22b358 -/
section Source305
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCanonical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem actualSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (actualSextic P hg) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  exact (orderOf_injective Φ hΦ _).trans (sexticChar_order P hg hchar)

def primePowerRow (P : Ideal O) [P.IsMaximal] (hg : goodLambda ∉ P)
    {c : ℕ} (hc : 1 ≤ c) (x : O ⧸ P ^ c) : ℂ :=
  (actualSextic P hg ^ c) (primePowerReduction P hc x)

theorem canonical_primePower_units (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (O ⧸ P ^ c)] [Fintype (O ⧸ P)]
    (u : (O ⧸ P ^ c)ˣ) (v k : O ⧸ P ^ c)
    (hv : primePowerReduction P hc v ≠ 0) :
    letI : Field (O ⧸ P) := Ideal.Quotient.field P
    fullCorrelation (fun x => v * x) (fun y => (u : O ⧸ P ^ c) * y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      actualSextic P hg (primePowerReduction P hc u / primePowerReduction P hc v) ^ c *
      (if primePowerReduction P hc k = 0 then (Ideal.absNorm P : ℂ) - 1
       else if 6 ∣ c then (Ideal.absNorm P : ℂ) - 2 else -1) :=
  primePower_localCorrelation_units P hc (actualSextic P hg)
    (actualSextic_order_six P hg hchar) u v k hv

theorem canonical_primePower_second_zero (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (O ⧸ P ^ c)] [Fintype (O ⧸ P)]
    (u : (O ⧸ P ^ c)ˣ) (v k : O ⧸ P ^ c)
    (hv : primePowerReduction P hc v = 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : O ⧸ P ^ c) * y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0 then (Ideal.absNorm P : ℂ) - 1 else 0) :=
  primePower_localCorrelation_second_zero P hc (actualSextic P hg)
    (actualSextic_order_six P hg hchar) u v k hv

theorem canonical_primePower_first_zero (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (O ⧸ P ^ c)] [Fintype (O ⧸ P)]
    (u : O ⧸ P ^ c) (v : (O ⧸ P ^ c)ˣ) (k : O ⧸ P ^ c)
    (hu : primePowerReduction P hc u = 0) :
    fullCorrelation (fun x => (v : O ⧸ P ^ c) * x) (fun y => u * y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0 then (Ideal.absNorm P : ℂ) - 1 else 0) :=
  primePower_localCorrelation_first_zero P hc (actualSextic P hg)
    (actualSextic_order_six P hg hchar) u v k hu

def canonicalPrimePowerCharacter (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) {c : ℕ} (hc : 1 ≤ c) : MulChar (O ⧸ P ^ c) ℂ :=
  primePowerCharacter P hc (actualSextic P hg ^ c)

theorem canonicalPrimePowerCharacter_mk (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) {c : ℕ} (hc : 1 ≤ c) (x : O) :
    canonicalPrimePowerCharacter P hg hc (Ideal.Quotient.mk (P ^ c) x) =
      CanonicalRowCompletion.idealRowHom x (P ^ c) := by
  change (actualSextic P hg ^ c) (Ideal.Quotient.mk P x) = _
  rw [MulChar.pow_apply' _ (by omega), map_pow,
    CanonicalRowCompletion.idealRowHom_prime x P hg]

private theorem pairwise_isCoprime_pow {ι : Type*}
    (P : ι → Ideal O) (c : ι → ℕ)
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    Pairwise (Function.onFun IsCoprime (fun i => P i ^ c i)) := by
  intro i j hij
  exact (hcop hij).pow

def canonicalCRTCharacter {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    MulChar (O ⧸ ∏ i, P i ^ c i) ℂ :=
  crtCharacter (IdealGaussCRT.quotientProdEquivPi (fun i => P i ^ c i)
    (pairwise_isCoprime_pow P c hcop))
    (fun i => canonicalPrimePowerCharacter (P i) (hg i) (hc i))

theorem canonicalCRTCharacter_mk {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) (x : O) :
    canonicalCRTCharacter P hg c hc hcop (Ideal.Quotient.mk (∏ i, P i ^ c i) x) =
      CanonicalRowCompletion.idealRowHom x (∏ i, P i ^ c i) := by
  simp only [canonicalCRTCharacter, crtCharacter_apply,
    IdealGaussCRT.quotientProdEquivPi_mk, canonicalPrimePowerCharacter_mk, map_prod]

theorem canonicalCRTCorrelation {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i ^ c i)] [∀ i, Fintype (O ⧸ P i ^ c i)]
    (u v k : O ⧸ ∏ i, P i ^ c i) :
    let e := IdealGaussCRT.quotientProdEquivPi (fun i => P i ^ c i)
      (pairwise_isCoprime_pow P c hcop)
    fullCorrelation (fun x => v * x) (fun y => u * y)
      (canonicalCRTCharacter P hg c hc hcop) (canonicalCRTCharacter P hg c hc hcop) k =
      ∏ i, fullCorrelation (fun x => e v i * x) (fun y => e u i * y)
        (primePowerRow (P i) (hg i) (hc i)) (primePowerRow (P i) (hg i) (hc i))
        (e k i) := by
  dsimp only
  change fullCorrelation (fun x => v * x) (fun y => u * y)
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i)
      (IdealGaussCRT.quotientProdEquivPi _ _ x i))
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i)
      (IdealGaussCRT.quotientProdEquivPi _ _ x i)) k = _
  rw [fullCorrelation_ringEquiv (IdealGaussCRT.quotientProdEquivPi _ _) u v k
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i) (x i))
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i) (x i)), fullCorrelation_pi]

end SevenEighths.CenteredMomentCanonical
end

end OAI

end Source305

/- Original source: OAI/NumberTheory/DirichletL/Moments/FullCorrelation.lean; sha256: 1ca3f1b22920fbc75dd7f41351aebd6293db8a421196210048175e235d51ef65 -/
section Source306
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]

def scaledResidue (d a m : A) (hm : m = d * a) :
    (A ⧸ Ideal.span {d}) → (A ⧸ Ideal.span {m}) := fun x =>
  Quotient.liftOn' x (fun z => Ideal.Quotient.mk (Ideal.span {m}) (a * z)) (by
    intro x y hxy
    apply Ideal.Quotient.eq.mpr
    have hd : d ∣ x - y := Ideal.mem_span_singleton.mp
      ((Ideal.span {d}).quotientRel_def.mp hxy)
    apply Ideal.mem_span_singleton.mpr
    obtain ⟨z, hz⟩ := hd
    refine ⟨z, ?_⟩
    rw [hm, ← mul_sub, hz]
    ring)

@[simp] theorem scaledResidue_mk (d a m : A) (hm : m = d * a) (x : A) :
    scaledResidue d a m hm (Ideal.Quotient.mk (Ideal.span {d}) x) =
      Ideal.Quotient.mk (Ideal.span {m}) (a * x) := rfl

def fullModulusCorrelation (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ) (j : A) : ℂ :=
  fullCorrelation (scaledResidue u v (u * v) rfl)
    (scaledResidue v u (u * v) (mul_comm u v)) χu χv
    (Ideal.Quotient.mk (Ideal.span {u * v}) j)

theorem scaledResidue_congruence (u v x y j : A) :
    scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) x) -
      scaledResidue v u (u * v) (mul_comm u v)
        (Ideal.Quotient.mk (Ideal.span {v}) y) =
      Ideal.Quotient.mk (Ideal.span {u * v}) j ↔
      u * v ∣ v * x - u * y - j := by
  rw [scaledResidue_mk, scaledResidue_mk, ← map_sub, Ideal.Quotient.eq]
  exact Ideal.mem_span_singleton

theorem fullModulusCorrelation_fourier (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    [Fintype (A ⧸ Ideal.span {u * v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ) (j : A)
    (ψ : AddChar (A ⧸ Ideal.span {u * v}) ℂ) (hψ : ψ.IsPrimitive) :
    (∑ h : A ⧸ Ideal.span {u * v},
      fourierSum ψ (scaledResidue u v (u * v) rfl) χu h *
        star (fourierSum ψ (scaledResidue v u (u * v) (mul_comm u v)) χv h) *
          ψ (-(h * Ideal.Quotient.mk (Ideal.span {u * v}) j))) =
      (Fintype.card (A ⧸ Ideal.span {u * v}) : ℂ) * fullModulusCorrelation u v χu χv j :=
  fullCorrelation_fourier ψ hψ _ _ χu χv _

theorem common_divisor_frequency {u v d x y j : A}
    (hdu : d ∣ u) (hdv : d ∣ v) (hcong : u * v ∣ v * x - u * y - j) : d ∣ j := by
  have hleft : d ∣ v * x - u * y := dvd_sub (hdv.trans (dvd_mul_right v x))
    (hdu.trans (dvd_mul_right u y))
  have hprod : d ∣ u * v := hdu.trans (dvd_mul_right u v)
  have hdiff := dvd_sub hleft (hprod.trans hcong)
  convert hdiff using 1 ; ring

theorem fullModulusCorrelation_eq_zero_of_common_not_dvd (u v d j : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ)
    (hdu : d ∣ u) (hdv : d ∣ v) (hdj : ¬d ∣ j) :
    fullModulusCorrelation u v χu χv j = 0 := by
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  refine Quotient.inductionOn₂' x y ?_
  intro a b
  have hn : ¬ scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) a) -
      scaledResidue v u (u * v) (mul_comm u v) (Ideal.Quotient.mk (Ideal.span {v}) b) =
      Ideal.Quotient.mk (Ideal.span {u * v}) j := by
    intro h
    exact hdj (common_divisor_frequency hdu hdv ((scaledResidue_congruence u v a b j).mp h))
  exact ite_eq_right hn

theorem dvd_of_unit_residue_mul {u x v : A}
    (hx : IsUnit (Ideal.Quotient.mk (Ideal.span {u}) x)) (hdiv : u ∣ v * x) : u ∣ v := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hm : Ideal.Quotient.mk (Ideal.span {u}) v *
      Ideal.Quotient.mk (Ideal.span {u}) x = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
  exact hx.mul_right_injective (by simpa only [mul_comm, mul_zero, zero_mul] using hm)

theorem zero_frequency_units_force_divides {u v x y : A}
    (hx : IsUnit (Ideal.Quotient.mk (Ideal.span {u}) x))
    (hy : IsUnit (Ideal.Quotient.mk (Ideal.span {v}) y))
    (hcong : u * v ∣ v * x - u * y) : u ∣ v ∧ v ∣ u := by
  have hu : u ∣ v * x := by
    have h := dvd_add ((dvd_mul_right u v).trans hcong) (dvd_mul_right u y)
    simpa only [sub_add_cancel] using h
  have hv : v ∣ u * y := by
    have h := dvd_sub (dvd_mul_right v x) ((dvd_mul_left v u).trans hcong)
    convert h using 1 ; ring
  exact ⟨dvd_of_unit_residue_mul hx hu, dvd_of_unit_residue_mul hy hv⟩

theorem fullModulusCorrelation_zero_frequency_off_diagonal (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ)
    (hne : Ideal.span ({u} : Set A) ≠ Ideal.span ({v} : Set A)) :
    fullModulusCorrelation u v χu χv 0 = 0 := by
  classical
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  refine Quotient.inductionOn₂' x y ?_
  intro a b
  change (if scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) a) -
      scaledResidue v u (u * v) (mul_comm u v) (Ideal.Quotient.mk (Ideal.span {v}) b) =
      Ideal.Quotient.mk (Ideal.span {u * v}) 0
    then χu (Ideal.Quotient.mk (Ideal.span {u}) a) *
      star (χv (Ideal.Quotient.mk (Ideal.span {v}) b)) else 0) = 0
  by_cases hx : χu (Ideal.Quotient.mk (Ideal.span {u}) a) = 0
  · simp only [hx, zero_mul, ite_self]
  by_cases hy : χv (Ideal.Quotient.mk (Ideal.span {v}) b) = 0
  · simp only [hy, star_zero, mul_zero, ite_self]
  split_ifs with h
  · exfalso
    have hd := (scaledResidue_congruence u v a b 0).mp h
    rw [sub_zero] at hd
    obtain ⟨huv, hvu⟩ := zero_frequency_units_force_divides
      (χu.apply_ne_zero_iff.mp hx) (χv.apply_ne_zero_iff.mp hy) hd
    apply hne
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact Ideal.mem_span_singleton.mpr hvu
    · apply Ideal.span_le.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact Ideal.mem_span_singleton.mpr huv
  · rfl

variable [IsDomain A]

theorem scaledResidue_injective (d a m : A) (hm : m = d * a) (ha : a ≠ 0) :
    Function.Injective (scaledResidue d a m hm) := by
  intro x y
  refine Quotient.inductionOn₂' x y ?_
  intro r s hrs
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hrs)
  change m ∣ a * r - a * s at hd
  rw [hm, ← mul_sub, mul_comm d a] at hd
  exact (mul_dvd_mul_iff_left ha).mp hd

theorem fullModulusCorrelation_zero_frequency_diagonal (u : A) (hu : u ≠ 0)
    [Fintype (A ⧸ Ideal.span {u})] (χ : MulChar (A ⧸ Ideal.span {u}) ℂ) :
    fullModulusCorrelation u u χ χ 0 =
      (Fintype.card (A ⧸ Ideal.span {u})ˣ : ℂ) := by
  classical
  have hinj := scaledResidue_injective u u (u * u) rfl hu
  unfold fullModulusCorrelation fullCorrelation
  have hcond (x y : A ⧸ Ideal.span {u}) :
      scaledResidue u u (u * u) rfl x -
        scaledResidue u u (u * u) (mul_comm u u) y =
        Ideal.Quotient.mk (Ideal.span {u * u}) 0 ↔ y = x := by
    rw [map_zero, sub_eq_zero]
    exact hinj.eq_iff.trans eq_comm
  simp only [hcond, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.sum_one_eq_card_units

end SevenEighths.CenteredMomentCorrelation
end

end OAI

end Source306

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonSupport.lean; sha256: 113f473e9110173390c8d05d3471bf87f6e4a4ebf1cc95ab0dca0b1f4732f396 -/
section Source307
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCommonSupport
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A]

abbrev Residue (d : A) := A ⧸ Ideal.span {d}

def principalCRT (d a : A) (h : IsCoprime d a) :
    Residue (d * a) ≃+* Residue d × Residue a :=
  (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton d a).symm).trans
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {d}) (Ideal.span {a})
      ((Ideal.isCoprime_span_singleton_iff d a).mpr h))

@[simp] theorem principalCRT_mk (d a : A) (h : IsCoprime d a) (x : A) :
    principalCRT d a h (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ x) := by
  ext <;> simp [principalCRT, Ideal.quotEquivOfEq_mk]

lemma coprime_mul_dvd_iff (d a n : A) (h : IsCoprime d a) :
    d * a ∣ n ↔ d ∣ n ∧ a ∣ n := by
  constructor
  · intro hn
    exact ⟨(dvd_mul_right d a).trans hn, (dvd_mul_left a d).trans hn⟩
  · rintro ⟨hd, ha⟩
    exact h.mul_dvd hd ha

theorem full_product_congruence (D E a b n : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b) :
    (D * a) * (E * b) ∣ n ↔ D * E ∣ n ∧ a ∣ n ∧ b ∣ n := by
  have heq : (D * a) * (E * b) = (D * E) * (a * b) := by ring
  rw [heq, coprime_mul_dvd_iff _ _ _ (ha.mul_right hb), coprime_mul_dvd_iff _ _ _ hab]

theorem isUnit_residue_of_coprime (d a : A) (h : IsCoprime d a) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {d}) a) := by
  obtain ⟨u, v, huv⟩ := h
  apply IsUnit.of_mul_eq_one (Ideal.Quotient.mk (Ideal.span {d}) v)
  have hd : Ideal.Quotient.mk (Ideal.span {d}) d = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton d))
  have hm := congrArg (Ideal.Quotient.mk (Ideal.span {d})) huv
  simpa only [map_add, map_mul, map_one, hd, mul_zero, zero_mul, zero_add, mul_comm] using hm

lemma residue_eq_zero_iff_dvd (d n : A) :
    Ideal.Quotient.mk (Ideal.span {d}) n = 0 ↔ d ∣ n := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem full_congruence_split (D E a b x y j : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b) :
    (D * a) * (E * b) ∣ (E * b) * x - (D * a) * y - j ↔
      (D * E ∣ E * (b * x) - D * (a * y) - j) ∧
      Ideal.Quotient.mk (Ideal.span {a}) (E * b * x) = Ideal.Quotient.mk _ j ∧
      Ideal.Quotient.mk (Ideal.span {b}) (D * a * y) = Ideal.Quotient.mk _ (-j) := by
  rw [full_product_congruence D E a b _ ha hb hab]
  have hzeroa : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    (residue_eq_zero_iff_dvd a a).mpr dvd_rfl
  have hzerob : Ideal.Quotient.mk (Ideal.span {b}) b = 0 :=
    (residue_eq_zero_iff_dvd b b).mpr dvd_rfl
  have heq : (E * b) * x - (D * a) * y - j = E * (b * x) - D * (a * y) - j := by ring
  refine and_congr (by rw [heq]) (and_congr ?_ ?_)
  · rw [← residue_eq_zero_iff_dvd]
    simp only [map_sub, map_mul, hzeroa, mul_zero, zero_mul, sub_zero]
    exact sub_eq_zero
  · rw [← residue_eq_zero_iff_dvd]
    simp only [map_sub, map_mul, hzerob, mul_zero, zero_mul, zero_sub, map_neg]
    constructor <;> intro h <;> linear_combination -h

theorem sum_residual_constraints
    {X Y S T : Type*} [Fintype X] [Fintype Y] [CommRing S] [CommRing T]
    [Fintype S] [Fintype T]
    (p : X → Y → Prop) [∀ x y, Decidable (p x y)]
    (f : X → ℂ) (g : Y → ℂ) (α : S → ℂ) (β : T → ℂ)
    (a : Sˣ) (b : Tˣ) (j : S) (k : T) :
    (∑ x : X × S, ∑ y : Y × T,
      if p x.1 y.1 ∧ (a : S) * x.2 = j ∧ (b : T) * y.2 = k
      then (f x.1 * α x.2) * star (g y.1 * β y.2) else 0) =
    (∑ x : X, ∑ y : Y, if p x y then f x * star (g y) else 0) *
      α ((↑a⁻¹ : S) * j) * star (β ((↑b⁻¹ : T) * k)) := by
  have ha (x : S) : (a : S) * x = j ↔ x = (↑a⁻¹ : S) * j := by
    constructor
    · intro h
      rw [← h, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
  have hb (y : T) : (b : T) * y = k ↔ y = (↑b⁻¹ : T) * k := by
    constructor
    · intro h
      rw [← h, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
  simp only [Fintype.sum_prod_type, ha, hb]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : p x y
  · simp only [h, true_and, star_mul]
    simp [ite_and, Finset.sum_ite_eq', mul_assoc, mul_left_comm, mul_comm]
  · simp [h]

theorem fullCorrelation_unit_change
    {X Y R : Type*} [CommRing X] [CommRing Y] [CommRing R]
    [Fintype X] [Fintype Y]
    (left : X → R) (right : Y → R) (χ : MulChar X ℂ) (ψ : MulChar Y ℂ)
    (u : Xˣ) (v : Yˣ) (j : R) :
    fullCorrelation (fun x => left ((u : X) * x)) (fun y => right ((v : Y) * y)) χ ψ j =
      χ (↑u⁻¹ : X) * star (ψ (↑v⁻¹ : Y)) * fullCorrelation left right χ ψ j := by
  have hχ (x : X) : χ x = χ (↑u⁻¹ : X) * χ ((u : X) * x) := by
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  have hψ (y : Y) : ψ y = ψ (↑v⁻¹ : Y) * ψ ((v : Y) * y) := by
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  unfold fullCorrelation
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv u.mulLeft
  intro x
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv v.mulLeft
  intro y
  simp only [Units.mulLeft_apply]
  by_cases h : left ((u : X) * x) - right ((v : Y) * y) = j
  · simp only [h, ite_true]
    rw [hχ x, hψ y, star_mul]
    ring
  · simp only [h, ite_false, mul_zero]

lemma character_unit_inverse {X : Type*} [CommRing X] [Fintype X]
    (χ : MulChar X ℂ) (u : Xˣ) : χ (↑u⁻¹ : X) = star (χ (u : X)) := by
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit]

def residueUnit (d a : A) (h : IsCoprime d a) : (Residue d)ˣ :=
  (isUnit_residue_of_coprime d a h).unit

@[simp] theorem residueUnit_coe (d a : A) (h : IsCoprime d a) :
    (residueUnit d a h : Residue d) = Ideal.Quotient.mk _ a :=
  (isUnit_residue_of_coprime d a h).unit_spec

def scaledCommonCorrelation (D E a b : A)
    [Fintype (Residue D)] [Fintype (Residue E)]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ) (j : A) : ℂ :=
  fullCorrelation
    (fun x => scaledResidue D E (D * E) rfl (Ideal.Quotient.mk _ b * x))
    (fun y => scaledResidue E D (D * E) (mul_comm _ _) (Ideal.Quotient.mk _ a * y))
    χD χE (Ideal.Quotient.mk _ j)

theorem scaledCommonCorrelation_eq (D E a b : A)
    (hDb : IsCoprime D b) (hEa : IsCoprime E a)
    [Fintype (Residue D)] [Fintype (Residue E)]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ) (j : A) :
    scaledCommonCorrelation D E a b χD χE j =
      star (χD (Ideal.Quotient.mk _ b)) * χE (Ideal.Quotient.mk _ a) *
        fullModulusCorrelation D E χD χE j := by
  have h := fullCorrelation_unit_change
    (scaledResidue D E (D * E) rfl) (scaledResidue E D (D * E) (mul_comm _ _))
    χD χE (residueUnit D b hDb) (residueUnit E a hEa) (Ideal.Quotient.mk _ j)
  simpa only [residueUnit_coe, character_unit_inverse, star_star,
    scaledCommonCorrelation, fullModulusCorrelation] using h

theorem fullModulusCorrelation_extract (D E a b : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (χDa : MulChar (Residue (D * a)) ℂ) (χEb : MulChar (Residue (E * b)) ℂ)
    (hχDa : ∀ x : A, χDa (Ideal.Quotient.mk _ x) =
      χD (Ideal.Quotient.mk _ x) * χa (Ideal.Quotient.mk _ x))
    (hχEb : ∀ x : A, χEb (Ideal.Quotient.mk _ x) =
      χE (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x)) (j : A) :
    let α := residueUnit a (E * b) (((IsCoprime.mul_left_iff.mp ha).2.symm).mul_right hab)
    let β := residueUnit b (D * a) (((IsCoprime.mul_left_iff.mp hb).1.symm).mul_right hab.symm)
    fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      scaledCommonCorrelation D E a b χD χE j *
        χa ((↑α⁻¹ : Residue a) * Ideal.Quotient.mk _ j) *
        star (χb ((↑β⁻¹ : Residue b) * Ideal.Quotient.mk _ (-j))) := by
  dsimp only
  let e₁ := principalCRT D a (IsCoprime.mul_left_iff.mp ha).1
  let e₂ := principalCRT E b (IsCoprime.mul_left_iff.mp hb).2
  let α := residueUnit a (E * b) (((IsCoprime.mul_left_iff.mp ha).2.symm).mul_right hab)
  let β := residueUnit b (D * a) (((IsCoprime.mul_left_iff.mp hb).1.symm).mul_right hab.symm)
  let p := fun x : Residue D => fun y : Residue E =>
    scaledResidue D E (D * E) rfl (Ideal.Quotient.mk _ b * x) -
      scaledResidue E D (D * E) (mul_comm _ _) (Ideal.Quotient.mk _ a * y) =
        Ideal.Quotient.mk _ j
  have hextract : fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      ∑ x : Residue D × Residue a, ∑ y : Residue E × Residue b,
        if p x.1 y.1 ∧ (α : Residue a) * x.2 = Ideal.Quotient.mk _ j ∧
          (β : Residue b) * y.2 = Ideal.Quotient.mk _ (-j)
        then (χD x.1 * χa x.2) * star (χE y.1 * χb y.2) else 0 := by
    unfold fullModulusCorrelation fullCorrelation
    apply Fintype.sum_equiv e₁.toEquiv
    intro x
    apply Fintype.sum_equiv e₂.toEquiv
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [e₁, e₂, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, principalCRT_mk,
      hχDa, hχEb, p, α, β, residueUnit_coe, ← map_mul]
    rw [scaledResidue_congruence, scaledResidue_congruence,
      full_congruence_split D E a b x y j ha hb hab]
    split_ifs <;> rfl
  rw [hextract, sum_residual_constraints]
  rfl

theorem fullModulusCorrelation_complete_support (D E a b : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (χDa : MulChar (Residue (D * a)) ℂ) (χEb : MulChar (Residue (E * b)) ℂ)
    (hχDa : ∀ x : A, χDa (Ideal.Quotient.mk _ x) =
      χD (Ideal.Quotient.mk _ x) * χa (Ideal.Quotient.mk _ x))
    (hχEb : ∀ x : A, χEb (Ideal.Quotient.mk _ x) =
      χE (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x)) (j : A) :
    fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      fullModulusCorrelation D E χD χE j *
        (χE (Ideal.Quotient.mk _ a) * star (χa (Ideal.Quotient.mk _ E))) *
        (χb (Ideal.Quotient.mk _ D) * star (χD (Ideal.Quotient.mk _ b))) *
        (χb (Ideal.Quotient.mk _ a) * star (χa (Ideal.Quotient.mk _ b))) *
        χa (Ideal.Quotient.mk _ j) * star (χb (Ideal.Quotient.mk _ (-j))) := by
  rw [fullModulusCorrelation_extract D E a b ha hb hab χD χE χa χb χDa χEb hχDa hχEb j]
  rw [scaledCommonCorrelation_eq D E a b (IsCoprime.mul_left_iff.mp hb).1
    (IsCoprime.mul_left_iff.mp ha).2 χD χE j]
  simp only [map_mul, character_unit_inverse, residueUnit_coe, star_mul, star_star]
  ring

end SevenEighths.CenteredMomentCommonSupport
end

end OAI

end Source307

/- Original source: OAI/NumberTheory/DirichletL/Moments/Basic.lean; sha256: 437f147882d26f668db45b3ed9721f3c9c334ecc4e76fe22e8848e005f26ba71 -/
section Source308
namespace OAI

open scoped BigOperators NNReal
namespace SevenEighths.CenteredMoment
noncomputable section

variable {M R : Type*} [CommMonoid M] [CommRing R]

structure MaskedCharacter (M R : Type*) [CommMonoid M] [CommRing R] where
  residue : M →* R
  character : MulChar R ℂ
  keep : M → Prop
  keep_mul : ∀ a b, keep (a * b) ↔ keep a ∧ keep b

def ofResidueMask {S : Type*} [CommRing S] (ρ : M →* R)
    (χ : MulChar R ℂ) (puncture : M →* S) : MaskedCharacter M R where
  residue := ρ
  character := χ
  keep a := IsUnit (puncture a)
  keep_mul a b := by
    rw [map_mul]
    exact (Commute.all _ _).isUnit_mul_iff

@[simp] theorem ofResidueMask_keep_one {S : Type*} [CommRing S]
    (ρ : M →* R) (χ : MulChar R ℂ) (puncture : M →* S) :
    (ofResidueMask ρ χ puncture).keep 1 := by
  change IsUnit (puncture 1)
  simp only [map_one, isUnit_one]

def MaskedCharacter.value (d : MaskedCharacter M R) (a : M) : ℂ :=
  @ite ℂ (d.keep a) (Classical.propDecidable _) (d.character (d.residue a)) 0

@[simp] theorem MaskedCharacter.value_mul (d : MaskedCharacter M R) (a b : M) :
    d.value (a * b) = d.value a * d.value b := by
  classical
  simp only [MaskedCharacter.value, d.keep_mul, map_mul]
  split_ifs <;> simp_all

def normTwist (N : M →* ℝ≥0) (t : ℝ) (a : M) : ℂ :=
  ((N a : ℝ) : ℂ) ^ (Complex.I * t)

@[simp] theorem normTwist_mul (N : M →* ℝ≥0) (t : ℝ) (a b : M) :
    normTwist N t (a * b) = normTwist N t a * normTwist N t b := by
  simp only [normTwist, map_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (N a).coe_nonneg (N b).coe_nonneg _

def coefficient (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ) (a : M) : ℂ :=
  d.value a * normTwist N t a

@[simp] theorem coefficient_mul (d : MaskedCharacter M R) (N : M →* ℝ≥0)
    (t : ℝ) (a b : M) :
    coefficient d N t (a * b) = coefficient d N t a * coefficient d N t b := by
  simp only [coefficient, MaskedCharacter.value_mul, normTwist_mul]
  ring

def plainSum (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (s : Finset M) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ a ∈ s, coefficient d N t a * W ((N a : ℝ) / X)

def rectangle (N : M →* ℝ≥0) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (a b : M) : ℂ :=
  W₁ ((N a : ℝ) / X₁) * W₂ ((N b : ℝ) / X₂) -
    W₁ ((N a : ℝ) / Y₁) * W₂ ((N b : ℝ) / Y₂)

theorem rectangle_sum_eq (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (s₁ s₂ : Finset M) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ a ∈ s₁, ∑ b ∈ s₂,
      coefficient d N t (a * b) * rectangle N W₁ W₂ X₁ X₂ Y₁ Y₂ a b) =
      plainSum d N t s₁ W₁ X₁ * plainSum d N t s₂ W₂ X₂ -
        plainSum d N t s₁ W₁ Y₁ * plainSum d N t s₂ W₂ Y₂ := by
  simp only [plainSum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [coefficient_mul, rectangle]
  ring

theorem slot_rectangle_sum_eq (d : MaskedCharacter M R) (N : M →* ℝ≥0) (t : ℝ)
    (p : M) (s₁ s₂ : Finset M) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ a ∈ s₁, ∑ b ∈ s₂,
      coefficient d N t (p * (a * b)) * rectangle N W₁ W₂ X₁ X₂ Y₁ Y₂ a b) =
      coefficient d N t p *
        (plainSum d N t s₁ W₁ X₁ * plainSum d N t s₂ W₂ X₂ -
          plainSum d N t s₁ W₁ Y₁ * plainSum d N t s₂ W₂ Y₂) := by
  rw [← rectangle_sum_eq]
  simp only [coefficient_mul, Finset.mul_sum, mul_assoc]

def volumeTerm (c I : ℂ) (t X : ℝ) : ℂ :=
  c * (X : ℂ) ^ (1 + Complex.I * t) * I

theorem volume_products_eq (c I₁ I₂ : ℂ) (t X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hscale : X₁ * X₂ = Y₁ * Y₂) :
    volumeTerm c I₁ t X₁ * volumeTerm c I₂ t X₂ =
      volumeTerm c I₁ t Y₁ * volumeTerm c I₂ t Y₂ := by
  have hpow : (X₁ : ℂ) ^ (1 + Complex.I * t) *
      (X₂ : ℂ) ^ (1 + Complex.I * t) =
      (Y₁ : ℂ) ^ (1 + Complex.I * t) * (Y₂ : ℂ) ^ (1 + Complex.I * t) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hX₁ hX₂,
      ← Complex.mul_cpow_ofReal_nonneg hY₁ hY₂, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, hscale]
  unfold volumeTerm
  calc
    _ = c ^ 2 * I₁ * I₂ *
      ((X₁ : ℂ) ^ (1 + Complex.I * t) * (X₂ : ℂ) ^ (1 + Complex.I * t)) := by ring
    _ = _ := by rw [hpow]; ring

theorem centered_error_identity (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (hmain : a₁ * a₂ = b₁ * b₂) :
    A₁ * A₂ - B₁ * B₂ =
      (A₁ - a₁) * A₂ + a₁ * (A₂ - a₂) -
        (B₁ - b₁) * B₂ - b₁ * (B₂ - b₂) := by
  linear_combination hmain

theorem norm_centered_le (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (hmain : a₁ * a₂ = b₁ * b₂) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤
      ‖A₁ - a₁‖ * ‖A₂‖ + ‖a₁‖ * ‖A₂ - a₂‖ +
        ‖B₁ - b₁‖ * ‖B₂‖ + ‖b₁‖ * ‖B₂ - b₂‖ := by
  rw [centered_error_identity A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hmain]
  calc
    _ ≤ ‖(A₁ - a₁) * A₂ + a₁ * (A₂ - a₂) - (B₁ - b₁) * B₂‖ +
        ‖b₁ * (B₂ - b₂)‖ := norm_sub_le _ _
    _ ≤ (‖(A₁ - a₁) * A₂ + a₁ * (A₂ - a₂)‖ +
        ‖(B₁ - b₁) * B₂‖) + ‖b₁ * (B₂ - b₂)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖(A₁ - a₁) * A₂‖ + ‖a₁ * (A₂ - a₂)‖) +
        ‖(B₁ - b₁) * B₂‖) + ‖b₁ * (B₂ - b₂)‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ = _ := by simp only [norm_mul]

theorem norm_centered_le_of_approx
    (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ C E : ℝ)
    (hmain : a₁ * a₂ = b₁ * b₂)
    (hE : 0 ≤ E)
    (hA₁ : ‖A₁ - a₁‖ ≤ E) (hA₂ : ‖A₂ - a₂‖ ≤ E)
    (hB₁ : ‖B₁ - b₁‖ ≤ E) (hB₂ : ‖B₂ - b₂‖ ≤ E)
    (hvA₂ : ‖A₂‖ ≤ C * X₂) (hva₁ : ‖a₁‖ ≤ C * X₁)
    (hvB₂ : ‖B₂‖ ≤ C * Y₂) (hvb₁ : ‖b₁‖ ≤ C * Y₁) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ E * C * (X₁ + X₂ + Y₁ + Y₂) := by
  have h₁ := mul_le_mul hA₁ hvA₂ (norm_nonneg A₂) hE
  have h₂ := mul_le_mul hA₂ hva₁ (norm_nonneg a₁) hE
  have h₃ := mul_le_mul hB₁ hvB₂ (norm_nonneg B₂) hE
  have h₄ := mul_le_mul hB₂ hvb₁ (norm_nonneg b₁) hE
  have h := norm_centered_le A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hmain
  nlinarith

theorem scale_le_product_div {X Y T L : ℝ}
    (hX : 0 ≤ X) (hL : 0 < L) (hY : L ≤ Y) (hprod : X * Y = T) :
    X ≤ T / L := by
  apply (le_div_iff₀ hL).mpr
  rw [← hprod]
  exact mul_le_mul_of_nonneg_left hY hX

theorem sum_scales_le {X₁ X₂ Y₁ Y₂ T L : ℝ}
    (hL : 0 < L) (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    X₁ + X₂ + Y₁ + Y₂ ≤ 4 * (T / L) := by
  have a := scale_le_product_div (le_trans hL.le hX₁) hL hX₂ hprodX
  have b := scale_le_product_div (le_trans hL.le hX₂) hL hX₁
    (by simpa only [mul_comm] using hprodX)
  have c := scale_le_product_div (le_trans hL.le hY₁) hL hY₂ hprodY
  have d := scale_le_product_div (le_trans hL.le hY₂) hL hY₁
    (by simpa only [mul_comm] using hprodY)
  linarith

theorem centered_saving_of_approx
    (A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ T L C E : ℝ)
    (hmain : a₁ * a₂ = b₁ * b₂)
    (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hA₁ : ‖A₁ - a₁‖ ≤ E) (hA₂ : ‖A₂ - a₂‖ ≤ E)
    (hB₁ : ‖B₁ - b₁‖ ≤ E) (hB₂ : ‖B₂ - b₂‖ ≤ E)
    (hvA₂ : ‖A₂‖ ≤ C * X₂) (hva₁ : ‖a₁‖ ≤ C * X₁)
    (hvB₂ : ‖B₂‖ ≤ C * Y₂) (hvb₁ : ‖b₁‖ ≤ C * Y₁)
    (hL : 0 < L) (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂)
    (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ 4 * E * C * (T / L) := by
  have h := norm_centered_le_of_approx A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ C E hmain hE hA₁ hA₂ hB₁ hB₂ hvA₂ hva₁ hvB₂ hvb₁
  have hs := sum_scales_le hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY
  calc
    _ ≤ E * C * (X₁ + X₂ + Y₁ + Y₂) := h
    _ ≤ E * C * (4 * (T / L)) := mul_le_mul_of_nonneg_left hs (mul_nonneg hE hC)
    _ = _ := by ring

theorem extracted_volume_phase (X D t : ℝ) (hX : 0 ≤ X) (hD : 0 < D) :
    (D : ℂ) ^ (Complex.I * t) * ((X / D : ℝ) : ℂ) ^ (1 + Complex.I * t) =
      (X : ℂ) ^ (1 + Complex.I * t) / (D : ℂ) := by
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hD)
  have hp : (D : ℂ) ^ (Complex.I * t) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hDc)
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hX hD.le,
    Complex.cpow_add _ _ hDc, Complex.cpow_one]
  field_simp

theorem extracted_volume_sum {D : Type*} (s : Finset D) (a : D → ℂ)
    (norm : D → ℝ) (hnorm : ∀ d ∈ s, 0 < norm d)
    (c I : ℂ) (t X : ℝ) (hX : 0 ≤ X) :
    (∑ d ∈ s, a d * (norm d : ℂ) ^ (Complex.I * t) *
      volumeTerm c I t (X / norm d)) =
      volumeTerm (c * ∑ d ∈ s, a d / (norm d : ℂ)) I t X := by
  unfold volumeTerm
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have h := extracted_volume_phase X (norm d) t hX (hnorm d hd)
  calc
    _ = a d * c * I * ((norm d : ℂ) ^ (Complex.I * t) *
        ((X / norm d : ℝ) : ℂ) ^ (1 + Complex.I * t)) := by ring
    _ = _ := by rw [h]; ring

theorem centered_volume_fallback (A₁ A₂ B₁ B₂ : ℂ)
    (X₁ X₂ Y₁ Y₂ T C : ℝ)
    (hA₁ : ‖A₁‖ ≤ C * X₁) (hA₂ : ‖A₂‖ ≤ C * X₂)
    (hB₁ : ‖B₁‖ ≤ C * Y₁) (hB₂ : ‖B₂‖ ≤ C * Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    ‖A₁ * A₂ - B₁ * B₂‖ ≤ 2 * C ^ 2 * T := by
  have hA := mul_le_mul hA₁ hA₂ (norm_nonneg A₂) ((norm_nonneg A₁).trans hA₁)
  have hB := mul_le_mul hB₁ hB₂ (norm_nonneg B₂) ((norm_nonneg B₁).trans hB₁)
  have h := norm_sub_le (A₁ * A₂) (B₁ * B₂)
  rw [norm_mul, norm_mul] at h
  have heX : C * X₁ * (C * X₂) = C ^ 2 * T := by rw [← hprodX]; ring
  have heY : C * Y₁ * (C * Y₂) = C ^ 2 * T := by rw [← hprodY]; ring
  rw [heX] at hA
  rw [heY] at hB
  linarith

theorem normalized_centered_saving (D : ℂ) (T L C E : ℝ)
    (hT : 0 < T) (hbound : ‖D‖ ≤ 4 * E * C * (T / L)) :
    ‖(Real.sqrt T : ℂ)⁻¹ * D‖ ≤ 4 * E * C * (Real.sqrt T / L) := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
  calc
    _ ≤ (Real.sqrt T)⁻¹ * (4 * E * C * (T / L)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hs.le)
    _ = 4 * E * C * ((T / Real.sqrt T) / L) := by ring
    _ = _ := by
      have hdiv : T / Real.sqrt T = Real.sqrt T :=
        (div_eq_iff hs.ne').mpr (Real.mul_self_sqrt hT.le).symm
      rw [hdiv]

end
end SevenEighths.CenteredMoment

end OAI

end Source308

/- Original source: OAI/NumberTheory/DirichletL/Moments/Mask.lean; sha256: d97b84e6f9e170826f96c17bda9cbe979257f5823032244acfc48702d9071e43 -/
section Source309
namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentMask
open ActualEisensteinCubic IdealMobiusDivisorSum
open UniqueFactorizationMonoid

theorem ideal_coprime_mobius (I R : Ideal O) (hR : R ≠ 0) :
    (if IsCoprime I R then (1 : ℂ) else 0) =
      ∑ D ∈ idealDivisors R, if D ∣ I then (moebius D : ℂ) else 0 := by
  let G : Ideal O := R ⊔ I
  have hG : G ≠ 0 := by
    intro hz
    apply hR
    apply le_antisymm _ bot_le
    exact le_sup_left.trans_eq hz
  have hdiv : (idealDivisors R).filter (fun D => D ∣ I) = idealDivisors G := by
    ext D
    simp only [Finset.mem_filter, mem_idealDivisors hR, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G, sup_comm]

theorem tsum_ideal_divisible (D : Ideal O) (hD : D ≠ 0) (f : Ideal O → ℂ) :
    (∑' I : Ideal O, if D ∣ I then f I else 0) =
      ∑' J : Ideal O, f (D * J) := by
  let F : Ideal O → ℂ := fun I => if D ∣ I then f I else 0
  have hrange : Function.support F ⊆ Set.range (fun J : Ideal O => D * J) := by
    intro I hI
    have hd : D ∣ I := by
      by_contra hn
      exact hI (by simp only [F, ite_eq_right hn])
    obtain ⟨J, hJ⟩ := hd
    exact ⟨J, hJ.symm⟩
  have ht := (mul_right_injective₀ hD).tsum_eq hrange
  calc
    _ = ∑' J : Ideal O, F (D * J) := ht.symm
    _ = _ := by
      apply tsum_congr
      intro J
      simp only [F, dvd_mul_right, ite_true]

theorem masked_ideal_sum_eq (R : Ideal O) (hR : R ≠ 0)
    (f : Ideal O → ℂ) (hf : Summable f) :
    (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) * f I) =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * ∑' J : Ideal O, f (D * J) := by
  have hterm (I : Ideal O) : (if IsCoprime I R then (1 : ℂ) else 0) * f I =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * (if D ∣ I then f I else 0) := by
    rw [ideal_coprime_mobius I R hR, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro D _
    by_cases h : D ∣ I <;> simp only [h, ite_true, ite_false, zero_mul, mul_zero]
  have hsum (D : Ideal O) :
      Summable (fun I : Ideal O => (moebius D : ℂ) * (if D ∣ I then f I else 0)) := by
    have h := (hf.indicator {I : Ideal O | D ∣ I}).mul_left (moebius D : ℂ)
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using h
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun D _ => hsum D)]
  apply Finset.sum_congr rfl
  intro D hD
  rw [tsum_mul_left, tsum_ideal_divisible D (ne_zero_of_dvd_ne_zero hR
    ((mem_idealDivisors hR).mp hD))]

theorem annular_ideal_sum_summable (χ : Ideal O → ℂ) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b) :
    Summable (fun I : Ideal O => χ I * W ((Ideal.absNorm I : ℝ) / X)) := by
  apply summable_of_hasFiniteSupport
  apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil (b * X))).subset
  intro I hI
  have hw : W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
    intro hz
    exact hI (by simp only [hz, mul_zero])
  have hn : (Ideal.absNorm I : ℝ) ≤ b * X := (div_le_iff₀ hX).mp (hs hw)
  exact_mod_cast hn.trans (Nat.le_ceil (b * X))

theorem masked_plain_ideal_sum (R : Ideal O) (hR : R ≠ 0)
    (χ : Ideal O →* ℂ) (W : ℝ → ℂ) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b) :
    (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (χ I * W ((Ideal.absNorm I : ℝ) / X))) =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * χ D *
        ∑' J : Ideal O, χ J * W ((Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D)) := by
  rw [masked_ideal_sum_eq R hR _ (annular_ideal_sum_summable χ W b X hX hs)]
  apply Finset.sum_congr rfl
  intro D hD
  have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
  have hnD : (Ideal.absNorm D : ℝ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm D ≠ 0 by
      intro hz
      exact hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hterms (J : Ideal O) :
      χ (D * J) * W ((Ideal.absNorm (D * J) : ℝ) / X) =
        χ D * (χ J * W ((Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D))) := by
    rw [map_mul, map_mul, Nat.cast_mul]
    have harg : (Ideal.absNorm D : ℝ) * Ideal.absNorm J / X =
        (Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D) := by field_simp
    rw [harg]
    ring
  simp_rw [hterms]
  rw [tsum_mul_left]
  ring

theorem polynomial_mask_divisor_bound (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ R : Ideal O, R ≠ 0 →
      (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ((idealDivisors R).card : ℝ) ≤ C * Z ^ ε := by
  let δ := ε / (B + 1)
  have hden : 0 < B + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨C, hC, hcount⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm
  have hexp : B * δ ≤ ε := by
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc
    _ ≤ C * (Ideal.absNorm R : ℝ) ^ δ := hcount R hR
    _ ≤ C * (Z ^ B) ^ δ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hnorm hδ.le) hC.le
    _ = C * Z ^ (B * δ) := by rw [← Real.rpow_mul (by linarith : 0 ≤ Z)]
    _ ≤ C * Z ^ ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hexp) hC.le

end SevenEighths.CenteredMomentMask
end

end OAI

end Source309

/- Original source: OAI/NumberTheory/DirichletL/Moments/SupportedCorrelation.lean; sha256: 1b1544a26117427e8f81bbd6cf36248b1899164a746e63215716440c82c9a82e -/
section Source310
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupportedCorrelation
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentCommonSupport

def supportedModulusCharacter (d : O) (hd : Supported (Ideal.span {d})) :
    MulChar (Residue d) ℂ where
  toFun x := Quotient.liftOn' x (fun z => idealRowHom z (Ideal.span {d})) (by
    intro x y hxy
    exact idealRowHom_congr_mod _ x y ((Ideal.span {d}).quotientRel_def.mp hxy))
  map_one' := idealRowHom_one_supported _ hd
  map_mul' := by
    intro x y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact idealRowHom_argument_mul x y _
  map_nonunit' := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change idealRowHom x (Ideal.span {d}) = 0
    by_contra hn
    have hm := idealRowHom_sixth_mask x (Ideal.span {d}) hd
    rw [idealRowHom_argument_pow x 6 _ hd, Ideal.isCoprime_span_singleton_iff] at hm
    have hcop : IsCoprime d x := by
      by_contra h
      rw [ite_eq_right h] at hm
      exact (pow_ne_zero 6 hn) hm
    exact hx (isUnit_residue_of_coprime d x hcop)

@[simp] theorem supportedModulusCharacter_mk (d : O)
    (hd : Supported (Ideal.span {d})) (x : O) :
    supportedModulusCharacter d hd (Ideal.Quotient.mk _ x) = idealRowHom x (Ideal.span {d}) := rfl

lemma supported_mul_elements (d a : O)
    (hd : Supported (Ideal.span {d})) (ha : Supported (Ideal.span {a})) :
    Supported (Ideal.span {d * a}) := by
  rw [← Ideal.span_singleton_mul_span_singleton]
  exact (supported_mul_iff _ _).mpr ⟨hd, ha⟩

theorem supportedModulusCharacter_mul (d a : O)
    (hd : Supported (Ideal.span {d})) (ha : Supported (Ideal.span {a})) (x : O) :
    supportedModulusCharacter (d * a) (supported_mul_elements d a hd ha) (Ideal.Quotient.mk _ x) =
      supportedModulusCharacter d hd (Ideal.Quotient.mk _ x) *
        supportedModulusCharacter a ha (Ideal.Quotient.mk _ x) := by
  simp only [supportedModulusCharacter_mk, ← Ideal.span_singleton_mul_span_singleton, map_mul]

lemma sexticReciprocityPhase_symm (a b : O) :
    sexticReciprocityPhase a b = sexticReciprocityPhase b a := by
  exact congrArg (fun z : ℤ => (z : ℂ)) (QuadraticAllOddCRT.quadraticRaySign_symm _ _)

@[simp] lemma star_sexticReciprocityPhase (a b : O) :
    star (sexticReciprocityPhase a b) = sexticReciprocityPhase a b := by
  simp only [sexticReciprocityPhase, star_intCast]

theorem supported_opposite_phase (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcop : IsCoprime a b) [Fintype (Residue a)] :
    idealRowHom a (Ideal.span {b}) * star (idealRowHom b (Ideal.span {a})) =
      sexticReciprocityPhase a b := by
  rw [idealRowHom_primary_reciprocity b a hpb hpa hb ha,
    sexticReciprocityPhase_symm b a, mul_assoc]
  have hunit := isUnit_residue_of_coprime a b hcop
  have hn := (supportedModulusCharacter a ha).apply_ne_zero_iff.mpr hunit
  change idealRowHom b (Ideal.span {a}) ≠ 0 at hn
  have heq : idealRowHom b (Ideal.span {a}) * star (idealRowHom b (Ideal.span {a})) = 1 := by
    change supportedModulusCharacter a ha (Ideal.Quotient.mk _ b) *
      star (supportedModulusCharacter a ha (Ideal.Quotient.mk _ b)) = 1
    rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
    exact mul_inv_cancel₀ hn
  rw [heq, mul_one]

def supportedCorrelation (u v : O)
    (hu : Supported (Ideal.span {u})) (hv : Supported (Ideal.span {v}))
    [Fintype (Residue u)] [Fintype (Residue v)] (j : O) : ℂ :=
  fullModulusCorrelation u v (supportedModulusCharacter u hu) (supportedModulusCharacter v hv) j

theorem supported_complete_common_support (D E a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcopA : IsCoprime (D * E) a) (hcopB : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))] (j : O) :
    supportedCorrelation (D * a) (E * b)
      (supported_mul_elements D a hD ha) (supported_mul_elements E b hE hb) j =
      supportedCorrelation D E hD hE j * sexticReciprocityPhase a E *
        star (sexticReciprocityPhase b D) * sexticReciprocityPhase a b *
        idealRowHom j (Ideal.span {a}) * star (idealRowHom (-j) (Ideal.span {b})) := by
  unfold supportedCorrelation
  rw [fullModulusCorrelation_complete_support D E a b hcopA hcopB hab
    (supportedModulusCharacter D hD) (supportedModulusCharacter E hE)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)
    (supportedModulusCharacter (D * a) (supported_mul_elements D a hD ha))
    (supportedModulusCharacter (E * b) (supported_mul_elements E b hE hb))
    (supportedModulusCharacter_mul D a hD ha) (supportedModulusCharacter_mul E b hE hb) j]
  simp only [supportedModulusCharacter_mk]
  rw [supported_opposite_phase a E ha hE hpa hpE (IsCoprime.mul_left_iff.mp hcopA).2.symm,
    supported_opposite_phase D b hD hb hpD hpb (IsCoprime.mul_left_iff.mp hcopB).1,
    supported_opposite_phase a b ha hb hpa hpb hab,
    sexticReciprocityPhase_symm D b, star_sexticReciprocityPhase]

lemma supported_element_ne_zero (d : O) (hd : Supported (Ideal.span {d})) : d ≠ 0 := by
  intro h
  exact hd.1 (by simp [h])

def actualCorrelation (u v : O)
    (hu : Supported (Ideal.span {u})) (hv : Supported (Ideal.span {v})) (j : O) : ℂ := by
  letI := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero u hu)
  letI := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero v hv)
  letI : Fintype (Residue u) := Fintype.ofFinite _
  letI : Fintype (Residue v) := Fintype.ofFinite _
  exact supportedCorrelation u v hu hv j

def completeSupportExtension (D E : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (j a b : O) : ℂ :=
  actualCorrelation D E hD hE j * sexticReciprocityPhase a E *
    star (sexticReciprocityPhase b D) * sexticReciprocityPhase a b *
    idealRowHom j (Ideal.span {a}) * star (idealRowHom (-j) (Ideal.span {b}))

theorem actual_complete_common_support (D E a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcopA : IsCoprime (D * E) a) (hcopB : IsCoprime (D * E) b) (hab : IsCoprime a b)
    (j : O) :
    actualCorrelation (D * a) (E * b)
      (supported_mul_elements D a hD ha) (supported_mul_elements E b hE hb) j =
      completeSupportExtension D E hD hE j a b := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero D hD)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero E hE)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero a ha)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero b hb)
  let := ConcreteTraceCRT.finite_quotient_span
    (mul_ne_zero (supported_element_ne_zero D hD) (supported_element_ne_zero a ha))
  let := ConcreteTraceCRT.finite_quotient_span
    (mul_ne_zero (supported_element_ne_zero E hE) (supported_element_ne_zero b hb))
  let : Fintype (Residue D) := Fintype.ofFinite _
  let : Fintype (Residue E) := Fintype.ofFinite _
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (D * a)) := Fintype.ofFinite _
  let : Fintype (Residue (E * b)) := Fintype.ofFinite _
  exact supported_complete_common_support D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB hab j

theorem actual_complete_support_mobius (D E a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcopA : IsCoprime (D * E) a) (hcopB : IsCoprime (D * E) b) (j : O) :
    (if IsCoprime a b then actualCorrelation (D * a) (E * b)
      (supported_mul_elements D a hD ha) (supported_mul_elements E b hE hb) j else 0) =
      completeSupportExtension D E hD hE j a b *
        ∑ T ∈ IdealMobiusDivisorSum.idealDivisors (Ideal.span {b}),
          if T ∣ Ideal.span {a} then (UniqueFactorizationMonoid.moebius T : ℂ) else 0 := by
  rw [← CenteredMomentMask.ideal_coprime_mobius (Ideal.span {a}) (Ideal.span {b}) hb.1,
    Ideal.isCoprime_span_singleton_iff]
  by_cases hab : IsCoprime a b
  · rw [ite_eq_left hab, ite_eq_left hab, mul_one]
    exact actual_complete_common_support D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB hab j
  · simp only [hab, ite_false, mul_zero]

end SevenEighths.CenteredMomentSupportedCorrelation
end

end OAI

end Source310

/- Original source: OAI/NumberTheory/DirichletL/Moments/Support.lean; sha256: 2399cec862de47958a5240c0fcc82add5ecec41e589b619d174fd1791c59ea98 -/
section Source311
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupport
open UniqueFactorizationMonoid IdealMobiusDivisorSum CanonicalQuadraticSieve

def supportExtract (I : Ideal O) (S : Finset (Ideal O)) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P ∈ S)).prod

def supportResidual (I : Ideal O) (S : Finset (Ideal O)) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P ∉ S)).prod

theorem supportExtract_factors (I : Ideal O) (S : Finset (Ideal O)) :
    normalizedFactors (supportExtract I S) = (normalizedFactors I).filter (fun P => P ∈ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_factors (I : Ideal O) (S : Finset (Ideal O)) :
    normalizedFactors (supportResidual I S) = (normalizedFactors I).filter (fun P => P ∉ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportExtract_ne_zero (I : Ideal O) (S : Finset (Ideal O)) : supportExtract I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_ne_zero (I : Ideal O) (S : Finset (Ideal O)) : supportResidual I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)

theorem support_reconstruct (I : Ideal O) (hI : I ≠ 0) (S : Finset (Ideal O)) :
    supportExtract I S * supportResidual I S = I := by
  rw [supportExtract, supportResidual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportExtract_support (I : Ideal O) (S : Finset (Ideal O)) :
    primeSupport (supportExtract I S) = primeSupport I ∩ S := by
  ext P
  simp [primeSupport, supportExtract_factors]

theorem supportResidual_support (I : Ideal O) (S : Finset (Ideal O)) :
    primeSupport (supportResidual I S) = primeSupport I \ S := by
  ext P
  simp [primeSupport, supportResidual_factors]

theorem supportExtract_count (I P : Ideal O) (S : Finset (Ideal O)) :
    (normalizedFactors (supportExtract I S)).count P =
      if P ∈ S then (normalizedFactors I).count P else 0 := by
  rw [supportExtract_factors, Multiset.count_filter]

theorem supportResidual_count (I P : Ideal O) (S : Finset (Ideal O)) :
    (normalizedFactors (supportResidual I S)).count P =
      if P ∈ S then 0 else (normalizedFactors I).count P := by
  rw [supportResidual_factors, Multiset.count_filter]
  split_ifs <;> rfl

theorem supportExtract_supported (I : Ideal O) (hI : Supported I) (S : Finset (Ideal O)) :
    Supported (supportExtract I S) := by
  refine ⟨supportExtract_ne_zero I S, ?_⟩
  intro P hP
  rw [supportExtract_factors] at hP
  exact hI.2 P (Multiset.mem_filter.mp hP).1

theorem supportResidual_supported (I : Ideal O) (hI : Supported I) (S : Finset (Ideal O)) :
    Supported (supportResidual I S) := by
  refine ⟨supportResidual_ne_zero I S, ?_⟩
  intro P hP
  rw [supportResidual_factors] at hP
  exact hI.2 P (Multiset.mem_filter.mp hP).1

theorem extracted_residual_coprime (I J : Ideal O) (S : Finset (Ideal O)) :
    IsCoprime (supportExtract I S) (supportResidual J S) := by
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportExtract_ne_zero I S) (supportResidual_ne_zero J S)).mp
  rw [supportExtract_support, supportResidual_support]
  exact Finset.disjoint_left.mpr (by
    intro P hP hQ
    exact (Finset.mem_sdiff.mp hQ).2 (Finset.mem_inter.mp hP).2)

theorem common_support_residual_coprime (I J : Ideal O) :
    let S := primeSupport I ∩ primeSupport J
    IsCoprime (supportResidual I S) (supportResidual J S) := by
  dsimp only
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportResidual_ne_zero I _) (supportResidual_ne_zero J _)).mp
  rw [supportResidual_support, supportResidual_support]
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  exact (Finset.mem_sdiff.mp hP).2
    (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hP).1, (Finset.mem_sdiff.mp hQ).1⟩)

theorem supportExtract_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) :
    supportExtract (I * J) S = supportExtract I S * supportExtract J S := by
  simp only [supportExtract, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportResidual_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) :
    supportResidual (I * J) S = supportResidual I S * supportResidual J S := by
  simp only [supportResidual, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportExtract_prime (P : Ideal O) (hP : Prime P) (S : Finset (Ideal O)) :
    supportExtract P S = if P ∈ S then P else 1 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP))
  simp only [supportExtract, hf, Multiset.filter_singleton]
  split_ifs <;> simp

theorem supportResidual_prime (P : Ideal O) (hP : Prime P) (S : Finset (Ideal O)) :
    supportResidual P S = if P ∈ S then 1 else P := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP))
  simp only [supportResidual, hf, Multiset.filter_singleton]
  split_ifs <;> simp_all

theorem shared_prime_slot_freeze (P I : Ideal O) (hP : Prime P) (hI : I ≠ 0)
    (S : Finset (Ideal O)) (hPS : P ∈ S) :
    supportExtract (P * I) S = P * supportExtract I S ∧
      supportResidual (P * I) S = supportResidual I S := by
  rw [supportExtract_mul P I hP.ne_zero hI S, supportResidual_mul P I hP.ne_zero hI S,
    supportExtract_prime P hP S, supportResidual_prime P hP S]
  simp only [hPS, ite_true, one_mul, and_self]

theorem supportExtract_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (hp : ∀ i ∈ T, p i ≠ 0) (S : Finset (Ideal O)) :
    supportExtract (∏ i ∈ T, p i) S = ∏ i ∈ T, supportExtract (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportExtract, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportExtract_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

theorem supportResidual_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (hp : ∀ i ∈ T, p i ≠ 0) (S : Finset (Ideal O)) :
    supportResidual (∏ i ∈ T, p i) S = ∏ i ∈ T, supportResidual (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportResidual, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportResidual_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

open CompletedGauss hiding primeSupport
open CanonicalRowCompletion CenteredMomentSupportedCorrelation

def idealCorrelation (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (j : O) : ℂ :=
  actualCorrelation (primaryGenerator I) (primaryGenerator J)
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) j

theorem idealCorrelation_complete_extraction (I J : Ideal O)
    (hI : Supported I) (hJ : Supported J) (j : O) :
    let S := primeSupport I ∩ primeSupport J
    let D := supportExtract I S
    let E := supportExtract J S
    let A := supportResidual I S
    let B := supportResidual J S
    idealCorrelation I J hI hJ j =
      idealCorrelation D E (supportExtract_supported I hI S) (supportExtract_supported J hJ S) j *
        sexticReciprocityPhase (primaryGenerator A) (primaryGenerator E) *
        star (sexticReciprocityPhase (primaryGenerator B) (primaryGenerator D)) *
        sexticReciprocityPhase (primaryGenerator A) (primaryGenerator B) *
        idealRowHom j A * star (idealRowHom (-j) B) := by
  let S := primeSupport I ∩ primeSupport J
  let D := supportExtract I S
  let E := supportExtract J S
  let A := supportResidual I S
  let B := supportResidual J S
  have hD := supportExtract_supported I hI S
  have hE := supportExtract_supported J hJ S
  have hA := supportResidual_supported I hI S
  have hB := supportResidual_supported J hJ S
  have hpD := primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)
  have hpE := primaryGenerator_spec E (supported_primaryGenerator_ne_zero E hE)
  have hpA := primaryGenerator_spec A (supported_primaryGenerator_ne_zero A hA)
  have hpB := primaryGenerator_spec B (supported_primaryGenerator_ne_zero B hB)
  have hcpA : IsCoprime (primaryGenerator D * primaryGenerator E) (primaryGenerator A) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpD.1, hpE.1, hpA.1]
    exact (extracted_residual_coprime I I S).mul_left (extracted_residual_coprime J I S)
  have hcpB : IsCoprime (primaryGenerator D * primaryGenerator E) (primaryGenerator B) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpD.1, hpE.1, hpB.1]
    exact (extracted_residual_coprime I J S).mul_left (extracted_residual_coprime J J S)
  have hcpAB : IsCoprime (primaryGenerator A) (primaryGenerator B) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [hpA.1, hpB.1]
    exact common_support_residual_coprime I J
  have h := actual_complete_common_support
    (primaryGenerator D) (primaryGenerator E) (primaryGenerator A) (primaryGenerator B)
    ((supported_span_primaryGenerator_iff D).mpr hD)
    ((supported_span_primaryGenerator_iff E).mpr hE)
    ((supported_span_primaryGenerator_iff A).mpr hA)
    ((supported_span_primaryGenerator_iff B).mpr hB)
    hpD.2 hpE.2 hpA.2 hpB.2 hcpA hcpB hcpAB j
  have hDA : D * A = I := support_reconstruct I hI.1 S
  have hEB : E * B = J := support_reconstruct J hJ.1 S
  simpa only [completeSupportExtension, ← primaryGenerator_mul, hDA, hEB, hpA.1, hpB.1,
    idealCorrelation] using h

end SevenEighths.CenteredMomentSupport
end

end OAI

end Source311

/- Original source: OAI/NumberTheory/DirichletL/ThetaProduct.lean; sha256: 6748e3720bcd136b2c688b12b5cc50f7fab6a764d9da82ba87e7149b86d75595 -/
section Source312
namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology

namespace SevenEighths.ThetaProduct

theorem rapid_product_sub (f g : ℝ → ℂ) (a b : ℂ)
    (hf : ∀ r : ℝ, (fun x => f x - a) =O[atTop] (fun x : ℝ => x ^ r))
    (hg : ∀ r : ℝ, (fun x => g x - b) =O[atTop] (fun x : ℝ => x ^ r))
    (r : ℝ) :
    (fun x => f x * g x - a * b) =O[atTop] (fun x : ℝ => x ^ r) := by
  have hg0 : g =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    have hc : (fun _ : ℝ => b) =O[atTop] (fun x : ℝ => x ^ (0 : ℝ)) := by
      simpa using (isBigO_const_one ℝ b (atTop : Filter ℝ))
    have h := (hg 0).add hc
    simpa using h
  have h₁ := (hf r).mul hg0
  have h₂ := (hg r).const_mul_left a
  have hid : (fun x => f x * g x - a * b) =
      fun x => (f x - a) * g x + a * (g x - b) := by
    funext x
    ring
  rw [hid]
  have h₁' : (fun x => (f x - a) * g x) =O[atTop] (fun x : ℝ => x ^ r) := by
    simpa using h₁
  exact h₁'.add h₂

def product (P Q : WeakFEPair ℂ)
    (hPf : ContinuousOn P.f (Ioi 0)) (hPg : ContinuousOn P.g (Ioi 0))
    (hQf : ContinuousOn Q.f (Ioi 0)) (hQg : ContinuousOn Q.g (Ioi 0)) :
    WeakFEPair ℂ where
  f := fun x => P.f x * Q.f x
  g := fun x => P.g x * Q.g x
  k := P.k + Q.k
  ε := P.ε * Q.ε
  f₀ := P.f₀ * Q.f₀
  g₀ := P.g₀ * Q.g₀
  hf_int := (hPf.mul hQf).locallyIntegrableOn measurableSet_Ioi
  hg_int := (hPg.mul hQg).locallyIntegrableOn measurableSet_Ioi
  hk := add_pos P.hk Q.hk
  hε := mul_ne_zero P.hε Q.hε
  h_feq x hx := by
    rw [P.h_feq x hx, Q.h_feq x hx, Real.rpow_add hx]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  hf_top := rapid_product_sub P.f Q.f P.f₀ Q.f₀ P.hf_top Q.hf_top
  hg_top := rapid_product_sub P.g Q.g P.g₀ Q.g₀ P.hg_top Q.hg_top

theorem rapid_rescale (f : ℝ → ℂ) (a : ℂ)
    (hf : ∀ r : ℝ, (fun x => f x - a) =O[atTop] (fun x : ℝ => x ^ r))
    {u : ℝ} (hu : 0 < u) (r : ℝ) :
    (fun x => f (u * x) - a) =O[atTop] (fun x : ℝ => x ^ r) := by
  have ht : Tendsto (fun x : ℝ => u * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hu).2 tendsto_id
  have h := (hf r).comp_tendsto ht
  have heq : (fun x : ℝ => (u * x) ^ r) =ᶠ[atTop]
      (fun x : ℝ => u ^ r * x ^ r) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact Real.mul_rpow hu.le hx
  exact h.trans (heq.isBigO.trans ((isBigO_refl (fun x : ℝ => x ^ r) atTop).const_mul_left _))

def rescale (P : WeakFEPair ℂ)
    (hPf : ContinuousOn P.f (Ioi 0)) (hPg : ContinuousOn P.g (Ioi 0))
    (u : ℝ) (hu : 0 < u) : WeakFEPair ℂ where
  f := fun x => P.f (u * x)
  g := fun x => P.g (u⁻¹ * x)
  k := P.k
  ε := P.ε * (u ^ (-P.k) : ℝ)
  f₀ := P.f₀
  g₀ := P.g₀
  hf_int := (hPf.comp (by fun_prop) (fun x hx => mul_pos hu hx)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (hPg.comp (by fun_prop) (fun x hx => mul_pos (inv_pos.mpr hu) hx)).locallyIntegrableOn
    measurableSet_Ioi
  hk := P.hk
  hε := mul_ne_zero P.hε (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hu _).ne')
  h_feq x hx := by
    have heq : u * (1 / x) = 1 / (u⁻¹ * x) := by field_simp
    rw [heq, P.h_feq _ (mul_pos (inv_pos.mpr hu) hx),
      Real.mul_rpow (inv_pos.mpr hu).le hx.le, Real.inv_rpow hu.le,
      ← Real.rpow_neg hu.le]
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  hf_top := rapid_rescale P.f P.f₀ P.hf_top hu
  hg_top := rapid_rescale P.g P.g₀ P.hg_top (inv_pos.mpr hu)

def shiftedPair (a b : UnitAddCircle) : WeakFEPair ℂ :=
  product (HurwitzZeta.hurwitzEvenFEPair a) (HurwitzZeta.hurwitzEvenFEPair b)
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_evenKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_cosKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_evenKernel b))
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_cosKernel b))

@[simp] theorem shiftedPair_k (a b : UnitAddCircle) : (shiftedPair a b).k = 1 := by
  norm_num [shiftedPair, product, HurwitzZeta.hurwitzEvenFEPair]

@[simp] theorem shiftedPair_f (a b : UnitAddCircle) (t : ℝ) :
    (shiftedPair a b).f t =
      (HurwitzZeta.evenKernel a t : ℂ) * (HurwitzZeta.evenKernel b t : ℂ) := rfl

theorem shiftedPair_differentiableAt (a b : UnitAddCircle) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DifferentiableAt ℂ (shiftedPair a b).Λ s := by
  exact (shiftedPair a b).differentiableAt_Λ (Or.inl hs₀)
    (Or.inl (by simpa using hs₁))

def scaledEvenPair (a : UnitAddCircle) (u : ℝ) (hu : 0 < u) : WeakFEPair ℂ :=
  rescale (HurwitzZeta.hurwitzEvenFEPair a)
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_evenKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (HurwitzZeta.continuousOn_cosKernel a)) u hu

theorem scaledEvenPair_f_continuous (a : UnitAddCircle) (u : ℝ) (hu : 0 < u) :
    ContinuousOn (scaledEvenPair a u hu).f (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn
    (HurwitzZeta.continuousOn_evenKernel a)).comp (by fun_prop)
      (fun x hx => mul_pos hu hx)

theorem scaledEvenPair_g_continuous (a : UnitAddCircle) (u : ℝ) (hu : 0 < u) :
    ContinuousOn (scaledEvenPair a u hu).g (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn
    (HurwitzZeta.continuousOn_cosKernel a)).comp (by fun_prop)
      (fun x hx => mul_pos (inv_pos.mpr hu) hx)

def rectangularPair (a b : UnitAddCircle) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    WeakFEPair ℂ :=
  product (scaledEvenPair a u hu) (scaledEvenPair b v hv)
    (scaledEvenPair_f_continuous a u hu) (scaledEvenPair_g_continuous a u hu)
    (scaledEvenPair_f_continuous b v hv) (scaledEvenPair_g_continuous b v hv)

@[simp] theorem rectangularPair_k (a b : UnitAddCircle) (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) : (rectangularPair a b u v hu hv).k = 1 := by
  norm_num [rectangularPair, scaledEvenPair, rescale, product, HurwitzZeta.hurwitzEvenFEPair]

theorem rectangularPair_hasSum (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ =>
      (Real.exp (-Real.pi * (u * (n.1 + a) ^ 2 + v * (n.2 + b) ^ 2) * t) : ℂ))
      ((rectangularPair a b u v hu hv).f t) := by
  have h₁ := HurwitzZeta.hasSum_int_evenKernel a (mul_pos hu ht)
  have h₂ := HurwitzZeta.hasSum_int_evenKernel b (mul_pos hv ht)
  have hprod := h₁.mul h₂ (h₁.summable.mul_of_nonneg h₂.summable
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le))
  have hid (n : ℤ × ℤ) :
      Real.exp (-Real.pi * (u * (n.1 + a) ^ 2 + v * (n.2 + b) ^ 2) * t) =
      Real.exp (-Real.pi * (n.1 + a) ^ 2 * (u * t)) *
        Real.exp (-Real.pi * (n.2 + b) ^ 2 * (v * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hid]
  simpa only [rectangularPair, product, scaledEvenPair, rescale,
    HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, Complex.ofReal_mul] using
    (Complex.hasSum_ofReal.mpr hprod)

theorem rectangularPair_differentiableAt (a b : UnitAddCircle) (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DifferentiableAt ℂ (rectangularPair a b u v hu hv).Λ s := by
  exact (rectangularPair a b u v hu hv).differentiableAt_Λ (Or.inl hs₀)
    (Or.inl (by simpa using hs₁))

end SevenEighths.ThetaProduct

end

end OAI

end Source312

/- Original source: OAI/NumberTheory/DirichletL/EisensteinTheta.lean; sha256: da30674e27b65d10a3f472564263c57e26c24a9f1986e22cdcab26209e79da17 -/
section Source313
namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace SevenEighths.EisensteinTheta
open ThetaProduct

def normForm (x y : ℝ) : ℝ := x ^ 2 - x * y + y ^ 2

def shearEquiv : (ℤ × (ℤ × Fin 2)) ≃ (Fin 2 × (ℤ × ℤ)) where
  toFun n := (n.2.2, (n.1 - n.2.1, n.2.1))
  invFun p := (p.2.1 + p.2.2, (p.2.2, p.1))
  left_inv n := by simp
  right_inv p := by simp

def parityEquiv : (ℤ × ℤ) ≃ (Fin 2 × (ℤ × ℤ)) :=
  (Equiv.prodCongr (Equiv.refl ℤ) (Int.divModEquiv 2)).trans shearEquiv

def xShift (a b L : ℝ) (e : Fin 2) : ℝ := (2 * a - b - L * e) / (2 * L)
def yShift (b L : ℝ) (e : Fin 2) : ℝ := (b + L * e) / (2 * L)

theorem normForm_parity (a b L : ℝ) (hL : L ≠ 0) (e : Fin 2) (i j : ℤ) :
    normForm (a + L * (i + j)) (b + L * (2 * j + e)) =
      L ^ 2 * (i + xShift a b L e) ^ 2 +
        (3 * L ^ 2) * (j + yShift b L e) ^ 2 := by
  unfold normForm xShift yShift
  field_simp
  ring

def cosetTheta (a b L t : ℝ) : ℂ :=
  ∑' n : ℤ × ℤ,
    (Real.exp (-Real.pi * normForm (a + L * n.1) (b + L * n.2) * t) : ℂ)

def parityPair (a b L : ℝ) (hL : 0 < L) (e : Fin 2) : WeakFEPair ℂ :=
  rectangularPair (xShift a b L e) (yShift b L e) (L ^ 2) (3 * L ^ 2)
    (sq_pos_of_pos hL) (mul_pos (by norm_num) (sq_pos_of_pos hL))

theorem cosetTheta_hasSum (a b L : ℝ) (hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ =>
      (Real.exp (-Real.pi * normForm (a + L * n.1) (b + L * n.2) * t) : ℂ))
      (∑ e : Fin 2, (parityPair a b L hL e).f t) := by
  let F : Fin 2 × (ℤ × ℤ) → ℝ := fun p =>
    Real.exp (-Real.pi * (L ^ 2 * (p.2.1 + xShift a b L p.1) ^ 2 +
      (3 * L ^ 2) * (p.2.2 + yShift b L p.1) ^ 2) * t)
  have hsum (e : Fin 2) : HasSum (fun n : ℤ × ℤ => (F (e, n) : ℂ))
      ((parityPair a b L hL e).f t) :=
    rectangularPair_hasSum (xShift a b L e) (yShift b L e) (L ^ 2) (3 * L ^ 2) (sq_pos_of_pos hL)
      (mul_pos (by norm_num) (sq_pos_of_pos hL)) ht
  have hreal (e : Fin 2) : Summable (fun n : ℤ × ℤ => F (e, n)) :=
    Complex.summable_ofReal.mp (hsum e).summable
  have hF : Summable F :=
    (summable_prod_of_nonneg (fun _ => (Real.exp_pos _).le)).2
      ⟨hreal, (hasSum_fintype _).summable⟩
  have hFC : Summable (fun p => (F p : ℂ)) := Complex.summable_ofReal.mpr hF
  have hid (p : Fin 2 × (ℤ × ℤ)) :
      Real.exp (-Real.pi * normForm
        (a + L * (parityEquiv.symm p).1) (b + L * (parityEquiv.symm p).2) * t) = F p := by
    change Real.exp (-Real.pi * normForm
      (a + L * ((p.2.1 + p.2.2 : ℤ) : ℝ))
      (b + L * ((p.2.2 * 2 + (p.1 : ℕ) : ℤ) : ℝ)) * t) = _
    push_cast
    rw [show (p.2.2 : ℝ) * 2 = 2 * p.2.2 from mul_comm _ _]
    rw [normForm_parity a b L hL.ne']
  apply parityEquiv.symm.hasSum_iff.mp
  change HasSum (fun p : Fin 2 × (ℤ × ℤ) =>
    (Real.exp (-Real.pi * normForm (a + L * (parityEquiv.symm p).1)
      (b + L * (parityEquiv.symm p).2) * t) : ℂ)) _
  simp_rw [hid]
  convert hFC.hasSum using 1
  rw [hFC.tsum_prod, tsum_fintype]
  exact (Finset.sum_congr rfl (fun e _ => (hsum e).tsum_eq)).symm

theorem cosetTheta_eq_parity_sum (a b L : ℝ) (hL : 0 < L) {t : ℝ} (ht : 0 < t) :
    cosetTheta a b L t = ∑ e : Fin 2, (parityPair a b L hL e).f t :=
  (cosetTheta_hasSum a b L hL ht).tsum_eq

@[simp] theorem parityPair_k (a b L : ℝ) (hL : 0 < L) (e : Fin 2) :
    (parityPair a b L hL e).k = 1 := rectangularPair_k _ _ _ _ _ _

def cosetConstant (a b L : ℝ) (hL : 0 < L) : ℂ :=
  ∑ e : Fin 2, (parityPair a b L hL e).f₀

theorem parityPair_f₀ (a b L : ℝ) (hL : 0 < L) (e : Fin 2) :
    (parityPair a b L hL e).f₀ =
      (if (xShift a b L e : UnitAddCircle) = 0 then 1 else 0) *
      (if (yShift b L e : UnitAddCircle) = 0 then 1 else 0) := rfl

theorem cosetConstant_eq (a b L : ℝ) (hL : 0 < L)
    (ha₀ : 0 ≤ a) (haL : a < L) (hb₀ : 0 ≤ b) (hbL : b < L) :
    cosetConstant a b L hL = if a = 0 ∧ b = 0 then 1 else 0 := by
  have htwo : 0 < 2 * L := by positivity
  have hy1 : yShift b L 1 ∈ Set.Ico (0 : ℝ) 1 := by
    simp only [yShift, Fin.val_one, Nat.cast_one, mul_one, Set.mem_Ico]
    constructor
    · positivity
    · apply (div_lt_one htwo).2
      linarith
  have hy1pos : 0 < yShift b L 1 := by
    simp only [yShift, Fin.val_one, Nat.cast_one, mul_one]
    exact div_pos (by linarith) htwo
  have hy1ne : (yShift b L 1 : UnitAddCircle) ≠ 0 := by
    intro h
    have := (AddCircle.coe_eq_zero_iff_of_mem_Ico hy1).mp h
    linarith
  have hy0 : yShift b L 0 ∈ Set.Ico (0 : ℝ) 1 := by
    simp only [yShift, Fin.val_zero, Nat.cast_zero, mul_zero, add_zero, Set.mem_Ico]
    constructor
    · positivity
    · apply (div_lt_one htwo).2
      linarith
  have hy0iff : (yShift b L 0 : UnitAddCircle) = 0 ↔ b = 0 := by
    rw [AddCircle.coe_eq_zero_iff_of_mem_Ico hy0]
    simp [yShift, div_eq_zero_iff, hL.ne']
  rw [cosetConstant, Fin.sum_univ_two, parityPair_f₀, parityPair_f₀,
    ite_eq_right hy1ne, mul_zero, add_zero]
  by_cases hb : b = 0
  · subst b
    rw [ite_eq_left (hy0iff.mpr rfl), mul_one]
    have hx : xShift a 0 L 0 = a / L := by
      simp only [xShift, sub_zero, Fin.val_zero, Nat.cast_zero, mul_zero]
      field_simp
    have hxmem : a / L ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨div_nonneg ha₀ hL.le, (div_lt_one hL).2 haL⟩
    have hxiff : (xShift a 0 L 0 : UnitAddCircle) = 0 ↔ a = 0 := by
      rw [hx, AddCircle.coe_eq_zero_iff_of_mem_Ico hxmem]
      simp [div_eq_zero_iff, hL.ne']
    simp only [hxiff, and_true]
  · rw [ite_eq_right (fun h => hb (hy0iff.mp h)), mul_zero, ite_eq_right (fun h => hb h.2)]

def completedCoset (a b L : ℝ) (hL : 0 < L) (s : ℂ) : ℂ :=
  ∑ e : Fin 2, (parityPair a b L hL e).Λ s

theorem completedCoset_differentiableAt (a b L : ℝ) (hL : 0 < L)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DifferentiableAt ℂ (completedCoset a b L hL) s := by
  apply DifferentiableAt.fun_sum
  intro e _
  exact rectangularPair_differentiableAt (xShift a b L e) (yShift b L e)
    (L ^ 2) (3 * L ^ 2) _ _ hs₀ hs₁

end SevenEighths.EisensteinTheta

end

end OAI

end Source313

/- Original source: OAI/NumberTheory/DirichletL/Hecke/Theta.lean; sha256: 5fe20e38278c74632a0b77aac4bc7a2b6217360378178e0b7dc5085cd73954c9 -/
section Source314
namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta

theorem locallyIntegrableOn_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, LocallyIntegrableOn (f i) (Ioi 0)) :
    LocallyIntegrableOn (∑ i ∈ s, f i) (Ioi 0) := by
  exact Finset.sum_induction f (fun g => LocallyIntegrableOn g (Ioi 0))
    (fun _ _ => LocallyIntegrableOn.add) (locallyIntegrableOn_const 0) hf

def finitePair {ι : Type*} [Fintype ι] (P : ι → WeakFEPair ℂ)
    (hk : ∀ i, (P i).k = 1) (w : ι → ℂ) : WeakFEPair ℂ where
  f := ∑ i, w i • (P i).f
  g := ∑ i, (w i * (P i).ε) • (P i).g
  k := 1
  ε := 1
  f₀ := ∑ i, w i * (P i).f₀
  g₀ := ∑ i, w i * (P i).ε * (P i).g₀
  hf_int := locallyIntegrableOn_sum Finset.univ _
    (fun i _ => (P i).hf_int.smul (w i))
  hg_int := locallyIntegrableOn_sum Finset.univ _
    (fun i _ => (P i).hg_int.smul (w i * (P i).ε))
  hk := by norm_num
  hε := one_ne_zero
  h_feq x hx := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(P i).h_feq x hx, hk i]
    simp only [smul_eq_mul]
    ring
  hf_top r := by
    have h := Asymptotics.IsBigO.fun_sum (s := Finset.univ)
      (fun i _ => ((P i).hf_top r).const_mul_left (w i))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      mul_sub] using h
  hg_top r := by
    have h := Asymptotics.IsBigO.fun_sum (s := Finset.univ)
      (fun i _ => ((P i).hg_top r).const_mul_left (w i * (P i).ε))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      mul_sub] using h

def regroup (N : ℕ) : ((ℤ × Fin N) × (ℤ × Fin N)) ≃ ((Fin N × Fin N) × (ℤ × ℤ)) where
  toFun p := ((p.1.2, p.2.2), (p.1.1, p.2.1))
  invFun p := ((p.2.1, p.1.1), (p.2.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def residueEquiv (N : ℕ) [NeZero N] : (ℤ × ℤ) ≃ ((Fin N × Fin N) × (ℤ × ℤ)) :=
  (Equiv.prodCongr (Int.divModEquiv N) (Int.divModEquiv N)).trans (regroup N)

def periodicCoeff {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (n : ℤ × ℤ) : ℂ :=
  w (residueEquiv N n).1

def theta {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℤ × ℤ, periodicCoeff w n *
    (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ)

def pair {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) : WeakFEPair ℂ :=
  finitePair (fun p : (Fin N × Fin N) × Fin 2 =>
    parityPair p.1.1 p.1.2 N (Nat.cast_pos.mpr (NeZero.pos N)) p.2)
    (fun _ => ThetaProduct.rectangularPair_k ..) (fun p => w p.1)

@[simp] theorem pair_k {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).k = 1 := rfl

theorem theta_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ => periodicCoeff w n *
      (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ)) ((pair w).f t) := by
  let hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  let F : (Fin N × Fin N) × (ℤ × ℤ) → ℂ := fun p => w p.1 *
    (Real.exp (-Real.pi * normForm (p.1.1 + (N : ℝ) * p.2.1)
      (p.1.2 + (N : ℝ) * p.2.2) * t) : ℂ)
  have hinner (a : Fin N × Fin N) : HasSum (fun n : ℤ × ℤ => F (a,n))
      (w a * ∑ e : Fin 2, (parityPair a.1 a.2 N hN e).f t) :=
    (cosetTheta_hasSum a.1 a.2 N hN ht).mul_left (w a)
  have hFnorm : Summable (fun p => ‖F p‖) :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
      ⟨fun a => (hinner a).summable.norm, (hasSum_fintype _).summable⟩
  have hF : Summable F := hFnorm.of_norm
  have hid (p : (Fin N × Fin N) × (ℤ × ℤ)) :
      periodicCoeff w ((residueEquiv N).symm p) *
        (Real.exp (-Real.pi * normForm (((residueEquiv N).symm p).1)
          (((residueEquiv N).symm p).2) * t) : ℂ) = F p := by
    simp only [periodicCoeff, Equiv.apply_symm_apply]
    change w p.1 * (Real.exp (-Real.pi * normForm
      ((p.2.1 * (N : ℤ) + p.1.1 : ℤ) : ℝ)
      ((p.2.2 * (N : ℤ) + p.1.2 : ℤ) : ℝ) * t) : ℂ) = F p
    simp only [F, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    congr 4 ; ring_nf
  apply (residueEquiv N).symm.hasSum_iff.mp
  change HasSum (fun p => periodicCoeff w ((residueEquiv N).symm p) *
    (Real.exp (-Real.pi * normForm (((residueEquiv N).symm p).1)
      (((residueEquiv N).symm p).2) * t) : ℂ)) _
  simp_rw [hid]
  convert hF.hasSum using 1
  rw [hF.tsum_prod, tsum_fintype]
  simp_rw [(hinner _).tsum_eq]
  simp only [pair, finitePair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, Finset.mul_sum]

theorem theta_eq_pair {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) : theta w t = (pair w).f t :=
  (theta_hasSum w ht).tsum_eq

theorem pair_f₀ {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).f₀ = w (0, 0) := by
  have hconst (a : Fin N × Fin N) :
      cosetConstant a.1 a.2 N (Nat.cast_pos.mpr (NeZero.pos N)) =
        if a = (0, 0) then 1 else 0 := by
    rw [cosetConstant_eq _ _ _ _ (by positivity) (by exact_mod_cast a.1.isLt)
      (by positivity) (by exact_mod_cast a.2.isLt)]
    have hz : (a.1 : ℝ) = 0 ∧ (a.2 : ℝ) = 0 ↔ a = (0, 0) := by
      simp only [Prod.ext_iff, Fin.ext_iff, Fin.val_zero, Nat.cast_eq_zero]
    simp only [hz]
  change (∑ p : (Fin N × Fin N) × Fin 2,
    w p.1 * (parityPair p.1.1 p.1.2 N _ p.2).f₀) = _
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  change (∑ a : Fin N × Fin N, w a * cosetConstant a.1 a.2 N _) = _
  simp_rw [hconst]
  simp

def dualScalar (N : ℕ) : ℂ :=
  ((((N : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    (((3 * (N : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

theorem pair_g₀ {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).g₀ = 2 * dualScalar N * ∑ a, w a := by
  simp only [pair, finitePair, parityPair, ThetaProduct.rectangularPair,
    ThetaProduct.product, ThetaProduct.scaledEvenPair, ThetaProduct.rescale,
    HurwitzZeta.hurwitzEvenFEPair, one_mul, mul_one]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  simp_rw [← two_mul]
  rw [← Finset.mul_sum]
  simp only [← Finset.sum_mul, dualScalar]
  ring

theorem pair_g₀_eq_zero {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (hw : ∑ a, w a = 0) : (pair w).g₀ = 0 := by rw [pair_g₀, hw, mul_zero]

def completed {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) : ℂ → ℂ := (pair w).Λ

theorem completed_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) : DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inl (by simpa using hs₁))

theorem pair_hasMellin {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t => (pair w).f t - (pair w).f₀) s (completed w s) :=
  (pair w).hasMellin (by simpa using hs)

def latticeL {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * completed w s

theorem completed_differentiableAt_of_mean_zero {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (hw : ∑ a, w a = 0) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inr (pair_g₀_eq_zero w hw))

theorem latticeL_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, w a = 0) :
    DifferentiableAt ℂ (latticeL w) s := by
  have hΛ : DifferentiableAt ℂ (completed w) s := by
    rcases hs₁ with hs₁ | hw
    · exact completed_differentiableAt w hs₀ hs₁
    · exact completed_differentiableAt_of_mean_zero w hw hs₀
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul hΛ

def regularizedCompleted {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) : ℂ :=
  (s - 1) * ((pair w).Λ₀ s - s⁻¹ * (pair w).f₀) + (pair w).g₀

theorem regularizedCompleted_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedCompleted w) s := by
  exact (((differentiableAt_id.sub_const 1).mul
    (((pair w).differentiable_Λ₀ s).sub
      ((differentiableAt_id.inv hs₀).mul_const (pair w).f₀))).add_const (pair w).g₀)

theorem regularizedCompleted_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedCompleted w s = (s - 1) * completed w s := by
  unfold regularizedCompleted completed WeakFEPair.Λ
  simp only [pair_k, Complex.ofReal_one, show (pair w).ε = 1 from rfl,
    smul_eq_mul, one_div]
  have hsub : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
  field_simp
  ring

def regularizedLatticeL {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * regularizedCompleted w s

theorem regularizedLatticeL_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedLatticeL w) s := by
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul
        (regularizedCompleted_differentiableAt w hs₀)

theorem regularizedLatticeL_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedLatticeL w s = (s - 1) * latticeL w s := by
  unfold regularizedLatticeL latticeL
  rw [regularizedCompleted_eq w hs₀ hs₁]
  ring

theorem completed_functional_equation {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (s : ℂ) :
    completed w (1 - s) = (pair w).symm.Λ s := by
  change (pair w).Λ (1 - s) = (pair w).symm.Λ s
  simpa only [pair_k, Complex.ofReal_one, show (pair w).ε = 1 from rfl, one_smul] using
    (pair w).functional_equation s

end SevenEighths.HeckeTheta

end

end OAI

end Source314

/- Original source: OAI/NumberTheory/DirichletL/Hecke/Family.lean; sha256: 9871d175749b34ec40cf66ccc14b4faa0a9ef08831cb3fa901c944e57c7b9ec6 -/
section Source315
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeFamily

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

def omega : O := (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

def coordinateElement (x y : ℤ) : O := (x : O) + (y : O) * omega

structure Character where
  modulus : Ideal O
  modulus_ne_bot : modulus ≠ ⊥
  residue : MulChar (O ⧸ modulus) ℂ
  unit_trivial : ∀ u : Oˣ, residue (Ideal.Quotient.mk modulus (u : O)) = 1
  period : ℕ
  period_pos : 0 < period
  period_mem : (period : O) ∈ modulus

def Character.ofResidue (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk M (u : O)) = 1) : Character := by
  letI : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  letI : Fintype (O ⧸ M) := Fintype.ofFinite _
  exact {
    modulus := M
    modulus_ne_bot := hM
    residue := χ
    unit_trivial := hu
    period := Fintype.card (O ⧸ M)
    period_pos := Fintype.card_pos
    period_mem := Ideal.Quotient.eq_zero_iff_mem.mp (by
      simpa only [map_natCast] using Nat.cast_card_eq_zero (O ⧸ M)) }

instance (χ : Character) : NeZero χ.period := ⟨Nat.ne_of_gt χ.period_pos⟩

def elementCoeff (χ : Character) (z : O) : ℂ := χ.residue (Ideal.Quotient.mk χ.modulus z)

def coefficients (χ : Character) (a : Fin χ.period × Fin χ.period) : ℂ :=
  elementCoeff χ (coordinateElement a.1 a.2)

@[simp] theorem elementCoeff_one (χ : Character) : elementCoeff χ 1 = 1 := by
  simp [elementCoeff]

theorem elementCoeff_mul (χ : Character) (z w : O) :
    elementCoeff χ (z * w) = elementCoeff χ z * elementCoeff χ w := by
  simp [elementCoeff, map_mul]

theorem elementCoeff_unit_mul (χ : Character) (u : Oˣ) (z : O) :
    elementCoeff χ ((u : O) * z) = elementCoeff χ z := by
  rw [elementCoeff_mul]
  have hu : elementCoeff χ (u : O) = 1 := χ.unit_trivial u
  rw [hu, one_mul]

theorem quotient_period (χ : Character) :
    Ideal.Quotient.mk χ.modulus (χ.period : O) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr χ.period_mem

theorem elementCoeff_add_period_mul (χ : Character) (z w : O) :
    elementCoeff χ (z + (χ.period : O) * w) = elementCoeff χ z := by
  simp [elementCoeff, map_add, map_mul, quotient_period χ]

theorem periodicCoeff_eq_elementCoeff (χ : Character) (n : ℤ × ℤ) :
    HeckeTheta.periodicCoeff (coefficients χ) n =
      elementCoeff χ (coordinateElement n.1 n.2) := by
  obtain ⟨p, rfl⟩ := (HeckeTheta.residueEquiv χ.period).symm.surjective n
  simp only [HeckeTheta.periodicCoeff, Equiv.apply_symm_apply, coefficients]
  change elementCoeff χ (coordinateElement p.1.1 p.1.2) =
    elementCoeff χ (coordinateElement (p.2.1 * (χ.period : ℤ) + p.1.1)
      (p.2.2 * (χ.period : ℤ) + p.1.2))
  have heq : coordinateElement (p.2.1 * (χ.period : ℤ) + p.1.1)
      (p.2.2 * (χ.period : ℤ) + p.1.2) =
      coordinateElement p.1.1 p.1.2 + (χ.period : O) *
        ((p.2.1 : O) + (p.2.2 : O) * omega) := by
    unfold coordinateElement
    push_cast
    ring
  rw [heq, elementCoeff_add_period_mul]

def continuedLattice (χ : Character) : ℂ → ℂ := HeckeTheta.latticeL (coefficients χ)

theorem continuedLattice_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, (coefficients χ) a = 0) :
    DifferentiableAt ℂ (continuedLattice χ) s :=
  HeckeTheta.latticeL_differentiableAt (coefficients χ) hs₀ hs₁

end SevenEighths.HeckeFamily

end

end OAI

end Source315

/- Original source: OAI/NumberTheory/DirichletL/Detector/Phase.lean; sha256: 410cb5e78d9182c1d215bf98800886db38237408e6cc270b1d649c4f529cfc66 -/
section Source316
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay ConcreteTraceCRT
open QuadraticAllOddCRT
local notation "O" => ActualEisensteinCubic.O

def G (a : O) : ℂ := fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)

def reciprocitySign (a b : O) : ℂ :=
  (quadraticRaySign (residue a) (residue b) : ℂ)

theorem G_mul (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    G (a * b) = G a * G b * reciprocitySign a b := by
  change fixedGValue (residue (a * b)) = fixedGValue (residue a) * fixedGValue (residue b) * reciprocitySign a b
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift]
  simp only [map_mul, mul_inv_rev, residue_mul]
  rw [quadraticRayValue_mul _ _ ha hb]
  unfold reciprocitySign
  ring

theorem reciprocitySign_mul_right (a b c : O) :
    reciprocitySign a (b * c) = reciprocitySign a b * reciprocitySign a c := by
  simp only [reciprocitySign, residue_mul, quadraticRaySign_mul_right, Int.cast_mul]

theorem reciprocitySign_sq (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    reciprocitySign a b ^ 2 = 1 := by
  unfold reciprocitySign
  exact_mod_cast quadraticRaySign_sq (residue a) (residue b) ha hb

theorem reciprocitySign_cube_right (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    reciprocitySign a (b ^ 3) = reciprocitySign a b := by
  rw [show b ^ 3 = b ^ 2 * b by ring, reciprocitySign_mul_right,
    pow_two, reciprocitySign_mul_right]
  have hs := reciprocitySign_sq a b ha hb
  calc
    _ = reciprocitySign a b ^ 2 * reciprocitySign a b := by ring
    _ = reciprocitySign a b := by rw [hs, one_mul]

theorem G_completed_index (c n : O)
    (hc : EisensteinEPrimaryPhase.odd (residue c))
    (hn : EisensteinEPrimaryPhase.odd (residue n)) :
    G (c * n ^ 3) = G c * reciprocitySign c n * G (n ^ 3) := by
  have hn3 : EisensteinEPrimaryPhase.odd (residue (n ^ 3)) := by
    rw [show n ^ 3 = (n * n) * n by ring, residue_mul, residue_mul]
    exact QuadraticAllOddCRT.odd_mul _ _ (QuadraticAllOddCRT.odd_mul _ _ hn hn) hn
  rw [G_mul c (n ^ 3) hc hn3, reciprocitySign_cube_right c n hc hn]
  ring

theorem quadraticRayValue_cube (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) :
    quadraticRayValue (EisensteinEPrimaryPhase.mul
      (EisensteinEPrimaryPhase.mul r r) r) = quadraticRayValue r := by
  have he : ∀ r : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.odd r →
      quadraticRayExponent (EisensteinEPrimaryPhase.mul
        (EisensteinEPrimaryPhase.mul r r) r) = quadraticRayExponent r := by decide
  rw [quadraticRayValue_eq_fourthRoot _ (odd_mul _ _ (odd_mul _ _ hr hr) hr),
    he r hr, ← quadraticRayValue_eq_fourthRoot r hr]

theorem G_cube (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) :
    G (a ^ 3) = quadraticRayValue (residue a) := by
  have hχ := congrArg
    (fun η : MulChar (O ⧸ cubicTwoIdeal) O => η (Ideal.Quotient.mk cubicTwoIdeal a))
    (cubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hχ
  have hc := congrArg eisEmbedding hχ
  simp only [map_pow, map_one] at hc
  change fixedGValue (residue (a ^ 3)) = quadraticRayValue (residue a)
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift]
  simp only [map_pow, hc, inv_one, one_mul]
  rw [show a ^ 3 = (a * a) * a by ring, residue_mul, residue_mul]
  exact quadraticRayValue_cube (residue a) ha

end SevenEighths.ProbePhase
end

end OAI

end Source316

/- Original source: OAI/NumberTheory/DirichletL/Detector/Completed.lean; sha256: aacdde1452e633f7190ef1170925afa84cb14f38222898cf4ca6c91cae7b843a -/
section Source317
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeCompleted
open ActualEisensteinCubic CompletedGauss
open RayFourExpansion QuadraticGaussRay SecondPassArithmetic

local notation "O" => ActualEisensteinCubic.O

def completedIndex (I J : Ideal O) : O := primaryGenerator I * primaryGenerator J ^ 3

def completedMask (S : Finset (Ideal O)) (D I J : Ideal O) : ℂ :=
  if D ∣ I * J ^ 3 ∧ ∀ p ∈ S, ¬p ∣ I * J ^ 3 then 1 else 0

def completedCorrection (I J : Ideal O) : ℂ :=
  rayMask (completedIndex I J) *
    star (fixedGQuotientValue
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (completedIndex I J)))

theorem completedCorrection_eq_phase (I J : Ideal O) :
    completedCorrection I J = rayMask (completedIndex I J) *
      star (ProbePhase.G (completedIndex I J)) := rfl

theorem completedMask_norm_le_one (S : Finset (Ideal O)) (D I J : Ideal O) :
    ‖completedMask S D I J‖ ≤ 1 := by
  unfold completedMask
  split_ifs <;> norm_num

theorem completedCorrection_norm_le_two (I J : Ideal O) :
    ‖completedCorrection I J‖ ≤ 2 := by
  have hm : ‖rayMask (completedIndex I J)‖ ≤ 1 := by
    unfold rayMask
    split_ifs <;> norm_num
  unfold completedCorrection
  rw [norm_mul, norm_star]
  exact (mul_le_mul hm (fixedGQuotientValue_norm_le_two _) (norm_nonneg _) (by norm_num)).trans_eq
    (by norm_num)

def markedSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  completedMask S D I J * summand Ψ W X I J

def correctedSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  completedCorrection I J * markedSummand S D Ψ W X I J

def markedCompletedT (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Ideal O × Ideal O, markedSummand S D Ψ W X p.1 p.2

def correctedCompletedT (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Ideal O × Ideal O, correctedSummand S D Ψ W X p.1 p.2

def correctionCoeff (χ : RayCharacter) : ℂ :=
  phaseCoeff (fun r => star (fixedGQuotientValue r)) χ

theorem correctionCoeff_sum_norm_le :
    (∑ χ : RayCharacter, ‖correctionCoeff χ‖) ≤ 32 := by
  have h := phaseCoeff_sum_norm_le (fun r => star (fixedGQuotientValue r)) 2
    (fun u => by simpa only [norm_star] using fixedGQuotientValue_norm_le_two (u : RayRing))
  simpa only [correctionCoeff] using h.trans_eq (by norm_num : (16 : ℝ) * 2 = 32)

theorem completedIndex_eq_primaryGenerator (I J : Ideal O) :
    completedIndex I J = primaryGenerator (I * J ^ 3) := by
  simp only [completedIndex, primaryGenerator_mul, CubicEisenstein.primaryGenerator_pow]

theorem completedMask_zero_of_excluded (S : Finset (Ideal O)) (D I J p : Ideal O)
    (hp : p ∈ S) (hpdiv : p ∣ I * J ^ 3) : completedMask S D I J = 0 := by
  unfold completedMask
  rw [ite_eq_right]
  intro h
  exact h.2 p hp hpdiv

theorem completedMask_zero_of_not_marked (S : Finset (Ideal O)) (D I J : Ideal O)
    (hD : ¬D ∣ I * J ^ 3) : completedMask S D I J = 0 := by
  simp [completedMask, hD]

theorem completedCorrection_expansion (I J : Ideal O) :
    completedCorrection I J =
      ∑ χ : RayCharacter, correctionCoeff χ * rayCharacter χ (completedIndex I J) := by
  exact phase_expansion (fun r => star (fixedGQuotientValue r)) (completedIndex I J)

theorem correctedSummand_ray_expansion (S : Finset (Ideal O)) (D I J : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    correctedSummand S D Ψ W X I J =
      ∑ χ : RayCharacter, correctionCoeff χ *
        markedSummand S D (rayMonoid χ * Ψ) W X I J := by
  unfold correctedSummand
  rw [completedCorrection_expansion, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ _
  unfold markedSummand
  rw [CanonicalRowCompletion.summand_mul_fixed_twist]
  simp only [rayMonoid_apply, completedIndex]
  ring

theorem markedSummand_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => markedSummand S D Ψ W X p.1 p.2) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp
  exact fun hz => hp (by simp only [markedSummand, hz, mul_zero])

theorem correctedSummand_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => correctedSummand S D Ψ W X p.1 p.2) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp
  exact fun hz => hp (by simp only [correctedSummand, markedSummand, hz, mul_zero])

theorem correctedCompletedT_ray_expansion (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    correctedCompletedT S D Ψ W X =
      ∑ χ : RayCharacter, correctionCoeff χ *
        markedCompletedT S D (rayMonoid χ * Ψ) W X := by
  unfold correctedCompletedT
  simp_rw [correctedSummand_ray_expansion]
  rw [Summable.tsum_finsetSum (fun χ _ =>
    (markedSummand_summable S D (rayMonoid χ * Ψ) W hW X hX).mul_left (correctionCoeff χ))]
  simp only [tsum_mul_left, markedCompletedT]

theorem correctedCompletedT_norm_le (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ χ : RayCharacter, ‖markedCompletedT S D (rayMonoid χ * Ψ) W X‖ ≤ B) :
    ‖correctedCompletedT S D Ψ W X‖ ≤ 32 * B := by
  rw [correctedCompletedT_ray_expansion S D Ψ W hW X hX]
  calc
    _ ≤ ∑ χ : RayCharacter, ‖correctionCoeff χ *
        markedCompletedT S D (rayMonoid χ * Ψ) W X‖ := norm_sum_le _ _
    _ ≤ ∑ χ : RayCharacter, ‖correctionCoeff χ‖ * B := by
      apply Finset.sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound χ) (norm_nonneg _)
    _ = (∑ χ : RayCharacter, ‖correctionCoeff χ‖) * B := (Finset.sum_mul ..).symm
    _ ≤ 32 * B := mul_le_mul_of_nonneg_right correctionCoeff_sum_norm_le hB

end SevenEighths.ProbeCompleted
end

end OAI

end Source317

/- Original source: OAI/NumberTheory/DirichletL/Detector/Row.lean; sha256: 94cd0a68ced17d2ad52c67c13af03a3d199568862ebe43fde2f9f0ed96949ce0 -/
section Source318
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve InitialMeanSquare ProbeCompleted

local notation "O" => ActualEisensteinCubic.O

def targetMonoid (η : HeckeFamily.Character) : O →* ℂ where
  toFun := HeckeFamily.elementCoeff η
  map_one' := HeckeFamily.elementCoeff_one η
  map_mul' := HeckeFamily.elementCoeff_mul η

theorem targetMonoid_norm_le_one (η : HeckeFamily.Character) (a : O) :
    ‖targetMonoid η a‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue (Ideal.Quotient.mk η.modulus a)

def rowCoefficient (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m : O) : O →* ℂ :=
  targetMonoid η * conjugateMonoid Xi * reciprocityPhaseMonoid s hs *
    (idealRowHom m).toMonoidHom.comp principalIdealHom.toMonoidHom

theorem rowCoefficient_apply (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O) :
    rowCoefficient η Xi s hs m a = HeckeFamily.elementCoeff η a * star (Xi a) *
      sexticReciprocityPhase s a * idealRowHom m (Ideal.span {a}) := rfl

theorem rowCoefficient_apply_unit (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O) (hXi : ‖Xi a‖ = 1) :
    rowCoefficient η Xi s hs m a = HeckeFamily.elementCoeff η a * (Xi a)⁻¹ *
      sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) := by
  rw [rowCoefficient_apply]
  have hc : star (Xi a) = (Xi a)⁻¹ := (Complex.inv_eq_conj hXi).symm
  have hsym : sexticReciprocityPhase s a = sexticReciprocityPhase a s := by
    simp only [sexticReciprocityPhase, QuadraticAllOddCRT.quadraticRaySign_symm]
  rw [hc, hsym]

theorem rowCoefficient_norm_le_one (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (hXi : ∀ a, ‖Xi a‖ ≤ 1) (s : O) (hs : Supported (Ideal.span {s})) (m a : O) :
    ‖rowCoefficient η Xi s hs m a‖ ≤ 1 := by
  rw [rowCoefficient_apply]
  simp only [norm_mul, norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (idealRowHom_norm _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (sexticReciprocityPhase_norm _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)).trans (hXi a)

def spectralSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (t : ℂ) (I J : Ideal O) : ℂ :=
  (completedMask S D I J * completedCorrection I J *
    (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I) : ℂ)) * cubeWeight Ψ J) *
      (CubicEisenstein.fullIdealWeight t I * CubicEisenstein.fullIdealWeight (3 * t) J)

def spectralRow (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ) (t : ℂ) : ℂ :=
  ∑' p : Ideal O × Ideal O, spectralSummand S D Ψ t p.1 p.2

theorem spectralSummand_norm_le (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (t : ℂ) (I J : Ideal O) :
    ‖spectralSummand S D Ψ t I J‖ ≤
      2 * (‖CubicEisenstein.fullIdealWeight t I‖ *
        ‖CubicEisenstein.fullIdealWeight (3 * t) J‖) := by
  have hmc : ‖completedMask S D I J * completedCorrection I J‖ ≤ 2 := by
    rw [norm_mul]
    exact (mul_le_mul (completedMask_norm_le_one S D I J)
      (completedCorrection_norm_le_two I J) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hcol := columnWeight_div_sqrt_norm_le_one Ψ hΨ I
  have hcube := cubeWeight_norm_le_one Ψ hΨ J
  have hc : ‖completedMask S D I J * completedCorrection I J *
      (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I) : ℂ)) * cubeWeight Ψ J‖ ≤ 2 := by
    rw [norm_mul, norm_mul]
    exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hcube).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hcol).trans hmc)
  unfold spectralSummand
  simpa only [norm_mul] using mul_le_mul_of_nonneg_right hc (mul_nonneg
    (norm_nonneg (CubicEisenstein.fullIdealWeight t I))
    (norm_nonneg (CubicEisenstein.fullIdealWeight (3 * t) J)))

theorem spectralRow_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (t : ℂ) (ht : 1 < t.re) :
    Summable (fun p : Ideal O × Ideal O => spectralSummand S D Ψ t p.1 p.2) := by
  have ht3 : 1 < (3 * t).re := by
    norm_num [Complex.mul_re]
    linarith
  have h1 := CubicEisenstein.fullIdealWeight_summable_norm t ht
  have h3 := CubicEisenstein.fullIdealWeight_summable_norm (3 * t) ht3
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => spectralSummand_norm_le S D Ψ hΨ t p.1 p.2)
    ((h1.mul_of_nonneg h3 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left 2)

end SevenEighths.ProbeRow
end

end OAI

end Source318

/- Original source: OAI/NumberTheory/DirichletL/Detector/Compensation.lean; sha256: db4b2b2ca1c5cfc9d23fefb08b30e1411891d1007462492211abb4140e4a71d2 -/
section Source319
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeCompensation

def tupleOperation {α : Type*} [CommMonoid α] {K : ℕ}
    (p : Fin K → α) (q : α → ℝ) (η : α → ℂ)
    (F : α → ℝ → ℝ → ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  ∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
    (-1 : ℂ) ^ J.card * ((q (∏ i ∈ J, p i) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      star (η (∏ i ∈ Finset.univ \ J, p i)) *
      F (∏ i ∈ Finset.univ \ J, p i)
        (X / q (∏ i ∈ J, p i)) (Y / q (∏ i ∈ J, p i))
        (Z * q (∏ i ∈ Finset.univ \ J, p i))

theorem tupleOperation_zero {α : Type*} [CommMonoid α]
    (p : Fin 0 → α) (q : α → ℝ) (η : α → ℂ)
    (hq : q 1 = 1) (hη : η 1 = 1)
    (F : α → ℝ → ℝ → ℝ → ℂ) (X Y Z : ℝ) :
    tupleOperation p q η F X Y Z = F 1 X Y Z := by
  simp [tupleOperation, hq, hη]

theorem tupleOperation_one {α : Type*} [CommMonoid α]
    (p : Fin 1 → α) (q : α → ℝ) (η : α → ℂ)
    (hq : q 1 = 1) (hη : η 1 = 1)
    (F : α → ℝ → ℝ → ℝ → ℂ) (X Y Z : ℝ) :
    tupleOperation p q η F X Y Z =
      star (η (p 0)) * F (p 0) X Y (Z * q (p 0)) -
      ((q (p 0) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * F 1 (X / q (p 0)) (Y / q (p 0)) Z := by
  have hp : (Finset.univ : Finset (Fin 1)).powerset = {∅, {0}} := by decide
  simp only [tupleOperation, hp]
  simp [hq, hη]
  ring

end SevenEighths.ProbeCompensation
end

end OAI

end Source319
