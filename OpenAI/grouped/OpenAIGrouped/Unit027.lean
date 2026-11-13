import OpenAIGrouped.Unit026
import OpenAIGrouped.Unit012
import OpenAIGrouped.Unit008
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit021
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import OpenAIGrouped.Unit013

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalCoefficientScaling.lean; sha256: a30f9eda13fa221ba38775b389c7925951aefafb772a569c5243bff5d9bb6529 -/
section Source1080
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem physical_spectral_coefficient_scale (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : CalibrationData) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime C.generator (completedIndex I J)) (X : ℝ) (hX : 0<X) (t : ℂ) (H : O) :
    let A := completedIndex I J
    let hA := supportedElement_ne_zero A (supported_completed _ _
      ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*A):ℝ):ℂ)*actualCongruenceCoefficient C A s hA H =
    (Real.sqrt X:ℂ) * completedMask S D I J *
      calibratedHighCoefficient C η I (supported_primaryGenerator_ne_zero I hI) A s hA H /
      ((elementNorm A:ℂ)*(Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)) *
      (fullIdealWeight t I*fullIdealWeight (3*t) J) := by
  dsimp only
  have hA := supportedElement_ne_zero (completedIndex I J) (supported_completed _ _
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
  have he := physical_poisson_prefactor (elementNorm C.generator) (elementNorm (completedIndex I J))
    (elementNorm s) X (elementNorm_pos _ C.generator_ne_zero) (elementNorm_pos _ hA)
    (elementNorm_pos _ (supportedElement_ne_zero s hs)) hX
  rw [spectralSummand_source_coefficient S D I J η C s hs hI hJ hsf hcop t]
  simp only [elementNorm_mul,Complex.ofReal_div,Complex.ofReal_mul] at he ⊢
  unfold calibratedHighCoefficient
  have hh := congrArg (fun v : ℂ=>v*
    (idealRowHom C.generator (Ideal.span {s})/(C.tau*C.residueMonoid s))*
    (completedMask S D I J *
      (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
        star (FiniteGaussPhase.angularFactor (completedIndex I J)*ProbePhase.G (completedIndex I J))*
        targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*
        ProbePhase.reciprocitySign (completedIndex I J) s)/
      ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)))*
    (fullIdealWeight t I*fullIdealWeight (3*t) J)*
    actualCongruenceCoefficient C (completedIndex I J) s hA H) he
  convert hh using 1 <;> ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1080

/- Original source: OAI/NumberTheory/DirichletL/Detector/MellinPowers.lean; sha256: bd852004a4eba595d9ffcaa5363d1b4dcb5c69bd77b48f33538b56f6815903fa -/
section Source1081
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ProbeEuler

lemma sourceNormPower_identity (I J H X : ℝ) (hI : 0<I) (hJ : 0<J) (hH : 0<H) (hX : 0<X)
    (t z : ℂ) :
    ((I*J^3:ℝ):ℂ)⁻¹*((X*H/(I*J^3):ℝ):ℂ)^(-z)*
      ((I:ℂ)^(-t)*(J:ℂ)^(-3*t)) /
      ((Real.sqrt I:ℂ)*(J:ℂ)) * (Real.sqrt X:ℂ) =
      (X:ℂ)^(1/2-z)*(H:ℂ)^(-z)*
        (I:ℂ)^(-(t+1-z)-1/2)*(J:ℂ)^(-(1+3*(t+1-z))) := by
  have hi : (I:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hI.ne'
  have hj : (J:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hJ.ne'
  have hh : (H:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hH.ne'
  have hx : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  rw [←cpow_half_eq_sqrt I hI.le,←cpow_half_eq_sqrt X hX.le]
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (mul_pos hX hH).le (mul_pos hI (pow_pos hJ 3)).le]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  rw [Complex.mul_cpow_ofReal_nonneg hX.le hH.le]
  have hmul : ((I:ℂ)*(J:ℂ)^3)^(-z)=(I:ℂ)^(-z)*((J:ℂ)^3)^(-z) := by
    simpa only [Complex.ofReal_pow] using Complex.mul_cpow_ofReal_nonneg hI.le (pow_pos hJ 3).le (-z)
  rw [hmul]
  have hp : ((J:ℂ)^3)^(-z)=(J:ℂ)^((3:ℂ)*(-z)) := by
    simpa only [Real.rpow_ofNat,Real.rpow_natCast,Complex.ofReal_pow,Complex.cpow_ofNat,Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg hJ.le (3:ℝ) (-z)).symm
  rw [hp]
  rw [show (J:ℂ)^3=(J:ℂ)^(3:ℂ) by simp]
  have hir : (I:ℂ)=Complex.exp (Complex.log (I:ℂ)) := (Complex.exp_log hi).symm
  have hjr : (J:ℂ)=Complex.exp (Complex.log (J:ℂ)) := (Complex.exp_log hj).symm
  simp only [Complex.cpow_def_of_ne_zero hi,Complex.cpow_def_of_ne_zero hj,
    Complex.cpow_def_of_ne_zero hh,Complex.cpow_def_of_ne_zero hx,div_eq_mul_inv,
    mul_inv_rev,←Complex.exp_neg,←Complex.exp_add]
  rw [hir,hjr]
  simp only [←Complex.exp_neg,←Complex.exp_add]
  rw [Complex.exp_log hi,Complex.exp_log hj]
  congr 1
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1081

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalMellinCoefficient.lean; sha256: 60fb71f6f6d55ef930eafcd18cacdb6889d3bbc58c2c04d6e0d23b4fa1bef4ad -/
section Source1082
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma completedIndex_norm (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    elementNorm (completedIndex I J)=(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  rw [completedIndex, elementNorm_mul, elementNorm_pow]
  unfold elementNorm
  rw [(primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1,
    (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J hJ)).1]

theorem physical_mellin_coefficient (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (D I J : Ideal O) (η : HeckeFamily.Character) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime (calibrationForSet S hS).generator (completedIndex I J*s))
    (X : ℝ) (hX : 0<X) (H : O) (hH : H≠0) (t z : ℂ) :
    let C := calibrationForSet S hS
    let A := completedIndex I J
    let hA := supportedElement_ne_zero A (supported_completed _ _
      ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*A):ℝ):ℂ)*actualCongruenceCoefficient C A s hA H *
      ((K*elementNorm H/elementNorm ((C.generator*A)*s)):ℂ)^(-z) =
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*completedMask S D I J*star (C.residueMonoid H)*
      bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I hI) A s hA H *
      (fullIdealWeight (t+1-z+1/2) I*fullIdealWeight (1+3*(t+1-z)) J) := by
  dsimp only
  have hA : Supported (Ideal.span {completedIndex I J}) := supported_completed _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ)
  rw [physical_spectral_coefficient_scale S D I J η (calibrationForSet S hS) s hs hI hJ hsf
    hcop.of_mul_right_left X hX t H]
  rw [calibratedHighCoefficient_eq_bare S hS η I (supported_primaryGenerator_ne_zero I hI)
    (completedIndex I J) s hA hs hcop H]
  have hr := congrArg (fun r : ℝ => (r : ℂ)) (physical_radial_argument
    (calibrationForSet S hS).generator (completedIndex I J) s H X
    (elementNorm_pos _ (calibrationForSet S hS).generator_ne_zero).ne'
    (elementNorm_pos _ (supportedElement_ne_zero s hs)).ne')
  simp only [Complex.ofReal_div, Complex.ofReal_mul] at hr
  simp only [Complex.ofReal_mul]
  rw [hr]
  rw [completedIndex_norm I J hI hJ]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ.1)
  have hn := sourceNormPower_identity (Ideal.absNorm I) (Ideal.absNorm J) (elementNorm H) X
    hi hj (elementNorm_pos H hH) hX t z
  rw [show -(t+1-z)-1/2= -(t+1-z+1/2) by ring] at hn
  simp only [fullIdealWeight,hI.1,hJ.1,ite_false,Complex.ofReal_natCast,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow] at hn ⊢
  have he := congrArg (fun v : ℂ=>v*completedMask S D I J*
    star ((calibrationForSet S hS).residueMonoid H)*
    bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I hI) (completedIndex I J) s
      (supportedElement_ne_zero _ hA) H) hn
  convert he using 1 <;> ring_nf

end SevenEighths.ProbePhysical
end

end OAI

end Source1082

/- Original source: OAI/NumberTheory/DirichletL/Detector/SpectralPoisson.lean; sha256: 51cade1ad1cece39d3e1eb3bdbe0c7624bf27195d3a07529a9a3fab333147404 -/
section Source1083
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def transformedSpectralTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (K : ℝ) (t : ℂ) (I J : Ideal O) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
        ∑' H : O, actualCongruenceCoefficient C (completedIndex I J) s hA H *
          paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*completedIndex I J)*s))
  else 0

theorem physical_spectral_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K : ℝ) (hK : 0<K) (t : ℂ) (ht : 1<t.re) :
    (∑' m : O, C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) *
      W (elementNorm m/K) * spectralRow S D (rowCoefficient η C.Xi s hs m) t) =
    ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C S D s hs W K t p.1 p.2 := by
  rw [physical_spectral_reopen η C S D s hs W hWc K hK t ht]
  apply tsum_congr
  intro p
  unfold transformedSpectralTerm
  by_cases hA : completedIndex p.1 p.2≠0
  · rw [dite_eq_left hA, physical_row_poisson C (completedIndex p.1 p.2) s hA
      (supportedElement_ne_zero s hs) W hWc hWs K hK]
    ring
  · rw [dite_eq_right hA, spectralSummand_zero_completedIndex S D p.1 p.2 _ t (not_ne_iff.mp hA), zero_mul]

end SevenEighths.ProbePhysical
end

end OAI

end Source1083

/- Original source: OAI/NumberTheory/DirichletL/Detector/RadialSpectral.lean; sha256: f5ee7a76bdb3d0a9208ff86c785cd3671dcb342ddd0fc8f7da4358f796072332 -/
section Source1084
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma spectralSummand_mask_nonzero (S : Finset Id) (D I J : Id) (Ψ : O→*ℂ) (t : ℂ)
    (h : spectralSummand S D Ψ t I J≠0) : completedMask S D I J≠0 := by
  intro hz
  exact h (by simp only [spectralSummand,hz,zero_mul])

lemma spectralSummand_calibration_coprime (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D I J : Id) (Ψ : O→*ℂ) (t : ℂ) (h : spectralSummand S D Ψ t I J≠0) :
    IsCoprime (calibrationForSet S hS).generator (completedIndex I J) := by
  have hm := spectralSummand_mask_nonzero S D I J Ψ t h
  have hA : completedIndex I J≠0 := by
    intro hz
    exact h (spectralSummand_zero_completedIndex S D I J Ψ t hz)
  have hout : ∀P∈S,¬P∣I*J^3 := by
    unfold completedMask at hm
    split_ifs at hm with hd
    · exact hd.2
    · exact False.elim (hm rfl)
  apply calibrationForSet_coprime_of_excluded S hS
  rw [completedIndex_eq_primaryGenerator] at hA ⊢
  rw [(primaryGenerator_spec (I*J^3) hA).1]
  exact hout

def radialMellinSpectralTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset Id) (D : Id) (s : O) (hs : Supported (Ideal.span {s}))
    (W : SchwartzMap ℝ ℂ) (K σ : ℝ) (t : ℂ) (I J : Id) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C (completedIndex I J) s hA H.val*
          ((K*elementNorm H.val/elementNorm ((C.generator*completedIndex I J)*s)):ℂ)^(-z)*
            mellin (paperRadialFourier W) z)
  else 0

theorem transformedSpectralTerm_radial_mellin (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty) (D : Id)
    (s : O) (hs : Supported (Ideal.span {s})) (hcs : IsCoprime (calibrationForSet S hS).generator s)
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W⊆Set.Icc a b)
    (K σ : ℝ) (hK : 0<K) (hσ : 1<σ) (t : ℂ) (I J : Id) :
    transformedSpectralTerm η (calibrationForSet S hS) S D s hs W K t I J=
      radialMellinSpectralTerm η (calibrationForSet S hS) S D s hs W K σ t I J := by
  unfold transformedSpectralTerm radialMellinSpectralTerm
  split_ifs with hA
  · by_cases hz : spectralSummand S D (baseRowCoefficient η (calibrationForSet S hS).Xi s hs) t I J=0
    · simp only [hz,zero_mul]
    · rw [actualFrequency_mellin S hS hSne (completedIndex I J) s hA (supportedElement_ne_zero s hs)
        ((spectralSummand_calibration_coprime S hS D I J _ t hz).mul_right hcs)
        W a b ha hW K hK σ hσ]
  · rfl

end SevenEighths.ProbePhysical
end

end OAI

end Source1084

/- Original source: OAI/NumberTheory/DirichletL/Detector/SpectralSupport.lean; sha256: 50d90d7dd10d083f05af694cbf365fab833b6e51ab2632e948ca51ef6f5e81f7 -/
section Source1085
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ProbeCompleted ProbeRow SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

lemma supported_of_source_exclusions (S : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆S) (I : Ideal O) (hI : I≠0)
    (hS : ∀P∈S,¬P∣I) : Supported I := by
  refine ⟨hI,?_⟩
  intro P hP
  have hp : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply (prime_good_iff_not_bad P).mpr
  intro hb
  exact hS P (hbad hb) (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)

lemma spectralSummand_support (S : Finset (Ideal O)) (hbad : fixedBadPrimes⊆S)
    (D I J : Ideal O) (Ψ : O→*ℂ) (t : ℂ)
    (h : spectralSummand S D Ψ t I J≠0) :
    Squarefree I ∧ Supported I ∧ Supported J := by
  have hI : I≠0 := by
    intro hz
    subst I
    exact h (by simp [spectralSummand])
  have hJ : J≠0 := by
    intro hz
    subst J
    exact h (by simp [spectralSummand])
  have hsf : Squarefree I := by
    by_contra hn
    exact h (by simp [spectralSummand,columnWeight,squarefreeGaussCoefficient,hn])
  have hm := spectralSummand_mask_nonzero S D I J Ψ t h
  have hex : ∀P∈S,¬P∣I*J^3 := by
    unfold completedMask at hm
    split_ifs at hm with hd
    · exact hd.2
    · exact False.elim (hm rfl)
  refine ⟨hsf,supported_of_source_exclusions S hbad I hI ?_,
    supported_of_source_exclusions S hbad J hJ ?_⟩
  · intro P hP hd
    exact hex P hP (dvd_mul_of_dvd_left hd _)
  · intro P hP hd
    exact hex P hP (dvd_mul_of_dvd_right (hd.trans (dvd_pow_self J (by decide : 3≠0))) _)

end SevenEighths.ProbePhysical
end

end OAI

end Source1085

/- Original source: OAI/NumberTheory/DirichletL/Detector/MellinGuarded.lean; sha256: cf2dd37a6a13766af08d4f0d0bbee03183f7f99cf40e5c75aea5a5bb2c0723bb -/
section Source1086
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def physicalMellinCoefficientTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (X : ℝ) (H : O) (t z : ℂ) : ℂ :=
  if hA : completedIndex I J≠0 then
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ)*
      actualCongruenceCoefficient C (completedIndex I J) s hA H *
      ((K*elementNorm H/elementNorm ((C.generator*completedIndex I J)*s)):ℂ)^(-z)
  else 0

def guardedHighMellinCoefficient (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J : Ideal O) (s : O) (X : ℝ) (H : O) (x z : ℂ) : ℂ :=
  if h : Squarefree I ∧ Supported I ∧ Supported J then
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*completedMask S D I J*star (C.residueMonoid H)*
      bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I h.2.1)
        (completedIndex I J) s (supportedElement_ne_zero _ (supported_completed _ _
          ((supported_span_primaryGenerator_iff I).mpr h.2.1)
          ((supported_span_primaryGenerator_iff J).mpr h.2.2))) H *
      (fullIdealWeight (x+1/2) I*fullIdealWeight (1+3*x) J)
  else 0

theorem physicalMellinCoefficientTerm_eq_guarded (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (D I J : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (hcs : IsCoprime (calibrationForSet S hS).generator s)
    (X : ℝ) (hX : 0<X) (H : O) (hH : H≠0) (t z : ℂ) :
    physicalMellinCoefficientTerm η (calibrationForSet S hS) S D I J s hs X H t z=
      guardedHighMellinCoefficient η (calibrationForSet S hS) S D I J s X H (t+1-z) z := by
  by_cases hg : Squarefree I ∧ Supported I ∧ Supported J
  · have hA : completedIndex I J≠0 := supportedElement_ne_zero _ (supported_completed _ _
      ((supported_span_primaryGenerator_iff I).mpr hg.2.1)
      ((supported_span_primaryGenerator_iff J).mpr hg.2.2))
    rw [physicalMellinCoefficientTerm,dite_eq_left hA,guardedHighMellinCoefficient,dite_eq_left hg]
    dsimp only
    by_cases hm : completedMask S D I J=0
    · simp only [spectralSummand,hm,zero_mul,mul_zero]
    · have hc : IsCoprime (calibrationForSet S hS).generator (completedIndex I J) := by
        apply calibrationForSet_coprime_of_excluded S hS
        rw [completedIndex_eq_primaryGenerator] at hA ⊢
        rw [(primaryGenerator_spec (I*J^3) hA).1]
        unfold completedMask at hm
        split_ifs at hm with hd
        · exact hd.2
        · exact False.elim (hm rfl)
      exact physical_mellin_coefficient S hS D I J η s hs hg.2.1 hg.2.2 hg.1
        (hc.mul_right hcs) X hX H hH t z
  · have hz : spectralSummand S D (baseRowCoefficient η (calibrationForSet S hS).Xi s hs) t I J=0 := by
      by_contra hn
      exact hg (spectralSummand_support S hbad D I J _ t hn)
    rw [guardedHighMellinCoefficient,dite_eq_right hg]
    unfold physicalMellinCoefficientTerm
    split_ifs <;> simp only [hz,mul_zero,zero_mul]

theorem guardedHighMellinCoefficient_eq_high (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (D I J K : Ideal O)
    (hK : Supported K) (hKS : ∀P∈S,¬P∣K) (X : ℝ) (H : O) (x w z : ℂ) :
    guardedHighMellinCoefficient η C S D I J (primaryGenerator K) X H x z *
      fullIdealWeight w K =
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*star (C.residueMonoid H)*
      markedIdealHighSummand S D η H x w z I J K 1 := by
  have h1 : ∀P∈S,¬P∣(1:Ideal O) := by
    intro P hP hd
    exact (hS P hP).not_isUnit (isUnit_of_dvd_one hd)
  have hw : fullIdealWeight (6*z) (1:Ideal O)=1 := (IdealEuler.normWeight (6*z)).map_one
  unfold guardedHighMellinCoefficient markedIdealHighSummand highIdealMask
    bareIdealHighSummand bareIdealHighCoefficient
  simp only [ite_eq_left hKS,ite_eq_left h1,mul_one,hw,primaryGenerator_one,one_pow]
  by_cases hg : Squarefree I ∧ Supported I ∧ Supported J
  · have hfull : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O) :=
      ⟨hg.1,hg.2.1,hg.2.2,hK,supported_one_ideal⟩
    rw [dite_eq_left hg,dite_eq_left hfull]
    dsimp only [completedIndex]
    ring
  · have hfull : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O)) :=
      fun h=>hg ⟨h.1,h.2.1,h.2.2.1⟩
    rw [dite_eq_right hg,dite_eq_right hfull]
    simp only [mul_zero,zero_mul]

end SevenEighths.ProbePhysical
end

end OAI

end Source1086

/- Original source: OAI/NumberTheory/DirichletL/ContinuationInversion.lean; sha256: 166139695fcd8753df43d21f7e0b3a5a0ffc774bd75d0535fb4d0b33757170d8 -/
section Source1087
namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform
namespace SevenEighths.Continuation

theorem integrable_logProfile {f : ℝ → ℂ} {σ : ℝ}
    (hf : MellinConvergent f (σ : ℂ)) :
    Integrable (fun u : ℝ => Real.exp (-σ * u) • f (Real.exp (-u))) := by
  have hder : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
    fun x _ => mul_neg_one (Real.exp (-x)) ▸
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt
  have himage : Real.exp ∘ Neg.neg '' (univ : Set ℝ) = Ioi 0 := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
      Set.image_univ, Real.range_exp]
  have hinj : univ.InjOn (Real.exp ∘ Neg.neg) :=
    Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)
  rw [MellinConvergent, ← himage,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hder hinj] at hf
  have heq (u : ℝ) :
      |-(Real.exp (-u))| • ((Real.exp (-u) : ℂ) ^ ((σ : ℂ) - 1) • f (Real.exp (-u))) =
        Real.exp (-σ * u) • f (Real.exp (-u)) := by
    rw [abs_neg, abs_of_pos (Real.exp_pos _)]
    change (Real.exp (-u) : ℂ) *
      ((Real.exp (-u) : ℂ) ^ ((σ : ℂ) - 1) * f (Real.exp (-u))) =
        (Real.exp (-σ * u) : ℂ) * f (Real.exp (-u))
    rw [← mul_assoc]
    congr 1
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (Real.exp_pos (-u)).le]
    norm_cast
    rw [Real.rpow_def_of_pos (Real.exp_pos (-u)), Real.log_exp, ← Real.exp_add]
    congr 1
    ring
  simpa only [Function.comp_apply, integrableOn_univ, heq] using hf

theorem mellin_mellinInv_eq (σ : ℝ) (F : ℂ → ℂ) (f : ℝ → ℂ)
    (hf : MellinConvergent f (σ : ℂ))
    (hF : Integrable (fun y : ℝ => F ((σ : ℂ) + 2 * Real.pi * y * Complex.I)))
    (hcont : Continuous (fun y : ℝ => F ((σ : ℂ) + 2 * Real.pi * y * Complex.I)))
    (hrep : ∀ x : ℝ, 0 < x → f x = mellinInv σ F x) (y : ℝ) :
    mellin f ((σ : ℂ) + 2 * Real.pi * y * Complex.I) =
      F ((σ : ℂ) + 2 * Real.pi * y * Complex.I) := by
  let A : ℝ → ℂ := fun y => F ((σ : ℂ) + 2 * Real.pi * y * Complex.I)
  let g : ℝ → ℂ := fun u => Real.exp (-σ * u) • f (Real.exp (-u))
  have hg : Integrable g := integrable_logProfile hf
  have hginv : g = 𝓕⁻ A := by
    funext u
    dsimp [g]
    rw [hrep _ (Real.exp_pos _), mellinInv_eq_fourierInv _ _ (Real.exp_pos _)]
    simp only [Real.log_exp, neg_neg]
    change (Real.exp (-σ * u) : ℂ) *
      ((Real.exp (-u) : ℂ) ^ (-(σ : ℂ)) * 𝓕⁻ A u) = 𝓕⁻ A u
    rw [← mul_assoc, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow (Real.exp_pos (-u)).le]
    have hc : Real.exp (-σ * u) * Real.exp (-u) ^ (-σ) = 1 := by
      rw [Real.rpow_def_of_pos (Real.exp_pos (-u)), Real.log_exp, ← Real.exp_add]
      rw [show -σ * u + -u * -σ = 0 by ring, Real.exp_zero]
    rw [← Complex.ofReal_mul, hc, Complex.ofReal_one, one_mul]
  have hfourier : Integrable (𝓕 A) := by
    have hn := hg.comp_neg
    rw [hginv] at hn
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hn
  rw [mellin_eq_fourier]
  have hre : ((σ : ℂ) + 2 * Real.pi * y * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + 2 * Real.pi * y * Complex.I).im / (2 * Real.pi) = y := by
    simp
  rw [hre, him]
  change 𝓕 g y = A y
  rw [hginv]
  exact hF.fourier_fourierInv_eq hfourier hcont.continuousAt

def normalizedSignal (f : ℝ → ℂ) (c : ℝ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-(c : ℂ)) • f x

theorem mellin_normalizedSignal (f : ℝ → ℂ) (c : ℝ) (s : ℂ) :
    mellin (normalizedSignal f c) (-s) = signalMellin f c s := by
  unfold normalizedSignal signalMellin
  rw [mellin_cpow_smul]
  congr 1
  ring

theorem signalMellin_eq_on_line (f : ℝ → ℂ) (A : ℂ → ℂ) (c d : ℝ)
    (hf : MellinConvergent f (-((d : ℂ) + (c : ℂ))))
    (hA : Integrable (fun y : ℝ => A ((d : ℂ) - 2 * Real.pi * y * Complex.I)))
    (hcont : Continuous (fun y : ℝ => A ((d : ℂ) - 2 * Real.pi * y * Complex.I)))
    (hrep : ∀ x : ℝ, 0 < x → normalizedSignal f c x =
      mellinInv (-d) (fun s => A (-s)) x) (y : ℝ) :
    signalMellin f c ((d : ℂ) - 2 * Real.pi * y * Complex.I) =
      A ((d : ℂ) - 2 * Real.pi * y * Complex.I) := by
  have hf' : MellinConvergent (normalizedSignal f c) ((-d : ℝ) : ℂ) := by
    unfold normalizedSignal
    apply MellinConvergent.cpow_smul.mpr
    convert hf using 1; push_cast; ring
  have harg (y : ℝ) : -(((-d : ℝ) : ℂ) + 2 * Real.pi * y * Complex.I) =
      (d : ℂ) - 2 * Real.pi * y * Complex.I := by push_cast; ring
  have hA' : Integrable
      (fun y : ℝ => A (-(((-d : ℝ) : ℂ) + 2 * Real.pi * y * Complex.I))) := by
    simpa only [harg] using hA
  have hcont' : Continuous
      (fun y : ℝ => A (-(((-d : ℝ) : ℂ) + 2 * Real.pi * y * Complex.I))) := by
    simpa only [harg] using hcont
  have hid := mellin_mellinInv_eq (-d) (fun s => A (-s))
    (normalizedSignal f c) hf' hA' hcont' hrep y
  rw [harg] at hid
  rw [← mellin_normalizedSignal]
  convert hid using 1; congr 1; push_cast; ring

end SevenEighths.Continuation

end

end OAI

end Source1087

/- Original source: OAI/NumberTheory/DirichletL/ContinuationContour.lean; sha256: 3c29ca9681de5e41e20b9b8ada0a90b033efc4c4ce02583d32b89c0a33d81aac -/
section Source1088
namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
namespace SevenEighths.Continuation

theorem vertical_integral_eq_of_horizontal_vanish (F : ℂ → ℂ) {a b : ℝ}
    (hab : a ≤ b) (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (ha : Integrable (fun y : ℝ => F ((a : ℂ) + y * I)))
    (hb : Integrable (fun y : ℝ => F ((b : ℂ) + y * I)))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + (-T) * I))
      atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + T * I))
      atTop (𝓝 0)) :
    (∫ y : ℝ, F ((a : ℂ) + y * I)) = ∫ y : ℝ, F ((b : ℂ) + y * I) := by
  have hrect (T : ℝ) :
      (∫ x : ℝ in a..b, F ((x : ℂ) + (-T) * I)) -
      (∫ x : ℝ in a..b, F ((x : ℂ) + T * I)) +
      I * (∫ y : ℝ in -T..T, F ((b : ℂ) + y * I)) -
      I * (∫ y : ℝ in -T..T, F ((a : ℂ) + y * I)) = 0 := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn F
      ((a : ℂ) + (-T) * I) ((b : ℂ) + T * I) (hhol.mono ?_)
    · simpa [smul_eq_mul] using h
    · intro z hz
      have hzre := hz.1
      simpa [uIcc_of_le hab] using hzre
  have hlim := ((hbot.sub htop).add
    ((intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id).const_mul I)).sub
    ((intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id).const_mul I)
  have hzero : (0 : ℂ) - 0 + I * (∫ y : ℝ, F ((b : ℂ) + y * I)) -
      I * (∫ y : ℝ, F ((a : ℂ) + y * I)) = 0 :=
    tendsto_nhds_unique hlim (by simpa only [id_eq, hrect] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0)))
  have heq : I * (∫ y : ℝ, F ((b : ℂ) + y * I)) =
      I * (∫ y : ℝ, F ((a : ℂ) + y * I)) := by simpa using sub_eq_zero.mp hzero
  exact (mul_left_cancel₀ I_ne_zero heq).symm

theorem horizontal_integral_tendsto_zero (F : ℂ → ℂ) (a b C : ℝ)
    (hbound : ∀ x ∈ Set.uIcc a b, ∀ y : ℝ,
      ‖F ((x : ℂ) + y * I)‖ ≤ C * Real.exp (-(y ^ 2))) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + T * I)) atTop (𝓝 0) := by
  have hnorm (T : ℝ) : ‖∫ x : ℝ in a..b, F ((x : ℂ) + T * I)‖ ≤
      C * Real.exp (-(T ^ 2)) * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => hbound x (uIoc_subset_uIcc hx) T)
  have hexp : Tendsto (fun T : ℝ => Real.exp (-(T ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by decide)))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hnorm
    (by simpa using (hexp.const_mul C).mul_const |b-a|)

theorem integrable_of_gaussian_bound (f : ℝ → ℂ) (C : ℝ)
    (hmeas : AEStronglyMeasurable f) (hbound : ∀ y, ‖f y‖ ≤ C * Real.exp (-(y ^ 2))) :
    Integrable f := by
  have hg : Integrable (fun y : ℝ => C * Real.exp (-(y ^ 2))) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul C
  exact hg.mono' hmeas (ae_of_all _ hbound)

theorem vertical_integral_eq_of_gaussian_bound (F : ℂ → ℂ) {a b C : ℝ}
    (hab : a ≤ b) (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ,
      ‖F ((x : ℂ) + y * I)‖ ≤ C * Real.exp (-(y ^ 2))) :
    (∫ y : ℝ, F ((a : ℂ) + y * I)) = ∫ y : ℝ, F ((b : ℂ) + y * I) := by
  have hc (x : ℝ) (hx : x ∈ Icc a b) : Continuous (fun y : ℝ => F ((x : ℂ) + y * I)) :=
    hhol.continuousOn.comp_continuous (by fun_prop) (by intro y; simpa using hx)
  apply vertical_integral_eq_of_horizontal_vanish F hab hhol
    (integrable_of_gaussian_bound _ C (hc a ⟨le_rfl, hab⟩).aestronglyMeasurable
      (hbound a ⟨le_rfl, hab⟩))
    (integrable_of_gaussian_bound _ C (hc b ⟨hab, le_rfl⟩).aestronglyMeasurable
      (hbound b ⟨hab, le_rfl⟩))
  · have h := horizontal_integral_tendsto_zero (fun s => F ((s.re : ℂ) - s.im * I)) a b C ?_
    · simpa [sub_eq_add_neg, neg_mul] using h
    · intro x hx y
      simpa [sub_eq_add_neg, neg_mul] using hbound x (by simpa [uIcc_of_le hab] using hx) (-y)
  · exact horizontal_integral_tendsto_zero F a b C
      (by simpa [uIcc_of_le hab] using hbound)

def gaussianContourIntegrand (G : ℂ → ℂ) (c Z : ℝ) (s : ℂ) : ℂ :=
  (Z : ℂ) ^ (s + (c : ℂ)) * Complex.exp ((s - 5 / 6) ^ 2) * G s

theorem norm_gaussianContourIntegrand (G : ℂ → ℂ) (c x y : ℝ) {Z : ℝ}
    (hZ : 0 < Z) :
    ‖gaussianContourIntegrand G c Z ((x : ℂ) + y * I)‖ =
      Z ^ (x + c) * Real.exp ((x - 5 / 6) ^ 2) *
        ‖G ((x : ℂ) + y * I)‖ * Real.exp (-(y ^ 2)) := by
  unfold gaussianContourIntegrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_exp]
  have hre : ((((x : ℂ) + y * I) - 5 / 6) ^ 2).re = (x - 5 / 6) ^ 2 - y ^ 2 := by
    simp [pow_two]
  rw [hre, Real.exp_sub]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, zero_mul, sub_self,
    add_zero, Real.exp_neg]
  ring

theorem gaussianContourIntegrand_differentiableOn {G : ℂ → ℂ} {U : Set ℂ}
    (hG : DifferentiableOn ℂ G U) (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    DifferentiableOn ℂ (gaussianContourIntegrand G c Z) U := by
  apply DifferentiableOn.mul _ hG
  apply DifferentiableOn.mul
  · exact ((differentiable_id.add_const (c : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).differentiableOn
  · exact (((differentiable_id.sub_const (5 / 6 : ℂ)).pow 2).cexp).differentiableOn

end SevenEighths.Continuation

end

end OAI

end Source1088

/- Original source: OAI/NumberTheory/DirichletL/PrincipalMellinResidues.lean; sha256: 0363acf8efc10c765e7851f9030ae6fd80f82ce3917b194734d177d2bac3be24 -/
section Source1089
namespace OAI

noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace SevenEighths.PrincipalMellinResidues
open ProbePhysical

lemma inverse_vertical_continuous (c : ℝ) (hc : c≠0) :
    Continuous (fun t : ℝ => ((c:ℂ)+t*I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro t h
  have he := congrArg Complex.re h
  simp at he
  exact hc he

lemma inverse_vertical_truncated (c T : ℝ) (hc : c≠0) :
    (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) = (2*Real.arctan (T/c):ℝ) := by
  have hi : IntervalIntegrable (fun t : ℝ => ((c:ℂ)+t*I)⁻¹) volume (-T) T :=
    (inverse_vertical_continuous c hc).intervalIntegrable (-T) T
  apply Complex.ext
  · have hh := Complex.reCLM.intervalIntegral_comp_comm hi
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).re) = (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹).re at hh
    rw [← hh]
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).re) = _
    have he : (fun t : ℝ => (((c:ℂ)+t*I)⁻¹).re) =
        (fun t : ℝ => c/(c^2+t^2)) := by
      funext t
      simp [Complex.inv_re, Complex.normSq_apply, pow_two]
    rw [he, integral_div_sq_add_sq]
    simp [neg_div, Real.arctan_neg]
    ring
  · have hh := Complex.imCLM.intervalIntegral_comp_comm hi
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).im) = (∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹).im at hh
    rw [← hh]
    change (∫ t : ℝ in -T..T, (((c:ℂ)+t*I)⁻¹).im) = _
    have he : (fun t : ℝ => (((c:ℂ)+t*I)⁻¹).im) =
        (fun t : ℝ => -(t/(c^2+t^2))) := by
      funext t
      simp [Complex.inv_im, Complex.normSq_apply, pow_two, neg_div]
    rw [he, intervalIntegral.integral_neg, integral_id_div_sq_add_sq hc]
    simp

lemma inverse_vertical_limit_pos (c : ℝ) (hc : 0<c) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) atTop (𝓝 (Real.pi:ℂ)) := by
  simp_rw [inverse_vertical_truncated c _ hc.ne']
  have ht := Real.tendsto_arctan_atTop.comp (Filter.tendsto_id.atTop_div_const hc)
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp ((ht.mono_right inf_le_left).const_mul 2)
  convert hh using 1 <;> simp [Function.comp_def]; ring

lemma inverse_vertical_limit_neg (c : ℝ) (hc : c<0) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, ((c:ℂ)+t*I)⁻¹) atTop (𝓝 (-(Real.pi:ℂ))) := by
  simp_rw [inverse_vertical_truncated c _ hc.ne]
  have ht := Real.tendsto_arctan_atBot.comp (Filter.tendsto_id.atTop_div_const_of_neg hc)
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp ((ht.mono_right inf_le_left).const_mul 2)
  convert hh using 1 <;> simp [Function.comp_def]; ring

lemma inverse_horizontal_limit (a b p : ℝ) (ε : ℝ) (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      ((x : ℂ) + (ε*T)*I - p)⁻¹) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (show ∀ᶠ T : ℝ in atTop, ‖∫ x : ℝ in a..b,
      ((x : ℂ) + (ε*T)*I - p)⁻¹‖ ≤ T⁻¹ * |b-a| from ?_) ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [norm_inv]
    apply inv_anti₀ hT
    have h := Complex.abs_im_le_norm ((x:ℂ)+(ε*T)*I-p)
    simpa [abs_mul, hε, abs_of_pos hT] using h
  · simpa using (tendsto_inv_atTop_zero.mul_const |b-a|)

lemma dslope_eq_sub_pole {A F : ℂ → ℂ} {p z : ℂ} (hz : z≠p)
    (hF : F z = A z / (z-p)) :
    dslope A p z = F z - A p * (z-p)⁻¹ := by
  rw [dslope_of_ne A hz, slope, hF]
  simp only [smul_eq_mul, div_eq_mul_inv, vsub_eq_sub]
  ring

lemma dslope_vertical_truncated (A F : ℂ → ℂ) (p x T : ℝ) (hx : x≠p)
    (hF : ∀ z : ℂ, z.re = x → F z = A z / (z-p))
    (hi : Integrable (fun t : ℝ => F ((x:ℂ)+t*I))) :
    (∫ t : ℝ in -T..T, dslope A (p:ℂ) ((x:ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, F ((x:ℂ)+t*I)) -
        A p * (∫ t : ℝ in -T..T, (((x-p:ℝ):ℂ)+t*I)⁻¹) := by
  have he (t : ℝ) : dslope A (p:ℂ) ((x:ℂ)+t*I) =
      F ((x:ℂ)+t*I) - A p * ((((x-p:ℝ):ℂ)+t*I)⁻¹) := by
    have hn : (x:ℂ)+t*I ≠ p := by
      intro h
      exact hx (by simpa using congrArg Complex.re h)
    have h := dslope_eq_sub_pole hn (hF _ (by simp))
    convert h using 1; push_cast; ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub hi.intervalIntegrable
    (((inverse_vertical_continuous (x-p) (sub_ne_zero.mpr hx)).const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]

lemma rectangle_limits (G : ℂ → ℂ) {a b : ℝ} (hab : a≤b)
    (hG : DifferentiableOn ℂ G {z : ℂ | a≤z.re ∧ z.re≤b})
    {Va Vb : ℂ}
    (ha : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((a:ℂ)+t*I)) atTop (𝓝 Va))
    (hb : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, G ((b:ℂ)+t*I)) atTop (𝓝 Vb))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x:ℂ)+(-T)*I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, G ((x:ℂ)+T*I)) atTop (𝓝 0)) :
    Va = Vb := by
  have hrect (T : ℝ) :
      (∫ x : ℝ in a..b, G ((x:ℂ)+(-T)*I)) -
      (∫ x : ℝ in a..b, G ((x:ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, G ((b:ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, G ((a:ℂ)+t*I)) = 0 := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn G
      ((a:ℂ)+(-T)*I) ((b:ℂ)+T*I) (hG.mono ?_)
    · simpa [smul_eq_mul] using h
    · intro z hz
      simpa [uIcc_of_le hab] using hz.1
  have hlim := ((hbot.sub htop).add (hb.const_mul I)).sub (ha.const_mul I)
  have hz : (0:ℂ)-0+I*Vb-I*Va=0 := tendsto_nhds_unique hlim
    (by simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0)))
  exact (mul_left_cancel₀ I_ne_zero (show I*Vb=I*Va by simpa using sub_eq_zero.mp hz)).symm

lemma horizontal_quotient_continuousOn (A : ℂ → ℂ) {a b p y : ℝ}
    (hab : a≤b) (hy : y≠0)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤z.re ∧ z.re≤b}) :
    ContinuousOn (fun x : ℝ => A ((x:ℂ)+y*I) / ((x:ℂ)+y*I-p)) (uIcc a b) := by
  apply ContinuousOn.div
  · apply hA.continuousOn.comp (by fun_prop)
    intro x hx
    simpa [uIcc_of_le hab] using hx
  · fun_prop
  · intro x hx h
    have hh := congrArg Complex.im h
    exact hy (by simpa using hh)

lemma dslope_horizontal_limit (A F : ℂ → ℂ) {a b p : ℝ} (hab : a≤b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤z.re ∧ z.re≤b})
    (hF : ∀ z : ℂ, a≤z.re → z.re≤b → z≠p → F z = A z/(z-p))
    (ε : ℝ) (hε : |ε|=1)
    (hlim : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, dslope A p ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0) := by
  have hl := hlim.sub ((inverse_horizontal_limit a b p ε hε).const_mul (A p))
  simp only [mul_zero, sub_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hy : ε*T≠0 := mul_ne_zero (by intro h; simp [h] at hε) hT.ne'
  have hn (x : ℝ) : (x:ℂ)+(ε*T)*I≠p := by
    intro h
    exact hy (by simpa using congrArg Complex.im h)
  have he (x : ℝ) (hx : x∈uIcc a b) := hF ((x:ℂ)+(ε*T)*I)
    (by have := (uIcc_of_le hab ▸ hx).1; simpa using this)
    (by have := (uIcc_of_le hab ▸ hx).2; simpa using this) (hn x)
  have hfi : IntervalIntegrable (fun x : ℝ => F ((x:ℂ)+(ε*T)*I)) volume a b := by
    apply ((horizontal_quotient_continuousOn A (p:=p) hab hy hA).congr ?_).intervalIntegrable
    intro x hx
    simpa using he x hx
  have hki : IntervalIntegrable (fun x : ℝ => ((x:ℂ)+(ε*T)*I-p)⁻¹) volume a b := by
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀ (by fun_prop)
    intro x h
    exact hn x (sub_eq_zero.mp h)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hfi (hki.const_mul _)]
  apply intervalIntegral.integral_congr
  intro x hx
  exact (dslope_eq_sub_pole (hn x) (he x hx)).symm

theorem verticalIntegral_simple_pole (A F : ℂ → ℂ) {a b p : ℝ}
    (hap : a<p) (hpb : p<b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a≤z.re ∧ z.re≤b})
    (hF : ∀ z : ℂ, a≤z.re → z.re≤b → z≠p → F z = A z/(z-p))
    (ha : Integrable (fun t : ℝ => F ((a:ℂ)+t*I)))
    (hb : Integrable (fun t : ℝ => F ((b:ℂ)+t*I)))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(-T)*I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+T*I)) atTop (𝓝 0)) :
    verticalIntegral b F = verticalIntegral a F + A p := by
  have hab := hap.le.trans hpb.le
  have hnb : {z : ℂ | a≤z.re ∧ z.re≤b} ∈ 𝓝 (p:ℂ) := by
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
        (show a<(p:ℂ).re ∧ (p:ℂ).re<b from ⟨hap,hpb⟩))
    intro z hz
    exact ⟨hz.1.le,hz.2.le⟩
  have hG := (Complex.differentiableOn_dslope hnb).mpr hA
  have haF := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hbF := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have haG : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, dslope A (p:ℂ) ((a:ℂ)+t*I))
      atTop (𝓝 ((∫ t : ℝ, F ((a:ℂ)+t*I)) - A p * (-(Real.pi:ℂ)))) := by
    simp_rw [dslope_vertical_truncated A F p a _ hap.ne
      (fun z hz => hF z (by simp [hz]) (by simpa [hz] using hab)
        (by intro h; have := congrArg Complex.re h; simp [hz] at this; exact hap.ne this)) ha]
    exact haF.sub ((inverse_vertical_limit_neg (a-p) (sub_neg.mpr hap)).const_mul (A p))
  have hbG : Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, dslope A (p:ℂ) ((b:ℂ)+t*I))
      atTop (𝓝 ((∫ t : ℝ, F ((b:ℂ)+t*I)) - A p * (Real.pi:ℂ))) := by
    simp_rw [dslope_vertical_truncated A F p b _ hpb.ne'
      (fun z hz => hF z (by simpa [hz] using hab) (by simp [hz])
        (by intro h; have := congrArg Complex.re h; simp [hz] at this; exact hpb.ne' this)) hb]
    exact hbF.sub ((inverse_vertical_limit_pos (b-p) (sub_pos.mpr hpb)).const_mul (A p))
  have hbotG := dslope_horizontal_limit A F hab hA hF (-1) (by norm_num)
    (by simpa using hbot)
  have htopG := dslope_horizontal_limit A F hab hA hF 1 (by norm_num)
    (by simpa using htop)
  have he := rectangle_limits (dslope A p) hab hG haG hbG
    (by simpa using hbotG) (by simpa using htopG)
  have he' : (∫ t : ℝ, F ((b:ℂ)+t*I)) =
      (∫ t : ℝ, F ((a:ℂ)+t*I)) + 2*(Real.pi:ℂ)*A p := by
    linear_combination -he
  unfold verticalIntegral
  rw [he']
  push_cast
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp only [mul_comm]

structure BoundaryControl (F : ℂ → ℂ) (a b : ℝ) : Prop where
  left : Integrable (fun t : ℝ => F ((a:ℂ)+t*I))
  right : Integrable (fun t : ℝ => F ((b:ℂ)+t*I))
  lower : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(-T)*I)) atTop (𝓝 0)
  upper : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+T*I)) atTop (𝓝 0)

open HeckeFamily

theorem verticalIntegral_hecke (χ : Character) (K : ℂ → ℂ) {a b : ℝ}
    (ha : 0<a) (ha1 : a<1) (h1b : 1<b)
    (hK : DifferentiableOn ℂ K {z : ℂ | a≤z.re ∧ z.re≤b})
    (hB : BoundaryControl (fun z => K z * LFunction χ z) a b) :
    verticalIntegral b (fun z => K z * LFunction χ z) =
      verticalIntegral a (fun z => K z * LFunction χ z) +
        K 1 * HeckeReciprocal.regularizedL χ 1 := by
  have h := verticalIntegral_simple_pole
    (fun z => K z * HeckeOrigin.poleRemoved χ z)
    (fun z => K z * LFunction χ z) ha1 h1b
    (hK.mul (HeckeOrigin.poleRemoved_entire χ).differentiableOn) ?_
    hB.left hB.right hB.lower hB.upper
  · simpa [HeckeOrigin.poleRemoved_one] using h
  · intro z hza hzb hzp
    have hz0 : z≠0 := by intro h; subst z; simp at hza; linarith
    have hz1 : z≠1 := by simpa using hzp
    rw [HeckeOrigin.poleRemoved_eq χ hz0 hz1]
    norm_num
    field_simp

theorem verticalIntegral_hecke_six (χ : Character) (K : ℂ → ℂ) {a b : ℝ}
    (ha : 0<a) (hap : a<1/6) (hpb : 1/6<b)
    (hK : DifferentiableOn ℂ K {z : ℂ | a≤z.re ∧ z.re≤b})
    (hB : BoundaryControl (fun z => K z * LFunction χ (6*z)) a b) :
    verticalIntegral b (fun z => K z * LFunction χ (6*z)) =
      verticalIntegral a (fun z => K z * LFunction χ (6*z)) +
        K (1/6) * HeckeReciprocal.regularizedL χ 1 / 6 := by
  have hhol : Differentiable ℂ (fun z => HeckeOrigin.poleRemoved χ (6*z)) :=
    (HeckeOrigin.poleRemoved_entire χ).comp (differentiable_id.const_mul 6)
  have h := verticalIntegral_simple_pole
    (fun z => K z * HeckeOrigin.poleRemoved χ (6*z) / 6)
    (fun z => K z * LFunction χ (6*z)) hap hpb
    ((hK.mul hhol.differentiableOn).div_const 6) ?_
    hB.left hB.right hB.lower hB.upper
  · norm_num [HeckeOrigin.poleRemoved_one] at h ⊢
    exact h
  · intro z hza hzb hzp
    have hz0 : 6*z≠0 := by
      intro h
      have h' := congrArg Complex.re h
      simp at h'
      have : z.re=0 := by linarith
      linarith
    have hz1 : 6*z≠1 := by
      intro h
      apply hzp
      push_cast
      linear_combination h / 6
    rw [HeckeOrigin.poleRemoved_eq χ hz0 hz1]
    have hden : z-(1/6:ℂ)≠0 := sub_ne_zero.mpr (by simpa using hzp)
    push_cast
    field_simp

theorem source_w_shift (χ : Character) (K : ℂ → ℂ → ℂ) (z : ℂ) {cw : ℝ}
    (hcw : 1<cw)
    (hK : DifferentiableOn ℂ (fun w => K w z)
      {w : ℂ | 19/20≤w.re ∧ w.re≤cw})
    (hB : BoundaryControl (fun w => K w z * LFunction χ w) (19/20) cw) :
    verticalIntegral cw (fun w => K w z * LFunction χ w) =
      verticalIntegral (19/20) (fun w => K w z * LFunction χ w) +
      K 1 z * HeckeReciprocal.regularizedL χ 1 :=
  verticalIntegral_hecke χ (fun w => K w z) (by norm_num) (by norm_num) hcw hK hB

theorem source_residue_z_shift (χ : Character) (K : ℂ → ℂ) {e : ℝ} (he : 0<e)
    (hK : DifferentiableOn ℂ K {z : ℂ | 33/200≤z.re ∧ z.re≤1/6+e})
    (hB : BoundaryControl (fun z => K z * LFunction χ (6*z)) (33/200) (1/6+e)) :
    verticalIntegral (1/6+e) (fun z => K z * LFunction χ (6*z)) =
      verticalIntegral (33/200) (fun z => K z * LFunction χ (6*z)) +
      K (1/6) * HeckeReciprocal.regularizedL χ 1 / 6 :=
  verticalIntegral_hecke_six χ K (by norm_num) (by norm_num) (by linarith) hK hB

lemma verticalIntegral_add (a : ℝ) (F G : ℂ → ℂ)
    (hF : Integrable (fun t : ℝ => F ((a:ℂ)+t*I)))
    (hG : Integrable (fun t : ℝ => G ((a:ℂ)+t*I))) :
    verticalIntegral a (fun z => F z + G z) = verticalIntegral a F + verticalIntegral a G := by
  unfold verticalIntegral
  rw [integral_add hF hG, mul_add]

lemma verticalIntegral_mul_const (a : ℝ) (F : ℂ → ℂ) (c : ℂ) :
    verticalIntegral a (fun z => F z * c) = verticalIntegral a F * c := by
  unfold verticalIntegral
  rw [integral_mul_const]
  ring

theorem source_ordered_double_shift (χ : Character) (K : ℂ → ℂ → ℂ)
    {cw e : ℝ} (hcw : 1<cw) (he : 0<e)
    (hwK : ∀ z : ℂ, z.re=1/6+e → DifferentiableOn ℂ (fun w => K w z)
      {w : ℂ | 19/20≤w.re ∧ w.re≤cw})
    (hwB : ∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction χ (6*z) * LFunction χ w) (19/20) cw)
    (hzK : DifferentiableOn ℂ (fun z => K 1 z)
      {z : ℂ | 33/200≤z.re ∧ z.re≤1/6+e})
    (hzB : BoundaryControl (fun z => K 1 z * LFunction χ (6*z)) (33/200) (1/6+e))
    (houter : Integrable (fun t : ℝ => verticalIntegral (19/20)
      (fun w => K w ((1/6+e:ℝ)+t*I) *
        LFunction χ (6*((1/6+e:ℝ)+t*I)) * LFunction χ w))) :
    verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K w z * LFunction χ (6*z) * LFunction χ w)) =
    verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K w z * LFunction χ (6*z) * LFunction χ w)) +
    HeckeReciprocal.regularizedL χ 1 *
      verticalIntegral (33/200) (fun z => K 1 z * LFunction χ (6*z)) +
    (HeckeReciprocal.regularizedL χ 1)^2 / 6 * K 1 (1/6) := by
  have hw (z : ℂ) (hz : z.re=1/6+e) := verticalIntegral_hecke χ
    (fun w => K w z * LFunction χ (6*z)) (by norm_num : (0:ℝ)<19/20)
    (by norm_num : (19/20:ℝ)<1) hcw ((hwK z hz).mul_const _) (hwB z hz)
  have hpoint : verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K w z * LFunction χ (6*z) * LFunction χ w)) =
      verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => K w z * LFunction χ (6*z) * LFunction χ w) +
        (K 1 z * LFunction χ (6*z)) * HeckeReciprocal.regularizedL χ 1) := by
    unfold verticalIntegral
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    exact hw _ (by simp)
  rw [hpoint, verticalIntegral_add _ _ _ houter (hzB.right.mul_const _),
    verticalIntegral_mul_const, source_residue_z_shift χ (fun z => K 1 z) he hzK hzB]
  ring

abbrev fixedPrincipal (M : Ideal O) [NeZero M] : Character :=
  HeckeRayFamily.character M 1

def fixedPrincipalResidue (M : Ideal O) [NeZero M] : ℂ :=
  HeckeReciprocal.regularizedL (fixedPrincipal M) 1

theorem fixedPrincipalResidue_ne_zero (M : Ideal O) [NeZero M] :
    fixedPrincipalResidue M ≠ 0 := by
  rw [fixedPrincipalResidue, ← HeckeOrigin.poleRemoved_one]
  exact HeckeRayFamily.principal_pole_ne_zero M

def sourceMultiplier (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (eta : Character) (s : ℂ) (H B : ℂ → ℂ → ℂ) (w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z) * (Z:ℂ)^(s+z-1) * (Y:ℂ)^(w-1) *
    Complex.exp ((s+z-1)^2) *
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z * mellin W1 w /
      LFunction eta s * H w z * B w z

theorem sourceMultiplier_integrand (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (eta principal : Character) (s : ℂ) (H B : ℂ → ℂ → ℂ) (w z : ℂ) :
    sourceMultiplier W0 W1 X Y Z eta s H B w z *
      LFunction principal (6*z) * LFunction principal w =
    (X:ℂ)^(1/2-z) * (Z:ℂ)^(s+z-1) * (Y:ℂ)^(w-1) *
      Complex.exp ((s+z-1)^2) *
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z * mellin W1 w *
      LFunction principal (6*z) * LFunction principal w /
      LFunction eta s * H w z * B w z := by
  unfold sourceMultiplier
  ring

def sourceResidueConstant (W0 W1 : SchwartzMap ℝ ℂ) (M : Ideal O) [NeZero M] : ℂ :=
  mellin W1 1 * mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) (1/6) *
    fixedPrincipalResidue M ^ 2 / 6

theorem source_double_residue (W0 W1 : SchwartzMap ℝ ℂ) (M : Ideal O) [NeZero M]
    (X Y Z : ℝ) (eta : Character) (s : ℂ) (H B : ℂ → ℂ → ℂ) :
    fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 X Y Z eta s H B 1 (1/6) =
    sourceResidueConstant W0 W1 M *
      ((X:ℂ)^(1/3:ℂ) * (Z:ℂ)^(s-5/6) * Complex.exp ((s-5/6)^2) /
        LFunction eta s * H 1 (1/6) * B 1 (1/6)) := by
  unfold sourceResidueConstant sourceMultiplier
  rw [show (1/2:ℂ)-1/6=1/3 by norm_num,
    show s+(1/6:ℂ)-1=s-5/6 by ring]
  simp only [sub_self, Complex.cpow_zero, mul_one]
  ring

theorem source_axes_separated (t : ℝ) {cw e : ℝ} (hcw : 1<cw) (he : 0<e) :
    (1/20:ℝ) ≤ ‖((19/20:ℂ)+t*I)-1‖ ∧
    (1/100:ℝ) ≤ ‖6*((33/200:ℂ)+t*I)-1‖ ∧
    6*e ≤ ‖6*(((1/6+e:ℝ):ℂ)+t*I)-1‖ ∧
    cw-1 ≤ ‖((cw:ℂ)+t*I)-1‖ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := Complex.abs_re_le_norm (((19/20:ℂ)+t*I)-1)
    norm_num at h ⊢
    exact h
  · have h := Complex.abs_re_le_norm (6*((33/200:ℂ)+t*I)-1)
    norm_num at h ⊢
    exact h
  · have h := Complex.abs_re_le_norm (6*(((1/6+e:ℝ):ℂ)+t*I)-1)
    have hr : (6*(((1/6+e:ℝ):ℂ)+t*I)-1).re=6*e := by simp; ring
    rw [hr, abs_of_pos (by positivity)] at h
    exact h
  · have h := Complex.abs_re_le_norm (((cw:ℂ)+t*I)-1)
    simpa [abs_of_pos (sub_pos.mpr hcw)] using h

end SevenEighths.PrincipalMellinResidues

end

end OAI

end Source1089

/- Original source: OAI/NumberTheory/DirichletL/ContinuationPolynomialContour.lean; sha256: ca696aa09c2045be9482062c22c0e89d997c02b802af1605348765a91682253d -/
section Source1090
namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
namespace SevenEighths.Continuation

def polynomialGaussian (n : ℕ) (y : ℝ) : ℝ :=
  (1+|y|^n)*Real.exp (-(y^2))

theorem polynomialGaussian_nonneg (n : ℕ) (y : ℝ) : 0 ≤ polynomialGaussian n y := by
  unfold polynomialGaussian
  positivity

theorem polynomialGaussian_even (n : ℕ) (y : ℝ) :
    polynomialGaussian n (-y) = polynomialGaussian n y := by
  simp [polynomialGaussian]

theorem polynomialGaussian_integrable (n : ℕ) : Integrable (polynomialGaussian n) := by
  have hp := (integrable_rpow_mul_exp_neg_mul_sq
    (by norm_num : (0 : ℝ)<1) (show (-1 : ℝ)<(n : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])).norm
  have hg := integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have he : (fun y : ℝ => ‖y^(n : ℝ)*Real.exp (-1*y^2)‖) =
      fun y : ℝ => |y|^n*Real.exp (-(y^2)) := by
    funext y
    simp [Real.rpow_natCast, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [he] at hp
  convert hg.add hp using 1
  funext y
  simp [polynomialGaussian, add_mul]

theorem polynomialGaussian_tendsto (n : ℕ) :
    Tendsto (polynomialGaussian n) atTop (𝓝 0) := by
  have hp := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (by norm_num : (0 : ℝ)<1) (n : ℝ)
  rw [cocompact_eq_atBot_atTop] at hp
  have hp' := hp.mono_left le_sup_right
  have hg : Tendsto (fun y : ℝ => Real.exp (-(y^2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by decide)))
  change Tendsto (fun y : ℝ => (1+|y|^n)*Real.exp (-(y^2))) atTop (𝓝 0)
  simpa [Real.rpow_natCast, add_mul] using hg.add hp'

theorem vertical_integral_eq_of_even_envelope (F : ℂ → ℂ) {a b C : ℝ}
    (E : ℝ → ℝ) (hE : Integrable E) (heven : ∀ y, E (-y)=E y)
    (hlim : Tendsto E atTop (𝓝 0)) (hab : a ≤ b)
    (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ, ‖F ((x : ℂ)+y*I)‖ ≤ C*E y) :
    (∫ y : ℝ, F ((a : ℂ)+y*I)) = ∫ y : ℝ, F ((b : ℂ)+y*I) := by
  have hc (x : ℝ) (hx : x ∈ Icc a b) : Continuous (fun y : ℝ => F ((x : ℂ)+y*I)) :=
    hhol.continuousOn.comp_continuous (by fun_prop) (by intro y; simpa using hx)
  have hint (x : ℝ) (hx : x ∈ Icc a b) : Integrable (fun y : ℝ => F ((x : ℂ)+y*I)) :=
    (hE.const_mul C).mono' (hc x hx).aestronglyMeasurable (ae_of_all _ (hbound x hx))
  have hhorizontal (sgn : ℝ) (heq : ∀ y, E (sgn*y)=E y) :
      Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ)+(sgn*T)*I)) atTop (𝓝 0) := by
    have hnorm (T : ℝ) : ‖∫ x : ℝ in a..b, F ((x : ℂ)+(sgn*T)*I)‖ ≤ C*E T*|b-a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      simpa only [heq, Complex.ofReal_mul] using hbound x (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx) (sgn*T)
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hnorm
      (by simpa using (hlim.const_mul C).mul_const |b-a|)
  apply vertical_integral_eq_of_horizontal_vanish F hab hhol
    (hint a ⟨le_rfl,hab⟩) (hint b ⟨hab,le_rfl⟩)
  · simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul] using hhorizontal (-1) (by simpa only [neg_one_mul] using heven)
  · simpa only [Complex.ofReal_one, one_mul] using hhorizontal 1 (by simp)

theorem vertical_integral_eq_of_polynomial_gaussian_bound (F : ℂ → ℂ)
    {a b C : ℝ} (n : ℕ) (hab : a ≤ b)
    (hhol : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ,
      ‖F ((x : ℂ)+y*I)‖ ≤ C*polynomialGaussian n y) :
    (∫ y : ℝ, F ((a : ℂ)+y*I)) = ∫ y : ℝ, F ((b : ℂ)+y*I) :=
  vertical_integral_eq_of_even_envelope F _ (polynomialGaussian_integrable n)
    (polynomialGaussian_even n) (polynomialGaussian_tendsto n) hab hhol hbound

end SevenEighths.Continuation

end

end OAI

end Source1090

/- Original source: OAI/NumberTheory/DirichletL/Detector/MellinBoundary.lean; sha256: b8d654cf361f161da883614d9e47d4ccbc79a007dfb8ec306ac908f3705e5566 -/
section Source1091
namespace OAI

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology
namespace SevenEighths.ProbeMellinBoundary
open PrincipalMellinResidues HeckeFamily EisensteinSchwartzPoisson

def height (t : ℝ) : ℝ := 1+|t|
lemma height_pos (t : ℝ) : 0<height t := by unfold height; positivity
lemma height_one_le (t : ℝ) : 1≤height t := by simp [height]

def cauchy (t : ℝ) : ℝ := (1+t^2)⁻¹
lemma cauchy_nonneg (t : ℝ) : 0≤cauchy t := by unfold cauchy; positivity
lemma cauchy_integrable : Integrable cauchy := integrable_inv_one_add_sq
lemma cauchy_tendsto : Tendsto cauchy atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_left atTop (1:ℝ) (tendsto_pow_atTop (by decide : 2≠0)))

theorem boundaryControl_of_cauchy (F : ℂ → ℂ) {a b C : ℝ}
    (ha : Continuous (fun t : ℝ => F ((a:ℂ)+t*I)))
    (hb : Continuous (fun t : ℝ => F ((b:ℂ)+t*I)))
    (hla : ∀t : ℝ, ‖F ((a:ℂ)+t*I)‖≤C*cauchy t)
    (hlb : ∀t : ℝ, ‖F ((b:ℂ)+t*I)‖≤C*cauchy t)
    (hjoin : ∀x∈uIcc a b, ∀t : ℝ, 1≤|t| → ‖F ((x:ℂ)+t*I)‖≤C*cauchy t) :
    BoundaryControl F a b := by
  have hi (h : Continuous (fun t : ℝ => F ((a:ℂ)+t*I))) :=
    (cauchy_integrable.const_mul C).mono' h.aestronglyMeasurable (Eventually.of_forall hla)
  have hj (ε : ℝ) (hε : |ε|=1) :
      Tendsto (fun T : ℝ => ∫x : ℝ in a..b, F ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
      (by simpa using (cauchy_tendsto.const_mul C).mul_const |b-a|)
    filter_upwards [eventually_ge_atTop 1] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have ht : |ε*T|=T := by rw [abs_mul,hε,one_mul,abs_of_nonneg (by linarith)]
    have hh := hjoin x (uIoc_subset_uIcc hx) (ε*T) (by simpa [ht] using hT)
    have he : cauchy (ε*T)=cauchy T := by
      unfold cauchy
      have hs : (ε*T)^2=T^2 := by nlinarith [sq_abs (ε*T)]
      rw [hs]
    simpa [he] using hh
  refine ⟨hi ha, (cauchy_integrable.const_mul C).mono' hb.aestronglyMeasurable
    (Eventually.of_forall hlb), ?_, ?_⟩
  · simpa using hj (-1) (by norm_num)
  · simpa using hj 1 (by norm_num)

lemma pole_distance_vertical (p x t : ℝ) : |x-p|≤‖(x:ℂ)+t*I-p‖ := by
  simpa using Complex.abs_re_le_norm ((x:ℂ)+t*I-p)
lemma pole_distance_horizontal (p x t : ℝ) : |t|≤‖(x:ℂ)+t*I-p‖ := by
  simpa using Complex.abs_im_le_norm ((x:ℂ)+t*I-p)

theorem boundaryControl_of_pole_product (F V G : ℂ → ℂ) {a b p C D δ : ℝ} (J : ℕ)
    (hδ : 0<δ) (hδ1 : δ≤1) (hpa : δ≤|a-p|) (hpb : δ≤|b-p|)
    (hF : ∀x∈uIcc a b, ∀t : ℝ, (x:ℂ)+t*I≠p →
      F ((x:ℂ)+t*I)=V ((x:ℂ)+t*I)*G ((x:ℂ)+t*I)/((x:ℂ)+t*I-p))
    (hV : ContinuousOn V {z : ℂ | z.re∈uIcc a b})
    (hG : ContinuousOn G {z : ℂ | z.re∈uIcc a b})
    (_hC : 0≤C) (hD : 0≤D)
    (hVbd : ∀x∈uIcc a b, ∀t : ℝ, height t^(J+2)*‖V ((x:ℂ)+t*I)‖≤C)
    (hGbd : ∀x∈uIcc a b, ∀t : ℝ, (x=a ∨ x=b ∨ 1≤|t|) →
      ‖G ((x:ℂ)+t*I)‖≤D*height t^J) :
    BoundaryControl F a b := by
  have hne (x t : ℝ) (hd : δ≤‖(x:ℂ)+t*I-p‖) : (x:ℂ)+t*I≠p := by
    intro h
    rw [h, sub_self, norm_zero] at hd
    linarith
  have hc (x : ℝ) (hx : x∈uIcc a b) (hd : δ≤|x-p|) :
      Continuous (fun t : ℝ => F ((x:ℂ)+t*I)) := by
    have hn (t : ℝ) : (x:ℂ)+t*I≠p := hne x t (hd.trans (pole_distance_vertical p x t))
    have hv := hV.comp_continuous (by fun_prop : Continuous (fun t : ℝ => (x:ℂ)+t*I))
      (by intro t; simpa using hx)
    have hg := hG.comp_continuous (by fun_prop : Continuous (fun t : ℝ => (x:ℂ)+t*I))
      (by intro t; simpa using hx)
    exact ((hv.mul hg).div (by fun_prop) (fun t => sub_ne_zero.mpr (hn t))).congr
      (fun t => (hF x hx t (hn t)).symm)
  have hbound (x : ℝ) (hx : x∈uIcc a b) (t : ℝ)
      (hd : δ≤‖(x:ℂ)+t*I-p‖) (hboundary : x=a ∨ x=b ∨ 1≤|t|) : ‖F ((x:ℂ)+t*I)‖≤(C*D/δ)*cauchy t := by
    have hn := hne x t hd
    have hv : height t^2 * (height t^J*‖V ((x:ℂ)+t*I)‖)≤C := by
      simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hVbd x hx t
    have hv' := CubicReflectionKernel.weighted_two_to_cauchy
      (mul_nonneg (pow_nonneg (height_pos t).le _) (norm_nonneg _)) t hv
    change height t^J*‖V ((x:ℂ)+t*I)‖≤C*cauchy t at hv'
    rw [hF x hx t hn, norm_div, norm_mul]
    apply (div_le_div₀ (mul_nonneg (norm_nonneg _) (mul_nonneg hD (pow_nonneg (height_pos t).le _)))
      (mul_le_mul_of_nonneg_left (hGbd x hx t hboundary) (norm_nonneg _)) hδ hd).trans
    calc
      ‖V ((x:ℂ)+t*I)‖*(D*height t^J)/δ = D/δ*(height t^J*‖V ((x:ℂ)+t*I)‖) := by ring
      _ ≤ D/δ*(C*cauchy t) := mul_le_mul_of_nonneg_left hv' (div_nonneg hD hδ.le)
      _ = _ := by ring
  apply boundaryControl_of_cauchy F (hc a (left_mem_uIcc) hpa) (hc b (right_mem_uIcc) hpb)
  · intro t
    exact hbound a left_mem_uIcc t (hpa.trans (pole_distance_vertical p a t)) (Or.inl rfl)
  · intro t
    exact hbound b right_mem_uIcc t (hpb.trans (pole_distance_vertical p b t)) (Or.inr (Or.inl rfl))
  · intro x hx t ht
    exact hbound x hx t ((hδ1.trans ht).trans (pole_distance_horizontal p x t)) (Or.inr (Or.inr ht))

def scaleBound (q lo hi : ℝ) : ℝ := Real.exp (max (Real.log q*lo) (Real.log q*hi))
lemma scaleBound_pos (q lo hi : ℝ) : 0<scaleBound q lo hi := Real.exp_pos _
lemma rpow_le_scaleBound {q lo hi x : ℝ} (hq : 0<q) (hx : x∈Icc lo hi) :
    q^x≤scaleBound q lo hi := by
  rw [Real.rpow_def_of_pos hq]
  apply Real.exp_le_exp.mpr
  by_cases hl : 0≤Real.log q
  · exact (mul_le_mul_of_nonneg_left hx.2 hl).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hl)).trans (le_max_left _ _)
lemma cpow_le_scaleBound {q lo hi : ℝ} (hq : 0<q) (z : ℂ) (hz : z.re∈Icc lo hi) :
    ‖(q:ℂ)^z‖≤scaleBound q lo hi := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hq]
  exact rpow_le_scaleBound hq hz

def wScalar (W0 : SchwartzMap ℝ ℂ) (X Z : ℝ) (eta : Character) (s z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
    mellin (paperRadialFourier W0) z / LFunction eta s

theorem source_w_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (eta : Character) (s z : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {cw AH AL : ℝ}
    (hcw : 1<cw) (hAH : 0≤AH) (hAL : 0≤AL) (JH JL : ℕ)
    (hHB : ContinuousOn (fun w => H w z*B w z) {w : ℂ | (19/20:ℝ)≤w.re ∧ w.re≤cw})
    (hHBbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖H ((x:ℂ)+t*I) z * B ((x:ℂ)+t*I) z‖≤AH*height t^JH)
    (hLbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖HeckeOrigin.poleRemoved (fixedPrincipal M) ((x:ℂ)+t*I)‖≤AL*height t^JL) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z eta s H B w z *
      LFunction (fixedPrincipal M) w) (19/20) cw := by
  let δ : ℝ := min (1/20) (cw-1)
  have hδ : 0<δ := lt_min (by norm_num) (sub_pos.mpr hcw)
  have hab : (19/20:ℝ)≤cw := by linarith
  have hu : uIcc (19/20:ℝ) cw=Icc (19/20:ℝ) cw := uIcc_of_le hab
  obtain ⟨C,hC,hV⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) (19/20) cw (JH+JL+2)
  let G (w : ℂ) := wScalar W0 X Z eta s z * (Y:ℂ)^(w-1) *
    (H w z*B w z) * HeckeOrigin.poleRemoved (fixedPrincipal M) w
  have hGc : ContinuousOn G {w : ℂ | w.re∈uIcc (19/20:ℝ) cw} := by
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact (continuous_const.mul ((continuous_id.sub continuous_const).const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne')))).continuousOn
      · rw [hu]; exact hHB
    · exact (HeckeOrigin.poleRemoved_entire (fixedPrincipal M)).continuous.continuousOn
  apply boundaryControl_of_pole_product _ (mellin W1) G (p:=1) (δ:=δ) (C:=C)
    (D:=‖wScalar W0 X Z eta s z‖*scaleBound Y (19/20-1) (cw-1)*AH*AL) (JH+JL)
    hδ (by dsimp [δ]; exact (min_le_left _ _).trans (by norm_num))
    (by dsimp [δ]; norm_num)
    (by dsimp [δ]; rw [abs_of_pos (sub_pos.mpr hcw)]; exact min_le_right _ _) ?_
    (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1
      (W1.smooth ⊤)).continuous.continuousOn hGc hC.le
    (by unfold scaleBound; positivity) (by intro x hx t; exact hV x (hu ▸ hx) t) ?_
  · intro x hx t hn
    have hxp := (hu ▸ hx).1
    have h0 : (x:ℂ)+t*I≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 : (x:ℂ)+t*I≠1 := by simpa using hn
    dsimp only [G]
    rw [HeckeOrigin.poleRemoved_eq _ h0 h1]
    unfold sourceMultiplier wScalar
    norm_num only [Complex.ofReal_one]
    field_simp [hEta]
  · intro x hx t hboundary
    have hv := cpow_le_scaleBound hY (((x:ℂ)+t*I)-1)
      (show (((x:ℂ)+t*I)-1).re∈Icc (19/20-1) (cw-1) by
        simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,zero_mul,
          sub_zero,add_zero,one_re]
        exact ⟨sub_le_sub_right (hu ▸ hx).1 1, sub_le_sub_right (hu ▸ hx).2 1⟩)
    dsimp only [G]
    rw [norm_mul,norm_mul,norm_mul]
    calc
      _ ≤ ‖wScalar W0 X Z eta s z‖ * scaleBound Y (19/20-1) (cw-1) *
          (AH*height t^JH) * (AL*height t^JL) := by
        have hscale := (scaleBound_pos Y (19/20-1) (cw-1)).le
        have hp := (height_pos t).le
        exact mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
            (hHBbd x (hu ▸ hx) t hboundary) (norm_nonneg _) (by positivity))
          (hLbd x (hu ▸ hx) t hboundary) (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring

lemma gaussian_strip_norm_le (s : ℂ) {a b x : ℝ} (ha : 0<a) (hx : x∈Icc a b) (t : ℝ) :
    ‖Complex.exp ((s+((x:ℂ)+t*I)-1)^2)‖≤Real.exp ((|s.re|+b+1)^2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hr : ((s+((x:ℂ)+t*I)-1)^2).re = (s.re+x-1)^2-(s.im+t)^2 := by simp [pow_two]
  rw [hr]
  have hxb : 0<x := ha.trans_le hx.1
  have hK : 0≤|s.re|+b+1 := by linarith [abs_nonneg s.re, hx.2]
  have hA : |s.re+x-1|≤|s.re|+b+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le s.re, le_abs_self s.re, hx.2]
  have hsq := pow_le_pow_left₀ (abs_nonneg (s.re+x-1)) hA 2
  rw [sq_abs] at hsq
  nlinarith [sq_nonneg (s.im+t)]

def zScalar (W1 : SchwartzMap ℝ ℂ) (X Z : ℝ) (eta : Character) (s z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*mellin W1 1 / LFunction eta s

def zScaleBound (W1 : SchwartzMap ℝ ℂ) (X Z : ℝ) (eta : Character) (s : ℂ) (a b : ℝ) : ℝ :=
  scaleBound X (1/2-b) (1/2-a) * scaleBound Z (s.re+a-1) (s.re+b-1) *
    Real.exp ((|s.re|+b+1)^2) * ‖mellin W1 1‖ / ‖LFunction eta s‖

lemma zScalar_continuous (W1 : SchwartzMap ℝ ℂ) {X Z : ℝ} (hX : 0<X) (hZ : 0<Z)
    (eta : Character) (s : ℂ) : Continuous (zScalar W1 X Z eta s) := by
  unfold zScalar
  apply Continuous.div_const
  apply Continuous.mul_const
  apply Continuous.mul
  · exact (((continuous_const.sub continuous_id).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).mul
      (((continuous_const.add continuous_id).sub continuous_const).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))))
  · fun_prop

lemma zScalar_norm_le (W1 : SchwartzMap ℝ ℂ) {X Z a b x : ℝ}
    (hX : 0<X) (hZ : 0<Z) (ha : 0<a) (hx : x∈Icc a b)
    (eta : Character) (s : ℂ) (t : ℝ) :
    ‖zScalar W1 X Z eta s ((x:ℂ)+t*I)‖≤zScaleBound W1 X Z eta s a b := by
  unfold zScalar zScaleBound
  simp only [norm_div,norm_mul]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul
  · apply mul_le_mul
    · apply cpow_le_scaleBound hX
      simpa using And.intro (sub_le_sub_left hx.2 (1/2)) (sub_le_sub_left hx.1 (1/2))
    · apply cpow_le_scaleBound hZ
      simpa using And.intro (by linarith [hx.1] : s.re+a-1≤s.re+x-1)
        (by linarith [hx.2] : s.re+x-1≤s.re+b-1)
    · exact norm_nonneg _
    · exact (scaleBound_pos _ _ _).le
  · exact gaussian_strip_norm_le s ha hx t
  · exact norm_nonneg _
  · exact mul_nonneg (scaleBound_pos _ _ _).le (scaleBound_pos _ _ _).le

theorem source_z_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0<a0) (hW0 : Function.support W0⊆Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (eta : Character) (s : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {e AH AL : ℝ}
    (he : 0<e) (hAH : 0≤AH) (hAL : 0≤AL) (JH JL : ℕ)
    (hHB : ContinuousOn (fun z => H 1 z*B 1 z)
      {z : ℂ | (33/200:ℝ)≤z.re ∧ z.re≤1/6+e})
    (hHBbd : ∀x∈Icc (33/200:ℝ) (1/6+e), ∀t : ℝ, (x=33/200 ∨ x=1/6+e ∨ 1≤|t|) →
      ‖H 1 ((x:ℂ)+t*I) * B 1 ((x:ℂ)+t*I)‖≤AH*height t^JH)
    (hLbd : ∀x∈Icc (33/200:ℝ) (1/6+e), ∀t : ℝ, (x=33/200 ∨ x=1/6+e ∨ 1≤|t|) →
      ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((x:ℂ)+t*I))‖≤AL*height t^JL) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z eta s H B 1 z *
      LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  let δ : ℝ := min (1/600) e
  have hδ : 0<δ := lt_min (by norm_num) he
  have hab : (33/200:ℝ)≤1/6+e := by linarith
  have hu : uIcc (33/200:ℝ) (1/6+e)=Icc (33/200:ℝ) (1/6+e) := uIcc_of_le hab
  obtain ⟨C,hC,hV⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0
    (33/200) (1/6+e) (by norm_num) (JH+JL+2)
  let G (z : ℂ) := zScalar W1 X Z eta s z * (H 1 z*B 1 z) *
    HeckeOrigin.poleRemoved (fixedPrincipal M) (6*z) / 6
  have hGc : ContinuousOn G {z : ℂ | z.re∈uIcc (33/200:ℝ) (1/6+e)} := by
    apply ContinuousOn.div_const
    apply ContinuousOn.mul
    · exact (zScalar_continuous W1 hX hZ eta s).continuousOn.mul (by rw [hu]; exact hHB)
    · exact ((HeckeOrigin.poleRemoved_entire (fixedPrincipal M)).continuous.comp
        (continuous_const.mul continuous_id)).continuousOn
  apply boundaryControl_of_pole_product _ (mellin (paperRadialFourier W0)) G
    (p:=1/6) (δ:=δ) (C:=C)
    (D:=zScaleBound W1 X Z eta s (33/200) (1/6+e)*AH*AL/6) (JH+JL)
    hδ (by dsimp [δ]; exact (min_le_left _ _).trans (by norm_num))
    (by dsimp [δ]; norm_num)
    (by dsimp [δ]; rw [show (1/6+e:ℝ)-1/6=e by ring, abs_of_pos he]; exact min_le_right _ _)
    ?_ ?_ hGc hC.le (by unfold zScaleBound scaleBound; positivity) (by intro x hx t; exact hV x (hu ▸ hx) t) ?_
  · intro x hx t hn
    have hxp := (hu ▸ hx).1
    have h0 : 6*((x:ℂ)+t*I)≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 : 6*((x:ℂ)+t*I)≠1 := by
      intro h
      apply hn
      push_cast
      linear_combination h/6
    have hd : (x:ℂ)+t*I-(1/6:ℂ)≠0 := sub_ne_zero.mpr (by simpa using hn)
    dsimp only [G]
    rw [HeckeOrigin.poleRemoved_eq _ h0 h1]
    norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    apply (eq_div_iff hd).mpr
    unfold sourceMultiplier zScalar
    norm_num only [sub_self,Complex.cpow_zero,mul_one]
    field_simp [hEta]
  · apply (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.mono
    intro z hz
    have := (hu ▸ hz).1
    change 0<z.re
    linarith
  · intro x hx t hboundary
    dsimp only [G]
    rw [norm_div,norm_mul,norm_mul]
    norm_num only [Complex.norm_ofNat]
    calc
      _ ≤ (zScaleBound W1 X Z eta s (33/200) (1/6+e) *
          (AH*height t^JH) * (AL*height t^JL))/6 := by
        have hS : 0≤zScaleBound W1 X Z eta s (33/200) (1/6+e) := by
          unfold zScaleBound scaleBound
          positivity
        have hp := (height_pos t).le
        apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ)≤6)
        exact mul_le_mul
          (mul_le_mul (zScalar_norm_le W1 hX hZ (by norm_num) (hu ▸ hx) eta s t)
            (hHBbd x (hu ▸ hx) t hboundary) (norm_nonneg _) hS)
          (hLbd x (hu ▸ hx) t hboundary) (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring

def profile (W0 W1 : SchwartzMap ℝ ℂ) (s w z : ℂ) : ℂ :=
  Complex.exp ((s+z-1)^2) * mellin (paperRadialFourier W0) z * mellin W1 w

def jointHeight (t v w : ℝ) : ℝ := 1+|t|+|v|+|w|
lemma jointHeight_pos (t v w : ℝ) : 0<jointHeight t v w := by unfold jointHeight; positivity

def gaussianMoment (n : ℕ) (u : ℝ) : ℝ := height u^n*Real.exp (-(u^2))
lemma gaussianMoment_nonneg (n : ℕ) (u : ℝ) : 0≤gaussianMoment n u := by
  unfold gaussianMoment height
  positivity
lemma gaussianMoment_integrable (n : ℕ) : Integrable (gaussianMoment n) := by
  apply ((Continuation.polynomialGaussian_integrable n).const_mul ((2:ℝ)^(n-1))).mono'
  · unfold gaussianMoment height
    exact (by fun_prop : Continuous _).aestronglyMeasurable
  · apply Eventually.of_forall
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianMoment_nonneg n u)]
    have h := add_pow_le (by norm_num : (0:ℝ)≤1) (abs_nonneg u) n
    simpa [gaussianMoment,height,Continuation.polynomialGaussian,mul_assoc] using
      mul_le_mul_of_nonneg_right h (Real.exp_pos (-(u^2))).le

lemma height_sub_le (t v : ℝ) : height t≤height (t+v)*height v := by
  have ht : |t|≤|t+v|+|v| := by
    simpa using (abs_sub_le (t+v) 0 v)
  unfold height
  nlinarith [mul_nonneg (abs_nonneg (t+v)) (abs_nonneg v), abs_nonneg (t+v),abs_nonneg v]

lemma jointHeight_le_shear (t v w : ℝ) :
    jointHeight t v w≤2*height (t+v)*height v*height w := by
  have ht : |t|≤|t+v|+|v| := by simpa using (abs_sub_le (t+v) 0 v)
  have huv : 1≤height (t+v)*height v := one_le_mul_of_one_le_of_one_le (height_one_le _) (height_one_le _)
  have h1 : 1+|t|+|v|≤2*height (t+v)*height v := by
    unfold height
    nlinarith [mul_nonneg (abs_nonneg (t+v)) (abs_nonneg v), abs_nonneg (t+v),abs_nonneg v]
  unfold jointHeight
  change 1+|t|+|v|+|w|≤2*height (t+v)*height v*(1+|w|)
  calc
    _ ≤ 2*height (t+v)*height v+|w| := by linarith [h1]
    _ ≤ 2*height (t+v)*height v+(2*height (t+v)*height v)*|w| := by
      have hh : 1≤2*height (t+v)*height v := by nlinarith
      have hhh := mul_le_mul_of_nonneg_right hh (abs_nonneg w)
      linarith
    _ = _ := by ring

lemma weighted_to_cauchy {f C : ℝ} (J : ℕ) (t : ℝ) (hf : 0≤f)
    (h : height t^(J+2)*f≤C) : height t^J*f≤C*cauchy t := by
  have hh : (1+|t|)^2*(height t^J*f)≤C := by
    simpa [height,pow_add,mul_assoc,mul_comm,mul_left_comm] using h
  exact CubicReflectionKernel.weighted_two_to_cauchy
    (mul_nonneg (pow_nonneg (height_pos t).le _) hf) t hh

lemma weighted_coupled_cauchy (J : ℕ) (t v w A B C D : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (_hD : 0≤D)
    (ha : height v^(J+2)*A≤C) (hb : height w^(J+2)*B≤D) :
    jointHeight t v w^J * Real.exp (-((t+v)^2))*A*B ≤
      (2:ℝ)^J*C*D*(gaussianMoment J (t+v)*cauchy v*cauchy w) := by
  have hpow := pow_le_pow_left₀ (jointHeight_pos t v w).le (jointHeight_le_shear t v w) J
  have ha' := weighted_to_cauchy J v hA ha
  have hb' := weighted_to_cauchy J w hB hb
  calc
    _ ≤ (2*height (t+v)*height v*height w)^J * Real.exp (-((t+v)^2))*A*B := by gcongr
    _ = (2:ℝ)^J * gaussianMoment J (t+v) * (height v^J*A)*(height w^J*B) := by
      simp only [mul_pow,gaussianMoment]
      ring
    _ ≤ (2:ℝ)^J * gaussianMoment J (t+v) * (C*cauchy v)*(D*cauchy w) := by
      have hg := gaussianMoment_nonneg J (t+v)
      have hc := cauchy_nonneg v
      have hd := cauchy_nonneg w
      have hw := (height_pos w).le
      have hv := (height_pos v).le
      gcongr
    _ = _ := by ring

abbrev HeightSpace := (ℝ×ℝ)×ℝ
abbrev heightMeasure : Measure HeightSpace := (volume.prod volume).prod volume

def jointEnvelope (J : ℕ) (p : HeightSpace) : ℝ :=
  gaussianMoment J (p.1.1+p.1.2)*cauchy p.1.2*cauchy p.2

lemma jointEnvelope_nonneg (J : ℕ) (p : HeightSpace) : 0≤jointEnvelope J p := by
  exact mul_nonneg (mul_nonneg (gaussianMoment_nonneg _ _) (cauchy_nonneg _)) (cauchy_nonneg _)

lemma jointEnvelope_integrable (J : ℕ) : Integrable (jointEnvelope J) heightMeasure := by
  have hp : MeasurePreserving (fun p : ℝ×ℝ => (p.1+p.2,p.2))
      (volume.prod volume) (volume.prod volume) := by
    have hp0 : MeasurePreserving (fun p : ℝ×ℝ => (p.2,p.2+p.1))
        (volume.prod volume) (volume.prod volume) := measurePreserving_prod_add_swap volume volume
    have hp1 := (Measure.measurePreserving_swap (μ:=(volume : Measure ℝ)) (ν:=volume)).comp hp0
    simpa only [Function.comp_def,Prod.swap,add_comm] using! hp1
  have ht := hp.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hi := ((gaussianMoment_integrable J).mul_prod cauchy_integrable).mul_prod cauchy_integrable
  exact ht.integrable_comp_of_integrable hi

def onLines (W0 W1 : SchwartzMap ℝ ℂ) (σ ξ υ : ℝ) (p : HeightSpace) : ℂ :=
  profile W0 W1 ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)

lemma onLines_norm (W0 W1 : SchwartzMap ℝ ℂ) (σ ξ υ : ℝ) (p : HeightSpace) :
    ‖onLines W0 W1 σ ξ υ p‖ = Real.exp ((σ+ξ-1)^2)*Real.exp (-((p.1.1+p.1.2)^2))*
      ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖ *
      ‖mellin W1 ((υ:ℂ)+p.2*I)‖ := by
  unfold onLines profile
  rw [norm_mul,norm_mul,Complex.norm_exp]
  have hr : ((((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)^2).re =
      (σ+ξ-1)^2+(-((p.1.1+p.1.2)^2)) := by simp [pow_two]; ring
  rw [hr,Real.exp_add]

lemma onLines_continuous (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (σ ξ υ : ℝ) (hξ : 0<ξ) : Continuous (onLines W0 W1 σ ξ υ) := by
  have hR : Continuous (fun t : ℝ => mellin (paperRadialFourier W0) ((ξ:ℂ)+t*I)) :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.comp_continuous
      (by fun_prop) (by intro t; simpa using hξ)
  have hW := (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1
    (W1.smooth ⊤)).continuous
  unfold onLines profile
  apply Continuous.mul
  · apply Continuous.mul
    · fun_prop
    · exact hR.comp (continuous_snd.comp continuous_fst)
  · exact hW.comp (by fun_prop)

def realGaussianBound (slo shi zlo zhi : ℝ) : ℝ :=
  Real.exp ((|slo|+|shi|+|zlo|+|zhi|+1)^2)
lemma realGaussianBound_pos (slo shi zlo zhi : ℝ) : 0<realGaussianBound slo shi zlo zhi :=
  Real.exp_pos _
lemma realGaussian_le {slo shi zlo zhi σ ξ : ℝ} (hσ : σ∈Icc slo shi) (hξ : ξ∈Icc zlo zhi) :
    Real.exp ((σ+ξ-1)^2)≤realGaussianBound slo shi zlo zhi := by
  have hs : |σ|≤|slo|+|shi| := by
    rw [abs_le]
    constructor <;> linarith [hσ.1,hσ.2,neg_abs_le slo,le_abs_self shi,abs_nonneg slo,abs_nonneg shi]
  have hz : |ξ|≤|zlo|+|zhi| := by
    rw [abs_le]
    constructor <;> linarith [hξ.1,hξ.2,neg_abs_le zlo,le_abs_self zhi,abs_nonneg zlo,abs_nonneg zhi]
  have hh : |σ+ξ-1|≤|slo|+|shi|+|zlo|+|zhi|+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le σ,le_abs_self σ,neg_abs_le ξ,le_abs_self ξ]
  apply Real.exp_le_exp.mpr
  have hp := pow_le_pow_left₀ (abs_nonneg (σ+ξ-1)) hh 2
  simpa [sq_abs] using hp

lemma profile_moment_majorant (W0 W1 : SchwartzMap ℝ ℂ) (J : ℕ)
    {slo shi zlo zhi σ ξ υ C D : ℝ} (hσ : σ∈Icc slo shi) (hξ : ξ∈Icc zlo zhi)
    (hC : 0≤C) (hD : 0≤D)
    (hR : ∀v : ℝ, height v^(J+2)*‖mellin (paperRadialFourier W0) ((ξ:ℂ)+v*I)‖≤C)
    (hW : ∀w : ℝ, height w^(J+2)*‖mellin W1 ((υ:ℂ)+w*I)‖≤D) (p : HeightSpace) :
    jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ≤
      (realGaussianBound slo shi zlo zhi*2^J*C*D)*jointEnvelope J p := by
  have hb := weighted_coupled_cauchy J p.1.1 p.1.2 p.2
    ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖ ‖mellin W1 ((υ:ℂ)+p.2*I)‖ C D
    (norm_nonneg _) (norm_nonneg _) hC hD (hR _) (hW _)
  rw [onLines_norm]
  calc
    _ = Real.exp ((σ+ξ-1)^2) * (jointHeight p.1.1 p.1.2 p.2^J*
        Real.exp (-((p.1.1+p.1.2)^2))*
        ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖*‖mellin W1 ((υ:ℂ)+p.2*I)‖) := by ring
    _ ≤ realGaussianBound slo shi zlo zhi *
        ((2:ℝ)^J*C*D*(gaussianMoment J (p.1.1+p.1.2)*cauchy p.1.2*cauchy p.2)) :=
      mul_le_mul (realGaussian_le hσ hξ) hb
        (by have := (jointHeight_pos p.1.1 p.1.2 p.2).le; positivity)
        (realGaussianBound_pos _ _ _ _).le
    _ = _ := by unfold jointEnvelope; ring

theorem profile_uniform_moments (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      Integrable (fun p : HeightSpace => jointHeight p.1.1 p.1.2 p.2^J*
        ‖onLines W0 W1 σ ξ υ p‖) heightMeasure ∧
      (∫p : HeightSpace, jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)≤K := by
  obtain ⟨C,hC,hR⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 zlo zhi hzlo (J+2)
  obtain ⟨D,hD,hW⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) wlo whi (J+2)
  let A := realGaussianBound slo shi zlo zhi*2^J*C*D
  have hA : 0<A := by dsimp [A]; exact mul_pos (mul_pos (mul_pos (realGaussianBound_pos _ _ _ _)
    (by positivity)) hC) hD
  refine ⟨A*(1+|∫p, jointEnvelope J p ∂heightMeasure|),by positivity,?_⟩
  intro σ hσ ξ hξ υ hυ
  have hbound := profile_moment_majorant W0 W1 J hσ hξ hC.le hD.le (hR ξ hξ) (hW υ hυ)
  have hc := onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ (hzlo.trans_le hξ.1)
  have hf : Integrable (fun p : HeightSpace => jointHeight p.1.1 p.1.2 p.2^J*
      ‖onLines W0 W1 σ ξ υ p‖) heightMeasure := by
    apply ((jointEnvelope_integrable J).const_mul A).mono'
    · exact ((by unfold jointHeight; fun_prop : Continuous (fun p : HeightSpace =>
        jointHeight p.1.1 p.1.2 p.2^J)).mul hc.norm).aestronglyMeasurable
    · apply Eventually.of_forall
      intro p
      have hn : 0≤jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ :=
        mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)
      rw [Real.norm_eq_abs,abs_of_nonneg hn]
      exact hbound p
  refine ⟨hf,?_⟩
  calc
    _ ≤ ∫p, A*jointEnvelope J p ∂heightMeasure := integral_mono hf
      ((jointEnvelope_integrable J).const_mul A) hbound
    _ = A*(∫p, jointEnvelope J p ∂heightMeasure) := integral_const_mul _ _
    _ ≤ _ := by
      have hh := le_abs_self (∫p, jointEnvelope J p ∂heightMeasure)
      exact mul_le_mul_of_nonneg_left (by linarith) hA.le

def outsideBox (T : ℝ) : Set HeightSpace :=
  {p | T < |p.1.1| ∨ T < |p.1.2| ∨ T < |p.2|}
lemma outsideBox_measurable (T : ℝ) : MeasurableSet (outsideBox T) := by
  unfold outsideBox
  measurability
lemma height_le_joint_on_tail {T : ℝ} {p : HeightSpace} (hp : p∈outsideBox T) :
    1+T≤jointHeight p.1.1 p.1.2 p.2 := by
  rcases hp with h|h|h <;> unfold jointHeight <;>
    linarith [abs_nonneg p.1.1,abs_nonneg p.1.2,abs_nonneg p.2]

lemma weighted_tail_pointwise (f : HeightSpace → ℂ) (J N : ℕ) {T : ℝ} (hT : 0≤T)
    {p : HeightSpace} (hp : p∈outsideBox T) :
    jointHeight p.1.1 p.1.2 p.2^J*‖f p‖ ≤
      (jointHeight p.1.1 p.1.2 p.2^(J+N)*‖f p‖)/(1+T)^N := by
  apply (le_div_iff₀ (by positivity)).mpr
  have hn := pow_le_pow_left₀ (by linarith : 0≤1+T) (height_le_joint_on_tail hp) N
  have hh := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (pow_nonneg (jointHeight_pos p.1.1 p.1.2 p.2).le J) (norm_nonneg (f p)))
  convert hh using 1 ; rw [pow_add] ; ring

theorem profile_uniform_tails (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi, ∀T : ℝ, 0≤T →
      (∫p : HeightSpace in outsideBox T, jointHeight p.1.1 p.1.2 p.2^J*
        ‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)≤K/(1+T)^N := by
  obtain ⟨K,hK,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo (J+N)
  obtain ⟨K0,hK0,hM0⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ T hT
  obtain ⟨hi,hb⟩ := hM σ hσ ξ hξ υ hυ
  have hi0 := (hM0 σ hσ ξ hξ υ hυ).1
  calc
    _ ≤ ∫p : HeightSpace in outsideBox T,
        (jointHeight p.1.1 p.1.2 p.2^(J+N)*‖onLines W0 W1 σ ξ υ p‖)/(1+T)^N ∂heightMeasure := by
      apply setIntegral_mono_on hi0.integrableOn (hi.div_const _).integrableOn (outsideBox_measurable T)
      intro p hp
      exact weighted_tail_pointwise _ J N hT hp
    _ = (∫p : HeightSpace in outsideBox T,
        jointHeight p.1.1 p.1.2 p.2^(J+N)*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)/(1+T)^N :=
      integral_div _ _
    _ ≤ (∫p : HeightSpace,
        jointHeight p.1.1 p.1.2 p.2^(J+N)*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)/(1+T)^N := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply setIntegral_le_integral hi
      exact Eventually.of_forall (fun p => mul_nonneg
        (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _))
    _ ≤ _ := div_le_div_of_nonneg_right hb (by positivity)

theorem profile_arithmetic_integrable (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1) (σ ξ υ : ℝ) (hξ : 0<ξ)
    (G : HeightSpace → ℂ) (hG : AEStronglyMeasurable G heightMeasure) (A : ℝ) (J : ℕ)
    (hbound : ∀p, ‖G p‖≤A*jointHeight p.1.1 p.1.2 p.2^J) :
    Integrable (fun p => G p*onLines W0 W1 σ ξ υ p) heightMeasure := by
  obtain ⟨K,hK,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ ξ ξ υ υ hξ J
  have hi := (hM σ ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩).1
  apply (hi.const_mul A).mono'
  · exact hG.mul (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ hξ).aestronglyMeasurable
  · apply Eventually.of_forall
    intro p
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg _)

inductive SliceAxis where
  | s | z | w

def sliceMap (axis : SliceAxis) (T : ℝ) (q : ℝ×ℝ) : HeightSpace :=
  match axis with
  | .s => ((T,q.1),q.2)
  | .z => ((q.1,T),q.2)
  | .w => ((q.1,q.2),T)

lemma sliceMap_continuous (axis : SliceAxis) (T : ℝ) : Continuous (sliceMap axis T) := by
  cases axis <;> unfold sliceMap <;> fun_prop

lemma slice_height_le (axis : SliceAxis) (T : ℝ) (q : ℝ×ℝ) :
    height T≤jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2 := by
  cases axis <;> unfold sliceMap height jointHeight <;>
    linarith [abs_nonneg q.1,abs_nonneg q.2]

lemma cauchy_le_one (t : ℝ) : cauchy t≤1 := by
  simpa [cauchy] using inv_anti₀ (by norm_num : (0:ℝ)<1)
    (show 1≤1+t^2 by nlinarith [sq_nonneg t])

def sliceEnvelope (axis : SliceAxis) (J : ℕ) (T : ℝ) (q : ℝ×ℝ) : ℝ :=
  match axis with
  | .s | .z => gaussianMoment J (T+q.1)*cauchy q.2
  | .w => gaussianMoment J (q.1+q.2)*cauchy q.2

def sliceMass (J : ℕ) : ℝ := (∫u : ℝ, gaussianMoment J u)*(∫v : ℝ, cauchy v)

lemma sliceEnvelope_nonneg (axis : SliceAxis) (J : ℕ) (T : ℝ) (q : ℝ×ℝ) :
    0≤sliceEnvelope axis J T q := by
  cases axis <;> exact mul_nonneg (gaussianMoment_nonneg _ _) (cauchy_nonneg _)

lemma jointEnvelope_slice_le (axis : SliceAxis) (J : ℕ) (T : ℝ) (q : ℝ×ℝ) :
    jointEnvelope J (sliceMap axis T q)≤sliceEnvelope axis J T q := by
  cases axis
  · change gaussianMoment J (T+q.1)*cauchy q.1*cauchy q.2 ≤ gaussianMoment J (T+q.1)*cauchy q.2
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (cauchy_le_one q.1) (gaussianMoment_nonneg J (T+q.1))) (cauchy_nonneg q.2)
    simpa using hh
  · change gaussianMoment J (q.1+T)*cauchy T*cauchy q.2 ≤ gaussianMoment J (T+q.1)*cauchy q.2
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (cauchy_le_one T) (gaussianMoment_nonneg J (q.1+T))) (cauchy_nonneg q.2)
    simpa [add_comm] using hh
  · change gaussianMoment J (q.1+q.2)*cauchy q.2*cauchy T ≤ gaussianMoment J (q.1+q.2)*cauchy q.2
    simpa using mul_le_mul_of_nonneg_left (cauchy_le_one T)
      (mul_nonneg (gaussianMoment_nonneg _ _) (cauchy_nonneg _))

lemma pairEnvelope_integrable (J : ℕ) :
    Integrable (fun q : ℝ×ℝ => gaussianMoment J (q.1+q.2)*cauchy q.2) (volume.prod volume) := by
  have hp0 : MeasurePreserving (fun p : ℝ×ℝ => (p.2,p.2+p.1))
      (volume.prod volume) (volume.prod volume) := measurePreserving_prod_add_swap volume volume
  have hp1 := (Measure.measurePreserving_swap (μ:=(volume : Measure ℝ)) (ν:=volume)).comp hp0
  have hi := hp1.integrable_comp_of_integrable ((gaussianMoment_integrable J).mul_prod cauchy_integrable)
  simpa only [Function.comp_def,Prod.swap,add_comm] using! hi

lemma sliceEnvelope_integrable (axis : SliceAxis) (J : ℕ) (T : ℝ) :
    Integrable (sliceEnvelope axis J T) (volume.prod volume) := by
  cases axis
  · exact ((gaussianMoment_integrable J).comp_add_left T).mul_prod cauchy_integrable
  · exact ((gaussianMoment_integrable J).comp_add_left T).mul_prod cauchy_integrable
  · exact pairEnvelope_integrable J

lemma sliceEnvelope_integral (axis : SliceAxis) (J : ℕ) (T : ℝ) :
    (∫q : ℝ×ℝ, sliceEnvelope axis J T q ∂volume.prod volume)=sliceMass J := by
  cases axis
  · change (∫q : ℝ×ℝ, gaussianMoment J (T+q.1)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_mul (fun u : ℝ => gaussianMoment J (T+u)) cauchy,integral_add_left_eq_self]
    rfl
  · change (∫q : ℝ×ℝ, gaussianMoment J (T+q.1)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_mul (fun u : ℝ => gaussianMoment J (T+u)) cauchy,integral_add_left_eq_self]
    rfl
  · change (∫q : ℝ×ℝ, gaussianMoment J (q.1+q.2)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_symm _ (pairEnvelope_integrable J)]
    simp_rw [integral_mul_const,integral_add_right_eq_self]
    exact integral_const_mul _ _

lemma weighted_slice_pointwise (f : HeightSpace → ℂ) (axis : SliceAxis) (J N : ℕ) (T : ℝ) (q : ℝ×ℝ) :
    jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
      ‖f (sliceMap axis T q)‖ ≤
    (jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^(J+N)*
      ‖f (sliceMap axis T q)‖)/height T^N := by
  apply (le_div_iff₀ (pow_pos (height_pos T) N)).mpr
  have hn := pow_le_pow_left₀ (height_pos T).le (slice_height_le axis T q) N
  have hh := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (pow_nonneg (jointHeight_pos (sliceMap axis T q).1.1
      (sliceMap axis T q).1.2 (sliceMap axis T q).2).le J) (norm_nonneg (f (sliceMap axis T q))))
  convert hh using 1 ; rw [pow_add] ; ring

theorem profile_uniform_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀axis : SliceAxis, ∀T : ℝ,
      Integrable (fun q : ℝ×ℝ =>
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
        ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
        ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume)≤K/height T^N := by
  obtain ⟨C,hC,hR⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0
    zlo zhi hzlo (J+N+2)
  obtain ⟨D,hD,hW⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) wlo whi (J+N+2)
  let A := realGaussianBound slo shi zlo zhi*2^(J+N)*C*D
  have hA : 0<A := by dsimp [A]; exact mul_pos (mul_pos (mul_pos (realGaussianBound_pos _ _ _ _)
    (by positivity)) hC) hD
  refine ⟨A*(1+|sliceMass (J+N)|),by positivity,?_⟩
  intro σ hσ ξ hξ υ hυ axis T
  have hb := profile_moment_majorant W0 W1 (J+N) hσ hξ hC.le hD.le (hR ξ hξ) (hW υ hυ)
  let f (q : ℝ×ℝ) := jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
    (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖
  have hbound (q : ℝ×ℝ) : f q≤(A/height T^N)*sliceEnvelope axis (J+N) T q := by
    calc
      _ ≤ (jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^(J+N)*
          ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖)/height T^N :=
        weighted_slice_pointwise _ axis J N T q
      _ ≤ (A*jointEnvelope (J+N) (sliceMap axis T q))/height T^N :=
        div_le_div_of_nonneg_right (hb _) (pow_nonneg (height_pos T).le N)
      _ ≤ (A*sliceEnvelope axis (J+N) T q)/height T^N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (jointEnvelope_slice_le _ _ _ _) hA.le)
          (pow_nonneg (height_pos T).le N)
      _ = _ := by ring
  have hfnonneg (q : ℝ×ℝ) : 0≤f q := mul_nonneg
    (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)
  have hf : Integrable f (volume.prod volume) := by
    apply ((sliceEnvelope_integrable axis (J+N) T).const_mul (A/height T^N)).mono'
    · have hc := (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ
        (hzlo.trans_le hξ.1)).comp (sliceMap_continuous axis T)
      exact ((by cases axis <;> unfold sliceMap jointHeight <;> fun_prop : Continuous (fun q : ℝ×ℝ =>
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J)).mul hc.norm).aestronglyMeasurable
    · exact Eventually.of_forall (fun q => by rw [Real.norm_eq_abs,abs_of_nonneg (hfnonneg q)]; exact hbound q)
  refine ⟨hf,?_⟩
  calc
    _ ≤ ∫q : ℝ×ℝ, (A/height T^N)*sliceEnvelope axis (J+N) T q ∂volume.prod volume :=
      integral_mono hf ((sliceEnvelope_integrable axis (J+N) T).const_mul _) hbound
    _ = (A/height T^N)*sliceMass (J+N) := by rw [integral_const_mul,sliceEnvelope_integral]
    _ ≤ (A/height T^N)*(1+|sliceMass (J+N)|) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hA.le (pow_nonneg (height_pos T).le N))
      linarith [le_abs_self (sliceMass (J+N))]
    _ = _ := by ring

theorem profile_arithmetic_tails (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀A : ℝ, 0≤A → ∀G : HeightSpace → ℂ,
      AEStronglyMeasurable G heightMeasure →
      (∀p, ‖G p‖≤A*jointHeight p.1.1 p.1.2 p.2^J) →
      Integrable (fun p => G p*onLines W0 W1 σ ξ υ p) heightMeasure ∧
      ∀T : ℝ, 0≤T →
      (∫p : HeightSpace in outsideBox T, ‖G p*onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)
        ≤ A*K/(1+T)^N := by
  obtain ⟨K,hK,hT⟩ := profile_uniform_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  obtain ⟨K0,hK0,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ A hA G hG hbound
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ ξ υ (hzlo.trans_le hξ.1) G hG A J hbound
  refine ⟨hi,?_⟩
  intro T hT0
  calc
    _ ≤ ∫p : HeightSpace in outsideBox T,
        A*(jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖) ∂heightMeasure := by
      apply setIntegral_mono_on hi.norm.integrableOn
        (((hM σ hσ ξ hξ υ hυ).1).const_mul A).integrableOn (outsideBox_measurable T)
      intro p hp
      rw [norm_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg _)
    _ = A*(∫p : HeightSpace in outsideBox T,
        jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure) :=
      integral_const_mul _ _
    _ ≤ A*(K/(1+T)^N) := mul_le_mul_of_nonneg_left (hT σ hσ ξ hξ υ hυ T hT0) hA
    _ = _ := by ring

theorem profile_arithmetic_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀axis : SliceAxis, ∀T A : ℝ, 0≤A → ∀G : ℝ×ℝ → ℂ,
      AEStronglyMeasurable G (volume.prod volume) →
      (∀q, ‖G q‖≤A*jointHeight (sliceMap axis T q).1.1
        (sliceMap axis T q).1.2 (sliceMap axis T q).2^J) →
      Integrable (fun q => G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ, ‖G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume)
        ≤ A*K/height T^N := by
  obtain ⟨K,hK,hM⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ axis T A hA G hG hbound
  obtain ⟨hm,hmb⟩ := hM σ hσ ξ hξ υ hυ axis T
  have hdom (q : ℝ×ℝ) : ‖G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)‖≤
      A*(jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
        (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) := by
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound q) (norm_nonneg _)
  have hi : Integrable (fun q => G q*onLines W0 W1 σ ξ υ (sliceMap axis T q))
      (volume.prod volume) := by
    apply (hm.const_mul A).mono'
    · exact hG.mul (((onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ
        (hzlo.trans_le hξ.1)).comp (sliceMap_continuous axis T)).aestronglyMeasurable)
    · exact Eventually.of_forall hdom
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫q : ℝ×ℝ,
        A*(jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
          (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) ∂volume.prod volume :=
      integral_mono hi.norm (hm.const_mul A) hdom
    _ = A*(∫q : ℝ×ℝ,
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
          (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume) :=
      integral_const_mul _ _
    _ ≤ A*(K/height T^N) := mul_le_mul_of_nonneg_left hmb hA
    _ = _ := by ring

theorem profile_arithmetic_fubini (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1) (σ ξ υ : ℝ) (hξ : 0<ξ)
    (G : HeightSpace → ℂ) (hG : AEStronglyMeasurable G heightMeasure) (A : ℝ) (J : ℕ)
    (hbound : ∀p, ‖G p‖≤A*jointHeight p.1.1 p.1.2 p.2^J) :
    ((∫p : HeightSpace, G p*onLines W0 W1 σ ξ υ p ∂heightMeasure) =
      ∫τ : ℝ, ∫ν : ℝ, ∫ω : ℝ, G ((τ,ν),ω)*onLines W0 W1 σ ξ υ ((τ,ν),ω)) ∧
    ((∫p : HeightSpace, G p*onLines W0 W1 σ ξ υ p ∂heightMeasure) =
      ∫ω : ℝ, ∫ν : ℝ, ∫τ : ℝ, G ((τ,ν),ω)*onLines W0 W1 σ ξ υ ((τ,ν),ω)) := by
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ ξ υ hξ G hG A J hbound
  constructor
  · rw [integral_prod _ hi]
    exact integral_prod _ hi.integral_prod_left
  · rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with ω hω
    exact integral_prod_symm _ hω

end SevenEighths.ProbeMellinBoundary

end

end OAI

end Source1091

/- Original source: OAI/NumberTheory/DirichletL/Detector/InitialMajorant.lean; sha256: 7437017a8ba8545bb3daf0cf74a2560b2cb1a406532469fa44a06c58026d2ba9 -/
section Source1092
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein ProbeRow
attribute [local fun_prop] fullIdealWeight_continuous
local notation "O" => ActualEisensteinCubic.O
abbrev FullHighIndex := NonzeroFrequency×((Ideal O×Ideal O)×(Ideal O×Ideal O))

def initialHighMajorant (σ υ ξ : ℝ) (p : FullHighIndex) : ℝ :=
  ‖frequencyWeight (ξ:ℂ) p.1‖*highAbsoluteMajorant (σ:ℂ) (υ:ℂ) (ξ:ℂ) p.2

lemma initialHighMajorant_nonneg (σ υ ξ : ℝ) (p : FullHighIndex) :
    0≤ initialHighMajorant σ υ ξ p := mul_nonneg (norm_nonneg _) (highAbsoluteMajorant_nonneg _ _ _ _)

lemma initialHighMajorant_summable (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ) :
    Summable (initialHighMajorant σ υ ξ) := by
  exact (frequencyWeight_summable_norm (ξ:ℂ) hξ).mul_of_nonneg
    (highAbsoluteMajorant_summable (σ:ℂ) (υ:ℂ) (ξ:ℂ) hσ hυ (by simpa using (show (1/6:ℝ)<ξ by linarith)))
    (fun _=>norm_nonneg _) (highAbsoluteMajorant_nonneg _ _ _)

lemma frequencyWeight_norm_eq_of_re (z z' : ℂ) (h : z.re=z'.re) (H : NonzeroFrequency) :
    ‖frequencyWeight z H‖=‖frequencyWeight z' H‖ := by simp only [frequencyWeight_norm,h]

lemma highAbsoluteMajorant_eq_of_re (x w z x' w' z' : ℂ)
    (hx : x.re=x'.re) (hw : w.re=w'.re) (hz : z.re=z'.re)
    (p : (Ideal O×Ideal O)×(Ideal O×Ideal O)) :
    highAbsoluteMajorant x w z p=highAbsoluteMajorant x' w' z' p := by
  unfold highAbsoluteMajorant
  rw [fullIdealWeight_norm_eq_of_re (x-1/2) (x'-1/2) (by simp [hx]),
    fullIdealWeight_norm_eq_of_re (3*x-2) (3*x'-2) (by simp [hx]),
    fullIdealWeight_norm_eq_of_re (w-1) (w'-1) (by simp [hw]),
    fullIdealWeight_norm_eq_of_re (6*z) (6*z') (by simp [hz])]

def fullHighCoefficient (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (x w z : ℂ) (p : FullHighIndex) : ℂ :=
  mask p.1*frequencyWeight z p.1*
    markedIdealHighSummand S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2

lemma fullHighCoefficient_norm_le (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1) (x w z : ℂ)
    (σ υ ξ : ℝ) (hx : x.re=σ) (hw : w.re=υ) (hz : z.re=ξ) (p : FullHighIndex) :
    ‖fullHighCoefficient S D η mask x w z p‖≤ initialHighMajorant σ υ ξ p := by
  unfold fullHighCoefficient
  rw [norm_mul,norm_mul]
  have hb := (markedIdealHighSummand_norm_le S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2).trans
    (bareIdealHighSummand_norm_le η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
  calc
    _ ≤ (1*‖frequencyWeight z p.1‖)*highAbsoluteMajorant x w z p.2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hm _) (norm_nonneg _)) hb (norm_nonneg _) (by positivity)
    _ = initialHighMajorant σ υ ξ p := by
      rw [one_mul,frequencyWeight_norm_eq_of_re z (ξ:ℂ) hz,
        highAbsoluteMajorant_eq_of_re x w z (σ:ℂ) (υ:ℂ) (ξ:ℂ) hx hw hz]
      rfl

lemma fullHighCoefficient_continuous (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (p : FullHighIndex) :
    Continuous (fun q : (ℂ × ℂ) × ℂ => fullHighCoefficient S D η mask q.1.1 q.1.2 q.2 p) := by
  have hH : (elementNorm p.1.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (elementNorm_pos _ p.1.property).ne'
  unfold fullHighCoefficient frequencyWeight markedIdealHighSummand bareIdealHighSummand
  have hc : Continuous (fun q : (ℂ × ℂ) × ℂ => (elementNorm p.1.val:ℂ)^(-q.2)) :=
    continuous_snd.neg.const_cpow (Or.inl hH)
  have h1 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight (q.1.1+1/2) p.2.1.1) :=
    (fullIdealWeight_continuous _).comp (by fun_prop)
  have h2 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight (1+3*q.1.1) p.2.1.2) :=
    (fullIdealWeight_continuous _).comp (by fun_prop)
  have h3 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight q.1.2 p.2.2.1) :=
    (fullIdealWeight_continuous _).comp (by fun_prop)
  have h4 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight (6*q.2) p.2.2.2) :=
    (fullIdealWeight_continuous _).comp (by fun_prop)
  exact (continuous_const.mul hc).mul
    (continuous_const.mul ((((continuous_const.mul h1).mul h2).mul h3).mul h4))

end SevenEighths.ProbePhysical
end

end OAI

end Source1092

/- Original source: OAI/NumberTheory/DirichletL/Detector/InitialIntegral.lean; sha256: 9bbd62b5960f39b5a751a8ea56feb10dd4ed33bfa3822c7e30f0fe8e3e83afaa -/
section Source1093
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def initialHighOnLines (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (σ υ ξ : ℝ) (i : FullHighIndex) (p : HeightSpace) : ℂ :=
  fullHighCoefficient S D η mask ((σ:ℂ)+p.1.1*Complex.I)
    ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) i

lemma initialHighOnLines_continuous (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (σ υ ξ : ℝ) (i : FullHighIndex) :
    Continuous (initialHighOnLines S D η mask σ υ ξ i) := by
  unfold initialHighOnLines
  have hc : Continuous (fun p : HeightSpace =>
      (((σ:ℂ)+p.1.1*Complex.I,(υ:ℂ)+p.2*Complex.I),(ξ:ℂ)+p.1.2*Complex.I)) := by fun_prop
  have hh := (fullHighCoefficient_continuous S D η mask i).comp hc
  simpa only [Function.comp_def] using hh

lemma initialHighOnLines_norm_le (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1) (σ υ ξ : ℝ)
    (i : FullHighIndex) (p : HeightSpace) :
    ‖initialHighOnLines S D η mask σ υ ξ i p‖≤ initialHighMajorant σ υ ξ i := by
  exact fullHighCoefficient_norm_le S D η mask hm _ _ _ σ υ ξ (by simp) (by simp) (by simp) i

lemma initial_profile_integrable (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1) (σ ξ υ : ℝ) (hξ : 0<ξ) :
    Integrable (onLines W0 W1 σ ξ υ) heightMeasure := by
  simpa only [one_mul] using profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ ξ υ hξ (fun _=>1) aestronglyMeasurable_const 1 0 (fun _=>by simp)

theorem initialHigh_integral_tsum (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ) :
    (∫p,∑'i : FullHighIndex, initialHighOnLines S D η mask σ υ ξ i p*
      onLines W0 W1 σ ξ υ p ∂heightMeasure)=
      ∑'i : FullHighIndex, ∫p,initialHighOnLines S D η mask σ υ ξ i p*
        onLines W0 W1 σ ξ υ p ∂heightMeasure := by
  have hξ0 : 0<ξ := by linarith
  have hp := initial_profile_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 σ ξ υ hξ0
  let F := fun i p=>initialHighOnLines S D η mask σ υ ξ i p*onLines W0 W1 σ ξ υ p
  have hb (i : FullHighIndex) (p : HeightSpace) :
      ‖F i p‖≤ initialHighMajorant σ υ ξ i*‖onLines W0 W1 σ ξ υ p‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (initialHighOnLines_norm_le S D η mask hm σ υ ξ i p) (norm_nonneg _)
  have hF (i : FullHighIndex) : Integrable (F i) heightMeasure := by
    apply (hp.norm.const_mul (initialHighMajorant σ υ ξ i)).mono'
    · exact ((initialHighOnLines_continuous S D η mask σ υ ξ i).mul
        (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ hξ0)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hb i)
  have hsum : Summable (fun i : FullHighIndex=>∫p,‖F i p‖ ∂heightMeasure) := by
    apply Summable.of_nonneg_of_le (fun i=>integral_nonneg (fun _=>norm_nonneg _))
      (fun i=>?_) ((initialHighMajorant_summable σ υ ξ hσ hυ hξ).mul_right
        (∫p,‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure))
    rw [←integral_const_mul]
    exact integral_mono (hF i).norm (hp.norm.const_mul _) (hb i)
  exact (integral_tsum_of_summable_integral_norm hF hsum).symm

theorem initialHigh_integral_tsum_test (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) :
    (∫p,∑'i : FullHighIndex, initialHighOnLines S D η mask σ υ ξ i p*T p ∂heightMeasure)=
      ∑'i : FullHighIndex, ∫p,initialHighOnLines S D η mask σ υ ξ i p*T p ∂heightMeasure := by
  let F := fun i p=>initialHighOnLines S D η mask σ υ ξ i p*T p
  have hb (i : FullHighIndex) (p : HeightSpace) :
      ‖F i p‖≤ initialHighMajorant σ υ ξ i*‖T p‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (initialHighOnLines_norm_le S D η mask hm σ υ ξ i p) (norm_nonneg _)
  have hF (i : FullHighIndex) : Integrable (F i) heightMeasure := by
    apply (hT.norm.const_mul (initialHighMajorant σ υ ξ i)).mono'
    · exact (initialHighOnLines_continuous S D η mask σ υ ξ i).aestronglyMeasurable.mul hT.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hb i)
  have hsum : Summable (fun i : FullHighIndex=>∫p,‖F i p‖ ∂heightMeasure) := by
    apply Summable.of_nonneg_of_le (fun i=>integral_nonneg (fun _=>norm_nonneg _))
      (fun i=>?_) ((initialHighMajorant_summable σ υ ξ hσ hυ hξ).mul_right
        (∫p,‖T p‖ ∂heightMeasure))
    rw [←integral_const_mul]
    exact integral_mono (hF i).norm (hT.norm.const_mul _) (hb i)
  exact (integral_tsum_of_summable_integral_norm hF hsum).symm

end SevenEighths.ProbePhysical
end

end OAI

end Source1093

/- Original source: OAI/NumberTheory/DirichletL/Detector/InitialScales.lean; sha256: 61a16a34794fce8a386ee05aca2e96af394ff74c46ff4921c5dff1dd326ab5a2 -/
section Source1094
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary

def sourceScale (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)

lemma sourceMellinWeight_eq_scale (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z x w z=sourceScale X Y Z x w z*profile W0 W1 x w z := by
  unfold sourceMellinWeight sourceScale profile
  ring

lemma sourceScale_continuous (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Continuous (fun q : (ℂ × ℂ) × ℂ =>sourceScale X Y Z q.1.1 q.1.2 q.2) := by
  have hx : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  unfold sourceScale
  exact (((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ =>(1/2:ℂ)-q.2)).const_cpow (Or.inl hx)).mul
    (((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ =>q.1.1+q.2-1)).const_cpow (Or.inl hz)))) |>.mul
      ((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ =>q.1.2-1)).const_cpow (Or.inl hy))

lemma sourceScale_norm (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (x w z : ℂ) :
    ‖sourceScale X Y Z x w z‖=X^(1/2-z.re)*Z^(x.re+z.re-1)*Y^(w.re-1) := by
  simp only [sourceScale,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
    Complex.norm_cpow_eq_rpow_re_of_pos hY,Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  norm_num [Complex.sub_re,Complex.add_re]

theorem sourceMellinWeight_initial_integrable (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ ξ υ : ℝ) (hξ : 0<ξ) :
    Integrable (fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  let G := fun p : HeightSpace=>sourceScale X Y Z
    ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I)
  have hc0 := (sourceScale_continuous X Y Z hX hY hZ).comp
    (show Continuous (fun p : HeightSpace=>(((σ:ℂ)+p.1.1*Complex.I,(υ:ℂ)+p.2*Complex.I),
      (ξ:ℂ)+p.1.2*Complex.I)) by fun_prop)
  have hc : Continuous G := by simpa only [G,Function.comp_def] using hc0
  have hb (p : HeightSpace) : ‖G p‖≤(X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1))*jointHeight p.1.1 p.1.2 p.2^0 := by
    simp only [G,sourceScale_norm X Y Z hX hY hZ]
    simp
  simpa only [sourceMellinWeight_eq_scale,onLines,G] using
    profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 σ ξ υ hξ G
      hc.aestronglyMeasurable _ 0 hb

lemma sourceMellinWeight_initial_continuous (W0 W1 : SchwartzMap ℝ ℂ)
    (a1 b1 : ℝ) (ha1 : 0<a1) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ ξ υ : ℝ) (hξ : 0<ξ) :
    Continuous (fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I)) := by
  have hc := (sourceScale_continuous X Y Z hX hY hZ).comp
    (show Continuous (fun p : HeightSpace=>(((σ:ℂ)+p.1.1*Complex.I,(υ:ℂ)+p.2*Complex.I),
      (ξ:ℂ)+p.1.2*Complex.I)) by fun_prop)
  simpa only [Function.comp_def,Pi.mul_def,sourceMellinWeight_eq_scale,onLines] using
    hc.mul (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ hξ)

end SevenEighths.ProbePhysical
end

end OAI

end Source1094

/- Original source: OAI/NumberTheory/DirichletL/Detector/InitialFubini.lean; sha256: dff0235ae0f994e42ea2dd0ab782aaf4b80ce5e13d5a4a827972bb94a2248b9b -/
section Source1095
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O

theorem source_initial_integral_tsum (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ) :
    (∫p : HeightSpace,∑'i : FullHighIndex, initialHighOnLines S D η mask σ υ ξ i p*
      sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure)=
      ∑'i : FullHighIndex, ∫p : HeightSpace,initialHighOnLines S D η mask σ υ ξ i p*
        sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
          ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure := by
  exact initialHigh_integral_tsum_test S D η mask hm σ υ ξ hσ hυ hξ _
    (sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ σ ξ υ (by linarith))

end SevenEighths.ProbePhysical
end

end OAI

end Source1095

/- Original source: OAI/NumberTheory/DirichletL/Detector/InitialSubseries.lean; sha256: 5b4fe96e6947c39f7dc52d0857e3480fc7d4995d9d269f89f2a6d3392d5b2dcc -/
section Source1096
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O

abbrev RawHighIndex := NonzeroFrequency×((Ideal O×Ideal O)×Ideal O)

def rawHighEmbedding (p : RawHighIndex) : FullHighIndex := (p.1,(p.2.1,(p.2.2,1)))

lemma rawHighEmbedding_injective : Function.Injective rawHighEmbedding := by
  rintro ⟨h,⟨ij,k⟩⟩ ⟨h',⟨ij',k'⟩⟩ he
  simpa only [rawHighEmbedding,Prod.mk.injEq,and_true] using he

theorem initialHigh_integral_tsum_subseries {ι : Type*} [Countable ι]
    (e : ι→FullHighIndex) (he : Function.Injective e)
    (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) :
    (∫p,∑'i : ι, initialHighOnLines S D η mask σ υ ξ (e i) p*T p ∂heightMeasure)=
      ∑'i : ι, ∫p,initialHighOnLines S D η mask σ υ ξ (e i) p*T p ∂heightMeasure := by
  let F := fun i p=>initialHighOnLines S D η mask σ υ ξ (e i) p*T p
  have hb (i : ι) (p : HeightSpace) :
      ‖F i p‖≤ initialHighMajorant σ υ ξ (e i)*‖T p‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (initialHighOnLines_norm_le S D η mask hm σ υ ξ (e i) p) (norm_nonneg _)
  have hF (i : ι) : Integrable (F i) heightMeasure := by
    apply (hT.norm.const_mul (initialHighMajorant σ υ ξ (e i))).mono'
    · exact (initialHighOnLines_continuous S D η mask σ υ ξ (e i)).aestronglyMeasurable.mul hT.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hb i)
  have hsum : Summable (fun i : ι=>∫p,‖F i p‖ ∂heightMeasure) := by
    apply Summable.of_nonneg_of_le (fun i=>integral_nonneg (fun _=>norm_nonneg _))
      (fun i=>?_) (((initialHighMajorant_summable σ υ ξ hσ hυ hξ).comp_injective he).mul_right
        (∫p,‖T p‖ ∂heightMeasure))
    rw [←integral_const_mul]
    exact integral_mono (hF i).norm (hT.norm.const_mul _) (hb i)
  exact (integral_tsum_of_summable_integral_norm hF hsum).symm

end SevenEighths.ProbePhysical
end

end OAI

end Source1096

/- Original source: OAI/NumberTheory/DirichletL/Detector/InitialProduct.lean; sha256: d05765a7030675146a694fda3a16483ac4f593de9a0e231bfe749a13270a3ab3 -/
section Source1097
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O

theorem initialHigh_counting_product_integrable {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (e : ι→FullHighIndex) (he : Function.Injective e)
    (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) (hcT : Continuous T) :
    Integrable (fun p : ι×HeightSpace=>initialHighOnLines S D η mask σ υ ξ (e p.1) p.2*T p.2)
      ((Measure.count:Measure ι).prod heightMeasure) := by
  have hb : Integrable (fun i : ι=>initialHighMajorant σ υ ξ (e i)) Measure.count := by
    rw [integrable_count_iff]
    simpa only [Function.comp_def,Real.norm_eq_abs,abs_of_nonneg (initialHighMajorant_nonneg _ _ _ _)] using
      (initialHighMajorant_summable σ υ ξ hσ hυ hξ).comp_injective he
  apply (hb.mul_prod hT.norm).mono'
  · apply Measurable.aestronglyMeasurable
    apply measurable_from_prod_countable_right
    intro i
    exact ((initialHighOnLines_continuous S D η mask σ υ ξ (e i)).mul hcT).measurable
  · apply Filter.Eventually.of_forall
    intro p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (initialHighOnLines_norm_le S D η mask hm σ υ ξ (e p.1) p.2) (norm_nonneg _)

end SevenEighths.ProbePhysical
end

end OAI

end Source1097

/- Original source: OAI/NumberTheory/DirichletL/Detector/ContourShear.lean; sha256: 77dc612bf332da5325252d52e0499fb9069c4f8424553ab6f5d6b3667e320c23 -/
section Source1098
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary

def sourceHeightShear : HeightSpace ≃ᵐ HeightSpace where
  toFun p := ((p.1.1+p.1.2,p.1.2),p.2)
  invFun p := ((p.1.1-p.1.2,p.1.2),p.2)
  left_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  right_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  measurable_toFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1+p.1.2,p.1.2),p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1-p.1.2,p.1.2),p.2))
    fun_prop

lemma sourceHeightShear_preserving : MeasurePreserving sourceHeightShear heightMeasure heightMeasure := by
  exact (measurePreserving_add_prod (volume:Measure ℝ) volume).prod (MeasurePreserving.id volume)

lemma sourceHeightShear_integral (F : HeightSpace→ℂ) :
    (∫p,F (sourceHeightShear p) ∂heightMeasure)=∫p,F p ∂heightMeasure :=
  sourceHeightShear_preserving.integral_comp' F

theorem source_contour_shear (F : ℂ→ℂ→ℂ→ℂ) (σ ξ υ : ℝ) :
    (∫p : HeightSpace,F (((σ:ℂ)+p.1.1*Complex.I)+((ξ:ℂ)+p.1.2*Complex.I)-1)
      ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure)=
    ∫p : HeightSpace,F (((σ+ξ-1:ℝ):ℂ)+p.1.1*Complex.I)
      ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure := by
  have hh := sourceHeightShear_integral (fun p : HeightSpace=>F
    (((σ+ξ-1:ℝ):ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I))
  convert hh using 1
  congr 1
  funext p
  dsimp only [sourceHeightShear,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk]
  congr 2 ; push_cast ; ring

lemma sourceMellinWeight_shear (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (t w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z (t+1-z) w z=
      (X:ℂ)^(1/2-z)*(Z:ℂ)^t*(Y:ℂ)^(w-1)*Complex.exp (t^2)*
        mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*mellin W1 w := by
  simp only [sourceMellinWeight,show t+1-z+z-1=t by ring]

end SevenEighths.ProbePhysical
end

end OAI

end Source1098

/- Original source: OAI/NumberTheory/DirichletL/Detector/RawMellinTerm.lean; sha256: 2cdf3d37bc5185e66155dee24e9c441a4a5346c081b888e1bd461b152e206058 -/
section Source1099
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CanonicalQuadraticSieve CubicEisenstein
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def rawPhysicalMellinTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J K : Ideal O) (hK : Supported K)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (H : O) (t w z : ℂ) : ℂ :=
  physicalMellinCoefficientTerm η C S D I J (primaryGenerator K)
    ((supported_span_primaryGenerator_iff K).mpr hK) X H t z *fullIdealWeight w K*
    (Y:ℂ)^(w-1)*(Z:ℂ)^t*Complex.exp (t^2)*mellin (paperRadialFourier W0) z*mellin W1 w

theorem rawPhysicalMellinTerm_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D I J K : Ideal O) (hK : Supported K)
    (hKS : ∀P∈S,¬P∣K) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (H : NonzeroFrequency) (t w z : ℂ) :
    rawPhysicalMellinTerm η (calibrationForSet S hS) S D I J K hK W0 W1 X Y Z H.val t w z=
      sourceMellinWeight W0 W1 X Y Z (t+1-z) w z *
        fullHighCoefficient S D η (fun h=>star ((calibrationForSet S hS).residueMonoid h.val))
          (t+1-z) w z (rawHighEmbedding (H,((I,J),K))) := by
  have hcs : IsCoprime (calibrationForSet S hS).generator (primaryGenerator K) := by
    apply calibrationForSet_coprime_of_excluded S hS
    rw [(primaryGenerator_spec K (supported_primaryGenerator_ne_zero K hK)).1]
    exact hKS
  unfold rawPhysicalMellinTerm
  rw [physicalMellinCoefficientTerm_eq_guarded η S hS hbad D I J (primaryGenerator K)
    ((supported_span_primaryGenerator_iff K).mpr hK) hcs X hX H.val H.property t z,
    guardedHighMellinCoefficient_eq_high η (calibrationForSet S hS) S hpS D I J K hK hKS X H.val
      (t+1-z) w z,sourceMellinWeight_shear]
  simp only [fullHighCoefficient,frequencyWeight,rawHighEmbedding]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1099

/- Original source: OAI/NumberTheory/DirichletL/Detector/RawPhysicalIntegral.lean; sha256: c9f886288938c7e375ea3385ae6b70c526e2f3f260751b06af2799d3f5b071ac -/
section Source1100
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def SourceRawIndex (S : Finset (Ideal O)) :=
  {p : RawHighIndex // Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2}

instance (S : Finset (Ideal O)) : Countable (SourceRawIndex S) := inferInstanceAs (Countable {_p : RawHighIndex // _})

def sourceRawEmbedding (S : Finset (Ideal O)) (i : SourceRawIndex S) : FullHighIndex :=
  rawHighEmbedding i.val

lemma sourceRawEmbedding_injective (S : Finset (Ideal O)) : Function.Injective (sourceRawEmbedding S) :=
  rawHighEmbedding_injective.comp Subtype.val_injective

def originalRawOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (i : SourceRawIndex S) (p : HeightSpace) : ℂ :=
  rawPhysicalMellinTerm η (calibrationForSet S hS) S D i.val.2.1.1 i.val.2.1.2 i.val.2.2 i.property.1
    W0 W1 X Y Z i.val.1.val ((4:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)

theorem originalRaw_counting_product_integrable (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun p : SourceRawIndex S×HeightSpace=>originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  let mask := fun H : NonzeroFrequency=>star ((calibrationForSet S hS).residueMonoid H.val)
  have hm (H : NonzeroFrequency) : ‖mask H‖≤1 := by
    simpa only [mask,norm_star] using (calibrationForSet S hS).residueMonoid_norm_le_one H.val
  let T := fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
    ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)
  have hT : Integrable T heightMeasure := sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ 3 2 3 (by norm_num)
  have hcT : Continuous T := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1
    X Y Z hX hY hZ 3 2 3 (by norm_num)
  have hi := initialHigh_counting_product_integrable (sourceRawEmbedding S) (sourceRawEmbedding_injective S)
    S D η mask hm 3 3 2 (by norm_num) (by norm_num) (by norm_num) T hT hcT
  have hp := (MeasurePreserving.id (Measure.count:Measure (SourceRawIndex S))).prod
    (sourceHeightShear_preserving.symm sourceHeightShear)
  have hh := hp.integrable_comp_of_integrable hi
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro p
  dsimp only [Function.comp_def,Prod.map]
  rw [originalRawOnLines,rawPhysicalMellinTerm_eq_source η S hS hpS hbad D _ _ _ p.1.property.1
    p.1.property.2 W0 W1 X Y Z hX p.1.val.1]
  have he : (4:ℂ)+p.2.1.1*Complex.I+1-((2:ℂ)+p.2.1.2*Complex.I)=
      3+((p.2.1.1-p.2.1.2:ℝ):ℂ)*Complex.I := by push_cast;ring
  have hsh : sourceHeightShear.symm p.2=((p.2.1.1-p.2.1.2,p.2.1.2),p.2.2) := rfl
  simp only [he,initialHighOnLines,T,hsh,sourceRawEmbedding,mask,id_eq,Complex.ofReal_ofNat]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1100

/- Original source: OAI/NumberTheory/DirichletL/Detector/MixedFubini.lean; sha256: f33ed12c2275149b14d917ce28452ee59bd727409cda397f61d4961ba9ca2668 -/
section Source1101
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical

lemma count_product {A B : Type*} [Countable A] [Countable B]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    (Measure.count:Measure A).prod (Measure.count:Measure B)=Measure.count := by
  apply Measure.ext_of_singleton
  rintro ⟨a,b⟩
  rw [←Set.singleton_prod_singleton,Measure.prod_prod]
  simp

lemma count_equiv_preserving {A B : Type*} [Countable A] [Countable B]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (e : A≃ᵐB) : MeasurePreserving e Measure.count Measure.count := by
  refine ⟨e.measurable,?_⟩
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply e.measurable (measurableSet_singleton b)]
  have he : e ⁻¹' {b}={e.symm b} := by ext a;simp [e.eq_symm_apply]
  rw [he]
  simp

def quadShuffle {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] : (A×B)×(C×D) ≃ᵐ (A×C)×(B×D) where
  toFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  invFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  left_inv p := rfl
  right_inv p := rfl
  measurable_toFun := by change Measurable (fun p : (A×B)×(C×D)=>((p.1.1,p.2.1),(p.1.2,p.2.2)));fun_prop
  measurable_invFun := by change Measurable (fun p : (A×C)×(B×D)=>((p.1.1,p.2.1),(p.1.2,p.2.2)));fun_prop

lemma quadShuffle_preserving {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μA : Measure A) (μB : Measure B)
    (μC : Measure C) (μD : Measure D) [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] :
    MeasurePreserving (quadShuffle : (A×B)×(C×D) ≃ᵐ (A×C)×(B×D))
      ((μA.prod μB).prod (μC.prod μD)) ((μA.prod μC).prod (μB.prod μD)) := by
  have h1 := measurePreserving_prodAssoc μA μB (μC.prod μD)
  have h2 := (MeasurePreserving.id μA).prod ((measurePreserving_prodAssoc μB μC μD).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id μA).prod
    ((Measure.measurePreserving_swap (μ:=μB) (ν:=μC)).prod (MeasurePreserving.id μD))
  have h4 := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μC μB μD)
  have h5 := (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm MeasurableEquiv.prodAssoc
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

def physicalNestingEquiv {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F] :
    (A×(B×C))×((D×E)×F) ≃ᵐ A×(F×(D×(B×(E×C)))) where
  toFun p := (p.1.1,(p.2.2,(p.2.1.1,(p.1.2.1,(p.2.1.2,p.1.2.2)))))
  invFun p := ((p.1,(p.2.2.2.1,p.2.2.2.2.2)),((p.2.2.1,p.2.2.2.2.1),p.2.1))
  left_inv p := rfl
  right_inv p := rfl
  measurable_toFun := by
    change Measurable (fun p : (A×(B×C))×((D×E)×F)=>
      (p.1.1,(p.2.2,(p.2.1.1,(p.1.2.1,(p.2.1.2,p.1.2.2))))))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : A×(F×(D×(B×(E×C))))=>
      ((p.1,(p.2.2.2.1,p.2.2.2.2.2)),((p.2.2.1,p.2.2.2.2.1),p.2.1)))
    fun_prop

lemma physicalNesting_preserving {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F]
    (μA : Measure A) (μB : Measure B) (μC : Measure C)
    (μD : Measure D) (μE : Measure E) (μF : Measure F)
    [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] [SFinite μE] [SFinite μF] :
    MeasurePreserving (physicalNestingEquiv : (A×(B×C))×((D×E)×F) ≃ᵐ A×(F×(D×(B×(E×C)))))
      ((μA.prod (μB.prod μC)).prod ((μD.prod μE).prod μF))
      (μA.prod (μF.prod (μD.prod (μB.prod (μE.prod μC))))) := by
  have h1 := measurePreserving_prodAssoc μA (μB.prod μC) ((μD.prod μE).prod μF)
  have hr := (Measure.measurePreserving_swap (μ:=(μB.prod μC).prod (μD.prod μE)) (ν:=μF)).comp
    ((measurePreserving_prodAssoc (μB.prod μC) (μD.prod μE) μF).symm MeasurableEquiv.prodAssoc)
  have hq := quadShuffle_preserving μB μC μD μE
  have hs := (Measure.measurePreserving_swap (μ:=μB) (ν:=μD)).prod
    (Measure.measurePreserving_swap (μ:=μC) (ν:=μE))
  have ha := measurePreserving_prodAssoc μD μB (μE.prod μC)
  exact ((MeasurePreserving.id μA).prod
    (((MeasurePreserving.id μF).prod (ha.comp (hs.comp hq))).comp hr)).comp h1

lemma integral_count_eq_tsum {A : Type*} [Countable A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (f : A→ℂ) (hf : Integrable f Measure.count) :
    (∫a,f a ∂Measure.count)=∑'a,f a := by
  simpa using integral_countable hf

theorem integral_physical_nesting {A B C : Type*} [Countable A] [Countable B] [Countable C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (F : A×(ℝ×(ℝ×(B×(ℝ×C))))→ℂ)
    (hF : Integrable F ((Measure.count:Measure A).prod (volume.prod (volume.prod
      ((Measure.count:Measure B).prod (volume.prod (Measure.count:Measure C))))))) :
    (∫p,F p ∂((Measure.count:Measure A).prod (volume.prod (volume.prod
      ((Measure.count:Measure B).prod (volume.prod (Measure.count:Measure C)))))))=
      ∑'a : A,∫w : ℝ,∫t : ℝ,∑'b : B,∫z : ℝ,∑'c : C,F (a,(w,(t,(b,(z,c))))) := by
  rw [integral_prod _ hF,integral_count_eq_tsum _ hF.integral_prod_left]
  apply tsum_congr
  intro a
  have ha := (Measure.ae_count_iff.mp hF.prod_right_ae) a
  rw [integral_prod _ ha]
  apply integral_congr_ae
  filter_upwards [ha.prod_right_ae] with w hw
  rw [integral_prod _ hw]
  apply integral_congr_ae
  filter_upwards [hw.prod_right_ae] with t ht
  rw [integral_prod _ ht,integral_count_eq_tsum _ ht.integral_prod_left]
  apply tsum_congr
  intro b
  have hb := (Measure.ae_count_iff.mp ht.prod_right_ae) b
  rw [integral_prod _ hb]
  apply integral_congr_ae
  filter_upwards [hb.prod_right_ae] with z hz
  exact integral_count_eq_tsum _ hz

end SevenEighths.ProbePhysical
end

end OAI

end Source1101

/- Original source: OAI/NumberTheory/DirichletL/Detector/RawIndexGrouping.lean; sha256: 0ffc2e3e81d7aae068d057cea7adc8d93263c5d5dd6aad75ec346c76a154a357 -/
section Source1102
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

abbrev SourceOuter (S : Finset (Ideal O)) := {K : Ideal O // Supported K ∧ ∀P∈S,¬P∣K}
abbrev CompletedPair := Ideal O×Ideal O

def sourceRawGrouping (S : Finset (Ideal O)) :
    SourceRawIndex S ≃ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toFun i := (⟨i.val.2.2,i.property⟩,(i.val.2.1,i.val.1))
  invFun i := ⟨(i.2.2,(i.2.1,i.1.val)),i.1.property⟩
  left_inv _i := rfl
  right_inv _i := rfl

def sourceRawGroupingMeasurable (S : Finset (Ideal O))
    [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    [MeasurableSpace (SourceOuter S)] [MeasurableSingletonClass (SourceOuter S)]
    [MeasurableSpace CompletedPair] [MeasurableSingletonClass CompletedPair]
    [MeasurableSpace NonzeroFrequency] [MeasurableSingletonClass NonzeroFrequency] :
    SourceRawIndex S ≃ᵐ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toEquiv := sourceRawGrouping S
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

lemma sourceRawGrouping_preserving (S : Finset (Ideal O))
    [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    [MeasurableSpace (SourceOuter S)] [MeasurableSingletonClass (SourceOuter S)]
    [MeasurableSpace CompletedPair] [MeasurableSingletonClass CompletedPair]
    [MeasurableSpace NonzeroFrequency] [MeasurableSingletonClass NonzeroFrequency] :
    MeasurePreserving (sourceRawGroupingMeasurable S) Measure.count
      ((Measure.count:Measure (SourceOuter S)).prod
        ((Measure.count:Measure CompletedPair).prod (Measure.count:Measure NonzeroFrequency))) := by
  rw [count_product,count_product]
  exact count_equiv_preserving _

end SevenEighths.ProbePhysical
end

end OAI

end Source1102

/- Original source: OAI/NumberTheory/DirichletL/Detector/RawNesting.lean; sha256: 44ab74af47d525a729adcbd7e1addbf26bbcc674ffdcc8182d07d59162d13713 -/
section Source1103
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance : MeasurableSpace O := ⊤
local instance : MeasurableSingletonClass O := ⟨fun _=>trivial⟩
local instance : MeasurableSpace (Ideal O) := ⊤
local instance : MeasurableSingletonClass (Ideal O) := ⟨fun _=>trivial⟩

local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩

abbrev PhysicalNestedSpace (S : Finset (Ideal O)) := SourceOuter S×(ℝ×(ℝ×(CompletedPair×(ℝ×NonzeroFrequency))))

def physicalRawNesting (S : Finset (Ideal O)) : SourceRawIndex S×HeightSpace ≃ᵐ PhysicalNestedSpace S :=
  ((sourceRawGroupingMeasurable S).prodCongr (MeasurableEquiv.refl HeightSpace)).trans physicalNestingEquiv

lemma physicalRawNesting_preserving (S : Finset (Ideal O)) :
    MeasurePreserving (physicalRawNesting S)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)
      ((Measure.count:Measure (SourceOuter S)).prod (volume.prod (volume.prod
        ((Measure.count:Measure CompletedPair).prod (volume.prod (Measure.count:Measure NonzeroFrequency)))))) := by
  exact (physicalNesting_preserving Measure.count Measure.count Measure.count volume volume volume).comp
    ((sourceRawGrouping_preserving S).prod (MeasurePreserving.id heightMeasure))

def originalNestedOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (p : PhysicalNestedSpace S) : ℂ :=
  originalRawOnLines η S hS D W0 W1 X Y Z
    ⟨(p.2.2.2.2.2,(p.2.2.2.1,p.1.val)),p.1.property⟩ ((p.2.2.1,p.2.2.2.2.1),p.2.1)

theorem originalRaw_integral_eq_nesting (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure))=
    ∑'K : SourceOuter S,∫w : ℝ,∫t : ℝ,∑'IJ : CompletedPair,∫z : ℝ,∑'H : NonzeroFrequency,
      originalNestedOnLines η S hS D W0 W1 X Y Z (K,(w,(t,(IJ,(z,H))))) := by
  have hi := originalRaw_counting_product_integrable η S hS hpS hbad D W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hp := physicalRawNesting_preserving S
  have hj := (hp.symm (physicalRawNesting S)).integrable_comp_of_integrable hi
  have he := hp.integral_comp' (originalNestedOnLines η S hS D W0 W1 X Y Z)
  have he' : (∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure))=
      ∫p : PhysicalNestedSpace S,originalNestedOnLines η S hS D W0 W1 X Y Z p
        ∂((Measure.count:Measure (SourceOuter S)).prod (volume.prod (volume.prod
          ((Measure.count:Measure CompletedPair).prod (volume.prod (Measure.count:Measure NonzeroFrequency)))))) := by
    exact he
  rw [he']
  apply integral_physical_nesting
  exact hj

end SevenEighths.ProbePhysical
end

end OAI

end Source1103

/- Original source: OAI/NumberTheory/DirichletL/Detector/MellinPoisson.lean; sha256: 547898e89145c23c58df9dfbbcb1401c8264fc177ec874a9c63a1c77bb75e408 -/
section Source1104
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

lemma finiteSupport_verticalIntegral {α : Type*} (c : α → ℂ)
    (hc : (Function.support c).Finite) (F : α → ℂ → ℂ) (σ : ℝ)
    (hF : ∀ a, Integrable (fun y : ℝ => F a ((σ:ℂ)+y*Complex.I))) :
    verticalIntegral σ (fun t => ∑' a, c a * F a t) =
      ∑' a, c a * verticalIntegral σ (F a) := by
  have hz (a : α) (ha : a∉hc.toFinset) : c a=0 := by
    simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using ha
  have he (t : ℂ) : (∑' a, c a*F a t) = ∑ a∈hc.toFinset, c a*F a t :=
    tsum_eq_sum (fun a ha => by rw [hz a ha, zero_mul])
  rw [tsum_eq_sum (s := hc.toFinset) (fun a ha => by rw [hz a ha, zero_mul])]
  unfold verticalIntegral
  simp_rw [he]
  rw [integral_finsetSum _ (fun a ha => (hF a).const_mul (c a)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_const_mul]
  ring

theorem inner_mellin_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K Z : ℝ) (hK : 0<K) (hZ : 0<Z) :
    (∑' m : O, C.residueMonoid m * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) *
      verticalIntegral 4 (fun t => (Z:ℂ)^t * Complex.exp (t^2) *
        spectralRow C.excluded D (rowCoefficient η C.Xi s hs m) t)) =
    verticalIntegral 4 (fun t => (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      ((Z:ℂ)^t * Complex.exp (t^2)) *
        ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C C.excluded D s hs W K t p.1 p.2) := by
  let c (m : O) := C.residueMonoid m * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
    sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K)
  have hc : (Function.support c).Finite := by
    apply (elementWindow_finite_support W hWc K hK).subset
    intro m hm hz
    exact hm (by simp only [c, hz, mul_zero])
  rw [← finiteSupport_verticalIntegral c hc
    (fun m t => (Z:ℂ)^t * Complex.exp (t^2) *
      spectralRow C.excluded D (rowCoefficient η C.Xi s hs m) t) 4
    (fun m => physicalRow_integrable η C D s hs m Z hZ)]
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  norm_num only [Complex.ofReal_ofNat]
  have ht : 1 < ((4:ℂ)+(y:ℂ)*Complex.I).re := by simp
  rw [← physical_spectral_poisson η C C.excluded D s hs W hWc hWs K hK _ ht,
    ← tsum_mul_left]
  apply tsum_congr
  intro m
  dsimp only [c]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1104

/- Original source: OAI/NumberTheory/DirichletL/Detector/Transformed.lean; sha256: 60df1fb14e7056098016561e34189118d99f8710309d74cc746091147888dfaa -/
section Source1105
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

def poissonPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  (Y:ℂ)⁻¹ * ∑' s : {I : Ideal O // Supported I},
    if ∀ p∈C.excluded, ¬p∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let q_s : ℝ := Ideal.absNorm s.val
      W₁ (q_s/Y) * CanonicalRowCompletion.idealRowHom C.generator s.val /
        (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q_s*X):ℂ)) *
      verticalIntegral 4 (fun t => (Real.sqrt q_s:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2)) *
        ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C C.excluded D a has W₀
          (elementNorm C.generator*q_s*X) t p.1 p.2)
    else 0

theorem markedPhysicalProbe_eq_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (hWc : HasCompactSupport W₀)
    (hWs : ContDiff ℝ ∞ W₀) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) :
    markedPhysicalProbe η C D W₀ W₁ X Y Z = poissonPhysicalProbe η C D W₀ W₁ X Y Z := by
  unfold markedPhysicalProbe poissonPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with h
  · dsimp only
    congr 1
    have ha := supported_primaryGenerator_ne_zero s.val s.property
    have has := (supported_span_primaryGenerator_iff s.val).mpr s.property
    have hn : elementNorm (primaryGenerator s.val) = (Ideal.absNorm s.val:ℝ) := by
      unfold elementNorm
      rw [(primaryGenerator_spec s.val ha).1]
    have hb : 0<elementNorm C.generator := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
    have hs : 0<(Ideal.absNorm s.val:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
    have hK : 0<elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X := mul_pos (mul_pos hb hs) hX
    simpa only [hn] using inner_mellin_poisson η C D (primaryGenerator s.val) has
      W₀ hWc hWs (elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X) Z hK hZ
  · rfl

theorem physicalProbe_eq_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (hWc : HasCompactSupport W₀) (hWs : ContDiff ℝ ∞ W₀)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) :
    physicalProbe η C W₀ W₁ X Y Z = poissonPhysicalProbe η C 1 W₀ W₁ X Y Z :=
  markedPhysicalProbe_eq_poisson η C 1 W₀ W₁ hWc hWs X Y Z hX hZ

end SevenEighths.ProbePhysical
end

end OAI

end Source1105

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalRadial.lean; sha256: 5618ad5c655abca16647c176857d4fcb169e206186ef0559d837a7b815c440d4 -/
section Source1106
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

def radialMellinPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 : SchwartzMap ℝ ℂ) (W1 : ℝ→ℂ) (X Y Z σ : ℝ) : ℂ :=
  (Y:ℂ)⁻¹*∑'s : {I : Ideal O // Supported I},
    if ∀P∈C.excluded,¬P∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let qs : ℝ := Ideal.absNorm s.val
      W1 (qs/Y)*CanonicalRowCompletion.idealRowHom C.generator s.val /
        (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*qs*X):ℂ))*
      verticalIntegral 4 (fun t=>(Real.sqrt qs:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))*
        ∑'p : Ideal O×Ideal O,radialMellinSpectralTerm η C C.excluded D a has W0
          (elementNorm C.generator*qs*X) σ t p.1 p.2)
    else 0

theorem markedPhysicalProbe_eq_radial_mellin (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (D : Ideal O) (W0 : SchwartzMap ℝ ℂ) (W1 : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Set.Icc a b)
    (X Y Z σ : ℝ) (hX : 0<X) (hZ : 0<Z) (hσ : 1<σ) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      radialMellinPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z σ := by
  have hWc : HasCompactSupport (W0 : ℝ→ℂ) := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW
  rw [markedPhysicalProbe_eq_poisson η (calibrationForSet S hS) D W0 W1 hWc (W0.smooth (⊤:ℕ∞)) X Y Z hX hZ]
  unfold poissonPhysicalProbe radialMellinPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with hs
  · dsimp only
    congr 1
    unfold verticalIntegral
    congr 1
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    congr 1
    apply tsum_congr
    intro p
    have hcs : IsCoprime (calibrationForSet S hS).generator (primaryGenerator s.val) := by
      apply calibrationForSet_coprime_of_excluded S hS
      rw [(primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1]
      simpa only [calibrationForSet_excluded] using hs
    have hK : 0<elementNorm (calibrationForSet S hS).generator*(Ideal.absNorm s.val:ℝ)*X :=
      mul_pos (mul_pos (elementNorm_pos _ (calibrationForSet S hS).generator_ne_zero)
        (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1))) hX
    simpa only [calibrationForSet_excluded] using transformedSpectralTerm_radial_mellin η S hS hSne D
      (primaryGenerator s.val) ((supported_span_primaryGenerator_iff s.val).mpr s.property) hcs
      W0 a b ha hW _ σ hK hσ _ p.1 p.2
  · rfl

end SevenEighths.ProbePhysical
end

end OAI

end Source1106

/- Original source: OAI/NumberTheory/DirichletL/Detector/OuterMellin.lean; sha256: 6b8986e291a27ae6f13faac8e383cb460148937f24d15c5bec0fba6da2a859d7 -/
section Source1107
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss

lemma outer_source_vertical_inverse (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (σ r : ℝ) (hr : 0<r) :
    W r=verticalIntegral σ (fun w=>(r:ℂ)^(-w)*mellin W w) := by
  simpa only [verticalIntegral,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,
    Complex.ofReal_ofNat] using compactMellin_inversion W a b ha hW (W.smooth (⊤:ℕ∞)) σ r hr

lemma outer_source_scaled_inverse (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (σ N Y : ℝ) (hN : 0<N) (hY : 0<Y) :
    (Y:ℂ)⁻¹*W (N/Y)=
      verticalIntegral σ (fun w=>(Y:ℂ)^(w-1)*(N:ℂ)^(-w)*mellin W w) := by
  rw [outer_source_vertical_inverse W a b ha hW σ (N/Y) (div_pos hN hY)]
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have he (w : ℂ) : (Y:ℂ)⁻¹*((N/Y:ℝ):ℂ)^(-w)=(Y:ℂ)^(w-1)*(N:ℂ)^(-w) := by
    rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hN.le hY.le,div_eq_mul_inv,
      ←Complex.cpow_neg,neg_neg]
    rw [show w-1=(-1)+w by ring,Complex.cpow_add _ _ hy,Complex.cpow_neg_one]
    ring
  unfold verticalIntegral
  simp_rw [←he,mul_assoc,integral_const_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1107

/- Original source: OAI/NumberTheory/DirichletL/Detector/NestedMellin.lean; sha256: 372c7270be3e0125db289d8a2c6835143fd3341e141ac57df73ab8a3d1016131 -/
section Source1108
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

def nestedMellinPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) : ℂ :=
  ∑'s : {I : Ideal O // Supported I},
    if ∀P∈C.excluded,¬P∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let qs : ℝ := Ideal.absNorm s.val
      verticalIntegral υ (fun w=>(Y:ℂ)^(w-1)*(qs:ℂ)^(-w)*mellin W1 w*
        (CanonicalRowCompletion.idealRowHom C.generator s.val /
          (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*qs*X):ℂ)))*
        verticalIntegral 4 (fun t=>(Real.sqrt qs:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))*
          ∑'p : Ideal O×Ideal O,radialMellinSpectralTerm η C C.excluded D a has W0
            (elementNorm C.generator*qs*X) ξ t p.1 p.2))
    else 0

lemma verticalIntegral_mul_const (σ : ℝ) (F : ℂ→ℂ) (c : ℂ) :
    verticalIntegral σ (fun s=>F s*c)=verticalIntegral σ F*c := by
  unfold verticalIntegral
  rw [integral_mul_const,mul_assoc]

theorem markedPhysicalProbe_eq_nested_mellin (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z ξ υ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (hξ : 1<ξ) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      nestedMellinPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z ξ υ := by
  rw [markedPhysicalProbe_eq_radial_mellin η S hS hSne D W0 W1 a0 b0 ha0 hW0 X Y Z ξ hX hZ hξ]
  unfold radialMellinPhysicalProbe nestedMellinPhysicalProbe
  rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  split_ifs with hs
  · dsimp only
    rw [verticalIntegral_mul_const,verticalIntegral_mul_const,
      ←outer_source_scaled_inverse W1 a1 b1 ha1 hW1 υ (Ideal.absNorm s.val:ℝ) Y
        (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)) hY]
    ring
  · simp only [mul_zero]

end SevenEighths.ProbePhysical
end

end OAI

end Source1108

/- Original source: OAI/NumberTheory/DirichletL/Detector/RawRadialJoin.lean; sha256: b3322a9714df0dd43e6779d25af1471fdbafe1cc5e4a3be3baaeb70bcbf67c08 -/
section Source1109
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion ProbeCompleted ProbeRow CubicEisenstein
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma verticalIntegral_const_mul (σ : ℝ) (F : ℂ→ℂ) (c : ℂ) :
    verticalIntegral σ (fun z=>c*F z)=c*verticalIntegral σ F := by
  unfold verticalIntegral
  rw [integral_const_mul]
  ring

def rawRadialOuterFactor (C : CalibrationData) (K : Ideal O)
    (W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (t w : ℂ) : ℂ :=
  (Y:ℂ)^(w-1)*fullIdealWeight w K*mellin W1 w*
    (idealRowHom C.generator K /
      (C.tau*C.residueMonoid (primaryGenerator K)*(Real.sqrt (elementNorm C.generator*(Ideal.absNorm K:ℝ)*X):ℂ)))*
    (Real.sqrt (Ideal.absNorm K):ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))

lemma rawPhysicalMellinTerm_radial_join (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J K : Ideal O) (hK : Supported K)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ : ℝ) (t w : ℂ) :
    verticalIntegral ξ (fun z=>∑'H : NonzeroFrequency,
      rawPhysicalMellinTerm η C S D I J K hK W0 W1 X Y Z H.val t w z)=
    rawRadialOuterFactor C K W1 X Y Z t w*
      radialMellinSpectralTerm η C S D (primaryGenerator K)
        ((supported_span_primaryGenerator_iff K).mpr hK) W0
          (elementNorm C.generator*(Ideal.absNorm K:ℝ)*X) ξ t I J := by
  have hgen := (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K hK)).1
  have hn : elementNorm (primaryGenerator K)=(Ideal.absNorm K:ℝ) := by
    unfold elementNorm
    rw [hgen]
  unfold rawPhysicalMellinTerm physicalMellinCoefficientTerm radialMellinSpectralTerm
  split_ifs with hA
  · dsimp only
    simp only [hn,hgen]
    let c := rawRadialOuterFactor C K W1 X Y Z t w *
      (spectralSummand S D (baseRowCoefficient η C.Xi (primaryGenerator K)
        ((supported_span_primaryGenerator_iff K).mpr hK)) t I J *
        ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X/elementNorm (C.generator*completedIndex I J):ℝ):ℂ))
    have hp (z : ℂ) (H : NonzeroFrequency) :
        idealRowHom C.generator K /
          (C.tau*C.residueMonoid (primaryGenerator K)*
            (Real.sqrt (elementNorm C.generator*(Ideal.absNorm K:ℝ)*X):ℂ)) *
          (Real.sqrt (Ideal.absNorm K):ℂ)⁻¹ *
          spectralSummand S D (baseRowCoefficient η C.Xi (primaryGenerator K)
            ((supported_span_primaryGenerator_iff K).mpr hK)) t I J *
          ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
          actualCongruenceCoefficient C (completedIndex I J) (primaryGenerator K) hA H.val *
          ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X*elementNorm H.val /
            elementNorm ((C.generator*completedIndex I J)*primaryGenerator K):ℝ):ℂ)^(-z) *
          fullIdealWeight w K*(Y:ℂ)^(w-1)*(Z:ℂ)^t*Complex.exp (t^2)*
          mellin (paperRadialFourier W0) z*mellin W1 w =
        c*(actualCongruenceCoefficient C (completedIndex I J) (primaryGenerator K) hA H.val *
          ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X*elementNorm H.val /
            elementNorm ((C.generator*completedIndex I J)*primaryGenerator K):ℝ):ℂ)^(-z)*
          mellin (paperRadialFourier W0) z) := by
      dsimp only [c,rawRadialOuterFactor]
      ring
    simp only [Complex.ofReal_mul,Complex.ofReal_div] at hp ⊢
    simp_rw [hp,tsum_mul_left]
    rw [verticalIntegral_const_mul]
    dsimp only [c]
    simp only [Complex.ofReal_mul,Complex.ofReal_div]
    ring_nf
    congr 1
    apply congrArg (verticalIntegral ξ)
    funext z
    apply tsum_congr
    intro H
    congr 1 ; congr 1 ; ring_nf
  · simp only [zero_mul,tsum_zero,verticalIntegral,integral_zero,mul_zero]

end SevenEighths.ProbePhysical
end

end OAI

end Source1109

/- Original source: OAI/NumberTheory/DirichletL/Detector/OuterIndex.lean; sha256: 3b859737e4192d97ff4b94ad7b3e1187f3a310d971d5054b4c86f61f0358da8b -/
section Source1110
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def sourceOuterEquiv (S : Finset (Ideal O)) : SourceOuter S ≃
    {K : {I : Ideal O // Supported I} // ∀P∈S,¬P∣K.val} where
  toFun K := ⟨⟨K.val,K.property.1⟩,K.property.2⟩
  invFun K := ⟨K.val.val,K.val.property,K.property⟩
  left_inv _K := rfl
  right_inv _K := rfl

lemma sourceOuter_tsum (S : Finset (Ideal O)) (f : {I : Ideal O // Supported I}→ℂ) :
    (∑'K : {I : Ideal O // Supported I},if ∀P∈S,¬P∣K.val then f K else 0)=
      ∑'K : SourceOuter S,f ⟨K.val,K.property.1⟩ := by
  have hs := tsum_subtype {K : {I : Ideal O // Supported I} | ∀P∈S,¬P∣K.val} f
  have he := (sourceOuterEquiv S).tsum_eq (fun K=>f K.val)
  calc
    _ = ∑' K : {I : Ideal O // Supported I},
        Set.indicator {K | ∀ P ∈ S, ¬P ∣ K.val} f K := by
      apply tsum_congr
      intro K
      simp only [Set.indicator, Set.mem_ofPred_eq]
      split_ifs <;> rfl
    _ = _ := hs.symm.trans he.symm

end SevenEighths.ProbePhysical
end

end OAI

end Source1110

/- Original source: OAI/NumberTheory/DirichletL/Detector/RawNestedJoin.lean; sha256: ee81be44221376a57bd4e72d3534438c4699521320f637e1529fa0db894ae453 -/
section Source1111
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def rawNestedPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) : ℂ :=
  ∑'K : SourceOuter C.excluded,verticalIntegral υ (fun w=>verticalIntegral 4 (fun t=>
    ∑'IJ : CompletedPair,verticalIntegral ξ (fun z=>∑'H : NonzeroFrequency,
      rawPhysicalMellinTerm η C C.excluded D IJ.1 IJ.2 K.val K.property.1 W0 W1 X Y Z H.val t w z)))

theorem nestedMellinPhysicalProbe_eq_raw (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) :
    nestedMellinPhysicalProbe η C D W0 W1 X Y Z ξ υ=
      rawNestedPhysicalProbe η C D W0 W1 X Y Z ξ υ := by
  unfold nestedMellinPhysicalProbe rawNestedPhysicalProbe
  rw [sourceOuter_tsum]
  apply tsum_congr
  intro K
  dsimp only
  simp_rw [rawPhysicalMellinTerm_radial_join,tsum_mul_left]
  apply congrArg (verticalIntegral υ)
  funext w
  unfold rawRadialOuterFactor
  simp only [fullIdealWeight,ite_eq_right K.property.1.1]
  unfold verticalIntegral
  simp_rw [mul_assoc,integral_const_mul]
  simp only [Complex.ofReal_natCast]
  ring_nf
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  ring_nf

end SevenEighths.ProbePhysical
end

end OAI

end Source1111

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalRawIntegral.lean; sha256: 6d9f08623f0bcd16512307a6fcf00754c2259e94a4130a6fee60c2e26e0bc445 -/
section Source1112
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance : MeasurableSpace O := ⊤
local instance : MeasurableSingletonClass O := ⟨fun _=>trivial⟩
local instance : MeasurableSpace (Ideal O) := ⊤
local instance : MeasurableSingletonClass (Ideal O) := ⟨fun _=>trivial⟩
local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩

def rawPhysicalTotalIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)

theorem rawNestedPhysicalProbe_eq_integral (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    rawNestedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z 2 3=
      rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z := by
  unfold rawPhysicalTotalIntegral
  rw [originalRaw_integral_eq_nesting η S hS hpS hbad D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ]
  unfold rawNestedPhysicalProbe
  simp only [calibrationForSet_excluded]
  simp only [verticalIntegral,integral_const_mul,tsum_mul_left]
  unfold originalNestedOnLines originalRawOnLines
  simp only [Complex.ofReal_ofNat]
  ring_nf
  congr 1
  let e : SourceOuter S ≃ SourceOuter (calibrationForSet S hS).excluded :=
    Equiv.subtypeEquivRight (fun K=>by rw [calibrationForSet_excluded])
  rw [←e.tsum_eq]
  apply tsum_congr
  intro K
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  apply tsum_congr
  intro IJ
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  apply tsum_congr
  intro H
  congr 1 ; ring

theorem markedPhysicalProbe_eq_raw_integral (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z := by
  rw [markedPhysicalProbe_eq_nested_mellin η S hS hSne D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 2 3 hX hY hZ (by norm_num),nestedMellinPhysicalProbe_eq_raw]
  exact rawNestedPhysicalProbe_eq_integral η S hS hpS hbad D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ

end SevenEighths.ProbePhysical
end

end OAI

end Source1112

/- Original source: OAI/NumberTheory/DirichletL/Detector/RawArithmetic.lean; sha256: 8776a70147b31f817b6fcc99945130181dfa6c537b039f1a1e7c2e028ace27ce -/
section Source1113
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def rawArithmeticSeries (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (C : CalibrationData) (x w z : ℂ) : ℂ :=
  ∑'p : RawHighIndex,fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val))
    x w z (rawHighEmbedding p)

lemma rawHighCoefficient_outer_support (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (x w z : ℂ) (p : RawHighIndex)
    (hp : fullHighCoefficient S D η mask x w z (rawHighEmbedding p)≠0) :
    Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2 := by
  have hb : bareIdealHighCoefficient η p.1.val p.2.1.1 p.2.1.2 p.2.2 1≠0 := by
    intro hz
    exact hp (by simp only [fullHighCoefficient,rawHighEmbedding,markedIdealHighSummand,bareIdealHighSummand,hz,mul_zero,zero_mul])
  have hs : Supported p.2.2 := by
    unfold bareIdealHighCoefficient at hb
    split_ifs at hb with hh
    · exact hh.2.2.2.1
    · exact False.elim (hb rfl)
  refine ⟨hs,?_⟩
  by_contra hn
  exact hp (by simp [fullHighCoefficient,rawHighEmbedding,markedIdealHighSummand,highIdealMask,hn])

lemma rawArithmeticSeries_eq_sourceRaw (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (C : CalibrationData) (x w z : ℂ) :
    rawArithmeticSeries S D η C x w z=
      ∑'i : SourceRawIndex S,fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val))
        x w z (sourceRawEmbedding S i) := by
  unfold rawArithmeticSeries sourceRawEmbedding
  change _ = ∑'i : {p : RawHighIndex // Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2}, _
  symm
  apply tsum_subtype_eq_of_support_subset (f:=fun p : RawHighIndex=>
    fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val)) x w z (rawHighEmbedding p))
    (s:={p : RawHighIndex | Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2})
  intro p hp
  exact rawHighCoefficient_outer_support S D η _ x w z p hp

end SevenEighths.ProbePhysical
end

end OAI

end Source1113

/- Original source: OAI/NumberTheory/DirichletL/Detector/RawSourceIntegral.lean; sha256: 74aff08d078e20db4745aad32e2a8b1fc29ce7dc01e963d6f70d6df9c3dc83bd -/
section Source1114
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

def rawSourceOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (i : SourceRawIndex S) (p : HeightSpace) : ℂ :=
  initialHighOnLines S D η (fun H=>star ((calibrationForSet S hS).residueMonoid H.val))
    3 3 2 (sourceRawEmbedding S i) p *sourceMellinWeight W0 W1 X Y Z
      ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)

lemma originalRawOnLines_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (i : SourceRawIndex S) (p : HeightSpace) :
    originalRawOnLines η S hS D W0 W1 X Y Z i p=
      rawSourceOnLines η S hS D W0 W1 X Y Z i (sourceHeightShear.symm p) := by
  rw [originalRawOnLines,rawPhysicalMellinTerm_eq_source η S hS hpS hbad D _ _ _ i.property.1
    i.property.2 W0 W1 X Y Z hX i.val.1]
  have he : (4:ℂ)+p.1.1*Complex.I+1-((2:ℂ)+p.1.2*Complex.I)=
      3+((p.1.1-p.1.2:ℝ):ℂ)*Complex.I := by push_cast;ring
  have hs : sourceHeightShear.symm p=((p.1.1-p.1.2,p.1.2),p.2) := rfl
  simp only [rawSourceOnLines,initialHighOnLines,he,hs,sourceRawEmbedding,Complex.ofReal_ofNat]
  ring

lemma rawSourceOnLines_integrable (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun p : SourceRawIndex S×HeightSpace=>rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  have hm (H : NonzeroFrequency) : ‖star ((calibrationForSet S hS).residueMonoid H.val)‖≤1 := by
    simpa only [norm_star] using (calibrationForSet S hS).residueMonoid_norm_le_one H.val
  unfold rawSourceOnLines
  apply initialHigh_counting_product_integrable (sourceRawEmbedding S) (sourceRawEmbedding_injective S)
    S D η (fun H=>star ((calibrationForSet S hS).residueMonoid H.val)) hm 3 3 2
    (by norm_num) (by norm_num) (by norm_num)
    (fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
      ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I))
  · exact sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ 3 2 3 (by norm_num)
  · exact sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1
      X Y Z hX hY hZ 3 2 3 (by norm_num)

lemma rawPhysicalTotalIntegral_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) :
    rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : SourceRawIndex S×HeightSpace,rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2
          ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  unfold rawPhysicalTotalIntegral
  congr 1
  let e : SourceRawIndex S×HeightSpace ≃ᵐ SourceRawIndex S×HeightSpace :=
    (MeasurableEquiv.refl (SourceRawIndex S)).prodCongr sourceHeightShear.symm
  have hp : MeasurePreserving e ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) :=
    (MeasurePreserving.id _).prod (sourceHeightShear_preserving.symm sourceHeightShear)
  have he := hp.integral_comp' (fun p : SourceRawIndex S×HeightSpace=>
    rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2)
  refine Eq.trans ?_ he
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  exact originalRawOnLines_eq_source η S hS hpS hbad D W0 W1 X Y Z hX p.1 p.2

def rawSourceTripleIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫p : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
    rawArithmeticSeries S D η (calibrationForSet S hS) ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I) ∂heightMeasure

lemma rawPhysicalTotalIntegral_eq_triple (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z=
      rawSourceTripleIntegral η S hS D W0 W1 X Y Z := by
  rw [rawPhysicalTotalIntegral_eq_source η S hS hpS hbad D W0 W1 X Y Z hX]
  unfold rawSourceTripleIntegral
  congr 1
  have hi := rawSourceOnLines_integrable η S hS D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_left_ae] with p hp
  rw [integral_count_eq_tsum _ hp,rawArithmeticSeries_eq_sourceRaw]
  simp only [rawSourceOnLines,initialHighOnLines,Complex.ofReal_ofNat,tsum_mul_right]
  ring

theorem markedPhysicalProbe_eq_raw_triple (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      rawSourceTripleIntegral η S hS D W0 W1 X Y Z := by
  rw [markedPhysicalProbe_eq_raw_integral η S hS hpS hbad hSne D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ]
  exact rawPhysicalTotalIntegral_eq_triple η S hS hpS hbad D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ

end SevenEighths.ProbePhysical
end

end OAI

end Source1114

/- Original source: OAI/NumberTheory/DirichletL/Detector/SixthDecomposition.lean; sha256: 9b03e1100a886fef891e79e664b2c895699f7eab0389b6c1e10a77334870ff90 -/
section Source1115
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ActualEisensteinCubic HeckeInverseAmplification CenteredExceptionalCount ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem sixthRow_surjective (H : NonzeroFrequency) :
    ∃p : FreeRow×HeckeInverseAmplification.NonzeroIdeal,rowMap p=H.val := by
  let I : Id := Ideal.span {H.val}
  have hI : I≠0 := Ideal.span_singleton_eq_bot.not.mpr H.property
  let J : Id := sixthQuotient I
  have hJ : J≠0 := sixthQuotient_ne_zero I
  let a := idealGenerator J
  have ha : a≠0 := idealGenerator_ne_zero J hJ
  have hspan : Ideal.span {a}=J := span_idealGenerator J
  have hd : a^6∣H.val := by
    apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
    rw [←Ideal.span_singleton_pow,hspan]
    change J^6∣I
    rw [←sixth_normal_form I hI]
    exact dvd_mul_left _ _
  obtain ⟨u,hu⟩ := hd
  have hu0 : u≠0 := by
    intro hz
    rw [hz,mul_zero] at hu
    exact H.property hu
  have hsu : Ideal.span {u}=sixthRemainder I := by
    have hi : Ideal.span {u}*J^6=I := by
      rw [←hspan,Ideal.span_singleton_pow,Ideal.span_singleton_mul_span_singleton]
      exact congrArg (fun b : O=>Ideal.span {b}) (by simpa only [mul_comm] using hu.symm)
    apply mul_right_cancel₀ (pow_ne_zero 6 hJ)
    exact hi.trans (sixth_normal_form I hI).symm
  have hf : SixthFree (Ideal.span {u}) := by
    rw [hsu]
    intro P
    exact sixthRemainder_valuation_lt I P
  refine ⟨(⟨u,hu0,hf⟩,⟨J,hJ⟩),?_⟩
  change u*a^6=H.val
  simpa only [mul_comm] using hu.symm

def sixthFrequencyEquiv : FreeRow×HeckeInverseAmplification.NonzeroIdeal ≃ NonzeroFrequency :=
  Equiv.ofBijective (fun p=>⟨rowMap p,rowMap_ne_zero p⟩) ⟨
    fun p q h=>rowMap_injective (congrArg Subtype.val h),
    fun H=>by obtain ⟨p,hp⟩ := sixthRow_surjective H;exact ⟨p,Subtype.ext hp⟩⟩

lemma sixthFrequencyEquiv_apply (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) :
    (sixthFrequencyEquiv p).val=p.1.val*(idealGenerator p.2.val)^6 := rfl

theorem tsum_sixth_decomposition (f : NonzeroFrequency→ℂ) :
    (∑'H : NonzeroFrequency,f H)=
      ∑'p : FreeRow×HeckeInverseAmplification.NonzeroIdeal,f (sixthFrequencyEquiv p) :=
  (sixthFrequencyEquiv.tsum_eq f).symm

lemma idealGenerator_sixth_eq_primary (I : Id) (hI : CanonicalQuadraticSieve.Supported I) :
    (idealGenerator I)^6=(CompletedGauss.primaryGenerator I)^6 := by
  have he : Ideal.span {idealGenerator I}=Ideal.span {CompletedGauss.primaryGenerator I} :=
    (span_idealGenerator I).trans
      (CompletedGauss.primaryGenerator_spec I
        (supported_primaryGenerator_ne_zero I hI)).1.symm
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp he
  have hh := congrArg (fun a : O=>a^6) hu
  simpa only [mul_pow,CanonicalUnitEuler.unit_pow_six,mul_one] using hh

lemma sixthFrequencyEquiv_primary (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal)
    (hP : CanonicalQuadraticSieve.Supported p.2.val) :
    (sixthFrequencyEquiv p).val=p.1.val*(CompletedGauss.primaryGenerator p.2.val)^6 := by
  rw [sixthFrequencyEquiv_apply,idealGenerator_sixth_eq_primary p.2.val hP]

end SevenEighths.ProbePhysical
end

end OAI

end Source1115

/- Original source: OAI/NumberTheory/DirichletL/Detector/SixthMask.lean; sha256: 494806ed075034ccf48004359c047e57077210b1a189f075bb7fec265c0b54f4 -/
section Source1116
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve CubicEisenstein
open HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O

lemma calibration_sixth_ideal_mask (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (L : Ideal O) :
    (calibrationForSet S hS).residueMonoid (idealGenerator L)^6=
      if ∀P∈S,¬P∣L then 1 else 0 := by
  by_cases hL : ∀P∈S,¬P∣L
  · rw [ite_eq_left hL]
    apply calibrationForSet_residue_sixth
    apply calibrationForSet_coprime_of_excluded
    simpa only [span_idealGenerator] using hL
  · rw [ite_eq_right hL]
    have hz : (calibrationForSet S hS).residueMonoid (idealGenerator L)=0 := by
      by_contra hn
      have hu := (calibrationForSet S hS).residue.apply_ne_zero_iff.mp hn
      have hc := (isUnit_quotient_span_iff (calibrationForSet S hS).generator (idealGenerator L)).mp hu
      have ho := (calibrationForSet_coprime_iff S hS (idealGenerator L)).mp hc
      apply hL
      intro P hP hd
      apply ho P hP
      apply (Ideal.dvd_iff_le.mp hd)
      have hm : idealGenerator L∈Ideal.span ({idealGenerator L}:Set O) := Ideal.subset_span (by simp)
      rw [span_idealGenerator L] at hm
      exact hm
    rw [hz,zero_pow (by decide : 6≠0)]

lemma calibration_sixth_frequency_mask (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (u : O) (L : Ideal O) :
    star ((calibrationForSet S hS).residueMonoid (u*idealGenerator L^6))=
      star ((calibrationForSet S hS).residueMonoid u)*(if ∀P∈S,¬P∣L then 1 else 0) := by
  rw [map_mul,map_pow,calibration_sixth_ideal_mask]
  split_ifs <;> simp only [mul_one,mul_zero,star_zero]

lemma sixthFrequencyWeight (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (z : ℂ) :
    frequencyWeight z (sixthFrequencyEquiv p)=
      frequencyWeight z ⟨p.1.val,p.1.property.1⟩*fullIdealWeight (6*z) p.2.val := by
  have hu : 0<elementNorm p.1.val := elementNorm_pos _ p.1.property.1
  have hl : 0<(Ideal.absNorm p.2.val:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.2.property)
  have hn : elementNorm (sixthFrequencyEquiv p).val=
      elementNorm p.1.val*(Ideal.absNorm p.2.val:ℝ)^6 := by
    unfold elementNorm
    exact_mod_cast rowMap_norm p
  simp only [frequencyWeight,fullIdealWeight,ite_eq_right p.2.property,hn,Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hu.le (pow_nonneg hl.le 6)]
  congr 1
  have he := Complex.cpow_mul_ofReal_nonneg hl.le (6:ℝ) (-z)
  simp only [Real.rpow_ofNat,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_natCast] at he
  simp only [Complex.ofReal_pow,Complex.ofReal_natCast]
  rw [←he]
  congr 1
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1116

/- Original source: OAI/NumberTheory/DirichletL/Detector/SixthArray.lean; sha256: 73d27648449592bd164f4a58557934a512b6ba1e2c1dbb18ac52b586b61c59d8 -/
section Source1117
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeCompleted
open HeckeInverseAmplification ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma bareIdealHighCoefficient_sixth (η : HeckeFamily.Character)
    (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (hL : Supported p.2.val)
    (I J K : Ideal O) :
    bareIdealHighCoefficient η (sixthFrequencyEquiv p).val I J K 1=
      bareIdealHighCoefficient η p.1.val I J K p.2.val := by
  rw [sixthFrequencyEquiv_primary p hL]
  unfold bareIdealHighCoefficient
  by_cases h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K
  · simp only [h.1,h.2.1,h.2.2.1,h.2.2.2,hL,supported_one_ideal,and_self,dite_eq_left]
    congr 1
    simp only [primaryGenerator_one,one_pow,mul_one]
  · have h1 : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O)) :=
      fun hh=>h ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
    have h2 : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported p.2.val) :=
      fun hh=>h ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
    rw [dite_eq_right h1,dite_eq_right h2]

lemma rawHighCoefficient_sixth (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hprime : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (D : Ideal O) (η : HeckeFamily.Character) (x w z : ℂ)
    (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (I J K : Ideal O) :
    fullHighCoefficient S D η
      (fun H=>star ((calibrationForSet S hS).residueMonoid H.val)) x w z
      (rawHighEmbedding (sixthFrequencyEquiv p,((I,J),K)))=
    star ((calibrationForSet S hS).residueMonoid p.1.val)*
      frequencyWeight z ⟨p.1.val,p.1.property.1⟩*
      markedIdealHighSummand S D η p.1.val x w z I J K p.2.val := by
  have hOne : ∀P∈S,¬P∣(1:Ideal O) := fun P hP=> (hprime P hP).not_dvd_one
  change star ((calibrationForSet S hS).residueMonoid (sixthFrequencyEquiv p).val)*
    frequencyWeight z (sixthFrequencyEquiv p)*
      markedIdealHighSummand S D η (sixthFrequencyEquiv p).val x w z I J K 1=_
  rw [sixthFrequencyWeight]
  rw [sixthFrequencyEquiv_apply,calibration_sixth_frequency_mask]
  by_cases hL : ∀P∈S,¬P∣p.2.val
  · have hs := supported_of_source_exclusions S hbad p.2.val p.2.property hL
    have hb := bareIdealHighCoefficient_sixth η p hs I J K
    rw [sixthFrequencyEquiv_apply] at hb
    simp only [ite_eq_left hL,mul_one,markedIdealHighSummand,highIdealMask,ite_eq_left hOne,
      bareIdealHighSummand,hb]
    have hw1 : fullIdealWeight (6*z) (1:Ideal O)=1 := (IdealEuler.normWeight (6*z)).map_one
    rw [hw1]
    ring
  · simp only [ite_eq_right hL,mul_zero,zero_mul,markedIdealHighSummand,highIdealMask]

end SevenEighths.ProbePhysical
end

end OAI

end Source1117

/- Original source: OAI/NumberTheory/DirichletL/Detector/SixthSeries.lean; sha256: fb456564d9f040517092ac5b383aa7e04ffb518dc57a48cc1b18f98cff3c89d7 -/
section Source1118
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve HeckeInverseAmplification ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev SixthInnerIndex := HeckeInverseAmplification.NonzeroIdeal×((Id×Id)×Id)

def sixthRawEquiv : FreeRow×SixthInnerIndex ≃ RawHighIndex :=
  (Equiv.prodAssoc _ _ _).symm.trans
    (Equiv.prodCongr sixthFrequencyEquiv (Equiv.refl _))

def nonzeroLastEquiv : SixthInnerIndex ≃ {p : (Id×Id)×(Id×Id) // p.2.2≠0} where
  toFun p := ⟨(p.2.1,(p.2.2,p.1.val)),p.1.property⟩
  invFun p := (⟨p.val.2.2,p.property⟩,(p.val.1,p.val.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

lemma markedIdealHighSummand_last_zero (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K : Id) :
    markedIdealHighSummand S D η u x w z I J K 0=0 := by
  have hz : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (0:Id)) :=
    fun h=>h.2.2.2.2.1 rfl
  simp only [markedIdealHighSummand,bareIdealHighSummand,bareIdealHighCoefficient,
    dite_eq_right hz,zero_mul,mul_zero]

lemma markedIdealHighSeries_eq_sixth_inner (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) :
    markedIdealHighSeries S D η u x w z=
      ∑'p : SixthInnerIndex,markedIdealHighSummand S D η u x w z p.2.1.1 p.2.1.2 p.2.2 p.1.val := by
  have he := nonzeroLastEquiv.tsum_eq (fun p=>
    markedIdealHighSummand S D η u x w z p.val.1.1 p.val.1.2 p.val.2.1 p.val.2.2)
  change (∑'p : SixthInnerIndex,markedIdealHighSummand S D η u x w z p.2.1.1 p.2.1.2 p.2.2 p.1.val)=_ at he
  rw [he]
  unfold markedIdealHighSeries
  symm
  apply tsum_subtype_eq_of_support_subset
    (f:=fun p : (Id×Id)×(Id×Id)=>markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2)
    (s:={p : (Id×Id)×(Id×Id) | p.2.2≠0})
  intro p hp hz
  apply hp
  change markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2=0
  rw [hz,markedIdealHighSummand_last_zero]

theorem rawArithmeticSeries_eq_sixth_high (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hprime : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (D : Id) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re) :
    rawArithmeticSeries S D η (calibrationForSet S hS) x w z=
      ∑'u : FreeRow,star ((calibrationForSet S hS).residueMonoid u.val)*
        frequencyWeight z ⟨u.val,u.property.1⟩*markedIdealHighSeries S D η u.val x w z := by
  let mask : NonzeroFrequency→ℂ := fun H=>star ((calibrationForSet S hS).residueMonoid H.val)
  have hm (H : NonzeroFrequency) : ‖mask H‖≤1 := by
    simpa only [mask,norm_star] using (calibrationForSet S hS).residueMonoid_norm_le_one H.val
  have hs := (fullHighSummand_summable S D η x w z hx hw hz mask hm).comp_injective
    rawHighEmbedding_injective
  have ht : Summable (fun p : FreeRow×SixthInnerIndex=>
      fullHighCoefficient S D η (fun H=>star ((calibrationForSet S hS).residueMonoid H.val)) x w z
        (rawHighEmbedding (sixthRawEquiv p))) := hs.comp_injective sixthRawEquiv.injective
  unfold rawArithmeticSeries
  rw [←sixthRawEquiv.tsum_eq]
  rw [ht.tsum_prod]
  apply tsum_congr
  intro u
  rw [markedIdealHighSeries_eq_sixth_inner,←tsum_mul_left]
  apply tsum_congr
  intro p
  exact rawHighCoefficient_sixth S hS hprime hbad D η x w z (u,p.1) p.2.1.1 p.2.1.2 p.2.2

end SevenEighths.ProbePhysical
end

end OAI

end Source1118

/- Original source: OAI/NumberTheory/DirichletL/Detector/SourceTriple.lean; sha256: d373bbfbf14028dd3167a1b4780b3bc547ddca7d1121c6c50349b5b43bc2f4c0 -/
section Source1119
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary ProbeCompleted HeckeInverseAmplification CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def sourceRowSeries (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (C : CalibrationData) (D : Ideal O) (x w z : ℂ) : ℂ :=
  ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
    markedIdealHighSeries S D η u.val x w z

def sourceTripleIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫p : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
    sourceRowSeries η S (calibrationForSet S hS) D ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I) ∂heightMeasure

lemma rawSourceTripleIntegral_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    rawSourceTripleIntegral η S hS D W0 W1 X Y Z=
      sourceTripleIntegral η S hS D W0 W1 X Y Z := by
  unfold rawSourceTripleIntegral sourceTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  dsimp only
  congr 1
  unfold sourceRowSeries
  exact rawArithmeticSeries_eq_sixth_high S hS hpS hbad D η
    ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])

theorem markedPhysicalProbe_eq_source_triple (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      sourceTripleIntegral η S hS D W0 W1 X Y Z := by
  rw [markedPhysicalProbe_eq_raw_triple η S hS hpS hbad hSne D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ]
  exact rawSourceTripleIntegral_eq_source η S hS hpS hbad D W0 W1 X Y Z

end SevenEighths.ProbePhysical
end

end OAI

end Source1119
