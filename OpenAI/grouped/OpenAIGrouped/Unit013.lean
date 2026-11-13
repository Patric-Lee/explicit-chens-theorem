import OpenAIGrouped.Unit012
import OpenAIGrouped.Unit009
import OpenAIGrouped.Unit008
import OpenAIGrouped.Unit010
import OpenAIGrouped.Unit007
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import OpenAIGrouped.Unit011
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Complex.PhragmenLindelof

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Detector/CalibrationCancellation.lean; sha256: 2e6bedeaedd3c5c2f5869a6a3478b81984d4dfe12b396e79077c1a47729ec95e -/
section Source520
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma Xi_apply (C : CalibrationData) (a : O) :
    C.Xi a = C.residueMonoid a * idealRowHom C.generator (Ideal.span {a}) := rfl

theorem calibration_coefficient_cancel (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : IsCoprime (calibrationForSet S hS).generator H) :
    let C := calibrationForSet S hS
    actualCongruenceCoefficient C A s (supportedElement_ne_zero A hA) H *
      idealRowHom C.generator (Ideal.span {s}) /
        ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s*star (C.residueMonoid H)) *
      (C.Xi A)⁻¹ = bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H := by
  dsimp only
  let C := calibrationForSet S hS
  have hcA : IsCoprime C.generator A := hcop.of_mul_right_left
  have hcs : IsCoprime C.generator s := hcop.of_mul_right_right
  have hXA : C.Xi A≠0 := by
    intro h
    have hn := C.Xi_norm_one A hA hcA
    rw [h, norm_zero] at hn
    norm_num at hn
  have hXs : C.Xi s≠0 := by
    intro h
    have hn := C.Xi_norm_one s hs hcs
    rw [h, norm_zero] at hn
    norm_num at hn
  rw [Xi_apply] at hXA hXs
  have hηA := left_ne_zero_of_mul hXA
  have hκA := right_ne_zero_of_mul hXA
  have hηs := left_ne_zero_of_mul hXs
  have hκs := right_ne_zero_of_mul hXs
  have hηH : C.residueMonoid H≠0 :=
    C.residue.apply_ne_zero_iff.mpr ((isUnit_quotient_span_iff C.generator H).mpr hH)
  have hηHstar : star (C.residueMonoid H)≠0 := star_ne_zero.mpr hηH
  have hτ : C.tau≠0 := calibrationForSet_tau_ne_zero S hS
  have hq : 0<elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hroot : (Real.sqrt (elementNorm C.generator):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have he := actualCongruenceCoefficient_calibration_factor S hS A s
    (supportedElement_ne_zero A hA) hs hcop H
  dsimp only at he
  rw [he, Xi_apply, map_mul]
  change _ = bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H
  dsimp only [C] at hηA hκA hηs hκs hηHstar hτ hroot
  field_simp

end SevenEighths.ProbePhysical
end

end OAI

end Source520

/- Original source: OAI/NumberTheory/DirichletL/Detector/SourceCoefficient.lean; sha256: 374110c8227301a3be4ce6269f22ededcb0484583fc28a76c39e6b898fef70a4 -/
section Source521
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbePhase ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def sourceHighCoefficient (C : CalibrationData) (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O) (hA : A≠0) (u a : O) : ℂ :=
  actualCongruenceCoefficient C A s hA (u*a^6) * idealRowHom C.generator (Ideal.span {s}) /
    ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s*star (C.residueMonoid u)) *
    gaussTwo I hI * star (FiniteGaussPhase.angularFactor A * G A) *
    targetMonoid η A * (C.Xi A)⁻¹ * reciprocitySign A s

def bareSourceCoefficient (η : HeckeFamily.Character) (I : Ideal O)
    (hI : primaryGenerator I≠0) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  targetMonoid η A * star (FiniteGaussPhase.angularFactor A) *
    correctedFiniteCoefficient I hI A s hA H

theorem sourceHighCoefficient_eq_bare (S : Finset (Ideal O)) (hS : ∀ P∈S,P.IsMaximal)
    (η : HeckeFamily.Character) (I : Ideal O) (hI : primaryGenerator I≠0)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (u a : O)
    (hH : IsCoprime (calibrationForSet S hS).generator (u*a^6)) :
    sourceHighCoefficient (calibrationForSet S hS) η I hI A s (supportedElement_ne_zero A hA) u a =
      bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) (u*a^6) := by
  let C := calibrationForSet S hS
  have ha : IsCoprime C.generator a :=
    hH.of_isCoprime_of_dvd_right (by refine ⟨u*a^5,?_⟩; ring)
  have hval : C.residueMonoid (u*a^6)=C.residueMonoid u := by
    rw [map_mul,map_pow,calibrationForSet_residue_sixth S hS a ha,mul_one]
  have he := calibration_coefficient_cancel S hS A s hA hs hcop (u*a^6) hH
  dsimp only at he
  dsimp only [C] at hval
  rw [hval] at he
  unfold sourceHighCoefficient bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  simp only [star_mul]
  calc
    _ = (actualCongruenceCoefficient (calibrationForSet S hS) A s (supportedElement_ne_zero A hA) (u*a^6) *
      idealRowHom (calibrationForSet S hS).generator (Ideal.span {s}) /
      ((Real.sqrt (elementNorm (calibrationForSet S hS).generator):ℂ)*(calibrationForSet S hS).tau*
       (calibrationForSet S hS).residueMonoid s*star ((calibrationForSet S hS).residueMonoid u)) *
      ((calibrationForSet S hS).Xi A)⁻¹) *
      (gaussTwo I hI * star (G A) * star (FiniteGaussPhase.angularFactor A) *
        targetMonoid η A * reciprocitySign A s) := by ring
    _ = _ := by rw [he]; ring

theorem bareSourceCoefficient_product (η : HeckeFamily.Character) (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryGenerator I})) (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r)) (H : O) :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) H =
      bareSourceCoefficient η I hI.2 A s hA H * bareSourceCoefficient η J hJ.2 B r hB H := by
  have he := correctedFiniteCoefficient_product I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop H
  dsimp only at he ⊢
  unfold bareSourceCoefficient
  rw [he,map_mul,angularFactor_mul,star_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source521

/- Original source: OAI/NumberTheory/DirichletL/Detector/SixthFrequency.lean; sha256: aeeff56575517a387397660c9131a32b786dfe64a5d09d5994a3e1cb6133477c -/
section Source522
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
open CompletedGauss ConcreteTraceCRT GaussianShiftedPartition CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma finite_fourier_invariant_unit {R : Type*} [CommRing R] [Fintype R]
    (F : R→ℂ) (ψ : AddChar R ℂ) (u : Rˣ) (hF : ∀ x,F ((u:R)*x)=F x) (H : R) :
    (∑ x,F x*ψ (((u:R)*H)*x)) = ∑ x,F x*ψ (H*x) := by
  symm
  rw [← Equiv.sum_comp u.mulLeft (fun x=>F x*ψ (H*x))]
  simp only [Units.mulLeft_apply,hF]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  congr 1
  ring

lemma supported_sixth_value (A v : O) (hA : Supported (Ideal.span {A}))
    (hcop : IsCoprime A v) : idealRowHom (v^6) (Ideal.span {A})=1 := by
  rw [idealRowHom_sixth_mask _ _ hA, ite_eq_left ((Ideal.isCoprime_span_singleton_iff A v).mpr hcop)]

theorem barePhysicalFourier_sixth_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A*s)) :
    barePhysicalFourier A s (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs) (v^6*H) =
      barePhysicalFourier A s (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs) H := by
  have hAs := mul_ne_zero (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs)
  let := finite_quotient_span hAs
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let u := residueUnit (A*s) (v^6) hcop.pow_left.symm
  have hF (x : Residue (A*s)) :
      movingQuotient A s (supportedElement_ne_zero s hs) ((u:Residue (A*s))*x) =
        movingQuotient A s (supportedElement_ne_zero s hs) x := by
    rw [show (u:Residue (A*s))=Ideal.Quotient.mk _ (v^6) by rfl,
      movingQuotient_unit_scale A s hs (v^6) hcop.of_mul_right_right.pow_left,
      supported_sixth_value A v hA hcop.of_mul_right_left.symm,
      supported_sixth_value s v hs hcop.of_mul_right_right.symm,inv_one,one_mul,one_mul]
  have he := finite_fourier_invariant_unit (movingQuotient A s (supportedElement_ne_zero s hs))
    (quotientTrace (A*s) hAs) u hF (Ideal.Quotient.mk _ H)
  unfold barePhysicalFourier elementFourier
  simp only [tsum_fintype]
  change (∑ x,movingQuotient A s (supportedElement_ne_zero s hs) x *
    quotientTrace (A*s) hAs (Ideal.Quotient.mk _ (v^6*H)*x)) =
    ∑ x,movingQuotient A s (supportedElement_ne_zero s hs) x *
      quotientTrace (A*s) hAs (Ideal.Quotient.mk _ H*x)
  simpa only [u,residueUnit_coe,map_mul] using he

theorem bareCongruenceCoefficient_sixth_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A*s)) :
    bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (v^6*H) =
      bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H := by
  have he := barePhysicalFourier_sixth_frequency A s hA hs v H hcop
  simp only [barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  exact mul_left_cancel₀ hn he

theorem bareSourceCoefficient_sixth_frequency (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A*s)) :
    bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) (v^6*H) =
      bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) H := by
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [bareCongruenceCoefficient_sixth_frequency A s hA hs v H hcop]

theorem bareSourceCoefficient_product_frequency (η : HeckeFamily.Character) (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryGenerator I})) (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r)) (a b : O)
    (hba : IsCoprime b ((primaryGenerator I*n^3)*s))
    (hab : IsCoprime a ((primaryGenerator J*m^3)*r)) :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) ((a*b)^6) =
      bareSourceCoefficient η I hI.2 A s hA (a^6) * bareSourceCoefficient η J hJ.2 B r hB (b^6) := by
  have he := bareSourceCoefficient_product η I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop ((a*b)^6)
  dsimp only at he ⊢
  have hi := bareSourceCoefficient_sixth_frequency η I hI.2 (primaryGenerator I*n^3) s
    (supported_completed _ _ hc hn) hs b (a^6) hba
  have hj := bareSourceCoefficient_sixth_frequency η J hJ.2 (primaryGenerator J*m^3) r
    (supported_completed _ _ hd hm) hr a (b^6) hab
  rw [show b^6*a^6=(a*b)^6 by ring] at hi
  rw [show a^6*b^6=(a*b)^6 by ring] at hj
  rw [hi,hj] at he
  exact he

end SevenEighths.ProbePhysical
end

end OAI

end Source522

/- Original source: OAI/NumberTheory/DirichletL/Moments/Amplification.lean; sha256: 1246e38a3c1fbb39bada8a0517d55ac0fc785f7d927b81a434b0c45815fe1244 -/
section Source523
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplification
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge ProbePrimePower ProbePhysical
open CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem gauss_prime_power_one (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) 1 =
      if n = 0 then primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 else 0 := by
  rw [sexticGauss_prime_power p hp hg]
  have ht := actualSextic_primePowerGauss_at_pow p hp hg hc (n+1) n 0
  simp only [pow_zero] at ht
  rw [ht]
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hn0 : ¬0 = n := Ne.symm hn
    have hpos : ¬n ≤ 0 := by omega
    simp only [ite_eq_right hn,ite_eq_right hn0,ite_eq_right hpos,show ¬n+1 ≤ 0 by omega,ite_false,sub_self]
    split_ifs <;> rfl

theorem gauss_prime_power_six (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (p^6) =
      if n = 5 then (Ideal.absNorm (Ideal.span {p}) : ℂ)^5 *
        ((Ideal.absNorm (Ideal.span {p}) : ℂ)-1)
      else if n = 6 then (Ideal.absNorm (Ideal.span {p}) : ℂ)^6 *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 else 0 := by
  rw [sexticGauss_prime_power p hp hg,actualSextic_primePowerGauss_at_pow p hp hg hc]
  have h6 : actualSextic (Ideal.span {p}) hg ^ 6 = 1 :=
    (actualSextic_pow_eq_one_iff _ hg hc 6).mpr dvd_rfl
  by_cases hn5 : n = 5
  · subst n
    norm_num
    ring
  · by_cases hn6 : n = 6
    · subst n
      simp only [hn5,show ¬6 ∣ 6+1 by decide,ite_false,ite_true,
        pow_succ (actualSextic (Ideal.span {p}) hg) 6,h6,one_mul]
    · rw [ite_eq_right hn5,ite_eq_right hn6]
      by_cases hd : 6 ∣ n+1
      · have hlarge : 6 < n := by omega
        simp only [hd,ite_true,show ¬n+1 ≤ 6 by omega,ite_false,
          show ¬n ≤ 6 by omega,sub_self]
      · simp only [hd,ite_false,show ¬6=n from Ne.symm hn6]

theorem gauss_prime_power_unchanged (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ)
    (hn0 : n ≠ 0) (hn5 : n ≠ 5) (hn6 : n ≠ 6) (h : O) (hph : ¬p ∣ h) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (h*p^6) =
      sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) h := by
  have hcop : IsCoprime h (p^(n+1)) :=
    (hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right
  have hsp := supported_power p hs (n+1)
  rw [sexticGauss_unit_scale _ hsp h (p^6) hcop,
    ← mul_one h, sexticGauss_unit_scale _ hsp h 1 hcop,
    gauss_prime_power_six p hp hg hc,gauss_prime_power_one p hp hg hc]
  simp only [hn0,hn5,hn6,ite_false,mul_zero]

theorem gauss_sixth_frequency (a : O) (ha : Supported (Ideal.span {a}))
    (p h : O) (hcop : IsCoprime p a) :
    sexticGauss a (supportedElement_ne_zero a ha) (p^6*h) =
      sexticGauss a (supportedElement_ne_zero a ha) h := by
  rw [sexticGauss_unit_scale a ha (p^6) h hcop.pow_left,
    supported_sixth_value a p ha hcop.symm,inv_one,one_mul]

theorem twelfth_power_mask (p : O) (hs : Supported (Ideal.span {p})) (u : O) :
    idealRowHom u (Ideal.span {p}) ^ 12 = coprimalityMask u p := by
  rw [show 12=6*2 by decide,pow_mul,← idealRowHom_argument_pow u 6 _ hs,
    idealRowHom_sixth_eq_mask u p hs]
  change (if IsCoprime u p then (1 : ℂ) else 0)^2 = if IsCoprime u p then 1 else 0
  split_ifs <;> norm_num

end SevenEighths.CenteredMomentAmplification

end

end OAI

end Source523

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationLocal.lean; sha256: 6788aa02350ace40c4f6d4ae3cfc450bc6f2c4902f9ffb63ae4a1c0c8defb36e -/
section Source524
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationLocal
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge ProbePrimePower ProbePhysical
open CenteredMomentUnequal CenteredMomentAmplification CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

def centralLocal (p : O) (hp : p ≠ 0) (n : ℕ) (h : O) : ℂ :=
  sexticGauss (p^(n+1)) (pow_ne_zero _ hp) h / (Ideal.absNorm (Ideal.span {p}) : ℂ)^(n+1)

theorem gauss_unit_scale_norm (a : O) (ha : Supported (Ideal.span {a}))
    (b h : O) (hcop : IsCoprime b a) :
    ‖sexticGauss a (supportedElement_ne_zero a ha) (b*h)‖ =
      ‖sexticGauss a (supportedElement_ne_zero a ha) h‖ := by
  let := finite_quotient_span (supportedElement_ne_zero a ha)
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := CenteredMomentCommonSupport.isUnit_residue_of_coprime a b hcop.symm
  have hn : ‖idealRowHom b (Ideal.span {a})‖ = 1 := by
    change ‖supportedModulusCharacter a ha (Ideal.Quotient.mk _ b)‖ = 1
    rw [← hu]
    exact FiniteRayExpansion.norm_char_unit _ u
  rw [sexticGauss_unit_scale a ha b h hcop,norm_mul,norm_inv,hn,inv_one,one_mul]

theorem primeGauss_actual_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    ‖primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1‖^2 =
      (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := finite_quotient_span hp.ne_zero
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hχ : actualSextic (Ideal.span {p}) hg ≠ 1 := by
    intro he
    have ho := CenteredMomentCanonical.actualSextic_order_six (Ideal.span {p}) hg hc
    rw [he,orderOf_one] at ho
    norm_num at ho
  have ht : (CubicEisenstein.quotientTrace p hp.ne_zero).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero
  have he : primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 =
      gaussSum (actualSextic (Ideal.span {p}) hg) (CubicEisenstein.quotientTrace p hp.ne_zero) := by
    simp [primeGauss,tsum_fintype,gaussSum]
  rw [he,FiniteFieldSieve.primitive_gauss_norm_sq _ _ hχ ht]
  norm_cast
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem centralLocal_six (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    centralLocal p hp.ne_zero 5 (p^6) = 1 - (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ := by
  rw [centralLocal,gauss_prime_power_six p hp hg hc]
  simp only [ite_true]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  field_simp
  ring

theorem centralLocal_seven (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    centralLocal p hp.ne_zero 6 (p^6) =
      primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 /
        (Ideal.absNorm (Ideal.span {p}) : ℂ) := by
  rw [centralLocal,gauss_prime_power_six p hp hg hc]
  simp only [show ¬(6:ℕ)=5 by decide,ite_false,ite_true]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  field_simp
  ring

theorem centralLocal_unit_norm (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (n : ℕ) (h k : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero n (h*k)‖ = ‖centralLocal p hp.ne_zero n k‖ := by
  unfold centralLocal
  rw [norm_div,norm_div,gauss_unit_scale_norm _ (supported_power p hs (n+1)) h k
    ((hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right)]

theorem centralLocal_one_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero 0 h‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ := by
  rw [← mul_one h,centralLocal_unit_norm p hp hs 0 h 1 hph,centralLocal,
    gauss_prime_power_one p hp hg hc]
  simp only [ite_true,zero_add,pow_one,norm_div,Complex.norm_natCast,div_pow,
    primeGauss_actual_norm_sq p hp hg hc]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  field_simp

theorem centralLocal_seven_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero 6 (h*p^6)‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ := by
  rw [centralLocal_unit_norm p hp hs 6 h (p^6) hph,centralLocal_seven p hp hg hc,
    norm_div,Complex.norm_natCast,div_pow,primeGauss_actual_norm_sq p hp hg hc]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  field_simp

theorem centralLocal_six_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero 5 (h*p^6)‖^2 =
      (1 - (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹)^2 := by
  rw [centralLocal_unit_norm p hp hs 5 h (p^6) hph,centralLocal_six p hp hg hc]
  rw [← Complex.ofReal_natCast,← Complex.ofReal_inv,← Complex.ofReal_one,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

end SevenEighths.CenteredMomentAmplificationLocal

end

end OAI

end Source524

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationGlobal.lean; sha256: f91dac31155eadad18f47ab01509cb5ce4887290c2191a7d8858c3e12b8d7b81 -/
section Source525
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationGlobal
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentSupportedCorrelation CenteredMomentUnequal CenteredMomentGaussEnergy
open CenteredMomentAmplification ProbePhysical
local notation "O" => ActualEisensteinCubic.O

theorem full_column_unchanged (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ)
    (hn1 : n ≠ 1) (hn6 : n ≠ 6) (hn7 : n ≠ 7)
    (a : O) (ha : Supported (Ideal.span {a})) (hcop : IsCoprime p a)
    (h : O) (hph : ¬p ∣ h) :
    sexticGauss (p^n*a) (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supported_element_ne_zero a ha))
      (p^6*h) =
    sexticGauss (p^n*a) (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supported_element_ne_zero a ha)) h := by
  cases n with
  | zero =>
    simp only [pow_zero,one_mul]
    exact gauss_sixth_frequency a ha p h hcop
  | succ n =>
    rw [sexticGauss_coprime_product _ a (supported_power p hs (n+1)) ha hcop.pow_left,
      sexticGauss_coprime_product _ a (supported_power p hs (n+1)) ha hcop.pow_left,
      gauss_sixth_frequency a ha p h hcop,
      mul_comm (p^6) h,gauss_prime_power_unchanged p hp hs hg hc n
        (by omega) (by omega) (by omega) h hph]

def amplificationError {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (ν : α → ℕ) (p : O) (k : ℕ) (h : O) : ℂ :=
  ∑ i ∈ S, if ν i = k then c i *
    (gaussRow (a i) (ha i) h - gaussRow (a i) (ha i) (p^6*h)) else 0

theorem polynomial_amplification {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ν : α → ℕ) (r : α → O) (hr : ∀ i, Supported (Ideal.span {r i}))
    (hfactor : ∀ i ∈ S, a i = p^(ν i)*r i)
    (hcop : ∀ i ∈ S, IsCoprime p (r i)) (h : O) (hph : ¬p ∣ h) :
    gaussPolynomial S a ha c h = gaussPolynomial S a ha c (p^6*h) +
      amplificationError S a ha c ν p 1 h + amplificationError S a ha c ν p 6 h +
      amplificationError S a ha c ν p 7 h := by
  simp only [gaussPolynomial,amplificationError,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h1 : ν i = 1
  · simp only [h1,ite_true,show ¬(1:ℕ)=6 by decide,show ¬(1:ℕ)=7 by decide,ite_false]
    ring
  · by_cases h6 : ν i = 6
    · simp only [h6,ite_true,show ¬(6:ℕ)=1 by decide,show ¬(6:ℕ)=7 by decide,ite_false]
      ring
    · by_cases h7 : ν i = 7
      · simp only [h7,ite_true,show ¬(7:ℕ)=1 by decide,show ¬(7:ℕ)=6 by decide,ite_false]
        ring
      · simp only [h1,h6,h7,ite_false,add_zero]
        congr 1
        unfold gaussRow
        congr 1
        have he := full_column_unchanged p hp hs hg hc (ν i) h1 h6 h7
          (r i) (hr i) (hcop i hi) h hph
        simpa only [hfactor i hi] using he.symm

def primeRemainder (p : O) (hp : Prime p) (a : O) (ha : a ≠ 0) : O :=
  Classical.choose ((FiniteMultiplicity.of_prime_left hp ha).exists_eq_pow_mul_and_not_dvd)

theorem primeRemainder_spec (p : O) (hp : Prime p) (a : O) (ha : a ≠ 0) :
    a = p^(multiplicity p a)*primeRemainder p hp a ha ∧ ¬p ∣ primeRemainder p hp a ha :=
  Classical.choose_spec ((FiniteMultiplicity.of_prime_left hp ha).exists_eq_pow_mul_and_not_dvd)

theorem primeRemainder_supported (p : O) (hp : Prime p) (a : O)
    (ha : Supported (Ideal.span {a})) :
    Supported (Ideal.span {primeRemainder p hp a (supported_element_ne_zero a ha)}) := by
  have hs := ha
  rw [(primeRemainder_spec p hp a (supported_element_ne_zero a ha)).1,
    ← Ideal.span_singleton_mul_span_singleton,supported_mul_iff] at hs
  exact hs.2

theorem polynomial_amplification_actual {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    gaussPolynomial S a ha c h = gaussPolynomial S a ha c (p^6*h) +
      amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h +
      amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h +
      amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h := by
  apply polynomial_amplification S a ha c p hp hs hg hc _
    (fun i => primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i)))
    (fun i => primeRemainder_supported p hp (a i) (ha i))
  · exact fun i _ => (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).1
  · exact fun i _ => hp.irreducible.coprime_iff_not_dvd.mpr
      (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).2
  · exact hph

theorem norm_four_sum_sq (a b c d : ℂ) :
    ‖a+b+c+d‖^2 ≤ 4*(‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2) := by
  have hn : ‖a+b+c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
    calc
      _ ≤ ‖a+b+c‖ + ‖d‖ := norm_add_le _ _
      _ ≤ (‖a+b‖+‖c‖)+‖d‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add (norm_add_le a b) le_rfl) le_rfl
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖a‖-‖d‖),
    sq_nonneg (‖b‖-‖c‖),sq_nonneg (‖b‖-‖d‖),sq_nonneg (‖c‖-‖d‖)]

theorem polynomial_amplification_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ν : α → ℕ) (r : α → O) (hr : ∀ i, Supported (Ideal.span {r i}))
    (hfactor : ∀ i ∈ S, a i = p^(ν i)*r i)
    (hcop : ∀ i ∈ S, IsCoprime p (r i)) (h : O) (hph : ¬p ∣ h) :
    ‖gaussPolynomial S a ha c h‖^2 ≤ 4*(‖gaussPolynomial S a ha c (p^6*h)‖^2 +
      ‖amplificationError S a ha c ν p 1 h‖^2 +
      ‖amplificationError S a ha c ν p 6 h‖^2 +
      ‖amplificationError S a ha c ν p 7 h‖^2) := by
  rw [polynomial_amplification S a ha c p hp hs hg hc ν r hr hfactor hcop h hph]
  exact norm_four_sum_sq _ _ _ _

theorem eligible_pool_average {β : Type*} (P : Finset β) (hP : P.Nonempty)
    (H : ℂ) (A E₁ E₆ E₇ : β → ℂ)
    (hid : ∀ p ∈ P, H = A p + E₁ p + E₆ p + E₇ p) :
    ‖H‖^2 ≤ (4 / (P.card : ℝ)) *
      ∑ p ∈ P, (‖A p‖^2 + ‖E₁ p‖^2 + ‖E₆ p‖^2 + ‖E₇ p‖^2) := by
  have hc : (0 : ℝ) < P.card := Nat.cast_pos.mpr hP.card_pos
  have hb : (P.card : ℝ)*‖H‖^2 ≤ 4 *
      ∑ p ∈ P, (‖A p‖^2 + ‖E₁ p‖^2 + ‖E₆ p‖^2 + ‖E₇ p‖^2) := by
    have hb := Finset.sum_le_sum (s := P) (fun p hp => show ‖H‖^2 ≤
      4*(‖A p‖^2+‖E₁ p‖^2+‖E₆ p‖^2+‖E₇ p‖^2) by
        rw [hid p hp]
        exact norm_four_sum_sq _ _ _ _)
    simpa only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum] using hb
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  convert hb using 1 ; ring

theorem polynomial_pool_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (P : Finset O) (hP : P.Nonempty) (hp : ∀ p ∈ P, Prime p)
    (hs : ∀ p ∈ P, Supported (Ideal.span {p}))
    (hgood : ∀ p ∈ P, goodLambda ∉ Ideal.span {p})
    (hc : ∀ p ∈ P, ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (h : O) (hph : ∀ p ∈ P, ¬p ∣ h) :
    ‖gaussPolynomial S a ha c h‖^2 ≤ (4 / (P.card : ℝ)) *
      ∑ p ∈ P, (‖gaussPolynomial S a ha c (p^6*h)‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h‖^2) := by
  apply eligible_pool_average P hP
  intro p hpP
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (hp p hpP).irreducible
  exact polynomial_amplification_actual S a ha c p (hp p hpP) (hs p hpP)
    (hgood p hpP) (hc p hpP) h (hph p hpP)

end SevenEighths.CenteredMomentAmplificationGlobal

end

end OAI

end Source525

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationCount.lean; sha256: fa60d70ffaa73aa7e43bd0e43e4a7d86d437a1bab9f4dc2c0d8dedabc79ef9c2 -/
section Source526
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationCount
open UniqueFactorizationMonoid CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O

theorem primeDivisors_product_dvd (S : Finset (Ideal O))
    (hP : ∀ P ∈ S, Prime P) (I : Ideal O) (hd : ∀ P ∈ S, P ∣ I) :
    (∏ P ∈ S, P) ∣ I := by
  apply Finset.prod_dvd_of_coprime _ hd
  intro P hPS Q hQS hPQ
  let : P.IsMaximal := (Ideal.isPrime_of_prime (hP P hPS)).isMaximal (hP P hPS).ne_zero
  let : Q.IsMaximal := (Ideal.isPrime_of_prime (hP Q hQS)).isMaximal (hP Q hQS).ne_zero
  exact Ideal.isCoprime_of_isMaximal hPQ

theorem large_prime_divisor_count (S : Finset (Ideal O)) (hP : ∀ P ∈ S, Prime P)
    (I : Ideal O) (hI : I ≠ 0) (hd : ∀ P ∈ S, P ∣ I)
    (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ P ∈ S, Z^ℓ ≤ (Ideal.absNorm P : ℝ))
    (hupper : (Ideal.absNorm I : ℝ) ≤ Z^B) : (S.card : ℝ) ≤ B/ℓ := by
  have hpow : Z ^ (ℓ * (S.card : ℝ)) ≤ Z^B := by
    calc
      _ = (Z^ℓ)^S.card := Real.rpow_mul_natCast (zero_lt_one.trans hZ).le ℓ S.card
      _ = ∏ _P ∈ S, Z^ℓ := (Finset.prod_const _).symm
      _ ≤ ∏ P ∈ S, (Ideal.absNorm P : ℝ) := Finset.prod_le_prod₀
        (fun _ _ => Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hlower
      _ = (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by simp only [map_prod,Nat.cast_prod]
      _ ≤ (Ideal.absNorm I : ℝ) := norm_le_of_dvd hI (primeDivisors_product_dvd S hP I hd)
      _ ≤ _ := hupper
  have he := (Real.rpow_le_rpow_left_iff hZ).mp hpow
  apply (le_div_iff₀ hℓ).mpr
  simpa only [mul_comm] using he

theorem indexed_large_prime_divisor_count {α : Type*} (S : Finset α) (P : α → Ideal O)
    (hinj : Set.InjOn P S) (hp : ∀ i ∈ S, Prime (P i))
    (I : Ideal O) (hI : I ≠ 0) (hd : ∀ i ∈ S, P i ∣ I)
    (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ i ∈ S, Z^ℓ ≤ (Ideal.absNorm (P i) : ℝ))
    (hupper : (Ideal.absNorm I : ℝ) ≤ Z^B) : (S.card : ℝ) ≤ B/ℓ := by
  have hb := large_prime_divisor_count (S.image P) (by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hp i hi) I hI (by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hd i hi) Z ℓ B hZ hℓ (by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hlower i hi) hupper
  simpa only [Finset.card_image_of_injOn hinj] using hb

theorem amplified_row_fiber_count (F : Finset (O × O)) (y : O) (hy : y ≠ 0)
    (hprime : ∀ x ∈ F, Prime x.2)
    (hprimary : ∀ x ∈ F, ConcretePrimeRowBridge.goodLambda^2 ∣ x.2-1)
    (hrow : ∀ x ∈ F, x.2^6*x.1 = y)
    (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ x ∈ F, Z^ℓ ≤ (Ideal.absNorm (Ideal.span {x.2}) : ℝ))
    (hupper : (Ideal.absNorm (Ideal.span {y}) : ℝ) ≤ Z^B) : (F.card : ℝ) ≤ B/ℓ := by
  apply indexed_large_prime_divisor_count F (fun x => Ideal.span {x.2}) ?_
    (fun x hx => CubicEisenstein.gaussPrimeIdeal_prime x.2 (hprime x hx))
    (Ideal.span {y}) (Ideal.span_singleton_eq_bot.not.mpr hy) ?_ Z ℓ B hZ hℓ hlower hupper
  · intro x hx z hz heq
    have hp : x.2 = z.2 := by
      rw [← CompletedGauss.primaryGenerator_span x.2 (hprime x hx).ne_zero (hprimary x hx),
        ← CompletedGauss.primaryGenerator_span z.2 (hprime z hz).ne_zero (hprimary z hz)]
      exact congrArg CompletedGauss.primaryGenerator heq
    have hh : x.1 = z.1 := by
      apply mul_left_cancel₀ (pow_ne_zero 6 (hprime x hx).ne_zero)
      rw [hrow x hx,hp,hrow z hz]
    exact Prod.ext hh hp
  · intro x hx
    rw [Ideal.dvd_iff_le,Ideal.span_singleton_le_span_singleton,← hrow x hx]
    exact (dvd_pow_self x.2 (by decide : 6 ≠ 0)).trans (dvd_mul_right _ _)

theorem positive_pushforward_bound {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (g : β → ℝ) (C : ℝ)
    (hg : ∀ y ∈ S.image f, 0 ≤ g y)
    (hf : ∀ y ∈ S.image f, ((S.filter (fun x => f x = y)).card : ℝ) ≤ C) :
    (∑ x ∈ S, g (f x)) ≤ C * ∑ y ∈ S.image f, g y := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem f hx)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  calc
    _ = ((S.filter (fun x => f x = y)).card : ℝ) * g y := by
      rw [← nsmul_eq_mul,← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hf y hy) (hg y hy)

end SevenEighths.CenteredMomentAmplificationCount

end

end OAI

end Source526

/- Original source: OAI/NumberTheory/DirichletL/Moments/PrimePool.lean; sha256: 5147e754c3107eec3c8f49f62c4af701b9a7f9ff0e54a5025832466aca3744e7 -/
section Source527
namespace OAI

noncomputable section
open scoped BigOperators Classical Topology ContDiff
open Filter
namespace SevenEighths.CenteredMomentPrimePool
open HeckeFamily PNT.AnnularPrimeMass CenteredMomentAmplificationCount

def primePool (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (a b x : ℝ) : Finset (Ideal O) :=
  annularPrimeIdeals (RayQuotient.identityClass M H) a b x \ S

theorem annular_weighted_card_bound (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (a b B x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hW : ∀ y, W y ≤ B) (hx : 0 < x) :
    weightedPrimeSumDeleted C S W x ≤
      ((annularPrimeIdeals C a b x \ S).card : ℝ) * (B * a^(-5/6 : ℝ)) * x^(-5/6 : ℝ) := by
  rw [weightedPrimeSumDeleted_eq_annular C S W ha hab hsupp hx]
  calc
    _ ≤ ∑ _P ∈ annularPrimeIdeals C a b x \ S, B*(a*x)^(-5/6 : ℝ) := by
      apply Finset.sum_le_sum
      intro P hP
      have hn := (norm_bounds_of_mem_annularPrimeIdeals ha.le hab hx (Finset.mem_sdiff.mp hP).1).1
      apply mul_le_mul (hW _) _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hB
      exact Real.rpow_le_rpow_of_nonpos (mul_pos ha hx) (by nlinarith) (by norm_num)
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul,Real.mul_rpow ha.le hx.le]
      ring

section FixedRay
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

include hH

theorem eventually_primePool_card (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0)
    (a b B : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 < B)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hbound : ∀ y, W y ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c*x/Real.log x ≤ (primePool M H S a b x).card := by
  obtain ⟨c,hcpos,hlower⟩ := RayPrimeNormalizer.eventually_lower_bound M H hH S W hW hc hp hW0 hWne
  let D : ℝ := B*a^(-5/6 : ℝ)
  have hD : 0 < D := mul_pos hB (Real.rpow_pos_of_pos ha _)
  refine ⟨c/D,div_pos hcpos hD,?_⟩
  filter_upwards [hlower,eventually_gt_atTop (1 : ℝ)] with x hlow hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hu := annular_weighted_card_bound (RayQuotient.identityClass M H) S W a b B x
    ha hab hB.le hsupp hbound hx0
  change weightedPrimeSumDeleted _ S W x ≤ (primePool M H S a b x).card * D * x^(-5/6 : ℝ) at hu
  change c*x^(1/6 : ℝ)/Real.log x ≤ weightedPrimeSumDeleted _ S W x at hlow
  have hpower : x*x^(-5/6 : ℝ) = x^(1/6 : ℝ) := by
    calc
      _ = x^(1 : ℝ)*x^(-5/6 : ℝ) := by rw [Real.rpow_one]
      _ = x^((1 : ℝ)+(-5/6)) := (Real.rpow_add hx0 _ _).symm
      _ = _ := by norm_num
  have hmul : (c*x/Real.log x)*x^(-5/6 : ℝ) ≤
      ((primePool M H S a b x).card * D)*x^(-5/6 : ℝ) := by
    calc
      _ = c*(x*x^(-5/6 : ℝ))/Real.log x := by ring
      _ = _ := by rw [hpower]
      _ ≤ _ := hlow.trans hu
  have hcancel := le_of_mul_le_mul_right hmul (Real.rpow_pos_of_pos hx0 (-5/6 : ℝ))
  convert (div_le_iff₀ hD).mpr hcancel using 1 ; ring

end FixedRay

def eligiblePool (P : Finset (Ideal O)) (R : Ideal O) : Finset (Ideal O) :=
  P.filter (fun Q => ¬Q ∣ R)

theorem eligiblePool_card_lower (P : Finset (Ideal O)) (hp : ∀ Q ∈ P, Prime Q)
    (R : Ideal O) (hR : R ≠ 0) (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ Q ∈ P, Z^ℓ ≤ (Ideal.absNorm Q : ℝ))
    (hupper : (Ideal.absNorm R : ℝ) ≤ Z^B) :
    (P.card : ℝ) - B/ℓ ≤ (eligiblePool P R).card := by
  have hbad := large_prime_divisor_count (P.filter (fun Q => Q ∣ R))
    (fun Q hQ => hp Q (Finset.mem_filter.mp hQ).1) R hR
    (fun Q hQ => (Finset.mem_filter.mp hQ).2) Z ℓ B hZ hℓ
    (fun Q hQ => hlower Q (Finset.mem_filter.mp hQ).1) hupper
  have he := Finset.card_filter_add_card_filter_not (s := P) (fun Q => Q ∣ R)
  have her : ((P.filter (fun Q => Q ∣ R)).card : ℝ) + (eligiblePool P R).card = P.card := by
    exact_mod_cast he
  linarith

theorem eligiblePool_half (P : Finset (Ideal O)) (hp : ∀ Q ∈ P, Prime Q)
    (R : Ideal O) (hR : R ≠ 0) (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ Q ∈ P, Z^ℓ ≤ (Ideal.absNorm Q : ℝ))
    (hupper : (Ideal.absNorm R : ℝ) ≤ Z^B) (hsize : 2*(B/ℓ) ≤ P.card) :
    (P.card : ℝ)/2 ≤ (eligiblePool P R).card := by
  have h := eligiblePool_card_lower P hp R hR Z ℓ B hZ hℓ hlower hupper
  linarith

end SevenEighths.CenteredMomentPrimePool

end

end OAI

end Source527

/- Original source: OAI/NumberTheory/DirichletL/Moments/PrimeElements.lean; sha256: 5d0d52de73f648b4593ba0f52cb95f17d50db88e546d26e01566e37bdeea2147 -/
section Source528
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentPrimeElements
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentPrimePool CenteredMomentAmplificationGlobal
local notation "O" => ActualEisensteinCubic.O

def elementPool (P : Finset (Ideal O)) : Finset O := P.image primaryPrime

theorem primaryPrime_data (P : Ideal O) (hp : Prime P) (hbad : P ∉ fixedBadPrimes) :
    Prime (primaryPrime P) ∧ Ideal.span {primaryPrime P} = P ∧
    ConcretePrimeRowBridge.goodLambda^2 ∣ primaryPrime P - 1 ∧
    Supported (Ideal.span {primaryPrime P}) ∧
    ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {primaryPrime P} ∧
    ringChar (O ⧸ Ideal.span {primaryPrime P}) ≠ 2 := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := (prime_good_iff_not_bad P).mpr hbad
  have hn := primaryPrime_ne_zero P hg.1
  have hs := (primaryPrime_spec P hn).2.2
  have hsupport : Supported P := by
    refine ⟨hp.ne_zero,?_⟩
    intro Q hQ
    have he : Q = P := by
      simpa only [UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible,
        normalize_eq,Multiset.mem_singleton] using hQ
    subst Q
    exact hg
  refine ⟨?_,hs.1,hs.2,?_,?_,?_⟩
  · apply (Ideal.span_singleton_prime hn).mp
    rw [hs.1]
    infer_instance
  · rwa [hs.1]
  · rw [hs.1]
    exact hg.1
  · rw [hs.1]
    exact hg.2

theorem elementPool_card (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes) :
    (elementPool P).card = P.card := by
  apply Finset.card_image_of_injOn
  intro Q hQ R hR he
  rw [← (primaryPrime_data Q (hp Q hQ) (hbad Q hQ)).2.1,
    ← (primaryPrime_data R (hp R hR) (hbad R hR)).2.1,he]

theorem elementPool_data (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (p : O) (hpm : p ∈ elementPool P) :
    Prime p ∧ Ideal.span {p} ∈ P ∧
    ConcretePrimeRowBridge.goodLambda^2 ∣ p-1 ∧
    Supported (Ideal.span {p}) ∧
    ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p} ∧
    ringChar (O ⧸ Ideal.span {p}) ≠ 2 := by
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hpm
  obtain ⟨hpr,hspan,hprim,hs,hg,hc⟩ := primaryPrime_data Q (hp Q hQ) (hbad Q hQ)
  exact ⟨hpr,hspan.symm ▸ hQ,hprim,hs,hg,hc⟩

theorem eligible_not_dvd (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (R : Ideal O) (h : O) (hh : Ideal.span {h} ∣ R)
    (p : O) (hpm : p ∈ elementPool (eligiblePool P R)) : ¬p ∣ h := by
  have hd := elementPool_data (eligiblePool P R)
    (fun Q hQ => hp Q (Finset.mem_filter.mp hQ).1)
    (fun Q hQ => hbad Q (Finset.mem_filter.mp hQ).1) p hpm
  intro hph
  apply (Finset.mem_filter.mp hd.2.1).2
  exact (Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hph)).trans hh

theorem primePool_data (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (hS : fixedBadPrimes ⊆ S) (a b x : ℝ)
    (Q : Ideal O) (hQ : Q ∈ primePool M H S a b x) :
    Prime Q ∧ Q ∉ fixedBadPrimes := by
  obtain ⟨hQ,hQS⟩ := Finset.mem_sdiff.mp hQ
  exact ⟨((PNT.AnnularPrimeMass.mem_annularPrimeIdeals _ _ _ _ _).mp hQ).2.1,
    fun hbad => hQS (hS hbad)⟩

theorem elementPool_eligible (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (R : Ideal O) :
    (elementPool P).filter (fun p => ¬Ideal.span {p} ∣ R) =
      elementPool (eligiblePool P R) := by
  ext p
  simp only [elementPool,eligiblePool,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨Q,hQ,rfl⟩,hnot⟩
    refine ⟨Q,⟨hQ,?_⟩,rfl⟩
    rwa [← (primaryPrime_data Q (hp Q hQ) (hbad Q hQ)).2.1]
  · rintro ⟨Q,⟨hQ,hnot⟩,rfl⟩
    refine ⟨⟨Q,hQ,rfl⟩,?_⟩
    rwa [(primaryPrime_data Q (hp Q hQ) (hbad Q hQ)).2.1]

theorem eligible_element_card_half (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (R : Ideal O) (hR : R ≠ 0) (Z ell B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ Q ∈ P, Z^ell ≤ (Ideal.absNorm Q : ℝ))
    (hupper : (Ideal.absNorm R : ℝ) ≤ Z^B) (hsize : 2*(B/ell) ≤ P.card) :
    (P.card : ℝ)/2 ≤ ((elementPool P).filter (fun p => ¬Ideal.span {p} ∣ R)).card := by
  rw [elementPool_eligible P hp hbad R,elementPool_card (eligiblePool P R)
    (fun Q hQ => hp Q (Finset.mem_filter.mp hQ).1)
    (fun Q hQ => hbad Q (Finset.mem_filter.mp hQ).1)]
  exact eligiblePool_half P hp R hR Z ell B hZ hell hlower hupper hsize

theorem ideal_pool_polynomial_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (P : Finset (Ideal O)) (hne : P.Nonempty)
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (h : O) (hh : ∀ Q ∈ P, ¬Q ∣ Ideal.span {h}) :
    ‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c h‖^2 ≤ (4/(P.card : ℝ))*
      ∑ p ∈ elementPool P,
        (‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c (p^6*h)‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h‖^2) := by
  have he := polynomial_pool_bound S a ha c (elementPool P) (Finset.Nonempty.image hne _)
    (fun p hpm => (elementPool_data P hp hbad p hpm).1)
    (fun p hpm => (elementPool_data P hp hbad p hpm).2.2.2.1)
    (fun p hpm => (elementPool_data P hp hbad p hpm).2.2.2.2.1)
    (fun p hpm => (elementPool_data P hp hbad p hpm).2.2.2.2.2) h (by
      intro p hpm hph
      apply hh (Ideal.span {p}) (elementPool_data P hp hbad p hpm).2.1
      exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hph))
  simpa only [elementPool_card P hp hbad] using he

end SevenEighths.CenteredMomentPrimeElements

end

end OAI

end Source528

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationEnergy.lean; sha256: 805dd6717ecfea9de33eb2398e2b1d7f0504dddd379f899bf73e485b136f0c59 -/
section Source529
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationCount
local notation "O" => ActualEisensteinCubic.O

def eligiblePairs (rows P : Finset O) (allow : O → O → Prop) : Finset (O × O) :=
  (rows.product P).filter (fun x => allow x.1 x.2)

def outputRow (x : O × O) : O := x.2^6*x.1

theorem outputRow_norm (x : O × O) (Z M L : ℝ) (hZ : 0 < Z)
    (hh : (Ideal.absNorm (Ideal.span {x.1}) : ℝ) ≤ Z^M)
    (hp : (Ideal.absNorm (Ideal.span {x.2}) : ℝ) ≤ Z^L) :
    (Ideal.absNorm (Ideal.span {outputRow x}) : ℝ) ≤ Z^(M+6*L) := by
  calc
    _ = (Ideal.absNorm (Ideal.span {x.2}) : ℝ)^6 *
        (Ideal.absNorm (Ideal.span {x.1}) : ℝ) := by
      simp only [outputRow,← Ideal.span_singleton_mul_span_singleton,
        ← Ideal.span_singleton_pow,map_mul,map_pow,Nat.cast_mul,Nat.cast_pow]
    _ ≤ (Z^L)^6 * Z^M := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hp 6) hh
      (Nat.cast_nonneg _) (by positivity)
    _ = Z^(M+6*L) := by
      rw [← Real.rpow_mul_natCast hZ.le,← Real.rpow_add hZ]
      congr 1
      ring

theorem amplified_energy_pushforward (rows P : Finset O) (allow : O → O → Prop)
    (hrows : ∀ h ∈ rows, h ≠ 0) (hp : ∀ p ∈ P, Prime p)
    (hprimary : ∀ p ∈ P, ConcretePrimeRowBridge.goodLambda^2 ∣ p-1)
    (Z ell M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hpl : ∀ p ∈ P, Z^ell ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ))
    (hpu : ∀ p ∈ P, (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤ Z^L)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ Z^M)
    (H : O → ℂ) :
    (∑ x ∈ eligiblePairs rows P allow, ‖H (outputRow x)‖^2) ≤
      ((M+6*L)/ell)*∑ y ∈ (eligiblePairs rows P allow).image outputRow, ‖H y‖^2 := by
  apply positive_pushforward_bound _ outputRow (fun y => ‖H y‖^2) _ (fun _ _ => sq_nonneg _)
  intro y hy
  obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp hy
  have hxm := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have hy0 : y ≠ 0 := by
    rw [← hxy]
    exact mul_ne_zero (pow_ne_zero _ (hp x.2 hxm.2).ne_zero) (hrows x.1 hxm.1)
  apply amplified_row_fiber_count _ y hy0
  · intro z hz
    exact hp z.2 (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2
  · intro z hz
    exact hprimary z.2 (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2
  · intro z hz
    exact (Finset.mem_filter.mp hz).2
  · exact hZ
  · exact hell
  · intro z hz
    exact hpl z.2 (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2
  · rw [← hxy]
    exact outputRow_norm x Z M L (zero_lt_one.trans hZ) (hhu x.1 hxm.1) (hpu x.2 hxm.2)

theorem sum_eligiblePairs (rows P : Finset O) (allow : O → O → Prop) (f : O → O → ℝ) :
    (∑ h ∈ rows, ∑ p ∈ P.filter (allow h), f h p) =
      ∑ x ∈ eligiblePairs rows P allow, f x.1 x.2 := by
  simp only [eligiblePairs,Finset.sum_filter]
  exact (Finset.sum_product rows P (fun x : O × O => if allow x.1 x.2 then f x.1 x.2 else 0)).symm

def errorEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (h p : O) : ℝ :=
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h‖^2 +
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h‖^2 +
  ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h‖^2

theorem gauss_energy_amplification {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (rows P : Finset O) (allow : O → O → Prop)
    (hrows : ∀ h ∈ rows, h ≠ 0) (hp : ∀ p ∈ P, Prime p)
    (hs : ∀ p ∈ P, Supported (Ideal.span {p}))
    (hg : ∀ p ∈ P, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p})
    (hc : ∀ p ∈ P, ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : ∀ p ∈ P, ConcretePrimeRowBridge.goodLambda^2 ∣ p-1)
    (hallow : ∀ h ∈ rows, ∀ p ∈ P, allow h p → ¬p ∣ h)
    (κ : ℝ) (hκ : 0 < κ) (hsize : ∀ h ∈ rows, κ ≤ (P.filter (allow h)).card)
    (Z ell M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hpl : ∀ p ∈ P, Z^ell ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ))
    (hpu : ∀ p ∈ P, (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤ Z^L)
    (hhu : ∀ h ∈ rows, (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ Z^M) :
    (∑ h ∈ rows, ‖gaussPolynomial S a ha c h‖^2) ≤ (4/κ)*
      (((M+6*L)/ell)*(∑ y ∈ (eligiblePairs rows P allow).image outputRow,
        ‖gaussPolynomial S a ha c y‖^2) +
        ∑ x ∈ eligiblePairs rows P allow, errorEnergy S a ha c x.1 x.2) := by
  have hj : (∑ h ∈ rows, ‖gaussPolynomial S a ha c h‖^2) ≤
      (4/κ)*∑ x ∈ eligiblePairs rows P allow,
        (‖gaussPolynomial S a ha c (outputRow x)‖^2 + errorEnergy S a ha c x.1 x.2) := by
    change _ ≤ (4/κ)*∑ x ∈ eligiblePairs rows P allow,
      (‖gaussPolynomial S a ha c (x.2^6*x.1)‖^2 + errorEnergy S a ha c x.1 x.2)
    rw [← sum_eligiblePairs rows P allow (fun h p =>
      ‖gaussPolynomial S a ha c (p^6*h)‖^2 + errorEnergy S a ha c h p),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    have hn : (P.filter (allow h)).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (hκ.trans_le (hsize h hh)))
    have hb := polynomial_pool_bound S a ha c (P.filter (allow h)) hn
      (fun p hpP => hp p (Finset.mem_filter.mp hpP).1)
      (fun p hpP => hs p (Finset.mem_filter.mp hpP).1)
      (fun p hpP => hg p (Finset.mem_filter.mp hpP).1)
      (fun p hpP => hc p (Finset.mem_filter.mp hpP).1) h
      (fun p hpP => hallow h hh p (Finset.mem_filter.mp hpP).1 (Finset.mem_filter.mp hpP).2)
    calc
      _ ≤ (4 / ((P.filter (allow h)).card : ℝ)) *
          ∑ p ∈ P.filter (allow h), (‖gaussPolynomial S a ha c (p^6*h)‖^2 + errorEnergy S a ha c h p) := by
        simpa only [errorEnergy,add_assoc] using hb
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) hκ (hsize h hh))
        (Finset.sum_nonneg (fun p _ => add_nonneg (sq_nonneg _) (by unfold errorEnergy; positivity)))
  have hf := amplified_energy_pushforward rows P allow hrows hp hprimary Z ell M L hZ hell
    hpl hpu hhu (gaussPolynomial S a ha c)
  apply hj.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.sum_add_distrib]
  exact add_le_add hf le_rfl

end SevenEighths.CenteredMomentAmplificationEnergy

end

end OAI

end Source529

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationShortening.lean; sha256: 690b6d41b0f4b27f114990708e67eebb81725c20e7e51474065932900a479d77 -/
section Source530
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationShortening
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentAmplification CenteredMomentAmplificationLocal CenteredMomentAmplificationGlobal
open ProbePhysical
local notation "O" => ActualEisensteinCubic.O

def residualCharacter (p : O) (k : ℕ) (u : O) : ℂ :=
  sexticReciprocityPhase p u ^ k * idealRowHom u (Ideal.span {p}) ^ (2*k)

theorem crossFactor_primary (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1) :
    idealRowHom u (Ideal.span {p^k}) * idealRowHom (p^k) (Ideal.span {u}) =
      residualCharacter p k u := by
  rw [← Ideal.span_singleton_pow,map_pow,idealRowHom_argument_pow p k _ hu,
    idealRowHom_primary_reciprocity u p hup hpp hu hp,
    sexticReciprocityPhase_symm u p,mul_pow]
  unfold residualCharacter
  rw [show 2*k=k+k by omega,pow_add]
  ring

theorem gauss_primary_power_product (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1)
    (hcop : IsCoprime p u) (h : O) :
    sexticGauss (p^k*u) (mul_ne_zero (pow_ne_zero _ (supportedElement_ne_zero p hp))
      (supportedElement_ne_zero u hu)) h =
      residualCharacter p k u * sexticGauss (p^k) (pow_ne_zero _ (supportedElement_ne_zero p hp)) h *
        sexticGauss u (supportedElement_ne_zero u hu) h := by
  rw [sexticGauss_coprime_product (p^k) u (supported_power p hp k) hu hcop.pow_left,
    crossFactor_primary p u k hp hu hpp hup]

theorem residualCharacter_six (p u : O) (hp : Supported (Ideal.span {p})) :
    residualCharacter p 6 u = sexticReciprocityPhase p u ^ 6 *
      coprimalityMask u p := by
  unfold residualCharacter
  norm_num only
  rw [twelfth_power_mask p hp u]

def primeRoot (p : O) (k : ℕ) : ℂ :=
  (Real.sqrt ((Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)

theorem primeRoot_sq (p : O) (k : ℕ) :
    primeRoot p k * primeRoot p k = (Ideal.absNorm (Ideal.span {p}) : ℂ)^k := by
  rw [primeRoot,← Complex.ofReal_mul,Real.mul_self_sqrt (by positivity),Complex.ofReal_pow,
    Complex.ofReal_natCast]

theorem modulusRoot_product (p u : O) (k : ℕ) :
    (Real.sqrt (Ideal.absNorm (Ideal.span {p^k*u}) : ℝ) : ℂ) =
      primeRoot p k * (Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) := by
  simp only [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
    map_mul,map_pow,Nat.cast_mul,Nat.cast_pow,Real.sqrt_mul (by positivity :
      0 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)^k),Complex.ofReal_mul,primeRoot]

theorem gaussRow_shortening (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1)
    (hcop : IsCoprime p u) (h : O) :
    gaussRow (p^k*u) (supported_mul_elements _ _ (supported_power p hp k) hu) h =
      residualCharacter p k u *
        (sexticGauss (p^k) (pow_ne_zero _ (supportedElement_ne_zero p hp)) h / primeRoot p k) *
          gaussRow u hu h := by
  unfold gaussRow
  rw [gauss_primary_power_product p u k hp hu hpp hup hcop h,modulusRoot_product]
  ring

theorem central_error_shortening (p u : O) (n : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1)
    (hcop : IsCoprime p u) (h : O) :
    (gaussRow (p^(n+1)*u) (supported_mul_elements _ _ (supported_power p hp (n+1)) hu) h -
      gaussRow (p^(n+1)*u) (supported_mul_elements _ _ (supported_power p hp (n+1)) hu) (p^6*h)) /
        primeRoot p (n+1) =
      (centralLocal p (supportedElement_ne_zero p hp) n h -
        centralLocal p (supportedElement_ne_zero p hp) n (p^6*h)) *
          (residualCharacter p (n+1) u * gaussRow u hu h) := by
  rw [gaussRow_shortening p u (n+1) hp hu hpp hup hcop,
    gaussRow_shortening p u (n+1) hp hu hpp hup hcop]
  have hinv : gaussRow u hu (p^6*h) = gaussRow u hu h := by
    unfold gaussRow
    rw [gauss_sixth_frequency u hu p h hcop]
  rw [hinv]
  unfold centralLocal
  rw [← primeRoot_sq p (n+1)]
  ring

theorem supported_phase_sq (p u : O) (hp : Supported (Ideal.span {p}))
    (hu : Supported (Ideal.span {u})) : sexticReciprocityPhase p u ^ 2 = 1 := by
  unfold sexticReciprocityPhase
  exact_mod_cast QuadraticAllOddCRT.quadraticRaySign_sq _ _
    (supported_residue_odd p hp) (supported_residue_odd u hu)

theorem residualCharacter_moving (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1) :
    residualCharacter p k u = sexticReciprocityPhase p u ^ k *
      idealRowHom (p^(2*k)) (Ideal.span {u}) := by
  rw [residualCharacter,idealRowHom_argument_pow p (2*k) _ hu,
    idealRowHom_primary_reciprocity p u hpp hup hp hu,mul_pow,
    pow_mul,supported_phase_sq p u hp hu,one_pow,one_mul]

def errorScalar (p : O) (hp : p ≠ 0) (n : ℕ) (h : O) : ℂ :=
  centralLocal p hp n h - centralLocal p hp n (p^6*h)

theorem centralLocal_unit_zero (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) (hn : n ≠ 0)
    (h : O) (hph : ¬p ∣ h) : centralLocal p hp.ne_zero n h = 0 := by
  unfold centralLocal
  rw [← mul_one h,sexticGauss_unit_scale _ (supported_power p hs (n+1)) h 1
    ((hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right),
    gauss_prime_power_one p hp hg hc]
  simp only [hn,ite_false,mul_zero,zero_div]

theorem centralLocal_six_zero (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) (hn5 : n ≠ 5) (hn6 : n ≠ 6)
    (h : O) (hph : ¬p ∣ h) : centralLocal p hp.ne_zero n (p^6*h) = 0 := by
  unfold centralLocal
  rw [mul_comm (p^6) h,sexticGauss_unit_scale _ (supported_power p hs (n+1)) h (p^6)
    ((hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right),
    gauss_prime_power_six p hp hg hc]
  simp only [hn5,hn6,ite_false,mul_zero,zero_div]

theorem errorScalar_norms (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖errorScalar p hp.ne_zero 0 h‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ ∧
    ‖errorScalar p hp.ne_zero 5 h‖^2 = (1-(Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹)^2 ∧
    ‖errorScalar p hp.ne_zero 6 h‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ := by
  unfold errorScalar
  rw [centralLocal_six_zero p hp hs hg hc 0 (by decide) (by decide) h hph,
    centralLocal_unit_zero p hp hs hg hc 5 (by decide) h hph,
    centralLocal_unit_zero p hp hs hg hc 6 (by decide) h hph,
    sub_zero,zero_sub,zero_sub,norm_neg,norm_neg,mul_comm (p^6) h]
  exact ⟨centralLocal_one_norm_sq p hp hs hg hc h hph,
    centralLocal_six_norm_sq p hp hs hg hc h hph,
    centralLocal_seven_norm_sq p hp hs hg hc h hph⟩

theorem error_polynomial_shortening {α : Type*} (S : Finset α)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (u : α → O)
    (hu : ∀ i, Supported (Ideal.span {u i})) (hup : ∀ i, goodLambda^2 ∣ u i-1)
    (hcop : ∀ i, IsCoprime p (u i)) (c : α → ℂ) (h : O) :
    amplificationError S (fun i => p^(n+1)*u i)
      (fun i => supported_mul_elements _ _ (supported_power p hs (n+1)) (hu i))
      (fun i => c i / primeRoot p (n+1)) (fun i => multiplicity p (p^(n+1)*u i)) p (n+1) h =
      errorScalar p hp.ne_zero n h *
        gaussPolynomial S u hu (fun i => c i * residualCharacter p (n+1) (u i)) h := by
  unfold amplificationError gaussPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hv : multiplicity p (p^(n+1)*u i) = n+1 := by
    rw [multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp
      (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supportedElement_ne_zero _ (hu i)))),
      multiplicity_pow_self_of_prime hp,
      multiplicity_eq_zero_of_not_dvd (hp.irreducible.coprime_iff_not_dvd.mp (hcop i)),add_zero]
  dsimp only
  simp only [ite_eq_left hv]
  have he := central_error_shortening p (u i) n hs (hu i) hpp (hup i) (hcop i) h
  change _ = errorScalar p hp.ne_zero n h *
    (c i * residualCharacter p (n+1) (u i) * gaussRow (u i) (hu i) h)
  calc
    _ = c i * ((gaussRow (p^(n+1)*u i)
        (supported_mul_elements _ _ (supported_power p hs (n+1)) (hu i)) h -
      gaussRow (p^(n+1)*u i)
        (supported_mul_elements _ _ (supported_power p hs (n+1)) (hu i)) (p^6*h)) /
        primeRoot p (n+1)) := by ring
    _ = _ := by rw [he]; unfold errorScalar; ring

end SevenEighths.CenteredMomentAmplificationShortening

end

end OAI

end Source530

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationRectangle.lean; sha256: 0b81edbeea72cc93f83ce462bd1ddea5d8c3441246d48b9ad9ac34b28809be8d -/
section Source531
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentAmplificationRectangle
open CenteredMomentRectangle CenteredMomentExtraction CenteredMomentAmplificationShortening
local notation "O" => ActualEisensteinCubic.O

theorem centralRoot_extract (p : O) (hp : p ≠ 0) (k : ℕ) (T : ℝ) (hT : 0 < T) :
    (Real.sqrt T : ℂ)⁻¹ = (primeRoot p k)⁻¹ *
      (Real.sqrt (T / (Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)⁻¹ := by
  have hN : 0 < (Ideal.absNorm (Ideal.span {p}) : ℝ) := Nat.cast_pos.mpr
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp)))
  have hroot : Real.sqrt T = Real.sqrt ((Ideal.absNorm (Ideal.span {p}) : ℝ)^k) *
      Real.sqrt (T / (Ideal.absNorm (Ideal.span {p}) : ℝ)^k) := by
    rw [← Real.sqrt_mul (pow_nonneg hN.le k)]
    congr 1
    field_simp
  rw [hroot,Complex.ofReal_mul,mul_inv,primeRoot]

theorem centered_coefficient_prime_extract (p : O) (hp : p ≠ 0)
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ T : ℝ) (hT : 0 < T)
    (Q I J : Ideal O) (k j : ℕ) (hj : j ≤ k) :
    (Real.sqrt T : ℂ)⁻¹ *
      (idealWeight c χ R t (Q * ((Ideal.span {p})^j*I) * ((Ideal.span {p})^(k-j)*J)) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
          ((Ideal.span {p})^j*I) ((Ideal.span {p})^(k-j)*J)) =
      (idealWeight c χ R t ((Ideal.span {p})^k) / primeRoot p k) *
        ((Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)⁻¹ *
          (idealWeight c χ R t (Q*I*J) *
            idealRectangle W₁ W₂
              (X₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j)
              (X₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j))
              (Y₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j)
              (Y₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j)) I J)) := by
  rw [extracted_rectangle_coefficient,centralRoot_extract p hp k T hT]
  have hprod : Q*(Ideal.span {p})^j*(Ideal.span {p})^(k-j) = Q*(Ideal.span {p})^k := by
    rw [mul_assoc,← pow_add,Nat.add_sub_of_le hj]
  rw [hprod]
  simp only [idealWeight_mul,map_pow,Nat.cast_pow]
  ring

theorem centered_product_prime_extract (p : O) (k j : ℕ) (hj : j ≤ k)
    (X₁ X₂ Y₁ Y₂ T : ℝ) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j) *
      (X₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j)) =
        T/(Ideal.absNorm (Ideal.span {p}) : ℝ)^k ∧
    (Y₁/(Ideal.absNorm (Ideal.span {p}) : ℝ)^j) *
      (Y₂/(Ideal.absNorm (Ideal.span {p}) : ℝ)^(k-j)) =
        T/(Ideal.absNorm (Ideal.span {p}) : ℝ)^k := by
  simp only [div_mul_div_comm,← pow_add,Nat.add_sub_of_le hj,hX,hY,and_self]

end SevenEighths.CenteredMomentAmplificationRectangle

end

end OAI

end Source531

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationMask.lean; sha256: 4c5690d301bc881610a7669d54011a1b78f7f53521b9fc6decebf7b0a74d484b -/
section Source532
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentAmplificationMask
open CenteredMomentRectangle CenteredMomentAmplificationRectangle CenteredMomentAmplificationShortening
local notation "O" => ActualEisensteinCubic.O

theorem whole_product_divisibility (p : O) (s Q I J : Ideal O)
    (hcop : IsCoprime s (Ideal.span {p})) (k j : ℕ) (hj : j ≤ k) :
    s∣Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) ↔ s∣Q*I*J := by
  have he : Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) =
      (Ideal.span {p})^k*(Q*I*J) := by
    calc
      _ = ((Ideal.span {p})^j*(Ideal.span {p})^(k-j))*(Q*I*J) := by ring
      _ = _ := by rw [← pow_add,Nat.add_sub_of_le hj]
  rw [he]
  exact (hcop.pow_right (n := k)).dvd_mul_left_iff

theorem masked_centered_coefficient_prime_extract (p : O) (hp : p ≠ 0)
    (s : Ideal O) (hcop : IsCoprime s (Ideal.span {p}))
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ T : ℝ) (hT : 0 < T)
    (Q I J : Ideal O) (k j : ℕ) (hj : j ≤ k) :
    (Real.sqrt T:ℂ)⁻¹ *
      (idealWeight c χ R t (Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J))*
        CenteredMomentRectangle.idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
          ((Ideal.span {p})^j*I) ((Ideal.span {p})^(k-j)*J)) *
      (if s∣Q*((Ideal.span {p})^j*I)*((Ideal.span {p})^(k-j)*J) then (1:ℂ) else 0) =
      (idealWeight c χ R t ((Ideal.span {p})^k)/primeRoot p k)*
        ((Real.sqrt (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^k):ℂ)⁻¹ *
          (idealWeight c χ R t (Q*I*J)*
            CenteredMomentRectangle.idealRectangle W₁ W₂
              (X₁/(Ideal.absNorm (Ideal.span {p}):ℝ)^j)
              (X₂/(Ideal.absNorm (Ideal.span {p}):ℝ)^(k-j))
              (Y₁/(Ideal.absNorm (Ideal.span {p}):ℝ)^j)
              (Y₂/(Ideal.absNorm (Ideal.span {p}):ℝ)^(k-j)) I J)*
          (if s∣Q*I*J then (1:ℂ) else 0)) := by
  simp only [whole_product_divisibility p s Q I J hcop k j hj]
  rw [centered_coefficient_prime_extract p hp c χ R t W₁ W₂ X₁ X₂ Y₁ Y₂ T hT Q I J k j hj]
  ring

end SevenEighths.CenteredMomentAmplificationMask

end

end OAI

end Source532

/- Original source: OAI/NumberTheory/DirichletL/Hecke/ReciprocalBound.lean; sha256: b68d5ef937121a5834d1656a79cf6ca586ba643ca8d997127c3c820a19166fa4 -/
section Source533
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeReciprocalBound
open HeckeFamily

def bound (σ : ℝ) : ℝ :=
  ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight (σ : ℂ) I‖

theorem normWeight_le_of_re_ge {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) (I : Ideal O) :
    ‖CubicEisenstein.fullIdealWeight s I‖ ≤
      ‖CubicEisenstein.fullIdealWeight (σ : ℂ) I‖ := by
  by_cases hI : I = 0
  · simp [hI, CubicEisenstein.fullIdealWeight]
  · have hN : (1 : ℝ) ≤ Ideal.absNorm I := by
      have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff I).mpr (Ring.HasFiniteQuotients.finiteQuotient hI))
      exact_mod_cast hpos
    simp only [CubicEisenstein.fullIdealWeight, hI, ite_false]
    have hn : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one hN
    rw [show (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hs)

theorem reciprocal_norm_le (χ : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖HeckeReciprocal.reciprocal χ s‖ ≤ bound σ := by
  have hs1 : 1 < s.re := hσ.trans_le hs
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs1
  have hsp : s ≠ 1 := by intro h; norm_num [h] at hs1
  rw [HeckeReciprocal.reciprocal_eq_inv χ hs0 hsp, LFunction_eq_series χ hs1,
    ← IdealEuler.inverseSeries_eq_inv _ (idealCoeff_norm_le_one χ) s hs1]
  have hsum := IdealEuler.inverse_summable_norm (idealCoeff χ)
    (idealCoeff_norm_le_one χ) s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (CubicEisenstein.fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ))
  intro I
  change ‖(UniqueFactorizationMonoid.moebius I : ℂ) *
    (idealCoeff χ I * CubicEisenstein.fullIdealWeight s I)‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖CubicEisenstein.fullIdealWeight s I‖ := by
      apply (mul_le_of_le_one_left (by positivity)
        (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)
    _ ≤ _ := normWeight_le_of_re_ge hs I

end SevenEighths.HeckeReciprocalBound

end

end OAI

end Source533

/- Original source: OAI/NumberTheory/DirichletL/Hecke/Dyadic.lean; sha256: 532a488b08c81b0f60a9f765693a9cf26d800cd08caba9c261a79fb65921dcd3 -/
section Source534
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

abbrev NonzeroIdeal := UnrestrictedIdealReindex.NonzeroIdeal

private instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
private instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def norm (I : NonzeroIdeal) : ℝ := I.val.absNorm

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

def coefficient (χ : Character) (inverse : Bool) (I : Ideal O) : ℂ :=
  if inverse then (UniqueFactorizationMonoid.moebius I : ℂ)*idealCoeff χ I else idealCoeff χ I

theorem coefficient_norm_le (χ : Character) (inverse : Bool) (I : Ideal O) :
    ‖coefficient χ inverse I‖ ≤ 1 := by
  cases inverse
  · exact idealCoeff_norm_le_one χ I
  · change ‖(UniqueFactorizationMonoid.moebius I : ℂ)*idealCoeff χ I‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      (idealCoeff_norm_le_one χ I)

@[simp] theorem coefficient_zero (χ : Character) (inverse : Bool) : coefficient χ inverse 0 = 0 := by
  cases inverse
  · exact idealCoeff_zero χ
  · change (UniqueFactorizationMonoid.moebius (0 : Ideal O) : ℂ)*idealCoeff χ 0 = 0
    rw [idealCoeff_zero, mul_zero]

def shift (σ ω : ℝ) : ℂ := (σ : ℂ)-(ω : ℂ)*Complex.I

@[simp] theorem shift_re (σ ω : ℝ) : (shift σ ω).re = σ := by simp [shift]

def summand (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ ω : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ inverse I.val * W (norm I/D) * ((norm I/D : ℝ) : ℂ)^(-shift σ ω)

def polynomial (χ : Character) (inverse : Bool) (W : ℝ → ℂ) (D σ ω : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ)) * ∑' I : NonzeroIdeal, summand χ inverse W D σ ω I

theorem summand_finite_support (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b D σ ω : ℝ) (hD : 0 < D) (hW : Function.support W ⊆ Icc a b) :
    (Function.support (summand χ inverse W D σ ω)).Finite := by
  have hfin := Ideal.finite_setOfPred_absNorm_le (S := O) ⌈D*b⌉₊
  apply (Set.Finite.preimage (f := fun I : NonzeroIdeal => I.val) Subtype.val_injective.injOn hfin).subset
  intro I hI
  have hw : W (norm I/D) ≠ 0 := by
    intro h
    exact hI (by simp [summand, h])
  have hupper := (hW hw).2
  have hq : norm I ≤ D*b := by
    have h := (div_le_iff₀ hD).mp hupper
    linarith
  have hr : norm I ≤ (⌈D*b⌉₊ : ℝ) := hq.trans (Nat.le_ceil _)
  change I.val.absNorm ≤ ⌈D*b⌉₊
  dsimp [norm] at hr
  exact_mod_cast hr

def series (χ : Character) (inverse : Bool) (s : ℂ) : ℂ :=
  if inverse then HeckeReciprocal.reciprocal χ s else LFunction χ s

theorem series_eq_tsum (χ : Character) (inverse : Bool) {s : ℂ} (hs : 1 < s.re) :
    series χ inverse s =
      ∑' I : NonzeroIdeal, coefficient χ inverse I.val * (norm I : ℂ)^(-s) := by
  have he : (∑' I : NonzeroIdeal, coefficient χ inverse I.val *
      CubicEisenstein.fullIdealWeight s I.val) =
      ∑' I : Ideal O, coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I := by
    apply tsum_subtype_eq_of_support_subset
      (s := {I : Ideal O | I ≠ 0})
      (f := fun I : Ideal O => coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I)
    intro I hI hi
    subst I
    exact hI (by
      change coefficient χ inverse 0 * CubicEisenstein.fullIdealWeight s 0 = 0
      rw [coefficient_zero, zero_mul])
  have hc : (∑' I : NonzeroIdeal, coefficient χ inverse I.val * (norm I : ℂ)^(-s)) =
      ∑' I : Ideal O, coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I := by
    rw [← he]
    apply tsum_congr
    intro I
    have hI : I.val ≠ 0 := I.property
    rw [CubicEisenstein.fullIdealWeight, ite_eq_right hI]
    simp only [norm, Complex.ofReal_natCast]
  rw [hc]
  cases inverse
  · exact LFunction_eq_series χ hs
  · have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
    change HeckeReciprocal.reciprocal χ s = _
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1, LFunction_eq_series χ hs,
      ← IdealEuler.inverseSeries_eq_inv _ (idealCoeff_norm_le_one χ) s hs]
    apply tsum_congr
    intro I
    simp only [coefficient,  ite_true, IdealEuler.weighted,
      IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    ring

end SevenEighths.HeckeDyadic

end

end OAI

end Source534

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorRowSpecialization.lean; sha256: cc461149e20ee542203ce8324c9255ee2b82d1cf06996d8176e94a324e096b3a -/
section Source535
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRowSpecialization
open HeckeFamily HeckeDyadic HeckeRowClosure

theorem inverse_polynomial_original_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ true W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑' J : NonzeroIdeal,
        (UniqueFactorizationMonoid.moebius J.val : ℂ)*idealCoeff η J.val*
          CanonicalRowCompletion.idealRowHom (m^6*f^4*z) J.val*
          W (norm J/D)*((norm J/D : ℝ) : ℂ)^(-shift σ freq) := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  unfold summand coefficient
  simp only [ite_true,idealCoeff_eq_row η χ m f z heq]
  ring

theorem plain_polynomial_original_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ false W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑' J : NonzeroIdeal,
        idealCoeff η J.val*CanonicalRowCompletion.idealRowHom (m^6*f^4*z) J.val*
          W (norm J/D)*((norm J/D : ℝ) : ℂ)^(-shift σ freq) := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  unfold summand coefficient
  simp only [Bool.false_eq_true,ite_false,idealCoeff_eq_row η χ m f z heq]

end SevenEighths.HeckeDetectorRowSpecialization

end

end OAI

end Source535

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationRows.lean; sha256: 5aba9352dc9c92b7fb7052957d9215cb2272087e3b791de6b3cb70c52fded135 -/
section Source536
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily UniqueFactorizationMonoid

def SixthFree (I : Ideal O) : Prop := ∀ P, (normalizedFactors I).count P<6

theorem ideal_decomposition_unique {I J A B : Ideal O}
    (hI : I≠0) (hJ : J≠0) (hA : A≠0) (hB : B≠0)
    (hIf : SixthFree I) (hJf : SixthFree J) (he : I*A^6=J*B^6) :
    I=J ∧ A=B := by
  have hf := congrArg normalizedFactors he
  rw [normalizedFactors_mul hI (pow_ne_zero _ hA),
    normalizedFactors_mul hJ (pow_ne_zero _ hB),normalizedFactors_pow,normalizedFactors_pow] at hf
  have hc (P : Ideal O) := congrArg (Multiset.count P) hf
  have hcounts (P : Ideal O) :
      (normalizedFactors I).count P=(normalizedFactors J).count P ∧
      (normalizedFactors A).count P=(normalizedFactors B).count P := by
    have hh := hc P
    simp only [Multiset.count_add,Multiset.count_nsmul] at hh
    have hi := hIf P
    have hj := hJf P
    omega
  have hIJ : normalizedFactors I=normalizedFactors J :=
    Multiset.ext.mpr (fun P => (hcounts P).1)
  have hAB : normalizedFactors A=normalizedFactors B :=
    Multiset.ext.mpr (fun P => (hcounts P).2)
  constructor
  · simpa only [Ideal.prod_normalizedFactors_eq_self hI,Ideal.prod_normalizedFactors_eq_self hJ]
      using congrArg Multiset.prod hIJ
  · simpa only [Ideal.prod_normalizedFactors_eq_self hA,Ideal.prod_normalizedFactors_eq_self hB]
      using congrArg Multiset.prod hAB

abbrev FreeRow := {u : O // u≠0 ∧ SixthFree (Ideal.span {u})}
abbrev NonzeroIdeal := UnrestrictedIdealReindex.NonzeroIdeal

def rowMap (p : FreeRow×NonzeroIdeal) : O :=
  p.1.val*(ConcretePrimeRowBridge.idealGenerator p.2.val)^6

theorem rowMap_ne_zero (p : FreeRow×NonzeroIdeal) : rowMap p≠0 :=
  mul_ne_zero p.1.property.1 (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero
    p.2.val p.2.property))

theorem rowMap_span (p : FreeRow×NonzeroIdeal) :
    Ideal.span {rowMap p}=Ideal.span {p.1.val}*p.2.val^6 := by
  unfold rowMap
  rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow,
    ConcretePrimeRowBridge.span_idealGenerator]

theorem rowMap_injective : Function.Injective rowMap := by
  intro p q hpq
  have he := congrArg (fun u : O => Ideal.span {u}) hpq
  rw [rowMap_span,rowMap_span] at he
  have hd := ideal_decomposition_unique
    (Ideal.span_singleton_eq_bot.not.mpr p.1.property.1)
    (Ideal.span_singleton_eq_bot.not.mpr q.1.property.1)
    p.2.property q.2.property p.1.property.2 q.1.property.2 he
  have ha : p.2=q.2 := Subtype.ext hd.2
  apply Prod.ext
  · apply Subtype.ext
    change p.1.val*(ConcretePrimeRowBridge.idealGenerator p.2.val)^6=
      q.1.val*(ConcretePrimeRowBridge.idealGenerator q.2.val)^6 at hpq
    rw [ha] at hpq
    exact mul_right_cancel₀ (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero
      q.2.val q.2.property)) hpq
  · exact ha

theorem rowMap_norm (p : FreeRow×NonzeroIdeal) :
    (Ideal.span {rowMap p}).absNorm=(Ideal.span {p.1.val}).absNorm*p.2.val.absNorm^6 := by
  rw [rowMap_span,map_mul,map_pow]

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source536

/- Original source: OAI/NumberTheory/DirichletL/TraceCharacter.lean; sha256: 4589b073e682eaf08d284c02447ad938c1197c7f3879a06674886a1890cb2703 -/
section Source537
namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap

namespace SevenEighths.TraceCharacter

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic EisensteinEmbedding ConcreteTraceCRT
open EisensteinSchwartzPoisson FiniteFourier

def traceCharacter (c : O) (hc : c ≠ 0) : AddChar (O ⧸ Ideal.span {c}) ℂ :=
  eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc

theorem traceCharacter_mk (c : O) (hc : c ≠ 0) (x : O) :
    traceCharacter c hc (Ideal.Quotient.mk (Ideal.span {c}) x) =
      ShortDraftTrace.breveE (eisEmbedding x / (eisEmbedding c * eisLam)) := by
  simp only [traceCharacter, eisTraceModChar, IdealGaussCRT.traceModChar_mk]

theorem traceCharacter_eq_paperE (c : O) (hc : c ≠ 0) (x : O) :
    traceCharacter c hc (Ideal.Quotient.mk (Ideal.span {c}) x) =
      paperE (eisEmbedding x / eisEmbedding c) :=
  eisTraceModChar_eq_paperE c hc x

theorem traceCharacter_isPrimitive (c : O) (hc : c ≠ 0) :
    (traceCharacter c hc).IsPrimitive :=
  GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

theorem residue_card :
    Fintype.card (O ⧸ Ideal.span {c}) = Ideal.absNorm (Ideal.span {c}) := by
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

def gaussScalar (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ :=
  gaussSum χ (traceCharacter c (NeZero.ne c))

theorem transform_nonunit (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) (ha : ¬ IsUnit a) :
    (∑ x : O ⧸ Ideal.span {c}, χ x * traceCharacter c (NeZero.ne c) (a * x)) = 0 :=
  gaussSum_mulShift_nonunit_eq_zero χ hχ (traceCharacter c (NeZero.ne c)) ha

theorem transform_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) :
    (∑ x : O ⧸ Ideal.span {c}, χ x * traceCharacter c (NeZero.ne c) (a * x)) =
      χ⁻¹ a * gaussScalar c χ :=
  transform_primitive_character χ hχ (traceCharacter c (NeZero.ne c)) a

theorem paper_transform_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (h : O) :
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      paperE (eisEmbedding (GaussianShiftedPartition.representative c x) *
        eisEmbedding h / eisEmbedding c)) =
      χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) * gaussScalar c χ := by
  simpa only [traceCharacter, eisTraceModChar_frequency] using
    transform_eq c χ hχ (Ideal.Quotient.mk (Ideal.span {c}) h)

theorem gaussScalar_norm_sq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ ^ 2 = (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
  simpa only [gaussScalar, residue_card c] using
    primitive_gaussSum_norm_sq χ hχ (traceCharacter c (NeZero.ne c))
      (traceCharacter_isPrimitive c (NeZero.ne c))

theorem gaussScalar_norm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ = Real.sqrt (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
  rw [← gaussScalar_norm_sq c χ hχ, Real.sqrt_sq (norm_nonneg _)]

theorem gaussScalar_norm_embedding (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ = ‖eisEmbedding c‖ := by
  rw [gaussScalar_norm c χ hχ, ← eisEmbedding_norm_sq_eq_absNorm_span,
    Real.sqrt_sq (norm_nonneg _)]

theorem gaussScalar_ne_zero (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : gaussScalar c χ ≠ 0 :=
  primitive_gaussSum_ne_zero χ hχ (traceCharacter c (NeZero.ne c))
    (traceCharacter_isPrimitive c (NeZero.ne c))

def normalizedGauss (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ :=
  gaussScalar c χ / (‖eisEmbedding c‖ : ℂ)

theorem normalizedGauss_norm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : ‖normalizedGauss c χ‖ = 1 := by
  rw [normalizedGauss, norm_div, gaussScalar_norm_embedding c χ hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))]

theorem character_expansion (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) :
    χ a = (∑ x : O ⧸ Ideal.span {c}, χ⁻¹ x * traceCharacter c (NeZero.ne c) (a * x)) /
      gaussScalar c χ⁻¹ :=
  primitive_character_expansion χ hχ (traceCharacter c (NeZero.ne c))
    (traceCharacter_isPrimitive c (NeZero.ne c)) a

theorem primitive_paper_poisson (f : 𝓢(ℂ, ℂ))
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (gaussScalar c χ / (Ideal.absNorm (Ideal.span {c}) : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  have hp := actual_eisenstein_paper_poisson_trace f c (NeZero.ne c) χ
  change _ = (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      traceCharacter c (NeZero.ne c) (Ideal.Quotient.mk (Ideal.span {c}) h * x)) *
        paperFourier f (eisEmbedding h / eisEmbedding c) at hp
  simp_rw [transform_eq c χ hχ] at hp
  rw [hp, ← tsum_mul_left]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    eisEmbedding_norm_sq_eq_absNorm_span, Complex.ofReal_natCast]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

theorem primitive_radial_paper_poisson (W : 𝓢(ℝ, ℂ)) (scale : ℝ)
    (hscale : 0 < scale) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * gaussScalar c χ / (Ideal.absNorm (Ideal.span {c}) : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (Ideal.span {c}) : ℝ)) := by
  have hp := actual_radial_paper_poisson_trace W scale hscale c (NeZero.ne c) χ
  change _ = (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      traceCharacter c (NeZero.ne c) (Ideal.Quotient.mk (Ideal.span {c}) h * x)) *
        paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [transform_eq c χ hχ, eisEmbedding_norm_sq_eq_absNorm_span c] at hp
  rw [hp, ← tsum_mul_left]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

theorem primitive_radial_paper_poisson_normalized (W : 𝓢(ℝ, ℂ)) (scale : ℝ)
    (hscale : 0 < scale) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * normalizedGauss c χ / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  have hp := primitive_radial_paper_poisson c W scale hscale χ hχ
  rw [← eisEmbedding_norm_sq_eq_absNorm_span c] at hp
  have hnorm : (Ideal.absNorm (Ideal.span {c}) : ℂ) = (‖eisEmbedding c‖ : ℂ) ^ 2 := by
    exact_mod_cast (eisEmbedding_norm_sq_eq_absNorm_span c).symm
  rw [hnorm] at hp
  rw [hp]
  congr 1
  rw [normalizedGauss]
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))
  field_simp

end SevenEighths.TraceCharacter

end

end OAI

end Source537

/- Original source: OAI/NumberTheory/DirichletL/TraceConductor.lean; sha256: 8fa161f44ec9988d35ff37ec2ebaf5e8165cc84a35c647011961fd4f6266503d -/
section Source538
namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap Classical

namespace SevenEighths.TraceConductor

abbrev O := ActualEisensteinCubic.O

open FiniteFourier CharacterTransport ConcretePrimeRowBridge
open ConcreteTraceCRT EisensteinSchwartzPoisson

structure PrimitivePresentation (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ) where
  generator : O
  generator_ne_zero : generator ≠ 0
  character : MulChar (O ⧸ Ideal.span {generator}) ℂ
  primitive : IsPrimitiveOnIdeals character
  modulus_le : M ≤ Ideal.span {generator}
  norm_le : Ideal.absNorm (Ideal.span {generator}) ≤ M.absNorm
  source_mask : ∀ a : O, χ (Ideal.Quotient.mk M a) =
    if IsUnit (Ideal.Quotient.mk M a) then
      character (Ideal.Quotient.mk (Ideal.span {generator}) a) else 0

theorem exists_primitivePresentation (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ) : Nonempty (PrimitivePresentation M χ) := by
  let : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  obtain ⟨K, φ, hMK, hK, hφ, hnorm, hmask⟩ :=
    ConductorPresentation.exists_primitive_presentation M χ
  let c := idealGenerator K
  let e : (O ⧸ Ideal.span {c}) ≃+* (O ⧸ K) :=
    Ideal.quotEquivOfEq (span_idealGenerator K)
  let θ := pullback e φ
  refine ⟨{
    generator := c
    generator_ne_zero := idealGenerator_ne_zero K hK
    character := θ
    primitive := primitive_pullback e φ hφ
    modulus_le := ?_
    norm_le := ?_
    source_mask := ?_ }⟩
  · simpa only [c, span_idealGenerator] using hMK
  · simpa only [c, span_idealGenerator] using hnorm
  · intro a
    simpa only [θ, pullback_apply, e, Ideal.quotEquivOfEq_mk] using hmask a

def primitivePresentation (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ) : PrimitivePresentation M χ :=
  Classical.choice (exists_primitivePresentation M hM χ)

namespace PrimitivePresentation

variable {M : Ideal O} {χ : MulChar (O ⧸ M) ℂ}

def conductor (P : PrimitivePresentation M χ) : Ideal O := Ideal.span {P.generator}

theorem conductor_ne_bot (P : PrimitivePresentation M χ) : P.conductor ≠ ⊥ := by
  intro h
  exact P.generator_ne_zero (Ideal.span_singleton_eq_bot.mp h)

def gauss (P : PrimitivePresentation M χ) : ℂ := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.gaussScalar P.generator P.character

theorem gauss_norm (P : PrimitivePresentation M χ) :
    ‖P.gauss‖ = Real.sqrt (P.conductor.absNorm : ℝ) := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.gaussScalar_norm P.generator P.character P.primitive

theorem gauss_ne_zero (P : PrimitivePresentation M χ) : P.gauss ≠ 0 := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.gaussScalar_ne_zero P.generator P.character P.primitive

def fourier (P : PrimitivePresentation M χ) (a : O ⧸ P.conductor) : ℂ := by
  let : Finite (O ⧸ Ideal.span {P.generator}) := finite_quotient_span P.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {P.generator}) := Fintype.ofFinite _
  exact transform (TraceCharacter.traceCharacter P.generator P.generator_ne_zero) P.character a

theorem fourier_eq (P : PrimitivePresentation M χ) (a : O ⧸ P.conductor) :
    P.fourier a = P.character⁻¹ a * P.gauss := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.transform_eq P.generator P.character P.primitive a

theorem fourier_nonunit (P : PrimitivePresentation M χ) (a : O ⧸ P.conductor)
    (ha : ¬ IsUnit a) : P.fourier a = 0 := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.transform_nonunit P.generator P.character P.primitive a ha

theorem source_sum_eq_masked (P : PrimitivePresentation M χ) (f : O → ℂ) :
    (∑' a : O, χ (Ideal.Quotient.mk M a) * f a) =
      ∑' a : O, (if IsUnit (Ideal.Quotient.mk M a) then
        P.character (Ideal.Quotient.mk P.conductor a) else 0) * f a := by
  apply tsum_congr
  intro a
  rw [P.source_mask]
  rfl

def normalizedGauss (P : PrimitivePresentation M χ) : ℂ := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.normalizedGauss P.generator P.character

theorem normalizedGauss_norm (P : PrimitivePresentation M χ) :
    ‖P.normalizedGauss‖ = 1 := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.normalizedGauss_norm P.generator P.character P.primitive

theorem paper_poisson (P : PrimitivePresentation M χ) (f : 𝓢(ℂ, ℂ)) :
    (∑' z : O, P.character (Ideal.Quotient.mk P.conductor z) * f (eisEmbedding z)) =
      (P.gauss / (P.conductor.absNorm : ℂ)) *
        ∑' h : O, P.character⁻¹ (Ideal.Quotient.mk P.conductor h) *
          paperFourier f (eisEmbedding h / eisEmbedding P.generator) := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.primitive_paper_poisson P.generator f P.character P.primitive

theorem radial_paper_poisson (P : PrimitivePresentation M χ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, P.character (Ideal.Quotient.mk P.conductor z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * P.normalizedGauss / (‖eisEmbedding P.generator‖ : ℂ)) *
        ∑' h : O, P.character⁻¹ (Ideal.Quotient.mk P.conductor h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding P.generator‖ ^ 2) := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.primitive_radial_paper_poisson_normalized
    P.generator W scale hscale P.character P.primitive

end PrimitivePresentation

end SevenEighths.TraceConductor

end

end OAI

end Source538

/- Original source: OAI/NumberTheory/DirichletL/GaussianTheta.lean; sha256: ae3496a86f536df3c5eb068eb006818cfe15c1de183946de06b1b46a250d1e8f -/
section Source539
namespace OAI

noncomputable section

open scoped BigOperators Classical FourierTransform

namespace SevenEighths.GaussianTheta

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic EisensteinEmbedding ConcreteTraceCRT EisensteinSchwartzPoisson

def gaussian (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (‖z‖ : ℂ) ^ 2)

def coordinate (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * omega3

theorem omega3_re : omega3.re = -(1 / 2 : ℝ) := by norm_num [omega3]

theorem coordinate_norm_sq (x y : ℝ) :
    ‖coordinate x y‖ ^ 2 = RankTwoEisShift.Q x y := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [coordinate, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, omega3_re, omega3_im, zero_mul, zero_add,
    add_zero, sub_zero]
  unfold RankTwoEisShift.Q
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem exists_coordinate (w : ℂ) : ∃ x y : ℝ, w = coordinate x y := by
  let v := (basisEquiv omega3 omega3_im_ne_zero).symm w
  refine ⟨v.re, v.im, ?_⟩
  have h := (basisEquiv omega3 omega3_im_ne_zero).apply_symm_apply w
  simpa only [basisEquiv_apply, coordinate, mul_comm] using h.symm

theorem coordinate_dual_phase (x y : ℝ) (p : ℤ × ℤ) :
    paperE (coordinate x y * eisEmbedding (dualFrequencyEquiv p)) =
      RankTwoEisShift.dualPhase p.1 p.2 x y := by
  rw [paperE_eq_exp, dualFrequencyEquiv_coordinates]
  simp only [coordinate, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, omega3_re, omega3_im,
    zero_mul, zero_add, add_zero, sub_zero, complexPoint]
  unfold RankTwoEisShift.dualPhase
  congr 1
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  push_cast
  field_simp
  ring

theorem gaussian_coordinate_shift (a x y : ℝ) (p : ℤ × ℤ) :
    gaussian a (eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) +
      coordinate x y) = RankTwoEisShift.shifted a x y p := by
  have he : eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) + coordinate x y =
      coordinate ((p.1 : ℝ) + x) ((p.2 : ℝ) + y) := by
    rw [eisEmbedding_eval]
    simp only [coordinate, Complex.ofReal_add, Complex.ofReal_intCast]
    ring
  rw [he]
  unfold gaussian RankTwoEisShift.shifted
  rw [← Complex.ofReal_pow, coordinate_norm_sq]
  congr 1
  push_cast
  ring

theorem gaussian_dual_coordinate (a : ℝ) (p : ℤ × ℤ) :
    gaussian a (eisEmbedding (dualFrequencyEquiv p)) =
      Complex.exp (((-Real.pi * a * RankTwoPoisson.eisQ (p.1, -p.2) : ℝ) : ℂ)) := by
  unfold gaussian
  rw [← Complex.ofReal_pow, dualFrequencyEquiv_norm_sq]
  unfold RankTwoPoisson.eisQ
  congr 1
  push_cast
  ring

theorem shifted_prefactor (a : ℝ) (ha : 0 < a) :
    (1 / (a : ℂ) ^ (1 / 2 : ℂ)) *
      (1 / (((3 * a / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) =
      ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) := by
  have h := EisensteinGaussianPrefactor.complex_eta_times_prefactor a 1 ha (by norm_num)
  simp only [mul_one] at h
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  apply (mul_left_cancel₀ ha0)
  rw [← mul_assoc, h]
  push_cast
  field_simp

theorem shifted_lattice_poisson (a : ℝ) (ha : 0 < a) (w : ℂ) :
    (∑' z : O, gaussian a (eisEmbedding z + w)) =
      ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) *
        ∑' h : O, paperE (w * eisEmbedding h) *
          gaussian (4 / (3 * a)) (eisEmbedding h) := by
  obtain ⟨x, y, rfl⟩ := exists_coordinate w
  have hp := RankTwoEisShift.shifted_eisenstein_gaussian_poisson ha x y
  rw [shifted_prefactor a ha] at hp
  change (∑' p : ℤ × ℤ, RankTwoEisShift.shifted a x y p) =
    ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) * ∑' p : ℤ × ℤ,
      Complex.exp (((-Real.pi * (4 / (3 * a)) * RankTwoPoisson.eisQ (p.1, -p.2) : ℝ) : ℂ)) *
        RankTwoEisShift.dualPhase p.1 p.2 x y at hp
  calc
    _ = ∑' p : ℤ × ℤ, gaussian a
        (eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) + coordinate x y) :=
      (latticeCoordEquiv.symm.tsum_eq _).symm
    _ = ∑' p : ℤ × ℤ, RankTwoEisShift.shifted a x y p := by
      apply tsum_congr
      exact gaussian_coordinate_shift a x y
    _ = _ := by
      rw [hp]
      congr 1
      rw [← dualFrequencyEquiv.tsum_eq]
      apply tsum_congr
      intro p
      rw [coordinate_dual_phase, gaussian_dual_coordinate]
      exact mul_comm _ _

theorem gaussian_mul (a : ℝ) (z w : ℂ) :
    gaussian a (z * w) = gaussian (a * ‖z‖ ^ 2) w := by
  unfold gaussian
  rw [norm_mul]
  congr 1
  push_cast
  ring

theorem gaussian_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun z : O => gaussian a (eisEmbedding z)) := by
  exact eis_gaussian_summable ha

theorem paperE_norm (z : ℂ) : ‖paperE z‖ = 1 := by
  rw [paperE_eq_exp, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem weighted_gaussian_summable {R : Type*} [Fintype R]
    (q : O → R) (P : R → ℂ) (a : ℝ) (ha : 0 < a) :
    Summable (fun z : O => P (q z) * gaussian a (eisEmbedding z)) := by
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun r _ => norm_nonneg (P r)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((gaussian_summable a ha).norm.mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP _) (norm_nonneg _)

theorem gaussian_coset_poisson (a : ℝ) (ha : 0 < a) (c : O) (hc : c ≠ 0) (r : O) :
    (∑' z : O, gaussian a (eisEmbedding (r + c * z))) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        ∑' h : O, paperE (eisEmbedding r * eisEmbedding h / eisEmbedding c) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  have hc' := eisEmbedding_ne_zero hc
  have hscale : 0 < a * ‖eisEmbedding c‖ ^ 2 :=
    mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hc'))
  have he (z : O) : eisEmbedding (r + c * z) =
      eisEmbedding c * (eisEmbedding z + eisEmbedding r / eisEmbedding c) := by
    rw [map_add, map_mul]
    field_simp
    ring
  simp_rw [he, gaussian_mul]
  rw [shifted_lattice_poisson _ hscale]
  congr 1
  apply tsum_congr
  intro h
  congr 2
  ring

theorem finite_gaussian_phase_sum {R : Type*} [Fintype R]
    (a : ℝ) (ha : 0 < a) (b : R → ℂ) (P : R → ℂ) (K : ℂ) :
    (∑ r : R, P r * (K * ∑' h : O,
      paperE (b r * eisEmbedding h) * gaussian a (eisEmbedding h))) =
      K * ∑' h : O, (∑ r : R, P r * paperE (b r * eisEmbedding h)) *
        gaussian a (eisEmbedding h) := by
  have hs (r : R) : Summable (fun h : O =>
      P r * (paperE (b r * eisEmbedding h) * gaussian a (eisEmbedding h))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [norm_mul, paperE_norm, one_mul] using (gaussian_summable a ha).norm
  simp_rw [mul_left_comm (P _) K, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r _ => (hs r).mul_left K)]
  apply tsum_congr
  intro h
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

theorem periodic_gaussian_poisson (P : O ⧸ Ideal.span {c} → ℂ)
    (a : ℝ) (ha : 0 < a) :
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (eisEmbedding z)) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        ∑' h : O, (∑ r : O ⧸ Ideal.span {c}, P r *
          TraceCharacter.traceCharacter c (NeZero.ne c)
            (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c})) P (fun z => gaussian a (eisEmbedding z))
    (weighted_gaussian_summable _ P a ha)]
  have hfiber (r : O ⧸ Ideal.span {c}) :=
    GaussianFiberEquiv.fiber_tsum c (NeZero.ne c) r
      (GaussianShiftedPartition.representative c r)
      (GaussianShiftedPartition.representative_spec c r)
      (fun z => gaussian a (eisEmbedding z))
  simp_rw [hfiber, gaussian_coset_poisson a ha c (NeZero.ne c)]
  have hd : 0 < 4 / (3 * (a * ‖eisEmbedding c‖ ^ 2)) := by
    exact div_pos (by norm_num) (mul_pos (by norm_num)
      (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))))))
  have h := finite_gaussian_phase_sum (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) hd
    (fun r => eisEmbedding (GaussianShiftedPartition.representative c r) / eisEmbedding c) P
    (((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ))
  simp_rw [TraceCharacter.traceCharacter, eisTraceModChar_frequency]
  convert h using 1 <;>
    congr 1 <;> (try ext r) <;>
    simp only [div_mul_eq_mul_div]

theorem primitive_gaussian_poisson (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (a : ℝ) (ha : 0 < a) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (eisEmbedding z)) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        TraceCharacter.gaussScalar c χ *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  have hp := periodic_gaussian_poisson c χ a ha
  simp_rw [TraceCharacter.transform_eq c χ hχ] at hp
  rw [hp]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

def parameter (t : ℝ) : ℝ := 2 * t / (Real.sqrt 3 * ‖eisEmbedding c‖)

def theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) : ℂ :=
  ∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
    gaussian (parameter c t) (eisEmbedding z)

theorem parameter_pos (t : ℝ) (ht : 0 < t) : 0 < parameter c t := by
  unfold parameter
  exact div_pos (mul_pos (by norm_num) ht)
    (mul_pos (Real.sqrt_pos.mpr (by norm_num))
      (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))))

theorem theta_summable (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 0 < t) :
    Summable (fun z : O => χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      gaussian (parameter c t) (eisEmbedding z)) :=
  weighted_gaussian_summable _ χ _ (parameter_pos c t ht)

theorem parameter_dual (t : ℝ) (ht : 0 < t) :
    4 / (3 * (parameter c t * ‖eisEmbedding c‖ ^ 2)) = parameter c (1 / t) := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  unfold parameter
  field_simp
  ring_nf
  norm_num [Real.sq_sqrt]

theorem parameter_prefactor (t : ℝ) (ht : 0 < t) :
    2 / (Real.sqrt 3 * (parameter c t * ‖eisEmbedding c‖ ^ 2)) =
      1 / (‖eisEmbedding c‖ * t) := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  unfold parameter
  field_simp

theorem theta_functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) (ht : 0 < t) :
    theta c χ t = (TraceCharacter.normalizedGauss c χ / (t : ℂ)) *
      theta c χ⁻¹ (1 / t) := by
  have hp := primitive_gaussian_poisson c χ hχ (parameter c t) (parameter_pos c t ht)
  rw [parameter_dual c t ht, parameter_prefactor c t ht] at hp
  change theta c χ t =
    (((1 / (‖eisEmbedding c‖ * t) : ℝ) : ℂ) * TraceCharacter.gaussScalar c χ) *
      theta c χ⁻¹ (1 / t) at hp
  rw [hp]
  congr 1
  unfold TraceCharacter.normalizedGauss
  push_cast
  ring

def constantTerm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ := χ 0

omit [NeZero c] in
theorem constantTerm_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    constantTerm c χ = if IsUnit c then 1 else 0 := by
  unfold constantTerm
  by_cases hu : IsUnit c
  · rw [ite_eq_left hu]
    have h10 : (1 : O ⧸ Ideal.span {c}) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [Ideal.span_singleton_eq_top.mpr hu]
      trivial
    rw [← h10, map_one]
  · rw [ite_eq_right hu]
    apply MulChar.map_nonunit
    intro hz
    have h10 := (isUnit_zero_iff.mp hz).symm
    have h1 : (1 : O) ∈ Ideal.span {c} := Ideal.Quotient.eq_zero_iff_mem.mp h10
    exact hu (Ideal.span_singleton_eq_top.mp ((Ideal.eq_top_iff_one _).mpr h1))

omit [NeZero c] in
theorem theta_zero_term (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) :
    χ (Ideal.Quotient.mk (Ideal.span {c}) (0 : O)) *
      gaussian (parameter c t) (eisEmbedding 0) = constantTerm c χ := by
  simp [gaussian, constantTerm]

theorem theta_inversion (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) (ht : 0 < t) :
    theta c χ (1 / t) = (TraceCharacter.normalizedGauss c χ * (t : ℂ)) * theta c χ⁻¹ t := by
  have h := theta_functional_equation c χ hχ (1 / t) (one_div_pos.mpr ht)
  simpa only [one_div, Complex.ofReal_inv, inv_inv, div_inv_eq_mul, one_mul] using h

theorem theta_root_nonzero (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) : TraceCharacter.normalizedGauss c χ ≠ 0 := by
  have h := TraceCharacter.normalizedGauss_norm c χ hχ
  intro hz
  rw [hz, norm_zero] at h
  exact zero_ne_one h

theorem embedding_unit_norm (u : Oˣ) : ‖eisEmbedding (u : O)‖ = 1 := by
  have h := eisEmbedding_norm_sq_eq_absNorm_span (u : O)
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (u : O))]

omit [NeZero c] in

theorem theta_mul_global_unit (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (u : Oˣ) :
    theta c χ t = χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) * theta c χ t := by
  have h := u.mulLeft.tsum_eq (fun z : O =>
    χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (eisEmbedding z))
  calc
    theta c χ t = ∑' z : O,
        χ (Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * z)) *
          gaussian (parameter c t) (eisEmbedding ((u : O) * z)) := h.symm
    _ = χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) * theta c χ t := by
      rw [theta, ← tsum_mul_left]
      apply tsum_congr
      intro z
      simp only [map_mul, gaussian, norm_mul, embedding_unit_norm, one_mul, mul_assoc]

omit [NeZero c] in

theorem theta_eq_zero_of_global_unit (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ)
    (u : Oˣ) (hu : χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) ≠ 1) :
    theta c χ t = 0 :=
  eq_zero_of_mul_eq_self_left hu (theta_mul_global_unit c χ t u).symm

omit [NeZero c] in
theorem global_unit_invariant_of_theta_ne_zero
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : theta c χ t ≠ 0) :
    ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1 := by
  intro u
  by_contra hu
  exact ht (theta_eq_zero_of_global_unit c χ t u hu)

end SevenEighths.GaussianTheta

end

end OAI

end Source539

/- Original source: OAI/NumberTheory/DirichletL/PeriodicThetaRegularity.lean; sha256: 7589b5c6ec1711370690b5f13fa463df7d707721e88c732e6e8fce9bd20aafa5 -/
section Source540
namespace OAI

noncomputable section
open Set Filter Asymptotics MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.PeriodicThetaRegularity
open ThetaProduct EisensteinTheta HeckeTheta

theorem rectangularPair_f_continuous (a b : UnitAddCircle) (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) :
    ContinuousOn (rectangularPair a b u v hu hv).f (Ioi 0) :=
  (scaledEvenPair_f_continuous a u hu).mul (scaledEvenPair_f_continuous b v hv)

theorem pair_f_continuous {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    ContinuousOn (pair w).f (Ioi 0) := by
  have h : ContinuousOn (fun t => ∑ p : (Fin N × Fin N) × Fin 2,
      w p.1 * (parityPair p.1.1 p.1.2 N (Nat.cast_pos.mpr (NeZero.pos N)) p.2).f t)
      (Ioi 0) := by
    apply continuousOn_finsetSum
    intro p _
    exact continuousOn_const.mul
      (rectangularPair_f_continuous (xShift p.1.1 p.1.2 N p.2)
        (yShift p.1.2 N p.2) _ _ _ _)
  apply h.congr
  intro t _
  simp only [pair, finitePair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem theta_continuous {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    ContinuousOn (theta w) (Ioi 0) :=
  (pair_f_continuous w).congr (fun _t ht => theta_eq_pair w ht)

theorem theta_locallyIntegrable {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    LocallyIntegrableOn (theta w) (Ioi 0) :=
  (theta_continuous w).locallyIntegrableOn measurableSet_Ioi

theorem theta_rapid {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (r : ℝ) :
    (fun t => theta w t - w (0,0)) =O[atTop] (fun t : ℝ => t ^ r) := by
  apply ((pair w).hf_top r).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [theta_eq_pair w ht, pair_f₀]

theorem scaledTheta_continuous {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (A : ℝ) (hA : 0 < A) :
    ContinuousOn (fun t => theta w (A * t)) (Ioi 0) :=
  (theta_continuous w).comp (by fun_prop) (fun t ht => mul_pos hA ht)

theorem scaledTheta_rapid {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (A : ℝ) (hA : 0 < A) (r : ℝ) :
    (fun t => theta w (A * t) - w (0,0)) =O[atTop] (fun t : ℝ => t ^ r) :=
  rapid_rescale (theta w) (w (0,0)) (theta_rapid w) hA r

def primitivePair {N M : ℕ} [NeZero N] [NeZero M]
    (w : Fin N × Fin N → ℂ) (v : Fin M × Fin M → ℂ)
    (A : ℝ) (hA : 0 < A) (ε : ℂ) (hε : ε ≠ 0)
    (hfeq : ∀ t : ℝ, 0 < t →
      theta w (A / t) = ε * (t : ℂ) * theta v (A * t)) : WeakFEPair ℂ where
  f := fun t => theta w (A * t)
  g := fun t => theta v (A * t)
  k := 1
  ε := ε
  f₀ := w (0,0)
  g₀ := v (0,0)
  hf_int := (scaledTheta_continuous w A hA).locallyIntegrableOn measurableSet_Ioi
  hg_int := (scaledTheta_continuous v A hA).locallyIntegrableOn measurableSet_Ioi
  hk := zero_lt_one
  hε := hε
  h_feq t ht := by
    simpa only [mul_one_div, Real.rpow_one, smul_eq_mul] using hfeq t ht
  hf_top := scaledTheta_rapid w A hA
  hg_top := scaledTheta_rapid v A hA

end SevenEighths.PeriodicThetaRegularity

end

end OAI

end Source540

/- Original source: OAI/NumberTheory/DirichletL/Hecke/Primitive.lean; sha256: 6f1f8df20ee09e62dcafc8cbcd966761d0114302684965732159fb570902a7c6 -/
section Source541
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckePrimitive
open HeckeFamily

variable (c : O) [NeZero c]

private theorem span_ne_bot : Ideal.span ({c} : Set O) ≠ ⊥ := by
  simpa only [ne_eq, Ideal.span_singleton_eq_bot] using NeZero.ne c

private instance : Fintype (O ⧸ Ideal.span {c}) := by
  letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (span_ne_bot c)
  exact Fintype.ofFinite _

def character (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) : Character :=
  Character.ofResidue (Ideal.span {c}) (span_ne_bot c) χ hu

omit [NeZero c] in
theorem inverse_unit_trivial (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) :
    ∀ u : Oˣ, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1 := by
  intro u
  rw [MulChar.inv_apply_eq_inv', hu, inv_one]

def scale : ℝ := GaussianTheta.parameter c 1

theorem scale_pos : 0 < scale c := GaussianTheta.parameter_pos c 1 zero_lt_one

omit [NeZero c] in
theorem parameter_eq_scale_mul (t : ℝ) : GaussianTheta.parameter c t = scale c * t := by
  unfold scale GaussianTheta.parameter
  ring

theorem gaussianTheta_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) (t : ℝ) :
    GaussianTheta.theta c χ t = HeckeTheta.theta (coefficients (character c χ hu))
      (scale c * t) := by
  unfold GaussianTheta.theta HeckeTheta.theta
  rw [← coordinateEquiv.tsum_eq]
  apply tsum_congr
  intro n
  rw [periodicCoeff_eq_elementCoeff]
  change χ (Ideal.Quotient.mk (Ideal.span {c}) (coordinateElement n.1 n.2)) *
      GaussianTheta.gaussian (GaussianTheta.parameter c t)
        (ConcreteTraceCRT.eisEmbedding (coordinateElement n.1 n.2)) = _
  congr 1
  unfold GaussianTheta.gaussian
  rw [Complex.ofReal_exp]
  congr 1
  rw [← Complex.ofReal_pow, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    ← normForm_eq_absNorm_span, parameter_eq_scale_mul]
  push_cast
  ring

def pair (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) : WeakFEPair ℂ :=
  PeriodicThetaRegularity.primitivePair
    (coefficients (character c χ hu))
    (coefficients (character c χ⁻¹ (inverse_unit_trivial c χ hu)))
    (scale c) (scale_pos c) (TraceCharacter.normalizedGauss c χ)
    (GaussianTheta.theta_root_nonzero c χ hp) (by
      intro t ht
      have h := GaussianTheta.theta_inversion c χ hp t ht
      rw [gaussianTheta_eq c χ hu,
        gaussianTheta_eq c χ⁻¹ (inverse_unit_trivial c χ hu)] at h
      simpa only [mul_one_div] using h)

@[simp] theorem pair_f (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) :
    (pair c χ hu hp).f t = GaussianTheta.theta c χ t :=
  (gaussianTheta_eq c χ hu t).symm

@[simp] theorem pair_g (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) :
    (pair c χ hu hp).g t = GaussianTheta.theta c χ⁻¹ t :=
  (gaussianTheta_eq c χ⁻¹ (inverse_unit_trivial c χ hu) t).symm

def completedL (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (s : ℂ) : ℂ :=
  (pair c χ hu hp).Λ s / 6

theorem pair_completed_eq_right (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (hs : 1 < s.re) :
    (pair c χ hu hp).Λ s = (scale c : ℂ) ^ (-s) *
      HeckeTheta.completed (coefficients (character c χ hu)) s := by
  let w := coefficients (character c χ hu)
  have h := (pair c χ hu hp).hasMellin hs
  calc
    (pair c χ hu hp).Λ s =
        mellin (fun t => HeckeTheta.theta w (scale c * t) - w (0,0)) s := h.2.symm
    _ = (scale c : ℂ) ^ (-s) * mellin (fun t => HeckeTheta.theta w t - w (0,0)) s :=
      by simpa only [smul_eq_mul] using
        mellin_comp_mul_left (fun t => HeckeTheta.theta w t - w (0,0)) s (scale_pos c)
    _ = (scale c : ℂ) ^ (-s) * HeckeTheta.completed w s := by
      congr 1
      rw [← (HeckeTheta.pair_hasMellin w hs).2]
      unfold mellin
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [HeckeTheta.theta_eq_pair w ht, HeckeTheta.pair_f₀]

theorem pair_completed_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    (pair c χ hu hp).Λ s = (scale c : ℂ) ^ (-s) *
      HeckeTheta.completed (coefficients (character c χ hu)) s :=
  HeckeMellinIdentity.scaled_eq (pair c χ hu hp)
    (HeckeTheta.pair (coefficients (character c χ hu))) rfl (HeckeTheta.pair_k _)
    (scale c) (scale_pos c) (fun _ hs => pair_completed_eq_right c χ hu hp hs) h0 h1

theorem symm_completed_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    (pair c χ hu hp).symm.Λ s =
      (pair c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv).Λ s := by
  apply HeckeMellinIdentity.eq_of_f (pair c χ hu hp).symm
    (pair c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv) rfl rfl _ rfl h0 h1
  intro t _
  change (pair c χ hu hp).g t = _
  rw [pair_g, pair_f]

theorem completedL_functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedL c χ hu hp (1-s) = TraceCharacter.normalizedGauss c χ *
      completedL c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv s := by
  have h := (pair c χ hu hp).functional_equation s
  change (pair c χ hu hp).Λ (1-s) = TraceCharacter.normalizedGauss c χ *
    (pair c χ hu hp).symm.Λ s at h
  rw [symm_completed_eq c χ hu hp h0 h1] at h
  unfold completedL
  rw [h]
  ring

theorem completedL_eq_gamma_mul_LFunction (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) (hΓ : Complex.Gamma s ≠ 0) :
    completedL c χ hu hp s = (scale c : ℂ)^(-s) * (Real.pi : ℂ)^(-s) *
      Complex.Gamma s * LFunction (character c χ hu) s := by
  unfold completedL
  rw [pair_completed_eq c χ hu hp h0 h1]
  unfold LFunction continuedLattice HeckeTheta.latticeL
  simp only [Complex.cpow_neg]
  have hπ : (Real.pi : ℂ)^s ≠ 0 := by
    exact (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [Real.pi_ne_zero])
  field_simp

end SevenEighths.HeckePrimitive

end

end OAI

end Source541

/- Original source: OAI/NumberTheory/DirichletL/ThetaRegularity.lean; sha256: adf047348f003a9442f47729534ae0a2d02ddcf4e9044efaca6def27c96424c1 -/
section Source542
namespace OAI

noncomputable section

open scoped BigOperators Classical Topology
open Filter Asymptotics

namespace SevenEighths.ThetaRegularity

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic ConcreteTraceCRT GaussianTheta

theorem norm_gaussian (a : ℝ) (z : ℂ) :
    ‖gaussian a z‖ = Real.exp (-Real.pi * a * ‖z‖ ^ 2) := by
  simp [gaussian, Complex.norm_exp, pow_two, Complex.mul_re, Complex.mul_im]

theorem lattice_gap (z : O) (hz : z ≠ 0) : 1 ≤ ‖eisEmbedding z‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {z}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hz)

theorem gaussian_le_inverse_square (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    ‖gaussian a z‖ ≤ ((1 + a * ‖z‖ ^ 2) ^ 2)⁻¹ := by
  let x := a * ‖z‖ ^ 2
  have hx : 0 ≤ x := mul_nonneg ha (sq_nonneg _)
  have h1 : 1 + x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hs : (1 + x) ^ 2 ≤ Real.exp (Real.pi * x) := calc
    _ ≤ (Real.exp x) ^ 2 := by gcongr
    _ = Real.exp (2 * x) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right Real.two_le_pi hx)
  rw [norm_gaussian]
  have hexp : -Real.pi * a * ‖z‖ ^ 2 = -(Real.pi * x) := by dsimp [x]; ring
  rw [hexp]
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr hs

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

def decayRate : ℝ := Real.pi * parameter c 1

theorem decayRate_pos : 0 < decayRate c :=
  mul_pos Real.pi_pos (parameter_pos c 1 one_pos)

omit [NeZero c] in
theorem parameter_eq (t : ℝ) : parameter c t = parameter c 1 * t := by
  unfold parameter
  ring

omit [NeZero c] in
theorem norm_gaussian_parameter (t : ℝ) (z : ℂ) :
    ‖gaussian (parameter c t) z‖ = Real.exp (-decayRate c * t * ‖z‖ ^ 2) := by
  rw [norm_gaussian, parameter_eq]
  congr 1
  unfold decayRate
  ring

theorem coefficient_norm_le_one (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (r : O ⧸ Ideal.span {c}) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    have hu : ‖χ (u : O ⧸ Ideal.span {c})‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using
        Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    exact hu.le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    norm_num

theorem term_norm_le (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (z : O) :
    ‖χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      gaussian (parameter c t) (eisEmbedding z)‖ ≤
        Real.exp (-decayRate c * t * ‖eisEmbedding z‖ ^ 2) := by
  rw [norm_mul, norm_gaussian_parameter]
  exact mul_le_of_le_one_left (Real.exp_nonneg _) (coefficient_norm_le_one c χ _)

theorem continuousOn_theta_above (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (δ : ℝ) (hδ : 0 < δ) : ContinuousOn (theta c χ) (Set.Ioi δ) := by
  apply continuousOn_tsum (u := fun z : O => ‖gaussian (parameter c δ) (eisEmbedding z)‖)
  · intro z
    unfold gaussian parameter
    fun_prop
  · exact (gaussian_summable _ (parameter_pos c δ hδ)).norm
  · intro z t ht
    apply (term_norm_le c χ t z).trans
    rw [norm_gaussian_parameter]
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ decayRate c * ‖eisEmbedding z‖ ^ 2 :=
      mul_nonneg (decayRate_pos c).le (sq_nonneg _)
    have htd : δ < t := ht
    nlinarith

theorem continuousAt_theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 0 < t) : ContinuousAt (theta c χ) t := by
  have h := continuousOn_theta_above c χ (t / 2) (half_pos ht)
  exact h.continuousAt (isOpen_Ioi.mem_nhds (show t / 2 < t by linarith))

theorem continuousOn_theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    ContinuousOn (theta c χ) (Set.Ioi 0) :=
  fun t ht => (continuousAt_theta c χ t ht).continuousWithinAt

theorem theta_locallyIntegrableOn (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    MeasureTheory.LocallyIntegrableOn (theta c χ) (Set.Ioi 0) :=
  (continuousOn_theta c χ).locallyIntegrableOn measurableSet_Ioi

def tailConstant : ℝ := ∑' z : O, ‖gaussian (parameter c (1 / 2)) (eisEmbedding z)‖

omit [NeZero c] in
theorem tailConstant_nonneg : 0 ≤ tailConstant c := tsum_nonneg (fun _z => norm_nonneg _)

theorem tailConstant_le_cauchy :
    tailConstant c ≤ 4 * (1 + Real.pi / Real.sqrt (parameter c (1 / 2))) ^ 2 := by
  have ha := parameter_pos c (1 / 2) (by norm_num)
  apply le_trans (Summable.tsum_le_tsum
    (fun z : O => gaussian_le_inverse_square _ ha.le (eisEmbedding z))
    (gaussian_summable _ ha).norm
    (EisensteinSchwartzPoisson.scaled_eisenstein_cauchy_summable _ ha))
  exact EisensteinSchwartzPoisson.scaled_eisenstein_cauchy_bound _ ha

theorem tailConstant_le_linear :
    tailConstant c ≤ 8 * (1 + Real.pi ^ 2 * Real.sqrt 3 * ‖eisEmbedding c‖) := by
  have ha := parameter_pos c (1 / 2) (by norm_num)
  have hs : (Real.pi / Real.sqrt (parameter c (1 / 2))) ^ 2 =
      Real.pi ^ 2 * Real.sqrt 3 * ‖eisEmbedding c‖ := by
    rw [div_pow, Real.sq_sqrt ha.le]
    simp only [parameter]
    norm_num
    field_simp
  have h := tailConstant_le_cauchy c
  have hsq := sq_nonneg (1 - Real.pi / Real.sqrt (parameter c (1 / 2)))
  nlinarith

theorem tail_eq_tsum (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 0 < t) :
    theta c χ t - constantTerm c χ = ∑' z : O, if z = 0 then 0 else
      χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (eisEmbedding z) := by
  have h := (theta_summable c χ t ht).tsum_eq_add_tsum_ite (0 : O)
  rw [theta_zero_term c χ t] at h
  exact sub_eq_iff_eq_add.mpr (by simpa only [theta, add_comm] using h)

theorem tail_term_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 1 ≤ t) (z : O) :
    ‖if z = 0 then (0 : ℂ) else
      χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (eisEmbedding z)‖ ≤
      Real.exp (-decayRate c * t / 2) *
        ‖gaussian (parameter c (1 / 2)) (eisEmbedding z)‖ := by
  by_cases hz : z = 0
  · simp only [ite_eq_left hz, norm_zero]
    positivity
  · rw [ite_eq_right hz]
    apply (term_norm_le c χ t z).trans
    rw [norm_gaussian_parameter, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn := lattice_gap z hz
    have hβ := decayRate_pos c
    have hprod : 0 ≤ (t - 1) * (‖eisEmbedding z‖ ^ 2 - 1) :=
      mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hn)
    have hineq : t / 2 + ‖eisEmbedding z‖ ^ 2 / 2 ≤ t * ‖eisEmbedding z‖ ^ 2 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hineq hβ.le]

theorem theta_tail_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 1 ≤ t) :
    ‖theta c χ t - constantTerm c χ‖ ≤
      tailConstant c * Real.exp (-decayRate c * t / 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [tail_eq_tsum c χ t ht0]
  have hsum := (gaussian_summable _ (parameter_pos c (1 / 2) (by norm_num))).norm
  have hmajor := hsum.mul_left (Real.exp (-decayRate c * t / 2))
  have hnorm := Summable.of_nonneg_of_le (fun z => norm_nonneg _)
    (tail_term_bound c χ t ht) hmajor
  apply (norm_tsum_le_tsum_norm hnorm).trans
  have h := Summable.tsum_le_tsum (tail_term_bound c χ t ht) hnorm hmajor
  simpa only [tsum_mul_left, tailConstant, mul_comm] using h

theorem theta_tail_bound_conductor (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖theta c χ t - constantTerm c χ‖ ≤
      8 * (1 + Real.pi ^ 2 * Real.sqrt 3 * ‖eisEmbedding c‖) *
        Real.exp (-decayRate c * t / 2) :=
  (theta_tail_bound c χ t ht).trans
    (mul_le_mul_of_nonneg_right (tailConstant_le_linear c) (Real.exp_nonneg _))

theorem theta_tail_isBigO_exp (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    (fun t : ℝ => theta c χ t - constantTerm c χ) =O[atTop]
      (fun t : ℝ => Real.exp (-(decayRate c / 2) * t)) := by
  apply isBigO_iff.mpr
  refine ⟨tailConstant c, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have he : -(decayRate c / 2) * t = -decayRate c * t / 2 := by ring
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), he] using theta_tail_bound c χ t ht

theorem theta_tail_isBigO_rpow (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (r : ℝ) :
    (fun t : ℝ => theta c χ t - constantTerm c χ) =O[atTop] (fun t : ℝ => t ^ r) :=
  (theta_tail_isBigO_exp c χ).trans
    (isLittleO_exp_neg_mul_rpow_atTop (half_pos (decayRate_pos c)) r).isBigO

end SevenEighths.ThetaRegularity

end

end OAI

end Source542

/- Original source: OAI/NumberTheory/DirichletL/Hecke/Strip.lean; sha256: b720580769968346ea6b92ef674fc411e7c61fc65ebd617eae9053bd7c8834b8 -/
section Source543
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter Asymptotics Set MeasureTheory

namespace SevenEighths.HeckeStrip

def gammaConstant : ℝ := Real.Gamma (11 / 10) / Real.Gamma (19 / 10)

theorem gammaConstant_pos : 0 < gammaConstant :=
  div_pos (Real.Gamma_pos_of_pos (by norm_num)) (Real.Gamma_pos_of_pos (by norm_num))

theorem gamma_ratio_left_bound (t : ℝ) :
    ‖Complex.Gamma (1 - ((-(1 / 10) : ℂ) + t * Complex.I)) /
      Complex.Gamma ((-(1 / 10) : ℂ) + t * Complex.I)‖ ≤
        gammaConstant * (3 + |t|) ^ 2 := by
  let s : ℂ := -(1 / 10) + t * Complex.I
  have hb := CubicReflectionKernel.Gamma_shifted_pair_bound
    (1 / 2) (3 / 5) (-t) 2 (by norm_num) (by norm_num)
  simp only [Complex.ofReal_neg] at hb
  have hnum : ((1 / 2 : ℝ) : ℂ) + ((3 / 5 : ℝ) + (-t) * Complex.I) = 1 - s := by
    dsimp [s]; push_cast; ring
  have hden : ((1 / 2 : ℝ) : ℂ) - ((3 / 5 : ℝ) + (-t) * Complex.I) + (2 : ℕ) = s + 2 := by
    dsimp [s]; push_cast; ring
  rw [hnum, hden] at hb
  norm_num only [show (1 / 2 : ℝ) + 3 / 5 = 11 / 10 by norm_num,
    show (1 / 2 : ℝ) - 3 / 5 + (2 : ℕ) = 19 / 10 by norm_num] at hb
  have heq : Complex.Gamma (1 - s) / Complex.Gamma s =
      (∏ k ∈ Finset.range 2, (s + k)) *
        (Complex.Gamma (1 - s) / Complex.Gamma (s + 2)) := by
    rw [div_eq_mul_inv, CubicReflectionKernel.inverse_Gamma_shift s 2]
    simp only [Nat.cast_ofNat, div_eq_mul_inv]
    ring
  have hs : ‖s‖ ≤ 1 / 10 + |t| := by
    simpa [s, norm_mul] using norm_add_le (-(1 / 10) : ℂ) ((t : ℂ) * Complex.I)
  have hf := CubicReflectionKernel.norm_Gamma_shift_factor s 2
  have hf' : ‖∏ k ∈ Finset.range 2, (s + k)‖ ≤ (3 + |t|) ^ 2 := by
    have hs2 : ‖s‖ + (2 : ℝ) ≤ 3 + |t| := by linarith
    exact hf.trans (pow_le_pow_left₀ (by positivity) hs2 2)
  change ‖Complex.Gamma (1 - s) / Complex.Gamma s‖ ≤ _
  rw [heq, norm_mul]
  exact (mul_le_mul hf' hb (norm_nonneg _) (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem gamma_ratio_left_bound_of_re (z : ℂ) (hz : z.re = -(1 / 10)) :
    ‖Complex.Gamma (1 - z) / Complex.Gamma z‖ ≤ gammaConstant * (3 + |z.im|) ^ 2 := by
  have he : (-(1 / 10) : ℂ) + z.im * Complex.I = z := by
    simpa only [hz, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using Complex.re_add_im z
  simpa only [he] using gamma_ratio_left_bound z.im

def completionScale (Q : ℝ) : ℝ := Real.sqrt (3 * Q) / (2 * Real.pi)

theorem completionScale_pos (Q : ℝ) (hQ : 0 < Q) : 0 < completionScale Q := by
  unfold completionScale
  positivity

theorem completionScale_left_power (Q : ℝ) (hQ : 0 < Q) :
    completionScale Q ^ (6 / 5 : ℝ) =
      (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ) := by
  have he : completionScale Q = (Real.sqrt 3 / (2 * Real.pi)) * Real.sqrt Q := by
    unfold completionScale
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  rw [he, Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)]
  congr 1
  rw [Real.sqrt_eq_rpow Q, ← Real.rpow_mul hQ.le]
  norm_num

def leftConstant : ℝ :=
  (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * gammaConstant

theorem leftConstant_pos : 0 < leftConstant :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) gammaConstant_pos

theorem left_boundary_of_functional_equation (Q D : ℝ) (hQ : 0 < Q) (_hD : 0 ≤ D)
    (L Ldual : ℂ → ℂ) (ε : ℂ) (hε : ‖ε‖ = 1)
    (hfe : ∀ z : ℂ, z.re = -(1 / 10) → L z =
      ε * (completionScale Q : ℂ) ^ (1 - 2 * z) *
        (Complex.Gamma (1 - z) / Complex.Gamma z) * Ldual (1 - z))
    (hdual : ∀ z : ℂ, z.re = 11 / 10 → ‖Ldual z‖ ≤ D)
    (z : ℂ) (hz : z.re = -(1 / 10)) :
    ‖L z‖ ≤ leftConstant * D * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hscale : ‖(completionScale Q : ℂ) ^ (1 - 2 * z)‖ =
      (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (completionScale_pos Q hQ)]
    have hre : (1 - 2 * z).re = 6 / 5 := by simp [hz]; norm_num
    rw [hre, completionScale_left_power Q hQ]
  have hd : ‖Ldual (1 - z)‖ ≤ D := hdual _ (by simp [hz]; norm_num)
  rw [hfe z hz, norm_mul, norm_mul, norm_mul, hε, one_mul, hscale]
  have hg := gamma_ratio_left_bound_of_re z hz
  have hc := gammaConstant_pos
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_left hg (by positivity)) hd (norm_nonneg _)
    (by positivity : 0 ≤ ((Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ)) *
      (gammaConstant * (3 + |z.im|) ^ 2))
  calc
    _ ≤ ((Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ)) *
        (gammaConstant * (3 + |z.im|) ^ 2) * D := hm
    _ = _ := by unfold leftConstant; ring

def strip : Set ℂ := Complex.re ⁻¹' Ioo (-(1 / 10)) (11 / 10)
def closedStrip : Set ℂ := Complex.re ⁻¹' Icc (-(1 / 10)) (11 / 10)

theorem vertical_strip_of_exp_bound (F : ℂ → ℂ) (C : ℝ)
    (hF : DiffContOnCl ℂ F strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖F z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) → ‖F z‖ ≤ C)
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖F z‖ ≤ C)
    (z : ℂ) (hz : z ∈ closedStrip) : ‖F z‖ ≤ C := by
  obtain ⟨A, B, hA, hB, hgrowth⟩ := hgrowth
  apply PhragmenLindelof.vertical_strip hF ?_ hleft hright hz.1 hz.2
  refine ⟨1, ?_, B, ?_⟩
  · apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 11 / 10 - -(1 / 10))).mpr
    linarith [Real.two_le_pi]
  · apply isBigO_iff.mpr
    refine ⟨A, eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_)⟩
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply (hgrowth z hz).trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    simp only [one_mul]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp |z.im|]) hB

theorem closure_strip_subset : closure strip ⊆ closedStrip :=
  closure_minimal (fun _ hz => ⟨hz.1.le, hz.2.le⟩)
    (isClosed_Icc.preimage Complex.continuous_re)

theorem shift_norm_lower (z : ℂ) (hz : z ∈ closedStrip) : 1 ≤ ‖z + 2‖ := by
  have h := Complex.re_le_norm (z + 2)
  norm_num at h
  linarith [hz.1]

theorem shift_ne_zero (z : ℂ) (hz : z ∈ closedStrip) : z + 2 ≠ 0 := by
  have h := shift_norm_lower z hz
  intro hzero
  rw [hzero, norm_zero] at h
  norm_num at h

theorem height_le_shift_norm (z : ℂ) (hz : z ∈ closedStrip) :
    3 + |z.im| ≤ 3 * ‖z + 2‖ := by
  have hr := Complex.re_le_norm (z + 2)
  have hi := Complex.abs_im_le_norm (z + 2)
  norm_num at hr hi
  linarith [hz.1]

theorem shift_norm_le_height (z : ℂ) (hz : z ∈ closedStrip) :
    ‖z + 2‖ ≤ 2 * (3 + |z.im|) := by
  have hr : 0 ≤ z.re + 2 := by linarith [hz.1]
  have h := Complex.norm_le_abs_re_add_abs_im (z + 2)
  norm_num [abs_of_nonneg hr] at h
  linarith [hz.2, abs_nonneg z.im]

def normalized (Q : ℝ) (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  L z / (((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) * (z + 2) ^ 2)

theorem norm_normalized (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ) (z : ℂ) :
    ‖normalized Q L z‖ = ‖L z‖ / (Q ^ (3 / 5 : ℝ) * ‖z + 2‖ ^ 2) := by
  simp [normalized, norm_pow,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hQ _)]

theorem normalized_diffContOnCl (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ)
    (hL : DiffContOnCl ℂ L strip) : DiffContOnCl ℂ (normalized Q L) strip := by
  have hqn : ((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)).ne'
  have hd : Differentiable ℂ (fun z : ℂ => ((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) * (z + 2) ^ 2) := by
    fun_prop
  refine ⟨hL.differentiableOn.div hd.differentiableOn ?_, hL.continuousOn.div hd.continuous.continuousOn ?_⟩
  · intro z hz
    exact mul_ne_zero hqn (pow_ne_zero _ (shift_ne_zero z ⟨hz.1.le, hz.2.le⟩))
  · intro z hz
    exact mul_ne_zero hqn (pow_ne_zero _ (shift_ne_zero z (closure_strip_subset hz)))

theorem normalized_exp_bound (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖normalized Q L z‖ ≤ A * Real.exp (B * |z.im|) := by
  obtain ⟨A, B, hA, hB, hg⟩ := hgrowth
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  refine ⟨A / Q ^ (3 / 5 : ℝ), B, div_nonneg hA hq.le, hB, ?_⟩
  intro z hz
  have hn := shift_norm_lower z ⟨hz.1.le, hz.2.le⟩
  have hn2 : 1 ≤ ‖z + 2‖ ^ 2 := by nlinarith
  rw [norm_normalized Q hQ]
  calc
    _ ≤ ‖L z‖ / Q ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hq (by nlinarith)
    _ ≤ (A * Real.exp (B * |z.im|)) / Q ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_right (hg z hz) hq.le
    _ = _ := by ring

theorem normalized_boundary_bound (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (z : ℂ) (hz : z ∈ closedStrip)
    (hL : ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2) :
    ‖normalized Q L z‖ ≤ 9 * C := by
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  have hn : 0 < ‖z + 2‖ := lt_of_lt_of_le zero_lt_one (shift_norm_lower z hz)
  have hh := height_le_shift_norm z hz
  have hh2 : (3 + |z.im|) ^ 2 ≤ 9 * ‖z + 2‖ ^ 2 := by
    nlinarith [abs_nonneg z.im, norm_nonneg (z + 2)]
  rw [norm_normalized Q hQ]
  apply (div_le_iff₀ (mul_pos hq (sq_pos_of_pos hn))).mpr
  apply hL.trans
  have h := mul_le_mul_of_nonneg_left hh2 (mul_nonneg hC hq.le)
  nlinarith

theorem uniform_strip_bound_of_edges (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (hright : ∀ z : ℂ, z.re = 11 / 10 →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hn : ‖normalized Q L z‖ ≤ 9 * C := by
    apply vertical_strip_of_exp_bound _ _ (normalized_diffContOnCl Q hQ L hL)
      (normalized_exp_bound Q hQ L hgrowth) ?_ ?_ z hz
    · intro w hw
      apply normalized_boundary_bound Q C hQ hC L w
        (show w ∈ closedStrip from ⟨by rw [hw], by rw [hw]; norm_num⟩) (hleft w hw)
    · intro w hw
      apply normalized_boundary_bound Q C hQ hC L w
        (show w ∈ closedStrip from ⟨by rw [hw]; norm_num, by rw [hw]⟩) (hright w hw)
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  have hnz : 0 < ‖z + 2‖ := lt_of_lt_of_le zero_lt_one (shift_norm_lower z hz)
  rw [norm_normalized Q hQ] at hn
  have hb := (div_le_iff₀ (mul_pos hq (sq_pos_of_pos hnz))).mp hn
  have hh := shift_norm_le_height z hz
  have hh2 : ‖z + 2‖ ^ 2 ≤ 4 * (3 + |z.im|) ^ 2 := by
    nlinarith [norm_nonneg (z + 2), abs_nonneg z.im]
  have h := mul_le_mul_of_nonneg_left hh2 (mul_nonneg (by positivity : 0 ≤ 9 * C) hq.le)
  nlinarith

theorem uniform_strip_bound (Q C : ℝ) (hQ : 1 ≤ Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖L z‖ ≤ C)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  apply uniform_strip_bound_of_edges Q C (lt_of_lt_of_le zero_lt_one hQ) hC L hL
    hgrowth hleft ?_ z hz
  intro w hw
  apply (hright w hw).trans
  have hq : 1 ≤ Q ^ (3 / 5 : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hh : 1 ≤ (3 + |w.im|) ^ 2 := by nlinarith [abs_nonneg w.im]
  calc
    C ≤ C * Q ^ (3 / 5 : ℝ) := le_mul_of_one_le_right hC hq
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hC (le_trans zero_le_one hq)) hh

theorem uniform_strip_bound_of_functional_equation
    (Q D : ℝ) (hQ : 1 ≤ Q) (hD : 0 ≤ D) (L Ldual : ℂ → ℂ)
    (ε : ℂ) (hε : ‖ε‖ = 1) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hfe : ∀ z : ℂ, z.re = -(1 / 10) → L z =
      ε * (completionScale Q : ℂ) ^ (1 - 2 * z) *
        (Complex.Gamma (1 - z) / Complex.Gamma z) * Ldual (1 - z))
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖L z‖ ≤ D)
    (hdual : ∀ z : ℂ, z.re = 11 / 10 → ‖Ldual z‖ ≤ D)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * ((1 + leftConstant) * D) * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hQ0 := lt_of_lt_of_le zero_lt_one hQ
  have hc := leftConstant_pos
  apply uniform_strip_bound Q ((1 + leftConstant) * D) hQ (by positivity) L hL hgrowth ?_ ?_ z hz
  · intro w hw
    apply (left_boundary_of_functional_equation Q D hQ0 hD L Ldual ε hε hfe hdual w hw).trans
    have hbase : leftConstant * D ≤ (1 + leftConstant) * D := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hQ0.le _)) (sq_nonneg _)
  · intro w hw
    apply (hright w hw).trans
    nlinarith

theorem uncompleted_exp_bound (a : ℝ) (ha : 0 < a) (F : ℂ → ℂ)
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closedStrip, ‖F z‖ ≤ C) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ strip,
      ‖(a : ℂ) ^ (-z) * (Complex.Gamma z)⁻¹ * F z‖ ≤
        A * Real.exp (B * |z.im|) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨G, hG, hg⟩ := CubicGammaExponential.inverse_Gamma_strip_exp_bound_complex
    (-(1 / 10)) (11 / 10)
  let S : ℝ := a ^ (-(11 / 10) : ℝ) + a ^ (1 / 10 : ℝ)
  have hS : 0 ≤ S := add_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg ha.le _)
  refine ⟨S * G * C, Real.pi, by positivity, Real.pi_pos.le, ?_⟩
  intro z hz
  have hzc : z ∈ closedStrip := ⟨hz.1.le, hz.2.le⟩
  have haBound : ‖(a : ℂ) ^ (-z)‖ ≤ S := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.neg_re]
    exact VerticalContourShift.rpow_between_endpoints a (-(11 / 10)) (1 / 10) (-z.re)
      ha (by linarith [hz.2]) (by linarith [hz.1])
  rw [norm_mul, norm_mul]
  have hgamma := hg z hzc
  have hprod := mul_le_mul (mul_le_mul haBound hgamma (norm_nonneg _) hS)
    (hF z hzc) (norm_nonneg _) (mul_nonneg hS (mul_nonneg hG.le (Real.exp_nonneg _)))
  nlinarith

theorem mellin_uncompleted_exp_bound (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ)
    (hleft : MellinConvergent f (-(1 / 10) : ℂ))
    (hright : MellinConvergent f (11 / 10 : ℂ)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ strip,
      ‖(a : ℂ) ^ (-z) * (Complex.Gamma z)⁻¹ * mellin f z‖ ≤
        A * Real.exp (B * |z.im|) := by
  apply uncompleted_exp_bound a ha (mellin f)
  obtain ⟨C, hC, hb⟩ := VerticalContourShift.mellin_uniform_strip_bound f
    (-(1 / 10)) (11 / 10) (by simpa using hleft) (by simpa using hright)
  exact ⟨C, hC, fun z hz => hb z hz.1 hz.2⟩

end SevenEighths.HeckeStrip
end

end OAI

end Source543

/- Original source: OAI/NumberTheory/DirichletL/Hecke/StripActual.lean; sha256: 3c4e1debb9c1265a90079382fdcef5433cdde33035256873c993debcc5c2e579 -/
section Source544
namespace OAI

noncomputable section
open scoped Classical Topology BigOperators
open Set MeasureTheory
namespace SevenEighths.HeckeStripActual
open HeckeFamily HeckePrimitive

variable (c : O) [NeZero c]

private instance : Fintype (O ⧸ Ideal.span {c}) := by
  letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using NeZero.ne c)
  exact Fintype.ofFinite _

def conductor : ℝ := Ideal.absNorm (Ideal.span {c})

theorem conductor_ge_one : 1 ≤ conductor c := by
  unfold conductor
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {c}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact NeZero.ne c)

theorem completionScale_eq_inv :
    HeckeStrip.completionScale (conductor c) = (Real.pi * scale c)⁻¹ := by
  have hn : 0 < ‖ConcreteTraceCRT.eisEmbedding c‖ := by
    have h := ThetaRegularity.lattice_gap c (NeZero.ne c)
    nlinarith [norm_nonneg (ConcreteTraceCRT.eisEmbedding c)]
  unfold HeckeStrip.completionScale conductor scale GaussianTheta.parameter
  rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq (norm_nonneg _)]
  field_simp

theorem completionScale_cpow (s : ℂ) :
    (HeckeStrip.completionScale (conductor c) : ℂ)^s =
      (scale c : ℂ)^(-s) * (Real.pi : ℂ)^(-s) := by
  rw [completionScale_eq_inv, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg (mul_nonneg Real.pi_pos.le (scale_pos c).le),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (scale_pos c).le,
    mul_inv_rev]
  simp only [Complex.cpow_neg]

theorem completedL_eq_standard (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) (hΓ : Complex.Gamma s ≠ 0) :
    completedL c χ hu hp s =
      (HeckeStrip.completionScale (conductor c) : ℂ)^s * Complex.Gamma s *
        LFunction (character c χ hu) s := by
  rw [completedL_eq_gamma_mul_LFunction c χ hu hp h0 h1 hΓ, completionScale_cpow]

theorem LFunction_norm_le (η : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖LFunction η s‖ ≤ HeckeReciprocalBound.bound σ := by
  have hs1 := hσ.trans_le hs
  rw [LFunction_eq_series η hs1, IdealEuler.series]
  have hsum := IdealEuler.weighted_summable_norm (idealCoeff η) (idealCoeff_norm_le_one η) s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (CubicEisenstein.fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ))
  intro I
  change ‖idealCoeff η I * CubicEisenstein.fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I)).trans
    (HeckeReciprocalBound.normWeight_le_of_re_ge hs I)

theorem pair_strong (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) :
    IsStrongFEPair (pair c χ hu hp) := by
  constructor
  · exact HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal (character c χ hu) hχ
  · apply HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal
      (character c χ⁻¹ (inverse_unit_trivial c χ hu))
    change χ⁻¹ ≠ 1
    simpa only [ne_eq, inv_eq_one] using hχ

theorem LFunction_eq_uncompleted (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) (s : ℂ) :
    LFunction (character c χ hu) s =
      (HeckeStrip.completionScale (conductor c) : ℂ)^(-s) * (Complex.Gamma s)⁻¹ *
        completedL c χ hu hp s := by
  let a := HeckeStrip.completionScale (conductor c)
  have ha : 0 < a := HeckeStrip.completionScale_pos _ (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))
  have hL := LFunction_entire_nonprincipal (character c χ hu) hχ
  have hΛ : Differentiable ℂ (completedL c χ hu hp) :=
    (pair_strong c χ hu hp hχ).differentiable_Λ.div_const 6
  have hR : Differentiable ℂ (fun z : ℂ => (a : ℂ)^(-z) * (Complex.Gamma z)⁻¹ *
      completedL c χ hu hp z) :=
    (((differentiable_id.neg).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))).mul
      Complex.differentiable_one_div_Gamma).mul hΛ
  have he : LFunction (character c χ hu) = fun z : ℂ => (a : ℂ)^(-z) *
      (Complex.Gamma z)⁻¹ * completedL c χ hu hp z := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hL).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hR) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have h0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have h1 : z ≠ 1 := by intro h; norm_num [h] at hz
    have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    rw [completedL_eq_standard c χ hu hp h0 h1 hΓ]
    have haz : (a : ℂ)^z ≠ 0 := (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [ha.ne'])
    change LFunction (character c χ hu) z = (a : ℂ)^(-z) * (Complex.Gamma z)⁻¹ *
      ((a : ℂ)^z * Complex.Gamma z * LFunction (character c χ hu) z)
    rw [Complex.cpow_neg]
    field_simp
  exact congr_fun he s

theorem functional_equation_left (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (hs : s.re = -(1/10)) :
    LFunction (character c χ hu) s = TraceCharacter.normalizedGauss c χ *
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-2*s) *
      (Complex.Gamma (1-s) / Complex.Gamma s) *
        LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s) := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hs0 : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hs1 : 1-s ≠ 1 := by intro h; apply h0; linear_combination -h
  have hΓdual : Complex.Gamma (1-s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hs]; norm_num)
  have hΓ : Complex.Gamma s ≠ 0 := by
    have h := Complex.Gamma_ne_zero_of_re_pos (s := s+1) (by simp [hs]; norm_num)
    rw [Complex.Gamma_add_one s h0] at h
    exact (mul_ne_zero_iff.mp h).2
  have he := completedL_functional_equation c χ hu hp hs0 hs1
  rw [sub_sub_cancel] at he
  rw [completedL_eq_standard c χ hu hp h0 h1 hΓ,
    completedL_eq_standard c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv hs0 hs1 hΓdual] at he
  let a := HeckeStrip.completionScale (conductor c)
  have ha : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (HeckeStrip.completionScale_pos _ (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))).ne'
  have haz : (a : ℂ)^s ≠ 0 := (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [ha])
  have hpow : (a : ℂ)^(1-s) = (a : ℂ)^s * (a : ℂ)^(1-2*s) := by
    rw [← Complex.cpow_add _ _ ha]
    congr 1
    ring
  apply mul_left_cancel₀ (mul_ne_zero haz hΓ)
  calc
    _ = TraceCharacter.normalizedGauss c χ * ((a : ℂ)^(1-s) * Complex.Gamma (1-s) *
        LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s)) := he
    _ = _ := by
      change _ = ((a : ℂ)^s * Complex.Gamma s) *
        (TraceCharacter.normalizedGauss c χ * (a : ℂ)^(1-2*s) *
          (Complex.Gamma (1-s)/Complex.Gamma s) * _)
      rw [hpow]
      field_simp

theorem LFunction_exp_growth (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ HeckeStrip.strip,
      ‖LFunction (character c χ hu) z‖ ≤ A * Real.exp (B * |z.im|) := by
  let f : ℝ → ℂ := fun t => (pair c χ hu hp).f t / 6
  have hP := pair_strong c χ hu hp hχ
  have hconv (s : ℂ) : MellinConvergent f s := (hP.hasMellin s).1.div_const 6
  have h := HeckeStrip.mellin_uncompleted_exp_bound
    (HeckeStrip.completionScale (conductor c))
    (HeckeStrip.completionScale_pos _ (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))) f
    (hconv _) (hconv _)
  have heq (z : ℂ) :
      (HeckeStrip.completionScale (conductor c) : ℂ)^(-z) * (Complex.Gamma z)⁻¹ * mellin f z =
        LFunction (character c χ hu) z := by
    rw [LFunction_eq_uncompleted c χ hu hp hχ]
    congr 1
    change mellin (fun t => (pair c χ hu hp).f t / 6) z = (pair c χ hu hp).Λ z / 6
    rw [mellin_div_const, (hP.hasMellin z).2]
  simpa only [heq] using h

theorem uniform_strip_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖LFunction (character c χ hu) z‖ ≤
      36 * ((1 + HeckeStrip.leftConstant) * HeckeReciprocalBound.bound (11/10)) *
        conductor c ^ (3/5 : ℝ) * (3 + |z.im|)^2 := by
  apply HeckeStrip.uniform_strip_bound_of_functional_equation
    (conductor c) (HeckeReciprocalBound.bound (11/10)) (conductor_ge_one c)
    (tsum_nonneg (fun _ => norm_nonneg _))
    (LFunction (character c χ hu))
    (LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)))
    (TraceCharacter.normalizedGauss c χ) (TraceCharacter.normalizedGauss_norm c χ hp)
    (LFunction_entire_nonprincipal (character c χ hu) hχ).diffContOnCl
    (LFunction_exp_growth c χ hu hp hχ) (fun _ hs => functional_equation_left c χ hu hp hs)
    _ _ z hz
  · intro s hs
    exact LFunction_norm_le _ (by norm_num : (1 : ℝ) < 11/10) hs.ge
  · intro s hs
    exact LFunction_norm_le _ (by norm_num : (1 : ℝ) < 11/10) hs.ge

end SevenEighths.HeckeStripActual

end

end OAI

end Source544

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicMellin.lean; sha256: 7d39e81729715eeb072b352fc9298d47698ff2758364294508d33019ae442e82 -/
section Source545
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

private instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
private instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def twistedCoefficient (χ : Character) (inverse : Bool) (σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ inverse I.val * (norm I : ℂ)^(-shift σ freq)

theorem twisted_coefficient_summable (χ : Character) (inverse : Bool) (c σ freq : ℝ)
    (hc : 1 < c+σ) :
    Summable (fun I : NonzeroIdeal => ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c)) := by
  have hf := (CubicEisenstein.fullIdealWeight_summable_norm ((c+σ : ℝ) : ℂ)
    (by simpa using hc)).comp_injective (Subtype.val_injective : Function.Injective
      (fun I : NonzeroIdeal => I.val))
  apply hf.of_nonneg_of_le (fun I => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_pos I).le _))
  intro I
  have hI : I.val ≠ 0 := I.property
  change ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c) ≤
    ‖CubicEisenstein.fullIdealWeight ((c+σ : ℝ) : ℂ) I.val‖
  rw [CubicEisenstein.fullIdealWeight, ite_eq_right hI]
  change ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c) ≤
    ‖(norm I : ℂ)^(-((c+σ : ℝ) : ℂ))‖
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp only [Complex.neg_re, Complex.ofReal_re]
  unfold twistedCoefficient
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I), Complex.neg_re, shift_re]
  calc
    _ = ‖coefficient χ inverse I.val‖ * (norm I)^(-(c+σ)) := by
      rw [mul_assoc, ← Real.rpow_add (norm_pos I)]
      congr 2
      ring
    _ ≤ _ := mul_le_of_le_one_left (Real.rpow_nonneg (norm_pos I).le _)
      (coefficient_norm_le χ inverse I.val)

theorem twisted_series_eq (χ : Character) (inverse : Bool) (σ freq : ℝ)
    {s : ℂ} (hs : 1 < (s+shift σ freq).re) :
    (∑' I : NonzeroIdeal, twistedCoefficient χ inverse σ freq I*(norm I : ℂ)^(-s)) =
      series χ inverse (s+shift σ freq) := by
  rw [series_eq_tsum χ inverse hs]
  apply tsum_congr
  intro I
  unfold twistedCoefficient
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_pos I).ne')]
  congr 2
  ring

theorem polynomial_eq_weighted (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0 < D) :
    polynomial χ inverse W D σ freq =
      (D : ℂ)^(shift σ freq-(1/2 : ℂ)) *
        ∑' I : NonzeroIdeal, twistedCoefficient χ inverse σ freq I * W (norm I/D) := by
  have he (I : NonzeroIdeal) : summand χ inverse W D σ freq I =
      (D : ℂ)^(shift σ freq) * (twistedCoefficient χ inverse σ freq I * W (norm I/D)) := by
    unfold summand twistedCoefficient
    rw [CompletedGauss.positive_quotient_cpow_neg _ _ (norm_pos I) hD]
    ring
  unfold polynomial
  simp_rw [he]
  rw [tsum_mul_left, ← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 2
  ring

theorem polynomial_mellin (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hWs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (D c σ freq : ℝ) (hD : 0 < D) (hc : 1 < c+σ) :
    polynomial χ inverse W D σ freq = (1/(2*Real.pi) : ℂ)*∫ t : ℝ,
      mellin W ((c : ℂ)+t*Complex.I) *
        (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) *
          series χ inverse (((c : ℂ)+t*Complex.I)+shift σ freq) := by
  rw [polynomial_eq_weighted χ inverse W D σ freq hD]
  rw [CompletedGauss.weightedMellin_inversion norm norm_pos
    (twistedCoefficient χ inverse σ freq) c (twisted_coefficient_summable χ inverse c σ freq hc)
    W a b ha hWs hW D hD]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [twisted_series_eq χ inverse σ freq (by simpa using hc)]
  have he : (D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I) =
      (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
    congr 1
    ring
  calc
    _ = mellin W ((c : ℂ)+t*Complex.I) *
        ((D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I)) *
          series χ inverse (((c : ℂ)+t*Complex.I)+shift σ freq) := by ring
    _ = _ := by rw [he]

end SevenEighths.HeckeDyadic

end

end OAI

end Source545

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicContour.lean; sha256: e6b8fae8e52db0a45f050758ec3cbeea8a92e7e5ab13eac517320a0cd6644c6c -/
section Source546
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

def integrand (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D : ℂ)^(s+shift σ freq-(1/2 : ℂ)) *
    series χ inverse (s+shift σ freq)

theorem series_norm_le (χ : Character) (inverse : Bool) {b : ℝ} (hb : 1<b)
    {s : ℂ} (hs : b≤s.re) :
    ‖series χ inverse s‖ ≤ HeckeReciprocalBound.bound b := by
  cases inverse
  · exact HeckeStripActual.LFunction_norm_le χ hb hs
  · exact HeckeReciprocalBound.reciprocal_norm_le χ hb hs

theorem series_differentiableAt_right (χ : Character) (inverse : Bool) {s : ℂ}
    (hs : 1<s.re) : DifferentiableAt ℂ (series χ inverse) s := by
  cases inverse
  · exact LFunction_differentiableAt χ
      (by intro h; norm_num [h] at hs) (Or.inl (by intro h; norm_num [h] at hs))
  · exact HeckeReciprocal.reciprocal_differentiableAt χ
      (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one hs)

theorem series_differentiableAt_nonprincipal (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) {s : ℂ} (hz : inverse=true → LFunction χ s≠0) :
    DifferentiableAt ℂ (series χ inverse) s := by
  cases inverse
  · exact LFunction_entire_nonprincipal χ hχ s
  · have he : series χ true = fun z => (LFunction χ z)⁻¹ := by
      funext z
      simp [series, HeckeReciprocal.reciprocal, hχ]
    rw [he]
    exact (LFunction_entire_nonprincipal χ hχ s).inv (hz rfl)

theorem integrand_differentiableAt (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) {s : ℂ}
    (hseries : DifferentiableAt ℂ (series χ inverse) (s+shift σ freq)) :
    DifferentiableAt ℂ (integrand χ inverse W D σ freq) s := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · exact CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hWs hW s
    · exact ((differentiableAt_id.add_const (shift σ freq)).sub_const (1/2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  · exact hseries.comp s (differentiableAt_id.add_const (shift σ freq))

theorem integrand_norm (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0<D) (s : ℂ) :
    ‖integrand χ inverse W D σ freq s‖ =
      ‖mellin W s‖*D^(s.re+σ-1/2)*‖series χ inverse (s+shift σ freq)‖ := by
  unfold integrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  simp

theorem integrand_vertical_integrable (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D c σ freq : ℝ) (hD : 0<D) (hc : 1<c+σ) :
    Integrable (fun t : ℝ => integrand χ inverse W D σ freq ((c : ℂ)+t*I)) := by
  have hcont : Continuous (fun t : ℝ => integrand χ inverse W D σ freq ((c : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (integrand_differentiableAt χ inverse W a b ha hWs hW D σ freq hD
      (series_differentiableAt_right χ inverse (by simpa using hc))).continuousAt.comp
    fun_prop
  have hm := (CompletedGauss.compactMellin_vertical_integrable W a b ha hWs hW c).norm
  apply (hm.mul_const (D^(c+σ-1/2)*HeckeReciprocalBound.bound (c+σ))).mono'
    hcont.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [integrand_norm χ inverse W D σ freq hD]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (series_norm_le χ inverse hc (by simp))
  positivity

theorem finite_rectangle (χ : Character) (hχ : χ.residue≠1) (inverse : Bool)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0) :
    (∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I))) := by
  have hhol : DifferentiableOn ℂ (integrand χ inverse W D σ freq)
      (uIcc l r ×ℂ uIcc (-T) T) := by
    intro s hs
    exact (integrand_differentiableAt χ inverse W a b ha hWs hW D σ freq hD
      (series_differentiableAt_nonprincipal χ hχ inverse (hz s hs))).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (integrand χ inverse W D σ freq) ((l : ℂ)+(-T)*I) ((r : ℂ)+T*I)
    (by simpa using hhol)
  have hr :
      (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
      (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) = 0 := by
    simpa [smul_eq_mul] using h
  have hh := congrArg (fun z : ℂ => -I*z) hr
  ring_nf at hh ⊢
  simp only [I_sq] at hh
  linear_combination hh

theorem polynomial_finite_shift (χ : Character) (hχ : χ.residue≠1) (inverse : Bool)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D) (hr : 1<r+σ) (hT : 0≤T)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0) :
    polynomial χ inverse W D σ freq = (1/(2*Real.pi) : ℂ)*
      ((∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I))) +
      ∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) := by
  rw [polynomial_mellin χ inverse W a b ha hWs hW D r σ freq hD hr]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) = _
  rw [← integral_add_compl measurableSet_Icc
    (integrand_vertical_integrable χ inverse W a b ha hWs hW D r σ freq hD hr)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T≤T)]
  rw [finite_rectangle χ hχ inverse W a b ha hWs hW D σ freq l r T hD hz]

end SevenEighths.HeckeDyadic

end

end OAI

end Source546

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationColumn.lean; sha256: 06c2bae203bb819f97d15138f6636da46e73236bbed44cc48461037a5388372c -/
section Source547
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem prime_reciprocal_identity (χ ψ : Character) (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    {s : ℂ} (hs : 1<s.re) :
    series χ true s=(1-idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-s))*series ψ true s := by
  have hL : LFunction ψ s=LFunction χ s*(1-idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-s)) := by
    rw [LFunction_eq_series ψ hs,LFunction_eq_series χ hs,hm,
      IdealEuler.series_deletePrimes {P} (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs]
    simp only [Finset.prod_singleton]
    change IdealEuler.series (idealCoeff χ) s *
      (1-idealCoeff χ P.val*CubicEisenstein.fullIdealWeight s P.val)=_
    rw [CubicEisenstein.fullIdealWeight,ite_eq_right P.property.ne_zero]
  have h0 : s≠0 := by intro h; norm_num [h] at hs
  have h1 : s≠1 := by intro h; norm_num [h] at hs
  simp only [series,ite_true,HeckeReciprocal.reciprocal_eq_inv χ h0 h1,
    HeckeReciprocal.reciprocal_eq_inv ψ h0 h1]
  have hχ := LFunction_ne_zero_of_one_lt_re χ hs
  have hψ := LFunction_ne_zero_of_one_lt_re ψ hs
  apply (mul_right_cancel₀ hψ)
  rw [mul_assoc,inv_mul_cancel₀ hψ,mul_one,hL]
  rw [←mul_assoc,inv_mul_cancel₀ hχ,one_mul]

lemma rescaled_power (D N : ℝ) (hD : 0<D) (hN : 0<N) (w : ℂ) :
    (D : ℂ)^(w-(1/2 : ℂ))*(N : ℂ)^(-w)=
      (N : ℂ)^(-(1/2 : ℂ))*((D/N : ℝ) : ℂ)^(w-(1/2 : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hD hN).ne')]
  rw [←Complex.ofReal_log hD.le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log (div_pos hD hN).le,Real.log_div hD.ne' hN.ne']
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem prime_column_identity (χ ψ : Character) (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D σ freq : ℝ) (hD : 0<D) :
    polynomial χ true W D σ freq=polynomial ψ true W D σ freq-
      idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*
        polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq := by
  let N : ℝ := P.val.absNorm
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  have hc : 1<(2-σ)+σ := by linarith
  have he (t : ℝ) : integrand χ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I)=
      integrand ψ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I)-
      (idealCoeff χ P.val*(N : ℂ)^(-(1/2 : ℂ)))*
        integrand ψ true W (D/N) σ freq (((2-σ : ℝ) : ℂ)+t*I) := by
    let w : ℂ := (((2-σ : ℝ) : ℂ)+t*I)+shift σ freq
    have hw : 1<w.re := by dsimp [w]; simp
    have hr := prime_reciprocal_identity χ ψ P hm hw
    have hp := rescaled_power D N hD hN w
    unfold integrand
    change mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*series χ true w=_
    rw [hr]
    change mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*
      ((1-idealCoeff χ P.val*(N : ℂ)^(-w))*series ψ true w)=_
    calc
      _ = mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*series ψ true w-
          idealCoeff χ P.val*mellin W _*((D : ℂ)^(w-(1/2 : ℂ))*(N : ℂ)^(-w))*series ψ true w := by ring
      _ = _ := by rw [hp]; ring
  have hI := integrand_vertical_integrable ψ true W a b ha hWs hW D (2-σ) σ freq hD hc
  have hJ := integrand_vertical_integrable ψ true W a b ha hWs hW (D/N) (2-σ) σ freq (div_pos hD hN) hc
  rw [polynomial_mellin χ true W a b ha hWs hW D (2-σ) σ freq hD hc,
    polynomial_mellin ψ true W a b ha hWs hW D (2-σ) σ freq hD hc,
    polynomial_mellin ψ true W a b ha hWs hW (D/(P.val.absNorm : ℝ)) (2-σ) σ freq (div_pos hD hN) hc]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I))=_
  simp_rw [he]
  rw [integral_sub hI (hJ.const_mul _),integral_const_mul]
  change _=(1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand ψ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I))-
    idealCoeff χ P.val*(N : ℂ)^(-(1/2 : ℂ))*
      ((1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand ψ true W (D/N) σ freq (((2-σ : ℝ) : ℂ)+t*I)))
  ring

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source547

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationMask.lean; sha256: 54f61f71149f0d32b6fd9ad5a285197b2a329494d5460e3e4c8c18b638dc4d47 -/
section Source548
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve hiding O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem row_coeff_zero_unsupported (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) (J : Ideal O) (hJ : ¬Supported J) :
    idealCoeff χ J=0 := by
  by_cases hz : J=0
  · subst J
    exact map_zero _
  let n := ConcretePrimeRowBridge.idealGenerator J
  have hn : n≠0 := ConcretePrimeRowBridge.idealGenerator_ne_zero J hz
  have hs : Ideal.span {n}=J := ConcretePrimeRowBridge.span_idealGenerator J
  rw [←hs,idealCoeff_span χ hn,heq]
  exact rowTwist_zero_of_not_supported (elementHom η) m f z n hmLam hm2 (hs ▸ hJ)

theorem prime_coprime_iff (P : SmoothMobiusCorrection.PrimeIdeal) (J : Ideal O) :
    IsCoprime J P.val ↔ ¬P.val∣J := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  rw [isCoprime_comm,Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint,
    ←Ideal.dvd_iff_le]

theorem amplified_row_prime_mask (η χ ψ : Character) (m f z a : O)
    (P : SmoothMobiusCorrection.PrimeIdeal) (hspan : Ideal.span {a}=P.val)
    (hχ : ∀ n : O, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hψ : ∀ n : O, elementCoeff ψ n=rowTwist (elementHom η) m f (z*a^6) n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) :
    idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ) := by
  ext J
  rw [IdealEuler.deletePrimes_apply]
  simp only [Finset.mem_singleton,forall_eq]
  by_cases hs : Supported J
  · rw [idealCoeff_eq_row η ψ m f (z*a^6) hψ,
      show m^6*f^4*(z*a^6)=(m^6*f^4*z)*a^6 by ring,
      idealRowHom_argument_mul,idealRowHom_sixth_mask a J hs,hspan,prime_coprime_iff]
    by_cases hd : P.val∣J
    · simp [hd]
    · simp only [hd,not_false_eq_true,ite_true,mul_one]
      exact (idealCoeff_eq_row η χ m f z hχ J).symm
  · rw [row_coeff_zero_unsupported η ψ m f (z*a^6) hψ hmLam hm2 J hs,
      row_coeff_zero_unsupported η χ m f z hχ hmLam hm2 J hs]
    simp

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source548

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationEligibility.lean; sha256: f9ea020aadfe572d7d5e02a7f1c85aa6f12930e62e83672c448efe80cd9ea322 -/
section Source549
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentAmplificationEligibility
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEnergy
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def exclusionIdeal (R s : Ideal O) (h : O) : Ideal O := R*s*Ideal.span {h}

def eligible (R s : Ideal O) (h p : O) : Prop := ¬Ideal.span {p}∣exclusionIdeal R s h

theorem exclusionIdeal_ne_zero (R s : Ideal O) (h : O)
    (hR : R ≠ 0) (hs : s ≠ 0) (hh : h ≠ 0) : exclusionIdeal R s h ≠ 0 :=
  mul_ne_zero (mul_ne_zero hR hs) (Ideal.span_singleton_eq_bot.not.mpr hh)

theorem exclusionIdeal_norm (R s : Ideal O) (h : O) (Z B b M : ℝ) (hZ : 0 < Z)
    (hR : (Ideal.absNorm R:ℝ) ≤ Z^B) (hs : (Ideal.absNorm s:ℝ) ≤ Z^b)
    (hh : (Ideal.absNorm (Ideal.span {h}):ℝ) ≤ Z^M) :
    (Ideal.absNorm (exclusionIdeal R s h):ℝ) ≤ Z^(B+b+M) := by
  simp only [exclusionIdeal,map_mul,Nat.cast_mul]
  calc
    _ ≤ (Z^B*Z^b)*Z^M := mul_le_mul
      (mul_le_mul hR hs (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)) hh
      (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hZ,← Real.rpow_add hZ]

theorem eligible_not_dvd_row (R s : Ideal O) (h p : O) (he : eligible R s h p) : ¬p∣h := by
  intro hd
  apply he
  exact (Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hd)).trans
    (dvd_mul_left (Ideal.span {h}) (R*s))

theorem eligible_coprime_divisor (R s : Ideal O) (h p : O)
    (hp : Prime (Ideal.span {p})) (he : eligible R s h p) : IsCoprime s (Ideal.span {p}) := by
  apply (HeckeInverseAmplification.prime_coprime_iff ⟨Ideal.span {p},hp⟩ s).mpr
  intro hd
  exact he (hd.trans ((dvd_mul_left s R).mul_right (Ideal.span {h})))

theorem uniform_eligible_pool (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P,Q ∉ fixedBadPrimes)
    (R s : Ideal O) (hR0 : R ≠ 0) (hs0 : s ≠ 0)
    (Z ell B b M : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ Q ∈ P,Z^ell ≤ (Ideal.absNorm Q:ℝ))
    (hR : (Ideal.absNorm R:ℝ) ≤ Z^B) (hs : (Ideal.absNorm s:ℝ) ≤ Z^b)
    (hsize : 2*((B+b+M)/ell) ≤ P.card)
    (h : O) (hh0 : h ≠ 0) (hh : (Ideal.absNorm (Ideal.span {h}):ℝ) ≤ Z^M) :
    (P.card:ℝ)/2 ≤ ((elementPool P).filter (eligible R s h)).card := by
  unfold eligible
  convert eligible_element_card_half P hp hbad (exclusionIdeal R s h)
    (exclusionIdeal_ne_zero R s h hR0 hs0 hh0) Z ell (B+b+M) hZ hell hlower
    (exclusionIdeal_norm R s h Z B b M (zero_lt_one.trans hZ) hR hs hh) hsize

theorem actual_eligible_amplification {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (rows : Finset O) (hrows : ∀ h ∈ rows,h ≠ 0)
    (P : Finset (Ideal O)) (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P,Q ∉ fixedBadPrimes)
    (hP : P.Nonempty) (R s : Ideal O) (hR0 : R ≠ 0) (hs0 : s ≠ 0)
    (Z ell B b M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ Q ∈ P,Z^ell ≤ (Ideal.absNorm Q:ℝ))
    (hupper : ∀ Q ∈ P,(Ideal.absNorm Q:ℝ) ≤ Z^L)
    (hR : (Ideal.absNorm R:ℝ) ≤ Z^B) (hs : (Ideal.absNorm s:ℝ) ≤ Z^b)
    (hsize : 2*((B+b+M)/ell) ≤ P.card)
    (hrowNorm : ∀ h ∈ rows,(Ideal.absNorm (Ideal.span {h}):ℝ) ≤ Z^M) :
    (∑ h ∈ rows, ‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c h‖^2) ≤
      (8/(P.card:ℝ))*
        (((M+6*L)/ell)*(∑ y ∈ (eligiblePairs rows (elementPool P) (eligible R s)).image outputRow,
          ‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c y‖^2)+
          ∑ x ∈ eligiblePairs rows (elementPool P) (eligible R s),errorEnergy S a ha c x.1 x.2) := by
  have hpos : (0:ℝ)<P.card := by exact_mod_cast Finset.card_pos.mpr hP
  have hb := gauss_energy_amplification S a ha c rows (elementPool P) (eligible R s) hrows
    (fun p hpP => (elementPool_data P hp hbad p hpP).1)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.2.1)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.2.2.1)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.2.2.2)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.1)
    (fun h hh p hpP he => eligible_not_dvd_row R s h p he)
    ((P.card:ℝ)/2) (by positivity)
    (fun h hh => uniform_eligible_pool P hp hbad R s hR0 hs0 Z ell B b M hZ hell hlower hR hs hsize h (hrows h hh) (hrowNorm h hh))
    Z ell M L hZ hell
    (fun p hpP => hlower (Ideal.span {p}) (elementPool_data P hp hbad p hpP).2.1)
    (fun p hpP => hupper (Ideal.span {p}) (elementPool_data P hp hbad p hpP).2.1)
    hrowNorm
  convert hb using 1 ; ring

end SevenEighths.CenteredMomentAmplificationEligibility

end

end OAI

end Source549

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationSlotGap.lean; sha256: 7aac61e5450a041016403affecf4acc96c533c3b0c87f08ed7b18c559220707d -/
section Source550
namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter
namespace SevenEighths.CenteredMomentAmplificationSlotGap
local notation "O" => ActualEisensteinCubic.O

theorem eventually_scale_gap (b η ell : ℝ) (hgap : η < ell) :
    ∀ᶠ Z : ℝ in atTop, 1 ≤ Z ∧ b*Z^η < Z^ell := by
  have hg := (tendsto_rpow_atTop (sub_pos.mpr hgap)).eventually (eventually_gt_atTop b)
  filter_upwards [hg,eventually_ge_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hh := mul_lt_mul_of_pos_right hz (Real.rpow_pos_of_pos hZ0 η)
  rwa [← Real.rpow_add hZ0,sub_add_cancel] at hh

theorem amplifier_not_dvd_slot (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q)
    (Z ell η b : ℝ) (hgap : b*Z^η < Z^ell)
    (hPN : Z^ell ≤ (Ideal.absNorm P:ℝ)) (hQN : (Ideal.absNorm Q:ℝ) ≤ b*Z^η) :
    ¬P∣Q := by
  intro hd
  have he := (prime_dvd_prime_iff_eq hP hQ).mp hd
  subst Q
  linarith

theorem amplifier_not_dvd_slot_product {ι : Type*} (S : Finset ι) (v : ι → Ideal O)
    (P : Ideal O) (hP : Prime P) (hv : ∀ i ∈ S,Prime (v i))
    (Z ell η b : ℝ) (hgap : b*Z^η < Z^ell) (hPN : Z^ell ≤ (Ideal.absNorm P:ℝ))
    (hN : ∀ i ∈ S,(Ideal.absNorm (v i):ℝ) ≤ b*Z^η) :
    ¬P∣∏ i ∈ S,v i := by
  apply hP.not_dvd_finsetProd
  intro i hi
  exact amplifier_not_dvd_slot P (v i) hP (hv i hi) Z ell η b hgap hPN (hN i hi)

theorem live_profile_norm_bound (W : ℝ → ℂ) (b Z z η : ℝ) (I : Ideal O)
    (hb : 0 ≤ b) (hZ : 1 ≤ Z) (hz : z ≤ η)
    (hs : Function.support W ⊆ Set.Iic b)
    (hW : W ((Ideal.absNorm I:ℝ)/Z^z) ≠ 0) :
    (Ideal.absNorm I:ℝ) ≤ b*Z^η := by
  have hpow : 0 < Z^z := Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _
  have h := (div_le_iff₀ hpow).mp (hs hW)
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hz) hb)

theorem eventually_live_slot_exclusion (b η ell : ℝ) (hb : 0 ≤ b) (hgap : η < ell) :
    ∀ᶠ Z : ℝ in atTop,
      ∀ {ι : Type*} (S : Finset ι) (v : ι → Ideal O) (W : ι → ℝ → ℂ) (z : ι → ℝ),
      (∀ i ∈ S,Prime (v i)) → (∀ i ∈ S,z i ≤ η) →
      (∀ i ∈ S,Function.support (W i) ⊆ Set.Iic b) →
      (∀ i ∈ S,W i ((Ideal.absNorm (v i):ℝ)/Z^(z i)) ≠ 0) →
      ∀ P : Ideal O,Prime P → Z^ell ≤ (Ideal.absNorm P:ℝ) → ¬P∣∏ i ∈ S,v i := by
  filter_upwards [eventually_scale_gap b η ell hgap] with Z hZ
  intro ι S v W z hv hz hs hW P hP hPN
  exact amplifier_not_dvd_slot_product S v P hP hv Z ell η b hZ.2 hPN
    (fun i hi => live_profile_norm_bound (W i) b Z (z i) η (v i) hb hZ.1 (hz i hi) (hs i hi) (hW i hi))

end SevenEighths.CenteredMomentAmplificationSlotGap

end

end OAI

end Source550

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationAllocation.lean; sha256: 6d5afba9b28fe2aac2e73c822cc868807b5bad99dc2826b0b49cac6064550c38 -/
section Source551
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationAllocation
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem primaryGenerator_power (I : Ideal O) (n : ℕ) :
    primaryGenerator (I^n) = primaryGenerator I ^ n := map_pow primaryGeneratorHom I n

theorem primeRemainder_primary (p : O) (hp : Prime p) (hpp : goodLambda^2 ∣ p-1)
    (a : O) (ha : Supported (Ideal.span {a})) (hpa : goodLambda^2 ∣ a-1) :
    goodLambda^2 ∣ primeRemainder p hp a (supported_element_ne_zero a ha)-1 := by
  let r := primeRemainder p hp a (supported_element_ne_zero a ha)
  have hr := primeRemainder_supported p hp a ha
  have hgen := supported_primaryGenerator_ne_zero (Ideal.span {r}) hr
  have he : a = p^(multiplicity p a)*primaryGenerator (Ideal.span {r}) := by
    calc
      a = primaryGenerator (Ideal.span {a}) := (primaryGenerator_span a
        (supported_element_ne_zero a ha) hpa).symm
      _ = _ := by
        conv_lhs => rw [(primeRemainder_spec p hp a (supported_element_ne_zero a ha)).1]
        rw [← Ideal.span_singleton_mul_span_singleton,primaryGenerator_mul,
          ← Ideal.span_singleton_pow,primaryGenerator_power,primaryGenerator_span p hp.ne_zero hpp]
  have hre : r = primaryGenerator (Ideal.span {r}) := by
    apply mul_left_cancel₀ (pow_ne_zero (multiplicity p a) hp.ne_zero)
    exact (primeRemainder_spec p hp a (supported_element_ne_zero a ha)).1.symm.trans he
  change goodLambda^2 ∣ r-1
  rw [hre]
  exact (primaryGenerator_spec _ hgen).2

theorem plain_product_valuation (p : O) (hp : Prime p) (q a b : O)
    (hq : q ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hpq : ¬p ∣ q) :
    multiplicity p (q*a*b) = multiplicity p a + multiplicity p b := by
  rw [multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero (mul_ne_zero hq ha) hb)),
    multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp (mul_ne_zero hq ha)),
    multiplicity_eq_zero_of_not_dvd hpq,zero_add]

theorem plain_product_remainder (p : O) (hp : Prime p) (q a b : O)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    q*a*b = p^(multiplicity p a + multiplicity p b) *
      (q*primeRemainder p hp a ha*primeRemainder p hp b hb) := by
  conv_lhs => rw [(primeRemainder_spec p hp a ha).1,(primeRemainder_spec p hp b hb).1]
  rw [pow_add]
  ring

theorem split_plain_valuation {α β : Type*} (S : Finset α) (T : Finset β)
    (v : α → ℕ) (w : β → ℕ) (k : ℕ) (c : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if v i + w j = k then c i j else 0) =
      ∑ r ∈ Finset.range (k+1), ∑ i ∈ S, ∑ j ∈ T,
        if v i = r ∧ w j = k-r then c i j else 0 := by
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hk : v i + w j = k
  · rw [ite_eq_left hk,Finset.sum_eq_single (v i)]
    · simp only [true_and]
      rw [ite_eq_left (by omega)]
    · intro r hr hne
      rw [ite_eq_right (fun h => hne h.1.symm)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [ite_eq_right hk]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    rw [ite_eq_right]
    intro h
    exact hk (by have hh := Finset.mem_range.mp hr; omega)

theorem split_actual_plain_product {α β : Type*} (S : Finset α) (T : Finset β)
    (p : O) (hp : Prime p) (q : O) (hq : q ≠ 0) (hpq : ¬p ∣ q)
    (a : α → O) (ha : ∀ i, a i ≠ 0) (b : β → O) (hb : ∀ j, b j ≠ 0)
    (k : ℕ) (c : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if multiplicity p (q*a i*b j) = k then c i j else 0) =
      ∑ r ∈ Finset.range (k+1), ∑ i ∈ S, ∑ j ∈ T,
        if multiplicity p (a i) = r ∧ multiplicity p (b j) = k-r then c i j else 0 := by
  simp_rw [plain_product_valuation p hp q _ _ hq (ha _) (hb _) hpq]
  exact split_plain_valuation S T _ _ k c

theorem error_allocation_count (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    (Finset.range (k+1)).card ≤ 8 := by
  rw [Finset.card_range]
  rcases hk with rfl | rfl | rfl <;> omega

end SevenEighths.CenteredMomentAmplificationAllocation

end

end OAI

end Source551

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationSource.lean; sha256: 2d8df260bd82004ee3f367c7ee1e0cc7c9f36e606ee2b2b37eb1dd6b2fdaf831 -/
section Source552
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSource
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationAllocation CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

 theorem primeRoot_ne_zero (p : O) (hp : p ≠ 0) (k : ℕ) : primeRoot p k ≠ 0 := by
  unfold primeRoot
  apply Complex.ofReal_ne_zero.mpr
  apply Real.sqrt_ne_zero'.mpr
  apply pow_pos
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hp))

theorem original_error_shortening {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hap : ∀ i, goodLambda^2 ∣ a i-1) (c : α → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (h : O) :
    amplificationError S a ha c (fun i => multiplicity p (a i)) p (n+1) h =
      (primeRoot p (n+1)*errorScalar p hp.ne_zero n h)*
        gaussPolynomial S
          (fun i => primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i)))
          (fun i => primeRemainder_supported p hp (a i) (ha i))
          (fun i => if multiplicity p (a i)=n+1 then
            c i*residualCharacter p (n+1)
              (primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i))) else 0) h := by
  unfold amplificationError gaussPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  by_cases hv : multiplicity p (a i)=n+1
  · simp only [ite_eq_left hv]
    let r := primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i))
    have hr := primeRemainder_supported p hp (a i) (ha i)
    have hcop : IsCoprime p r := hp.irreducible.coprime_iff_not_dvd.mpr
      (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).2
    have hf : a i=p^(n+1)*r := by
      simpa only [hv] using (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).1
    have he := central_error_shortening p r n hs hr hpp
      (primeRemainder_primary p hp hpp (a i) (ha i) (hap i)) hcop h
    have he' : gaussRow (a i) (ha i) h-gaussRow (a i) (ha i) (p^6*h) =
        primeRoot p (n+1)*(errorScalar p hp.ne_zero n h *
          (residualCharacter p (n+1) r*gaussRow r hr h)) := by
      have hh := (div_eq_iff (primeRoot_ne_zero p hp.ne_zero (n+1))).mp he
      simp only [hf,errorScalar]
      exact hh.trans (by ring)
    rw [he']
    ring
  · simp only [ite_eq_right hv,zero_mul,mul_zero]

theorem source_error_shortening (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (h : O) :
    amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h =
      (primeRoot p (n+1)*errorScalar p hp.ne_zero n h)*
        gaussPolynomial Finset.univ
          (fun I : supportedColumns S => primeRemainder p hp (sourceGenerator S I)
            (supported_element_ne_zero _ (sourceGenerator_supported S I)))
          (fun I => primeRemainder_supported p hp (sourceGenerator S I) (sourceGenerator_supported S I))
          (fun I => if multiplicity p (sourceGenerator S I)=n+1 then
            c I*residualCharacter p (n+1)
              (primeRemainder p hp (sourceGenerator S I)
                (supported_element_ne_zero _ (sourceGenerator_supported S I))) else 0) h := by
  apply original_error_shortening _ _ _ _ _ p hp hs hpp n h
  intro I
  exact (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I
    (Finset.mem_filter.mp I.property).2)).2

end SevenEighths.CenteredMomentAmplificationSource

end

end OAI

end Source552

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationSourceDomain.lean; sha256: 1937ee17f56e794f2035249a73318cd614a980dcbc18cc77203a7efe9bc7d8c9 -/
section Source553
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourceDomain
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationAllocation CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

def residualIdeal (p : O) (hp : Prime p) (I : Ideal O) : Ideal O :=
  if hI : Supported I then Ideal.span {primeRemainder p hp (primaryGenerator I)
    (supported_primaryGenerator_ne_zero I hI)} else 0

theorem residualIdeal_supported (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    Supported (residualIdeal p hp I) := by
  rw [residualIdeal,dite_eq_left hI]
  exact primeRemainder_supported p hp (primaryGenerator I)
    (by rw [primary_span_supported I hI];exact hI)

theorem residualIdeal_generator (p : O) (hp : Prime p) (hpp : goodLambda^2 ∣ p-1)
    (I : Ideal O) (hI : Supported I) :
    primaryGenerator (residualIdeal p hp I) =
      primeRemainder p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI) := by
  rw [residualIdeal,dite_eq_left hI]
  apply primaryGenerator_span
  · apply supported_element_ne_zero
    simpa only [residualIdeal,dite_eq_left hI] using residualIdeal_supported p hp I hI
  · exact primeRemainder_primary p hp hpp (primaryGenerator I)
      (by rw [primary_span_supported I hI];exact hI)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).2

theorem residualIdeal_reconstruct (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    (Ideal.span {p})^(multiplicity p (primaryGenerator I))*residualIdeal p hp I=I := by
  rw [residualIdeal,dite_eq_left hI,Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton,
    ← (primeRemainder_spec p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI)).1]
  exact primary_span_supported I hI

def valuationColumns (S : Finset (Ideal O)) (p : O) (k : ℕ) : Finset (Ideal O) :=
  (supportedColumns S).filter (fun I => multiplicity p (primaryGenerator I)=k)

def residualColumns (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) : Finset (Ideal O) :=
  (valuationColumns S p k).image (residualIdeal p hp)

theorem valuationColumns_supported (S : Finset (Ideal O)) (p : O) (k : ℕ)
    (I : Ideal O) (hI : I∈valuationColumns S p k) : Supported I :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2

theorem residualIdeal_injOn (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) :
    Set.InjOn (residualIdeal p hp) (valuationColumns S p k) := by
  intro I hI J hJ he
  have hi := residualIdeal_reconstruct p hp I (valuationColumns_supported S p k I hI)
  have hj := residualIdeal_reconstruct p hp J (valuationColumns_supported S p k J hJ)
  rw [(Finset.mem_filter.mp hI).2] at hi
  rw [(Finset.mem_filter.mp hJ).2] at hj
  exact hi.symm.trans ((congrArg (fun x => (Ideal.span {p})^k*x) he).trans hj)

theorem residualColumns_supported (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ)
    (I : Ideal O) (hI : I∈residualColumns S p hp k) : Supported I := by
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact residualIdeal_supported p hp J (valuationColumns_supported S p k J hJ)

theorem residual_column_sum (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ)
    (c f : Ideal O → ℂ) :
    (∑ I∈valuationColumns S p k,c I*f (residualIdeal p hp I))=
      ∑ I∈residualColumns S p hp k,c ((Ideal.span {p})^k*I)*f I := by
  rw [residualColumns,Finset.sum_image (residualIdeal_injOn S p hp k)]
  apply Finset.sum_congr rfl
  intro I hI
  have hi := residualIdeal_reconstruct p hp I (valuationColumns_supported S p k I hI)
  rw [(Finset.mem_filter.mp hI).2] at hi
  rw [hi]

end SevenEighths.CenteredMomentAmplificationSourceDomain

end

end OAI

end Source553

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationSourcePolynomial.lean; sha256: fbeb1b39ba5d85c9d17f4e7f28d343c2e923feeb4d5d59904843592746090e45 -/
section Source554
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourcePolynomial
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSource CenteredMomentAmplificationSourceDomain
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

 theorem residual_primaryGaussRow (p : O) (hp : Prime p)
    (hpp : goodLambda^2 ∣ p-1) (I : Ideal O) (hI : Supported I) (h : O) :
    primaryGaussRow (residualIdeal p hp I) h=
      gaussRow (primeRemainder p hp (primaryGenerator I)
        (supported_primaryGenerator_ne_zero I hI))
        (primeRemainder_supported p hp (primaryGenerator I)
          (by rw [primary_span_supported I hI];exact hI)) h := by
  simp only [primaryGaussRow,dite_eq_left (residualIdeal_supported p hp I hI),
    residualIdeal_generator p hp hpp I hI]

 theorem supported_residualColumns (S : Finset (Ideal O)) (p : O) (hp : Prime p) (k : ℕ) :
    supportedColumns (residualColumns S p hp k)=residualColumns S p hp k := by
  apply Finset.filter_eq_self.mpr
  exact residualColumns_supported S p hp k

theorem remainder_polynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) (hpp : goodLambda^2 ∣ p-1) (k : ℕ) (h : O) :
    gaussPolynomial Finset.univ
      (fun I : supportedColumns S => primeRemainder p hp (sourceGenerator S I)
        (supported_element_ne_zero _ (sourceGenerator_supported S I)))
      (fun I => primeRemainder_supported p hp (sourceGenerator S I) (sourceGenerator_supported S I))
      (fun I => if multiplicity p (sourceGenerator S I)=k then
        c I*residualCharacter p k
          (primeRemainder p hp (sourceGenerator S I)
            (supported_element_ne_zero _ (sourceGenerator_supported S I))) else 0) h =
      gaussPolynomial Finset.univ (sourceGenerator (residualColumns S p hp k))
        (sourceGenerator_supported (residualColumns S p hp k))
        (fun I : supportedColumns (residualColumns S p hp k) =>
          c ((Ideal.span {p})^k*I)*residualCharacter p k (primaryGenerator I)) h := by
  let f : Ideal O → ℂ := fun I => residualCharacter p k (primaryGenerator I)*primaryGaussRow I h
  have he := residual_column_sum S p hp k c f
  have hl : (∑ I∈valuationColumns S p k,c I*f (residualIdeal p hp I))=
      gaussPolynomial Finset.univ
        (fun I : supportedColumns S => primeRemainder p hp (sourceGenerator S I)
          (supported_element_ne_zero _ (sourceGenerator_supported S I)))
        (fun I => primeRemainder_supported p hp (sourceGenerator S I) (sourceGenerator_supported S I))
        (fun I => if multiplicity p (sourceGenerator S I)=k then
          c I*residualCharacter p k
            (primeRemainder p hp (sourceGenerator S I)
              (supported_element_ne_zero _ (sourceGenerator_supported S I))) else 0) h := by
    rw [valuationColumns,Finset.sum_filter]
    unfold gaussPolynomial
    rw [← Finset.sum_coe_sort (supportedColumns S)]
    apply Finset.sum_congr rfl
    intro I hI
    dsimp only [sourceGenerator]
    rw [show f (residualIdeal p hp I)=
      residualCharacter p k (primeRemainder p hp (primaryGenerator I)
        (supported_primaryGenerator_ne_zero I (Finset.mem_filter.mp I.property).2))*
      gaussRow (primeRemainder p hp (primaryGenerator I)
        (supported_primaryGenerator_ne_zero I (Finset.mem_filter.mp I.property).2))
        (primeRemainder_supported p hp (primaryGenerator I)
          (by rw [primary_span_supported I (Finset.mem_filter.mp I.property).2]
              exact (Finset.mem_filter.mp I.property).2)) h by
      dsimp only [f]
      rw [residualIdeal_generator p hp hpp I (Finset.mem_filter.mp I.property).2,
        residual_primaryGaussRow p hp hpp I (Finset.mem_filter.mp I.property).2 h]]
    split_ifs with hk <;> simp only [hk, ite_true, ite_false, zero_mul]
    ring
  refine hl.symm.trans (he.trans ?_)
  have hh := source_gaussPolynomial (residualColumns S p hp k)
    (fun I => c ((Ideal.span {p})^k*I)*residualCharacter p k (primaryGenerator I)) h
  refine Eq.trans ?_ hh.symm
  rw [supported_residualColumns]
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only [f]
  ring

end SevenEighths.CenteredMomentAmplificationSourcePolynomial

end

end OAI

end Source554

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplificationSourcePool.lean; sha256: 47feb47f42de198798355f65c16e7af9fe4823ef2dd41ef77359a1be7b2ca1ae -/
section Source555
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourcePool
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationAllocation CenteredMomentAmplificationSourceDomain
open CenteredMomentSourceRow CenteredMomentLiveDomain CenteredMomentFirstSectors
open CenteredMomentSupportedCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem residualIdeal_coprime (p : O) (hp : Prime p) (I : Ideal O) (hI : Supported I) :
    IsCoprime (Ideal.span {p}) (residualIdeal p hp I) := by
  rw [residualIdeal,dite_eq_left hI,Ideal.isCoprime_span_singleton_iff]
  exact hp.irreducible.coprime_iff_not_dvd.mpr
    (primeRemainder_spec p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI)).2

theorem residualColumns_eq (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (hpp : goodLambda^2 ∣ p-1) (k : ℕ) :
    residualColumns S p hp k=
      (supportedColumns (residualPool ((Ideal.span {p})^k) (pow_ne_zero k hs.1) S)).filter
        (fun I => IsCoprime (Ideal.span {p}) I) := by
  ext I
  constructor
  · intro hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    have hsJ := valuationColumns_supported S p k J hJ
    have hh := residualIdeal_reconstruct p hp J hsJ
    rw [(Finset.mem_filter.mp hJ).2] at hh
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_,residualIdeal_supported p hp J hsJ⟩,
      residualIdeal_coprime p hp J hsJ⟩
    apply (mem_residualPool _ _ S _).mpr
    rw [hh]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).1
  · intro hI
    obtain ⟨hI,hcop⟩ := Finset.mem_filter.mp hI
    obtain ⟨hpool,hsI⟩ := Finset.mem_filter.mp hI
    have hIS := (mem_residualPool _ _ S I).mp hpool
    let J := (Ideal.span {p})^k*I
    have hsJ : Supported J := by
      rw [supported_mul_iff]
      constructor
      · simpa only [← Ideal.span_singleton_pow] using supported_power p hs k
      · exact hsI
    have hgen : primaryGenerator J=p^k*primaryGenerator I := by
      rw [show J=(Ideal.span {p})^k*I from rfl,primaryGenerator_mul,primaryGenerator_power,
        primaryGenerator_span p hp.ne_zero hpp]
    have hcop' : IsCoprime p (primaryGenerator I) := by
      apply (Ideal.isCoprime_span_singleton_iff _ _).mp
      rw [primary_span_supported I hsI]
      exact hcop
    have hv : multiplicity p (primaryGenerator J)=k := by
      rw [hgen,multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp
        (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supported_primaryGenerator_ne_zero I hsI))),
        multiplicity_pow_self_of_prime hp,
        multiplicity_eq_zero_of_not_dvd (hp.irreducible.coprime_iff_not_dvd.mp hcop'),add_zero]
    have hj : J∈valuationColumns S p k :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hIS,hsJ⟩,hv⟩
    refine Finset.mem_image.mpr ⟨J,hj,?_⟩
    apply mul_left_cancel₀ (pow_ne_zero k hs.1)
    have hh := residualIdeal_reconstruct p hp J hsJ
    simpa only [hv] using hh

end SevenEighths.CenteredMomentAmplificationSourcePool

end

end OAI

end Source555

/- Original source: OAI/NumberTheory/DirichletL/Moments/DivisorTensor.lean; sha256: 8506a85d4c97df57dfa5583436db68405985e10b233aa231c4e6b490b80d49c8 -/
section Source556
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorTensor
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentMask HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def allocationSign (D : Ideal O) (s : Finset ι) (a : Allocation D s) : ℂ :=
  ∏ P : primeSupport D, (-1:ℂ)^((a P).val.card+1)

theorem allocationSign_norm (D : Ideal O) (s : Finset ι) (a : Allocation D s) :
    ‖allocationSign D s a‖=1 := by
  simp only [allocationSign,norm_prod,norm_pow,norm_neg,norm_one,one_pow,Finset.prod_const_one]

theorem allocationTerm_eq_ite (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a =
      if ∀ i ∈ s, selectedDivisor D s a i∣v i then allocationSign D s a else 0 := by
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [ite_eq_left hh]
    unfold allocationTerm allocationSign
    apply Finset.prod_congr rfl
    intro P hP
    have he : (∏ i ∈ (a P).val,if (P:Ideal O)∣v i then (1:ℂ) else 0)=1 := by
      apply Finset.prod_eq_one
      intro i hi
      have his : i ∈ s := (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (a P).property)) hi
      have hPi : (P:Ideal O)∣selectedDivisor D s a i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ P,hi⟩)
      rw [ite_eq_left (hPi.trans (hh i his))]
    rw [he,mul_one]
  · rw [ite_eq_right hh]
    by_contra hn
    exact hh (fun i _ => selectedDivisor_dvd D s v a hn i)

theorem allocationTerm_eq_product (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a = allocationSign D s a*
      ∏ i ∈ s, if selectedDivisor D s a i∣v i then (1:ℂ) else 0 := by
  rw [allocationTerm_eq_ite]
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [ite_eq_left hh,Finset.prod_eq_one (fun i hi => by rw [ite_eq_left (hh i hi)]),mul_one]
  · rw [ite_eq_right hh]
    push Not at hh
    obtain ⟨i,hi,hnd⟩ := hh
    rw [Finset.prod_eq_zero hi (by simp only [ite_eq_right hnd]),mul_zero]

theorem selected_plain_sum (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (hD : D ≠ 0) (W : ℝ → ℂ) (X : ℝ) :
    (∑' I : Ideal O, if D∣I then rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) else 0) =
      rowWeight η m A z t D*rowTwistedSum η m A z W t (X/Ideal.absNorm D) := by
  rw [tsum_ideal_divisible D hD, rowTwistedSum_eq_weight,← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [map_mul]
  have he : (Ideal.absNorm (D*I):ℝ)/X = (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm D:ℝ)) := by
    simp only [map_mul,Nat.cast_mul,div_div_eq_mul_div]
    ring
  rw [he]
  ring

theorem selected_plain_scales (D₁ D₂ : Ideal O) (X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/Ideal.absNorm D₁)*(X₂/Ideal.absNorm D₂)=T/(Ideal.absNorm D₁*Ideal.absNorm D₂:ℝ) ∧
    (Y₁/Ideal.absNorm D₁)*(Y₂/Ideal.absNorm D₂)=T/(Ideal.absNorm D₁*Ideal.absNorm D₂:ℝ) :=
  CenteredMomentExtraction.extracted_product_scale X₁ X₂ Y₁ Y₂ T D₁ D₂ hX hY

end SevenEighths.CenteredMomentDivisorTensor

end

end OAI

end Source556

/- Original source: OAI/NumberTheory/DirichletL/Moments/DivisorSlots.lean; sha256: 5852401d74e917107563e1488fa6603cd3d4a9dfcfb7b1790eb867cd1a6562d0 -/
section Source557
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorSlots
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem selected_slot_exact (η : Character) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I) (β : Ideal O → ℂ) :
    rowSlot η m A z S (fun I => if D∣I then β I else 0) t =
      if P ∈ S ∧ D∣P then β P*rowWeight η m A z t P else 0 := by
  rw [rowSlot_eq_weight]
  have hz (I : Ideal O) (hI : I ∈ S) (hne : I ≠ P) :
      (if D∣I then β I else 0)*rowWeight η m A z t I=0 := by
    have hnd : ¬D∣I := fun hd => hne ((prime_dvd_prime_iff_eq hP (hS I hI)).mp (hPD.trans hd)).symm
    simp only [ite_eq_right hnd,zero_mul]
  by_cases hmem : P ∈ S
  · rw [Finset.sum_eq_single P (fun I hI hne => hz I hI hne) (fun h => (h hmem).elim)]
    by_cases hd : D∣P <;> simp only [hmem,hd,and_self,true_and,ite_true,ite_false,zero_mul]
  · rw [Finset.sum_eq_zero (fun I hI => hz I hI (fun he => hmem (he ▸ hI)))]
    simp only [hmem,false_and,ite_false]

theorem selected_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I)
    (β : Ideal O → ℂ) (M : ℝ) (hM : 0 ≤ M) (hβ : ∀ I ∈ S, ‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if D∣I then β I else 0) t‖ ≤ M := by
  rw [selected_slot_exact η m A z t D P hP hPD S hS β]
  split_ifs with h
  · rw [norm_mul]
    exact (mul_le_mul (hβ P h.1) (row_twisted_coefficient_norm η m A z t P hP.ne_zero)
      (norm_nonneg _) hM).trans_eq (mul_one M)
  · simpa only [norm_zero] using hM

theorem selectedDivisor_empty (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι)
    (he : selectedPrimes D s a i=∅) : selectedDivisor D s a i=1 := by
  simp only [selectedDivisor,he,Finset.prod_empty]

theorem allocated_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I)
    (β : Ideal O → ℂ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : ∀ I ∈ S, ‖β I‖ ≤ M)
    (hN : ∀ I ∈ S, β I ≠ 0 → (Ideal.absNorm I:ℝ) ≤ H) :
    ‖rowSlot η m A z S (fun I => if selectedDivisor D s a i∣I then β I else 0) t‖ ≤
      if (selectedPrimes D s a i).Nonempty then M else 128*M*H := by
  by_cases hn : (selectedPrimes D s a i).Nonempty
  · rw [ite_eq_left hn]
    obtain ⟨P,hP⟩ := hn
    exact selected_slot_bound η m A z t (selectedDivisor D s a i) P (support_prime P.property)
      (Finset.dvd_prod_of_mem _ hP) S hS β M hM hβ
  · rw [ite_eq_right hn]
    have he := selectedDivisor_empty D s a i (Finset.not_nonempty_iff_eq_empty.mp hn)
    simp only [he,one_dvd,ite_true]
    exact rowSlot_bound η m A z S β t H M hH hM hβ hN

end SevenEighths.CenteredMomentDivisorSlots

end

end OAI

end Source557

/- Original source: OAI/NumberTheory/DirichletL/Moments/DivisorRectangle.lean; sha256: 1feb949fd3e521247dd0c1c61d814a5da8eadc6b376c84f211213dcb0189a5a4 -/
section Source558
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorRectangle
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor
open CenteredMomentHeckeExpansion CenteredMomentMask CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def factorTuple (v : ι → Ideal O) (I J : Ideal O) : (ι ⊕ Fin 2) → Ideal O :=
  Sum.elim v (fun j => if j=0 then I else J)

def selectedPlain (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (j : Fin 2) : Ideal O := selectedDivisor D Finset.univ a (Sum.inr j)

def selectedSlot (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) : Ideal O := selectedDivisor D Finset.univ a (Sum.inl i)

theorem allocationTerm_rectangle (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (I J : Ideal O) :
    allocationTerm D Finset.univ (factorTuple v I J) a =
      allocationSign D Finset.univ a *
        (∏ i,if selectedSlot D a i ∣ v i then (1:ℂ) else 0)*
        (if selectedPlain D a 0 ∣ I then 1 else 0)*
        (if selectedPlain D a 1 ∣ J then 1 else 0) := by
  rw [allocationTerm_eq_product,Fintype.prod_sum_type,Fin.prod_univ_two]
  simp only [factorTuple,Sum.elim_inl,Sum.elim_inr,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false,
    selectedPlain,selectedSlot]
  simp only [mul_assoc]
  rfl

theorem double_selected_reindex (D₁ D₂ : Ideal O) (h₁ : D₁ ≠ 0) (h₂ : D₂ ≠ 0)
    (F : Ideal O → Ideal O → ℂ) :
    (∑' I : Ideal O,∑' J : Ideal O,
      (if D₁∣I then (1:ℂ) else 0)*(if D₂∣J then 1 else 0)*F I J) =
      ∑' I : Ideal O,∑' J : Ideal O,F (D₁*I) (D₂*J) := by
  have he (I J : Ideal O) :
      (if D₁∣I then (1:ℂ) else 0)*(if D₂∣J then 1 else 0)*F I J =
        if D₁∣I then (if D₂∣J then F I J else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  have hi (I : Ideal O) :
      (∑' J : Ideal O,if D₁∣I then (if D₂∣J then F I J else 0) else 0) =
        if D₁∣I then (∑' J : Ideal O,if D₂∣J then F I J else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [hi]
  rw [tsum_ideal_divisible D₁ h₁]
  exact tsum_congr (fun I => tsum_ideal_divisible D₂ h₂ (F (D₁*I)))

theorem allocated_rectangle_reindex (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) :
    (∑ v : (i : ι) → S i,(∏ i,β i (v i))*
      ∑' I : Ideal O,∑' J : Ideal O,
        allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      allocationSign D Finset.univ a *
        rowWeight η m A z t (selectedPlain D a 0*selectedPlain D a 1)*
        ∑ v : (i : ι) → S i,
          (∏ i,if selectedSlot D a i ∣ (v i:Ideal O) then β i (v i) else 0)*
          ∑' I : Ideal O,∑' J : Ideal O,
            rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
            idealRectangle W₁ W₂
              (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))
              (Y₁/Ideal.absNorm (selectedPlain D a 0)) (Y₂/Ideal.absNorm (selectedPlain D a 1)) I J := by
  let F (v : (i : ι) → S i) (I J : Ideal O) :=
    rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J
  have he (v : (i : ι) → S i) (I J : Ideal O) :
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
      (allocationSign D Finset.univ a * (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0))*
        ((if selectedPlain D a 0∣I then (1:ℂ) else 0)*
          (if selectedPlain D a 1∣J then 1 else 0)*F v I J) := by
    rw [allocationTerm_rectangle]
    dsimp only [F]
    ring
  have hint (v : (i : ι) → S i) :
      (∑' I : Ideal O,∑' J : Ideal O,
        allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      (allocationSign D Finset.univ a * (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0))*
        (∑' I : Ideal O,∑' J : Ideal O,F v (selectedPlain D a 0*I) (selectedPlain D a 1*J)) := by
    simp_rw [he]
    have ht := double_selected_reindex (selectedPlain D a 0) (selectedPlain D a 1)
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)) (F v)
    rw [← ht,← tsum_mul_left]
    apply tsum_congr
    intro I
    exact tsum_mul_left
  simp_rw [hint]
  have hβ (v : (i : ι) → S i) :
      (∏ i,β i (v i))*(allocationSign D Finset.univ a*
        (∏ i,if selectedSlot D a i∣(v i:Ideal O) then (1:ℂ) else 0)) =
      allocationSign D Finset.univ a *
        (∏ i,if selectedSlot D a i∣(v i:Ideal O) then β i (v i) else 0) := by
    rw [mul_left_comm,← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> simp
  simp_rw [← mul_assoc]
  simp only [← mul_assoc] at hβ
  simp_rw [hβ]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  dsimp only [F]
  rw [common_extracted_slot_rectangle η m A z S
    (fun i I => if selectedSlot D a i∣I then β i I else 0) t
    W₁ W₂ X₁ X₂ Y₁ Y₂ (selectedPlain D a 0) (selectedPlain D a 1)]
  simp only [mul_assoc]

end SevenEighths.CenteredMomentDivisorRectangle

end

end OAI

end Source558

/- Original source: OAI/NumberTheory/DirichletL/Moments/DivisorRows.lean; sha256: 18d3d631ca666307faf2d4374adefd25f97163f998f12c4ea91737b09d24d519 -/
section Source559
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRows
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor
open CenteredMomentDivisorRectangle CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def allocatedRectangle (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑ v : (i : ι) → S i,(∏ i,β i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J

theorem allocatedRectangle_eq_rows (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ =
      allocationSign D Finset.univ a *
        rowWeight η m A z t (selectedPlain D a 0*selectedPlain D a 1)*
        ((rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
          rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
          rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
          rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1)))*
          ∏ i,rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t) := by
  have hN (j : Fin 2) : (0:ℝ) < Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  unfold allocatedRectangle
  rw [allocated_rectangle_reindex]
  rw [actual_slot_rectangle_sum η m A z S
    (fun i I => if selectedSlot D a i∣I then β i I else 0) t W₁ W₂ b₁ b₂
    _ _ _ _ hW₁ hW₂ (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1))
    (div_pos hY₁ (hN 0)) (div_pos hY₂ (hN 1))]

theorem allocatedRectangle_norm_le (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖ ≤
      ‖rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
        rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
        rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
        rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1))‖ *
        ∏ i,‖rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t‖ := by
  rw [allocatedRectangle_eq_rows η m A z t S β D a W₁ W₂ b₁ b₂ _ _ _ _
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂,norm_mul,norm_mul,allocationSign_norm,one_mul,norm_mul,norm_prod]
  apply mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  exact row_twisted_coefficient_norm η m A z t _ (mul_ne_zero
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)))

end SevenEighths.CenteredMomentDivisorRows

end

end OAI

end Source559
