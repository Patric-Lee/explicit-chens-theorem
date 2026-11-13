import OpenAIGrouped.Unit008
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OpenAIGrouped.Unit007
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonAllowance.lean; sha256: cfb53306eee5439f00de7d632dd61b716b6a4e5141893106589943b855fdbb53 -/
section Source360
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCommonAllowance
open CenteredMomentActive CenteredMomentSecondLedger CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def activeIndicator (c d : ℕ) : ℝ := if netExponent c d ≠ 0 then 1 else 0

theorem netExponent_self (c : ℕ) : netExponent c c = 0 := by
  unfold netExponent
  have h : c+5*c=6*c := by omega
  rw [h, Nat.mul_mod_right]

theorem local_allowance (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    max (3*(c:ℝ)-5*(d:ℝ)-activeIndicator c d) 0 / 6 +
      max (3*(d:ℝ)-5*(c:ℝ)-activeIndicator c d) 0 / 6 ≤
      (c:ℝ)+(d:ℝ)-2-activeIndicator c d := by
  have hc' : (1:ℝ) ≤ c := by exact_mod_cast hc
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  unfold activeIndicator
  split_ifs with he
  · have hne : c ≠ d := by rintro rfl; exact he (netExponent_self c)
    have hgap : (c:ℝ)+1 ≤ d ∨ (d:ℝ)+1 ≤ c := by
      rcases lt_or_gt_of_ne hne with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    rcases hgap with hgap | hgap <;>
      rw [max_def,max_def] <;> split_ifs <;> linarith
  · rw [max_def,max_def]; split_ifs <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem weighted_positive_part (a w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    max (∑ i, a i*w i) 0 ≤ ∑ i, max (a i) 0*w i := by
  apply max_le
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (hw i)
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (hw i)

omit [DecidableEq ι] in
theorem weighted_allowance (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hd : ∀ i, 1 ≤ d i) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    max (3*(∑ i, (c i:ℝ)*w i)-5*(∑ i, (d i:ℝ)*w i)-
      ∑ i, activeIndicator (c i) (d i)*w i) 0/6 +
    max (3*(∑ i, (d i:ℝ)*w i)-5*(∑ i, (c i:ℝ)*w i)-
      ∑ i, activeIndicator (c i) (d i)*w i) 0/6 ≤
      (∑ i, (c i:ℝ)*w i)+(∑ i, (d i:ℝ)*w i)-
        2*(∑ i, w i)-(∑ i, activeIndicator (c i) (d i)*w i) := by
  have h₁ := weighted_positive_part (fun i => 3*(c i:ℝ)-5*(d i:ℝ)-activeIndicator (c i) (d i)) w hw
  have h₂ := weighted_positive_part (fun i => 3*(d i:ℝ)-5*(c i:ℝ)-activeIndicator (c i) (d i)) w hw
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_right (local_allowance (c i) (d i) (hc i) (hd i)) (hw i))
  simp only [sub_mul, add_mul, div_mul_eq_mul_div, mul_assoc,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
    ] at h₁ h₂ hsum ⊢
  simp only [← Finset.sum_div] at hsum
  linarith

omit [DecidableEq ι] in
theorem actual_common_support_allowance (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (Z : ℝ) (hZ : 1 < Z) :
    let C := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ)
    let D := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ)
    let P := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ)
    let R := Real.logb Z (Ideal.absNorm
      (∏ i ∈ activeSupport Finset.univ c d, Ideal.span {p i}) : ℝ)
    max (3*C-5*D-R) 0/6 + max (3*D-5*C-R) 0/6 ≤ C+D-2*P-R := by
  dsimp only
  rw [log_norm_power_product p hp c,log_norm_power_product p hp d,
    log_norm_radical p hp,log_norm_radical p hp]
  simpa only [activeSupport,Finset.sum_filter,activeIndicator,ite_mul,one_mul,zero_mul]
    using weighted_allowance c d hc hd
      (fun i => Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ))
      (fun i => Real.logb_nonneg hZ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))))

end SevenEighths.CenteredMomentCommonAllowance

end

end OAI

end Source360

/- Original source: OAI/NumberTheory/DirichletL/Moments/PrimaryCharacter.lean; sha256: 2862ea64b31464b3f3aae20bd6734bf165509076c2d9401baa87ba5995a7590c -/
section Source361
namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentPrimaryCharacter
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentPrimary CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def rawPrimaryHom (r : O) (χ : MulChar (Residue r) ℂ) : O →* ℂ where
  toFun n := primaryIdealCharacter r χ (Ideal.span {n})
  map_one' := by simp [← Ideal.one_eq_top]
  map_mul' x y := by rw [← Ideal.span_singleton_mul_span_singleton,map_mul]

def maskedPrimaryHom (r : O) (χ : MulChar (Residue r) ℂ) : O →* ℂ :=
  coprimalityMask (3:O)*rawPrimaryHom r χ

theorem maskedPrimaryHom_unit_mul (r : O) (χ : MulChar (Residue r) ℂ) (u : Oˣ) (n : O) :
    maskedPrimaryHom r χ ((u:O)*n)=maskedPrimaryHom r χ n := by
  change (if IsCoprime (3:O) ((u:O)*n) then (1:ℂ) else 0)*
      primaryIdealCharacter r χ (Ideal.span {(u:O)*n}) =
    (if IsCoprime (3:O) n then (1:ℂ) else 0)*primaryIdealCharacter r χ (Ideal.span {n})
  rw [isCoprime_mul_unit_left_right u.isUnit,Ideal.span_singleton_mul_left_unit u.isUnit]

theorem maskedPrimaryHom_ramified (r : O) (χ : MulChar (Residue r) ℂ) (n : O) (hn : λ₀∣n) :
    maskedPrimaryHom r χ n=0 := by
  have h3 : λ₀∣(3:O) := (dvd_pow_self λ₀ (by decide : 2≠0)).trans ActualEisensteinCubic.lambda_sq_dvd_three
  have hc : ¬IsCoprime (3:O) n := fun hc =>
    PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (hc.isUnit_of_dvd' h3 hn)
  change (if IsCoprime (3:O) n then (1:ℂ) else 0)*_=0
  rw [ite_eq_right hc,zero_mul]

theorem maskedPrimaryHom_primary (r : O) (χ : MulChar (Residue r) ℂ) (n : O)
    (hn : λ₀^2∣n-1) : maskedPrimaryHom r χ n=χ (Ideal.Quotient.mk _ n) := by
  change (if IsCoprime (3:O) n then (1:ℂ) else 0)*
    χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator (Ideal.span {n})))=_
  rw [ite_eq_left (CubicEisenstein.primary_coprime_three n hn).symm,one_mul,
    CompletedGauss.primaryGenerator_span n (CubicJacobiGlobal.primary_ne_zero n hn) hn]

theorem maskedPrimaryHom_periodic (r : O) (χ : MulChar (Residue r) ℂ) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {3*r}) (maskedPrimaryHom r χ) := by
  let F : O →* ℂ := χ.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {r})).toMonoidHom
  apply periodic_of_primary _ _ _ F _ (maskedPrimaryHom_unit_mul r χ)
    (maskedPrimaryHom_ramified r χ) (maskedPrimaryHom_primary r χ)
  · apply Ideal.span_singleton_le_span_singleton.mpr
    exact ActualEisensteinCubic.lambda_sq_dvd_three.trans (dvd_mul_right _ _)
  · intro x y hxy
    apply congrArg χ
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ((dvd_mul_left r 3).trans (Ideal.mem_span_singleton.mp hxy))

def primaryCharacter (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) : Character :=
  rowCharacter (Ideal.span {3*r})
    (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (by norm_num) hr))
    (maskedPrimaryHom r χ) (maskedPrimaryHom_periodic r χ)
    (fun u => by simpa only [mul_one,map_one] using maskedPrimaryHom_unit_mul r χ u 1)

@[simp] theorem primaryCharacter_modulus (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) :
    (primaryCharacter r hr χ).modulus=Ideal.span {3*r} := rfl

theorem primaryCharacter_primary (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) (n : O)
    (hn : λ₀^2∣n-1) : elementCoeff (primaryCharacter r hr χ) n=χ (Ideal.Quotient.mk _ n) := by
  rw [primaryCharacter,elementCoeff_rowCharacter,maskedPrimaryHom_primary r χ n hn]
  split_ifs with hc
  · rfl
  · symm
    apply MulChar.map_nonunit
    intro hu
    apply hc
    apply isUnit_residue_of_coprime
    apply (CubicEisenstein.primary_coprime_three n hn).symm.mul_left
    exact (CubicEisenstein.isUnit_quotient_span_iff r n).mp hu

theorem primaryCharacter_all (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) (n : O) :
    elementCoeff (primaryCharacter r hr χ) n=maskedPrimaryHom r χ n := by
  by_cases hn : λ₀∣n
  · rw [primaryCharacter,elementCoeff_rowCharacter,maskedPrimaryHom_ramified r χ n hn]
    split_ifs <;> rfl
  · have hg := (PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff n).mpr hn
    have hs := CompletedGauss.primaryGenerator_spec (Ideal.span {n}) hg
    obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs.1.symm
    have hp : λ₀^2∣(u:O)*n-1 := by
      have hp' : λ₀^2∣CompletedGauss.primaryGenerator (Ideal.span {n})-1 := hs.2
      rwa [mul_comm,hu]
    rw [← elementCoeff_unit_mul (primaryCharacter r hr χ) u n,
      ← maskedPrimaryHom_unit_mul r χ u n,primaryCharacter_primary r hr χ _ hp,
      maskedPrimaryHom_primary r χ _ hp]

theorem primaryCharacter_ideal (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (primaryCharacter r hr χ) I=
      χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator I)) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := CompletedGauss.primaryGenerator_spec I hn
  calc
    _ = elementCoeff (primaryCharacter r hr χ) (CompletedGauss.primaryGenerator I) := by
      rw [← idealCoeff_span _ hn,hs.1]
    _ = _ := primaryCharacter_primary r hr χ _ hs.2

theorem primaryCharacter_modulus_norm (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) :
    (primaryCharacter r hr χ).modulus.absNorm=
      (Ideal.span {(3:O)}).absNorm*(Ideal.span {r}).absNorm := by
  rw [primaryCharacter_modulus,← Ideal.span_singleton_mul_span_singleton,map_mul]

end SevenEighths.CenteredMomentPrimaryCharacter

end

end OAI

end Source361

/- Original source: OAI/NumberTheory/DirichletL/Detector/Calibration.lean; sha256: d8721f13440e278aab51b6625c948b89095b74ef89615eeb78fcb52cff1726c9 -/
section Source362
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def crtCharacter {ι T : Type*} [Fintype ι] [CommRing T]
    (R : ι → Type*) [∀ i, Field (R i)] (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) : MulChar T ℂ where
  toFun x := ∏ i, χ i (e x i)
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]
  map_nonunit' x hx := by
    have he : ¬∀ i, IsUnit (e x i) := by
      intro h
      apply hx
      have hu := (Pi.isUnit_iff.mpr h).map e.symm.toMonoidHom
      simpa using hu
    obtain ⟨i, hi⟩ := not_forall.mp he
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact (χ i).map_nonunit hi

theorem crtCharacter_pow_six {ι T : Type*} [Fintype ι] [CommRing T]
    (R : ι → Type*) [∀ i, Field (R i)] (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (hχ : ∀ i, χ i ^ 6 = 1) :
    crtCharacter R e χ ^ 6 = 1 := by
  apply MulChar.ext
  intro x
  rw [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply x.isUnit]
  change (∏ i, χ i (e x i)) ^ 6 = 1
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  have hu : IsUnit (e x i) := (Pi.isUnit_iff.mp (x.isUnit.map e.toMonoidHom)) i
  have he := congrArg (fun f : MulChar (R i) ℂ => f (e x i)) (hχ i)
  simpa only [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply hu] using he

theorem residue_char_ne_two_of_lambda_mem (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∈ P) : ringChar (O ⧸ P) ≠ 2 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field _
  intro hc
  have hd : goodLambda ∣ (3 : O) :=
    (dvd_pow_self goodLambda (by decide : (2 : ℕ) ≠ 0)).trans lambda_sq_dvd_three
  obtain ⟨k, hk⟩ := hd
  have h3m : (3 : O) ∈ P := by rw [hk]; exact P.mul_mem_right k hg
  have h3 : (3 : O ⧸ P) = 0 := by
    simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr h3m
  have h2 : (2 : O ⧸ P) = 0 := by
    exact (ringChar.spec (O ⧸ P) 2).mpr (by rw [hc])
  have h1 : (1 : O ⧸ P) = 0 := by linear_combination h3 - h2
  exact one_ne_zero h1

theorem exists_local_calibration (P : Ideal O) [P.IsMaximal] :
    ∃ χ : MulChar (O ⧸ P) ℂ, χ ≠ 1 ∧ χ ^ 6 = 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field _
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  by_cases hg : goodLambda ∉ P
  · refine ⟨actualSextic P hg ^ 2, ?_, ?_⟩
    · intro h
      exact ((MulChar.ringHomComp_ne_one_iff eisEmbedding_injective).mpr
        (cubicChar_ne_one P hg)) ((canonicalSextic_pow_two P hg).symm.trans h)
    · calc
        (actualSextic P hg ^ 2) ^ 6 = actualSextic P hg ^ (2 * 6) := (pow_mul _ 2 6).symm
        _ = actualSextic P hg ^ (6 * 2) := rfl
        _ = (actualSextic P hg ^ 6) ^ 2 := pow_mul _ 6 2
        _ = (1 : MulChar (O ⧸ P) ℂ) ^ 2 :=
          congrArg (fun χ : MulChar (O ⧸ P) ℂ => χ ^ 2)
            (CanonicalRowCompletion.actualSextic_sixth_one P hg)
        _ = 1 := one_pow 2
  · have hchar := residue_char_ne_two_of_lambda_mem P (not_not.mp hg)
    let χ : MulChar (O ⧸ P) ℂ := (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom ℂ)
    refine ⟨χ, ?_, ?_⟩
    · exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr (quadraticChar_ne_one hchar)
    · have h2 : χ ^ 2 = 1 := by
        dsimp only [χ]
        rw [MulChar.ringHomComp_pow, (quadraticChar_isQuadratic (O ⧸ P)).sq_eq_one,
          MulChar.ringHomComp_one]
      rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, h2, one_pow]

def localCalibration (P : Ideal O) [P.IsMaximal] : MulChar (O ⧸ P) ℂ :=
  Classical.choose (exists_local_calibration P)

theorem localCalibration_nonprincipal (P : Ideal O) [P.IsMaximal] :
    localCalibration P ≠ 1 := (Classical.choose_spec (exists_local_calibration P)).1

theorem localCalibration_pow_six (P : Ideal O) [P.IsMaximal] :
    localCalibration P ^ 6 = 1 := (Classical.choose_spec (exists_local_calibration P)).2

def calibrationFromPrimes {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) : CalibrationData := by
  letI (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  exact {
    excluded := Finset.univ.image P
    generator := finitePrimeModulus P
    generator_ne_zero := finitePrimeModulus_ne_zero P
    residue := crtCharacter (fun i => O ⧸ P i)
      ((Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
        (IdealGaussCRT.quotientProdEquivPi P hcop)) (fun i => localCalibration (P i)) }

theorem calibrationFromPrimes_pow_six {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    (calibrationFromPrimes P hcop).residue ^ 6 = 1 := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  exact crtCharacter_pow_six _ _ _ (fun i => localCalibration_pow_six (P i))

theorem calibrationFromPrimes_tau_norm {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    ‖(calibrationFromPrimes P hcop).tau‖ = 1 := by
  let b := finitePrimeModulus P
  have hb : b ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {b}) := ConcreteTraceCRT.finite_quotient_span hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let e : (O ⧸ Ideal.span {b}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let ψ := quotientTrace b hb
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive b hb
  have hg := IdealGaussCRT.norm_gauss_finite_crt_sq (fun i => O ⧸ P i) e
    (fun i => localCalibration (P i)) ψ (fun i => localCalibration_nonprincipal (P i))
    (fun i => IdealGaussCRT.coordinateAddChar_isPrimitive _ e ψ hψ i)
  have hcard : (Fintype.card (O ⧸ Ideal.span {b}) : ℝ) = elementNorm b := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hcard] at hg
  have hQ : 0 < elementNorm b := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hb))
  have hn : ‖∑ x : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e x i)) * ψ x‖ =
      Real.sqrt (elementNorm b) := by
    have hs := Real.sq_sqrt hQ.le
    have hs0 := Real.sqrt_nonneg (elementNorm b)
    have hn0 := norm_nonneg (∑ x : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e x i)) * ψ x)
    nlinarith
  change ‖(∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) * ψ d) /
    (Real.sqrt (elementNorm b) : ℂ)‖ = 1
  rw [tsum_fintype, norm_div, hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr hQ).ne']

theorem calibrationFromPrimes_tau_ne_zero {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    (calibrationFromPrimes P hcop).tau ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [calibrationFromPrimes_tau_norm]; norm_num)

def calibrationForSet (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) : CalibrationData := by
  letI (P : S) : P.val.IsMaximal := hS P.val P.property
  exact calibrationFromPrimes (fun P : S => P.val)
    (fun P Q hPQ => Ideal.isCoprime_of_isMaximal (fun h => hPQ (Subtype.ext h)))

theorem calibrationForSet_excluded (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).excluded = S := by
  change Finset.univ.image (fun P : S => P.val) = S
  ext P
  simp

theorem calibrationForSet_span (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    Ideal.span {(calibrationForSet S hS).generator} = ∏ P ∈ S, P := by
  change Ideal.span {finitePrimeModulus (fun P : S => P.val)} = _
  rw [span_finitePrimeModulus]
  exact Finset.prod_coe_sort S (fun P : Ideal O => P)

theorem calibrationForSet_pow_six (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).residue ^ 6 = 1 := by
  let (P : S) : P.val.IsMaximal := hS P.val P.property
  unfold calibrationForSet
  apply calibrationFromPrimes_pow_six

theorem calibrationForSet_tau_norm (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    ‖(calibrationForSet S hS).tau‖ = 1 := by
  let (P : S) : P.val.IsMaximal := hS P.val P.property
  unfold calibrationForSet
  apply calibrationFromPrimes_tau_norm

theorem calibrationForSet_tau_ne_zero (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).tau ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [calibrationForSet_tau_norm]; norm_num)

end SevenEighths.ProbePhysical
end

end OAI

end Source362

/- Original source: OAI/NumberTheory/DirichletL/Detector/CalibrationFourier.lean; sha256: 38d5b05a2473ea3fdb4de76fa3ee8ee3db2d2463657e409f4dbe5af726ba9f1a -/
section Source363
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def calibrationGauss (C : CalibrationData) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {C.generator}, C.residue d *
    quotientTrace C.generator C.generator_ne_zero
      (Ideal.Quotient.mk (Ideal.span {C.generator}) h * d)

theorem calibrationGauss_one (C : CalibrationData) :
    calibrationGauss C 1 = (Real.sqrt (elementNorm C.generator) : ℂ) * C.tau := by
  have hn : 0 < elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hc : (Real.sqrt (elementNorm C.generator) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
  simp only [calibrationGauss, map_one, one_mul, CalibrationData.tau]
  field_simp

theorem calibrationFromPrimes_gauss {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) (h : O) :
    calibrationGauss (calibrationFromPrimes P hcop) h =
      ((calibrationFromPrimes P hcop).residueMonoid h)⁻¹ *
        calibrationGauss (calibrationFromPrimes P hcop) 1 := by
  let b := finitePrimeModulus P
  have hb : b ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {b}) := ConcreteTraceCRT.finite_quotient_span hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let e : (O ⧸ Ideal.span {b}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let ψ := quotientTrace b hb
  have ht := IdealGaussCRT.gauss_transform_finite_crt_scalar (fun i => O ⧸ P i) e
    (fun i => localCalibration (P i)) ψ (fun i => localCalibration_nonprincipal (P i))
    (Ideal.Quotient.mk (Ideal.span {b}) h)
  change (∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) *
      ψ (Ideal.Quotient.mk (Ideal.span {b}) h * d)) =
    (∏ i, localCalibration (P i) (e (Ideal.Quotient.mk (Ideal.span {b}) h) i))⁻¹ *
      ∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) *
        ψ (Ideal.Quotient.mk (Ideal.span {b}) 1 * d)
  simpa only [tsum_fintype, map_one, one_mul] using ht

theorem calibrationForSet_gauss (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (h : O) :
    calibrationGauss (calibrationForSet S hS) h =
      star ((calibrationForSet S hS).residueMonoid h) *
        (Real.sqrt (elementNorm (calibrationForSet S hS).generator) : ℂ) *
        (calibrationForSet S hS).tau := by
  let C := calibrationForSet S hS
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  have hc : star (C.residueMonoid h) = (C.residueMonoid h)⁻¹ := by
    exact (MulChar.star_apply' C.residue (Ideal.Quotient.mk _ h)).trans
      (MulChar.inv_apply_eq_inv' _ _)
  have he : calibrationGauss C h = (C.residueMonoid h)⁻¹ * calibrationGauss C 1 := by
    let (P : S) : P.val.IsMaximal := hS P.val P.property
    unfold C calibrationForSet
    apply calibrationFromPrimes_gauss
  rw [he, calibrationGauss_one, ← hc]
  ring

theorem calibrationForSet_residue_sixth (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) (ha : IsCoprime (calibrationForSet S hS).generator a) :
    (calibrationForSet S hS).residueMonoid a ^ 6 = 1 := by
  let C := calibrationForSet S hS
  have hu := (isUnit_quotient_span_iff C.generator a).mpr ha
  have h6 := congrArg (fun χ : MulChar (O ⧸ Ideal.span {C.generator}) ℂ =>
    χ (Ideal.Quotient.mk _ a)) (calibrationForSet_pow_six S hS)
  change C.residue (Ideal.Quotient.mk _ a) ^ 6 = 1
  simpa only [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply hu] using h6

theorem calibrationForSet_quotient_conjugate (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (s k u a : O)
    (hs : IsCoprime (calibrationForSet S hS).generator s)
    (ha : IsCoprime (calibrationForSet S hS).generator a)
    (hrel : s * k = u * a ^ 6) :
    star ((calibrationForSet S hS).residueMonoid k) =
      star ((calibrationForSet S hS).residueMonoid u) *
        (calibrationForSet S hS).residueMonoid s := by
  let C := calibrationForSet S hS
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  have hc (x : O) : star (C.residueMonoid x) = (C.residueMonoid x)⁻¹ := by
    exact (MulChar.star_apply' C.residue (Ideal.Quotient.mk _ x)).trans
      (MulChar.inv_apply_eq_inv' _ _)
  have hu := (isUnit_quotient_span_iff C.generator s).mpr hs
  have hsn : C.residueMonoid s ≠ 0 := C.residue.apply_ne_zero_iff.mpr hu
  have he := congrArg C.residueMonoid hrel
  simp only [map_mul, map_pow] at he
  have h6 : C.residueMonoid a ^ 6 = 1 := calibrationForSet_residue_sixth S hS a ha
  rw [h6, mul_one] at he
  have hk : C.residueMonoid k = (C.residueMonoid s)⁻¹ * C.residueMonoid u := by
    rw [← he, ← mul_assoc, inv_mul_cancel₀ hsn, one_mul]
  change star (C.residueMonoid k) = star (C.residueMonoid u) * C.residueMonoid s
  rw [hc k, hc u, hk, mul_inv_rev, inv_inv]

theorem calibrationForSet_gauss_sixth_row (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (s k u a : O)
    (hs : IsCoprime (calibrationForSet S hS).generator s)
    (ha : IsCoprime (calibrationForSet S hS).generator a)
    (hrel : s * k = u * a ^ 6) :
    calibrationGauss (calibrationForSet S hS) k =
      star ((calibrationForSet S hS).residueMonoid u) *
        (calibrationForSet S hS).residueMonoid s *
        (Real.sqrt (elementNorm (calibrationForSet S hS).generator) : ℂ) *
        (calibrationForSet S hS).tau := by
  rw [calibrationForSet_gauss,
    calibrationForSet_quotient_conjugate S hS s k u a hs ha hrel]

end SevenEighths.ProbePhysical
end

end OAI

end Source363

/- Original source: OAI/NumberTheory/DirichletL/Detector/Gauss.lean; sha256: 703401fb77716560cd0f33774271bd867e0f23853c5b255c7543bdb86f7dd14e -/
section Source364
namespace OAI

namespace SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section

def frequencyGauss {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) : ℂ :=
  ∑ v : F, ξ v * ψ (h * v)

theorem frequencyGauss_eq_shift {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) :
    frequencyGauss ξ ψ h = gaussSum ξ (ψ.mulShift h) := rfl

theorem frequencyGauss_nonzero {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) {h : F} (hh : h ≠ 0) :
    frequencyGauss ξ ψ h = ξ⁻¹ h * gaussSum ξ ψ := by
  exact gaussSum_mulShift_eq ξ ψ (Units.mk0 h hh)

theorem frequencyGauss_zero_nonprincipal {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (hξ : ξ ≠ 1) :
    frequencyGauss ξ ψ 0 = 0 := by
  simpa [frequencyGauss] using MulChar.sum_eq_zero_of_ne_one hξ

theorem frequencyGauss_nonprincipal {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (hξ : ξ ≠ 1) (h : F) :
    frequencyGauss ξ ψ h = ξ⁻¹ h * gaussSum ξ ψ := by
  by_cases hh : h = 0
  · subst h
    rw [frequencyGauss_zero_nonprincipal ξ ψ hξ, MulChar.map_zero, zero_mul]
  · exact frequencyGauss_nonzero ξ ψ hh

theorem frequencyGauss_principal {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (h : F) :
    frequencyGauss 1 ψ h = if h = 0 then (Nat.card Fˣ : ℂ) else -1 := by
  classical
  by_cases hh : h = 0
  · subst h
    simpa [frequencyGauss, Nat.card_eq_fintype_card] using
      (MulChar.sum_one_eq_card_units (R := F) (R' := ℂ))
  · rw [ite_eq_right hh, frequencyGauss_nonzero _ ψ hh, inv_one,
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hh), one_mul]
    exact gaussSum_one_left hψ

theorem gauss_inverse_pair {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * (Fintype.card F : ℂ) := by
  rw [← mul_gaussSum_inv_eq_gaussSum χ⁻¹, mul_left_comm,
    gaussSum_mul_gaussSum_eq_card hχ hψ, MulChar.inv_apply', inv_neg_one]

def normalizedGauss {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  gaussSum χ ψ / (Real.sqrt (Fintype.card F) : ℂ)

theorem normalizedGauss_inverse_pair {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    normalizedGauss χ ψ * normalizedGauss χ⁻¹ ψ = χ (-1) := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt (Fintype.card F) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ _)
  unfold normalizedGauss
  rw [div_mul_div_comm, ← pow_two, hs, gauss_inverse_pair χ ψ hχ hψ]
  exact mul_div_cancel_right₀ _ hq

theorem finite_gauss_convolution {F : Type*} [Field F] [Fintype F]
    (χ ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) :
    (∑ d : F, χ d * frequencyGauss ξ ψ (h - d)) =
      χ⁻¹ (-1) * gaussSum χ ψ * frequencyGauss (ξ * χ⁻¹) ψ h := by
  classical
  have hfreq (v : F) :
      ξ v * (∑ d : F, χ d * ψ (-(v * d))) =
        χ⁻¹ (-1) * gaussSum χ ψ * (ξ v * χ⁻¹ v) := by
    by_cases hv : v = 0
    · subst v
      simp [MulChar.map_zero]
    · have hn : -v ≠ 0 := neg_ne_zero.mpr hv
      have he := gaussSum_mulShift_eq χ ψ (Units.mk0 (-v) hn)
      simp only [gaussSum, AddChar.mulShift_apply, Units.val_mk0] at he
      have hinv : χ⁻¹ (-v) = χ⁻¹ (-1) * χ⁻¹ v := by rw [← map_mul]; congr 1; ring
      rw [hinv] at he
      have he' : (∑ d : F, χ d * ψ (-(v * d))) =
          (χ⁻¹ (-1) * χ⁻¹ v) * gaussSum χ ψ := by
        simpa only [neg_mul, gaussSum] using he
      rw [he']
      ring
  unfold frequencyGauss
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ v : F, ∑ d : F, χ d * (ξ v * ψ ((h - d) * v))) =
        ∑ v : F, ψ (h * v) * (ξ v * ∑ d : F, χ d * ψ (-(v * d))) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [show (h - d) * v = h * v + -(v * d) by ring, ψ.map_add_eq_mul]
      ring
    _ = ∑ v : F, ψ (h * v) *
        (χ⁻¹ (-1) * gaussSum χ ψ * (ξ v * χ⁻¹ v)) := by simp_rw [hfreq]
    _ = ∑ v : F, χ⁻¹ (-1) * gaussSum χ ψ * ((ξ * χ⁻¹) v * ψ (h * v)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [MulChar.mul_apply]
      ring

end
end SevenEighths.ProbeGauss

end OAI

end Source364

/- Original source: OAI/NumberTheory/DirichletL/Detector/PrimePower.lean; sha256: 2a1f1361af78658be0076053f8169e6900093b25ddc014ff88a2179aec0f1bdb -/
section Source365
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein

local notation "O" => ActualEisensteinCubic.O

def primeGauss (p : O) (hp : p ≠ 0) (χ : MulChar (O ⧸ Ideal.span {p}) ℂ)
    (h : O) : ℂ :=
  ∑' x : O ⧸ Ideal.span {p}, χ x * quotientTrace p hp (Ideal.Quotient.mk _ h * x)

def primePowerGauss (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) : ℂ :=
  conductorFourier p (p ^ n) hp (pow_ne_zero _ hp) χ h

theorem primePowerGauss_support (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O)
    (hG : primePowerGauss p hp χ n h ≠ 0) : p ^ n ∣ h :=
  conductorFourier_support p (p ^ n) hp (pow_ne_zero _ hp) χ h hG

theorem primePowerGauss_zero_off_support (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O)
    (hdiv : ¬p ^ n ∣ h) : primePowerGauss p hp χ n h = 0 := by
  by_contra hG
  exact hdiv (primePowerGauss_support p hp χ n h hG)

theorem primePowerGauss_lift (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) :
    primePowerGauss p hp χ n (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n * primeGauss p hp χ h := by
  unfold primePowerGauss primeGauss
  rw [conductorFourier_lift]
  have hn : Ideal.absNorm (Ideal.span {p ^ n}) = Ideal.absNorm (Ideal.span {p}) ^ n := by
    rw [← Ideal.span_singleton_pow, map_pow]
  rw [hn, Nat.cast_pow]

theorem primePowerGauss_nonprincipal_extra_divisibility (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) (n : ℕ) (h : O)
    (hph : p ∣ h) : primePowerGauss p hp χ n (p ^ n * h) = 0 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primePowerGauss_lift]
  have hz : Ideal.Quotient.mk (Ideal.span {p}) h = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hph)
  have hzero : primeGauss p hp χ h = 0 := by
    rw [primeGauss, tsum_fintype]
    simp only [hz, zero_mul, AddChar.map_zero_eq_one, mul_one]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  rw [hzero, mul_zero]

theorem primePowerGauss_principal (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hψ : quotientTrace p hp ≠ 1) (n : ℕ) (h : O) :
    primePowerGauss p hp 1 n (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        (if p ∣ h then (Nat.card (O ⧸ Ideal.span {p})ˣ : ℂ) else -1) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primePowerGauss_lift]
  congr 1
  have hdiv : Ideal.Quotient.mk (Ideal.span {p}) h = 0 ↔ p ∣ h := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  simpa only [primeGauss, tsum_fintype, ProbeGauss.frequencyGauss, hdiv] using
    ProbeGauss.frequencyGauss_principal (quotientTrace p hp) hψ
      (Ideal.Quotient.mk (Ideal.span {p}) h)

theorem higher_outer_lift_annihilated (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) {n : ℕ} (hn : 0 < n) (m : O) :
    ξ (Ideal.Quotient.mk (Ideal.span {p}) m) * primePowerGauss p hp χ n (-m) = 0 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  by_cases hG : primePowerGauss p hp χ n (-m) = 0
  · rw [hG, mul_zero]
  · have hdneg := primePowerGauss_support p hp χ n (-m) hG
    have hdpow : p ∣ p ^ n := dvd_pow_self p (Nat.ne_of_gt hn)
    have hdm : p ∣ m := dvd_neg.mp (hdpow.trans hdneg)
    have hz : Ideal.Quotient.mk (Ideal.span {p}) m = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdm)
    rw [hz, MulChar.map_zero, zero_mul]

def scalarKOne (p : O) (hp : p ≠ 0)
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {p}, χ d * primePowerGauss p hp ξ n
    (h - p ^ n * GaussianShiftedPartition.representative p d)

theorem scalarKOne_eq (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) :
    scalarKOne p hp χ ξ n h =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (ξ * χ⁻¹) n h := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  by_cases hdiv : p ^ n ∣ h
  · obtain ⟨k, rfl⟩ := hdiv
    have hmk (d : O ⧸ Ideal.span {p}) :
        Ideal.Quotient.mk (Ideal.span {p})
          (k - GaussianShiftedPartition.representative p d) =
          Ideal.Quotient.mk (Ideal.span {p}) k - d := by
      rw [map_sub, GaussianShiftedPartition.representative_spec]
    have hscalar : scalarKOne p hp χ ξ n (p ^ n * k) =
        (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
          ∑ d : O ⧸ Ideal.span {p}, χ d * ProbeGauss.frequencyGauss ξ
            (quotientTrace p hp) (Ideal.Quotient.mk _ k - d) := by
      unfold scalarKOne
      rw [tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [← mul_sub, primePowerGauss_lift]
      have he : primeGauss p hp ξ (k - GaussianShiftedPartition.representative p d) =
          ProbeGauss.frequencyGauss ξ (quotientTrace p hp) (Ideal.Quotient.mk _ k - d) := by
        rw [primeGauss, tsum_fintype]
        simp only [hmk, ProbeGauss.frequencyGauss]
      rw [he]
      ring
    rw [hscalar, ProbeGauss.finite_gauss_convolution, primePowerGauss_lift]
    have hG : primeGauss p hp χ 1 = gaussSum χ (quotientTrace p hp) := by
      simp [primeGauss, tsum_fintype, gaussSum]
    have hF : primeGauss p hp (ξ * χ⁻¹) k =
        ProbeGauss.frequencyGauss (ξ * χ⁻¹) (quotientTrace p hp) (Ideal.Quotient.mk _ k) := by
      simp only [primeGauss, tsum_fintype, ProbeGauss.frequencyGauss]
    rw [hG, hF]
    ring
  · rw [primePowerGauss_zero_off_support p hp (ξ * χ⁻¹) n h hdiv, mul_zero]
    unfold scalarKOne
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro d _
    have hndiv : ¬p ^ n ∣ h - p ^ n * GaussianShiftedPartition.representative p d := by
      intro hd
      apply hdiv
      have ha := dvd_add hd (dvd_mul_right (p ^ n)
        (GaussianShiftedPartition.representative p d))
      simpa only [sub_add_cancel] using ha
    rw [primePowerGauss_zero_off_support p hp ξ n _ hndiv, mul_zero]

end SevenEighths.ProbePrimePower
end

end OAI

end Source365

/- Original source: OAI/NumberTheory/DirichletL/Detector/GaussValuation.lean; sha256: d3a89fbcbfc27d896d16326057e3825d3814a547b99547be22b1a73c27a02a45 -/
section Source366
namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem primePowerGauss_at_pow_nonprincipal (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) (n j : ℕ) :
    primePowerGauss p hp.ne_zero χ n (p ^ j) =
      if j = n then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n * primeGauss p hp.ne_zero χ 1
      else 0 := by
  by_cases he : j = n
  · subst j
    rw [ite_eq_left rfl]
    simpa only [mul_one] using primePowerGauss_lift p hp.ne_zero χ n 1
  rw [ite_eq_right he]
  rcases lt_or_gt_of_ne he with hjn | hnj
  · apply primePowerGauss_zero_off_support
    rw [pow_dvd_pow_iff hp.ne_zero hp.not_isUnit]
    omega
  · have hle : n ≤ j := Nat.le_of_lt hnj
    have heq : p ^ j = p ^ n * p ^ (j - n) := by rw [← pow_add, Nat.add_sub_of_le hle]
    rw [heq]
    apply primePowerGauss_nonprincipal_extra_divisibility p hp.ne_zero χ hχ
    exact dvd_pow_self p (by omega)

theorem primePowerGauss_at_pow_principal (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hψ : quotientTrace p hp.ne_zero ≠ 1) (n j : ℕ) :
    primePowerGauss p hp.ne_zero 1 n (p ^ j) =
      (if n + 1 ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (n + 1) else 0) -
      (if n ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n else 0) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp.ne_zero
  have hcard : (Nat.card (O ⧸ Ideal.span {p})ˣ : ℂ) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1 := by
    rw [Nat.card_units, Nat.cast_sub (Nat.card_pos : 0 < Nat.card (O ⧸ Ideal.span {p})),
      Nat.cast_one]
    rfl
  rcases lt_trichotomy j n with hjn | he | hnj
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_self]
    apply primePowerGauss_zero_off_support
    rw [pow_dvd_pow_iff hp.ne_zero hp.not_isUnit]
    omega
  · subst j
    have hnot : ¬p ∣ (1 : O) := by simpa only [isUnit_iff_dvd_one] using hp.not_isUnit
    simpa only [mul_one, ite_eq_right hnot, ite_eq_right (Nat.not_succ_le_self n),
      ite_eq_left (le_refl n), zero_sub, mul_neg_one] using
      primePowerGauss_principal p hp.ne_zero hψ n 1
  · have hle : n ≤ j := by omega
    have heq : p ^ j = p ^ n * p ^ (j - n) := by rw [← pow_add, Nat.add_sub_of_le hle]
    have hd : p ∣ p ^ (j - n) := dvd_pow_self p (by omega)
    rw [heq, primePowerGauss_principal, ite_eq_left hd, ite_eq_left (by omega : n + 1 ≤ j),
      ite_eq_left hle, hcard, pow_succ]
    ring
    exact hψ

end SevenEighths.ProbePrimePower
end

end OAI

end Source366

/- Original source: OAI/NumberTheory/DirichletL/Detector/Sextic.lean; sha256: 7f72a9a6cec65f0d477abccafe320400b4c5598b430f9d161d937ef803a1419c -/
section Source367
namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem actualSextic_pow_eq_one_iff (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) (n : ℕ) :
    actualSextic P hg ^ n = 1 ↔ 6 ∣ n := by
  rw [← orderOf_dvd_iff_pow_eq_one, CenteredMomentCanonical.actualSextic_order_six P hg hc]

theorem actualSextic_primePowerGauss_at_pow (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r n j : ℕ) :
    primePowerGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) n (p ^ j) =
      if 6 ∣ r then
        (if n + 1 ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (n + 1) else 0) -
        (if n ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n else 0)
      else if j = n then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) 1 else 0 := by
  by_cases hr : 6 ∣ r
  · rw [ite_eq_left hr, (actualSextic_pow_eq_one_iff _ hg hc r).mpr hr]
    apply primePowerGauss_at_pow_principal p hp
    have hprim : (quotientTrace p hp.ne_zero).IsPrimitive :=
      GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero
    simpa using hprim (a := 1) one_ne_zero
  · rw [ite_eq_right hr]
    exact primePowerGauss_at_pow_nonprincipal p hp _
      (fun h => hr ((actualSextic_pow_eq_one_iff _ hg hc r).mp h)) n j

end SevenEighths.ProbePrimePower
end

end OAI

end Source367

/- Original source: OAI/NumberTheory/DirichletL/Detector/CongruenceScalar.lean; sha256: 125a7bd771511b098c3e600d894a8d19704798583a82d2e03ee1b56e37a6476b -/
section Source368
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

def exactQuotient (a b : O) (h : b ∣ a) : O := Classical.choose h

lemma exactQuotient_spec (a b : O) (h : b ∣ a) : a = b * exactQuotient a b h :=
  Classical.choose_spec h

lemma exactQuotient_eq (a b c : O) (h : b ∣ a) (hb : b ≠ 0) (he : a = b*c) :
    exactQuotient a b h = c := by
  apply mul_left_cancel₀ hb
  exact (exactQuotient_spec a b h).symm.trans he

def positiveScalar (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k j : ℕ) : ℂ :=
  if k = 0 then primePowerGauss p hp (χ^(n+1)) n (p^j)
  else ∑' d : O ⧸ Ideal.span {p^k},
    if h : p^k ∣ p^j-p^(n+1)*representative (p^k) d then
      (χ^k) (Ideal.Quotient.mk (Ideal.span {p}) (representative (p^k) d)) *
        primePowerGauss p hp (χ^(n+1)) n
          (exactQuotient (p^j-p^(n+1)*representative (p^k) d) (p^k) h)
    else 0

@[simp] theorem positiveScalar_kzero (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 0 j = primePowerGauss p hp (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, ite_true]

theorem positiveScalar_kone_jzero (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) :
    positiveScalar p hp.ne_zero χ n 1 0 = 0 := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false]
  rw [pow_one]
  simp only [pow_zero, pow_one]
  refine (tsum_congr (g := fun _ => (0:ℂ)) ?_).trans tsum_zero
  intro d
  rw [dite_eq_right]
  intro hd
  have hd2 : p ∣ p^(n+1)*representative p d :=
    (dvd_pow_self p (by omega : n+1 ≠ 0)).mul_right _
  have hunit : p ∣ (1:O) := by
    have := dvd_add hd hd2
    simpa only [sub_add_cancel] using this
  exact hp.not_isUnit (isUnit_iff_dvd_one.mpr hunit)

theorem positiveScalar_kone_convolution (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) = scalarKOne p hp χ (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false, scalarKOne]
  rw [pow_one]
  simp only [pow_one]
  apply tsum_congr
  intro d
  have he : p^(j+1)-p^(n+1)*representative p d = p*(p^j-p^n*representative p d) := by
    simp only [pow_succ]
    ring
  have hd : p ∣ p^(j+1)-p^(n+1)*representative p d := ⟨_,he⟩
  rw [dite_eq_left hd, exactQuotient_eq _ _ _ hd hp he, representative_spec]

theorem positiveScalar_kone (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (χ^n) n (p^j) := by
  rw [positiveScalar_kone_convolution, scalarKOne_eq]
  have he : χ^(n+1)*χ⁻¹ = χ^n := by rw [pow_succ, mul_assoc, mul_inv_cancel, mul_one]
  rw [he]

end SevenEighths.ProbePrimePower
end

end OAI

end Source368

/- Original source: OAI/NumberTheory/DirichletL/Detector/LiftedFourier.lean; sha256: 786b7869d73469ebe13497c7d7fe1d72aa9a8978b2972b840f34ef4c90a9f91a -/
section Source369
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

theorem primePowerGauss_lift_add (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k : ℕ) (h : O) :
    primePowerGauss p hp.ne_zero χ (n+k) (p^k*h) =
      (Ideal.absNorm (Ideal.span {p}):ℂ)^k * primePowerGauss p hp.ne_zero χ n h := by
  by_cases hd : p^n ∣ h
  · obtain ⟨a, rfl⟩ := hd
    have he : p^k*(p^n*a) = p^(n+k)*a := by rw [pow_add]; ring
    rw [he, primePowerGauss_lift, primePowerGauss_lift, pow_add]
    ring
  · have hbig : ¬p^(n+k) ∣ p^k*h := by
      rw [pow_add, mul_comm (p^n) (p^k), mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)]
      exact hd
    rw [primePowerGauss_zero_off_support _ _ _ _ _ hbig,
      primePowerGauss_zero_off_support _ _ _ _ _ hd, mul_zero]

theorem primePowerGauss_add_period (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h a : O) :
    primePowerGauss p hp χ n (h+p^(n+1)*a) = primePowerGauss p hp χ n h := by
  unfold primePowerGauss conductorFourier
  apply tsum_congr
  intro x
  have hz : Ideal.Quotient.mk (Ideal.span {p*p^n}) (p^(n+1)*a) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    rw [pow_succ']
  simp only [map_add, hz, add_zero]

theorem gauss_exactQuotient_lift (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k : ℕ) (h : O) :
    (if hd : p^k ∣ h then primePowerGauss p hp.ne_zero χ n (exactQuotient h (p^k) hd) else 0) =
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^k)⁻¹ * primePowerGauss p hp.ne_zero χ (n+k) h := by
  have hq : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  by_cases hd : p^k ∣ h
  · rw [dite_eq_left hd]
    conv_rhs => rw [exactQuotient_spec h (p^k) hd]
    rw [primePowerGauss_lift_add p hp, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]
  · rw [dite_eq_right hd]
    have hnd : ¬p^(n+k) ∣ h := by
      intro he
      exact hd ((show p^k ∣ p^(n+k) from ⟨p^n, by rw [pow_add]; ring⟩).trans he)
    rw [primePowerGauss_zero_off_support _ _ _ _ _ hnd, mul_zero]

theorem positiveScalar_full_lift (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k j : ℕ) (hk : k ≠ 0) :
    positiveScalar p hp.ne_zero χ n k j =
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^k)⁻¹ *
        ∑' d : O ⧸ Ideal.span {p^k},
          (χ^k) (Ideal.Quotient.mk _ (representative (p^k) d)) *
            primePowerGauss p hp.ne_zero (χ^(n+1)) (n+k)
              (p^j-p^(n+1)*representative (p^k) d) := by
  rw [positiveScalar, ite_eq_right hk, ← tsum_mul_left]
  apply tsum_congr
  intro d
  have he := gauss_exactQuotient_lift p hp (χ^(n+1)) n k
    (p^j-p^(n+1)*representative (p^k) d)
  by_cases hd : p^k ∣ p^j-p^(n+1)*representative (p^k) d
  · rw [dite_eq_left hd] at he ⊢
    rw [he]
    ring
  · rw [dite_eq_right hd] at he ⊢
    linear_combination (χ^k) (Ideal.Quotient.mk _ (representative (p^k) d)) * he

lemma quotientTrace_split_frequency (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (H d v : O) :
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ ((H-b*d)*v)) =
      quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (H*v)) *
        quotientTrace a ha (Ideal.Quotient.mk _ ((-v)*d)) := by
  have hs := quotientTrace_conductor_scale a b ((-v)*d) ha hb 1
  simp only [mul_one, map_one] at hs
  rw [show (H-b*d)*v = H*v+b*((-v)*d) by ring, map_add, AddChar.map_add_eq_mul, hs]

def quotientFourier (p c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (H : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {c}, χ (Ideal.Quotient.mk _ (representative c d)) *
    quotientTrace c hc (Ideal.Quotient.mk _ (H*representative c d))

lemma quotientFourier_congr (p a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (H : O) (he : a=b) :
    quotientFourier p a ha χ H = quotientFourier p b hb χ H := by
  subst b
  rfl

lemma primePowerGauss_eq_quotientFourier (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (H : O) :
    primePowerGauss p hp χ n H =
      quotientFourier p (p*p^n) (mul_ne_zero hp (pow_ne_zero _ hp)) χ H := by
  unfold primePowerGauss conductorFourier quotientFourier
  apply tsum_congr
  intro d
  have hr : conductorReduction p (p^n) d =
      Ideal.Quotient.mk (Ideal.span {p}) (representative (p*p^n) d) := by
    conv_lhs => rw [← representative_spec (p*p^n) d]
    rfl
  have hm : Ideal.Quotient.mk (Ideal.span {p*p^n}) (H*representative (p*p^n) d) =
      Ideal.Quotient.mk _ H*d := by rw [map_mul, representative_spec]
  rw [hr, hm]

end SevenEighths.ProbePrimePower
end

end OAI

end Source369

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalFourier.lean; sha256: 926b9974a073f7ff4b3d979415254858e76c57bf6c8bd806799cbda8f974ec91 -/
section Source370
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein GaussianShiftedPartition ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

def rawFourier (a : O) (ha : a≠0) (F : (O ⧸ Ideal.span {a}) → ℂ) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {a}, F m * quotientTrace a ha (Ideal.Quotient.mk _ H * m)

theorem rawFourier_exactQuotient (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (H : O) :
    conductorFourier a s ha hs F H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) *
        (if h : s∣H then rawFourier a ha F (exactQuotient H s h) else 0) := by
  by_cases h : s∣H
  · rw [dite_eq_left h]
    conv_lhs => rw [exactQuotient_spec H s h]
    exact conductorFourier_lift a s ha hs F _
  · rw [dite_eq_right h, mul_zero]
    by_contra hn
    exact h (conductorFourier_support a s ha hs F H hn)

def congruenceCoefficient (a s : O) (ha : a≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {s}, χ d *
    (if h : s ∣ H-a*representative s d then
      rawFourier a ha F (exactQuotient (H-a*representative s d) s h) else 0)

lemma trace_split_product (a s : O) (ha : a≠0) (hs : s≠0) (H m d : O) :
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ (H*m)) *
      quotientTrace s hs (Ideal.Quotient.mk _ ((-m)*d)) =
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ ((H-a*d)*m)) := by
  have he := quotientTrace_split_frequency s a hs ha H d m
  simp only [quotientTrace_mk] at he ⊢
  simpa only [mul_comm s a] using he.symm

def fullFourier (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {a*s}, F (conductorReduction a s m) *
    rawFourier s hs χ (-representative (a*s) m) *
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ H*m)

theorem fullFourier_eq_congruence (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) :
    fullFourier a s ha hs F χ H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) * congruenceCoefficient a s ha F χ H := by
  let : Finite (O ⧸ Ideal.span {a*s}) := finite_quotient_span (mul_ne_zero ha hs)
  let : Finite (O ⧸ Ideal.span {s}) := finite_quotient_span hs
  let : Fintype (O ⧸ Ideal.span {a*s}) := Fintype.ofFinite _
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  unfold fullFourier rawFourier
  simp_rw [tsum_fintype, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold congruenceCoefficient
  rw [tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    _ = χ d * conductorFourier a s ha hs F (H-a*representative s d) := by
      rw [conductorFourier, tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have ht := trace_split_product a s ha hs H (representative (a*s) m) (representative s d)
      simp only [map_mul, representative_spec] at ht
      rw [← ht]
      ring
    _ = _ := by rw [rawFourier_exactQuotient]; ring

theorem rawFourier_norm_le (a : O) (ha : a≠0) (F : (O ⧸ Ideal.span {a}) → ℂ)
    (hF : ∀ m, ‖F m‖≤1) (H : O) :
    ‖rawFourier a ha F H‖ ≤ (Ideal.absNorm (Ideal.span {a}):ℝ) := by
  let := finite_quotient_span ha
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  rw [rawFourier, tsum_fintype]
  calc
    _ ≤ ∑ m : O ⧸ Ideal.span {a}, ‖F m * quotientTrace a ha (Ideal.Quotient.mk _ H*m)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m : O ⧸ Ideal.span {a}, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, AddChar.norm_apply, mul_one]
      exact hF m
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem congruenceCoefficient_norm_le (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ)
    (hF : ∀ m, ‖F m‖≤1) (hχ : ∀ d, ‖χ d‖≤1) (H : O) :
    ‖congruenceCoefficient a s ha F χ H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ) * (Ideal.absNorm (Ideal.span {a}):ℝ) := by
  let := finite_quotient_span hs
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  unfold congruenceCoefficient
  rw [tsum_fintype]
  calc
    _ ≤ ∑ d : O ⧸ Ideal.span {s}, ‖χ d *
        (if h : s ∣ H-a*representative s d then
          rawFourier a ha F (exactQuotient (H-a*representative s d) s h) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _d : O ⧸ Ideal.span {s}, (Ideal.absNorm (Ideal.span {a}):ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · rw [norm_mul]
        exact (mul_le_mul (hχ d) (rawFourier_norm_le a ha F hF _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      · simp only [mul_zero, norm_zero]
        positivity
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end SevenEighths.ProbePhysical
end

end OAI

end Source370

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalCoefficient.lean; sha256: cc0d219fc811ba2c1198a4f75dd08cd5f7dc40fdd9a6dba9eacd185085c46d1d -/
section Source371
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

def calibratedNumerator (C : CalibrationData) (A m : O) : ℂ :=
  C.residueMonoid m * idealRowHom m (Ideal.span {A})

lemma calibratedNumerator_congr (C : CalibrationData) (A m n : O)
    (h : m-n ∈ (Ideal.span {C.generator*A} : Ideal O)) :
    calibratedNumerator C A m = calibratedNumerator C A n := by
  have hd : C.generator*A ∣ m-n := Ideal.mem_span_singleton.mp h
  have hb : Ideal.Quotient.mk (Ideal.span {C.generator}) m =
      Ideal.Quotient.mk (Ideal.span {C.generator}) n := by
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ((dvd_mul_right C.generator A).trans hd)
  have hA : m-n ∈ (Ideal.span {A} : Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_left A C.generator).trans hd)
  unfold calibratedNumerator CalibrationData.residueMonoid
  simp only [MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, hb, idealRowHom_congr_mod (Ideal.span {A}) m n hA]

def calibratedQuotient (C : CalibrationData) (A : O)
    (m : O ⧸ Ideal.span {C.generator*A}) : ℂ :=
  calibratedNumerator C A (representative (C.generator*A) m)

lemma calibratedQuotient_mk (C : CalibrationData) (A m : O) :
    calibratedQuotient C A (Ideal.Quotient.mk _ m) = calibratedNumerator C A m := by
  apply calibratedNumerator_congr
  exact Ideal.Quotient.eq.mp (representative_spec _ _)

def outerQuotient (s : O) (d : O ⧸ Ideal.span {s}) : ℂ :=
  idealRowHom (representative s d) (Ideal.span {s})

lemma rawFourier_outer (s : O) (hs : s≠0) (h : O) :
    rawFourier s hs (outerQuotient s) h = sexticGauss s hs h := rfl

def actualCongruenceCoefficient (C : CalibrationData) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  congruenceCoefficient (C.generator*A) s (mul_ne_zero C.generator_ne_zero hA)
    (calibratedQuotient C A) (outerQuotient s) H

def actualPhysicalFourier (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {(C.generator*A)*s},
    calibratedNumerator C A (representative ((C.generator*A)*s) m) *
    sexticGauss s hs (-representative ((C.generator*A)*s) m) *
    quotientTrace ((C.generator*A)*s) (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)
      (Ideal.Quotient.mk _ H*m)

theorem actualPhysicalFourier_eq (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    actualPhysicalFourier C A s hA hs H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) * actualCongruenceCoefficient C A s hA H := by
  unfold actualCongruenceCoefficient
  rw [← fullFourier_eq_congruence (C.generator*A) s (mul_ne_zero C.generator_ne_zero hA) hs]
  unfold actualPhysicalFourier fullFourier
  apply tsum_congr
  intro m
  rw [rawFourier_outer]
  have he : conductorReduction (C.generator*A) s m =
      Ideal.Quotient.mk (Ideal.span {C.generator*A}) (representative ((C.generator*A)*s) m) := by
    conv_lhs => rw [← representative_spec ((C.generator*A)*s) m]
    rfl
  rw [he, calibratedQuotient_mk]

lemma calibratedNumerator_norm_le (C : CalibrationData) (A m : O) :
    ‖calibratedNumerator C A m‖≤1 := by
  let := ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  have hC : ‖C.residueMonoid m‖≤1 :=
    QuadraticInitialBound.norm_finite_character_le_one C.residue _
  rw [calibratedNumerator, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hC).trans (idealRowHom_norm _ _)

theorem actualCongruenceCoefficient_norm_le (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (H : O) :
    ‖actualCongruenceCoefficient C A s hA H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ) *
        (Ideal.absNorm (Ideal.span {C.generator*A}):ℝ) := by
  apply congruenceCoefficient_norm_le _ _ _ hs
  · intro m
    exact calibratedNumerator_norm_le C A _
  · intro d
    exact idealRowHom_norm _ _

theorem normalizedPhysicalFourier_eq (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (H : O) :
    (Real.sqrt (Ideal.absNorm (Ideal.span {s})):ℂ)⁻¹ * actualPhysicalFourier C A s hA hs H =
      (Real.sqrt (Ideal.absNorm (Ideal.span {s})):ℂ) * actualCongruenceCoefficient C A s hA H := by
  have hQ : 0<(Ideal.absNorm (Ideal.span {s}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hs))
  have hroot : (Real.sqrt (Ideal.absNorm (Ideal.span {s})):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hQ).ne'
  have he : (Ideal.absNorm (Ideal.span {s}):ℂ) =
      (Real.sqrt (Ideal.absNorm (Ideal.span {s})):ℂ)^2 := by
    exact_mod_cast (Real.sq_sqrt hQ.le).symm
  rw [actualPhysicalFourier_eq, he]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI

end Source371

/- Original source: OAI/NumberTheory/DirichletL/Detector/CalibrationCRT.lean; sha256: 8b959980cda702c19574fbffcabdec524da979475df31bf725dd9c2bf4f0a552 -/
section Source372
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstPoisson
local notation "O" => ActualEisensteinCubic.O

theorem coprime_mixed_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (F : Residue b → ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        F (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      χa (Ideal.Quotient.mk _ b) *
        residueGauss a ha χa (frequencyReduction a (a*b) (dvd_mul_right a b) h) *
        (∑ y : Residue b, F (Ideal.Quotient.mk _ a*y) *
          quotientTrace b hb (frequencyReduction b (a*b) (dvd_mul_left b a) h*y)) := by
  let ua := residueUnit a b hcop
  let ub := residueUnit b a hcop.symm
  let e : Residue a × Residue b ≃ Residue (a * b) :=
    (ua.mulLeft.prodCongr ub.mulLeft).trans (principalCRT a b hcop).toEquiv.symm
  have heproj (x : Residue a × Residue b) : principalCRT a b hcop (e x) =
      ((ua : Residue a) * x.1, (ub : Residue b) * x.2) := by
    change (principalCRT a b hcop).toEquiv
      ((principalCRT a b hcop).toEquiv.symm ((ua : Residue a) * x.1, (ub : Residue b) * x.2)) = _
    exact (principalCRT a b hcop).toEquiv.apply_symm_apply _
  have he (x : Residue a × Residue b) : e x =
      scaledResidue a b (a * b) rfl x.1 + scaledResidue b a (a * b) (mul_comm a b) x.2 := by
    apply (principalCRT a b hcop).injective
    rw [heproj, map_add, principalCRT_scaled_left, principalCRT_scaled_right]
    simp only [Prod.mk_add_mk, add_zero, zero_add, ua, ub, residueUnit_coe]
  have hproj (x : Residue (a * b)) :
      (frequencyReduction a (a * b) (dvd_mul_right a b) x,
        frequencyReduction b (a * b) (dvd_mul_left b a) x) = principalCRT a b hcop x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [frequencyReduction_mk, principalCRT_mk]
  have hprojA (x : Residue a × Residue b) :
      frequencyReduction a (a * b) (dvd_mul_right a b) (e x) = Ideal.Quotient.mk _ b * x.1 := by
    have ht := congrArg Prod.fst (hproj (e x))
    rw [heproj] at ht
    simpa only [ua, residueUnit_coe] using ht
  have hprojB (x : Residue a × Residue b) :
      frequencyReduction b (a * b) (dvd_mul_left b a) (e x) = Ideal.Quotient.mk _ a * x.2 := by
    have ht := congrArg Prod.snd (hproj (e x))
    rw [heproj] at ht
    simpa only [ub, residueUnit_coe] using ht
  rw [← e.sum_comp]
  simp_rw [hprojA, hprojB]
  simp only [map_mul, he, mul_add, AddChar.map_add_eq_mul,
    quotientTrace_scaled a b (a * b) rfl ha hb (mul_ne_zero ha hb),
    quotientTrace_scaled b a (a * b) (mul_comm a b) hb ha (mul_ne_zero ha hb)]
  simp only [Fintype.sum_prod_type, residueGauss, tsum_fintype]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem calibration_mixed_fourier (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (b : O) (hb : b≠0) (hcop : IsCoprime (calibrationForSet S hS).generator b)
    (F : Residue b → ℂ) (H : O) :
    let C := calibrationForSet S hS
    (∑' x : Residue (C.generator*b),
      C.residue (frequencyReduction C.generator (C.generator*b) (dvd_mul_right _ _) x) *
        F (frequencyReduction b (C.generator*b) (dvd_mul_left _ _) x) *
        quotientTrace (C.generator*b) (mul_ne_zero C.generator_ne_zero hb) (Ideal.Quotient.mk _ H*x)) =
      C.residueMonoid b * star (C.residueMonoid H) * (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        (∑' y : Residue b, F (Ideal.Quotient.mk _ C.generator*y) *
          quotientTrace b hb (Ideal.Quotient.mk _ H*y)) := by
  dsimp only
  let C := calibrationForSet S hS
  let := finite_quotient_span C.generator_ne_zero
  let := finite_quotient_span hb
  let := finite_quotient_span (mul_ne_zero C.generator_ne_zero hb)
  let : Fintype (Residue C.generator) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (C.generator*b)) := Fintype.ofFinite _
  rw [tsum_fintype, coprime_mixed_fourier _ _ C.generator_ne_zero hb hcop]
  change C.residueMonoid b * calibrationGauss C H * _ = _
  rw [calibrationForSet_gauss]
  rw [tsum_fintype]
  dsimp only [C]
  simp only [frequencyReduction_mk]
  ring

theorem calibration_mixed_fourier_zero (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (b : O) (hb : b≠0) (hcop : IsCoprime (calibrationForSet S hS).generator b)
    (F : Residue b → ℂ) (H : O) (hH : ¬IsCoprime (calibrationForSet S hS).generator H) :
    let C := calibrationForSet S hS
    (∑' x : Residue (C.generator*b),
      C.residue (frequencyReduction C.generator (C.generator*b) (dvd_mul_right _ _) x) *
        F (frequencyReduction b (C.generator*b) (dvd_mul_left _ _) x) *
        quotientTrace (C.generator*b) (mul_ne_zero C.generator_ne_zero hb) (Ideal.Quotient.mk _ H*x)) = 0 := by
  dsimp only
  rw [calibration_mixed_fourier S hS b hb hcop F H]
  have hz : (calibrationForSet S hS).residueMonoid H=0 := by
    change (calibrationForSet S hS).residue (Ideal.Quotient.mk _ H)=0
    apply MulChar.map_nonunit
    exact fun h => hH ((isUnit_quotient_span_iff _ _).mp h)
  rw [hz, star_zero]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source372

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstMixed.lean; sha256: 090a4c5a631abc46004b0ad7a085c8d6f906fb3f3690ff9d353ade5566e50322 -/
section Source373
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstMixed
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem frequencyReduction_comp (d n M : O) (hd : d∣n) (hn : n∣M) (x : Residue M) :
    frequencyReduction d n hd (frequencyReduction n M hn x)=frequencyReduction d M (hd.trans hn) x := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [frequencyReduction_mk]

theorem three_factor_mixed_fourier (a b c : O) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : IsCoprime a (b*c)) (hbc : IsCoprime b c)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue c)]
    [Fintype (Residue (b*c))] [Fintype (Residue (a*(b*c)))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (G : Residue c → ℂ)
    (h : Residue (a*(b*c))) :
    (∑ x : Residue (a*(b*c)),
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
      χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
      G (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x)*
        quotientTrace (a*(b*c)) (mul_ne_zero ha (mul_ne_zero hb hc)) (h*x)) =
      χa (Ideal.Quotient.mk _ (b*c))*χb (Ideal.Quotient.mk _ (a*c))*
        residueGauss a ha χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) h)*
        residueGauss b hb χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) h)*
        (∑ y : Residue c,G (Ideal.Quotient.mk _ (a*b)*y)*
          quotientTrace c hc (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) h*y)) := by
  let F : Residue (b*c) → ℂ := fun y =>
    χb (frequencyReduction b (b*c) (dvd_mul_right _ _) y)*
      G (frequencyReduction c (b*c) (dvd_mul_left _ _) y)
  let h' := frequencyReduction (b*c) (a*(b*c)) (dvd_mul_left _ _) h
  have he (x : Residue (a*(b*c))) :
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
        F (frequencyReduction (b*c) (a*(b*c)) (dvd_mul_left _ _) x) =
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
        χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
        G (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x) := by
    dsimp only [F]
    rw [frequencyReduction_comp,frequencyReduction_comp]
    ring
  simp_rw [← he]
  rw [ProbePhysical.coprime_mixed_fourier a (b*c) ha (mul_ne_zero hb hc) habc χa F h]
  have hf (y : Residue (b*c)) : F (Ideal.Quotient.mk _ a*y)=
      χb (Ideal.Quotient.mk _ a)*
        (χb (frequencyReduction b (b*c) (dvd_mul_right _ _) y)*
          G (Ideal.Quotient.mk _ a*frequencyReduction c (b*c) (dvd_mul_left _ _) y)) := by
    simp only [F,map_mul,frequencyReduction_mk]
    ring
  simp_rw [hf,mul_assoc]
  rw [← Finset.mul_sum]
  have hh := ProbePhysical.coprime_mixed_fourier b c hb hc hbc χb
    (fun y => G (Ideal.Quotient.mk _ a*y)) h'
  simp only [mul_assoc] at hh
  rw [hh]
  simp only [h',frequencyReduction_comp,map_mul,mul_assoc]
  ring

end SevenEighths.CenteredMomentFirstMixed

end

end OAI

end Source373

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstReduced.lean; sha256: 47b1c62b2c400acbb50b3d049d1751a5c5a76071f7ab5a97d77168daccc7e764 -/
section Source374
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstReduced
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstMixed CenteredMomentActive
local notation "O" => ActualEisensteinCubic.O

def tripleRow (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (z : O) : ℂ :=
  χa (Ideal.Quotient.mk _ z)*χb (Ideal.Quotient.mk _ z)*G (Ideal.Quotient.mk _ z)

def tripleResidue (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (x : Residue (a*(b*r))) : ℂ :=
  χa (frequencyReduction a _ (dvd_mul_right _ _) x)*
    χb (frequencyReduction b _ (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
    G (frequencyReduction r _ (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x)

@[simp] theorem tripleResidue_mk (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (z : O) :
    tripleResidue a b r χa χb G (Ideal.Quotient.mk _ z)=tripleRow a b r χa χb G z := by
  simp only [tripleResidue,tripleRow,frequencyReduction_mk]

theorem tripleRow_mul (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ)
    (hG : ∀ x y,G (x*y)=G x*G y) (x y : O) :
    tripleRow a b r χa χb G (x*y)=tripleRow a b r χa χb G x*tripleRow a b r χa χb G y := by
  simp only [tripleRow,map_mul,hG]
  ring

def tripleFourier (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (h : O) : ℂ :=
  ∑' x : Residue (a*(b*r)),tripleResidue a b r χa χb G x*
    quotientTrace (a*(b*r)) (mul_ne_zero ha (mul_ne_zero hb hr)) (Ideal.Quotient.mk _ h*x)

theorem tripleRow_radial_summable (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => tripleRow a b r χa χb G z*W (‖eisEmbedding z‖^2/K)) := by
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  have hh := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a*(b*r)})) (tripleResidue a b r χa χb G)
  simpa only [tripleResidue_mk,scaledRadialTest_apply] using hh

theorem tripleRow_poisson (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O,tripleRow a b r χa χb G z*W (‖eisEmbedding z‖^2/K)) =
      ((K/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
        tripleFourier a b r ha hb hr χa χb G h*
          paperRadialFourier W (K*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2) := by
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  have hh := actual_radial_paper_poisson_trace W K hK (a*(b*r))
    (mul_ne_zero ha (mul_ne_zero hb hr)) (tripleResidue a b r χa χb G)
  simpa only [tripleResidue_mk,tripleFourier,quotientTrace,tsum_fintype,Complex.real_smul] using hh

theorem masked_triple_poisson {α : Type*} (P : α → Ideal O)
    [∀ i,(P i).IsMaximal] (hinj : Function.Injective P) (S : Finset α)
    (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x y,G (x*y)=G x*G y)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O,rowCoprimeMask P S z*tripleRow a b r χa χb G z*W (‖eisEmbedding z‖^2/K)) =
      ∑ E ∈ S.powerset,
        let e := primeSubsetGenerator P E
        let k := K/‖eisEmbedding e‖^2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E,P i):ℂ)*tripleRow a b r χa χb G e*
          (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
            tripleFourier a b r ha hb hr χa χb G h*
              paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2)) := by
  rw [tsum_masked_radial_dilations P hinj S _ (tripleRow_mul a b r χa χb G hG) W K
    (tripleRow_radial_summable a b r ha hb hr χa χb G W K hK)]
  apply Finset.sum_congr rfl
  intro E hE
  rw [tripleRow_poisson a b r ha hb hr χa χb G W _ (primeSubset_reducedScale_pos P E hK)]

theorem principalSexticRow_mul {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (j : ι → ℕ) (r : O) (hr : Ideal.span {r}=∏ i,P i) (x y : Residue r) :
    principalSexticRow P hcop hg j r hr (x*y)=
      principalSexticRow P hcop hg j r hr x*principalSexticRow P hcop hg j r hr y := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul,principalSexticRow_mk P hcop hg j r hr (x*y),
    principalSexticRow_mk P hcop hg j r hr x,principalSexticRow_mk P hcop hg j r hr y,
    finiteSexticRow_mul P hg j x y]

theorem common_residual_reduced_poisson {ι : Type*}
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i) (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (B : Finset ι) (c d : ι → ℕ) (hc : ∀ i∈B,c i≠0) (hd : ∀ i∈B,d i≠0)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    let Q := fun i : activeSupport B c d => P i.val
    let hj := fun i : activeSupport B c d => netExponent (c i.val) (d i.val)
    let r := finitePrimeModulus Q
    let G := principalSexticRow Q (activePrimes_pairwise_coprime P hinj B c d)
      (fun i => hg i.val) hj r (span_finitePrimeModulus Q)
    (∑' z : O,χa (Ideal.Quotient.mk _ z)*χb (Ideal.Quotient.mk _ z)*
      (CanonicalRowCompletion.idealRowHom z (∏ i∈B,P i^c i)*
        star (CanonicalRowCompletion.idealRowHom z (∏ i∈B,P i^d i)))*
      W (‖eisEmbedding z‖^2/K)) =
      ∑ E ∈ (principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        let k := K/‖eisEmbedding e‖^2
        (UniqueFactorizationMonoid.moebius (∏ i∈E,P i):ℂ)*tripleRow a b r χa χb G e*
          (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
            tripleFourier a b r ha hb (finitePrimeModulus_ne_zero Q) χa χb G h*
              paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2)) := by
  dsimp only
  rw [← masked_triple_poisson P hinj (principalSupport B c d) a b _ ha hb
    (finitePrimeModulus_ne_zero _) χa χb _
    (principalSexticRow_mul _ _ _ _ _ _) W K hK]
  apply tsum_congr
  intro z
  rw [common_ideal_pair_active P hg hchar B c d hc hd]
  simp only [tripleRow,principalSexticRow_mk (fun i : activeSupport B c d => P i.val)
    (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => netExponent (c i.val) (d i.val)) _ (span_finitePrimeModulus _) z]
  ring

end SevenEighths.CenteredMomentFirstReduced

end

end OAI

end Source374

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstActiveFourier.lean; sha256: 43e18188c6bce00c925ac8b8b3e723266460753a19f882c58abdd88a6a0306bd -/
section Source375
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstActiveFourier
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstMixed CenteredMomentFirstReduced
local notation "O" => ActualEisensteinCubic.O

theorem shifted_active_fourier {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6) (v h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    (∑' x : Residue r,G (Ideal.Quotient.mk _ v*x)*
      quotientTrace r (finitePrimeModulus_ne_zero P) (Ideal.Quotient.mk _ h*x)) =
      finiteSexticRow P hg j v*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j := by
  dsimp only
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i,P i) := Fintype.ofEquiv (Residue (finitePrimeModulus P)) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  rw [tsum_fintype]
  simp_rw [CenteredMomentFirstReduced.principalSexticRow_mul P hcop hg j
    (finitePrimeModulus P) (span_finitePrimeModulus P),
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P),mul_assoc]
  rw [← Finset.mul_sum,canonical_principal_gauss_transform P hcop hg hchar j hj0 hj6,
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)]
  change finiteSexticRow P hg j v*(star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j)=_
  ring

theorem tripleFourier_active {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    tripleFourier a b r ha hb (finitePrimeModulus_ne_zero P) χa χb G h =
      χa (Ideal.Quotient.mk _ (b*r))*χb (Ideal.Quotient.mk _ (a*r))*
        residueGauss a ha χa (Ideal.Quotient.mk _ h)*residueGauss b hb χb (Ideal.Quotient.mk _ h)*
        (finiteSexticRow P hg j (a*b)*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j) := by
  dsimp only
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let := finite_quotient_span (mul_ne_zero hb (finitePrimeModulus_ne_zero P))
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb (finitePrimeModulus_ne_zero P)))
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (b*finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (a*(b*finitePrimeModulus P))) := Fintype.ofFinite _
  unfold tripleFourier tripleResidue
  rw [tsum_fintype,three_factor_mixed_fourier a b (finitePrimeModulus P) ha hb
    (finitePrimeModulus_ne_zero P) har hbr]
  simp only [frequencyReduction_mk]
  have hs := shifted_active_fourier P hcop hg hchar j hj0 hj6 (a*b) h
  dsimp only at hs
  rw [tsum_fintype] at hs
  rw [hs]

theorem tripleFourier_active_norm_le {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    ‖tripleFourier a b r ha hb (finitePrimeModulus_ne_zero P) χa χb G h‖ ≤
      ‖eisEmbedding r‖*‖residueGauss a ha χa (Ideal.Quotient.mk _ h)‖*
        ‖residueGauss b hb χb (Ideal.Quotient.mk _ h)‖ := by
  dsimp only
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  rw [tripleFourier_active P hcop hg hchar j hj0 hj6 a b ha hb har hbr]
  simp only [norm_mul,norm_star,norm_canonicalGaussSum P hcop hg hchar j hj0 hj6]
  have hχa := QuadraticInitialBound.norm_finite_character_le_one χa (Ideal.Quotient.mk _ (b*finitePrimeModulus P))
  have hχb := QuadraticInitialBound.norm_finite_character_le_one χb (Ideal.Quotient.mk _ (a*finitePrimeModulus P))
  have hv := QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j (a*b)
  have hh := QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j h
  calc
    _ ≤ 1*1*‖residueGauss a ha χa (Ideal.Quotient.mk _ h)‖*
      ‖residueGauss b hb χb (Ideal.Quotient.mk _ h)‖*(1*1*‖eisEmbedding (finitePrimeModulus P)‖) := by
        gcongr
    _ = _ := by ring

end SevenEighths.CenteredMomentFirstActiveFourier

end

end OAI

end Source375

/- Original source: OAI/NumberTheory/DirichletL/Moments/MaskedVolume.lean; sha256: b6e64c3b29c9dbb2f0e3db7a0c5634b69b0a7ef6d36f1418ddd7102611f163f2 -/
section Source376
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentMaskedVolume
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open IdealMobiusDivisorSum UniqueFactorizationMonoid QuadraticInitialBound
open CenteredMomentPrimary CenteredMomentMask

theorem masked_primary_ideal_volume_error
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W : 𝓢(ℝ, ℂ)) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Iic b) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let Ψ := primaryIdealCharacter c χ
    let v := (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
      ((∑ r : O ⧸ Ideal.span {c}, primaryResidueValue c χ r) * paperRadialFourier W 0)
    ‖(∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
      (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v‖ ≤
      ((idealDivisors R).card : ℝ) *
        ((∑ r : O ⧸ Ideal.span {c}, ‖primaryResidueValue c χ r‖) * pvControl W) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let Ψ := primaryIdealCharacter c χ
  let v := (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
    ((∑ r : O ⧸ Ideal.span {c}, primaryResidueValue c χ r) * paperRadialFourier W 0)
  let B := (∑ r : O ⧸ Ideal.span {c}, ‖primaryResidueValue c χ r‖) * pvControl W
  let L : ℝ → ℂ := fun Y => ∑' I : Ideal O, Ψ I * W ((Ideal.absNorm I : ℝ) / Y)
  have hB : 0 ≤ B := mul_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (pvControl_nonneg W)
  have hnD (D : Ideal O) (hD : D ∈ idealDivisors R) : 0 < (Ideal.absNorm D : ℝ) := by
    have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hsingle (D : Ideal O) (hD : D ∈ idealDivisors R) :
      ‖L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v‖ ≤ B := by
    have h := primary_ideal_volume_error_all c hc h3 χ W
      (X / Ideal.absNorm D) (div_pos hX (hnD D hD))
    convert h using 1
    congr 1
    dsimp only [v]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    ring
  have hcoef (D : Ideal O) : ‖(moebius D : ℂ) * Ψ D‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_ideal_moebius_le_one D)
      (primaryIdealCharacter_norm_le_one c hc χ D) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have heq :
      (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
        (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v =
      ∑ D ∈ idealDivisors R, ((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v) := by
    rw [masked_plain_ideal_sum R hR Ψ W b X hX hs]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro D _
    simp only [L, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  change ‖_ - (X : ℂ) * _ * v‖ ≤ ((idealDivisors R).card : ℝ) * B
  rw [heq]
  calc
    _ ≤ ∑ D ∈ idealDivisors R, ‖((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v)‖ := norm_sum_le _ _
    _ ≤ ∑ _D ∈ idealDivisors R, B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul (hcoef D) (hsingle D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

end SevenEighths.CenteredMomentMaskedVolume
end

end OAI

end Source376

/- Original source: OAI/NumberTheory/DirichletL/IdealEuler.lean; sha256: 6d266b5758b5e34be713d67cdaccbfdb9686899f20f22e75ad1fe574eb785825 -/
section Source377
namespace OAI

namespace SevenEighths.IdealEuler

open ActualEisensteinCubic UniqueFactorizationMonoid
open CompletedGauss (MulFiber mulFiber_moebius_sum)
open SmoothMobiusCorrection (PrimeIdeal)
open scoped BigOperators Classical

noncomputable section

def normWeight (s : ℂ) : Ideal O →*₀ ℂ where
  toFun := CubicEisenstein.fullIdealWeight s
  map_zero' := by simp [CubicEisenstein.fullIdealWeight]
  map_one' := by simp [CubicEisenstein.fullIdealWeight]
  map_mul' I J := by
    by_cases hI : I = 0
    · simp [CubicEisenstein.fullIdealWeight, hI]
    by_cases hJ : J = 0
    · simp [CubicEisenstein.fullIdealWeight, hJ]
    simp only [CubicEisenstein.fullIdealWeight, hI, hJ, mul_ne_zero hI hJ,
      ite_false, map_mul, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

def weighted (a : Ideal O →*₀ ℂ) (s : ℂ) : Ideal O →*₀ ℂ where
  toFun I := a I * normWeight s I
  map_zero' := by rw [map_zero, map_zero, zero_mul]
  map_one' := by rw [map_one, map_one, one_mul]
  map_mul' I J := by simp only [map_mul]; ring

def series (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ := ∑' I : Ideal O, weighted a s I

def inverseSeries (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ :=
  ∑' I : Ideal O, (moebius I : ℂ) * weighted a s I

theorem weighted_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun I : Ideal O => ‖weighted a s I‖) := by
  apply (CubicEisenstein.fullIdealWeight_summable_norm s hs).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro I
  change ‖a I * CubicEisenstein.fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem weighted_summable (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun I : Ideal O => weighted a s I) :=
  (weighted_summable_norm a ha s hs).of_norm

theorem inverse_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I : Ideal O => ‖(moebius I : ℂ) * weighted a s I‖) := by
  apply (weighted_summable_norm a ha s hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)

theorem series_eq_LSeries (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = LSeries (ShortDraftHeckeBridge.normFiberCoeff a) s :=
  SmoothMobiusCorrection.idealDirichlet_eq_LSeries a ha s hs

theorem inverseSeries_mul_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s * series a s = 1 := by
  let f := weighted a s
  let F : Ideal O × Ideal O → ℂ := fun p => (moebius p.1 : ℂ) * f (p.1 * p.2)
  have hprod := (inverse_summable_norm a ha s hs).mul_norm (weighted_summable_norm a ha s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F, f]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.1) = if B = 1 then 1 else 0 := by
    by_cases hB : B = 0
    · subst B
      have hz (p : MulFiber 0) : F p.1 = 0 := by simp only [F, p.2, map_zero, mul_zero]
      simp only [hz, tsum_zero, zero_ne_one, ite_false]
    · calc
        _ = (∑' p : MulFiber B, (moebius p.1.1 : ℂ)) * f B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.2])
        _ = _ := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with hB1
          · subst B
            simp only [map_one, one_mul]
          · exact zero_mul _
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.1) (∑' p, F p) at hsum
  simp_rw [hfiber] at hsum
  have hFone : (∑' p, F p) = 1 := by simpa using hsum.tsum_eq.symm
  calc
    _ = ∑' p : Ideal O × Ideal O, ((moebius p.1 : ℂ) * f p.1) * f p.2 :=
      tsum_mul_tsum_of_summable_norm (inverse_summable_norm a ha s hs)
        (weighted_summable_norm a ha s hs)
    _ = ∑' p, F p := by
      apply tsum_congr
      intro p
      simp only [F, map_mul]
      ring
    _ = 1 := hFone

theorem series_ne_zero (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : series a s ≠ 0 := by
  intro hz
  have h := inverseSeries_mul_series a ha s hs
  rw [hz, mul_zero] at h
  exact zero_ne_one h

theorem inverseSeries_eq_inv (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s = (series a s)⁻¹ := by
  calc
    _ = (inverseSeries a s * series a s) * (series a s)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (series_ne_zero a ha s hs), mul_one]
    _ = _ := by rw [inverseSeries_mul_series a ha s hs, one_mul]

theorem primeValueHom_eq (f : Ideal O →*₀ ℂ) : CanonicalRowCompletion.primeValueHom f = f := by
  ext I
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
  · change (if I = 0 then 0 else ((normalizedFactors I).map f).prod) = f I
    simp only [hI, ite_false]
    rw [← map_multiset_prod, prod_normalizedFactors_eq hI, normalize_eq]

theorem prime_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun P : PrimeIdeal => ‖weighted a s P.val‖) :=
  (weighted_summable_norm a ha s hs).comp_injective Subtype.val_injective

theorem prime_norm_lt_one (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : ‖weighted a s P.val‖ < 1 := by
  change ‖a P.val * CubicEisenstein.fullIdealWeight s P.val‖ < 1
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false, norm_mul]
  change ‖a P.val‖ * ‖SmoothMobiusCorrection.primeNormPower P s‖ < 1
  rw [SmoothMobiusCorrection.norm_primeNormPower]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (ha P.val)).trans_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by have h := SmoothMobiusCorrection.prime_norm_two_le P
        exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)) (by simpa using neg_neg_of_pos hs)

theorem local_factor_ne_zero (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : 1 - weighted a s P.val ≠ 0 :=
  SmoothMobiusCorrection.one_sub_ne_zero (prime_norm_lt_one a ha s hs P)

theorem inverseSeries_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    inverseSeries a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val) := by
  have h := SmoothMobiusCorrection.mobiusPrimeCoeff_euler (weighted a s)
    (prime_summable_norm a ha s hs)
  simpa only [SmoothMobiusCorrection.mobiusPrimeCoeff, primeValueHom_eq, inverseSeries] using h

theorem euler_hasProd (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹) (series a s) := by
  have hm : Multipliable (fun P : PrimeIdeal => 1 - weighted a s P.val) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (show Summable (fun P : PrimeIdeal => ‖-weighted a s P.val‖) by
        simpa only [norm_neg] using prime_summable_norm a ha s hs)
  have heq : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) = (series a s)⁻¹ :=
    (inverseSeries_euler a ha s hs).symm.trans (inverseSeries_eq_inv a ha s hs)
  have hne : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) ≠ 0 := by
    rw [heq]
    exact inv_ne_zero (series_ne_zero a ha s hs)
  simpa only [heq, inv_inv] using hm.hasProd.inv₀ hne

theorem series_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val)⁻¹ :=
  (euler_hasProd a ha s hs).tprod_eq.symm

def deletePrimes (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) : Ideal O →*₀ ℂ :=
  CanonicalRowCompletion.primeValueHom
    (fun I => if I ∈ S.image Subtype.val then 0 else a I)

theorem deletePrimes_prime (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (P : PrimeIdeal) :
    deletePrimes S a P.val = if P ∈ S then 0 else a P.val := by
  have hmem : P.val ∈ S.image Subtype.val ↔ P ∈ S := by
    constructor
    · intro hP
      obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hP
      exact (Subtype.ext hQP : Q = P) ▸ hQ
    · intro hP
      exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
  change CanonicalRowCompletion.primeValueHom _ P.val = _
  rw [CanonicalRowCompletion.primeValueHom_prime _ _ P.property]
  simp only [hmem]

theorem deletePrimes_norm_le_one (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) : ∀ I, ‖deletePrimes S a I‖ ≤ 1 := by
  apply CanonicalRowCompletion.primeValueHom_norm_le_one
  intro I
  split_ifs
  · simp only [norm_zero, zero_le_one]
  · exact ha I

theorem deletePrimes_apply (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes S a I = if ∀ P ∈ S, ¬P.val ∣ I then a I else 0 := by
  by_cases ho : ∀ P ∈ S, ¬P.val ∣ I
  · rw [ite_eq_left ho]
    by_cases hI : I = 0
    · subst I
      rw [map_zero, map_zero]
    · change (if I = 0 then 0 else
        ((normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J)).prod) = a I
      simp only [hI, ite_false]
      have hmap : (normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J) =
          (normalizedFactors I).map a := by
        apply Multiset.map_congr rfl
        intro J hJ
        have hnot : J ∉ S.image Subtype.val := by
          intro hmem
          obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hmem
          exact ho P hP (dvd_of_mem_normalizedFactors hJ)
        simp only [hnot, ite_false]
      rw [hmap, ← map_multiset_prod, prod_normalizedFactors_eq hI, normalize_eq]
  · simp only [ho, ite_false]
    push Not at ho
    obtain ⟨P, hPS, J, hJ⟩ := ho
    rw [hJ, map_mul, deletePrimes_prime]
    simp only [hPS, ite_true, zero_mul]

theorem deletePrimes_primeSet_apply (M : Ideal O) (hM : M ≠ 0)
    (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes (SmoothMobiusCorrection.primeSet M) a I =
      if IsCoprime I M then a I else 0 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
    exact (ite_self _).symm
  have heq : (∀ P ∈ SmoothMobiusCorrection.primeSet M, ¬P.val ∣ I) ↔ IsCoprime I M := by
    rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff hI hM]
    constructor
    · intro h
      apply Finset.disjoint_left.mpr
      intro P hPI hPM
      have hp : Prime P := IdealMobiusDivisorSum.support_prime hPM
      exact h ⟨P, hp⟩ (SmoothMobiusCorrection.mem_primeSet M ⟨P, hp⟩ |>.mpr hPM)
        (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPI))
    · intro h P hPM hPI
      exact Finset.disjoint_left.mp h
        (Multiset.mem_toFinset.mpr ((mem_normalizedFactors_iff hI).mpr ⟨P.property, hPI⟩))
        ((SmoothMobiusCorrection.mem_primeSet M P).mp hPM)
  simpa only [heq] using deletePrimes_apply (SmoothMobiusCorrection.primeSet M) a I

theorem series_deletePrimes (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    series (deletePrimes S a) s =
      series a s * ∏ P ∈ S, (1 - weighted a s P.val) := by
  have hlocal (P : PrimeIdeal) :
      (1 - weighted (deletePrimes S a) s P.val)⁻¹ =
        (1 - weighted a s P.val)⁻¹ * (if P ∈ S then 1 - weighted a s P.val else 1) := by
    change (1 - deletePrimes S a P.val * normWeight s P.val)⁻¹ = _
    rw [deletePrimes_prime]
    by_cases hP : P ∈ S
    · simp only [hP, ite_true, zero_mul, sub_zero, inv_one]
      exact (inv_mul_cancel₀ (local_factor_ne_zero a ha s (by linarith) P)).symm
    · simp only [hP, ite_false, mul_one]
      rfl
  have hfinite : Multipliable (fun P : PrimeIdeal => if P ∈ S then 1 - weighted a s P.val else 1) := by
    apply multipliable_of_hasFiniteMulSupport
    apply S.finite_toSet.subset
    intro P hP
    by_contra hPS
    change P ∉ S at hPS
    exact hP (by simp only [hPS, ite_false])
  rw [series_euler _ (deletePrimes_norm_le_one S a ha) s hs,
    series_euler a ha s hs]
  simp_rw [hlocal]
  rw [(euler_hasProd a ha s hs).multipliable.tprod_mul hfinite]
  congr 1
  rw [tprod_eq_prod (s := S) (fun P hP => by simp only [hP, ite_false])]
  exact Finset.prod_congr rfl (fun P hP => by simp only [hP, ite_true])

theorem series_of_coprime_mask (M : Ideal O) (hM : M ≠ 0)
    (a b : Ideal O →*₀ ℂ) (hb : ∀ I, ‖b I‖ ≤ 1)
    (hmask : ∀ I, a I = if IsCoprime I M then b I else 0)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = series b s *
      ∏ P ∈ SmoothMobiusCorrection.primeSet M, (1 - weighted b s P.val) := by
  have heq : a = deletePrimes (SmoothMobiusCorrection.primeSet M) b := by
    ext I
    rw [deletePrimes_primeSet_apply M hM, hmask]
  rw [heq]
  exact series_deletePrimes _ b hb s hs

theorem series_ofResidue_source_mask (M K : Ideal O) (hM : M ≠ 0)
    [Finite (O ⧸ K)] (χ : MulChar (O ⧸ M) ℂ) (φ : MulChar (O ⧸ K) ℂ)
    (hχ : IdealCharacter.UnitInvariant M χ) (hφ : IdealCharacter.UnitInvariant K φ)
    (hmask : ∀ x : O, χ (Ideal.Quotient.mk M x) =
      if IsUnit (Ideal.Quotient.mk M x) then φ (Ideal.Quotient.mk K x) else 0)
    (s : ℂ) (hs : 1 < s.re) :
    series (IdealCharacter.ofResidue M χ hχ) s =
      series (IdealCharacter.ofResidue K φ hφ) s *
        ∏ P ∈ SmoothMobiusCorrection.primeSet M,
          (1 - weighted (IdealCharacter.ofResidue K φ hφ) s P.val) :=
  series_of_coprime_mask M hM _ _ (IdealCharacter.norm_ofResidue_le_one K φ hφ)
    (IdealCharacter.ofResidue_source_mask M K χ φ hχ hφ hmask) s hs

theorem exists_primitive_series_associate (M : Ideal O) (hM : M ≠ 0)
    [Finite (O ⧸ M)] (χ : MulChar (O ⧸ M) ℂ) (hχ : IdealCharacter.UnitInvariant M χ) :
    ∃ (K : Ideal O) (φ : MulChar (O ⧸ K) ℂ) (hφ : IdealCharacter.UnitInvariant K φ),
      M ≤ K ∧ K ≠ ⊥ ∧ FiniteFourier.IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      ∀ (s : ℂ), 1 < s.re →
        series (IdealCharacter.ofResidue M χ hχ) s =
          series (IdealCharacter.ofResidue K φ hφ) s *
            ∏ P ∈ SmoothMobiusCorrection.primeSet M,
              (1 - weighted (IdealCharacter.ofResidue K φ hφ) s P.val) := by
  obtain ⟨K, φ, hφ, hMK, hK, hp, hn, hmask, _⟩ :=
    IdealCharacter.exists_primitive_associate M χ hχ
  let : Finite (O ⧸ K) := Finite.of_surjective _ (Ideal.Quotient.factor_surjective hMK)
  refine ⟨K, φ, hφ, hMK, hK, hp, hn, ?_⟩
  intro s hs
  exact series_of_coprime_mask M hM _ _
    (IdealCharacter.norm_ofResidue_le_one K φ hφ) hmask s hs

end

end SevenEighths.IdealEuler

end OAI

end Source377

/- Original source: OAI/NumberTheory/DirichletL/Hecke/Euler.lean; sha256: 3c2d31189b4eb5efa3417c73fa7390c7add3350143df5e98fd951a375631558d -/
section Source378
namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

private instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem idealCoeff_norm_le_one (χ : Character) (I : Ideal O) : ‖idealCoeff χ I‖ ≤ 1 := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact IdealCharacter.norm_ofResidue_le_one χ.modulus χ.residue χ.unit_trivial I

theorem idealTerm_eq_weighted (χ : Character) (s : ℂ) (I : Ideal O) :
    idealTerm χ s I = IdealEuler.weighted (idealCoeff χ) s I := by
  change idealCoeff χ I / (Ideal.absNorm I : ℂ)^s =
    idealCoeff χ I * CubicEisenstein.fullIdealWeight s I
  by_cases hI : I = 0
  · rw [hI, map_zero]
    simp
  · simp only [CubicEisenstein.fullIdealWeight, hI, ite_false,
      Complex.cpow_neg, div_eq_mul_inv]

theorem LFunction_eq_series (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = IdealEuler.series (idealCoeff χ) s := by
  rw [LFunction_eq_ideal_tsum χ hs]
  exact tsum_congr (idealTerm_eq_weighted χ s)

theorem LFunction_ne_zero_of_one_lt_re (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s ≠ 0 := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.series_ne_zero (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs

theorem inverseSeries_mul_LFunction (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    IdealEuler.inverseSeries (idealCoeff χ) s * LFunction χ s = 1 := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.inverseSeries_mul_series (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs

theorem LFunction_eq_normFiber_LSeries (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LSeries (ShortDraftHeckeBridge.normFiberCoeff (idealCoeff χ)) s := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.series_eq_LSeries (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs

end SevenEighths.HeckeFamily

end

end OAI

end Source378

/- Original source: OAI/NumberTheory/DirichletL/Hecke/ZeroSupremum.lean; sha256: 3b3ca749fb669e5a278a5d956a61eec73bab919e0369f7d46d2abae2e0f0011e -/
section Source379
namespace OAI

noncomputable section
namespace SevenEighths.HeckeZeroSupremum
open HeckeFamily

def zeroRealParts : Set ℝ :=
  {x | ∃ (χ : Character) (s : ℂ), 0 < s.re ∧
    (s ≠ 1 ∨ χ.residue ≠ 1) ∧ LFunction χ s = 0 ∧ s.re = x}

def zeroSetWithSentinel : Set ℝ := insert (1 / 2) zeroRealParts

def beta : ℝ := sSup zeroSetWithSentinel

theorem zeroRealParts_le_one {x : ℝ} (hx : x ∈ zeroRealParts) : x ≤ 1 := by
  obtain ⟨χ, s, _, _, hz, rfl⟩ := hx
  by_contra h
  exact LFunction_ne_zero_of_one_lt_re χ (lt_of_not_ge h) hz

theorem zeroSet_bddAbove : BddAbove zeroSetWithSentinel := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zeroSet_nonempty : zeroSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem half_le_beta : (1 / 2 : ℝ) ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert _ _)

theorem beta_le_one : beta ≤ 1 := by
  apply csSup_le zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zero_re_le_beta (χ : Character) {s : ℂ} (hs : 0 < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    s.re ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert_of_mem _ ⟨χ, s, hs, hpole, hz, rfl⟩)

theorem LFunction_ne_zero_of_beta_lt (χ : Character) {s : ℂ}
    (hs : beta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 := by
  intro hz
  have hpos : 0 < s.re := lt_trans (by linarith [half_le_beta]) hs
  exact (not_lt_of_ge (zero_re_le_beta χ hpos hpole hz)) hs

theorem exists_zero_near_beta {ε : ℝ} (hε : 0 < ε)
    (hεsmall : (1 / 2 : ℝ) ≤ beta - ε) :
    ∃ (χ : Character) (s : ℂ), 0 < s.re ∧
      (s ≠ 1 ∨ χ.residue ≠ 1) ∧ LFunction χ s = 0 ∧ beta - ε < s.re := by
  obtain ⟨x, hx, hlt⟩ := Supremum.exists_gt_supremum_sub_of_insert
    zeroSet_bddAbove hε hεsmall
  obtain ⟨χ, s, hpos, hpole, hz, rfl⟩ := hx
  exact ⟨χ, s, hpos, hpole, hz, hlt⟩

theorem beta_le_seven_eighths_of_uniform_margin
    (hbound : 7 / 8 < beta →
      ∃ ω σ : ℝ, 0 < ω ∧ ω < beta - 7 / 8 ∧ 0 < σ ∧
        ∀ (χ : Character) (s : ℂ), 0 < s.re →
          (s ≠ 1 ∨ χ.residue ≠ 1) → LFunction χ s = 0 →
            s.re ≤ beta - Supremum.continuationMargin beta ω σ) :
    beta ≤ 7 / 8 := by
  apply Supremum.seven_eighths_of_uniform_margin_with_sentinel zeroSet_bddAbove
  intro hbeta
  obtain ⟨ω, σ, hω, hωb, hσ, hzeros⟩ := hbound hbeta
  refine ⟨ω, σ, hω, hωb, hσ, ?_⟩
  rintro x ⟨χ, s, hpos, hpole, hz, rfl⟩
  exact hzeros χ s hpos hpole hz

end SevenEighths.HeckeZeroSupremum

end

end OAI

end Source379

/- Original source: OAI/NumberTheory/DirichletL/Hecke/Reciprocal.lean; sha256: d243f1e44bb2fcec20d209300980172dcaf2f5a09e31c45dcb761343b9c9e89b -/
section Source380
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeReciprocal
open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem coefficients_sum_ne_zero_of_principal (χ : Character) (hχ : χ.residue = 1) :
    (∑ a, coefficients χ a) ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  let e := Equiv.prodCongr (finCastEquiv χ.period) (finCastEquiv χ.period)
  have heq : (∑ a, coefficients χ a) =
      (Nat.card (coordinateQuotientHom χ).ker : ℂ) *
        (Fintype.card (O ⧸ χ.modulus)ˣ : ℂ) := by
    calc
      _ = ∑ a, χ.residue (coordinateQuotientHom χ (e a)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact coefficients_eq_quotient_character χ a
      _ = ∑ a : ZMod χ.period × ZMod χ.period,
          χ.residue (coordinateQuotientHom χ a) :=
        e.bijective.sum_comp (fun a => χ.residue (coordinateQuotientHom χ a))
      _ = _ := by
        rw [sum_comp_additiveHom _ (coordinateQuotientHom_surjective χ), hχ,
          MulChar.sum_one_eq_card_units]
  rw [heq]
  apply mul_ne_zero
  · exact_mod_cast (Nat.card_pos (α := (coordinateQuotientHom χ).ker)).ne'
  · exact_mod_cast (Fintype.card_pos (α := (O ⧸ χ.modulus)ˣ)).ne'

theorem dualScalar_ne_zero (N : ℕ) [NeZero N] : HeckeTheta.dualScalar N ≠ 0 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  unfold HeckeTheta.dualScalar
  apply mul_ne_zero <;> apply Complex.ofReal_ne_zero.mpr
  · exact (Real.rpow_pos_of_pos (sq_pos_of_pos hN) _).ne'
  · exact (Real.rpow_pos_of_pos (mul_pos (by norm_num) (sq_pos_of_pos hN)) _).ne'

theorem principal_dual_constant_ne_zero (χ : Character) (hχ : χ.residue = 1) :
    (HeckeTheta.pair (coefficients χ)).g₀ ≠ 0 := by
  rw [HeckeTheta.pair_g₀]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (dualScalar_ne_zero χ.period))
    (coefficients_sum_ne_zero_of_principal χ hχ)

def regularizedL (χ : Character) (s : ℂ) : ℂ :=
  HeckeTheta.regularizedLatticeL (coefficients χ) s / 6

theorem regularizedL_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    regularizedL χ s = (s - 1) * LFunction χ s := by
  unfold regularizedL LFunction continuedLattice
  rw [HeckeTheta.regularizedLatticeL_eq _ h0 h1]
  ring

theorem regularizedL_at_one (χ : Character) :
    regularizedL χ 1 = (Real.pi : ℂ) * (HeckeTheta.pair (coefficients χ)).g₀ / 6 := by
  simp [regularizedL, HeckeTheta.regularizedLatticeL, HeckeTheta.regularizedCompleted]

theorem regularizedL_ne_zero_at_one (χ : Character) (hχ : χ.residue = 1) :
    regularizedL χ 1 ≠ 0 := by
  rw [regularizedL_at_one]
  exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (principal_dual_constant_ne_zero χ hχ)) (by norm_num)

theorem regularizedL_differentiableAt (χ : Character) {s : ℂ} (h0 : s ≠ 0) :
    DifferentiableAt ℂ (regularizedL χ) s :=
  (HeckeTheta.regularizedLatticeL_differentiableAt _ h0).div_const 6

theorem regularizedL_ne_zero (χ : Character) (hχ : χ.residue = 1) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : regularizedL χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    exact regularizedL_ne_zero_at_one χ hχ
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  rw [regularizedL_eq χ h0 h1]
  exact mul_ne_zero (sub_ne_zero.mpr h1)
    (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inl h1))

def reciprocal (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then (s - 1) / regularizedL χ s else (LFunction χ s)⁻¹

theorem reciprocal_eq_inv (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    reciprocal χ s = (LFunction χ s)⁻¹ := by
  unfold reciprocal
  split_ifs
  · rw [regularizedL_eq χ h0 h1, div_mul_eq_div_div,
      div_self (sub_ne_zero.mpr h1), one_div]
  · rfl

theorem reciprocal_principal_one (χ : Character) (hχ : χ.residue = 1) :
    reciprocal χ 1 = 0 := by simp [reciprocal, hχ]

theorem reciprocal_differentiableAt (χ : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : DifferentiableAt ℂ (reciprocal χ) s := by
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  by_cases hχ : χ.residue = 1
  · have heq : reciprocal χ = fun z => (z - 1) / regularizedL χ z := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (differentiableAt_id.sub_const 1).div
      (regularizedL_differentiableAt χ h0) (regularizedL_ne_zero χ hχ hs)
  · have heq : reciprocal χ = fun z => (LFunction χ z)⁻¹ := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (LFunction_differentiableAt χ h0 (Or.inr hχ)).inv
      (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inr hχ))

end SevenEighths.HeckeReciprocal

end

end OAI

end Source380

/- Original source: OAI/NumberTheory/DirichletL/EulerFactors.lean; sha256: 50f6f2d96896496111c5e21f79dc8ba20ddd0dfba0421da1a83650361f239572 -/
section Source381
namespace OAI

namespace SevenEighths.EulerFactors

noncomputable section

def factor (N : ℝ) (a s : ℂ) : ℂ := 1 - a * (N : ℂ) ^ (-s)

theorem norm_term_lt_one {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : ‖a * (N : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N),
    Complex.neg_re]
  calc
    ‖a‖ * N ^ (-s.re) ≤ 1 * N ^ (-s.re) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (by linarith) _)
    _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hN (neg_neg_of_pos hs)

theorem factor_ne_zero {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : factor N a s ≠ 0 := by
  intro h
  have heq : a * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hlt := norm_term_lt_one hN ha hs
  rw [heq, norm_one] at hlt
  exact (lt_irrefl _ hlt)

theorem differentiable_factor {N : ℝ} (hN : 0 < N) (a : ℂ) :
    Differentiable ℂ (factor N a) := by
  exact (differentiable_const (1 : ℂ)).sub ((differentiable_const a).mul
    (differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))))

def deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ) (a : ι → ℂ)
    (s : ℂ) : ℂ := ∏ p ∈ S, factor (N p) (a p) s

theorem deletedProduct_ne_zero {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : deletedProduct S N a s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact factor_ne_zero (hN p hp) (ha p hp) hs

theorem differentiable_deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 0 < N p) :
    Differentiable ℂ (deletedProduct S N a) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Differentiable ℂ (fun _ : ℂ => (1 : ℂ))
    exact differentiable_const _
  | @insert p S hp ih =>
    have hpN := hN p (Finset.mem_insert_self p S)
    have hSN : ∀ q ∈ S, 0 < N q := fun q hq => hN q (Finset.mem_insert_of_mem hq)
    have heq : deletedProduct (insert p S) N a =
        fun s => factor (N p) (a p) s * deletedProduct S N a s := by
      funext s
      simp only [deletedProduct, Finset.prod_insert hp]
    rw [heq]
    exact (differentiable_factor hpN (a p)).mul (ih hSN)

theorem deleted_eq_zero_iff {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {L Ldeleted : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hidentity : Ldeleted s = deletedProduct S N a s * L s) :
    Ldeleted s = 0 ↔ L s = 0 := by
  rw [hidentity, mul_eq_zero]
  exact or_iff_right (deletedProduct_ne_zero S N a hN ha hs)

end

end SevenEighths.EulerFactors

end OAI

end Source381

/- Original source: OAI/NumberTheory/DirichletL/Hecke/FiniteDeletion.lean; sha256: dfb26a8cb221175f3c7cef4e854e21c467b040ca903bde1ff75bca00ff7eeee1 -/
section Source382
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFiniteDeletion
open HeckeFamily HeckeReciprocal

def factors (M : Ideal O) (ψ : Character) : ℂ → ℂ :=
  EulerFactors.deletedProduct (SmoothMobiusCorrection.primeSet M)
    (fun P => Ideal.absNorm P.val) (fun P => idealCoeff ψ P.val)

theorem factors_eq (M : Ideal O) (ψ : Character) (s : ℂ) :
    factors M ψ s = ∏ P ∈ SmoothMobiusCorrection.primeSet M,
      (1 - IdealEuler.weighted (idealCoeff ψ) s P.val) := by
  apply Finset.prod_congr rfl
  intro P _
  simp only [EulerFactors.factor, IdealEuler.weighted, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, IdealEuler.normWeight, CubicEisenstein.fullIdealWeight,
    P.property.ne_zero, ite_false, Complex.ofReal_natCast]

theorem factors_differentiable (M : Ideal O) (ψ : Character) :
    Differentiable ℂ (factors M ψ) := by
  apply EulerFactors.differentiable_deletedProduct
  intro P _
  have h := SmoothMobiusCorrection.prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

theorem factors_ne_zero (M : Ideal O) (ψ : Character) {s : ℂ} (hs : 0 < s.re) :
    factors M ψ s ≠ 0 := by
  apply EulerFactors.deletedProduct_ne_zero _ _ _ _ _ hs
  · intro P _
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)
  · intro P _
    exact idealCoeff_norm_le_one ψ P.val

theorem LFunction_eq_of_mask_right (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  rw [LFunction_eq_series χ hs, LFunction_eq_series ψ hs, factors_eq]
  exact IdealEuler.series_of_coprime_mask χ.modulus χ.modulus_ne_bot
    _ _ (idealCoeff_norm_le_one ψ) hmask s hs

theorem regularizedL_analytic (χ : Character) :
    AnalyticOnNhd ℂ (regularizedL χ) {s : ℂ | 0 < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
  intro s hs
  exact (regularizedL_differentiableAt χ (by intro h; simp [h] at hs)).differentiableWithinAt

theorem regularizedL_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    regularizedL χ s = regularizedL ψ s * factors χ.modulus ψ s := by
  have hf : AnalyticOnNhd ℂ (factors χ.modulus ψ) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    exact (factors_differentiable _ _).differentiableOn
  apply Eq.symm
  apply Continuation.product_identity_on_halfPlane 0 1
    (regularizedL ψ) (factors χ.modulus ψ) (regularizedL χ)
    (regularizedL_analytic ψ) hf (regularizedL_analytic χ) _ hs
  intro z hz
  have hz' : 1 < z.re := by simpa using hz
  have h0 : z ≠ 0 := by intro h; norm_num [h] at hz'
  have h1 : z ≠ 1 := by intro h; norm_num [h] at hz'
  rw [regularizedL_eq χ h0 h1, regularizedL_eq ψ h0 h1,
    LFunction_eq_of_mask_right χ ψ hmask hz']
  ring

theorem LFunction_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h := regularizedL_eq_of_mask χ ψ hmask hs
  rw [regularizedL_eq χ h0 h1, regularizedL_eq ψ h0 h1, mul_assoc] at h
  exact mul_left_cancel₀ (sub_ne_zero.mpr h1) h

theorem regularizedL_one_ne_zero_iff (χ : Character) :
    regularizedL χ 1 ≠ 0 ↔ χ.residue = 1 := by
  constructor
  · intro h
    by_contra hχ
    rw [regularizedL_at_one,
      HeckeTheta.pair_g₀_eq_zero _ (HeckeCharacterAnalytic.coefficients_sum_eq_zero χ hχ),
      mul_zero, zero_div] at h
    exact h rfl
  · exact regularizedL_ne_zero_at_one χ

theorem principal_iff_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0) :
    χ.residue = 1 ↔ ψ.residue = 1 := by
  rw [← regularizedL_one_ne_zero_iff χ, ← regularizedL_one_ne_zero_iff ψ,
    regularizedL_eq_of_mask χ ψ hmask (by norm_num : 0 < (1 : ℂ).re),
    mul_ne_zero_iff, and_iff_left (factors_ne_zero χ.modulus ψ (by norm_num))]

theorem LFunction_eq_of_mask_nonprincipal (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have ha (η : Character) (hη : η.residue ≠ 1) :
      AnalyticOnNhd ℂ (LFunction η) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    intro z hz
    exact (LFunction_differentiableAt η (by intro h; simp [h] at hz)
      (Or.inr hη)).differentiableWithinAt
  have hf : AnalyticOnNhd ℂ (factors χ.modulus ψ) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    exact (factors_differentiable _ _).differentiableOn
  apply Eq.symm
  apply Continuation.product_identity_on_halfPlane 0 1
    (LFunction ψ) (factors χ.modulus ψ) (LFunction χ) (ha ψ hψ) hf (ha χ hχ) _ hs
  intro z hz
  exact (LFunction_eq_of_mask_right χ ψ hmask (by simpa using hz)).symm

theorem LFunction_eq_of_mask_nonpole (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  rcases hpole with h1 | hχ
  · exact LFunction_eq_of_mask χ ψ hmask hs h1
  · exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs

theorem exists_primitive_same_zeros (χ : Character) :
    ∃ ψ : Character, χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
      ∀ s : ℂ, 0 < s.re → s ≠ 1 →
        (LFunction χ s = 0 ↔ LFunction ψ s = 0) := by
  obtain ⟨ψ, hmod, hp, hnorm, hmask⟩ := exists_primitive_character χ
  refine ⟨ψ, hmod, hp, hnorm, ?_⟩
  intro s hs h1
  rw [LFunction_eq_of_mask χ ψ hmask hs h1, mul_eq_zero]
  exact or_iff_left (factors_ne_zero χ.modulus ψ hs)

theorem exists_primitive_zero (χ : Character) {s : ℂ}
    (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (s ≠ 1 ∨ ψ.residue ≠ 1) ∧ LFunction ψ s = 0 := by
  obtain ⟨ψ, _, hp, _, hmask⟩ := exists_primitive_character χ
  refine ⟨ψ, hp, ?_, ?_⟩
  · rcases hpole with h1 | hχ
    · exact Or.inl h1
    · exact Or.inr (fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h))
  · rw [LFunction_eq_of_mask_nonpole χ ψ hmask hs hpole, mul_eq_zero] at hz
    exact hz.resolve_right (factors_ne_zero χ.modulus ψ hs)

end SevenEighths.HeckeFiniteDeletion

end

end OAI

end Source382

/- Original source: OAI/NumberTheory/DirichletL/Hecke/UnitRows.lean; sha256: c60223ea086c923299f92e63cd46d668823b23db61dab989baf7871743d322bf -/
section Source383
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeUnitRows
open HeckeFamily CanonicalUnitEuler CanonicalRowCompletion
open ActualEisensteinCubic CubicRamified ConcreteTraceCRT
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
local notation "ω" => HeckeFamily.omega
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem seven_coprime_thirty_six : IsCoprime sevenPrime (36 : O) := by
  have hω : ω ^ 2 = -ω - 1 := by
    simpa [HeckeFamily.omega] using IsCyclotomicExtension.Rat.Three.eta_sq
      (IsCyclotomicExtension.zeta_spec 3 ℚ HeckeFamily.K)
  change IsCoprime (1 + 3 * ω) (36 : O)
  refine ⟨31 * (-2 - 3 * ω), -6, ?_⟩
  linear_combination -279 * hω

theorem supported_unit_thirty_six (n : O) (hn : Supported (Ideal.span {n})) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(36 : O)}) n) := by
  have hs := (supported_span_iff n).mp hn
  have hneg2 : IsCoprime (-2 : O) n := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using hs.2)
  have h2 : IsCoprime n (2 : O) := (hneg2.of_isCoprime_of_dvd_left ⟨-1, by ring⟩).symm
  have h9 := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n hs.1).symm
  rw [IdealCharacter.isUnit_mk_iff_isCoprime, Ideal.isCoprime_span_singleton_iff]
  convert (h2.pow_right : IsCoprime n ((2 : O)^2)).mul_right h9 using 1 ; norm_num

theorem unitSupplement_unit (u v : Oˣ) : unitSupplement u (v : O) = 1 := by
  have hspan : (Ideal.span {(v : O)} : Ideal O) = 1 := by
    simpa only [Ideal.one_eq_top] using Ideal.span_singleton_eq_top.mpr v.isUnit
  have hs : Supported (1 : Ideal O) := ⟨one_ne_zero, by
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact False.elim (Multiset.notMem_zero P hP)⟩
  change (if Supported (Ideal.span {(v : O)}) then idealRowHom (u : O) (Ideal.span {(v : O)}) else 0) = 1
  rw [hspan, ite_eq_left hs, map_one]

private theorem unitSupplement_factorsModulo (u : Oˣ) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(36 : O)}) (unitSupplement u) :=
  unitSupplement_periodic u

def character (u : Oˣ) : Character :=
  HeckeRowClosure.rowCharacter (Ideal.span {(36 : O)})
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)) (unitSupplement u)
    (unitSupplement_factorsModulo u) (unitSupplement_unit u)

theorem elementCoeff_character (u : Oˣ) (n : O) :
    elementCoeff (character u) n = unitSupplement u n := by
  rw [character, HeckeRowClosure.elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · change 0 = if Supported (Ideal.span {n}) then _ else 0
    rw [ite_eq_right (fun hs => hn (supported_unit_thirty_six n hs))]

theorem seven_supported : Supported (Ideal.span {sevenPrime}) := by
  rw [supported_span_iff]
  constructor
  · intro h
    have hd : λ₀ ∣ (36 : O) :=
      ((dvd_pow_self λ₀ (by decide : (2 : ℕ) ≠ 0)).trans lambda_sq_dvd_three).trans ⟨12, by norm_num⟩
    exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit
      (seven_coprime_thirty_six.isUnit_of_dvd' h hd)
  · intro h
    have hu := seven_coprime_thirty_six.isUnit_of_dvd' h (show (2 : O) ∣ 36 from ⟨18, by norm_num⟩)
    exact negative_two_prime.not_isUnit hu.neg

theorem unitSupplement_seven (u : Oˣ) :
    unitSupplement u sevenPrime = eisEmbedding (u : O) := by
  change (if Supported (Ideal.span {sevenPrime}) then idealRowHom (u : O) (Ideal.span {sevenPrime}) else 0) = _
  rw [ite_eq_left seven_supported,
    idealRowHom_unit_norm u _ seven_supported.1
      (supported_factors_good _ seven_supported)]
  change eisEmbedding ((u : O) ^ ((Ideal.absNorm sevenIdeal - 1) / 6)) = _
  rw [sevenIdeal_norm]
  norm_num

theorem character_nonprincipal (u : Oˣ) (hu : u ≠ 1) :
    (character u).residue ≠ 1 := by
  have hv : elementCoeff (character u) sevenPrime = eisEmbedding (u : O) := by
    rw [elementCoeff_character, unitSupplement_seven]
  have hv0 : elementCoeff (character u) sevenPrime ≠ 0 :=
    hv ▸ (u.isUnit.map eisEmbedding).ne_zero
  intro h
  have hunit := MulChar.apply_ne_zero_iff.mp hv0
  have hv1 : elementCoeff (character u) sevenPrime = 1 := by
    change (character u).residue _ = 1
    rw [h, MulChar.one_apply hunit]
  apply hu
  apply Units.ext
  apply eisEmbedding_injective
  simpa only [Units.val_one, map_one] using hv.symm.trans hv1

theorem masked_character_nonprincipal (u : Oˣ) (hu : u ≠ 1) (χ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff (character u) I else 0) :
    χ.residue ≠ 1 := by
  intro h
  exact character_nonprincipal u hu ((HeckeFiniteDeletion.principal_iff_of_mask χ (character u) hmask).mp h)

end SevenEighths.HeckeUnitRows

end

end OAI

end Source383

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalPair.lean; sha256: fd3d1272f43eabb4c8e3f5d33d8dc2ec52798948da3eee8d27f75fdb665c93a7 -/
section Source384
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentExceptionalPair
open HeckeFamily CenteredExceptionalProfile CenteredMomentChildRows CenteredMomentFixedRay
open CanonicalRowCompletion CanonicalQuadraticSieve RayFourExpansion
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem idealCoeff_ne_zero_iff (χ : Character) (I : Ideal O) :
    idealCoeff χ I ≠ 0 ↔ I ≠ ⊥ ∧ IsCoprime I χ.modulus := by
  change (if I = ⊥ then 0 else χ.residue
    (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator I))) ≠ 0 ↔ _
  by_cases hI : I = ⊥
  · simp only [hI,ite_true,ne_eq,not_true_eq_false,false_and]
  · rw [ite_eq_right hI]
    have he : χ.residue (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator I)) ≠ 0 ↔
        IsUnit (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator I)) := MulChar.apply_ne_zero_iff
    rw [IdealCharacter.isUnit_mk_iff_isCoprime,Ideal.span_singleton_generator] at he
    exact he.trans (and_iff_right hI).symm

theorem fixed_primitive_product (χ ψ τ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hψ : Q ≤ ψ.modulus) (hτ : Q ≤ τ.modulus) :
    ∃ ρ : Character, FiniteFourier.IsPrimitiveOnIdeals ρ.residue ∧
      Q ≤ ρ.modulus ∧ InducedBy (χ.product τ) ρ := by
  obtain ⟨ρ,hmod,hprim,hnorm,hmask⟩ := exists_primitive_product_character ψ τ
  refine ⟨ρ,hprim,(le_inf hψ hτ).trans hmod,?_⟩
  intro I
  by_cases hI : I = 0
  · simp only [hI,idealCoeff_zero,ite_self]
  by_cases hc : IsCoprime I (χ.product τ).modulus
  · have hn := (idealCoeff_ne_zero_iff (χ.product τ) I).mpr ⟨hI,hc⟩
    rw [idealCoeff_product] at hn
    have hχ := (idealCoeff_ne_zero_iff χ I).mp (left_ne_zero_of_mul hn) |>.2
    have he : idealCoeff χ I = idealCoeff ψ I := by rw [h I,ite_eq_left hχ]
    have hnψ : idealCoeff (ψ.product τ) I ≠ 0 := by
      rw [idealCoeff_product,← he]
      exact hn
    have hcψ := (idealCoeff_ne_zero_iff (ψ.product τ) I).mp hnψ |>.2
    change IsCoprime I (ψ.modulus ⊓ τ.modulus) at hcψ
    rw [ite_eq_left hc,idealCoeff_product,he,hmask I,ite_eq_left hcψ]
  · have hz : idealCoeff (χ.product τ) I = 0 := by
      by_contra hn
      exact hc ((idealCoeff_ne_zero_iff (χ.product τ) I).mp hn).2
    rw [hz,ite_eq_right hc]

theorem fixedInducingRow_of_product (η₁ η₂ τ : Character) (Q : Ideal O)
    (m A z₁ z₂ : O) (hτ : Q ≤ τ.modulus)
    (he : ∀ n, rowTwist (HeckeRowClosure.elementHom η₂) m 1 (A*z₂) n =
      rowTwist (HeckeRowClosure.elementHom η₁) m 1 (A*z₁) n * elementCoeff τ n)
    (hx : FixedInducingRow η₁ Q m A z₁) : FixedInducingRow η₂ Q m A z₂ := by
  obtain ⟨χ,ψ,hprim,hind,hQ,hrow⟩ := hx
  obtain ⟨ρ,hρ,hQρ,hindρ⟩ := fixed_primitive_product χ ψ τ hind Q hQ hτ
  refine ⟨χ.product τ,ρ,hρ,hindρ,hQρ,?_⟩
  intro n
  rw [elementCoeff_product,hrow n,he n]

def rayRatio (χ ξ : RayCharacter) : Character :=
  (primaryRayCharacter χ).inverse.product (primaryRayCharacter ξ)

theorem childCharacter_ratio (η : Character) (χ ξ : RayCharacter) (n : O) :
    elementCoeff (childCharacter η ξ) n =
      elementCoeff (childCharacter η χ) n * elementCoeff (rayRatio χ ξ) n := by
  simp only [childCharacter,rayRatio,elementCoeff_product,elementCoeff_inverse]
  by_cases hn : IsUnit (Ideal.Quotient.mk (Ideal.span {(12 : O)}) n)
  · have hχ : elementCoeff (primaryRayCharacter χ) n ≠ 0 :=
      MulChar.apply_ne_zero_iff.mpr hn
    field_simp
  · have hz (ψ : RayCharacter) : elementCoeff (primaryRayCharacter ψ) n = 0 :=
      MulChar.map_nonunit _ hn
    rw [hz χ,hz ξ]
    ring

def reflectionRatio (χ ξ : RayCharacter) : Character :=
  (rayRatio χ ξ).product (HeckeUnitRows.character (-1 : Oˣ))

theorem reflectionRatio_modulus (χ ξ : RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72 : O)}) : Q ≤ (reflectionRatio χ ξ).modulus := by
  change Q ≤ ((Ideal.span {(12 : O)}) ⊓ (Ideal.span {(12 : O)})) ⊓ Ideal.span {(36 : O)}
  refine le_inf (le_inf ?_ ?_) ?_
  · exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨6,by norm_num⟩)
  · exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨6,by norm_num⟩)
  · exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨2,by norm_num⟩)

end SevenEighths.CenteredMomentExceptionalPair

end

end OAI

end Source384

/- Original source: OAI/NumberTheory/DirichletL/Moments/HeckeVolume.lean; sha256: df9586c81da96e8b8f7c3eed562b2c437ac77e270ef6acb533bc862f494617a8 -/
section Source385
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentHeckeVolume
open HeckeFamily CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentPrimary CanonicalQuadraticSieve QuadraticInitialBound
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentMask
open PrimaryIdealUnitReindex (GoodIdeal)
open CubicEisenstein (PrimaryLower primaryLowerIdealEquiv)
local notation "O" => ActualEisensteinCubic.O

def primaryCoefficient (ψ : Character) : Ideal O →* ℂ where
  toFun I := if primaryGenerator I=0 then 0 else idealCoeff ψ I
  map_one' := by simp only [primaryGenerator_one,one_ne_zero,ite_false,map_one]
  map_mul' := by
    intro I J
    simp only [primaryGenerator_mul,map_mul]
    by_cases hI : primaryGenerator I=0 <;> by_cases hJ : primaryGenerator J=0 <;>
      simp only [hI,hJ,mul_eq_zero,or_false,ite_true,ite_false,zero_mul,mul_zero]

theorem primaryCoefficient_good (ψ : Character) (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    primaryCoefficient ψ I = elementCoeff ψ (primaryGenerator I) := by
  change (if primaryGenerator I=0 then 0 else idealCoeff ψ I)=_
  rw [ite_eq_right hI]
  conv_lhs => rw [← (primaryGenerator_spec I hI).1,idealCoeff_span ψ hI]

theorem primaryCoefficient_norm (ψ : Character) (I : Ideal O) : ‖primaryCoefficient ψ I‖ ≤ 1 := by
  change ‖if primaryGenerator I=0 then 0 else idealCoeff ψ I‖ ≤ 1
  split_ifs
  · simp only [norm_zero,zero_le_one]
  · exact idealCoeff_norm_le_one ψ I

def periodicValue (c : O) (ψ : Character) (r : O ⧸ Ideal.span {c}) : ℂ :=
  if (3:O) ∣ Quotient.out r-1 then elementCoeff ψ (Quotient.out r) else 0

theorem periodicValue_mk (c : O) (h3 : (3:O) ∣ c) (ψ : Character)
    (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus) (x : O) :
    periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) x) =
      if (3:O) ∣ x-1 then elementCoeff ψ x else 0 := by
  have hc : c ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)-x :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk _ x)))
  have hd := h3.trans hc
  have hprimary : (3:O) ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)-1 ↔ (3:O) ∣ x-1 := by
    constructor
    · intro h; convert dvd_sub h hd using 1 ; ring
    · intro h; convert dvd_add hd h using 1 ; ring
  have hres : Ideal.Quotient.mk ψ.modulus (Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)) =
      Ideal.Quotient.mk ψ.modulus x :=
    Ideal.Quotient.eq.mpr (hmod (Ideal.mem_span_singleton.mpr hc))
  simp only [periodicValue,hprimary,elementCoeff,hres]

theorem periodicValue_norm (c : O) (ψ : Character) (r : O ⧸ Ideal.span {c}) :
    ‖periodicValue c ψ r‖ ≤ 1 := by
  let : Finite (O ⧸ ψ.modulus) := Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  let : Fintype (O ⧸ ψ.modulus) := Fintype.ofFinite _
  unfold periodicValue
  split_ifs
  · exact norm_finite_character_le_one ψ.residue _
  · simp only [norm_zero,zero_le_one]

theorem lattice_eq_ideal_sum (c : O) (h3 : (3:O) ∣ c) (ψ : Character)
    (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus) (W : ℝ → ℂ) (X : ℝ) :
    (∑' z : O, periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖eisEmbedding z‖^2/X)) =
      ∑' I : Ideal O, primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X) := by
  let f : O → ℂ := fun z => elementCoeff ψ z*W (‖eisEmbedding z‖^2/X)
  have hleft : (∑' z : O, periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖eisEmbedding z‖^2/X)) =
      ∑' z : PrimaryLower, f z.val := by
    calc
      _ = ∑' z : O, ({z : O | (3:O) ∣ z-1} : Set O).indicator f z := by
        apply tsum_congr
        intro z
        rw [periodicValue_mk c h3 ψ hmod z]
        simp only [Set.indicator_apply,Set.mem_ofPred_eq,f]
        split_ifs <;> simp only [zero_mul]
      _ = _ := (tsum_subtype {z : O | (3:O) ∣ z-1} f).symm
  have hideal : (∑' I : GoodIdeal, primaryCoefficient ψ I.val*W ((Ideal.absNorm I.val:ℝ)/X)) =
      ∑' I : Ideal O, primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X) := by
    apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | primaryGenerator I ≠ 0})
      (f := fun I : Ideal O => primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X))
    intro I hI
    change primaryGenerator I ≠ 0
    intro hz
    apply hI
    simp only [primaryCoefficient,MonoidHom.coe_mk,OneHom.coe_mk,hz,ite_true,zero_mul]
  rw [hleft,← hideal,← primaryLowerIdealEquiv.symm.tsum_eq]
  apply tsum_congr
  intro I
  change elementCoeff ψ (primaryGenerator I.val)*W (‖eisEmbedding (primaryGenerator I.val)‖^2/X)=_
  rw [primaryGenerator_norm_sq I.val I.property,primaryCoefficient_good ψ I.val I.property]

theorem fixed_period_volume (c : O) (hc : c ≠ 0) (h3 : (3:O) ∣ c)
    (ψ : Character) (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0 < X) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖(∑' I : Ideal O, primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X)) -
      (X/‖eisEmbedding c‖^2:ℝ) • ((∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r)*paperRadialFourier W 0)‖ ≤
      (Fintype.card (O ⧸ Ideal.span {c}):ℝ)*pvControl W := by
  let := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [← lattice_eq_ideal_sum c h3 ψ hmod W X]
  have h := CenteredMomentLattice.periodic_lattice_volume_error W X hX c hc (periodicValue c ψ)
  exact h.trans (mul_le_mul_of_nonneg_right (by
    calc
      _ ≤ ∑ _r : O ⧸ Ideal.span {c}, (1:ℝ) := Finset.sum_le_sum (fun r hr => periodicValue_norm c ψ r)
      _ = _ := by simp) (pvControl_nonneg W))

theorem masked_hecke_volume
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    (ψ : Character) (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus)
    (R : Ideal O) (hR : R ≠ 0) (W : 𝓢(ℝ, ℂ)) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Iic b) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let Ψ := primaryCoefficient ψ
    let v := (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
      ((∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r) * paperRadialFourier W 0)
    ‖(∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
      (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v‖ ≤
      ((idealDivisors R).card : ℝ) *
        ((Fintype.card (O ⧸ Ideal.span {c}) : ℝ) * pvControl W) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let Ψ := primaryCoefficient ψ
  let v := (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
    ((∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r) * paperRadialFourier W 0)
  let B := (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) * pvControl W
  let L : ℝ → ℂ := fun Y => ∑' I : Ideal O, Ψ I * W ((Ideal.absNorm I : ℝ) / Y)
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) (pvControl_nonneg W)
  have hnD (D : Ideal O) (hD : D ∈ idealDivisors R) : 0 < (Ideal.absNorm D : ℝ) := by
    have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hsingle (D : Ideal O) (hD : D ∈ idealDivisors R) :
      ‖L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v‖ ≤ B := by
    have h := fixed_period_volume c hc h3 ψ hmod W
      (X / Ideal.absNorm D) (div_pos hX (hnD D hD))
    convert h using 1
    congr 1
    dsimp only [v]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    ring
  have hcoef (D : Ideal O) : ‖(moebius D : ℂ) * Ψ D‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_ideal_moebius_le_one D)
      (primaryCoefficient_norm ψ D) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have heq :
      (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
        (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v =
      ∑ D ∈ idealDivisors R, ((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v) := by
    rw [masked_plain_ideal_sum R hR Ψ W b X hX hs]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro D _
    simp only [L, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  change ‖_ - (X : ℂ) * _ * v‖ ≤ ((idealDivisors R).card : ℝ) * B
  rw [heq]
  calc
    _ ≤ ∑ D ∈ idealDivisors R, ‖((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v)‖ := norm_sum_le _ _
    _ ≤ ∑ _D ∈ idealDivisors R, B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul (hcoef D) (hsingle D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

def fixedPeriod (Q : Ideal O) : O := 3*ConcretePrimeRowBridge.idealGenerator Q

theorem fixedPeriod_ne_zero (Q : Ideal O) (hQ : Q ≠ 0) : fixedPeriod Q ≠ 0 :=
  mul_ne_zero (by norm_num) (ConcretePrimeRowBridge.idealGenerator_ne_zero Q hQ)

theorem fixedPeriod_three (Q : Ideal O) : (3:O) ∣ fixedPeriod Q := dvd_mul_right _ _

theorem span_fixedPeriod_le (Q : Ideal O) : (Ideal.span {fixedPeriod Q} : Ideal O) ≤ Q := by
  conv_rhs => rw [← ConcretePrimeRowBridge.span_idealGenerator Q]
  exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)

theorem inducedBy_of_elementCoeff_eq (χ χ' ψ : Character)
    (heq : ∀ n, elementCoeff χ' n=elementCoeff χ n)
    (hind : CenteredExceptionalProfile.InducedBy χ ψ) :
    CenteredExceptionalProfile.InducedBy χ' ψ := by
  have hideal (I : Ideal O) : idealCoeff χ' I=idealCoeff χ I := by
    by_cases hI : I=0
    · simp only [hI,map_zero]
    · conv_lhs => rw [← ConcretePrimeRowBridge.span_idealGenerator I,
        idealCoeff_span χ' (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),heq]
      rw [← idealCoeff_span χ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),
        ConcretePrimeRowBridge.span_idealGenerator]
  intro I
  by_cases hI : I=0
  · simp only [hI,map_zero,ite_self]
  by_cases hc : IsCoprime I χ'.modulus
  · have hn := CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I |>.mpr ⟨hI,hc⟩
    rw [hideal I] at hn
    have hc' := (CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn |>.2
    rw [ite_eq_left hc,hideal I,hind I,ite_eq_left hc']
  · have hz : idealCoeff χ' I=0 := by
      by_contra hn
      exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I).mp hn).2
    rw [ite_eq_right hc,hz]

theorem fixedInducingRow_controlled (η : Character) (Q : Ideal O) (m A₀ z : O)
    (hm : m ≠ 0) (hA : A₀ ≠ 0) (hz : z ≠ 0)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hex : CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z) :
    ∃ χ ψ : Character,
      χ.modulus.absNorm ≤ HeckeRowClosure.rowConductorBound η m 1 (A₀*z) ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      CenteredExceptionalProfile.InducedBy χ ψ ∧ Q ≤ ψ.modulus ∧
      ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A₀*z) n := by
  obtain ⟨χ₀,ψ,hprim,hind,hQ,hrow₀⟩ := hex
  obtain ⟨χ,hbound,hrow⟩ := HeckeRowClosure.exists_row_character_with_conductor
    η m 1 (A₀*z) hm one_ne_zero (mul_ne_zero hA hz) hmLam hm2
  refine ⟨χ,ψ,hbound,hprim,?_,hQ,hrow⟩
  exact inducedBy_of_elementCoeff_eq χ₀ χ ψ (fun n => (hrow n).trans (hrow₀ n).symm) hind

theorem induced_primaryCoefficient (χ ψ : Character)
    (hind : CenteredExceptionalProfile.InducedBy χ ψ) (I : Ideal O) :
    primaryCoefficient χ I =
      (if IsCoprime I χ.modulus then (1:ℂ) else 0)*primaryCoefficient ψ I := by
  change (if primaryGenerator I=0 then 0 else idealCoeff χ I)=
    (if IsCoprime I χ.modulus then (1:ℂ) else 0)*(if primaryGenerator I=0 then 0 else idealCoeff ψ I)
  rw [hind I]
  split_ifs <;> simp only [one_mul,zero_mul]

theorem primaryCoefficient_actual_row (η χ : Character) (m A₀ z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (I : Ideal O) :
    primaryCoefficient χ I=idealCoeff χ I := by
  change (if primaryGenerator I=0 then 0 else idealCoeff χ I)=_
  by_cases hI : I=0
  · simp only [hI,primaryGenerator_zero,map_zero,ite_self]
  by_cases hg : primaryGenerator I=0
  · rw [ite_eq_left hg]
    let n := ConcretePrimeRowBridge.idealGenerator I
    have hn : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
    have hs : Ideal.span {n}=I := ConcretePrimeRowBridge.span_idealGenerator I
    have hbad : ¬Supported (Ideal.span {n}) := by
      intro h
      have hp : primaryGenerator (Ideal.span {n}) ≠ 0 :=
        PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff n |>.mpr ((CanonicalQuadraticSieve.supported_span_iff n).mp h).1
      exact hp (hs ▸ hg)
    rw [← hs,idealCoeff_span χ hn,hrow,
      CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hbad]
  · rw [ite_eq_right hg]

def density (c : O) (hc : c ≠ 0) (ψ : Character) (R : Ideal O) : ℂ :=
  letI := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  (∑ D ∈ idealDivisors R, (moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)) *
    (1/(‖eisEmbedding c‖^2:ℂ))*(∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r)

theorem density_norm_le (c : O) (hc : c ≠ 0) (ψ : Character) (R : Ideal O) (hR : R ≠ 0) :
    ‖density c hc ψ R‖ ≤
      ((idealDivisors R).card:ℝ)*(Nat.card (O ⧸ Ideal.span {c}):ℝ)/‖eisEmbedding c‖^2 := by
  let := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have hdiv : ‖∑ D ∈ idealDivisors R, (moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)‖ ≤
      ((idealDivisors R).card:ℝ) := by
    calc
      _ ≤ ∑ D ∈ idealDivisors R, ‖(moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _D ∈ idealDivisors R, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro D hD
        have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
        have hN : (1:ℝ) ≤ Ideal.absNorm D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
        rw [norm_div,norm_mul,Complex.norm_natCast]
        apply (div_le_one (by linarith : 0 < (Ideal.absNorm D:ℝ))).mpr
        exact ((mul_le_of_le_one_left (norm_nonneg _) (norm_ideal_moebius_le_one D)).trans
          (primaryCoefficient_norm ψ D)).trans hN
      _ = _ := by simp
  have hres : ‖∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r‖ ≤
      (Nat.card (O ⧸ Ideal.span {c}):ℝ) := by
    calc
      _ ≤ ∑ r : O ⧸ Ideal.span {c}, ‖periodicValue c ψ r‖ := norm_sum_le _ _
      _ ≤ ∑ _r : O ⧸ Ideal.span {c}, (1:ℝ) := Finset.sum_le_sum (fun r hr => periodicValue_norm c ψ r)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  unfold density
  rw [norm_mul,norm_mul,norm_div,norm_one,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  calc
    _ ≤ (((idealDivisors R).card:ℝ)*(1/‖eisEmbedding c‖^2))*(Nat.card (O ⧸ Ideal.span {c}):ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hdiv (by positivity)) hres (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem actual_induced_volume (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W : 𝓢(ℝ,ℂ)) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support (W:ℝ→ℂ) ⊆ Set.Iic b) :
    ‖(∑' I : Ideal O, idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X)) -
      (X:ℂ)*(density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus*paperRadialFourier W 0)‖ ≤
      ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)*pvControl W := by
  let := finite_quotient_span (fixedPeriod_ne_zero Q hQ)
  let : Fintype (O ⧸ Ideal.span {fixedPeriod Q}) := Fintype.ofFinite _
  have h := masked_hecke_volume (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ)
    (fixedPeriod_three Q) ψ ((span_fixedPeriod_le Q).trans hQψ)
    χ.modulus χ.modulus_ne_bot W b X hX hs
  have he (I : Ideal O) :
      (if IsCoprime I χ.modulus then (1:ℂ) else 0)*primaryCoefficient ψ I=idealCoeff χ I := by
    rw [← induced_primaryCoefficient χ ψ hind I,primaryCoefficient_actual_row η χ m A₀ z hmLam hm2 hrow I]
  simp_rw [show ∀ I : Ideal O, (if IsCoprime I χ.modulus then (1:ℂ) else 0)*
      (primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X)) =
        idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X) by intro I; rw [← mul_assoc,he]] at h
  convert h using 1
  · congr 1
    unfold density
    ring
  · rw [Nat.card_eq_fintype_card]
    ring

end SevenEighths.CenteredMomentHeckeVolume

end

end OAI

end Source385

/- Original source: OAI/NumberTheory/DirichletL/Moments/Cancellation.lean; sha256: 38bae6356dab92a3933d50858cd8b102b151cde64849a84395441079c957a36d -/
section Source386
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCancellation
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open IdealMobiusDivisorSum UniqueFactorizationMonoid QuadraticInitialBound
open CenteredMomentPrimary CenteredMomentMaskedVolume

def maskedSum (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
    (primaryIdealCharacter c χ I * W ((Ideal.absNorm I : ℝ) / X))

def maskedDensity (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) : ℂ :=
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  (∑ D ∈ idealDivisors R, (moebius D : ℂ) * primaryIdealCharacter c χ D /
    (Ideal.absNorm D : ℂ)) * (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
      ∑ r : O ⧸ Ideal.span {c}, primaryResidueValue c χ r

def maskedError (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : 𝓢(ℝ, ℂ)) : ℝ :=
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  ((idealDivisors R).card : ℝ) *
    ((∑ r : O ⧸ Ideal.span {c}, ‖primaryResidueValue c χ r‖) * pvControl W)

lemma maskedError_nonneg (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : 𝓢(ℝ, ℂ)) : 0 ≤ maskedError c hc χ R W := by
  unfold maskedError
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (pvControl_nonneg W))

theorem maskedSum_volume (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W : 𝓢(ℝ, ℂ)) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Iic b) :
    ‖maskedSum c χ R W X - (X : ℂ) *
      (maskedDensity c hc χ R * paperRadialFourier W 0)‖ ≤ maskedError c hc χ R W := by
  have h := masked_primary_ideal_volume_error c hc h3 χ R hR W b X hX hs
  convert h using 1
  unfold maskedSum maskedDensity
  congr 1
  ring
  all_goals rfl

theorem masked_rectangle_saving
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W₁ W₂ : 𝓢(ℝ, ℂ)) (b₁ b₂ : ℝ)
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Iic b₁)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Iic b₂)
    (X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 1 ≤ L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    let E := maskedError c hc χ R W₁ + maskedError c hc χ R W₂
    let C := ‖maskedDensity c hc χ R * paperRadialFourier W₁ 0‖ +
      ‖maskedDensity c hc χ R * paperRadialFourier W₂ 0‖ + E
    ‖maskedSum c χ R W₁ X₁ * maskedSum c χ R W₂ X₂ -
      maskedSum c χ R W₁ Y₁ * maskedSum c χ R W₂ Y₂‖ ≤ 4 * E * C * (T / L) := by
  let E := maskedError c hc χ R W₁ + maskedError c hc χ R W₂
  let v₁ := maskedDensity c hc χ R * paperRadialFourier W₁ 0
  let v₂ := maskedDensity c hc χ R * paperRadialFourier W₂ 0
  let C := ‖v₁‖ + ‖v₂‖ + E
  have hE₁ := maskedError_nonneg c hc χ R W₁
  have hE₂ := maskedError_nonneg c hc χ R W₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hC : 0 ≤ C := add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) hE
  have hL0 : 0 < L := by linarith
  have ha₁ (X : ℝ) (hX : L ≤ X) : ‖maskedSum c χ R W₁ X - (X : ℂ) * v₁‖ ≤ E :=
    (maskedSum_volume c hc h3 χ R hR W₁ b₁ X (lt_of_lt_of_le hL0 hX) hs₁).trans
      (le_add_of_nonneg_right hE₂)
  have ha₂ (X : ℝ) (hX : L ≤ X) : ‖maskedSum c χ R W₂ X - (X : ℂ) * v₂‖ ≤ E :=
    (maskedSum_volume c hc h3 χ R hR W₂ b₂ X (lt_of_lt_of_le hL0 hX) hs₂).trans
      (le_add_of_nonneg_left hE₁)
  have hv₁ (X : ℝ) (hX : L ≤ X) : ‖(X : ℂ) * v₁‖ ≤ C * X := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans hL0.le hX)]
    have hv : ‖v₁‖ ≤ C := by dsimp only [C]; linarith [norm_nonneg v₂]
    nlinarith [mul_le_mul_of_nonneg_right hv (le_trans hL0.le hX)]
  have hv₂ (X : ℝ) (hX : L ≤ X) : ‖maskedSum c χ R W₂ X‖ ≤ C * X := by
    have hb := norm_le_norm_sub_add (maskedSum c χ R W₂ X) ((X : ℂ) * v₂)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans hL0.le hX)] at hb
    have hEX : E ≤ E * X := by nlinarith [mul_le_mul_of_nonneg_left (le_trans hL hX) hE]
    have hbound := ha₂ X hX
    dsimp only [C]
    nlinarith [mul_nonneg (norm_nonneg v₁) (le_trans hL0.le hX)]
  have hmain : ((X₁ : ℂ) * v₁) * ((X₂ : ℂ) * v₂) =
      ((Y₁ : ℂ) * v₁) * ((Y₂ : ℂ) * v₂) := by
    have hp : (X₁ : ℂ) * X₂ = (Y₁ : ℂ) * Y₂ := by exact_mod_cast hprodX.trans hprodY.symm
    calc
      _ = ((X₁ : ℂ) * X₂) * (v₁ * v₂) := by ring
      _ = ((Y₁ : ℂ) * Y₂) * (v₁ * v₂) := by rw [hp]
      _ = _ := by ring
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (ha₁ X₁ hX₁) (ha₂ X₂ hX₂)
    (ha₁ Y₁ hY₁) (ha₂ Y₂ hY₂) (hv₂ X₂ hX₂) (hv₁ X₁ hX₁)
    (hv₂ Y₂ hY₂) (hv₁ Y₁ hY₁) hL0 hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end SevenEighths.CenteredMomentCancellation
end

end OAI

end Source386

/- Original source: OAI/NumberTheory/DirichletL/Moments/HeckeCancellation.lean; sha256: 3148739bbbcb292de174fc5ce3dcbed2187e23a9a7475653d967a330f802c440 -/
section Source387
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentHeckeCancellation
open HeckeFamily CenteredMomentHeckeVolume ConcreteTraceCRT EisensteinSchwartzPoisson
open IdealMobiusDivisorSum QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

def idealSum (χ : Character) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X)

def volumeControl (Q : Ideal O) (χ : Character) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)*pvControl W

def densityControl (Q : Ideal O) (χ : Character) : ℝ :=
  ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)/‖eisEmbedding (fixedPeriod Q)‖^2

lemma volumeControl_nonneg (Q : Ideal O) (χ : Character) (W : 𝓢(ℝ,ℂ)) : 0 ≤ volumeControl Q χ W :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pvControl_nonneg W)

lemma densityControl_nonneg (Q : Ideal O) (χ : Character) : 0 ≤ densityControl Q χ := by
  unfold densityControl
  positivity

theorem actual_rectangle_saving (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b₁ b₂ : ℝ)
    (hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Set.Iic b₁)
    (hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Set.Iic b₂)
    (X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 1 ≤ L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁*X₂=T) (hprodY : Y₁*Y₂=T) :
    let E := volumeControl Q χ W₁+volumeControl Q χ W₂
    let C := densityControl Q χ*(‖paperRadialFourier W₁ 0‖+‖paperRadialFourier W₂ 0‖)+E
    ‖idealSum χ W₁ X₁*idealSum χ W₂ X₂-idealSum χ W₁ Y₁*idealSum χ W₂ Y₂‖ ≤
      4*E*C*(T/L) := by
  let E := volumeControl Q χ W₁+volumeControl Q χ W₂
  let D := densityControl Q χ
  let C := D*(‖paperRadialFourier W₁ 0‖+‖paperRadialFourier W₂ 0‖)+E
  let v₁ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus*paperRadialFourier W₁ 0
  let v₂ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus*paperRadialFourier W₂ 0
  have hE₁ := volumeControl_nonneg Q χ W₁
  have hE₂ := volumeControl_nonneg Q χ W₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hD : 0 ≤ D := densityControl_nonneg Q χ
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hL0 : 0 < L := by linarith
  have hden : ‖density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus‖ ≤ D :=
    density_norm_le _ _ ψ χ.modulus χ.modulus_ne_bot
  have hvol₁ : ‖v₁‖ ≤ D*‖paperRadialFourier W₁ 0‖ := by
    dsimp only [v₁]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hden (norm_nonneg _)
  have hvol₂ : ‖v₂‖ ≤ D*‖paperRadialFourier W₂ 0‖ := by
    dsimp only [v₂]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hden (norm_nonneg _)
  have ha₁ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ W₁ X-(X:ℂ)*v₁‖ ≤ E :=
    (actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ b₁ X
      (lt_of_lt_of_le hL0 hX) hs₁).trans (le_add_of_nonneg_right hE₂)
  have ha₂ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ W₂ X-(X:ℂ)*v₂‖ ≤ E :=
    (actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₂ b₂ X
      (lt_of_lt_of_le hL0 hX) hs₂).trans (le_add_of_nonneg_left hE₁)
  have hv₁ (X : ℝ) (hX : L ≤ X) : ‖(X:ℂ)*v₁‖ ≤ C*X := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_trans hL0.le hX)]
    have hv : ‖v₁‖ ≤ C := by
      dsimp only [C]
      nlinarith [mul_nonneg hD (norm_nonneg (paperRadialFourier W₂ 0))]
    nlinarith [mul_le_mul_of_nonneg_right hv (le_trans hL0.le hX)]
  have hv₂ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ W₂ X‖ ≤ C*X := by
    have hb := norm_le_norm_sub_add (idealSum χ W₂ X) ((X:ℂ)*v₂)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_trans hL0.le hX)] at hb
    have hEX : E ≤ E*X := by nlinarith [mul_le_mul_of_nonneg_left (le_trans hL hX) hE]
    have hbound := ha₂ X hX
    have hv := mul_le_mul_of_nonneg_left hvol₂ (le_trans hL0.le hX)
    dsimp only [C]
    nlinarith [mul_nonneg (mul_nonneg hD (norm_nonneg (paperRadialFourier W₁ 0))) (le_trans hL0.le hX)]
  have hmain : ((X₁:ℂ)*v₁)*((X₂:ℂ)*v₂)=((Y₁:ℂ)*v₁)*((Y₂:ℂ)*v₂) := by
    have hp : (X₁:ℂ)*X₂=(Y₁:ℂ)*Y₂ := by exact_mod_cast hprodX.trans hprodY.symm
    calc
      _ = ((X₁:ℂ)*X₂)*(v₁*v₂) := by ring
      _ = ((Y₁:ℂ)*Y₂)*(v₁*v₂) := by rw [hp]
      _ = _ := by ring
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (ha₁ X₁ hX₁) (ha₂ X₂ hX₂)
    (ha₁ Y₁ hY₁) (ha₂ Y₂ hY₂) (hv₂ X₂ hX₂) (hv₁ X₁ hX₁)
    (hv₂ Y₂ hY₂) (hv₁ Y₁ hY₁) hL0 hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end SevenEighths.CenteredMomentHeckeCancellation

end

end OAI

end Source387

/- Original source: OAI/NumberTheory/DirichletL/Moments/Counting.lean; sha256: 0a3c0198d00776d735b5c4cda7d71a64389ae24d7b585345c0bc17cf07809b6c -/
section Source388
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCounting
open CenteredMomentCancellation CenteredMomentPrimary
open QuadraticInitialBound

theorem norm_tsum_ideal_ball (f : Ideal O → ℂ) (H M : ℝ)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hzero : f ⊥ = 0)
    (hbound : ∀ I, ‖f I‖ ≤ M)
    (hsupport : ∀ I, f I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ H) :
    ‖∑' I : Ideal O, f I‖ ≤ 128 * M * H := by
  classical
  have hfinite : (Function.support f).Finite := by
    apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil H)).subset
    intro I hI
    exact_mod_cast (hsupport I hI).trans (Nat.le_ceil H)
  let S := hfinite.toFinset
  have hmem (I : Ideal O) : I ∈ S ↔ f I ≠ 0 := hfinite.mem_toFinset
  have htsum : (∑' I : Ideal O, f I) = ∑ I ∈ S, f I := by
    exact tsum_eq_sum (fun I hI => not_ne_iff.mp (mt (hmem I).mpr hI))
  rw [htsum]
  by_cases hS : S.Nonempty
  · obtain ⟨I, hI⟩ := hS
    have hI0 : I ≠ ⊥ := by intro h; exact (hmem I).mp hI (h ▸ hzero)
    have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => hI0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hH1 : 1 ≤ H := hn.trans (hsupport I ((hmem I).mp hI))
    have hcount := DescentFiberCost.finite_ideal_count_real S H hH1
      (fun J hJ hz => (hmem J).mp hJ (hz ▸ hzero))
      (fun J hJ => hsupport J ((hmem J).mp hJ))
    calc
      _ ≤ ∑ I ∈ S, ‖f I‖ := norm_sum_le _ _
      _ ≤ ∑ _I ∈ S, M := Finset.sum_le_sum (fun I _ => hbound I)
      _ = (S.card : ℝ) * M := by simp
      _ ≤ (128 * H) * M := mul_le_mul_of_nonneg_right hcount hM
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.sum_empty, norm_zero]
    positivity

theorem masked_coefficient_norm_le_one (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R I : Ideal O) :
    ‖(if IsCoprime I R then (1 : ℂ) else 0) * primaryIdealCharacter c χ I‖ ≤ 1 := by
  split_ifs
  · simpa only [one_mul] using primaryIdealCharacter_norm_le_one c hc χ I
  · simp only [zero_mul, norm_zero, zero_le_one]

theorem maskedSum_absolute (c : O) (hc : c ≠ 0)
    [Nontrivial (O ⧸ Ideal.span {c})]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O)
    (W : ℝ → ℂ) (b M X : ℝ) (hb : 0 ≤ b) (hM : 0 ≤ M) (hX : 0 < X)
    (hW : ∀ y, ‖W y‖ ≤ M) (hs : Function.support W ⊆ Set.Iic b) :
    ‖maskedSum c χ R W X‖ ≤ (128 * b * M) * X := by
  have hzero : primaryIdealCharacter c χ (⊥ : Ideal O) = 0 := by
    apply primaryIdealCharacter_zero_of_bad
    exact map_zero CompletedGauss.primaryGeneratorHom
  have h := norm_tsum_ideal_ball
    (fun I => (if IsCoprime I R then (1 : ℂ) else 0) *
      (primaryIdealCharacter c χ I * W ((Ideal.absNorm I : ℝ) / X)))
    (b * X) M (mul_nonneg hb hX.le) hM
    (by simp only [hzero, zero_mul, mul_zero])
    (by
      intro I
      rw [← mul_assoc, norm_mul]
      exact (mul_le_mul (masked_coefficient_norm_le_one c hc χ R I)
        (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul M))
    (by
      intro I hI
      have hw : W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
        intro hz
        exact hI (by simp only [hz, mul_zero])
      exact (div_le_iff₀ hX).mp (hs hw))
  change ‖maskedSum c χ R W X‖ ≤ _ at h
  convert h using 1 ; ring

theorem norm_linear_coefficient_le (S : ℝ → ℂ) (v : ℂ) (C E : ℝ) (hE : 0 ≤ E)
    (herror : ∀ X : ℝ, 0 < X → ‖S X - (X : ℂ) * v‖ ≤ E)
    (habsolute : ∀ X : ℝ, 0 < X → ‖S X‖ ≤ C * X) : ‖v‖ ≤ C := by
  by_contra hn
  have hδ : 0 < ‖v‖ - C := sub_pos.mpr (lt_of_not_ge hn)
  let X := (E + 1) / (‖v‖ - C)
  have hX : 0 < X := div_pos (by linarith) hδ
  have heq : X * (‖v‖ - C) = E + 1 := div_mul_cancel₀ _ hδ.ne'
  have h := norm_le_norm_sub_add ((X : ℂ) * v) (S X)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hX.le, norm_sub_rev] at h
  have ha := habsolute X hX
  have hb := herror X hX
  nlinarith

end SevenEighths.CenteredMomentCounting
end

end OAI

end Source388

/- Original source: OAI/NumberTheory/DirichletL/Moments/Twist.lean; sha256: 4037b36343435e0d685e578d293c8e1a30c425155894b0083beeb2f1b1537af2 -/
section Source389
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentTwist
open ActualEisensteinCubic EisensteinSchwartzPoisson
open CenteredMomentLattice CenteredMomentCancellation CenteredMomentCounting

def twistedMaskedSum (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
    (CenteredMomentPrimary.primaryIdealCharacter c χ I *
      (Ideal.absNorm I : ℂ) ^ (Complex.I * t) * W ((Ideal.absNorm I : ℝ) / X))

lemma normPowerProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    Function.support (normPowerProfile W a b ha hs hW t : ℝ → ℂ) ⊆ Function.support W := by
  intro x hx hz
  exact hx (by rw [normPowerProfile_apply, hz, mul_zero])

lemma normPowerProfile_norm (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    ‖normPowerProfile W a b ha hs hW t x‖ = ‖W x‖ := by
  rw [normPowerProfile, CompletedHeight.uniformTwistedSchwartz_apply,
    CompletedHeight.normTwistedSource, norm_mul, FourierBridge.logPhase_norm, one_mul]

lemma norm_real_imaginary_power (X t : ℝ) (hX : 0 < X) :
    ‖(X : ℂ) ^ (Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp

theorem twistedMaskedSum_scale (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    twistedMaskedSum c χ R W t X = (X : ℂ) ^ (Complex.I * t) *
      maskedSum c χ R (normPowerProfile W a b ha hs hW t) X := by
  unfold twistedMaskedSum maskedSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [normPowerProfile_apply]
  have hphase : (Ideal.absNorm I : ℂ) ^ (Complex.I * t) =
      (X : ℂ) ^ (Complex.I * t) *
        (((Ideal.absNorm I : ℝ) / X : ℝ) : ℂ) ^ (Complex.I * t) := by
    have h := Complex.mul_cpow_ofReal_nonneg hX.le
      (div_nonneg (Nat.cast_nonneg (Ideal.absNorm I)) hX.le) (Complex.I * t)
    have heq : X * ((Ideal.absNorm I : ℝ) / X) = (Ideal.absNorm I : ℝ) := by field_simp
    rw [← Complex.ofReal_mul, heq, Complex.ofReal_natCast] at h
    exact h
  rw [hphase]
  ring

theorem twistedMaskedSum_volume (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    ‖twistedMaskedSum c χ R W t X -
      (X : ℂ) ^ (1 + Complex.I * t) * maskedDensity c hc χ R *
        paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      maskedError c hc χ R (normPowerProfile W a b ha hs hW t) := by
  rw [twistedMaskedSum_scale c χ R W a b ha hs hW t X hX]
  have hmain : (X : ℂ) ^ (1 + Complex.I * t) * maskedDensity c hc χ R *
      paperRadialFourier (normPowerProfile W a b ha hs hW t) 0 =
    (X : ℂ) ^ (Complex.I * t) * ((X : ℂ) *
      (maskedDensity c hc χ R * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0)) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne'), Complex.cpow_one]
    ring
  rw [hmain, ← mul_sub, norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact maskedSum_volume c hc h3 χ R hR _ b X hX
    ((normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2))

theorem twistedMaskedSum_absolute (c : O) (hc : c ≠ 0)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : ℝ → ℂ) (a b M : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t X : ℝ) (hX : 0 < X) :
    ‖twistedMaskedSum c χ R W t X‖ ≤ (128 * b * M) * X := by
  rw [twistedMaskedSum_scale c χ R W a b ha hs hW t X hX,
    norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact maskedSum_absolute c hc χ R _ b M X hb hM hX
    (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y))
    ((normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2))

theorem twisted_volumeCoefficient_norm_le (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W : ℝ → ℂ) (a b M : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t : ℝ) :
    ‖maskedDensity c hc χ R * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      128 * b * M := by
  let V := normPowerProfile W a b ha hs hW t
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Iic b :=
    (normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2)
  exact norm_linear_coefficient_le (fun X => maskedSum c χ R V X)
    _ (128 * b * M) (maskedError c hc χ R V) (maskedError_nonneg c hc χ R V)
    (fun X hX => maskedSum_volume c hc h3 χ R hR V b X hX hV)
    (fun X hX => maskedSum_absolute c hc χ R V b M X hb hM hX
      (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y)) hV)

theorem twisted_rectangle_saving
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ M₁ M₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (hbound₁ : ∀ y, ‖W₁ y‖ ≤ M₁) (hbound₂ : ∀ y, ‖W₂ y‖ ≤ M₂)
    (t X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    let E := maskedError c hc χ R (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
      maskedError c hc χ R (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
    ‖twistedMaskedSum c χ R W₁ t X₁ * twistedMaskedSum c χ R W₂ t X₂ -
      twistedMaskedSum c χ R W₁ t Y₁ * twistedMaskedSum c χ R W₂ t Y₂‖ ≤
      4 * E * (128 * (b₁ * M₁ + b₂ * M₂)) * (T / L) := by
  let V₁ := normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t
  let V₂ := normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t
  let E := maskedError c hc χ R V₁ + maskedError c hc χ R V₂
  let C := 128 * (b₁ * M₁ + b₂ * M₂)
  let v₁ := maskedDensity c hc χ R * paperRadialFourier V₁ 0
  let v₂ := maskedDensity c hc χ R * paperRadialFourier V₂ 0
  let m₁ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₁
  let m₂ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₂
  have hE₁ := maskedError_nonneg c hc χ R V₁
  have hE₂ := maskedError_nonneg c hc χ R V₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  have hC₁ : 128 * b₁ * M₁ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₂ hM₂]
  have hC₂ : 128 * b₂ * M₂ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₁ hM₁]
  have he₁ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum c χ R W₁ t X - m₁ X‖ ≤ E := by
    have h := twistedMaskedSum_volume c hc h3 χ R hR W₁ a₁ b₁ ha₁ hs₁ hW₁ t X
      (lt_of_lt_of_le hL hX)
    change ‖_ - _ * v₁‖ ≤ E
    simpa only [v₁, mul_assoc] using h.trans (le_add_of_nonneg_right hE₂)
  have he₂ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum c χ R W₂ t X - m₂ X‖ ≤ E := by
    have h := twistedMaskedSum_volume c hc h3 χ R hR W₂ a₂ b₂ ha₂ hs₂ hW₂ t X
      (lt_of_lt_of_le hL hX)
    change ‖_ - _ * v₂‖ ≤ E
    simpa only [v₂, mul_assoc] using h.trans (le_add_of_nonneg_left hE₁)
  have hmain₁ (X : ℝ) (hX : L ≤ X) : ‖m₁ X‖ ≤ C * X := by
    have hv := (twisted_volumeCoefficient_norm_le c hc h3 χ R hR W₁ a₁ b₁ M₁
      ha₁ hb₁ hM₁ hs₁ hW₁ hbound₁ t).trans hC₁
    dsimp only [m₁]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hL hX)]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.ofReal_im, mul_zero, sub_self, add_zero, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hv (le_trans hL.le hX)]
  have habs₂ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum c χ R W₂ t X‖ ≤ C * X :=
    (twistedMaskedSum_absolute c hc χ R W₂ a₂ b₂ M₂ ha₂ hb₂ hM₂ hs₂ hW₂ hbound₂ t X
      (lt_of_lt_of_le hL hX)).trans (mul_le_mul_of_nonneg_right hC₂ (le_trans hL.le hX))
  have hmain : m₁ X₁ * m₂ X₂ = m₁ Y₁ * m₂ Y₂ := by
    have hpow := CenteredMoment.volume_products_eq
      (1 : ℂ) v₁ v₂ t X₁ X₂ Y₁ Y₂ (le_trans hL.le hX₁) (le_trans hL.le hX₂)
      (le_trans hL.le hY₁) (le_trans hL.le hY₂) (hprodX.trans hprodY.symm)
    simpa only [CenteredMoment.volumeTerm, one_mul, m₁, m₂] using hpow
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (he₁ X₁ hX₁) (he₂ X₂ hX₂)
    (he₁ Y₁ hY₁) (he₂ Y₂ hY₂) (habs₂ X₂ hX₂) (hmain₁ X₁ hX₁)
    (habs₂ Y₂ hY₂) (hmain₁ Y₁ hY₁) hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end SevenEighths.CenteredMomentTwist
end

end OAI

end Source389

/- Original source: OAI/NumberTheory/DirichletL/Moments/Height.lean; sha256: fbbacbc778756595e60b96291a80f624796fede5d485f9c1e530fb8b2bea4ea8 -/
section Source390
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentHeight
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open QuadraticInitialBound CenteredMomentLattice CenteredMomentMask
open CenteredMomentPrimary CenteredMomentCancellation CenteredMomentTwist

lemma normalized_height_le (t : ℝ) : ‖t / (2 * Real.pi)‖ ≤ ‖t‖ := by
  rw [norm_div, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])

theorem maskedError_polynomial_height (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ R : Ideal O, R ≠ 0 → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ t : ℝ, maskedError c hc χ R (normPowerProfile W a b ha hs hW t) ≤
        C * Z ^ ε * (1 + ‖t‖) ^ n := by
  obtain ⟨n, hn⟩ := normPowerProfile_uniform_degree a b ha pvSeminorms
  obtain ⟨D, hD, hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  refine ⟨n, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hprofile⟩ := hn W hs hW
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let mass : ℝ := ∑ r : O ⧸ Ideal.span {c}, ‖primaryResidueValue c χ r‖
  have hmass : 0 ≤ mass := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let A := D * mass * pvConstant * C
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg hD.le hmass) pvConstant_pos.le) hC.le
  refine ⟨1 + A, by linarith, ?_⟩
  intro Z hZ R hR hnorm t
  have hheight : (1 + ‖t / (2 * Real.pi)‖) ^ n ≤ (1 + ‖t‖) ^ n := by
    gcongr
    exact normalized_height_le t
  have hseminorm := (hprofile t).trans (mul_le_mul_of_nonneg_left hheight hC.le)
  have herr : maskedError c hc χ R (normPowerProfile W a b ha hs hW t) ≤
      (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := by
    unfold maskedError pvControl
    apply mul_le_mul (hdiv Z hZ R hR hnorm)
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hseminorm pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg pvConstant_pos.le (apply_nonneg _ _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := herr
    _ = A * Z ^ ε * (1 + ‖t‖) ^ n := by dsimp only [A]; ring
    _ ≤ (1 + A) * Z ^ ε * (1 + ‖t‖) ^ n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : A ≤ 1 + A)
          (Real.rpow_nonneg (le_trans zero_le_one hZ) ε)) (by positivity)

theorem normalized_masked_rectangle_estimate
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal O, R ≠ 0 → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (twistedMaskedSum c χ R W₁ t X₁ * twistedMaskedSum c χ R W₂ t X₂ -
          twistedMaskedSum c χ R W₁ t Y₁ * twistedMaskedSum c χ R W₂ t Y₂)‖ ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J * (Real.sqrt T / L) := by
  obtain ⟨n₁, hn₁⟩ := maskedError_polynomial_height c hc χ a₁ b₁ ε B ha₁ hε hB
  obtain ⟨n₂, hn₂⟩ := maskedError_polynomial_height c hc χ a₂ b₂ ε B ha₂ hε hB
  refine ⟨max n₁ n₂, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨D₁, hD₁, herr₁⟩ := hn₁ W₁ hs₁ hW₁
  obtain ⟨D₂, hD₂, herr₂⟩ := hn₂ W₂ hs₂ hW₂
  let M₁ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ 0)
  let M₂ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ 0)
  have hM₁ : 0 ≤ M₁ := apply_nonneg _ _
  have hM₂ : 0 ≤ M₂ := apply_nonneg _ _
  have hbound₁ (y : ℝ) : ‖W₁ y‖ ≤ M₁ := by
    rw [← normPowerProfile_norm W₁ a₁ b₁ ha₁ hs₁ hW₁ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hbound₂ (y : ℝ) : ‖W₂ y‖ ≤ M₂ := by
    rw [← normPowerProfile_norm W₂ a₂ b₂ ha₂ hs₂ hW₂ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  let V := 128 * (b₁ * M₁ + b₂ * M₂)
  have hV : 0 ≤ V := mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  let C := 1 + 4 * (D₁ + D₂) * V
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let E := maskedError c hc χ R (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
    maskedError c hc χ R (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have hpow₁ := pow_le_pow_right₀ ht (le_max_left n₁ n₂)
  have hpow₂ := pow_le_pow_right₀ ht (le_max_right n₁ n₂)
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (le_trans zero_le_one hZ) ε
  have hE : E ≤ (D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ := by
    have h₁ := (herr₁ Z hZ R hR hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₁ (mul_nonneg hD₁.le hz))
    have h₂ := (herr₂ Z hZ R hR hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₂ (mul_nonneg hD₂.le hz))
    dsimp only [E]
    nlinarith
  have hraw := twisted_rectangle_saving c hc h3 χ R hR W₁ W₂ a₁ b₁ a₂ b₂ M₁ M₂
    ha₁ ha₂ hb₁ hb₂ hM₁ hM₂ hs₁ hs₂ hW₁ hW₂ hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
  have hnormalized := CenteredMoment.normalized_centered_saving _ T L V E hT hraw
  have hratio : 0 ≤ Real.sqrt T / L := div_nonneg (Real.sqrt_nonneg T) hL.le
  calc
    _ ≤ 4 * E * V * (Real.sqrt T / L) := hnormalized
    _ ≤ 4 * ((D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂) * V *
        (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hV) hratio
    _ = (4 * (D₁ + D₂) * V) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ *
        (Real.sqrt T / L) := by ring
    _ ≤ C * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ * (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hz) (by positivity)) hratio

end SevenEighths.CenteredMomentHeight
end

end OAI

end Source390

/- Original source: OAI/NumberTheory/DirichletL/Moments/HeckeTwist.lean; sha256: a495e58ad0f408343b2e7808881086f01681a194b570d6d54e21d5c1d2c292fa -/
section Source391
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeTwist
open HeckeFamily CenteredMomentHeckeVolume CenteredMomentHeckeCancellation
open CenteredMomentLattice CenteredMomentCounting CenteredMomentTwist
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def twistedIdealSum (χ : Character) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, idealCoeff χ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)

theorem idealSum_absolute (χ : Character) (W : ℝ → ℂ) (b M X : ℝ)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hX : 0 < X)
    (hW : ∀ y, ‖W y‖ ≤ M) (hs : Function.support W ⊆ Set.Iic b) :
    ‖idealSum χ W X‖ ≤ (128*b*M)*X := by
  have h := norm_tsum_ideal_ball (fun I => idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X))
    (b*X) M (mul_nonneg hb hX.le) hM (by change idealCoeff χ (0:Ideal O)*_ = 0; rw [map_zero,zero_mul])
    (by intro I; rw [norm_mul]; exact (mul_le_mul (idealCoeff_norm_le_one χ I) (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul M))
    (by intro I hI; apply (div_le_iff₀ hX).mp; apply hs; intro hz; exact hI (by rw [hz,mul_zero]))
  change ‖idealSum χ W X‖ ≤ _ at h
  convert h using 1 ; ring

theorem twistedIdealSum_scale (χ : Character) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    twistedIdealSum χ W t X = (X : ℂ) ^ (Complex.I * t) *
      idealSum χ (normPowerProfile W a b ha hs hW t) X := by
  unfold twistedIdealSum idealSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [normPowerProfile_apply]
  have hphase : (Ideal.absNorm I : ℂ) ^ (Complex.I * t) =
      (X : ℂ) ^ (Complex.I * t) *
        (((Ideal.absNorm I : ℝ) / X : ℝ) : ℂ) ^ (Complex.I * t) := by
    have h := Complex.mul_cpow_ofReal_nonneg hX.le
      (div_nonneg (Nat.cast_nonneg (Ideal.absNorm I)) hX.le) (Complex.I * t)
    have heq : X * ((Ideal.absNorm I : ℝ) / X) = (Ideal.absNorm I : ℝ) := by field_simp
    rw [← Complex.ofReal_mul, heq, Complex.ofReal_natCast] at h
    exact h
  rw [hphase]
  ring

theorem twistedIdealSum_volume (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    ‖twistedIdealSum χ W t X -
      (X : ℂ) ^ (1 + Complex.I * t) * density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus *
        paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      volumeControl Q χ (normPowerProfile W a b ha hs hW t) := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX]
  have hmain : (X : ℂ) ^ (1 + Complex.I * t) * density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus *
      paperRadialFourier (normPowerProfile W a b ha hs hW t) 0 =
    (X : ℂ) ^ (Complex.I * t) * ((X : ℂ) *
      (density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0)) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne'), Complex.cpow_one]
    ring
  rw [hmain, ← mul_sub, norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow _ b X hX
    ((normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2))

theorem twistedIdealSum_absolute (χ : Character) (W : ℝ → ℂ) (a b M : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t X : ℝ) (hX : 0 < X) :
    ‖twistedIdealSum χ W t X‖ ≤ (128 * b * M) * X := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX,
    norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact idealSum_absolute χ _ b M X hb hM hX
    (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y))
    ((normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2))

theorem twisted_actual_volumeCoefficient_norm_le (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (W : ℝ → ℂ) (a b M : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t : ℝ) :
    ‖density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      128 * b * M := by
  let V := normPowerProfile W a b ha hs hW t
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Iic b :=
    (normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2)
  exact norm_linear_coefficient_le (fun X => idealSum χ V X)
    _ (128 * b * M) (volumeControl Q χ V) (volumeControl_nonneg Q χ V)
    (fun X hX => actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow V b X hX hV)
    (fun X hX => idealSum_absolute χ V b M X hb hM hX
      (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y)) hV)

theorem actual_twisted_rectangle_saving
    (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ M₁ M₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (hbound₁ : ∀ y, ‖W₁ y‖ ≤ M₁) (hbound₂ : ∀ y, ‖W₂ y‖ ≤ M₂)
    (t X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    let E := volumeControl Q χ (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
      volumeControl Q χ (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
    ‖twistedIdealSum χ W₁ t X₁ * twistedIdealSum χ W₂ t X₂ -
      twistedIdealSum χ W₁ t Y₁ * twistedIdealSum χ W₂ t Y₂‖ ≤
      4 * E * (128 * (b₁ * M₁ + b₂ * M₂)) * (T / L) := by
  let V₁ := normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t
  let V₂ := normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t
  let E := volumeControl Q χ V₁ + volumeControl Q χ V₂
  let C := 128 * (b₁ * M₁ + b₂ * M₂)
  let v₁ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier V₁ 0
  let v₂ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier V₂ 0
  let m₁ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₁
  let m₂ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₂
  have hE₁ := volumeControl_nonneg Q χ V₁
  have hE₂ := volumeControl_nonneg Q χ V₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  have hC₁ : 128 * b₁ * M₁ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₂ hM₂]
  have hC₂ : 128 * b₂ * M₂ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₁ hM₁]
  have he₁ (X : ℝ) (hX : L ≤ X) : ‖twistedIdealSum χ W₁ t X - m₁ X‖ ≤ E := by
    have h := twistedIdealSum_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ a₁ b₁ ha₁ hs₁ hW₁ t X
      (lt_of_lt_of_le hL hX)
    change ‖_ - _ * v₁‖ ≤ E
    simpa only [v₁, mul_assoc] using h.trans (le_add_of_nonneg_right hE₂)
  have he₂ (X : ℝ) (hX : L ≤ X) : ‖twistedIdealSum χ W₂ t X - m₂ X‖ ≤ E := by
    have h := twistedIdealSum_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₂ a₂ b₂ ha₂ hs₂ hW₂ t X
      (lt_of_lt_of_le hL hX)
    change ‖_ - _ * v₂‖ ≤ E
    simpa only [v₂, mul_assoc] using h.trans (le_add_of_nonneg_left hE₁)
  have hmain₁ (X : ℝ) (hX : L ≤ X) : ‖m₁ X‖ ≤ C * X := by
    have hv := (twisted_actual_volumeCoefficient_norm_le η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ a₁ b₁ M₁
      ha₁ hb₁ hM₁ hs₁ hW₁ hbound₁ t).trans hC₁
    dsimp only [m₁]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hL hX)]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.ofReal_im, mul_zero, sub_self, add_zero, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hv (le_trans hL.le hX)]
  have habs₂ (X : ℝ) (hX : L ≤ X) : ‖twistedIdealSum χ W₂ t X‖ ≤ C * X :=
    (twistedIdealSum_absolute χ W₂ a₂ b₂ M₂ ha₂ hb₂ hM₂ hs₂ hW₂ hbound₂ t X
      (lt_of_lt_of_le hL hX)).trans (mul_le_mul_of_nonneg_right hC₂ (le_trans hL.le hX))
  have hmain : m₁ X₁ * m₂ X₂ = m₁ Y₁ * m₂ Y₂ := by
    have hpow := CenteredMoment.volume_products_eq
      (1 : ℂ) v₁ v₂ t X₁ X₂ Y₁ Y₂ (le_trans hL.le hX₁) (le_trans hL.le hX₂)
      (le_trans hL.le hY₁) (le_trans hL.le hY₂) (hprodX.trans hprodY.symm)
    simpa only [CenteredMoment.volumeTerm, one_mul, m₁, m₂] using hpow
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (he₁ X₁ hX₁) (he₂ X₂ hX₂)
    (he₁ Y₁ hY₁) (he₂ Y₂ hY₂) (habs₂ X₂ hX₂) (hmain₁ X₁ hX₁)
    (habs₂ Y₂ hY₂) (hmain₁ Y₁ hY₁) hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end SevenEighths.CenteredMomentHeckeTwist

end

end OAI

end Source391

/- Original source: OAI/NumberTheory/DirichletL/Moments/HeckeHeight.lean; sha256: 9070c8b58f75529fdd0a1563d9c4c8201eb0d4eaf2e8038d5ad195dc9f096176 -/
section Source392
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeHeight
open HeckeFamily CenteredMomentHeckeVolume CenteredMomentHeckeCancellation CenteredMomentHeckeTwist
open CenteredMomentLattice CenteredMomentMask CenteredMomentTwist CenteredMomentHeight
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem volumeControl_polynomial_height (Q : Ideal O) (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      ∀ t : ℝ, volumeControl Q χ (normPowerProfile W a b ha hs hW t) ≤
        C * Z ^ ε * (1 + ‖t‖) ^ n := by
  obtain ⟨n, hn⟩ := normPowerProfile_uniform_degree a b ha pvSeminorms
  obtain ⟨D, hD, hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  refine ⟨n, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hprofile⟩ := hn W hs hW
  let mass : ℝ := Nat.card (O ⧸ Ideal.span {fixedPeriod Q})
  have hmass : 0 ≤ mass := Nat.cast_nonneg _
  let A := D * mass * pvConstant * C
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg hD.le hmass) pvConstant_pos.le) hC.le
  refine ⟨1 + A, by linarith, ?_⟩
  intro Z hZ χ hnorm t
  have hheight : (1 + ‖t / (2 * Real.pi)‖) ^ n ≤ (1 + ‖t‖) ^ n := by
    gcongr
    exact normalized_height_le t
  have hseminorm := (hprofile t).trans (mul_le_mul_of_nonneg_left hheight hC.le)
  have herr : volumeControl Q χ (normPowerProfile W a b ha hs hW t) ≤
      (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := by
    unfold volumeControl pvControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hnorm)
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hseminorm pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg pvConstant_pos.le (apply_nonneg _ _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := herr
    _ = A * Z ^ ε * (1 + ‖t‖) ^ n := by dsimp only [A]; ring
    _ ≤ (1 + A) * Z ^ ε * (1 + ‖t‖) ^ n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : A ≤ 1 + A)
          (Real.rpow_nonneg (le_trans zero_le_one hZ) ε)) (by positivity)

theorem normalized_actual_rectangle_estimate
    (Q : Ideal O) (hQ : Q ≠ 0)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ η χ ψ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      (Q ≤ ψ.modulus) → CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A₀ z : O, (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (twistedIdealSum χ W₁ t X₁ * twistedIdealSum χ W₂ t X₂ -
          twistedIdealSum χ W₁ t Y₁ * twistedIdealSum χ W₂ t Y₂)‖ ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J * (Real.sqrt T / L) := by
  obtain ⟨n₁, hn₁⟩ := volumeControl_polynomial_height Q a₁ b₁ ε B ha₁ hε hB
  obtain ⟨n₂, hn₂⟩ := volumeControl_polynomial_height Q a₂ b₂ ε B ha₂ hε hB
  refine ⟨max n₁ n₂, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨D₁, hD₁, herr₁⟩ := hn₁ W₁ hs₁ hW₁
  obtain ⟨D₂, hD₂, herr₂⟩ := hn₂ W₂ hs₂ hW₂
  let M₁ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ 0)
  let M₂ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ 0)
  have hM₁ : 0 ≤ M₁ := apply_nonneg _ _
  have hM₂ : 0 ≤ M₂ := apply_nonneg _ _
  have hbound₁ (y : ℝ) : ‖W₁ y‖ ≤ M₁ := by
    rw [← normPowerProfile_norm W₁ a₁ b₁ ha₁ hs₁ hW₁ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hbound₂ (y : ℝ) : ‖W₂ y‖ ≤ M₂ := by
    rw [← normPowerProfile_norm W₂ a₂ b₂ ha₂ hs₂ hW₂ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  let V := 128 * (b₁ * M₁ + b₂ * M₂)
  have hV : 0 ≤ V := mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  let C := 1 + 4 * (D₁ + D₂) * V
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z hZ η χ ψ hnorm hQψ hind m A₀ z hmLam hm2 hrow t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let E := volumeControl Q χ (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
    volumeControl Q χ (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have hpow₁ := pow_le_pow_right₀ ht (le_max_left n₁ n₂)
  have hpow₂ := pow_le_pow_right₀ ht (le_max_right n₁ n₂)
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (le_trans zero_le_one hZ) ε
  have hE : E ≤ (D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ := by
    have h₁ := (herr₁ Z hZ χ hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₁ (mul_nonneg hD₁.le hz))
    have h₂ := (herr₂ Z hZ χ hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₂ (mul_nonneg hD₂.le hz))
    dsimp only [E]
    nlinarith
  have hraw := actual_twisted_rectangle_saving η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ W₂ a₁ b₁ a₂ b₂ M₁ M₂
    ha₁ ha₂ hb₁ hb₂ hM₁ hM₂ hs₁ hs₂ hW₁ hW₂ hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
  have hnormalized := CenteredMoment.normalized_centered_saving _ T L V E hT hraw
  have hratio : 0 ≤ Real.sqrt T / L := div_nonneg (Real.sqrt_nonneg T) hL.le
  calc
    _ ≤ 4 * E * V * (Real.sqrt T / L) := hnormalized
    _ ≤ 4 * ((D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂) * V *
        (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hV) hratio
    _ = (4 * (D₁ + D₂) * V) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ *
        (Real.sqrt T / L) := by ring
    _ ≤ C * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ * (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hz) (by positivity)) hratio

def rowTwistedSum (η : Character) (m A₀ z : O) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A₀*z)) I)*
    (Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)

theorem rowTwistedSum_eq (η χ : Character) (m A₀ z : O)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W : ℝ → ℂ) (t X : ℝ) :
    rowTwistedSum η m A₀ z W t X=twistedIdealSum χ W t X := by
  apply tsum_congr
  intro I
  have he := HeckeRowClosure.idealCoeff_eq_row η χ m 1 (A₀*z) hrow I
  simp only [one_pow,mul_one] at he
  rw [he]

theorem exceptional_rectangle_estimate (Q : Ideal O) (hQ : Q ≠ 0)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (η : Character) (m A₀ z : O),
      m ≠ 0 → A₀ ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A₀*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A₀ z W₁ t X₁*rowTwistedSum η m A₀ z W₂ t X₂-
         rowTwistedSum η m A₀ z W₁ t Y₁*rowTwistedSum η m A₀ z W₂ t Y₂)‖ ≤
        C*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,hJ⟩ := normalized_actual_rectangle_estimate Q hQ a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ η m A₀ z hm hA hz hmLam hm2 hcond hex t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  obtain ⟨χ,ψ,hχ,hprim,hind,hQψ,hrow⟩ := fixedInducingRow_controlled η Q m A₀ z hm hA hz hmLam hm2 hex
  have hχnorm : (Ideal.absNorm χ.modulus:ℝ) ≤ Z^B :=
    (show (Ideal.absNorm χ.modulus:ℝ) ≤ HeckeRowClosure.rowConductorBound η m 1 (A₀*z) by exact_mod_cast hχ).trans hcond
  simp_rw [rowTwistedSum_eq η χ m A₀ z hrow]
  exact hbound Z hZ η χ ψ hχnorm hQψ hind m A₀ z hmLam hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

end SevenEighths.CenteredMomentHeckeHeight

end

end OAI

end Source392

/- Original source: OAI/NumberTheory/DirichletL/Moments/HeckeSlots.lean; sha256: 6ffc5659cfaa00feeebb1e7e9ca65b44de7071b460346cbeb28381f9b17d9c8d -/
section Source393
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeSlots
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentCounting CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

def rowSlot (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t : ℝ) : ℂ :=
  ∑ P ∈ S, β P * (idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
    (Ideal.absNorm P:ℂ)^(Complex.I*t)

theorem row_twisted_coefficient_norm (η : Character) (m A z : O) (t : ℝ)
    (P : Ideal O) (hP : P ≠ 0) :
    ‖(idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
      (Ideal.absNorm P:ℂ)^(Complex.I*t)‖ ≤ 1 := by
  have hn : 0 < (Ideal.absNorm P:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  rw [norm_mul, norm_mul, show (Ideal.absNorm P:ℂ)=((Ideal.absNorm P:ℝ):ℂ) by simp,
    norm_real_imaginary_power _ t hn, mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η P)).trans
    (CanonicalRowCompletion.idealRowHom_norm _ _)

theorem rowSlot_bound (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hβ : ∀ P ∈ S, ‖β P‖ ≤ M)
    (hN : ∀ P ∈ S, β P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ H) :
    ‖rowSlot η m A z S β t‖ ≤ 128*M*H := by
  let f : Ideal O → ℂ := fun P => if P ∈ S then
    β P * (idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
      (Ideal.absNorm P:ℂ)^(Complex.I*t) else 0
  have hf0 : f 0=0 := by simp only [f, map_zero, zero_mul, mul_zero, ite_self]
  have hf : ∀ P, ‖f P‖ ≤ M := by
    intro P
    by_cases hP : P ∈ S
    · by_cases hP0 : P=0
      · rw [hP0,hf0,norm_zero]; exact hM
      · dsimp only [f]; rw [ite_eq_left hP, mul_assoc, norm_mul]
        exact (mul_le_mul (hβ P hP) (row_twisted_coefficient_norm η m A z t P hP0)
          (norm_nonneg _) hM).trans_eq (mul_one M)
    · simp only [f,ite_eq_right hP,norm_zero]; exact hM
  have hsup : ∀ P, f P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ H := by
    intro P hP
    have hm : P ∈ S := by by_contra hn; exact hP (by simp only [f,ite_eq_right hn])
    exact hN P hm (by intro hz; exact hP (by simp only [f,ite_eq_left hm,hz,zero_mul]))
  have he : (∑' P, f P)=rowSlot η m A z S β t := by
    rw [tsum_eq_sum (s := S) (fun P hP => by simp only [f,ite_eq_right hP])]
    unfold rowSlot
    exact Finset.sum_congr rfl (fun P hP => by simp only [f,ite_eq_left hP])
  rw [← he]
  exact norm_tsum_ideal_ball f H M hH hM hf0 hf hsup

variable {ι : Type*} [Fintype ι]

theorem whole_product_normalization (R : ℂ) (q : ι → ℂ) (k p : ι → ℝ)
    (D T L : ℝ) (hD : 0 ≤ D) (hT : 0 < T) (hL : 0 < L)
    (_hk : ∀ i, 0 ≤ k i) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, ‖q i‖ ≤ k i*p i)
    (hR : ‖(Real.sqrt T:ℂ)⁻¹*R‖ ≤ D*(Real.sqrt T/L)) :
    ‖(Real.sqrt (T*∏ i,p i):ℂ)⁻¹*(R*∏ i,q i)‖ ≤
      D*(∏ i,k i)*(Real.sqrt (T*∏ i,p i)/L) := by
  have hP : 0 < ∏ i,p i := Finset.prod_pos (fun i _ => hp i)
  have hTP : 0 < T*∏ i,p i := mul_pos hT hP
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hsTP : 0 < Real.sqrt (T*∏ i,p i) := Real.sqrt_pos.2 hTP
  have hQ : ‖∏ i,q i‖ ≤ (∏ i,k i)*(∏ i,p i) := by
    rw [norm_prod,← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hq i)
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsT.le] at hR
  have hR' : ‖R‖ ≤ D*T/L := by
    have h := mul_le_mul_of_nonneg_left hR hsT.le
    rw [← mul_assoc,mul_inv_cancel₀ hsT.ne',one_mul] at h
    have hs := Real.sq_sqrt hT.le
    convert h using 1
    calc
      D*T/L = D*(Real.sqrt T)^2/L := by rw [hs]
      _ = _ := by ring
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsTP.le,norm_mul]
  calc
    _ ≤ (Real.sqrt (T*∏ i,p i))⁻¹*((D*T/L)*((∏ i,k i)*(∏ i,p i))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hR' hQ (norm_nonneg _) (by positivity)) (inv_nonneg.mpr hsTP.le)
    _ = _ := by
      have hs := Real.sq_sqrt hTP.le
      field_simp
      rw [hs]

def centeredSlotRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (p : ι → ℝ) (t X₁ X₂ Y₁ Y₂ T : ℝ) : ℂ :=
  (Real.sqrt (T*∏ i,p i):ℂ)⁻¹ *
    ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
      rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)*
      ∏ i,rowSlot η m A z (S i) (β i) t)

theorem exceptional_slots_estimate (Q : Ideal O) (hQ : Q ≠ 0)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (η : Character) (m A z : O),
      m ≠ 0 → A ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀ (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (p b M : ι → ℝ),
      (∀ i, 0 < p i) → (∀ i, 0 ≤ b i) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ P ∈ S i, ‖β i P‖ ≤ M i) →
      (∀ i, ∀ P ∈ S i, β i P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ b i*p i) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z W₁ W₂ S β p t X₁ X₂ Y₁ Y₂ T‖ ≤
        C*Z^ε*(1+‖t‖)^J*(∏ i,128*b i*M i)*(Real.sqrt (T*∏ i,p i)/L) := by
  obtain ⟨J,hJ⟩ := exceptional_rectangle_estimate Q hQ a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ η m A z hm hA hz hmLam hm2 hcond hex S β p b M hp hb hM hβ hN
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) t‖ ≤ (128*b i*M i)*p i := by
    convert rowSlot_bound η m A z (S i) (β i) t (b i*p i) (M i)
      (mul_nonneg (hb i) (hp i).le) (hM i) (hβ i) (hN i) using 1 ; ring
  exact whole_product_normalization _ (fun i => rowSlot η m A z (S i) (β i) t)
    (fun i => 128*b i*M i) p (C*Z^ε*(1+‖t‖)^J) T L
    (by positivity) hT hL (fun i => mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hp hslots
    (hbound Z hZ η m A z hm hA hz hmLam hm2 hcond hex
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentHeckeSlots

end

end OAI

end Source393

/- Original source: OAI/NumberTheory/DirichletL/Moments/Rectangle.lean; sha256: ab9b973e9c4255c9c50e939222121820191a6fd6a72e0e74514bd1248320fba5 -/
section Source394
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentRectangle
open CenteredMomentPrimary CenteredMomentMask CenteredMomentTwist

def idealWeight (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (I : Ideal O) : ℂ :=
  (if IsCoprime I R then (1 : ℂ) else 0) *
    primaryIdealCharacter c χ I * (Ideal.absNorm I : ℂ) ^ (Complex.I * t)

theorem idealWeight_mul (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (I J : Ideal O) :
    idealWeight c χ R t (I * J) = idealWeight c χ R t I * idealWeight c χ R t J := by
  have hpow : ((Ideal.absNorm I : ℂ) * (Ideal.absNorm J : ℂ)) ^ (Complex.I * t) =
      (Ideal.absNorm I : ℂ) ^ (Complex.I * t) * (Ideal.absNorm J : ℂ) ^ (Complex.I * t) := by
    exact_mod_cast Complex.mul_cpow_ofReal_nonneg
      (Nat.cast_nonneg (Ideal.absNorm I) : (0 : ℝ) ≤ Ideal.absNorm I)
      (Nat.cast_nonneg (Ideal.absNorm J) : (0 : ℝ) ≤ Ideal.absNorm J) (Complex.I * t)
  simp only [idealWeight, map_mul, Nat.cast_mul, hpow, IsCoprime.mul_left_iff]
  by_cases hI : IsCoprime I R <;> by_cases hJ : IsCoprime J R <;> simp [hI, hJ] ; ring

def idealRectangle (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (I J : Ideal O) : ℂ :=
  W₁ ((Ideal.absNorm I : ℝ) / X₁) * W₂ ((Ideal.absNorm J : ℝ) / X₂) -
    W₁ ((Ideal.absNorm I : ℝ) / Y₁) * W₂ ((Ideal.absNorm J : ℝ) / Y₂)

theorem twistedMaskedSum_eq_weight (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (W : ℝ → ℂ) (X : ℝ) :
    twistedMaskedSum c χ R W t X =
      ∑' I : Ideal O, idealWeight c χ R t I * W ((Ideal.absNorm I : ℝ) / X) := by
  apply tsum_congr
  intro I
  unfold idealWeight
  ring

theorem actual_rectangle_sum
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O, ∑' J : Ideal O,
      idealWeight c χ R t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      twistedMaskedSum c χ R W₁ t X₁ * twistedMaskedSum c χ R W₂ t X₂ -
        twistedMaskedSum c χ R W₁ t Y₁ * twistedMaskedSum c χ R W₂ t Y₂ := by
  let w := idealWeight c χ R t
  let f₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / X₁)
  let f₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / X₂)
  let g₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / Y₁)
  let g₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / Y₂)
  have hf₁ : Summable f₁ := annular_ideal_sum_summable w W₁ b₁ X₁ hX₁ hs₁
  have hf₂ : Summable f₂ := annular_ideal_sum_summable w W₂ b₂ X₂ hX₂ hs₂
  have hg₁ : Summable g₁ := annular_ideal_sum_summable w W₁ b₁ Y₁ hY₁ hs₁
  have hg₂ : Summable g₂ := annular_ideal_sum_summable w W₂ b₂ Y₂ hY₂ hs₂
  have hterm (I J : Ideal O) :
      idealWeight c χ R t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        f₁ I * f₂ J - g₁ I * g₂ J := by
    rw [idealWeight_mul]
    dsimp only [idealRectangle, f₁, f₂, g₁, g₂, w]
    ring
  simp_rw [hterm]
  have hinner (I : Ideal O) : (∑' J : Ideal O, (f₁ I * f₂ J - g₁ I * g₂ J)) =
      f₁ I * (∑' J : Ideal O, f₂ J) - g₁ I * (∑' J : Ideal O, g₂ J) := by
    rw [Summable.tsum_sub (hf₂.mul_left _) (hg₂.mul_left _), tsum_mul_left, tsum_mul_left]
  simp_rw [hinner]
  rw [Summable.tsum_sub (hf₁.mul_right _) (hg₁.mul_right _), tsum_mul_right, tsum_mul_right]
  simp only [twistedMaskedSum_eq_weight]
  rfl

end SevenEighths.CenteredMomentRectangle
end

end OAI

end Source394

/- Original source: OAI/NumberTheory/DirichletL/Moments/Extraction.lean; sha256: 61ef32b1cc86714301ad0f18867afd8621877155e34bbed925a875b8655115cc -/
section Source395
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentExtraction
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist

theorem idealRectangle_extract (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ I J : Ideal O) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J) =
      idealRectangle W₁ W₂
        (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
        (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J := by
  simp only [idealRectangle, map_mul, Nat.cast_mul, div_div_eq_mul_div]
  congr 2 <;> congr 1 <;> ring

theorem extracted_rectangle_coefficient (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (P B₁ B₂ I J : Ideal O) :
    idealWeight c χ R t (P * (B₁ * I) * (B₂ * J)) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J) =
      idealWeight c χ R t (P * B₁ * B₂) *
        (idealWeight c χ R t (I * J) *
          idealRectangle W₁ W₂
            (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
            (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J) := by
  rw [idealRectangle_extract]
  simp only [idealWeight_mul]
  ring

theorem extracted_rectangle_sum (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (P B₁ B₂ : Ideal O) :
    (∑' I : Ideal O, ∑' J : Ideal O,
      idealWeight c χ R t (P * (B₁ * I) * (B₂ * J)) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J)) =
      idealWeight c χ R t (P * B₁ * B₂) *
        ∑' I : Ideal O, ∑' J : Ideal O,
          idealWeight c χ R t (I * J) * idealRectangle W₁ W₂
            (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
            (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J := by
  simp_rw [extracted_rectangle_coefficient, tsum_mul_left]

theorem extracted_product_scale (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁ * X₂ = T) (hY : Y₁ * Y₂ = T) :
    (X₁ / Ideal.absNorm B₁) * (X₂ / Ideal.absNorm B₂) =
      T / (Ideal.absNorm B₁ * Ideal.absNorm B₂ : ℝ) ∧
    (Y₁ / Ideal.absNorm B₁) * (Y₂ / Ideal.absNorm B₂) =
      T / (Ideal.absNorm B₁ * Ideal.absNorm B₂ : ℝ) := by
  simp only [div_mul_div_comm, hX, hY, and_self]

theorem idealWeight_norm_le_one (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (I : Ideal O) (hI : I ≠ 0) : ‖idealWeight c χ R t I‖ ≤ 1 := by
  have hnorm : (0 : ℝ) < Ideal.absNorm I := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hpow := norm_real_imaginary_power (Ideal.absNorm I : ℝ) t hnorm
  norm_cast at hpow
  simp only [idealWeight, norm_mul, hpow, mul_one]
  by_cases hcop : IsCoprime I R
  · simpa only [hcop, ite_true, norm_one, one_mul] using primaryIdealCharacter_norm_le_one c hc χ I
  · simp only [hcop, ite_false, norm_zero, zero_mul, zero_le_one]

theorem normalized_extracted_rectangle_estimate
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ K : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal O, R ≠ 0 → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ P B₁ B₂ : Ideal O, P ≠ 0 → B₁ ≠ 0 → B₂ ≠ 0 →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ / Ideal.absNorm B₁ → L ≤ X₂ / Ideal.absNorm B₂ →
      L ≤ Y₁ / Ideal.absNorm B₁ → L ≤ Y₂ / Ideal.absNorm B₂ →
      X₁ * X₂ = T → Y₁ * Y₂ = T →
      let T' := T / (Ideal.absNorm B₁ * Ideal.absNorm B₂ : ℝ)
      ‖(Real.sqrt T' : ℂ)⁻¹ *
        (∑' I : Ideal O, ∑' J : Ideal O,
          idealWeight c χ R t (P * (B₁ * I) * (B₂ * J)) *
            idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J))‖ ≤
        C * Z ^ ε * (1 + ‖t‖) ^ K * (Real.sqrt T' / L) := by
  obtain ⟨K, hK⟩ := CenteredMomentHeight.normalized_masked_rectangle_estimate
    c hc h3 χ a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨K, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C, hC, hbound⟩ := hK W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm P B₁ B₂ hP hB₁ hB₂ t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  dsimp only
  obtain ⟨heqX, heqY⟩ := extracted_product_scale X₁ X₂ Y₁ Y₂ T B₁ B₂ hpX hpY
  have hraw := hbound Z hZ R hR hnorm t
    (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
    (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂)
    (T / (Ideal.absNorm B₁ * Ideal.absNorm B₂ : ℝ)) L hL hX₁ hX₂ hY₁ hY₂ heqX heqY
  rw [extracted_rectangle_sum, actual_rectangle_sum c χ R t W₁ W₂ b₁ b₂
    (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
    (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂)
    (fun x hx => (hs₁ hx).2) (fun x hx => (hs₂ hx).2)
    (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
    (lt_of_lt_of_le hL hY₁) (lt_of_lt_of_le hL hY₂)]
  have hw := idealWeight_norm_le_one c hc χ R t (P * B₁ * B₂)
    (mul_ne_zero (mul_ne_zero hP hB₁) hB₂)
  rw [mul_left_comm, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans hraw

theorem centered_slot_allocation {ι : Type*} (T : Finset ι)
    (p : ι → Ideal O) (ν : ι → ℂ) (S : Finset (Ideal O))
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ I J : Ideal O) :
    let F := T.filter (fun i => p i ∈ S)
    let L := T.filter (fun i => p i ∉ S)
    (∏ i ∈ T, ν i) *
      (idealWeight c χ R t ((∏ i ∈ T, p i) * (B₁ * I) * (B₂ * J)) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J)) =
      ((∏ i ∈ F, ν i) * idealWeight c χ R t ((∏ i ∈ F, p i) * B₁ * B₂)) *
        ((∏ i ∈ L, ν i) *
          (idealWeight c χ R t ((∏ i ∈ L, p i) * I * J) *
            idealRectangle W₁ W₂
              (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
              (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J)) := by
  dsimp only
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun i => p i ∈ S) ν,
    ← Finset.prod_filter_mul_prod_filter_not T (fun i => p i ∈ S) p,
    idealRectangle_extract]
  simp only [idealWeight_mul]
  ring

theorem prime_slot_allocation {ι : Type*} (T : Finset ι)
    (p : ι → Ideal O) (hp : ∀ i ∈ T, Prime (p i)) (S : Finset (Ideal O)) :
    CenteredMomentSupport.supportExtract (∏ i ∈ T, p i) S =
        ∏ i ∈ T.filter (fun i => p i ∈ S), p i ∧
      CenteredMomentSupport.supportResidual (∏ i ∈ T, p i) S =
        ∏ i ∈ T.filter (fun i => p i ∉ S), p i := by
  rw [CenteredMomentSupport.supportExtract_prod T p (fun i hi => (hp i hi).ne_zero) S,
    CenteredMomentSupport.supportResidual_prod T p (fun i hi => (hp i hi).ne_zero) S]
  constructor
  · rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    exact CenteredMomentSupport.supportExtract_prime (p i) (hp i hi) S
  · rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    rw [CenteredMomentSupport.supportResidual_prime (p i) (hp i hi) S]
    split_ifs <;> rfl

end SevenEighths.CenteredMomentExtraction
end

end OAI

end Source395

/- Original source: OAI/NumberTheory/DirichletL/Moments/HeckeExpansion.lean; sha256: ec6c0372863b81a30c6868959da1062567506f318d9b90d3b1b2aefcbc00f264 -/
section Source396
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeExpansion
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist CenteredMomentMask
local notation "O" => ActualEisensteinCubic.O

def rowWeight (η : Character) (m A z : O) (t : ℝ) : Ideal O →*₀ ℂ where
  toFun I := (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)*
    (Ideal.absNorm I:ℂ)^(Complex.I*t)
  map_one' := by simp only [map_one,Nat.cast_one,Complex.one_cpow,one_mul]
  map_zero' := by simp only [map_zero,zero_mul,mul_zero]
  map_mul' I J := by
    have hpow : ((Ideal.absNorm I:ℂ)*(Ideal.absNorm J:ℂ))^(Complex.I*t) =
        (Ideal.absNorm I:ℂ)^(Complex.I*t)*(Ideal.absNorm J:ℂ)^(Complex.I*t) := by
      exact_mod_cast Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg (Ideal.absNorm I) : (0:ℝ) ≤ Ideal.absNorm I)
        (Nat.cast_nonneg (Ideal.absNorm J) : (0:ℝ) ≤ Ideal.absNorm J) (Complex.I*t)
    simp only [map_mul,Nat.cast_mul,hpow]
    ring

theorem rowTwistedSum_eq_weight (η : Character) (m A z : O) (t : ℝ) (W : ℝ → ℂ) (X : ℝ) :
    rowTwistedSum η m A z W t X =
      ∑' I : Ideal O, rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) := rfl

theorem rowSlot_eq_weight (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t : ℝ) :
    rowSlot η m A z S β t = ∑ P ∈ S, β P*rowWeight η m A z t P := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro P hP
  simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk]
  ring

theorem actual_hecke_rectangle_sum
    (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O, ∑' J : Ideal O,
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      rowTwistedSum η m A z W₁ t X₁ * rowTwistedSum η m A z W₂ t X₂ -
        rowTwistedSum η m A z W₁ t Y₁ * rowTwistedSum η m A z W₂ t Y₂ := by
  let w := rowWeight η m A z t
  let f₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / X₁)
  let f₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / X₂)
  let g₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / Y₁)
  let g₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / Y₂)
  have hf₁ : Summable f₁ := annular_ideal_sum_summable w W₁ b₁ X₁ hX₁ hs₁
  have hf₂ : Summable f₂ := annular_ideal_sum_summable w W₂ b₂ X₂ hX₂ hs₂
  have hg₁ : Summable g₁ := annular_ideal_sum_summable w W₁ b₁ Y₁ hY₁ hs₁
  have hg₂ : Summable g₂ := annular_ideal_sum_summable w W₂ b₂ Y₂ hY₂ hs₂
  have hterm (I J : Ideal O) :
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        f₁ I * f₂ J - g₁ I * g₂ J := by
    rw [map_mul]
    dsimp only [idealRectangle, f₁, f₂, g₁, g₂, w]
    ring
  simp_rw [hterm]
  have hinner (I : Ideal O) : (∑' J : Ideal O, (f₁ I * f₂ J - g₁ I * g₂ J)) =
      f₁ I * (∑' J : Ideal O, f₂ J) - g₁ I * (∑' J : Ideal O, g₂ J) := by
    rw [Summable.tsum_sub (hf₂.mul_left _) (hg₂.mul_left _), tsum_mul_left, tsum_mul_left]
  simp_rw [hinner]
  rw [Summable.tsum_sub (hf₁.mul_right _) (hg₁.mul_right _), tsum_mul_right, tsum_mul_right]
  simp only [rowTwistedSum_eq_weight]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem live_slot_product (η : Character) (m A z : O) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (t : ℝ) :
    (∏ i,rowSlot η m A z (S i) (β i) t) =
      ∑ v : (i : ι) → S i, (∏ i,β i (v i))*rowWeight η m A z t (∏ i,(v i:Ideal O)) := by
  have hs (i : ι) : rowSlot η m A z (S i) (β i) t =
      ∑ P : S i, β i P*rowWeight η m A z t P := by
    rw [rowSlot_eq_weight]
    exact (Finset.sum_coe_sort (S i) (fun P => β i P*rowWeight η m A z t P)).symm
  simp_rw [hs]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_prod,← Finset.prod_mul_distrib]

theorem actual_slot_rectangle_sum (η : Character) (m A z : O)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal O, ∑' J : Ideal O,
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)*
       ∏ i,rowSlot η m A z (S i) (β i) t := by
  have ht (v : (i : ι) → S i) (I J : Ideal O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        rowWeight η m A z t (∏ i,(v i:Ideal O))*
          (rowWeight η m A z t (I*J)*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) := by
    simp only [map_mul]; ring
  simp_rw [ht,tsum_mul_left]
  rw [actual_hecke_rectangle_sum η m A z t W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂,
    live_slot_product]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem common_extracted_slot_rectangle (η : Character) (m A z : O)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal O, ∑' J : Ideal O,
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)) =
      rowWeight η m A z t (B₁*B₂)*
        ∑ v : (i : ι) → S i, (∏ i,β i (v i))*
          ∑' I : Ideal O, ∑' J : Ideal O,
            rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
              idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
                (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J := by
  have ht (v : (i : ι) → S i) (I J : Ideal O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J) =
      rowWeight η m A z t (B₁*B₂)*
        (rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
            (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J) := by
    rw [CenteredMomentExtraction.idealRectangle_extract]
    simp only [map_mul]
    ring
  simp_rw [ht,tsum_mul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

end SevenEighths.CenteredMomentHeckeExpansion

end

end OAI

end Source396

/- Original source: OAI/NumberTheory/DirichletL/Moments/MobiusRegroup.lean; sha256: 30326a9df8798a1ffd91c03643d6c82f0d94705da578699d9af0861b3d7e923d -/
section Source397
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentMobiusRegroup
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentMask
local notation "O" => ActualEisensteinCubic.O

def divisorPool {β : Type*} (T : Finset β) (B : β → Ideal O) : Finset (Ideal O) :=
  T.biUnion (fun j => idealDivisors (B j))

theorem mobius_on_pool {β : Type*} (T : Finset β) (B : β → Ideal O)
    (hB : ∀ j ∈ T, B j ≠ 0) (j : β) (hj : j ∈ T) (I : Ideal O) :
    (if IsCoprime I (B j) then (1 : ℂ) else 0) =
      ∑ D ∈ divisorPool T B, if D ∣ I ∧ D ∣ B j then (moebius D : ℂ) else 0 := by
  rw [ideal_coprime_mobius I (B j) (hB j hj)]
  have hsub : idealDivisors (B j) ⊆ divisorPool T B :=
    fun D hD => Finset.mem_biUnion.mpr ⟨j,hj,hD⟩
  calc
    _ = ∑ D ∈ idealDivisors (B j), if D ∣ I ∧ D ∣ B j then (moebius D : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro D hD
      simp only [(mem_idealDivisors (hB j hj)).mp hD, and_true]
    _ = _ := Finset.sum_subset hsub (by
      intro D hD hn
      have hnd : ¬ D ∣ B j := fun hd => hn ((mem_idealDivisors (hB j hj)).mpr hd)
      simp only [hnd, and_false, ite_false])

theorem finite_pair_mobius {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → Ideal O) (B : β → Ideal O) (hB : ∀ j ∈ T, B j ≠ 0)
    (F : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if IsCoprime (A i) (B j) then F i j else 0) =
      ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
        ∑ i ∈ S, ∑ j ∈ T, if D ∣ A i ∧ D ∣ B j then F i j else 0 := by
  have ht (i : α) (j : β) (hj : j ∈ T) :
      (if IsCoprime (A i) (B j) then F i j else 0) =
        ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
          (if D ∣ A i ∧ D ∣ B j then F i j else 0) := by
    have hm := congrArg (fun z : ℂ => z * F i j) (mobius_on_pool T B hB j hj (A i))
    simpa only [ite_mul, one_mul, zero_mul, Finset.sum_mul, mul_ite, mul_zero] using hm
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
        (if D ∣ A i ∧ D ∣ B j then F i j else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact ht i j hj
    _ = _ := by
      simp_rw [Finset.sum_comm (s := T) (t := divisorPool T B)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro D hD
      simp only [Finset.mul_sum]

open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation

theorem finite_correlation_mobius {α β : Type*} (S : Finset α) (T : Finset β)
    (D E : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a i - 1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b j - 1)
    (hcopA : ∀ i, IsCoprime (D * E) (a i)) (hcopB : ∀ j, IsCoprime (D * E) (b j))
    (h : O) (c : α → ℂ) (d : β → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D * a i) (E * b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) h
       else 0) * (c i * star (d j)) * K i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}), (moebius L : ℂ) *
        ∑ i ∈ S, ∑ j ∈ T,
          if L ∣ Ideal.span {a i} ∧ L ∣ Ideal.span {b j} then
            completeSupportExtension D E hD hE h (a i) (b j) * (c i * star (d j)) * K i j
          else 0 := by
  have he (i : α) (j : β) :
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D * a i) (E * b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) h
       else 0) * (c i * star (d j)) * K i j =
      if IsCoprime (Ideal.span {a i}) (Ideal.span {b j}) then
        completeSupportExtension D E hD hE h (a i) (b j) * (c i * star (d j)) * K i j else 0 := by
    rw [Ideal.isCoprime_span_singleton_iff]
    by_cases hab : IsCoprime (a i) (b j)
    · rw [ite_eq_left hab, ite_eq_left hab, actual_complete_common_support D E (a i) (b j)
        hD hE (ha i) (hb j) hpD hpE (hpa i) (hpb j) (hcopA i) (hcopB j) hab]
    · simp only [ite_eq_right hab, zero_mul]
  simp_rw [he]
  exact finite_pair_mobius S T (fun i => Ideal.span {a i}) (fun j => Ideal.span {b j})
    (fun j _ => (hb j).1) _

end SevenEighths.CenteredMomentMobiusRegroup

end

end OAI

end Source397

/- Original source: OAI/NumberTheory/DirichletL/Moments/DivisorAllocation.lean; sha256: d5197083ebb0e8133eeb36b7516732f029355ff02692059d904b0e2f7bb9de0e -/
section Source398
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorAllocation
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def nonemptySelections (s : Finset ι) : Finset (Finset ι) := s.powerset.erase ∅

omit [DecidableEq ι] in
theorem prime_complement (P : Ideal O) (hP : Prime P) (s : Finset ι) (v : ι → Ideal O) :
    (∏ i ∈ s, (1-(if P ∣ v i then (1:ℂ) else 0))) =
      if P ∣ ∏ i ∈ s,v i then 0 else 1 := by
  by_cases h : P ∣ ∏ i ∈ s,v i
  · rw [ite_eq_left h]
    obtain ⟨i,hi,hd⟩ := (hP.dvd_finsetProd_iff v).mp h
    exact Finset.prod_eq_zero hi (by simp only [ite_eq_left hd,sub_self])
  · rw [ite_eq_right h]
    apply Finset.prod_eq_one
    intro i hi
    have hd : ¬P∣v i := fun hh => h ((hP.dvd_finsetProd_iff v).mpr ⟨i,hi,hh⟩)
    simp only [ite_eq_right hd,sub_zero]

theorem prime_factor_allocation (P : Ideal O) (hP : Prime P)
    (s : Finset ι) (v : ι → Ideal O) :
    (if P ∣ ∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ J ∈ nonemptySelections s, (-1:ℂ)^(J.card+1)*
        ∏ i ∈ J, if P ∣ v i then (1:ℂ) else 0 := by
  let f := fun J : Finset ι => (-1:ℂ)^J.card*∏ i ∈ J,if P∣v i then (1:ℂ) else 0
  have he : (∑ J ∈ nonemptySelections s,f J)+1 =
      if P ∣ ∏ i ∈ s,v i then (0:ℂ) else 1 := by
    have hr := Finset.sum_erase_add s.powerset f (Finset.mem_powerset.mpr (Finset.empty_subset s))
    have hh := Finset.prod_sub (fun _i : ι => (1:ℂ))
      (fun i => if P∣v i then (1:ℂ) else 0) s
    simp only [Finset.prod_const_one,mul_one] at hh
    rw [prime_complement P hP s v] at hh
    simpa only [nonemptySelections,f,Finset.card_empty,pow_zero,Finset.prod_empty,one_mul] using hr.trans hh.symm
  have hn : (∑ J ∈ nonemptySelections s, (-1:ℂ)^(J.card+1)*
      ∏ i ∈ J,if P∣v i then (1:ℂ) else 0) = -(∑ J ∈ nonemptySelections s,f J) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [f]
    rw [pow_succ]
    ring
  rw [hn]
  by_cases h : P∣∏ i ∈ s,v i <;> simp only [h,ite_true,ite_false] at he ⊢ <;>
    linear_combination he

theorem squarefree_dvd_iff (D I : Ideal O) (hD : Squarefree D) :
    D∣I ↔ ∀ P ∈ primeSupport D,P∣I := by
  constructor
  · intro hd P hP
    exact (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)).trans hd
  · intro h
    rw [← squarefree_support_product_self hD]
    apply Finset.prod_dvd_of_coprime ?_ h
    intro P hP Q hQ hne
    let : P.IsMaximal := (Ideal.isPrime_of_prime (support_prime hP)).isMaximal (support_prime hP).ne_zero
    let : Q.IsMaximal := (Ideal.isPrime_of_prime (support_prime hQ)).isMaximal (support_prime hQ).ne_zero
    exact Ideal.isCoprime_of_isMaximal hne

abbrev Allocation (D : Ideal O) (s : Finset ι) :=
  (P : primeSupport D) → nonemptySelections s

def allocationTerm (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) : ℂ :=
  ∏ P : primeSupport D, (-1:ℂ)^((a P).val.card+1)*
    ∏ i ∈ (a P).val, if (P:Ideal O)∣v i then (1:ℂ) else 0

theorem squarefree_mask_allocation (D : Ideal O) (hD : Squarefree D)
    (s : Finset ι) (v : ι → Ideal O) :
    (if D∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ a : Allocation D s, allocationTerm D s v a := by
  have hprod : (if D∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∏ P : primeSupport D, if (P:Ideal O)∣∏ i ∈ s,v i then (1:ℂ) else 0 := by
    by_cases hd : D∣∏ i ∈ s,v i
    · rw [ite_eq_left hd]
      symm
      apply Finset.prod_eq_one
      intro P hP
      rw [ite_eq_left ((squarefree_dvd_iff _ _ hD).mp hd P P.property)]
    · rw [ite_eq_right hd]
      obtain ⟨P,hP,hnd⟩ := not_forall.mp (fun h => hd ((squarefree_dvd_iff _ _ hD).mpr h))
        |> fun h => by simpa only [not_forall,not_imp] using h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨P,hP⟩ : primeSupport D)) (by simp only [ite_eq_right hnd])
  rw [hprod]
  have hl (P : primeSupport D) :
      (if (P:Ideal O)∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ J : nonemptySelections s, (-1:ℂ)^(J.val.card+1)*
        ∏ i ∈ J.val, if (P:Ideal O)∣v i then (1:ℂ) else 0 := by
    rw [prime_factor_allocation P (support_prime P.property) s v]
    exact (Finset.sum_coe_sort (nonemptySelections s) (fun J =>
      (-1:ℂ)^(J.card+1)*∏ i ∈ J,if (P:Ideal O)∣v i then (1:ℂ) else 0)).symm
  simp_rw [hl]
  exact Fintype.prod_sum _

theorem allocationTerm_norm_le_one (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) : ‖allocationTerm D s v a‖ ≤ 1 := by
  unfold allocationTerm
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro P hP
  rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i hi
  split_ifs <;> norm_num

theorem allocation_card_bound (D : Ideal O) (s : Finset ι) :
    Fintype.card (Allocation D s) ≤ (2^(primeSupport D).card)^s.card := by
  have hc : (nonemptySelections s).card ≤ 2^s.card := by
    simpa only [nonemptySelections,Finset.card_powerset] using
      (Finset.card_erase_le (s := s.powerset) (a := (∅:Finset ι)))
  change Fintype.card (primeSupport D → nonemptySelections s) ≤ _
  simp only [Fintype.card_fun,Fintype.card_coe]
  calc
    _ ≤ (2^s.card)^(primeSupport D).card := Nat.pow_le_pow_left hc _
    _ = _ := by simp only [← pow_mul,Nat.mul_comm]

theorem allocation_mass_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), D ≠ 0 → ∀ s : Finset ι, s.card ≤ N →
      ∀ v : ι → Ideal O, (∑ a : Allocation D s, ‖allocationTerm D s v a‖) ≤
        C*(Ideal.absNorm D:ℝ)^ε := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/N) (div_pos hε hNr)
  refine ⟨C^N,pow_pos hC _,?_⟩
  intro D hD s hs v
  have hn : 0 ≤ (Ideal.absNorm D:ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ∑ _a : Allocation D s,(1:ℝ) := Finset.sum_le_sum (fun a _ => allocationTerm_norm_le_one D s v a)
    _ = (Fintype.card (Allocation D s):ℝ) := by simp
    _ ≤ ((2:ℝ)^(primeSupport D).card)^s.card := by exact_mod_cast allocation_card_bound D s
    _ ≤ ((2:ℝ)^(primeSupport D).card)^N := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hs
    _ ≤ (C*(Ideal.absNorm D:ℝ)^(ε/N))^N := pow_le_pow_left₀ (by positivity) (hb D hD) N
    _ = C^N*(Ideal.absNorm D:ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hn]
      congr 2
      field_simp

end SevenEighths.CenteredMomentDivisorAllocation

end

end OAI

end Source398

/- Original source: OAI/NumberTheory/DirichletL/Moments/DivisorExtraction.lean; sha256: d4facecfb46c7e1aa1e52f3a515db0564aee71b0147fedea97c164010e05b01e -/
section Source399
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorExtraction
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def selectedPrimes (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    Finset (primeSupport D) := Finset.univ.filter (fun P => i ∈ (a P).val)

def selectedDivisor (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) : Ideal O :=
  ∏ P ∈ selectedPrimes D s a i, (P:Ideal O)

theorem selected_divides_factor (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) : (P:Ideal O)∣v i := by
  have hP := (Finset.prod_ne_zero_iff.mp hn) P (Finset.mem_univ P)
  have hprod := (mul_ne_zero_iff.mp hP).2
  have hfactor := (Finset.prod_ne_zero_iff.mp hprod) i hi
  by_contra h
  exact hfactor (by simp only [ite_eq_right h])

theorem selectedDivisor_ne_zero (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    selectedDivisor D s a i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => (support_prime P.property).ne_zero)

theorem selectedDivisor_dvd (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) (i : ι) :
    selectedDivisor D s a i ∣ v i := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hne
    let : (P:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal
      (support_prime P.property).ne_zero
    let : (Q:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime Q.property)).isMaximal
      (support_prime Q.property).ne_zero
    exact Ideal.isCoprime_of_isMaximal (fun he => hne (Subtype.ext he))
  · intro P hP
    exact selected_divides_factor D s v a hn P i (Finset.mem_filter.mp hP).2

theorem exists_factor_quotients (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) :
    ∃ q : ι → Ideal O, ∀ i, v i=selectedDivisor D s a i*q i := by
  choose q hq using (fun i => selectedDivisor_dvd D s v a hn i)
  exact ⟨q,hq⟩

theorem selected_prime_slot (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) (hv : Prime (v i)) :
    v i=(P:Ideal O) :=
  ((prime_dvd_prime_iff_eq (support_prime P.property) hv).mp
    (selected_divides_factor D s v a hn P i hi)).symm

theorem double_selected_prime_slot_zero (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (P Q : primeSupport D) (hPQ : P ≠ Q)
    (i : ι) (hPi : i ∈ (a P).val) (hQi : i ∈ (a Q).val) (hv : Prime (v i)) :
    allocationTerm D s v a=0 := by
  by_contra hn
  apply hPQ
  apply Subtype.ext
  exact (selected_prime_slot D s v a hn P i hPi hv).symm.trans
    (selected_prime_slot D s v a hn Q i hQi hv)

end SevenEighths.CenteredMomentDivisorExtraction

end

end OAI

end Source399
