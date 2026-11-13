import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit018
import OpenAIGrouped.Unit008
import OpenAIGrouped.Unit015
import OpenAIGrouped.Unit013
import Mathlib.Analysis.InnerProductSpace.Calculus
import OpenAIGrouped.Unit017
import OpenAIGrouped.Unit016
import OpenAIGrouped.Unit009

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Hecke/RayQuotient.lean; sha256: 7eed3879d118ca87d25dfeb78babe3b7fc2b4204cb1cc32404aaf0203b23a3a6 -/
section Source760
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayQuotient
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def character (χ : RayQuotient.Characters M H) : Character :=
  HeckeRayFamily.character M (RayQuotient.toFullRay M H hH χ)

theorem idealCoeff_character (χ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (character M H hH χ) I = RayQuotient.idealCharacter M H hH χ I := rfl

theorem principal_iff (χ : RayQuotient.Characters M H) :
    (character M H hH χ).residue = 1 ↔ χ = 1 := by
  rw [character, HeckeRayFamily.principal_iff, RayQuotient.toFullRay_eq_one]

theorem character_entire (χ : RayQuotient.Characters M H) (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction (character M H hH χ)) :=
  LFunction_entire_nonprincipal _ (fun h => hχ ((principal_iff M H hH χ).mp h))

theorem character_boundary_ne_zero (χ : RayQuotient.Characters M H)
    {s : ℂ} (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ ≠ 1) :
    LFunction (character M H hH χ) s ≠ 0 := by
  apply LFunction_ne_zero_of_one_le_re _ hs
  exact hpole.imp id (fun h hn => h ((principal_iff M H hH χ).mp hn))

theorem principal_pole_ne_zero : HeckeOrigin.poleRemoved (character M H hH 1) 1 ≠ 0 :=
  HeckeOrigin.poleRemoved_one_ne_zero _ ((principal_iff M H hH 1).mpr rfl)

theorem average_idealCoeff (I : Ideal O) :
    (RayQuotient.classNumber M H : ℂ)⁻¹ *
      ∑ χ : RayQuotient.Characters M H, idealCoeff (character M H hH χ) I =
      if I ∈ RayQuotient.identityClass M H then 1 else 0 := by
  simp only [idealCoeff_character]
  simpa only [div_eq_mul_inv, mul_comm] using RayQuotient.average_idealCharacters M H hH I

theorem mangoldt_LSeries (χ : RayQuotient.Characters M H)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ)) s =
      (if χ = 1 then (1 : ℂ)/(s-1) else 0) +
        HeckeLogDerivative.poleSubtracted (character M H hH χ) s := by
  have h := HeckeLogDerivative.coeff_LSeries_eq_poleSubtracted (character M H hH χ) hs
  change LSeries (IdealLogDerivative.coeff (idealCoeff (character M H hH χ))) s = _ at h
  have heq : idealCoeff (character M H hH χ) = RayQuotient.idealCharacter M H hH χ := rfl
  rw [heq, principal_iff] at h
  by_cases hc : χ = 1 <;> simpa [hc] using h

theorem poleSubtracted_analyticAt (χ : RayQuotient.Characters M H)
    {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (HeckeLogDerivative.poleSubtracted (character M H hH χ)) s :=
  HeckeLogDerivative.poleSubtracted_analyticAt _ hs

end SevenEighths.HeckeRayQuotient

end

end OAI

end Source760

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeRay.lean; sha256: 262e079333d693fb895b4e64a929838af480c378e0e39b3e59de73a51436ed00 -/
section Source761
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.HeckePrimeRay
open HeckeFamily HeckePrimeAnnular
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def twistedFamily (η : Character) (θ : RayQuotient.Characters M H) : Character :=
  η.product (HeckeRayQuotient.character M H hH θ)

def rayPrimePolynomial (η : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ I∈(annulusSet b D).filter
    (fun I => Prime I ∧ I∈RayQuotient.identityClass M H),
      idealCoeff η I*annularWeight W D σ freq I

theorem finite_average (η : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑ I∈S.filter (fun I => I∈RayQuotient.identityClass M H), idealCoeff η I*f I) =
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H, ∑ I∈S,
          idealCoeff (twistedFamily M H hH η θ) I*f I := by
  rw [Finset.sum_filter,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  simp only [twistedFamily,idealCoeff_product]
  have hs : (∑ θ : RayQuotient.Characters M H,
      idealCoeff η I*idealCoeff (HeckeRayQuotient.character M H hH θ) I*f I) =
      (idealCoeff η I*f I)*∑ θ : RayQuotient.Characters M H,
        idealCoeff (HeckeRayQuotient.character M H hH θ) I := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro θ _
    ring
  rw [hs,mul_left_comm,HeckeRayQuotient.average_idealCoeff M H hH I]
  split_ifs <;> simp

theorem rayPrimePolynomial_eq_average (η : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) :
    rayPrimePolynomial M H η W b D σ freq =
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H,
          primePolynomial (twistedFamily M H hH η θ) W b D σ freq := by
  unfold rayPrimePolynomial
  have hfilter : (annulusSet b D).filter (fun I => Prime I ∧ I∈RayQuotient.identityClass M H) =
      ((annulusSet b D).filter Prime).filter (fun I => I∈RayQuotient.identityClass M H) := by
    ext I
    simp only [Finset.mem_filter]
    tauto
  rw [hfilter,finite_average M H hH η _ (annularWeight W D σ freq)]
  simp only [primePolynomial]
  rw [←Finset.mul_sum]
  ring

theorem rayPrimePolynomial_norm_le (η : Character) (W : ℝ→ℂ) (b D σ freq C : ℝ)
    (hbound : ∀ θ : RayQuotient.Characters M H,
      ‖primePolynomial (twistedFamily M H hH η θ) W b D σ freq‖≤C) :
    ‖rayPrimePolynomial M H η W b D σ freq‖≤C := by
  rw [rayPrimePolynomial_eq_average M H hH η W b D σ freq,norm_mul,norm_inv]
  have hcard : (0 : ℝ)<RayQuotient.classNumber M H := by
    exact_mod_cast RayQuotient.classNumber_pos M H
  have heq : Fintype.card (RayQuotient.Characters M H)=RayQuotient.classNumber M H :=
    RayOrthogonality.card_characters H
  have hn : ‖(RayQuotient.classNumber M H : ℂ)‖=(RayQuotient.classNumber M H : ℝ) := by simp
  rw [hn]
  calc
    _ ≤ (RayQuotient.classNumber M H : ℝ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H, C :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun θ _ => hbound θ)))
        (by positivity)
    _ = C := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,heq]; rw [←mul_assoc,inv_mul_cancel₀ hcard.ne',one_mul]

theorem ray_prime_bin_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (ηrow : Character) (hχ : ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH ηrow θ).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH ηrow) hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, 0≤r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      (∀ θ : RayQuotient.Characters M H,
        (twistedFamily M H hH ηrow θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖rayPrimePolynomial M H ηrow W B ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨C,hC,hbound⟩ := prime_bin_bound W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ hε he he' hκ hη hbudget
  refine ⟨C,hC,?_⟩
  intro Z d hZ hd hd' hU hT ηrow hχ a i ha ha' hmax r σ freq hr hrR
    hσmin hσmax hlarge hQ hfreq hheight
  apply rayPrimePolynomial_norm_le M H hH
  intro θ
  exact hbound Z d hZ hd hd' hU hT (twistedFamily M H hH ηrow) hχ a i ha ha' hmax
    r σ freq hr hrR hσmin hσmax hlarge θ (hQ θ) hfreq hheight

end SevenEighths.HeckePrimeRay

end

end OAI

end Source761

/- Original source: OAI/NumberTheory/DirichletL/Moments/RayNonprincipal.lean; sha256: 087a295b1eb697b449ab398e2254fd295ff23392e813fe545980712cf213df47 -/
section Source762
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRayNonprincipal
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion HeckePrimeRay
local notation "O" => HeckeFamily.O

theorem product_principal_descent (χ θ:Character)
    (hp:(χ.product θ).residue=1) :
    FiniteConductor.FactorsThroughIdeal χ.residue
      (θ.modulus.map (Ideal.Quotient.mk χ.modulus)) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  rw [FiniteConductor.factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨q,hq,hqu⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk χ.modulus) Ideal.Quotient.mk_surjective).mp hu
  let a:O := 1+q
  have ha:Ideal.Quotient.mk χ.modulus a=(u:O⧸χ.modulus) := by
    dsimp [a]; rw [map_add,map_one,hqu]; ring
  have hθa:Ideal.Quotient.mk θ.modulus a=1 := by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr hq,add_zero]
  have hcχ:IsCoprime (Ideal.span {a}) χ.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (ha ▸ u.isUnit)
  have hcθ:IsCoprime (Ideal.span {a}) θ.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hθa ▸ isUnit_one)
  have hcp:IsCoprime (Ideal.span {a}) (χ.product θ).modulus :=
    (hcχ.mul_right hcθ).of_isCoprime_of_dvd_right
      (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)
  have hv:elementCoeff (χ.product θ) a=1 := by
    change (χ.product θ).residue _=1
    rw [hp]
    exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hcp)
  rw [elementCoeff_product] at hv
  change χ.residue (Ideal.Quotient.mk χ.modulus a)*
    θ.residue (Ideal.Quotient.mk θ.modulus a)=1 at hv
  simpa only [ha,hθa,map_one,mul_one] using hv

theorem product_principal_inducing (χ θ:Character)
    (hp:(χ.product θ).residue=1) :
    ∃ψ:Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      θ.modulus≤ψ.modulus ∧ InducedBy χ ψ :=
  HeckeMaskDescent.exists_primitive_above χ θ.modulus
    (product_principal_descent χ θ hp)

theorem actual_row_twist_nonprincipal (η χ θ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hQ:Q≤θ.modulus) (hex:¬FixedInducingRow η Q m A z) :
    (χ.product θ).residue≠1 := by
  intro hp
  obtain ⟨ψ,hψ,hmod,hind⟩ := product_principal_inducing χ θ hp
  exact hex ⟨χ,ψ,hψ,hind,hQ.trans hmod,hrow⟩

variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

theorem all_ray_twists_nonprincipal (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hQ:Q≤M) (hex:¬FixedInducingRow η Q m A z) :
    ∀θ:RayQuotient.Characters M H, (twistedFamily M H hH χ θ).residue≠1 := by
  intro θ
  exact actual_row_twist_nonprincipal η χ (HeckeRayQuotient.character M H hH θ)
    Q m A z hrow hQ hex

end SevenEighths.CenteredMomentRayNonprincipal

end

end OAI

end Source762

/- Original source: OAI/NumberTheory/DirichletL/Moments/PrimeSlot.lean; sha256: e94a635d9180764a79bc5969c4ea75a0afc673494388add1d25dd99de2ea21b4 -/
section Source763
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlot
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
local notation "O" => HeckeFamily.O

def primePool (M:Ideal O) (H:Subgroup (O⧸M)ˣ) (b D:ℝ) : Finset (Ideal O) :=
  (annulusSet b D).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H)

def slotProfile (W:ℝ→ℂ) (D σ:ℝ) (I:Ideal O) : ℂ := annularWeight W D σ 0 I

lemma norm_height_split (N D σ t:ℝ) (hN:0<N) (hD:0<D) :
    (((N/D:ℝ):ℂ)^(-shift σ 0))*(N:ℂ)^(Complex.I*t)=
      (D:ℂ)^(Complex.I*t)*((N/D:ℝ):ℂ)^(-shift σ t) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    ←Complex.ofReal_log (div_pos hN hD).le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log hD.le,Real.log_div hN.ne' hD.ne',←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [HeckeDyadic.shift,Complex.ofReal_sub,Complex.ofReal_zero,zero_mul,sub_zero]
  ring

lemma sqrt_inverse_cpow (D:ℝ) (hD:0<D) :
    (Real.sqrt D:ℂ)⁻¹=(D:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hD.le (1/2:ℝ))

theorem normalizedSlot_eq_ray (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t:ℝ) (hD:0<D) :
    normalizedSlot η m A z (primePool M H b D) (slotProfile W D σ) t D=
      (D:ℂ)^(Complex.I*t)*rayPrimePolynomial M H χ W b D σ t := by
  unfold normalizedSlot rowSlot rayPrimePolynomial primePool
  rw [sqrt_inverse_cpow D hD]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hp:Prime I := (Finset.mem_filter.mp hI).2.1
  have hN:0<(I.absNorm:ℝ) := norm_pos ⟨I,hp.ne_zero⟩
  have hc:=idealCoeff_eq_row η χ m 1 (A*z) hrow I
  simp only [one_pow,mul_one] at hc
  rw [←hc]
  change (D:ℂ)^(-(1/2:ℂ))*
    ((W ((I.absNorm:ℝ)/D)*(((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ 0))*idealCoeff χ I*
      (I.absNorm:ℂ)^(Complex.I*t))=_
  have hn:=norm_height_split (I.absNorm:ℝ) D σ t hN hD
  simp only [Complex.ofReal_natCast] at hn
  calc
    _=(D:ℂ)^(-(1/2:ℂ))*(W ((I.absNorm:ℝ)/D)*idealCoeff χ I)*
      ((((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ 0)*(I.absNorm:ℂ)^(Complex.I*t)) := by ring
    _=_ := by rw [hn]; unfold annularWeight; ring

theorem normalizedSlot_norm_sq (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t:ℝ) (hD:0<D) :
    ‖normalizedSlot η m A z (primePool M H b D) (slotProfile W D σ) t D‖^2=
      ‖rayPrimePolynomial M H χ W b D σ t‖^2 := by
  rw [normalizedSlot_eq_ray M H η χ m A z hrow W b D σ t hD,norm_mul,
    norm_real_imaginary_power D t hD,one_mul]

end SevenEighths.CenteredMomentPrimeSlot

end

end OAI

end Source763

/- Original source: OAI/NumberTheory/DirichletL/Moments/PrimeSlotShift.lean; sha256: 4e01124feb01caec738881fff5b60338ecc998267cff570f6c984fe0555b130c -/
section Source764
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlotShift
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
open CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma norm_height_split (N D σ t v:ℝ) (hN:0<N) (hD:0<D) :
    (((N/D:ℝ):ℂ)^(-shift σ v))*(N:ℂ)^(Complex.I*t)=
      (D:ℂ)^(Complex.I*t)*((N/D:ℝ):ℂ)^(-shift σ (t+v)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    ←Complex.ofReal_log (div_pos hN hD).le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log hD.le,Real.log_div hN.ne' hD.ne',←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [HeckeDyadic.shift,Complex.ofReal_sub,Complex.ofReal_add]
  ring

theorem normalizedSlot_eq_ray (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t v:ℝ) (hD:0<D) :
    normalizedSlot η m A z (primePool M H b D) (annularWeight W D σ v) t D=
      (D:ℂ)^(Complex.I*t)*rayPrimePolynomial M H χ W b D σ (t+v) := by
  unfold normalizedSlot rowSlot rayPrimePolynomial primePool
  rw [sqrt_inverse_cpow D hD]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hp:Prime I := (Finset.mem_filter.mp hI).2.1
  have hN:0<(I.absNorm:ℝ) := norm_pos ⟨I,hp.ne_zero⟩
  have hc:=idealCoeff_eq_row η χ m 1 (A*z) hrow I
  simp only [one_pow,mul_one] at hc
  rw [←hc]
  change (D:ℂ)^(-(1/2:ℂ))*
    ((W ((I.absNorm:ℝ)/D)*(((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ v))*idealCoeff χ I*
      (I.absNorm:ℂ)^(Complex.I*t))=_
  have hn:=norm_height_split (I.absNorm:ℝ) D σ t v hN hD
  simp only [Complex.ofReal_natCast] at hn
  calc
    _=(D:ℂ)^(-(1/2:ℂ))*(W ((I.absNorm:ℝ)/D)*idealCoeff χ I)*
      ((((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ v)*(I.absNorm:ℂ)^(Complex.I*t)) := by ring
    _=_ := by rw [hn]; unfold annularWeight; ring

theorem normalizedSlot_norm_sq (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t v:ℝ) (hD:0<D) :
    ‖normalizedSlot η m A z (primePool M H b D) (annularWeight W D σ v) t D‖^2=
      ‖rayPrimePolynomial M H χ W b D σ (t+v)‖^2 := by
  rw [normalizedSlot_eq_ray M H η χ m A z hrow W b D σ t v hD,norm_mul,
    norm_real_imaginary_power D t hD,one_mul]

end SevenEighths.CenteredMomentPrimeSlotShift

end

end OAI

end Source764

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationEnergy.lean; sha256: 34813bee6e142bd8452de0e19980e2aa7176e21d564919e28893b500b0d55c73 -/
section Source765
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem prime_column_energy (χ ψ : Character) (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ true W D σ freq‖^2≤
      2*(‖polynomial ψ true W D σ freq‖^2+
        ‖polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq‖^2) := by
  have hN : (1 : ℝ)≤P.val.absNorm := by
    exact_mod_cast (show 1≤P.val.absNorm from (SmoothMobiusCorrection.prime_norm_two_le P).trans' (by norm_num))
  have hNp : (0 : ℝ)<P.val.absNorm := by linarith
  have hc : ‖idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))‖≤1 := by
    rw [norm_mul]
    have hh : ‖(P.val.absNorm : ℂ)^(-(1/2 : ℂ))‖≤1 := by
      change ‖((P.val.absNorm : ℝ) : ℂ)^(-(1/2 : ℂ))‖≤1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNp]
      norm_num
      exact Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (idealCoeff_norm_le_one χ P.val)).trans hh
  rw [prime_column_identity χ ψ P hm W a b ha hWs hW D σ freq hD]
  have hn := norm_sub_le (polynomial ψ true W D σ freq)
    (idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq)
  rw [norm_mul] at hn
  have hb := mul_le_of_le_one_left
    (norm_nonneg (polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq)) hc
  nlinarith [norm_nonneg (polynomial ψ true W D σ freq),
    norm_nonneg (polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq),
    norm_nonneg (polynomial ψ true W D σ freq-
      idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq),
    sq_nonneg (‖polynomial ψ true W D σ freq‖-
      ‖polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq‖)]

theorem finite_amplification (rows : Finset FreeRow) (multipliers : Finset NonzeroIdeal)
    (target : Finset O) (F : FreeRow→ℝ) (E : O→ℝ) (K : ℝ)
    (hK : 0≤K) (hE : ∀ u, 0≤E u)
    (hmap : ∀ u∈rows, ∀ A∈multipliers, rowMap (u,A)∈target)
    (hamp : ∀ u∈rows, ∀ A∈multipliers, F u≤K*E (rowMap (u,A))) :
    (multipliers.card : ℝ)*(∑ u∈rows, F u)≤K*∑ v∈target, E v := by
  have hs : (multipliers.card : ℝ)*(∑ u∈rows, F u)=
      ∑ p∈rows×ˢmultipliers, F p.1 := by
    rw [Finset.sum_product]
    simp only [Finset.sum_const,nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [hs]
  calc
    _ ≤ ∑ p∈rows×ˢmultipliers, K*E (rowMap p) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hu,hA⟩ := Finset.mem_product.mp hp
      exact hamp p.1 hu p.2 hA
    _ = K*∑ v∈(rows×ˢmultipliers).image rowMap, E v := by
      rw [Finset.mul_sum,Finset.sum_image]
      exact fun p hp q hq h => rowMap_injective h
    _ ≤ K*∑ v∈target, E v := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨hu,hA⟩ := Finset.mem_product.mp hp
        exact hmap p.1 hu p.2 hA
      · intro v hv hn
        exact hE v

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source765

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationFamily.lean; sha256: 9d1af7a50e0dcdda149b234c790aea46581a971ebb54f46881086ee986a097f4 -/
section Source766
namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeRowClosure
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
abbrev NonzeroElement := UnrestrictedIdealReindex.NonzeroElement

structure RowData where
  η : Character
  m : O
  f : O
  m_ne_zero : m≠0
  f_ne_zero : f≠0
  lambda_dvd : λ₀∣m
  two_dvd : (2 : O)∣m

def RowData.character (data : RowData) (u : NonzeroElement) : Character :=
  Classical.choose (exists_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd)

theorem RowData.character_spec (data : RowData) (u : NonzeroElement) (n : O) :
    elementCoeff (data.character u) n=
      CanonicalRowCompletion.rowTwist (elementHom data.η) data.m data.f u.val n :=
  Classical.choose_spec (exists_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd) n

def amplifiedElement (u : NonzeroElement) (A : NonzeroIdeal) : NonzeroElement :=
  ⟨u.val*(ConcretePrimeRowBridge.idealGenerator A.val)^6,
    mul_ne_zero u.property (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero A.val A.property))⟩

theorem RowData.amplified_prime_mask (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) :
    idealCoeff (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩))=
      IdealEuler.deletePrimes {P} (idealCoeff (data.character u)) := by
  exact amplified_row_prime_mask data.η (data.character u)
    (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) data.m data.f u.val
    (ConcretePrimeRowBridge.idealGenerator P.val) P
    (ConcretePrimeRowBridge.span_idealGenerator P.val)
    (data.character_spec u) (data.character_spec (amplifiedElement u ⟨P.val,P.property.ne_zero⟩))
    data.lambda_dvd data.two_dvd

theorem RowData.prime_column (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) (W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) :
    polynomial (data.character u) true W D σ freq=
      polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W D σ freq-
      idealCoeff (data.character u) P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*
        polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W
          (D/(P.val.absNorm : ℝ)) σ freq :=
  prime_column_identity _ _ P (data.amplified_prime_mask u P) W a b ha hWs hW D σ freq hD

theorem RowData.prime_energy (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) (W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial (data.character u) true W D σ freq‖^2≤
      2*(‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W D σ freq‖^2+
        ‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W
          (D/(P.val.absNorm : ℝ)) σ freq‖^2) :=
  prime_column_energy _ _ P (data.amplified_prime_mask u P) W a b ha hWs hW D σ freq hD

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source766

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorRowCount.lean; sha256: e9a384fe36df1591d34836022a452c23d79cc6918fbaa45363403b46efde5634 -/
section Source767
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRowCount
open HeckeFamily HeckeDyadic

lemma card_of_energy {α : Type*} (rows : Finset α) (F : α→ℂ)
    (U p b C : ℝ) (hU : 0<U)
    (hspike : ∀ u∈rows, U^p≤‖F u‖^2)
    (henergy : ∑ u∈rows, ‖F u‖^2≤C*U^b) :
    (rows.card : ℝ)≤C*U^(b-p) := by
  have hs : (rows.card : ℝ)*U^p≤C*U^b := by
    calc
      _ = ∑ u∈rows, U^p := by simp
      _ ≤ ∑ u∈rows, ‖F u‖^2 := Finset.sum_le_sum hspike
      _ ≤ _ := henergy
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hU p)).mp
  calc
    _ ≤ C*U^b := hs
    _ = (C*U^(b-p))*U^p := by rw [mul_assoc,←Real.rpow_add hU]; congr 2; ring

theorem inverse_count {α : Type*} (rows : Finset α) (χ : α→Character)
    (W : ℝ→ℂ) (D : ℝ) (σ freq : α→ℝ) (P : α→ℂ)
    (U δ r q z εw εp εm C : ℝ) (hU : 0<U)
    (hM : ∀ u∈rows, U^(δ*r-εw)≤‖polynomial (χ u) true W D (σ u) (freq u)‖^2)
    (hP : ∀ u∈rows, U^(2*q*z-εp)≤‖P u‖^2)
    (henergy : ∑ u∈rows,
      ‖polynomial (χ u) true W D (σ u) (freq u)*P u‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤C*U^(1-δ*r-2*q*z+εw+εp+εm) := by
  have hs (u : α) (hu : u∈rows) :
      U^((δ*r-εw)+(2*q*z-εp))≤‖polynomial (χ u) true W D (σ u) (freq u)*P u‖^2 := by
    rw [Real.rpow_add hU,norm_mul,mul_pow]
    exact mul_le_mul (hM u hu) (hP u hu) (Real.rpow_nonneg hU.le _) (sq_nonneg _)
  have hh := card_of_energy rows _ U _ (1+εm) C hU hs henergy
  convert hh using 1; congr 2; ring

theorem plain_count {α : Type*} (rows : Finset α) (χ : α→Character)
    (W : ℝ→ℂ) (N : ℝ) (σ freq : α→ℝ) (P : α→ℂ)
    (U δ m q z εw εp εm C : ℝ) (hU : 0<U)
    (hS : ∀ u∈rows, U^(δ*m-εw)≤‖polynomial (χ u) false W N (σ u) (freq u)‖^2)
    (hP : ∀ u∈rows, U^(2*q*z-εp)≤‖P u‖^2)
    (henergy : ∑ u∈rows,
      ‖polynomial (χ u) false W N (σ u) (freq u)*
        polynomial (χ u) false W N (σ u) (freq u)*P u‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤C*U^(1-2*δ*m-2*q*z+2*εw+εp+εm) := by
  have hs (u : α) (hu : u∈rows) :
      U^((δ*m-εw)+(δ*m-εw)+(2*q*z-εp))≤
        ‖polynomial (χ u) false W N (σ u) (freq u)*
          polynomial (χ u) false W N (σ u) (freq u)*P u‖^2 := by
    rw [Real.rpow_add hU,Real.rpow_add hU,norm_mul,norm_mul,mul_pow,mul_pow]
    exact mul_le_mul (mul_le_mul (hS u hu) (hS u hu) (Real.rpow_nonneg hU.le _) (sq_nonneg _))
      (hP u hu) (Real.rpow_nonneg hU.le _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hh := card_of_energy rows _ U _ (1+εm) C hU hs henergy
  convert hh using 1; congr 2; ring

theorem classified_card_bound {α Label : Type*} [Fintype Label]
    (rows : Finset α) (presentation : α→Label) (left right : α→ℕ)
    (B : ℕ) (hleft : ∀ u∈rows, left u<B) (hright : ∀ u∈rows, right u<B)
    (K : ℝ)
    (hfiber : ∀ p : Label, ∀ j∈Finset.range B, ∀ k∈Finset.range B,
      ((rows.filter (fun u => presentation u=p ∧ left u=j ∧ right u=k)).card : ℝ)≤K) :
    (rows.card : ℝ)≤(Fintype.card Label : ℝ)*(B : ℝ)^2*K := by
  let labels : Finset (Label×ℕ×ℕ) := Finset.univ ×ˢ (Finset.range B ×ˢ Finset.range B)
  let label : α→Label×ℕ×ℕ := fun u => (presentation u,left u,right u)
  have hmaps : (rows : Set α).MapsTo label labels := by
    intro u hu
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (hleft u hu),Finset.mem_range.mpr (hright u hu)⟩⟩
  have he := Finset.card_eq_sum_card_fiberwise hmaps
  have he' : (rows.card : ℝ)=∑ l∈labels,
      ((rows.filter (fun u => label u=l)).card : ℝ) := by exact_mod_cast he
  rw [he']
  calc
    _ ≤ ∑ l∈labels, K := by
      apply Finset.sum_le_sum
      intro l hl
      rcases l with ⟨p,j,k⟩
      obtain ⟨hp,hjk⟩ := Finset.mem_product.mp hl
      obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
      have hh := hfiber p j hj k hk
      simpa only [label,Prod.mk.injEq] using hh
    _ = _ := by simp [labels,Finset.card_product,pow_two,mul_assoc]

end SevenEighths.HeckeDetectorRowCount

end

end OAI

end Source767

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorRowwise.lean; sha256: f8e678f568a18ac5029c33c7293ace7482797b5c2316af7969696acf1cdd4dc6 -/
section Source768
namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory Set
namespace SevenEighths.HeckeDetectorRowwise

theorem norm_sq_le_anchor_integral (F F' : ℝ→ℂ)
    (hF : Continuous F) (hF' : Continuous F')
    (hd : ∀ x, HasDerivAt F (F' x) x) {a b x : ℝ} (hx : x∈Icc a b) :
    ‖F x‖^2≤‖F a‖^2+∫ t in a..b, (‖F t‖^2+‖F' t‖^2) := by
  let G : ℝ→ℝ := fun t => ‖F t‖^2+‖F' t‖^2
  have hG : Continuous G := (hF.norm.pow 2).add (hF'.norm.pow 2)
  have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hx.1
    (hF.norm.pow 2).continuousOn
    (fun t ht => (hd t).norm_sq.hasDerivWithinAt)
    (hG.continuousOn.integrableOn_Icc)
    (fun t ht => show 2*inner (𝕜:=ℝ) (F t) (F' t)≤G t by
      dsimp [G]
      have hc := real_inner_le_norm (F t) (F' t)
      change (F' t * (starRingEnd ℂ) (F t)).re ≤ ‖F t‖*‖F' t‖ at hc
      nlinarith [sq_nonneg (‖F t‖-‖F' t‖)])
  simp only [Pi.pow_apply] at hh
  have hm := intervalIntegral.integral_mono_interval (μ:=volume) (le_refl a) hx.1 hx.2
    (Filter.Eventually.of_forall (fun t => show 0≤G t by dsimp [G]; positivity))
    (hG.intervalIntegrable a b)
  change ‖F x‖^2≤‖F a‖^2+∫ t in a..b, G t
  linarith

theorem rowwise_energy {ι : Type*} (rows : Finset ι) (F F' : ι→ℝ→ℂ)
    (hF : ∀ i∈rows, Continuous (F i)) (hF' : ∀ i∈rows, Continuous (F' i))
    (hd : ∀ i∈rows, ∀ x, HasDerivAt (F i) (F' i x) x)
    (a b E : ℝ) (hab : a≤b) (choice : ι→ℝ)
    (hc : ∀ i∈rows, choice i∈Icc a b)
    (henergy : ∀ t∈Icc a b, ∑ i∈rows, ‖F i t‖^2≤E)
    (henergy' : ∀ t∈Icc a b, ∑ i∈rows, ‖F' i t‖^2≤E) :
    ∑ i∈rows, ‖F i (choice i)‖^2≤(1+2*(b-a))*E := by
  have hg (i : ι) (hi : i∈rows) :
      Continuous (fun t => ‖F i t‖^2+‖F' i t‖^2) :=
    ((hF i hi).norm.pow 2).add ((hF' i hi).norm.pow 2)
  have hs := Finset.sum_le_sum (fun i hi =>
    norm_sq_le_anchor_integral (F i) (F' i) (hF i hi) (hF' i hi) (hd i hi) (hc i hi))
  rw [Finset.sum_add_distrib,←intervalIntegral.integral_finsetSum
    (fun i hi => (hg i hi).intervalIntegrable a b)] at hs
  have hm : (∫ t in a..b, ∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤(b-a)*(2*E) := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hab
      ((continuous_finsetSum rows (fun i hi => hg i hi)).intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b)
      (fun t ht => show (∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤2*E by
        rw [Finset.sum_add_distrib]
        linarith [henergy t ht,henergy' t ht])
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  have ha := henergy a ⟨le_refl a,hab⟩
  nlinarith

theorem rowwise_energy_two {ι : Type*} (rows : Finset ι)
    (F : Fin 2→Fin 2→ι→ℝ→ℝ→ℂ)
    (hcont : ∀ j k i, i∈rows → Continuous (Function.uncurry (F j k i)))
    (hdx : ∀ k i, i∈rows → ∀ x y,
      HasDerivAt (fun u => F 0 k i u y) (F 1 k i x y) x)
    (hdy : ∀ j i, i∈rows → ∀ x y,
      HasDerivAt (F j 0 i x) (F j 1 i x y) y)
    (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d) (px py : ι→ℝ)
    (hpx : ∀ i∈rows, px i∈Icc a b) (hpy : ∀ i∈rows, py i∈Icc c d)
    (henergy : ∀ j k x, x∈Icc a b → ∀ y, y∈Icc c d →
      ∑ i∈rows, ‖F j k i x y‖^2≤E) :
    ∑ i∈rows, ‖F 0 0 i (px i) (py i)‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  have cx (j k : Fin 2) (i : ι) (hi : i∈rows) (y : ℝ) :
      Continuous (fun x => F j k i x y) :=
    (hcont j k i hi).comp (continuous_id.prodMk continuous_const)
  have cy (j k : Fin 2) (i : ι) (hi : i∈rows) (x : ℝ) :
      Continuous (F j k i x) :=
    (hcont j k i hi).comp (continuous_const.prodMk continuous_id)
  have he (j : Fin 2) (x : ℝ) (hx : x∈Icc a b) :
      ∑ i∈rows, ‖F j 0 i x (py i)‖^2≤(1+2*(d-c))*E :=
    rowwise_energy rows (fun i => F j 0 i x) (fun i => F j 1 i x)
      (fun i hi => cy j 0 i hi x) (fun i hi => cy j 1 i hi x)
      (fun i hi y => hdy j i hi x y) c d E hcd py hpy
      (fun y hy => henergy j 0 x hx y hy) (fun y hy => henergy j 1 x hx y hy)
  exact rowwise_energy rows (fun i x => F 0 0 i x (py i))
    (fun i x => F 1 0 i x (py i))
    (fun i hi => cx 0 0 i hi (py i)) (fun i hi => cx 1 0 i hi (py i))
    (fun i hi x => hdx 0 i hi x (py i)) a b ((1+2*(d-c))*E) hab px hpx
    (he 0) (he 1)

theorem source_height_cost {T E : ℝ} (_hT : 0≤T) (hE : 0≤E) :
    (1+2*((1:ℝ)-0))*((1+2*(T-(-T)))*E)≤12*(1+T)*E := by
  nlinarith

end SevenEighths.HeckeDetectorRowwise

end

end OAI

end Source768

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorRowwisePolynomial.lean; sha256: 0b423728a729766e8540c39f3bfc9db72df4c9cea9210ef475b582d9703bed0c -/
section Source769
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff Topology
open Set Complex
namespace SevenEighths.HeckeDetectorRowwisePolynomial
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge

def logProfile (W : ℝ→ℂ) (x : ℝ) : ℂ := (Real.log x : ℂ)*W x

theorem logProfile_cover (W : ℝ→ℂ) (D : ℝ) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    ∀ J : Ideal O, J≠0 → logProfile W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
  intro J hJ hw
  exact hc J hJ (fun hz => hw (by simp [logProfile,hz]))

theorem logProfile_support (W : ℝ→ℂ) :
    Function.support (logProfile W)⊆Function.support W := by
  intro x hx hw
  exact hx (by simp [logProfile,hw])

theorem logProfile_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (logProfile W) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : logProfile W =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds ha] with y hy
      have hw : W y=0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp [logProfile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (Real.contDiffAt_log.mpr hx)).mul hW.contDiffAt

lemma power_sigma_deriv (x σ freq : ℝ) (hx : 0<x) :
    HasDerivAt (fun u : ℝ => (x : ℂ)^(-HeckeDyadic.shift u freq))
      (-(Real.log x : ℂ)*(x : ℂ)^(-HeckeDyadic.shift σ freq)) σ := by
  have hd := (((hasDerivAt_id (σ : ℂ)).neg).add_const ((freq : ℂ)*I)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hh := hd.comp_ofReal
  rw [←Complex.ofReal_log hx.le] at hh
  convert hh using 1
  · ext u
    congr 1
    simp only [HeckeDyadic.shift,neg_sub,Pi.neg_apply,id_eq]
    ring
  · have he : -HeckeDyadic.shift σ freq= -(σ : ℂ)+(freq : ℂ)*I := by unfold HeckeDyadic.shift; ring
    rw [he]
    simp only [Pi.neg_apply,id_eq]
    ring

lemma power_freq_deriv (x σ freq : ℝ) (hx : 0<x) :
    HasDerivAt (fun u : ℝ => (x : ℂ)^(-HeckeDyadic.shift σ u))
      (I*(Real.log x : ℂ)*(x : ℂ)^(-HeckeDyadic.shift σ freq)) freq := by
  have hd := (((hasDerivAt_id (freq : ℂ)).mul_const I).const_add (-(σ : ℂ))).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hh := hd.comp_ofReal
  rw [←Complex.ofReal_log hx.le] at hh
  convert hh using 1
  · ext u
    congr 1
    simp [HeckeDyadic.shift]
    ring
  · have he : -HeckeDyadic.shift σ freq= -(σ : ℂ)+(freq : ℂ)*I := by unfold HeckeDyadic.shift; ring
    rw [he]
    simp only [id_eq]
    ring

theorem polynomial_sigma_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    HasDerivAt (fun u => polynomial χ inv W D u freq)
      (-polynomial χ inv (logProfile W) D σ freq) σ := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  rw [polynomial_eq_finite χ inv (logProfile W) D σ freq S (logProfile_cover W D S hc)]
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun u => coefficient χ inv J*W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift u freq))
      (-coefficient χ inv J*logProfile W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)) σ := by
    by_cases hz : J=0
    · subst J
      simpa only [coefficient_zero,zero_mul,neg_zero] using hasDerivAt_const σ (0 : ℂ)
    have hn : 0<(J.absNorm : ℝ)/D := div_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
    convert (power_sigma_deriv _ σ freq hn).const_mul
      (coefficient χ inv J*W ((J.absNorm : ℝ)/D)) using 1
    unfold logProfile
    ring
  convert (HasDerivAt.sum (u:=S) hd).const_mul ((D : ℂ)^(-(1/2 : ℂ))) using 1
  all_goals simp only [Finset.sum_apply,neg_mul,Finset.sum_neg_distrib,mul_neg]

theorem polynomial_freq_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    HasDerivAt (fun u => polynomial χ inv W D σ u)
      (I*polynomial χ inv (logProfile W) D σ freq) freq := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  rw [polynomial_eq_finite χ inv (logProfile W) D σ freq S (logProfile_cover W D S hc)]
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun u => coefficient χ inv J*W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ u))
      (I*(coefficient χ inv J*logProfile W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq))) freq := by
    by_cases hz : J=0
    · subst J
      simpa only [coefficient_zero,zero_mul,mul_zero] using hasDerivAt_const freq (0 : ℂ)
    have hn : 0<(J.absNorm : ℝ)/D := div_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
    convert (power_freq_deriv _ σ freq hn).const_mul
      (coefficient χ inv J*W ((J.absNorm : ℝ)/D)) using 1
    unfold logProfile
    ring
  convert (HasDerivAt.sum (u:=S) hd).const_mul ((D : ℂ)^(-(1/2 : ℂ))) using 1
  all_goals simp only [Finset.sum_apply,←Finset.mul_sum]
  ring

theorem polynomial_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    Continuous (fun p : ℝ×ℝ => polynomial χ inv W D p.1 p.2) := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro J hJ
  by_cases hz : J=0
  · subst J
    simp only [coefficient_zero,zero_mul]
    exact continuous_const
  have hn : 0<(J.absNorm : ℝ)/D := div_pos
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
  apply Continuous.const_mul
  apply Continuous.const_cpow _ (Or.inl (Complex.ofReal_ne_zero.mpr hn.ne'))
  unfold HeckeDyadic.shift
  fun_prop

end SevenEighths.HeckeDetectorRowwisePolynomial

end

end OAI

end Source769

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorRowwiseChain.lean; sha256: 77e379be5bc80840034768e5d13db3422ce63fae24f94913070da84ebdbab214 -/
section Source770
namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwise

theorem chain_rowwise {ι : Type*} (rows : Finset ι) (M : ℕ→ι→ℝ→ℝ→ℂ)
    (cm : ∀ n i, n≤2 → Continuous (Function.uncurry (M n i)))
    (dx : ∀ n i x y, n≤1 → HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x)
    (dy : ∀ n i x y, n≤1 → HasDerivAt (M n i x) (I*M (n+1) i x y) y)
    (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (henergy : ∀ n, n≤2 → ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖M n i x y‖^2≤E) :
    ∑ i∈rows, ‖M 0 i (σ i) (freq i)‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  let F : Fin 2→Fin 2→ι→ℝ→ℝ→ℂ := fun j k i x y =>
    if j=0 then (if k=0 then M 0 i x y else I*M 1 i x y)
    else (if k=0 then -M 1 i x y else -(I*M 2 i x y))
  have cF (j k : Fin 2) (i : ι) (hi : i∈rows) : Continuous (Function.uncurry (F j k i)) := by
    have c0 := cm 0 i (by norm_num)
    have c1 := cm 1 i (by norm_num)
    have c2 := cm 2 i (by norm_num)
    fin_cases j <;> fin_cases k
    · simpa [F] using c0
    · convert c1.const_mul I using 1
      ext p
      simp [F]
      rfl
    · convert c1.neg using 1
      ext p
      simp [F]
      rfl
    · convert (c2.const_mul I).neg using 1
      ext p
      simp [F]
      rfl
  have dFx (k : Fin 2) (i : ι) (hi : i∈rows) (x y : ℝ) :
      HasDerivAt (fun u => F 0 k i u y) (F 1 k i x y) x := by
    fin_cases k
    · simpa [F] using dx 0 i x y (by norm_num)
    · simpa [F] using (dx 1 i x y (by norm_num)).const_mul I
  have dFy (j : Fin 2) (i : ι) (hi : i∈rows) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    fin_cases j
    · simpa [F] using dy 0 i x y (by norm_num)
    · convert (dy 1 i x y (by norm_num)).neg using 1
      · ext t
        simp [F]
      · simp [F]
  have eF (j k : Fin 2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖F j k i x y‖^2≤E := by
    fin_cases j <;> fin_cases k
    · simpa [F] using henergy 0 (by norm_num) x hx y hy
    · simpa [F,norm_mul] using henergy 1 (by norm_num) x hx y hy
    · simpa [F] using henergy 1 (by norm_num) x hx y hy
    · simpa [F,norm_mul] using henergy 2 (by norm_num) x hx y hy
  simpa only [F,ite_true] using
    rowwise_energy_two rows F cF dFx dFy a b c d E hab hcd σ freq hσ hf eF

end SevenEighths.HeckeDetectorRowwise

end

end OAI

end Source770

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorRowwiseMarked.lean; sha256: 12eb24e111a1effaa70d5cb05530024c9c00c84c28253515cb25713503bd7240 -/
section Source771
namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwiseMarked
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorRowwisePolynomial

theorem marked_rowwise {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (inv : Bool) (W : ℝ→ℂ) (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (P : ι→ℂ) (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (h0 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv W D x y*P i‖^2≤E)
    (h1 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv (logProfile W) D x y*P i‖^2≤E)
    (h2 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv (logProfile (logProfile W)) D x y*P i‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) inv W D (σ i) (freq i)*P i‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  let M (n : ℕ) (i : ι) (x y : ℝ) :=
    polynomial (χ i) inv ((logProfile^[n]) W) D x y*P i
  have hc1 := logProfile_cover W D S hc
  have hc2 := logProfile_cover (logProfile W) D S hc1
  have cm (n : ℕ) (i : ι) (hn : n≤2) : Continuous (Function.uncurry (M n i)) := by
    interval_cases n
    all_goals
      dsimp [M,Function.uncurry]
      apply Continuous.mul_const
    · exact polynomial_continuous (χ i) inv W D hD S hc
    · exact polynomial_continuous (χ i) inv (logProfile W) D hD S hc1
    · exact polynomial_continuous (χ i) inv (logProfile (logProfile W)) D hD S hc2
  have dx (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x := by
    interval_cases n
    · simpa [M] using (polynomial_sigma_deriv (χ i) inv W D x y hD S hc).mul_const (P i)
    · simpa [M] using (polynomial_sigma_deriv (χ i) inv (logProfile W) D x y hD S hc1).mul_const (P i)
  have dy (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (M n i x) (I*M (n+1) i x y) y := by
    interval_cases n
    · simpa [M,mul_assoc] using (polynomial_freq_deriv (χ i) inv W D x y hD S hc).mul_const (P i)
    · simpa [M,mul_assoc] using (polynomial_freq_deriv (χ i) inv (logProfile W) D x y hD S hc1).mul_const (P i)
  have he (n : ℕ) (hn : n≤2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖M n i x y‖^2≤E := by
    interval_cases n
    · simpa [M] using h0 x hx y hy
    · simpa [M] using h1 x hx y hy
    · simpa [M] using h2 x hx y hy
  exact chain_rowwise rows M cm dx dy a b c d E hab hcd σ freq hσ hf he

end SevenEighths.HeckeDetectorRowwiseMarked

end

end OAI

end Source771

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorRowwisePlain.lean; sha256: ae1459a1396d719e2741f98db6618a06340ec439aa22943e66c9c185e3cd8e3e -/
section Source772
namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwisePlain
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorRowwisePolynomial

lemma norm_sum_sq_le (u v : ℂ) : ‖u+v‖^2≤2*(‖u‖^2+‖v‖^2) := by
  have h := norm_add_le u v
  nlinarith [norm_nonneg (u+v),norm_nonneg u,norm_nonneg v,sq_nonneg (‖u‖-‖v‖)]

theorem plain_squared_rowwise {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (W : ℝ→ℂ) (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (P : ι→ℂ) (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d) (hE : 0≤E)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (henergy : ∀ j k : ℕ, j+k≤2 → ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) false ((logProfile^[j]) W) D x y*
        polynomial (χ i) false ((logProfile^[k]) W) D x y*P i‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) false W D (σ i) (freq i)*
      polynomial (χ i) false W D (σ i) (freq i)*P i‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*(16*E)) := by
  let Q (n : ℕ) (i : ι) (x y : ℝ) := polynomial (χ i) false ((logProfile^[n]) W) D x y
  let M (n : ℕ) (i : ι) (x y : ℝ) :=
    if n=0 then Q 0 i x y*Q 0 i x y*P i
    else if n=1 then 2*Q 0 i x y*Q 1 i x y*P i
    else 2*(Q 1 i x y*Q 1 i x y+Q 0 i x y*Q 2 i x y)*P i
  have hc1 := logProfile_cover W D S hc
  have hc2 := logProfile_cover (logProfile W) D S hc1
  have cq (n : ℕ) (i : ι) (hn : n≤2) : Continuous (Function.uncurry (Q n i)) := by
    interval_cases n
    · exact polynomial_continuous (χ i) false W D hD S hc
    · exact polynomial_continuous (χ i) false (logProfile W) D hD S hc1
    · exact polynomial_continuous (χ i) false (logProfile (logProfile W)) D hD S hc2
  have qx (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (fun u => Q n i u y) (-Q (n+1) i x y) x := by
    interval_cases n
    · exact polynomial_sigma_deriv (χ i) false W D x y hD S hc
    · exact polynomial_sigma_deriv (χ i) false (logProfile W) D x y hD S hc1
  have qy (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (Q n i x) (I*Q (n+1) i x y) y := by
    interval_cases n
    · exact polynomial_freq_deriv (χ i) false W D x y hD S hc
    · exact polynomial_freq_deriv (χ i) false (logProfile W) D x y hD S hc1
  have cm (n : ℕ) (i : ι) (hn : n≤2) : Continuous (Function.uncurry (M n i)) := by
    have c0 := cq 0 i (by norm_num)
    have c1 := cq 1 i (by norm_num)
    have c2 := cq 2 i (by norm_num)
    change Continuous (fun p : ℝ×ℝ => M n i p.1 p.2)
    change Continuous (fun p : ℝ×ℝ => Q 0 i p.1 p.2) at c0
    change Continuous (fun p : ℝ×ℝ => Q 1 i p.1 p.2) at c1
    change Continuous (fun p : ℝ×ℝ => Q 2 i p.1 p.2) at c2
    interval_cases n <;> dsimp [M] <;> fun_prop
  have dx (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x := by
    interval_cases n
    · convert ((qx 0 i x y (by norm_num)).mul (qx 0 i x y (by norm_num))).mul_const (P i) using 1
      · ext u; simp [M]
      · simp [M]; ring
    · convert (((qx 0 i x y (by norm_num)).mul (qx 1 i x y (by norm_num))).const_mul 2).mul_const (P i) using 1
      · ext u; dsimp [M]; ring
      · simp [M]; ring
  have dy (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (M n i x) (I*M (n+1) i x y) y := by
    interval_cases n
    · convert ((qy 0 i x y (by norm_num)).mul (qy 0 i x y (by norm_num))).mul_const (P i) using 1
      · ext u; simp [M]
      · simp [M]; ring
    · convert (((qy 0 i x y (by norm_num)).mul (qy 1 i x y (by norm_num))).const_mul 2).mul_const (P i) using 1
      · ext u; dsimp [M]; ring
      · simp [M]; ring
  have he (n : ℕ) (hn : n≤2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖M n i x y‖^2≤16*E := by
    have e00 := henergy 0 0 (by norm_num) x hx y hy
    have e01 := henergy 0 1 (by norm_num) x hx y hy
    have e11 := henergy 1 1 (by norm_num) x hx y hy
    have e02 := henergy 0 2 (by norm_num) x hx y hy
    change ∑ i∈rows, ‖Q 0 i x y*Q 0 i x y*P i‖^2≤E at e00
    change ∑ i∈rows, ‖Q 0 i x y*Q 1 i x y*P i‖^2≤E at e01
    change ∑ i∈rows, ‖Q 1 i x y*Q 1 i x y*P i‖^2≤E at e11
    change ∑ i∈rows, ‖Q 0 i x y*Q 2 i x y*P i‖^2≤E at e02
    interval_cases n
    · simpa only [M,ite_true] using e00.trans (show E≤16*E by linarith)
    · have heq : (∑ i∈rows, ‖M 1 i x y‖^2)=4*∑ i∈rows, ‖Q 0 i x y*Q 1 i x y*P i‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hm : M 1 i x y=2*(Q 0 i x y*Q 1 i x y*P i) := by simp [M]; ring
        rw [hm,norm_mul,mul_pow]
        norm_num
      rw [heq]
      linarith
    · have hh : (∑ i∈rows, ‖M 2 i x y‖^2)≤
          8*((∑ i∈rows, ‖Q 1 i x y*Q 1 i x y*P i‖^2)+
          ∑ i∈rows, ‖Q 0 i x y*Q 2 i x y*P i‖^2) := by
        rw [←Finset.sum_add_distrib,Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hm : M 2 i x y=2*(Q 1 i x y*Q 1 i x y*P i+Q 0 i x y*Q 2 i x y*P i) := by simp [M]; ring
        rw [hm,norm_mul,mul_pow]
        norm_num
        have hh := norm_sum_sq_le (Q 1 i x y*Q 1 i x y*P i) (Q 0 i x y*Q 2 i x y*P i)
        simp only [norm_mul] at hh
        nlinarith
      linarith
  simpa only [M,ite_true,Q,Function.iterate_zero,id_eq] using
    chain_rowwise rows M cm dx dy a b c d (16*E) hab hcd σ freq hσ hf he

end SevenEighths.HeckeDetectorRowwisePlain

end

end OAI

end Source772

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationScale.lean; sha256: 8960ab7f090f31a1d0d67fdd84c449c767380134deb74a5486696389b5852c60 -/
section Source773
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeDetectorRowwise

def scaleProfile (W : ℝ→ℂ) (y : ℝ) : ℂ := -W y/2-(y : ℂ)*deriv W y

def scaleSum (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    coefficient χ true J*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem scaleProfile_continuous (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    Continuous (scaleProfile W) := by
  have hd := hW.continuous_deriv (by simp)
  unfold scaleProfile
  fun_prop

theorem scaleProfile_support (W : ℝ→ℂ) (a b : ℝ)
    (hs : Function.support W⊆Icc a b) : Function.support (scaleProfile W)⊆Icc a b := by
  intro y hy
  by_contra hn
  have hw : W y=0 := by by_contra hw; exact hn (hs hw)
  have hd : deriv W y=0 := by
    apply deriv_of_notMem_tsupport
    exact fun h => hn ((closure_minimal hs isClosed_Icc) h)
  exact hy (by simp [scaleProfile,hw,hd])

theorem scaleSum_continuous (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (scaleSum χ W S) := by
  unfold scaleSum
  fun_prop

theorem scaleSum_deriv (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (scaleSum χ W S) (scaleSum χ (scaleProfile W) S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => coefficient χ true J*W ((J.absNorm : ℝ)*Real.exp (-t)))
        (coefficient χ true J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert ((hW _).hasDerivAt.scomp l hy).const_mul (coefficient χ true J) using 1
    · rfl
    · change coefficient χ true J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        coefficient χ true J*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
      rw [Complex.real_smul]
      push_cast
      ring
  convert hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  · ext t
    simp only [scaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [scaleSum,scaleProfile]
    simp only [Finset.sum_apply]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    push_cast
    ring

theorem scale_normalization (l : ℝ) :
    ((Real.exp l : ℝ) : ℂ)^(-(1/2 : ℂ))=Complex.exp (-(l : ℂ)/2) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos l).ne'),
    ←Complex.ofReal_log (Real.exp_pos l).le,Real.log_exp]
  congr 1
  ring

theorem scaleSum_eq_polynomial (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (l : ℝ) (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    scaleSum χ W S l=polynomial χ true W (Real.exp l) 0 0 := by
  rw [polynomial_eq_finite χ true W (Real.exp l) 0 0 S hc,scale_normalization]
  simp only [HeckeDyadic.shift,ofReal_zero,zero_mul,sub_self,neg_zero,Complex.cpow_zero,mul_one]
  unfold scaleSum
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Real.exp_neg,div_eq_mul_inv]

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source773

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationConjugation.lean; sha256: 9ca4335527c05e335587d807b24d3600f28477744ffb28f63174eb386af2aeac -/
section Source774
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate ContDiff
open Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem coefficient_inverse_conj (χ : Character) (inv : Bool) (J : Ideal O) :
    coefficient χ.inverse inv J=conj (coefficient χ inv J) := by
  cases inv <;> simp [coefficient,idealCoeff_inverse_conj]

theorem conj_positive_cpow (x : ℝ) (hx : 0<x) (z : ℂ) :
    conj ((x : ℂ)^z)=(x : ℂ)^(conj z) := by
  have hh := Complex.cpow_conj (x : ℂ) z
    (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm)
  simpa only [conj_ofReal] using hh.symm

theorem conj_shift (σ freq : ℝ) : conj (shift σ freq)=shift σ (-freq) := by
  simp only [HeckeDyadic.shift,map_sub,map_mul,conj_ofReal,conj_I,ofReal_neg]
  ring

theorem conj_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    conj (polynomial χ inv W D σ freq)=
      polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq) := by
  unfold polynomial
  rw [map_mul,conj_tsum,conj_positive_cpow D hD]
  have hhalf : conj (-(1/2 : ℂ))= -(1/2 : ℂ) := by
    simp only [map_neg,map_div₀,map_one,map_ofNat]
  rw [hhalf]
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,map_mul,←coefficient_inverse_conj]
  rw [conj_positive_cpow _ (div_pos (norm_pos J) hD),map_neg,conj_shift]

theorem polynomial_inverse_norm (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq)‖=
      ‖polynomial χ inv W D σ freq‖ := by
  rw [←conj_polynomial χ inv W D σ freq hD,norm_conj]

theorem conjugate_profile_support (W : ℝ→ℂ) :
    Function.support (fun x => conj (W x))=Function.support W := by
  ext x
  simp

theorem conjugate_profile_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (fun x => conj (W x)) := by
  exact Complex.conjCLE.contDiff.comp hW

theorem scaleProfile_conjugate (W : ℝ→ℂ) (x : ℝ) :
    scaleProfile (fun y => conj (W y)) x=conj (scaleProfile W x) := by
  have hd : deriv (fun y => conj (W y)) x=conj (deriv W x) := by
    simpa only [star_def] using (deriv.star (f:=W) (x:=x))
  simp only [scaleProfile,hd,map_sub,map_div₀,map_neg,map_mul,conj_ofReal,map_ofNat]

theorem logProfile_conjugate (W : ℝ→ℂ) (x : ℝ) :
    HeckeDetectorRowwisePolynomial.logProfile (fun y => conj (W y)) x=
      conj (HeckeDetectorRowwisePolynomial.logProfile W x) := by
  simp only [HeckeDetectorRowwisePolynomial.logProfile,map_mul,conj_ofReal]

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source774

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorCoefficientTransfer.lean; sha256: 7a9d7381e364c5dcf8189d1f2b3b61b40d75de1a5a7a45b4ba2e44a859f0adbd -/
section Source775
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
open Complex
namespace SevenEighths.HeckeDetectorCoefficientTransfer
open HeckeFamily HeckeDyadic HeckeInverseAmplification

theorem polynomial_eq_of_idealCoeff (χ ψ : Character)
    (hc : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ inv W D σ freq=polynomial ψ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,coefficient,hc]

def orientedProfile (reverse : Bool) (W : ℝ→ℂ) : ℝ→ℂ :=
  if reverse then fun x => conj (W x) else W

def orientedFrequency (reverse : Bool) (freq : ℝ) : ℝ := if reverse then -freq else freq

theorem norm_of_oriented_coefficients (χ ψ : Character) (reverse : Bool)
    (hc : ∀ J : Ideal O,idealCoeff χ J=
      if reverse then conj (idealCoeff ψ J) else idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ inv W D σ freq‖=
      ‖polynomial ψ inv (orientedProfile reverse W) D σ (orientedFrequency reverse freq)‖ := by
  cases reverse
  · exact congrArg (fun z : ℂ => ‖z‖) (polynomial_eq_of_idealCoeff χ ψ hc inv W D σ freq)
  · have hc' : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ.inverse J := by
      intro J
      simpa only [Bool.true_eq,ite_true,idealCoeff_inverse_conj] using hc J
    rw [polynomial_eq_of_idealCoeff χ ψ.inverse hc' inv W D σ freq]
    have hh := polynomial_inverse_norm ψ inv (fun x => conj (W x)) D σ (-freq) hD
    simpa only [orientedProfile,orientedFrequency,Bool.true_eq,ite_true,conj_conj,neg_neg] using hh

theorem orientedFrequency_abs (reverse : Bool) (freq : ℝ) :
    |orientedFrequency reverse freq|=|freq| := by cases reverse <;> simp [orientedFrequency]

end SevenEighths.HeckeDetectorCoefficientTransfer

end

end OAI

end Source775

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationScaleSup.lean; sha256: 3bb1b731ea80b8899c1980c48cc2a0f6be279511ac7825beddc1674ec5296529 -/
section Source776
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorRowwise
open ConcretePrimeRowBridge hiding O

def scaleSupport (upper b : ℝ) : Finset (Ideal O) := idealsUpTo ⌈Real.exp upper*b⌉₊

theorem scaleSupport_cover (W : ℝ→ℂ) (a b upper l : ℝ) (hb : 0≤b)
    (hWs : Function.support W⊆Icc a b) (hl : l≤upper) :
    ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈scaleSupport upper b := by
  intro J hJ hw
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ),?_⟩
  have hh := (div_le_iff₀ (Real.exp_pos l)).mp (hWs hw).2
  have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hl) hb
  have hn : (J.absNorm : ℝ)≤Real.exp upper*b := by nlinarith
  exact_mod_cast hn.trans (Nat.le_ceil _)

theorem rowwise_scales {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (W : ℝ→ℂ) (a b : ℝ) (hb : 0≤b) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (lo hi E : ℝ) (hlh : lo≤hi) (l : ι→ℝ)
    (hl : ∀ i∈rows, l i∈Icc lo hi)
    (h0 : ∀ t∈Icc lo hi, ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤E)
    (h1 : ∀ t∈Icc lo hi, ∑ i∈rows,
      ‖polynomial (χ i) true (scaleProfile W) (Real.exp t) 0 0‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp (l i)) 0 0‖^2≤(1+2*(hi-lo))*E := by
  let S := scaleSupport hi b
  have hsp := scaleProfile_support W a b hWs
  have eq0 (i : ι) (t : ℝ) (ht : t∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) W S t (scaleSupport_cover W a b hi t hb hWs ht.2)
  have eq1 (i : ι) (t : ℝ) (ht : t∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) (scaleProfile W) S t
      (scaleSupport_cover (scaleProfile W) a b hi t hb hsp ht.2)
  have hh := rowwise_energy rows (fun i => scaleSum (χ i) W S)
    (fun i => scaleSum (χ i) (scaleProfile W) S)
    (fun i hi => scaleSum_continuous (χ i) W S hW.continuous)
    (fun i hi => scaleSum_continuous (χ i) (scaleProfile W) S (scaleProfile_continuous W hW))
    (fun i hi t => scaleSum_deriv (χ i) W S (hW.differentiable (by simp)) t)
    lo hi E hlh l hl
    (fun t ht => by simpa only [eq0 _ t ht] using h0 t ht)
    (fun t ht => by simpa only [eq1 _ t ht] using h1 t ht)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [eq0 i (l i) (hl i hi)]

theorem exists_scale_majorant {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (W : ℝ→ℂ) (a b : ℝ) (hb : 0≤b) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (lo hi E : ℝ) (hlh : lo≤hi)
    (h0 : ∀ t∈Icc lo hi, ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤E)
    (h1 : ∀ t∈Icc lo hi, ∑ i∈rows,
      ‖polynomial (χ i) true (scaleProfile W) (Real.exp t) 0 0‖^2≤E) :
    ∃ B : ι→ℝ, (∀ i, 0≤B i) ∧
      (∀ i, ∀ t∈Icc lo hi, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤B i) ∧
      (∑ i∈rows, B i)≤(1+2*(hi-lo))*E := by
  let S := scaleSupport hi b
  have hm (i : ι) : ∃ t∈Icc lo hi, ∀ u∈Icc lo hi,
      ‖scaleSum (χ i) W S u‖^2≤‖scaleSum (χ i) W S t‖^2 := by
    exact isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hlh)
      ((scaleSum_continuous (χ i) W S hW.continuous).norm.pow 2).continuousOn
  choose t ht hmax using hm
  refine ⟨fun i => ‖polynomial (χ i) true W (Real.exp (t i)) 0 0‖^2,
    fun i => sq_nonneg _,?_,?_⟩
  · intro i u hu
    have hh := hmax i u hu
    rw [scaleSum_eq_polynomial (χ i) W S u (scaleSupport_cover W a b hi u hb hWs hu.2),
      scaleSum_eq_polynomial (χ i) W S (t i) (scaleSupport_cover W a b hi (t i) hb hWs (ht i).2)] at hh
    exact hh
  · exact rowwise_scales rows χ W a b hb hWs hW lo hi E hlh t (fun i hi => ht i) h0 h1

theorem polynomial_zero_small_scale (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (a b D σ freq : ℝ) (hD : 0<D) (hs : Function.support W⊆Icc a b)
    (hsmall : D*b<1) : polynomial χ inv W D σ freq=0 := by
  unfold polynomial
  suffices hh : (∑' J : HeckeDyadic.NonzeroIdeal, summand χ inv W D σ freq J)=0 by
    rw [hh,mul_zero]
  have hz : ∀ J : HeckeDyadic.NonzeroIdeal, summand χ inv W D σ freq J=0 := by
    intro J
    have hw : W (norm J/D)=0 := by
      by_contra hn
      have hb := (div_le_iff₀ hD).mp (hs hn).2
      have hN : 1≤norm J := by
        change (1 : ℝ) ≤ (J.val.absNorm : ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr J.property)
      nlinarith
    simp only [summand,hw,mul_zero,zero_mul]
  simp only [hz,tsum_zero]

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source776

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationAggregate.lean; sha256: 852cb55e661ce0a465e310b20c73f05e9909d37c68ee118c5d15d088b6f9e836 -/
section Source777
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic
abbrev PrimeIdeal := SmoothMobiusCorrection.PrimeIdeal

def primeRowMap (p : FreeRow×PrimeIdeal) : NonzeroElement :=
  amplifiedElement ⟨p.1.val,p.1.property.1⟩ ⟨p.2.val,p.2.property.ne_zero⟩

theorem primeRowMap_injective : Function.Injective primeRowMap := by
  intro p q hpq
  have he : rowMap (p.1,⟨p.2.val,p.2.property.ne_zero⟩)=
      rowMap (q.1,⟨q.2.val,q.2.property.ne_zero⟩) := congrArg Subtype.val hpq
  have hh := rowMap_injective he
  apply Prod.ext
  · exact congrArg (fun r : FreeRow×NonzeroIdeal => r.1) hh
  · apply Subtype.ext
    exact congrArg (fun r : FreeRow×NonzeroIdeal => r.2.val) hh

theorem primeRowMap_norm_bound (p : FreeRow×PrimeIdeal) (U V : ℝ)
    (hU : (Ideal.span {p.1.val}).absNorm≤U) (hV : (p.2.val.absNorm : ℝ)≤V) :
    ((Ideal.span {((primeRowMap p).val)}).absNorm : ℝ)≤U*V^6 := by
  have hn := rowMap_norm (p.1,⟨p.2.val,p.2.property.ne_zero⟩)
  change ((Ideal.span {rowMap (p.1,⟨p.2.val,p.2.property.ne_zero⟩)}).absNorm : ℝ)≤_
  rw [hn,Nat.cast_mul,Nat.cast_pow]
  exact mul_le_mul hU (pow_le_pow_left₀ (Nat.cast_nonneg _) hV 6)
    (by positivity) ((Nat.cast_nonneg _).trans hU)

theorem averaged_energy (data : RowData) (rows : Finset FreeRow) (primes : Finset PrimeIdeal)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hb : 0≤b)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D U V E : ℝ) (hD : 0<D) (hV : 1≤V)
    (hrows : ∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U)
    (hprimes : ∀ P∈primes, (P.val.absNorm : ℝ)≤V)
    (hraw0 : ∀ R : Finset NonzeroElement,
      (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
      ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true W (Real.exp l) 0 0‖^2≤E)
    (hraw1 : ∀ R : Finset NonzeroElement,
      (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
      ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true (scaleProfile W) (Real.exp l) 0 0‖^2≤E) :
    (primes.card : ℝ)*∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤
      4*(1+2*Real.log V)*E := by
  let R := (rows×ˢprimes).image primeRowMap
  have hR : ∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6 := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hu,hP⟩ := Finset.mem_product.mp hp
    exact primeRowMap_norm_bound p U V (hrows p.1 hu) (hprimes p.2 hP)
  have hl : Real.log D-Real.log V≤Real.log D := by linarith [Real.log_nonneg hV]
  obtain ⟨B,hB,hmajor,henergy⟩ := exists_scale_majorant R data.character W a b hb hWs hW
    (Real.log D-Real.log V) (Real.log D) E hl (hraw0 R hR) (hraw1 R hR)
  have hamp (u : FreeRow) (hu : u∈rows) (P : PrimeIdeal) (hP : P∈primes) :
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤4*B (primeRowMap (u,P)) := by
    have hN : (1 : ℝ)≤P.val.absNorm := by
      exact_mod_cast (show 1≤P.val.absNorm from (SmoothMobiusCorrection.prime_norm_two_le P).trans' (by norm_num))
    have hNp : (0 : ℝ)<P.val.absNorm := by linarith
    have hlog : Real.log (P.val.absNorm : ℝ)≤Real.log V :=
      Real.log_le_log hNp (hprimes P hP)
    have hDV : Real.log (D/(P.val.absNorm : ℝ))∈Icc (Real.log D-Real.log V) (Real.log D) := by
      rw [Real.log_div hD.ne' hNp.ne']
      constructor <;> linarith [Real.log_nonneg hN]
    have hbase := hmajor (primeRowMap (u,P)) (Real.log D) ⟨hl,le_refl _⟩
    have hlow := hmajor (primeRowMap (u,P)) (Real.log (D/(P.val.absNorm : ℝ))) hDV
    rw [Real.exp_log hD] at hbase
    rw [Real.exp_log (div_pos hD hNp)] at hlow
    have hh := data.prime_energy ⟨u.val,u.property.1⟩ P W a b ha hWs hW D 0 0 hD
    change ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤
      2*(‖polynomial (data.character (primeRowMap (u,P))) true W D 0 0‖^2+
        ‖polynomial (data.character (primeRowMap (u,P))) true W (D/(P.val.absNorm : ℝ)) 0 0‖^2) at hh
    linarith
  have hs : (primes.card : ℝ)*∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤4*∑ v∈R, B v := by
    calc
      _ = ∑ p∈rows×ˢprimes,
          ‖polynomial (data.character ⟨p.1.val,p.1.property.1⟩) true W D 0 0‖^2 := by
        rw [Finset.sum_product]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        change (primes.card : ℝ) *
          ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2 =
          ∑ _P∈primes, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p∈rows×ˢprimes, 4*B (primeRowMap p) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hu,hP⟩ := Finset.mem_product.mp hp
        exact hamp p.1 hu p.2 hP
      _ = _ := by
        dsimp [R]
        rw [Finset.mul_sum,Finset.sum_image]
        exact fun p hp q hq h => primeRowMap_injective h
  have hh := mul_le_mul_of_nonneg_left henergy (by norm_num : (0 : ℝ)≤4)
  nlinarith

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source777

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationPrimePool.lean; sha256: 17dab5c7c9e4ce7233739f9edab79113d04d6c961cb50c9ba35dd4ecc90f2ada -/
section Source778
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def RawScaleEnergy (data : RowData) (W : ℝ→ℂ) (U D V E : ℝ) : Prop :=
  ∀ R : Finset NonzeroElement,
    (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
    ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true W (Real.exp l) 0 0‖^2≤E

def typedPrimePool (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) : Finset PrimeIdeal :=
  (CenteredMomentPrimePool.primePool M H S a b x).subtype Prime

theorem typedPrimePool_card (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) :
    (typedPrimePool M H S a b x).card=
      (CenteredMomentPrimePool.primePool M H S a b x).card := by
  rw [typedPrimePool,Finset.card_subtype]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro P hP
  exact ((PNT.AnnularPrimeMass.mem_annularPrimeIdeals _ _ _ _ _).mp
    (Finset.mem_sdiff.mp hP).1).2.1

theorem typedPrimePool_norm (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) (ha : 0≤a) (hab : a≤b) (hx : 0<x)
    (P : PrimeIdeal) (hP : P∈typedPrimePool M H S a b x) :
    (P.val.absNorm : ℝ)≤x*b := by
  have hh := Finset.mem_subtype.mp hP
  exact (PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals ha hab hx
    (Finset.mem_sdiff.mp hh).1).2

theorem eventually_fixed_ray_amplification
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb D U E : ℝ),
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      0<D → (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      RawScaleEnergy data W U D (x*b) E →
      RawScaleEnergy data (scaleProfile W) U D (x*b) E →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2)≤
        4*(1+2*Real.log (x*b))*E*Real.log x/(c*x) := by
  obtain ⟨c,hc,hcard⟩ := CenteredMomentPrimePool.eventually_primePool_card M H hH S
    φ hφ hφc hφp hφ0 hφne a b B ha hab hB hφs hφB
  have hb : 0<b := ha.trans_le hab
  refine ⟨c,hc,?_⟩
  filter_upwards [hcard,eventually_gt_atTop (1 : ℝ),eventually_ge_atTop (1/b)] with x hcard hx hxB
  intro data rows W wa wb D U E hwa hwb hWs hW hD hrows hraw0 hraw1
  have hx0 : 0<x := zero_lt_one.trans hx
  have hxblog : 1≤x*b := (div_le_iff₀ hb).mp hxB
  have hlog : 0<Real.log x := Real.log_pos hx
  have hc' : c*x/Real.log x≤((typedPrimePool M H S a b x).card : ℝ) := by
    rw [typedPrimePool_card]
    exact hcard
  have havg := averaged_energy data rows (typedPrimePool M H S a b x) W wa wb hwa hwb
    hWs hW D U (x*b) E hD hxblog hrows
    (fun P hP => typedPrimePool_norm M H S a b x ha.le hab hx0 P hP) hraw0 hraw1
  have hsum : 0≤∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh := (mul_le_mul_of_nonneg_right hc' hsum).trans havg
  apply (le_div_iff₀ (mul_pos hc hx0)).mpr
  calc
    _ = (c*x/Real.log x*(∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2))*Real.log x := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hh hlog.le

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source778

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationBudget.lean; sha256: 25ac5ce13723bf3f0660d8845a3c7b1579852016b46d6b05d8589249b3a55e83 -/
section Source779
namespace OAI

noncomputable section
open Filter
namespace SevenEighths.HeckeInverseAmplification

def amplificationPower (c r : ℝ) : ℝ := max 0 (((1+c)*r-1)/6)
def sourceExponent (r : ℝ) : ℝ := max 1 ((1+5*r)/6)

theorem amplificationPower_nonneg (c r : ℝ) : 0≤amplificationPower c r := le_max_left _ _

theorem amplificationPower_upper (c r R : ℝ) (hc : c≤1) (hr : 0≤r)
    (hrR : r≤R) : amplificationPower c r≤R/3 := by
  apply max_le (by linarith)
  have hh := mul_le_mul_of_nonneg_right hc hr
  nlinarith

theorem amplified_exponent (c r : ℝ) :
    1+5*amplificationPower c r=max 1 ((1+5*(1+c)*r)/6) := by
  unfold amplificationPower
  by_cases h : 0≤((1+c)*r-1)/6
  · rw [max_eq_right h,max_eq_right (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge h),max_eq_left (by linarith)]
    ring

theorem amplified_exponent_le (c r R : ℝ) (hc : 0≤c) (hrR : r≤R)
    (hR : 0≤R) : 1+5*amplificationPower c r≤sourceExponent r+5*c*R/6 := by
  rw [amplified_exponent]
  apply max_le
  · have hh := le_max_left 1 ((1+5*r)/6)
    unfold sourceExponent
    nlinarith [mul_nonneg hc hR]
  · have hh := le_max_right 1 ((1+5*r)/6)
    have hh' := mul_le_mul_of_nonneg_left hrR hc
    unfold sourceExponent
    nlinarith

theorem exists_amplification_budget (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧
      ∀ r : ℝ, 0≤r → r≤R →
      1+5*amplificationPower c r+κ*(1+6*amplificationPower c r+r)≤
        sourceExponent r+ε/2 := by
  let c := min 1 (ε/(4*(R+1)))
  let κ := ε/(4*(1+3*R))
  have hc : 0<c := lt_min zero_lt_one (div_pos hε (by positivity))
  have hκ : 0<κ := div_pos hε (by positivity)
  have hc1 : c≤1 := min_le_left _ _
  have hcb : c*(4*(R+1))≤ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hκb : κ*(4*(1+3*R))=ε := by dsimp [κ]; field_simp
  refine ⟨c,κ,hc,hc1,hκ,?_⟩
  intro r hr hrR
  have hp := amplificationPower_upper c r R hc1 hr hrR
  have he := amplified_exponent_le c r R hc.le hrR hR
  have hraw : κ*(1+6*amplificationPower c r+r)≤κ*(1+3*R) := by
    apply mul_le_mul_of_nonneg_left _ hκ.le
    linarith
  nlinarith

theorem logarithmic_cost_eventually (A b P η : ℝ) (hA : 1≤A)
    (hbA : 1≤b*A) (hP : 0≤P) (hη : 0<η) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ U : ℝ in atTop, ∀ p : ℝ, 0≤p → p≤P →
      (1+2*Real.log (b*(A*U^p)))*Real.log (A*U^p)≤K*U^η := by
  let K := (1+2*Real.log (b*A)+2*P)*(Real.log A+P)
  have hLA : 0≤Real.log A := Real.log_nonneg hA
  have hLB : 0≤Real.log (b*A) := Real.log_nonneg hbA
  have hK : 0≤K := mul_nonneg (by positivity) (by positivity)
  have hlog := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hη).bound (by norm_num : (0 : ℝ)<1)
  refine ⟨K,hK,?_⟩
  filter_upwards [hlog,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with U hlog hLU hU
  intro p hp hpP
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hpow : 0<U^p := Real.rpow_pos_of_pos hUp _
  have hx : 1≤A*U^p := one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hU hp)
  have hlogx : Real.log (A*U^p)=Real.log A+p*Real.log U := by
    rw [Real.log_mul (ne_of_gt (zero_lt_one.trans_le hA)) hpow.ne',Real.log_rpow hUp]
  have hlogbx : Real.log (b*(A*U^p))=Real.log (b*A)+p*Real.log U := by
    rw [show b*(A*U^p)=b*A*U^p by ring,
      Real.log_mul (ne_of_gt (zero_lt_one.trans_le hbA)) hpow.ne',Real.log_rpow hUp]
  have hfirst : 1+2*Real.log (b*(A*U^p))≤(1+2*Real.log (b*A)+2*P)*Real.log U := by
    rw [hlogbx]
    nlinarith [mul_le_mul_of_nonneg_right hpP (by linarith : 0≤Real.log U),
      mul_le_mul_of_nonneg_left hLU hLB]
  have hsecond : Real.log (A*U^p)≤(Real.log A+P)*Real.log U := by
    rw [hlogx]
    nlinarith [mul_le_mul_of_nonneg_right hpP (by linarith : 0≤Real.log U),
      mul_le_mul_of_nonneg_left hLU hLA]
  have hsq : (Real.log U)^2≤U^η := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log U)),
      abs_of_nonneg (Real.rpow_nonneg hUp.le _),one_mul] using hlog
  calc
    _ ≤ ((1+2*Real.log (b*A)+2*P)*Real.log U)*((Real.log A+P)*Real.log U) :=
      mul_le_mul hfirst hsecond (Real.log_nonneg hx) (by positivity)
    _ = K*(Real.log U)^2 := by dsimp [K]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq hK

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source779

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationPowers.lean; sha256: 6eb9afc7d2422e10b9609db850dab9fa495b658b61bb838402c5e69c2121f6f1 -/
section Source780
namespace OAI

noncomputable section
namespace SevenEighths.HeckeInverseAmplification

theorem amplified_norm_power (U A b p : ℝ) (hU : 0<U) :
    U*(b*(A*U^p))^6=(b*A)^6*U^(1+6*p) := by
  have h6 : (U^p)^6=U^(6*p) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
    congr 1
    norm_num
    ring
  calc
    _ = (b*A)^6*(U^(1 : ℝ)*U^(6*p)) := by
      rw [show b*(A*U^p)=(b*A)*U^p by ring,mul_pow,h6,Real.rpow_one]
      ring
    _ = _ := by rw [←Real.rpow_add hU]

theorem amplified_energy_power (U A b p r κ : ℝ) (hU : 0<U) :
    (U*(b*(A*U^p))^6)*((U*(b*(A*U^p))^6)*U^r)^κ/(A*U^p)=
      ((b*A)^6*((b*A)^6)^κ/A)*U^(1+5*p+κ*(1+6*p+r)) := by
  rw [amplified_norm_power U A b p hU]
  have hHD : ((b*A)^6*U^(1+6*p))*U^r=(b*A)^6*U^(1+6*p+r) := by
    rw [mul_assoc,←Real.rpow_add hU]
  rw [hHD,Real.mul_rpow (by positivity) (Real.rpow_nonneg hU.le _),
    ←Real.rpow_mul hU.le]
  calc
    _ = ((b*A)^6*((b*A)^6)^κ/A)*
        ((U^(1+6*p)*U^((1+6*p+r)*κ))/U^p) := by ring
    _ = ((b*A)^6*((b*A)^6)^κ/A)*U^((1+6*p)+(1+6*p+r)*κ-p) := by
      rw [←Real.rpow_add hU,←Real.rpow_sub hU]
    _ = _ := by congr 2; ring

theorem fixed_multiplier_lower (U A p : ℝ) (hU : 1≤U) (hA : 0≤A) (hp : 0≤p) :
    A≤A*U^p := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_rpow hU hp) hA

theorem amplified_norm_dominates (U A b c r : ℝ) (hU : 1≤U) (hbA : 1≤b*A) :
    (U^r)^(1+c)≤U*(b*(A*U^(amplificationPower c r)))^6 := by
  have hUp : 0<U := zero_lt_one.trans_le hU
  rw [amplified_norm_power U A b _ hUp,←Real.rpow_mul hUp.le]
  have he : r*(1+c)≤1+6*amplificationPower c r := by
    have hh := le_max_right 0 (((1+c)*r-1)/6)
    unfold amplificationPower
    nlinarith
  have hp := Real.rpow_le_rpow_of_exponent_le hU he
  have hconst : (1 : ℝ)≤(b*A)^6 := one_le_pow₀ hbA
  exact hp.trans (le_mul_of_one_le_left (Real.rpow_nonneg hUp.le _) hconst)

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source780

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationRaw.lean; sha256: b769af45d6c89e213a94e1c964486b5c9cfaa186824678a734d44008093e29c6 -/
section Source781
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def RawMoment (data : RowData) (W : ℝ→ℂ) (c κ C : ℝ) : Prop :=
  ∀ H D : ℝ, 1≤H → 0<D → D^(1+c)≤H →
    ∀ rows : Finset NonzeroElement,
      (∀ v∈rows, ((Ideal.span {v.val}).absNorm : ℝ)≤H) →
      ∑ v∈rows, ‖polynomial (data.character v) true W D 0 0‖^2≤
        C*H*(H*max 1 D)^κ

theorem RawMoment.scaleEnergy {data : RowData} {W : ℝ→ℂ} {c κ C : ℝ}
    (hraw : RawMoment data W c κ C) (hc : 0≤c) (hκ : 0≤κ) (hC : 0≤C)
    (U D V : ℝ) (hD : 1≤D) (hH : 1≤U*V^6) (hHD : D^(1+c)≤U*V^6) :
    RawScaleEnergy data W U D V (C*(U*V^6)*((U*V^6)*D)^κ) := by
  intro rows hrows l hl
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hHp : 0<U*V^6 := zero_lt_one.trans_le hH
  have hexp : Real.exp l≤D := by
    rw [←Real.exp_log hDp]
    exact Real.exp_le_exp.mpr hl.2
  have hp : (Real.exp l)^(1+c)≤U*V^6 :=
    (Real.rpow_le_rpow (Real.exp_pos l).le hexp (by linarith)).trans hHD
  have hh := hraw (U*V^6) (Real.exp l) hH (Real.exp_pos l) hp rows hrows
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hHp.le)
  apply Real.rpow_le_rpow (by positivity) _ hκ
  exact mul_le_mul_of_nonneg_left (max_le hD hexp) hHp.le

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source781

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationEndpoint.lean; sha256: 11580ed37a1c8f2ecfd4d58ed1f90836818aaf812d2052c27343c2ac5bd3d5b4 -/
section Source782
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem no_slot_endpoint
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B)
    (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ K : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (r : ℝ) (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb C : ℝ),
      0≤r → r≤R → 0≤C →
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      RawMoment data W c κ C → RawMoment data (scaleProfile W) c κ C →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W (U^r) 0 0‖^2)≤
        C*K*U^(sourceExponent r+ε) := by
  obtain ⟨c,κ,hc,hc1,hκ,hbudget⟩ := exists_amplification_budget R ε hR hε
  obtain ⟨d,hd,havg⟩ := eventually_fixed_ray_amplification M H hH S φ hφ hφc hφp
    hφ0 hφne a b B ha hab hB hφs hφB
  obtain ⟨x0,hx0⟩ := eventually_atTop.mp havg
  let A := max 1 (max x0 (1/b))
  have hb : 0<b := ha.trans_le hab
  have hA : 1≤A := le_max_left _ _
  have hAp : 0<A := zero_lt_one.trans_le hA
  have hAx0 : x0≤A := (le_max_left _ _).trans (le_max_right _ _)
  have hbA : 1≤b*A := by
    have hh : 1/b≤A := (le_max_right _ _).trans (le_max_right _ _)
    have hh' := (div_le_iff₀ hb).mp hh
    nlinarith
  obtain ⟨Klog,hKlog,hlog⟩ := logarithmic_cost_eventually A b (R/3) (ε/2)
    hA hbA (by positivity) (by positivity)
  let F := (b*A)^6*((b*A)^6)^κ/A
  let K := (4/d)*F*Klog
  have hF : 0≤F := by dsimp [F]; positivity
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨c,κ,K,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hlog,eventually_ge_atTop (1 : ℝ)] with U hlog hU
  intro r data rows W wa wb C hr hrR hC hwa hwb hWs hW hrows hraw0 hraw1
  let p := amplificationPower c r
  let x := A*U^p
  let D := U^r
  let V := b*x
  let N := U*V^6
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hp : 0≤p := amplificationPower_nonneg c r
  have hpR : p≤R/3 := amplificationPower_upper c r R hc1 hr hrR
  have hxA : A≤x := fixed_multiplier_lower U A p hU hAp.le hp
  have hV : 1≤V := by
    change 1≤b*(A*U^p)
    rw [←mul_assoc]
    exact one_le_mul_of_one_le_of_one_le hbA (Real.one_le_rpow hU hp)
  have hD : 1≤D := Real.one_le_rpow hU hr
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hN : 1≤N := one_le_mul_of_one_le_of_one_le hU (one_le_pow₀ hV)
  have hDN : D^(1+c)≤N := amplified_norm_dominates U A b c r hU hbA
  have hxb : x*b=V := mul_comm x b
  have hav := hx0 x (hAx0.trans hxA) data rows W wa wb D U
    (C*N*(N*D)^κ) hwa hwb hWs hW hDp hrows
    (by rw [hxb]; exact hraw0.scaleEnergy hc.le hκ.le hC U D V hD hN hDN)
    (by rw [hxb]; exact hraw1.scaleEnergy hc.le hκ.le hC U D V hD hN hDN)
  have hlog' := hlog p hp hpR
  have hnorm : N*(N*D)^κ/x=F*U^(1+5*p+κ*(1+6*p+r)) :=
    amplified_energy_power U A b p r κ hUp
  have hexp := hbudget r hr hrR
  have hpow : U^(1+5*p+κ*(1+6*p+r)+ε/2)≤U^(sourceExponent r+ε) :=
    Real.rpow_le_rpow_of_exponent_le hU (by dsimp [p]; linarith)
  calc
    _ ≤ 4*(1+2*Real.log (x*b))*(C*N*(N*D)^κ)*Real.log x/(d*x) := hav
    _ = C*(4/d)*(N*(N*D)^κ/x)*((1+2*Real.log (b*x))*Real.log x) := by
      rw [mul_comm x b]
      ring
    _ = (C*(4/d)*F)*((1+2*Real.log (b*x))*Real.log x)*
        U^(1+5*p+κ*(1+6*p+r)) := by rw [hnorm]; ring
    _ ≤ (C*(4/d)*F)*(Klog*U^(ε/2))*U^(1+5*p+κ*(1+6*p+r)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUp.le _)
      exact mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ = C*K*U^(1+5*p+κ*(1+6*p+r)+ε/2) := by
      rw [Real.rpow_add hUp (1+5*p+κ*(1+6*p+r)) (ε/2)]
      dsimp [K]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hK)

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source782

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationProfiles.lean; sha256: d3cd9a85d492c9e8472a0b36938ba84a3273e8bfca6a3f3cd91d95524c9e408e -/
section Source783
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Set Filter Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def twistProfile (W : ℝ→ℂ) (σ freq x : ℝ) : ℂ := W x*(x : ℂ)^(-shift σ freq)

theorem twistProfile_support (W : ℝ→ℂ) (σ freq : ℝ) :
    Function.support (twistProfile W σ freq)⊆Function.support W := by
  intro x hx hw
  exact hx (by simp [twistProfile,hw])

theorem polynomial_twistProfile (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) :
    polynomial χ inv (twistProfile W σ freq) D 0 0=polynomial χ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp [summand,twistProfile,HeckeDyadic.shift,mul_assoc]

theorem twistProfile_smooth (W : ℝ→ℂ) (σ freq a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (twistProfile W σ freq) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0<x
  · have he : twistProfile W σ freq =ᶠ[nhds x]
        (fun y : ℝ => W y*Complex.exp ((Real.log y : ℂ)*(-shift σ freq))) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      unfold twistProfile
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
        ←Complex.ofReal_log hy.le]
    apply ContDiffAt.congr_of_eventuallyEq _ he
    apply hW.contDiffAt.mul
    apply Complex.contDiff_exp.contDiffAt.comp x
    have hl : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx.ne')
    exact hl.mul contDiffAt_const
  · have hxa : x<a := lt_of_le_of_lt (le_of_not_gt hx) ha
    have he : twistProfile W σ freq =ᶠ[nhds x] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds hxa] with y hy
      have hw : W y=0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp [twistProfile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source783

/- Original source: OAI/NumberTheory/DirichletL/Moments/DetectorDictionary.lean; sha256: 1c7232a450d47106ef84bb8e2f7d8e3bd649fdf3328e728d358e200d54d81146 -/
section Source784
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentSlotNormalization
local notation "O" => HeckeFamily.O

lemma plain_zero_height (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    polynomial χ false W X 0 0 = (Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W 0 X := by
  rw [sqrt_inverse_cpow X hX]
  unfold polynomial twistedIdealSum
  congr 1
  have he := tsum_subtype_eq_of_support_subset
    (s := {I : Ideal O | I≠0})
    (f := fun I : Ideal O=>idealCoeff χ I*W ((I.absNorm:ℝ)/X))
    (by intro I hI hi; subst I; exact hI (by simp only [map_zero,zero_mul]))
  change (∑' I : HeckeDyadic.NonzeroIdeal,idealCoeff χ I.val*W ((I.val.absNorm:ℝ)/X))=
    ∑' I : Ideal O,idealCoeff χ I*W ((I.absNorm:ℝ)/X) at he
  simpa only [summand,coefficient,Bool.false_eq_true,ite_false,HeckeDyadic.norm,HeckeDyadic.shift,
    Complex.ofReal_zero,zero_mul,mul_zero,sub_zero,neg_zero,Complex.cpow_zero,mul_one,
    HeckeDyadic.NonzeroIdeal,UnrestrictedIdealReindex.NonzeroIdeal] using he

theorem plain_polynomial_eq_row (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W : ℝ→ℂ) (X σ t : ℝ) (hX : 0<X) :
    polynomial χ false W X σ t = (Real.sqrt X:ℂ)⁻¹*
      rowTwistedSum η m A z (twistProfile W σ t) 0 X := by
  rw [←polynomial_twistProfile,plain_zero_height _ _ X hX,rowTwistedSum_eq η χ m A z hrow]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveSlotRow_eq_product
    (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η m A z (twistProfile W₁ σ t) (twistProfile W₂ σ t) S β P 0 X₁ X₂ =
      polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
        ∏i,normalizedSlot η m A z (S i) (β i) 0 (P i) := by
  rw [←selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ (mul_pos hX₁ hX₂).le (fun i=>(hP i).le)]
  unfold selectedProduct
  rw [plain_polynomial_eq_row η χ m A z hrow W₁ X₁ σ t hX₁,
    plain_polynomial_eq_row η χ m A z hrow W₂ X₂ σ t hX₂,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  ring

theorem positiveSlotRow_eq_polynomials
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P σp tp : ι→ℝ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η m A z (twistProfile W₁ σ t) (twistProfile W₂ σ t)
      (fun i=>primePool M H (b i) (P i))
      (fun i=>HeckePrimeAnnular.annularWeight (V i) (P i) (σp i) (tp i)) P 0 X₁ X₂ =
      polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
        ∏i,HeckePrimeRay.rayPrimePolynomial M H χ (V i) (b i) (P i) (σp i) (tp i) := by
  rw [←selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ (mul_pos hX₁ hX₂).le (fun i=>(hP i).le)]
  unfold selectedProduct
  have hslot (i : ι) := CenteredMomentPrimeSlotShift.normalizedSlot_eq_ray M H η χ m A z hrow
    (V i) (b i) (P i) (σp i) 0 (tp i) (hP i)
  simp_rw [hslot]
  simp only [Complex.ofReal_zero,mul_zero,Complex.cpow_zero,one_mul,zero_add]
  rw [plain_polynomial_eq_row η χ m A z hrow W₁ X₁ σ t hX₁,
    plain_polynomial_eq_row η χ m A z hrow W₂ X₂ σ t hX₂,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  ring

theorem oriented_twist_support (reverse : Bool) (W : ℝ→ℂ) (σ t : ℝ) :
    Function.support (twistProfile (HeckeDetectorCoefficientTransfer.orientedProfile reverse W) σ t)
      ⊆Function.support W := by
  apply (twistProfile_support _ _ _).trans
  cases reverse <;> simp only [HeckeDetectorCoefficientTransfer.orientedProfile,ite_true]
  · exact Set.Subset.rfl
  · intro x hx hzero
    exact hx (by simp only [hzero,map_zero])

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end Source784

/- Original source: OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationRowwise.lean; sha256: cce7c7a2c63b24649183bb14120cde67bc43bb1cc088b92d343b1a72c971895f -/
section Source785
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorRowwisePolynomial

def logTest (W : ℝ→ℂ) : ℕ→ℝ→ℂ
  | 0 => W
  | n+1 => logProfile (logTest W n)

theorem logTest_support (W : ℝ→ℂ) (n : ℕ) :
    Function.support (logTest W n)⊆Function.support W := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (logProfile_support (logTest W n)).trans ih

theorem logTest_smooth (W : ℝ→ℂ) (n : ℕ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (logTest W n) := by
  induction n with
  | zero => exact hW
  | succ n ih => exact logProfile_smooth (logTest W n) a b ha ((logTest_support W n).trans hs) ih

theorem no_slot_rowwise_endpoint
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B)
    (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ K : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (r : ℝ) (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb C T : ℝ) (σ freq : FreeRow→ℝ),
      0≤r → r≤R → 0≤C → 0≤T →
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      (∀ u∈rows, σ u∈Icc 0 1) → (∀ u∈rows, freq u∈Icc (-T) T) →
      (∀ n : ℕ, n≤2 → ∀ s∈Icc (0 : ℝ) 1, ∀ t∈Icc (-T) T,
        RawMoment data (twistProfile (logTest W n) s t) c κ C ∧
        RawMoment data (scaleProfile (twistProfile (logTest W n) s t)) c κ C) →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W (U^r) (σ u) (freq u)‖^2)≤
        12*(1+T)*(C*K*U^(sourceExponent r+ε)) := by
  obtain ⟨c,κ,K,hc,hc1,hκ,hK,he⟩ := no_slot_endpoint M H hH S φ hφ hφc hφp hφ0 hφne
    a b B ha hab hB hφs hφB R ε hR hε
  refine ⟨c,κ,K,hc,hc1,hκ,hK,?_⟩
  filter_upwards [he,eventually_ge_atTop (1 : ℝ)] with U he hU
  intro r data rows W wa wb C T σ freq hr hrR hC hT hwa hwb hWs hW hrows hσ hf hraw
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hD : 0<U^r := Real.rpow_pos_of_pos hUp _
  have henergy (n : ℕ) (hn : n≤2) (s : ℝ) (hs : s∈Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t∈Icc (-T) T) :
      ∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true (logTest W n) (U^r) s t‖^2≤
        C*K*U^(sourceExponent r+ε) := by
    have hlW := (logTest_support W n).trans hWs
    have htW := (twistProfile_support (logTest W n) s t).trans hlW
    have hlS := logTest_smooth W n wa wb hwa hWs hW
    have htS := twistProfile_smooth (logTest W n) s t wa wb hwa hlW hlS
    have hh := he r data rows (twistProfile (logTest W n) s t) wa wb C hr hrR hC
      hwa hwb htW htS hrows (hraw n hn s hs t ht).1 (hraw n hn s hs t ht).2
    simpa only [polynomial_twistProfile] using hh
  let Q := scaleSupport (Real.log (U^r)) wb
  have hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/(U^r))≠0 → J∈Q := by
    simpa only [Real.exp_log hD] using scaleSupport_cover W wa wb (Real.log (U^r))
      (Real.log (U^r)) hwb hWs (le_refl _)
  have hh := HeckeDetectorRowwiseMarked.marked_rowwise rows
    (fun u : FreeRow => data.character ⟨u.val,u.property.1⟩) true W (U^r) hD Q hcover
    (fun _ => 1) 0 1 (-T) T (C*K*U^(sourceExponent r+ε)) (by norm_num) (by linarith)
    σ freq hσ hf
    (by simpa only [mul_one,logTest] using henergy 0 (by omega))
    (by simpa only [mul_one,logTest] using henergy 1 (by omega))
    (by simpa only [mul_one,logTest] using henergy 2 (by omega))
  simp only [mul_one] at hh
  refine hh.trans ?_
  have hE : 0≤C*K*U^(sourceExponent r+ε) := by positivity
  nlinarith

end SevenEighths.HeckeInverseAmplification

end

end OAI

end Source785

/- Original source: OAI/NumberTheory/DirichletL/Moments/DetectorDictionaryProfiles.lean; sha256: e0269ea9a9637b66bbf82eae7d776e0cdcccae18fa7413796a2952c128771146 -/
section Source786
namespace OAI

noncomputable section
open scoped Classical ContDiff ComplexConjugate
namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

lemma logTest_eq_iterate (W : ℝ→ℂ) (n : ℕ) : logTest W n=(logProfile^[n]) W := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [logTest,Function.iterate_succ_apply',ih]

lemma oriented_logTest (reverse : Bool) (W : ℝ→ℂ) (n : ℕ) :
    orientedProfile reverse ((logProfile^[n]) W)=logTest (orientedProfile reverse W) n := by
  rw [←logTest_eq_iterate]
  cases reverse
  · rfl
  · induction n with
    | zero => rfl
    | succ n ih =>
      simp only [logTest,orientedProfile,ite_true] at ih ⊢
      funext x
      rw [←logProfile_conjugate]
      exact congrArg (fun f : ℝ→ℂ=>logProfile f x) ih

theorem detector_profile_support (reverse : Bool) (n : ℕ) (σ t : ℝ) :
    Function.support (twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ t)
      ⊆Set.Icc (1/4) (9/4) := by
  apply (oriented_twist_support reverse _ σ t).trans
  rw [←logTest_eq_iterate]
  exact (logTest_support positiveAnnular n).trans positiveAnnular_support

theorem detector_profile_smooth (reverse : Bool) (n : ℕ) (σ t : ℝ) :
    ContDiff ℝ ∞ (twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ t) := by
  apply twistProfile_smooth _ σ t (1/4) (9/4) (by norm_num)
  · cases reverse <;> simp only [orientedProfile,ite_true]
    · rw [←logTest_eq_iterate]
      exact (logTest_support positiveAnnular n).trans positiveAnnular_support
    · rw [conjugate_profile_support,←logTest_eq_iterate]
      exact (logTest_support positiveAnnular n).trans positiveAnnular_support
  · have hw := logTest_smooth positiveAnnular n (1/4) (9/4) (by norm_num)
      positiveAnnular_support positiveAnnular_smooth
    rw [logTest_eq_iterate] at hw
    cases reverse
    · exact hw
    · exact conjugate_profile_smooth _ hw

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end Source786

/- Original source: OAI/NumberTheory/DirichletL/Moments/DetectorDictionaryUniform.lean; sha256: 061aabfa0f4a4cbd471b5ed156c1158683a161b16022bc6dc48129642c47f0c5 -/
section Source787
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeDetectorDyadicProfiles

theorem compact_family_seminorm
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (k n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀p∈J,SchwartzMap.seminorm ℝ k n (G p)≤C := by
  have hc := (section_iteratedDeriv_smooth F hF n).continuous.norm
  obtain ⟨M,hM⟩ := (hJ.prod isCompact_Icc).bddAbove_image hc.continuousOn
  refine ⟨1+L^k*(|M|+1),by positivity,?_⟩
  intro p hp
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro x
  have he : (G p : ℝ→ℂ)=F p := funext (hG p)
  rw [he]
  by_cases hx : x∈Icc (-L) L
  · have hnorm : ‖iteratedDeriv n (F p) x‖≤|M|+1 := by
      have hb := hM (Set.mem_image_of_mem _ (show (p,x)∈J×ˢIcc (-L) L from ⟨hp,hx⟩))
      exact hb.trans (by linarith [le_abs_self M])
    have hxp : ‖x‖^k≤L^k := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using hx
    exact (mul_le_mul hxp hnorm (norm_nonneg _) (pow_nonneg hL k)).trans (by linarith)
  · have hout : iteratedDeriv n (F p) x=0 := by
      by_contra hn
      have hx' := (subset_tsupport (iteratedDeriv n (F p))) hn
      have hh := (CubicReflectionKernel.tsupport_iteratedDeriv_subset (F p) n) hx'
      exact hx ((closure_minimal (hs p) isClosed_Icc) hh)
    rw [hout,norm_zero,mul_zero]
    positivity

theorem compact_family_finite_seminorm
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀p∈J,S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G p)≤C := by
  choose C hC hb using fun z : ℕ×ℕ=>compact_family_seminorm F hF L hL hs J hJ G hG z.1 z.2
  have hsum : 0≤∑z∈S,C z := Finset.sum_nonneg (fun z _=>(hC z).le)
  refine ⟨1+∑z∈S,C z,by linarith,?_⟩
  intro p hp
  apply Seminorm.finset_sup_apply_le (by linarith)
  intro z hz
  apply (hb z p hp).trans
  have hh := Finset.single_le_sum (fun z (_ : z∈S)=>(hC z).le) hz
  linarith

theorem compact_family_frequencyTwist
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀p∈J,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (JointLogSeparation.frequencyTwist (G p) t)≤C*(1+‖t‖)^n := by
  let S' := S.biUnion (fun z=> (Finset.range (z.2+1)).image (fun i=>(z.1,i)))
  obtain ⟨B,hB,hbound⟩ := compact_family_finite_seminorm F hF L hL hs J hJ G hG S'
  let c : ℕ×ℕ→ℝ := fun z=>(2:ℝ)^z.2*(1+2*Real.pi)^z.2*((z.2+1)*B)
  have hc (z : ℕ×ℕ) : 0≤c z := by dsimp [c];positivity
  have hsum : 0≤∑z∈S,c z := Finset.sum_nonneg (fun z _=>hc z)
  refine ⟨S.sup Prod.snd,1+∑z∈S,c z,by linarith,?_⟩
  intro p hp t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hd : JointLogSeparation.derivativeSeminormSum (G p) z.1 z.2≤(z.2+1)*B := by
    unfold JointLogSeparation.derivativeSeminormSum
    calc
      _≤∑i∈Finset.range (z.2+1),B := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : (z.1,i)∈S' := Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
        exact (Seminorm.le_finset_sup_apply hi').trans (hbound p hp)
      _=_ := by simp
  have hzC : c z≤1+∑z∈S,c z := by
    have hh := Finset.single_le_sum (fun z (_ : z∈S)=>hc z) hz
    linarith
  have he := JointLogSeparation.frequencyTwist_seminorm_polynomial (G p) t z.1 z.2
  have hb : SchwartzMap.seminorm ℝ z.1 z.2 (JointLogSeparation.frequencyTwist (G p) t)≤c z*(1+‖t‖)^z.2 := by
    apply he.trans
    dsimp only [c]
    gcongr
  exact hb.trans (mul_le_mul hzC
    (pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Finset.le_sup hz)) (by positivity) (by linarith))

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end Source787

/- Original source: OAI/NumberTheory/DirichletL/Moments/DetectorDictionaryUniformLog.lean; sha256: a4998cbac5b5001efcc83c86914d5fa26456fddb67c907addc70bb4182b2921a -/
section Source788
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic

def realInterpolatedLog (W : ℝ→ℂ) (p : ℝ×ℝ) (x : ℝ) : ℂ :=
  Real.exp (-p.1*x) • W (Real.exp x)

lemma realInterpolatedLog_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (realInterpolatedLog W)) := by
  unfold realInterpolatedLog Function.uncurry
  exact (by fun_prop : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=>Real.exp (-p.1.1*p.2))).smul
    (hW.comp (by fun_prop))

lemma realInterpolatedLog_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (realInterpolatedLog W p)⊆Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro x hx
  have hw : W (Real.exp x)≠0 := by intro hw;exact hx (by simp [realInterpolatedLog,hw])
  have hlo : Real.log a≤x := by simpa only [Real.log_exp] using Real.log_le_log ha (hs hw).1
  have hhi : x≤Real.log b := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos x) (hs hw).2
  constructor <;> linarith [neg_abs_le (Real.log a),le_abs_self (Real.log b),abs_nonneg (Real.log a),abs_nonneg (Real.log b)]

def realInterpolatedLogSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (p : ℝ×ℝ) : 𝓢(ℝ,ℂ) :=
  CubicReflectionKernel.logSchwartz (twistProfile W p.1 0) a b ha
    ((twistProfile_support _ _ _).trans hs) (twistProfile_smooth W p.1 0 a b ha hs hW)

lemma realInterpolatedLogSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (p : ℝ×ℝ) (x : ℝ) :
    realInterpolatedLogSchwartz W a b ha hs hW p x=realInterpolatedLog W p x := by
  rw [realInterpolatedLogSchwartz,CubicReflectionKernel.logSchwartz_apply]
  unfold twistProfile realInterpolatedLog
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ←Complex.ofReal_log (Real.exp_pos x).le,Real.log_exp]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero]
  change W (Real.exp x)*Complex.exp ((x:ℂ)*-(p.1:ℂ))=
    ((Real.exp (-p.1*x):ℝ):ℂ)*W (Real.exp x)
  rw [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]
  have he : (x:ℂ)*-(p.1:ℂ)=-(p.1:ℂ)*(x:ℂ) := by ring
  rw [he,mul_comm]

def interpolatedProfile (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  CenteredMomentLattice.normPowerProfile (twistProfile W σ 0) a b ha
    ((twistProfile_support _ _ _).trans hs) (twistProfile_smooth W σ 0 a b ha hs hW) t

lemma interpolatedProfile_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (σ t x : ℝ) :
    interpolatedProfile W a b ha hs hW σ t x=twistProfile W σ t x := by
  rw [interpolatedProfile,CenteredMomentLattice.normPowerProfile_apply]
  unfold twistProfile
  by_cases hw : W x=0
  · simp [hw]
  · have hx : 0<x := ha.trans_le (hs hw).1
    calc
      _=W x*((x:ℂ)^(Complex.I*t)*(x:ℂ)^(-HeckeDyadic.shift σ 0)) := by ring
      _=W x*(x:ℂ)^(Complex.I*t-HeckeDyadic.shift σ 0) := by
        rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')];rfl
      _=_ := by congr 2;unfold HeckeDyadic.shift;simp only [Complex.ofReal_zero,zero_mul,sub_zero];ring

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end Source788

/- Original source: OAI/NumberTheory/DirichletL/Moments/DetectorDictionaryUniformHeight.lean; sha256: 02786e3187ade1aa46acbca98e597dd96f1e00cf85f464711fad6b4644a4e27c -/
section Source789
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic JointLogSeparation

 theorem interpolatedProfile_uniform (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (interpolatedProfile W a b ha hs hW σ t)≤C*(1+‖t‖)^n := by
  obtain ⟨T,A,hA,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (CompletedHeight.fixedLogReturnCLM a b ha) S
  obtain ⟨n,B,hB,hbound⟩ := compact_family_frequencyTwist
    (realInterpolatedLog W) (realInterpolatedLog_smooth W hW)
    (|Real.log a|+|Real.log b|) (by positivity) (realInterpolatedLog_support W a b ha hs)
    (Icc (0:ℝ) 1 ×ˢ ({0}:Set ℝ)) (isCompact_Icc.prod isCompact_singleton)
    (realInterpolatedLogSchwartz W a b ha hs hW) (realInterpolatedLogSchwartz_apply W a b ha hs hW) T
  refine ⟨n,A*B,mul_pos hA hB,?_⟩
  intro σ hσ t
  have hp : (σ,0)∈Icc (0:ℝ) 1 ×ˢ ({0}:Set ℝ) := ⟨hσ,rfl⟩
  have hheight : ‖t/(2*Real.pi)‖≤‖t‖ := by
    rw [norm_div,Real.norm_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])
  have hh := hcontrol (frequencyTwist (realInterpolatedLogSchwartz W a b ha hs hW (σ,0)) (t/(2*Real.pi)))
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (interpolatedProfile W a b ha hs hW σ t)≤_ at hh
  apply hh.trans
  have hb : T.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (realInterpolatedLogSchwartz W a b ha hs hW (σ,0)) (t/(2*Real.pi)))≤B*(1+‖t‖)^n :=
    (hbound (σ,0) hp (t/(2*Real.pi))).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) n) hB.le)
  exact (mul_le_mul_of_nonneg_left hb hA.le).trans_eq (by ring)

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end Source789

/- Original source: OAI/NumberTheory/DirichletL/Moments/DetectorDictionaryUniformTests.lean; sha256: 2e4a2dfe4c3499924e985ceab3f89f73ff0fba29f2ce844bffec266e0f824043 -/
section Source790
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

lemma twistProfile_zero (W : ℝ→ℂ) : twistProfile W 0 0=W := by
  funext x
  simp [twistProfile,HeckeDyadic.shift]

lemma oriented_detector_log_support (reverse : Bool) (n : ℕ) :
    Function.support (orientedProfile reverse ((logProfile^[n]) positiveAnnular))⊆Icc (1/4) (9/4) := by
  simpa only [twistProfile_zero] using detector_profile_support reverse n 0 0

lemma oriented_detector_log_smooth (reverse : Bool) (n : ℕ) :
    ContDiff ℝ ∞ (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) := by
  simpa only [twistProfile_zero] using detector_profile_smooth reverse n 0 0

def detectorSchwartz (reverse : Bool) (n : ℕ) (σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  interpolatedProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) (1/4) (9/4)
    (by norm_num) (oriented_detector_log_support reverse n) (oriented_detector_log_smooth reverse n) σ
      (orientedFrequency reverse t)

lemma detectorSchwartz_apply (reverse : Bool) (n : ℕ) (σ t x : ℝ) :
    detectorSchwartz reverse n σ t x=
      twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ (orientedFrequency reverse t) x :=
  interpolatedProfile_apply _ _ _ _ _ _ _ _ _

theorem detectorSchwartz_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀reverse : Bool,∀n : ℕ,n≤2→∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorSchwartz reverse n σ t)≤C*(1+‖t‖)^J := by
  choose degree C hC hb using fun q : Bool×Fin 3=>interpolatedProfile_uniform
    (orientedProfile q.1 ((logProfile^[q.2.val]) positiveAnnular)) (1/4) (9/4)
    (by norm_num) (oriented_detector_log_support q.1 q.2.val) (oriented_detector_log_smooth q.1 q.2.val) S
  let J := (Finset.univ : Finset (Bool×Fin 3)).sup degree
  have hsum : 0≤∑q : Bool×Fin 3,C q := Finset.sum_nonneg (fun q _=>(hC q).le)
  refine ⟨J,1+∑q : Bool×Fin 3,C q,by linarith,?_⟩
  intro reverse n hn σ hσ t
  let q : Bool×Fin 3 := (reverse,⟨n,by omega⟩)
  have hCq : C q≤1+∑q : Bool×Fin 3,C q := by
    have hh := Finset.single_le_sum (fun q (_ : q∈(Finset.univ : Finset (Bool×Fin 3)))=>(hC q).le) (Finset.mem_univ q)
    linarith
  have hdegree : degree q≤J := Finset.le_sup (Finset.mem_univ q)
  have he := hb q σ hσ (orientedFrequency reverse t)
  have hnorm : ‖orientedFrequency reverse t‖=‖t‖ := by cases reverse <;> simp [orientedFrequency]
  rw [hnorm] at he
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorSchwartz reverse n σ t)≤_ at he
  exact he.trans (mul_le_mul hCq (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree)
    (by positivity) (by linarith))

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end Source790

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceDetectorProfile.lean; sha256: 5648950eb7c0b420fabf94f0867ece8135a6da9c92695666c4ea5e0b4198978c -/
section Source791
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles CenteredMomentDetectorDictionary
open CenteredMomentLattice CenteredMomentHeckeCancellation CenteredMomentHeckeVolume
open CenteredMomentMask QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma detectorSchwartz_support (reverse : Bool) (n : ℕ) (σ t : ℝ) :
    Function.support (detectorSchwartz reverse n σ t:ℝ→ℂ)⊆Set.Icc (1/4) (9/4) := by
  intro x hx
  change detectorSchwartz reverse n σ t x≠0 at hx
  rw [detectorSchwartz_apply] at hx
  exact detector_profile_support reverse n σ (orientedFrequency reverse t) hx

def detectorNormProfile (reverse : Bool) (n : ℕ) (σ t h : ℝ) : 𝓢(ℝ,ℂ) :=
  normPowerProfile (detectorSchwartz reverse n σ t) (1/4) (9/4) (by norm_num)
    (detectorSchwartz_support reverse n σ t) ((detectorSchwartz reverse n σ t).smooth ⊤) h

lemma orientedFrequency_add_height (reverse : Bool) (t h : ℝ) :
    orientedFrequency reverse (t+orientedFrequency reverse h)=orientedFrequency reverse t+h := by
  cases reverse <;> simp [orientedFrequency] ; ring

theorem detectorNormProfile_eq (reverse : Bool) (n : ℕ) (σ t h : ℝ) :
    detectorNormProfile reverse n σ t h=
      detectorSchwartz reverse n σ (t+orientedFrequency reverse h) := by
  ext x
  rw [detectorNormProfile,normPowerProfile_apply,detectorSchwartz_apply,detectorSchwartz_apply,
    orientedFrequency_add_height]
  unfold twistProfile
  by_cases hw : orientedProfile reverse ((logProfile^[n]) positiveAnnular) x=0
  · simp only [hw,zero_mul,mul_zero]
  · have hx : 0<x := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4)
      ((oriented_detector_log_support reverse n) hw).1
    calc
      _=orientedProfile reverse ((logProfile^[n]) positiveAnnular) x*
          ((x:ℂ)^(Complex.I*h)*(x:ℂ)^(-HeckeDyadic.shift σ (orientedFrequency reverse t))) := by ring
      _=orientedProfile reverse ((logProfile^[n]) positiveAnnular) x*
          (x:ℂ)^(Complex.I*h-HeckeDyadic.shift σ (orientedFrequency reverse t)) := by
        rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')];rfl
      _=_ := by congr 2; unfold HeckeDyadic.shift; push_cast; ring

theorem detectorNormProfile_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀reverse : Bool,∀n : ℕ,n≤2 → ∀σ∈Set.Icc (0:ℝ) 1,∀t h : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorNormProfile reverse n σ t h)≤
        C*(1+‖t‖+‖h‖)^J := by
  obtain ⟨J,C,hC,hbound⟩:=detectorSchwartz_uniform S
  refine ⟨J,C,hC,?_⟩
  intro reverse n hn σ hσ t h
  rw [detectorNormProfile_eq]
  apply (hbound reverse n hn σ hσ (t+orientedFrequency reverse h)).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply pow_le_pow_left₀ (by positivity)
  have he : ‖orientedFrequency reverse h‖=‖h‖ := by cases reverse <;> simp [orientedFrequency]
  have hh:=norm_add_le t (orientedFrequency reverse h)
  rw [he] at hh
  linarith

theorem detector_volumeControl_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀χ : Character,
      (χ.modulus.absNorm:ℝ)≤Z^B → ∀reverse : Bool,∀n : ℕ,n≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t h : ℝ,
      volumeControl Q χ (detectorNormProfile reverse n σ t h)≤C*Z^ε*(1+‖t‖+‖h‖)^J := by
  obtain ⟨J,A,hA,hprofile⟩:=detectorNormProfile_uniform pvSeminorms
  obtain ⟨D,hD,hdiv⟩:=polynomial_mask_divisor_bound ε B hε hB
  refine ⟨J,?_⟩
  intro Q
  let mass : ℝ:=Nat.card (O⧸Ideal.span {fixedPeriod Q})
  let K : ℝ:=D*mass*pvConstant*A
  have hmass : 0≤mass:=Nat.cast_nonneg _
  have hK : 0≤K:=by dsimp [K];exact mul_nonneg (mul_nonneg (mul_nonneg hD.le hmass) pvConstant_pos.le) hA.le
  refine ⟨1+K,by linarith,?_⟩
  intro Z hZ χ hχ reverse n hn σ hσ t h
  have herr : volumeControl Q χ (detectorNormProfile reverse n σ t h)≤
      (D*Z^ε)*(mass*(pvConstant*(A*(1+‖t‖+‖h‖)^J))) := by
    unfold volumeControl pvControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hχ)
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hprofile reverse n hn σ hσ t h) pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg pvConstant_pos.le (apply_nonneg _ _))
    · positivity
  calc
    _≤(D*Z^ε)*(mass*(pvConstant*(A*(1+‖t‖+‖h‖)^J))) := herr
    _=K*Z^ε*(1+‖t‖+‖h‖)^J := by dsimp [K];ring
    _≤(1+K)*Z^ε*(1+‖t‖+‖h‖)^J := by gcongr;linarith

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source791

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceDetectorCancellation.lean; sha256: 302ba7a28bcfc5aec782d9e8f75848d21e8d28d4bfd46b32e5f8492366e7fff3 -/
section Source792
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles CenteredMomentDetectorDictionary
open CenteredMomentLattice CenteredMomentHeckeCancellation CenteredMomentHeckeTwist
open ConcretePrimeRowBridge CenteredMomentHeckeVolume
local notation "O" => HeckeFamily.O

lemma detectorSchwartz_norm_zero_height (reverse : Bool) (n : ℕ) (σ t x : ℝ) :
    ‖detectorSchwartz reverse n σ t x‖=‖detectorSchwartz reverse n σ 0 x‖ := by
  rw [detectorSchwartz_apply,detectorSchwartz_apply]
  unfold twistProfile
  by_cases hw : orientedProfile reverse ((logProfile^[n]) positiveAnnular) x=0
  · simp only [hw,zero_mul]
  · have hx : 0<x := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4)
      ((oriented_detector_log_support reverse n) hw).1
    simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.neg_re,
      HeckeDyadic.shift_re]

lemma detectorSchwartz_absolute :
    ∃A : ℝ,0<A ∧ ∀reverse : Bool,∀n : ℕ,n≤2 → ∀σ∈Set.Icc (0:ℝ) 1,∀t x : ℝ,
      ‖detectorSchwartz reverse n σ t x‖≤A := by
  obtain ⟨J,A,hA,hbound⟩:=detectorSchwartz_uniform {(0,0)}
  refine ⟨A,hA,?_⟩
  intro reverse n hn σ hσ t x
  rw [detectorSchwartz_norm_zero_height]
  apply (SchwartzMap.norm_le_seminorm ℝ (detectorSchwartz reverse n σ 0) x).trans
  simpa using hbound reverse n hn σ hσ 0

theorem detector_rectangle_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
      ∀η χ ψ : Character,(χ.modulus.absNorm:ℝ)≤Z^B → Q≤ψ.modulus →
      CenteredExceptionalProfile.InducedBy χ ψ → ∀m A z : O,goodLambda∣m → (2:O)∣m →
      (∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η) m 1 (A*z) n) →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(
        twistedIdealSum χ (detectorSchwartz r₁ j σ₁ t₁) h X₁*twistedIdealSum χ (detectorSchwartz r₂ k σ₂ t₂) h X₂-
        twistedIdealSum χ (detectorSchwartz r₁ j σ₁ t₁) h Y₁*twistedIdealSum χ (detectorSchwartz r₂ k σ₂ t₂) h Y₂)‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,hJ⟩:=detector_volumeControl_uniform ε B hε hB
  obtain ⟨A0,hA0,habs⟩:=detectorSchwartz_absolute
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hvolume⟩:=hJ Q
  refine ⟨4608*C*A0,by positivity,?_⟩
  intro Z hZ η χ ψ hχ hQψ hind m A z hml hm2 hrow r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let E:=volumeControl Q χ (detectorNormProfile r₁ j σ₁ t₁ h)+
    volumeControl Q χ (detectorNormProfile r₂ k σ₂ t₂ h)
  let H:=1+‖t₁‖+‖t₂‖+‖h‖
  have hH : 0≤H:=by dsimp [H];positivity
  have hp₁ : (1+‖t₁‖+‖h‖)^J≤H^J := pow_le_pow_left₀ (by positivity) (by dsimp [H];linarith [abs_nonneg t₂]) J
  have hp₂ : (1+‖t₂‖+‖h‖)^J≤H^J := pow_le_pow_left₀ (by positivity) (by dsimp [H];linarith [abs_nonneg t₁]) J
  have hE : E≤2*C*Z^ε*H^J := by
    have h₁:=(hvolume Z hZ χ hχ r₁ j hj σ₁ hσ₁ t₁ h).trans
      (mul_le_mul_of_nonneg_left
        hp₁
        (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)))
    have h₂:=(hvolume Z hZ χ hχ r₂ k hk σ₂ hσ₂ t₂ h).trans
      (mul_le_mul_of_nonneg_left
        hp₂
        (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)))
    dsimp only [E]
    linarith
  have hraw:=actual_twisted_rectangle_saving η χ ψ Q hQ hQψ hind m A z hml hm2 hrow
    (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂)
    (1/4) (9/4) (1/4) (9/4) A0 A0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hA0.le hA0.le (detectorSchwartz_support _ _ _ _) (detectorSchwartz_support _ _ _ _)
    ((detectorSchwartz r₁ j σ₁ t₁).smooth ⊤) ((detectorSchwartz r₂ k σ₂ t₂).smooth ⊤)
    (habs r₁ j hj σ₁ hσ₁ t₁) (habs r₂ k hk σ₂ hσ₂ t₂)
    h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T:=hpX ▸ mul_pos (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
  have hn:=CenteredMoment.normalized_centered_saving _ T L (128*((9/4)*A0+(9/4)*A0)) E hT hraw
  have hr : 0≤Real.sqrt T/L:=div_nonneg (Real.sqrt_nonneg _) hL.le
  calc
    _≤4*E*(128*((9/4)*A0+(9/4)*A0))*(Real.sqrt T/L) := hn
    _≤4*(2*C*Z^ε*H^J)*(128*((9/4)*A0+(9/4)*A0))*(Real.sqrt T/L) := by
      gcongr
    _=_ := by dsimp [H];ring

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source792

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceDetectorSlots.lean; sha256: 8077be47cabb4a7b99e1e179da7ae3199a2625332e4c4206caebec122f6ed587 -/
section Source793
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure ConcretePrimeRowBridge CenteredMomentDetectorDictionary
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredExceptionalProfile CenteredMomentHeckeVolume
local notation "O" => HeckeFamily.O

 theorem detector_row_rectangle_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
      ∀η : Character,∀m A z : O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^B → FixedInducingRow η Q m A z →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h X₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h X₂-
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h Y₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h Y₂)‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,hJ⟩:=detector_rectangle_uniform ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro Z hZ η m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  obtain ⟨χ,ψ,hχ,hprim,hind,hQψ,hrow⟩:=fixedInducingRow_controlled η Q m A z hm hA hz hml hm2 hex
  have hχnorm : (χ.modulus.absNorm:ℝ)≤Z^B :=
    (show (χ.modulus.absNorm:ℝ)≤rowConductorBound η m 1 (A*z) by exact_mod_cast hχ).trans hcond
  simp_rw [rowTwistedSum_eq η χ m A z hrow]
  exact hbound Z hZ η χ ψ hχnorm hQψ hind m A z hml hm2 hrow r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

theorem detector_slots_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],∀Z : ℝ,1≤Z →
      ∀η : Character,∀m A z : O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^B → FixedInducingRow η Q m A z →
      ∀S : ι→Finset (Ideal O),∀β : ι→Ideal O→ℂ,∀p b M : ι→ℝ,
      (∀i,0<p i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀P∈S i,‖β i P‖≤M i) → (∀i,∀P∈S i,β i P≠0 → (P.absNorm:ℝ)≤b i*p i) →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂)
        S β p h X₁ X₂ Y₁ Y₂ T‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,p i)/L) := by
  obtain ⟨J,hJ⟩:=detector_row_rectangle_uniform ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι inst Z hZ η m A z hm hA hz hml hm2 hcond hex S β p b M hp hb hM hβ hN
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T:=hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) h‖≤(128*b i*M i)*p i := by
    convert rowSlot_bound η m A z (S i) (β i) h (b i*p i) (M i)
      (mul_nonneg (hb i) (hp i).le) (hM i) (hβ i) (hN i) using 1 ; ring
  exact whole_product_normalization _ (fun i=>rowSlot η m A z (S i) (β i) h)
    (fun i=>128*b i*M i) p (C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J) T L
    (by positivity) hT hL (fun i=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hp hslots
    (hbound Z hZ η m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
      t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source793

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceDetectorCapped.lean; sha256: 428990df3a2e1ee6249b102a286b637042fffd322730afe6b59630e5382a58e6 -/
section Source794
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure ConcretePrimeRowBridge CenteredMomentDetectorDictionary
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredExceptionalProfile CenteredMomentHeckeVolume
open CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O

theorem detector_capped_rectangle_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
      ∀η : Character,∀m A z : O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^B → FixedInducingRow η Q m A z →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h X₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h X₂-
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h Y₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h Y₂)‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(Real.sqrt T/max 1 L) := by
  obtain ⟨J,hJ⟩:=detector_row_rectangle_uniform ε B hε hB
  obtain ⟨A0,hA0,habs⟩:=detectorSchwartz_absolute
  let D : ℝ:=2*(128*(9/4)*A0)*(128*(9/4)*A0)
  have hD : 0≤D:=by dsimp [D];positivity
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcancel⟩:=hJ Q hQ
  refine ⟨C+D,by positivity,?_⟩
  intro Z hZ η m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hpow : 0≤Z^ε:=Real.rpow_nonneg (zero_le_one.trans hZ) _
  by_cases hlarge : 1≤L
  · rw [max_eq_right hlarge]
    exact (hcancel Z hZ η m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
      t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) hpow) (by positivity))
        (div_nonneg (Real.sqrt_nonneg _) hL.le))
  · rw [max_eq_left (le_of_not_ge hlarge),div_one]
    have ha:=normalized_rectangle_absolute η m A z
      (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂)
      (9/4) (9/4) A0 A0 (by norm_num) (by norm_num) hA0.le hA0.le
      (fun x hx=>(detectorSchwartz_support r₁ j σ₁ t₁ hx).2)
      (fun x hx=>(detectorSchwartz_support r₂ k σ₂ t₂ hx).2)
      (habs r₁ j hj σ₁ hσ₁ t₁) (habs r₂ k hk σ₂ hσ₂ t₂)
      h X₁ X₂ Y₁ Y₂ T (hL.trans_le hX₁) (hL.trans_le hX₂)
      (hL.trans_le hY₁) (hL.trans_le hY₂) hpX hpY
    apply ha.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg T)
    calc
      D≤C+D:=le_add_of_nonneg_left hC.le
      _≤(C+D)*Z^ε:=le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hε.le)
      _≤(C+D)*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J:=le_mul_of_one_le_right (by positivity)
        (one_le_pow₀ (by linarith [norm_nonneg t₁,norm_nonneg t₂,norm_nonneg h]))

theorem detector_capped_slots_uniform (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],∀Z : ℝ,1≤Z →
      ∀η : Character,∀m A z : O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^B → FixedInducingRow η Q m A z →
      ∀S : ι→Finset (Ideal O),∀β : ι→Ideal O→ℂ,∀p b M : ι→ℝ,
      (∀i,0<p i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀P∈S i,‖β i P‖≤M i) → (∀i,∀P∈S i,β i P≠0 → (P.absNorm:ℝ)≤b i*p i) →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂)
        S β p h X₁ X₂ Y₁ Y₂ T‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,p i)/max 1 L) := by
  obtain ⟨J,hJ⟩:=detector_capped_rectangle_uniform ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι inst Z hZ η m A z hm hA hz hml hm2 hcond hex S β p b M hp hb hM hβ hN
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T:=hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) h‖≤(128*b i*M i)*p i := by
    convert rowSlot_bound η m A z (S i) (β i) h (b i*p i) (M i)
      (mul_nonneg (hb i) (hp i).le) (hM i) (hβ i) (hN i) using 1 ; ring
  exact whole_product_normalization _ (fun i=>rowSlot η m A z (S i) (β i) h)
    (fun i=>128*b i*M i) p (C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J) T (max 1 L)
    (by positivity) hT (zero_lt_one.trans_le (le_max_left _ _))
    (fun i=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hp hslots
    (hbound Z hZ η m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
      t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source794

/- Original source: OAI/NumberTheory/DirichletL/Moments/AllocatedDetectorCapped.lean; sha256: 2fb1d04237e5a4e48b9afe589e43a42b842712962d55e57ed33ff353b11e60df -/
section Source795
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedDetectorCapped
open HeckeFamily CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorRectangle CenteredMomentAllocatedCenteredCapped
open ConcretePrimeRowBridge CenteredMomentExceptionalCappedAmplitude
local notation "O" => HeckeFamily.O

theorem actual_detector_allocated_capped (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀Z:ℝ,1<Z → ∀η:Character,∀m A z:O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b M:ι→ℝ),
      (∀i,1≤P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀(L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2))),
      ∀r₁ r₂:Bool,∀j k:ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T r:ℝ,Z^r≤X₁ → Z^r≤X₂ → Z^r≤Y₁ → Z^r≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖residualCenteredRow η m A z h S β P L a
        (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂) X₁ X₂ Y₁ Y₂ T‖≤
      C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(∏i:liveIndices L a,128*b i*M i)*
        (Real.sqrt ((T*∏i,P i)/formalReductionFactor L a P)/
          Z^(max (r-Real.logb Z (formalReductionFactor L a P)) 0)):=by
  obtain ⟨J,hJ⟩:=detector_capped_slots_uniform ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι _ _ Z hZ η m A z hm hA hz hmLam hm2 hcond hex S β P b M hP hb hM hβ hN
    L a r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h X₁ X₂ Y₁ Y₂ T r hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hp (i:ι):0<P i:=zero_lt_one.trans_le (hP i)
  have hred:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hp i))
  have hh:=hbound (ι:=liveIndices L a) Z hZ.le η m A z hm hA hz hmLam hm2 hcond hex
    (fun i=>S i) (fun i=>β i) (fun i=>P i) (fun i=>b i) (fun i=>M i)
    (fun i=>hp i) (fun i=>hb i) (fun i=>hM i) (fun i=>hβ i) (fun i=>hN i)
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h
    (X₁/Ideal.absNorm (selectedPlain L a 0)) (X₂/Ideal.absNorm (selectedPlain L a 1))
    (Y₁/Ideal.absNorm (selectedPlain L a 0)) (Y₂/Ideal.absNorm (selectedPlain L a 1))
    (T/selectedNorm L a) (Z^r/formalReductionFactor L a P)
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hred)
    (allocated_lower L a P hP Z r X₁ (zero_lt_one.trans hZ) hX₁ 0)
    (allocated_lower L a P hP Z r X₂ (zero_lt_one.trans hZ) hX₂ 1)
    (allocated_lower L a P hP Z r Y₁ (zero_lt_one.trans hZ) hY₁ 0)
    (allocated_lower L a P hP Z r Y₂ (zero_lt_one.trans hZ) hY₂ 1)
    (by rw [div_mul_div_comm,hXT];rfl) (by rw [div_mul_div_comm,hYT];rfl)
  rw [remaining_volume L a P hp T,max_raw_reduction Z _ r hZ hred] at hh
  exact hh

end SevenEighths.CenteredMomentAllocatedDetectorCapped

end

end OAI

end Source795

/- Original source: OAI/NumberTheory/DirichletL/Moments/AllocatedDetectorAmplitude.lean; sha256: fa9ce867620d3e61439f5ebbac5aeadc057e7527c5c0fd3fc323a7ea67bcfb13 -/
section Source796
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedDetectorAmplitude
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRawEnergy CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentAllocatedDetectorCapped CenteredMomentDetectorDictionary
open ConcretePrimeRowBridge CenteredMomentDivisorRows
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def amplitude (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (z:O):ℂ:=
  (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    allocatedRectangle s.η s.m s.A z s.t s.slots s.coefficient D a s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

def slotControl (s:Data ι):ℝ:=
  (∏i,s.M i)*(∏i,max 1 (128*max 0 (s.hi i)*s.M i))

omit [DecidableEq ι] in
lemma slotControl_nonneg (s:Data ι):0≤slotControl s:=by
  unfold slotControl
  exact mul_nonneg (Finset.prod_nonneg (fun i _=>(zero_le_one.trans (s.M_ge_one i))))
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (le_max_left _ _)))

lemma slot_product_bound (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):
    (∏i∈frozenIndices D a,s.M i)*(∏i:liveIndices D a,128*max 0 (s.hi i)*s.M i)≤slotControl s:=by
  have hf:(∏i∈frozenIndices D a,s.M i)≤∏i,s.M i:=
    Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
  have hl:(∏i:liveIndices D a,128*max 0 (s.hi i)*s.M i)≤∏i,max 1 (128*max 0 (s.hi i)*s.M i):=by
    have he := Finset.prod_coe_sort (liveIndices D a) (fun i:ι=>128*max 0 (s.hi i)*s.M i)
    rw [he]
    apply (Finset.prod_le_prod₀ (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _))
      (zero_le_one.trans (s.M_ge_one i))) (fun i _=>le_max_right 1 _)).trans
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (le_max_left _ _)) (fun i _ _=>le_max_left _ _)
  exact mul_le_mul hf hl (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _)) (zero_le_one.trans (s.M_ge_one i))))
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))

omit [DecidableEq ι] in
lemma coefficient_support (s:Data ι) (i:ι) (I:Ideal O) (hI:s.coefficient i I≠0):
    (Ideal.absNorm I:ℝ)≤max 0 (s.hi i)*s.P i:=by
  have hw:s.W i ((Ideal.absNorm I:ℝ)/s.P i)≠0:=right_ne_zero_of_mul hI
  exact (div_le_iff₀ (s.P_pos i)).mp ((s.support i hw).2.trans (le_max_right _ _))

theorem actual_allocated_amplitude (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀(s:Data ι)(Z:ℝ),1<Z → (∀i,1≤s.P i) →
      ∀z:O,s.m≠0 → s.A≠0 → z≠0 → goodLambda∣s.m → (2:O)∣s.m →
      (HeckeRowClosure.rowConductorBound s.η s.m 1 (s.A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow s.η Q s.m s.A z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))),
      ∀r₁ r₂:Bool,∀j k:ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ r:ℝ,s.W₁=detectorSchwartz r₁ j σ₁ t₁ → s.W₂=detectorSchwartz r₂ k σ₂ t₂ →
      Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ‖amplitude s D a z‖^2≤
        (C*Z^ε*(1+‖t₁‖+‖t₂‖+‖s.t‖)^J*slotControl s)^2*
          (s.X₁*s.X₂*∏i,s.P i)/
          ((formalReductionFactor D a s.P)^2*(Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0))^2):=by
  obtain ⟨J,hJ⟩:=actual_detector_allocated_capped ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcap⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι _ _ s Z hZ hP z hm hA hz hml hm2 hcond hex D a r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ r hW₁ hW₂ hX₁ hX₂ hY₁ hY₂
  have hb:=hcap ι Z hZ s.η s.m s.A z hm hA hz hml hm2 hcond hex s.slots s.coefficient s.P
    (fun i=>max 0 (s.hi i)) s.M hP (fun i=>le_max_left _ _) (fun i=>zero_le_one.trans (s.M_ge_one i))
    s.coefficient_bound (fun i I _ hi=>coefficient_support s i I hi) D a
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ s.t s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) r
    hX₁ hX₂ hY₁ hY₂ rfl s.same_product
  rw [←hW₁,←hW₂] at hb
  have ha:=allocated_raw_energy s.η s.m s.A z s.t s.slots s.prime s.coefficient s.M s.P
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound D a s.W₁ s.W₂
    s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos (mul_pos s.X₁_pos s.X₂_pos)
  have hred:=s.reduction_pos D a
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  let V:=s.X₁*s.X₂*∏i,s.P i
  let d:=formalReductionFactor D a s.P
  let H:=C*Z^ε*(1+‖t₁‖+‖t₂‖+‖s.t‖)^J
  let F:=∏i∈frozenIndices D a,s.M i
  let L:=∏i:liveIndices D a,128*max 0 (s.hi i)*s.M i
  let M:=Z^(max (r-Real.logb Z d) 0)
  have hH:0≤H:=by dsimp [H]; positivity
  have hM:0<M:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hFL:0≤F*L:=mul_nonneg
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
    (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _)) (zero_le_one.trans (s.M_ge_one i))))
  have hp:F*L≤slotControl s:=slot_product_bound s D a
  calc
    ‖amplitude s D a z‖^2≤F^2/d*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=ha
    _≤F^2/d*(H*L*(Real.sqrt (V/d)/M))^2:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (div_nonneg (sq_nonneg _) hred.le)
    _=(H*(F*L))^2*V/(d^2*M^2):=by
      rw [mul_pow,mul_pow,div_pow,Real.sq_sqrt (div_nonneg hraw.le hred.le)]
      dsimp only [V,d]
      field_simp [hred.ne']
    _≤(H*slotControl s)^2*V/(d^2*M^2):=by
      apply div_le_div_of_nonneg_right _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_right _ hraw.le
      exact pow_le_pow_left₀ (mul_nonneg hH hFL) (mul_le_mul_of_nonneg_left hp hH) 2
    _=_:=rfl

end SevenEighths.CenteredMomentAllocatedDetectorAmplitude

end

end OAI

end Source796

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalAmplitudePair.lean; sha256: 6760a1977d0b627cf843aa1603f6e5c2bcaa5ee36685447f2278949393e3ef2f -/
section Source797
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentExceptionalAmplitudePair
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentDetectorDictionary
open CenteredMomentExceptionalAllocationShell ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
universe u

structure Tests where
  reverse : Fin 2→Bool
  index : Fin 2→ℕ
  index_le : ∀j,index j≤2
  sigma : Fin 2→ℝ
  sigma_mem : ∀j,sigma j∈Set.Icc (0:ℝ) 1
  height : Fin 2→ℝ

def Tests.profile (p:Tests) (i:Fin 2):𝓢(ℝ,ℂ):=
  detectorSchwartz (p.reverse i) (p.index i) (p.sigma i) (p.height i)

def Tests.heightWeight (p:Tests) (t:ℝ):ℝ:=1+‖p.height 0‖+‖p.height 1‖+‖t‖

def volume {ι:Type u} [Fintype ι] (s:Data ι):ℝ:=s.X₁*s.X₂*∏i,s.P i

lemma volume_pos {ι:Type u} [Fintype ι] (s:Data ι):0<volume s:=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

def Admissible {ι:Type u} [Fintype ι] (s:Data ι) (p:Tests)
    (Q:Ideal O) (Z B r:ℝ) (z:O):Prop:=
  (∀i,1≤s.P i) ∧ s.m≠0 ∧ s.A≠0 ∧ z≠0 ∧ goodLambda∣s.m ∧ (2:O)∣s.m ∧
  (HeckeRowClosure.rowConductorBound s.η s.m 1 (s.A*z):ℝ)≤Z^B ∧
  CenteredExceptionalProfile.FixedInducingRow s.η Q s.m s.A z ∧
  s.W₁=p.profile 0 ∧ s.W₂=p.profile 1 ∧
  Z^r≤s.X₁ ∧ Z^r≤s.X₂ ∧ Z^r≤s.Y₁ ∧ Z^r≤s.Y₂

lemma norm_le_of_squared (x:ℂ) (H V d M:ℝ) (hH:0≤H) (hV:0≤V) (hd:0<d) (hM:0<M)
    (hb:‖x‖^2≤H^2*V/(d^2*M^2)):
    ‖x‖≤H*Real.sqrt V/(d*M):=by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  convert hb using 1
  rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hV]

lemma reduction_cap_identity {ι κ:Type u} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (s:Data ι) (v:Data κ) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))) (Z r:ℝ) (hZ:1<Z):
    1/(formalReductionFactor D a s.P*formalReductionFactor D b v.P*
      Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0))=
      exceptionalWeight s.toSource v.toSource D a b Z r:=by
  have hz:=zero_lt_one.trans hZ
  unfold exceptionalWeight
  rw [show -Real.logb Z (formalReductionFactor D a s.P)-Real.logb Z (formalReductionFactor D b v.P)-
      max (r-Real.logb Z (formalReductionFactor D a s.P)) 0=
      -(Real.logb Z (formalReductionFactor D a s.P)+Real.logb Z (formalReductionFactor D b v.P)+
        max (r-Real.logb Z (formalReductionFactor D a s.P)) 0) by ring,
    Real.rpow_neg hz.le,Real.rpow_add hz,Real.rpow_add hz,
    Real.rpow_logb hz hZ.ne' (s.reduction_pos D a),Real.rpow_logb hz hZ.ne' (v.reduction_pos D b)]
  exact one_div _

theorem actual_paired_amplitude (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(ι κ:Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ],
      ∀(s:Data ι)(v:Data κ)(p q:Tests)(Z r:ℝ),1<Z → ∀z:O,
      Admissible s p Q Z B r z → Admissible v q Q Z B r z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*Z^(2*ε)*p.heightWeight s.t^J*q.heightWeight v.t^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z r:=by
  obtain ⟨J,hJ⟩:=actual_allocated_amplitude ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι κ _ _ _ _ s v p q Z r hZ z hs hv D a b
  have hpoint (α:Type u) [Fintype α] [DecidableEq α] (s:Data α)(p:Tests)
      (hs:Admissible s p Q Z B r z)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):
      ‖amplitude s D a z‖≤C*Z^ε*p.heightWeight s.t^J*slotControl s*Real.sqrt (volume s)/
        (formalReductionFactor D a s.P*Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0)):=by
    obtain ⟨hP,hm,hA,hz,hml,hm2,hcond,hex,hW₁,hW₂,hX₁,hX₂,hY₁,hY₂⟩:=hs
    apply norm_le_of_squared _ _ _ _ _
    · exact mul_nonneg (by dsimp [Tests.heightWeight]; positivity) (slotControl_nonneg s)
    · exact (volume_pos s).le
    · exact s.reduction_pos D a
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact hbound α s Z hZ hP z hm hA hz hml hm2 hcond hex D a
        (p.reverse 0) (p.reverse 1) (p.index 0) (p.index 1) (p.index_le 0) (p.index_le 1)
        (p.sigma 0) (p.sigma_mem 0) (p.sigma 1) (p.sigma_mem 1)
        (p.height 0) (p.height 1) r hW₁ hW₂ hX₁ hX₂ hY₁ hY₂
  have hl:=hpoint ι s p hs a
  have hr:=hpoint κ v q hv b
  have hcap:1≤Z^(max (r-Real.logb Z (formalReductionFactor D b v.P)) 0):=
    Real.one_le_rpow hZ.le (le_max_right _ _)
  have hr':‖amplitude v D b z‖≤
      C*Z^ε*q.heightWeight v.t^J*slotControl v*Real.sqrt (volume v)/formalReductionFactor D b v.P:=by
    apply hr.trans
    apply div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity) (slotControl_nonneg v)) (Real.sqrt_nonneg _))
      (v.reduction_pos D b)
    exact le_mul_of_one_le_right (v.reduction_pos D b).le hcap
  apply (mul_le_mul hl hr' (norm_nonneg _) (by
    exact div_nonneg (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity)
      (slotControl_nonneg s)) (Real.sqrt_nonneg _)) (mul_nonneg (s.reduction_pos D a).le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))).trans_eq
  rw [←reduction_cap_identity s v D a b Z r hZ]
  have hp:Z^(2*ε)=(Z^ε)^2:=by rw [mul_comm (2:ℝ) ε,Real.rpow_mul (zero_lt_one.trans hZ).le,Real.rpow_two]
  rw [hp]
  ring

end SevenEighths.CenteredMomentExceptionalAmplitudePair

end

end OAI

end Source797

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalSourceShell.lean; sha256: ad25aeeb74a6297a25082bb6e668ac0349beb550198a4c08cbd3440c1db3b872 -/
section Source798
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalSourceShell
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalAllocationShell
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

def profileMass {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Tests)(J:ℕ):ℝ:=
  p.heightWeight s.t^J*q.heightWeight v.t^J*slotControl s*slotControl v*
    Real.sqrt (volume s)*Real.sqrt (volume v)

lemma profileMass_nonneg {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Tests)(J:ℕ):0≤profileMass s v p q J:=by
  unfold profileMass
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity)
    (slotControl_nonneg s)) (slotControl_nonneg v)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem actual_paired_source_shell (ε δ B:ℝ) (hε:0<ε) (hδ:0<δ) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests)(Z r:ℝ),1<Z →
      ∀rows:Finset O,(∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B r z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T:ℝ,1≤T →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        C*(rows.card:ℝ)*(2*T)^(2*δ)*Z^(2*ε+v.toSource.allowance Z-r)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_paired_amplitude ε B hε hB
  obtain ⟨Cs,hCs,hshell⟩:=uniform_subset_shell (ι:=ι) δ hδ
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨Ca,hCa,hpoint⟩:=hJ Q hQ
  refine ⟨Ca*Cs,mul_pos hCa hCs,?_⟩
  intro I L s v p q Z r hZ rows hs hv Ds hD T hT hlo hhi
  have hz:0<Z:=zero_lt_one.trans hZ
  let A:=Ca*Z^(2*ε)*profileMass s v p q J
  have hA:0≤A:=mul_nonneg (mul_nonneg hCa.le (Real.rpow_nonneg hz.le _)) (profileMass_nonneg s v p q J)
  have hp (D:Ideal O)(a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (I⊕Fin 2)))
      (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (L⊕Fin 2))):
      (∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        (rows.card:ℝ)*A*exceptionalWeight s.toSource v.toSource D a b Z r:=by
    calc
      _≤∑z∈rows,A*exceptionalWeight s.toSource v.toSource D a b Z r:=by
        apply Finset.sum_le_sum
        intro z hzrow
        exact (hpoint I L s v p q Z r hZ z (hs z hzrow) (hv z hzrow) D a b).trans_eq (by
          dsimp only [A,profileMass]
          ring)
      _=_:=by simp; ring
  have hsum:=hshell I L s.toSource v.toSource Ds hD T Z r hT hZ hlo hhi
  calc
    _≤∑D∈Ds,∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        (rows.card:ℝ)*A*exceptionalWeight s.toSource v.toSource D a b Z r:=
      Finset.sum_le_sum (fun D _=>Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hp D a b)))
    _=(rows.card:ℝ)*A*(∑D∈Ds,∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        exceptionalWeight s.toSource v.toSource D a b Z r):=by simp only [Finset.mul_sum]
    _≤(rows.card:ℝ)*A*(Cs*(2*T)^(2*δ)*Z^(v.toSource.allowance Z-r)):=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (Nat.cast_nonneg _) hA)
    _=_:=by
      rw [show 2*ε+v.toSource.allowance Z-r=2*ε+(v.toSource.allowance Z-r) by ring,Real.rpow_add hz]
      dsimp only [A]
      ring

end SevenEighths.CenteredMomentExceptionalSourceShell

end

end OAI

end Source798

/- Original source: OAI/NumberTheory/DirichletL/Moments/WholeDivisorShell.lean; sha256: d5f9fe3d51245334263ad7544c285338f37ddfebfadce3070f0938b4a577ab1e -/
section Source799
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentWholeDivisorShell
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentMobiusRegroup CenteredMomentDyadicCount CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

lemma divisorPool_nonzero_norm {α : Type*} (T : Finset α) (B : α→Ideal O)
    (hB : ∀j∈T,B j≠0) (Y : ℝ) (hY : ∀j∈T,(Ideal.absNorm (B j):ℝ)≤Y)
    (D : Ideal O) (hD : D∈divisorPool T B) : D≠0 ∧ (D.absNorm:ℝ)≤Y := by
  obtain ⟨j,hj,hd⟩:=Finset.mem_biUnion.mp hD
  have hdiv := (mem_idealDivisors (hB j hj)).mp hd
  have hn : 0<(B j).absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hB j hj))
  have hle : (D.absNorm:ℝ)≤(B j).absNorm := by
    exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hdiv)
  exact ⟨IdealDivisorBound.divisor_ne_zero (hB j hj) hd,hle.trans (hY j hj)⟩

lemma moebius_norm_le_one (D : Ideal O) : ‖(moebius D:ℂ)‖≤1 := by
  by_cases hD : Squarefree D
  · simp only [hD.moebius_eq,Int.cast_pow,Int.cast_neg,Int.cast_one,norm_pow,norm_neg,norm_one,one_pow,le_refl]
  · simp only [moebius_of_not_squarefree hD,Int.cast_zero,norm_zero,zero_le_one]

lemma squarefree_of_moebius_ne_zero (D : Ideal O) (hD : (moebius D:ℂ)≠0) : Squarefree D := by
  by_contra hn
  exact hD (by rw [moebius_of_not_squarefree hn,Int.cast_zero])

def live (Ds : Finset (Ideal O)) : Finset (Ideal O) := Ds.filter (fun D=>(moebius D:ℂ)≠0)

lemma mem_live (Ds : Finset (Ideal O)) (D : Ideal O) :
    D∈live Ds ↔ D∈Ds ∧ (moebius D:ℂ)≠0 := Finset.mem_filter

lemma live_squarefree (Ds : Finset (Ideal O)) (D : Ideal O) (hD : D∈live Ds) : Squarefree D :=
  squarefree_of_moebius_ne_zero D ((mem_live Ds D).mp hD).2

lemma live_norm_one (Ds : Finset (Ideal O)) (D : Ideal O) (hD : D∈live Ds) : 1≤(D.absNorm:ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (live_squarefree Ds D hD).ne_zero)

theorem sum_moebius_live (Ds : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑D∈Ds,(moebius D:ℂ)*f D)=∑D∈live Ds,(moebius D:ℂ)*f D := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro D hD hn
  have hz : (moebius D:ℂ)=0 := by
    by_contra hne
    exact hn ((mem_live Ds D).mpr ⟨hD,hne⟩)
  rw [hz,zero_mul]

theorem sum_norm_moebius_live (Ds : Finset (Ideal O)) (f : Ideal O→ℝ) :
    (∑D∈Ds,‖(moebius D:ℂ)‖*f D)=∑D∈live Ds,‖(moebius D:ℂ)‖*f D := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro D hD hn
  have hz : (moebius D:ℂ)=0 := by
    by_contra hne
    exact hn ((mem_live Ds D).mpr ⟨hD,hne⟩)
  rw [hz,norm_zero,zero_mul]

def normKey (D : Ideal O) : ℤ := ⌊Real.logb 2 (D.absNorm:ℝ)⌋
def shell (Ds : Finset (Ideal O)) (n : ℤ) : Finset (Ideal O) := (live Ds).filter (fun D=>normKey D=n)
def selectedShells (Ds : Finset (Ideal O)) : Finset ℤ := (live Ds).image normKey

lemma normKey_eq_iff (D : Ideal O) (hD : D≠0) (n : ℤ) :
    normKey D=n ↔ dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  have hn : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hl := Real.logb_le_logb (by norm_num : (1:ℝ)<2) (dyadicScale_pos n) hn
  have hu := Real.logb_lt_logb_iff (by norm_num : (1:ℝ)<2) hn (dyadicScale_pos (n+1))
  simp only [logb_dyadicScale,Int.cast_add,Int.cast_one] at hl hu
  rw [normKey,Int.floor_eq_iff,←hl,←dyadicScale_add,←hu]

lemma mem_shell_iff (Ds : Finset (Ideal O)) (n : ℤ) (D : Ideal O) :
    D∈shell Ds n ↔ D∈Ds ∧ (moebius D:ℂ)≠0 ∧
      dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  rw [shell,Finset.mem_filter]
  constructor
  · rintro ⟨hd,hk⟩
    exact ⟨((mem_live Ds D).mp hd).1,((mem_live Ds D).mp hd).2,
      (normKey_eq_iff D (live_squarefree Ds D hd).ne_zero n).mp hk⟩
  · rintro ⟨hd,hm,hlo,hhi⟩
    exact ⟨(mem_live Ds D).mpr ⟨hd,hm⟩,
      (normKey_eq_iff D (squarefree_of_moebius_ne_zero D hm).ne_zero n).mpr ⟨hlo,hhi⟩⟩

lemma shell_disjoint (Ds : Finset (Ideal O)) (m n : ℤ) (hmn : m≠n) :
    Disjoint (shell Ds m) (shell Ds n) := by
  apply Finset.disjoint_left.mpr
  intro D hm hn
  exact hmn ((Finset.mem_filter.mp hm).2.symm.trans (Finset.mem_filter.mp hn).2)

lemma shell_nonempty_iff (Ds : Finset (Ideal O)) (n : ℤ) :
    (shell Ds n).Nonempty ↔ n∈selectedShells Ds := by
  constructor
  · rintro ⟨D,hD⟩
    exact Finset.mem_image.mpr ⟨D,(Finset.mem_filter.mp hD).1,(Finset.mem_filter.mp hD).2⟩
  · rintro hn
    obtain ⟨D,hD,hk⟩:=Finset.mem_image.mp hn
    exact ⟨D,Finset.mem_filter.mpr ⟨hD,hk⟩⟩

lemma biUnion_shell (Ds : Finset (Ideal O)) :
    (selectedShells Ds).biUnion (shell Ds)=live Ds := by
  ext D
  simp only [Finset.mem_biUnion,shell,Finset.mem_filter]
  constructor
  · rintro ⟨n,hn,hd,hk⟩;exact hd
  · intro hd
    exact ⟨normKey D,Finset.mem_image.mpr ⟨D,hd,rfl⟩,hd,rfl⟩

theorem sum_moebius_shells (Ds : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑D∈Ds,(moebius D:ℂ)*f D)=
      ∑n∈selectedShells Ds,∑D∈shell Ds n,(moebius D:ℂ)*f D := by
  rw [sum_moebius_live]
  exact (Finset.sum_fiberwise_of_maps_to (fun D hD=>Finset.mem_image.mpr ⟨D,hD,rfl⟩) _).symm

theorem sum_norm_moebius_shells (Ds : Finset (Ideal O)) (f : Ideal O→ℝ) :
    (∑D∈Ds,‖(moebius D:ℂ)‖*f D)=
      ∑n∈selectedShells Ds,∑D∈shell Ds n,‖(moebius D:ℂ)‖*f D := by
  rw [sum_norm_moebius_live]
  exact (Finset.sum_fiberwise_of_maps_to (fun D hD=>Finset.mem_image.mpr ⟨D,hD,rfl⟩) _).symm

lemma selected_scale_bounds (Ds : Finset (Ideal O)) (Y : ℝ)
    (hY : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Y)
    (n : ℤ) (hn : n∈selectedShells Ds) :
    1≤dyadicScale n ∧ dyadicScale n≤Y := by
  obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hn
  have hd:=live_squarefree Ds D hD
  have hnorm:=live_norm_one Ds D hD
  have hkey : 0≤normKey D := Int.floor_nonneg.mpr
    (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hnorm)
  have hscale : 1≤dyadicScale (normKey D) := by
    simpa only [dyadicScale,zpow_zero] using
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) hkey
  exact ⟨hscale,((normKey_eq_iff D hd.ne_zero _).mp rfl).1.trans
    (hY D ((mem_live Ds D).mp hD).1 ((mem_live Ds D).mp hD).2)⟩

lemma selected_subset_indices (Ds : Finset (Ideal O)) (Y : ℝ) (hY : 1≤Y)
    (hbound : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Y) :
    selectedShells Ds⊆indices 1 Y := by
  intro n hn
  have hh:=selected_scale_bounds Ds Y hbound n hn
  exact (mem_indices_iff_scale 1 Y (by norm_num) (zero_lt_one.trans_le hY) n).mpr
    ⟨hh.1,hh.2.trans (by linarith)⟩

theorem selected_card_log (B Z : ℝ) (hB : 0≤B) (hZ : 1≤Z)
    (Ds : Finset (Ideal O))
    (hbound : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^B) :
    ((selectedShells Ds).card:ℝ)≤(3+B/Real.log 2)*(1+Real.log Z) := by
  have hY : 1≤Z^B := Real.one_le_rpow hZ hB
  have hc : ((selectedShells Ds).card:ℝ)≤(indices 1 (Z^B)).card := by
    exact_mod_cast Finset.card_le_card (selected_subset_indices Ds (Z^B) hY hbound)
  have hi:=indices_card_log_bound 1 B Z 1 (Z^B) le_rfl hB hZ (by norm_num) hY
    (by simp only [div_one,one_mul,le_refl])
  exact hc.trans (by simpa only [Real.logb_one,add_zero] using hi)

theorem selected_card_subpower (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Ds:Finset (Ideal O),
      (∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^B) →
      ((selectedShells Ds).card:ℝ)≤C*Z^δ := by
  let C:=2*(3+B/Real.log 2)
  have hC : 0<C := by
    have hh:=div_nonneg hB (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [C];linarith
  have ht:=(isLittleO_log_rpow_rpow_atTop (1:ℝ) hδ).bound (by norm_num : (0:ℝ)<1)
  refine ⟨C,hC,?_⟩
  filter_upwards [ht,eventually_ge_atTop (Real.exp 1)] with Z ht hZ
  have hz : 1<Z := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hZ
  have hl : 1≤Real.log Z := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hZ
  have hp : Real.log Z≤Z^δ := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log Z),
      abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hz).le _),one_mul] using ht
  refine ⟨hz,?_⟩
  intro Ds hb
  apply (selected_card_log B Z hB hz.le Ds hb).trans
  have hk : 0≤3+B/Real.log 2 := by positivity
  dsimp [C]
  nlinarith [mul_le_mul_of_nonneg_left hp hk]

theorem divisorPool_card_log {α : Type*} (T : Finset α) (B : α→Ideal O)
    (hB : ∀j∈T,B j≠0) (L Z : ℝ) (hL : 0≤L) (hZ : 1≤Z)
    (hN : ∀j∈T,(Ideal.absNorm (B j):ℝ)≤Z^L) :
    ((selectedShells (divisorPool T B)).card:ℝ)≤(3+L/Real.log 2)*(1+Real.log Z) :=
  selected_card_log L Z hL hZ _ (fun D hD _=>(divisorPool_nonzero_norm T B hB _ hN D hD).2)

theorem divisorPool_card_subpower (L δ : ℝ) (hL : 0≤L) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α:Type*}(T:Finset α)(B:α→Ideal O),
      (∀j∈T,B j≠0) → (∀j∈T,(Ideal.absNorm (B j):ℝ)≤Z^L) →
      ((selectedShells (divisorPool T B)).card:ℝ)≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower L δ hL hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro α T B hB hN
  exact hz.2 _ (fun D hD _=>(divisorPool_nonzero_norm T B hB _ hN D hD).2)

lemma shell_member_data (Ds : Finset (Ideal O)) (n : ℤ) (D : Ideal O)
    (hD : D∈shell Ds n) :
    D∈Ds ∧ (moebius D:ℂ)≠0 ∧ Squarefree D ∧ D≠0 ∧
      dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  have hh:=(mem_shell_iff Ds n D).mp hD
  have hs:=squarefree_of_moebius_ne_zero D hh.2.1
  exact ⟨hh.1,hh.2.1,hs,hs.ne_zero,hh.2.2⟩

theorem finite_pair_mobius_shells {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α→Ideal O) (B : β→Ideal O) (hB : ∀j∈T,B j≠0) (F : α→β→ℂ) :
    (∑i∈S,∑j∈T,if IsCoprime (A i) (B j) then F i j else 0)=
      ∑n∈selectedShells (divisorPool T B),∑D∈shell (divisorPool T B) n,
        (moebius D:ℂ)*∑i∈S,∑j∈T,if D∣A i ∧ D∣B j then F i j else 0 := by
  rw [finite_pair_mobius S T A B hB F]
  exact sum_moebius_shells _ _

theorem divisorPool_weighted_shells {α : Type*} (T : Finset α) (B : α→Ideal O)
    (f : Ideal O→ℝ) :
    (∑D∈divisorPool T B,‖(moebius D:ℂ)‖*f D)=
      ∑n∈selectedShells (divisorPool T B),∑D∈shell (divisorPool T B) n,
        ‖(moebius D:ℂ)‖*f D := sum_norm_moebius_shells _ _

end SevenEighths.CenteredMomentWholeDivisorShell

end

end OAI

end Source799
