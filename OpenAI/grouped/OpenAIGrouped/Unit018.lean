import OpenAIGrouped.Unit017
import OpenAIGrouped.Unit007
import OpenAIGrouped.Unit013
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.MellinInversion
import OpenAIGrouped.Unit016
import OpenAIGrouped.Unit011

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DyadicSource.lean; sha256: 16c4e2b0da614f6532f026074cd804282f39808866c56d2fd40456fb497e2f70 -/
section Source720
namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem source_dyadic_bounds (R dmax τ ε e κ η : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0≤profileBound k) :
    ∃ n : ℕ, ∃ C : ℝ, 0<C ∧
    ∀ (Z d : ℝ), 1≤Z → 0≤d → d≤dmax → 2<Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
      51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
      ∀ (j : ι) (inverse : Bool) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ r σ freq : ℝ, (χ j).modulus.absNorm≤Z^d → 0≤r → r≤R →
      |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
      (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^2*‖mellin W ((x : ℂ)+t*I)‖≤profileBound 2) →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤profileBound (n+2)) →
      ‖polynomial (χ j) inverse W ((Z^d)^r) σ freq‖^2≤C*(Z^d)^((2*a-1)*r+ε) ∧
      ‖polynomial (χ j) false W ((Z^d)^r) σ freq‖^2≤C*(Z^d)^((2*a-1)*min r (1-r)+ε) := by
  obtain ⟨Cd,hCd,hdirect⟩ := scaled_direct_bound e κ he he' hκ hκ'
  obtain ⟨Cr,hCr,hreflect⟩ := scaled_reflected_bound e κ he he' hκ hκ'
  obtain ⟨n,htail⟩ := uniform_external_tail_order τ dmax (2*R+2+η) (R+1)
    hτ hdmax (by positivity) (by positivity)
  let K := Cd+Cr
  have hK : 0<K := add_pos hCd hCr
  let M := K*profileBound 2
  let E := K*profileBound (n+2)*(2 : ℝ)^n
  let C := (M+E)^2+1
  have hM : 0≤M := mul_nonneg hK.le (hprofile 2)
  have hE : 0≤E := mul_nonneg (mul_nonneg hK.le (hprofile (n+2))) (by positivity)
  refine ⟨n,C,by dsimp [C]; positivity,?_⟩
  intro Z d hZ hd hd' hT ι _ χ hχ a i ha ha' hmax j inverse W A B hA hWs hW
    r σ freq hQ hr hrR hfreq hheight hm₂ hmn
  let U := Z^d
  have hU : 1≤U := Real.one_le_rpow hZ hd
  have hV : 0≤Z^τ/2 := by positivity
  have hleft : a+6*e-σ ∈ Icc (1-a-6*e-σ) (2-σ) := ⟨by linarith,by linarith⟩
  have hleft' : 1-a-6*e-σ ∈ Icc (1-a-6*e-σ) (2-σ) := ⟨le_rfl,by linarith⟩
  have hsub : Icc (a+6*e-σ) (2-σ)⊆Icc (1-a-6*e-σ) (2-σ) := by
    intro x hx
    exact ⟨hleft.1.trans hx.1,hx.2⟩
  have hD (inv : Bool) := hdirect χ hχ (Z^τ) a i hT ha ha' hmax j inv W A B hA hWs hW
    U r R η σ freq (Z^τ/2) (profileBound 2) (profileBound (n+2)) n hQ hr hrR hη hV
    hfreq hheight (hprofile 2) (hprofile (n+2))
    (hm₂ _ hleft) (fun x hx => hmn x (hsub hx))
  have hP := hreflect χ hχ (Z^τ) a i hT ha ha' hmax j W A B hA hWs hW
    U r R η σ freq (Z^τ/2) (profileBound 2) (profileBound (n+2)) n hQ hr hrR hη hV
    hfreq hheight (hprofile 2) (hprofile (n+2)) (hm₂ _ hleft') hmn
  have hCdK : Cd≤K := le_add_of_nonneg_right hCr.le
  have hCrK : Cr≤K := le_add_of_nonneg_left hCd.le
  have hnormD (inv : Bool) :
      ‖polynomial (χ j) inv W (U^r) σ freq‖≤
        M*U^((a-1/2)*r+(6*e*r+2*κ+η))+
          K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n := by
    apply (hD inv).trans
    dsimp only [M]
    have hexp : (a-1/2+6*e)*r+2*κ+η=(a-1/2)*r+(6*e*r+2*κ+η) := by ring
    rw [hexp]
    gcongr <;> exact hprofile _
  have hnormP : ‖polynomial (χ j) false W (U^r) σ freq‖≤
      M*U^((a-1/2)*(1-r)+(6*e*(2-r)+4*κ+η))+
        K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n := by
    apply hP.trans
    dsimp only [M]
    have hexp : (a-1/2)*(1-r)+6*e*(2-r)+4*κ+η=
        (a-1/2)*(1-r)+(6*e*(2-r)+4*κ+η) := by ring
    rw [hexp]
    gcongr <;> exact hprofile _
  have hfinish (z : ℂ) (p b : ℝ) (hp : -(R+1)≤p) (hb : 2*b≤ε)
      (hz : ‖z‖≤M*U^(p+b)+K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n) :
      ‖z‖^2≤C*U^(2*p+ε) := by
    have ht := htail Z d p hZ hd hd' hp
    have herror : K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n≤E*U^p := by
      calc
        _ = (K*profileBound (n+2))*(U^(2*R+2+η)/(1+Z^τ/2)^n) := by ring
        _ ≤ (K*profileBound (n+2))*((2 : ℝ)^n*U^p) :=
          mul_le_mul_of_nonneg_left ht (mul_nonneg hK.le (hprofile _))
        _ = _ := by dsimp [E]; ring
    have hn := hz.trans (add_le_add (le_refl _) herror)
    have hs := squared_bound_of_central_and_error z U M E p b ε hU hM hE hε.le hb hn
    apply hs.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    dsimp [C]
    linarith
  have hpos : 0≤(a-1/2)*r := mul_nonneg (by linarith) hr
  have href : -(R+1)≤(a-1/2)*(1-r) := by
    have hp : (a-1/2)*r≤(1/2)*R := mul_le_mul (by linarith) hrR hr (by norm_num)
    nlinarith
  have hbud := central_squared_exponents R a e κ η ε r r hR he.le hκ.le hη hrR hr hbudget
  have hbD : 2*(6*e*r+2*κ+η)≤ε := by nlinarith [hbud.1]
  have hbP : 2*(6*e*(2-r)+4*κ+η)≤ε := by nlinarith [hbud.2]
  have hfinalD (inv : Bool) :
      ‖polynomial (χ j) inv W (U^r) σ freq‖^2≤C*U^((2*a-1)*r+ε) := by
    convert hfinish _ ((a-1/2)*r) (6*e*r+2*κ+η) (by linarith) hbD (hnormD inv) using 1 ;
      congr 2 ; ring
  have hfinalP : ‖polynomial (χ j) false W (U^r) σ freq‖^2≤C*U^((2*a-1)*(1-r)+ε) := by
    convert hfinish _ ((a-1/2)*(1-r)) (6*e*(2-r)+4*κ+η) href hbP hnormP using 1 ;
      congr 2 ; ring
  exact ⟨hfinalD inverse,min_plain_bound _ C U (2*a-1) r ε (hfinalD false) hfinalP⟩

end SevenEighths.HeckeDyadic

end

end OAI

end Source720

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorDyadicBridge.lean; sha256: bcd6a1684cde46e6198037c05268ea4f9b4fe7e2db89eba9682adb8577b6d880 -/
section Source721
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Set Complex
namespace SevenEighths.HeckeDetectorDyadicBridge
open HeckeFamily HeckeDyadic HeckeDetectorFourier

lemma norm_phase (x D : ℝ) (hx : 0<x) (hD : 0<D) (s : ℂ) (t : ℝ) :
    (x : ℂ)^(-s)*FourierBridge.logPhase t (Real.log (x/D)) =
      (D : ℂ)^(-s)*((x/D : ℝ) : ℂ)^(-HeckeDyadic.shift s.re (2*Real.pi*t-s.im)) := by
  have hxD : 0<x/D := div_pos hx hD
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hxD.ne')]
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hD.le,
    ← Complex.ofReal_log hxD.le]
  unfold FourierBridge.logPhase HeckeDyadic.shift
  rw [← Complex.exp_add, ← Complex.exp_add, Real.log_div hx.ne' hD.ne']
  congr 1
  have hs : s=(s.re : ℂ)+(s.im : ℂ)*I := (Complex.re_add_im s).symm
  rw [hs]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
  push_cast
  ring

lemma normalization (D : ℝ) (hD : 0<D) (s : ℂ) :
    (D : ℂ)^((1/2 : ℂ)-s)*(D : ℂ)^(-(1/2 : ℂ))=(D : ℂ)^(-s) := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 1
  ring

lemma polynomial_eq_finite (χ : Character) (inverse : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (S : Finset (Ideal O))
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    polynomial χ inverse W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑ J∈S,
        coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
          (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq) := by
  unfold polynomial
  congr 1
  let f : Ideal O→ℂ := fun J => coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
    (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)
  have hf : Function.support f ⊆ {J : Ideal O | J≠0} := by
    intro J hJ hzero
    subst J
    apply hJ
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have he := tsum_subtype_eq_of_support_subset hf
  change (∑' J : {J : Ideal O // J≠0}, f J.val)=_
  apply he.trans
  apply tsum_eq_sum
  intro J hJ
  by_cases hj : J=0
  · subst J
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have hw : W ((J.absNorm : ℝ)/D)=0 := by
    by_contra hw
    exact hJ (hcover J hj hw)
  simp [f,hw]

theorem phase_sum_eq_polynomial (χ : Character) (inverse : Bool) (W : ℝ→ℂ)
    (D : ℝ) (hD : 0<D) (s : ℂ) (t : ℝ) (S : Finset (Ideal O))
    (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    (∑ J∈S, coefficient χ inverse J*(J.absNorm : ℂ)^(-s)*
      W ((J.absNorm : ℝ)/D)*FourierBridge.logPhase t (Real.log ((J.absNorm : ℝ)/D))) =
      (D : ℂ)^((1/2 : ℂ)-s)*polynomial χ inverse W D s.re (2*Real.pi*t-s.im) := by
  rw [polynomial_eq_finite χ inverse W D s.re (2*Real.pi*t-s.im) S hcover,
    ← mul_assoc, normalization D hD s, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have hnorm : 0<(J.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS J hJ))
  have hp := norm_phase (J.absNorm : ℝ) D hnorm hD s t
  simp only [Complex.ofReal_natCast] at hp
  calc
    _ = coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
        ((J.absNorm : ℂ)^(-s)*FourierBridge.logPhase t (Real.log ((J.absNorm : ℝ)/D))) := by ring
    _ = _ := by rw [hp]; ring

def inverseProfile (V W : ℝ→ℂ) (Dstar D : ℝ) (x : ℝ) : ℂ :=
  V (D*x/Dstar)*W x

lemma inverseProfile_at_norm (V W : ℝ→ℂ) (Dstar D x : ℝ) (hD : 0<D) :
    inverseProfile V W Dstar D (x/D)=V (x/Dstar)*W (x/D) := by
  unfold inverseProfile
  congr 2
  field_simp

lemma weighted_eq (χ : Character) (s : ℂ) (J : Ideal O) (hJ : J≠0) :
    IdealEuler.weighted (idealCoeff χ) s J=idealCoeff χ J*(J.absNorm : ℂ)^(-s) := by
  simp only [IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight, ite_eq_right hJ]

theorem plain_phase_eq (χ : Character) (W : ℝ→ℂ) (D : ℝ) (hD : 0<D)
    (s : ℂ) (t : ℝ) (S : Finset (Ideal O)) (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    phasePolynomial S (plainCoefficient χ W D s)
      (fun J => Real.log ((J.absNorm : ℝ)/D)) t =
      (D : ℂ)^((1/2 : ℂ)-s)*polynomial χ false W D s.re (2*Real.pi*t-s.im) := by
  rw [← phase_sum_eq_polynomial χ false W D hD s t S hS hcover]
  unfold phasePolynomial
  apply Finset.sum_congr rfl
  intro J hJ
  rw [plainCoefficient, weighted_eq χ s J (hS J hJ)]
  rfl

theorem inverse_phase_eq (χ : Character) (V W : ℝ→ℂ) (Dstar D : ℝ) (hD : 0<D)
    (s : ℂ) (t : ℝ) (S : Finset (Ideal O)) (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → inverseProfile V W Dstar D ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    phasePolynomial S (inverseCoefficient χ V W Dstar D s)
      (fun J => Real.log ((J.absNorm : ℝ)/D)) t =
      (D : ℂ)^((1/2 : ℂ)-s)*
        polynomial χ true (inverseProfile V W Dstar D) D s.re (2*Real.pi*t-s.im) := by
  rw [← phase_sum_eq_polynomial χ true (inverseProfile V W Dstar D) D hD s t S hS hcover]
  unfold phasePolynomial
  apply Finset.sum_congr rfl
  intro J hJ
  rw [inverseCoefficient, weighted_eq χ s J (hS J hJ), inverseProfile_at_norm V W Dstar D _ hD]
  simp only [coefficient, ite_true]
  ring

lemma normalization_norm (D : ℝ) (hD : 0<D) (s : ℂ) :
    ‖(D : ℂ)^((1/2 : ℂ)-s)‖=D^(1/2-s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]
  congr 1
  simp

theorem pair_phase_norm (χ : Character) (V W₁ W₂ : ℝ→ℂ) (Dstar D N : ℝ)
    (hD : 0<D) (hN : 0<N) (s : ℂ) (t : ℝ) (S R : Finset (Ideal O))
    (hS : ∀ J∈S, J≠0) (hR : ∀ J∈R, J≠0)
    (hcoverS : ∀ J : Ideal O, J≠0 → inverseProfile V W₁ Dstar D ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (hcoverR : ∀ J : Ideal O, J≠0 → W₂ ((J.absNorm : ℝ)/N)≠0 → J∈R) :
    ‖phasePolynomial S (inverseCoefficient χ V W₁ Dstar D s)
        (fun J => Real.log ((J.absNorm : ℝ)/D)) t‖ *
      ‖phasePolynomial R (plainCoefficient χ W₂ N s)
        (fun J => Real.log ((J.absNorm : ℝ)/N)) t‖ =
      D^(1/2-s.re)*N^(1/2-s.re)*
        (‖polynomial χ true (inverseProfile V W₁ Dstar D) D s.re (2*Real.pi*t-s.im)‖ *
         ‖polynomial χ false W₂ N s.re (2*Real.pi*t-s.im)‖) := by
  rw [inverse_phase_eq χ V W₁ Dstar D hD s t S hS hcoverS,
    plain_phase_eq χ W₂ N hN s t R hR hcoverR,
    norm_mul, norm_mul, normalization_norm D hD s, normalization_norm N hN s]
  ring

end SevenEighths.HeckeDetectorDyadicBridge

end

end OAI

end Source721

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorFinite.lean; sha256: 1cad5f111e1143f0095b5a5663ffe5dd05a6f6900a5d64b3f00f22085127a997 -/
section Source722
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorFinite
open HeckeFamily HeckeDetectorWitnessArithmetic HeckeDetectorTail HeckeDetectorPartition
open CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def pairSet (U : ℝ) : Finset (Ideal O × Ideal O) :=
  (idealsUpTo ⌈2*U⌉₊) ×ˢ (idealsUpTo ⌈2*U⌉₊)

lemma pairCoefficient_zero_left (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (J : Ideal O) :
    pairCoefficient χ V T D Y U s (0,J) = 0 := by
  simp only [pairCoefficient,zero_mul,map_zero,mul_zero]

lemma pairCoefficient_zero_right (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (J : Ideal O) :
    pairCoefficient χ V T D Y U s (J,0) = 0 := by
  simp only [pairCoefficient,mul_zero,map_zero,zero_mul]

theorem pairCoefficient_support (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ)
    (p : Ideal O × Ideal O) (hp : p ∉ pairSet U) :
    pairCoefficient χ V T D Y U s p = 0 := by
  by_cases h1 : p.1 = 0
  · change pairCoefficient χ V T D Y U s (p.1,p.2) = 0
    rw [h1]
    exact pairCoefficient_zero_left χ V T D Y U s p.2
  by_cases h2 : p.2 = 0
  · change pairCoefficient χ V T D Y U s (p.1,p.2) = 0
    rw [h2]
    exact pairCoefficient_zero_right χ V T D Y U s p.1
  have hprod : p.1*p.2 ≠ 0 := mul_ne_zero h1 h2
  have hnpos : 0 < Ideal.absNorm (p.1*p.2) := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hprod)
  have hnorm : 2*U ≤ (Ideal.absNorm (p.1*p.2) : ℝ) := by
    by_contra h
    have hb : Ideal.absNorm (p.1*p.2) ≤ ⌈2*U⌉₊ := by
      exact_mod_cast (le_trans (lt_of_not_ge h).le (Nat.le_ceil (2*U)))
    have hh1 : Ideal.absNorm p.1 ≤ Ideal.absNorm (p.1*p.2) :=
      Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm (dvd_mul_right p.1 p.2))
    have hh2 : Ideal.absNorm p.2 ≤ Ideal.absNorm (p.1*p.2) :=
      Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm (dvd_mul_left p.2 p.1))
    apply hp
    exact Finset.mem_product.mpr
      ⟨mem_idealsUpTo.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h1),hh1.trans hb⟩,
       mem_idealsUpTo.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h2),hh2.trans hb⟩⟩
  have hz := hT ((Ideal.absNorm (p.1*p.2) : ℝ)/U) ((le_div_iff₀ hU).mpr hnorm)
  simp only [pairCoefficient,hz,mul_zero]

theorem pair_fiber (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) :
    (∑' p : MulFiber I, pairCoefficient χ V T D Y U s p.val) =
      terminalTerm χ V T D Y U s I := by
  have h := weighted_fiber χ V D s I
  unfold terminalTerm exponentialTerm
  rw [←h,←tsum_mul_right,←tsum_mul_right,←tsum_mul_right]
  apply tsum_congr
  intro p
  simp only [pairCoefficient,p.property]

theorem terminal_sum_eq_pair_sum (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ p ∈ pairSet U, pairCoefficient χ V T D Y U s p := by
  have hfinite : Function.HasFiniteSupport (pairCoefficient χ V T D Y U s) := by
    apply (pairSet U).finite_toSet.subset
    intro p hp
    by_contra hn
    exact hp (pairCoefficient_support χ V T D Y U hU hT s p hn)
  have hsum := (summable_of_hasFiniteSupport hfinite).hasSum.tsum_fiberwise
    (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun I : Ideal O => ∑' p : MulFiber I, pairCoefficient χ V T D Y U s p.val)
    (∑' p, pairCoefficient χ V T D Y U s p) at hsum
  simp_rw [pair_fiber] at hsum
  rw [hsum.tsum_eq]
  exact tsum_eq_sum (pairCoefficient_support χ V T D Y U hU hT s)

def dyadicBlock (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (j k : ℕ) : ℂ :=
  ∑ p ∈ pairSet U, pairCoefficient χ V T D Y U s p *
    DyadicTransfer.annularCutoff V ((Ideal.absNorm p.1 : ℝ)/(2 : ℝ)^j) *
    DyadicTransfer.annularCutoff V ((Ideal.absNorm p.2 : ℝ)/(2 : ℝ)^k)

theorem terminal_sum_eq_dyadic (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ j ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
        ∑ k ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1), dyadicBlock χ V T D Y U s j k := by
  have hX : (0 : ℝ) < ⌈2*U⌉₊ := lt_of_lt_of_le (by positivity) (Nat.le_ceil (2*U))
  rw [terminal_sum_eq_pair_sum χ V T D Y U hU hT s]
  apply actual_pair_reassembly χ V T hV hVzero D Y U _ _ hX hX s
  intro p hp
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
  obtain ⟨hp1,hp1b⟩ := mem_idealsUpTo.mp h1
  obtain ⟨hp2,hp2b⟩ := mem_idealsUpTo.mp h2
  exact ⟨Ideal.absNorm_eq_zero_iff.not.mp (by omega),
    Ideal.absNorm_eq_zero_iff.not.mp (by omega),by exact_mod_cast hp1b,by exact_mod_cast hp2b⟩

theorem exists_dyadic_block (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (c : ℝ)
    (hc : c ≤ ‖∑' I : Ideal O, terminalTerm χ V T D Y U s I‖) :
    ∃ j ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
      ∃ k ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
        c ≤ (((length (⌈2*U⌉₊ : ℝ)+1 : ℕ) : ℝ)^2)*‖dyadicBlock χ V T D Y U s j k‖ := by
  rw [terminal_sum_eq_dyadic χ V T D Y U hU hT hV hVzero s] at hc
  obtain ⟨j,hj,k,hk,hb⟩ := exists_large_pair (length (⌈2*U⌉₊ : ℝ))
    (length (⌈2*U⌉₊ : ℝ)) (dyadicBlock χ V T D Y U s)
  exact ⟨j,hj,k,hk,by simpa only [pow_two] using hc.trans hb⟩

theorem nonzero_block_scale_bounds (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hD : 0 < D) (hU : 0 < U)
    (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (j k : ℕ)
    (hb : dyadicBlock χ V T D Y U s j k ≠ 0) :
    (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
      (2 : ℝ)^j*(2 : ℝ)^k < 8*U := by
  obtain ⟨p,hp,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hk := (mul_ne_zero_iff.mp hne).2
  have hj := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2
  have hc := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1
  simp only [pairCoefficient,ne_eq,mul_eq_zero,not_or] at hc
  obtain ⟨⟨⟨⟨⟨hmu,hfirst⟩,hweight⟩,hexp⟩,hproduct⟩,hterminal⟩ := hc
  apply pair_scale_bounds V T hV hVzero hT
    (Ideal.absNorm p.1) (Ideal.absNorm p.2) D U (by positivity) (by positivity)
    hD hU j k hj hk hfirst
  · simpa only [map_mul,Nat.cast_mul] using hproduct
  · simpa only [map_mul,Nat.cast_mul] using hterminal

end SevenEighths.HeckeDetectorFinite

end

end OAI

end Source722

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorDyadicSupport.lean; sha256: 467a4c3d414ff91b1411e18eff8955a42978291a301c777e1318a0bd9292c3b2 -/
section Source723
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorDyadicBridge
open HeckeFamily HeckeDetectorFinite HeckeDetectorPartition
open CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def fourierSet (U : ℝ) : Finset (Ideal O) := idealsUpTo ⌈16*U⌉₊

lemma fourierSet_nonzero (U : ℝ) (J : Ideal O) (hJ : J∈fourierSet U) : J≠0 := by
  have hn := (mem_idealsUpTo.mp hJ).1
  exact Ideal.absNorm_eq_zero_iff.not.mp (by omega)

lemma pairSet_subset_fourier (U : ℝ) (hU : 0≤U) :
    pairSet U ⊆ fourierSet U ×ˢ fourierSet U := by
  intro p hp
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
  have hb : ⌈2*U⌉₊ ≤ ⌈16*U⌉₊ := Nat.ceil_mono (by linarith)
  exact Finset.mem_product.mpr
    ⟨mem_idealsUpTo.mpr ⟨(mem_idealsUpTo.mp h1).1,(mem_idealsUpTo.mp h1).2.trans hb⟩,
     mem_idealsUpTo.mpr ⟨(mem_idealsUpTo.mp h2).1,(mem_idealsUpTo.mp h2).2.trans hb⟩⟩

lemma annular_covered (U D : ℝ) (hD : 0<D) (hDU : D≤8*U)
    (W : ℝ→ℂ) (hW : ∀ x : ℝ, 2≤x → W x=0)
    (J : Ideal O) (hJ : J≠0) (hw : W ((J.absNorm : ℝ)/D)≠0) :
    J∈fourierSet U := by
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ),?_⟩
  have hr : (J.absNorm : ℝ)/D<2 := lt_of_not_ge (fun hn => hw (hW _ hn))
  have hn : (J.absNorm : ℝ)≤16*U := by
    have hh := (div_lt_iff₀ hD).mp hr
    linarith
  exact_mod_cast hn.trans (Nat.le_ceil (16*U))

lemma inverse_annular_covered (U D Dstar : ℝ) (hD : 0<D) (hDU : D≤8*U)
    (V W : ℝ→ℂ) (hW : ∀ x : ℝ, 2≤x → W x=0)
    (J : Ideal O) (hJ : J≠0) (hw : inverseProfile V W Dstar D ((J.absNorm : ℝ)/D)≠0) :
    J∈fourierSet U := by
  apply annular_covered U D hD hDU W hW J hJ
  exact (mul_ne_zero_iff.mp hw).2

lemma scales_le_eight_terminal (U : ℝ) (j k : ℕ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U) :
    (2 : ℝ)^j≤8*U ∧ (2 : ℝ)^k≤8*U := by
  have hj : 1≤(2 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hk : 1≤(2 : ℝ)^k := one_le_pow₀ (by norm_num)
  constructor
  · exact (le_mul_of_one_le_right (by positivity) hk).trans hprod.le
  · exact (le_mul_of_one_le_left (by positivity) hj).trans hprod.le

theorem dyadicBlock_eq_fourier_rectangle (χ : Character) (V T : ℝ→ℂ)
    (D Y U : ℝ) (hU : 0<U) (hT : ∀ x : ℝ, 2≤x → T x=0)
    (s : ℂ) (j k : ℕ) :
    dyadicBlock χ V T D Y U s j k =
      ∑ J∈fourierSet U, ∑ K∈fourierSet U,
        pairCoefficient χ V T D Y U s (J,K)*
          DyadicTransfer.annularCutoff V ((J.absNorm : ℝ)/(2 : ℝ)^j)*
          DyadicTransfer.annularCutoff V ((K.absNorm : ℝ)/(2 : ℝ)^k) := by
  unfold dyadicBlock
  calc
    _ = ∑ p∈fourierSet U ×ˢ fourierSet U,
        pairCoefficient χ V T D Y U s p *
          DyadicTransfer.annularCutoff V ((p.1.absNorm : ℝ)/(2 : ℝ)^j) *
          DyadicTransfer.annularCutoff V ((p.2.absNorm : ℝ)/(2 : ℝ)^k) := by
      apply Finset.sum_subset (pairSet_subset_fourier U hU.le)
      intro p hp hn
      rw [pairCoefficient_support χ V T D Y U hU hT s p hn, zero_mul, zero_mul]
    _ = _ := Finset.sum_product _ _ _

end SevenEighths.HeckeDetectorDyadicBridge

end

end OAI

end Source723

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorFrequency.lean; sha256: 747c68ae236e9f8431be90600b8ba9649e62a2f54a57a7ca20a63fd331c6409f -/
section Source724
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open MeasureTheory
namespace SevenEighths.HeckeDetectorFrequency
open HeckeFamily HeckeDetectorProfiles HeckeDetectorFourier
open HeckeDetectorCoefficientBounds HeckeDetectorFinite HeckeDetectorDyadicBridge
local notation "O" => HeckeFamily.O

theorem dyadic_frequency_bound (Ω : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L)
    (hΩone : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      DyadicTransfer.annularCutoff cutoff x ≠ 0 →
      DyadicTransfer.annularCutoff cutoff y ≠ 0 → Ω (Real.log x+Real.log y)=1)
    (n : ℕ) :
    ∃ C₀ Cn : ℝ, 1 ≤ C₀ ∧ 0 ≤ Cn ∧ ∀ (U Dstar F : ℝ),
      1 ≤ U → 0 < Dstar → 0 < F → ∀ (χ : Character) (s : ℂ), 0 ≤ s.re →
      ∀ j k : ℕ, ∃ t : ℝ, ‖t‖ ≤ F ∧
        ‖dyadicBlock χ cutoff cutoff Dstar (U^20) (U^21) s j k‖ ≤
          (67108864*U^42)*Cn/F^n + C₀*
            ‖phasePolynomial (expandedSet U)
                (inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar ((2 : ℝ)^j) s)
                (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^j)) t *
              phasePolynomial (expandedSet U)
                (plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) ((2 : ℝ)^k) s)
                (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^k)) t‖ := by
  obtain ⟨C₀,hC₀,hb₀⟩ := uniform_fourier_moment Ω cutoff cutoff hΩc hΩ L hL hwindow 0
  obtain ⟨Cn,hCn,hbn⟩ := uniform_fourier_moment Ω cutoff cutoff hΩc hΩ L hL hwindow n
  refine ⟨1+C₀,Cn,by linarith,hCn,?_⟩
  intro U Dstar F hU hDstar hF χ s hs j k
  let D : ℝ := (2 : ℝ)^j
  let N : ℝ := (2 : ℝ)^k
  let a := inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar D s
  let b := plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) N s
  let x := fun I : Ideal O => Real.log ((Ideal.absNorm I : ℝ)/D)
  let y := fun I : Ideal O => Real.log ((Ideal.absNorm I : ℝ)/N)
  let g := logSource Ω cutoff cutoff hΩc hΩ (cutoff.smooth ⊤) (cutoff.smooth ⊤)
    (2*D*N/Dstar) (D*N/U^20) (D*N/U^21)
  have hUpos : 0 < U := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have heq : dyadicBlock χ cutoff cutoff Dstar (U^20) (U^21) s j k =
      ∑ I ∈ expandedSet U, ∑ J ∈ expandedSet U, a I*b J*g (x I+y J) := by
    rw [dyadicBlock_eq_fourier_rectangle χ cutoff cutoff Dstar (U^20) (U^21)
      (by positivity) cutoff_zero s j k]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    exact actual_pair_profile χ Ω cutoff cutoff (DyadicTransfer.annularCutoff cutoff)
      (DyadicTransfer.annularCutoff cutoff) Dstar D N (U^20) (U^21) hD hN s I J
      (fourierSet_nonzero _ I hI) (fourierSet_nonzero _ J hJ)
      (hΩone _ _ (by positivity) (by positivity))
  obtain ⟨t,ht,hb⟩ := exists_bounded_frequency (expandedSet U) (expandedSet U) a b x y g F hF n
  refine ⟨t,ht,?_⟩
  rw [heq]
  have hg₀ : (∫ t : ℝ, ‖(𝓕 g) t‖) ≤ C₀ := by
    simpa only [pow_zero,one_mul] using hb₀ (2*D*N/Dstar) (D*N/U^20) (D*N/U^21)
      (by positivity) (by positivity) (by positivity)
  have hgn : (∫ t : ℝ, (1+‖t‖)^n*‖(𝓕 g) t‖) ≤ Cn :=
    hbn (2*D*N/Dstar) (D*N/U^20) (D*N/U^21) (by positivity) (by positivity) (by positivity)
  have hmass := coefficient_mass χ cutoff cutoff_norm_le U Dstar D N hU s hs
  apply hb.trans
  apply add_le_add
  · calc
      _ ≤ ((67108864*U^42)/F^n)*Cn := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right hmass (by positivity)
        · exact hgn
        · exact integral_nonneg (fun t => by positivity)
        · positivity
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_right (hg₀.trans (by linarith)) (norm_nonneg _)

end SevenEighths.HeckeDetectorFrequency

end

end OAI

end Source724

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorFrequencyTail.lean; sha256: 3b0c035a218d31b8aacba0106d2e9d8c726b895046c391494ec87c3311fa98dc -/
section Source725
namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace SevenEighths.HeckeDetectorFrequency

lemma logb_square_div_rpow_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun U : ℝ => (Real.logb 2 U)^2/U^a) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) ha).tendsto_div_nhds_zero
  have h' := h.const_mul ((Real.log 2)^2)⁻¹
  convert h' using 1
  · ext U
    rw [Real.rpow_two,Real.logb]
    ring
  · ring_nf

theorem exists_frequency_tail_order (τ : ℝ) (hτ : 0 < τ) :
    ∃ n : ℕ, ∀ C : ℝ, ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      (625*(Real.logb 2 U)^2)*((67108864*U^42)*C/(U^τ)^n) ≤ 1/4 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (43/τ)
  have he : 0 < τ*(n : ℝ)-42 := by
    have hh := (div_lt_iff₀ hτ).mp hn
    nlinarith
  refine ⟨n,?_⟩
  intro C
  have ht := (logb_square_div_rpow_tendsto (τ*(n : ℝ)-42) he).const_mul (625*67108864*C)
  have ht' : Tendsto
      (fun U : ℝ => (625*(Real.logb 2 U)^2)*((67108864*U^42)*C/(U^τ)^n))
      atTop (𝓝 0) := by
    apply (show Tendsto (fun U : ℝ => (625*67108864*C)*
      ((Real.logb 2 U)^2/U^(τ*(n : ℝ)-42))) atTop (𝓝 0) by simpa using ht).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
    rw [Real.rpow_sub hU,Real.rpow_mul_natCast hU.le,
      show (42 : ℝ)=((42 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
    field_simp
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht').2 (1/4) (by norm_num))
  exact ⟨U₀,fun U hU hU1 => (hU₀ U hU).le⟩

end SevenEighths.HeckeDetectorFrequency

end

end OAI

end Source725

/- Original source: OAI/NumberTheory/DirichletL/GammaZeroDetector.lean; sha256: 3ec3bab7d9c8bd0e3a0d4b94738147d6f002b405a539547df172d1751489f60b -/
section Source726
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex

namespace SevenEighths.GammaZeroDetector

theorem gamma_shift (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    Gamma (z + n) = Gamma z * ∏ k ∈ Finset.range n, (z + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : z + n ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp only [add_im, natCast_im, add_zero, zero_im] at this
      exact hz this
    rw [Nat.cast_succ, ← add_assoc, Gamma_add_one _ hn, ih, Finset.prod_range_succ]
    ring

theorem gamma_shift_norm_lower (z : ℂ) (n : ℕ) :
    |z.im| ^ n ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ := by
  rw [norm_prod]
  calc
    _ = ∏ _k ∈ Finset.range n, |z.im| := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro k _
      simpa using Complex.abs_im_le_norm (z + k)

theorem gamma_power_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      |z.im| ^ n * ‖Gamma z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := CubicGammaExponential.real_Gamma_compact_bound
    (a + n) (b + n) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro z hza hzb hzi
  have hzne : z.im ≠ 0 := by intro h; norm_num [h] at hzi
  have hzre : 0 < (z + n).re := by simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ * ‖Gamma z‖ :=
      mul_le_mul_of_nonneg_right (gamma_shift_norm_lower z n) (norm_nonneg _)
    _ = ‖Gamma (z + n)‖ := by rw [gamma_shift z hzne n, norm_mul, mul_comm]
    _ ≤ Real.Gamma (z + n).re := CubicGammaExponential.norm_Gamma_le_real _ hzre
    _ ≤ C := hbound _ (by simp only [add_re, natCast_re]; constructor <;> linarith)

theorem gamma_rapid_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      (1 + |z.im|) ^ n * ‖Gamma z‖ ≤ C := by
  obtain ⟨C₁, hC₁, hlarge⟩ := gamma_power_bound a b ha n
  obtain ⟨C₀, hC₀, hsmall⟩ := CubicGammaExponential.real_Gamma_compact_bound a b ha
  refine ⟨2 ^ n * (C₀ + C₁), by positivity, ?_⟩
  intro z hza hzb
  by_cases ht : 1 ≤ |z.im|
  · have hp : (1 + |z.im|) ^ n ≤ 2 ^ n * |z.im| ^ n := by
      rw [← mul_pow]
      gcongr
      linarith
    calc
      _ ≤ (2 ^ n * |z.im| ^ n) * ‖Gamma z‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ 2 ^ n * C₁ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hlarge z hza hzb ht) (by positivity)
      _ ≤ _ := by gcongr; linarith
  · have hg : ‖Gamma z‖ ≤ C₀ :=
      (CubicGammaExponential.norm_Gamma_le_real z (ha.trans_le hza)).trans (hsmall z.re ⟨hza,hzb⟩)
    have hp : (1 + |z.im|) ^ n ≤ (2 : ℝ) ^ n := by gcongr; linarith
    calc
      _ ≤ 2 ^ n * C₀ := mul_le_mul hp hg (norm_nonneg _) (by positivity)
      _ ≤ _ := by gcongr; linarith

theorem gamma_differentiableAt_right {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro n hn
  have h := congrArg Complex.re hn
  simp only [neg_re, natCast_re] at h
  linarith [Nat.cast_nonneg (α := ℝ) n]

def cancelledKernel (f g : ℂ → ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  (Y : ℂ) ^ z * Gamma (z + 1) * dslope f 0 z * g z

def literalKernel (f g : ℂ → ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  (Y : ℂ) ^ z * Gamma z * f z * g z

theorem cancelledKernel_eq_literal {f g : ℂ → ℂ} {Y : ℝ} (hf0 : f 0 = 0)
    {z : ℂ} (hz : z ≠ 0) : cancelledKernel f g Y z = literalKernel f g Y z := by
  unfold cancelledKernel literalKernel
  rw [Gamma_add_one z hz, dslope_of_ne f hz]
  simp only [slope, sub_zero, hf0, smul_eq_mul, vsub_eq_sub]
  field_simp

theorem cancelledKernel_at_zero (f g : ℂ → ℂ) (Y : ℝ) :
    cancelledKernel f g Y 0 = deriv f 0 * g 0 := by
  simp [cancelledKernel, Complex.cpow_zero, Complex.Gamma_one]

theorem dslope_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (dslope f 0) := by
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).mpr hf.differentiableOn

theorem cancelledKernel_differentiableAt {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {Y : ℝ} (hY : 0 < Y) {z : ℂ} (hz : -1 < z.re) :
    DifferentiableAt ℂ (cancelledKernel f g Y) z := by
  exact ((((differentiableAt_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))).mul
    ((gamma_differentiableAt_right (by change 0 < z.re + 1; linarith)).comp z
      (differentiableAt_id.add_const 1))).mul (dslope_entire hf z)).mul (hg z))

theorem literalKernel_norm (f g : ℂ → ℂ) {Y : ℝ} (hY : 0 < Y) (z : ℂ) :
    ‖literalKernel f g Y z‖ = Y ^ z.re * ‖Gamma z‖ * ‖f z‖ * ‖g z‖ := by
  simp only [literalKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]

theorem cancelledKernel_large_height_bound {f g : ℂ → ℂ} (hf0 : f 0 = 0)
    {Y a b A B G : ℝ} (hY : 1 ≤ Y) (_ha : -1 < a) (n : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hG : 0 ≤ G)
    (hgamma : ∀ z : ℂ, a + 1 ≤ z.re → z.re ≤ b + 1 →
      (1 + |z.im|) ^ (n + 2) * ‖Gamma z‖ ≤ G)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hg : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) (hzi : 1 ≤ |z.im|) :
    ‖cancelledKernel f g Y z‖ ≤ (Y ^ b * G * A * B) / (1 + z.im ^ 2) := by
  have hY0 : 0 < Y := by linarith
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hzi
  have hnorm : 1 ≤ ‖z‖ := hzi.trans (Complex.abs_im_le_norm z)
  have hΓ : ‖Gamma z‖ ≤ ‖Gamma (z + 1)‖ := by
    rw [Gamma_add_one z hz0, norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hnorm
  have hga := hgamma (z + 1) (by simpa using hza) (by simpa using hzb)
  simp only [add_im, one_im, add_zero] at hga
  have hweighted : (1 + z.im ^ 2) * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) ≤ G := by
    calc
      _ ≤ (1 + |z.im|) ^ 2 * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) := by
        gcongr
        nlinarith [sq_abs z.im, abs_nonneg z.im]
      _ = (1 + |z.im|) ^ (n + 2) * ‖Gamma (z + 1)‖ := by rw [pow_add]; ring
      _ ≤ _ := hga
  have hgdiv : ‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n ≤ G / (1 + z.im ^ 2) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hweighted)
  rw [cancelledKernel_eq_literal hf0 hz0, literalKernel_norm f g hY0]
  calc
    _ ≤ Y ^ b * ‖Gamma (z + 1)‖ * (A * (1 + |z.im|) ^ n) * B := by
      gcongr
      · exact hf z hza hzb
      · exact hg z hza hzb
    _ = (Y ^ b * A * B) * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) := by ring
    _ ≤ (Y ^ b * A * B) * (G / (1 + z.im ^ 2)) :=
      mul_le_mul_of_nonneg_left hgdiv (by positivity)
    _ = _ := by ring

theorem cancelledKernel_strip_bound {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y a b A B : ℝ}
    (hY : 1 ≤ Y) (ha : -1 < a) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖cancelledKernel f g Y z‖ ≤ C / (1 + z.im ^ 2) := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨G,hG,hgamma⟩ := gamma_rapid_bound (a+1) (b+1) (by linarith) (n+2)
  let S : Set ℂ := Icc a b ×ℂ Icc (-1 : ℝ) 1
  have hc : ContinuousOn (cancelledKernel f g Y) S := by
    intro z hz
    exact (cancelledKernel_differentiableAt hf hg hY0 (ha.trans_le hz.1.1)).continuousAt.continuousWithinAt
  have hw : ContinuousOn (fun z : ℂ => (1 + z.im ^ 2) * ‖cancelledKernel f g Y z‖) S :=
    (continuous_const.add (continuous_im.pow 2)).continuousOn.mul hc.norm
  obtain ⟨K,hK⟩ := (isCompact_Icc.reProdIm isCompact_Icc : IsCompact S).bddAbove_image hw
  refine ⟨|K| + Y ^ b * G * A * B + 1, by positivity, ?_⟩
  intro z hza hzb
  by_cases ht : 1 ≤ |z.im|
  · apply (cancelledKernel_large_height_bound hf0 hY ha n hA hB hG.le hgamma
      hfbound hgbound hza hzb ht).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [abs_nonneg K]
  · have hzS : z ∈ S := ⟨⟨hza,hzb⟩, abs_le.mp (le_of_lt (lt_of_not_ge ht))⟩
    have hb := hK (Set.mem_image_of_mem _ hzS)
    apply (le_div_iff₀ (by positivity : 0 < 1 + z.im ^ 2)).mpr
    have hnonneg : 0 ≤ Y ^ b * G * A * B := by positivity
    nlinarith [le_abs_self K]

theorem cancelledKernel_vertical_integrable {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {Y a b C x : ℝ}
    (hY : 0 < Y) (ha : -1 < a) (hx : x ∈ Icc a b)
    (hbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖cancelledKernel f g Y z‖ ≤ C / (1 + z.im ^ 2)) :
    Integrable (fun t : ℝ => cancelledKernel f g Y ((x : ℂ) + t * I)) := by
  have hc : Continuous (fun t : ℝ => cancelledKernel f g Y ((x : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (cancelledKernel_differentiableAt hf hg hY (by simpa using ha.trans_le hx.1)).continuousAt.comp
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  apply ae_of_all
  intro t
  simpa [div_eq_mul_inv] using hbound ((x : ℂ) + t * I) (by simpa using hx.1) (by simpa using hx.2)

theorem cancelledKernel_contour_shift {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y a b A B : ℝ}
    (hY : 1 ≤ Y) (ha : -1 < a) (hab : a ≤ b) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B) :
    (∫ t : ℝ, cancelledKernel f g Y ((a : ℂ) + t * I)) =
      ∫ t : ℝ, cancelledKernel f g Y ((b : ℂ) + t * I) := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨C,_,hbnd⟩ := cancelledKernel_strip_bound hf hg hf0 hY ha n hA hB hfbound hgbound
  apply VerticalContourShift.integral_eq_of_strip_decay _ a b C hab
    (fun z hz _ => cancelledKernel_differentiableAt hf hg hY0 (ha.trans_le hz))
    (cancelledKernel_vertical_integrable hf hg hY0 ha ⟨le_rfl,hab⟩ hbnd)
    (cancelledKernel_vertical_integrable hf hg hY0 ha ⟨hab,le_rfl⟩ hbnd)
  intro x hx t
  simpa using hbnd ((x : ℂ) + t * I) (by simpa using hx.1) (by simpa using hx.2)

theorem literal_contour_shift {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y A B : ℝ}
    (hY : 1 ≤ Y) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖g z‖ ≤ B) :
    (∫ t : ℝ, literalKernel f g Y ((2 : ℂ) + t * I)) =
      ∫ t : ℝ, literalKernel f g Y ((-(1/4) : ℂ) + t * I) := by
  have h := cancelledKernel_contour_shift hf hg hf0 hY (by norm_num : (-1 : ℝ) < -(1/4))
    (by norm_num : (-(1/4) : ℝ)≤2) n hA hB hfbound hgbound
  have he (x : ℝ) (hx : x ≠ 0) (t : ℝ) :
      cancelledKernel f g Y ((x : ℂ) + t * I) = literalKernel f g Y ((x : ℂ) + t * I) := by
    apply cancelledKernel_eq_literal hf0
    intro hz
    apply hx
    simpa using congrArg Complex.re hz
  simp only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one] at h
  have h2 (t : ℝ) := he 2 (by norm_num) t
  have hq (t : ℝ) := he (-(1/4)) (by norm_num) t
  norm_num only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one] at h2 hq
  simpa only [h2, hq] using h.symm

theorem gamma_negative_quarter_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ t : ℝ,
      (1 + t ^ 2) * (1 + |t|) ^ n * ‖Gamma ((-(1/4) : ℂ) + t * I)‖ ≤ G := by
  obtain ⟨C,hC,hgamma⟩ := gamma_rapid_bound (3/4) (3/4) (by norm_num) (n+2)
  refine ⟨4*C, by positivity, ?_⟩
  intro t
  let z : ℂ := (-(1/4) : ℂ) + t * I
  have hzre : z.re = -(1/4) := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hzre
  have hn : (1/4 : ℝ) ≤ ‖z‖ := by simpa only [hzre, abs_neg, abs_of_pos (by norm_num : (0 : ℝ)<1/4)] using Complex.abs_re_le_norm z
  have hΓ : ‖Gamma z‖ ≤ 4 * ‖Gamma (z+1)‖ := by
    rw [Gamma_add_one z hz0, norm_mul]
    nlinarith [norm_nonneg (Gamma z)]
  have hbound := hgamma (z+1) (by norm_num [hzre]) (by norm_num [hzre])
  simp only [add_im, one_im, add_zero, hzim] at hbound
  have hp : 1+t^2 ≤ (1+|t|)^2 := by nlinarith [sq_abs t, abs_nonneg t]
  change (1+t^2)*(1+|t|)^n*‖Gamma z‖ ≤ 4*C
  calc
    _ ≤ (1+|t|)^2*(1+|t|)^n*(4*‖Gamma (z+1)‖) := by gcongr
    _ = 4*((1+|t|)^(n+2)*‖Gamma (z+1)‖) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by norm_num)

theorem literal_shifted_integral_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ (f g : ℂ → ℂ) (Y A B : ℝ),
      0 < Y → 0 ≤ A → 0 ≤ B →
      (∀ t : ℝ, ‖f ((-(1/4) : ℂ)+t*I)‖ ≤ A*(1+|t|)^n) →
      (∀ t : ℝ, ‖g ((-(1/4) : ℂ)+t*I)‖ ≤ B) →
      ‖∫ t : ℝ, literalKernel f g Y ((-(1/4) : ℂ)+t*I)‖ ≤
        Real.pi * G * A * B * Y ^ (-(1/4 : ℝ)) := by
  obtain ⟨G,hG,hgamma⟩ := gamma_negative_quarter_bound n
  refine ⟨G,hG,?_⟩
  intro f g Y A B hY hA hB hf hg
  have hbound (t : ℝ) :
      ‖literalKernel f g Y ((-(1/4) : ℂ)+t*I)‖ ≤
        (G*A*B*Y^(-(1/4 : ℝ)))*(1+t^2)⁻¹ := by
    have hga : (1+|t|)^n*‖Gamma ((-(1/4) : ℂ)+t*I)‖ ≤ G/(1+t^2) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [hgamma t])
    rw [literalKernel_norm f g hY]
    have hzre : (((-(1/4) : ℂ)+t*I).re) = (-(1/4) : ℝ) := by norm_num
    rw [hzre]
    change Y^(-(1/4 : ℝ))*‖Gamma ((-(1/4) : ℂ)+t*I)‖*
      ‖f ((-(1/4) : ℂ)+t*I)‖*‖g ((-(1/4) : ℂ)+t*I)‖ ≤ _
    calc
      _ ≤ Y^(-(1/4 : ℝ))*‖Gamma ((-(1/4) : ℂ)+t*I)‖*(A*(1+|t|)^n)*B := by gcongr; exact hf t; exact hg t
      _ = (A*B*Y^(-(1/4 : ℝ)))*((1+|t|)^n*‖Gamma ((-(1/4) : ℂ)+t*I)‖) := by ring
      _ ≤ (A*B*Y^(-(1/4 : ℝ)))*(G/(1+t^2)) := mul_le_mul_of_nonneg_left hga (by positivity)
      _ = _ := by ring
  have hint := norm_integral_le_of_norm_le
    (integrable_inv_one_add_sq.const_mul (G*A*B*Y^(-(1/4 : ℝ)))) (ae_of_all _ hbound)
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hint
  convert hint using 1; ring

theorem literal_detector_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ (f g : ℂ → ℂ) (Y A B : ℝ),
      Differentiable ℂ f → Differentiable ℂ g → f 0 = 0 →
      1 ≤ Y → 0 ≤ A → 0 ≤ B →
      (∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖f z‖ ≤ A*(1+|z.im|)^n) →
      (∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖g z‖ ≤ B) →
      ‖∫ t : ℝ, literalKernel f g Y ((2 : ℂ)+t*I)‖ ≤
        Real.pi * G * A * B * Y ^ (-(1/4 : ℝ)) := by
  obtain ⟨G,hG,hbound⟩ := literal_shifted_integral_bound n
  refine ⟨G,hG,?_⟩
  intro f g Y A B hf hg hf0 hY hA hB hfb hgb
  rw [literal_contour_shift hf hg hf0 hY n hA hB hfb hgb]
  apply hbound f g Y A B (by linarith) hA hB
  · intro t; simpa using hfb ((-(1/4) : ℂ)+t*I) (by norm_num) (by norm_num)
  · intro t; exact hgb _ (by norm_num) (by norm_num)

open HeckeFamily

def cutoffSet (D : ℝ) : Finset (Ideal O) :=
  ConcretePrimeRowBridge.idealsUpTo ⌊2*D⌋₊

theorem mem_cutoffSet {D : ℝ} (hD : 0 ≤ D) {J : Ideal O} :
    J ∈ cutoffSet D ↔ J ≠ 0 ∧ (J.absNorm : ℝ) ≤ 2*D := by
  rw [cutoffSet, ConcretePrimeRowBridge.mem_idealsUpTo]
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨?_, ?_⟩
    · intro h; simp [h] at hp
    · exact (by exact_mod_cast hb : (J.absNorm : ℝ) ≤ ⌊2*D⌋₊).trans
        (Nat.floor_le (by positivity))
  · rintro ⟨hp, hb⟩
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp),
      Nat.le_floor hb⟩

def cutoffTerm (χ : Character) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) (s : ℂ) : ℂ :=
  HeckeDyadic.coefficient χ true J * V ((J.absNorm : ℝ)/D) *
    CubicEisenstein.fullIdealWeight s J

def cutoff (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) : ℂ :=
  ∑ J ∈ cutoffSet D, cutoffTerm χ V D J s

@[simp] theorem cutoffTerm_zero (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) :
    cutoffTerm χ V D 0 s = 0 := by
  simp [cutoffTerm, CubicEisenstein.fullIdealWeight]

theorem cutoffTerm_eq (χ : Character) (V : ℝ → ℂ) (D : ℝ) {J : Ideal O}
    (hJ : J ≠ 0) (s : ℂ) :
    cutoffTerm χ V D J s = (UniqueFactorizationMonoid.moebius J : ℂ) *
      idealCoeff χ J * V ((J.absNorm : ℝ)/D) * (J.absNorm : ℂ)^(-s) := by
  rw [cutoffTerm, CubicEisenstein.fullIdealWeight, ite_eq_right hJ]
  rfl

theorem cutoff_eq_tsum (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    cutoff χ V D s = ∑' J : Ideal O, cutoffTerm χ V D J s := by
  symm
  apply tsum_eq_sum
  intro J hJ
  by_cases hzero : J = 0
  · subst J; exact cutoffTerm_zero χ V D s
  · have hn : 2*D < (J.absNorm : ℝ) := by
      by_contra h
      exact hJ ((mem_cutoffSet hD.le).mpr ⟨hzero, le_of_not_gt h⟩)
    have hv := hV ((J.absNorm : ℝ)/D) ((le_div_iff₀ hD).mpr hn.le)
    simp [cutoffTerm, hv]

theorem cutoffTerm_entire (χ : Character) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) :
    Differentiable ℂ (cutoffTerm χ V D J) := by
  by_cases hJ : J = 0
  · subst J
    have he : cutoffTerm χ V D 0 = fun _ : ℂ => 0 := funext (cutoffTerm_zero χ V D)
    rw [he]
    exact differentiable_const 0
  · have hn : (J.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hJ
    unfold cutoffTerm
    simp only [CubicEisenstein.fullIdealWeight, ite_eq_right hJ]
    exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul _

theorem cutoff_entire (χ : Character) (V : ℝ → ℂ) (D : ℝ) :
    Differentiable ℂ (cutoff χ V D) := by
  exact Differentiable.fun_sum fun J _ => cutoffTerm_entire χ V D J

theorem cutoffTerm_norm_le (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) (J : Ideal O) :
    ‖cutoffTerm χ V D J s‖ ≤ 1 := by
  by_cases hJ : J = 0
  · subst J
    rw [cutoffTerm_zero, norm_zero]
    norm_num
  · have hnorm : 1 ≤ (J.absNorm : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
    have hw : ‖CubicEisenstein.fullIdealWeight s J‖ ≤ 1 := by
      rw [CubicEisenstein.fullIdealWeight, ite_eq_right hJ]
      have hn : 0 < (J.absNorm : ℝ) := by linarith
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn, neg_re]
      exact (Real.rpow_le_rpow_of_exponent_le hnorm (neg_nonpos.mpr hs)).trans_eq (Real.rpow_zero _)
    rw [cutoffTerm, norm_mul, norm_mul]
    calc
      _ ≤ (1 : ℝ)*1*1 := by gcongr; exact HeckeDyadic.coefficient_norm_le χ true J; exact hV _
      _ = 1 := by norm_num

theorem cutoff_norm_le (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 1 ≤ D)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖cutoff χ V D s‖ ≤ 256*D := by
  have hcount := DescentFiberCost.finite_ideal_count_real (cutoffSet D) (2*D) (by linarith)
    (fun J hJ => ((mem_cutoffSet (by linarith : 0 ≤ D)).mp hJ).1)
    (fun J hJ => ((mem_cutoffSet (by linarith : 0 ≤ D)).mp hJ).2)
  calc
    _ ≤ ∑ J ∈ cutoffSet D, ‖cutoffTerm χ V D J s‖ := norm_sum_le _ _
    _ ≤ ∑ _J ∈ cutoffSet D, (1 : ℝ) := Finset.sum_le_sum (fun J _ => cutoffTerm_norm_le χ V D hV hs J)
    _ = ((cutoffSet D).card : ℝ) := by simp
    _ ≤ 256*D := by linarith

theorem original_right_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ s : ℂ,
      (1/4 : ℝ) ≤ s.re → ‖LFunction χ s‖ ≤
        C*(χ.modulus.absNorm : ℝ)^2*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hdel⟩ := HeckeDeletionBounds.factors_subpower_bound
    (1/4) 1 (by norm_num) (by norm_num)
  let Cp := HeckeLogarithmicInput.uniformConstant
  have hCp : 0 ≤ Cp := HeckeLogarithmicInput.uniformConstant_nonneg
  refine ⟨(1+Cp)*Cd, by positivity, ?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hn,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue ≠ 1 := fun h => hχ
    ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hL := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10 : ℝ) ≤ s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hL
  have hnorm : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
  have hqp : (ψ.modulus.absNorm : ℝ)^(3/5 : ℝ) ≤ χ.modulus.absNorm := by
    apply le_trans _ hnorm
    simpa using Real.rpow_le_rpow_of_exponent_le
      (HeckeLogarithmicInput.modulus_norm_ge_one ψ) (by norm_num : (3/5 : ℝ) ≤ 1)
  have hLd : ‖LFunction ψ s‖ ≤ (1+Cp)*(χ.modulus.absNorm : ℝ)*(3+|s.im|)^2 := by
    apply hL.trans
    change Cp * _ * _ ≤ _
    gcongr
    linarith
  have hd := hdel χ.modulus χ.modulus_ne_bot ψ s hs
  rw [Real.rpow_one] at hd
  have hd' : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖ ≤ Cd*(χ.modulus.absNorm : ℝ) := by
    linarith [norm_nonneg ((HeckeFiniteDeletion.factors χ.modulus ψ s)⁻¹)]
  rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ (by linarith), norm_mul]
  calc
    _ ≤ ((1+Cp)*(χ.modulus.absNorm : ℝ)*(3+|s.im|)^2) *
        (Cd*(χ.modulus.absNorm : ℝ)) := mul_le_mul hLd hd' (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem shifted_original_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ (ρ z : ℂ),
      (51/100 : ℝ) ≤ ρ.re → -(1/4 : ℝ) ≤ z.re →
      ‖LFunction χ (ρ+z)‖ ≤
        (C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2)*(1+|z.im|)^2 := by
  obtain ⟨C,hC,hbound⟩ := original_right_growth
  refine ⟨C,hC,?_⟩
  intro χ hχ ρ z hρ hz
  have hb := hbound χ hχ (ρ+z) (by simp only [add_re]; linarith)
  have hh : 3+|(ρ+z).im| ≤ (3+|ρ.im|)*(1+|z.im|) := by
    simp only [add_im]
    have hab := abs_add_le ρ.im z.im
    nlinarith [abs_nonneg ρ.im, abs_nonneg z.im]
  calc
    _ ≤ C*(χ.modulus.absNorm : ℝ)^2*((3+|ρ.im|)*(1+|z.im|))^2 := by
      apply hb.trans; gcongr
    _ = _ := by ring

def detectorIntegrand (χ : Character) (V : ℝ → ℂ) (D Y : ℝ) (ρ z : ℂ) : ℂ :=
  (Y : ℂ)^z * Gamma z * LFunction χ (ρ+z) * cutoff χ V D (ρ+z)

def detectorIntegral (χ : Character) (V : ℝ → ℂ) (D Y : ℝ) (ρ : ℂ) : ℂ :=
  ((2*Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)

theorem detector_contour_shift (χ : Character) (hχ : χ.residue ≠ 1)
    (V : ℝ → ℂ) (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {D Y : ℝ}
    (hD : 1 ≤ D) (hY : 1 ≤ Y) {ρ : ℂ} (hρ : (51/100 : ℝ) ≤ ρ.re)
    (hzero : LFunction χ ρ = 0) :
    (∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)) =
      ∫ t : ℝ, detectorIntegrand χ V D Y ρ (-(1/4)+t*I) := by
  obtain ⟨C,hC,hgrowth⟩ := shifted_original_growth
  apply literal_contour_shift (A := C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2) (B := 256*D)
    ((LFunction_entire_nonprincipal χ hχ).comp (differentiable_const ρ |>.add differentiable_id))
    ((cutoff_entire χ V D).comp (differentiable_const ρ |>.add differentiable_id))
    (by simpa using hzero) hY 2 (by positivity) (by positivity : 0 ≤ 256*D)
  · intro z hz _
    exact hgrowth χ hχ ρ z hρ hz
  · intro z hz _
    exact cutoff_norm_le χ V hD hV (s := ρ+z) (by simp only [add_re]; linarith)

theorem detector_integral_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (χ : Character), χ.residue ≠ 1 →
      ∀ (V : ℝ → ℂ), (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ (D Y : ℝ),
      1 ≤ D → 1 ≤ Y → ∀ ρ : ℂ, (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 →
      ‖detectorIntegral χ V D Y ρ‖ ≤
        K*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2*D*Y^(-(1/4 : ℝ)) := by
  obtain ⟨C,hC,hgrowth⟩ := shifted_original_growth
  obtain ⟨G,hG,hgamma⟩ := literal_detector_bound 2
  refine ⟨128*G*C, by positivity, ?_⟩
  intro χ hχ V hV D Y hD hY ρ hρ hzero
  have hb := hgamma (fun z => LFunction χ (ρ+z)) (fun z => cutoff χ V D (ρ+z))
    Y (C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2) (256*D)
    ((LFunction_entire_nonprincipal χ hχ).comp (differentiable_const ρ |>.add differentiable_id))
    ((cutoff_entire χ V D).comp (differentiable_const ρ |>.add differentiable_id))
    (by simpa using hzero) hY (by positivity) (by positivity)
    (fun z hz _ => hgrowth χ hχ ρ z hρ hz)
    (fun z hz _ => cutoff_norm_le χ V hD hV (by simp only [add_re]; linarith))
  change ‖∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)‖ ≤ _ at hb
  rw [detectorIntegral, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (by positivity))).trans_eq
  field_simp
  ring

theorem detector_integrable (χ : Character) (hχ : χ.residue ≠ 1)
    (V : ℝ → ℂ) (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {D Y : ℝ}
    (hD : 1 ≤ D) (hY : 1 ≤ Y) {ρ : ℂ} (hρ : (51/100 : ℝ) ≤ ρ.re)
    (hzero : LFunction χ ρ = 0) {x : ℝ} (hx : x ∈ Icc (-(1/4)) 2) (hx0 : x ≠ 0) :
    Integrable (fun t : ℝ => detectorIntegrand χ V D Y ρ ((x : ℂ)+t*I)) := by
  obtain ⟨C,hC,hgrowth⟩ := shifted_original_growth
  let f : ℂ → ℂ := fun z => LFunction χ (ρ+z)
  let g : ℂ → ℂ := fun z => cutoff χ V D (ρ+z)
  have hf : Differentiable ℂ f :=
    (LFunction_entire_nonprincipal χ hχ).comp (differentiable_const ρ |>.add differentiable_id)
  have hg : Differentiable ℂ g :=
    (cutoff_entire χ V D).comp (differentiable_const ρ |>.add differentiable_id)
  have hf0 : f 0 = 0 := by simpa [f] using hzero
  obtain ⟨B,_,hb⟩ := cancelledKernel_strip_bound (b := 2) hf hg hf0 hY
    (by norm_num : (-1 : ℝ) < -(1/4)) 2
    (A := C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2) (B := 256*D)
    (by positivity) (by positivity)
    (fun z hz _ => hgrowth χ hχ ρ z hρ hz)
    (fun z hz _ => cutoff_norm_le χ V hD hV (s := ρ+z) (by simp only [add_re]; linarith))
  have hi := cancelledKernel_vertical_integrable hf hg (by linarith : 0 < Y)
    (by norm_num : (-1 : ℝ) < -(1/4)) hx hb
  apply hi.congr
  filter_upwards [] with t
  apply cancelledKernel_eq_literal hf0
  intro hz
  apply hx0
  simpa using congrArg Complex.re hz

theorem detectorIntegral_contour_normalization (χ : Character) (V : ℝ → ℂ)
    (D Y : ℝ) (ρ : ℂ) :
    detectorIntegral χ V D Y ρ = ((2*Real.pi : ℂ)*I)⁻¹ *
      ∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)*I := by
  rw [MeasureTheory.integral_mul_const, mul_inv_rev]
  simp only [detectorIntegral, ofReal_mul, ofReal_ofNat]
  have hi : I⁻¹*I = 1 := inv_mul_cancel₀ I_ne_zero
  calc
    _ = (I⁻¹*I)*(((2*Real.pi : ℂ))⁻¹ * ∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)) := by rw [hi, one_mul]
    _ = _ := by ring

theorem detector_power_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (R θ : ℝ), 0 ≤ R → 0 ≤ θ →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ (U D : ℝ), 1 ≤ U →
      1 ≤ D → D ≤ U^(3/2 : ℝ) → (χ.modulus.absNorm : ℝ) ≤ R*U →
      ∀ ρ : ℂ, (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ‖detectorIntegral χ V D (U^20) ρ‖ ≤ (K*R^2)*U^(-(3/2 : ℝ)+2*θ) := by
  obtain ⟨K,hK,hbound⟩ := detector_integral_bound
  refine ⟨16*K, by positivity, ?_⟩
  intro R θ hR hθ χ hχ V hV U D hU hD hDU hQ ρ hρ hzero ht
  have hU0 : 0 < U := by linarith
  have huθ : 1 ≤ U^θ := Real.one_le_rpow hU hθ
  have hheight : 3+|ρ.im| ≤ 4*U^θ := by linarith
  have hY : 1 ≤ U^20 := one_le_pow₀ hU
  have he : (U^20)^(-(1/4 : ℝ)) = U^(-5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    norm_num
  have hb := hbound χ hχ V hV D (U^20) hD hY ρ hρ hzero
  rw [he] at hb
  calc
    _ ≤ K*(R*U)^2*(4*U^θ)^2*U^(3/2 : ℝ)*U^(-5 : ℝ) := by
      apply hb.trans; gcongr
    _ = (16*K*R^2)*(U^(2 : ℝ)*(U^θ)^2*U^(3/2 : ℝ)*U^(-5 : ℝ)) := by
      rw [Real.rpow_two]; ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hU0.le, ← Real.rpow_add hU0,
        ← Real.rpow_add hU0, ← Real.rpow_add hU0]
      congr 2
      ring

theorem detector_uniform_small (R θ ε : ℝ) (hR : 0 ≤ R)
    (hθ : 0 ≤ θ) (hθ' : θ < 3/4) (hε : 0 < ε) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ D : ℝ, 1 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ‖detectorIntegral χ V D (U^20) ρ‖ < ε := by
  obtain ⟨K,hK,hbound⟩ := detector_power_bound
  have ht : Tendsto (fun U : ℝ => (K*R^2)*U^(-(3/2 : ℝ)+2*θ)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < (3/2 : ℝ)-2*θ)).const_mul (K*R^2)
    simpa [neg_sub, sub_eq_add_neg, add_comm] using h
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  refine ⟨U₀,?_⟩
  intro U hU₀' hU χ hχ V hV D hD hDU hQ ρ hρ hzero ht
  exact (hbound R θ hR hθ χ hχ V hV U D hU hD hDU hQ ρ hρ hzero ht).trans_lt (hU₀ U hU₀')

end SevenEighths.GammaZeroDetector

end

end OAI

end Source726

/- Original source: OAI/NumberTheory/DirichletL/GammaDetectorExpansion.lean; sha256: f1e455f9752c9573a43abc59eee148dcd5bf21577eb4603dc2eeb1c5599fd9f6 -/
section Source727
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex
namespace SevenEighths.GammaDetectorExpansion
open GammaZeroDetector HeckeFamily

def line (t : ℝ) : ℂ := 2+t*I

@[simp] theorem line_re (t : ℝ) : (line t).re = 2 := by simp [line]
@[simp] theorem line_im (t : ℝ) : (line t).im = t := by simp [line]

theorem gamma_line_integrable : Integrable (fun t : ℝ => Gamma (line t)) := by
  obtain ⟨C,hC,hbound⟩ := gamma_rapid_bound 2 2 (by norm_num) 2
  apply (integrable_inv_one_add_sq.const_mul C).mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    exact fun t => (gamma_differentiableAt_right (by simp : 0 < (line t).re)).continuousAt.comp
      (by unfold line; fun_prop)
  · filter_upwards [] with t
    have hb := hbound (line t) (by simp) (by simp)
    simp only [line_im] at hb
    have hp : 1+t^2 ≤ (1+|t|)^2 := by nlinarith [sq_abs t, abs_nonneg t]
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [norm_nonneg (Gamma (line t))]

theorem gamma_mellin_inverse {x : ℝ} (hx : 0 < x) :
    ((2*Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t : ℝ, (x : ℂ)^(-line t)*Gamma (line t)) = Complex.exp (-(x : ℂ)) := by
  let f : ℝ → ℂ := fun x => (Real.exp (-x) : ℂ)
  have hm (s : ℂ) (hs : 0 < s.re) : mellin f s = Gamma s := by
    rw [Gamma_eq_integral hs, GammaIntegral_eq_mellin]
  have hf : MellinConvergent f (2 : ℂ) := by
    simpa only [MellinConvergent, f, smul_eq_mul, mul_comm] using
      (GammaIntegral_convergent (by norm_num : 0 < (2 : ℂ).re))
  have hline (t : ℝ) : mellin f (line t) = Gamma (line t) := hm _ (by simp)
  have hv : VerticalIntegrable (mellin f) 2 := by
    change Integrable (fun t : ℝ => mellin f (line t))
    simpa only [hline] using gamma_line_integrable
  have hi := mellinInv_mellin_eq 2 f hx hf hv (by unfold f; fun_prop)
  change (1/(2*Real.pi)) • (∫ t : ℝ, (x : ℂ)^(-line t) • mellin f (line t)) = f x at hi
  simp_rw [hline] at hi
  simp only [smul_eq_mul, f, ofReal_exp, ofReal_neg] at hi
  convert hi using 1; simp [one_div, Complex.real_smul]

def gammaTerm (a : ℂ) (N : ℝ) (ρ : ℂ) (Y : ℝ) (t : ℝ) : ℂ :=
  (Y : ℂ)^(line t)*Gamma (line t)*a*(N : ℂ)^(-(ρ+line t))

theorem gammaTerm_separate (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y)
    (ρ : ℂ) (t : ℝ) :
    gammaTerm a N ρ Y t = (a*(N : ℂ)^(-ρ))*
      (((N/Y : ℝ) : ℂ)^(-line t)*Gamma (line t)) := by
  rw [gammaTerm, neg_add, cpow_add _ _ (ofReal_ne_zero.mpr hN.ne'),
    ofReal_div, div_cpow_ofReal_nonneg hN.le hY.le, cpow_neg (Y : ℂ), div_inv_eq_mul]
  ring

theorem gammaTerm_integral (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y) (ρ : ℂ) :
    ((2*Real.pi : ℝ) : ℂ)⁻¹ * (∫ t : ℝ, gammaTerm a N ρ Y t) =
      a*(N : ℂ)^(-ρ)*Complex.exp (-(N : ℂ)/(Y : ℂ)) := by
  simp_rw [gammaTerm_separate a hN hY ρ]
  rw [integral_const_mul]
  calc
    _ = (a*(N : ℂ)^(-ρ))*(((2*Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, ((N/Y : ℝ) : ℂ)^(-line t)*Gamma (line t)) := by ring
    _ = _ := by rw [gamma_mellin_inverse (div_pos hN hY)]; push_cast; rw [neg_div]

@[simp] theorem gammaTerm_zero (N : ℝ) (ρ : ℂ) (Y t : ℝ) : gammaTerm 0 N ρ Y t = 0 := by
  simp [gammaTerm]

theorem gammaTerm_norm (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y)
    (ρ : ℂ) (t : ℝ) :
    ‖gammaTerm a N ρ Y t‖ = (Y^2 * (‖a‖*N^(-(ρ.re+2)))) * ‖Gamma (line t)‖ := by
  simp only [gammaTerm, norm_mul, norm_cpow_eq_rpow_re_of_pos hY,
    norm_cpow_eq_rpow_re_of_pos hN, neg_re, add_re, line_re, Real.rpow_two]
  ring

theorem gammaTerm_integrable (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y) (ρ : ℂ) :
    Integrable (gammaTerm a N ρ Y) := by
  apply (gamma_line_integrable.norm.const_mul (Y^2*(‖a‖*N^(-(ρ.re+2))))).mono'
  · apply Continuous.aestronglyMeasurable
    have hl : Continuous line := by unfold line; fun_prop
    have hg : Continuous (fun t : ℝ => Gamma (line t)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (gamma_differentiableAt_right (by simp : 0 < (line t).re)).continuousAt.comp hl.continuousAt
    have hy := (differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hY.ne'))).continuous.comp hl
    have hn := (((differentiable_const ρ).add differentiable_id).neg.const_cpow
      (Or.inl (ofReal_ne_zero.mpr hN.ne'))).continuous.comp hl
    exact ((hy.mul hg).mul continuous_const).mul hn
  · exact ae_of_all _ (fun t => (gammaTerm_norm a hN hY ρ t).le)

theorem gamma_expansion {ι : Type*} [Countable ι] (a : ι → ℂ) (N : ι → ℝ)
    (hN : ∀ i, 0 ≤ N i) (hzero : ∀ i, N i = 0 → a i = 0)
    (ρ : ℂ) {Y : ℝ} (hY : 0 < Y)
    (hsum : Summable (fun i => ‖a i‖*(N i)^(-(ρ.re+2)))) :
    HasSum (fun i => a i*(N i : ℂ)^(-ρ)*Complex.exp (-(N i : ℂ)/(Y : ℂ)))
      (((2*Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, ∑' i, gammaTerm (a i) (N i) ρ Y t) := by
  have hint (i : ι) : Integrable (gammaTerm (a i) (N i) ρ Y) := by
    by_cases hi : N i = 0
    · rw [hzero i hi]
      have he : gammaTerm 0 (N i) ρ Y = fun _ : ℝ => 0 := funext (gammaTerm_zero _ _ _)
      rw [he]
      exact integrable_zero ℝ ℂ volume
    · exact gammaTerm_integrable _ (lt_of_le_of_ne (hN i) (Ne.symm hi)) hY ρ
  have hnorm (i : ι) (t : ℝ) :
      ‖gammaTerm (a i) (N i) ρ Y t‖ =
        (Y^2*(‖a i‖*(N i)^(-(ρ.re+2))))*‖Gamma (line t)‖ := by
    by_cases hi : N i = 0
    · simp [hzero i hi]
    · exact gammaTerm_norm _ (lt_of_le_of_ne (hN i) (Ne.symm hi)) hY ρ t
  have hnormsum : Summable (fun i => ∫ t : ℝ, ‖gammaTerm (a i) (N i) ρ Y t‖) := by
    simp_rw [hnorm, integral_const_mul]
    convert hsum.mul_left (Y^2*(∫ t : ℝ, ‖Gamma (line t)‖)) using 1
    funext i
    ring
  have hi := (hasSum_integral_of_summable_integral_norm hint hnormsum).mul_left
    (((2*Real.pi : ℝ) : ℂ)⁻¹)
  have he (i : ι) : (((2*Real.pi : ℝ) : ℂ)⁻¹) * (∫ t : ℝ, gammaTerm (a i) (N i) ρ Y t) =
      a i*(N i : ℂ)^(-ρ)*Complex.exp (-(N i : ℂ)/(Y : ℂ)) := by
    by_cases hn : N i = 0
    · simp [hzero i hn]
    · exact gammaTerm_integral _ (lt_of_le_of_ne (hN i) (Ne.symm hn)) hY ρ
  simpa only [he] using hi

private instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
private instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

theorem cutoffTerm_weighted (χ : Character) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) (s : ℂ) :
    cutoffTerm χ V D J s = (UniqueFactorizationMonoid.moebius J : ℂ) *
      V ((J.absNorm : ℝ)/D) * IdealEuler.weighted (idealCoeff χ) s J := by
  simp only [cutoffTerm, HeckeDyadic.coefficient, ite_true,
    IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  ring

theorem cutoffTerm_outside (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (J : Ideal O)
    (hJ : J ∉ cutoffSet D) : cutoffTerm χ V D J s = 0 := by
  by_cases hzero : J = 0
  · subst J; exact cutoffTerm_zero χ V D s
  · have hn : 2*D < (J.absNorm : ℝ) := by
      by_contra h
      exact hJ ((mem_cutoffSet hD.le).mpr ⟨hzero, le_of_not_gt h⟩)
    have hv := hV ((J.absNorm : ℝ)/D) ((le_div_iff₀ hD).mpr hn.le)
    simp [cutoffTerm, hv]

theorem cutoffTerm_hasSum (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    HasSum (fun J : Ideal O => cutoffTerm χ V D J s) (cutoff χ V D s) :=
  hasSum_sum_of_ne_finset_zero (cutoffTerm_outside χ V hD hV s)

def pairCoefficient (χ : Character) (V : ℝ → ℂ) (D : ℝ) (p : Ideal O × Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius p.1 : ℂ) * V ((p.1.absNorm : ℝ)/D) *
    idealCoeff χ (p.1*p.2)

def pairNorm (p : Ideal O × Ideal O) : ℝ := (p.1*p.2).absNorm

theorem pairCoefficient_zero_norm (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (p : Ideal O × Ideal O) (hp : pairNorm p = 0) : pairCoefficient χ V D p = 0 := by
  have hn : (p.1*p.2).absNorm = 0 := by unfold pairNorm at hp; exact_mod_cast hp
  have hzero := Ideal.absNorm_eq_zero_iff.mp hn
  rw [pairCoefficient, hzero]
  rw [show (⊥ : Ideal O) = 0 from rfl, HeckeFamily.idealCoeff_zero, mul_zero]

theorem pairTerm_eq (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ)
    (p : Ideal O × Ideal O) :
    pairCoefficient χ V D p * (pairNorm p : ℂ)^(-s) =
      cutoffTerm χ V D p.1 s * IdealEuler.weighted (idealCoeff χ) s p.2 := by
  rw [cutoffTerm_weighted]
  by_cases hp : p.1*p.2 = 0
  · have he : pairNorm p = 0 := by simp [pairNorm, hp]
    rw [pairCoefficient_zero_norm χ V D p he, zero_mul]
    rw [mul_assoc, ← map_mul, hp, map_zero, mul_zero]
  · rw [mul_assoc, ← map_mul]
    simp only [pairCoefficient, pairNorm, Complex.ofReal_natCast,
      IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      CubicEisenstein.fullIdealWeight, ite_eq_right hp]
    ring

theorem pairTerm_summable_norm (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : Ideal O × Ideal O =>
      ‖pairCoefficient χ V D p * (pairNorm p : ℂ)^(-s)‖) := by
  simpa only [pairTerm_eq] using
    (cutoffTerm_hasSum χ V hD hV s).summable.norm.mul_norm
      (IdealEuler.weighted_summable_norm _ (idealCoeff_norm_le_one χ) s hs)

theorem pairSeries_eq (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 1 < s.re) :
    (∑' p : Ideal O × Ideal O, pairCoefficient χ V D p * (pairNorm p : ℂ)^(-s)) =
      cutoff χ V D s * LFunction χ s := by
  simp_rw [pairTerm_eq]
  rw [← tsum_mul_tsum_of_summable_norm (cutoffTerm_hasSum χ V hD hV s).summable.norm
    (IdealEuler.weighted_summable_norm _ (idealCoeff_norm_le_one χ) s hs)]
  rw [(cutoffTerm_hasSum χ V hD hV s).tsum_eq, LFunction_eq_series χ hs]
  rfl

theorem pairMajorant_summable (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re) :
    Summable (fun p : Ideal O × Ideal O =>
      ‖pairCoefficient χ V D p‖*(pairNorm p)^(-(ρ.re+2))) := by
  have h := pairTerm_summable_norm χ V hD hV (ρ+2) (by norm_num; linarith)
  apply h.congr
  intro p
  by_cases hp : pairNorm p = 0
  · simp [pairCoefficient_zero_norm χ V D p hp]
  · have hn : 0 < pairNorm p := lt_of_le_of_ne (by unfold pairNorm; positivity) (Ne.symm hp)
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hn]
    simp only [neg_re, add_re]
    norm_num

theorem pairGamma_tsum (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re)
    (Y t : ℝ) :
    (∑' p : Ideal O × Ideal O, gammaTerm (pairCoefficient χ V D p) (pairNorm p) ρ Y t) =
      detectorIntegrand χ V D Y ρ (line t) := by
  have hs : 1 < (ρ+line t).re := by simp only [add_re, line_re]; linarith
  calc
    _ = (Y : ℂ)^(line t)*Gamma (line t)*
        (∑' p : Ideal O × Ideal O, pairCoefficient χ V D p*(pairNorm p : ℂ)^(-(ρ+line t))) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      unfold gammaTerm
      ring
    _ = _ := by rw [pairSeries_eq χ V hD hV _ hs]; unfold detectorIntegrand; ring

def pairExponential (χ : Character) (V : ℝ → ℂ) (D : ℝ) (ρ : ℂ) (Y : ℝ)
    (p : Ideal O × Ideal O) : ℂ :=
  pairCoefficient χ V D p*(pairNorm p : ℂ)^(-ρ)*Complex.exp (-(pairNorm p : ℂ)/(Y : ℂ))

theorem detector_hasSum_pairs (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (pairExponential χ V D ρ Y) (detectorIntegral χ V D Y ρ) := by
  have h := gamma_expansion (pairCoefficient χ V D) pairNorm
    (fun p => by unfold pairNorm; positivity) (pairCoefficient_zero_norm χ V D)
    ρ hY (pairMajorant_summable χ V hD hV hρ)
  unfold pairExponential detectorIntegral
  simpa only [pairGamma_tsum χ V hD hV hρ, line] using h

theorem detector_eq_double_sum (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    detectorIntegral χ V D Y ρ = ∑' J : Ideal O, ∑' K : Ideal O,
      (UniqueFactorizationMonoid.moebius J : ℂ) * V ((J.absNorm : ℝ)/D) *
      idealCoeff χ (J*K) * (((J*K).absNorm : ℝ) : ℂ)^(-ρ) *
        Complex.exp (-(((J*K).absNorm : ℝ) : ℂ)/(Y : ℂ)) := by
  have h := detector_hasSum_pairs χ V hD hY hV hρ
  rw [← h.tsum_eq, h.summable.tsum_prod]
  rfl

theorem pairExponential_zero_left (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (K : Ideal O) : pairExponential χ V D ρ Y (0,K) = 0 := by
  unfold pairExponential
  rw [pairCoefficient_zero_norm χ V D _ (by simp [pairNorm]), zero_mul, zero_mul]

theorem pairExponential_zero_right (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (J : Ideal O) : pairExponential χ V D ρ Y (J,0) = 0 := by
  unfold pairExponential
  rw [pairCoefficient_zero_norm χ V D _ (by simp [pairNorm]), zero_mul, zero_mul]

theorem pairExponential_fiber (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (J : Ideal O) :
    (∑' p : CompletedGauss.MulFiber J, pairExponential χ V D ρ Y p.val) =
      HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y J := by
  have he (p : CompletedGauss.MulFiber J) :
      pairExponential χ V D ρ Y p.val =
        ((UniqueFactorizationMonoid.moebius p.val.1 : ℂ)*V ((p.val.1.absNorm : ℝ)/D)*
          IdealEuler.weighted (idealCoeff χ) ρ (p.val.1*p.val.2))*
          Complex.exp (-((J.absNorm : ℝ) : ℂ)/(Y : ℂ)) := by
    rw [pairExponential, pairTerm_eq, cutoffTerm_weighted, mul_assoc _ _
      (IdealEuler.weighted (idealCoeff χ) ρ p.val.2), ← map_mul]
    congr 2
    rw [pairNorm, p.property]
  simp_rw [he]
  rw [tsum_mul_right, HeckeDetectorWitnessArithmetic.weighted_fiber]
  rfl

theorem detector_hasSum_convolution (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y)
      (detectorIntegral χ V D Y ρ) := by
  have h := (detector_hasSum_pairs χ V hD hY hV hρ).tsum_fiberwise
    (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun J : Ideal O => ∑' p : CompletedGauss.MulFiber J,
    pairExponential χ V D ρ Y p.val) _ at h
  simpa only [pairExponential_fiber] using h

theorem detector_large_product_tail (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re) :
    (∑' J : Ideal O, HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y J *
      (1-V (2*(J.absNorm : ℝ)/D))) =
      detectorIntegral χ V D Y ρ - Complex.exp (-1/(Y : ℂ)) := by
  have h := detector_hasSum_convolution χ V (by linarith : 0 < D) hY hVzero hρ
  rw [HeckeDetectorWitnessArithmetic.exponential_sum_tail χ V D hD hV hVzero ρ Y h.summable,
    h.tsum_eq]

theorem pairExponential_summable_norm (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    Summable (fun p : Ideal O × Ideal O => ‖pairExponential χ V D ρ Y p‖) :=
  (detector_hasSum_pairs χ V hD hY hV hρ).summable.norm

def pairTail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (ρ : ℂ) (Y : ℝ)
    (p : Ideal O × Ideal O) : ℂ :=
  pairExponential χ V D ρ Y p * (1-V (2*pairNorm p/D))

theorem pairTail_summable (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {ρ : ℂ} (hρ : -1 < ρ.re) :
    Summable (pairTail χ V D ρ Y) := by
  apply Summable.of_norm
  apply ((pairExponential_summable_norm χ V hD hY hVzero hρ).mul_right 2).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro p
  rw [pairTail, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hn := norm_sub_le (1 : ℂ) (V (2*pairNorm p/D))
  rw [norm_one] at hn
  linarith [hV (2*pairNorm p/D)]

theorem pairTail_fiber (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (J : Ideal O) :
    (∑' p : CompletedGauss.MulFiber J, pairTail χ V D ρ Y p.val) =
      HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y J *
        (1-V (2*(J.absNorm : ℝ)/D)) := by
  have hn (p : CompletedGauss.MulFiber J) : pairNorm p.val = (J.absNorm : ℝ) := by
    rw [pairNorm, p.property]
  simp_rw [pairTail, hn]
  rw [tsum_mul_right, pairExponential_fiber]

theorem detector_eq_pair_tail (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hVone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (pairTail χ V D ρ Y)
      (detectorIntegral χ V D Y ρ - Complex.exp (-1/(Y : ℂ))) := by
  have hs := pairTail_summable χ V (by linarith : 0 < D) hY hVzero hV hρ
  have hf := hs.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun J : Ideal O => ∑' p : CompletedGauss.MulFiber J,
    pairTail χ V D ρ Y p.val) _ at hf
  simp_rw [pairTail_fiber] at hf
  have he := hf.tsum_eq
  rw [detector_large_product_tail χ V hD hY hVone hVzero hρ] at he
  exact he.symm ▸ hs.hasSum

end SevenEighths.GammaDetectorExpansion

end

end OAI

end Source727

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorBudget.lean; sha256: 9e41194ee21e1ad7aa6f698638b19420293f71d33f7bd863e7191f2d70118f80 -/
section Source728
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorBudget
open HeckeDetectorPartition

lemma source_length_bound (U : ℝ) (hU : 2 ≤ U) :
    ((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ) ≤ 25*Real.logb 2 U := by
  have hUp : 0 < U := by linarith
  have hp : 1 ≤ U^21 := one_le_pow₀ (by linarith) (n := 21)
  have hc : (1 : ℝ) ≤ ⌈2*U^21⌉₊ := le_trans (by linarith) (Nat.le_ceil (2*U^21))
  have hcu : (⌈2*U^21⌉₊ : ℝ) ≤ 4*U^21 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2*U^21 by positivity)
    linarith
  have hl : 1 ≤ Real.logb 2 U := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) (by norm_num : (0 : ℝ)<2) hU
    simpa using h
  have hb := length_bound (⌈2*U^21⌉₊ : ℝ) hc
  have hm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) (by linarith : (0 : ℝ)<⌈2*U^21⌉₊) hcu
  have he : Real.logb 2 (4*U^21) = 2+21*Real.logb 2 U := by
    rw [Real.logb_mul (by norm_num) (by positivity),Real.logb_pow]
    have hfour : Real.logb 2 4 = 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num,Real.logb_pow]
      norm_num
    rw [hfour]
    norm_num
  rw [he] at hm
  push_cast
  linarith

lemma source_pair_count_bound (U : ℝ) (hU : 2 ≤ U) :
    (((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ)^2) ≤ 625*(Real.logb 2 U)^2 := by
  have h := source_length_bound U hU
  have hl : 0 ≤ Real.logb 2 U := Real.logb_nonneg (by norm_num) (by linarith)
  nlinarith [sq_nonneg (((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ)-25*Real.logb 2 U)]

end SevenEighths.HeckeDetectorBudget

end

end OAI

end Source728

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorLower.lean; sha256: 1107f7f6ad56b42a2627e97ad555c1971d19ff4f486033c401083586817662eb -/
section Source729
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorLower
open HeckeFamily HeckeDetectorTail HeckeDetectorFinite HeckeDetectorPartition
open GammaZeroDetector
local notation "O" => HeckeFamily.O

lemma unit_term_lower (U : ℝ) (hU : 2 ≤ U) :
    (3/4 : ℝ) ≤ ‖Complex.exp (-1/((U^20 : ℝ) : ℂ))‖ := by
  have hUp : 0 < U := by linarith
  have hp : 4 ≤ U^20 := by
    calc
      4 ≤ U^2 := by nlinarith
      _ ≤ U^20 := pow_le_pow_right₀ (by linarith : 1 ≤ U) (by norm_num : 2 ≤ 20)
  have hi : 1/(U^20) ≤ (1/4 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hp
  rw [Complex.norm_exp]
  have he : (-1/((U^20 : ℝ) : ℂ)).re = -1/(U^20) := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num,←Complex.ofReal_div,Complex.ofReal_re]
  rw [he]
  have hh := Real.add_one_le_exp (-1/(U^20))
  simp only [neg_div] at hh ⊢
  linarith

theorem terminal_uniform_lower (R θ : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθ' : θ < 3/4) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → (∀ x : ℝ, ‖T x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1) →
      (∀ x : ℝ, 2 ≤ x → V x = 0) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      (1/2 : ℝ) ≤ ‖∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I‖ := by
  obtain ⟨UG,hUG⟩ := detector_uniform_small R θ (1/8) hR hθ hθ' (by norm_num)
  obtain ⟨UT,hUT⟩ := terminalRemainder_uniform_small 1 1 (1/8) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max 2 (max UG UT),?_⟩
  intro U hU χ hχ V T hVb hTb hVone hVzero hTone D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hU1 : 1 ≤ U := by linarith
  have hUp : 0 < U := by linarith
  have hg := hUG U ((le_max_left UG UT).trans ((le_max_right 2 _).trans hU)) hU1
    χ hχ V hVb D (by linarith) hDU hQ ρ hρ hzero hheight
  have ht := hUT U ((le_max_right UG UT).trans ((le_max_right 2 _).trans hU)) hU1
    χ V T hVb hTb hTone D ρ (by linarith)
  have hi := terminal_sum_identity χ V T 1 1 D (U^20) (U^21) (by norm_num)
    hVb hTb hD (by positivity) hVone hVzero ρ (by linarith)
  rw [(GammaDetectorExpansion.detector_hasSum_convolution χ V
    (by linarith : 0 < D) (by positivity : 0 < U^20) hVzero (by linarith : -1 < ρ.re)).tsum_eq] at hi
  have he : Complex.exp (-1/((U^20 : ℝ) : ℂ)) =
      detectorIntegral χ V D (U^20) ρ -
        (∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I) -
        (∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I) := by
    rw [hi]
    ring
  have hn := norm_sub_le
    (detectorIntegral χ V D (U^20) ρ - ∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I)
    (∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I)
  rw [←he] at hn
  have hn' := norm_sub_le (detectorIntegral χ V D (U^20) ρ)
    (∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I)
  have hu := unit_term_lower U hU2
  linarith

theorem exists_dyadic_zero_witness (R θ : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθ' : θ < 3/4) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → (∀ x : ℝ, ‖T x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1) →
      (∀ x : ℝ, 2 ≤ x → V x = 0) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      (∀ x : ℝ, 2 ≤ x → T x = 0) →
      ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ∃ j ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
          (1/2 : ℝ) ≤ 625*(Real.logb 2 U)^2*‖dyadicBlock χ V T D (U^20) (U^21) ρ j k‖ ∧
          (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
          (2 : ℝ)^j*(2 : ℝ)^k < 8*U^21 := by
  obtain ⟨U₁,hU₁⟩ := terminal_uniform_lower R θ hR hθ hθ'
  refine ⟨max 2 U₁,?_⟩
  intro U hU χ hχ V T hVb hTb hVone hVzero hTone hTzero D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hUpos : 0 < U := by linarith
  have ht := hU₁ U ((le_max_right _ _).trans hU) χ hχ V T hVb hTb hVone hVzero hTone D hD hDU hQ ρ hρ hzero hheight
  obtain ⟨j,hj,k,hk,hb⟩ := exists_dyadic_block χ V T D (U^20) (U^21)
    (by positivity) hTzero hVone hVzero ρ (1/2) ht
  have hbn : dyadicBlock χ V T D (U^20) (U^21) ρ j k ≠ 0 := by
    intro hz
    rw [hz,norm_zero,mul_zero] at hb
    norm_num at hb
  refine ⟨j,hj,k,hk,?_,nonzero_block_scale_bounds χ V T D (U^20) (U^21)
    (by linarith) (by positivity) hTzero hVone hVzero ρ j k hbn⟩
  exact hb.trans (mul_le_mul_of_nonneg_right
    (HeckeDetectorBudget.source_pair_count_bound U hU2) (norm_nonneg _))

end SevenEighths.HeckeDetectorLower

end

end OAI

end Source729

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorCommonFrequency.lean; sha256: 31e30e6678eb204a8172f6a5b847eefce471a55a4a7ee2ba6cc7458b70925807 -/
section Source730
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
namespace SevenEighths.HeckeDetectorFrequency
open HeckeFamily HeckeDetectorProfiles HeckeDetectorFourier HeckeDetectorLower
open HeckeDetectorCoefficientBounds HeckeDetectorFinite HeckeDetectorPartition
local notation "O" => HeckeFamily.O

def phaseProduct (χ : Character) (D U : ℝ) (s : ℂ) (j k : ℕ) (t : ℝ) : ℂ :=
  phasePolynomial (expandedSet U)
    (inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) D ((2 : ℝ)^j) s)
    (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^j)) t *
  phasePolynomial (expandedSet U)
    (plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) ((2 : ℝ)^k) s)
    (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^k)) t

theorem exists_common_frequency_witness (R θ τ : ℝ) (hR : 0 ≤ R)
    (hθ : 0 ≤ θ) (hθ' : θ < 3/4) (hτ : 0 < τ) :
    ∃ C U₀ : ℝ, 0 < C ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ χ : Character, χ.residue ≠ 1 → ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ∃ j ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
          ∃ t : ℝ, ‖t‖ ≤ U^τ ∧
            1 ≤ C*(Real.logb 2 U)^2*‖phaseProduct χ D U ρ j k t‖ ∧
            (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
            (2 : ℝ)^j*(2 : ℝ)^k < 8*U^21 := by
  obtain ⟨Ω,hΩc,hΩ,hwindow,hΩone⟩ := exists_product_log_cutoff
  obtain ⟨n,hn⟩ := exists_frequency_tail_order τ hτ
  have hL : 0 ≤ 2*Real.log 2+1 := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  obtain ⟨C₀,Cn,hC₀,hCn,hfreq⟩ := dyadic_frequency_bound Ω hΩc hΩ
    (2*Real.log 2+1) hL hwindow hΩone n
  obtain ⟨UF,hUF⟩ := hn Cn
  obtain ⟨UL,hUL⟩ := exists_dyadic_zero_witness R θ hR hθ hθ'
  refine ⟨2500*C₀,max 2 (max UF UL),by positivity,?_⟩
  intro U hU χ hχ D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hU1 : 1 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  obtain ⟨j,hj,k,hk,hblock,hsupport⟩ :=
    hUL U ((le_max_right UF UL).trans ((le_max_right 2 _).trans hU))
      χ hχ cutoff cutoff cutoff_norm_le cutoff_norm_le cutoff_one cutoff_zero cutoff_one cutoff_zero
      D hD hDU hQ ρ hρ hzero hheight
  obtain ⟨t,ht,hb⟩ := hfreq U D (U^τ) hU1 (by linarith) (by positivity) χ ρ (by linarith) j k
  have htail := hUF U ((le_max_left UF UL).trans ((le_max_right 2 _).trans hU)) hU1
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 625*(Real.logb 2 U)^2 by positivity)
  refine ⟨j,hj,k,hk,t,ht,?_,hsupport⟩
  change ‖dyadicBlock χ cutoff cutoff D (U^20) (U^21) ρ j k‖ ≤
    (67108864*U^42)*Cn/(U^τ)^n+C₀*‖phaseProduct χ D U ρ j k t‖ at hb
  change (625*(Real.logb 2 U)^2)*‖dyadicBlock χ cutoff cutoff D (U^20) (U^21) ρ j k‖ ≤
    (625*(Real.logb 2 U)^2)*((67108864*U^42)*Cn/(U^τ)^n+C₀*‖phaseProduct χ D U ρ j k t‖) at hb'
  nlinarith

end SevenEighths.HeckeDetectorFrequency

end

end OAI

end Source730

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorDyadicProfiles.lean; sha256: a14db8091860078d6e4af081528e578df153cd74140c712dba99186c4ee5b278 -/
section Source731
namespace OAI

noncomputable section

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace SevenEighths.HeckeDetectorDyadicProfiles
open CubicReflectionKernel
theorem section_deriv_smooth (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : (ℝ × ℝ) × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem compact_family_deriv_integrable (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : ℝ × ℝ) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set (ℝ × ℝ)) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set (ℝ × ℝ)) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable F hF K hK hsupp σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) =
      ‖𝓕 (iteratedDeriv j (F σ)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (F σ)) w‖ ≤ C := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (F σ)) w).trans
    exact hb σ hσ
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := mul_comm _ _
    _ ≤ C := hn

theorem compact_family_fourier_weighted_bound (F : (ℝ × ℝ) → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set (ℝ × ℝ)) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  have hbase : ‖𝓕 (F σ) w‖ ≤ C₀ := by simpa using h0 σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * C₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * Cj := mul_le_mul_of_nonneg_left (hj σ hσ w) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

def ratioProfile (V W : ℝ→ℂ) (R x : ℝ) : ℂ := V (R*x)*W x

def logFamily (V W : ℝ→ℂ) (p : ℝ×ℝ) (y : ℝ) : ℂ :=
  Real.exp (-p.2*y) • ratioProfile V W p.1 (Real.exp (-y))

lemma logFamily_smooth (V W : ℝ→ℂ) (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (logFamily V W)) := by
  unfold Function.uncurry logFamily ratioProfile
  have he : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ => Real.exp (-p.1.2*p.2)) := by fun_prop
  have hv : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ => V (p.1.1*Real.exp (-p.2))) :=
    hV.comp (by fun_prop)
  have hw : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ => W (Real.exp (-p.2))) :=
    hW.comp (by fun_prop)
  exact he.smul (hv.mul hw)

lemma ratioProfile_support (V W : ℝ→ℂ) (R : ℝ) :
    Function.support (ratioProfile V W R)⊆Function.support W := by
  intro x hx
  exact (mul_ne_zero_iff.mp hx).2

lemma logFamily_support (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (logFamily V W p)⊆Icc (-Real.log b) (-Real.log a) := by
  exact mellinLogFamily_support (ratioProfile V W p.1) a b ha
    ((ratioProfile_support V W p.1).trans hW) p.2

theorem ratioProfile_mellin_bound (V W : ℝ→ℂ)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b)
    (Rmax lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ R∈Icc 0 Rmax, ∀ σ∈Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin (ratioProfile V W R) ((σ : ℂ)+t*Complex.I)‖≤C := by
  obtain ⟨C,hC,hb⟩ := compact_family_fourier_weighted_bound
    (logFamily V W) (logFamily_smooth V W hV hW)
    (Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (logFamily_support V W a b ha hWs)
    (Icc 0 Rmax ×ˢ Icc lo hi) (isCompact_Icc.prod isCompact_Icc) j
  refine ⟨(1+2*Real.pi)^j*C,by positivity,?_⟩
  intro R hR σ hσ t
  rw [mellin_eq_logFamily_fourier]
  have ht : |t|=(2*Real.pi)*|t/(2*Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0<2*Real.pi)]
    field_simp
  have hbase : 1+|t|≤(1+2*Real.pi)*(1+|t/(2*Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t/(2*Real.pi))]
  calc
    _ ≤ ((1+2*Real.pi)*(1+|t/(2*Real.pi)|))^j *
        ‖𝓕 (mellinLogFamily (ratioProfile V W R) σ) (t/(2*Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1+2*Real.pi)^j * ((1+|t/(2*Real.pi)|)^j *
        ‖𝓕 (logFamily V W (R,σ)) (t/(2*Real.pi))‖) := by rw [mul_pow, mul_assoc]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb (R,σ) ⟨hR,hσ⟩ _) (by positivity)

lemma inverseProfile_eq_ratio (V W : ℝ→ℂ) (Dstar D : ℝ) :
    HeckeDetectorDyadicBridge.inverseProfile V W Dstar D=ratioProfile V W (D/Dstar) := by
  funext x
  unfold HeckeDetectorDyadicBridge.inverseProfile ratioProfile
  congr 2
  ring

theorem exists_profile_bounds (V W : ℝ→ℂ) (hV : ContDiff ℝ ∞ V)
    (hW : ContDiff ℝ ∞ W) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (lo hi : ℝ) :
    ∃ C : ℕ→ℝ, (∀ j, 0<C j) ∧
      (∀ j : ℕ, ∀ σ∈Icc lo hi, ∀ t : ℝ,
        (1+|t|)^j*‖mellin W ((σ : ℂ)+t*Complex.I)‖≤C j) ∧
      (∀ j : ℕ, ∀ Dstar D : ℝ, 0<Dstar → 0≤D → D≤4*Dstar →
        ∀ σ∈Icc lo hi, ∀ t : ℝ,
        (1+|t|)^j*‖mellin (HeckeDetectorDyadicBridge.inverseProfile V W Dstar D)
          ((σ : ℂ)+t*Complex.I)‖≤C j) := by
  choose Cp hCp hbP using fun j => compact_source_mellin_strip_decay W a b ha hWs hW lo hi j
  choose Ci hCi hbI using fun j => ratioProfile_mellin_bound V W hV hW a b ha hWs 4 lo hi j
  refine ⟨fun j => Cp j+Ci j,fun j => add_pos (hCp j) (hCi j),?_,?_⟩
  · intro j σ hσ t
    exact (hbP j σ hσ t).trans (le_add_of_nonneg_right (hCi j).le)
  · intro j Dstar D hDs hD hratio σ hσ t
    rw [inverseProfile_eq_ratio]
    exact (hbI j (D/Dstar) ⟨div_nonneg hD hDs.le,(div_le_iff₀ hDs).mpr hratio⟩ σ hσ t).trans
      (le_add_of_nonneg_left (hCp j).le)

end SevenEighths.HeckeDetectorDyadicProfiles

end

end OAI

end Source731

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorDyadicCutoff.lean; sha256: a51edeb1cffd8f4ca88f35e5bacf69eda2738c722546fd2392fa705516d300a7 -/
section Source732
namespace OAI

noncomputable section
open scoped Classical ContDiff
open Set
namespace SevenEighths.HeckeDetectorDyadicProfiles
open HeckeDetectorProfiles

lemma exists_positive_annular : ∃ W : ℝ→ℂ,
    ContDiff ℝ ∞ W ∧ Function.support W⊆Icc (1/4) (9/4) ∧
    ∀ x : ℝ, 0≤x → W x=DyadicTransfer.annularCutoff cutoff x := by
  obtain ⟨g,hgc,hgs,hgone,hgsupp,hgzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff 3 (by norm_num)
  let W : ℝ→ℂ := fun x => g (4*x-5)*DyadicTransfer.annularCutoff cutoff x
  have hs : ContDiff ℝ ∞ (DyadicTransfer.annularCutoff cutoff) :=
    (cutoff.smooth ⊤).sub ((cutoff.smooth ⊤).comp (by fun_prop))
  refine ⟨W,(hgs.comp (by fun_prop)).mul hs,?_,?_⟩
  · intro x hx
    have hg : g (4*x-5)≠0 := (mul_ne_zero_iff.mp hx).1
    have hh := hgsupp (subset_tsupport g hg)
    constructor <;> norm_num at hh <;> linarith [hh.1,hh.2]
  · intro x hx
    by_cases hh : DyadicTransfer.annularCutoff cutoff x=0
    · simp [W,hh]
    have ha := HeckeDetectorPartition.annular_support cutoff cutoff_one cutoff_zero x hx 0
      (by simpa using hh)
    norm_num at ha
    have hg : g (4*x-5)=1 := hgone _ (abs_le.mpr ⟨by linarith [ha.1],by linarith [ha.2]⟩)
    simp only [W,hg,one_mul]

def positiveAnnular : ℝ→ℂ := Classical.choose exists_positive_annular

lemma positiveAnnular_smooth : ContDiff ℝ ∞ positiveAnnular :=
  (Classical.choose_spec exists_positive_annular).1

lemma positiveAnnular_support : Function.support positiveAnnular⊆Icc (1/4) (9/4) :=
  (Classical.choose_spec exists_positive_annular).2.1

lemma positiveAnnular_eq (x : ℝ) (hx : 0≤x) :
    positiveAnnular x=DyadicTransfer.annularCutoff cutoff x :=
  (Classical.choose_spec exists_positive_annular).2.2 x hx

lemma positiveAnnular_zero (x : ℝ) (hx : 2≤x) : positiveAnnular x=0 := by
  rw [positiveAnnular_eq x (by linarith)]
  exact DyadicTransfer.annularCutoff_eq_zero_of_two_le cutoff cutoff_zero hx

theorem actual_profile_bounds :
    ∃ C : ℕ→ℝ, (∀ j, 0<C j) ∧
      (∀ j : ℕ, ∀ σ : ℝ, σ∈Icc (-2) 2 → ∀ t : ℝ,
        (1+|t|)^j*‖mellin positiveAnnular ((σ : ℂ)+t*Complex.I)‖≤C j) ∧
      (∀ j : ℕ, ∀ Dstar D : ℝ, 0<Dstar → 0≤D → D≤4*Dstar →
        ∀ σ : ℝ, σ∈Icc (-2) 2 → ∀ t : ℝ,
        (1+|t|)^j*‖mellin (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D)
          ((σ : ℂ)+t*Complex.I)‖≤C j) :=
  exists_profile_bounds cutoff positiveAnnular (cutoff.smooth ⊤) positiveAnnular_smooth
    (1/4) (9/4) (by norm_num) positiveAnnular_support (-2) 2

end SevenEighths.HeckeDetectorDyadicProfiles

end

end OAI

end Source732

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorNormalized.lean; sha256: 3bad55d4115e7264eff96fba13f8b3dc28823efd5376c7951eb2417eb96bf37b -/
section Source733
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorNormalized
open HeckeFamily HeckeDyadic HeckeDetectorFourier HeckeDetectorProfiles
open HeckeDetectorDyadicBridge HeckeDetectorDyadicProfiles HeckeDetectorFrequency

lemma plainCoefficient_positive (χ : Character) (D : ℝ) (hD : 0<D) (s : ℂ) :
    plainCoefficient χ positiveAnnular D s=
      plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) D s := by
  funext J
  unfold plainCoefficient
  rw [positiveAnnular_eq _ (div_nonneg (Nat.cast_nonneg _) hD.le)]

lemma inverseCoefficient_positive (χ : Character) (Dstar D : ℝ) (hD : 0<D) (s : ℂ) :
    inverseCoefficient χ cutoff positiveAnnular Dstar D s=
      inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar D s := by
  funext J
  unfold inverseCoefficient
  rw [positiveAnnular_eq _ (div_nonneg (Nat.cast_nonneg _) hD.le)]

theorem phaseProduct_norm (χ : Character) (Dstar U : ℝ) (s : ℂ) (j k : ℕ) (t : ℝ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U^21) :
    ‖phaseProduct χ Dstar U s j k t‖ =
      ((2 : ℝ)^j)^(1/2-s.re)*((2 : ℝ)^k)^(1/2-s.re)*
        (‖polynomial χ true (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((2 : ℝ)^j))
            ((2 : ℝ)^j) s.re (2*Real.pi*t-s.im)‖ *
         ‖polynomial χ false positiveAnnular ((2 : ℝ)^k) s.re (2*Real.pi*t-s.im)‖) := by
  obtain ⟨hj,hk⟩ := scales_le_eight_terminal (U^21) j k hprod
  have hDj : 0<(2 : ℝ)^j := by positivity
  have hNk : 0<(2 : ℝ)^k := by positivity
  unfold phaseProduct
  rw [norm_mul, ← inverseCoefficient_positive χ Dstar ((2 : ℝ)^j) hDj s,
    ← plainCoefficient_positive χ ((2 : ℝ)^k) hNk s]
  exact pair_phase_norm χ cutoff positiveAnnular positiveAnnular Dstar ((2 : ℝ)^j) ((2 : ℝ)^k)
    hDj hNk s t (fourierSet (U^21)) (fourierSet (U^21))
    (fourierSet_nonzero (U^21)) (fourierSet_nonzero (U^21))
    (inverse_annular_covered (U^21) ((2 : ℝ)^j) Dstar hDj hj cutoff positiveAnnular positiveAnnular_zero)
    (annular_covered (U^21) ((2 : ℝ)^k) hNk hk positiveAnnular positiveAnnular_zero)

theorem exists_normalized_product (R θ τ : ℝ) (hR : 0≤R)
    (hθ : 0≤θ) (hθ' : θ<3/4) (hτ : 0<τ) :
    ∃ C U₀ : ℝ, 0<C ∧ ∀ U : ℝ, U₀≤U →
      ∀ χ : Character, χ.residue≠1 → ∀ Dstar : ℝ, 2≤Dstar → Dstar≤U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ)≤R*U → ∀ ρ : ℂ,
      (51/100 : ℝ)≤ρ.re → LFunction χ ρ=0 → |ρ.im|≤U^θ →
      ∃ j∈Finset.range (HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k∈Finset.range (HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1),
          ∃ t : ℝ, ‖t‖≤U^τ ∧
            1≤C*(Real.logb 2 U)^2*((2 : ℝ)^j)^(1/2-ρ.re)*((2 : ℝ)^k)^(1/2-ρ.re)*
              (‖polynomial χ true (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((2 : ℝ)^j))
                  ((2 : ℝ)^j) ρ.re (2*Real.pi*t-ρ.im)‖ *
               ‖polynomial χ false positiveAnnular ((2 : ℝ)^k) ρ.re (2*Real.pi*t-ρ.im)‖) ∧
            (2 : ℝ)^j<4*Dstar ∧ Dstar/8<(2 : ℝ)^j*(2 : ℝ)^k ∧
            (2 : ℝ)^j*(2 : ℝ)^k<8*U^21 := by
  obtain ⟨C,U₀,hC,hbound⟩ := exists_common_frequency_witness R θ τ hR hθ hθ' hτ
  refine ⟨C,U₀,hC,?_⟩
  intro U hU χ hχ Dstar hD hDU hQ ρ hρ hzero hheight
  obtain ⟨j,hj,k,hk,t,ht,hb,hd,hn,hprod⟩ := hbound U hU χ hχ Dstar hD hDU hQ ρ hρ hzero hheight
  refine ⟨j,hj,k,hk,t,ht,?_,hd,hn,hprod⟩
  rw [phaseProduct_norm χ Dstar U ρ j k t hprod] at hb
  convert hb using 1; ring

end SevenEighths.HeckeDetectorNormalized

end

end OAI

end Source733

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorDyadicActual.lean; sha256: e3ba1b9c5a860f607d8c42476312a1551d72e99f72eb43ff79877b0742ea91dc -/
section Source734
namespace OAI

noncomputable section

open scoped Classical ContDiff
open Set
namespace SevenEighths.HeckeDetectorDyadicActual
open HeckeFamily HeckeDyadic HeckeDetectorDyadicProfiles HeckeDetectorProfiles

lemma inverse_profile_smooth (Dstar D : ℝ) :
    ContDiff ℝ ∞ (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D) := by
  unfold HeckeDetectorDyadicBridge.inverseProfile
  have hv : ContDiff ℝ ∞ (fun x : ℝ => cutoff (D*x/Dstar)) := (cutoff.smooth ⊤).comp (by fun_prop)
  exact hv.mul positiveAnnular_smooth

lemma inverse_profile_support (Dstar D : ℝ) :
    Function.support (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D)⊆Icc (1/4) (9/4) := by
  intro x hx
  exact positiveAnnular_support ((mul_ne_zero_iff.mp hx).2)

theorem simultaneous_upper (R dmax τ ε e κ η : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2<Z^τ →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
        (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
        51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, ∀ Dstar r m σ freq : ℝ,
        (χ j).modulus.absNorm≤Z^d → 0<Dstar →
        0≤r → r≤R → 0≤m → m≤R → (Z^d)^r≤4*Dstar →
        51/100≤σ → σ≤1 → |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
        (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
        ‖polynomial (χ j) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
          ((Z^d)^r) σ freq‖^2≤C*(Z^d)^((2*a-1)*r+ε) ∧
        ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) σ freq‖^2≤
          C*(Z^d)^((2*a-1)*min m (1-m)+ε) := by
  obtain ⟨Cp,hCp,hplain,hinverse⟩ := actual_profile_bounds
  obtain ⟨n,C,hC,hbound⟩ := source_dyadic_bounds R dmax τ ε e κ η
    hR hdmax hτ hε he he' hκ hκ' hη hbudget Cp (fun k => (hCp k).le)
  refine ⟨C,hC,?_⟩
  intro Z d hZ hd hdmax' hT ι _ χ hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσ hσ' hfreq hheight
  have hU : 1≤Z^d := Real.one_le_rpow hZ hd
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (by linarith) _
  have hstrip : Icc (1-a-6*e-σ) (2-σ)⊆Icc (-2 : ℝ) 2 := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hInv := hbound Z d hZ hd hdmax' hT χ hχ a i ha ha' hmax j true
    (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
    (1/4) (9/4) (by norm_num) (inverse_profile_support Dstar ((Z^d)^r))
    (inverse_profile_smooth Dstar ((Z^d)^r)) r σ freq hQ hr hrR hfreq hheight
    (fun x hx t => hinverse 2 Dstar ((Z^d)^r) hDs hD.le hratio x (hstrip hx) t)
    (fun x hx t => hinverse (n+2) Dstar ((Z^d)^r) hDs hD.le hratio x (hstrip hx) t)
  have hPlain := hbound Z d hZ hd hdmax' hT χ hχ a i ha ha' hmax j false
    positiveAnnular (1/4) (9/4) (by norm_num) positiveAnnular_support positiveAnnular_smooth
    m σ freq hQ hm hmR hfreq hheight
    (fun x hx t => hplain 2 x (hstrip hx) t)
    (fun x hx t => hplain (n+2) x (hstrip hx) t)
  exact ⟨hInv.1,hPlain.2⟩

end SevenEighths.HeckeDetectorDyadicActual

end

end OAI

end Source734

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorSaturation.lean; sha256: 483523e4b40337a39c66bbef06a8e2bc719dd5af4e4b533186010ea2ef75a8de -/
section Source735
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorSaturation
open HeckeDetectorFrequency

lemma logarithmic_cost_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ U : ℝ in atTop, (C*(Real.logb 2 U)^2)^2≤U^ε := by
  have ht := (logb_square_div_rpow_tendsto (ε/2) (by linarith)).pow 2
  have ht' := ht.const_mul (C^2)
  have hbound : ∀ᶠ U : ℝ in atTop,
      C^2*((Real.logb 2 U)^2/U^(ε/2))^2≤1 := by
    have hh : Tendsto (fun U : ℝ => C^2*((Real.logb 2 U)^2/U^(ε/2))^2)
        atTop (𝓝 0) := by simpa using ht'
    exact (tendsto_order.mp hh).2 1 (by norm_num) |>.mono (fun _ h => h.le)
  filter_upwards [hbound,eventually_gt_atTop (0 : ℝ)] with U hb hU
  have he : (U^(ε/2))^2=U^ε := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hU.le]
    congr 1
    norm_num
  rw [div_pow, he] at hb
  have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hU ε)).mp
    (show C^2*((Real.logb 2 U)^2)^2/U^ε≤1 by simpa only [mul_div_assoc] using hb)
  simpa only [one_mul,mul_one,mul_pow] using hh

lemma normalized_product_lower (U r m σ a ε K A B : ℝ)
    (hU : 1<U) (hr : 0≤r) (hm : 0≤m) (hσ : a≤σ)
    (_hK : 0≤K) (_hA : 0≤A) (_hB : 0≤B)
    (hcost : K^2≤U^ε)
    (hprod : 1≤K*(U^r)^(1/2-σ)*(U^m)^(1/2-σ)*(A*B)) :
    U^((2*a-1)*(r+m)-ε)≤A^2*B^2 := by
  have hUp : 0<U := by linarith
  have hcentral : (U^r)^(1/2-σ)*(U^m)^(1/2-σ)=U^((1/2-σ)*(r+m)) := by
    rw [← Real.rpow_mul hUp.le,← Real.rpow_mul hUp.le,← Real.rpow_add hUp]
    congr 1
    ring
  have hp : 1≤K*U^((1/2-σ)*(r+m))*(A*B) := by
    calc
      1 ≤ K*(U^r)^(1/2-σ)*(U^m)^(1/2-σ)*(A*B) := hprod
      _ = _ := by rw [←hcentral]; ring
  have hsq : 1≤(K*U^((1/2-σ)*(r+m))*(A*B))^2 := by nlinarith
  have he : (U^((1/2-σ)*(r+m)))^2=U^((1-2*σ)*(r+m)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
    congr 1
    ring
  rw [mul_pow,mul_pow,he,mul_pow] at hsq
  let q := (2*a-1)*(r+m)-ε
  let L := K^2*U^((1-2*σ)*(r+m))
  have hLq : L*U^q≤1 := by
    calc
      _ ≤ U^ε*U^((1-2*σ)*(r+m))*U^q := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUp.le _)
        exact mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hUp.le _)
      _ = U^(ε+(1-2*σ)*(r+m)+q) := by rw [←Real.rpow_add hUp,←Real.rpow_add hUp]
      _ ≤ U^0 := Real.rpow_le_rpow_of_exponent_le hU.le (by
        dsimp [q]
        nlinarith [mul_nonneg (sub_nonneg.mpr hσ) (add_nonneg hr hm)])
      _ = 1 := Real.rpow_zero _
  calc
    U^q = U^q*1 := by ring
    _ ≤ U^q*(L*(A^2*B^2)) := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hUp.le _)
    _ = (L*U^q)*(A^2*B^2) := by ring
    _ ≤ 1*(A^2*B^2) := mul_le_mul_of_nonneg_right hLq (by positivity)
    _ = _ := by ring

open HeckeFamily HeckeDyadic HeckeDetectorDyadicActual HeckeDetectorDyadicProfiles HeckeDetectorProfiles

theorem actual_saturation (R dmax τ ε e κ η Clower : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε/2) (hClower : 0≤Clower) :
    ∃ U₀ : ℝ, ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2<Z^τ →
      U₀≤Z^d → 1<Z^d →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
        (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
        51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, ∀ Dstar r m σ freq : ℝ,
        (χ j).modulus.absNorm≤Z^d → 0<Dstar →
        0≤r → r≤R → 0≤m → m≤R → (Z^d)^r≤4*Dstar →
        a≤σ → σ≤1 → |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
        (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
        let M := polynomial (χ j) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
          ((Z^d)^r) σ freq
        let S := polynomial (χ j) false positiveAnnular ((Z^d)^m) σ freq
        1≤Clower*(Real.logb 2 (Z^d))^2*((Z^d)^r)^(1/2-σ)*((Z^d)^m)^(1/2-σ)*(‖M‖*‖S‖) →
        m≤1/2+75*ε ∧ (Z^d)^((2*a-1)*r-2*ε)≤‖M‖^2 ∧
          (Z^d)^((2*a-1)*m-2*ε)≤‖S‖^2 := by
  obtain ⟨Cu,hCu,hupper⟩ := simultaneous_upper R dmax τ (ε/2) e κ η
    hR hdmax hτ (by linarith) he he' hκ hκ' hη hbudget
  have hev := (logarithmic_cost_eventually Clower ε hε).and
    (constant_absorbed_eventually Cu (ε/2) (by linarith))
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨U₀,?_⟩
  intro Z d hZ hd hd' hT hlarge hU ι _ χ hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσ hσ' hfreq hheight M S hprod
  have hσlo : 51/100≤σ := ha.trans hσ
  obtain ⟨hcost,hconst⟩ := hU₀ (Z^d) hlarge
  obtain ⟨hMu,hSu⟩ := hupper Z d hZ hd hd' hT χ hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσlo hσ' hfreq hheight
  have hp := normalized_product_lower (Z^d) r m σ a ε
    (Clower*(Real.logb 2 (Z^d))^2) ‖M‖ ‖S‖ hU hr hm hσ
    (mul_nonneg hClower (sq_nonneg _)) (norm_nonneg _) (norm_nonneg _) hcost hprod
  have hbound (x : ℝ) : Cu*(Z^d)^(x+ε/2)≤(Z^d)^(x+ε) := by
    calc
      _ ≤ (Z^d)^(ε/2)*(Z^d)^(x+ε/2) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (by linarith) _)
      _ = _ := by rw [←Real.rpow_add (by linarith : 0<Z^d)]; congr 1; ring
  exact Detector.simultaneous_saturation hU (by linarith) hε.le (sq_nonneg _) (sq_nonneg _)
    hp (hMu.trans (hbound _)) (hSu.trans (hbound _))

end SevenEighths.HeckeDetectorSaturation

end

end OAI

end Source735

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorDyadicGeometry.lean; sha256: d95f006e9e029c6be4fbf46aa7775d41c94e2f6f51ff36e203f871834c8a2df0 -/
section Source736
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorDyadicGeometry
open HeckeDyadic

lemma uniform_power_allowance (C p dmin α : ℝ) (hα : 0≤α) (hgap : p<dmin*α) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → C*Z^p≤(Z^d)^α := by
  have hh := constant_absorbed_eventually C (dmin*α-p) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ d hd
  have hZp : 0<Z := by linarith
  calc
    _ ≤ Z^(dmin*α-p)*Z^p := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(dmin*α) := by rw [←Real.rpow_add hZp]; congr 1; ring
    _ ≤ Z^(d*α) := Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd hα)
    _ = _ := Real.rpow_mul hZp.le _ _

lemma uniform_scale_threshold (dmin A : ℝ) (hd : 0<dmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → A≤Z^d := by
  have hh := constant_absorbed_eventually A dmin hd
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hA hZ d hd'
  exact hA.trans (Real.rpow_le_rpow_of_exponent_le hZ hd')

lemma uniform_zero_height (dmin τ : ℝ) (I : ℕ) (hgap : τ<dmin/2) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d →
      ∀ i : ℕ, i≤I → (3*i : ℕ)*Z^τ≤(Z^d)^(1/2 : ℝ) := by
  have hh := uniform_power_allowance (3*I : ℕ) τ dmin (1/2) (by norm_num) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hZ hZ1 d hd i hi
  have hn : (3*i : ℕ)≤3*I := by omega
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (Real.rpow_nonneg (by linarith) _)).trans (hZ d hd)

lemma uniform_height_budget (dmin τ η : ℝ) (I : ℕ) (hτ : 0≤τ)
    (hη : 0≤η) (hgap : 4*τ<dmin*η) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d →
      ∀ i : ℕ, i≤I → (3+(3*i+2 : ℕ)*Z^τ)^4≤(Z^d)^η := by
  have hh := uniform_power_allowance ((3*(I : ℝ)+5)^4*16) (4*τ) dmin η hη hgap
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hZ hZ1 d hd i hi
  have hT : 1≤Z^τ := Real.one_le_rpow hZ1 hτ
  have hp : (1+Z^τ)^4≤16*Z^(4*τ) := by
    calc
      _ ≤ (2*Z^τ)^4 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by
        have he : (Z^τ)^4=Z^(4*τ) := by
          rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : 0≤Z)]
          congr 1
          norm_num
          ring
        rw [mul_pow,he]
        norm_num
  calc
    _ ≤ (3*(I : ℝ)+5)^4*(1+Z^τ)^4 := indexed_height_bound i I hi (Z^τ) (by linarith)
    _ ≤ (3*(I : ℝ)+5)^4*(16*Z^(4*τ)) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((3*(I : ℝ)+5)^4*16)*Z^(4*τ) := by ring
    _ ≤ _ := hZ d hd

lemma uniform_fourier_allowance (dmax τ : ℝ) (hdmax : 0<dmax) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, 0≤d → d≤dmax →
      2*Real.pi*(Z^d)^(τ/(2*dmax))≤Z^τ/2 := by
  have hh := constant_absorbed_eventually (4*Real.pi) (τ/2) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ d hd hd'
  have hZp : 0<Z := by linarith
  have hp : (Z^d)^(τ/(2*dmax))≤Z^(τ/2) := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    have hm := mul_le_mul_of_nonneg_right hd' (show 0≤τ/(2*dmax) by positivity)
    have he : dmax*(τ/(2*dmax))=τ/2 := by field_simp
    rwa [he] at hm
  have he : Z^(τ/2)*Z^(τ/2)=Z^τ := by rw [←Real.rpow_add hZp]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le (τ/2))
  rw [he] at hh
  have hpi := mul_le_mul_of_nonneg_left hp (show 0≤2*Real.pi by positivity)
  nlinarith

end SevenEighths.HeckeDetectorDyadicGeometry

end

end OAI

end Source736

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorDyadicLengths.lean; sha256: a6983512af1c788015607a605ee25599eef56de27b32ca8bac8055c53c9230bc -/
section Source737
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorDyadicGeometry

lemma log_scale_bounds (U x : ℝ) (hU : 8≤U) (hx : 1≤x) (hxU : x≤8*U^21) :
    0≤Real.logb U x ∧ Real.logb U x≤22 ∧ U^(Real.logb U x)=x := by
  have hUp : 0<U := by linarith
  have hU1 : 1<U := by linarith
  have hxp : 0<x := by linarith
  have he := Real.rpow_logb hUp hU1.ne' hxp
  refine ⟨Real.logb_nonneg hU1 hx,?_,he⟩
  apply (Real.rpow_le_rpow_left_iff hU1).mp
  rw [he,show (22 : ℝ)=((22 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
  calc
    x ≤ 8*U^21 := hxU
    _ ≤ U*U^21 := mul_le_mul_of_nonneg_right hU (by positivity)
    _ = U^22 := by ring

lemma dyadic_scale_bounds (U : ℝ) (hU : 8≤U) (j k : ℕ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U^21) :
    0≤Real.logb U ((2 : ℝ)^j) ∧ Real.logb U ((2 : ℝ)^j)≤22 ∧
      0≤Real.logb U ((2 : ℝ)^k) ∧ Real.logb U ((2 : ℝ)^k)≤22 ∧
      U^(Real.logb U ((2 : ℝ)^j))=(2 : ℝ)^j ∧
      U^(Real.logb U ((2 : ℝ)^k))=(2 : ℝ)^k := by
  obtain ⟨hj,hk⟩ := HeckeDetectorDyadicBridge.scales_le_eight_terminal (U^21) j k hprod
  obtain ⟨hr,hr',he⟩ := log_scale_bounds U ((2 : ℝ)^j) hU (one_le_pow₀ (by norm_num)) hj
  obtain ⟨hm,hm',he'⟩ := log_scale_bounds U ((2 : ℝ)^k) hU (one_le_pow₀ (by norm_num)) hk
  exact ⟨hr,hr',hm,hm',he,he'⟩

lemma support_exponents (U t r m ε : ℝ) (hU : 1<U) (hcost : 8≤U^ε)
    (hleft : U^r<4*U^t) (hright : U^t/8<U^r*U^m) :
    r≤t+ε ∧ t-ε≤r+m := by
  have hUp : 0<U := by linarith
  constructor
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    calc
      U^r ≤ 4*U^t := hleft.le
      _ ≤ U^ε*U^t := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hUp.le _)
      _ = U^(t+ε) := by rw [←Real.rpow_add hUp]; congr 1; ring
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    calc
      U^(t-ε) = U^t/U^ε := Real.rpow_sub hUp _ _
      _ ≤ U^t/8 := div_le_div_of_nonneg_left (Real.rpow_nonneg hUp.le _) (by norm_num) hcost
      _ ≤ U^r*U^m := hright.le
      _ = U^(r+m) := (Real.rpow_add hUp _ _).symm

lemma truncation_scale (U t : ℝ) (hU : 2≤U) (ht : 1≤t) (ht' : t≤3/2) :
    2≤U^t ∧ U^t≤U^(3/2 : ℝ) := by
  have hU1 : 1≤U := by linarith
  constructor
  · apply hU.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU1 ht
  · exact Real.rpow_le_rpow_of_exponent_le hU1 ht'

end SevenEighths.HeckeDetectorDyadicGeometry

end

end OAI

end Source737

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorSimultaneous.lean; sha256: 047c424f89d6daba8327d96fd6882ef2d92a1ae137b147bd71eff11f04a1beab -/
section Source738
namespace OAI

noncomputable section

open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorSimultaneous
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorDyadicGeometry HeckeDetectorSaturation HeckeDetectorNormalized

theorem from_actual_zero (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, (χ j).modulus.absNorm≤Z^d → ∀ ρ : ℂ,
        LFunction (χ j) ρ=0 → a≤ρ.re → |ρ.im|≤(3*i : ℕ)*Z^τ →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤r ∧ r≤tstar+ε ∧ 0≤m ∧ m≤1/2+75*ε ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  have hdmaxp : 0<dmax := hdmin.trans_le hdmax
  have hτF : 0<τ/(2*dmax) := by positivity
  obtain ⟨C,UN,hC,hN⟩ := exists_normalized_product 1 (1/2) (τ/(2*dmax))
    (by norm_num) (by norm_num) (by norm_num) hτF
  obtain ⟨US,hS⟩ := actual_saturation 22 dmax τ ε e κ η C
    (by norm_num) hdmaxp.le hτ hε he he' hκ hκ' hη hbudget hC.le
  have hscale := uniform_scale_threshold dmin (max 8 (max UN US)) hdmin
  have hzeroH := uniform_zero_height dmin τ I hτzero
  have hbudgetH := uniform_height_budget dmin τ η I hτ.le hη hτheight
  have hFourier := uniform_fourier_allowance dmax τ hdmaxp hτ
  have hcost := uniform_power_allowance 8 0 dmin ε hε.le (mul_pos hdmin hε)
  have hT := (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ))
  have hall := hscale.and (hzeroH.and (hbudgetH.and (hFourier.and (hcost.and
    (hT.and (eventually_ge_atTop (1 : ℝ)))))))
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨Z₀,?_⟩
  intro Z hZlarge d hd hd' ι _ χ hχ a i hi ha ha' hmax j hQ ρ hzero hρ him tstar ht ht'
  obtain ⟨hscale,hzeroH,hbudgetH,hFourier,hcost,hT,hZ⟩ := hZ₀ Z hZlarge
  let U := Z^d
  have hd0 : 0≤d := (hdmin.trans_le hd).le
  have hlarge := hscale d hd
  have hU8 : 8≤U := (le_max_left _ _).trans hlarge
  have hUN : UN≤U := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hUS : US≤U := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hU2 : 2≤U := by linarith
  have hU1 : 1<U := by linarith
  have hUp : 0<U := by linarith
  have hρlo : 51/100≤ρ.re := ha.trans hρ
  have hρhi : ρ.re≤1 := le_of_lt (lt_of_not_ge (fun hh =>
    LFunction_ne_zero_of_one_le_re (χ j) hh (Or.inr (hχ j)) hzero))
  have hh := him.trans (hzeroH d hd i hi)
  obtain ⟨hDs,hDs'⟩ := truncation_scale U tstar hU2 ht ht'
  obtain ⟨J,hJ,K,hK,ν,hν,hprod,hD,hDN,hterminal⟩ :=
    hN U hUN (χ j) (hχ j) (U^tstar) hDs hDs' (by simpa using hQ) ρ hρlo hzero hh
  obtain ⟨hr,hr',hm,hm',heJ,heK⟩ := dyadic_scale_bounds U hU8 J K hterminal
  let r := Real.logb U ((2 : ℝ)^J)
  let m := Real.logb U ((2 : ℝ)^K)
  change U^r=(2 : ℝ)^J at heJ
  change U^m=(2 : ℝ)^K at heK
  have hJpow : (Z^d)^r=(2 : ℝ)^J := heJ
  have hKpow : (Z^d)^m=(2 : ℝ)^K := heK
  have hcostU : 8≤U^ε := by simpa using hcost d hd
  have hsupport := support_exponents U tstar r m ε hU1 hcostU
    (by simpa only [heJ] using hD) (by simpa only [heJ,heK] using hDN)
  have hfreq : |2*Real.pi*ν-ρ.im|+(Z^τ)/2≤(3*i+2 : ℕ)*Z^τ := by
    have habs : |ν|≤U^(τ/(2*dmax)) := by simpa only [Real.norm_eq_abs] using hν
    have hnu := (mul_le_mul_of_nonneg_left habs (show 0≤2*Real.pi by positivity)).trans
      (hFourier d hd0 hd')
    have hbase : |2*Real.pi*ν-ρ.im|≤2*Real.pi*|ν|+|ρ.im| := by
      simpa only [sub_zero,zero_sub,abs_neg,abs_mul,
        abs_of_pos (show 0<2*Real.pi by positivity)] using
        (abs_sub_le (2*Real.pi*ν) 0 ρ.im)
    push_cast at him ⊢
    nlinarith
  have hs := hS Z d hZ hd0 hd' hT hUS hU1 χ hχ a i ha ha' hmax j (U^tstar)
    r m ρ.re (2*Real.pi*ν-ρ.im) hQ (by positivity) hr hr' hm hm'
    (by simpa only [hJpow] using hD.le) hρ hρhi hfreq (hbudgetH d hd i hi)
    (by simpa only [hJpow,hKpow] using hprod)
  refine ⟨J,hJ,K,hK,ν,r,m,hν,heJ,heK,?_,hsupport.1,hm,hs.1,hs.2.1,hs.2.2⟩
  linarith [hsupport.2,hs.1]

theorem from_actual_maximum (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100<a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        a≤HeckeDetectorZeros.zeroMaximum χ hχ ((3*i : ℕ)*Z^τ) →
        (∀ j : ι, (χ j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ j : ι, ∃ ρ : ℂ, LFunction (χ j) ρ=0 ∧ a≤ρ.re ∧ |ρ.im|≤(3*i : ℕ)*Z^τ ∧
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤r ∧ r≤tstar+ε ∧ 0≤m ∧ m≤1/2+75*ε ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  obtain ⟨Z₀,hZ₀⟩ := from_actual_zero dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' ι _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  obtain ⟨j,ρ,hzero,him,heq⟩ := HeckeDetectorZeros.maximum_attained χ hχ
    ((3*i : ℕ)*Z^τ) (ha.trans_le hcurrent)
  have hρ : a≤ρ.re := by rw [heq]; exact hcurrent
  exact ⟨j,ρ,hzero,hρ,him,hZ₀ Z hZ d hd hd' χ hχ a i hi ha.le ha' hnext j
    (hQ j) ρ hzero hρ him tstar ht ht'⟩

end SevenEighths.HeckeDetectorSimultaneous

end

end OAI

end Source738

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorRowCountCrossing.lean; sha256: 1bc53cfbcc67251c35614694e55336e0e3ec3d872c7668ed7585a8ccff6864a4 -/
section Source739
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

def denominator (x : ℝ) : ℝ := 3-17*x/9

def primeWeight (x : ℝ) : ℝ := (2-8*x/9)*(1-x)

def crossing (x t : ℝ) : ℝ := ((2-8*x/9)*t-5*x/9)/denominator x

def inverseExponent (δ x r : ℝ) : ℝ := 1-δ*(x+(1-x)*r)

def plainExponent (δ x t r : ℝ) : ℝ := 1-δ*(4*x/9+(2-8*x/9)*(t-r))

def shortExponent (δ x t : ℝ) : ℝ := 1-δ+δ*primeWeight x/denominator x*(3/2-t)

def longExponent (δ t : ℝ) : ℝ := 1-δ+(5/6-δ)*(t-1)

lemma denominator_lower {x : ℝ} (hx : x≤1/2) : 37/18≤denominator x := by
  unfold denominator
  linarith

theorem crossing_bounds {x t : ℝ} (hx : 0≤x) (hx' : x≤1/2)
    (ht : 1≤t) (ht' : t≤3/2) :
    23/37≤crossing x t ∧ crossing x t≤1 ∧
      1/3≤t-crossing x t ∧ t-crossing x t≤1/2 := by
  have hd : 0<denominator x := lt_of_lt_of_le (by norm_num) (denominator_lower hx')
  have hp : 0≤2-8*x/9 := by linarith
  have hpt := mul_le_mul_of_nonneg_left ht hp
  have hpt' := mul_le_mul_of_nonneg_left ht' hp
  have hm : 0≤1-x := by linarith
  have hmt := mul_le_mul_of_nonneg_left ht hm
  have hmt' := mul_le_mul_of_nonneg_left ht' hm
  have he : t-crossing x t=((1-x)*t+5*x/9)/denominator x := by
    unfold crossing
    apply (eq_div_iff hd.ne').mpr
    rw [sub_mul,div_mul_cancel₀ _ hd.ne']
    unfold denominator
    ring
  refine ⟨(le_div_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_,?_,?_⟩
  · unfold denominator
    nlinarith
  · unfold denominator
    nlinarith
  · rw [he]
    apply (le_div_iff₀ hd).mpr
    unfold denominator
    nlinarith
  · rw [he]
    apply (div_le_iff₀ hd).mpr
    unfold denominator
    nlinarith

theorem crossing_average (δ x t r : ℝ) (hd : denominator x≠0) :
    ((2-8*x/9)*inverseExponent δ x r+(1-x)*plainExponent δ x t r)/denominator x =
      shortExponent δ x t := by
  unfold inverseExponent plainExponent shortExponent primeWeight
  field_simp
  unfold denominator
  ring

lemma inverse_at_crossing (δ x t : ℝ) (hd : denominator x≠0) :
    inverseExponent δ x (crossing x t)=shortExponent δ x t := by
  unfold inverseExponent crossing shortExponent primeWeight
  field_simp
  unfold denominator
  ring

lemma plain_at_crossing (δ x t : ℝ) (hd : denominator x≠0) :
    plainExponent δ x t (crossing x t)=shortExponent δ x t := by
  unfold plainExponent crossing shortExponent primeWeight
  field_simp
  unfold denominator
  ring

theorem selected_short_bound {δ x t r : ℝ} (hδ : 0≤δ) (_hx : 0≤x) (hx' : x≤1/2) :
    (r≤crossing x t → plainExponent δ x t r≤shortExponent δ x t) ∧
      (crossing x t≤r → inverseExponent δ x r≤shortExponent δ x t) := by
  have hd : denominator x≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (denominator_lower hx'))
  constructor
  · intro hr
    rw [←plain_at_crossing δ x t hd]
    unfold plainExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤2-8*x/9 by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]
  · intro hr
    rw [←inverse_at_crossing δ x t hd]
    unfold inverseExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤1-x by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]

theorem strict_inverse_capacity {r ν : ℝ} (hr : 23/37≤r) (hν : 0<ν) :
    r+2*((1-r)/2-ν)<1 ∧ 2*r+8*((1-r)/2-ν)<3 ∧
      (1-r)/2≤7/37 ∧ 9/37≤3-2*r-8*((1-r)/2-ν) := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma plain_capacity_bound {m κ : ℝ} (hm : 1/3≤m) (hm' : m≤1/2) (hκ : 3/4≤κ) :
    0≤(1-2*m)/(6*κ) ∧ (1-2*m)/(6*κ)≤2/27 := by
  have hkp : 0<6*κ := by linarith
  constructor
  · exact div_nonneg (by linarith) hkp.le
  · apply (div_le_iff₀ hkp).mpr
    nlinarith

lemma prime_supply_margin : (8/39 : ℝ)-7/37=23/1443 := by norm_num

lemma short_ge_base {δ x t : ℝ} (hδ : 0≤δ) (_hx : 0≤x) (hx' : x≤1/2)
    (ht : t≤3/2) : 1-δ≤shortExponent δ x t := by
  have hd : 0<denominator x := lt_of_lt_of_le (by norm_num) (denominator_lower hx')
  have hp : 0≤primeWeight x := mul_nonneg (by linarith) (by linarith)
  unfold shortExponent
  exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (mul_nonneg hδ hp) hd.le) (by linarith))

lemma inverse_capacity_exponent (δ x r : ℝ) :
    1-δ*r-2*(δ*x)*((1-r)/2)=inverseExponent δ x r := by unfold inverseExponent; ring

theorem capacity_loss {q m Δ γ : ℝ} (_hq : 0≤q) (hq' : q≤1/2)
    (hm : 1/3-γ≤m) (hm' : m≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hγ : 0≤γ) :
    2*q*(1-2*m)*(2/9-1/(9/2+12*Δ))≤Δ/4+2*γ := by
  have hd : 0<9/2+12*Δ := by linarith
  have hden : (16 : ℝ)≤(9/2)*(9/2+12*Δ) := by nlinarith
  have hqmul : q*(1-2*m)≤(1/2)*(1/3+2*γ) :=
    mul_le_mul hq' (by linarith) (by linarith) (by norm_num)
  have hn := mul_le_mul_of_nonneg_right hqmul (show 0≤24*Δ by positivity)
  have hg := mul_le_mul_of_nonneg_left hΔ' (show 0≤24*γ by positivity)
  have he : 2*q*(1-2*m)*(2/9-1/(9/2+12*Δ)) =
      24*q*(1-2*m)*Δ/((9/2)*(9/2+12*Δ)) := by field_simp; ring
  rw [he]
  apply (div_le_iff₀ (show 0<(9/2)*(9/2+12*Δ) by positivity)).mpr
  have hb := mul_le_mul_of_nonneg_left hden (show 0≤Δ/4+2*γ by positivity)
  nlinarith

theorem plain_capacity_comparison {δ x Δ t r m γ : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤1) (hx : 0≤x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hm : 1/3-γ≤m) (hm' : m≤1/2)
    (hγ : 0≤γ) (hlength : t-r-γ≤m) :
    1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ)≤plainExponent δ x t r+Δ/4+4*γ := by
  have hq : 0≤δ*x := mul_nonneg hδ hx
  have hq' : δ*x≤1/2 := (mul_le_mul hδ' hx' hx (by norm_num)).trans_eq (by ring)
  have hloss := capacity_loss hq hq' hm hm' hΔ hΔ' hγ
  have hc : 0≤δ*(2-8*x/9) := mul_nonneg hδ (by linarith)
  have hc' : δ*(2-8*x/9)≤2 := by
    have hh := mul_le_mul_of_nonneg_right hδ' (show 0≤2-8*x/9 by linarith)
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left (show t-r-m≤γ by linarith) hc
  have herror := mul_le_mul_of_nonneg_right hc' hγ
  have hid : (1-2*δ*m-2*(δ*x)*(1-2*m)*(2/9))-plainExponent δ x t r =
      δ*(2-8*x/9)*(t-r-m) := by unfold plainExponent; ring
  have hid' : 1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ) =
      (1-2*δ*m-2*(δ*x)*(1-2*m)*(2/9)) +
      2*(δ*x)*(1-2*m)*(2/9-1/(9/2+12*Δ)) := by ring
  rw [hid']
  linarith

lemma inverse_zero_capacity {δ r ν : ℝ} (hδ : 0≤δ)
    (hcap : (1-r)/2≤ν) : 1-δ*r≤1-δ+2*δ*ν := by
  have hh := mul_le_mul_of_nonneg_left hcap hδ
  nlinarith

lemma plain_zero_capacity {δ m κ ν : ℝ} (hδ : 0≤δ) (hκ : 0<κ)
    (hκ' : κ≤1) (hν : 0≤ν) (hcap : (1-2*m)/(6*κ)≤ν) :
    1-2*δ*m≤1-δ+6*δ*ν := by
  have hh := (div_le_iff₀ (show 0<6*κ by positivity)).mp hcap
  have hk := mul_le_mul_of_nonneg_right hκ' hν
  have hm : 1-2*m≤6*ν := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hm hδ
  nlinarith

lemma long_count_bound {δ r t γ : ℝ} (hδ : δ≤5/6) (_hγ : 0≤γ)
    (hr : r≤t+γ) :
    1-5/6+(5/6-δ)*r≤longExponent δ t+(5/6-δ)*γ := by
  have hh := mul_le_mul_of_nonneg_left hr (show 0≤5/6-δ by linarith)
  unfold longExponent
  nlinarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI

end Source739

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DetectorSlotSelection.lean; sha256: 38f9b0897fec2028bd01afc2f8c04e3d49d7af056dbd22d1a376f2b69ff066ac -/
section Source740
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorSlotSelection

theorem whole_slots {α : Type*} (s : Finset α) (w g : α→ℝ) (G mesh : ℝ)
    (hG : 0≤G) (hmesh : 0≤mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
    (hg : ∀ i∈s, 0≤g i) (hgG : ∀ i∈s, g i≤G)
    (q z : ℝ) (hq : 0≤q) (hqG : q≤G) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*g i) :
    ∃ T : Finset α, T⊆s ∧ (∑ i∈T, w i)≤z ∧ q*z-G*mesh≤∑ i∈T, w i*g i := by
  classical
  induction s using Finset.strongInductionOn generalizing q z with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a,ha,hmax⟩ := s.exists_max_image g hs
      by_cases hza : z≤w a
      · refine ⟨∅,Finset.empty_subset _,by simpa using hz,?_⟩
        have hzmesh : z≤mesh := hza.trans (hwm a ha)
        have hprod := mul_le_mul hqG hzmesh hz hG
        simpa only [Finset.sum_empty] using (sub_nonpos.mpr hprod)
      have haz : w a<z := lt_of_not_ge hza
      let s' := s.erase a
      have hss : s'⊂s := Finset.erase_ssubset ha
      have hsub : s'⊆s := Finset.erase_subset a s
      have hsum : ∑ i∈s, w i=w a+∑ i∈s', w i := by
        simpa [s',add_comm] using (Finset.sum_erase_add s w ha).symm
      have hgain : ∑ i∈s, w i*g i=w a*g a+∑ i∈s', w i*g i := by
        simpa [s',add_comm] using (Finset.sum_erase_add s (fun i => w i*g i) ha).symm
      let W := ∑ i∈s', w i
      let A := ∑ i∈s', w i*g i
      have hW : 0<W := by rw [hsum] at hzs; dsimp [W]; linarith
      have hA : 0≤A := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i (hsub hi)) (hg i (hsub hi)))
      have hAg : A≤W*g a := by
        calc
          _ ≤ ∑ i∈s', w i*g a := Finset.sum_le_sum (fun i hi =>
            mul_le_mul_of_nonneg_left (hmax i (hsub hi)) (hw i (hsub hi)))
          _ = _ := by dsimp [W]; rw [Finset.sum_mul]
      let q' := A/W
      have hq' : 0≤q' := div_nonneg hA hW.le
      have hq'a : q'≤g a := (div_le_iff₀ hW).mpr (by simpa [mul_comm] using hAg)
      have hq'G : q'≤G := hq'a.trans (hgG a ha)
      have he : q'*W=A := div_mul_cancel₀ A hW.ne'
      have hz' : 0≤z-w a := sub_nonneg.mpr haz.le
      have hzs' : z-w a≤∑ i∈s', w i := by rw [hsum] at hzs; linarith
      obtain ⟨T,hTs,hTz,hTgain⟩ := ih s' hss
        (fun i hi => hw i (hsub hi)) (fun i hi => hwm i (hsub hi))
        (fun i hi => hg i (hsub hi)) (fun i hi => hgG i (hsub hi))
        q' (z-w a) hq' hq'G hz' hzs' he.le
      have haT : a∉T := fun h => (Finset.mem_erase.mp (hTs h)).1 rfl
      refine ⟨insert a T,Finset.insert_subset_iff.mpr ⟨ha,hTs.trans hsub⟩,?_,?_⟩
      · rw [Finset.sum_insert haT]
        linarith
      · rw [Finset.sum_insert haT]
        have hprefix : q*z≤w a*g a+q'*(z-w a) := by
          rw [hsum,hgain] at hmean
          change q*(w a+W)≤w a*g a+A at hmean
          rw [←he] at hmean
          by_cases hqq : q≤q'
          · have h1 := mul_le_mul_of_nonneg_right hqq hz
            have h2 := mul_le_mul_of_nonneg_left hq'a (hw a ha)
            nlinarith
          · have hqq' : 0≤q-q' := by linarith
            have h1 := mul_le_mul_of_nonneg_left hzs hqq'
            rw [hsum] at h1
            change (q-q')*z≤(q-q')*(w a+W) at h1
            nlinarith
        linarith
    · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      have hz0 : z=0 := by simpa using le_antisymm hzs hz
      refine ⟨∅,Finset.empty_subset _,by simpa using hz,?_⟩
      simp only [Finset.sum_empty,hz0,mul_zero,zero_sub]
      exact neg_nonpos.mpr (mul_nonneg hG hmesh)

theorem whole_positive_slots {α : Type*} (s : Finset α) (w g : α→ℝ) (G mesh : ℝ)
    (hG : 0≤G) (hmesh : 0≤mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
    (hgG : ∀ i∈s, g i≤G)
    (q z : ℝ) (hq : 0≤q) (hqG : q≤G) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0) :
    ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧
      (∑ i∈T, w i)≤z ∧ q*z-G*mesh≤∑ i∈T, w i*g i := by
  classical
  obtain ⟨T,hTs,hTz,hTgain⟩ := whole_slots s w (fun i => max (g i) 0) G mesh hG hmesh
    hw hwm (fun i hi => le_max_right _ _) (fun i hi => max_le (hgG i hi) hG)
    q z hq hqG hz hzs hmean
  let P := T.filter (fun i => 0<g i)
  have hPT : P⊆T := Finset.filter_subset _ _
  refine ⟨P,hPT.trans hTs,fun i hi => (Finset.mem_filter.mp hi).2,?_,?_⟩
  · exact (Finset.sum_le_sum_of_subset_of_nonneg hPT (fun i hi _ => hw i (hTs hi))).trans hTz
  · have he : (∑ i∈T, w i*max (g i) 0)=∑ i∈P, w i*g i := by
      calc
        _ = ∑ i∈P, w i*max (g i) 0 := by
          symm
          apply Finset.sum_subset hPT
          intro i hi hn
          have hg : g i≤0 := le_of_not_gt (fun h => hn (Finset.mem_filter.mpr ⟨hi,h⟩))
          rw [max_eq_right hg,mul_zero]
        _ = _ := Finset.sum_congr rfl (fun i hi => by
          rw [max_eq_left (Finset.mem_filter.mp hi).2.le])
    rwa [he] at hTgain

theorem selected_product_spike {α : Type*} (s : Finset α) (w g : α→ℝ)
    (U δ mesh q z : ℝ) (hU : 1≤U) (hδ : 0≤δ) (hmesh : 0≤mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
    (hg : ∀ i∈s, g i≤δ/2) (hq : 0≤q) (hqδ : q≤δ/2) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0)
    : ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧ (∑ i∈T, w i)≤z ∧
      ∀ Q : α→ℂ, (∀ i∈s, 0<g i → U^(2*w i*g i)≤‖Q i‖^2) →
        U^(2*q*z-δ*mesh)≤‖∏ i∈T, Q i‖^2 := by
  obtain ⟨T,hTs,hTpos,hTz,hgain⟩ := whole_positive_slots s w g (δ/2) mesh
    (by positivity) hmesh hw hwm hg q z hq hqδ hz hzs hmean
  refine ⟨T,hTs,hTpos,hTz,?_⟩
  intro Q hQ
  have hUp : 0<U := by linarith
  calc
    _ ≤ U^(∑ i∈T, 2*w i*g i) := Real.rpow_le_rpow_of_exponent_le hU (by
      have he : (∑ i∈T, 2*w i*g i)=2*(∑ i∈T, w i*g i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [he]
      linarith)
    _ = ∏ i∈T, U^(2*w i*g i) := Real.rpow_sum_of_pos hUp _ _
    _ ≤ ∏ i∈T, ‖Q i‖^2 := Finset.prod_le_prod₀ (fun i hi => Real.rpow_nonneg hUp.le _)
      (fun i hi => hQ i (hTs hi) (hTpos i hi))
    _ = _ := by rw [norm_prod,Finset.prod_pow]

theorem selected_product_with_decrement {α : Type*} (s : Finset α) (w g : α→ℝ)
    (U δ mesh q z ν : ℝ) (hU : 1≤U) (hδ : 0≤δ) (hmesh : 0≤mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤mesh)
    (hg : ∀ i∈s, g i≤δ/2) (hq : 0≤q) (hqδ : q≤δ/2) (hz : 0≤z) (hν : 0≤ν)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0) :
    ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧
      (∑ i∈T, w i)≤max 0 (z-ν) ∧
      ∀ Q : α→ℂ, (∀ i∈s, 0<g i → U^(2*w i*g i)≤‖Q i‖^2) →
        U^(2*q*z-2*q*ν-δ*mesh)≤‖∏ i∈T, Q i‖^2 := by
  have hcap : max 0 (z-ν)≤z := max_le hz (by linarith)
  obtain ⟨T,hTs,hTp,hTw,hTb⟩ := selected_product_spike s w g U δ mesh q (max 0 (z-ν))
    hU hδ hmesh hw hwm hg hq hqδ (le_max_left _ _) (hcap.trans hzs) hmean
  refine ⟨T,hTs,hTp,hTw,?_⟩
  intro Q hQ
  apply le_trans _ (hTb Q hQ)
  apply Real.rpow_le_rpow_of_exponent_le hU
  have hh := mul_le_mul_of_nonneg_left (le_max_right 0 (z-ν)) (show 0≤2*q by positivity)
  nlinarith

end SevenEighths.HeckeDetectorSlotSelection

end

end OAI

end Source740

/- Original source: OAI/NumberTheory/DirichletL/Moments/SlotRemoval.lean; sha256: bb31cc639692cc79356f61ce83fc44366b14a6630f340b375ab1d15efb5369a3 -/
section Source741
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentSlotRemoval

theorem whole_slot_removal {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧
      (∑ i ∈ R, length i) ≤ min (∑ i ∈ s, length i) (F/(6*κ)+η) ∧
      (R=s ∨ F ≤ 6*κ*(∑ i ∈ R, length i)) := by
  have hthreshold : 0 ≤ F/(6*κ) := div_nonneg hF (by positivity)
  by_cases htotal : (∑ i ∈ s, length i) ≤ F/(6*κ)
  · refine ⟨s,Finset.Subset.refl _,le_min le_rfl ?_,Or.inl rfl⟩
    linarith
  · have htarget : 0 ≤ (∑ i ∈ s, length i)-F/(6*κ) := by linarith
    obtain ⟨T,hTs,hTupper,hTlower⟩ := HeckeDetectorSlotSelection.whole_slots
      s length (fun _ => 1) 1 η (by norm_num) hη hL hmesh
      (by intros; norm_num) (by intros; norm_num) 1
      ((∑ i ∈ s, length i)-F/(6*κ)) (by norm_num) (by norm_num)
      htarget (by linarith) (by simp)
    simp only [one_mul,mul_one] at hTlower
    have hsum : (∑ i ∈ s, length i)=(∑ i ∈ s\T, length i)+(∑ i ∈ T, length i) :=
      (Finset.sum_sdiff hTs).symm
    have hTnonneg : 0 ≤ ∑ i ∈ T, length i := Finset.sum_nonneg (fun i hi => hL i (hTs hi))
    refine ⟨s\T,Finset.sdiff_subset,le_min (by linarith) (by linarith),Or.inr ?_⟩
    have hremove : F/(6*κ) ≤ ∑ i ∈ s\T, length i := by linarith
    exact (div_le_iff₀ (by positivity : 0 < 6*κ)).mp hremove |>.trans_eq (mul_comm _ _)

theorem removal_cost {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧
      κ*(∑ i ∈ R, length i) ≤ F/6+κ*η ∧
      (R=s ∨ F-6*κ*(∑ i ∈ R, length i) ≤ 0) := by
  obtain ⟨R,hRs,hR,hpay⟩ := whole_slot_removal s length η κ F hη hκ hF hL hmesh
  refine ⟨R,hRs,?_,hpay.imp_right sub_nonpos.mpr⟩
  have hh := mul_le_mul_of_nonneg_left (hR.trans (min_le_right _ _)) hκ.le
  have he : κ*(F/(6*κ)+η)=F/6+κ*η := by field_simp
  rwa [he] at hh

theorem actual_product_removal {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧ (R=s ∨ F-6*κ*(∑ i ∈ R, length i) ≤ 0) ∧
      ∀ (Z : ℝ), 1 ≤ Z → ∀ (C : α → ℝ), (∀ i ∈ s, 0 ≤ C i) →
      ∀ (Q : α → ℂ), (∀ i ∈ s, ‖Q i‖^2 ≤ C i*Z^(κ*length i)) →
      ‖∏ i ∈ s, Q i‖^2 ≤
        (∏ i ∈ R, C i)*Z^(F/6+κ*η)*‖∏ i ∈ s\R, Q i‖^2 := by
  obtain ⟨R,hRs,hcost,hpay⟩ := removal_cost s length η κ F hη hκ hF hL hmesh
  refine ⟨R,hRs,hpay,?_⟩
  intro Z hZ C hC Q hQ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hremoved : ‖∏ i ∈ R, Q i‖^2 ≤ (∏ i ∈ R, C i)*Z^(F/6+κ*η) := by
    rw [norm_prod,← Finset.prod_pow]
    calc
      _ ≤ ∏ i ∈ R, C i*Z^(κ*length i) :=
        Finset.prod_le_prod₀ (fun i hi => sq_nonneg _) (fun i hi => hQ i (hRs hi))
      _ = (∏ i ∈ R, C i)*Z^(κ*(∑ i ∈ R, length i)) := by
        rw [Finset.prod_mul_distrib,Finset.mul_sum,Real.rpow_sum_of_pos hZpos]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ hcost) (Finset.prod_nonneg (fun i hi => hC i (hRs hi)))
  have he : (∏ i ∈ s, Q i)=(∏ i ∈ s\R, Q i)*(∏ i ∈ R, Q i) :=
    (Finset.prod_sdiff hRs).symm
  rw [he,norm_mul,mul_pow,mul_comm (‖∏ i ∈ s\R, Q i‖^2)]
  exact mul_le_mul_of_nonneg_right hremoved (sq_nonneg _)

end SevenEighths.CenteredMomentSlotRemoval

end

end OAI

end Source741

/- Original source: OAI/NumberTheory/DirichletL/Moments/WholeSlotDeletion.lean; sha256: ec2989a9ebb4a4575e08abfa036dfea5ed00a7e82284223bf38875154d022285 -/
section Source742
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentWholeSlotDeletion
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentHeckeHeight
local notation "O" => ActualEisensteinCubic.O

theorem whole_removal {α:Type*} (S:Finset α) (w:α→ℝ) (F κ mesh:ℝ)
    (hF:0≤F) (hκ:0<κ) (hm:0≤mesh)
    (hw:∀i∈S,0≤w i) (hwm:∀i∈S,w i≤mesh) :
    ∃R:Finset α,R⊆S ∧
      (∑i∈R,w i)≤min (∑i∈S,w i) (F/(6*κ)+mesh) ∧
      (R=S ∨ F≤6*κ*(∑i∈R,w i)) ∧
      κ*(∑i∈R,w i)≤F/6+κ*mesh := by
  obtain ⟨R,hR,hbound,hpay⟩:=CenteredMomentSlotRemoval.whole_slot_removal S w mesh κ F hm hκ hF hw hwm
  refine ⟨R,hR,hbound,hpay,?_⟩
  have hh:=mul_le_mul_of_nonneg_left (hbound.trans (min_le_right _ _)) hκ.le
  have he:κ*(F/(6*κ)+mesh)=F/6+κ*mesh:=by field_simp
  rwa [he] at hh

def normalizedSlot (η:Character) (m A z:O) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (t P:ℝ) : ℂ := (Real.sqrt P:ℂ)⁻¹*rowSlot η m A z S β t

def selectedProduct {α:Type*} (J:Finset α) (η:Character) (m A z:O)
    (W₁ W₂:ℝ→ℂ) (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ)
    (t X₁ X₂:ℝ) : ℂ :=
  ((Real.sqrt (X₁*X₂):ℂ)⁻¹*
    (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂))*
    ∏i∈J,normalizedSlot η m A z (S i) (β i) t (P i)

theorem selectedProduct_remove {α:Type*} (J R:Finset α) (hR:R⊆J)
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ) (t X₁ X₂:ℝ) :
    selectedProduct J η m A z W₁ W₂ S β P t X₁ X₂=
      (∏i∈R,normalizedSlot η m A z (S i) (β i) t (P i))*
        selectedProduct (J\R) η m A z W₁ W₂ S β P t X₁ X₂ := by
  unfold selectedProduct
  rw [←Finset.prod_sdiff hR]
  ring

theorem selectedProduct_energy_remove {α:Type*} (J R:Finset α) (hR:R⊆J)
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ) (t X₁ X₂ Z κ:ℝ)
    (hZ:0<Z) (w B:α→ℝ) (_hB:∀i∈R,0≤B i)
    (hslot:∀i∈R,‖normalizedSlot η m A z (S i) (β i) t (P i)‖^2≤B i*Z^(κ*w i)) :
    ‖selectedProduct J η m A z W₁ W₂ S β P t X₁ X₂‖^2≤
      ((∏i∈R,B i)*Z^(κ*∑i∈R,w i))*
        ‖selectedProduct (J\R) η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  rw [selectedProduct_remove J R hR,norm_mul,mul_pow,norm_prod,←Finset.prod_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    _≤∏i∈R,B i*Z^(κ*w i):=Finset.prod_le_prod₀ (fun i _=>sq_nonneg _) hslot
    _=_:=by rw [Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hZ,Finset.mul_sum]

end SevenEighths.CenteredMomentWholeSlotDeletion

end

end OAI

end Source742

/- Original source: OAI/NumberTheory/DirichletL/Moments/SlotNormalization.lean; sha256: 07c63682bf1244e45e04c796292c9774c43e5409f8b530c67ab0f8361fc1ac6f -/
section Source743
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSlotNormalization
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentHeckeHeight
local notation "O" => HeckeFamily.O

lemma sqrt_product_normalizer {ι:Type*} [Fintype ι] (X:ℝ) (P:ι→ℝ)
    (hX:0≤X) (hP:∀i,0≤P i) :
    ((Real.sqrt X:ℂ)⁻¹)*(∏i,(Real.sqrt (P i):ℂ)⁻¹)=
      (Real.sqrt (X*∏i,P i):ℂ)⁻¹ := by
  rw [Real.sqrt_mul hX,Real.sqrt_prod _ (fun i _=>hP i),Complex.ofReal_mul,
    Complex.ofReal_prod,mul_inv_rev,Finset.prod_inv_distrib]
  ring

theorem selectedProduct_univ {ι:Type*} [Fintype ι] [DecidableEq ι]
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (t X₁ X₂:ℝ) (hX:0≤X₁*X₂) (hP:∀i,0≤P i) :
    selectedProduct Finset.univ η m A z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ := by
  unfold selectedProduct normalizedSlot positiveSlotRow
  rw [Finset.prod_mul_distrib]
  have he:=sqrt_product_normalizer (X₁*X₂) P hX hP
  calc
    _=((Real.sqrt (X₁*X₂):ℂ)⁻¹*(∏i,(Real.sqrt (P i):ℂ)⁻¹))*
      ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
        ∏i,rowSlot η m A z (S i) (β i) t) := by ring
    _=_ := by rw [he]

end SevenEighths.CenteredMomentSlotNormalization

end

end OAI

end Source743

/- Original source: OAI/NumberTheory/DirichletL/Moments/NonprincipalGate.lean; sha256: 3db2ba9b4a71294d9c0d61ec5241ff0c7c1c19d1ce892761bd27061b816f4c04 -/
section Source744
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNonprincipalGate
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion
open ConcretePrimeRowBridge CenteredMomentRestrictedEnergy CenteredMomentChildRows RayFourExpansion
local notation "O" => HeckeFamily.O

def unitCharacter : Character := Character.ofResidue ⊤ top_ne_bot 1 (by
  intro u
  exact MulChar.one_apply (IsUnit.map (Ideal.Quotient.mk ⊤) u.isUnit))

theorem unitCharacter_primitive : FiniteFourier.IsPrimitiveOnIdeals unitCharacter.residue := by
  change FiniteFourier.IsPrimitiveOnIdeals (1:MulChar (O⧸(⊤:Ideal O)) ℂ)
  intro I hI
  exact (hI (Subsingleton.elim _ _)).elim

theorem unitCharacter_ideal (I:Ideal O) (hI:I≠0) : idealCoeff unitCharacter I=1 := by
  rw [←span_idealGenerator I,idealCoeff_span _ (idealGenerator_ne_zero I hI)]
  change (1:MulChar (O⧸(⊤:Ideal O)) ℂ) (Ideal.Quotient.mk _ (idealGenerator I))=1
  rw [show Ideal.Quotient.mk (⊤:Ideal O) (idealGenerator I)=1 from Subsingleton.elim _ _]
  exact map_one _

theorem principal_inducedBy_unit (χ:Character) (hχ:χ.residue=1) : InducedBy χ unitCharacter := by
  intro I
  by_cases hI:I=0
  · subst I
    simp only [map_zero,ite_self]
  · have hn:=idealGenerator_ne_zero I hI
    rw [unitCharacter_ideal I hI]
    rw [←span_idealGenerator I,idealCoeff_span χ hn]
    change χ.residue (Ideal.Quotient.mk χ.modulus (idealGenerator I))=_
    rw [hχ]
    by_cases hc:IsCoprime (Ideal.span {idealGenerator I}) χ.modulus
    · rw [ite_eq_left hc]
      exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hc)
    · rw [ite_eq_right hc]
      exact MulChar.map_nonunit _ (fun h=>hc ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp h))

theorem principal_row_fixed (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hχ:χ.residue=1) : FixedInducingRow η Q m A z :=
  ⟨χ,unitCharacter,unitCharacter_primitive,principal_inducedBy_unit χ hχ,le_top,hrow⟩

theorem actual_row_nonprincipal (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hex:¬FixedInducingRow η Q m A z) : χ.residue≠1 :=
  fun h=>hex (principal_row_fixed η χ Q m A z hrow h)

theorem nonexceptional_row_nonprincipal (η χ:Character) (ξ:RayCharacter)
    (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom (childCharacter η ξ)) m 1 (A*z) n)
    (hex:nonexceptional η ξ Q m A z) : χ.residue≠1 :=
  actual_row_nonprincipal (childCharacter η ξ) χ Q m A z hrow hex.2

end SevenEighths.CenteredMomentNonprincipalGate

end

end OAI

end Source744

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeDyadic.lean; sha256: 4504481a089a7ea7650ce98cc15a574a4f354cf11aa5199b2611b595b84581b5 -/
section Source745
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

private instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
private instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def coefficient (χ : Character) (I : Ideal O) : ℂ :=
  (IdealMangoldt.value I : ℂ) * idealCoeff χ I

@[simp] theorem coefficient_zero (χ : Character) : coefficient χ 0 = 0 := by
  unfold coefficient
  rw [IdealMangoldt.value_zero, Complex.ofReal_zero, zero_mul]

def series (χ : Character) (s : ℂ) : ℂ := -deriv (LFunction χ) s / LFunction χ s

theorem series_eq_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    series χ s = ∑' I : NonzeroIdeal, coefficient χ I.val * (norm I : ℂ)^(-s) := by
  have he : (∑' I : NonzeroIdeal, (IdealMangoldt.value I.val : ℂ) *
      IdealEuler.weighted (idealCoeff χ) s I.val) =
      ∑' I : Ideal O, (IdealMangoldt.value I : ℂ) * IdealEuler.weighted (idealCoeff χ) s I := by
    apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | I ≠ 0})
      (f := fun I : Ideal O => (IdealMangoldt.value I : ℂ) * IdealEuler.weighted (idealCoeff χ) s I)
    intro I hI hi
    subst I
    exact hI (by
      change (IdealMangoldt.value 0 : ℂ) * IdealEuler.weighted (idealCoeff χ) s 0 = 0
      rw [IdealMangoldt.value_zero, Complex.ofReal_zero, zero_mul])
  change -deriv (LFunction χ) s / LFunction χ s = _
  rw [← HeckeLogDerivative.coeff_LSeries_eq χ hs]
  change LSeries (IdealLogDerivative.coeff (idealCoeff χ)) s = _
  rw [← IdealLogDerivative.mangoldt_series_eq_LSeries _ (idealCoeff_norm_le_one χ) s hs, ← he]
  apply tsum_congr
  intro I
  simp only [coefficient, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight]
  rw [ite_eq_right_iff.mpr (fun h => (I.property h).elim)]
  simp only [HeckeDyadic.norm, Complex.ofReal_natCast, mul_assoc]

def twistedCoefficient (χ : Character) (σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ I.val * (norm I : ℂ)^(-shift σ freq)

theorem twisted_coefficient_summable (χ : Character) (c σ freq : ℝ)
    (hc : 1 < c+σ) :
    Summable (fun I : NonzeroIdeal => ‖twistedCoefficient χ σ freq I‖*(norm I)^(-c)) := by
  have hf := (IdealLogDerivative.mangoldt_weighted_summable_norm
    (idealCoeff χ) (idealCoeff_norm_le_one χ) ((c+σ : ℝ) : ℂ)
    (by simpa using hc)).comp_injective (Subtype.val_injective : Function.Injective
      (fun I : NonzeroIdeal => I.val))
  convert hf using 1
  ext I
  simp only [Function.comp_apply, twistedCoefficient, coefficient, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight,
    ite_eq_right_iff.mpr (fun h => (I.property h).elim), norm_mul]
  change (‖(IdealMangoldt.value I.val : ℂ)‖ * ‖idealCoeff χ I.val‖ *
      ‖(norm I : ℂ)^(-shift σ freq)‖) * (norm I)^(-c) =
    ‖(IdealMangoldt.value I.val : ℂ)‖ * (‖idealCoeff χ I.val‖ *
      ‖(norm I : ℂ)^(-((c+σ : ℝ) : ℂ))‖)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I),
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp only [Complex.neg_re, shift_re, Complex.ofReal_re]
  rw [mul_assoc, mul_assoc, ← Real.rpow_add (norm_pos I)]
  congr 3
  ring

def summand (χ : Character) (W : ℝ → ℂ) (D σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ I.val * W (norm I/D) * ((norm I/D : ℝ) : ℂ)^(-shift σ freq)

def polynomial (χ : Character) (W : ℝ → ℂ) (D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ)) * ∑' I : NonzeroIdeal, summand χ W D σ freq I

theorem twisted_series_eq (χ : Character) (σ freq : ℝ)
    {s : ℂ} (hs : 1 < (s+shift σ freq).re) :
    (∑' I : NonzeroIdeal, twistedCoefficient χ σ freq I*(norm I : ℂ)^(-s)) =
      series χ (s+shift σ freq) := by
  rw [series_eq_tsum χ hs]
  apply tsum_congr
  intro I
  unfold twistedCoefficient
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_pos I).ne')]
  congr 2
  ring

theorem polynomial_eq_weighted (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0 < D) :
    polynomial χ W D σ freq =
      (D : ℂ)^(shift σ freq-(1/2 : ℂ)) *
        ∑' I : NonzeroIdeal, twistedCoefficient χ σ freq I * W (norm I/D) := by
  have he (I : NonzeroIdeal) : summand χ W D σ freq I =
      (D : ℂ)^(shift σ freq) * (twistedCoefficient χ σ freq I * W (norm I/D)) := by
    unfold summand twistedCoefficient
    rw [CompletedGauss.positive_quotient_cpow_neg _ _ (norm_pos I) hD]
    ring
  unfold polynomial
  simp_rw [he]
  rw [tsum_mul_left, ← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 2
  ring

theorem polynomial_mellin (χ : Character) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hWs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (D c σ freq : ℝ) (hD : 0 < D) (hc : 1 < c+σ) :
    polynomial χ W D σ freq = (1/(2*Real.pi) : ℂ)*∫ t : ℝ,
      mellin W ((c : ℂ)+t*Complex.I) *
        (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) *
          series χ (((c : ℂ)+t*Complex.I)+shift σ freq) := by
  rw [polynomial_eq_weighted χ W D σ freq hD]
  rw [CompletedGauss.weightedMellin_inversion norm norm_pos
    (twistedCoefficient χ σ freq) c (twisted_coefficient_summable χ c σ freq hc)
    W a b ha hWs hW D hD]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [twisted_series_eq χ σ freq (by simpa using hc)]
  have he : (D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I) =
      (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
    congr 1
    ring
  calc
    _ = mellin W ((c : ℂ)+t*Complex.I) *
        ((D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I)) *
          series χ (((c : ℂ)+t*Complex.I)+shift σ freq) := by ring
    _ = _ := by rw [he]

end SevenEighths.HeckePrimeDyadic

end

end OAI

end Source745

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimePowers.lean; sha256: 70c14f0e2aeb4f582ecd897b62b7f3cc39ef7d33fd8492d821c390fbf5a4248a -/
section Source746
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckePrimePowers
open HeckeFamily UniqueFactorizationMonoid

theorem nonprime_primePow_powerful {I : Ideal O} (hpow : IsPrimePow I) (hprime : ¬Prime I) :
    CompletedGauss.PowerfulIdeal I := by
  obtain ⟨P,k,hP,hk,rfl⟩ := hpow
  have hk2 : 2≤k := by
    by_contra h
    have hk1 : k=1 := by omega
    subst k
    exact hprime (by simpa using hP)
  refine ⟨pow_ne_zero _ hP.ne_zero,?_⟩
  intro Q hQ
  rw [hP.irreducible.normalizedFactors_pow] at hQ ⊢
  have hQP := (Multiset.mem_replicate.mp hQ).2
  subst Q
  simpa using hk2

def logWeight (I : Ideal O) : ℝ := IdealMangoldt.value I / Real.log (Ideal.absNorm I)

theorem logWeight_nonneg (I : Ideal O) : 0≤logWeight I :=
  div_nonneg (IdealMangoldt.value_nonneg _) (Real.log_natCast_nonneg _)

theorem logWeight_le_one (I : Ideal O) : logWeight I≤1 := by
  by_cases hlog : Real.log (Ideal.absNorm I)=0
  · simp [logWeight,hlog]
  · apply (div_le_one (lt_of_le_of_ne (Real.log_natCast_nonneg _) (Ne.symm hlog))).mpr
    exact IdealLogDerivative.value_le_log_norm I

theorem logWeight_prime {P : Ideal O} (hP : Prime P) : logWeight P=1 := by
  have hp2 : (2 : ℝ)≤P.absNorm := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩
  have hp : 0<Real.log (P.absNorm : ℝ) := Real.log_pos (by linarith)
  rw [logWeight, PNT.IdealPrimeMass.value_prime hP, div_self hp.ne']

theorem logWeight_eq_zero {I : Ideal O} (hI : ¬IsPrimePow I) : logWeight I=0 := by
  simp only [logWeight, IdealMangoldt.value, ite_eq_right hI, zero_div]

theorem sum_prime_extraction (χ : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑ I∈S, (logWeight I : ℂ)*idealCoeff χ I*f I) -
      (∑ I∈S.filter Prime, idealCoeff χ I*f I) =
      ∑ I∈S.filter (fun I => IsPrimePow I ∧ ¬Prime I),
        (logWeight I : ℂ)*idealCoeff χ I*f I := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hP : Prime I
  · simp only [hP, ite_true, not_true_eq_false, and_false, ite_false,
      logWeight_prime hP, Complex.ofReal_one, one_mul, sub_self]
  · by_cases hp : IsPrimePow I
    · simp [hP,hp]
    · simp [hP,hp,logWeight_eq_zero hp]

theorem prime_extraction_error (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ)
      (X B : ℝ), 1≤X → 0≤B →
      (∀ I∈S, (I.absNorm : ℝ)≤X) → (∀ I∈S, ‖f I‖≤B) →
      ‖(∑ I∈S, (logWeight I : ℂ)*idealCoeff χ I*f I) -
        (∑ I∈S.filter Prime, idealCoeff χ I*f I)‖ ≤ C*X^(1/2+ε)*B := by
  obtain ⟨C,hC,hcount⟩ := CompletedGauss.powerful_ideal_count ε hε
  refine ⟨C,hC,?_⟩
  intro χ S f X B hX hB hnorm hf
  rw [sum_prime_extraction]
  let A := S.filter (fun I => IsPrimePow I ∧ ¬Prime I)
  have hA : (A.card : ℝ)≤C*X^(1/2+ε) := by
    apply hcount A X hX
    intro I hI
    obtain ⟨hIS,hpow,hprime⟩ := Finset.mem_filter.mp hI
    exact ⟨nonprime_primePow_powerful hpow hprime,hnorm I hIS⟩
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _I∈A, B := by
      apply Finset.sum_le_sum
      intro I hI
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (logWeight_nonneg _)]
      have hcoeff : logWeight I*‖idealCoeff χ I‖≤1 :=
        (mul_le_of_le_one_right (logWeight_nonneg I) (idealCoeff_norm_le_one χ I)).trans
          (logWeight_le_one I)
      exact (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)).trans
        (by simpa using hf I (Finset.mem_filter.mp hI).1)
    _ = (A.card : ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hA hB

end SevenEighths.HeckePrimePowers

end

end OAI

end Source746

/- Original source: OAI/NumberTheory/DirichletL/CompactProfileFamily.lean; sha256: 0d19eb7d35bb31d17270f794e92e2a20ca9c2abcc5c1e15c3f7e08e3e4263937 -/
section Source747
namespace OAI

noncomputable section
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace SevenEighths.CompactProfileFamily
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem section_deriv_smooth (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : E × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : E × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : E × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem compact_family_deriv_integrable (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : E) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable F hF K hK hsupp σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) =
      ‖𝓕 (iteratedDeriv j (F σ)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (F σ)) w‖ ≤ C := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (F σ)) w).trans
    exact hb σ hσ
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := mul_comm _ _
    _ ≤ C := hn

theorem compact_family_fourier_weighted_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  have hbase : ‖𝓕 (F σ) w‖ ≤ C₀ := by simpa using h0 σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * C₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * Cj := mul_le_mul_of_nonneg_left (hj σ hσ w) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end SevenEighths.CompactProfileFamily

end

end OAI

end Source747

/- Original source: OAI/NumberTheory/DirichletL/PrimeLogProfile.lean; sha256: d4f8d1d6923cc340afa0d1a5144b5335e55b2600243d2d6db94f2577973288b3 -/
section Source748
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology FourierTransform SchwartzMap
open Set Filter MeasureTheory
namespace SevenEighths.PrimeLogProfile

def safeInverse (x : ℝ) : ℂ :=
  (1-QuadraticInitialBound.sieveCutoff (4*x))/(x : ℂ)

theorem safeInverse_eq (x : ℝ) (hx : 1/2≤|x|) : safeInverse x=(x : ℂ)⁻¹ := by
  have hz : QuadraticInitialBound.sieveBump (4*x)=0 := by
    apply QuadraticInitialBound.sieveBump.zero_of_le_dist
    change 2≤dist (4*x) 0
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul]
    norm_num
    linarith
  simp [safeInverse, QuadraticInitialBound.sieveCutoff_apply, hz]

theorem safeInverse_smooth : ContDiff ℝ ∞ safeInverse := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : safeInverse =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ)<1/4)] with y hy
      have hy' : |y|<1/4 := by simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hy
      have hone : QuadraticInitialBound.sieveBump (4*y)=1 := by
        apply QuadraticInitialBound.sieveBump.one_of_mem_closedBall
        change dist (4*y) 0≤1
        rw [dist_zero_right, Real.norm_eq_abs, abs_mul]
        norm_num
        linarith
      simp [safeInverse, QuadraticInitialBound.sieveCutoff_apply, hone]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hnum : ContDiff ℝ ∞ (fun y : ℝ => (1 : ℂ)-QuadraticInitialBound.sieveCutoff (4*y)) :=
      contDiff_const.sub ((QuadraticInitialBound.sieveCutoff.smooth ⊤).comp
        (contDiff_const.mul contDiff_id))
    change ContDiffAt ℝ ∞ (fun y : ℝ => (1-QuadraticInitialBound.sieveCutoff (4*y))/(y : ℂ)) x
    simpa only [div_eq_mul_inv, Pi.inv_apply, Complex.ofRealCLM_apply] using hnum.contDiffAt.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.inv (Complex.ofReal_ne_zero.mpr hx))

def profile (W : ℝ→ℂ) (A y : ℝ) : ℂ :=
  W y * (A : ℂ) * safeInverse (1+A*Real.log y)

theorem profile_support (W : ℝ→ℂ) (A : ℝ) :
    Function.support (profile W A) ⊆ Function.support W := by
  intro y hy hW
  exact hy (by simp [profile,hW])

theorem profile_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (A : ℝ) :
    ContDiff ℝ ∞ (profile W A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y=0
  · subst y
    have he : profile W A =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [(isOpen_Iio.mem_nhds ha)] with y hy
      have hw : W y=0 := by
        by_contra hh
        exact (not_le_of_gt hy) (hWs hh).1
      simp [profile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact ((hW.contDiffAt.mul contDiffAt_const).mul
      (safeInverse_smooth.contDiffAt.comp y
        (contDiffAt_const.add (contDiffAt_const.mul (Real.contDiffAt_log.mpr hy)))))

def logFamily (W : ℝ→ℂ) (p : ℝ×ℝ) (u : ℝ) : ℂ :=
  Real.exp (-p.2*u) • (W (Real.exp (-u)) * (p.1 : ℂ) * safeInverse (1-p.1*u))

theorem logFamily_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (logFamily W)) := by
  change ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ =>
    Real.exp (-p.1.2*p.2) • (W (Real.exp (-p.2)) * (p.1.1 : ℂ) * safeInverse (1-p.1.1*p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.snd.neg.mul contDiff_snd)).smul
    (((hW.comp (Real.contDiff_exp.comp contDiff_snd.neg)).mul
      (Complex.ofRealCLM.contDiff.comp contDiff_fst.fst)).mul
      (safeInverse_smooth.comp (contDiff_const.sub (contDiff_fst.fst.mul contDiff_snd))))

theorem logFamily_eq (W : ℝ→ℂ) (A σ u : ℝ) :
    logFamily W (A,σ) u = CubicReflectionKernel.mellinLogFamily (profile W A) σ u := by
  simp only [logFamily, CubicReflectionKernel.mellinLogFamily, profile, Real.log_exp]
  congr 3
  ring

theorem logFamily_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (logFamily W p) ⊆ Icc (-Real.log b) (-Real.log a) := by
  have he : logFamily W p = CubicReflectionKernel.mellinLogFamily (profile W p.1) p.2 := by
    funext u
    exact logFamily_eq W p.1 p.2 u
  rw [he]
  exact CubicReflectionKernel.mellinLogFamily_support _ a b ha ((profile_support W p.1).trans hWs) _

theorem uniform_mellin_decay (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ A ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin (profile W A) ((σ : ℂ)+t*Complex.I)‖≤C := by
  obtain ⟨C,hC,hb⟩ := CompactProfileFamily.compact_family_fourier_weighted_bound
    (logFamily W) (logFamily_smooth W hW)
    (Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (logFamily_support W a b ha hWs)
    ((Icc (0 : ℝ) 1) ×ˢ (Icc lo hi)) (isCompact_Icc.prod isCompact_Icc) j
  refine ⟨(1+2*Real.pi)^j*C,by positivity,?_⟩
  intro A hA σ hσ t
  rw [CubicReflectionKernel.mellin_eq_logFamily_fourier]
  have he : CubicReflectionKernel.mellinLogFamily (profile W A) σ = logFamily W (A,σ) := by
    funext u
    exact (logFamily_eq W A σ u).symm
  rw [he]
  have ht : |t|=(2*Real.pi)*|t/(2*Real.pi)| := by
    rw [abs_div,abs_of_pos (by positivity : 0<2*Real.pi)]
    field_simp
  have hbase : 1+|t|≤(1+2*Real.pi)*(1+|t/(2*Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos,abs_nonneg (t/(2*Real.pi))]
  calc
    _ ≤ ((1+2*Real.pi)*(1+|t/(2*Real.pi)|))^j *
        ‖𝓕 (logFamily W (A,σ)) (t/(2*Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1+2*Real.pi)^j*((1+|t/(2*Real.pi)|)^j *
        ‖𝓕 (logFamily W (A,σ)) (t/(2*Real.pi))‖) := by rw [mul_pow,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb (A,σ) ⟨hA,hσ⟩ _) (by positivity)

theorem profile_eq_log_division (W : ℝ→ℂ) (a b P : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hP : 0<P)
    (hlarge : 2*(|Real.log a|+|Real.log b|)+1≤Real.log P) :
    profile W (1/Real.log P) = fun y => W y / (Real.log (P*y) : ℂ) := by
  funext y
  by_cases hy : W y=0
  · simp [profile,hy]
  have hs := hWs hy
  have hyp : 0<y := ha.trans_le hs.1
  have hlogs : |Real.log y|≤|Real.log a|+|Real.log b| := by
    apply abs_le.mpr
    constructor
    · have h := Real.log_le_log ha hs.1
      linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
    · have h := Real.log_le_log hyp hs.2
      linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]
  have hp : 0<Real.log P := by linarith [abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
  have hhalf : 1/2≤1+(1/Real.log P)*Real.log y := by
    have he : 1+(1/Real.log P)*Real.log y = (Real.log P+Real.log y)/Real.log P := by field_simp
    rw [he]
    apply (le_div_iff₀ hp).mpr
    linarith [(abs_le.mp hlogs).1]
  have hi := safeInverse_eq (1+(1/Real.log P)*Real.log y)
    (hhalf.trans (le_abs_self _))
  rw [profile,hi,Real.log_mul (ne_of_gt hP) (ne_of_gt hyp)]
  push_cast
  have hn : (Real.log P : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hn' : (Real.log P : ℂ)+(Real.log y : ℂ)≠0 := by
    have : 0<Real.log P+Real.log y := by
      linarith [(abs_le.mp hlogs).1,abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
    exact_mod_cast this.ne'
  field_simp

end SevenEighths.PrimeLogProfile

end

end OAI

end Source748

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeAnnular.lean; sha256: 3687ff362cecec75d4be082abc2fc2d2a2adf6494d04a332b8def77bc7b26709 -/
section Source749
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Set
namespace SevenEighths.HeckePrimeAnnular
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def annulusSet (b D : ℝ) : Finset (Ideal O) := idealsUpTo ⌊max 1 b*D⌋₊

def annularWeight (W : ℝ→ℂ) (D σ freq : ℝ) (I : Ideal O) : ℂ :=
  W ((I.absNorm : ℝ)/D)*(((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-shift σ freq)

def primePolynomial (χ : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ I∈(annulusSet b D).filter Prime,
    idealCoeff χ I*annularWeight W D σ freq I

theorem annular_support (W : ℝ→ℂ) (a b D : ℝ) (ha : 0<a) (hD : 0<D)
    (hWs : Function.support W⊆Icc a b) (I : Ideal O)
    (hw : W ((I.absNorm : ℝ)/D)≠0) : I∈annulusSet b D := by
  have hs := hWs hw
  apply mem_idealsUpTo.mpr
  constructor
  · have hnorm : 0<(I.absNorm : ℝ) := by
      have := (le_div_iff₀ hD).mp hs.1
      nlinarith
    exact_mod_cast hnorm
  · have hn := (div_le_iff₀ hD).mp hs.2
    exact Nat.le_floor (hn.trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le))

theorem log_polynomial_eq_finite (χ : Character) (W : ℝ→ℂ) (a b D σ freq : ℝ)
    (ha : 0<a) (hD : 0<D) (hWs : Function.support W⊆Icc a b)
    (hlarge : 2*(|Real.log a|+|Real.log b|)+1≤Real.log D) :
    HeckePrimeDyadic.polynomial χ (PrimeLogProfile.profile W (1/Real.log D)) D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑ I∈annulusSet b D,
        (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I := by
  rw [PrimeLogProfile.profile_eq_log_division W a b D ha hWs hD hlarge]
  unfold HeckePrimeDyadic.polynomial
  congr 1
  have he : (fun I : NonzeroIdeal => HeckePrimeDyadic.summand χ
      (fun y => W y/(Real.log (D*y) : ℂ)) D σ freq I) =
      fun I : NonzeroIdeal => (HeckePrimePowers.logWeight I.val : ℂ)*
        idealCoeff χ I.val*annularWeight W D σ freq I.val := by
    funext I
    unfold HeckePrimeDyadic.summand HeckePrimeDyadic.coefficient annularWeight
    dsimp only [HeckePrimePowers.logWeight, HeckeDyadic.norm]
    rw [mul_div_cancel₀ _ hD.ne']
    simp only [Complex.ofReal_div]
    ring
  rw [he]
  calc
    _ = ∑' I : Ideal O, (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I := by
      apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | I≠0})
        (f := fun I : Ideal O => (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I)
      intro I hI hzero
      subst I
      exact hI (by simp [HeckePrimePowers.logWeight])
    _ = _ := by
      apply tsum_eq_sum
      intro I hI
      have hw : W ((I.absNorm : ℝ)/D)=0 := by
        by_contra hh
        exact hI (annular_support W a b D ha hD hWs I hh)
      simp [annularWeight,hw]

theorem fixed_profile_norm_bound (W : ℝ→ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0<a) :
    ∃ B : ℝ, 0<B ∧ ∀ σ∈Icc lo hi, ∀ y∈Icc a b, ‖W y‖*y^(-σ)≤B := by
  let K : Set (ℝ×ℝ) := Icc lo hi ×ˢ Icc a b
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun p : ℝ×ℝ => ‖W p.2‖*p.2^(-p.1)) K := by
    apply (hW.comp continuous_snd).norm.continuousOn.mul
    exact continuous_snd.continuousOn.rpow continuous_fst.neg.continuousOn
      (fun p hp => Or.inl (ne_of_gt (ha.trans_le hp.2.1)))
  obtain ⟨M,hM⟩ := hK.bddAbove_image hc
  refine ⟨|M|+1,by positivity,?_⟩
  intro σ hσ y hy
  exact (hM (Set.mem_image_of_mem _ (show (σ,y)∈K from ⟨hσ,hy⟩))).trans
    (by linarith [le_abs_self M])

theorem extraction_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character) (W : ℝ→ℂ) (a b D σ freq B : ℝ),
      0<a → 1≤D → Function.support W⊆Icc a b →
      2*(|Real.log a|+|Real.log b|)+1≤Real.log D → 0≤B →
      (∀ y∈Icc a b, ‖W y‖*y^(-σ)≤B) →
      ‖HeckePrimeDyadic.polynomial χ (PrimeLogProfile.profile W (1/Real.log D)) D σ freq -
        primePolynomial χ W b D σ freq‖≤
        C*(max 1 b)^((1/2 : ℝ)+ε)*D^ε*B := by
  obtain ⟨C,hC,herr⟩ := HeckePrimePowers.prime_extraction_error ε hε
  refine ⟨C,hC,?_⟩
  intro χ W a b D σ freq B ha hD hWs hlarge hB hWbound
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hX : 1≤max 1 b*D := hD.trans (le_mul_of_one_le_left hDp.le (le_max_left _ _))
  have hnorm (I : Ideal O) (hI : I∈annulusSet b D) : (I.absNorm : ℝ)≤max 1 b*D := by
    exact (Nat.cast_le.mpr (mem_idealsUpTo.mp hI).2).trans
      (Nat.floor_le (by positivity))
  have hw (I : Ideal O) (_hI : I∈annulusSet b D) : ‖annularWeight W D σ freq I‖≤B := by
    by_cases hz : W ((I.absNorm : ℝ)/D)=0
    · simpa [annularWeight,hz] using hB
    · have hs := hWs hz
      have hy : 0<(I.absNorm : ℝ)/D := ha.trans_le hs.1
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy]
      simpa only [Complex.neg_re,shift_re] using hWbound _ hs
  have hb := herr χ (annulusSet b D) (annularWeight W D σ freq) (max 1 b*D) B
    hX hB hnorm hw
  have hn : ‖(D : ℂ)^(-(1/2 : ℂ))‖=D^(-(1/2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hDp]
    norm_num
  rw [log_polynomial_eq_finite χ W a b D σ freq ha hDp hWs hlarge,
    primePolynomial,←mul_sub,norm_mul,hn]
  calc
    _ ≤ D^(-(1/2 : ℝ))*(C*(max 1 b*D)^(1/2+ε)*B) := by
      exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hDp.le _)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0≤max 1 b) hDp.le]
      have he : D^(-(1/2 : ℝ))*D^(1/2+ε)=D^ε := by
        rw [←Real.rpow_add hDp]
        congr 1
        ring
      calc
        _ = C*(max 1 b)^(1/2+ε)*(D^(-(1/2 : ℝ))*D^(1/2+ε))*B := by ring
        _ = _ := by rw [he]

end SevenEighths.HeckePrimeAnnular

end

end OAI

end Source749

/- Original source: OAI/NumberTheory/DirichletL/Hecke/DeletionDerivative.lean; sha256: fe8264f1e6793b10da38218403f23fa0c55aefacaf1bab35e84d3abcb250770e -/
section Source750
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDeletionDerivative
open HeckeFamily HeckeDeletionBounds

theorem factor_deriv {N : ℝ} (hN : 0 < N) (a s : ℂ) :
    deriv (EulerFactors.factor N a) s = a*(N : ℂ)^(-s)*Complex.log (N : ℂ) := by
  have h := (hasDerivAt_const s (1 : ℂ)).sub
    (((hasDerivAt_id s).neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))).const_mul a)
  have h' : HasDerivAt (EulerFactors.factor N a)
      (a*(N : ℂ)^(-s)*Complex.log (N : ℂ)) s := by
    convert h using 1
    · funext z
      rfl
    · dsimp
      ring
  exact h'.deriv

theorem factor_logDeriv_norm {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖logDeriv (EulerFactors.factor N a) s‖ ≤ localBound σ * Real.log N := by
  have hn0 : 0 < N := by linarith
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have ht := term_bound hσ hN ha hs
  have hδ : (2 : ℝ)^(-σ) ≤ 1 :=
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).le
  have hf := (factor_bounds hσ hN ha hs).2
  rw [logDeriv_apply, factor_deriv hn0, div_eq_mul_inv, norm_mul, norm_mul,
    ← Complex.ofReal_log hn0.le, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
  have hterm : ‖a*(N : ℂ)^(-s)‖ ≤ 1 := ht.trans hδ
  calc
    _ ≤ (1*Real.log N)*localBound σ := by gcongr
    _ = _ := by ring

theorem factors_logDeriv_norm (σ : ℝ) (hσ : 0 < σ) (M : Ideal O)
    (ψ : Character) {s : ℂ} (hs : σ ≤ s.re) :
    ‖logDeriv (HeckeFiniteDeletion.factors M ψ) s‖ ≤
      localBound σ * Real.log ((radical M).absNorm : ℝ) := by
  have hp0 (P : SmoothMobiusCorrection.PrimeIdeal) : 0 < (P.val.absNorm : ℝ) := by
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 0 < P.val.absNorm)
  have hp2 (P : SmoothMobiusCorrection.PrimeIdeal) : 2 ≤ (P.val.absNorm : ℝ) := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  have he : logDeriv (HeckeFiniteDeletion.factors M ψ) s =
      ∑ P ∈ SmoothMobiusCorrection.primeSet M,
        logDeriv (EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val)) s := by
    apply logDeriv_fun_prod
    · intro P _
      exact EulerFactors.factor_ne_zero (by linarith [hp2 P]) (idealCoeff_norm_le_one ψ P.val)
        (hσ.trans_le hs)
    · intro P _
      exact EulerFactors.differentiable_factor (hp0 P) _ s
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ P ∈ SmoothMobiusCorrection.primeSet M, localBound σ*Real.log (P.val.absNorm : ℝ) := by
      apply Finset.sum_le_sum
      intro P _
      exact factor_logDeriv_norm hσ (hp2 P) (idealCoeff_norm_le_one ψ P.val) hs
    _ = localBound σ * Real.log ((radical M).absNorm : ℝ) := by
      rw [← Finset.mul_sum, ← Real.log_prod (fun P _ => (hp0 P).ne')]
      simp only [radical, SmoothMobiusCorrection.primeProduct, map_prod, Nat.cast_prod]

end SevenEighths.HeckeDeletionDerivative

end

end OAI

end Source750

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeDyadicControl.lean; sha256: d8ce3846425186e749828db7303de5a37f385e44660a9d26974d5bbc8c84b4df -/
section Source751
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric Complex
namespace SevenEighths.HeckePrimeDyadicControl
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic HeckeFiniteDeletion
open HeckeDeletionBounds HeckeReciprocalGrowth

theorem logDeriv_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs : 0 < s.re)
    (hψs : LFunction ψ s ≠ 0) :
    logDeriv (LFunction χ) s = logDeriv (LFunction ψ) s +
      logDeriv (factors χ.modulus ψ) s := by
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have heq : LFunction χ =ᶠ[nhds s] (fun z => LFunction ψ z * factors χ.modulus ψ z) := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs] with z hz
    exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hz
  rw [(logDeriv_congr_nhds heq).self_of_nhds]
  exact logDeriv_fun_mul s hψs (factors_ne_zero _ _ hs)
    (LFunction_entire_nonprincipal ψ hψ s) (factors_differentiable _ _ s)

theorem original_disk_control (e : ℝ) (he : 0<e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤B ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖logDeriv (LFunction χ) z‖ ≤ B*Real.log (complexity χ t) +
          localBound (1/2)*Real.log ((radical χ.modulus).absNorm : ℝ) := by
  obtain ⟨Dp,B,_,hB,hprimitive⟩ := HeckeLogarithmicActual.disk_control e 1 he he' (by norm_num)
  refine ⟨B,hB,?_⟩
  intro χ hχ a t ha ha' hzero z hz
  obtain ⟨ψ,_,hp,hn,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have hregular : regular ψ = LFunction ψ := regular_eq_nonprincipal ψ hψ
  have hzeroψ : ∀ w ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular ψ w ≠ 0 := by
    intro w hw
    rw [hregular]
    have hwp : 0 < w.re := by
      have hr := LogarithmicControl.disk_re_gt hw
      linarith
    intro hh
    apply hzero w hw
    rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hwp, hh, zero_mul]
  have hbound := (hprimitive ψ hp a t ha ha' hzeroψ).2 z hz
  rw [hregular] at hbound
  have hz2 : z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    closedBall_subset_ball (by linarith) hz
  have hzre : (1/2 : ℝ) ≤ z.re := by
    have hr := LogarithmicControl.disk_re_gt hz2
    linarith
  have hzpos : 0 < z.re := by linarith
  have hdel := HeckeDeletionDerivative.factors_logDeriv_norm (1/2) (by norm_num)
    χ.modulus ψ hzre
  have hQ : complexity ψ t ≤ complexity χ t := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 < complexity ψ t := (Real.exp_pos 1).trans_le (complexity_ge_exp ψ t)
  rw [logDeriv_eq_of_mask χ ψ hmask hχ hzpos (by simpa [hregular] using hzeroψ z hz2)]
  apply (norm_add_le _ _).trans
  exact add_le_add (hbound.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hc0 hQ) hB)) hdel

theorem buffered_original_control (e : ℝ) (he : 0<e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e →
      ∀ (j : ι) (t : ℝ), |t| ≤ (3*i+2 : ℕ)*T →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖logDeriv (LFunction (χ j)) z‖ ≤ B*Real.log (complexity (χ j) t) +
          localBound (1/2)*Real.log ((radical (χ j).modulus).absNorm : ℝ) := by
  obtain ⟨B,hB,hbound⟩ := original_disk_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j t ht z hz
  exact hbound (χ j) (hχ j) a t (by linarith) ha'
    (fun w hw => HeckeDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
      hmax j t ht (ball_subset_closedBall hw)) z hz

theorem buffered_rectangle_control (e : ℝ)
    (he : 0<e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (z : ℂ), a+8*e≤z.re → z.re≤2 →
      |z.im|≤(3*i+2 : ℕ)*T →
      LFunction (χ j) z≠0 ∧
      ‖logDeriv (LFunction (χ j)) z‖≤
        B*Real.log (complexity (χ j) ((3*i+2 : ℕ)*T)) +
          localBound (1/2)*Real.log ((radical (χ j).modulus).absNorm : ℝ) := by
  obtain ⟨B,hB,hbound⟩ := buffered_original_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j z hzl hzr hzi
  have hz6 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-8*e) := by
    rw [mem_closedBall,dist_eq_norm]
    have heq : z-((2 : ℂ)+z.im*I)=((z.re-2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith : z.re-2≤0)]
    linarith
  have hz2 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-2*e) :=
    closedBall_subset_closedBall (by linarith) hz6
  refine ⟨HeckeDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
    hmax j z.im hzi hz2, ?_⟩
  apply (hbound χ hχ T a i hT ha ha' hmax j z.im hzi z hz6).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ hB
  apply Real.log_le_log ((Real.exp_pos 1).trans_le (complexity_ge_exp _ _))
  unfold complexity
  have hH : 0 ≤ (3*i+2 : ℕ)*T := (abs_nonneg z.im).trans hzi
  rw [abs_of_nonneg hH]
  gcongr

end SevenEighths.HeckePrimeDyadicControl

end

end OAI

end Source751

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeDyadicEuler.lean; sha256: 79ff926aaf930411e7e52b259fb004a2f4ac7736b3d8aabb417f6a9d3f4e96f1 -/
section Source752
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

def eulerBound (b : ℝ) : ℝ :=
  ∑' I : NonzeroIdeal, IdealMangoldt.value I.val * (norm I)^(-b)

theorem eulerBound_summable {b : ℝ} (hb : 1<b) :
    Summable (fun I : NonzeroIdeal => IdealMangoldt.value I.val * (norm I)^(-b)) := by
  have ha (I : Ideal O) : ‖IdealEuler.normWeight 0 I‖ ≤ 1 := by
    change ‖CubicEisenstein.fullIdealWeight 0 I‖ ≤ 1
    by_cases hI : I = 0
    · rw [CubicEisenstein.fullIdealWeight, ite_eq_left_iff.mpr (fun h => (h hI).elim), norm_zero]
      norm_num
    · rw [CubicEisenstein.fullIdealWeight, ite_eq_right_iff.mpr (fun h => (hI h).elim)]
      simp
  have hf := (IdealLogDerivative.mangoldt_weighted_summable_norm
    (IdealEuler.normWeight 0) ha (b : ℂ) (by simpa using hb)).comp_injective
      (Subtype.val_injective : Function.Injective (fun I : NonzeroIdeal => I.val))
  convert hf using 1
  ext I
  simp only [Function.comp_apply, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight,
    ite_eq_right_iff.mpr (fun h => (I.property h).elim), neg_zero, Complex.cpow_zero, one_mul]
  change IdealMangoldt.value I.val * (norm I)^(-b) =
    ‖(IdealMangoldt.value I.val : ℂ) * (norm I : ℂ)^(-(b : ℂ))‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp

theorem series_norm_le (χ : Character) {b : ℝ} (hb : 1<b)
    {s : ℂ} (hs : b≤s.re) : ‖series χ s‖ ≤ eulerBound b := by
  rw [series_eq_tsum χ (hb.trans_le hs)]
  have hbound (I : NonzeroIdeal) :
      ‖coefficient χ I.val * (norm I : ℂ)^(-s)‖ ≤
        IdealMangoldt.value I.val * (norm I)^(-b) := by
    rw [norm_mul]
    have hn : 1 ≤ norm I := by
      unfold HeckeDyadic.norm
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
    have hc : ‖coefficient χ I.val‖ ≤ IdealMangoldt.value I.val := by
      rw [coefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (IdealMangoldt.value_nonneg _)]
      exact mul_le_of_le_one_right (IdealMangoldt.value_nonneg _) (idealCoeff_norm_le_one χ _)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I), Complex.neg_re]
    exact mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hs))
      (Real.rpow_nonneg (norm_pos I).le _) (IdealMangoldt.value_nonneg _)

  have hf := (eulerBound_summable hb).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact (norm_tsum_le_tsum_norm hf).trans (hf.tsum_le_tsum hbound (eulerBound_summable hb))

end SevenEighths.HeckePrimeDyadic

end

end OAI

end Source752

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeDyadicContour.lean; sha256: 432a545c71db0c300ae45bde06cbaf4ec9399d8fc5c577c3779727ddf5938be9 -/
section Source753
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

def integrand (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D : ℂ)^(s+HeckeDyadic.shift σ freq-(1/2 : ℂ)) *
    series χ (s+HeckeDyadic.shift σ freq)

theorem series_differentiableAt_nonprincipal (χ : Character) (hχ : χ.residue≠1)
    {s : ℂ} (hz : LFunction χ s≠0) : DifferentiableAt ℂ (series χ) s := by
  have h := (LFunction_entire_nonprincipal χ hχ).analyticAt s
  exact (h.deriv.neg.div h hz).differentiableAt

theorem series_differentiableAt_right (χ : Character) {s : ℂ}
    (hs : 1<s.re) : DifferentiableAt ℂ (series χ) s := by
  have ha : AnalyticAt ℂ (LFunction χ) s := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 1)).2 ?_ s hs
    intro z hz
    exact (LFunction_differentiableAt χ
      (by intro h; norm_num [h] at hz) (Or.inl (by intro h; norm_num [h] at hz))).differentiableWithinAt
  exact (ha.deriv.neg.div ha (LFunction_ne_zero_of_one_lt_re χ hs)).differentiableAt

theorem integrand_differentiableAt (χ : Character) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) {s : ℂ}
    (hseries : DifferentiableAt ℂ (series χ) (s+HeckeDyadic.shift σ freq)) :
    DifferentiableAt ℂ (integrand χ W D σ freq) s := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · exact CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hWs hW s
    · exact ((differentiableAt_id.add_const (HeckeDyadic.shift σ freq)).sub_const (1/2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  · exact hseries.comp s (differentiableAt_id.add_const (HeckeDyadic.shift σ freq))

theorem integrand_norm (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0<D) (s : ℂ) :
    ‖integrand χ W D σ freq s‖ =
      ‖mellin W s‖*D^(s.re+σ-1/2)*‖series χ (s+HeckeDyadic.shift σ freq)‖ := by
  unfold integrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  simp

theorem integrand_vertical_integrable (χ : Character) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D c σ freq : ℝ) (hD : 0<D) (hc : 1<c+σ) :
    Integrable (fun t : ℝ => integrand χ W D σ freq ((c : ℂ)+t*I)) := by
  have hcont : Continuous (fun t : ℝ => integrand χ W D σ freq ((c : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (integrand_differentiableAt χ W a b ha hWs hW D σ freq hD
      (series_differentiableAt_right χ (by simpa using hc))).continuousAt.comp
    fun_prop
  have hm := (CompletedGauss.compactMellin_vertical_integrable W a b ha hWs hW c).norm
  apply (hm.mul_const (D^(c+σ-1/2)*eulerBound (c+σ))).mono'
    hcont.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [integrand_norm χ W D σ freq hD]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (series_norm_le χ hc (by simp))
  positivity

theorem finite_rectangle (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+HeckeDyadic.shift σ freq)≠0) :
    (∫ t : ℝ in -T..T, integrand χ W D σ freq ((r : ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+T*I))) := by
  have hhol : DifferentiableOn ℂ (integrand χ W D σ freq)
      (uIcc l r ×ℂ uIcc (-T) T) := by
    intro s hs
    exact (integrand_differentiableAt χ W a b ha hWs hW D σ freq hD
      (series_differentiableAt_nonprincipal χ hχ (hz s hs))).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (integrand χ W D σ freq) ((l : ℂ)+(-T)*I) ((r : ℂ)+T*I)
    (by simpa using hhol)
  have hr :
      (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+(-T)*I)) -
      (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, integrand χ W D σ freq ((r : ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)) = 0 := by
    simpa [smul_eq_mul] using h
  have hh := congrArg (fun z : ℂ => -I*z) hr
  ring_nf at hh ⊢
  simp only [I_sq] at hh
  linear_combination hh

theorem polynomial_finite_shift (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D) (hr : 1<r+σ) (hT : 0≤T)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+HeckeDyadic.shift σ freq)≠0) :
    polynomial χ W D σ freq = (1/(2*Real.pi) : ℂ)*
      ((∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+T*I))) +
      ∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ W D σ freq ((r : ℂ)+t*I)) := by
  rw [polynomial_mellin χ W a b ha hWs hW D r σ freq hD hr]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ W D σ freq ((r : ℂ)+t*I)) = _
  rw [← integral_add_compl measurableSet_Icc
    (integrand_vertical_integrable χ W a b ha hWs hW D r σ freq hD hr)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T≤T)]
  rw [finite_rectangle χ hχ W a b ha hWs hW D σ freq l r T hD hz]

end SevenEighths.HeckePrimeDyadic

end

end OAI

end Source753

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeDyadicEstimates.lean; sha256: 2f437de15a7e36581100f57a833e7f6c88524cce65384bee1845dd124a044c01 -/
section Source754
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem absolute_tail_bound (χ : Character) (W : ℝ → ℂ)
    (D r σ freq C T : ℝ) (n : ℕ) (hD : 0<D) (hr : 1<r+σ) (hC : 0≤C) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ W D σ freq ((r : ℂ)+t*I)‖ ≤
      (C*D^(r+σ-1/2)*eulerBound (r+σ))/(1+T)^n*Real.pi := by
  apply rapid_tail_bound _ _ T n
  · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hD.le _))
      (tsum_nonneg (fun I => mul_nonneg (IdealMangoldt.value_nonneg _) (Real.rpow_nonneg (norm_pos I).le _)))
  · exact hT
  · intro t
    rw [integrand_norm χ W D σ freq hD]
    have hb := series_norm_le χ hr (s := (r : ℂ)+t*I+shift σ freq) (by simp)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
      sub_self, add_zero]
    calc
      _ = ((1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖)*D^(r+σ-1/2)*
        ‖series χ ((r : ℂ)+t*I+shift σ freq)‖ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (hm t) (Real.rpow_nonneg hD.le _))
        hb (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hD.le _))

theorem central_segment_bound (χ : Character) (W : ℝ → ℂ)
    (D l σ freq C K T : ℝ) (hD : 0<D) (hC : 0≤C) (hK : 0≤K) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C)
    (hs : ∀ t ∈ Icc (-T) T, ‖series χ ((l : ℂ)+t*I+shift σ freq)‖≤K) :
    ‖∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)‖ ≤
      C*D^(l+σ-1/2)*K*Real.pi := by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T)]
  have hint := integrable_inv_one_add_sq.const_mul (C*D^(l+σ-1/2)*K)
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [integrand_norm χ W D σ freq hD]
      have hb := CubicReflectionKernel.weighted_two_to_cauchy (norm_nonneg _) t (hm t)
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
        sub_self, add_zero]
      calc
        _ ≤ (C/(1+t^2))*D^(l+σ-1/2)*K :=
          mul_le_mul (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hD.le _))
            (hs t ⟨ht.1.le,ht.2⟩) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ ≤ ∫ t : ℝ, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ :=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem horizontal_join_bound (χ : Character) (W : ℝ → ℂ)
    (D σ freq l r y C K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hC : 0≤C) (_hK : 0≤K)
    (hm : ∀ x ∈ Icc l r, (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤C)
    (hs : ∀ x ∈ Icc l r, ‖series χ ((x : ℂ)+y*I+shift σ freq)‖≤K) :
    ‖∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+y*I)‖ ≤
      (C*D^(r+σ-1/2)*K/(1+|y|)^n)*|r-l| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hx' : x ∈ Icc l r := by simpa [uIcc_of_le hlr] using uIoc_subset_uIcc hx
  have hb : ‖mellin W ((x : ℂ)+y*I)‖≤C/(1+|y|)^n := by
    apply (le_div_iff₀ (by positivity : 0<(1+|y|)^n)).mpr
    simpa [mul_comm] using hm x hx'
  have hpow : D^(x+σ-1/2)≤D^(r+σ-1/2) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith [hx'.2])
  rw [integrand_norm χ W D σ freq (by linarith)]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  calc
    _ ≤ (C/(1+|y|)^n)*D^(r+σ-1/2)*K :=
      mul_le_mul (mul_le_mul hb hpow (by positivity) (by positivity))
        (hs x hx') (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem polynomial_bound_of_rectangle (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hr : 1<r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ (s+shift σ freq)‖≤K) :
    ‖polynomial χ W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*K*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*eulerBound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0<D := by linarith
  have hmem (x t : ℝ) (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
      ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
    change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using And.intro hx ht
  have hcentral := central_segment_bound χ W D l σ freq C₂ K T hDp hC₂ hK hT
    hm₂ (fun t ht => hs _ (hmem l t ⟨le_rfl,hlr⟩ ht))
  have hm (x : ℝ) (hx : x∈Icc l r) (t : ℝ) :
      (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤Cn := by
    apply le_trans _ (hmn x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · omega
  have hbottom := horizontal_join_bound χ W D σ freq l r (-T) Cn K n hD hlr hCn hK
    (fun x hx => hm x hx (-T)) (fun x hx => hs _ (hmem x (-T) hx ⟨le_rfl,by linarith⟩))
  have htop := horizontal_join_bound χ W D σ freq l r T Cn K n hD hlr hCn hK
    (fun x hx => hm x hx T) (fun x hx => hs _ (hmem x T hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := absolute_tail_bound χ W D r σ freq Cn T n hDp hr hCn hT
    (hmn r ⟨hlr,le_rfl⟩)
  rw [polynomial_finite_shift χ hχ W a b ha hWs hW D σ freq l r T hDp hr hT hz,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

end SevenEighths.HeckePrimeDyadic

end

end OAI

end Source754

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeDyadicBuffered.lean; sha256: be851888a811a898dfbe764dc10c1ea2c1bf12dcee516a976a379334f597c5bd -/
section Source755
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Metric MeasureTheory Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeLogarithmic HeckeDeletionBounds

def binCost (B : ℝ) (χ : Character) (H : ℝ) : ℝ :=
  B*Real.log (complexity χ H) + localBound (1/2)*Real.log ((radical χ.modulus).absNorm : ℝ)

theorem binCost_nonneg {B : ℝ} (hB : 0≤B) (χ : Character) (H : ℝ) : 0≤binCost B χ H := by
  have hc : 1≤complexity χ H :=
    (Real.one_le_exp (by norm_num : (0 : ℝ)≤1)).trans (complexity_ge_exp χ H)
  have hr : (1 : ℝ)≤(radical χ.modulus).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero χ.modulus))
  exact add_nonneg (mul_nonneg hB (Real.log_nonneg hc))
    (mul_nonneg (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le (Real.log_nonneg hr))

theorem polynomial_bound_in_bin (e : ℝ) (he : 0<e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ→ℂ) (α β : ℝ), 0<α → Function.support W⊆Icc α β →
      ContDiff ℝ ∞ W → ∀ D σ freq L C₂ Cn : ℝ, ∀ n : ℕ,
      1≤D → 0≤L → 0≤C₂ → 0≤Cn → |freq|+L≤(3*i+2 : ℕ)*T →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+8*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x∈Icc (a+8*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) W D σ freq‖ ≤ (1/(2*Real.pi))*
        (C₂*D^(a+8*e-1/2)*binCost B (χ j) ((3*i+2 : ℕ)*T)*Real.pi +
          2*(Cn*D^(3/2 : ℝ)*binCost B (χ j) ((3*i+2 : ℕ)*T)/(1+L)^n)*|2-a-8*e| +
          (Cn*D^(3/2 : ℝ)*eulerBound 2)/(1+L)^n*Real.pi) := by
  obtain ⟨B,hB,hbound⟩ := HeckePrimeDyadicControl.buffered_rectangle_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W α β hα hWs hW D σ freq L C₂ Cn n
    hD hL hC₂ hCn hfreq hm₂ hmn
  have hlr : a+8*e-σ≤2-σ := by linarith
  have hmem (s : ℂ) (hs : s ∈ (uIcc (a+8*e-σ) (2-σ) ×ℂ uIcc (-L) L)) :
      a+8*e≤(s+HeckeDyadic.shift σ freq).re ∧ (s+HeckeDyadic.shift σ freq).re≤2 ∧
        |(s+HeckeDyadic.shift σ freq).im|≤(3*i+2 : ℕ)*T := by
    convert HeckeDyadic.translated_rectangle_mem (a := a+2*e) (e := e)
      (by linarith) (by linarith) hlr hL hfreq hs using 1 ; ring_nf
  have hs (s : ℂ) (hs : s ∈ (uIcc (a+8*e-σ) (2-σ) ×ℂ uIcc (-L) L)) :=
    hbound χ hχ T a i hT ha ha' hmax j (s+HeckeDyadic.shift σ freq)
      (hmem s hs).1 (hmem s hs).2.1 (hmem s hs).2.2
  have hh := polynomial_bound_of_rectangle (χ j) (hχ j) W α β hα hWs hW
    D σ freq (a+8*e-σ) (2-σ) L C₂ Cn (binCost B (χ j) ((3*i+2 : ℕ)*T)) n
    hD hlr (by linarith) hL hC₂ hCn (binCost_nonneg hB _ _)
    hm₂ hmn (fun s h => (hs s h).1) (fun s h => by
      simpa only [series, neg_div, norm_neg, logDeriv_apply, binCost] using (hs s h).2)
  convert hh using 1 ; congr 1 ; ring_nf

end SevenEighths.HeckePrimeDyadic

end

end OAI

end Source755

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeDyadicScale.lean; sha256: cfb00ec2c4a51977ffc5fd4abe1e316487530002b9b57c18cd1f385822afd8b0 -/
section Source756
namespace OAI

noncomputable section
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeDeletionBounds HeckeLogarithmic

theorem binCost_le_log (χ : Character) (B U H η : ℝ)
    (hB : 0≤B) (hU : 2≤U) (hQ : (χ.modulus.absNorm : ℝ)≤U)
    (hheight : (3+|H|)^2≤U^η) :
    binCost B χ H ≤ (B*(2+η)+localBound (1/2))*Real.log U := by
  have hUp : 0<U := by linarith
  have hcp : 0<complexity χ H := (Real.exp_pos 1).trans_le (complexity_ge_exp χ H)
  have hcomplex : complexity χ H ≤ 2*U^(1+η) := by
    unfold complexity
    calc
      2*(χ.modulus.absNorm : ℝ)*(3+|H|)^2 ≤ 2*U*U^η := by gcongr
      _ = _ := by rw [Real.rpow_add hUp, Real.rpow_one]; ring
  have hlog : Real.log (complexity χ H) ≤ (2+η)*Real.log U := by
    apply (Real.log_le_log hcp hcomplex).trans
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hUp _).ne', Real.log_rpow hUp]
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ)<2) hU
    nlinarith
  have hrad : 0<((radical χ.modulus).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero χ.modulus))
  have hrlog := Real.log_le_log hrad ((radical_norm_le_modulus χ).trans hQ)
  unfold binCost
  calc
    _ ≤ B*((2+η)*Real.log U)+localBound (1/2)*Real.log U :=
      add_le_add (mul_le_mul_of_nonneg_left hlog hB)
        (mul_le_mul_of_nonneg_left hrlog (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le)
    _ = _ := by ring

theorem binCost_le_power (χ : Character) (B U H η ε : ℝ)
    (hB : 0≤B) (hU : 2≤U) (hQ : (χ.modulus.absNorm : ℝ)≤U)
    (hη : 0≤η) (hε : 0<ε) (hheight : (3+|H|)^2≤U^η) :
    binCost B χ H ≤ ((B*(2+η)+localBound (1/2))/ε)*U^ε := by
  apply (binCost_le_log χ B U H η hB hU hQ hheight).trans
  have hc : 0≤B*(2+η)+localBound (1/2) := by
    exact add_nonneg (mul_nonneg hB (by linarith))
      (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_rpow_div (by linarith : 0≤U) hε) hc
  convert hh using 1 ; ring

end SevenEighths.HeckePrimeDyadic

end

end OAI

end Source756

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeDyadicScaled.lean; sha256: 90b849b5756d6c4a681ba7c9481199233079021ae93c9057854b8312d24f3f87 -/
section Source757
namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeDeletionBounds

theorem scaled_direct_bound (e κ η : ℝ) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R σ freq V C₂ Cn : ℝ) (n : ℕ),
      2≤U → (χ j).modulus.absNorm≤U → 0≤r → r≤R → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^2≤U^η → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+8*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (a+8*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2+8*e)*r+κ)+C*Cn*U^(2*R+κ)/(1+V)^n := by
  obtain ⟨B,hB,hbound⟩ := polynomial_bound_in_bin e he he'
  let Cb := (B*(2+η)+localBound (1/2))/κ
  have hCb : 0<Cb := div_pos
    (add_pos_of_nonneg_of_pos (mul_nonneg hB (by linarith))
      (localBound_pos (by norm_num : (0 : ℝ)<1/2))) hκ
  let E := eulerBound 2
  have hE : 0≤E := tsum_nonneg (fun I => mul_nonneg (IdealMangoldt.value_nonneg _) (Real.rpow_nonneg (norm_pos I).le _))
  let C := 1+Cb*Real.pi+4*Cb+E*Real.pi
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W A B' hA hWs hW
    U r R σ freq V C₂ Cn n hU2 hQ hr hrR hV hfreq hheight hC₂ hCn hm₂ hmn
  let H : ℝ := (3*i+2 : ℕ)*T
  have hH : 0≤H := by dsimp [H]; positivity
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one (χ j)).trans hQ
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤U^r := Real.one_le_rpow hU hr
  have hb := hbound χ hχ T a i hT ha ha' hmax j W A B' hA hWs hW
    (U^r) σ freq V C₂ Cn n hD hV hC₂ hCn hfreq hm₂ hmn
  have hcost : binCost B (χ j) H ≤ Cb*U^κ :=
    binCost_le_power (χ j) B U H η κ hB hU2 hQ hη hκ (by rw [abs_of_nonneg hH]; exact hheight)
  have hcentral : (U^r)^(a+8*e-1/2)*binCost B (χ j) H ≤
      Cb*U^((a-1/2+8*e)*r+κ) := by
    calc
      _ ≤ (U^r)^(a+8*e-1/2)*(Cb*U^κ) :=
        mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg (Real.rpow_nonneg hUp.le _) _)
      _ = _ := by rw [←Real.rpow_mul hUp.le, mul_left_comm, ←Real.rpow_add hUp]; congr 2; ring
  have hexternal : (U^r)^(3/2 : ℝ)*binCost B (χ j) H ≤ Cb*U^(2*R+κ) := by
    calc
      _ ≤ (U^r)^(3/2 : ℝ)*(Cb*U^κ) :=
        mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg (Real.rpow_nonneg hUp.le _) _)
      _ = Cb*U^(r*(3/2)+κ) := by rw [←Real.rpow_mul hUp.le, mul_left_comm, ←Real.rpow_add hUp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)) hCb.le
  have hpow : (U^r)^(3/2 : ℝ)≤U^(2*R+κ) := by
    rw [←Real.rpow_mul hUp.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hwidth : |2-a-8*e|≤2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hc : C₂*(U^r)^(a+8*e-1/2)*binCost B (χ j) H*Real.pi≤
      (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ) := by
    calc
      _ = (C₂*Real.pi)*((U^r)^(a+8*e-1/2)*binCost B (χ j) H) := by ring
      _ ≤ (C₂*Real.pi)*(Cb*U^((a-1/2+8*e)*r+κ)) :=
        mul_le_mul_of_nonneg_left hcentral (by positivity)
      _ = _ := by ring
  have hj : 2*(Cn*(U^r)^(3/2 : ℝ)*binCost B (χ j) H/(1+V)^n)*|2-a-8*e|≤
      (4*Cb)*Cn*U^(2*R+κ)/(1+V)^n := by
    calc
      _ = 2*Cn*((U^r)^(3/2 : ℝ)*binCost B (χ j) H)/(1+V)^n*|2-a-8*e| := by ring
      _ ≤ 2*Cn*(Cb*U^(2*R+κ))/(1+V)^n*2 := by gcongr
      _ = _ := by ring
  have ht : (Cn*(U^r)^(3/2 : ℝ)*E)/(1+V)^n*Real.pi≤
      (E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by
    calc
      _ ≤ (Cn*U^(2*R+κ)*E)/(1+V)^n*Real.pi := by gcongr
      _ = _ := by ring
  have hfac : 1/(2*Real.pi)≤(1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hcomp : 0≤binCost B (χ j) H := binCost_nonneg hB _ _
  apply (hb.trans (mul_le_of_le_one_left (by positivity) hfac)).trans
  change _ ≤ _ at hc hj ht
  have hcC : Cb*Real.pi≤C := by dsimp [C]; nlinarith only [hCb, mul_nonneg hE Real.pi_pos.le]
  have heC : 4*Cb+E*Real.pi≤C := by dsimp [C]; nlinarith only [mul_nonneg hCb.le Real.pi_pos.le]
  calc
    _ ≤ (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ)+
        (4*Cb)*Cn*U^(2*R+κ)/(1+V)^n+(E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by
      exact add_le_add (add_le_add hc hj) ht
    _ = (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ)+
        (4*Cb+E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by ring
    _ ≤ _ := by gcongr

end SevenEighths.HeckePrimeDyadic

end

end OAI

end Source757

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeDyadicSource.lean; sha256: f049474faa33b014c815f296c3c08574fba15b6237b412ce5ece05d05b6db1f4 -/
section Source758
namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem source_log_profile_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq L : ℝ,
      0≤r → r≤R → σmin≤σ → σ≤σmax → L∈Icc (0 : ℝ) 1 →
      ∀ k : ι, (χ k).modulus.absNorm≤Z^d →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖polynomial (χ k) (PrimeLogProfile.profile W L) ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨Cd,hCd,hdirect⟩ := scaled_direct_bound e κ η he he' hκ hη
  obtain ⟨n,htail⟩ := uniform_external_tail_order τ dmax (2*R+κ) 0
    hτ hdmax (by positivity) (by norm_num)
  obtain ⟨C₂,hC₂,hm₂⟩ := PrimeLogProfile.uniform_mellin_decay W A B hA hWs hW
    (-σmax) (2-σmin) 2
  obtain ⟨Cn,hCn,hmn⟩ := PrimeLogProfile.uniform_mellin_decay W A B hA hWs hW
    (-σmax) (2-σmin) (n+2)
  refine ⟨Cd*C₂+Cd*Cn*(2 : ℝ)^n,by positivity,?_⟩
  intro Z d hZ hd hd' hU2 hT ι _ χ hχ a i ha ha' hmax r σ freq L
    hr hrR hσmin hσmax hL k hQ hfreq hheight
  let U := Z^d
  have hU : 1≤U := Real.one_le_rpow hZ hd
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hs : Icc (a+8*e-σ) (2-σ)⊆Icc (-σmax) (2-σmin) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hleft : a+8*e-σ∈Icc (-σmax) (2-σmin) := by
    constructor <;> linarith
  have hb := hdirect χ hχ (Z^τ) a i hT ha ha' hmax k
    (PrimeLogProfile.profile W L) A B hA
    ((PrimeLogProfile.profile_support W L).trans hWs)
    (PrimeLogProfile.profile_smooth W A B hA hWs hW L)
    U r R σ freq (Z^τ/2) C₂ Cn n hU2 hQ hr hrR (by positivity)
    hfreq hheight hC₂.le hCn.le (hm₂ L hL _ hleft) (fun x hx => hmn L hL x (hs hx))
  have htail' := htail Z d 0 hZ hd hd' (by norm_num)
  simp only [Real.rpow_zero,mul_one] at htail'
  have hexp : (a-1/2+8*e)*r+κ≤(a-1/2)*r+ε := by
    nlinarith [mul_le_mul_of_nonneg_left hrR (by positivity : 0≤8*e)]
  have hp : 0≤(a-1/2)*r+ε := by
    have : 0≤8*e*R := by positivity
    nlinarith [mul_nonneg (show 0≤a-1/2 by linarith) hr]
  calc
    _ ≤ Cd*C₂*U^((a-1/2)*r+ε)+Cd*Cn*(2 : ℝ)^n := by
      apply hb.trans
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hexp) (by positivity)
      · calc
          _ = (Cd*Cn)*(U^(2*R+κ)/(1+Z^τ/2)^n) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left htail' (by positivity)
    _ ≤ (Cd*C₂+Cd*Cn*(2 : ℝ)^n)*U^((a-1/2)*r+ε) := by
      rw [add_mul]
      apply add_le_add (le_refl _)
      exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hU hp)

end SevenEighths.HeckePrimeDyadic

end

end OAI

end Source758

/- Original source: OAI/NumberTheory/DirichletL/Hecke/PrimeBin.lean; sha256: c0d0f071e7999c249d61416bf4822a6a9497de324cd5af821af8021ab253b2d2 -/
section Source759
namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeAnnular
open HeckeFamily HeckeDyadic

theorem prime_bin_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, 0≤r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      ∀ k : ι, (χ k).modulus.absNorm≤Z^d →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖primePolynomial (χ k) W B ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨Cp,hCp,hprime⟩ := HeckePrimeDyadic.source_log_profile_bound W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ he he' hκ hη hbudget
  let ξ := ε/(R+1)
  have hξ : 0<ξ := div_pos hε (by positivity)
  obtain ⟨Ce,hCe,herror⟩ := extraction_bound ξ hξ
  obtain ⟨Bf,hBf,hprofile⟩ := fixed_profile_norm_bound W hW.continuous A B σmin σmax hA
  let E := Ce*(max 1 B)^(1/2+ξ)*Bf
  have hE : 0<E := by dsimp [E]; positivity
  refine ⟨Cp+E,by positivity,?_⟩
  intro Z d hZ hd hd' hU2 hT ι _ χ hχ a i ha ha' hmax r σ freq hr hrR
    hσmin hσmax hlarge k hQ hfreq hheight
  let U := Z^d
  let D := U^r
  have hU : 1≤U := Real.one_le_rpow hZ hd
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤D := Real.one_le_rpow hU hr
  have hlog : 1≤Real.log D := by
    linarith [abs_nonneg (Real.log A),abs_nonneg (Real.log B)]
  have hL : 1/Real.log D∈Icc (0 : ℝ) 1 :=
    ⟨by positivity,(div_le_one (by linarith)).mpr hlog⟩
  have hp := hprime Z d hZ hd hd' hU2 hT χ hχ a i ha ha' hmax
    r σ freq (1/Real.log D) hr hrR hσmin hσmax hL k hQ hfreq hheight
  have he := herror (χ k) W A B D σ freq Bf hA hD hWs hlarge hBf.le
    (hprofile σ ⟨hσmin,hσmax⟩)
  have hpow : D^ξ≤U^((a-1/2)*r+ε) := by
    dsimp [D]
    rw [←Real.rpow_mul hUp.le]
    apply Real.rpow_le_rpow_of_exponent_le hU
    have hxi : ξ*(R+1)=ε := by dsimp [ξ]; field_simp
    nlinarith [mul_nonneg (show 0≤a-1/2 by linarith) hr,
      mul_le_mul_of_nonneg_right hrR hξ.le]
  have he' : ‖HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
      primePolynomial (χ k) W B D σ freq‖≤E*U^((a-1/2)*r+ε) := by
    apply he.trans
    calc
      _ = E*D^ξ := by dsimp [E]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hE.le
  calc
    _ ≤ ‖HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq‖+
        ‖HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
          primePolynomial (χ k) W B D σ freq‖ := by
      have hid : primePolynomial (χ k) W B D σ freq =
          HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
          (HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
            primePolynomial (χ k) W B D σ freq) := by ring
      conv_lhs => rw [hid]
      exact norm_sub_le _ _
    _ ≤ Cp*U^((a-1/2)*r+ε)+E*U^((a-1/2)*r+ε) := add_le_add hp he'
    _ = _ := by ring

end SevenEighths.HeckePrimeAnnular

end

end OAI

end Source759
