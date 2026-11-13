import OpenAIGrouped.Unit025
import OpenAIGrouped.Unit013
import OpenAIGrouped.Unit009
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.Analysis.Normed.Group.Tannery
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit015
import OpenAIGrouped.Unit008
import OpenAIGrouped.Unit017
import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit021
import OpenAIGrouped.Unit012
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighSeries.lean; sha256: eac7cc6bd848ea9b64e6f3b3022ca408f3dee5bf213f7df3ef12fc3f07fe022c -/
section Source1040
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def bareIdealHighCoefficient (η : HeckeFamily.Character) (u : O) (I J K L : Id) : ℂ :=
  if h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L then
    bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I h.2.1)
      (primaryGenerator I * primaryGenerator J^3) (primaryGenerator K)
      (mul_ne_zero (supported_primaryGenerator_ne_zero I h.2.1)
        (pow_ne_zero _ (supported_primaryGenerator_ne_zero J h.2.2.1)))
      (u*primaryGenerator L^6)
  else 0

theorem bareIdealHighCoefficient_norm_le (η : HeckeFamily.Character) (u : O) (I J K L : Id) :
    ‖bareIdealHighCoefficient η u I J K L‖ ≤ (K.absNorm:ℝ)*(I.absNorm:ℝ)*(J.absNorm:ℝ)^3 := by
  unfold bareIdealHighCoefficient
  split_ifs with h
  · have hi := (supported_span_primaryGenerator_iff I).mpr h.2.1
    have hj := (supported_span_primaryGenerator_iff J).mpr h.2.2.1
    have hk := (supported_span_primaryGenerator_iff K).mpr h.2.2.2.1
    have hb := bareSourceCoefficient_norm_le η I ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      (primaryGenerator I*primaryGenerator J^3) (primaryGenerator K)
      (supported_completed _ _ hi hj) hk (u*primaryGenerator L^6)
    rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).1,
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).1,
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).1,
      map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] at hb
    convert hb using 1 ; ring
  · simp only [norm_zero]
    positivity

def bareIdealHighSummand (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (I J K L : Id) : ℂ :=
  bareIdealHighCoefficient η u I J K L * fullIdealWeight (x+1/2) I *
    fullIdealWeight (1+3*x) J * fullIdealWeight w K * fullIdealWeight (6*z) L

lemma fullIdealWeight_nat_scale (s : ℂ) (I : Id) (hI : I≠0) (k : ℕ) :
    (I.absNorm:ℝ)^k * ‖fullIdealWeight s I‖ = ‖fullIdealWeight (s-k) I‖ := by
  have hN : 0<(I.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [fullIdealWeight,ite_eq_right hI]
  simp only [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN,Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp only [Complex.neg_re,Complex.sub_re,Complex.ofReal_re]
  rw [← Real.rpow_natCast,← Real.rpow_add hN]
  congr 1
  ring

theorem bareIdealHighSummand_norm_le (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (I J K L : Id) :
    ‖bareIdealHighSummand η u x w z I J K L‖ ≤
      ‖fullIdealWeight (x-1/2) I‖ * ‖fullIdealWeight (3*x-2) J‖ *
      ‖fullIdealWeight (w-1) K‖ * ‖fullIdealWeight (6*z) L‖ := by
  by_cases h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L
  · have hb := bareIdealHighCoefficient_norm_le η u I J K L
    calc
      _ ≤ ((K.absNorm:ℝ)*(I.absNorm:ℝ)*(J.absNorm:ℝ)^3) *
          ‖fullIdealWeight (x+1/2) I‖ * ‖fullIdealWeight (1+3*x) J‖ *
          ‖fullIdealWeight w K‖ * ‖fullIdealWeight (6*z) L‖ := by
        simp only [bareIdealHighSummand,norm_mul]
        gcongr
      _ = ((I.absNorm:ℝ)^1*‖fullIdealWeight (x+1/2) I‖) *
          ((J.absNorm:ℝ)^3*‖fullIdealWeight (1+3*x) J‖) *
          ((K.absNorm:ℝ)^1*‖fullIdealWeight w K‖) * ‖fullIdealWeight (6*z) L‖ := by ring
      _ = _ := by
        rw [fullIdealWeight_nat_scale _ I h.2.1.1 1,
          fullIdealWeight_nat_scale _ J h.2.2.1.1 3,
          fullIdealWeight_nat_scale _ K h.2.2.2.1.1 1]
        norm_num only [Nat.cast_one, Nat.cast_ofNat]
        rw [show x+(1/2:ℂ)-1=x-1/2 by ring,show (1:ℂ)+3*x-3=3*x-2 by ring]
  · simp only [bareIdealHighSummand,bareIdealHighCoefficient,dite_eq_right h,zero_mul,norm_zero]
    positivity

theorem bareIdealHighSummand_summable (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun p : (Id×Id)×(Id×Id) =>
      bareIdealHighSummand η u x w z p.1.1 p.1.2 p.2.1 p.2.2) := by
  have h1 := fullIdealWeight_summable_norm (x-1/2) (by
    simp only [Complex.sub_re,Complex.div_re,Complex.one_re,Complex.one_im,
      show (2:ℂ).re=2 by rfl,show (2:ℂ).im=0 by rfl]
    norm_num
    linarith)
  have h2 := fullIdealWeight_summable_norm (3*x-2) (by
    norm_num [Complex.sub_re,Complex.mul_re]
    linarith)
  have h3 := fullIdealWeight_summable_norm (w-1) (by
    simp only [Complex.sub_re,Complex.one_re]
    linarith)
  have h4 := fullIdealWeight_summable_norm (6*z) (by
    norm_num [Complex.mul_re]
    linarith)
  have h12 := h1.mul_of_nonneg h2 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have h34 := h3.mul_of_nonneg h4 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have hall := h12.mul_of_nonneg h34
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hall
  intro p
  simpa only [mul_assoc] using bareIdealHighSummand_norm_le η u x w z p.1.1 p.1.2 p.2.1 p.2.2

def bareIdealHighSeries (η : HeckeFamily.Character) (u : O) (x w z : ℂ) : ℂ :=
  ∑' p : (Id×Id)×(Id×Id), bareIdealHighSummand η u x w z p.1.1 p.1.2 p.2.1 p.2.2

end SevenEighths.ProbePhysical
end

end OAI

end Source1040

/- Original source: OAI/NumberTheory/DirichletL/Detector/IdealMultiplicative.lean; sha256: 177bb0614d6fb87cc0cafaf0bf49c7521dfb334306636e7c4f292e57b16f908c -/
section Source1041
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def highSupport (I J K L : Id) : Prop :=
  Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L

lemma highSupport_mul (I J K L I' J' K' L' : Id) (hcop : IsCoprime I I') :
    highSupport (I*I') (J*J') (K*K') (L*L') ↔
      highSupport I J K L ∧ highSupport I' J' K' L' := by
  simp only [highSupport, squarefree_mul_iff, supported_mul_iff]
  have hc := hcop.isRelPrime
  tauto

lemma span_primaryGenerator_of_supported (I : Id) (hI : Supported I) :
    Ideal.span {primaryGenerator I}=I :=
  (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1

lemma primaryGenerator_coprime (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hcop : IsCoprime I J) : IsCoprime (primaryGenerator I) (primaryGenerator J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rwa [span_primaryGenerator_of_supported I hI,span_primaryGenerator_of_supported J hJ]

lemma completed_block_dvd_cube (I J K L : Id) : I*J^3*K ∣ (I*J*K*L)^3 := by
  refine ⟨I^2*K^2*L^3,?_⟩
  ring

lemma first_block_dvd (I J K L : Id) : I ∣ I*J*K*L := by
  refine ⟨J*K*L,?_⟩
  ring

lemma last_block_dvd (I J K L : Id) : L ∣ I*J*K*L := by
  refine ⟨I*J*K,?_⟩
  ring

theorem bareIdealHighCoefficient_mul (η : HeckeFamily.Character)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighCoefficient η 1 (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighCoefficient η 1 I J K L * bareIdealHighCoefficient η 1 I' J' K' L' := by
  have hII := hcop.mono (first_block_dvd I J K L) (first_block_dvd I' J' K' L')
  by_cases h : highSupport I J K L ∧ highSupport I' J' K' L'
  · have hprod := (highSupport_mul I J K L I' J' K' L' hII).mpr h
    rcases h with ⟨h,h'⟩
    have hsA := (supported_mul_iff (I*J^3) K).mpr
      ⟨(supported_mul_iff I (J^3)).mpr ⟨h.2.1,supported_pow h.2.2.1 3⟩,h.2.2.2.1⟩
    have hsB := (supported_mul_iff (I'*J'^3) K').mpr
      ⟨(supported_mul_iff I' (J'^3)).mpr ⟨h'.2.1,supported_pow h'.2.2.1 3⟩,h'.2.2.2.1⟩
    have hc3 : IsCoprime ((I*J*K*L)^3) ((I'*J'*K'*L')^3) := hcop.pow_left.pow_right
    have hab := primaryGenerator_coprime _ _ hsA hsB
      (hc3.mono (completed_block_dvd_cube I J K L) (completed_block_dvd_cube I' J' K' L'))
    have hba := primaryGenerator_coprime _ _ h'.2.2.2.2 hsA
      (hcop.symm.pow_right.mono (last_block_dvd I' J' K' L') (completed_block_dvd_cube I J K L))
    have hab' := primaryGenerator_coprime _ _ h.2.2.2.2 hsB
      (hcop.pow_right.mono (last_block_dvd I J K L) (completed_block_dvd_cube I' J' K' L'))
    simp only [primaryGenerator_mul,primaryGenerator_pow] at hab hba hab'
    have he := bareSourceCoefficient_product_frequency η I I'
      ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      ⟨h'.1,supported_primaryGenerator_ne_zero I' h'.2.1⟩
      ⟨hprod.1,supported_primaryGenerator_ne_zero (I*I') hprod.2.1⟩ hII
      (primaryGenerator J) (primaryGenerator J') (primaryGenerator K) (primaryGenerator K')
      ((supported_span_primaryGenerator_iff I).mpr h.2.1)
      ((supported_span_primaryGenerator_iff I').mpr h'.2.1)
      ((supported_span_primaryGenerator_iff J).mpr h.2.2.1)
      ((supported_span_primaryGenerator_iff J').mpr h'.2.2.1)
      ((supported_span_primaryGenerator_iff K).mpr h.2.2.2.1)
      ((supported_span_primaryGenerator_iff K').mpr h'.2.2.2.1)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).2
      (primaryGenerator_spec I' (supported_primaryGenerator_ne_zero I' h'.2.1)).2
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).2
      (primaryGenerator_spec J' (supported_primaryGenerator_ne_zero J' h'.2.2.1)).2
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).2
      (primaryGenerator_spec K' (supported_primaryGenerator_ne_zero K' h'.2.2.2.1)).2
      hab (primaryGenerator L) (primaryGenerator L') hba hab'
    unfold highSupport at hprod h h'
    unfold bareIdealHighCoefficient
    rw [dite_eq_left hprod,dite_eq_left h,dite_eq_left h']
    simp only [primaryGenerator_mul,one_mul]
    dsimp only at he
    convert he using 1 ; ring_nf
  · have hprod := mt (highSupport_mul I J K L I' J' K' L' hII).mp h
    unfold highSupport at hprod
    unfold bareIdealHighCoefficient
    rw [dite_eq_right hprod]
    by_cases hi : highSupport I J K L
    · have hj : ¬highSupport I' J' K' L' := fun hj=>h ⟨hi,hj⟩
      unfold highSupport at hj
      rw [dite_eq_right hj,mul_zero]
    · unfold highSupport at hi
      rw [dite_eq_right hi,zero_mul]

lemma fullIdealWeight_mul (s : ℂ) (I J : Id) :
    fullIdealWeight s (I*J)=fullIdealWeight s I*fullIdealWeight s J :=
  (IdealEuler.normWeight s).map_mul I J

theorem bareIdealHighSummand_mul (η : HeckeFamily.Character) (x w z : ℂ)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighSummand η 1 x w z (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighSummand η 1 x w z I J K L * bareIdealHighSummand η 1 x w z I' J' K' L' := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_mul η I J K L I' J' K' L' hcop,
    fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1041

/- Original source: OAI/NumberTheory/DirichletL/Detector/IdealFactorization.lean; sha256: 884a54ef77d8d66811279d51b23db625beb4b471d4f5515f447f0a565c4ef09a -/
section Source1042
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev PrimeIdeal := {P : Id // Prime P}

def primeValuations (I : Id) : PrimeIdeal →₀ ℕ :=
  (factorization I).subtypeDomain Prime

def idealFromValuations (v : PrimeIdeal →₀ ℕ) : Id :=
  v.prod (fun P n=>P.val^n)

lemma idealFromValuations_ne_zero (v : PrimeIdeal →₀ ℕ) : idealFromValuations v≠0 := by
  unfold idealFromValuations Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr (fun P hP=>pow_ne_zero _ P.property.ne_zero)

@[simp] lemma primeValuations_apply (I : Id) (P : PrimeIdeal) :
    primeValuations I P=(normalizedFactors I).count P.val := by
  simp only [primeValuations,Finsupp.subtypeDomain_apply,factorization_eq_count]

@[simp] lemma primeValuations_one : primeValuations 1=0 := by
  simp only [primeValuations,factorization_one,Finsupp.subtypeDomain_zero]

lemma primeValuations_mul (I J : Id) (hI : I≠0) (hJ : J≠0) :
    primeValuations (I*J)=primeValuations I+primeValuations J := by
  simp only [primeValuations,factorization_mul hI hJ,Finsupp.subtypeDomain_add]

@[simp] lemma primeValuations_prime (P : PrimeIdeal) :
    primeValuations P.val=Finsupp.single P 1 := by
  ext Q
  simp only [primeValuations_apply,normalizedFactors_irreducible P.property.irreducible,
    normalize_eq,Multiset.count_singleton,Finsupp.single_apply]
  by_cases h : Q=P
  · subst Q
    simp
  · have hv : Q.val≠P.val := fun hh=>h (Subtype.ext hh)
    simp [Ne.symm h,hv]

lemma primeValuations_pow (I : Id) (n : ℕ) :
    primeValuations (I^n)=n • primeValuations I := by
  ext P
  simp only [primeValuations_apply,normalizedFactors_pow,Multiset.count_nsmul,
    Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]

@[simp] lemma idealFromValuations_zero : idealFromValuations 0=1 := by
  simp [idealFromValuations]

lemma idealFromValuations_add (v w : PrimeIdeal →₀ ℕ) :
    idealFromValuations (v+w)=idealFromValuations v*idealFromValuations w := by
  exact Finsupp.prod_add_index' (fun _=>pow_zero _) (fun _ _ _=>pow_add _ _ _)

@[simp] lemma idealFromValuations_single (P : PrimeIdeal) (n : ℕ) :
    idealFromValuations (Finsupp.single P n)=P.val^n := by
  simp [idealFromValuations]

@[simp] theorem primeValuations_idealFromValuations (v : PrimeIdeal →₀ ℕ) :
    primeValuations (idealFromValuations v)=v := by
  induction v using Finsupp.induction with
  | zero => simp only [idealFromValuations_zero,primeValuations_one]
  | @single_add P n v hP hn ih =>
    rw [idealFromValuations_add,primeValuations_mul _ _
      (idealFromValuations_ne_zero _) (idealFromValuations_ne_zero _),ih]
    simp only [idealFromValuations_single,primeValuations_pow,primeValuations_prime,
      Finsupp.smul_single,smul_eq_mul,mul_one]

@[simp] theorem idealFromValuations_primeValuations (I : Id) (hI : I≠0) :
    idealFromValuations (primeValuations I)=I := by
  have hs : ∀ P∈(factorization I).support,Prime P := by
    intro P hP
    exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp (by simpa using hP))
  unfold idealFromValuations primeValuations
  rw [Finsupp.prod_subtypeDomain_index hs]
  simp only [Finsupp.prod,support_factorization,factorization_eq_count]
  rw [← Finset.prod_multiset_count_of_subset _ _ (Finset.Subset.refl _)]
  exact Ideal.prod_normalizedFactors_eq_self hI

def nonzeroIdealValuationEquiv : {I : Id // I≠0} ≃ (PrimeIdeal →₀ ℕ) where
  toFun I := primeValuations I.val
  invFun v := ⟨idealFromValuations v,idealFromValuations_ne_zero v⟩
  left_inv I := Subtype.ext (idealFromValuations_primeValuations I.val I.property)
  right_inv := primeValuations_idealFromValuations

lemma primeIdeal_coprime (P Q : PrimeIdeal) (h : P≠Q) : IsCoprime P.val Q.val := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : Q.val.IsPrime := Ideal.isPrime_of_prime Q.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  let : Q.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance Q.property.ne_zero
  exact Ideal.isCoprime_of_isMaximal (fun hh=>h (Subtype.ext hh))

lemma prime_coprime_idealFromValuations (P : PrimeIdeal) (v : PrimeIdeal →₀ ℕ)
    (hP : v P=0) : IsCoprime P.val (idealFromValuations v) := by
  apply IsCoprime.prod_right
  intro Q hQ
  apply IsCoprime.pow_right
  apply primeIdeal_coprime
  intro hh
  subst Q
  exact Finsupp.mem_support_iff.mp hQ hP

def finsuppPairEquiv {α β γ : Type*} [Zero β] [Zero γ] :
    ((α→₀β)×(α→₀γ)) ≃ (α→₀(β×γ)) where
  toFun v := Finsupp.zipWith Prod.mk rfl v.1 v.2
  invFun v := (v.mapRange Prod.fst rfl,v.mapRange Prod.snd rfl)
  left_inv v := by
    apply Prod.ext <;> ext a <;> rfl
  right_inv v := by
    apply Finsupp.ext
    intro a
    exact Prod.eta (v a)

abbrev HighValuation := (ℕ×ℕ)×(ℕ×ℕ)
abbrev NonzeroIdeal := {I : Id // I≠0}

def highValuationEquiv : ((NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal)) ≃
    (PrimeIdeal→₀HighValuation) :=
  (Equiv.prodCongr
    (Equiv.prodCongr nonzeroIdealValuationEquiv nonzeroIdealValuationEquiv)
    (Equiv.prodCongr nonzeroIdealValuationEquiv nonzeroIdealValuationEquiv)).trans
      ((Equiv.prodCongr finsuppPairEquiv finsuppPairEquiv).trans finsuppPairEquiv)

@[simp] lemma highValuationEquiv_apply
    (a : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal)) (P : PrimeIdeal) :
    highValuationEquiv a P =
      ((primeValuations a.1.1.val P,primeValuations a.1.2.val P),
        (primeValuations a.2.1.val P,primeValuations a.2.2.val P)) := rfl

end SevenEighths.ProbePhysical
end

end OAI

end Source1042

/- Original source: OAI/NumberTheory/DirichletL/Detector/SourcePrime.lean; sha256: dcbeb867b568cf4da52fd647b502cc23f6ede73808f48f7fe34b3a93e3e9fe39 -/
section Source1043
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CubicEisenstein ConcreteTraceCRT
open ProbePhase ProbeEuler ProbePrimePower FiniteGaussPhase QuadraticGaussRay
local notation "O" => ActualEisensteinCubic.O

theorem gaussTwo_prime_localGamma (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hprimary : goodLambda^2∣p-1) (hI : primaryGenerator (Ideal.span {p})≠0) :
    gaussTwo (Ideal.span {p}) hI=localGamma p hp.ne_zero hg 2 := by
  let pp : Unit→O := fun _=>p
  have hpp : ∀i,pp i≠0 := fun _=>hp.ne_zero
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hi : primaryGenerator (Ideal.span {∏i,pp i})≠0 := by simpa [pp] using hI
  have he := gaussTwo_eq_canonicalProductGauss pp hpp hcop (fun _=>hg) (fun _=>hprimary) hi
  rw [canonicalProductGauss_cross_factors pp hpp hcop (fun _ => hg) (fun _ => 2)] at he
  simpa [pp,localGamma,ConcreteBreveE.normalizedTraceGauss] using he

theorem G_prime_localG (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1) :
    G p=MixedGaussConversion.localG p hp hg := by
  let pp : Unit→O := fun _=>p
  have hpp : ∀i,pp i≠0 := fun _=>hp
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have he := canonicalProductG_eq_fixedGValue pp hpp hcop (fun _=>hg)
    (fun _=>hchar) (fun _=>hprimary)
  unfold canonicalProductG at he
  rw [canonicalProductGauss_cross_factors pp hpp hcop (fun _ => hg) (fun _ => 3)] at he
  simpa [pp,G,fixedGQuotientValue,MixedGaussConversion.localG,breveLocalG,breveGamma3,
    ConcreteBreveE.normalizedTraceGauss] using he.symm

theorem localGamma_one_two_full_signal (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1) :
    localGamma p hp hg 1 * localGamma p hp hg 2 =
      -FiniteGaussPhase.angularFactor p * G p := by
  rw [G_prime_localG p hp hg hchar hprimary]
  exact localGamma_one_two_signal p hp hg hchar hprimary

lemma angularFactor_pow (p : O) (n : ℕ) : angularFactor (p^n)=angularFactor p^n := by
  simp only [angularFactor,map_pow,norm_pow,Complex.ofReal_pow,div_pow]

lemma gaussTwo_one : gaussTwo (1:Ideal O) (by rw [primaryGenerator_one]; exact one_ne_zero)=1 := by
  have hI : CubicSieve.Admissible (1:Ideal O) := ⟨squarefree_one,by rw [primaryGenerator_one]; exact one_ne_zero⟩
  rw [gaussTwo_eq_elementFourier (1:Ideal O) hI]
  simp only [primaryGenerator_one,map_one,norm_one,Complex.ofReal_one,div_one]
  have hrow (a : O) : CubicSieve.cubicRow (1:Ideal O) a=1 := by
    rw [CubicSieve.cubicRow,←idealRowHom_square,map_one,one_pow]
  rw [show CubicSieve.cubicRow (1:Ideal O)=(fun _=>1) from funext hrow]
  have he : elementFourier 1 one_ne_zero (fun _=>1) 1=sexticGauss 1 one_ne_zero 1 := by
    unfold elementFourier sexticGauss
    apply tsum_congr
    intro x
    simp only [Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,one_mul]
  rw [he,sexticGauss_one]

lemma gaussTwo_prime_power_small (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hprimary : goodLambda^2∣p-1) (e : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) :
    gaussTwo (Ideal.span {p^e}) hI=localGamma p hp.ne_zero hg 2^e := by
  have hcases : e=0 ∨ e=1 := by omega
  rcases hcases with rfl|rfl
  · simpa only [pow_zero,Ideal.span_singleton_one,←Ideal.one_eq_top] using gaussTwo_one
  · have hi : primaryGenerator (Ideal.span {p})≠0 := by simpa only [pow_one] using hI
    simpa only [pow_one] using gaussTwo_prime_localGamma p hp hg hprimary hi

lemma corrected_prime_cubic_signal (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) :
    localGamma p hp hg 2 * star (angularFactor p) * star (G p) = -(localGamma p hp hg 1)⁻¹ := by
  have hsig := localGamma_one_two_full_signal p hp hg hchar hprimary
  have hn := localGamma_norm_one p hp hg hchar 1 (by decide) (by decide)
  have hne : localGamma p hp hg 1≠0 := by intro h; rw [h,norm_zero] at hn; norm_num at hn
  have hG : G p*star (G p)=1 := by
    rw [mul_comm]
    exact G_conjugate_cancel p (supported_residue_odd p hs)
      (cubicTwo_isUnit_of_odd p (supported_residue_odd p hs))
  apply mul_left_cancel₀ hne
  calc
    _ = (localGamma p hp hg 1*localGamma p hp hg 2)*star (angularFactor p)*star (G p) := by ring
    _ = -1 := by
      rw [hsig]
      calc
        _ = -(angularFactor p*star (angularFactor p))*(G p*star (G p)) := by ring
        _ = _ := by rw [angularFactor_mul_star p hp,hG]; ring
    _ = _ := by rw [mul_neg,mul_inv_cancel₀ hne]

end SevenEighths.ProbePhysical
end

end OAI

end Source1043

/- Original source: OAI/NumberTheory/DirichletL/Detector/IdealUnit.lean; sha256: 9e945bfd6f13795198085de4a9bbfa9b4ac50070b3a2fbe511ad5f33b90d9746 -/
section Source1044
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CubicEisenstein ProbePhase ConcretePrimeRowBridge ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma supported_one_ideal : Supported (1 : Ideal O) := by
  refine ⟨one_ne_zero,?_⟩
  intro P hP
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP

lemma G_one : G (1:O)=1 := by
  have hs : Supported (Ideal.span {(1:O)}) := by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top]
    exact supported_one_ideal
  have ho := supported_residue_odd (1:O) hs
  have hn : G (1:O)≠0 := by
    intro hz
    have hh := G_norm_one_of_odd (1:O) ho
    rw [hz,norm_zero] at hh
    norm_num at hh
  have he := G_mul (1:O) 1 ho ho
  rw [one_mul,reciprocitySign_one_left (1:O) ho,mul_one] at he
  exact mul_left_cancel₀ hn (by simpa only [mul_one] using he.symm)

lemma angularFactor_one : FiniteGaussPhase.angularFactor (1:O)=1 := by
  simp only [FiniteGaussPhase.angularFactor,map_one,norm_one,Complex.ofReal_one,div_one]

@[simp] theorem bareIdealHighCoefficient_one (η : HeckeFamily.Character) :
    bareIdealHighCoefficient η 1 1 1 1 1=1 := by
  have hs := supported_one_ideal
  have hg : Squarefree (1:Ideal O) ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 :=
    ⟨squarefree_one,hs,hs,hs,hs⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hg]
  simp only [primaryGenerator_one,one_pow,one_mul]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_one,G_one,angularFactor_one]
  have ho := supported_residue_odd (1:O) (by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top];exact hs)
  rw [reciprocitySign_one_left (1:O) ho,
    bareCongruenceCoefficient_inner_one 1 one_ne_zero,outerQuotient_mk]
  simp only [map_one,star_one,one_mul,Ideal.span_singleton_one,←Ideal.one_eq_top]

@[simp] theorem bareIdealHighSummand_one (η : HeckeFamily.Character) (x w z : ℂ) :
    bareIdealHighSummand η 1 x w z 1 1 1 1=1 := by
  have hw (t : ℂ) : fullIdealWeight t (1:Ideal O)=1 := (IdealEuler.normWeight t).map_one
  simp only [bareIdealHighSummand,bareIdealHighCoefficient_one,hw,one_mul]

end SevenEighths.ProbePhysical
end

end OAI

end Source1044

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighValuations.lean; sha256: f5665ad6b57bb64680b003724c20a72c757ed0806a90f8d140e5f161de1c2369 -/
section Source1045
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev HighIdeal := (Id×Id)×(Id×Id)

def highIdeals (v : PrimeIdeal→₀HighValuation) : HighIdeal :=
  ((idealFromValuations (v.mapRange (fun b=>b.1.1) rfl),
    idealFromValuations (v.mapRange (fun b=>b.1.2) rfl)),
   (idealFromValuations (v.mapRange (fun b=>b.2.1) rfl),
    idealFromValuations (v.mapRange (fun b=>b.2.2) rfl)))

lemma highIdeals_eq_equiv (v : PrimeIdeal→₀HighValuation) :
    highIdeals v =
      (((highValuationEquiv.symm v).1.1.val,(highValuationEquiv.symm v).1.2.val),
       ((highValuationEquiv.symm v).2.1.val,(highValuationEquiv.symm v).2.2.val)) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    apply congrArg idealFromValuations
    ext P
    rfl

lemma highIdeals_injective : Function.Injective highIdeals := by
  intro v w h
  apply highValuationEquiv.symm.injective
  rw [highIdeals_eq_equiv,highIdeals_eq_equiv] at h
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.1.1) h)
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.1.2) h)
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.2.1) h)
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.2.2) h)

lemma highIdeals_zero : highIdeals 0=1 := by
  simp only [highIdeals,Finsupp.mapRange_zero,idealFromValuations_zero]
  rfl

lemma highIdeals_single (P : PrimeIdeal) (b : HighValuation) :
    highIdeals (Finsupp.single P b)=((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2)) := by
  simp only [highIdeals,Finsupp.mapRange_single,idealFromValuations_single]

lemma highIdeals_add (v w : PrimeIdeal→₀HighValuation) :
    highIdeals (v+w)=highIdeals v*highIdeals w := by
  have hproj (f : HighValuation→ℕ) (hf0 : f 0=0) (hf : ∀a b,f (a+b)=f a+f b) :
      (v+w).mapRange f hf0=v.mapRange f hf0+w.mapRange f hf0 := by
    ext P
    simp only [Finsupp.mapRange_apply,Finsupp.add_apply,hf]
  simp only [highIdeals,hproj (fun b=>b.1.1) rfl (fun _ _=>rfl),
    hproj (fun b=>b.1.2) rfl (fun _ _=>rfl),hproj (fun b=>b.2.1) rfl (fun _ _=>rfl),
    hproj (fun b=>b.2.2) rfl (fun _ _=>rfl),idealFromValuations_add]
  rfl

lemma prime_coprime_highIdeals (P : PrimeIdeal) (v : PrimeIdeal→₀HighValuation)
    (hv : v P=0) : IsCoprime P.val
      ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) := by
  have hc (f : HighValuation→ℕ) (hf0 : f 0=0) :
      IsCoprime P.val (idealFromValuations (v.mapRange f hf0)) := by
    apply prime_coprime_idealFromValuations
    simp only [Finsupp.mapRange_apply,hv,hf0]
  exact ((hc _ rfl).mul_right (hc _ rfl)).mul_right (hc _ rfl) |>.mul_right (hc _ rfl)

def highValuationTerm (η : HeckeFamily.Character) (x w z : ℂ)
    (v : PrimeIdeal→₀HighValuation) : ℂ :=
  bareIdealHighSummand η 1 x w z (highIdeals v).1.1 (highIdeals v).1.2
    (highIdeals v).2.1 (highIdeals v).2.2

def highPrimeTerm (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  bareIdealHighSummand η 1 x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)

lemma highPrimeTerm_zero (η : HeckeFamily.Character) (x w z : ℂ) (P : PrimeIdeal) :
    highPrimeTerm η x w z P 0=1 := by
  simp only [highPrimeTerm,Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_one]

theorem highValuationTerm_eq_prod (η : HeckeFamily.Character) (x w z : ℂ)
    (v : PrimeIdeal→₀HighValuation) :
    highValuationTerm η x w z v=v.prod (highPrimeTerm η x w z) := by
  induction v using Finsupp.induction with
  | zero =>
    simp only [highValuationTerm,highIdeals_zero,Prod.fst_one,Prod.snd_one,
      bareIdealHighSummand_one,Finsupp.prod_zero_index]
  | @single_add P b v hP hb ih =>
    have hv : v P=0 := Finsupp.notMem_support_iff.mp hP
    have hc := prime_coprime_highIdeals P v hv
    have hpow : IsCoprime (P.val^b.1.1*P.val^b.1.2*P.val^b.2.1*P.val^b.2.2)
        ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) :=
      ((hc.pow_left.mul_left hc.pow_left).mul_left hc.pow_left).mul_left hc.pow_left
    have hd : Disjoint (Finsupp.single P b).support v.support := by
      rw [Finsupp.support_single _ hb]
      exact Finset.disjoint_singleton_left.mpr hP
    rw [Finsupp.prod_add_index_of_disjoint hd,Finsupp.prod_single_index (highPrimeTerm_zero η x w z P),←ih]
    unfold highValuationTerm
    rw [highIdeals_add,highIdeals_single]
    exact bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hpow

theorem highValuationTerm_summable_norm (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun v : PrimeIdeal→₀HighValuation=>‖highValuationTerm η x w z v‖) :=
  (bareIdealHighSummand_summable η 1 x w z hx hw hz).norm.comp_injective highIdeals_injective

end SevenEighths.ProbePhysical
end

end OAI

end Source1045

/- Original source: OAI/NumberTheory/DirichletL/Detector/EulerFinsupp.lean; sha256: 68ef98e1a5abc9fb5606a9fe102e355fabcc9bbe1a78aa620489fff65a2c576e -/
section Source1046
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeEulerFinsupp

lemma finitePi_fin {β : Type*} (n : ℕ) (f : Fin n→β→ℂ)
    (hf : ∀ i,Summable (fun b=>‖f i b‖)) :
    Summable (fun v : Fin n→β => ‖∏ i,f i (v i)‖) ∧
      (∑' v : Fin n→β,∏ i,f i (v i))=∏ i,∑' b,f i b := by
  induction n with
  | zero =>
    constructor
    · exact (hasSum_fintype _).summable
    · simp
  | succ n ih =>
    have ht := ih (fun i=>f i.succ) (fun i=>hf i.succ)
    let e := Fin.consEquiv (fun _ : Fin (n+1)=>β)
    have he (v : β×(Fin n→β)) :
        (∏ i,f i (e v i))=f 0 v.1*(∏ i,f i.succ (v.2 i)) := by
      rw [Fin.prod_univ_succ]
      rfl
    constructor
    · rw [←e.summable_iff]
      simp only [Function.comp_def,he]
      have hm : Summable (fun v : β×(Fin n→β)=>‖f 0 v.1‖ * ‖∏ i : Fin n,f i.succ (v.2 i)‖) :=
        (hf 0).mul_of_nonneg ht.1 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
      simpa only [norm_mul] using hm
    · rw [←e.tsum_eq (fun v=>∏ i,f i (v i))]
      simp only [he]
      rw [←tsum_mul_tsum_of_summable_norm (f:=f 0)
        (g:=fun v : Fin n→β=>∏ i : Fin n,f i.succ (v i)) (hf 0) ht.1,ht.2,Fin.prod_univ_succ]

lemma finitePi {α β : Type*} [Fintype α] (f : α→β→ℂ)
    (hf : ∀ i,Summable (fun b=>‖f i b‖)) :
    Summable (fun v : α→β => ‖∏ i,f i (v i)‖) ∧
      (∑' v : α→β,∏ i,f i (v i))=∏ i,∑' b,f i b := by
  let e := Fintype.equivFin α
  let d := Equiv.arrowCongr e.symm (Equiv.refl β)
  have h := finitePi_fin (Fintype.card α) (fun i=>f (e.symm i)) (fun i=>hf (e.symm i))
  have hd (v : Fin (Fintype.card α)→β) :
      (∏ i,f i (d v i))=∏ j,f (e.symm j) (v j) := by
    apply Fintype.prod_equiv e
    intro i
    simp only [d,Equiv.arrowCongr_apply,Equiv.symm_symm,Equiv.refl_apply,e.symm_apply_apply,Function.comp_apply]
  constructor
  · rw [←d.summable_iff]
    simpa only [Function.comp_def,hd] using h.1
  · rw [←d.tsum_eq (fun v=>∏ i,f i (v i))]
    simp only [hd]
    rw [h.2]
    exact e.symm.prod_comp (fun i=>∑' b,f i b)

variable {α β : Type*} [AddCommMonoid β]

lemma finiteEuler (f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hf : ∀a,Summable (fun b=>‖f a b‖)) (S : Finset α) :
    (∑' v : {v : α→₀β // (v.support:Set α)⊆S},v.val.prod f)=
      ∏ a∈S,∑' b,f a b := by
  let e : {v : α→₀β // (v.support:Set α)⊆S} ≃ (S→β) :=
    (Finsupp.restrictSupportEquiv (S:Set α) β).trans Finsupp.equivFunOnFinite
  have he (v : {v : α→₀β // (v.support:Set α)⊆S}) :
      v.val.prod f=∏ a:S,f a.val (e v a) := by
    rw [←Finsupp.prod_subtypeDomain_index (p:=fun a=>a∈S) (fun a ha=>v.property ha)]
    exact Finsupp.prod_fintype _ _ (fun a=>h0 a.val)
  simp_rw [he]
  rw [e.tsum_eq (fun v : S→β=>∏ a:S,f a.val (v a))]
  rw [(finitePi (fun a:S=>f a.val) (fun a=>hf a.val)).2]
  exact Finset.prod_coe_sort S (fun a=>∑' b,f a b)

theorem hasProd_of_summable (f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hs : Summable (fun v : α→₀β=>‖v.prod f‖)) :
    HasProd (fun a=>∑' b,f a b) (∑' v : α→₀β,v.prod f) := by
  have hf (a : α) : Summable (fun b=>‖f a b‖) := by
    have hh := hs.comp_injective (Finsupp.single_injective a)
    simpa only [Function.comp_def,Finsupp.prod_single_index (h0 a)] using hh
  have ht : Tendsto (fun S : Finset α=>∑' v : α→₀β,
      if v.support⊆S then v.prod f else 0) atTop (𝓝 (∑' v : α→₀β,v.prod f)) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · intro v
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop v.support] with S hS
      simp only [ite_eq_left hS]
    · apply Filter.Eventually.of_forall
      intro S v
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (v.prod f)
  have he (S : Finset α) : (∑' v : α→₀β,if v.support⊆S then v.prod f else 0)=
      ∏a∈S,∑' b,f a b := by
    rw [←finiteEuler f h0 hf S]
    trans ∑' v : α→₀β, {v : α→₀β | (v.support:Set α)⊆S}.indicator (fun v=>v.prod f) v
    · apply tsum_congr
      intro v
      simp only [Set.indicator,Set.mem_ofPred_eq,Finset.coe_subset]
    · exact (tsum_subtype {v : α→₀β | (v.support:Set α)⊆S} (fun v=>v.prod f)).symm
  change Tendsto (fun S : Finset α=>∏a∈S,∑' b,f a b) atTop _
  simpa only [he] using ht

end SevenEighths.ProbeEulerFinsupp
end

end OAI

end Source1046

/- Original source: OAI/NumberTheory/DirichletL/Detector/SourcePrimeFactor.lean; sha256: 82d75a913c0811c2adb2f9328315efb2d782fc605a2b0a42384dcbd33cf13ba4 -/
section Source1047
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem bareSourceCoefficient_prime_formula (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k j : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (p^j) =
    (-1:ℂ)^e * ((localGamma p hp.ne_zero hg 1)⁻¹)^e * (targetMonoid η p)^e *
      (star (FiniteGaussPhase.angularFactor p)^3 * (targetMonoid η p)^3 *
        star (localGamma p hp.ne_zero hg 3))^l *
      (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j := by
  have ho := supported_residue_odd p hs
  have hself := reciprocitySign_self_eq_sextic_neg_one p hp.ne_zero hg hchar ho
  have hstar : star (actualSextic (Ideal.span {p}) hg (-1))=
      actualSextic (Ideal.span {p}) hg (-1) := by
    rw [←hself,reciprocitySign_star]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_prime_power_small p hp hg hprimary e he hI,
    bareCongruenceCoefficient_all_prime_powers p hp hg,
    angularFactor_pow,map_pow,
    G_completed_prime_power p ho e l he,
    G_cube_eq_normalizedTraceGauss p hp.ne_zero hg hchar ho,
    reciprocitySign_pow_left p _ (odd_residue_pow p ho k),reciprocitySign_pow_right p p ho,
    hself]
  change _ = _
  simp only [star_mul,star_pow,hstar]
  change (targetMonoid η p)^(e+3*l) * star (FiniteGaussPhase.angularFactor p)^(e+3*l) *
    (localGamma p hp.ne_zero hg 2^e *
      ((actualSextic (Ideal.span {p}) hg (-1))^(e*l+l.choose 2) *
        (star (localGamma p hp.ne_zero hg 3)^l * star (G p)^e)) *
      (((actualSextic (Ideal.span {p}) hg (-1))^k)^(e+3*l) *
        sourceScalar p hp hg (e+3*l) k j)) = _
  calc
    _ = (localGamma p hp.ne_zero hg 2 * star (FiniteGaussPhase.angularFactor p) * star (G p))^e *
      (targetMonoid η p)^e *
      (star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3*
        star (localGamma p hp.ne_zero hg 3))^l *
      (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j := by
        simp only [pow_add,pow_mul,mul_pow]
        ring
    _ = _ := by
      rw [corrected_prime_cubic_signal p hp.ne_zero hg hchar hprimary hs]
      rw [neg_eq_neg_one_mul ((localGamma p hp.ne_zero hg 1)⁻¹),mul_pow]

theorem bareSourceCoefficient_weighted_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) (x w z : ℂ) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (p^(6*m)) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  rw [bareSourceCoefficient_prime_formula η p hp hg hchar hprimary hs e l k (6*m) he hI]
  unfold sourcePrincipalTerm sourceWeightedScalar
  simp only [zpow_neg,zpow_natCast,←inv_pow,Complex.ofReal_natCast]
  have hpdiag := source_signed_phase
    (actualACube η p*star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) (actualSextic_neg_one_sq _ hg) e l k
  simp only [localCubePhase] at hpdiag
  have ha : actualACube η p=
      star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3 := rfl
  rw [ha] at hpdiag ⊢
  calc
    _ = ((-1:ℂ)^e*((localGamma p hp.ne_zero hg 1)⁻¹)^e*(targetMonoid η p)^e) *
      ((star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3*
        star (localGamma p hp.ne_zero hg 3))^l *
        (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2)) *
      sourceScalar p hp hg (e+3*l) k (6*m) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) := by ring
    _ = _ := by rw [←hpdiag]; ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1047

/- Original source: OAI/NumberTheory/DirichletL/Detector/IdealLocalEuler.lean; sha256: 01fd17bb0c9ac3e39734d4811083462a7fc8490e04561b16799ae9e3d4556f74 -/
section Source1048
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

lemma primaryGenerator_prime_power (p : O) (hp : p≠0) (hprimary : goodLambda^2∣p-1) (e : ℕ) :
    primaryGenerator ((Ideal.span {p})^e)=p^e := by
  rw [primaryGenerator_pow,primaryGenerator_span p hp hprimary]

lemma prime_power_small_squarefree (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (e : ℕ) (he : e≤1) :
    Squarefree ((Ideal.span {p})^e) := by
  have hP : Prime (Ideal.span {p}:Ideal O) :=
    Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero) inferInstance
  have hcases : e=0 ∨ e=1 := by omega
  rcases hcases with rfl|rfl
  · simpa only [pow_zero] using (squarefree_one : Squarefree (1:Ideal O))
  · simpa only [pow_one] using hP.squarefree

theorem bareIdealHighCoefficient_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) :
    bareIdealHighCoefficient η 1 ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    bareSourceCoefficient η (Ideal.span {p^e})
      (by rw [← Ideal.span_singleton_pow,primaryGenerator_prime_power p hp.ne_zero hprimary e];
          exact pow_ne_zero _ hp.ne_zero)
      (p^(e+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^(6*m)) := by
  have hguard : Squarefree ((Ideal.span {p})^e) ∧ Supported ((Ideal.span {p})^e) ∧
      Supported ((Ideal.span {p})^l) ∧ Supported ((Ideal.span {p})^k) ∧ Supported ((Ideal.span {p})^m) :=
    ⟨prime_power_small_squarefree p hp e he,supported_pow hs e,supported_pow hs l,supported_pow hs k,supported_pow hs m⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hguard]
  simp only [primaryGenerator_prime_power p hp.ne_zero hprimary,one_mul]
  have hA : p^e*(p^l)^3=p^(e+3*l) := by rw [←pow_mul,Nat.mul_comm l 3,←pow_add]
  have hH : (p^m)^6=p^(6*m) := by rw [←pow_mul,Nat.mul_comm m 6]
  simp only [hA,hH,Ideal.span_singleton_pow]

lemma fullIdealWeight_power (s : ℂ) (I : Ideal O) (n : ℕ) :
    fullIdealWeight s (I^n)=fullIdealWeight s I^n := (IdealEuler.normWeight s).map_pow I n

lemma prime_spectral_weights (p : O) (hp : p≠0) (e l k m : ℕ) (x w z : ℂ) :
    fullIdealWeight (x+1/2) ((Ideal.span {p})^e) *
      fullIdealWeight (1+3*x) ((Ideal.span {p})^l) *
      fullIdealWeight w ((Ideal.span {p})^k) * fullIdealWeight (6*z) ((Ideal.span {p})^m) =
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) := by
  have hI : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp
  have hQ : (Ideal.absNorm (Ideal.span {p}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hI
  simp only [fullIdealWeight_power]
  simp only [fullIdealWeight,ite_eq_right hI]
  rw [←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,
    ←Complex.cpow_add _ _ hQ,←Complex.cpow_add _ _ hQ,←Complex.cpow_add _ _ hQ]
  congr 1
  ring

theorem bareIdealHighSummand_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) (x w z : ℂ) :
    bareIdealHighSummand η 1 x w z ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_at_prime η p hp hprimary hs e l k m he]
  have hw := prime_spectral_weights p hp.ne_zero e l k m x w z
  simp only [mul_assoc] at hw ⊢
  rw [hw]
  simpa only [mul_assoc] using
    bareSourceCoefficient_weighted_prime η p hp hg hchar hprimary hs e l k m he _ x w z

def idealHighLocalFactor (η : HeckeFamily.Character) (P : Ideal O) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m,
    bareIdealHighSummand η 1 x w z (P^e.val) (P^l) (P^k) (P^m)

theorem idealHighLocalFactor_eq_source (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (x w z : ℂ) :
    idealHighLocalFactor η (Ideal.span {p}) x w z =
      sourcePrincipalSeries p hp hg (targetMonoid η p) (actualACube η p) x w z := by
  unfold idealHighLocalFactor sourcePrincipalSeries
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact bareIdealHighSummand_at_prime η p hp hg hchar hprimary hs e.val l k m (by omega) x w z

theorem idealHighLocalFactor_euler_identity (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    idealHighLocalFactor η (Ideal.span {p}) x w z =
      (1-coordD Q (targetMonoid η p) 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q ((actualACube η p)^2) (targetMonoid η p) 1 x w z := by
  rw [idealHighLocalFactor_eq_source η p hp hg hchar hprimary hs]
  exact sourcePrincipalSeries_euler_identity p hp hg hchar _ _ x w z hV hR hW hD

end SevenEighths.ProbePhysical
end

end OAI

end Source1048

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighEuler.lean; sha256: 86ca26f94a71e214d4361ddbd80ca5e83bdff37b592dac93b1eac03a6b584c32 -/
section Source1049
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma bareIdealHighSummand_support (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (I J K L : Id) (h : bareIdealHighSummand η u x w z I J K L≠0) :
    highSupport I J K L := by
  by_contra hn
  apply h
  unfold highSupport at hn
  simp only [bareIdealHighSummand,bareIdealHighCoefficient,dite_eq_right hn,zero_mul]

theorem highValuationTerm_tsum_eq (η : HeckeFamily.Character) (x w z : ℂ) :
    (∑'v : PrimeIdeal→₀HighValuation,highValuationTerm η x w z v)=
      bareIdealHighSeries η 1 x w z := by
  unfold highValuationTerm bareIdealHighSeries
  apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
    bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
  intro a ha
  have hs := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 ha
  let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
    ((⟨a.1.1,hs.2.1.1⟩,⟨a.1.2,hs.2.2.1.1⟩),
      (⟨a.2.1,hs.2.2.2.1.1⟩,⟨a.2.2,hs.2.2.2.2.1⟩))
  refine ⟨highValuationEquiv b,?_⟩
  rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]

theorem bareIdealHighSeries_hasProd (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,highPrimeTerm η x w z P b)
      (bareIdealHighSeries η 1 x w z) := by
  have hs := highValuationTerm_summable_norm η x w z hx hw hz
  simp only [highValuationTerm_eq_prod] at hs
  have he := ProbeEulerFinsupp.hasProd_of_summable (highPrimeTerm η x w z)
    (highPrimeTerm_zero η x w z) hs
  simpa only [←highValuationTerm_eq_prod,highValuationTerm_tsum_eq] using he

theorem bareIdealHighSeries_eq_tprod (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    bareIdealHighSeries η 1 x w z =
      ∏' P : PrimeIdeal,∑' b : HighValuation,highPrimeTerm η x w z P b :=
  (bareIdealHighSeries_hasProd η x w z hx hw hz).tprod_eq.symm

end SevenEighths.ProbePhysical
end

end OAI

end Source1049

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighEulerGeneral.lean; sha256: 32bb464b6df128eb31f45538e068cf6da905a15eab738f3e34cad41f1e9b50cc -/
section Source1050
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma highArray_val_prod (F : HighIdeal→ℂ) (h1 : F 1=1)
    (hmul : ∀ a b : HighIdeal,
      IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2) → F (a*b)=F a*F b)
    (v : PrimeIdeal→₀HighValuation) :
    F (highIdeals v)=v.prod (fun P b=>F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) := by
  have hzero (P : PrimeIdeal) : F ((P.val^0,P.val^0),(P.val^0,P.val^0))=1 := by
    simp only [pow_zero]
    change F (1 : HighIdeal)=1
    exact h1
  induction v using Finsupp.induction with
  | zero => simp only [highIdeals_zero,h1,Finsupp.prod_zero_index]
  | @single_add P b v hP hb ih =>
    have hc := prime_coprime_highIdeals P v (Finsupp.notMem_support_iff.mp hP)
    have hpow : IsCoprime (P.val^b.1.1*P.val^b.1.2*P.val^b.2.1*P.val^b.2.2)
        ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) :=
      ((hc.pow_left.mul_left hc.pow_left).mul_left hc.pow_left).mul_left hc.pow_left
    have hd : Disjoint (Finsupp.single P b).support v.support := by
      rw [Finsupp.support_single _ hb]
      exact Finset.disjoint_singleton_left.mpr hP
    rw [Finsupp.prod_add_index_of_disjoint hd,Finsupp.prod_single_index (hzero P),←ih,
      highIdeals_add,highIdeals_single]
    exact hmul _ _ hpow

theorem highArray_hasProd (F : HighIdeal→ℂ) (h1 : F 1=1)
    (hmul : ∀ a b : HighIdeal,
      IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2) → F (a*b)=F a*F b)
    (hzero : ∀ a : HighIdeal,F a≠0 → a.1.1≠0 ∧ a.1.2≠0 ∧ a.2.1≠0 ∧ a.2.2≠0)
    (hs : Summable (fun a=>‖F a‖)) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) (∑' a,F a) := by
  have hv := hs.comp_injective highIdeals_injective
  have hp := highArray_val_prod F h1 hmul
  simp only [Function.comp_def,hp] at hv
  have hlocal (P : PrimeIdeal) : F ((P.val^0,P.val^0),(P.val^0,P.val^0))=1 := by
    simp only [pow_zero]
    change F (1 : HighIdeal)=1
    exact h1
  have he := ProbeEulerFinsupp.hasProd_of_summable
    (fun (P : PrimeIdeal) (b : HighValuation)=>F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) hlocal hv
  have hsum : (∑' v : PrimeIdeal→₀HighValuation,F (highIdeals v))=∑' a,F a := by
    apply highIdeals_injective.tsum_eq
    intro a ha
    have hn := hzero a ha
    let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
      ((⟨a.1.1,hn.1⟩,⟨a.1.2,hn.2.1⟩),(⟨a.2.1,hn.2.2.1⟩,⟨a.2.2,hn.2.2.2⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [←hp,hsum] using he

end SevenEighths.ProbePhysical
end

end OAI

end Source1050

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsMultiplicative.lean; sha256: bc3e024e0ad6f3aee38e1c0e7ffa8b232d0f40872de5ea3b8662ba926fba9955 -/
section Source1051
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem bareSourceCoefficient_product_row_frequency (η : HeckeFamily.Character) (u : O) (I J : Ideal O)
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
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) (u*(a*b)^6) =
      bareSourceCoefficient η I hI.2 A s hA (u*a^6) * bareSourceCoefficient η J hJ.2 B r hB (u*b^6) := by
  have he := bareSourceCoefficient_product η I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop (u*(a*b)^6)
  dsimp only at he ⊢
  have hi := bareSourceCoefficient_sixth_frequency η I hI.2 (primaryGenerator I*n^3) s
    (supported_completed _ _ hc hn) hs b (u*a^6) hba
  have hj := bareSourceCoefficient_sixth_frequency η J hJ.2 (primaryGenerator J*m^3) r
    (supported_completed _ _ hd hm) hr a (u*b^6) hab
  rw [show b^6*(u*a^6)=u*(a*b)^6 by ring] at hi
  rw [show a^6*(u*b^6)=u*(a*b)^6 by ring] at hj
  rw [hi,hj] at he
  exact he

theorem bareIdealHighCoefficient_row_mul (η : HeckeFamily.Character) (u : O)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighCoefficient η u (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighCoefficient η u I J K L * bareIdealHighCoefficient η u I' J' K' L' := by
  have hII := hcop.mono (first_block_dvd I J K L) (first_block_dvd I' J' K' L')
  by_cases h : highSupport I J K L ∧ highSupport I' J' K' L'
  · have hprod := (highSupport_mul I J K L I' J' K' L' hII).mpr h
    rcases h with ⟨h,h'⟩
    have hsA := (supported_mul_iff (I*J^3) K).mpr
      ⟨(supported_mul_iff I (J^3)).mpr ⟨h.2.1,supported_pow h.2.2.1 3⟩,h.2.2.2.1⟩
    have hsB := (supported_mul_iff (I'*J'^3) K').mpr
      ⟨(supported_mul_iff I' (J'^3)).mpr ⟨h'.2.1,supported_pow h'.2.2.1 3⟩,h'.2.2.2.1⟩
    have hc3 : IsCoprime ((I*J*K*L)^3) ((I'*J'*K'*L')^3) := hcop.pow_left.pow_right
    have hab := primaryGenerator_coprime _ _ hsA hsB
      (hc3.mono (completed_block_dvd_cube I J K L) (completed_block_dvd_cube I' J' K' L'))
    have hba := primaryGenerator_coprime _ _ h'.2.2.2.2 hsA
      (hcop.symm.pow_right.mono (last_block_dvd I' J' K' L') (completed_block_dvd_cube I J K L))
    have hab' := primaryGenerator_coprime _ _ h.2.2.2.2 hsB
      (hcop.pow_right.mono (last_block_dvd I J K L) (completed_block_dvd_cube I' J' K' L'))
    simp only [primaryGenerator_mul,primaryGenerator_pow] at hab hba hab'
    have he := bareSourceCoefficient_product_row_frequency η u I I'
      ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      ⟨h'.1,supported_primaryGenerator_ne_zero I' h'.2.1⟩
      ⟨hprod.1,supported_primaryGenerator_ne_zero (I*I') hprod.2.1⟩ hII
      (primaryGenerator J) (primaryGenerator J') (primaryGenerator K) (primaryGenerator K')
      ((supported_span_primaryGenerator_iff I).mpr h.2.1)
      ((supported_span_primaryGenerator_iff I').mpr h'.2.1)
      ((supported_span_primaryGenerator_iff J).mpr h.2.2.1)
      ((supported_span_primaryGenerator_iff J').mpr h'.2.2.1)
      ((supported_span_primaryGenerator_iff K).mpr h.2.2.2.1)
      ((supported_span_primaryGenerator_iff K').mpr h'.2.2.2.1)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).2
      (primaryGenerator_spec I' (supported_primaryGenerator_ne_zero I' h'.2.1)).2
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).2
      (primaryGenerator_spec J' (supported_primaryGenerator_ne_zero J' h'.2.2.1)).2
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).2
      (primaryGenerator_spec K' (supported_primaryGenerator_ne_zero K' h'.2.2.2.1)).2
      hab (primaryGenerator L) (primaryGenerator L') hba hab'
    unfold highSupport at hprod h h'
    unfold bareIdealHighCoefficient
    rw [dite_eq_left hprod,dite_eq_left h,dite_eq_left h']
    simp only [primaryGenerator_mul]
    dsimp only at he
    convert he using 1 ; ring_nf
  · have hprod := mt (highSupport_mul I J K L I' J' K' L' hII).mp h
    unfold highSupport at hprod
    unfold bareIdealHighCoefficient
    rw [dite_eq_right hprod]
    by_cases hi : highSupport I J K L
    · have hj : ¬highSupport I' J' K' L' := fun hj=>h ⟨hi,hj⟩
      unfold highSupport at hj
      rw [dite_eq_right hj,mul_zero]
    · unfold highSupport at hi
      rw [dite_eq_right hi,zero_mul]

theorem bareIdealHighSummand_row_mul (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighSummand η u x w z (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighSummand η u x w z I J K L * bareIdealHighSummand η u x w z I' J' K' L' := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_row_mul η u I J K L I' J' K' L' hcop,
    fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1051

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsEuler.lean; sha256: 3f494f7fb3fa2ff558f4a96d08dc3fd3ac502550fa9d421d332b65f3127b59bd -/
section Source1052
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CubicEisenstein ProbePhase ConcretePrimeRowBridge ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

@[simp] theorem bareIdealHighCoefficient_row_one (η : HeckeFamily.Character) (u : O) :
    bareIdealHighCoefficient η u 1 1 1 1=1 := by
  have hs := supported_one_ideal
  have hg : Squarefree (1:Ideal O) ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 :=
    ⟨squarefree_one,hs,hs,hs,hs⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hg]
  simp only [primaryGenerator_one,one_pow,mul_one]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_one,G_one,angularFactor_one]
  have ho := supported_residue_odd (1:O) (by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top];exact hs)
  rw [reciprocitySign_one_left (1:O) ho,
    bareCongruenceCoefficient_inner_one 1 one_ne_zero,outerQuotient_mk]
  simp only [map_one,star_one,one_mul,Ideal.span_singleton_one,←Ideal.one_eq_top]

@[simp] theorem bareIdealHighSummand_row_one (η : HeckeFamily.Character) (u : O) (x w z : ℂ) :
    bareIdealHighSummand η u x w z 1 1 1 1=1 := by
  have hw (t : ℂ) : fullIdealWeight t (1:Ideal O)=1 := (IdealEuler.normWeight t).map_one
  simp only [bareIdealHighSummand,bareIdealHighCoefficient_row_one,hw,one_mul]

theorem bareIdealHighSeries_row_hasProd (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      bareIdealHighSummand η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (bareIdealHighSeries η u x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=>bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · exact bareIdealHighSummand_row_one η u x w z
  · intro a b hc
    exact bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc
  · intro a ha
    have hs := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 ha
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (bareIdealHighSummand_summable η u x w z hx hw hz).norm

end SevenEighths.ProbePhysical
end

end OAI

end Source1052

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighDeletion.lean; sha256: 220edd1faefc835cef352ad47ffadc47f48c96e7bcac54ad662e97ca7396db1c -/
section Source1053
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def highIdealMask (S : Finset Id) (D I J K L : Id) : ℂ :=
  completedMask S D I J *
    (if ∀ P∈S,¬P∣K then 1 else 0) * (if ∀ P∈S,¬P∣L then 1 else 0)

lemma highIdealMask_norm_le_one (S : Finset Id) (D I J K L : Id) :
    ‖highIdealMask S D I J K L‖≤1 := by
  unfold highIdealMask
  split_ifs <;> simp only [mul_one,mul_zero,norm_zero]
  · exact completedMask_norm_le_one S D I J
  all_goals norm_num

def markedIdealHighSummand (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) : ℂ :=
  highIdealMask S D I J K L * bareIdealHighSummand η u x w z I J K L

lemma markedIdealHighSummand_norm_le (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) :
    ‖markedIdealHighSummand S D η u x w z I J K L‖≤‖bareIdealHighSummand η u x w z I J K L‖ := by
  rw [markedIdealHighSummand,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (highIdealMask_norm_le_one S D I J K L)

theorem markedIdealHighSummand_summable (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun p : (Id×Id)×(Id×Id) =>
      markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (fun p=>markedIdealHighSummand_norm_le S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2)
    (bareIdealHighSummand_summable η u x w z hx hw hz).norm

def markedIdealHighSeries (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) : ℂ :=
  ∑' p : (Id×Id)×(Id×Id), markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2

end SevenEighths.ProbePhysical
end

end OAI

end Source1053

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighExcludedEuler.lean; sha256: 0b11695c3a22d240125d20b2609f169d91b0feebaf1e6d086903a1b9038247f3 -/
section Source1054
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeCompleted CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma outside_mul (S : Finset Id) (hS : ∀P∈S,Prime P) (A B : Id) :
    (∀P∈S,¬P∣A*B) ↔ (∀P∈S,¬P∣A) ∧ (∀P∈S,¬P∣B) := by
  constructor
  · intro h
    constructor
    · intro P hP hd
      exact h P hP ((hS P hP).dvd_mul.mpr (Or.inl hd))
    · intro P hP hd
      exact h P hP ((hS P hP).dvd_mul.mpr (Or.inr hd))
  · rintro ⟨hA,hB⟩ P hP hd
    exact ((hS P hP).dvd_mul.mp hd).elim (hA P hP) (hB P hP)

lemma outside_cube (S : Finset Id) (hS : ∀P∈S,Prime P) (A : Id) :
    (∀P∈S,¬P∣A^3) ↔ ∀P∈S,¬P∣A := by
  constructor
  · intro h P hP hd
    exact h P hP (dvd_trans hd (dvd_pow_self A (by decide : (3:ℕ)≠0)))
  · intro h P hP hd
    exact h P hP ((hS P hP).dvd_of_dvd_pow hd)

def highExclusion (S : Finset Id) (hS : ∀P∈S,Prime P) : Id→*ℂ where
  toFun A := if ∀P∈S,¬P∣A then 1 else 0
  map_one' := by
    rw [ite_eq_left]
    intro P hP hd
    exact (hS P hP).not_isUnit (isUnit_of_dvd_one hd)
  map_mul' A B := by
    simp only [outside_mul S hS A B]
    split_ifs <;> simp_all

lemma highExclusion_cube (S : Finset Id) (hS : ∀P∈S,Prime P) (A : Id) :
    highExclusion S hS (A^3)=highExclusion S hS A := by
  change (if ∀P∈S,¬P∣A^3 then (1:ℂ) else 0)=_
  simp only [outside_cube S hS]
  rfl

theorem highIdealMask_unmarked (S : Finset Id) (hS : ∀P∈S,Prime P) (I J K L : Id) :
    highIdealMask S 1 I J K L =
      highExclusion S hS I*highExclusion S hS J*highExclusion S hS K*highExclusion S hS L := by
  have he : completedMask S 1 I J=highExclusion S hS (I*J^3) := by
    simp only [completedMask,one_dvd,true_and]
    rfl
  unfold highIdealMask
  rw [he,map_mul,highExclusion_cube]
  rfl

lemma highIdealMask_unmarked_one (S : Finset Id) (hS : ∀P∈S,Prime P) :
    highIdealMask S 1 1 1 1 1=1 := by
  rw [highIdealMask_unmarked S hS]
  simp only [map_one,one_mul]

lemma highIdealMask_unmarked_mul (S : Finset Id) (hS : ∀P∈S,Prime P)
    (a b : HighIdeal) :
    highIdealMask S 1 (a.1.1*b.1.1) (a.1.2*b.1.2) (a.2.1*b.2.1) (a.2.2*b.2.2)=
      highIdealMask S 1 a.1.1 a.1.2 a.2.1 a.2.2 * highIdealMask S 1 b.1.1 b.1.2 b.2.1 b.2.2 := by
  simp only [highIdealMask_unmarked S hS,map_mul]
  ring

theorem excludedIdealHighSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      markedIdealHighSummand S 1 η 1 x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (markedIdealHighSeries S 1 η 1 x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=>markedIdealHighSummand S 1 η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · simp only [Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
      highIdealMask_unmarked_one S hS,bareIdealHighSummand_one,one_mul]
  · intro a b hc
    simp only [Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
      highIdealMask_unmarked_mul S hS a b,
      bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hc]
    ring
  · intro a ha
    have hh : bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hs := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (markedIdealHighSummand_summable S 1 η 1 x w z hx hw hz).norm

end SevenEighths.ProbePhysical
end

end OAI

end Source1054

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighEulerLocal.lean; sha256: 0cb562c7600fc508281e4b5bf04c8b06797f1e46d17a4f80e125f1440778fb18 -/
section Source1055
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma highPrimeTerm_summable_norm (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    Summable (fun b : HighValuation=>‖highPrimeTerm η x w z P b‖) := by
  have hs := (highValuationTerm_summable_norm η x w z hx hw hz).comp_injective
    (Finsupp.single_injective P)
  simpa only [Function.comp_def,highValuationTerm_eq_prod,
    Finsupp.prod_single_index (highPrimeTerm_zero η x w z P)] using hs

lemma highPrimeTerm_zero_of_two_le (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (e l k m : ℕ) (he : 2≤e) :
    highPrimeTerm η x w z P ((e,l),(k,m))=0 := by
  by_contra hn
  have hs := bareIdealHighSummand_support η 1 x w z (P.val^e) (P.val^l) (P.val^k) (P.val^m) hn
  have hc := hs.1.eq_zero_or_one_of_pow_of_not_isUnit P.property.not_isUnit
  omega

theorem highPrimeTerm_tsum_eq_localFactor (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,highPrimeTerm η x w z P b)=
      idealHighLocalFactor η P.val x w z := by
  have hs := (highPrimeTerm_summable_norm η x w z hx hw hz P).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) :
      (∑' b : ℕ×ℕ, highPrimeTerm η x w z P ((e,l),b))=
        ∑' k,∑' m,highPrimeTerm η x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [highPrimeTerm_zero_of_two_le η x w z P e _ _ _ hh,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

theorem bareIdealHighSeries_hasProd_localFactor (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>idealHighLocalFactor η P.val x w z)
      (bareIdealHighSeries η 1 x w z) := by
  have h := bareIdealHighSeries_hasProd η x w z hx hw hz
  simpa only [highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz] using h

end SevenEighths.ProbePhysical
end

end OAI

end Source1055

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighExcludedLocal.lean; sha256: 7351f907db305282a1ee41ce6c4ff427115535d30cce89552201c3d18fdc89ec -/
section Source1056
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma highExclusion_prime (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    highExclusion S hS P.val=if P.val∈S then 0 else 1 := by
  change (if ∀Q∈S,¬Q∣P.val then (1:ℂ) else 0)=_
  by_cases hP : P.val∈S
  · rw [ite_eq_right (fun h=>h P.val hP (dvd_refl _)),ite_eq_left hP]
  · have houtside : ∀Q∈S,¬Q∣P.val := by
      intro Q hQ hd
      have hn : (⟨Q,hS Q hQ⟩ : PrimeIdeal)≠P := by
        intro hh
        exact hP ((congrArg Subtype.val hh) ▸ hQ)
      exact (hS Q hQ).not_isUnit ((primeIdeal_coprime ⟨Q,hS Q hQ⟩ P hn).isUnit_of_dvd hd)
    rw [ite_eq_left houtside,ite_eq_right hP]

lemma highIdealMask_prime_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (P : PrimeIdeal) (hP : P.val∉S) (b : HighValuation) :
    highIdealMask S 1 (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=1 := by
  simp only [highIdealMask_unmarked S hS,map_pow,highExclusion_prime S hS P,
    ite_eq_right hP,one_pow,one_mul]

lemma highIdealMask_prime_inside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (P : PrimeIdeal) (hP : P.val∈S) (b : HighValuation) :
    highIdealMask S 1 (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=
      if b=0 then 1 else 0 := by
  rcases b with ⟨⟨e,l⟩,k,m⟩
  simp only [highIdealMask_unmarked S hS,map_pow,highExclusion_prime S hS P,ite_eq_left hP]
  by_cases he : e=0 <;> by_cases hl : l=0 <;> by_cases hk : k=0 <;> by_cases hm : m=0 <;>
    simp [he,hl,hk,hm,Prod.mk_eq_zero]

theorem excludedHighLocalFactor (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,markedIdealHighSummand S 1 η 1 x w z
      (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)) =
      if P.val∈S then 1 else idealHighLocalFactor η P.val x w z := by
  by_cases hP : P.val∈S
  · rw [ite_eq_left hP]
    have he (b : HighValuation) : markedIdealHighSummand S 1 η 1 x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=if b=0 then 1 else 0 := by
      rw [markedIdealHighSummand,highIdealMask_prime_inside S hS P hP b]
      by_cases hb : b=0
      · subst b
        simp only [Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_one,mul_one]
      · simp only [ite_eq_right hb,zero_mul]
    simp only [he,tsum_ite_eq]
  · rw [ite_eq_right hP]
    simp only [markedIdealHighSummand,highIdealMask_prime_outside S hS P hP,one_mul]
    exact highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz P

theorem excludedIdealHighSeries_hasProd_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealHighLocalFactor η P.val.val x w z)
      (markedIdealHighSeries S 1 η 1 x w z) := by
  have h := excludedIdealHighSeries_hasProd S hS η x w z hx hw hz
  simp only [excludedHighLocalFactor S hS η x w z hx hw hz] at h
  apply (hasProd_subtype_iff_mulIndicator
    (s:={P : PrimeIdeal | P.val∉S})
    (f:=fun P : PrimeIdeal=>idealHighLocalFactor η P.val x w z)).mpr
  convert h using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

end SevenEighths.ProbePhysical
end

end OAI

end Source1056

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsExcluded.lean; sha256: 682547640246401c505db0cefde78fc7b0ab2fcd0b846ae4516350e9904863ef -/
section Source1057
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem excludedIdealHighSeries_row_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      markedIdealHighSummand S 1 η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (markedIdealHighSeries S 1 η u x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=>markedIdealHighSummand S 1 η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · simp only [Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
      highIdealMask_unmarked_one S hS,bareIdealHighSummand_row_one,one_mul]
  · intro a b hc
    simp only [Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
      highIdealMask_unmarked_mul S hS a b,
      bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc]
    ring
  · intro a ha
    have hh : bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hs := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (markedIdealHighSummand_summable S 1 η u x w z hx hw hz).norm

end SevenEighths.ProbePhysical
end

end OAI

end Source1057

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsLocal.lean; sha256: 2fc6b3ae70dc532defc6344ca77dbe156f129d65a14ae8f7862b26d5603382c0 -/
section Source1058
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def rowHighPrimeTerm (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  bareIdealHighSummand η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)

def idealRowHighLocalFactor (η : HeckeFamily.Character) (u : O) (P : Id) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l : ℕ, ∑' k : ℕ, ∑' m : ℕ,
    bareIdealHighSummand η u x w z (P^e.val) (P^l) (P^k) (P^m)

lemma rowHighPrimeTerm_summable_norm (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    Summable (fun b : HighValuation=>‖rowHighPrimeTerm η u x w z P b‖) := by
  have hs := ((bareIdealHighSummand_summable η u x w z hx hw hz).norm.comp_injective
    highIdeals_injective).comp_injective (Finsupp.single_injective P)
  simpa only [Function.comp_def,highIdeals_single,rowHighPrimeTerm] using hs

lemma rowHighPrimeTerm_zero_of_two_le (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (e l k m : ℕ) (he : 2≤e) :
    rowHighPrimeTerm η u x w z P ((e,l),(k,m))=0 := by
  by_contra hn
  have hs := bareIdealHighSummand_support η u x w z (P.val^e) (P.val^l) (P.val^k) (P.val^m) hn
  have hc := hs.1.eq_zero_or_one_of_pow_of_not_isUnit P.property.not_isUnit
  omega

theorem rowHighPrimeTerm_tsum_eq_localFactor (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,rowHighPrimeTerm η u x w z P b)=
      idealRowHighLocalFactor η u P.val x w z := by
  have hs := (rowHighPrimeTerm_summable_norm η u x w z hx hw hz P).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) :
      (∑' b : ℕ×ℕ, rowHighPrimeTerm η u x w z P ((e,l),b))=
        ∑' k,∑' m,rowHighPrimeTerm η u x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [rowHighPrimeTerm_zero_of_two_le η u x w z P e _ _ _ hh,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

theorem bareIdealHighSeries_row_hasProd_localFactor (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>idealRowHighLocalFactor η u P.val x w z)
      (bareIdealHighSeries η u x w z) := by
  have h := bareIdealHighSeries_row_hasProd η u x w z hx hw hz
  change HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,rowHighPrimeTerm η u x w z P b) _ at h
  simpa only [rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz] using h

theorem excludedRowHighLocalFactor (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,markedIdealHighSummand S 1 η u x w z
      (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)) =
      if P.val∈S then 1 else idealRowHighLocalFactor η u P.val x w z := by
  by_cases hP : P.val∈S
  · rw [ite_eq_left hP]
    have he (b : HighValuation) : markedIdealHighSummand S 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=if b=0 then 1 else 0 := by
      rw [markedIdealHighSummand,highIdealMask_prime_inside S hS P hP b]
      by_cases hb : b=0
      · subst b
        simp only [Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_row_one,mul_one]
      · simp only [ite_eq_right hb,zero_mul]
    simp only [he,tsum_ite_eq]
  · rw [ite_eq_right hP]
    simp only [markedIdealHighSummand,highIdealMask_prime_outside S hS P hP,one_mul]
    exact rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz P

theorem excludedIdealHighSeries_row_hasProd_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealRowHighLocalFactor η u P.val.val x w z)
      (markedIdealHighSeries S 1 η u x w z) := by
  have h := excludedIdealHighSeries_row_hasProd S hS η u x w z hx hw hz
  simp only [excludedRowHighLocalFactor S hS η u x w z hx hw hz] at h
  apply (hasProd_subtype_iff_mulIndicator
    (s:={P : PrimeIdeal | P.val∉S})
    (f:=fun P : PrimeIdeal=>idealRowHighLocalFactor η u P.val x w z)).mpr
  convert h using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

end SevenEighths.ProbePhysical
end

end OAI

end Source1058

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighRowsPrime.lean; sha256: 512d888e7a3d039b7d715d62e468f636b5cfafaa4595bd25234c5277dbf94c0a -/
section Source1059
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

def sourceRowTerm (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (eta a rho x w z : ℂ) (j e l k m : ℕ) : ℂ :=
  (rho^k/rho^(e+3*l))*sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
    (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) x w z
    (sourceScalar p hp hg (e+3*l) k (j+6*m)) e l k m

theorem sourceRowTerm_pos (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (eta a rho x w z : ℂ) (j e l k m : ℕ)
    (ht : e+3*l≠0) :
    sourceRowTerm p hp hg eta a rho x w z j e l k m=
      rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        rho j e l k m := by
  unfold sourceRowTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [rowMarkedTerm,rowWeightedScalar,sourceScalar,ite_eq_right ht,coordV,Complex.ofReal_natCast]

end SevenEighths.ProbeEuler
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem bareSourceCoefficient_unit_frequency (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) (b*H)=
      ((idealRowHom b (Ideal.span {A}))⁻¹*idealRowHom b (Ideal.span {s}))*
        bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) H := by
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [bareCongruenceCoefficient_unit_frequency A s hA hs b H hcop]
  ring

theorem bareSourceCoefficient_row_prime_formula (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (e l k j : ℕ) (he : e≤1) (hI : primaryGenerator (Ideal.span {p^e})≠0) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (b*p^j)=
    ((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^(e+3*l)) *
    ((-1:ℂ)^e * ((localGamma p hp.ne_zero hg 1)⁻¹)^e * (targetMonoid η p)^e *
      (star (FiniteGaussPhase.angularFactor p)^3 * (targetMonoid η p)^3 *
        star (localGamma p hp.ne_zero hg 3))^l *
      (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j) := by
  rw [bareSourceCoefficient_unit_frequency η _ hI _ _
    (supported_element_power p hs _) (supported_element_power p hs _) b _
    (hb.pow_right.mul_right hb.pow_right),
    bareSourceCoefficient_prime_formula η p hp hg hchar hprimary hs e l k j he hI,
    idealRowHom_prime_power_value p b hg,idealRowHom_prime_power_value p b hg]
  simp only [div_eq_mul_inv]
  ac_rfl

theorem bareSourceCoefficient_row_weighted_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p) (j e l k m : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) (x w z : ℂ) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (b*p^(j+6*m)) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
    sourceRowTerm p hp hg (targetMonoid η p) (actualACube η p)
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x w z j e l k m := by
  rw [bareSourceCoefficient_row_prime_formula η p hp hg hchar hprimary hs b hb e l k (j+6*m) he hI]
  unfold sourceRowTerm sourceWeightedScalar
  simp only [zpow_neg,zpow_natCast,←inv_pow,Complex.ofReal_natCast]
  have hpdiag := source_signed_phase
    (actualACube η p*star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) (actualSextic_neg_one_sq _ hg) e l k
  simp only [localCubePhase] at hpdiag
  have ha : actualACube η p=
      star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3 := rfl
  rw [ha] at hpdiag ⊢
  linear_combination -((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^(e+3*l)) *
    ((-1:ℂ)^e*((localGamma p hp.ne_zero hg 1)⁻¹)^e*(targetMonoid η p)^e) *
    sourceScalar p hp hg (e+3*l) k (j+6*m) *
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) * hpdiag

theorem bareIdealHighCoefficient_row_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (u : O) (e l k m : ℕ) (he : e≤1) :
    bareIdealHighCoefficient η u ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    bareSourceCoefficient η (Ideal.span {p^e})
      (by rw [← Ideal.span_singleton_pow,primaryGenerator_prime_power p hp.ne_zero hprimary e];
          exact pow_ne_zero _ hp.ne_zero)
      (p^(e+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (u*p^(6*m)) := by
  have hguard : Squarefree ((Ideal.span {p})^e) ∧ Supported ((Ideal.span {p})^e) ∧
      Supported ((Ideal.span {p})^l) ∧ Supported ((Ideal.span {p})^k) ∧ Supported ((Ideal.span {p})^m) :=
    ⟨prime_power_small_squarefree p hp e he,supported_pow hs e,supported_pow hs l,supported_pow hs k,supported_pow hs m⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hguard]
  simp only [primaryGenerator_prime_power p hp.ne_zero hprimary]
  have hA : p^e*(p^l)^3=p^(e+3*l) := by rw [←pow_mul,Nat.mul_comm l 3,←pow_add]
  have hH : (p^m)^6=p^(6*m) := by rw [←pow_mul,Nat.mul_comm m 6]
  simp only [hA,hH,Ideal.span_singleton_pow]

theorem bareIdealHighSummand_row_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (j e l k m : ℕ) (he : e≤1) (x w z : ℂ) :
    bareIdealHighSummand η (b*p^j) x w z ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m)=
      sourceRowTerm p hp hg (targetMonoid η p) (actualACube η p)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x w z j e l k m := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_row_at_prime η p hp hprimary hs (b*p^j) e l k m he]
  rw [show b*p^j*p^(6*m)=b*p^(j+6*m) by rw [pow_add]; ring]
  have hw := prime_spectral_weights p hp.ne_zero e l k m x w z
  simp only [mul_assoc] at hw ⊢
  rw [hw]
  simpa only [mul_assoc] using
    bareSourceCoefficient_row_weighted_prime η p hp hg hchar hprimary hs b hb j e l k m he _ x w z

theorem idealRowHighLocalFactor_eq_source (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p) (j : ℕ) (x w z : ℂ) :
    idealRowHighLocalFactor η (b*p^j) (Ideal.span {p}) x w z=
      ∑ e : Fin 2,∑' l,∑' k,∑' m,sourceRowTerm p hp hg (targetMonoid η p) (actualACube η p)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x w z j e.val l k m := by
  unfold idealRowHighLocalFactor
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact bareIdealHighSummand_row_at_prime η p hp hg hchar hprimary hs b hb j e.val l k m (by omega) x w z

end SevenEighths.ProbePhysical
end

end OAI

end Source1059

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/Valuation.lean; sha256: 0c57756bea7fad7ffc3201f6593bc119646fc1e1a560c0bf4afa8d621ffc57e4 -/
section Source1060
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification UniqueFactorizationMonoid
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def unitPart (u : FreeRow) (p : O) (hp : Prime p) : O :=
  Classical.choose ((FiniteMultiplicity.of_prime_left hp u.property.1).exists_eq_pow_mul_and_not_dvd)

theorem unitPart_spec (u : FreeRow) (p : O) (hp : Prime p) :
    u.val=p^(multiplicity p u.val)*unitPart u p hp ∧ ¬p∣unitPart u p hp :=
  Classical.choose_spec ((FiniteMultiplicity.of_prime_left hp u.property.1).exists_eq_pow_mul_and_not_dvd)

theorem unitPart_coprime (u : FreeRow) (p : O) (hp : Prime p) : IsCoprime (unitPart u p hp) p :=
  (hp.irreducible.coprime_iff_not_dvd.mpr (unitPart_spec u p hp).2).symm

theorem unitPart_ne_zero (u : FreeRow) (p : O) (hp : Prime p) : unitPart u p hp≠0 := by
  intro he
  have hu := (unitPart_spec u p hp).1
  rw [he,mul_zero] at hu
  exact u.property.1 hu

theorem multiplicity_lt_six (u : FreeRow) (p : O) (hp : Prime p) : multiplicity p u.val<6 := by
  let P : Ideal O := Ideal.span {p}
  have hP0 : P≠0 := Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  have hP : Prime P := Ideal.prime_of_isPrime hP0 (Ideal.isPrime_span_singleton_of_prime hp)
  have hb : (Ideal.span {unitPart u p hp}:Ideal O)≠0 :=
    Ideal.span_singleton_eq_bot.not.mpr (unitPart_ne_zero u p hp)
  have he : (Ideal.span {u.val}:Ideal O)=P^(multiplicity p u.val)*Ideal.span {unitPart u p hp} := by
    conv_lhs => rw [(unitPart_spec u p hp).1]
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow]
  have hf := u.property.2 P
  rw [he,normalizedFactors_mul (pow_ne_zero _ hP0) hb,normalizedFactors_pow,
    normalizedFactors_irreducible hP.irreducible] at hf
  simp only [normalize_eq,Multiset.count_add,Multiset.count_nsmul,
    Multiset.count_singleton_self,mul_one] at hf
  omega

theorem canonical_decomposition (u : FreeRow) (p : O) (hp : Prime p) :
    u.val=unitPart u p hp*p^(multiplicity p u.val) ∧
      IsCoprime (unitPart u p hp) p ∧ multiplicity p u.val<6 := by
  exact ⟨(unitPart_spec u p hp).1.trans (mul_comm _ _),unitPart_coprime u p hp,
    multiplicity_lt_six u p hp⟩

theorem idealRowHighLocalFactor_canonical (η : Character) (u : FreeRow) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hprimary : ConcretePrimeRowBridge.goodLambda^2∣p-1)
    (hs : CanonicalQuadraticSieve.Supported (Ideal.span {p})) (x w z : ℂ) :
    ProbePhysical.idealRowHighLocalFactor η u.val (Ideal.span {p}) x w z=
      ∑ e : Fin 2,∑' l,∑' k,∑' m,
        ProbeEuler.sourceRowTerm p hp hg (ProbeRow.targetMonoid η p) (ProbeEuler.actualACube η p)
          (CompletedGauss.actualSextic (Ideal.span {p}) hg
            (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val) e.val l k m := by
  conv_lhs => rw [(canonical_decomposition u p hp).1]
  exact ProbePhysical.idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs
    (unitPart u p hp) (unitPart_coprime u p hp) (multiplicity p u.val) x w z

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1060

/- Original source: OAI/NumberTheory/DirichletL/Detector/FixedEuler.lean; sha256: 0e463f91308f01561e4c8dd1d71275e67f18009389f6e0a17d86187f994c807b -/
section Source1061
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic HeckeFamily
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma fixedPrimeProduct_ne_zero (S : Finset Id) (hS : ∀P∈S,Prime P) :
    (∏P∈S,P)≠0 := Finset.prod_ne_zero_iff.mpr (fun P hP=>(hS P hP).ne_zero)

def fixedSourcePrincipal (S : Finset Id) (hS : ∀P∈S,Prime P) : Character :=
  letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  HeckeRayFamily.character (∏P∈S,P) 1

lemma prime_coprime_fixedProduct (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    IsCoprime P.val (∏Q∈S,Q) ↔ P.val∉S := by
  rw [IsCoprime.prod_right_iff]
  constructor
  · intro h hP
    exact P.property.not_isUnit (isCoprime_self.mp (h P.val hP))
  · intro h Q hQ
    exact primeIdeal_coprime P ⟨Q,hS Q hQ⟩ (fun he=>h ((congrArg Subtype.val he).symm ▸ hQ))

lemma fixedSourcePrincipal_prime (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    idealCoeff (fixedSourcePrincipal S hS) P.val=if P.val∈S then 0 else 1 := by
  unfold fixedSourcePrincipal
  rw [HeckeRayFamily.idealCoeff_character,RayOrthogonality.idealCharacter_one]
  change (if P.val=0 then (0:ℂ) else if IsCoprime P.val (∏Q∈S,Q) then 1 else 0)=_
  simp only [P.property.ne_zero,ite_false,prime_coprime_fixedProduct S hS P]
  split_ifs <;> simp_all

lemma excludedTarget_prime (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    idealCoeff (η.excludePrimes S hS) P.val=if P.val∈S then 0 else idealCoeff η P.val := by
  rw [idealCoeff_excludePrimes]
  have he : (∀Q∈S,IsCoprime P.val Q) ↔ P.val∉S := by
    rw [←IsCoprime.prod_right_iff]
    exact prime_coprime_fixedProduct S hS P
  simp only [he]
  split_ifs <;> simp_all

theorem LFunction_hasProd_outside (χ : Character) (S : Finset Id) (a : Id→ℂ)
    (ha : ∀P : PrimeIdeal,idealCoeff χ P.val=if P.val∈S then 0 else a P.val)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-a P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹) (LFunction χ s) := by
  have h := IdealEuler.euler_hasProd (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs
  rw [←LFunction_eq_series χ hs] at h
  have he (P : PrimeIdeal) : (1-IdealEuler.weighted (idealCoeff χ) s P.val)⁻¹=
      if P.val∈S then 1 else (1-a P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹ := by
    change (1-idealCoeff χ P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹=_
    rw [ha]
    split_ifs <;> simp only [zero_mul,sub_zero,inv_one]
  simp only [he] at h
  apply (hasProd_subtype_iff_mulIndicator (s:={P : PrimeIdeal|P.val∉S})
    (f:=fun P : PrimeIdeal=>(1-a P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹)).mpr
  convert h using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

theorem fixedSourcePrincipal_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-CubicEisenstein.fullIdealWeight s P.val.val)⁻¹) (LFunction (fixedSourcePrincipal S hS) s) := by
  simpa only [one_mul] using
    LFunction_hasProd_outside (fixedSourcePrincipal S hS) S (fun _=>1) (fixedSourcePrincipal_prime S hS) s hs

theorem excludedTarget_hasProd (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-idealCoeff η P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction (η.excludePrimes S hS) s) :=
  LFunction_hasProd_outside _ S (idealCoeff η) (excludedTarget_prime η S hS) s hs

end SevenEighths.ProbePhysical
end

end OAI

end Source1061

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/Character.lean; sha256: 18c683744028feae68304ad0e35349983a48a63cc607ea0f9bb8aa47a07a3ba5 -/
section Source1062
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve ProbePhysical
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def rowMaskElement : O := 2*λ₀

theorem rowMaskElement_ne_zero : rowMaskElement≠0 :=
  mul_ne_zero (by norm_num) PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero

def rawRow (u : FreeRow) : Character := Classical.choose
  (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
    rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))

theorem rawRow_coeff (u : FreeRow) (I : Ideal O) :
    idealCoeff (rawRow u) I=idealCoeff (fixedSourcePrincipal ∅ (by simp)) I*
      idealRowHom (rowMaskElement^6*u.val) I := by
  have he := (Classical.choose_spec
    (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
      rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2
  simpa only [one_pow,mul_one] using idealCoeff_eq_row _ (rawRow u) rowMaskElement 1 u.val he I

theorem outside_good_coprime (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (P : PrimeIdeal) (hP : P.val∉S) :
    λ₀∉P.val ∧ IsCoprime P.val (Ideal.span {rowMaskElement}) := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have hn : P.val∉fixedBadPrimes := fun hh => hP (hbad hh)
  have hg := (prime_good_iff_not_bad P.val).mpr hn
  refine ⟨hg.1,?_⟩
  have hc := (prime_coprime_fixedProduct S hS P).mpr hP
  rw [IsCoprime.prod_right_iff] at hc
  have hLam : Ideal.span {λ₀}∈S := hbad (Finset.mem_insert_self _ _)
  have h2 : Ideal.span {(2 : O)}∈S := hbad (by simp [fixedBadPrimes])
  unfold rowMaskElement
  rw [←Ideal.span_singleton_mul_span_singleton]
  exact (hc _ h2).mul_right (hc _ hLam)

theorem rawRow_prime_outside (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (P : PrimeIdeal) (hP : P.val∉S) :
    idealCoeff (rawRow u) P.val=idealRowHom u.val P.val := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  obtain ⟨hg,hc⟩ := outside_good_coprime S hS hbad P hP
  rw [rawRow_coeff,fixedSourcePrincipal_prime]
  rw [ite_eq_right (by simp),one_mul]
  rw [idealRowHom_argument_mul,idealRowHom_prime_sixth_mask rowMaskElement P.val hg,
    ite_eq_left hc,one_mul]

def rowCharacter (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) : Character :=
  (rawRow u).excludePrimes S hS

def sourceRowCoeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) : Ideal O→*₀ℂ where
  toFun I := highExclusion S hS I*idealRowHom u.val I
  map_zero' := by rw [(idealRowHom u.val).map_zero, mul_zero]
  map_one' := by rw [map_one,map_one,mul_one]
  map_mul' I J := by simp only [map_mul]; ring

theorem hom_eq_of_primes (f g : Ideal O→*₀ℂ) (h : ∀P : PrimeIdeal,f P.val=g P.val) : f=g := by
  ext I
  by_cases hI : I=0
  · subst I; rw [map_zero,map_zero]
  have hf := congrArg (fun F : Ideal O→*₀ℂ => F I) (IdealEuler.primeValueHom_eq f)
  have hg := congrArg (fun F : Ideal O→*₀ℂ => F I) (IdealEuler.primeValueHom_eq g)
  rw [←hf,←hg]
  change (if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map f).prod)=
    (if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map g).prod)
  rw [ite_eq_right hI,ite_eq_right hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  exact h ⟨P,UniqueFactorizationMonoid.prime_of_normalized_factor P hP⟩

theorem rowCharacter_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (I : Ideal O) :
    idealCoeff (rowCharacter S hS u) I=highExclusion S hS I*idealRowHom u.val I := by
  have he : idealCoeff (rowCharacter S hS u)=sourceRowCoeff S hS u := by
    apply hom_eq_of_primes
    intro P
    change idealCoeff ((rawRow u).excludePrimes S hS) P.val=
      highExclusion S hS P.val*idealRowHom u.val P.val
    rw [excludedTarget_prime,highExclusion_prime]
    by_cases hP : P.val∈S
    · simp only [ite_eq_left hP,zero_mul]
    · simp only [ite_eq_right hP,one_mul]
      exact rawRow_prime_outside S hS hbad u P hP
  exact congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem target_inverseRow_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (P : PrimeIdeal) :
    idealCoeff ((η.product (rawRow u).inverse).excludePrimes S hS) P.val=
      if P.val∈S then 0 else idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val) := by
  rw [excludedTarget_prime,idealCoeff_product,idealCoeff_inverse_conj]
  by_cases hP : P.val∈S
  · simp only [ite_eq_left hP]
  · rw [ite_eq_right hP,ite_eq_right hP,rawRow_prime_outside S hS hbad u P hP]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1062

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/Euler.lean; sha256: a93ae1bc03e6175d2bb52bb5c0c2b9a13a3def143e955e79e9d311eecc54c7eb -/
section Source1063
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def targetRow (η : Character) (u : FreeRow) : Character := η.product (rawRow u).inverse

theorem rowCharacter_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>
      (1-idealRowHom u.val P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction (rowCharacter S hS u) s) := by
  apply LFunction_hasProd_outside (rowCharacter S hS u) S (idealRowHom u.val) _ s hs
  intro P
  rw [rowCharacter_coeff S hS hbad,highExclusion_prime]
  split_ifs <;> simp only [zero_mul,one_mul]

theorem targetRow_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>
      (1-idealCoeff η P.val.val*starRingEnd ℂ (idealRowHom u.val P.val.val)*
        CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction ((targetRow η u).excludePrimes S hS) s) :=
  LFunction_hasProd_outside _ S (fun P => idealCoeff η P*starRingEnd ℂ (idealRowHom u.val P))
    (target_inverseRow_coeff S hS hbad η u) s hs

def localCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  idealRowHighLocalFactor η u.val P.val x w z *
    (1-CubicEisenstein.fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*CubicEisenstein.fullIdealWeight w P.val)/
    (1-idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val)*CubicEisenstein.fullIdealWeight x P.val)

def globalCorrection (S : Finset (Ideal O)) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val∉S},localCorrection η u P.val x w z

theorem localCorrection_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>localCorrection η u P.val x w z)
      (markedIdealHighSeries S 1 η u.val x w z *
        (LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹ * (LFunction (rowCharacter S hS u) w)⁻¹ *
          LFunction ((targetRow η u).excludePrimes S hS) x) := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re]; linarith
  have hF := excludedIdealHighSeries_row_hasProd_outside S hS η u.val x w z hx hw hz
  have hZ := (fixedSourcePrincipal_hasProd S hS (6*z) hz1).inv₀
    (LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1)
  have hW := (rowCharacter_hasProd S hS hbad u w hw1).inv₀
    (LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1)
  have hD := targetRow_hasProd S hS hbad η u x hx1
  have he := ((hF.mul hZ).mul hW).mul hD
  simpa only [localCorrection,inv_inv,div_eq_mul_inv] using he

theorem globalCorrection_multipliable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S} =>localCorrection η u P.val x w z) :=
  (localCorrection_hasProd S hS hbad η u x w z hx hw hz).multipliable

theorem high_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η u.val x w z=
      LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (rowCharacter S hS u) w /
        LFunction ((targetRow η u).excludePrimes S hS) x * globalCorrection S η u x w z := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re]; linarith
  have hZ := LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := LFunction_ne_zero_of_one_lt_re ((targetRow η u).excludePrimes S hS) hx1
  rw [globalCorrection,(localCorrection_hasProd S hS hbad η u x w z hx hw hz).tprod_eq]
  field_simp

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1063

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/Moments.lean; sha256: 42f8abfdd47817cedba7a079f6338efe9da4cb68e9189d86d49ef6f78a40e9f7 -/
section Source1064
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure CanonicalRowCompletion
open ProbePhysical

def momentData (η : Character) : RowData where
  η := η
  m := rowMaskElement
  f := 1
  m_ne_zero := rowMaskElement_ne_zero
  f_ne_zero := one_ne_zero
  lambda_dvd := dvd_mul_left _ _
  two_dvd := dvd_mul_right _ _

def momentElement (u : FreeRow) : NonzeroElement := ⟨u.val,u.property.1⟩

theorem momentData_coeff (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((momentData η).character (momentElement u)) I=
      idealCoeff η I*idealRowHom (rowMaskElement^6*u.val) I := by
  simpa only [momentData,momentElement,one_pow,mul_one] using
    idealCoeff_eq_row η ((momentData η).character (momentElement u)) rowMaskElement 1 u.val
      ((momentData η).character_spec (momentElement u)) I

theorem momentData_prime_outside (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (P : PrimeIdeal) (hP : P.val∉S) :
    idealCoeff ((momentData η).character (momentElement u)) P.val=
      idealCoeff η P.val*idealRowHom u.val P.val := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  obtain ⟨hg,hc⟩ := outside_good_coprime S hS hbad P hP
  rw [momentData_coeff,idealRowHom_argument_mul,
    idealRowHom_prime_sixth_mask rowMaskElement P.val hg,ite_eq_left hc,one_mul]

theorem numerator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow) (I : Ideal O) :
    idealCoeff (rowCharacter S hS u) I=
      idealCoeff ((momentData (fixedSourcePrincipal S hS)).character (momentElement u)) I := by
  have he : idealCoeff (rowCharacter S hS u)=
      idealCoeff ((momentData (fixedSourcePrincipal S hS)).character (momentElement u)) := by
    apply hom_eq_of_primes
    intro P
    change idealCoeff ((rawRow u).excludePrimes S hS) P.val=_
    rw [excludedTarget_prime]
    by_cases hP : P.val∈S
    · rw [ite_eq_left hP,momentData_coeff,fixedSourcePrincipal_prime,ite_eq_left hP,zero_mul]
    · rw [ite_eq_right hP,rawRow_prime_outside S hS hbad u P hP,
        momentData_prime_outside S hS hbad _ u P hP,
        fixedSourcePrincipal_prime,ite_eq_right hP,one_mul]
  exact congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem denominator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((targetRow η u).excludePrimes S hS) I=
      conj (idealCoeff ((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)) I) := by
  have he : idealCoeff ((targetRow η u).excludePrimes S hS)=
      idealCoeff (((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)).inverse) := by
    apply hom_eq_of_primes
    intro P
    rw [idealCoeff_inverse_conj]
    change idealCoeff ((η.product (rawRow u).inverse).excludePrimes S hS) P.val=_
    rw [target_inverseRow_coeff S hS hbad]
    by_cases hP : P.val∈S
    · rw [ite_eq_left hP,momentData_coeff,excludedTarget_prime,ite_eq_left hP,zero_mul,map_zero]
    · rw [ite_eq_right hP,momentData_prime_outside S hS hbad _ u P hP,
        excludedTarget_prime,ite_eq_right hP,idealCoeff_inverse_conj,map_mul]
      simp only [starRingEnd_self_apply]
  simpa only [idealCoeff_inverse_conj] using congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem numerator_moment_polynomial (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    HeckeDyadic.polynomial (rowCharacter S hS u) inv W D σ freq=
      HeckeDyadic.polynomial ((momentData (fixedSourcePrincipal S hS)).character
        (momentElement u)) inv W D σ freq :=
  HeckeDetectorCoefficientTransfer.polynomial_eq_of_idealCoeff _ _
    (numerator_moment_coeff S hS hbad u) inv W D σ freq

theorem denominator_moment_norm (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖HeckeDyadic.polynomial ((targetRow η u).excludePrimes S hS) inv W D σ freq‖=
      ‖HeckeDyadic.polynomial ((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)) inv (fun x=>conj (W x)) D σ (-freq)‖ :=
  HeckeDetectorCoefficientTransfer.norm_of_oriented_coefficients _ _ true
    (denominator_moment_coeff S hS hbad η u) inv W D σ freq hD

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1064

/- Original source: OAI/NumberTheory/DirichletL/Detector/EulerMarked.lean; sha256: 6dd8d439e24b3cf7058756b2ce3189ba5bdc8a021a14b4b9b0323d4ddc5f2023 -/
section Source1065
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeEulerFinsupp
variable {α β : Type*} [AddCommMonoid β]

def markedArray (T : Finset α) (m f : α→β→ℂ) (v : α→₀β) : ℂ :=
  (∏a∈T,m a (v a))*v.prod f

def markedLocal (T : Finset α) (m f : α→β→ℂ) (a : α) (b : β) : ℂ :=
  (if a∈T then m a b else 1)*f a b

lemma markedArray_finite (T S : Finset α) (hTS : T⊆S) (m f : α→β→ℂ)
    (h0 : ∀a,f a 0=1) (v : α→₀β) (hv : v.support⊆S) :
    markedArray T m f v=∏a∈S,markedLocal T m f a (v a) := by
  simp only [markedArray,markedLocal,Finset.prod_mul_distrib]
  congr 1
  · symm
    rw [←Finset.prod_subset hTS]
    · apply Finset.prod_congr rfl
      intro a ha
      simp only [ite_eq_left ha]
    · intro a ha hna
      simp only [ite_eq_right hna]
  · exact Finsupp.prod_of_support_subset v hv _ (fun a _=>h0 a)

lemma markedArray_norm_le (T : Finset α) (m f : α→β→ℂ)
    (hm : ∀a∈T,∀b,‖m a b‖≤1) (v : α→₀β) :
    ‖markedArray T m f v‖≤‖v.prod f‖ := by
  rw [markedArray,norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun a ha=>hm a ha _)

lemma marked_finiteEuler (T S : Finset α) (hTS : T⊆S) (m f : α→β→ℂ)
    (h0 : ∀a,f a 0=1) (hf : ∀a,Summable (fun b=>‖f a b‖))
    (hm : ∀a∈T,∀b,‖m a b‖≤1) :
    (∑'v : {v : α→₀β // (v.support:Set α)⊆S},markedArray T m f v.val)=
      ∏a∈S,∑'b,markedLocal T m f a b := by
  let e : {v : α→₀β // (v.support:Set α)⊆S} ≃ (S→β) :=
    (Finsupp.restrictSupportEquiv (S:Set α) β).trans Finsupp.equivFunOnFinite
  have he (v : {v : α→₀β // (v.support:Set α)⊆S}) :
      markedArray T m f v.val=∏a:S,markedLocal T m f a.val (e v a) := by
    rw [markedArray_finite T S hTS m f h0 v.val v.property]
    exact (Finset.prod_coe_sort S _).symm
  have hg (a : α) : Summable (fun b=>‖markedLocal T m f a b‖) := by
    apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (hf a)
    intro b
    rw [markedLocal,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    split_ifs with ha
    · exact hm a ha b
    · simp
  simp_rw [he]
  rw [e.tsum_eq (fun v : S→β=>∏a:S,markedLocal T m f a.val (v a))]
  rw [(finitePi (fun a:S=>markedLocal T m f a.val) (fun a=>hg a.val)).2]
  exact Finset.prod_coe_sort S (fun a=>∑'b,markedLocal T m f a b)

theorem marked_hasProd (T : Finset α) (m f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hs : Summable (fun v : α→₀β=>‖v.prod f‖))
    (hm : ∀a∈T,∀b,‖m a b‖≤1) :
    HasProd (fun a=>∑'b,markedLocal T m f a b) (∑'v : α→₀β,markedArray T m f v) := by
  have hf (a : α) : Summable (fun b=>‖f a b‖) := by
    have hh := hs.comp_injective (Finsupp.single_injective a)
    simpa only [Function.comp_def,Finsupp.prod_single_index (h0 a)] using hh
  have ht : Tendsto (fun S : Finset α=>∑'v : α→₀β,
      if v.support⊆S then markedArray T m f v else 0) atTop
      (𝓝 (∑'v : α→₀β,markedArray T m f v)) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · intro v
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop v.support] with S hS
      simp only [ite_eq_left hS]
    · apply Filter.Eventually.of_forall
      intro S v
      split_ifs
      · exact markedArray_norm_le T m f hm v
      · simpa only [norm_zero] using norm_nonneg (v.prod f)
  change Tendsto (fun S : Finset α=>∏a∈S,∑'b,markedLocal T m f a b) atTop _
  apply ht.congr'
  filter_upwards [eventually_ge_atTop T] with S hTS
  rw [←marked_finiteEuler T S hTS m f h0 hf hm]
  trans ∑'v : α→₀β,{v : α→₀β | (v.support:Set α)⊆S}.indicator (markedArray T m f) v
  · apply tsum_congr
    intro v
    simp only [Set.indicator,Set.mem_ofPred_eq,Finset.coe_subset]
  · exact (tsum_subtype {v : α→₀β | (v.support:Set α)⊆S} (markedArray T m f)).symm

end SevenEighths.ProbeEulerFinsupp
end

end OAI

end Source1065

/- Original source: OAI/NumberTheory/DirichletL/Detector/MarkedValuations.lean; sha256: f5e6f9005f17f817ea15608aeb334ef361e50b12b502fb8558e018f9dd822037 -/
section Source1066
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic UniqueFactorizationMonoid ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma prime_dvd_iff_valuation (P : PrimeIdeal) (I : Id) (hI : I≠0) :
    P.val∣I ↔ primeValuations I P≠0 := by
  rw [primeValuations_apply,Multiset.count_ne_zero,mem_normalizedFactors_iff hI]
  exact ⟨fun h=>⟨P.property,h⟩,fun h=>h.2⟩

lemma prime_dvd_high_completed (P : PrimeIdeal) (v : PrimeIdeal→₀HighValuation) :
    P.val∣(highIdeals v).1.1*(highIdeals v).1.2^3 ↔ (v P).1.1+3*(v P).1.2≠0 := by
  have hI : (highIdeals v).1.1≠0 := idealFromValuations_ne_zero _
  have hJ : (highIdeals v).1.2≠0 := idealFromValuations_ne_zero _
  rw [prime_dvd_iff_valuation P _ (mul_ne_zero hI (pow_ne_zero _ hJ)),
    primeValuations_mul _ _ hI (pow_ne_zero _ hJ),primeValuations_pow]
  simp only [highIdeals,primeValuations_idealFromValuations,Finsupp.add_apply,
    Finsupp.mapRange_apply,Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]

lemma primeProduct_dvd (T : Finset PrimeIdeal) (I : Id) :
    (∏P∈T,P.val)∣I ↔ ∀P∈T,P.val∣I := by
  constructor
  · intro h P hP
    exact (Finset.dvd_prod_of_mem _ hP).trans h
  · intro h
    exact Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ=>primeIdeal_coprime P Q hPQ) h

def completedValuationMark (_P : PrimeIdeal) (b : HighValuation) : ℂ :=
  if b.1.1+3*b.1.2≠0 then 1 else 0

lemma completedValuationMark_norm (_P : PrimeIdeal) (b : HighValuation) :
    ‖completedValuationMark _P b‖≤1 := by
  unfold completedValuationMark
  split_ifs <;> norm_num

lemma completedValuationMark_product (T : Finset PrimeIdeal) (v : PrimeIdeal→₀HighValuation) :
    (∏P∈T,completedValuationMark P (v P))=
      if (∏P∈T,P.val)∣(highIdeals v).1.1*(highIdeals v).1.2^3 then 1 else 0 := by
  rw [primeProduct_dvd]
  simp only [prime_dvd_high_completed]
  by_cases h : ∀P∈T,(v P).1.1+3*(v P).1.2≠0
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro P hP
    exact ite_eq_left (h P hP)
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨P,hP,hv⟩ := h
    apply Finset.prod_eq_zero hP
    simp only [completedValuationMark,hv,ne_eq,not_true_eq_false,ite_false]

lemma highIdealMask_mark (S : Finset Id) (D I J K L : Id) :
    highIdealMask S D I J K L=(if D∣I*J^3 then 1 else 0)*highIdealMask S 1 I J K L := by
  unfold highIdealMask completedMask
  simp only [one_dvd,true_and]
  split_ifs <;> simp_all

lemma markedIdealHighSummand_mark (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) :
    markedIdealHighSummand S D η u x w z I J K L=
      (if D∣I*J^3 then 1 else 0)*markedIdealHighSummand S 1 η u x w z I J K L := by
  rw [markedIdealHighSummand,highIdealMask_mark,markedIdealHighSummand,mul_assoc]

end SevenEighths.ProbePhysical
end

end OAI

end Source1066

/- Original source: OAI/NumberTheory/DirichletL/Detector/MarkedEuler.lean; sha256: b1c397140e68d81ff368e0916083cbfb427c8a697a982148b62896c82dbb2001 -/
section Source1067
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEulerFinsupp
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def excludedHighArray (S : Finset Id) (η : HeckeFamily.Character) (x w z : ℂ) (a : HighIdeal) : ℂ :=
  markedIdealHighSummand S 1 η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2

lemma excludedHighArray_one (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ) : excludedHighArray S η x w z 1=1 := by
  simp only [excludedHighArray,Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
    highIdealMask_unmarked_one S hS,bareIdealHighSummand_one,one_mul]

lemma excludedHighArray_mul (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ) (a b : HighIdeal)
    (hc : IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2)) :
    excludedHighArray S η x w z (a*b)=excludedHighArray S η x w z a*excludedHighArray S η x w z b := by
  simp only [excludedHighArray,Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
    highIdealMask_unmarked_mul S hS a b,
    bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hc]
  ring

def excludedHighPrimeTerm (S : Finset Id) (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  excludedHighArray S η x w z ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))

lemma excludedHighArray_prod (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    excludedHighArray S η x w z (highIdeals v)=v.prod (excludedHighPrimeTerm S η x w z) :=
  highArray_val_prod _ (excludedHighArray_one S hS η x w z) (excludedHighArray_mul S hS η x w z) v

lemma markedHighArray_val (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    markedIdealHighSummand S (∏P∈T,P.val) η 1 x w z
      (highIdeals v).1.1 (highIdeals v).1.2 (highIdeals v).2.1 (highIdeals v).2.2=
        markedArray T completedValuationMark (excludedHighPrimeTerm S η x w z) v := by
  rw [markedIdealHighSummand_mark,markedArray,completedValuationMark_product]
  change _*excludedHighArray S η x w z (highIdeals v)=_
  rw [excludedHighArray_prod S hS]

theorem markedIdealHighSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b)
      (markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z) := by
  have h0 (P : PrimeIdeal) : excludedHighPrimeTerm S η x w z P 0=1 := by
    simp only [excludedHighPrimeTerm,Prod.fst_zero,Prod.snd_zero,pow_zero]
    exact excludedHighArray_one S hS η x w z
  have hs := (markedIdealHighSummand_summable S 1 η 1 x w z hx hw hz).norm.comp_injective highIdeals_injective
  change Summable (fun v=>‖excludedHighArray S η x w z (highIdeals v)‖) at hs
  simp only [excludedHighArray_prod S hS] at hs
  have he := marked_hasProd T completedValuationMark (excludedHighPrimeTerm S η x w z) h0 hs
    (fun P _ b=>completedValuationMark_norm P b)
  have hsum : (∑'v : PrimeIdeal→₀HighValuation,
      markedArray T completedValuationMark (excludedHighPrimeTerm S η x w z) v)=
      markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z := by
    simp only [←markedHighArray_val S hS T η x w z]
    unfold markedIdealHighSeries
    apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
      markedIdealHighSummand S (∏P∈T,P.val) η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
    intro a ha
    have hh : bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hc := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
      ((⟨a.1.1,hc.2.1.1⟩,⟨a.1.2,hc.2.2.1.1⟩),(⟨a.2.1,hc.2.2.2.1.1⟩,⟨a.2.2,hc.2.2.2.2.1⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [hsum] using he

end SevenEighths.ProbePhysical
end

end OAI

end Source1067

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/MarkedEuler.lean; sha256: efef8a8eb8e02a4eb79cece6b8faa8ddde74e4c802a037bbaf8765655d33c1c1 -/
section Source1068
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open ActualEisensteinCubic ProbeEulerFinsupp ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def excludedRowArray (S : Finset Id) (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (a : HighIdeal) : ℂ :=
  markedIdealHighSummand S 1 η u x w z a.1.1 a.1.2 a.2.1 a.2.2

lemma excludedRowArray_one (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ) : excludedRowArray S η u x w z 1=1 := by
  simp only [excludedRowArray,Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
    highIdealMask_unmarked_one S hS,bareIdealHighSummand_row_one,one_mul]

lemma excludedRowArray_mul (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (a b : HighIdeal)
    (hc : IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2)) :
    excludedRowArray S η u x w z (a*b)=excludedRowArray S η u x w z a*excludedRowArray S η u x w z b := by
  simp only [excludedRowArray,Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
    highIdealMask_unmarked_mul S hS a b,
    bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc]
  ring

def excludedRowPrimeTerm (S : Finset Id) (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  excludedRowArray S η u x w z ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))

lemma excludedRowArray_prod (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    excludedRowArray S η u x w z (highIdeals v)=v.prod (excludedRowPrimeTerm S η u x w z) :=
  highArray_val_prod _ (excludedRowArray_one S hS η u x w z) (excludedRowArray_mul S hS η u x w z) v

lemma markedRowArray_val (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    markedIdealHighSummand S (∏P∈T,P.val) η u x w z
      (highIdeals v).1.1 (highIdeals v).1.2 (highIdeals v).2.1 (highIdeals v).2.2=
        markedArray T completedValuationMark (excludedRowPrimeTerm S η u x w z) v := by
  rw [markedIdealHighSummand_mark,markedArray,completedValuationMark_product]
  change _*excludedRowArray S η u x w z (highIdeals v)=_
  rw [excludedRowArray_prod S hS]

theorem markedRowSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedRowPrimeTerm S η u x w z) P b)
      (markedIdealHighSeries S (∏P∈T,P.val) η u x w z) := by
  have h0 (P : PrimeIdeal) : excludedRowPrimeTerm S η u x w z P 0=1 := by
    simp only [excludedRowPrimeTerm,Prod.fst_zero,Prod.snd_zero,pow_zero]
    exact excludedRowArray_one S hS η u x w z
  have hs := (markedIdealHighSummand_summable S 1 η u x w z hx hw hz).norm.comp_injective highIdeals_injective
  change Summable (fun v=>‖excludedRowArray S η u x w z (highIdeals v)‖) at hs
  simp only [excludedRowArray_prod S hS] at hs
  have he := marked_hasProd T completedValuationMark (excludedRowPrimeTerm S η u x w z) h0 hs
    (fun P _ b=>completedValuationMark_norm P b)
  have hsum : (∑'v : PrimeIdeal→₀HighValuation,
      markedArray T completedValuationMark (excludedRowPrimeTerm S η u x w z) v)=
      markedIdealHighSeries S (∏P∈T,P.val) η u x w z := by
    simp only [←markedRowArray_val S hS T η u x w z]
    unfold markedIdealHighSeries
    apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
      markedIdealHighSummand S (∏P∈T,P.val) η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
    intro a ha
    have hh : bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hc := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
      ((⟨a.1.1,hc.2.1.1⟩,⟨a.1.2,hc.2.2.1.1⟩),(⟨a.2.1,hc.2.2.2.1.1⟩,⟨a.2.2,hc.2.2.2.2.1⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [hsum] using he

end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source1068

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighEulerRational.lean; sha256: 9b8177391e39881163f87443b6de514fbf0c807cbd9ce6383bf93c049b4e1507 -/
section Source1069
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma supported_primeGenerator_prime (P : PrimeIdeal) (hs : Supported P.val) :
    Prime (primaryGenerator P.val) := by
  apply (Ideal.span_singleton_prime (supported_primaryGenerator_ne_zero P.val hs)).mp
  rw [span_primaryGenerator_of_supported P.val hs]
  exact Ideal.isPrime_of_prime P.property

lemma targetMonoid_primaryGenerator (η : HeckeFamily.Character) (I : Ideal O) (hs : Supported I) :
    targetMonoid η (primaryGenerator I)=HeckeFamily.idealCoeff η I := by
  calc
    _ = HeckeFamily.idealCoeff η (Ideal.span {primaryGenerator I}) :=
      (HeckeFamily.idealCoeff_span η (supported_primaryGenerator_ne_zero I hs)).symm
    _ = _ := by rw [span_primaryGenerator_of_supported I hs]

def idealClosedCorrection (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
    (HeckeFamily.idealCoeff η P.val) 1 x w z

theorem idealHighLocalFactor_rational (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    idealHighLocalFactor η P.val x w z =
      (1-HeckeFamily.idealCoeff η P.val*(Q:ℂ)^(-x)) /
        ((1-(Q:ℂ)^(-6*z))*(1-(Q:ℂ)^(-w))) * idealClosedCorrection η P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    rw [hspan]
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1 := by
    rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1 := by
    apply (coordW_norm_le _ hQ0 1 w (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hDnorm : ‖coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x‖<1 := by
    apply (coordD_norm_le _ hQ0 _ 1 x (targetMonoid_norm_le_one η p) (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x≠0 := by
    intro he
    have hh : coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x=1 := (sub_eq_zero.mp he).symm
    rw [hh,norm_one] at hDnorm
    exact lt_irrefl _ hDnorm
  have he := idealHighLocalFactor_euler_identity η p hp hg.1 hg.2 hprimary hsp x w z hV hR hW hD
  dsimp only at he ⊢
  rw [hspan,actualACube_sq,targetMonoid_primaryGenerator η P.val hs] at he
  simpa only [coordD,coordV,coordW,star_one,mul_one,one_mul,idealClosedCorrection,p] using he

end SevenEighths.ProbePhysical
end

end OAI

end Source1069

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/MarkedLocal.lean; sha256: 71968b716bd08ee78f6557fc09bd0439b318ea0fabb8b4b1d86cb7f5b332d1f8 -/
section Source1070
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def idealRowMarkedLocalFactor (η : HeckeFamily.Character) (u : O) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∑e : Fin 2,∑'l,∑'k,∑'m,
    completedValuationMark P ((e.val,l),(k,m))*rowHighPrimeTerm η u x w z P ((e.val,l),(k,m))

lemma markedRowPrimeTerm_summable_norm (η : HeckeFamily.Character) (u : O) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun b : HighValuation=>‖completedValuationMark P b*rowHighPrimeTerm η u x w z P b‖) := by
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (rowHighPrimeTerm_summable_norm η u x w z hx hw hz P)
  intro b
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (completedValuationMark_norm P b)

lemma markedRowPrimeTerm_tsum (η : HeckeFamily.Character) (u : O) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (∑'b : HighValuation,completedValuationMark P b*rowHighPrimeTerm η u x w z P b)=
      idealRowMarkedLocalFactor η u P x w z := by
  have hs := (markedRowPrimeTerm_summable_norm η u P x w z hx hw hz).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) : (∑'b : ℕ×ℕ,completedValuationMark P ((e,l),b)*rowHighPrimeTerm η u x w z P ((e,l),b))=
      ∑'k,∑'m,completedValuationMark P ((e,l),(k,m))*rowHighPrimeTerm η u x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [rowHighPrimeTerm_zero_of_two_le η u x w z P e _ _ _ hh,mul_zero,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

lemma selectedRowLocal_outside (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (u : O) (P : PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (∑'b : HighValuation,ProbeEulerFinsupp.markedLocal T completedValuationMark
      (excludedRowPrimeTerm S η u x w z) P b)=
      if P∈T then idealRowMarkedLocalFactor η u P x w z else idealRowHighLocalFactor η u P.val x w z := by
  have he (b : HighValuation) : excludedRowPrimeTerm S η u x w z P b=rowHighPrimeTerm η u x w z P b := by
    simp only [excludedRowPrimeTerm,excludedRowArray,markedIdealHighSummand,
      highIdealMask_prime_outside S hS P hP,one_mul,rowHighPrimeTerm]
  simp only [ProbeEulerFinsupp.markedLocal,he]
  by_cases hPT : P∈T
  · simp only [ite_eq_left hPT]
    exact markedRowPrimeTerm_tsum η u P x w z hx hw hz
  · simp only [ite_eq_right hPT,one_mul]
    exact rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz P

end SevenEighths.ProbeHighRowFamily
end

end OAI

end Source1070

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/MarkedProduct.lean; sha256: fd52fd26a390c14a23ad75345a7dcf6fb3db68a30aa0a793aff726834fd8fa42 -/
section Source1071
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp
local notation "O" => HeckeFamily.O

def markExclusions (S : Finset (Ideal O)) (T : Finset PrimeIdeal) : Finset (Ideal O) :=
  S∪T.image Subtype.val

theorem markExclusions_prime (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) : ∀P∈markExclusions S T,Prime P := by
  intro P hP
  rcases Finset.mem_union.mp hP with hP|hP
  · exact hS P hP
  · obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    exact Q.property

@[simp] theorem mem_markExclusions (S : Finset (Ideal O)) (T : Finset PrimeIdeal) (P : PrimeIdeal) :
    P.val∈markExclusions S T ↔ P.val∈S ∨ P∈T := by
  simp only [markExclusions,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro (h|⟨Q,hQ,he⟩)
    · exact Or.inl h
    · exact Or.inr ((Subtype.ext he : Q=P) ▸ hQ)
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr ⟨P,h,rfl⟩

theorem markedRowSeries_eq_finite_replacement (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u x w z=
      markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,idealRowMarkedLocalFactor η u P x w z := by
  let R := fun P : PrimeIdeal=>if P∈T then idealRowMarkedLocalFactor η u P x w z else 1
  have hR : HasProd R (∏P∈T,idealRowMarkedLocalFactor η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := (excludedIdealHighSeries_row_hasProd (markExclusions S T)
    (markExclusions_prime S hS T) η u x w z hx hw hz).mul hR
  have heq (P : PrimeIdeal) :
      (∑'b : HighValuation,markedIdealHighSummand (markExclusions S T) 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*R P=
      ∑'b : HighValuation,markedLocal T completedValuationMark
        (excludedRowPrimeTerm S η u x w z) P b := by
    rw [excludedRowHighLocalFactor _ (markExclusions_prime S hS T) η u x w z hx hw hz]
    by_cases hP : P∈T
    · rw [ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hP)),
        selectedRowLocal_outside S hS T η u P (hT P hP) x w z hx hw hz,ite_eq_left hP]
      simp only [R,ite_eq_left hP,one_mul]
    · simp only [R,ite_eq_right hP,mul_one,markedLocal,one_mul]
      change _=∑'b : HighValuation,markedIdealHighSummand S 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)
      rw [excludedRowHighLocalFactor S hS η u x w z hx hw hz]
      simp only [mem_markExclusions,hP,or_false]
  have he' : HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedRowPrimeTerm S η u x w z) P b)
      (markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,idealRowMarkedLocalFactor η u P x w z) := by
    convert he using 1
    funext P
    exact (heq P).symm
  exact (markedRowSeries_hasProd S hS T η u x w z hx hw hz).unique he'

theorem markedRowSeries_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let S' := markExclusions S T
    let hS' := markExclusions_prime S hS T
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z=
      (LFunction (fixedSourcePrincipal S' hS') (6*z)*LFunction (rowCharacter S' hS' u) w/
        LFunction ((targetRow η u).excludePrimes S' hS') x*globalCorrection S' η u x w z)*
        ∏P∈T,idealRowMarkedLocalFactor η u.val P x w z := by
  dsimp only
  rw [markedRowSeries_eq_finite_replacement S hS T hT η u.val x w z hx hw hz,
    high_L_factorization (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1071

/- Original source: OAI/NumberTheory/DirichletL/PrimeRows/MarkedNormalization.lean; sha256: 8bb1a2924f7a5291da818a139010492b9c9cd7ed2e2a20de1968c1151470df70 -/
section Source1072
local notation "PrimeIdeal" => OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def localNormalization (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  (1-CubicEisenstein.fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*CubicEisenstein.fullIdealWeight w P.val)/
    (1-idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val)*CubicEisenstein.fullIdealWeight x P.val)

def markedLocalCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  idealRowMarkedLocalFactor η u.val P x w z*localNormalization η u P x w z

theorem localCorrection_eq_normalization (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) :
    localCorrection η u P x w z=idealRowHighLocalFactor η u.val P.val x w z*
      localNormalization η u P x w z := by
  unfold localCorrection localNormalization
  ring

lemma lift_outside_hasProd (S : Finset (Ideal O)) (f : PrimeIdeal→ℂ) (a : ℂ)
    (h : HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>f P.val) a) :
    HasProd (fun P : PrimeIdeal=>if P.val∈S then 1 else f P) a := by
  have hh := (hasProd_subtype_iff_mulIndicator (s:={P : PrimeIdeal | P.val∉S}) (f:=f)).mp h
  convert hh using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

theorem localNormalization_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 1<x.re) (hw : 1<w.re) (hz : 1<(6*z).re) :
    HasProd (fun P : PrimeIdeal=>if P.val∈S then 1 else localNormalization η u P x w z)
      ((LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
        (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x) := by
  apply lift_outside_hasProd
  have hZ := (fixedSourcePrincipal_hasProd S hS (6*z) hz).inv₀
    (LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz)
  have hW := (rowCharacter_hasProd S hS hbad u w hw).inv₀
    (LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw)
  have hD := targetRow_hasProd S hS hbad η u x hx
  simpa only [localNormalization,inv_inv,div_eq_mul_inv] using (hZ.mul hW).mul hD

theorem markedRowSeries_normalized (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z*
      ((LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
        (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x)=
      globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,markedLocalCorrection η u P x w z := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hleft := (markedRowSeries_hasProd S hS T η u.val x w z hx hw hz).mul
    (localNormalization_hasProd S hS hbad η u x w z hx1 hw1 hz1)
  have hbase := lift_outside_hasProd (markExclusions S T) (fun P=>localCorrection η u P x w z) _
    (globalCorrection_multipliable (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz).hasProd
  let R := fun P : PrimeIdeal=>if P∈T then markedLocalCorrection η u P x w z else 1
  have hR : HasProd R (∏P∈T,markedLocalCorrection η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have heq (P : PrimeIdeal) :
      (∑'b : HighValuation,markedLocal T completedValuationMark (excludedRowPrimeTerm S η u.val x w z) P b)*
        (if P.val∈S then 1 else localNormalization η u P x w z)=
      (if P.val∈markExclusions S T then 1 else localCorrection η u P x w z)*R P := by
    by_cases hP : P∈T
    · rw [selectedRowLocal_outside S hS T η u.val P (hT P hP) x w z hx hw hz,
        ite_eq_left hP,ite_eq_right (hT P hP),ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hP))]
      simp only [R,ite_eq_left hP,one_mul,markedLocalCorrection]
    · simp only [markedLocal,ite_eq_right hP,one_mul,R,mul_one]
      change (∑'b : HighValuation,markedIdealHighSummand S 1 η u.val x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*_=_
      rw [excludedRowHighLocalFactor S hS η u.val x w z hx hw hz]
      simp only [mem_markExclusions,hP,or_false]
      by_cases hPS : P.val∈S
      · simp only [ite_eq_left hPS,one_mul]
      · simp only [ite_eq_right hPS,localCorrection_eq_normalization]
  have hright := hbase.mul hR
  apply hleft.unique
  convert hright using 1
  · funext P
    exact heq P
  · rfl

theorem markedRowSeries_original_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z=
      (LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (rowCharacter S hS u) w/
        LFunction ((targetRow η u).excludePrimes S hS) x)*
      (globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,markedLocalCorrection η u P x w z) := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hZ := LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := LFunction_ne_zero_of_one_lt_re ((targetRow η u).excludePrimes S hS) hx1
  rw [←markedRowSeries_normalized S hS hbad T hT η u x w z hx hw hz]
  field_simp

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source1072

/- Original source: OAI/NumberTheory/DirichletL/Detector/MellinScaling.lean; sha256: 7304cb26073a299f790e6469fcb6d8ca6c8539475b5e1956f07bbc6e48537fb4 -/
section Source1073
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open EisensteinSchwartzPoisson

def sourceMellinWeight (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)*
    Complex.exp ((x+z-1)^2)*mellin (paperRadialFourier W0) z*mellin W1 w

lemma sourceMellinWeight_marked (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q : ℝ)
    (hZ : 0<Z) (hQ : 0<Q) (x w z : ℂ) :
    sourceMellinWeight W0 W1 X Y (Z*Q) x w z=
      (Q:ℂ)^(x+z-1)*sourceMellinWeight W0 W1 X Y Z x w z := by
  unfold sourceMellinWeight
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hZ.le hQ.le]
  ring

lemma sourceMellinWeight_rescaled (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q : ℝ)
    (hX : 0<X) (hY : 0<Y) (hQ : 0<Q) (x w z : ℂ) :
    ((Q^(-(3/2:ℝ)):ℝ):ℂ)*sourceMellinWeight W0 W1 (X/Q) (Y/Q) Z x w z=
      (Q:ℂ)^(z-w-1)*sourceMellinWeight W0 W1 X Y Z x w z := by
  have hQc : (Q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  unfold sourceMellinWeight
  rw [Complex.ofReal_div,Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hX.le hQ.le,Complex.div_cpow_ofReal_nonneg hY.le hQ.le,
    Complex.ofReal_cpow hQ.le]
  simp only [div_eq_mul_inv,←Complex.cpow_neg]
  have he : (Q:ℂ)^((-(3/2:ℝ):ℝ):ℂ)*(Q:ℂ)^(-(1/2-z))*(Q:ℂ)^(-(w-1))=(Q:ℂ)^(z-w-1) := by
    rw [←Complex.cpow_add _ _ hQc,←Complex.cpow_add _ _ hQc]
    congr 1
    push_cast
    ring
  calc
    _ = ((Q:ℂ)^((-(3/2:ℝ):ℝ):ℂ)*(Q:ℂ)^(-(1/2-z))*(Q:ℂ)^(-(w-1))) *
        ((X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)*
        Complex.exp ((x+z-1)^2)*mellin (paperRadialFourier W0) z*mellin W1 w) := by ring_nf
    _ = _ := by rw [he]; simp only [div_eq_mul_inv]

lemma sourceMellinWeight_marked_factor (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q : ℝ)
    (hZ : 0<Z) (hQ : 0<Q) (eta x w z : ℂ) :
    star eta*sourceMellinWeight W0 W1 X Y (Z*Q) x w z=
      (Q:ℂ)^(z-1)*(star eta*(Q:ℂ)^x)*sourceMellinWeight W0 W1 X Y Z x w z := by
  rw [sourceMellinWeight_marked W0 W1 X Y Z Q hZ hQ x w z]
  rw [show x+z-1=(z-1)+x by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hQ.ne')]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1073

/- Original source: OAI/NumberTheory/DirichletL/Detector/CoefficientDirect.lean; sha256: 1a7fb5daa29cb08f55ba17e630678ebf1b23a9162e5b10d833ecab6301932152 -/
section Source1074
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow ProbePhase
local notation "O" => ActualEisensteinCubic.O

def calibratedHighCoefficient (C : CalibrationData) (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  actualCongruenceCoefficient C A s hA H * idealRowHom C.generator (Ideal.span {s}) /
    ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s) *
    gaussTwo I hI * star (FiniteGaussPhase.angularFactor A * ProbePhase.G A) *
    targetMonoid η A * (C.Xi A)⁻¹ * reciprocitySign A s

lemma div_mul_frequency_cancel (a b c m : ℂ) (hc : c≠0) :
    c*(a/(b*c)*m)=a/b*m := by
  simp only [div_eq_mul_inv,mul_inv_rev]
  calc
    _ = (c*c⁻¹)*(a*b⁻¹*m) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hc,one_mul]

theorem calibratedHighCoefficient_eq_bare (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (η : HeckeFamily.Character) (I : Ideal O) (hI : primaryGenerator I≠0)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    calibratedHighCoefficient (calibrationForSet S hS) η I hI A s (supportedElement_ne_zero A hA) H=
      star ((calibrationForSet S hS).residueMonoid H)*
        bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) H := by
  let C := calibrationForSet S hS
  by_cases hH : IsCoprime C.generator H
  · have hn : star (C.residueMonoid H)≠0 := by
      apply star_ne_zero.mpr
      exact C.residue.apply_ne_zero_iff.mpr ((CubicEisenstein.isUnit_quotient_span_iff C.generator H).mpr hH)
    have he := sourceHighCoefficient_eq_bare S hS η I hI A s hA hs hcop H 1 (by simpa using hH)
    simp only [one_pow,mul_one] at he
    rw [←he]
    unfold sourceHighCoefficient calibratedHighCoefficient
    simp only [one_pow,mul_one]
    symm
    convert div_mul_frequency_cancel
      (actualCongruenceCoefficient C A s (supportedElement_ne_zero A hA) H * idealRowHom C.generator (Ideal.span {s}))
      ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s)
      (star (C.residueMonoid H))
      (gaussTwo I hI*star (FiniteGaussPhase.angularFactor A*ProbePhase.G A)*targetMonoid η A*(C.Xi A)⁻¹*reciprocitySign A s)
      hn using 1 <;> dsimp only [C] <;> ring
  · have hz := actualCongruenceCoefficient_zero_off_calibration S hS A s
      (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs) hcop H hH
    have hξ : C.residueMonoid H=0 := by
      change C.residue (Ideal.Quotient.mk _ H)=0
      apply MulChar.map_nonunit
      exact fun h=>hH ((CubicEisenstein.isUnit_quotient_span_iff _ _).mp h)
    dsimp only [C] at hξ
    simp only [calibratedHighCoefficient,hz,zero_mul,zero_div,hξ,star_zero]

end SevenEighths.ProbePhysical
end

end OAI

end Source1074

/- Original source: OAI/NumberTheory/DirichletL/Detector/SpectralCoefficient.lean; sha256: 65b87b9b5a9b516004c06b7385bf1f54ede41b6d779ef5dd4ffae03bd59d688d -/
section Source1075
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow ProbePhase ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma rayMask_supported (a : O) (ha : Supported (Ideal.span {a})) : RayFourExpansion.rayMask a=1 := by
  let : (Ideal.span {(2:O)}).IsMaximal := by
    simpa only [cubicTwoIdeal,Ideal.span_singleton_neg] using cubicTwoIdeal_isMaximal
  let : Field (O⧸Ideal.span {(2:O)}) := Ideal.Quotient.field _
  have h2 : IsCoprime (2:O) a := by
    apply (isUnit_quotient_span_iff _ _).mp
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact ((supported_span_iff a).mp ha).2
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have h4 : IsCoprime (4:O) a := by
    simpa only [show (2:O)^2=4 by norm_num] using (h2.pow_left : IsCoprime ((2:O)^2) a)
  exact ite_eq_left ((isUnit_quotient_span_iff (4:O) a).mpr h4)

lemma completedCorrection_supported (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    completedCorrection I J=star (G (completedIndex I J)) := by
  rw [completedCorrection_eq_phase,rayMask_supported]
  · exact one_mul _
  · exact supported_completed _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
      ((supported_span_primaryGenerator_iff J).mpr hJ)

lemma baseRowCoefficient_unit_apply (η : HeckeFamily.Character) (C : CalibrationData)
    (s : O) (hs : Supported (Ideal.span {s})) (A : O) (hA : Supported (Ideal.span {A}))
    (hcop : IsCoprime C.generator A) :
    baseRowCoefficient η C.Xi s hs A=targetMonoid η A*(C.Xi A)⁻¹*reciprocitySign A s := by
  change targetMonoid η A*star (C.Xi A)*sexticReciprocityPhase s A=_
  have hc : star (C.Xi A)=(C.Xi A)⁻¹ := (Complex.inv_eq_conj (C.Xi_norm_one A hA hcop)).symm
  rw [hc]
  congr 1
  exact congrArg (fun n : ℤ=>(n:ℂ)) (QuadraticAllOddCRT.quadraticRaySign_symm _ _)

theorem spectralSummand_source_coefficient (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : CalibrationData) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime C.generator (completedIndex I J)) (t : ℂ) :
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J=
      completedMask S D I J *
        (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
          star (FiniteGaussPhase.angularFactor (completedIndex I J)*G (completedIndex I J))*
          targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*
          reciprocitySign (completedIndex I J) s) /
        ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)) *
        (fullIdealWeight t I*fullIdealWeight (3*t) J) := by
  have hA := supported_completed _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ)
  have hb := baseRowCoefficient_unit_apply η C s hs (completedIndex I J) hA hcop
  have hangle : FiniteGaussPhase.angularFactor (completedIndex I J)=
      FiniteGaussPhase.angularFactor (primaryGenerator I)*FiniteGaussPhase.angularFactor (primaryGenerator J)^3 := by
    rw [completedIndex,angularFactor_mul,show primaryGenerator J^3=(primaryGenerator J*primaryGenerator J)*primaryGenerator J by ring,
      angularFactor_mul,angularFactor_mul]
    ring
  have hm : baseRowCoefficient η C.Xi s hs (primaryGenerator I)*
      baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3=
        targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*reciprocitySign (completedIndex I J) s := by
    rw [←map_pow,←map_mul]
    exact hb
  unfold spectralSummand CompletedGauss.columnWeight
  rw [completedCorrection_supported I J hI hJ,squarefreeGaussCoefficient_eq I hsf
    (supported_primaryGenerator_ne_zero I hI)]
  change _*(star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
      baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3/(Ideal.absNorm J:ℂ))*_=_
  rw [hangle]
  simp only [star_mul,star_pow]
  calc
    _ = completedMask S D I J*
      (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
        (star (FiniteGaussPhase.angularFactor (primaryGenerator I))*
         star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3)*star (G (completedIndex I J))*
        (baseRowCoefficient η C.Xi s hs (primaryGenerator I)*baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3)) /
      ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ))*(fullIdealWeight t I*fullIdealWeight (3*t) J) := by ring
    _ = _ := by rw [hm];ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1075

/- Original source: OAI/NumberTheory/DirichletL/Detector/PhysicalNorms.lean; sha256: f317b273df7e141d619230f721fff8b7a88703a486fe25695f51213956d58bb6 -/
section Source1076
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma elementNorm_mul (a b : ActualEisensteinCubic.O) :
    elementNorm (a*b)=elementNorm a*elementNorm b := by
  simp only [elementNorm,←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

lemma elementNorm_pow (a : ActualEisensteinCubic.O) (n : ℕ) :
    elementNorm (a^n)=elementNorm a^n := by
  simp only [elementNorm,←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]

lemma physical_radial_argument (B A s H : ActualEisensteinCubic.O) (X : ℝ)
    (hB : elementNorm B≠0) (hs : elementNorm s≠0) :
    (elementNorm B*elementNorm s*X)*elementNorm H/elementNorm ((B*A)*s)=
      X*elementNorm H/elementNorm A := by
  simp only [elementNorm_mul]
  field_simp

lemma physical_poisson_prefactor (B A S X : ℝ) (hB : 0<B) (hA : 0<A) (hS : 0<S) (hX : 0<X) :
    (Real.sqrt (B*S*X):ℂ)⁻¹*(Real.sqrt S:ℂ)⁻¹*((B*S*X/(B*A):ℝ):ℂ)=
      (Real.sqrt X:ℂ)/(Real.sqrt B:ℂ)/(A:ℂ) := by
  have hBc : (B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hB.ne'
  have hAc : (A:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hSb : (Real.sqrt B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB).ne'
  have hSs : (Real.sqrt S:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hS).ne'
  have hSx : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  rw [Real.sqrt_mul (mul_pos hB hS).le,Real.sqrt_mul hB.le]
  simp only [Complex.ofReal_mul,Complex.ofReal_div]
  field_simp
  have hb : (Real.sqrt B:ℂ)^2=(B:ℂ) := by exact_mod_cast Real.sq_sqrt hB.le
  have hs : (Real.sqrt S:ℂ)^2=(S:ℂ) := by exact_mod_cast Real.sq_sqrt hS.le
  have hx : (Real.sqrt X:ℂ)^2=(X:ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  rw [hs,hx]

end SevenEighths.ProbePhysical
end

end OAI

end Source1076

/- Original source: OAI/NumberTheory/DirichletL/Detector/HighAbsolute.lean; sha256: 51b80c27d59a001fef43bce1f68de88fee6b7ee0ee46a55422691f3948da9943 -/
section Source1077
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
abbrev NonzeroFrequency := {u : O // u≠0}

def frequencyWeight (z : ℂ) (u : NonzeroFrequency) : ℂ := (elementNorm u.val:ℂ)^(-z)

lemma frequencyWeight_norm (z : ℂ) (u : NonzeroFrequency) :
    ‖frequencyWeight z u‖=‖eisEmbedding u.val‖^(-2*z.re) := by
  have hn : 0<‖eisEmbedding u.val‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero u.property)
  unfold frequencyWeight elementNorm
  have hN : (Ideal.absNorm (Ideal.span {u.val}):ℝ)=‖eisEmbedding u.val‖^2 :=
    (eisEmbedding_norm_sq_eq_absNorm_span u.val).symm
  rw [hN,
    Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn), Complex.neg_re,
    ← Real.rpow_natCast_mul hn.le 2]
  congr 1
  ring

theorem frequencyWeight_summable_norm (z : ℂ) (hz : 1<z.re) :
    Summable (fun u : NonzeroFrequency => ‖frequencyWeight z u‖) := by
  simp only [frequencyWeight_norm]
  exact (summable_embedding_rpow (-2*z.re) (by linarith)).subtype _

def highAbsoluteMajorant (x w z : ℂ) (p : (Id×Id)×(Id×Id)) : ℝ :=
  ‖fullIdealWeight (x-1/2) p.1.1‖ * ‖fullIdealWeight (3*x-2) p.1.2‖ *
  ‖fullIdealWeight (w-1) p.2.1‖ * ‖fullIdealWeight (6*z) p.2.2‖

lemma highAbsoluteMajorant_nonneg (x w z : ℂ) (p : (Id×Id)×(Id×Id)) :
    0≤highAbsoluteMajorant x w z p := by unfold highAbsoluteMajorant; positivity

lemma highAbsoluteMajorant_summable (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) : Summable (highAbsoluteMajorant x w z) := by
  have h1 := fullIdealWeight_summable_norm (x-1/2) (by norm_num [Complex.sub_re,Complex.div_re]; linarith)
  have h2 := fullIdealWeight_summable_norm (3*x-2) (by norm_num [Complex.sub_re,Complex.mul_re]; linarith)
  have h3 := fullIdealWeight_summable_norm (w-1) (by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have h4 := fullIdealWeight_summable_norm (6*z) (by norm_num [Complex.mul_re]; linarith)
  have h12 := h1.mul_of_nonneg h2 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have h34 := h3.mul_of_nonneg h4 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have hall := h12.mul_of_nonneg h34
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
  unfold highAbsoluteMajorant
  simpa only [mul_assoc] using hall

theorem fullHighSummand_summable (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re)
    (mask : NonzeroFrequency→ℂ) (hmask : ∀u,‖mask u‖≤1) :
    Summable (fun p : NonzeroFrequency×((Id×Id)×(Id×Id)) =>
      mask p.1 * frequencyWeight z p.1 *
        markedIdealHighSummand S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2) := by
  have hm := (frequencyWeight_summable_norm z hz).mul_of_nonneg
    (highAbsoluteMajorant_summable x w z hx hw (by linarith))
    (fun _=>norm_nonneg _) (highAbsoluteMajorant_nonneg x w z)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hm
  intro p
  rw [norm_mul,norm_mul]
  have hcoeff := (markedIdealHighSummand_norm_le S D η p.1.val x w z
    p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2).trans
    (bareIdealHighSummand_norm_le η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
  change _≤‖frequencyWeight z p.1‖*highAbsoluteMajorant x w z p.2
  calc
    _ ≤ (1*‖frequencyWeight z p.1‖)*highAbsoluteMajorant x w z p.2 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (hmask p.1) (norm_nonneg _)
      · exact hcoeff
      · exact norm_nonneg _
      · positivity
    _ = _ := by rw [one_mul]

end SevenEighths.ProbePhysical
end

end OAI

end Source1077

/- Original source: OAI/NumberTheory/DirichletL/Detector/RadialExchange.lean; sha256: 23d7da49f52d45f6ab7e5a08a701ddc165a387d0e809cc67319335e2426a5abe -/
section Source1078
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma radialFourier_vertical_inverse (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (σ r : ℝ) (hσ : 0<σ) (hr : 0<r) :
    paperRadialFourier W r=verticalIntegral σ (fun z=>(r:ℂ)^(-z)*mellin (paperRadialFourier W) z) := by
  have he := ProbeRadialMellin.radial_mellin_inversion W a b ha hW σ r hσ hr
  simpa only [mellinInv,verticalIntegral,Complex.real_smul,smul_eq_mul] using he.symm

lemma radial_sum_exchange {ι : Type*} [Countable ι] (W : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hW : Function.support W⊆Set.Icc a b)
    (σ : ℝ) (hσ : 0<σ) (c : ι→ℂ) (r : ι→ℝ) (hr : ∀i,0<r i)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) :
    (∑'i,c i*paperRadialFourier W (r i))=
      verticalIntegral σ (fun z=>∑'i,c i*(r i:ℂ)^(-z)*mellin (paperRadialFourier W) z) := by
  let F := fun i (t : ℝ)=>c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*
    mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)
  have hF (i) : Integrable (F i) := by
    simpa only [F,mul_assoc] using
      (ProbeRadialMellin.radial_mellin_inverse_integrable W a b ha hW σ (r i) hσ (hr i)).const_mul (c i)
  have hn (i) (t : ℝ) : ‖F i t‖=(‖c i‖*(r i)^(-σ))*
      ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ := by
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hr i)]
    simp
  have hsum : Summable (fun i=>∫t : ℝ,‖F i t‖) := by
    simp only [hn,integral_const_mul]
    exact hc.mul_right _
  have he := integral_tsum_of_summable_integral_norm hF hsum
  simp_rw [radialFourier_vertical_inverse W a b ha hW σ _ hσ (hr _)]
  unfold verticalIntegral
  have hi (i) : c i*(↑(1/(2*Real.pi))*(∫t : ℝ,
      (r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)))=
      (↑(1/(2*Real.pi)):ℂ)*(∫t : ℝ,F i t) := by
    simp only [F,mul_assoc,integral_const_mul]
    ring
  simp_rw [hi]
  rw [tsum_mul_left,he]

lemma frequency_rpow_summable (σ : ℝ) (hσ : 1<σ) :
    Summable (fun H : NonzeroFrequency=>(elementNorm H.val)^(-σ)) := by
  have he (H : NonzeroFrequency) : ‖frequencyWeight (σ:ℂ) H‖=(elementNorm H.val)^(-σ) := by
    have hH : 0<elementNorm H.val := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr H.property))
    rw [frequencyWeight,Complex.norm_cpow_eq_rpow_re_of_pos hH]
    simp
  simpa only [he,Complex.ofReal_re] using frequencyWeight_summable_norm (σ:ℂ) hσ

theorem actualFrequency_moment_summable (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (K : ℝ) (hK : 0<K) (σ : ℝ) (hσ : 1<σ) :
    Summable (fun H : NonzeroFrequency=>‖actualCongruenceCoefficient C A s hA H.val‖*
      (K*elementNorm H.val/elementNorm ((C.generator*A)*s))^(-σ)) := by
  have hd : 0<elementNorm ((C.generator*A)*s) := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)))
  have hr (H : NonzeroFrequency) :
      (K*elementNorm H.val/elementNorm ((C.generator*A)*s))^(-σ)=
        (K/elementNorm ((C.generator*A)*s))^(-σ)*(elementNorm H.val)^(-σ) := by
    rw [show K*elementNorm H.val/elementNorm ((C.generator*A)*s)=
      (K/elementNorm ((C.generator*A)*s))*elementNorm H.val by ring]
    apply Real.mul_rpow (div_pos hK hd).le
    unfold elementNorm
    positivity
  simp only [hr]
  have hb := (frequency_rpow_summable σ hσ).mul_left
    (((Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {C.generator*A}):ℝ))*
      (K/elementNorm ((C.generator*A)*s))^(-σ))
  apply Summable.of_nonneg_of_le (fun H=>mul_nonneg (norm_nonneg _)
    (mul_nonneg (Real.rpow_nonneg (div_pos hK hd).le _) (Real.rpow_nonneg (by unfold elementNorm;positivity) _))) _ hb
  intro H
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (actualCongruenceCoefficient_norm_le C A s hA hs H.val)
      (Real.rpow_nonneg (div_pos hK hd).le _)) (Real.rpow_nonneg (by unfold elementNorm;positivity) _)

end SevenEighths.ProbePhysical
end

end OAI

end Source1078

/- Original source: OAI/NumberTheory/DirichletL/Detector/RadialIdentity.lean; sha256: 86b7cad968595a0915cbd27dcebe8529c098c0065981009db22a3e240d1a6fe2 -/
section Source1079
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma elementNorm_pos (a : O) (ha : a≠0) : 0<elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))

lemma actualCongruenceCoefficient_zero_frequency (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty) (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) :
    actualCongruenceCoefficient (calibrationForSet S hS) A s hA 0=0 := by
  apply actualCongruenceCoefficient_zero_off_calibration S hS A s hA hs hcop
  intro hc
  have hz := (calibrationForSet_coprime_iff S hS 0).mp hc
  obtain ⟨P,hP⟩ := hSne
  exact hz P hP P.zero_mem

theorem actualFrequency_mellin_nonzero (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (K : ℝ) (hK : 0<K) (σ : ℝ) (hσ : 1<σ) :
    (∑'H : NonzeroFrequency,actualCongruenceCoefficient C A s hA H.val*
      paperRadialFourier W (K*elementNorm H.val/elementNorm ((C.generator*A)*s)))=
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C A s hA H.val*
        ((K*elementNorm H.val/elementNorm ((C.generator*A)*s)):ℂ)^(-z)*
          mellin (paperRadialFourier W) z) := by
  let : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  have he := radial_sum_exchange W a b ha hW σ (by linarith)
    (fun H : NonzeroFrequency=>actualCongruenceCoefficient C A s hA H.val)
    (fun H=>K*elementNorm H.val/elementNorm ((C.generator*A)*s)) (by
      intro H
      exact div_pos (mul_pos hK (elementNorm_pos H.val H.property))
        (elementNorm_pos _ (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)))
    (actualFrequency_moment_summable C A s hA hs K hK σ hσ)
  simpa only [Complex.ofReal_mul,Complex.ofReal_div] using he

theorem actualFrequency_mellin (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s))
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (K : ℝ) (hK : 0<K) (σ : ℝ) (hσ : 1<σ) :
    let C := calibrationForSet S hS
    (∑'H : O,actualCongruenceCoefficient C A s hA H*
      paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*A)*s)))=
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C A s hA H.val*
        ((K*elementNorm H.val/elementNorm ((C.generator*A)*s)):ℂ)^(-z)*
          mellin (paperRadialFourier W) z) := by
  dsimp only
  rw [←actualFrequency_mellin_nonzero (calibrationForSet S hS) A s hA hs W a b ha hW K hK σ hσ]
  symm
  apply (Subtype.val_injective : Function.Injective (fun H : NonzeroFrequency=>H.val)).tsum_eq
    (f:=fun H : O=>actualCongruenceCoefficient (calibrationForSet S hS) A s hA H*
      paperRadialFourier W (K*elementNorm H/elementNorm (((calibrationForSet S hS).generator*A)*s)))
  intro H hH
  have hn : H≠0 := by
    intro hz
    subst H
    exact hH (by dsimp only; rw [actualCongruenceCoefficient_zero_frequency S hS hSne A s hA hs hcop,zero_mul])
  exact ⟨⟨H,hn⟩,rfl⟩

end SevenEighths.ProbePhysical
end

end OAI

end Source1079
