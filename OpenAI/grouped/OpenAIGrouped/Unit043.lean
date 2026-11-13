import OpenAIGrouped.Unit042
import OpenAIGrouped.Unit033
import OpenAIGrouped.Unit007
import OpenAIGrouped.Unit008
import OpenAIGrouped.Unit010

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGramPoisson.lean; sha256: e1c3965801756a42476c88d277cbe77c03015e89f396b5e4cb07a96507646b5d -/
section Source1720
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowGram_pair_prefactor (C : CalibrationData) (W1 : ℝ→ℂ)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v Q : ℝ) (s t : {I : Id // Supported I}) :
    (lowGaussColumn C W1 Y σ v s*star (lowGaussColumn C W1 Y σ v t))*
      ((Q:ℂ)/((Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ)))=
      ((Q/Y^3:ℝ):ℂ)*
        ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
          star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y))) := by
  calc
    _ = (Q:ℂ)*(lowGaussColumn C W1 Y σ v s/(Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ))*
        star (lowGaussColumn C W1 Y σ v t/(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ)) := by
      simp only [Complex.star_def,map_mul,map_inv₀,Complex.conj_ofReal,div_eq_mul_inv,mul_inv_rev]
      ring
    _ = (Q:ℂ)*(lowGramScale Y*star (lowGramScale Y))*
        ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
          star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y))) := by
      rw [lowGaussColumn_unnormalized C W1 Y hY σ v s,lowGaussColumn_unnormalized C W1 Y hY σ v t]
      simp only [star_mul]
      ring
    _ = _ := by rw [lowGramScale_mul_star Y hY];simp only [div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]

theorem lowGram_source_poisson (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ)
    (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0<Q) :
    gaussEnergy (lowGaussColumns W1 hW1 Y hY) (fun s=>primaryGenerator s.val)
      (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
      (lowGaussColumn C W1 Y σ v) U Q=
      ((Q/Y^3:ℝ):ℂ)*
        ∑s∈lowGaussColumns W1 hW1 Y hY,∑t∈lowGaussColumns W1 hW1 Y hY,
          ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
            star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y)))*
          ∑'h : O,actualCorrelation (primaryGenerator s.val) (primaryGenerator t.val)
            ((supported_span_primaryGenerator_iff s.val).mpr s.property)
            ((supported_span_primaryGenerator_iff t.val).mpr t.property) (-h)*
            paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator s.val*primaryGenerator t.val)‖^2) := by
  rw [gaussEnergy_poisson _ _ _ _ U Q hQ]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have hes := congrArg Ideal.absNorm ((primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1)
  have het := congrArg Ideal.absNorm ((primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1)
  rw [hes,het,←mul_assoc,lowGram_pair_prefactor C W1 Y hY σ v Q s t,mul_assoc]

theorem lowGram_kernel_scale (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (s t : {I : Id // Supported I}) (h : O) :
    Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator s.val*primaryGenerator t.val)‖^2=
      ‖eisEmbedding h‖^2/((Y^2/Q)*((Ideal.absNorm s.val:ℝ)/Y)*((Ideal.absNorm t.val:ℝ)/Y)) := by
  simp_rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  rw [←Ideal.span_singleton_mul_span_singleton]
  rw [(primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1,
    (primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1,map_mul,Nat.cast_mul]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI

end Source1720

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramGcdSource.lean; sha256: 55e6534bc06ff1b66ce12bb41ec2be3b71b4610502db15ff360dd1c72af2b74f -/
section Source1721
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma gcd_generator_left (I J : SupportedIdeal) :
    primaryGenerator I.val=primaryGenerator (gcdCommon I J).val*primaryGenerator (gcdLeft I J).val := by
  rw [←primaryGenerator_mul,gcd_common_left]

lemma gcd_generator_right (I J : SupportedIdeal) :
    primaryGenerator J.val=primaryGenerator (gcdCommon I J).val*primaryGenerator (gcdRight I J).val := by
  rw [←primaryGenerator_mul,gcd_common_right]

lemma gcd_generator_coprime (I J : SupportedIdeal) :
    IsCoprime (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdLeft I J).property)).1,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdRight I J).property)).1]
  exact gcd_residual_coprime I J

theorem actual_gcd_lift (I J : SupportedIdeal) (k : O) :
    let C:=primaryGenerator (gcdCommon I J).val
    let n₁:=primaryGenerator (gcdLeft I J).val
    let n₂:=primaryGenerator (gcdRight I J).val
    actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (C*k)=
      idealRowHom k (gcdLeft I J).val*star (idealRowHom (-k) (gcdRight I J).val)*
        sexticReciprocityPhase n₁ n₂*
          actualCommon C ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property) n₁ n₂ k := by
  dsimp only
  have h₁ := (supported_span_primaryGenerator_iff _).mpr (gcdLeft I J).property
  have h₂ := (supported_span_primaryGenerator_iff _).mpr (gcdRight I J).property
  have hp₁ : ConcretePrimeRowBridge.goodLambda^2∣primaryGenerator (gcdLeft I J).val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdLeft I J).property)).2
  have hp₂ : ConcretePrimeRowBridge.goodLambda^2∣primaryGenerator (gcdRight I J).val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdRight I J).property)).2
  have hh := actual_common_lift (primaryGenerator (gcdCommon I J).val)
    (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val) k
    ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property) h₁ h₂ hp₁ hp₂
    (gcd_generator_coprime I J)
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdLeft I J).property)).1,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdRight I J).property)).1] using hh

theorem actual_gcd_frequency_source (I J : SupportedIdeal) (U : SchwartzMap ℝ ℂ) (Q : ℝ) :
    (∑'h : O,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (-h)*
      paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))=
      ∑'k : O,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) (primaryGenerator (gcdCommon I J).val*k)*
        paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator (gcdCommon I J).val*k)‖^2/
          ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2) := by
  have hneg := (Equiv.neg O).tsum_eq (fun h : O=>
    actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) h*
      paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simp only [Equiv.neg_apply,map_neg,norm_neg] at hneg
  rw [hneg]
  have hh := actual_common_frequency_tsum (primaryGenerator (gcdCommon I J).val)
    (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val)
    ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdLeft I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdRight I J).property)
    (fun h=>paperRadialFourier U (Q*‖eisEmbedding h‖^2/
      ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J] using hh

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1721

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramPrimaryLattice.lean; sha256: ca5d6293ecc2593ff36929083a4c0353027b1f1cba38d4ffcd0318a048cf323f -/
section Source1722
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

abbrev PrimaryElement := {n : O // Supported (Ideal.span {n}) ∧ λ₀^2∣n-1}

def primaryIdealEquiv : SupportedIdeal≃PrimaryElement where
  toFun I := ⟨primaryGenerator I.val,(supported_span_primaryGenerator_iff _).mpr I.property,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).2⟩
  invFun n := ⟨Ideal.span {n.val},n.property.1⟩
  left_inv I := Subtype.ext (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1
  right_inv n := Subtype.ext (primaryGenerator_span n.val (supported_element_ne_zero _ n.property.1) n.property.2)

lemma primaryCoefficient_nonzero_supported (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (n : O) (hn : primaryCoefficient S hS σ n≠0) :
    Supported (Ideal.span {n}) ∧ λ₀^2∣n-1 := by
  have hp : λ₀^2∣n-1 := by
    by_contra h
    exact hn (by simp [primaryCoefficient,h])
  have hc : IsCoprime (calibrationForSet S hS).generator n := by
    by_contra h
    exact hn (by rw [primaryCoefficient,ite_eq_left hp,gramCoefficientExtension_zero S hS σ n h])
  have hb := calibration_generator_bad S hS hbad
  exact ⟨supported_of_coprime_bad _ n hb.1 hb.2 hc,hp⟩

lemma primary_factor_right (A n : O) (hA : λ₀^2∣A-1) (hAn : λ₀^2∣A*n-1) : λ₀^2∣n-1 := by
  have h := dvd_sub hAn (hA.mul_right n)
  convert h using 1 ; ring

lemma primaryCoefficient_residual (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (A n : O) (hA : λ₀^2∣A-1)
    (hn : primaryCoefficient S hS σ (A*n)≠0) :
    Supported (Ideal.span {n}) ∧ λ₀^2∣n-1 := by
  have hs := primaryCoefficient_nonzero_supported S hS hbad σ (A*n) hn
  have hsp : Supported (Ideal.span {A}*Ideal.span {n}) := by
    rw [Ideal.span_singleton_mul_span_singleton]
    exact hs.1
  exact ⟨((supported_mul_iff _ _).mp hsp).2,primary_factor_right A n hA hs.2⟩

theorem primary_ideal_tsum (f : O→ℂ)
    (hz : ∀n,¬(Supported (Ideal.span {n}) ∧ λ₀^2∣n-1)→f n=0) :
    (∑'I : SupportedIdeal,f (primaryGenerator I.val))=∑'n : O,f n := by
  have he := primaryIdealEquiv.tsum_eq (fun n : PrimaryElement=>f n.val)
  change (∑'I : SupportedIdeal,f (primaryGenerator I.val))=∑'n : PrimaryElement,f n.val at he
  rw [he]
  exact tsum_subtype_eq_of_support_subset (by intro n hn;by_contra h;exact hn (hz n h))

theorem primary_ideal_pair_tsum (f : O→O→ℂ)
    (hl : ∀n m,¬(Supported (Ideal.span {n}) ∧ λ₀^2∣n-1)→f n m=0)
    (hr : ∀n m,¬(Supported (Ideal.span {m}) ∧ λ₀^2∣m-1)→f n m=0) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,f (primaryGenerator I.val) (primaryGenerator J.val))=
      ∑'n : O,∑'m : O,f n m := by
  have hinner (n : O) : (∑'J : SupportedIdeal,f n (primaryGenerator J.val))=∑'m : O,f n m :=
    primary_ideal_tsum (fun m=>f n m) (fun m h=>hr n m h)
  simp_rw [hinner]
  apply primary_ideal_tsum (fun n=>∑'m : O,f n m)
  intro n hn
  simp only [hl n _ hn,tsum_zero]

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1722

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramLatticeSource.lean; sha256: 5e57d800caacd449f2fa0468a30ddf3de1a0d5652b8d4031cd981df5c46782d1 -/
section Source1723
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma jointExtension_zero_off_primary_left (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : O)
    (hCd : λ₀^2∣C*d-1) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (n m : O) (hn : ¬(Supported (Ideal.span {n}) ∧ λ₀^2∣n-1)) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)=0 := by
  have hz : primaryCoefficient S hS σ (C*(d*n))=0 := by
    by_contra h
    apply hn
    apply primaryCoefficient_residual S hS hbad σ (C*d) n hCd
    simpa only [mul_assoc] using h
  simp only [jointExtension,jointFixed,hz,zero_mul]

lemma jointExtension_zero_off_primary_right (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : O)
    (hCd : λ₀^2∣C*d-1) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (n m : O) (hm : ¬(Supported (Ideal.span {m}) ∧ λ₀^2∣m-1)) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)=0 := by
  have hz : primaryCoefficient S hS σ (C*(d*m))=0 := by
    by_contra h
    apply hm
    apply primaryCoefficient_residual S hS hbad σ (C*d) m hCd
    simpa only [mul_assoc] using h
  simp only [jointExtension,jointFixed,hz,star_zero,mul_zero,zero_mul]

theorem jointExtension_ideal_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : O)
    (hCd : λ₀^2∣C*d-1) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ) (W : O→O→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      jointExtension S hS σ C k u a b r hr P hg c (d*primaryGenerator I.val) (d*primaryGenerator J.val)*
        W (primaryGenerator I.val) (primaryGenerator J.val))=
      ∑'n : O,∑'m : O,jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)*W n m := by
  apply primary_ideal_pair_tsum (fun n m=>jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)*W n m)
  · intro n m hn
    rw [jointExtension_zero_off_primary_left S hS hbad σ C k d hCd u a b r hr P hg c n m hn,zero_mul]
  · intro n m hm
    rw [jointExtension_zero_off_primary_right S hS hbad σ C k d hCd u a b r hr P hg c n m hm,zero_mul]

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1723

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramMobiusLattice.lean; sha256: ecfa16f5b6220157bb39b0bb11eabead83d9f712d0a466d9fb1d1e21111e6302 -/
section Source1724
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma primary_product (C d : O) (hC : λ₀^2∣C-1) (hd : λ₀^2∣d-1) : λ₀^2∣C*d-1 := by
  have h := dvd_add (hC.mul_right d) hd
  convert h using 1 ; ring

theorem jointExtension_divisor_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k : O) (hC : λ₀^2∣C-1)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (D : SupportedIdeal) (W : O→O→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      if D.val∣I.val ∧ D.val∣J.val then
        jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator I.val) (primaryGenerator J.val)*
          W (primaryGenerator I.val) (primaryGenerator J.val) else 0)=
      ∑'n : O,∑'m : O,
        jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator D.val*n) (primaryGenerator D.val*m)*
          W (primaryGenerator D.val*n) (primaryGenerator D.val*m) := by
  rw [supported_divisor_pair_tsum D (fun I J=>
    jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator I.val) (primaryGenerator J.val)*
      W (primaryGenerator I.val) (primaryGenerator J.val))]
  simp only [supported_dilation_generator]
  have hd : λ₀^2∣primaryGenerator D.val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ D.property)).2
  exact jointExtension_ideal_lattice S hS hbad σ C k (primaryGenerator D.val) (primary_product C _ hC hd)
    u a b r hr P hg c (fun n m=>W (primaryGenerator D.val*n) (primaryGenerator D.val*m))

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1724

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGramHeight.lean; sha256: f308c1b0dccb35bda9354305aaf32901d739f93a0eca25b919a1d754f4c95f53 -/
section Source1725
namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap Topology
open Filter Set CompletedHeight FourierBridge
namespace SevenEighths.ProbePhysical

def lowGramBaseWindow (W : ℝ→ℂ) (r : ℝ) : ℂ := W r/(r:ℂ)

lemma lowGramBaseWindow_support (W : ℝ→ℂ) :
    Function.support (lowGramBaseWindow W)⊆Function.support W := by
  intro r hr hz
  exact hr (by simp [lowGramBaseWindow,hz])

lemma lowGramBaseWindow_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (lowGramBaseWindow W) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r=0
  · subst r
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ=>(0:ℂ)) 0).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds ha] with x hx
    have hz : W x=0 := by
      by_contra h
      exact (not_le.mpr hx) (hs h).1
    simp [lowGramBaseWindow,hz]
  · unfold lowGramBaseWindow
    simp only [div_eq_mul_inv]
    exact hW.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.fun_inv (Complex.ofReal_ne_zero.mpr hr))

lemma lowGramProfile_twist (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (v r : ℝ) :
    lowGramProfile W v r=normTwistedSource (lowGramBaseWindow W) (v/(2*Real.pi)) r := by
  by_cases hz : W r=0
  · simp [lowGramProfile,normTwistedSource,lowGramBaseWindow,hz]
  have hr : 0<r := ha.trans_le (hs hz).1
  have hrc : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hp : (r:ℂ)^((v:ℂ)*Complex.I)=logPhase (v/(2*Real.pi)) (Real.log r) := by
    rw [Complex.cpow_def_of_ne_zero hrc,←Complex.ofReal_log hr.le]
    unfold logPhase
    congr 1
    push_cast
    field_simp
  rw [lowGramProfile,Complex.cpow_add _ _ hrc,Complex.cpow_neg_one,hp]
  unfold normTwistedSource lowGramBaseWindow
  ring

def lowGramSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (v : ℝ) : SchwartzMap ℝ ℂ :=
  uniformTwistedSchwartz (lowGramBaseWindow W) a b ha
    ((lowGramBaseWindow_support W).trans hs) (lowGramBaseWindow_smooth W a b ha hs hW) (v/(2*Real.pi))

lemma lowGramSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (v r : ℝ) :
    lowGramSchwartz W a b ha hs hW v r=lowGramProfile W v r := by
  rw [lowGramSchwartz,uniformTwistedSchwartz_apply,lowGramProfile_twist W a b ha hs]

theorem lowGramProfile_uniform_degree (a b : ℝ) (ha : 0<a) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∀W : ℝ→ℂ,∀hs : Function.support W⊆Set.Icc a b,∀hW : ContDiff ℝ ∞ W,
      ∃C : ℝ,0<C ∧ ∀v : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (lowGramSchwartz W a b ha hs hW v)≤C*(1+‖v‖)^n := by
  obtain ⟨n,hn⟩ := normTwistedSource_uniform_degree a b ha S
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn (lowGramBaseWindow W) ((lowGramBaseWindow_support W).trans hs)
    (lowGramBaseWindow_smooth W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro v
  apply (hb (v/(2*Real.pi))).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply pow_le_pow_left₀ (by positivity)
  gcongr
  simp only [norm_div,Real.norm_eq_abs,abs_of_pos (show (0:ℝ)<2*Real.pi by positivity)]
  exact div_le_self (norm_nonneg v) (by linarith [Real.pi_gt_three])

end SevenEighths.ProbePhysical
end

end OAI

end Source1725

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramMeanLift.lean; sha256: ec2eb90970c05f09800f66e3e3e8abbbe4779d922301ca840b6d1212ae859458 -/
section Source1726
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O

theorem joint_mean_of_local_factor (Q P : Ideal O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (O⧸P)≠2)
    (c e : ℕ) (hc : 1≤c) (he : ¬6∣e) (hcop : IsCoprime Q (P^c))
    [Fintype (O⧸Q)] [Fintype (O⧸P^c)] [Fintype (O⧸Q*P^c)]
    (F : O→O→ℂ) (hF : ∀x z y,x-z∈Q → F x y=F z y) (d : O) :
    (∑x : O⧸Q*P^c,∑y : O⧸Q*P^c,
      (actualSextic P hg^e) (Ideal.Quotient.mk P (d*x.out))*F x.out y.out)=0 := by
  let E := Ideal.quotientMulEquivQuotientProd Q (P^c) hcop
  have hE (x : O⧸Q*P^c) : E x=(Ideal.Quotient.mk Q x.out,Ideal.Quotient.mk (P^c) x.out) := by
    conv_lhs => rw [←Ideal.Quotient.mk_out x]
    rfl
  have hf (x : O⧸Q*P^c) (y : O) : F x.out y=F (E x).1.out y := by
    apply hF
    apply Ideal.Quotient.eq.mp
    rw [Ideal.Quotient.mk_out,hE]
  have hp (x : O⧸Q*P^c) : Ideal.Quotient.mk P (d*x.out)=
      Ideal.Quotient.mk P d*primePowerReduction P hc (E x).2 := by
    rw [map_mul,hE]
    rfl
  have hz := crt_joint_mean_zero Q P hg hchar c e hc he hcop
    (fun x y=>F x.out y.out) d
  convert hz using 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [hp,hf]

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1726

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramJointMean.lean; sha256: 8383d3b5cc28ef2f1788428257a3e11ef79326506126a40d2b176cc0056f9eaf -/
section Source1727
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

def jointRemainder (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J : Id) (n₁ n₂ : O) : ℂ :=
  jointFixed S hS σ C u a b r hr n₁ n₂*
    (idealRowHom n₁ J*star (idealRowHom n₂ (Ideal.span {r})))*globalExtension P hg c n₁ n₂ k

theorem jointExtension_local_factor (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J p : Id) [p.IsMaximal] (hgp : goodLambda∉p) (e : ℕ) (he : e≠0)
    (hfactor : Ideal.span {r}=J*p^e) (n₁ n₂ : O) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      (actualSextic p hgp^e) (Ideal.Quotient.mk p n₁)*
        jointRemainder S hS σ C k u a b r hr P hg c J n₁ n₂ := by
  have hf : idealRowHom n₁ (Ideal.span {r})=
      idealRowHom n₁ J*(actualSextic p hgp^e) (Ideal.Quotient.mk p n₁) := by
    rw [hfactor,map_mul,map_pow,idealRowHom_prime n₁ p hgp,MulChar.pow_apply' _ he]
  rw [jointExtension,hf,jointRemainder]
  ring

lemma jointRemainder_periodic_first (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J : Id) (n m y : O) (h : n-m∈jointFixedModulus S hS*(∏i,P i)*J) :
    jointRemainder S hS σ C k u a b r hr P hg c J n y=
      jointRemainder S hS σ C k u a b r hr P hg c J m y := by
  have hf := jointFixed_periodic S hS σ C u a b r hr n y m y
    (Ideal.mul_le_left (Ideal.mul_le_left h)) (by simp)
  have hm := idealRowHom_congr_mod J n m (Ideal.mul_le_right h)
  have hg' := globalExtension_periodic P hg c n y m y k k
    (Ideal.mul_le_right (Ideal.mul_le_left h)) (by simp) (by simp)
  simp only [jointRemainder,hf,hm,hg']

theorem jointExtension_mean_zero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J p : Id) [p.IsMaximal] (hgp : goodLambda∉p) (hchar : ringChar (O⧸p)≠2)
    (e : ℕ) (he : ¬6∣e) (hfactor : Ideal.span {r}=J*p^e)
    (hcop : IsCoprime (jointFixedModulus S hS*(∏i,P i)*J) (p^e))
    [Fintype (O⧸jointFixedModulus S hS*(∏i,P i)*J)] [Fintype (O⧸p^e)]
    [Fintype (O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e)] (d : O) :
    (∑x : O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e,
      ∑y : O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e,
        jointExtension S hS σ C k u a b r hr P hg c (d*x.out) (d*y.out))=0 := by
  have he0 : e≠0 := by intro h;exact he (h ▸ dvd_zero 6)
  have he1 : 1≤e := Nat.one_le_iff_ne_zero.mpr he0
  simp_rw [jointExtension_local_factor S hS σ C k u a b r hr P hg c J p hgp e he0 hfactor]
  apply joint_mean_of_local_factor _ p hgp hchar e e he1 he hcop
    (fun x y=>jointRemainder S hS σ C k u a b r hr P hg c J (d*x) (d*y)) _ d
  intro x z y hxz
  apply jointRemainder_periodic_first
  rw [←mul_sub]
  exact (jointFixedModulus S hS*(∏i,P i)*J).mul_mem_left d hxz

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1727

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramJointPeriod.lean; sha256: 63c39693202d61945ffd6cd35dd5d4b3f0b50e8d3cb577b6d85ce788ad0c0853 -/
section Source1728
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma common_radical_norm_le (C : O) (hC : C≠0) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (∏i,P i)≤Ideal.absNorm (Ideal.span {C}) := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hC)))
  apply map_dvd Ideal.absNorm
  rw [he]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (hc i)))

lemma jointPeriod_norm_bound (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C k : O) (hC : C≠0) (hk0 : k≠0) (u : Oˣ) (a b : ℕ) (r : O)
    (hk : k=u.val*λ₀^a*(2:O)^b*r) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (jointPeriod S hS P r)≤
      Ideal.absNorm (jointFixedModulus S hS)*Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) := by
  rw [jointPeriod,map_mul,map_mul]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (common_radical_norm_le C hC P c hc he))
    (numerator_good_norm_le u a b r k hk hk0)

lemma jointPeriod_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C : O) (hC : C≠0) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (he : Ideal.span {C}=∏i,P i^c i) (r : O) (hr : r≠0) :
    jointPeriod S hS P r≠0 := by
  have hp : ∏i,P i≠(0:Id) := by
    intro hz
    have hd : (∏i,P i)∣Ideal.span {C} := by
      rw [he]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (hc i)))
    rw [hz,zero_dvd_iff] at hd
    exact hC (Ideal.span_singleton_eq_bot.mp hd)
  exact mul_ne_zero (mul_ne_zero (jointFixedModulus_nonzero S hS) hp)
    (Ideal.span_singleton_eq_bot.not.mpr hr)

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1728

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramPrimeSeparation.lean; sha256: 0b38dcd1c598364aae728a9ab21234b58603537637db351a07a75460151da233 -/
section Source1729
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma maximal_coprime_of_not_dvd (p J : Id) [p.IsMaximal] (h : ¬p∣J) : IsCoprime J p := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra htop
  have he : p=J⊔p := Ideal.IsMaximal.eq_of_le inferInstance htop le_sup_right
  apply h
  apply Ideal.dvd_iff_le.mpr
  rw [he]
  exact le_sup_left

theorem exists_prime_separation (I p : Id) (hI : I≠0) [p.IsMaximal] (hp0 : p≠0) :
    ∃J : Id,I=J*p^((normalizedFactors I).count p) ∧ IsCoprime J p ∧ J≠0 := by
  have hp : Prime p := Ideal.prime_of_isPrime hp0 inferInstance
  obtain ⟨J,hJ,hnd⟩ := (FiniteMultiplicity.of_prime_left hp hI).exists_eq_pow_mul_and_not_dvd
  have he : multiplicity p I=(normalizedFactors I).count p := by
    simpa only [normalize_eq] using multiplicity_eq_count_normalizedFactors hp.irreducible hI
  refine ⟨J,?_,maximal_coprime_of_not_dvd p J hnd,?_⟩
  · rw [←he,mul_comm]
    exact hJ
  · intro hz
    rw [hz,mul_zero] at hJ
    exact hI hJ

theorem exists_nonexceptional_separation (L R I p : Id) (hI : I≠0)
    [p.IsMaximal] (hp0 : p≠0) (hL : ¬p∣L) (hR : ¬p∣R) :
    ∃J : Id,I=J*p^((normalizedFactors I).count p) ∧
      IsCoprime (L*R*J) (p^((normalizedFactors I).count p)) ∧ J≠0 := by
  obtain ⟨J,hJ,hcop,hJ0⟩ := exists_prime_separation I p hI hp0
  exact ⟨J,hJ,((maximal_coprime_of_not_dvd p L hL).mul_left
    (maximal_coprime_of_not_dvd p R hR)).mul_left hcop |>.pow_right,hJ0⟩

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1729

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramResidue.lean; sha256: 6e343efbdc68ed9d8472273b5549a67a39f2f36036a90541cfb720687ff264c9 -/
section Source1730
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

theorem exists_nonexceptional_residue (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (hC : C≠0) (hk0 : k≠0) (u : Oˣ) (a b : ℕ) (r : O)
    (hr : Supported (Ideal.span {r})) (hk : k=u.val*goodLambda^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (hfac : Ideal.span {C}=∏i,P i^c i)
    (p : Id) [p.IsMaximal] (hp0 : p≠0) (hgp : goodLambda∉p)
    (hchar : ringChar (O⧸p)≠2) (hfixed : ¬p∣jointFixedModulus S hS) (hcommon : ¬p∣∏i,P i)
    (he : ¬6∣(normalizedFactors (Ideal.span {r})).count p) :
    ∃(M : Id)(hM : M≠0),
      Ideal.absNorm M≤Ideal.absNorm (jointFixedModulus S hS)*
        Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) ∧
      letI : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient hM
      letI : Fintype (O⧸M):=Fintype.ofFinite _
      ∀d : O,∃A : (O⧸M)→(O⧸M)→ℂ,
        (∀n₁ n₂,A (Ideal.Quotient.mk M n₁) (Ideal.Quotient.mk M n₂)=
          jointExtension S hS σ C k u a b r hr P hg c (d*n₁) (d*n₂)) ∧
        (∀x y,‖A x y‖≤Ideal.absNorm (Ideal.span {C})) ∧
        (∑x,∑y,A x y)=0 := by
  obtain ⟨J,hJ,hcop,hJ0⟩ := exists_nonexceptional_separation (jointFixedModulus S hS)
    (∏i,P i) (Ideal.span {r}) p hr.1 hp0 hfixed hcommon
  let e := (normalizedFactors (Ideal.span {r})).count p
  let M : Id := (jointFixedModulus S hS*(∏i,P i)*J)*p^e
  have hMperiod : M=jointPeriod S hS P r := by
    rw [jointPeriod,hJ]
    dsimp [M,e]
    ring
  have hM0 : M≠0 := hMperiod ▸ jointPeriod_nonzero S hS C hC P c hc hfac r
    (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr)
  refine ⟨M,hM0,?_,?_⟩
  · rw [hMperiod]
    exact jointPeriod_norm_bound S hS C k hC hk0 u a b r hk P c hc hfac
  · let : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient hM0
    let : Fintype (O⧸M) := Fintype.ofFinite _
    let : Finite (O⧸jointFixedModulus S hS*(∏i,P i)*J) :=
      Ring.HasFiniteQuotients.finiteQuotient (left_ne_zero_of_mul hM0)
    let : Fintype (O⧸jointFixedModulus S hS*(∏i,P i)*J) := Fintype.ofFinite _
    let : Finite (O⧸p^e) := Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ hp0)
    let : Fintype (O⧸p^e) := Fintype.ofFinite _
    intro d
    let A : (O⧸M)→(O⧸M)→ℂ := fun x y=>
      jointExtension S hS σ C k u a b r hr P hg c (d*x.out) (d*y.out)
    refine ⟨A,?_,?_,?_⟩
    · intro n₁ n₂
      apply jointExtension_dilation_periodic
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk M n₁))
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk M n₂))
    · intro x y
      rw [hfac]
      exact jointExtension_norm S hS σ C k u a b r hr P hg c hc _ _
    · exact jointExtension_mean_zero S hS σ C k u a b r hr P hg c J p hgp hchar e he hJ hcop d

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1730

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramShell.lean; sha256: 86c9d12bd6e9bc48949cf0745dcd36334a0f760ab7dfa83d5b3d07f57d3bd1c0 -/
section Source1731
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical EisensteinSchwartzPoisson

def shellProfile (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ) : ℂ :=
  lowGramProfile W v x*star (lowGramProfile W v y)*paperRadialFourier U (T/(x*y))

lemma shellProfile_zero_left (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ)
    (hx : W x=0) : shellProfile W v U T x y=0 := by
  simp [shellProfile,lowGramProfile,hx]

lemma shellProfile_zero_right (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ)
    (hy : W y=0) : shellProfile W v U T x y=0 := by
  simp [shellProfile,lowGramProfile,hy]

theorem shellProfile_weighted_bound (a b B : ℝ) (ha : 0<a) (hB : 0≤B) (A : ℕ) :
    ∃s : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
      ∀(W : ℝ→ℂ),(Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤B)→
      ∀(U : SchwartzMap ℝ ℂ)(v T x y : ℝ),0≤T→
        (1+T)^A*‖shellProfile W v U T x y‖≤
          C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := by
  obtain ⟨s,C,hC,hpaper⟩ := paperRadialFourier_euler_source_weighted_bound A 0
  refine ⟨s,(1+B/a)^2*(1+b^2)^A*C,by positivity,?_⟩
  intro W hs hW U v T x y hT
  by_cases hx : W x=0
  · rw [shellProfile_zero_left _ _ _ _ _ _ hx,norm_zero,mul_zero]
    positivity
  by_cases hy : W y=0
  · rw [shellProfile_zero_right _ _ _ _ _ _ hy,norm_zero,mul_zero]
    positivity
  have hxa := (hs hx).1
  have hya := (hs hy).1
  have hxb := (hs hx).2
  have hyb := (hs hy).2
  have hx0 := ha.trans_le hxa
  have hy0 := ha.trans_le hya
  have hxy : 0<x*y := mul_pos hx0 hy0
  have hxyb : x*y≤b^2 := by nlinarith [mul_le_mul hxb hyb hy0.le (hx0.le.trans hxb)]
  have ht : 0≤T/(x*y) := div_nonneg hT hxy.le
  have hp := hpaper U 0 (by omega) (T/(x*y)) ht
  simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hp
  have hscale : 1+T≤(1+b^2)*(1+T/(x*y)) := by
    have he : T=(x*y)*(T/(x*y)) := by field_simp
    have hbound := mul_le_mul_of_nonneg_right hxyb ht
    rw [←he] at hbound
    nlinarith [sq_nonneg b]
  have hp' : (1+T)^A*‖paperRadialFourier U (T/(x*y))‖≤
      (1+b^2)^A*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) := by
    calc
      _ ≤ ((1+b^2)*(1+T/(x*y)))^A*‖paperRadialFourier U (T/(x*y))‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hscale _) (norm_nonneg _)
      _ = (1+b^2)^A*((1+T/(x*y))^A*‖paperRadialFourier U (T/(x*y))‖) := by rw [mul_pow];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  have hwx : ‖lowGramProfile W v x‖≤1+B/a := by
    rw [lowGramProfile_norm W v x hx0]
    exact (div_le_div₀ hB (hW x) ha hxa).trans (by linarith)
  have hwy : ‖lowGramProfile W v y‖≤1+B/a := by
    rw [lowGramProfile_norm W v y hy0]
    exact (div_le_div₀ hB (hW y) ha hya).trans (by linarith)
  rw [shellProfile,norm_mul,norm_mul,norm_star]
  calc
    _ = (‖lowGramProfile W v x‖*‖lowGramProfile W v y‖)*
        ((1+T)^A*‖paperRadialFourier U (T/(x*y))‖) := by ring
    _ ≤ (1+B/a)^2*((1+b^2)^A*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      apply mul_le_mul _ hp' (by positivity) (by positivity)
      nlinarith [mul_le_mul hwx hwy (norm_nonneg _) (by positivity : 0≤1+B/a)]
    _ = _ := by ring

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1731

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramWindowMobius.lean; sha256: 7ca32dbbb91f3ab9fdd048ebb3d78a2c7372a93c5537c241db5bf50146e89bb9 -/
section Source1732
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma primary_norm (I : SupportedIdeal) :
    ‖eisEmbedding (primaryGenerator I.val)‖^2=(Ideal.absNorm I.val:ℝ) := by
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1]

lemma shell_dilated_column (D I : SupportedIdeal) (N : ℝ) :
    (Ideal.absNorm (supportedIdealProduct D I).val:ℝ)/N=
      ‖eisEmbedding (primaryGenerator I.val)‖^2/(N/Ideal.absNorm D.val) := by
  rw [primary_norm,supported_dilation_norm,Nat.cast_mul]
  rw [div_div_eq_mul_div]
  ring

lemma shell_window_support (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (I J : SupportedIdeal)
    (h : I∉lowGaussColumns W hW N hN ∨ J∉lowGaussColumns W hW N hN) :
    shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N)=0 := by
  rcases h with h|h
  · apply shellProfile_zero_left
    simpa only [lowGaussColumns_mem,not_not] using h
  · apply shellProfile_zero_right
    simpa only [lowGaussColumns_mem,not_not] using h

theorem original_window_mobius_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k : O) (hC : λ₀^2∣C-1)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) :
    (∑I∈lowGaussColumns W hW N hN,∑J∈lowGaussColumns W hW N hN,
      if IsCoprime I.val J.val then
        jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator I.val) (primaryGenerator J.val)*
          shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N) else 0)=
      ∑D∈divisorPool (lowGaussColumns W hW N hN) Subtype.val,(moebius D:ℂ)*
        ∑'n : O,∑'m : O,
          jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator D*n) (primaryGenerator D*m)*
            shellProfile W v U T (‖eisEmbedding n‖^2/(N/Ideal.absNorm D))
              (‖eisEmbedding m‖^2/(N/Ideal.absNorm D)) := by
  let F := lowGaussColumns W hW N hN
  let f := fun I J : SupportedIdeal=>jointExtension S hS σ C k u a b r hr P hg c
    (primaryGenerator I.val) (primaryGenerator J.val)*
      shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N)
  have hf : ∀I J,I∉F ∨ J∉F→f I J=0 := by
    intro I J h
    dsimp [f]
    rw [shell_window_support W hW N hN U v T I J h,mul_zero]
  change (∑I∈F,∑J∈F,if IsCoprime I.val J.val then f I J else 0)=_
  rw [finite_pair_mobius_dilation F F f hf]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  let D₀ := poolDivisor F D
  have hd : D₀.val=D := poolDivisor_val F D hD
  have hdp : λ₀^2∣primaryGenerator D₀.val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ D₀.property)).2
  have he := jointExtension_ideal_lattice S hS hbad σ C k (primaryGenerator D₀.val)
    (primary_product C _ hC hdp) u a b r hr P hg c
    (fun n m=>shellProfile W v U T (‖eisEmbedding n‖^2/(N/Ideal.absNorm D₀.val))
      (‖eisEmbedding m‖^2/(N/Ideal.absNorm D₀.val)))
  dsimp only [f]
  simp only [supported_dilation_generator,shell_dilated_column]
  convert he using 1
  rw [hd]

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1732

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramLatticeDecay.lean; sha256: 3deb1e33c61e6b0a79e024236a040e237f7bc3c9adc6ca94ccd313e767a9d889 -/
section Source1733
namespace OAI

noncomputable section
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramLatticeDecay
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

abbrev Joint := WithLp 2 (ℂ × ℂ)

def point (x y : ℂ) : Joint := WithLp.toLp 2 (x,y)

def sourceControl (S : Finset (ℕ × ℕ)) (W : 𝓢(Joint, ℂ)) : ℝ :=
  S.sup (schwartzSeminormFamily ℝ Joint ℂ) W

theorem sourceControl_nonneg (S : Finset (ℕ × ℕ)) (W : 𝓢(Joint, ℂ)) :
    0 ≤ sourceControl S W := apply_nonneg _ _

@[simp] theorem norm_point_sq (x y : ℂ) :
    ‖point x y‖^2 = ‖x‖^2 + ‖y‖^2 := WithLp.prod_norm_sq_eq_of_L2 _

theorem product_decay (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ((1+‖x‖^2)^2 * (1+‖y‖^2)^2) * ‖W (point x y)‖ ≤
      (2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W := by
  have hx := WithLp.norm_fst_le ℂ (point x y)
  have hy := WithLp.norm_snd_le ℂ (point x y)
  change ‖x‖ ≤ ‖point x y‖ at hx
  change ‖y‖ ≤ ‖point x y‖ at hy
  have hx2 : 1+‖x‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hy2 : 1+‖y‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hpow : (1+‖x‖^2)^2 * (1+‖y‖^2)^2 ≤ (1+‖point x y‖)^8 := by
    calc
      _ ≤ ((1+‖point x y‖)^2)^2 * ((1+‖point x y‖)^2)^2 := by gcongr
      _ = _ := by ring
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (8,0)) (k := 8) (n := 0) le_rfl le_rfl W (point x y)
  simp only [norm_iteratedFDeriv_zero] at h
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans h

def physicalPoint (N : ℝ) (m : O × O) : Joint :=
  point (eisEmbedding m.1 / (Real.sqrt N : ℂ))
    (eisEmbedding m.2 / (Real.sqrt N : ℂ))

theorem physicalPoint_eq_smul (N : ℝ) (m : O × O) :
    physicalPoint N m = (Real.sqrt N)⁻¹ • point (eisEmbedding m.1) (eisEmbedding m.2) := by
  apply WithLp.ofLp_injective
  simp [physicalPoint, point, div_eq_mul_inv, Algebra.smul_def, mul_comm]

theorem physical_summable (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N) :
    Summable (fun m : O × O => ‖W (physicalPoint N m)‖) := by
  let g : O → ℝ := fun m => ((1+N⁻¹*‖eisEmbedding m‖^2)^2)⁻¹
  have hg : Summable g := scaled_eisenstein_cauchy_summable _ (inv_pos.mpr hN)
  have hp := hg.mul_of_nonneg hg (fun _ => by dsimp [g]; positivity)
    (fun _ => by dsimp [g]; positivity)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hp.mul_left ((2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W))
  intro m
  have hb := product_decay W (eisEmbedding m.1 / (Real.sqrt N : ℂ))
    (eisEmbedding m.2 / (Real.sqrt N : ℂ))
  have hnorm (m : O) : ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 = N⁻¹*‖eisEmbedding m‖^2 := by
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hN.le]
    ring
  simp only [hnorm] at hb
  change ‖W (physicalPoint N m)‖ ≤ ((2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W) * (g m.1*g m.2)
  dsimp only [g]
  rw [ ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa only [physicalPoint, mul_comm] using hb

theorem physical_lattice_bound :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (N : ℝ), 1 ≤ N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2 := by
  refine ⟨Finset.Iic (8,0), (2:ℝ)^8 * (4*(1+Real.pi)^2)^2, by positivity, ?_⟩
  intro W N hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let g : O → ℝ := fun m => ((1+N⁻¹*‖eisEmbedding m‖^2)^2)⁻¹
  have hg : Summable g := scaled_eisenstein_cauchy_summable _ (inv_pos.mpr hNp)
  have hp := hg.mul_of_nonneg hg (fun _ => by dsimp [g]; positivity)
    (fun _ => by dsimp [g]; positivity)
  have hpoint (m : O × O) : ‖W (physicalPoint N m)‖ ≤
      ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W) * (g m.1*g m.2) := by
    have hb := product_decay W (eisEmbedding m.1 / (Real.sqrt N : ℂ))
      (eisEmbedding m.2 / (Real.sqrt N : ℂ))
    have hn (m : O) : ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 = N⁻¹*‖eisEmbedding m‖^2 := by
      rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hNp.le]
      ring
    simp only [hn] at hb
    dsimp only [g]
    rw [ ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    simpa only [physicalPoint, mul_comm] using hb
  have hmass : (∑' m : O, g m) ≤ (4*(1+Real.pi)^2)*N := by
    have h := scaled_eisenstein_cauchy_small N⁻¹ (inv_pos.mpr hNp) ((inv_le_one₀ hNp).mpr hN)
    have hh := mul_le_mul_of_nonneg_left h hNp.le
    simpa only [g, ← mul_assoc, mul_inv_cancel₀ hNp.ne', one_mul, mul_comm] using hh
  calc
    _ ≤ ∑' m : O × O, ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(g m.1*g m.2) :=
      (physical_summable W N hNp).tsum_le_tsum hpoint (hp.mul_left _)
    _ = ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(∑' m : O, g m)^2 := by
      rw [tsum_mul_left, ← hg.tsum_mul_tsum hg hp, pow_two]
    _ ≤ ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*((4*(1+Real.pi)^2)*N)^2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (sourceControl_nonneg _ _))
      exact pow_le_pow_left₀ (tsum_nonneg (fun _ => by dsimp [g]; positivity)) hmass 2
    _ = _ := by ring

abbrev DualIndex := (ℤ × ℤ) × (ℤ × ℤ)

def dualPoint (p : DualIndex) : Joint :=
  point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)

def dualRow (p : DualIndex) : Fin 2 → O :=
  ![dualFrequencyEquiv p.1, dualFrequencyEquiv p.2]

def dualCoordinates (p : DualIndex) : (Fin 2 × Fin 2) → ℤ :=
  CubicEisenstein.rowCoordinates (dualRow p)

theorem dualCoordinates_injective : Function.Injective dualCoordinates := by
  intro p q hp
  have h := CubicEisenstein.rowCoordinates_injective hp
  apply Prod.ext
  · exact dualFrequencyEquiv.injective (congrFun h 0)
  · exact dualFrequencyEquiv.injective (congrFun h 1)

@[simp] theorem dualCoordinates_zero : dualCoordinates 0 = 0 := by
  have hzero : ActualEisensteinCoordinates.coords (0 : O) = (0,0) := by
    simpa [ActualEisensteinCoordinates.eval] using ShortDraftLatticeCount.coords_eval 0 0
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [dualCoordinates, CubicEisenstein.rowCoordinates, dualRow,
      dualFrequencyEquiv, ActualEisensteinCoordinates.eval, hzero]

theorem dualCoordinates_norm_le (p : DualIndex) :
    ‖dualCoordinates p‖ ≤ 2 * ‖dualPoint p‖ := by
  have hc := CubicEisenstein.coordinates_norm_bound (dualRow p)
  have hp : ‖fun i => eisEmbedding (dualRow p i)‖ ≤ ‖dualPoint p‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have h1 := explicitDualFrequency_norm_sq 1 p.1
    have h2 := explicitDualFrequency_norm_sq 1 p.2
    norm_num only [norm_one, one_pow, div_one] at h1 h2
    have hq := norm_point_sq (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)
    fin_cases i
    · change ‖eisEmbedding (dualFrequencyEquiv p.1)‖ ≤ ‖dualPoint p‖
      dsimp only [dualPoint]
      nlinarith [sq_nonneg ‖eisEmbedding (dualFrequencyEquiv p.2)‖,
        norm_nonneg (point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)),
        norm_nonneg (eisEmbedding (dualFrequencyEquiv p.1))]
    · change ‖eisEmbedding (dualFrequencyEquiv p.2)‖ ≤ ‖dualPoint p‖
      dsimp only [dualPoint]
      nlinarith [sq_nonneg ‖eisEmbedding (dualFrequencyEquiv p.1)‖,
        norm_nonneg (point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)),
        norm_nonneg (eisEmbedding (dualFrequencyEquiv p.2))]
  exact hc.trans (mul_le_mul_of_nonneg_left hp (by norm_num))

theorem dualPoint_norm_pos (p : DualIndex) (hp : p ≠ 0) : 0 < ‖dualPoint p‖ := by
  have hc : dualCoordinates p ≠ 0 := by
    intro h
    exact hp (dualCoordinates_injective (h.trans dualCoordinates_zero.symm))
  have hh := norm_pos_iff.mpr hc
  have hb := dualCoordinates_norm_le p
  linarith

theorem dual_power_summable (k : ℝ) (hk : 4 < k) :
    Summable (fun p : {p : DualIndex // p ≠ 0} => ‖dualPoint p.val‖ ^ (-k)) := by
  have hs : Summable (fun p : {p : DualIndex // p ≠ 0} => ‖dualCoordinates p.val‖ ^ (-k)) :=
    (CubicEisenstein.summable_integer_four_rpow k hk).comp_injective
    (dualCoordinates_injective.comp (Subtype.val_injective))
  apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _) _
    (hs.mul_left ((2:ℝ)^k))
  intro p
  have hc : 0 < ‖dualCoordinates p.val‖ := norm_pos_iff.mpr (by
    intro h
    exact p.property (dualCoordinates_injective (h.trans dualCoordinates_zero.symm)))
  have h := Real.rpow_le_rpow_of_nonpos (half_pos hc)
    (by have := dualCoordinates_norm_le p.val; linarith : ‖dualCoordinates p.val‖ / 2 ≤ ‖dualPoint p.val‖)
    (by linarith : -k ≤ 0)
  calc
    _ ≤ (‖dualCoordinates p.val‖ / 2) ^ (-k) := h
    _ = (2:ℝ)^k * ‖dualCoordinates p.val‖ ^ (-k) := by
      rw [Real.div_rpow (norm_nonneg _) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      simp only [div_inv_eq_mul, mul_comm]

def scaledDualPoint (L : ℝ) (u : ℂ) (p : DualIndex) : Joint :=
  point (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)

theorem norm_scaledDualPoint (L : ℝ) (hL : 0 ≤ L) (u : ℂ) (hu : ‖u‖ = 1)
    (p : DualIndex) : ‖scaledDualPoint L u p‖ = L * ‖dualPoint p‖ := by
  have h1 := norm_point_sq (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)
  have h2 := norm_point_sq (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)
  simp only [norm_mul, hu, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL,
    one_mul] at h1
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  change ‖point (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)‖^2 =
      (L*‖point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)‖)^2
  simp only [h1, mul_pow, h2]
  ring

theorem fourier_seminorm_control (k : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(Joint, ℂ),
      SchwartzMap.seminorm ℝ k 0 (𝓕 W) ≤ C * sourceControl S W := by
  let T : 𝓢(Joint, ℂ) →L[ℝ] 𝓢(Joint, ℂ) := SchwartzMap.fourierTransformCLM ℝ
  let q : Seminorm ℝ 𝓢(Joint, ℂ) := (SchwartzMap.seminorm ℝ k 0).comp T.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ Joint ℂ).continuous_seminorm (k,0)).comp T.continuous
  obtain ⟨S,C,hC,hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ Joint ℂ) q hq
  refine ⟨S,C,?_,?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W
    exact Seminorm.le_def.mp hbound W

theorem scaledDual_decay (F : 𝓢(Joint, ℂ)) (k : ℕ) (L : ℝ) (hL : 0 < L)
    (u : ℂ) (hu : ‖u‖ = 1) (p : DualIndex) (hp : p ≠ 0) :
    ‖F (scaledDualPoint L u p)‖ ≤ SchwartzMap.seminorm ℝ k 0 F *
      L^(-(k:ℝ)) * ‖dualPoint p‖^(-(k:ℝ)) := by
  have hn : 0 < ‖scaledDualPoint L u p‖ := by
    rw [norm_scaledDualPoint L hL.le u hu]
    exact mul_pos hL (dualPoint_norm_pos p hp)
  have hb := SchwartzMap.norm_pow_mul_le_seminorm ℝ F k (scaledDualPoint L u p)
  have hh : ‖F (scaledDualPoint L u p)‖ ≤
      SchwartzMap.seminorm ℝ k 0 F * ‖scaledDualPoint L u p‖^(-(k:ℝ)) := by
    rw [Real.rpow_neg hn.le, Real.rpow_natCast, ← div_eq_mul_inv,
      le_div_iff₀ (pow_pos hn k)]
    simpa only [mul_comm] using hb
  rw [norm_scaledDualPoint L hL.le u hu,
    Real.mul_rpow hL.le (norm_nonneg _)] at hh
  simpa only [mul_assoc] using hh

theorem dual_fourier_summable (A : ℕ) (hA : 2 < A)
    (W : 𝓢(Joint, ℂ)) (L : ℝ) (hL : 0 < L) (u : ℂ) (hu : ‖u‖ = 1) :
    Summable (fun p : {p : DualIndex // p ≠ 0} => ‖(𝓕 W) (scaledDualPoint L u p.val)‖) := by
  have hdim : (4:ℝ) < ((2*A:ℕ):ℝ) := by exact_mod_cast (by omega : 4 < 2*A)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((dual_power_summable ((2*A:ℕ):ℝ) hdim).mul_left
      (SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ))))
  intro p
  exact scaledDual_decay (𝓕 W) (2*A) L hL u hu p.val p.property

theorem dual_fourier_lattice_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (L : ℝ), 1 ≤ L → ∀ (u : ℂ), ‖u‖ = 1 →
        (∑' p : {p : DualIndex // p ≠ 0}, ‖(𝓕 W) (scaledDualPoint L u p.val)‖) ≤
          C * sourceControl S W * L^(-((2*A:ℕ):ℝ)) := by
  obtain ⟨S,C,hC,hbound⟩ := fourier_seminorm_control (2*A)
  let mass : ℝ := ∑' p : {p : DualIndex // p ≠ 0}, ‖dualPoint p.val‖^(-((2*A:ℕ):ℝ))
  have hm : 0 ≤ mass := tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨S,C*(mass+1),mul_pos hC (by positivity),?_⟩
  intro W L hL u hu
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hdim : (4:ℝ) < ((2*A:ℕ):ℝ) := by exact_mod_cast (by omega : 4 < 2*A)
  calc
    _ ≤ ∑' p : {p : DualIndex // p ≠ 0},
        (SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ))) *
          ‖dualPoint p.val‖^(-((2*A:ℕ):ℝ)) :=
      (dual_fourier_summable A hA W L hLp u hu).tsum_le_tsum
        (fun p => scaledDual_decay (𝓕 W) (2*A) L hLp u hu p.val p.property)
        ((dual_power_summable ((2*A:ℕ):ℝ) hdim).mul_left _)
    _ = SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ)) * mass := tsum_mul_left
    _ ≤ (C * sourceControl S W) * L^(-((2*A:ℕ):ℝ)) * (mass+1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (hbound W) (Real.rpow_nonneg hLp.le _)
      · linarith
      · exact hm
      · exact mul_nonneg (mul_nonneg hC.le (sourceControl_nonneg S W)) (Real.rpow_nonneg hLp.le _)
    _ = _ := by ring

theorem sourceControl_mono {S T : Finset (ℕ × ℕ)} (hST : S ⊆ T)
    (W : 𝓢(Joint, ℂ)) : sourceControl S W ≤ sourceControl T W :=
  Seminorm.le_def.mp (Finset.sup_mono hST) W

theorem joint_lattice_bounds (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      (∀ (W : 𝓢(Joint, ℂ)) (N : ℝ), 1 ≤ N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2) ∧
      (∀ (W : 𝓢(Joint, ℂ)) (L : ℝ), 1 ≤ L → ∀ (u : ℂ), ‖u‖ = 1 →
        (∑' p : {p : DualIndex // p ≠ 0}, ‖(𝓕 W) (scaledDualPoint L u p.val)‖) ≤
          C * sourceControl S W * L^(-((2*A:ℕ):ℝ))) := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩ := physical_lattice_bound
  obtain ⟨S₂,C₂,hC₂,h₂⟩ := dual_fourier_lattice_bound A hA
  refine ⟨S₁∪S₂,C₁+C₂,add_pos hC₁ hC₂,?_,?_⟩
  · intro W N hN
    apply (h₁ W N hN).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul (le_add_of_nonneg_right hC₂.le)
      (sourceControl_mono Finset.subset_union_left W) (sourceControl_nonneg _ _) (by positivity)
  · intro W L hL u hu
    apply (h₂ W L hL u hu).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact mul_le_mul (le_add_of_nonneg_left hC₁.le)
      (sourceControl_mono Finset.subset_union_right W) (sourceControl_nonneg _ _) (by positivity)

end ProbeGramLatticeDecay

end

end OAI

end Source1733

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramAnnularLattice.lean; sha256: a9ccbd0bc3e40cac77aed15e5d1d9e95efdebad72309ef1e0fee3fcfbf2ef66f -/
section Source1734
namespace OAI

noncomputable section
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramAnnularLattice
open ProbeGramLatticeDecay ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def AnnularSupport (a b : ℝ) (W : 𝓢(Joint, ℂ)) : Prop :=
  Function.support W ⊆ {z : Joint | a ≤ ‖z.fst‖^2 ∧ ‖z.fst‖^2 ≤ b ∧
    a ≤ ‖z.snd‖^2 ∧ ‖z.snd‖^2 ≤ b}

theorem scaled_embedding_norm_sq (m : O) (N : ℝ) (hN : 0 ≤ N) :
    ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 = ‖eisEmbedding m‖^2 / N := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hN]

theorem physical_sample_eq_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (W : 𝓢(Joint, ℂ)) (hW : AnnularSupport a b W)
    (N : ℝ) (hN : 0 < N) (hsmall : N < b⁻¹) (m : O × O) :
    W (physicalPoint N m) = 0 := by
  by_contra h
  have hw := hW h
  change a ≤ ‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2 ∧
    ‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2 ≤ b ∧ _ at hw
  have hm : m.1 ≠ 0 := by
    intro hz
    have hh := hw.1
    rw [hz, map_zero, zero_div, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hh
    linarith
  have hl := one_le_eisenstein_norm_sq m.1 hm
  have hu := hw.2.1
  rw [scaled_embedding_norm_sq m.1 N hN.le, div_le_iff₀ hN] at hu
  have hs : b*N < 1 := by
    have hh := mul_lt_mul_of_pos_left hsmall hb
    simpa only [mul_inv_cancel₀ hb.ne'] using hh
  linarith

def cauchyWeight (m : O) : ℝ := ((1+‖eisEmbedding m‖^2)^2)⁻¹

theorem cauchyWeight_summable : Summable cauchyWeight := by
  change Summable (fun m : O => ((1+‖eisEmbedding m‖^2)^2)⁻¹)
  simpa only [one_mul] using scaled_eisenstein_cauchy_summable 1 zero_lt_one

theorem cauchyWeight_mass_le : (∑' m : O, cauchyWeight m) ≤ 4*(1+Real.pi)^2 := by
  simpa only [cauchyWeight, one_mul] using scaled_eisenstein_cauchy_small 1 zero_lt_one le_rfl

theorem physical_subunit_majorant (W : 𝓢(Joint, ℂ))
    (N : ℝ) (hN : 0 < N) (hN1 : N ≤ 1) (m : O × O) :
    ‖W (physicalPoint N m)‖ ≤ (2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W *
      (cauchyWeight m.1 * cauchyWeight m.2) := by
  have hn (m : O) : ‖eisEmbedding m‖^2 ≤ ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 := by
    rw [scaled_embedding_norm_sq m N hN.le, le_div_iff₀ hN]
    exact mul_le_of_le_one_right (sq_nonneg _) hN1
  have hd : (1+‖eisEmbedding m.1‖^2)^2 * (1+‖eisEmbedding m.2‖^2)^2 ≤
      (1+‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2)^2 *
        (1+‖eisEmbedding m.2 / (Real.sqrt N : ℂ)‖^2)^2 := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) (hn m.1)) 2)
      (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) (hn m.2)) 2) (by positivity) (by positivity)
  have hp := (mul_le_mul_of_nonneg_right hd (norm_nonneg (W (physicalPoint N m)))).trans
    (product_decay W (eisEmbedding m.1 / (Real.sqrt N : ℂ))
      (eisEmbedding m.2 / (Real.sqrt N : ℂ)))
  dsimp only [cauchyWeight]
  rw [← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using hp

theorem physical_subunit_bound (W : 𝓢(Joint, ℂ))
    (N : ℝ) (hN : 0 < N) (hN1 : N ≤ 1) :
    (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤
      ((2:ℝ)^8*(4*(1+Real.pi)^2)^2) * sourceControl (Finset.Iic (8,0)) W := by
  have hg := cauchyWeight_summable
  have hp := hg.mul_of_nonneg hg (fun _ => by unfold cauchyWeight; positivity)
    (fun _ => by unfold cauchyWeight; positivity)
  calc
    _ ≤ ∑' m : O × O, ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*
        (cauchyWeight m.1*cauchyWeight m.2) :=
      (physical_summable W N hN).tsum_le_tsum (physical_subunit_majorant W N hN hN1)
        (hp.mul_left _)
    _ = ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(∑' m : O, cauchyWeight m)^2 := by
      rw [tsum_mul_left, ← hg.tsum_mul_tsum hg hp, pow_two]
    _ ≤ ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(4*(1+Real.pi)^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (sourceControl_nonneg _ _))
      exact pow_le_pow_left₀ (tsum_nonneg (fun _ => by unfold cauchyWeight; positivity))
        cauchyWeight_mass_le 2
    _ = _ := by ring

theorem annular_lattice_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), AnnularSupport a b W → ∀ (N : ℝ), 0 < N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2 := by
  obtain ⟨S₀,C₀,hC₀,h₀⟩ := physical_lattice_bound
  let K : ℝ := (2:ℝ)^8*(4*(1+Real.pi)^2)^2
  have hK : 0 < K := by dsimp [K]; positivity
  have hb : 0 < b := ha.trans hab
  refine ⟨S₀ ∪ Finset.Iic (8,0),C₀ + K*b^2,by positivity,?_⟩
  intro W hW N hN
  have hS₀ := sourceControl_mono (S := S₀) (T := S₀ ∪ Finset.Iic (8,0)) Finset.subset_union_left W
  have hS₁ := sourceControl_mono (S := Finset.Iic (8,0))
    (T := S₀ ∪ Finset.Iic (8,0)) Finset.subset_union_right W
  by_cases hN1 : 1 ≤ N
  · apply (h₀ W N hN1).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul (le_add_of_nonneg_right (by positivity)) hS₀
      (sourceControl_nonneg _ _) (by positivity)
  · by_cases hs : N < b⁻¹
    · have hz : (∑' m : O × O, ‖W (physicalPoint N m)‖) = 0 := by
        calc
          _ = ∑' _m : O × O, (0:ℝ) := tsum_congr (fun m => by
            rw [physical_sample_eq_zero a b ha hb W hW N hN hs m, norm_zero])
          _ = 0 := tsum_zero
      rw [hz]
      exact mul_nonneg (mul_nonneg (by positivity) (sourceControl_nonneg _ _)) (sq_nonneg _)
    · have hBN : 1 ≤ b*N := by
        have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hs) hb.le
        simpa only [mul_inv_cancel₀ hb.ne'] using hh
      have hBN2 : 1 ≤ b^2*N^2 := by nlinarith [sq_nonneg (b*N-1)]
      calc
        _ ≤ K * sourceControl (Finset.Iic (8,0)) W :=
          physical_subunit_bound W N hN (le_of_not_ge hN1)
        _ ≤ K * sourceControl (S₀ ∪ Finset.Iic (8,0)) W :=
          mul_le_mul_of_nonneg_left hS₁ hK.le
        _ ≤ (K * sourceControl (S₀ ∪ Finset.Iic (8,0)) W) * (b^2*N^2) :=
          le_mul_of_one_le_right (mul_nonneg hK.le (sourceControl_nonneg _ _)) hBN2
        _ = (K*b^2) * sourceControl (S₀ ∪ Finset.Iic (8,0)) W * N^2 := by ring
        _ ≤ (C₀+K*b^2) * sourceControl (S₀ ∪ Finset.Iic (8,0)) W * N^2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀.le)
              (sourceControl_nonneg _ _)) (sq_nonneg _)

theorem weighted_summable (W : 𝓢(Joint, ℂ)) (d : O × O → ℂ) (B : ℝ)
    (hd : ∀ m, ‖d m‖ ≤ B) (N : ℝ) (hN : 0 < N) :
    Summable (fun m : O × O => d m * W (physicalPoint N m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((physical_summable W N hN).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hd m) (norm_nonneg _)

theorem annular_weighted_lattice_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), AnnularSupport a b W →
      ∀ (d : O × O → ℂ) (B : ℝ), 0 ≤ B → (∀ m, ‖d m‖ ≤ B) →
      ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O => d m * W (physicalPoint N m)) ∧
        ‖∑' m : O × O, d m * W (physicalPoint N m)‖ ≤ C * sourceControl S W * B * N^2 := by
  obtain ⟨S,C,hC,hbound⟩ := annular_lattice_bound a b ha hab
  refine ⟨S,C,hC,?_⟩
  intro W hW d B hB hd N hN
  refine ⟨weighted_summable W d B hd N hN,?_⟩
  calc
    _ ≤ ∑' m : O × O, B * ‖W (physicalPoint N m)‖ := by
      apply (norm_tsum_le_tsum_norm ((weighted_summable W d B hd N hN).norm)).trans
      apply ((weighted_summable W d B hd N hN).norm).tsum_le_tsum _
        ((physical_summable W N hN).mul_left B)
      intro m
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hd m) (norm_nonneg _)
    _ = B * ∑' m : O × O, ‖W (physicalPoint N m)‖ := tsum_mul_left
    _ ≤ B * (C * sourceControl S W * N^2) := mul_le_mul_of_nonneg_left (hbound W hW N hN) hB
    _ = _ := by ring

end ProbeGramAnnularLattice

end

end OAI

end Source1734

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramPeriodicPoisson.lean; sha256: 681a2be922084dfcd5900dcd733d3512b265758ae7ff8fdff60cb5a7fb2114d3 -/
section Source1735
namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramPeriodicPoisson

abbrev Joint := WithLp 2 (ℂ × ℂ)

def point (x y : ℂ) : Joint := WithLp.toLp 2 (x, y)

def embeddingPair (m : ActualEisensteinCubic.O × ActualEisensteinCubic.O) : Joint :=
  point (ConcreteTraceCRT.eisEmbedding m.1) (ConcreteTraceCRT.eisEmbedding m.2)

@[simp] theorem norm_point_sq (x y : ℂ) :
    ‖point x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

def leftInjection : ℂ →L[ℝ] Joint :=
  (((WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm.toLinearMap).comp
    (LinearMap.inl ℝ ℂ ℂ)).toContinuousLinearMap

def rightInjection : ℂ →L[ℝ] Joint :=
  (((WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm.toLinearMap).comp
    (LinearMap.inr ℝ ℂ ℂ)).toContinuousLinearMap

@[simp] theorem point_eq_add (x y : ℂ) :
    point x y = leftInjection x + rightInjection y := by
  change WithLp.toLp 2 (x,y) = WithLp.toLp 2 (x,0) + WithLp.toLp 2 (0,y)
  rw [← WithLp.toLp_add]
  simp

theorem slice_isometry (y : ℂ) : Isometry (fun x : ℂ => point x y) := by
  apply Isometry.of_dist_eq
  intro x z
  simp only [dist_eq_norm, point_eq_add, add_sub_add_right_eq_sub, ← map_sub]
  exact WithLp.norm_toLp_fst 2 ℂ ℂ (x-z)

theorem slice_temperate (y : ℂ) :
    (fun x : ℂ => point x y).HasTemperateGrowth := by
  simp only [point_eq_add]
  fun_prop

def leftSlice (W : 𝓢(Joint, ℂ)) (y : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (slice_temperate y)
    (slice_isometry y).antilipschitzWith W

@[simp] theorem leftSlice_apply (W : 𝓢(Joint, ℂ)) (y x : ℂ) :
    leftSlice W y x = W (point x y) := rfl

theorem fourier_joint_eq_iterated (f : Joint → ℂ) (hf : Integrable f) (ξ η : ℂ) :
    𝓕 f (point ξ η) =
      𝓕 (fun x : ℂ => 𝓕 (fun y : ℂ => f (point x y)) η) ξ := by
  let w : Joint := point ξ η
  let G : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z w) • f z
  have hG : Integrable G := (Real.fourierIntegral_convergent_iff w).mpr hf
  have hGp : Integrable (fun z : ℂ × ℂ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℂ ℂ).integrable_comp_of_integrable hG
  calc
    𝓕 f (point ξ η) = ∫ z : Joint, G z := rfl
    _ = ∫ z : ℂ × ℂ, G (WithLp.toLp 2 z) :=
      ((WithLp.volume_preserving_toLp ℂ ℂ).integral_comp
        (MeasurableEquiv.toLp 2 (ℂ × ℂ)).measurableEmbedding G).symm
    _ = ∫ x : ℂ, ∫ y : ℂ, G (WithLp.toLp 2 (x, y)) := integral_prod _ hGp
    _ = _ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          simp only [G, w, point, WithLp.prod_inner_apply,
            neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
            Circle.coe_mul, mul_assoc]

def partialFourier (W : 𝓢(Joint, ℂ)) (η x : ℂ) : ℂ :=
  𝓕 (fun y : ℂ => W (point x y)) η

def planeMajorant (y : ℂ) : ℝ := ((1 + ‖y‖ ^ 2) ^ 2)⁻¹

theorem planeMajorant_integrable : Integrable planeMajorant := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume)
    (r := 4) (by norm_num)
  change Integrable (fun y : ℂ => ((1 + ‖y‖ ^ 2) ^ 2)⁻¹)
  convert h using 1
  funext y
  rw [show -(4:ℝ)/2 = -(2:ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_two]

def majorantConstant (W : 𝓢(Joint, ℂ)) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 W + 2 * SchwartzMap.seminorm ℝ 2 0 W +
    SchwartzMap.seminorm ℝ 4 0 W

theorem norm_le_planeMajorant (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ‖W (point x y)‖ ≤ majorantConstant W * planeMajorant y := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ W (point x y)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ W 2 (point x y)
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ W 4 (point x y)
  have hy : ‖y‖^2 ≤ ‖point x y‖^2 := by rw [norm_point_sq]; exact le_add_of_nonneg_left (sq_nonneg _)
  have hy4 : ‖y‖^4 ≤ ‖point x y‖^4 := by nlinarith [sq_nonneg (‖x‖^2)]
  have hm2 := mul_le_mul_of_nonneg_right hy (norm_nonneg (W (point x y)))
  have hm4 := mul_le_mul_of_nonneg_right hy4 (norm_nonneg (W (point x y)))
  rw [planeMajorant, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  dsimp [majorantConstant]
  nlinarith

theorem partialFourier_continuous (W : 𝓢(Joint, ℂ)) (η : ℂ) :
    Continuous (partialFourier W η) := by
  change Continuous (fun x : ℂ => ∫ y : ℂ,
    Real.fourierChar (-inner ℝ y η) • W (point x y))
  apply continuous_of_dominated (bound := fun y => majorantConstant W * planeMajorant y)
  · intro x
    exact ((by fun_prop : Continuous (fun y : ℂ => Real.fourierChar (-inner ℝ y η))).smul
      (W.continuous.comp (show Continuous (fun y : ℂ => point x y) from by
        simp only [point_eq_add]; fun_prop))).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
        norm_le_planeMajorant W x y
  · exact planeMajorant_integrable.const_mul _
  · exact Eventually.of_forall fun y =>
      continuous_const.smul (W.continuous.comp (slice_isometry y).continuous)

theorem partialFourier_integrable (W : 𝓢(Joint, ℂ)) (η : ℂ) :
    Integrable (partialFourier W η) := by
  let G : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z.snd η) • W z
  have hG : Integrable G := W.integrable.norm.mono'
    (by fun_prop : Continuous G).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simp only [G, Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
      exact le_rfl)
  have hGp : Integrable (fun z : ℂ × ℂ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℂ ℂ).integrable_comp_of_integrable hG
  change Integrable (fun x : ℂ => ∫ y : ℂ,
    Real.fourierChar (-inner ℝ y η) • W (point x y))
  exact hGp.integral_prod_left

def partialFourierSchwartz (W : 𝓢(Joint, ℂ)) (η : ℂ) : 𝓢(ℂ, ℂ) :=
  𝓕⁻ (leftSlice (𝓕 W) η)

theorem partialFourierSchwartz_apply (W : 𝓢(Joint, ℂ)) (η x : ℂ) :
    partialFourierSchwartz W η x = partialFourier W η x := by
  have heq : 𝓕 (partialFourier W η) = (leftSlice (𝓕 W) η : ℂ → ℂ) := by
    funext ξ
    change 𝓕 (fun x : ℂ => 𝓕 (fun y : ℂ => W (point x y)) η) ξ = _
    rw [← fourier_joint_eq_iterated W W.integrable ξ η]
    exact (congrFun (SchwartzMap.fourier_coe W) (point ξ η)).symm
  have hi : Integrable (𝓕 (partialFourier W η)) := by
    rw [heq]
    exact (leftSlice (𝓕 W) η).integrable
  change (𝓕⁻ (leftSlice (𝓕 W) η)) x = _
  rw [congrFun (SchwartzMap.fourierInv_coe (leftSlice (𝓕 W) η)) x, ← heq]
  exact (partialFourier_integrable W η).fourierInv_fourier_eq hi
    (partialFourier_continuous W η).continuousAt

theorem fourier_partialFourierSchwartz (W : 𝓢(Joint, ℂ)) (ξ η : ℂ) :
    𝓕 (partialFourierSchwartz W η) ξ = (𝓕 W) (point ξ η) := by
  simp [partialFourierSchwartz]

theorem jointCLM_finite_seminorm_control
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : 𝓢(Joint, ℂ) →L[ℝ] 𝓢(E, ℂ)) (S : Finset (ℕ × ℕ)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(Joint, ℂ),
      S.sup (schwartzSeminormFamily ℝ E ℂ) (T W) ≤
        C * s.sup (schwartzSeminormFamily ℝ Joint ℂ) W := by
  let q : Seminorm ℝ 𝓢(Joint, ℂ) :=
    (S.sup (schwartzSeminormFamily ℝ E ℂ)).comp T.toLinearMap
  have hq : Continuous q :=
    (((schwartz_withSeminorms ℝ E ℂ).finset_sups).continuous_seminorm S).comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ Joint ℂ) q hq
  refine ⟨s, C, ?_, ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W
    exact Seminorm.le_def.mp hbound W

def productDecayConstant (W : 𝓢(Joint, ℂ)) : ℝ :=
  2 ^ (8:ℕ) * (Finset.Iic (8,0)).sup (schwartzSeminormFamily ℝ Joint ℂ) W

theorem product_decay (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ((1+‖x‖^2)^2 * (1+‖y‖^2)^2) * ‖W (point x y)‖ ≤ productDecayConstant W := by
  have hx := WithLp.norm_fst_le ℂ (point x y)
  have hy := WithLp.norm_snd_le ℂ (point x y)
  change ‖x‖ ≤ ‖point x y‖ at hx
  change ‖y‖ ≤ ‖point x y‖ at hy
  have hx2 : 1+‖x‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hy2 : 1+‖y‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hpow : (1+‖x‖^2)^2 * (1+‖y‖^2)^2 ≤ (1+‖point x y‖)^8 := by
    calc
      _ ≤ ((1+‖point x y‖)^2)^2 * ((1+‖point x y‖)^2)^2 := by gcongr
      _ = _ := by ring
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (8,0)) (k := 8) (n := 0) le_rfl le_rfl W (point x y)
  simp only [norm_iteratedFDeriv_zero] at h
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans h

theorem norm_le_product_majorant (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ‖W (point x y)‖ ≤ productDecayConstant W * (planeMajorant x * planeMajorant y) := by
  rw [planeMajorant, planeMajorant, ← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [mul_comm] using product_decay W x y

theorem planeMajorant_eisenstein_summable :
    Summable (fun m : ActualEisensteinCubic.O =>
      planeMajorant (ConcreteTraceCRT.eisEmbedding m)) := by
  have hs := CubicEisenstein.summable_embedding_rpow (-4) (by norm_num)
  rw [← Finset.summable_compl_iff (s := ({0} : Finset ActualEisensteinCubic.O))]
  apply Summable.of_nonneg_of_le (fun _ => by unfold planeMajorant; positivity) _
    (hs.subtype (fun m : ActualEisensteinCubic.O => m ∉ ({0} : Finset _)))
  intro m
  have hm : m.val ≠ 0 := by simpa using m.property
  have hn : 0 < ‖ConcreteTraceCRT.eisEmbedding m.val‖ := norm_pos_iff.mpr
    (ConcreteTraceCRT.eisEmbedding_ne_zero hm)
  change ((1+‖ConcreteTraceCRT.eisEmbedding m.val‖^2)^2)⁻¹ ≤
    ‖ConcreteTraceCRT.eisEmbedding m.val‖ ^ (-4:ℝ)
  rw [show (-4:ℝ) = -(4:ℝ) by rfl, Real.rpow_neg hn.le, Real.rpow_ofNat]
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg (‖ConcreteTraceCRT.eisEmbedding m.val‖^2)]

theorem joint_eisenstein_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun m : ActualEisensteinCubic.O × ActualEisensteinCubic.O =>
      ‖W (embeddingPair m)‖) := by
  have hs := planeMajorant_eisenstein_summable.mul_of_nonneg
    planeMajorant_eisenstein_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (hs.mul_left (productDecayConstant W))
  intro m
  exact norm_le_product_majorant W _ _

theorem joint_weighted_summable {R : Type*} (q : ActualEisensteinCubic.O → R)
    (a : R × R → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B) (W : 𝓢(Joint, ℂ)) :
    Summable (fun m : ActualEisensteinCubic.O × ActualEisensteinCubic.O =>
      a (q m.1,q m.2) * W (embeddingPair m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((joint_eisenstein_summable_norm W).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)

open scoped LineDeriv

theorem leftSlice_lineDeriv (F : 𝓢(Joint, ℂ)) (η v : ℂ) :
    ∂_{v} (leftSlice F η) = leftSlice (∂_{leftInjection v} F) η := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, leftSlice_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hd : HasFDerivAt (fun x : ℂ => point x η) leftInjection x := by
    simp only [point_eq_add]
    exact leftInjection.hasFDerivAt.add_const _
  have hc := (F.hasFDerivAt (point x η)).comp x hd
  change fderiv ℝ ((F : Joint → ℂ) ∘ (fun y => point y η)) x v = _
  rw [hc.fderiv]
  rfl

theorem norm_inverse_lineDeriv (g : 𝓢(ℂ, ℂ)) (v x : ℂ) :
    ‖(𝓕⁻ (∂_{v} g)) x‖ = (2 * Real.pi) * |inner ℝ x v| * ‖(𝓕⁻ g) x‖ := by
  have ht : (fun u : ℂ => inner ℝ u v).HasTemperateGrowth := by fun_prop
  have hc : ‖(-(2 * Real.pi * Complex.I) : ℂ)‖ = 2 * Real.pi := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    norm_smul]
  rw [hc]
  simp only [Real.norm_eq_abs, mul_assoc]

theorem inner_sq_mul_norm_inverse_le (g : 𝓢(ℂ, ℂ)) (v x : ℂ) :
    (inner ℝ x v)^2 * ‖(𝓕⁻ g) x‖ ≤ ‖(𝓕⁻ (∂_{v} (∂_{v} g))) x‖ := by
  rw [norm_inverse_lineDeriv, norm_inverse_lineDeriv]
  have hp : 1 ≤ (2 * Real.pi)^2 := by nlinarith [Real.pi_gt_three]
  calc
    _ ≤ ((2 * Real.pi)^2 * (inner ℝ x v)^2) * ‖(𝓕⁻ g) x‖ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg _) hp) (norm_nonneg _)
    _ = _ := by rw [← sq_abs (inner ℝ x v)]; ring

theorem norm_sq_mul_norm_inverse_le (g : 𝓢(ℂ, ℂ)) (x : ℂ) :
    ‖x‖^2 * ‖(𝓕⁻ g) x‖ ≤
      ‖(𝓕⁻ (∂_{(1:ℂ)} (∂_{(1:ℂ)} g))) x‖ +
      ‖(𝓕⁻ (∂_{Complex.I} (∂_{Complex.I} g))) x‖ := by
  have h1 := inner_sq_mul_norm_inverse_le g 1 x
  have hi := inner_sq_mul_norm_inverse_le g Complex.I x
  have he : (inner ℝ x (1:ℂ))^2 + (inner ℝ x Complex.I)^2 = ‖x‖^2 := by
    rw [Complex.sq_norm]
    simp [Complex.inner, Complex.normSq_apply, sq]
  rw [← he, add_mul]
  exact add_le_add h1 hi

theorem norm_inverse_leftSlice_le (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
      productDecayConstant F * planeMajorant η * ∫ y : ℂ, planeMajorant y := by
  have hb : Integrable (fun y : ℂ =>
      productDecayConstant F * planeMajorant η * planeMajorant y) :=
    planeMajorant_integrable.const_mul _
  have h := norm_integral_le_of_norm_le
    (f := fun y : ℂ => Real.fourierChar (inner ℝ y x) • leftSlice F η y) hb
    (Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul,
        leftSlice_apply, mul_left_comm, mul_assoc, mul_comm] using norm_le_product_majorant F y η)
  rw [congrFun (SchwartzMap.fourierInv_coe (leftSlice F η)) x, Real.fourierInv_eq]
  simpa only [integral_const_mul] using h

def leftSecondReal (F : 𝓢(Joint, ℂ)) : 𝓢(Joint, ℂ) :=
  ∂_{leftInjection (1:ℂ)} (∂_{leftInjection (1:ℂ)} F)

def leftSecondImag (F : 𝓢(Joint, ℂ)) : 𝓢(Joint, ℂ) :=
  ∂_{leftInjection Complex.I} (∂_{leftInjection Complex.I} F)

def sliceIntegralBound (F : 𝓢(Joint, ℂ)) : ℝ :=
  productDecayConstant F * ∫ y : ℂ, planeMajorant y

def firstDecayBound (F : 𝓢(Joint, ℂ)) : ℝ :=
  sliceIntegralBound F + sliceIntegralBound (leftSecondReal F) +
    sliceIntegralBound (leftSecondImag F)

def secondDecayBound (F : 𝓢(Joint, ℂ)) : ℝ :=
  firstDecayBound F + firstDecayBound (leftSecondReal F) +
    firstDecayBound (leftSecondImag F)

theorem inverse_leftSlice_weight_le (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    (1+‖x‖^2) * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
      ‖(𝓕⁻ (leftSlice F η)) x‖ +
      ‖(𝓕⁻ (leftSlice (leftSecondReal F) η)) x‖ +
      ‖(𝓕⁻ (leftSlice (leftSecondImag F) η)) x‖ := by
  have h := norm_sq_mul_norm_inverse_le (leftSlice F η) x
  simp only [leftSlice_lineDeriv] at h
  change ‖x‖^2 * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
    ‖(𝓕⁻ (leftSlice (leftSecondReal F) η)) x‖ +
    ‖(𝓕⁻ (leftSlice (leftSecondImag F) η)) x‖ at h
  nlinarith

theorem inverse_leftSlice_first_decay (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    (1+‖x‖^2) * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤ firstDecayBound F * planeMajorant η := by
  apply (inverse_leftSlice_weight_le F η x).trans
  have h0 := norm_inverse_leftSlice_le F η x
  have h1 := norm_inverse_leftSlice_le (leftSecondReal F) η x
  have h2 := norm_inverse_leftSlice_le (leftSecondImag F) η x
  dsimp [firstDecayBound, sliceIntegralBound]
  nlinarith

theorem inverse_leftSlice_second_decay (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    (1+‖x‖^2)^2 * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤ secondDecayBound F * planeMajorant η := by
  have h := mul_le_mul_of_nonneg_left (inverse_leftSlice_weight_le F η x)
    (show 0 ≤ 1+‖x‖^2 by positivity)
  have h0 := inverse_leftSlice_first_decay F η x
  have h1 := inverse_leftSlice_first_decay (leftSecondReal F) η x
  have h2 := inverse_leftSlice_first_decay (leftSecondImag F) η x
  dsimp [secondDecayBound]
  nlinarith

theorem norm_partialFourier_le (W : 𝓢(Joint, ℂ)) (η x : ℂ) :
    ‖partialFourier W η x‖ ≤
      secondDecayBound (𝓕 W) * (planeMajorant x * planeMajorant η) := by
  rw [← partialFourierSchwartz_apply]
  change ‖(𝓕⁻ (leftSlice (𝓕 W) η)) x‖ ≤ _
  have h := inverse_leftSlice_second_decay (𝓕 W) η x
  have hd : ‖(𝓕⁻ (leftSlice (𝓕 W) η)) x‖ ≤
      secondDecayBound (𝓕 W) * planeMajorant η / (1+‖x‖^2)^2 :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith [h])
  convert hd using 1
  simp only [planeMajorant, div_eq_mul_inv]
  ring

open EisensteinSchwartzPoisson hiding O

theorem planeMajorant_cartesian_summable :
    Summable (fun p : ℤ × ℤ => planeMajorant (complexPoint (p.1:ℝ) (p.2:ℝ))) := by
  apply Summable.of_nonneg_of_le (fun _ => by unfold planeMajorant; positivity) _
    summable_int_cauchy_product
  intro p
  change ((1+‖complexPoint (p.1:ℝ) (p.2:ℝ)‖^2)^2)⁻¹ ≤ _
  rw [← mul_inv]
  apply inv_anti₀ (by positivity)
  rw [Complex.sq_norm]
  simp only [complexPoint, Complex.normSq_apply]
  nlinarith [sq_nonneg (p.1:ℝ), sq_nonneg (p.2:ℝ),
    mul_nonneg (sq_nonneg (p.1:ℝ)) (sq_nonneg (p.2:ℝ))]

def cartesianPoint (p : ℤ × ℤ) : ℂ := complexPoint (p.1:ℝ) (p.2:ℝ)

theorem joint_cartesian_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖W (point (cartesianPoint p.1) (cartesianPoint p.2))‖) := by
  have hs := planeMajorant_cartesian_summable.mul_of_nonneg
    planeMajorant_cartesian_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_le_product_majorant W _ _) (hs.mul_left (productDecayConstant W))

theorem partialFourier_cartesian_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖partialFourier W (cartesianPoint p.2) (cartesianPoint p.1)‖) := by
  have hs := planeMajorant_cartesian_summable.mul_of_nonneg
    planeMajorant_cartesian_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_partialFourier_le W _ _) (hs.mul_left (secondDecayBound (𝓕 W)))

theorem rightSlice_isometry (x : ℂ) : Isometry (fun y : ℂ => point x y) := by
  apply Isometry.of_dist_eq
  intro y z
  simp only [dist_eq_norm, point_eq_add, add_sub_add_left_eq_sub, ← map_sub]
  exact WithLp.norm_toLp_snd 2 ℂ ℂ (y-z)

def rightSlice (W : 𝓢(Joint, ℂ)) (x : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (by simp only [point_eq_add]; fun_prop : (fun y : ℂ => point x y).HasTemperateGrowth)
    (rightSlice_isometry x).antilipschitzWith W

@[simp] theorem rightSlice_apply (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    rightSlice W x y = W (point x y) := rfl

theorem rightSlice_poisson (W : 𝓢(Joint, ℂ)) (x : ℂ) :
    (∑' p : ℤ × ℤ, W (point x (cartesianPoint p))) =
      ∑' p : ℤ × ℤ, partialFourier W (cartesianPoint p) x := by
  have h := integer_pair_poisson (rightSlice W x)
  have hcoe : (rightSlice W x : ℂ → ℂ) = fun y => W (point x y) := rfl
  simpa only [rightSlice_apply, SchwartzMap.fourier_coe, hcoe, partialFourier, cartesianPoint] using h

private theorem joint_cartesian_eq_partial (W : 𝓢(Joint, ℂ)) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (point (cartesianPoint p.1) (cartesianPoint p.2))) =
      ∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ,
        partialFourier W (cartesianPoint n) (cartesianPoint m) := by
  have hp := (joint_cartesian_summable_norm W).of_norm
  have hm := (partialFourier_cartesian_summable_norm W).of_norm
  calc
    _ = ∑' m : ℤ × ℤ, ∑' n : ℤ × ℤ,
        W (point (cartesianPoint m) (cartesianPoint n)) := hp.tsum_prod
    _ = ∑' m : ℤ × ℤ, ∑' n : ℤ × ℤ,
        partialFourier W (cartesianPoint n) (cartesianPoint m) := by
      apply tsum_congr
      intro m
      exact rightSlice_poisson W _
    _ = _ := hm.tsum_comm.symm

private theorem partial_cartesian_poisson (W : 𝓢(Joint, ℂ)) (n : ℤ × ℤ) :
    (∑' m : ℤ × ℤ, partialFourier W (cartesianPoint n) (cartesianPoint m)) =
      ∑' m : ℤ × ℤ, (𝓕 W) (point (cartesianPoint m) (cartesianPoint n)) := by
  calc
    _ = ∑' m : ℤ × ℤ, partialFourierSchwartz W (cartesianPoint n) (cartesianPoint m) :=
      tsum_congr fun m =>
        (partialFourierSchwartz_apply W (cartesianPoint n) (cartesianPoint m)).symm
    _ = ∑' m : ℤ × ℤ,
        (𝓕 (partialFourierSchwartz W (cartesianPoint n)) : 𝓢(ℂ, ℂ)) (cartesianPoint m) := by
      simpa only [cartesianPoint] using
        integer_pair_poisson (partialFourierSchwartz W (cartesianPoint n))
    _ = _ := tsum_congr fun m =>
      fourier_partialFourierSchwartz W (cartesianPoint m) (cartesianPoint n)

private theorem cartesian_swap_tsum (F : 𝓢(Joint, ℂ)) :
    (∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ, F (point (cartesianPoint m) (cartesianPoint n))) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), F (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  have hF := (joint_cartesian_summable_norm F).of_norm
  exact hF.tsum_comm.trans hF.tsum_prod.symm

private theorem partial_cartesian_eq_fourier (W : 𝓢(Joint, ℂ)) :
    (∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ,
      partialFourier W (cartesianPoint n) (cartesianPoint m)) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), (𝓕 W) (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  exact (tsum_congr (partial_cartesian_poisson W)).trans (cartesian_swap_tsum (𝓕 W))

theorem joint_cartesian_poisson (W : 𝓢(Joint, ℂ)) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (point (cartesianPoint p.1) (cartesianPoint p.2))) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), (𝓕 W) (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  exact (joint_cartesian_eq_partial W).trans (partial_cartesian_eq_fourier W)

def blockMap (A : ℂ ≃L[ℝ] ℂ) : Joint ≃L[ℝ] Joint :=
  ((A.toLinearEquiv.prodCongr A.toLinearEquiv).withLpCongr 2).toContinuousLinearEquiv

@[simp] theorem blockMap_apply (A : ℂ ≃L[ℝ] ℂ) (z : Joint) :
    blockMap A z = point (A z.fst) (A z.snd) := rfl

@[simp] theorem blockMap_symm_apply (A : ℂ ≃L[ℝ] ℂ) (z : Joint) :
    (blockMap A).symm z = point (A.symm z.fst) (A.symm z.snd) := rfl

theorem blockMap_det (A : ℂ ≃L[ℝ] ℂ) :
    LinearMap.det (blockMap A : Joint →ₗ[ℝ] Joint) =
      LinearMap.det (A : ℂ →ₗ[ℝ] ℂ) ^ 2 := by
  have h := LinearMap.det_conj
    ((A : ℂ →ₗ[ℝ] ℂ).prodMap (A : ℂ →ₗ[ℝ] ℂ))
    (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm
  rw [LinearMap.det_prodMap] at h
  convert h using 1 <;> first | rfl | ring

def jointInverseJacobian (A : Joint ≃L[ℝ] Joint) : ℝ :=
  |(LinearMap.det (A : Joint →ₗ[ℝ] Joint))⁻¹|

theorem jointInverseJacobian_blockMap (A : ℂ ≃L[ℝ] ℂ) :
    jointInverseJacobian (blockMap A) = inverseJacobian A ^ 2 := by
  rw [jointInverseJacobian, blockMap_det, ← inv_pow, abs_pow]
  rfl

def jointDual (A : Joint ≃L[ℝ] Joint) : Joint →L[ℝ] Joint :=
  A.symm.toContinuousLinearMap.adjoint

theorem joint_inner_linear_dual (A : Joint ≃L[ℝ] Joint) (x y : Joint) :
    inner ℝ (A x) (jointDual A y) = inner ℝ x y := by
  rw [jointDual, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem jointDual_blockMap (A : ℂ ≃L[ℝ] ℂ) (ξ η : ℂ) :
    jointDual (blockMap A) (point ξ η) = point (dualMap A ξ) (dualMap A η) := by
  apply ext_inner_left ℝ
  intro z
  rw [jointDual, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (point (A.symm z.fst) (A.symm z.snd)) (point ξ η) = _
  simp only [point, WithLp.prod_inner_apply, dualMap,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem joint_integral_comp_linearEquiv (A : Joint ≃L[ℝ] Joint) (f : Joint → ℂ) :
    (∫ x : Joint, f (A x)) = jointInverseJacobian A • ∫ x : Joint, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure Joint))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure Joint) =
      ENNReal.ofReal (jointInverseJacobian A) • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : Joint, f y ∂Measure.map A volume) = (∫ x : Joint, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal
    (show 0 ≤ jointInverseJacobian A from abs_nonneg _)] at h
  exact h.symm

theorem joint_fourier_comp_linearEquiv (A : Joint ≃L[ℝ] Joint)
    (f : Joint → ℂ) (w : Joint) :
    𝓕 (f ∘ A) w = jointInverseJacobian A • 𝓕 f (jointDual A w) := by
  let H : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z (jointDual A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : Joint, H (A x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [H, joint_inner_linear_dual, Function.comp_apply]
        rfl
    _ = jointInverseJacobian A • ∫ z : Joint, H z := joint_integral_comp_linearEquiv A H
    _ = _ := rfl

def jointTranslate (W : 𝓢(Joint, ℂ)) (b : Joint) : 𝓢(Joint, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun z : Joint => z+b)
    (by fun_prop) (isometry_add_right b).antilipschitzWith W

def jointAffine (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b : Joint) : 𝓢(Joint, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A (jointTranslate W b)

@[simp] theorem jointAffine_apply (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b z : Joint) :
    jointAffine W A b z = W (A z+b) := rfl

theorem joint_fourier_affine (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b w : Joint) :
    (𝓕 (jointAffine W A b)) w =
      jointInverseJacobian A •
        (Real.fourierChar (inner ℝ b (jointDual A w)) • (𝓕 W) (jointDual A w)) := by
  rw [congrFun (SchwartzMap.fourier_coe _) w]
  change 𝓕 ((fun z => W (z+b)) ∘ A) w = _
  rw [joint_fourier_comp_linearEquiv]
  have ht : 𝓕 (fun z => W (z+b)) (jointDual A w) =
      Real.fourierChar (inner ℝ b (jointDual A w)) • 𝓕 (W : Joint → ℂ) (jointDual A w) :=
    congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure Joint) (innerₗ Joint) (W : Joint → ℂ) b) (jointDual A w)
  rw [ht]
  rw [congrFun (SchwartzMap.fourier_coe W) (jointDual A w)]

theorem joint_affine_poisson (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b : Joint) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ),
      W (A (point (cartesianPoint p.1) (cartesianPoint p.2))+b)) =
      jointInverseJacobian A • ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
        Real.fourierChar (inner ℝ b
          (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))) •
        (𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2))) := by
  have h := joint_cartesian_poisson (jointAffine W A b)
  simp only [jointAffine_apply, joint_fourier_affine] at h
  rw [tsum_const_smul''] at h
  exact h

def jointFrequency (c : ℂ) (hc : c ≠ 0) (p : (ℤ × ℤ) × (ℤ × ℤ)) : Joint :=
  point (eisensteinDualFrequency c hc p.1) (eisensteinDualFrequency c hc p.2)

open ActualEisensteinCubic ConcreteTraceCRT

theorem actual_joint_coset_poisson (W : 𝓢(Joint, ℂ)) (b : O × O) (c : O) (hc : c ≠ 0) :
    (∑' m : O × O, W (embeddingPair (b.1+c*m.1,b.2+c*m.2))) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
        ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
          Real.fourierChar (inner ℝ (embeddingPair b)
            (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
            (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have h := joint_affine_poisson W (blockMap A) (embeddingPair b)
  simp only [jointInverseJacobian_blockMap, jointDual_blockMap] at h
  rw [eisenstein_inverseJacobian] at h
  calc
    _ = ∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (embeddingPair
        (b.1+c*latticeCoordEquiv.symm p.1,b.2+c*latticeCoordEquiv.symm p.2)) :=
      ((latticeCoordEquiv.symm.prodCongr latticeCoordEquiv.symm).tsum_eq _).symm
    _ = ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
        W (blockMap A (point (cartesianPoint p.1) (cartesianPoint p.2))+embeddingPair b) := by
      apply tsum_congr
      intro p
      congr 1
      change point (eisEmbedding (b.1+c*ActualEisensteinCoordinates.eval p.1.1 p.1.2))
        (eisEmbedding (b.2+c*ActualEisensteinCoordinates.eval p.2.1 p.2.2)) = _
      simp only [map_add, map_mul, blockMap_apply, point]
      rw [← eisensteinLatticeMap_point (eisEmbedding c) (eisEmbedding_ne_zero hc) p.1,
        ← eisensteinLatticeMap_point (eisEmbedding c) (eisEmbedding_ne_zero hc) p.2]
      change point (eisEmbedding b.1 + A (cartesianPoint p.1))
        (eisEmbedding b.2 + A (cartesianPoint p.2)) =
          point (A (cartesianPoint p.1)+eisEmbedding b.1)
            (A (cartesianPoint p.2)+eisEmbedding b.2)
      simp only [add_comm]
    _ = _ := h

theorem joint_dual_summable_norm (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖(𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))‖) := by
  have hJ : 0 < jointInverseJacobian A :=
    abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)
  have hs := joint_cartesian_summable_norm (𝓕 (jointAffine W A 0))
  have hn (p : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖(𝓕 (jointAffine W A 0)) (point (cartesianPoint p.1) (cartesianPoint p.2))‖ =
      jointInverseJacobian A *
        ‖(𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))‖ := by
    rw [joint_fourier_affine]
    simp [abs_of_pos hJ]
  simp_rw [hn] at hs
  have hi := hs.mul_left (jointInverseJacobian A)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hJ.ne', one_mul] using hi

theorem jointFrequency_summable_norm (W : 𝓢(Joint, ℂ)) (c : ℂ) (hc : c ≠ 0) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) => ‖(𝓕 W) (jointFrequency c hc p)‖) := by
  have h := joint_dual_summable_norm W (blockMap (eisensteinLatticeMap c hc))
  simpa only [jointDual_blockMap, jointFrequency, eisensteinDualFrequency, cartesianPoint] using h

abbrev Residue (c : O) := O ⧸ Ideal.span {c}

def quotientPair (c : O) (m : O × O) : Residue c × Residue c :=
  (Ideal.Quotient.mk (Ideal.span {c}) m.1, Ideal.Quotient.mk (Ideal.span {c}) m.2)

def representativePair (c : O) (r : Residue c × Residue c) : O × O :=
  (GaussianShiftedPartition.representative c r.1, GaussianShiftedPartition.representative c r.2)

def jointFiberSplit (c : O) (r : Residue c × Residue c) :
    (quotientPair c ⁻¹' {r}) ≃
      ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r.1}) ×
      ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r.2}) where
  toFun z := (⟨z.1.1, congrArg Prod.fst z.2⟩, ⟨z.1.2, congrArg Prod.snd z.2⟩)
  invFun z := ⟨(z.1.1,z.2.1), Prod.ext z.1.2 z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem joint_fiber_tsum (c : O) (hc : c ≠ 0) (r : Residue c × Residue c)
    (W : O × O → ℂ) :
    (∑' m : quotientPair c ⁻¹' {r}, W m.1) =
      ∑' m : O × O, W ((representativePair c r).1+c*m.1,
        (representativePair c r).2+c*m.2) := by
  let e1 := GaussianFiberEquiv.fiberEquiv c hc r.1
    (GaussianShiftedPartition.representative c r.1)
    (GaussianShiftedPartition.representative_spec c r.1)
  let e2 := GaussianFiberEquiv.fiberEquiv c hc r.2
    (GaussianShiftedPartition.representative c r.2)
    (GaussianShiftedPartition.representative_spec c r.2)
  let e := (e1.prodCongr e2).trans (jointFiberSplit c r).symm
  exact (e.tsum_eq (fun m => W m.1)).symm

def residueFourier (c : O) (hc : c ≠ 0) (a : Residue c × Residue c → ℂ)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) : ℂ :=
  ∑' r : Residue c × Residue c, a r *
    (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
      (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)

theorem actual_joint_periodic_poisson (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    letI : Finite (Residue c) := finite_quotient_span hc
    letI : Fintype (Residue c) := Fintype.ofFinite _
    (∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)) =
      ∑ r : Residue c × Residue c, a r *
        ((2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
          ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
            Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
              (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
              (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) := by
  classical
  let : Finite (Residue c) := finite_quotient_span hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  have ha (r : Residue c × Residue c) : ‖a r‖ ≤ ∑ t : Residue c × Residue c, ‖a t‖ :=
    Finset.single_le_sum (fun t _ => norm_nonneg (a t)) (Finset.mem_univ r)
  have hs := joint_weighted_summable (Ideal.Quotient.mk (Ideal.span {c})) a _ ha W
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition (quotientPair c) a
    (fun m => W (embeddingPair m)) hs]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact (joint_fiber_tsum c hc r (fun m => W (embeddingPair m))).trans
    (actual_joint_coset_poisson W (representativePair c r) c hc)

theorem actual_joint_periodic_fourier (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    (∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
        ∑' p : (ℤ × ℤ) × (ℤ × ℤ), residueFourier c hc a p *
          (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  classical
  let : Finite (Residue c) := finite_quotient_span hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  rw [actual_joint_periodic_poisson W c hc a]
  have hs (r : Residue c × Residue c) : Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      a r * (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
        (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
        (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [Circle.norm_smul] using
      jointFrequency_summable_norm W (eisEmbedding c) (eisEmbedding_ne_zero hc)
  simp_rw [mul_smul_comm, ← tsum_mul_left]
  rw [← Finset.smul_sum, ← Summable.tsum_finsetSum (fun r _ => hs r)]
  congr 1
  apply tsum_congr
  intro p
  simp only [residueFourier, tsum_fintype, Circle.smul_def, smul_eq_mul,
    Finset.sum_mul, mul_assoc]

@[simp] theorem jointFrequency_zero (c : ℂ) (hc : c ≠ 0) :
    jointFrequency c hc 0 = 0 := by
  have h : complexPoint (0:ℝ) 0 = 0 := by apply Complex.ext <;> rfl
  simp [jointFrequency, eisensteinDualFrequency, h, point]

@[simp] theorem residueFourier_zero (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    residueFourier c hc a 0 = ∑' r, a r := by
  simp [residueFourier]

theorem residueFourier_norm_le (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    ‖residueFourier c hc a p‖ ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)^2 * B := by
  classical
  let : Finite (Residue c) := finite_quotient_span hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  rw [residueFourier, tsum_fintype]
  calc
    _ ≤ ∑ r : Residue c × Residue c, ‖a r *
        (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
          (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r : Residue c × Residue c, B := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [norm_mul, Circle.norm_coe, mul_one] using hB r
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
        Nat.cast_mul, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_eq_fintype_card, Residue, pow_two]

theorem principal_joint_inverse_covolume (c : O) (hc : c ≠ 0) :
    (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 *
      (Ideal.absNorm (Ideal.span {c}) : ℝ)^2 = 4/3 := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)
  rw [← eisEmbedding_norm_sq_eq_absNorm_span]
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  nlinarith

theorem norm_periodic_zero_mean_le (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B)
    (hmean : (∑' r, a r) = 0) :
    ‖∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)‖ ≤
      (4/3:ℝ) * B *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ := by
  let F (p : (ℤ × ℤ) × (ℤ × ℤ)) := residueFourier c hc a p *
    (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)
  let q : ℝ := Ideal.absNorm (Ideal.span {c})
  have hF0 : F 0 = 0 := by simp [F, hmean]
  have hnorm (p : (ℤ × ℤ) × (ℤ × ℤ)) : ‖F p‖ ≤ q^2 * B *
      ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (residueFourier_norm_le c hc a B hB p) (norm_nonneg _)
  have hsF : Summable (fun p => ‖F p‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
      ((jointFrequency_summable_norm W (eisEmbedding c) (eisEmbedding_ne_zero hc)).mul_left _)
  have heq : (∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, F p.val) = ∑' p, F p := by
    apply tsum_subtype_eq_of_support_subset
    intro p hp
    change F p ≠ 0 at hp
    exact fun h => hp (h ▸ hF0)
  have hb : ‖∑' p, F p‖ ≤ q^2 * B *
      ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ := by
    rw [← heq]
    have hs1 : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} => ‖F p.val‖) :=
      hsF.subtype (fun p => p ≠ 0)
    have hm : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} =>
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖) :=
      (jointFrequency_summable_norm W (eisEmbedding c)
        (eisEmbedding_ne_zero hc)).subtype (fun p => p ≠ 0)
    have ht : (∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, ‖F p.val‖) ≤
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, q^2 * B *
          ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ :=
      Summable.tsum_le_tsum (fun p => hnorm p.val) hs1 (hm.mul_left (q^2*B))
    exact (norm_tsum_le_tsum_norm hs1).trans (by simpa only [tsum_mul_left] using ht)
  rw [actual_joint_periodic_fourier W c hc a, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (2/(Real.sqrt 3*‖eisEmbedding c‖^2))^2 * (q^2 * B *
      ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, principal_joint_inverse_covolume c hc]

def scaleMap (t : ℝ) (ht : 0 < t) : Joint ≃L[ℝ] Joint :=
  blockMap (complexMulEquiv ((t⁻¹:ℝ):ℂ)
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero ht.ne')))

@[simp] theorem scaleMap_apply (t : ℝ) (ht : 0 < t) (z : Joint) :
    scaleMap t ht z = t⁻¹ • z := by
  apply WithLp.ofLp_injective
  apply Prod.ext <;> simp [scaleMap, blockMap_apply, complexMulEquiv_apply, point, Algebra.smul_def]

theorem scaleMap_dual (t : ℝ) (ht : 0 < t) (z : Joint) :
    jointDual (scaleMap t ht) z = t • z := by
  have hz : z = point z.fst z.snd := rfl
  conv_lhs => rw [hz]
  rw [scaleMap, jointDual_blockMap, dual_mul_apply, dual_mul_apply]
  apply WithLp.ofLp_injective
  apply Prod.ext <;> simp [point, Algebra.smul_def]

theorem scaleMap_inverseJacobian (t : ℝ) (ht : 0 < t) :
    jointInverseJacobian (scaleMap t ht) = t^4 := by
  rw [scaleMap, jointInverseJacobian_blockMap, inverseJacobian, complexMulEquiv_det,
    abs_inv, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos ht, ← inv_pow, inv_inv]
  ring

def scaledSource (W : 𝓢(Joint, ℂ)) (t : ℝ) (ht : 0 < t) : 𝓢(Joint, ℂ) :=
  jointAffine W (scaleMap t ht) 0

@[simp] theorem scaledSource_apply (W : 𝓢(Joint, ℂ)) (t : ℝ) (ht : 0 < t) (z : Joint) :
    scaledSource W t ht z = W (t⁻¹ • z) := by
  simp [scaledSource]

theorem fourier_scaledSource (W : 𝓢(Joint, ℂ)) (t : ℝ) (ht : 0 < t) (z : Joint) :
    (𝓕 (scaledSource W t ht)) z = t^4 • (𝓕 W) (t • z) := by
  rw [scaledSource, joint_fourier_affine, scaleMap_inverseJacobian, scaleMap_dual]
  simp

theorem scaledSource_physicalPoint (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N) (m : O × O) :
    scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN) (embeddingPair m) =
      W (ProbeGramLatticeDecay.physicalPoint N m) := by
  rw [scaledSource_apply, ProbeGramLatticeDecay.physicalPoint_eq_smul]
  rfl

def generatorRotation (c : ℂ) : ℂ := (‖c‖:ℂ) / starRingEnd ℂ c

theorem norm_generatorRotation (c : ℂ) (hc : c ≠ 0) : ‖generatorRotation c‖ = 1 := by
  simp [generatorRotation, Complex.norm_real, norm_ne_zero_iff.mpr hc]

theorem scaled_jointFrequency_eq (c : ℂ) (hc : c ≠ 0) (N : ℝ) (hN : 0 < N)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    Real.sqrt N • jointFrequency c hc p =
      ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/‖c‖^2)) (generatorRotation c) p := by
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hs : Real.sqrt (N/‖c‖^2) = Real.sqrt N / ‖c‖ := by
    rw [Real.sqrt_div hN.le, Real.sqrt_sq (norm_nonneg c)]
  have hcoord (v : ℤ × ℤ) : (Real.sqrt N:ℂ) * eisensteinDualFrequency c hc v =
      generatorRotation c * (Real.sqrt (N/‖c‖^2):ℂ) * explicitDualFrequency 1 v := by
    rw [eisensteinDualFrequency_explicit, hs]
    simp only [generatorRotation, explicitDualFrequency, map_one, div_one, Complex.ofReal_div]
    have hnC : (‖c‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    field_simp
  apply WithLp.ofLp_injective
  change (Real.sqrt N • eisensteinDualFrequency c hc p.1,
    Real.sqrt N • eisensteinDualFrequency c hc p.2) = _
  apply Prod.ext
  · simpa [Algebra.smul_def, ProbeGramLatticeDecay.scaledDualPoint, ProbeGramLatticeDecay.point] using hcoord p.1
  · simpa [Algebra.smul_def, ProbeGramLatticeDecay.scaledDualPoint, ProbeGramLatticeDecay.point] using hcoord p.2

theorem sqrt_ratio_decay (N q : ℝ) (hN : 0 < N) (hq : 0 < q) (A : ℕ) :
    (Real.sqrt (N/q))^(-((2*A:ℕ):ℝ)) = (q/N)^A := by
  rw [Real.rpow_neg (Real.sqrt_nonneg _), Real.rpow_natCast, pow_mul,
    Real.sq_sqrt (div_nonneg hN.le hq.le), ← inv_pow, inv_div]

theorem physical_weighted_summable (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N)
    (d : O × O → ℂ) (B : ℝ) (hB : ∀ m, ‖d m‖ ≤ B) :
    Summable (fun m : O × O => d m * W (ProbeGramLatticeDecay.physicalPoint N m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((ProbeGramLatticeDecay.physical_summable W N hN).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB m) (norm_nonneg _)

theorem principal_high_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (c : O) (_hc : c ≠ 0)
        (a : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖a r‖ ≤ B) → (∑' r, a r) = 0 →
        ∀ (N : ℝ), 0 < N → (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N →
        ‖∑' m : O × O, a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A := by
  obtain ⟨S,C,hC,hhigh⟩ := ProbeGramLatticeDecay.dual_fourier_lattice_bound A hA
  refine ⟨S,(4/3)*C,mul_pos (by norm_num) hC,?_⟩
  intro W c hc a B hB0 hB hmean N hN hscale
  let q : ℝ := Ideal.absNorm (Ideal.span {c})
  have hq : 0 < q := by
    dsimp only [q]
    rw [← eisEmbedding_norm_sq_eq_absNorm_span]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
  have hL : 1 ≤ Real.sqrt (N/q) := by
    apply Real.le_sqrt_of_sq_le
    norm_num only [one_pow]
    exact (le_div_iff₀ hq).mpr (by simpa only [one_mul] using hscale)
  let u : ℂ := generatorRotation (eisEmbedding c)
  have hu : ‖u‖ = 1 := norm_generatorRotation _ (eisEmbedding_ne_zero hc)
  have ht4 : (Real.sqrt N)^4 = N^2 := by
    rw [show (4:ℕ) = 2*2 by norm_num, pow_mul, Real.sq_sqrt hN.le]
  have hf (p : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖(𝓕 (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)))
        (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)‖ =
      N^2 * ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p)‖ := by
    rw [fourier_scaledSource, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _), ht4,
      scaled_jointFrequency_eq _ _ N hN]
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
  have h := norm_periodic_zero_mean_le
    (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)) c hc a B hB hmean
  simp_rw [scaledSource_physicalPoint W N hN, hf, tsum_mul_left] at h
  have hD := hhigh W (Real.sqrt (N/q)) hL u hu
  rw [sqrt_ratio_decay N q hN hq A] at hD
  calc
    _ ≤ (4/3:ℝ)*B*(N^2 *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p.val)‖) := h
    _ ≤ (4/3:ℝ)*B*(N^2 *
        (C * ProbeGramLatticeDecay.sourceControl S W * (q/N)^A)) := by
      gcongr
    _ = _ := by ring

theorem norm_physical_weighted_le (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N)
    (d : O × O → ℂ) (B : ℝ) (hB : ∀ m, ‖d m‖ ≤ B) :
    ‖∑' m : O × O, d m * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
      B * ∑' m : O × O, ‖W (ProbeGramLatticeDecay.physicalPoint N m)‖ := by
  have hbound (m : O × O) : ‖d m * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
      B * ‖W (ProbeGramLatticeDecay.physicalPoint N m)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB m) (norm_nonneg _)
  have hs := ProbeGramLatticeDecay.physical_summable W N hN
  have hsD := Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbound (hs.mul_left B)
  apply (norm_tsum_le_tsum_norm hsD).trans
  have h := Summable.tsum_le_tsum hbound hsD (hs.mul_left B)
  simpa only [tsum_mul_left] using h

theorem principal_periodic_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (c : O), c ≠ 0 →
        ∀ (a : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖a r‖ ≤ B) → (∑' r, a r) = 0 → ∀ (N : ℝ), 1 ≤ N →
        Summable (fun m : O × O =>
          a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A) := by
  obtain ⟨Sl,Cl,hCl,hl⟩ := ProbeGramLatticeDecay.physical_lattice_bound
  obtain ⟨Sh,Ch,hCh,hh⟩ := principal_high_bound A hA
  refine ⟨Sl∪Sh,Cl+Ch,add_pos hCl hCh,?_⟩
  intro W c hc a B hB0 hB hm N hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  refine ⟨physical_weighted_summable W N hNp _ B (fun m => hB _),?_⟩
  have hSl : Cl*ProbeGramLatticeDecay.sourceControl Sl W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_right hCh.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_left W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hSh : Ch*ProbeGramLatticeDecay.sourceControl Sh W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_left hCl.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_right W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hratio : 0 ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)/N := div_nonneg (by positivity) hNp.le
  by_cases hscale : (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N
  · have hp : ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A ≤ 1 :=
      pow_le_one₀ hratio ((div_le_one hNp).mpr hscale)
    rw [min_eq_right hp]
    exact (hh W c hc a B hB0 hB hm N hNp hscale).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSh hB0) (sq_nonneg _))
        (pow_nonneg hratio _))
  · have hp : 1 ≤ ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A :=
      one_le_pow₀ ((le_div_iff₀ hNp).mpr (by linarith))
    rw [min_eq_left hp, mul_one]
    calc
      _ ≤ B * ∑' m : O × O, ‖W (ProbeGramLatticeDecay.physicalPoint N m)‖ :=
        norm_physical_weighted_le W N hNp _ B (fun m => hB _)
      _ ≤ B * (Cl*ProbeGramLatticeDecay.sourceControl Sl W*N^2) :=
        mul_le_mul_of_nonneg_left (hl W N hN) hB0
      _ = Cl*ProbeGramLatticeDecay.sourceControl Sl W*B*N^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSl hB0) (sq_nonneg _)

def idealQuotientPair (r : Ideal O) (m : O × O) : (O ⧸ r) × (O ⧸ r) :=
  (Ideal.Quotient.mk r m.1, Ideal.Quotient.mk r m.2)

theorem ideal_periodic_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (r : Ideal O), r ≠ 0 →
        ∀ (a : (O ⧸ r) × (O ⧸ r) → ℂ) (B : ℝ), 0 ≤ B →
        (∀ v, ‖a v‖ ≤ B) → (∑' v, a v) = 0 → ∀ (N : ℝ), 1 ≤ N →
        Summable (fun m : O × O =>
          a (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, a (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm r : ℝ)/N)^A) := by
  obtain ⟨S,C,hC,h⟩ := principal_periodic_bound A hA
  refine ⟨S,C,hC,?_⟩
  intro W r hr
  obtain ⟨c,hc,heq⟩ : ∃ c : O, c ≠ 0 ∧ Ideal.span {c} = r :=
    ⟨ConcretePrimeRowBridge.idealGenerator r,
      ConcretePrimeRowBridge.idealGenerator_ne_zero r hr,
      ConcretePrimeRowBridge.span_idealGenerator r⟩
  subst r
  exact h W c hc

theorem principal_annular_periodic_bound (A : ℕ) (hA : 2 < A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a b W →
      ∀ (c : O), c ≠ 0 → ∀ (d : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖d r‖ ≤ B) → (∑' r, d r) = 0 → ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O =>
          d (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, d (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A) := by
  obtain ⟨Sl,Cl,hCl,hl⟩ := ProbeGramAnnularLattice.annular_weighted_lattice_bound a b ha hab
  obtain ⟨Sh,Ch,hCh,hh⟩ := principal_high_bound A hA
  refine ⟨Sl∪Sh,Cl+Ch,add_pos hCl hCh,?_⟩
  intro W hW c hc d B hB0 hB hm N hN
  refine ⟨physical_weighted_summable W N hN _ B (fun m => hB _),?_⟩
  have hSl : Cl*ProbeGramLatticeDecay.sourceControl Sl W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_right hCh.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_left W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hSh : Ch*ProbeGramLatticeDecay.sourceControl Sh W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_left hCl.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_right W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hratio : 0 ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)/N := div_nonneg (by positivity) hN.le
  by_cases hscale : (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N
  · have hp : ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A ≤ 1 :=
      pow_le_one₀ hratio ((div_le_one hN).mpr hscale)
    rw [min_eq_right hp]
    exact (hh W c hc d B hB0 hB hm N hN hscale).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSh hB0) (sq_nonneg _))
        (pow_nonneg hratio _))
  · have hp : 1 ≤ ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A :=
      one_le_pow₀ ((le_div_iff₀ hN).mpr (by linarith))
    rw [min_eq_left hp, mul_one]
    exact (hl W hW (fun m => d (quotientPair c m)) B hB0
      (fun m => hB _) N hN).2.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSl hB0) (sq_nonneg _))

theorem ideal_annular_periodic_bound (A : ℕ) (hA : 2 < A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a b W →
      ∀ (r : Ideal O), r ≠ 0 → ∀ (d : (O ⧸ r) × (O ⧸ r) → ℂ) (B : ℝ), 0 ≤ B →
        (∀ v, ‖d v‖ ≤ B) → (∑' v, d v) = 0 → ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O =>
          d (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, d (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm r : ℝ)/N)^A) := by
  obtain ⟨S,C,hC,h⟩ := principal_annular_periodic_bound A hA a b ha hab
  refine ⟨S,C,hC,?_⟩
  intro W hW r hr
  obtain ⟨c,hc,heq⟩ : ∃ c : O, c ≠ 0 ∧ Ideal.span {c} = r :=
    ⟨ConcretePrimeRowBridge.idealGenerator r,
      ConcretePrimeRowBridge.idealGenerator_ne_zero r hr,
      ConcretePrimeRowBridge.span_idealGenerator r⟩
  subst r
  exact h W hW c hc

end ProbeGramPeriodicPoisson

end

end OAI

end Source1735

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramNonexceptionalBlock.lean; sha256: b0613a810151f4ce3362430bd59879cf9cd631643a252542476fec8679de7966 -/
section Source1736
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "Joint" => ProbeGramPeriodicPoisson.Joint

theorem literal_nonexceptional_block (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃H : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀{ι : Type*}[Fintype ι],∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C k : O)(_hC : C≠0)(_hk0 : k≠0)(u : Oˣ)(a b : ℕ)(r : O)
      (hr : Supported (Ideal.span {r})),k=u.val*goodLambda^a*(2:O)^b*r→
      ∀(P : ι→Id)[_hmax : ∀i,(P i).IsMaximal](hg : ∀i,goodLambda∉P i)(c : ι→ℕ),
      (∀i,1≤c i)→Ideal.span {C}=∏i,P i^c i→
      ∀(p : Id)[_hpmax : p.IsMaximal],p≠0→∀_hgp : goodLambda∉p,
      ringChar (O⧸p)≠2→(¬p∣jointFixedModulus S hS)→(¬p∣∏i,P i)→
      (¬6∣(normalizedFactors (Ideal.span {k})).count p)→
      ∀(W : SchwartzMap Joint ℂ),ProbeGramAnnularLattice.AnnularSupport a₀ b₀ W→
      ∀(d : O)(N : ℝ),0<N→
      Summable (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
      ‖∑'m : O×O,jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)‖≤
        K*ProbeGramLatticeDecay.sourceControl H W*(Ideal.absNorm (Ideal.span {C}):ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
            Ideal.absNorm (Ideal.span {k})/N)^A) := by
  obtain ⟨H,K,hK,hengine⟩ := ProbeGramPeriodicPoisson.ideal_annular_periodic_bound A hA a₀ b₀ ha₀ hab
  refine ⟨H,K,hK,?_⟩
  intro ι inst S hS σ C k hC hk0 u a b r hr hk P hmax hg c hc hfac p hpmax hp0 hgp hchar hfixed hcommon he W hW d N hN
  have hcount : (normalizedFactors (Ideal.span {k})).count p=
      (normalizedFactors (Ideal.span {r})).count p := by
    rw [hk]
    exact good_factor_count p hgp hchar u a b r hr
  have heR : ¬6∣(normalizedFactors (Ideal.span {r})).count p := hcount ▸ he
  obtain ⟨M,hM,hMN,hres⟩ := exists_nonexceptional_residue S hS σ C k hC hk0 u a b r hr hk
    P hg c hc hfac p hp0 hgp hchar hfixed hcommon heR
  let : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient hM
  let : Fintype (O⧸M) := Fintype.ofFinite _
  obtain ⟨f,hf,hfn,hfm⟩ := hres d
  have hmean : (∑'v : (O⧸M)×(O⧸M),f v.1 v.2)=0 := by
    rw [tsum_fintype,Fintype.sum_prod_type]
    exact hfm
  have hh := hengine W hW M hM (fun v=>f v.1 v.2) (Ideal.absNorm (Ideal.span {C}))
    (Nat.cast_nonneg _) (fun v=>hfn v.1 v.2) hmean N hN
  have hfun : (fun m : O×O=>f (ProbeGramPeriodicPoisson.idealQuotientPair M m).1
      (ProbeGramPeriodicPoisson.idealQuotientPair M m).2*W (ProbeGramLatticeDecay.physicalPoint N m))=
      (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)) := by
    funext m
    rw [ProbeGramPeriodicPoisson.idealQuotientPair,hf]
  rw [hfun] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by unfold ProbeGramLatticeDecay.sourceControl;positivity)
  apply min_le_min_left
  apply pow_le_pow_left₀ (by positivity)
  apply div_le_div_of_nonneg_right _ hN.le
  exact_mod_cast hMN

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1736

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramPhysicalScale.lean; sha256: fb99e339c680f2577938e7ced8103ffeaa6599947262630cb99c53cf052140ec -/
section Source1737
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

 def residualScale (C D : SupportedIdeal) (Y : ℝ) : ℝ :=
  Y/((Ideal.absNorm C.val:ℝ)*Ideal.absNorm D.val)

lemma residualScale_pos (C D : SupportedIdeal) (Y : ℝ) (hY : 0<Y) : 0<residualScale C D Y := by
  have hc : (0:ℝ)<Ideal.absNorm C.val := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr C.property.1)
  have hd : (0:ℝ)<Ideal.absNorm D.val := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr D.property.1)
  exact div_pos hY (mul_pos hc hd)

lemma residual_column_ratio (C D I : SupportedIdeal) (Y : ℝ) (hY : 0<Y) :
    (Ideal.absNorm (supportedIdealProduct C (supportedIdealProduct D I)).val:ℝ)/Y=
      (Ideal.absNorm I.val:ℝ)/residualScale C D Y := by
  simp only [supportedIdealProduct,map_mul,Nat.cast_mul,residualScale]
  field_simp

 def frequencyScale (C : SupportedIdeal) (k : O) (Y Q : ℝ) : ℝ :=
  (Ideal.absNorm C.val:ℝ)*‖eisEmbedding k‖^2/(Y^2/Q)

lemma frequencyScale_nonneg (C : SupportedIdeal) (k : O) (Y Q : ℝ) (hQ : 0≤Q) :
    0≤frequencyScale C k Y Q := by unfold frequencyScale;positivity

theorem original_kernel_residual_scale (C D I J : SupportedIdeal) (k : O)
    (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) :
    Q*‖eisEmbedding (primaryGenerator C.val*k)‖^2/
      ‖eisEmbedding (primaryGenerator (supportedIdealProduct C (supportedIdealProduct D I)).val*
        primaryGenerator (supportedIdealProduct C (supportedIdealProduct D J)).val)‖^2=
      frequencyScale C k Y Q/
        (((Ideal.absNorm I.val:ℝ)/residualScale C D Y)*((Ideal.absNorm J.val:ℝ)/residualScale C D Y)) := by
  rw [lowGram_kernel_scale Y Q hY hQ _ _ (primaryGenerator C.val*k),
    residual_column_ratio C D I Y hY,residual_column_ratio C D J Y hY]
  rw [map_mul,norm_mul,mul_pow,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    (primaryGenerator_spec C.val (supported_primaryGenerator_ne_zero C.val C.property)).1]
  unfold frequencyScale
  ring

lemma physicalPoint_first_norm (N : ℝ) (hN : 0<N) (m : O×O) :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).1‖^2=‖eisEmbedding m.1‖^2/N := by
  simp only [ProbeGramLatticeDecay.physicalPoint,ProbeGramLatticeDecay.point,WithLp.ofLp_toLp]
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.sqrt_pos.mpr hN),div_pow,Real.sq_sqrt hN.le]

lemma physicalPoint_second_norm (N : ℝ) (hN : 0<N) (m : O×O) :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).2‖^2=‖eisEmbedding m.2‖^2/N := by
  simp only [ProbeGramLatticeDecay.physicalPoint,ProbeGramLatticeDecay.point,WithLp.ofLp_toLp]
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.sqrt_pos.mpr hN),div_pow,Real.sq_sqrt hN.le]

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1737

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramCommonSource.lean; sha256: 0074d2abd52ad97dd071591523545937c1c9988768486f38ba8f3d957c1efef1 -/
section Source1738
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

def commonResidualScale (C : SupportedIdeal) (Y : ℝ) : ℝ := Y/Ideal.absNorm C.val
lemma commonResidualScale_pos (C : SupportedIdeal) (Y : ℝ) (hY : 0<Y) : 0<commonResidualScale C Y :=
  div_pos hY (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr C.property.1))
lemma common_column_ratio (C I : SupportedIdeal) (Y : ℝ) :
    (Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y=(Ideal.absNorm I.val:ℝ)/commonResidualScale C Y := by
  rw [supported_dilation_norm,Nat.cast_mul,commonResidualScale,div_div_eq_mul_div]
  ring
lemma common_kernel_scale (C I J : SupportedIdeal) (k : O) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) :
    Q*‖eisEmbedding (primaryGenerator C.val*k)‖^2/
      ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2=
      frequencyScale C k Y Q/
        (((Ideal.absNorm I.val:ℝ)/commonResidualScale C Y)*((Ideal.absNorm J.val:ℝ)/commonResidualScale C Y)) := by
  rw [lowGram_kernel_scale Y Q hY hQ,common_column_ratio,common_column_ratio,
    map_mul,norm_mul,mul_pow,primary_norm]
  unfold frequencyScale
  ring

theorem original_common_window_source (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C : SupportedIdeal) (k : O)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (hcop : Pairwise (Function.onFun IsCoprime P)) (he : C.val=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    let N:=commonResidualScale C Y
    let hN:=commonResidualScale_pos C Y hY
    let F:=lowGaussColumns W hW N hN
    (∑I∈F,∑J∈F,if IsCoprime I.val J.val then
      (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
      star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y))*
      actualCorrelation (primaryGenerator (supportedIdealProduct C I).val)
        (primaryGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C J).property)
        (primaryGenerator C.val*k)*
      paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator C.val*k)‖^2/
        ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2)
      else 0)=
      ∑D∈divisorPool F Subtype.val,(moebius D:ℂ)*∑'n : O,∑'m : O,
        jointExtension S hS σ (primaryGenerator C.val) k u a b r hr P hg c (primaryGenerator D*n) (primaryGenerator D*m)*
          shellProfile W v U (frequencyScale C k Y Q) (‖eisEmbedding n‖^2/(N/Ideal.absNorm D))
            (‖eisEmbedding m‖^2/(N/Ideal.absNorm D)) := by
  dsimp only
  have hpc : λ₀^2∣primaryGenerator C.val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ C.property)).2
  rw [←original_window_mobius_lattice S hS hbad σ (primaryGenerator C.val) k hpc
    u a b r hr P hg c W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)
    U v (frequencyScale C k Y Q)]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs with hIJ
  · have hni : Supported (Ideal.span {primaryGenerator I.val}) := (supported_span_primaryGenerator_iff _).mpr I.property
    have hnj : Supported (Ideal.span {primaryGenerator J.val}) := (supported_span_primaryGenerator_iff _).mpr J.property
    have hpi : λ₀^2∣primaryGenerator I.val-1 := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).2
    have hpj : λ₀^2∣primaryGenerator J.val-1 := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ J.property)).2
    have hij : IsCoprime (primaryGenerator I.val) (primaryGenerator J.val) := by
      apply (Ideal.isCoprime_span_singleton_iff _ _).mp
      simpa only [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1,
        (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ J.property)).1] using hIJ
    have hf : Ideal.span {primaryGenerator C.val}=∏i,P i^c i := by
      rw [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ C.property)).1,he]
    rw [jointExtension_source S hS σ (primaryGenerator C.val) k
      ((supported_span_primaryGenerator_iff _).mpr C.property) u a b r hr hpr hk P hg c hc hcop hf
      _ _ hni hnj hpi hpj hij]
    rw [lowGramCoefficient_eq_primary S hS hbad σ,lowGramCoefficient_eq_primary S hS hbad σ,
      common_kernel_scale C I J k Y Q hY hQ,common_column_ratio,common_column_ratio]
    simp only [supported_dilation_generator,shellProfile,star_mul]
    ring
  · rfl

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1738

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramJointConstruction.lean; sha256: e015a207789cb04eff2db13b45812e361290c69ad021408d86f63d5414ab6d74 -/
section Source1739
namespace OAI

noncomputable section
open Filter Set
open scoped Classical SchwartzMap ContDiff Topology

namespace ProbeGramJointConstruction
open ProbeGramLatticeDecay EisensteinSchwartzPoisson

def q1 (z : Joint) : ℝ := ‖z.fst‖^2
def q2 (z : Joint) : ℝ := ‖z.snd‖^2

lemma q1_smooth : ContDiff ℝ ∞ q1 :=
  (WithLp.fstL 2 ℝ ℂ ℂ).contDiff.norm_sq ℂ
lemma q2_smooth : ContDiff ℝ ∞ q2 :=
  (WithLp.sndL 2 ℝ ℂ ℂ).contDiff.norm_sq ℂ

lemma norm_sq_eq (z : Joint) : ‖z‖^2 = q1 z + q2 z :=
  WithLp.prod_norm_sq_eq_of_L2 z

def log1 (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  CompletedHeight.patchedLog a b ha (q1 z)
def log2 (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  CompletedHeight.patchedLog a b ha (q2 z)
def phase (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  log1 a b ha z - log2 a b ha z
def rootScale (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  Real.exp (-(log1 a b ha z + log2 a b ha z)/2)
def amplitude (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (z : Joint) : ℂ :=
  W (q1 z)*star (W (q2 z))*Complex.exp (-((log1 a b ha z+log2 a b ha z):ℂ))

lemma patchedLog_smooth (a b : ℝ) (ha : 0<a) :
    ContDiff ℝ ∞ (CompletedHeight.patchedLog a b ha) :=
  contDiff_id.add (CompletedHeight.logCorrection_smooth a b ha)
lemma log1_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (log1 a b ha) :=
  (patchedLog_smooth a b ha).comp q1_smooth
lemma log2_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (log2 a b ha) :=
  (patchedLog_smooth a b ha).comp q2_smooth
lemma phase_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (phase a b ha) :=
  (log1_smooth a b ha).sub (log2_smooth a b ha)
lemma rootScale_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (rootScale a b ha) :=
  (((log1_smooth a b ha).add (log2_smooth a b ha)).neg.div_const 2).exp
lemma rootScale_pos (a b : ℝ) (ha : 0<a) (z : Joint) : 0<rootScale a b ha z :=
  Real.exp_pos _
lemma amplitude_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (a b : ℝ) (ha : 0<a) :
    ContDiff ℝ ∞ (amplitude W a b ha) := by
  unfold amplitude
  have h1 := hW.comp q1_smooth
  have h2 := hW.comp q2_smooth
  have hl := (log1_smooth a b ha).add (log2_smooth a b ha)
  simpa only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_add, Complex.conjCLE_apply, Complex.star_def] using
    (h1.mul (Complex.conjCLE.contDiff.comp h2)).mul
      ((Complex.ofRealCLM.contDiff.comp hl).neg.cexp)

def rawProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint) : ℂ :=
  (W (q1 z)*(q1 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
    star (W (q2 z)*(q2 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
    paperRadialFourier U (T/(q1 z*q2 z))

def patchedProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (v T : ℝ) (z : Joint) : ℂ :=
  amplitude W a b ha z * FourierBridge.logPhase (v/(2*Real.pi)) (phase a b ha z) *
    paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z)

lemma patchedProfile_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (v T : ℝ) :
    ContDiff ℝ ∞ (patchedProfile W U a b ha v T) := by
  have h1 := amplitude_smooth W hW a b ha
  have h2 := phase_smooth a b ha
  have h3 := rootScale_smooth a b ha
  have h4 := (paperFourierRayCLM U).smooth (⊤ : ℕ∞)
  have hp : ContDiff ℝ ∞ (fun z => FourierBridge.logPhase (v/(2*Real.pi)) (phase a b ha z)) := by
    unfold FourierBridge.logPhase
    exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul h2)).mul contDiff_const).cexp
  exact (h1.mul hp).mul (h4.comp (contDiff_const.mul h3))

lemma rawProfile_zero_left (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint)
    (hz : W (q1 z)=0) : rawProfile W U v T z=0 := by simp [rawProfile,hz]
lemma rawProfile_zero_right (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint)
    (hz : W (q2 z)=0) : rawProfile W U v T z=0 := by simp [rawProfile,hz]
lemma patchedProfile_zero_left (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (v T : ℝ) (z : Joint) (hz : W (q1 z)=0) : patchedProfile W U a b ha v T z=0 := by
  simp [patchedProfile,amplitude,hz]
lemma patchedProfile_zero_right (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (v T : ℝ) (z : Joint) (hz : W (q2 z)=0) : patchedProfile W U a b ha v T z=0 := by
  simp [patchedProfile,amplitude,hz]

def sourceCompact (b : ℝ) : Set Joint := Metric.closedBall 0 (1+2*b)
lemma sourceCompact_isCompact (b : ℝ) : IsCompact (sourceCompact b) :=
  isCompact_closedBall _ _

lemma support_amplitude (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) :
    Function.support (amplitude W a b ha)⊆{z | a≤q1 z ∧ q1 z≤b ∧ a≤q2 z ∧ q2 z≤b} := by
  intro z hz
  have h1 : W (q1 z)≠0 := fun h => hz (by simp [amplitude,h])
  have h2 : W (q2 z)≠0 := fun h => hz (by simp [amplitude,h])
  exact ⟨(hs h1).1,(hs h1).2,(hs h2).1,(hs h2).2⟩

lemma annulus_subset_sourceCompact (a b : ℝ) (ha : 0<a) (hab : a<b) :
    {z : Joint | a≤q1 z ∧ q1 z≤b ∧ a≤q2 z ∧ q2 z≤b}⊆sourceCompact b := by
  intro z hz
  change dist z 0≤1+2*b
  rw [dist_zero_right]
  have hn := norm_sq_eq z
  have hb : 0<b := ha.trans hab
  nlinarith [norm_nonneg z, sq_nonneg (‖z‖-1),hz.2.1,hz.2.2.2]

lemma tsupport_amplitude_subset (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) :
    tsupport (amplitude W a b ha)⊆sourceCompact b := by
  exact closure_minimal ((support_amplitude W a b ha hs).trans
    (annulus_subset_sourceCompact a b ha hab)) Metric.isClosed_closedBall

lemma amplitude_hasCompactSupport (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) : HasCompactSupport (amplitude W a b ha) :=
  HasCompactSupport.of_support_subset_isCompact (sourceCompact_isCompact b)
    ((support_amplitude W a b ha hs).trans (annulus_subset_sourceCompact a b ha hab))

lemma patchedProfile_hasCompactSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    HasCompactSupport (patchedProfile W U a b ha v T) :=
  ((amplitude_hasCompactSupport W a b ha hab hs).mul_right).mul_right

lemma norm_power_pair (v x y : ℝ) (hx : 0<x) (hy : 0<y) :
    (x:ℂ)^(-1+(v:ℂ)*Complex.I)*star ((y:ℂ)^(-1+(v:ℂ)*Complex.I)) =
      Complex.exp (-((Real.log x+Real.log y):ℂ))*
        FourierBridge.logPhase (v/(2*Real.pi)) (Real.log x-Real.log y) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
  rw [←Complex.ofReal_log hx.le,←Complex.ofReal_log hy.le]
  simp only [Complex.star_def,←Complex.exp_conj,map_mul,map_add,map_neg,map_one,
    Complex.conj_ofReal,Complex.conj_I]
  unfold FourierBridge.logPhase
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

lemma sqrt_reciprocal_product (T x y : ℝ) (hT : 0≤T) (hx : 0<x) (hy : 0<y) :
    Real.sqrt (T/(x*y))=Real.sqrt T*Real.exp (-(Real.log x+Real.log y)/2) := by
  have he : Real.exp (-(Real.log x+Real.log y)/2)^2=(x*y)⁻¹ := by
    rw [←Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(-(Real.log x+Real.log y)/2)=-(Real.log x+Real.log y) by ring,
      Real.exp_neg,Real.exp_add,Real.exp_log hx,Real.exp_log hy]
  have hl := Real.sq_sqrt (div_nonneg hT (mul_pos hx hy).le)
  have hr : (Real.sqrt T*Real.exp (-(Real.log x+Real.log y)/2))^2=T/(x*y) := by
    rw [mul_pow,Real.sq_sqrt hT,he,div_eq_mul_inv]
  nlinarith [Real.sqrt_nonneg (T/(x*y)),Real.sqrt_nonneg T,
    Real.exp_pos (-(Real.log x+Real.log y)/2),mul_nonneg (Real.sqrt_nonneg T)
      (Real.exp_pos (-(Real.log x+Real.log y)/2)).le]

theorem rawProfile_eq_patchedProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Icc a b)
    (v T : ℝ) (hT : 0≤T) (z : Joint) :
    rawProfile W U v T z=patchedProfile W U a b ha v T z := by
  by_cases h1 : W (q1 z)=0
  · rw [rawProfile_zero_left W U v T z h1,patchedProfile_zero_left W U a b ha v T z h1]
  by_cases h2 : W (q2 z)=0
  · rw [rawProfile_zero_right W U v T z h2,patchedProfile_zero_right W U a b ha v T z h2]
  have hx := ha.trans_le (hs h1).1
  have hy := ha.trans_le (hs h2).1
  have hl1 : log1 a b ha z=Real.log (q1 z) := CompletedHeight.patchedLog_eq_log a b ha _ (hs h1)
  have hl2 : log2 a b ha z=Real.log (q2 z) := CompletedHeight.patchedLog_eq_log a b ha _ (hs h2)
  have hker : paperRadialFourier U (T/(q1 z*q2 z)) =
      paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) := by
    rw [paperRadialFourier_eq_ray]
    change paperFourierRayCLM U (Real.sqrt (T/(q1 z*q2 z))) = _
    rw [sqrt_reciprocal_product T _ _ hT hx hy]
    simp only [rootScale,hl1,hl2]
  unfold rawProfile patchedProfile amplitude phase
  rw [hker,hl1,hl2]
  simp only [star_mul]
  calc
    _ = (W (q1 z)*star (W (q2 z)))*
        ((q1 z:ℂ)^(-1+(v:ℂ)*Complex.I)*star ((q2 z:ℂ)^(-1+(v:ℂ)*Complex.I)))*
        paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) := by ring
    _ = _ := by rw [norm_power_pair v _ _ hx hy];ring

def amplitudeSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(Joint,ℂ) :=
  (amplitude_hasCompactSupport W a b ha hab hs).toSchwartzMap (amplitude_smooth W hW a b ha)

@[simp] lemma amplitudeSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (z : Joint) :
    amplitudeSchwartz W a b ha hab hs hW z=amplitude W a b ha z := rfl

lemma rawProfile_smooth (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) : ContDiff ℝ ∞ (rawProfile W U v T) := by
  have he : rawProfile W U v T=patchedProfile W U a b ha v T :=
    funext (rawProfile_eq_patchedProfile W U a b ha hs v T hT)
  rw [he]
  exact patchedProfile_smooth W hW U a b ha v T

lemma support_rawProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    Function.support (rawProfile W U v T)⊆{z | a≤q1 z ∧ q1 z≤b ∧ a≤q2 z ∧ q2 z≤b} := by
  intro z hz
  have h1 : W (q1 z)≠0 := fun h => hz (rawProfile_zero_left W U v T z h)
  have h2 : W (q2 z)≠0 := fun h => hz (rawProfile_zero_right W U v T z h)
  exact ⟨(hs h1).1,(hs h1).2,(hs h2).1,(hs h2).2⟩

lemma rawProfile_hasCompactSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    HasCompactSupport (rawProfile W U v T) :=
  HasCompactSupport.of_support_subset_isCompact (sourceCompact_isCompact b)
    ((support_rawProfile W U a b hs v T).trans (annulus_subset_sourceCompact a b ha hab))

def jointProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) : 𝓢(Joint,ℂ) :=
  (rawProfile_hasCompactSupport W U a b ha hab hs v T).toSchwartzMap
    (rawProfile_smooth W U a b ha hs hW v T hT)

@[simp] theorem jointProfile_apply (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) :
    jointProfile W U a b ha hab hs hW v T hT z=rawProfile W U v T z := rfl

theorem jointProfile_factorization (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) :
    jointProfile W U a b ha hab hs hW v T hT z=
      amplitude W a b ha z * FourierBridge.logPhase (v/(2*Real.pi)) (phase a b ha z) *
        paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) :=
  rawProfile_eq_patchedProfile W U a b ha hs v T hT z

theorem jointProfile_annularSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) :
    ProbeGramAnnularLattice.AnnularSupport a b (jointProfile W U a b ha hab hs hW v T hT) :=
  support_rawProfile W U a b hs v T

lemma jointProfile_zero_scale (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (v : ℝ) (z : Joint) :
    jointProfile W U a b ha hab hs hW v 0 (by positivity) z=
      (W (q1 z)*(q1 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
        star (W (q2 z)*(q2 z:ℂ)^(-1+(v:ℂ)*Complex.I))*paperRadialFourier U 0 := by
  simp only [jointProfile_apply,rawProfile,zero_div]

lemma jointProfile_zero_of_left_small (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) (hz : q1 z<a) :
    jointProfile W U a b ha hab hs hW v T hT z=0 := by
  apply rawProfile_zero_left
  by_contra h
  exact (not_le.mpr hz) (hs h).1

lemma jointProfile_zero_of_right_small (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) (hz : q2 z<a) :
    jointProfile W U a b ha hab hs hW v T hT z=0 := by
  apply rawProfile_zero_right
  by_contra h
  exact (not_le.mpr hz) (hs h).1

end ProbeGramJointConstruction

end

end OAI

end Source1739

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramJointProfile.lean; sha256: 7e93c802f68e5b8031c8dec1d507ef34f4c306d2459329a167fb173c18e1a62c -/
section Source1740
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set FourierBridge
namespace ProbeGramJointProfile
open ProbeGramLatticeDecay EisensteinSchwartzPoisson

def rayControl (B n : ℕ) (g : 𝓢(ℝ, ℂ)) : ℝ :=
  (Finset.Iic (2*B+n,n)).sup (schwartzSeminormFamily ℝ ℝ ℂ) g

lemma rayControl_nonneg (B n : ℕ) (g : 𝓢(ℝ, ℂ)) :
    0 ≤ rayControl B n g := apply_nonneg _ _

lemma mul_derivative_bound {f g : Joint → ℂ} (n : ℕ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Joint)
    {C D : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hfb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hgb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ 2^n*C*D := by
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x (by simp)
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (hfb i (Finset.mem_range_succ_iff.mp hi)) (by positivity))
        (hgb (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

lemma compact_derivatives {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set Joint} (hK : IsCompact K) {f : Joint → F}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ n, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
  have hb (i : ℕ) : ∃ D : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
    obtain ⟨D, hD⟩ := hK.bddAbove_image
      (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.continuousOn
    exact ⟨D, fun x hx => hD (Set.mem_image_of_mem _ hx)⟩
  choose D hD using hb
  refine ⟨1 + ∑ i ∈ Finset.range (n+1), |D i|, by
    have hn : 0 ≤ ∑ i ∈ Finset.range (n+1), |D i| := by positivity
    linarith, ?_⟩
  intro i hi x hx
  have hs : |D i| ≤ ∑ j ∈ Finset.range (n+1), |D j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (D j)) (Finset.mem_range.mpr (by omega))
  exact (hD i x hx).trans ((le_abs_self _).trans (by linarith))

lemma compact_positive_margin {K : Set Joint} (hK : IsCompact K)
    {h : Joint → ℝ} (hc : Continuous h) (hp : ∀ x ∈ K, 0 < h x) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ K, m ≤ h x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hm⟩ := hK.exists_isMinOn hne hc.continuousOn
    exact ⟨min 1 (h x), lt_min zero_lt_one (hp x hx), min_le_left _ _,
      fun y hy => (min_le_right _ _).trans (hm hy)⟩
  · exact ⟨1, zero_lt_one, le_rfl, fun x hx => False.elim (hne ⟨x,hx⟩)⟩

lemma scaled_argument_derivative {h : Joint → ℝ} (hh : ContDiff ℝ ∞ h)
    {D R : ℝ} (hD : 1 ≤ D) (hR : 0 ≤ R) (i : ℕ) (hi : 1 ≤ i)
    (x : Joint) (hb : ‖iteratedFDeriv ℝ i h x‖ ≤ D) :
    ‖iteratedFDeriv ℝ i (fun y => R*h y) x‖ ≤ (D^2*(1+R))^i := by
  have he : iteratedFDeriv ℝ i (fun y => R*h y) x = R • iteratedFDeriv ℝ i h x :=
    by simpa only [smul_eq_mul] using
      (iteratedFDeriv_const_smul_apply' (a := R) (i := i) (x := x)
        ((hh.of_le (by exact_mod_cast le_top)).contDiffAt))
  rw [he, norm_smul, Real.norm_of_nonneg hR]
  have hDi : D ≤ D^i := by
    calc D = D^1 := by simp
         _ ≤ D^i := pow_le_pow_right₀ hD hi
  have hRi : R ≤ (1+R)^i := by
    calc R ≤ 1+R := by linarith
         _ = (1+R)^1 := by simp
         _ ≤ (1+R)^i := pow_le_pow_right₀ (by linarith) hi
  calc
    R * ‖iteratedFDeriv ℝ i h x‖ ≤ R*D := mul_le_mul_of_nonneg_left hb hR
    _ ≤ (1+R)^i * D^i := mul_le_mul hRi hDi (by linarith) (by positivity)
    _ ≤ (D^2*(1+R))^i := by
      rw [mul_pow, pow_two, mul_pow]
      have hhD : 1 ≤ D^i := one_le_pow₀ hD
      nlinarith [mul_nonneg (show 0 ≤ (1+R)^i by positivity)
        (show 0 ≤ (D^i)^2-D^i by nlinarith)]

lemma normalized_phase_derivative (v x : ℝ) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (logPhase (v/(2*Real.pi))) x‖ = |v|^i := by
  rw [JointLogSeparation.logPhase_iteratedFDeriv_norm, norm_div,
    Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi), Real.norm_eq_abs]
  congr 1
  field_simp

lemma phase_derivative_bound {φ : Joint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {D : ℝ} (hD : 1 ≤ D) (n j : ℕ) (hj : j ≤ n)
    (x : Joint) (hb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i φ x‖ ≤ D) (v : ℝ) :
    ‖iteratedFDeriv ℝ j (fun y => logPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
      (n.factorial : ℝ)*D^n*(1+|v|)^n := by
  have hcomp := norm_iteratedFDeriv_comp_le (JointLogSeparation.logPhase_temperate (v/(2*Real.pi))).1
    hφ (n := j) (by simp) x (C := (1+|v|)^n) (D := D)
  have hc : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (logPhase (v/(2*Real.pi))) (φ x)‖ ≤
      (1+|v|)^n := by
    intro i hi
    rw [normalized_phase_derivative]
    exact (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |v| ≤ 1+|v|) i).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg v]) (hi.trans hj))
  have hd : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i φ x‖ ≤ D^i := by
    intro i hi hij
    exact (hb i (hij.trans hj)).trans (by
      calc D = D^1 := by simp
           _ ≤ D^i := pow_le_pow_right₀ hD hi)
  calc
    _ ≤ (j.factorial : ℝ)*(1+|v|)^n*D^j := hcomp hc hd
    _ ≤ (n.factorial : ℝ)*(1+|v|)^n*D^n := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) (by positivity))
        (pow_le_pow_right₀ hD hj) (by positivity) (by positivity)
    _ = _ := by ring

lemma kernel_derivative_bound {h : Joint → ℝ} (hh : ContDiff ℝ ∞ h)
    {D m R : ℝ} (hD : 1 ≤ D) (hm : 0 < m) (hm1 : m ≤ 1) (hR : 0 ≤ R)
    (B n j : ℕ) (hj : j ≤ n) (x : Joint)
    (hb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i h x‖ ≤ D) (hl : m ≤ h x)
    (g : 𝓢(ℝ, ℂ)) :
    ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (((n.factorial : ℝ)*2^(2*B+n)*(D^2)^n/m^(2*B+n))*rayControl B n g) /
        (1+R)^(2*B) := by
  have hu : 0 ≤ R*h x := mul_nonneg hR (hm.le.trans hl)
  have hden : 0 < (1+R*h x)^(2*B+n) := by positivity
  have harg : ContDiff ℝ ∞ (fun y => R*h y) := contDiff_const.mul hh
  have hcomp : ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g/(1+R*h x)^(2*B+n))*
        (D^2*(1+R))^j := by
    apply norm_iteratedFDeriv_comp_le (g.smooth ⊤) harg (by simp) x
    · intro i hi
      apply (le_div_iff₀ hden).mpr
      have hd := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (2*B+n,n)) (k := 2*B+n) (n := i) le_rfl (hi.trans hj) g (R*h x)
      change (1+‖R*h x‖)^(2*B+n) * ‖iteratedFDeriv ℝ i g (R*h x)‖ ≤
        2^(2*B+n)*rayControl B n g at hd
      rw [Real.norm_of_nonneg hu] at hd
      simpa only [mul_comm] using hd
    · intro i hi hij
      exact scaled_argument_derivative hh hD hR i hi x (hb i (hij.trans hj))
  have hscale : m*(1+R) ≤ 1+R*h x := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hl)]
  have habs := FourierBridge.derivative_scale_absorption R (R*h x) m D
    (2^(2*B+n)*rayControl B n g) (2*B) n j hR hm (by linarith)
    (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)) hu hscale hj
  have hbound : m^(2*B+n)*(1+R)^(2*B)*
      ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (n.factorial : ℝ)*(2^(2*B+n)*rayControl B n g)*(D^2)^n := by
    calc
      _ ≤ m^(2*B+n)*(1+R)^(2*B)*
          ((j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g/(1+R*h x)^(2*B+n))*
            (D^2*(1+R))^j) := mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ ≤ (j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g)*(D^2)^j := habs
      _ ≤ _ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj)
            (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)))
          (pow_le_pow_right₀ (one_le_pow₀ hD) hj) (by positivity)
          (mul_nonneg (by positivity) (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)))
  apply (le_div_iff₀ (by positivity : 0 < (1+R)^(2*B))).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < m^(2*B+n))).mpr
  convert hbound using 1 <;> ring

def amplitudeControl (n : ℕ) (A : 𝓢(Joint, ℂ)) : ℝ :=
  (Finset.Iic (0,n)).sup (schwartzSeminormFamily ℝ Joint ℂ) A

lemma amplitudeControl_nonneg (n : ℕ) (A : 𝓢(Joint, ℂ)) :
    0 ≤ amplitudeControl n A := apply_nonneg _ _

lemma amplitude_derivative_bound (n i : ℕ) (hi : i ≤ n)
    (A : 𝓢(Joint, ℂ)) (x : Joint) :
    ‖iteratedFDeriv ℝ i A x‖ ≤ amplitudeControl n A := by
  have hp : schwartzSeminormFamily ℝ Joint ℂ (0, i) ≤
      (Finset.Iic (0,n)).sup (schwartzSeminormFamily ℝ Joint ℂ) :=
    Finset.le_sup (Finset.mem_Iic.mpr ⟨le_rfl, hi⟩)
  have hz : ‖iteratedFDeriv ℝ i A x‖ ≤ SchwartzMap.seminorm ℝ 0 i A := by
    simpa using SchwartzMap.le_seminorm ℝ 0 i A x
  exact hz.trans (Seminorm.le_def.mp hp A)

theorem compact_profile_seminorm
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (g : 𝓢(ℝ, ℂ)) (v R : ℝ), 0 ≤ R →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * logPhase (v/(2*Real.pi)) (φ x) * g (R*h x)) →
      SchwartzMap.seminorm ℝ k n F ≤
        C*amplitudeControl n A*rayControl B n g*(1+|v|)^n/(1+R)^(2*B) := by
  obtain ⟨Dφ, hDφ, hbφ⟩ := compact_derivatives hK hφ n
  obtain ⟨Dh, hDh, hbh⟩ := compact_derivatives hK hh n
  obtain ⟨m, hm, hm1, hml⟩ := compact_positive_margin hK hh.continuous hhpos
  obtain ⟨L0, hL0⟩ := hK.bddAbove_image (continuous_norm.continuousOn : ContinuousOn (fun x : Joint => ‖x‖) K)
  let D := max Dφ Dh
  let L := max 1 L0
  have hD : 1 ≤ D := hDφ.trans (le_max_left _ _)
  have hL : 1 ≤ L := le_max_left _ _
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let Cg : ℝ := (n.factorial : ℝ)*2^(2*B+n)*(D^2)^n/m^(2*B+n)
  have hCg : 0 < Cg := by dsimp [Cg]; positivity
  let Cp : ℝ := (n.factorial : ℝ)*D^n
  have hCp : 0 < Cp := by dsimp [Cp]; positivity
  refine ⟨L^k*2^n*2^n*Cp*Cg, by positivity, ?_⟩
  intro A hA g v R hR F hF
  have hp : ContDiff ℝ ∞ (fun y => logPhase (v/(2*Real.pi)) (φ y)) :=
    (JointLogSeparation.logPhase_temperate _).1.comp hφ
  have hg : ContDiff ℝ ∞ (fun y => g (R*h y)) :=
    (g.smooth ⊤).comp (contDiff_const.mul hh)
  have hFfun : (F : Joint → ℂ) =
      fun x => A x * logPhase (v/(2*Real.pi)) (φ x) * g (R*h x) := funext hF
  have hFs : tsupport (F : Joint → ℂ) ⊆ K := by
    rw [hFfun]
    exact (tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans hA
  have hAn := amplitudeControl_nonneg n A
  have hgn := rayControl_nonneg B n g
  have hden : 0 < (1+R)^(2*B) := by positivity
  apply SchwartzMap.seminorm_le_bound ℝ k n F (by positivity)
  intro x
  by_cases hx : x ∈ K
  · have hxb : ‖x‖ ≤ L := (hL0 (mem_image_of_mem _ hx)).trans (le_max_right _ _)
    have hpbd (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => logPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
          Cp*(1+|v|)^n :=
      phase_derivative_bound hφ hD n j hj x
        (fun i hi => (hbφ i hi x hx).trans (le_max_left _ _)) v
    have hgbd (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
          Cg*rayControl B n g/(1+R)^(2*B) :=
      kernel_derivative_bound hh hD hm hm1 hR B n j hj x
        (fun i hi => (hbh i hi x hx).trans (le_max_right _ _)) (hml x hx) g
    have hap (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => A y * logPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
          2^n*amplitudeControl n A*(Cp*(1+|v|)^n) := by
      calc
        _ ≤ 2^j*amplitudeControl n A*(Cp*(1+|v|)^n) :=
          mul_derivative_bound j (A.smooth ⊤) hp x hAn (by positivity)
            (fun i hi => amplitude_derivative_bound n i (hi.trans hj) A x)
            (fun i hi => hpbd i (hi.trans hj))
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hAn) (by positivity)
    have hb := mul_derivative_bound n ((A.smooth ⊤).mul hp) hg x
      (C := 2^n*amplitudeControl n A*(Cp*(1+|v|)^n))
      (D := Cg*rayControl B n g/(1+R)^(2*B)) (by positivity) (by positivity) hap hgbd
    rw [hFfun]
    calc
      _ ≤ L^k * (2^n*(2^n*amplitudeControl n A*(Cp*(1+|v|)^n))*
          (Cg*rayControl B n g/(1+R)^(2*B))) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxb _) hb (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hz : iteratedFDeriv ℝ n (F : Joint → ℂ) x = 0 := by
      apply Function.notMem_support.mp
      intro hx'
      exact hx (hFs ((support_iteratedFDeriv_subset n) hx'))
    rw [hz, norm_zero, mul_zero]
    positivity

lemma amplitudeControl_mono {n N : ℕ} (hn : n ≤ N) (A : 𝓢(Joint, ℂ)) :
    amplitudeControl n A ≤ amplitudeControl N A := by
  exact Seminorm.le_def.mp (Finset.sup_mono (by
    intro p hp
    exact Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hp) ⟨le_rfl, hn⟩))) A

lemma rayControl_mono (B : ℕ) {n N : ℕ} (hn : n ≤ N) (g : 𝓢(ℝ, ℂ)) :
    rayControl B n g ≤ rayControl B N g := by
  exact Seminorm.le_def.mp (Finset.sup_mono (by
    intro p hp
    exact Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hp) ⟨by omega, hn⟩))) g

def heightOrder (H : Finset (ℕ × ℕ)) : ℕ := H.sup Prod.snd

theorem compact_profile_finite
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (g : 𝓢(ℝ, ℂ)) (v R : ℝ), 0 ≤ R →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * logPhase (v/(2*Real.pi)) (φ x) * g (R*h x)) →
      sourceControl H F ≤
        C*amplitudeControl (heightOrder H) A*rayControl B (heightOrder H) g*
          (1+|v|)^(heightOrder H)/(1+R)^(2*B) := by
  have hc (p : ℕ × ℕ) := compact_profile_seminorm hK hφ hh hhpos B p.1 p.2
  choose C hC hbound using hc
  let D : ℝ := 1+∑ p ∈ H, C p
  have hD : 0 < D := by
    have hs : 0 ≤ ∑ p ∈ H, C p := Finset.sum_nonneg (fun p _ => (hC p).le)
    dsimp [D]
    linarith
  refine ⟨D, hD, ?_⟩
  intro A hA g v R hR F hF
  have hAn := amplitudeControl_nonneg (heightOrder H) A
  have hgn := rayControl_nonneg B (heightOrder H) g
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro p hp
  have hn : p.2 ≤ heightOrder H := Finset.le_sup hp
  have hCD : C p ≤ D := by
    have hs := Finset.single_le_sum (fun p _ => (hC p).le) hp
    dsimp [D]
    linarith
  exact (hbound p A hA g v R hR F hF).trans (by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul
    · exact mul_le_mul
        (mul_le_mul hCD (amplitudeControl_mono hn A)
          (amplitudeControl_nonneg _ _) hD.le)
        (rayControl_mono B hn g) (rayControl_nonneg _ _ _) (by positivity)
    · exact pow_le_pow_right₀ (by linarith [abs_nonneg v]) hn
    · positivity
    · positivity)

lemma sqrt_decay_absorption (T : ℝ) (hT : 0 ≤ T) (B : ℕ) :
    (1+T)^B ≤ (1+Real.sqrt T)^(2*B) := by
  have hbase : 1+T ≤ (1+Real.sqrt T)^2 := by
    nlinarith [Real.sq_sqrt hT, Real.sqrt_nonneg T]
  calc
    _ ≤ ((1+Real.sqrt T)^2)^B := pow_le_pow_left₀ (by positivity) hbase B
    _ = _ := by rw [pow_mul]

theorem compact_fourier_profile_finite
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (U : 𝓢(ℝ, ℂ)) (v T : ℝ), 0 ≤ T →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * logPhase (v/(2*Real.pi)) (φ x) *
        paperFourierRayCLM U (Real.sqrt T*h x)) →
      sourceControl H F ≤ C*amplitudeControl (heightOrder H) A*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^(heightOrder H)/(1+T)^B := by
  obtain ⟨D, hD, hbound⟩ := compact_profile_finite hK hφ hh hhpos B H
  obtain ⟨S, E, hE, hEbound⟩ := schwartzCLM_finite_seminorm_control
    paperFourierRayCLM (Finset.Iic (2*B+heightOrder H,heightOrder H))
  refine ⟨S, D*E, by positivity, ?_⟩
  intro A hA U v T hT F hF
  have hAn := amplitudeControl_nonneg (heightOrder H) A
  have hUn : 0 ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := apply_nonneg _ _
  have hg := hEbound U
  change rayControl B (heightOrder H) (paperFourierRayCLM U) ≤
    E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U at hg
  calc
    _ ≤ D*amplitudeControl (heightOrder H) A*
        rayControl B (heightOrder H) (paperFourierRayCLM U)*
        (1+|v|)^(heightOrder H)/(1+Real.sqrt T)^(2*B) :=
      hbound A hA (paperFourierRayCLM U) v (Real.sqrt T) (Real.sqrt_nonneg _) F hF
    _ ≤ D*amplitudeControl (heightOrder H) A*
        (E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        (1+|v|)^(heightOrder H)/(1+Real.sqrt T)^(2*B) := by
      gcongr
    _ ≤ D*amplitudeControl (heightOrder H) A*
        (E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        (1+|v|)^(heightOrder H)/(1+T)^B :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (sqrt_decay_absorption T hT B)
    _ = _ := by ring

open ProbeGramJointConstruction

theorem jointProfile_homogeneous (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ) (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
        (U : 𝓢(ℝ, ℂ)) (v T : ℝ) (hT : 0 ≤ T),
      sourceControl H (jointProfile W U a b ha hab hs hW v T hT) ≤
        C*amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW)*
          S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*
          (1+|v|)^(heightOrder H)/(1+T)^B := by
  obtain ⟨S, C, hC, hb⟩ := compact_fourier_profile_finite
    (sourceCompact_isCompact b) (phase_smooth a b ha) (rootScale_smooth a b ha)
    (fun z _ => rootScale_pos a b ha z) B H
  refine ⟨S, C, hC, ?_⟩
  intro W hs hW U v T hT
  exact hb (amplitudeSchwartz W a b ha hab hs hW)
    (tsupport_amplitude_subset W a b ha hab hs) U v T hT
    (jointProfile W U a b ha hab hs hW v T hT)
    (jointProfile_factorization W U a b ha hab hs hW v T hT)

theorem jointProfile_uniform_degree (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (J : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (W : ℝ → ℂ) (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W),
      ∃ C : ℝ, 0 < C ∧ ∀ (U : 𝓢(ℝ, ℂ)) (v T : ℝ) (hT : 0 ≤ T),
        sourceControl H (jointProfile W U a b ha hab hs hW v T hT) ≤
          C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B := by
  obtain ⟨S, C, hC, hb⟩ := jointProfile_homogeneous a b ha hab B H
  refine ⟨heightOrder H, S, ?_⟩
  intro W hs hW
  let A := amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW)
  have hA : 0 ≤ A := amplitudeControl_nonneg _ _
  refine ⟨C*(1+A), by positivity, ?_⟩
  intro U v T hT
  have hU : 0 ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := apply_nonneg _ _
  exact (hb W hs hW U v T hT).trans (by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by dsimp [A]; linarith :
        amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW) ≤ 1+A) hC.le) hU)

end ProbeGramJointProfile

end

end OAI

end Source1740

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramSourceBlock.lean; sha256: a4ebe1af82819e3b2bb0d3bd97f53020ba52144f36fc38fdcd9d085c79c7b82c -/
section Source1741
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma jointProfile_physicalPoint (W : ℝ→ℂ) (U : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (v T : ℝ) (hT : 0≤T) (N : ℝ) (hN : 0<N) (m : O×O) :
    ProbeGramJointConstruction.jointProfile W U a b ha hab hs hW v T hT
      (ProbeGramLatticeDecay.physicalPoint N m)=
      shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N) := by
  rw [ProbeGramJointConstruction.jointProfile_apply]
  unfold ProbeGramJointConstruction.rawProfile ProbeGramJointConstruction.q1 ProbeGramJointConstruction.q2
  change lowGramProfile W v _ * star (lowGramProfile W v _) * _ = _
  have h₁ : ‖WithLp.fst (ProbeGramLatticeDecay.physicalPoint N m)‖^2=‖eisEmbedding m.1‖^2/N := physicalPoint_first_norm N hN m
  have h₂ : ‖WithLp.snd (ProbeGramLatticeDecay.physicalPoint N m)‖^2=‖eisEmbedding m.2‖^2/N := physicalPoint_second_norm N hN m
  rw [h₁,h₂]
  rfl

theorem literal_nonexceptional_source (A B : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧
      ∀{ι : Type*}[Fintype ι],∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C k : O)(_hC : C≠0)(_hk0 : k≠0)(u : Oˣ)(a b : ℕ)(r : O)
      (hr : Supported (Ideal.span {r})),k=u.val*goodLambda^a*(2:O)^b*r→
      ∀(P : ι→Id)[_hmax : ∀i,(P i).IsMaximal](hg : ∀i,goodLambda∉P i)(c : ι→ℕ),
      (∀i,1≤c i)→Ideal.span {C}=∏i,P i^c i→
      ∀(p : Id)[_hpmax : p.IsMaximal],p≠0→∀_hgp : goodLambda∉p,
      ringChar (O⧸p)≠2→(¬p∣jointFixedModulus S hS)→(¬p∣∏i,P i)→
      (¬6∣(normalizedFactors (Ideal.span {k})).count p)→
      ∀(U : SchwartzMap ℝ ℂ)(v T : ℝ),0≤T→∀(d : O)(N : ℝ),0<N→
      Summable (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) ∧
      ‖∑'m : O×O,jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)‖≤
        K*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B*
          (Ideal.absNorm (Ideal.span {C}):ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
            Ideal.absNorm (Ideal.span {k})/N)^A) := by
  obtain ⟨H₀,K₀,hK₀,hblock⟩ := literal_nonexceptional_block A hA a₀ b₀ ha₀ hab
  obtain ⟨J,H,hprofile⟩ := ProbeGramJointProfile.jointProfile_uniform_degree a₀ b₀ ha₀ hab B H₀
  refine ⟨J,H,?_⟩
  intro W hs hW
  obtain ⟨K₁,hK₁,hprofile⟩ := hprofile W hs hW
  refine ⟨K₀*K₁,mul_pos hK₀ hK₁,?_⟩
  intro ι inst S hS σ C k hC hk0 u a b r hr hk P hmax hg c hc hfac p hpmax hp0 hgp hchar hfixed hcommon he U v T hT d N hN
  let V := ProbeGramJointConstruction.jointProfile W U a₀ b₀ ha₀ hab hs hW v T hT
  have hv := ProbeGramJointConstruction.jointProfile_annularSupport W U a₀ b₀ ha₀ hab hs hW v T hT
  have hb := hblock S hS σ C k hC hk0 u a b r hr hk P hg c hc hfac p hp0 hgp hchar hfixed hcommon he V hv d N hN
  have hfun : (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
      V (ProbeGramLatticeDecay.physicalPoint N m))=
      (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) := by
    funext m
    rw [jointProfile_physicalPoint W U a₀ b₀ ha₀ hab hs hW v T hT N hN m]
  rw [hfun] at hb
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hm : 0≤min (1:ℝ) (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
      Ideal.absNorm (Ideal.span {k})/N)^A) := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hprofile U v T hT) hK₀.le)
        (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {C})))) (sq_nonneg N)) hm
  convert hh using 1 ; ring

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1741

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramCanonical.lean; sha256: 358f7b0daa24d6c9c2ca50672ab84dbbe46e67eb270b4dc61ca6a614cedce532 -/
section Source1742
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

abbrev GramFrequency := {k : O // k≠0}
abbrev GramPrime (C : SupportedIdeal) := {P : Id // P∈IdealMobiusDivisorSum.primeSupport C.val}
def gramPrime (C : SupportedIdeal) (P : GramPrime C) : Id := P.val
instance gramPrimeMaximal (C : SupportedIdeal) (P : GramPrime C) : (gramPrime C P).IsMaximal :=
  (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal (support_prime P.property).ne_zero

def gramExponent (C : SupportedIdeal) (P : GramPrime C) : ℕ := (normalizedFactors C.val).count P.val
lemma gramExponent_pos (C : SupportedIdeal) (P : GramPrime C) : 1≤gramExponent C P :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property)
lemma gramPrime_good (C : SupportedIdeal) (P : GramPrime C) : λ₀∉gramPrime C P :=
  (supported_factors_good C.val C.property P.val (Multiset.mem_toFinset.mp P.property)).2.1
lemma gramPrime_coprime (C : SupportedIdeal) : Pairwise (Function.onFun IsCoprime (gramPrime C)) := by
  intro P Q hpq
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hpq)
lemma gramPrime_product (C : SupportedIdeal) : C.val=∏P : GramPrime C,gramPrime C P^gramExponent C P := by
  calc
    C.val=(normalizedFactors C.val).prod := (Ideal.prod_normalizedFactors_eq_self C.property.1).symm
    _=∏P∈IdealMobiusDivisorSum.primeSupport C.val,P^(normalizedFactors C.val).count P := Finset.prod_multiset_count _
    _=_ := (Finset.prod_coe_sort _ _).symm

instance gramPrimePowerFinite (C : SupportedIdeal) (P : GramPrime C) :
    Finite (O⧸gramPrime C P^gramExponent C P) :=
  Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ (support_prime P.property).ne_zero)
instance gramPrimePowerFintype (C : SupportedIdeal) (P : GramPrime C) :
    Fintype (O⧸gramPrime C P^gramExponent C P) := Fintype.ofFinite _
instance gramProductFinite (C : SupportedIdeal) : Finite (O⧸∏P : GramPrime C,gramPrime C P^gramExponent C P) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  rw [←gramPrime_product C]
  exact C.property.1
instance gramProductFintype (C : SupportedIdeal) : Fintype (O⧸∏P : GramPrime C,gramPrime C P^gramExponent C P) := Fintype.ofFinite _

structure GramNumeratorData (k : GramFrequency) where
  unit : Oˣ
  lambdaExponent : ℕ
  twoExponent : ℕ
  good : O
  supported : Supported (Ideal.span {good})
  primary : λ₀^2∣good-1
  factor : k.val=unit.val*λ₀^lambdaExponent*(2:O)^twoExponent*good

lemma gramNumeratorData_nonempty (k : GramFrequency) : Nonempty (GramNumeratorData k) := by
  obtain ⟨u,a,b,r,hr,hpr,hf⟩ := exists_supported_numerator_factorization k.val k.property
  exact ⟨⟨u,a,b,r,hr,hpr,hf⟩⟩
def gramNumeratorData (k : GramFrequency) : GramNumeratorData k := Classical.choice (gramNumeratorData_nonempty k)

def canonicalJoint (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (n m : O) : ℂ :=
  let f:=gramNumeratorData k
  jointExtension S hS σ (primaryGenerator C.val) k.val f.unit f.lambdaExponent f.twoExponent
    f.good f.supported (gramPrime C) (gramPrime_good C) (gramExponent C) n m

lemma canonicalJoint_norm (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (n m : O) : ‖canonicalJoint S hS σ C k n m‖≤(Ideal.absNorm C.val:ℝ) := by
  have hh := jointExtension_norm S hS σ (primaryGenerator C.val) k.val
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramPrime C) (gramPrime_good C)
    (gramExponent C) (gramExponent_pos C) n m
  simpa only [←gramPrime_product C,canonicalJoint] using hh

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1742

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramClassification.lean; sha256: 521c571705d26372e1f4da19c6de934c464ca18821d78b823a6a1d8ffb910018 -/
section Source1743
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def exceptionalModulus (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) : Id :=
  jointFixedModulus S hS*C.val
lemma exceptionalModulus_nonzero (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) :
    exceptionalModulus S hS C≠0 := mul_ne_zero (jointFixedModulus_nonzero S hS) C.property.1
lemma exceptionalModulus_norm (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) :
    Ideal.absNorm (exceptionalModulus S hS C)=Ideal.absNorm (jointFixedModulus S hS)*Ideal.absNorm C.val :=
  map_mul Ideal.absNorm _ _

def ExceptionalFrequency (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) (k : GramFrequency) : Prop :=
  ∀p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C),valuation (Ideal.span {k.val}) p%6=0

lemma nonexceptional_prime (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) (k : GramFrequency)
    (hk : ¬ExceptionalFrequency S hS C k) :
    ∃p : Id,Prime p ∧ p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C) ∧
      ¬6∣(normalizedFactors (Ideal.span {k.val})).count p := by
  unfold ExceptionalFrequency at hk
  push Not at hk
  obtain ⟨p,hp,he⟩ := hk
  have hcount : (normalizedFactors (Ideal.span {k.val})).count p≠0 := by
    intro hz
    apply he
    simp [valuation,hz]
  have hprime := prime_of_normalized_factor p (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcount))
  exact ⟨p,hprime,hp,fun hd=>he (Nat.mod_eq_zero_of_dvd hd)⟩

lemma outside_exceptional_not_dvd (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal)
    (p : Id) (hp : Prime p) (hout : p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C)) :
    (¬p∣jointFixedModulus S hS) ∧ (¬p∣∏i : GramPrime C,gramPrime C i) := by
  have hnot : ¬p∣exceptionalModulus S hS C := by
    intro hd
    apply hout
    exact Multiset.mem_toFinset.mpr ((Ideal.mem_normalizedFactors_iff (exceptionalModulus_nonzero S hS C)).mpr
      ⟨Ideal.isPrime_of_prime hp,Ideal.dvd_iff_le.mp hd⟩)
  refine ⟨fun hd=>hnot (dvd_mul_of_dvd_left hd _),?_⟩
  intro hd
  apply hnot
  apply dvd_mul_of_dvd_right
  apply dvd_trans hd
  calc
    _∣∏i : GramPrime C,gramPrime C i^gramExponent C i :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (gramExponent_pos C i)))
    _=C.val := (gramPrime_product C).symm

lemma outside_exceptional_good (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal)
    (p : Id) (hp : Prime p) (hout : p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C)) :
    λ₀∉p ∧ ringChar (O⧸p)≠2 := by
  let : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hle : exceptionalModulus S hS C≤Ideal.span {(72:O)} :=
    le_trans Ideal.mul_le_left Ideal.mul_le_right
  have hh := CenteredExceptionalProfile.outside_fixed_support _ (exceptionalModulus_nonzero S hS C) hle p hp hout
  exact ⟨hh.1,ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem p hh.2.1⟩

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1743

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramAnnularCount.lean; sha256: 74668d84719e3a951e4f323bba16f71a338eb93e6195c0237f9247086f1e12f8 -/
section Source1744
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma nonzero_norm_one_le (z : O) (hz : z≠0) : (1:ℝ)≤‖eisEmbedding z‖^2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hz))

theorem annular_element_count (F : Finset O) (b N : ℝ) (hb : 0≤b) (hN : 0≤N)
    (hzero : ∀z∈F,z≠0) (hbound : ∀z∈F,‖eisEmbedding z‖^2≤b*N) :
    (F.card:ℝ)≤128*b*N := by
  by_cases hF : F.Nonempty
  · obtain ⟨z,hz⟩ := hF
    have hscale : 1≤b*N := (nonzero_norm_one_le z (hzero z hz)).trans (hbound z hz)
    simpa only [mul_assoc] using DescentFiberCost.finite_element_count_real F (b*N) hscale hbound
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF,Finset.card_empty,Nat.cast_zero]
    positivity

theorem annular_pair_count (F G : Finset O) (b N : ℝ) (hb : 0≤b) (hN : 0≤N)
    (hFzero : ∀z∈F,z≠0) (hGzero : ∀z∈G,z≠0)
    (hFbound : ∀z∈F,‖eisEmbedding z‖^2≤b*N)
    (hGbound : ∀z∈G,‖eisEmbedding z‖^2≤b*N) :
    ((F×ˢG).card:ℝ)≤(128*b)^2*N^2 := by
  rw [Finset.card_product,Nat.cast_mul]
  have hf := annular_element_count F b N hb hN hFzero hFbound
  have hg := annular_element_count G b N hb hN hGzero hGbound
  calc
    _ ≤ (128*b*N)*(128*b*N) := mul_le_mul hf hg (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1744

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramLatticeWindow.lean; sha256: 6edda56ed73b619b8452c10b912df76ad5b7da448e79ef7b97e5b15a9f356343 -/
section Source1745
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def shellLatticeColumns (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N) : Finset O :=
  (elementWindow_finite_support W hW N hN).toFinset

lemma shellLatticeColumns_mem (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N) (n : O) :
    n∈shellLatticeColumns W hW N hN ↔ W (‖eisEmbedding n‖^2/N)≠0 := by
  simp only [shellLatticeColumns,Set.Finite.mem_toFinset,Function.mem_support]
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  rfl

lemma shellLatticeColumns_nonzero (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) (n : O)
    (hn : n∈shellLatticeColumns W hW N hN) : n≠0 := by
  intro hz
  have hh := (hs ((shellLatticeColumns_mem W hW N hN n).mp hn)).1
  simp only [hz,map_zero,norm_zero,zero_pow (by decide : 2≠0),zero_div] at hh
  linarith

lemma shellLatticeColumns_norm (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (a b : ℝ) (hs : Function.support W⊆Set.Icc a b) (n : O)
    (hn : n∈shellLatticeColumns W hW N hN) : ‖eisEmbedding n‖^2≤b*N :=
  (div_le_iff₀ hN).mp (hs ((shellLatticeColumns_mem W hW N hN n).mp hn)).2

lemma shell_lattice_support (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (n m : O)
    (h : n∉shellLatticeColumns W hW N hN ∨ m∉shellLatticeColumns W hW N hN) :
    shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)=0 := by
  rcases h with h|h
  · apply shellProfile_zero_left
    simpa only [shellLatticeColumns_mem,not_not] using h
  · apply shellProfile_zero_right
    simpa only [shellLatticeColumns_mem,not_not] using h

lemma shell_lattice_summable (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (f : O→O→ℂ) :
    Summable (fun m : O×O=>f m.1 m.2*shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) := by
  apply summable_of_ne_finset_zero (s:=(shellLatticeColumns W hW N hN)×ˢ(shellLatticeColumns W hW N hN))
  intro m hm
  have h : m.1∉shellLatticeColumns W hW N hN ∨ m.2∉shellLatticeColumns W hW N hN := by simpa only [Finset.mem_product,not_and_or] using hm
  rw [shell_lattice_support W hW N hN U v T m.1 m.2 h,mul_zero]

lemma shell_lattice_tsum (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (f : O→O→ℂ) :
    (∑'m : O×O,f m.1 m.2*shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N))=
      ∑n∈shellLatticeColumns W hW N hN,∑m∈shellLatticeColumns W hW N hN,
        f n m*shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N) := by
  rw [tsum_eq_sum (s:=(shellLatticeColumns W hW N hN)×ˢ(shellLatticeColumns W hW N hN)) (by
    intro m hm
    have h : m.1∉shellLatticeColumns W hW N hN ∨ m.2∉shellLatticeColumns W hW N hN := by simpa only [Finset.mem_product,not_and_or] using hm
    rw [shell_lattice_support W hW N hN U v T m.1 m.2 h,mul_zero])]
  exact Finset.sum_product _ _ _

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1745

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramCanonicalBlock.lean; sha256: 6365678c7730e30aa63722623c0ed2478b0e5e9352c0342162db11bc9cb88064 -/
section Source1746
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def canonicalLatticeBlock (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (d : O) (W : ℝ→ℂ) (U : SchwartzMap ℝ ℂ)
    (v T N : ℝ) : ℂ :=
  ∑'m : O×O,canonicalJoint S hS σ C k (d*m.1) (d*m.2)*
    shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)

theorem canonical_nonexceptional_block (A B : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency),¬ExceptionalFrequency S hS C k→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v T N : ℝ),0≤T→0<N→
        ‖canonicalLatticeBlock S hS σ C k d W U v T N‖≤
        K*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B*
          (Ideal.absNorm C.val:ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*
            Ideal.absNorm (Ideal.span {k.val})/N)^A) := by
  obtain ⟨J,H,hsource⟩ := literal_nonexceptional_source A B hA a₀ b₀ ha₀ hab
  refine ⟨J,H,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hsource⟩ := hsource W hs hW
  refine ⟨K,hK,?_⟩
  intro S hS σ C k hk d U v T N hT hN
  obtain ⟨p,hp,hout,he⟩ := nonexceptional_prime S hS C k hk
  let : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := outside_exceptional_good S hS C p hp hout
  have hd := outside_exceptional_not_dvd S hS C p hp hout
  have hcspan := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ C.property)).1
  have hf : Ideal.span {primaryGenerator C.val}=∏i : GramPrime C,gramPrime C i^gramExponent C i := hcspan.trans (gramPrime_product C)
  have hh := hsource S hS σ (primaryGenerator C.val) k.val
    (supported_primaryGenerator_ne_zero _ C.property) k.property
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramNumeratorData k).factor
    (gramPrime C) (gramPrime_good C) (gramExponent C) (gramExponent_pos C) hf
    p hp.ne_zero hg.1 hg.2 hd.1 hd.2 he U v T hT d N hN
  simpa only [canonicalLatticeBlock,canonicalJoint,hcspan] using hh.2

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1746

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramCanonicalSource.lean; sha256: 0d5606064e55ed70638741ede5f837bef021040a342c3d0ff05cae82d5e084a9 -/
section Source1747
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def originalCommonBlock (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  let N:=commonResidualScale C Y
  let hN:=commonResidualScale_pos C Y hY
  let F:=lowGaussColumns W hW N hN
  (∑I∈F,∑J∈F,if IsCoprime I.val J.val then
      (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
      star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y))*
      actualCorrelation (primaryGenerator (supportedIdealProduct C I).val)
        (primaryGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C J).property)
        (primaryGenerator C.val*k.val)*
      paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator C.val*k.val)‖^2/
        ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2)
      else 0)

theorem originalCommonBlock_eq_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C : SupportedIdeal) (k : GramFrequency)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    originalCommonBlock S hS σ C k W hW Y Q hY U v=
      ∑D∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val,
        (moebius D:ℂ)*canonicalLatticeBlock S hS σ C k (primaryGenerator D) W U v
          (frequencyScale C k.val Y Q) (commonResidualScale C Y/Ideal.absNorm D) := by
  have hh := original_common_window_source S hS hbad σ C k.val
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramNumeratorData k).primary
    (gramNumeratorData k).factor (gramPrime C) (gramPrime_good C) (gramExponent C)
    (gramExponent_pos C) (gramPrime_coprime C) (gramPrime_product C) W hW Y Q hY hQ U v
  change originalCommonBlock S hS σ C k W hW Y Q hY U v=_ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hD0 := (divisorPool_supported _ D hD).1
  have hN : 0<commonResidualScale C Y/(Ideal.absNorm D:ℝ) :=
    div_pos (commonResidualScale_pos C Y hY) (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0))
  exact (shell_lattice_summable W hW _ hN U v (frequencyScale C k.val Y Q)
    (fun n m=>canonicalJoint S hS σ C k (primaryGenerator D*n) (primaryGenerator D*m))).tsum_prod.symm

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1747

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramFrequencyConvergence.lean; sha256: d508f202f7b99ab762134490e648ebffccb033289b8b21301378a01ac066f2cf -/
section Source1748
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma actual_correlation_radial_summable (I J : SupportedIdeal) (C : O) (hC : C≠0)
    (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0<Q) :
    Summable (fun k : O=>actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (C*k)*
      paperRadialFourier U (Q*‖eisEmbedding (C*k)‖^2/
        ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2)) := by
  let t:=Q*‖eisEmbedding C‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2
  have hc : 0<‖eisEmbedding C‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hC))
  have hd : 0<‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (mul_ne_zero
      (supported_primaryGenerator_ne_zero _ I.property) (supported_primaryGenerator_ne_zero _ J.property))))
  have ht : 0<t := div_pos (mul_pos hQ hc) hd
  have hs := paperRadialFourier_lattice_summable_norm U t ht
  let B : ℝ := (Ideal.absNorm I.val:ℝ)*Ideal.absNorm J.val
  have hb (k : O) : ‖actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (C*k)‖≤B := by
    have hh := CenteredMomentTail.actualCorrelation_norm_le (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (C*k)
    simpa only [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1,
      (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ J.property)).1] using hh
  have harg (k : O) : Q*‖eisEmbedding (C*k)‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2=t*‖eisEmbedding k‖^2 := by
    simp only [map_mul,norm_mul,mul_pow,t]
    ring
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun k=>norm_nonneg _) _ (hs.mul_left B)
  intro k
  rw [norm_mul,harg]
  exact mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _)

lemma originalCommonBlock_summable (S : Finset (Ideal O)) (hS : ∀p∈S,p.IsMaximal)
    (σ : RayFourExpansion.RayRing) (C : SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    Summable (fun k : GramFrequency=>originalCommonBlock S hS σ C k W hW Y Q hY U v) := by
  unfold originalCommonBlock
  apply summable_sum
  intro I hI
  apply summable_sum
  intro J hJ
  by_cases hij : IsCoprime I.val J.val
  · simp only [hij,ite_true]
    have hs := (actual_correlation_radial_summable (supportedIdealProduct C I) (supportedIdealProduct C J)
      (primaryGenerator C.val) (supported_primaryGenerator_ne_zero _ C.property) U Q hQ).subtype (fun k : O=>k≠0)
    simpa only [Function.comp_def,mul_assoc] using hs.mul_left
      ((lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
       star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y)))
  · simpa only [hij,ite_false] using (summable_zero : Summable (fun _ : GramFrequency=>(0:ℂ)))

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1748

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramNonzeroFrequency.lean; sha256: 3139cc2d821268fa31de88d4e30999075f0864ffcbead6dd4867988af4359bab -/
section Source1749
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma nonzero_tsum_indicator (f : O→ℂ) :
    (∑'k : O,if k=0 then 0 else f k)=∑'k : GramFrequency,f k.val := by
  rw [←tsum_subtype_eq_of_support_subset (s:={k : O | k≠0}) (by
    intro k hk hz
    subst k
    exact hk (by simp))]
  apply tsum_congr
  intro k
  exact ite_eq_right k.property

def gramFrequencyNeg : GramFrequency≃GramFrequency where
  toFun k:=⟨-k.val,neg_ne_zero.mpr k.property⟩
  invFun k:=⟨-k.val,neg_ne_zero.mpr k.property⟩
  left_inv k:=Subtype.ext (neg_neg k.val)
  right_inv k:=Subtype.ext (neg_neg k.val)

lemma actual_common_nonzero_tsum (C n₁ n₂ : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁})) (h₂ : Supported (Ideal.span {n₂}))
    (F : O→ℂ) :
    (∑'j : GramFrequency,actualCorrelation (C*n₁) (C*n₂)
      (supported_mul_elements C n₁ hC h₁) (supported_mul_elements C n₂ hC h₂) j.val*F j.val)=
      ∑'k : GramFrequency,actualCorrelation (C*n₁) (C*n₂)
        (supported_mul_elements C n₁ hC h₁) (supported_mul_elements C n₂ hC h₂) (C*k.val)*F (C*k.val) := by
  have hh := actual_common_frequency_tsum C n₁ n₂ hC h₁ h₂ (fun j=>if j=0 then 0 else F j)
  have hc0 := supported_element_ne_zero C hC
  simp only [mul_ite,mul_zero,mul_eq_zero,hc0,false_or] at hh
  simpa only [nonzero_tsum_indicator] using hh

lemma actual_gcd_nonzero_frequency_source (I J : SupportedIdeal) (U : SchwartzMap ℝ ℂ) (Q : ℝ) :
    (∑'h : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (-h.val)*
      paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))=
      ∑'k : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) (primaryGenerator (gcdCommon I J).val*k.val)*
        paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator (gcdCommon I J).val*k.val)‖^2/
          ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2) := by
  have hn := gramFrequencyNeg.tsum_eq (fun h : GramFrequency=>
    actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) h.val*
      paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simp only [gramFrequencyNeg,Equiv.coe_fn_mk,map_neg,norm_neg] at hn
  rw [hn]
  have hh := actual_common_nonzero_tsum (primaryGenerator (gcdCommon I J).val)
    (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val)
    ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdLeft I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdRight I J).property)
    (fun h=>paperRadialFourier U (Q*‖eisEmbedding h‖^2/
      ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J] using hh

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1749

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGramDiagonal.lean; sha256: 647bc9d9e54c15a55fb52539a12d70cfeeb9d2a3da6e23dd84747cbcea53227b -/
section Source1750
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSecondDiagonal EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramZeroMode (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) : ℂ :=
  (Q:ℂ)*paperRadialFourier U 0*
    secondZeroEnergy (lowGaussColumns W1 hW1 Y hY) (fun s=>primaryGenerator s.val)
      (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property) (lowGaussColumn C W1 Y σ v)

lemma lowGramZeroMode_eq_source (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) :
    lowGramZeroMode C W1 hW1 Y hY σ v U Q=
      ((Q/Y^3:ℝ):ℂ)*
        ∑s∈lowGaussColumns W1 hW1 Y hY,∑t∈lowGaussColumns W1 hW1 Y hY,
          ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
            star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y)))*
          actualCorrelation (primaryGenerator s.val) (primaryGenerator t.val)
            ((supported_span_primaryGenerator_iff s.val).mpr s.property)
            ((supported_span_primaryGenerator_iff t.val).mpr t.property) 0*paperRadialFourier U 0 := by
  unfold lowGramZeroMode secondZeroEnergy
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have hes := congrArg Ideal.absNorm ((primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1)
  have het := congrArg Ideal.absNorm ((primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1)
  rw [hes,het]
  calc
    _ = ((lowGaussColumn C W1 Y σ v s*star (lowGaussColumn C W1 Y σ v t))*
        ((Q:ℂ)/((Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ))))*
        actualCorrelation (primaryGenerator s.val) (primaryGenerator t.val) _ _ 0*paperRadialFourier U 0 := by ring
    _ = _ := by rw [lowGram_pair_prefactor C W1 Y hY σ v Q s t];ring

lemma lowGramZeroMode_bound (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0≤Q) :
    ‖lowGramZeroMode C W1 hW1 Y hY σ v U Q‖≤
      Q*‖paperRadialFourier U 0‖*∑s∈lowGaussColumns W1 hW1 Y hY,‖lowGaussColumn C W1 Y σ v s‖^2 := by
  rw [lowGramZeroMode,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply secondZeroEnergy_bound
  · intro s
    exact (primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).2
  · intro s hs t ht h
    apply Subtype.ext
    have hes := (primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1
    have het := (primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1
    rw [←hes,←het]
    exact congrArg (fun z : O=>Ideal.span {z}) h

theorem lowGramZeroMode_source_bound (a b B : ℝ) (ha : 0<a) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W1 : ℝ→ℂ,∀hW1 : HasCompactSupport W1,
      Function.support W1⊆Set.Icc a b→(∀x,‖W1 x‖≤B)→
      ∀Y : ℝ,∀hY : 1≤Y,∀σ : RayRing,∀v : ℝ,∀U : SchwartzMap ℝ ℂ,∀Q : ℝ,0≤Q→
      ‖lowGramZeroMode (calibrationForSet S hS) W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY) σ v U Q‖≤
        C*‖paperRadialFourier U 0‖*Q/Y := by
  obtain ⟨C,hC,hb⟩ := lowGaussColumn_l2_bound a b B ha hB
  refine ⟨C,hC,?_⟩
  intro S hS W1 hW1 hWS hWB Y hY σ v U Q hQ
  apply (lowGramZeroMode_bound (calibrationForSet S hS) W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY) σ v U Q hQ).trans
  calc
    _ ≤ Q*‖paperRadialFourier U 0‖*(C/Y) := by
      exact mul_le_mul_of_nonneg_left (hb S hS W1 hW1 hWS hWB Y hY σ v) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1750

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramEnergyNonzero.lean; sha256: bc894f29b3d0d4219f8363d3de8f077b39919d8dea453b97683092babcf85ace -/
section Source1751
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT RayFourExpansion
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

lemma original_pair_zero_split (I J : SupportedIdeal) (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0<Q) :
    (∑'h : O,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (-h)*
      paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))=
      actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) 0*paperRadialFourier U 0+
      ∑'h : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) (-h.val)*
        paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2) := by
  have hs := actual_correlation_radial_summable I J (-1) (by norm_num) U Q hQ
  simp only [neg_one_mul,map_neg,norm_neg] at hs
  have hh := hs.tsum_eq_add_tsum_ite 0
  simpa only [neg_zero,map_zero,norm_zero,zero_pow (by decide : 2≠0),mul_zero,zero_div,nonzero_tsum_indicator] using hh

theorem original_energy_nonzero (C : CalibrationData) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0<Q) :
    gaussEnergy (lowGaussColumns W hW Y hY) (fun I=>primaryGenerator I.val)
      (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
      (lowGaussColumn C W Y σ v) U Q=
      lowGramZeroMode C W hW Y hY σ v U Q+
      ((Q/Y^3:ℝ):ℂ)*∑I∈lowGaussColumns W hW Y hY,∑J∈lowGaussColumns W hW Y hY,
        ((lowGramCoefficient C σ I*lowGramProfile W v ((Ideal.absNorm I.val:ℝ)/Y))*
          star (lowGramCoefficient C σ J*lowGramProfile W v ((Ideal.absNorm J.val:ℝ)/Y)))*
        ∑'h : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
          ((supported_span_primaryGenerator_iff _).mpr I.property)
          ((supported_span_primaryGenerator_iff _).mpr J.property) (-h.val)*
          paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2) := by
  rw [lowGram_source_poisson C W hW Y hY σ v U Q hQ,lowGramZeroMode_eq_source]
  simp_rw [original_pair_zero_split _ _ U Q hQ,mul_add,Finset.sum_add_distrib]
  simp only [mul_add]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  ring

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1751

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramFiniteGcd.lean; sha256: 0cfc6f8f38d312936b6d49952d7b49f18cd2deb5737780725d83ffac83b4707c -/
section Source1752
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma supportedIdealProduct_injective (C : SupportedIdeal) : Function.Injective (supportedIdealProduct C) := by
  intro I J h
  apply Subtype.ext
  exact mul_left_cancel₀ C.property.1 (congrArg Subtype.val h)

def commonPool (F : Finset SupportedIdeal) : Finset SupportedIdeal :=
  (F×ˢF).image (fun p=>gcdCommon p.1 p.2)
def commonColumns (F : Finset SupportedIdeal) (C : SupportedIdeal) : Finset SupportedIdeal :=
  F.preimage (supportedIdealProduct C) (supportedIdealProduct_injective C).injOn
lemma commonColumns_mem (F : Finset SupportedIdeal) (C I : SupportedIdeal) :
    I∈commonColumns F C ↔ supportedIdealProduct C I∈F := Finset.mem_preimage

def commonTriples (F : Finset SupportedIdeal) : Finset ((_C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal)) :=
  (commonPool F).sigma (fun C=>(commonColumns F C×ˢcommonColumns F C).filter (fun p=>IsCoprime p.1.val p.2.val))

theorem finite_pair_gcd (F : Finset SupportedIdeal) (f : SupportedIdeal→SupportedIdeal→ℂ) :
    (∑I∈F,∑J∈F,f I J)=
      ∑C∈commonPool F,∑I∈commonColumns F C,∑J∈commonColumns F C,
        if IsCoprime I.val J.val then f (supportedIdealProduct C I) (supportedIdealProduct C J) else 0 := by
  have he : (∑p∈F×ˢF,f p.1 p.2)=
      ∑t∈commonTriples F,f (supportedIdealProduct t.1 t.2.1) (supportedIdealProduct t.1 t.2.2) := by
    apply Finset.sum_bij (fun p _=>⟨gcdCommon p.1 p.2,gcdLeft p.1 p.2,gcdRight p.1 p.2⟩)
    · intro p hp
      have hl : supportedIdealProduct (gcdCommon p.1 p.2) (gcdLeft p.1 p.2)=p.1 := Subtype.ext (gcd_common_left _ _)
      have hr : supportedIdealProduct (gcdCommon p.1 p.2) (gcdRight p.1 p.2)=p.2 := Subtype.ext (gcd_common_right _ _)
      simp only [commonTriples,Finset.mem_sigma,Finset.mem_filter,Finset.mem_product,commonColumns_mem]
      exact ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,⟨by rw [hl];exact (Finset.mem_product.mp hp).1,by rw [hr];exact (Finset.mem_product.mp hp).2⟩,gcd_residual_coprime _ _⟩
    · intro p hp q hq he
      have hc := congrArg Sigma.fst he
      have hl := congrArg (fun t : (C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal)=>t.2.1) he
      have hr := congrArg (fun t : (C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal)=>t.2.2) he
      apply Prod.ext <;> apply Subtype.ext
      · rw [←gcd_common_left p.1 p.2,←gcd_common_left q.1 q.2]
        rw [show gcdCommon p.1 p.2=gcdCommon q.1 q.2 from hc,show gcdLeft p.1 p.2=gcdLeft q.1 q.2 from hl]
      · rw [←gcd_common_right p.1 p.2,←gcd_common_right q.1 q.2]
        rw [show gcdCommon p.1 p.2=gcdCommon q.1 q.2 from hc,show gcdRight p.1 p.2=gcdRight q.1 q.2 from hr]
    · intro t ht
      have ht' : t.1∈commonPool F ∧ (t.2.1∈commonColumns F t.1 ∧ t.2.2∈commonColumns F t.1) ∧ IsCoprime t.2.1.val t.2.2.val := by
        simpa only [commonTriples,Finset.mem_sigma,Finset.mem_filter,Finset.mem_product] using ht
      let u : CoprimeTriple:=⟨(t.1,t.2),ht'.2.2⟩
      refine ⟨(supportedIdealProduct t.1 t.2.1,supportedIdealProduct t.1 t.2.2),?_,?_⟩
      · exact Finset.mem_product.mpr ⟨(commonColumns_mem F _ _).mp ht'.2.1.1,(commonColumns_mem F _ _).mp ht'.2.1.2⟩
      · have h:=congrArg Subtype.val (gcdTriple_multiply u)
        exact congrArg (fun p : SupportedIdeal×(SupportedIdeal×SupportedIdeal)=>(⟨p.1,p.2⟩ : (C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal))) h
    · intro p hp
      have hl : supportedIdealProduct (gcdCommon p.1 p.2) (gcdLeft p.1 p.2)=p.1 := Subtype.ext (gcd_common_left _ _)
      have hr : supportedIdealProduct (gcdCommon p.1 p.2) (gcdRight p.1 p.2)=p.2 := Subtype.ext (gcd_common_right _ _)
      simp only [hl,hr]
  rw [Finset.sum_product] at he
  rw [he,commonTriples,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.sum_filter,Finset.sum_product]

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1752

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramWindowGcd.lean; sha256: 940fed03536fbef774a1de0ac9d5a33b83a84f08be0efe58bea2cfdf10b3c162 -/
section Source1753
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss

lemma commonColumns_window (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C : SupportedIdeal) :
    commonColumns (lowGaussColumns W hW Y hY) C=
      lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY) := by
  ext I
  rw [commonColumns_mem,lowGaussColumns_mem,lowGaussColumns_mem,common_column_ratio]

theorem original_window_gcd (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y)
    (f : SupportedIdeal→SupportedIdeal→ℂ) :
    (∑I∈lowGaussColumns W hW Y hY,∑J∈lowGaussColumns W hW Y hY,f I J)=
      ∑C∈commonPool (lowGaussColumns W hW Y hY),
        ∑I∈lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY),
        ∑J∈lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY),
        if IsCoprime I.val J.val then f (supportedIdealProduct C I) (supportedIdealProduct C J) else 0 := by
  rw [finite_pair_gcd]
  simp_rw [commonColumns_window]

lemma commonPool_norm_bound (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y)
    (a b : ℝ) (hs : Function.support W⊆Set.Icc a b)
    (C : SupportedIdeal) (hC : C∈commonPool (lowGaussColumns W hW Y hY)) :
    (Ideal.absNorm C.val:ℝ)≤b*Y := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hC
  have hnp : (Ideal.absNorm p.1.val:ℝ)≤b*Y :=
    (div_le_iff₀ hY).mp (hs ((lowGaussColumns_mem W hW Y hY p.1).mp (Finset.mem_product.mp hp).1)).2
  have hg : Ideal.absNorm (gcdCommon p.1 p.2).val≤Ideal.absNorm p.1.val :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.1.property.1))
      (map_dvd Ideal.absNorm (gcd_dvd_left p.1.val p.2.val))
  exact (by exact_mod_cast hg : (Ideal.absNorm (gcdCommon p.1 p.2).val:ℝ)≤Ideal.absNorm p.1.val).trans hnp

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1753

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramCommonEnergy.lean; sha256: ed94d76e75d348f80649e7aa443a74446ace763933ad1fa70949208bc937832c -/
section Source1754
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT RayFourExpansion
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gcdCommon_product_coprime (C I J : SupportedIdeal) (h : IsCoprime I.val J.val) :
    gcdCommon (supportedIdealProduct C I) (supportedIdealProduct C J)=C := by
  have hh:=congrArg (fun t : CoprimeTriple=>t.val.1) (gcdTriple_multiply ⟨(C,I,J),h⟩)
  exact hh

def originalPairWeight (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (W : ℝ→ℂ) (Y v : ℝ) (I J : SupportedIdeal) : ℂ :=
  (lowGramCoefficient (calibrationForSet S hS) σ I*lowGramProfile W v ((Ideal.absNorm I.val:ℝ)/Y))*
    star (lowGramCoefficient (calibrationForSet S hS) σ J*lowGramProfile W v ((Ideal.absNorm J.val:ℝ)/Y))

theorem original_nonzero_common_sum (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    (∑I∈lowGaussColumns W hW Y hY,∑J∈lowGaussColumns W hW Y hY,
      originalPairWeight S hS σ W Y v I J*
      ∑'h : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) (-h.val)*
        paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))=
      ∑C∈commonPool (lowGaussColumns W hW Y hY),∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v := by
  simp_rw [actual_gcd_nonzero_frequency_source]
  rw [original_window_gcd]
  apply Finset.sum_congr rfl
  intro C hC
  let F:=lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)
  let f := fun (I J : SupportedIdeal) (k : GramFrequency)=>
    if IsCoprime I.val J.val then
      originalPairWeight S hS σ W Y v (supportedIdealProduct C I) (supportedIdealProduct C J)*
      actualCorrelation (primaryGenerator (supportedIdealProduct C I).val) (primaryGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C J).property) (primaryGenerator C.val*k.val)*
      paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator C.val*k.val)‖^2/
        ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2) else 0
  have hf (I J : SupportedIdeal) : Summable (f I J) := by
    by_cases hij : IsCoprime I.val J.val
    · have hh := ((actual_correlation_radial_summable (supportedIdealProduct C I) (supportedIdealProduct C J)
        (primaryGenerator C.val) (supported_primaryGenerator_ne_zero _ C.property) U Q hQ).subtype (fun k : O=>k≠0)).mul_left
          (originalPairWeight S hS σ W Y v (supportedIdealProduct C I) (supportedIdealProduct C J))
      simpa only [f,hij,ite_true,Function.comp_def,mul_assoc] using hh
    · simpa only [f,hij,ite_false] using (summable_zero : Summable (fun _ : GramFrequency=>(0:ℂ)))
  have hr : (∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v)=
      ∑I∈F,∑J∈F,∑'k : GramFrequency,f I J k := by
    change (∑'k : GramFrequency,∑I∈F,∑J∈F,f I J k)=_
    rw [Summable.tsum_finsetSum (fun I hI=>summable_sum (fun J hJ=>hf I J))]
    apply Finset.sum_congr rfl
    intro I hI
    exact Summable.tsum_finsetSum (fun J hJ=>hf I J)
  rw [hr]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases hij : IsCoprime I.val J.val
  · simp only [hij,ite_true,f,gcdCommon_product_coprime C I J hij]
    rw [←tsum_mul_left]
    apply tsum_congr
    intro k
    ring
  · simp only [hij,ite_false,f,tsum_zero]

theorem original_energy_common_blocks (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    gaussEnergy (lowGaussColumns W hW Y hY) (fun I=>primaryGenerator I.val)
      (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
      (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q=
      lowGramZeroMode (calibrationForSet S hS) W hW Y hY σ v U Q+
      ((Q/Y^3:ℝ):ℂ)*(∑C∈commonPool (lowGaussColumns W hW Y hY),
        ∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v) := by
  rw [original_energy_nonzero _ _ _ _ _ _ _ _ _ hQ]
  congr 1
  congr 1
  exact original_nonzero_common_sum S hS σ W hW Y Q hY hQ U v

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1754

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramWeightedFrequency.lean; sha256: 874fd2793a62a44ab2c420e96caa6cf82247299611b1454411aad0b8d5e52640 -/
section Source1755
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma min_product_amplification (L T : ℝ) (hL : 0≤L) (hT : 0≤T) (A : ℕ) :
    min 1 ((L*T)^A)≤(1+T)^A*min 1 (L^A) := by
  by_cases h : L^A≤1
  · rw [min_eq_right h]
    apply (min_le_right _ _).trans
    rw [mul_pow,mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT (by linarith) _) (pow_nonneg hL _)
  · rw [min_eq_left (le_of_not_ge h),mul_one]
    exact (min_le_left _ _).trans (one_le_pow₀ (by linarith))

lemma frequencyScale_ratio (C : SupportedIdeal) (k : GramFrequency) (Y Q : ℝ) :
    frequencyScale C k.val Y Q=(Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/Ideal.absNorm C.val) := by
  rw [frequencyScale,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,div_div_eq_mul_div]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem canonical_nonexceptional_weighted (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency),¬ExceptionalFrequency S hS C k→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v H N : ℝ),0<H→0<N→
        ‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
          (Ideal.absNorm C.val:ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A)*
          (1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := by
  obtain ⟨J,H₀,hblock⟩ := canonical_nonexceptional_block A (A+2) hA a₀ b₀ ha₀ hab
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hblock⟩ := hblock W hs hW
  refine ⟨K,hK,?_⟩
  intro S hS σ C k hk d U v H N hH hN
  let t : ℝ := (Ideal.absNorm (Ideal.span {k.val}):ℝ)/H
  let L : ℝ := (Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N
  have ht : 0≤t := by dsimp [t];positivity
  have hL : 0≤L := by dsimp [L];positivity
  have htp : 0<1+t := by linarith
  have he : (Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*Ideal.absNorm (Ideal.span {k.val})/N=L*t := by
    dsimp [L,t]
    field_simp
  have hb := hblock S hS σ C k hk d U v t N ht hN
  rw [he] at hb
  apply hb.trans
  calc
    _≤K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+t)^(A+2)*
        (Ideal.absNorm C.val:ℝ)*N^2*((1+t)^A*min 1 (L^A)) :=
      mul_le_mul_of_nonneg_left (min_product_amplification L t hL ht A) (by positivity)
    _=K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Ideal.absNorm C.val:ℝ)*N^2*
        min 1 (L^A)*(1+t)^(-2:ℝ) := by
      rw [Real.rpow_neg htp.le,Real.rpow_two,pow_add]
      field_simp
    _=_ := rfl

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1755

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramCanonicalTrivial.lean; sha256: 40d0da6ba5b0fff76855205f2b057579a8ac28b9f182632287f9d7c7a80bb44d -/
section Source1756
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem canonical_trivial_block (a b B : ℝ) (ha : 0<a) (hb : 0≤b) (hB : 0≤B) (A : ℕ) :
    ∃s : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀(W : ℝ→ℂ)(_hcompact : HasCompactSupport W),
      (Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤B)→
      ∀(U : SchwartzMap ℝ ℂ)(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency)(d : O)(N T v : ℝ),0<N→0≤T→
      (1+T)^A*‖canonicalLatticeBlock S hS σ C k d W U v T N‖≤
        K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Ideal.absNorm C.val:ℝ)*N^2 := by
  obtain ⟨s,K,hK,hprofile⟩ := shellProfile_weighted_bound a b B ha hB A
  refine ⟨s,(1+128*b)^2*K,by positivity,?_⟩
  intro W hcompact hs hW U S hS σ C k d N T v hN hT
  let F:=shellLatticeColumns W hcompact N hN
  let G:=F
  have hF0 : ∀z∈F,z≠0 := shellLatticeColumns_nonzero W hcompact N hN a b ha hs
  have hG0 : ∀z∈G,z≠0 := hF0
  have hFN : ∀z∈F,‖eisEmbedding z‖^2≤b*N := shellLatticeColumns_norm W hcompact N hN a b hs
  have hGN : ∀z∈G,‖eisEmbedding z‖^2≤b*N := hFN
  unfold canonicalLatticeBlock
  rw [shell_lattice_tsum W hcompact N hN U v T (fun n m=>canonicalJoint S hS σ C k (d*n) (d*m))]
  have hcoef (n m : O) : ‖canonicalJoint S hS σ C k (d*n) (d*m)‖≤(Ideal.absNorm C.val:ℝ) :=
    canonicalJoint_norm S hS σ C k _ _
  have hpoint (n m : O) : (1+T)^A*‖canonicalJoint S hS σ C k (d*n) (d*m)*
      shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)‖≤
      (Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) := by
    rw [norm_mul]
    calc
      _ = ‖canonicalJoint S hS σ C k (d*n) (d*m)‖*
          ((1+T)^A*‖shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)‖) := by ring
      _ ≤ _ := mul_le_mul (hcoef n m) (hprofile W hs hW U v T _ _ hT) (by positivity) (by positivity)
  have hcount := annular_pair_count F G b N hb hN.le hF0 hG0 hFN hGN
  calc
    _ ≤ (1+T)^A*(∑n∈F,∑m∈G,‖canonicalJoint S hS σ C k (d*n) (d*m)*
        shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _=>norm_sum_le _ _)
    _ ≤ (F.card:ℝ)*G.card*((Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      simp_rw [Finset.mul_sum]
      calc
        _ ≤ ∑n∈F,∑m∈G,(Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) :=
          Finset.sum_le_sum (fun n _=>Finset.sum_le_sum (fun m _=>hpoint n m))
        _ = _ := by simp;ring
    _ ≤ ((128*b)^2*N^2)*((Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Finset.card_product,Nat.cast_mul] using hcount
    _ ≤ _ := by
      have hb' : (128*b)^2≤(1+128*b)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hb' (show 0≤N^2*((Ideal.absNorm C.val:ℝ)*
        (K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) by positivity)]

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1756

/- Original source: OAI/NumberTheory/DirichletL/Detector/LowGramExceptional.lean; sha256: 350cb3efaee0d998f134aa74b998dffb1850170006eafdd6729a89fafe181b6c -/
section Source1757
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CenteredExceptionalCount IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramRemainders (F : Finset O) : Finset Id :=
  F.image (fun z=>sixthRemainder (Ideal.span {z}))

lemma lowGramRemainders_nonzero (F : Finset O) (R : Id) (hR : R∈lowGramRemainders F) : R≠0 := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hR
  exact sixthRemainder_ne_zero _

theorem lowGramRemainders_card (F : Finset O) (G : Id)
    (hres : ∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0) :
    (lowGramRemainders F).card≤6^(primeSupport G).card := by
  have hlt (R : lowGramRemainders F) (P : Id) : valuation R.val P<6 := by
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp R.property
    rw [←he]
    exact sixthRemainder_valuation_lt _ _
  let code : lowGramRemainders F→(primeSupport G→Fin 6) := fun R P=>⟨valuation R.val P.val,hlt R P.val⟩
  have hinj : Function.Injective code := by
    intro R T he
    apply Subtype.ext
    apply ideal_eq_of_valuation_eq (lowGramRemainders_nonzero F R.val R.property)
      (lowGramRemainders_nonzero F T.val T.property)
    intro P
    by_cases hp : P∈primeSupport G
    · exact congrArg Fin.val (congrFun he ⟨P,hp⟩)
    · obtain ⟨r,hr,her⟩ := Finset.mem_image.mp R.property
      obtain ⟨t,ht,het⟩ := Finset.mem_image.mp T.property
      rw [←her,←het,sixthRemainder_valuation,sixthRemainder_valuation,hres r hr P hp,hres t ht P hp]
  have hh := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using hh

theorem lowGramExceptional_raw_count (F : Finset O) (G : Id) (H : ℝ) (hH : 0≤H)
    (hF : ∀z∈F,z≠0)
    (hres : ∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0)
    (hN : ∀z∈F,(Ideal.absNorm (Ideal.span {z}):ℝ)≤H) :
    (F.card:ℝ)≤768*(6:ℝ)^(primeSupport G).card*H^(1/6:ℝ) := by
  have hh := element_count_remainder_family F (lowGramRemainders F)
    (lowGramRemainders_nonzero F) H hH hF (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩) hN
  calc
    _ ≤ ∑R∈lowGramRemainders F,768*(H/(Ideal.absNorm R:ℝ))^(1/6:ℝ) := hh
    _ ≤ ∑_R∈lowGramRemainders F,768*H^(1/6:ℝ) := by
      apply Finset.sum_le_sum
      intro R hR
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow (div_nonneg hH (Nat.cast_nonneg _)) _ (by norm_num)
      exact div_le_self hH (norm_one_le (lowGramRemainders_nonzero F R hR))
    _ = (lowGramRemainders F).card*(768*H^(1/6:ℝ)) := by simp
    _ ≤ ((6:ℝ)^(primeSupport G).card)*(768*H^(1/6:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast lowGramRemainders_card F G hres
    _ = _ := by ring

theorem lowGramExceptional_count (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀G : Id,G≠0→∀F : Finset O,∀H : ℝ,0≤H→
      (∀z∈F,z≠0)→
      (∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0)→
      (∀z∈F,(Ideal.absNorm (Ideal.span {z}):ℝ)≤H)→
      (F.card:ℝ)≤C*(Ideal.absNorm G:ℝ)^ε*H^(1/6:ℝ) := by
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (ε/3) (by positivity)
  refine ⟨768*C^3,by positivity,?_⟩
  intro G hG F H hH hF hres hN
  have hp : (6:ℝ)^(primeSupport G).card≤C^3*(Ideal.absNorm G:ℝ)^ε := by
    calc
      _ ≤ ((2:ℝ)^3)^(primeSupport G).card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = ((2:ℝ)^(primeSupport G).card)^3 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
      _ ≤ (C*(Ideal.absNorm G:ℝ)^(ε/3))^3 := pow_le_pow_left₀ (by positivity) (hb G hG) 3
      _ = _ := by
        rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg (Ideal.absNorm G))]
        congr 2
        norm_num
  apply (lowGramExceptional_raw_count F G H hH hF hres hN).trans
  calc
    _ ≤ 768*(C^3*(Ideal.absNorm G:ℝ)^ε)*H^(1/6:ℝ) := by gcongr
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI

end Source1757

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramFrequencySummation.lean; sha256: d1c71bdee596df79381076f24c4a2284d4d32d569846b81863313f44ee3e5bb2 -/
section Source1758
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.ProbeGramFrequencySummation
local notation "O" => ActualEisensteinCubic.O

def frequencyNorm (k : O) : ℝ := Ideal.absNorm (Ideal.span {k})

lemma frequencyNorm_nonneg (k : O) : 0 ≤ frequencyNorm k := Nat.cast_nonneg _

lemma frequencyNorm_one_le (k : O) (hk : k ≠ 0) : 1 ≤ frequencyNorm k := by
  unfold frequencyNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hk))

theorem finite_weighted_of_count {α : Type*} (E : Finset α) (q : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (C d H : ℝ) (hC : 0 ≤ C) (hd : d ≤ 1) (hH : 0 < H)
    (hcount : ∀ F : Finset α, F ⊆ E → ∀ R : ℝ, 0 < R →
      (∀ x ∈ F, q x ≤ R) → (F.card : ℝ) ≤ C * R ^ d) :
    ∑ x ∈ E, (1 + q x / H) ^ (-2 : ℝ) ≤ 4 * C * H ^ d := by
  have hex (x : α) : ∃ n : ℕ, (2:ℝ)^n ≤ 1 + q x / H ∧
      1 + q x / H < (2:ℝ)^(n+1) :=
    exists_nat_pow_near (by linarith [div_nonneg (hq x) hH.le]) (by norm_num)
  let bin (x : α) : ℕ := Classical.choose (hex x)
  have hlo (x : α) : (2:ℝ)^(bin x) ≤ 1 + q x / H := (Classical.choose_spec (hex x)).1
  have hhi (x : α) : 1 + q x / H < (2:ℝ)^(bin x+1) := (Classical.choose_spec (hex x)).2
  have hbin (n : ℕ) :
      ∑ x ∈ E.filter (fun x => bin x = n), (1 + q x / H) ^ (-2 : ℝ) ≤
        (2*C*H^d) * (1/2:ℝ)^n := by
    let F := E.filter (fun x => bin x = n)
    have hcard : (F.card:ℝ) ≤ C * ((2:ℝ)^(n+1)*H)^d := by
      apply hcount F (Finset.filter_subset _ _) _ (by positivity)
      intro x hx
      have he := (Finset.mem_filter.mp hx).2
      have hh := hhi x
      rw [he] at hh
      have hqdiv : q x/H ≤ (2:ℝ)^(n+1) := by linarith
      exact (div_le_iff₀ hH).mp hqdiv
    have hweight (x : α) (hx : x∈F) : (1+q x/H)^(-2:ℝ) ≤ (1/4:ℝ)^n := by
      have hl := hlo x
      rw [(Finset.mem_filter.mp hx).2] at hl
      apply (Real.rpow_le_rpow_of_nonpos (by positivity) hl (by norm_num)).trans_eq
      rw [Real.rpow_neg (by positivity), Real.rpow_two, ← pow_mul, Nat.mul_comm, pow_mul, ← inv_pow]
      norm_num
    have hp : ((2:ℝ)^(n+1))^d ≤ (2:ℝ)^(n+1) :=
      Real.rpow_le_self_of_one_le (one_le_pow₀ (by norm_num)) hd
    calc
      _ ≤ (F.card:ℝ)*(1/4:ℝ)^n := by
        apply (Finset.sum_le_sum hweight).trans_eq
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C*((2:ℝ)^(n+1)*H)^d)*(1/4:ℝ)^n :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (C*((2:ℝ)^(n+1)*H^d))*(1/4:ℝ)^n := by
        rw [Real.mul_rpow (by positivity) hH.le]
        gcongr
      _ = (2*C*H^d)*((2:ℝ)^n*(1/4:ℝ)^n) := by rw [pow_succ]; ring
      _ = _ := by rw [←mul_pow]; norm_num
  have hsum : (∑ x∈E,(1+q x/H)^(-2:ℝ)) =
      ∑ n∈E.image bin, ∑ x∈E.filter (fun x=>bin x=n), (1+q x/H)^(-2:ℝ) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) _
  rw [hsum]
  apply (Finset.sum_le_sum (fun n _=>hbin n)).trans
  have hs := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).mul_left (2*C*H^d)
  apply (Summable.sum_le_tsum _ (by intro n _; positivity) hs).trans_eq
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)]
  ring

theorem nonzero_frequency_count (E : Finset O) (R : ℝ) (hR : 0 < R)
    (hE : ∀ k∈E, k≠0) (hN : ∀ k∈E, frequencyNorm k≤R) :
    (E.card:ℝ) ≤ 128*R := by
  by_cases hr : 1≤R
  · apply DescentFiberCost.finite_element_count_real E R hr
    intro k hk
    simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,frequencyNorm]
      using hN k hk
  · have he : E=∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro k hk
      have hh := frequencyNorm_one_le k (hE k hk)
      have hb := hN k hk
      linarith)
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem frequency_weighted_sum :
    ∃ K : ℝ, 0<K ∧ ∀ (E : Finset O) (H : ℝ), 0<H →
      (∀ k∈E,k≠0) →
      ∑ k∈E,(1+frequencyNorm k/H)^(-2:ℝ) ≤ K*H := by
  refine ⟨512,by norm_num,?_⟩
  intro E H hH hE
  have hh := finite_weighted_of_count E frequencyNorm frequencyNorm_nonneg
    128 1 H (by norm_num) (by norm_num) hH (by
      intro F hFE R hR hN
      simpa only [Real.rpow_one] using
        nonzero_frequency_count F R hR (fun k hk=>hE k (hFE hk)) hN)
  norm_num only [Real.rpow_one,show (4:ℝ)*128=512 by norm_num] at hh
  exact hh

theorem exceptional_frequency_weighted_sum (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ, 0<K ∧ ∀ G : Ideal O, G≠0 → ∀ (E : Finset O) (H : ℝ), 0<H →
      (∀ k∈E,k≠0) →
      (∀ k∈E,∀ P∉IdealMobiusDivisorSum.primeSupport G,
        CenteredExceptionalCount.valuation (Ideal.span {k}) P % 6=0) →
      ∑ k∈E,(1+frequencyNorm k/H)^(-2:ℝ) ≤
        K*(Ideal.absNorm G:ℝ)^ε*H^(1/6:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := ProbePhysical.lowGramExceptional_count ε hε
  refine ⟨4*C,by positivity,?_⟩
  intro G hG E H hH hE hres
  have hh := finite_weighted_of_count E frequencyNorm frequencyNorm_nonneg
    (C*(Ideal.absNorm G:ℝ)^ε) (1/6) H (by positivity) (by norm_num) hH (by
      intro F hFE R hR hN
      exact hcount G hG F R hR.le (fun k hk=>hE k (hFE hk))
        (fun k hk=>hres k (hFE hk)) hN)
  convert hh using 1
  ring

end SevenEighths.ProbeGramFrequencySummation

end

end OAI

end Source1758

/- Original source: OAI/NumberTheory/DirichletL/Detector/GramFrequencyMass.lean; sha256: 9458192dc499582ef78016a73226122a4b3dba20d55d77ca0acf6d0e46d300d0 -/
section Source1759
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gramFrequency_image_sum (E : Finset GramFrequency) (f : O→ℝ) :
    (∑k∈E.image Subtype.val,f k)=∑k∈E,f k.val :=
  Finset.sum_image (fun _ _ _ _ h=>Subtype.val_injective h)

theorem canonical_nonexceptional_frequency_sum (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(E : Finset GramFrequency),
      (∀k∈E,¬ExceptionalFrequency S hS C k)→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v H N : ℝ),0<H→0<N→
        ‖∑k∈E,canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
          (Ideal.absNorm C.val:ℝ)*N^2*H*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A) := by
  obtain ⟨J,H₀,hblock⟩ := canonical_nonexceptional_weighted A hA a₀ b₀ ha₀ hab
  obtain ⟨L,hL,hcount⟩ := ProbeGramFrequencySummation.frequency_weighted_sum
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hblock⟩ := hblock W hs hW
  refine ⟨K*L,mul_pos hK hL,?_⟩
  intro S hS σ C E hE d U v H N hH hN
  have hc := hcount (E.image Subtype.val) H hH (by
    intro k hk;obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk;exact j.property)
  rw [gramFrequency_image_sum] at hc
  let V := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Ideal.absNorm C.val:ℝ)*N^2*
    min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A)
  have hV : 0≤V := by dsimp [V];positivity
  calc
    _≤∑k∈E,‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖ := norm_sum_le _ _
    _≤∑k∈E,V*(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) :=
      Finset.sum_le_sum (fun k hk=>hblock S hS σ C k (hE k hk) d U v H N hH hN)
    _=V*(∑k∈E,(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ)) := (Finset.mul_sum ..).symm
    _≤V*(L*H) := mul_le_mul_of_nonneg_left hc hV
    _=_ := by dsimp [V];ring

theorem canonical_exceptional_frequency_sum (a b M ε : ℝ) (ha : 0<a) (hb : 0≤b)
    (hM : 0≤M) (hε : 0<ε) :
    ∃H₀ : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀(W : ℝ→ℂ)(_hcompact : HasCompactSupport W),
      (Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤M)→
      ∀(U : SchwartzMap ℝ ℂ)(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(E : Finset GramFrequency),
      (∀k∈E,ExceptionalFrequency S hS C k)→
      ∀(d : O)(v H N : ℝ),0<H→0<N→
        ‖∑k∈E,canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Ideal.absNorm C.val:ℝ)*N^2*
          ((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val)^ε*H^(1/6:ℝ) := by
  obtain ⟨H₀,K,hK,hblock⟩ := canonical_trivial_block a b M ha hb hM 2
  obtain ⟨L,hL,hcount⟩ := ProbeGramFrequencySummation.exceptional_frequency_weighted_sum ε hε
  refine ⟨H₀,K*L,mul_pos hK hL,?_⟩
  intro W hcompact hs hW U S hS σ C E hE d v H N hH hN
  have hc := hcount (exceptionalModulus S hS C) (exceptionalModulus_nonzero S hS C)
    (E.image Subtype.val) H hH
    (by intro k hk;obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk;exact j.property)
    (by intro k hk;obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk;exact hE j hj)
  rw [gramFrequency_image_sum,exceptionalModulus_norm,Nat.cast_mul] at hc
  let V := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Ideal.absNorm C.val:ℝ)*N^2
  have hV : 0≤V := by dsimp [V];positivity
  have hp (k : GramFrequency) :
      ‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        V*(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := by
    have ht : 0≤(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H := by positivity
    have hb := hblock W hcompact hs hW U S hS σ C k d N _ v hN ht
    have hpos : 0<1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H := by positivity
    rw [Real.rpow_neg hpos.le,Real.rpow_two,←div_eq_mul_inv]
    apply (le_div_iff₀ (sq_pos_of_pos hpos)).mpr
    convert hb using 1 ; dsimp [V] ; ring
  calc
    _≤∑k∈E,‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖ := norm_sum_le _ _
    _≤∑k∈E,V*(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := Finset.sum_le_sum (fun k _=>hp k)
    _=V*(∑k∈E,(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ)) := (Finset.mul_sum ..).symm
    _≤V*(L*((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val)^ε*H^(1/6:ℝ)) := mul_le_mul_of_nonneg_left hc hV
    _=_ := by dsimp [V];ring

end SevenEighths.ProbeGramCommon
end

end OAI

end Source1759
