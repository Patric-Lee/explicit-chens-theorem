import OpenAIGrouped.Unit014
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit010
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Int.Interval
import OpenAIGrouped.Unit009
import OpenAIGrouped.Unit008

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondTail.lean; sha256: d29a4f81e9fddb368d90dcd2a9eaa114165c68d2365dfb6b60b2993dbf79a3b6 -/
section Source600
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSupportedCorrelation CenteredMomentSecondWholeKernel
local notation "O" => ActualEisensteinCubic.O

theorem actual_second_kernel_reference (I J : Ideal O) (hI : I≠0) (hJ : J≠0)
    (K X H Tsec : ℝ) (hK : 0<K) (hX : 0<X)
    (hi : (Ideal.absNorm I:ℝ)≤Real.exp H*X) (hj : (Ideal.absNorm J:ℝ)≤Real.exp H*X)
    (hsec : X^2/K≤Tsec) :
    kernelReference Tsec H≤K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hT : 0<Tsec := (div_pos (sq_pos_of_pos hX) hK).trans_le hsec
  have hNi := CenteredMomentFirstScale.norm_pos I hI
  have hNj := CenteredMomentFirstScale.norm_pos J hJ
  have hprod : (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)≤Real.exp (2*H)*X^2 := by
    apply (mul_le_mul hi hj hNj.le (by positivity)).trans_eq
    rw [show 2*H=H+H by ring,Real.exp_add]
    ring
  unfold kernelReference
  apply (le_div_iff₀ (mul_pos hNi hNj)).mpr
  calc
    _ ≤ (Real.exp (-2*H)/Tsec)*(Real.exp (2*H)*X^2) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = X^2/Tsec := by
      rw [show -2*H=-(2*H) by ring,Real.exp_neg]
      field_simp
    _ ≤ K := (div_le_iff₀ hT).mpr (by simpa only [mul_comm] using (div_le_iff₀ hK).mp hsec)

def secondDiscardedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
    ∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
      actualCorrelation (primaryGenerator I) (primaryGenerator J)
        ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) (-h)*
      paperRadialFourier W (K*‖eisEmbedding h‖^2/
        ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2)

theorem second_discarded_pair_bound (Adec : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
        (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp H*X → (Ideal.absNorm J:ℝ)≤Real.exp H*X →
      X^2/K≤Tsec → (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedPair I J hI hJ W K Tsec Z ξ‖≤
        K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_second_tail Adec
  refine ⟨s,C,hC,?_⟩
  intro W I J hI hJ K X H Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hT : 0<Tsec := (div_pos (sq_pos_of_pos hX) hK).trans_le hsec
  have hb := ht W Tsec Z Csec H ξ (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))
    hT hZ hCs hthreshold (actual_second_kernel_reference I J hI.1 hJ.1 K X H Tsec hK hX hi hj hsec)
    (primaryGenerator I) (primaryGenerator J)
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ)
  have he (h : O) : K*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2=
      (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*normValue h := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq I hI,primary_norm_sq J hJ,normValue_eq_embedding]
    ring
  have hu : normValue (primaryGenerator I)=(Ideal.absNorm I:ℝ) := by rw [normValue,primary_span_supported I hI]
  have hv : normValue (primaryGenerator J)=(Ideal.absNorm J:ℝ) := by rw [normValue,primary_span_supported J hJ]
  rw [hu,hv] at hb
  have hNi : (1:ℝ)≤Ideal.absNorm I := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hNj : (1:ℝ)≤Ideal.absNorm J := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ.1)
  have hroot : 1≤Real.sqrt (Ideal.absNorm I:ℝ)*Real.sqrt (Ideal.absNorm J:ℝ) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr hNi) (Real.one_le_sqrt.mpr hNj)
  have hnorm : ‖(K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))‖≤K := by
    rw [norm_div,norm_mul]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_self hK.le hroot
  unfold secondDiscardedPair
  simp_rw [he]
  rw [norm_mul]
  apply (mul_le_mul hnorm hb (norm_nonneg _) hK.le).trans
  have hprod := mul_le_mul hi hj (Nat.cast_nonneg _) (by positivity : 0≤Real.exp H*X)
  have hfac : 0≤(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
      ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by positivity
  have hb' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hfac) hK.le
  convert hb' using 1 <;> ring

end SevenEighths.CenteredMomentSecondTail

end

end OAI

end Source600

/- Original source: OAI/NumberTheory/DirichletL/Moments/SupportedTailAggregate.lean; sha256: 1902e96cff77a3de9b257b2cc7a93477a173ed540de2c5fc2be6061e839c6da2 -/
section Source601
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedTailAggregate
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondTail CenteredMomentFirstTailAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstScale CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
local notation "O" => ActualEisensteinCubic.O

private theorem pair_mass {α : Type*} [Fintype α] (c w : α → ℂ) (F : α → α → ℂ)
    (hw : ∀ i,‖w i‖≤1) (B : ℝ) (_hB : 0≤B)
    (hF : ∀ i j,c i≠0 → c j≠0 → ‖F i j‖≤B) :
    ‖∑ i,∑ j,((c i*w i)*star (c j*w j))*F i j‖≤(∑ i,‖c i‖)^2*B := by
  have ht (i j : α) : ‖((c i*w i)*star (c j*w j))*F i j‖≤‖c i‖*‖c j‖*B := by
    by_cases hi : c i=0
    · simp [hi]
    by_cases hj : c j=0
    · simp [hj]
    rw [norm_mul,norm_mul,norm_star]
    apply mul_le_mul _ (hF i j hi hj) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    apply mul_le_mul _ _ (norm_nonneg _) (norm_nonneg _)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw i)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw j)
  calc
    _ ≤ ∑ i,‖∑ j,((c i*w i)*star (c j*w j))*F i j‖ := norm_sum_le _ _
    _ ≤ ∑ i,∑ j,‖c i‖*‖c j‖*B := Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ht i j)))
    _ = _ := by rw [pow_two,Finset.sum_mul,Finset.sum_mul];apply Finset.sum_congr rfl;intro i hi;rw [Finset.mul_sum,Finset.sum_mul]

def secondDiscardedEnergy (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*heightCoeff η t I)*star (c J*heightCoeff η t J))*
      secondDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

theorem second_discarded_energy_bound (Adec : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (η : Character) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
        (W : 𝓢(ℝ,ℂ)) (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (∀ I∈S,c I≠0 → (Ideal.absNorm I:ℝ)≤Real.exp H*X) →
      X^2/K≤Tsec → (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedEnergy η t S c W K Tsec Z ξ‖≤
        (∑ I∈S,‖c I‖)^2*K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := second_discarded_pair_bound Adec
  refine ⟨s,C,hC,?_⟩
  intro η t S c W K X H Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤B := by dsimp only [B];positivity
  have hweight (I : supportedColumns S) : ‖heightCoeff η t I‖≤1 := by
    rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp I.property).2]
    exact rowWeight_norm_le_one η fixedBadMask 1 1 t I (Finset.mem_filter.mp I.property).2.1
  have hp := pair_mass (fun I : supportedColumns S => c I) (fun I => heightCoeff η t I)
    (fun I J => secondDiscardedPair I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ) hweight B hB
    (fun I J hi hj => ht W I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 K X H Tsec Z Csec ξ hK hX hZ hCs
      (hN I (Finset.mem_filter.mp I.property).1 hi) (hN J (Finset.mem_filter.mp J.property).1 hj) hsec hthreshold)
  have hm : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  apply hp.trans
  convert mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (show 0 ≤ ∑ I : supportedColumns S, ‖c I‖ from
      Finset.sum_nonneg (fun I _ => norm_nonneg (c I))) hm 2) hB using 1 ; dsimp only [B];ring

theorem first_discarded_energy_bound (Adec : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
        (W : 𝓢(ℝ,ℂ)) (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (∀ I∈S,c I≠0 → (Ideal.absNorm I:ℝ)≤Real.exp H*X) →
      (∀ I : supportedColumns S,∀ J : supportedColumns S,c I≠0 → c J≠0 →
        ∀ E∈inactiveSubsets I J,firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec) →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖discardedEnergy η m A t S c W K Tsec Z ξ‖≤
        (∑ I∈S,‖c I‖)^2*(Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_pair_bound Adec ε hε
  refine ⟨s,C,hC,?_⟩
  intro η m A t S c W K X H Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := (Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤B := by dsimp only [B];positivity
  have hpair (I J : supportedColumns S) (hi : c I≠0) (hj : c J≠0) :
      ‖canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ‖≤B := by
    have hni := hN I (Finset.mem_filter.mp I.property).1 hi
    have hnj := hN J (Finset.mem_filter.mp J.property).1 hj
    apply (ht W I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2
      K X H Tsec Z Csec ξ hK hX hZ hCs hni hnj (hsec I J hi hj) hthreshold).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hni hε.le) hK.le
  have hp := pair_mass (fun I : supportedColumns S => c I)
    (fun I => CenteredMomentHeckeExpansion.rowWeight η m A 1 t I)
    (fun I J => canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ)
    (fun I => rowWeight_norm_le_one η m A 1 t I (Finset.mem_filter.mp I.property).2.1) B hB hpair
  have hm : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  apply hp.trans
  convert mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (show 0 ≤ ∑ I : supportedColumns S, ‖c I‖ from
      Finset.sum_nonneg (fun I _ => norm_nonneg (c I))) hm 2) hB using 1 ; dsimp only [B];ring

end SevenEighths.CenteredMomentSupportedTailAggregate

end

end OAI

end Source601

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstLocalization.lean; sha256: f862d62de682ef44c3731b043ebc330b16c2d935ed5836e6187258887ae51761 -/
section Source602
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstLocalization
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentFirstTailAggregate
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentFirstEnergy
local notation "O" => ActualEisensteinCubic.O

theorem weighted_fourier_summable (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0<k)
    (c w : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤B) (hw : ∀ h,‖w h‖≤1) :
    Summable (fun h : O => w h*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := paperRadialFourier_lattice_summable_norm W k hk
  simp_rw [← normValue_eq_embedding] at hs
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs.mul_left B)
  intro h
  rw [norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_left (norm_nonneg _) (hw h)).trans (hc h)) (norm_nonneg _)

theorem retained_complex_norm (R q : ℝ) : ‖(retainedWeight R q:ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (retainedWeight_nonneg R q)]
  exact (retainedWeight_bounds R q).2

theorem discarded_complex_norm (R q : ℝ) : ‖(discardedWeight R q:ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (discardedWeight_nonneg R q)]
  exact (discardedWeight_bounds R q).2

theorem lattice_fourier_split (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0<k)
    (c : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤B) (R : ℝ) :
    (∑' h : O,c h*paperRadialFourier W (k*normValue h))=
      c 0*paperRadialFourier W 0+
        (∑' h : O,(retainedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h))+
        (∑' h : O,(discardedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := weighted_fourier_summable W k hk c (fun _ => 1) B hc (by simp)
  simp only [one_mul] at hs
  have hr := weighted_fourier_summable W k hk c (fun h => (retainedWeight R (normValue h):ℂ)) B hc
    (fun h => retained_complex_norm R _)
  have hd := weighted_fourier_summable W k hk c (fun h => (discardedWeight R (normValue h):ℂ)) B hc
    (fun h => discarded_complex_norm R _)
  rw [hs.tsum_eq_add_tsum_ite 0]
  have hzero : normValue (0:O)=0 := by simp [normValue]
  simp only [hzero,mul_zero]
  rw [add_assoc,← hr.tsum_add hd]
  congr 1
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · subst h
    simp only [ite_true,hzero,
      retainedWeight_zero_nonpos R 0 le_rfl,discardedWeight_zero_nonpos R 0 le_rfl,
      Complex.ofReal_zero,zero_mul,add_zero]
  · rw [ite_eq_right hh]
    have hp : 0<normValue h := norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr hh)
    have he : (retainedWeight R (normValue h):ℂ)+(discardedWeight R (normValue h):ℂ)=1 := by
      exact_mod_cast retained_add_discarded R (normValue h) hp
    rw [← add_mul,← add_mul,he,one_mul]

def canonicalRetainedTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
      (retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

def canonicalZeroTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*
      (tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
        (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) 0*paperRadialFourier W 0))

def canonicalRetainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalRetainedTerm I J hI hJ E W K Tsec Z ξ

def canonicalZeroPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalZeroTerm I J hI hJ E W K

theorem reducedFirstSum_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    reducedFirstSum I J hI hJ W K=canonicalZeroPair I J hI hJ W K+
      canonicalRetainedPair I J hI hJ W K Tsec Z ξ+canonicalDiscardedPair I J hI hJ W K Tsec Z ξ := by
  unfold reducedFirstSum canonicalZeroPair canonicalRetainedPair canonicalDiscardedPair
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only [canonicalZeroTerm,canonicalRetainedTerm,canonicalDiscardedTerm]
  simp_rw [← normValue_eq_embedding]
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  have ha : a≠0 := supported_element_ne_zero _ (residualGenerator_supported I J hI)
  have hb : b≠0 := supported_element_ne_zero _ (residualGenerator_supported J I hJ)
  have hr : r≠0 := finitePrimeModulus_ne_zero _
  have he : primeSubsetGenerator (fun P : CommonIndex I J => P.val) E≠0 := primeSubsetGenerator_ne_zero _ _
  have hk : 0<(K/normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/normValue (a*(b*r)) :=
    div_pos (div_pos hK (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)))
      (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr))))
  have hh := lattice_fourier_split W _ hk
    (tripleFourier a b r ha hb hr (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (normValue (a*(b*r)))
    (tripleFourier_norm_le_full a b r ha hb hr _ _ _ (activeFunction_norm_le_one I J hI))
    (frequencyRadius Tsec Z ξ)
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let k := (K/normValue e)/normValue (a*(b*r))
  let F := tripleFourier a b r ha hb hr (residualCharacter I J hI)
    (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
  let d := (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e
  change d*((k:ℂ)*∑' h : O,F h*paperRadialFourier W ((K/normValue e)*normValue h/normValue (a*(b*r))))=
    d*((k:ℂ)*(F 0*paperRadialFourier W 0))+
      d*((k:ℂ)*∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))+
      d*((k:ℂ)*∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))
  have heq (h : O) : (K/normValue e)*normValue h/normValue (a*(b*r))=k*normValue h := by dsimp [k];ring
  simp_rw [heq]
  rw [hh]
  ring

def retainedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalRetainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

def zeroEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalZeroPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K

theorem finiteHeckeEnergy_localized (η : Character) (m A : O) (t : ℝ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K=
      zeroEnergy η m A t S c W K+retainedEnergy η m A t S c W K Tsec Z ξ+
        discardedEnergy η m A t S c W K Tsec Z ξ := by
  rw [finiteHeckeEnergy_reduced_poisson η m A t hmLam hm2 S c W K hK]
  simp_rw [reducedFirstSum_split _ _ _ _ W K Tsec Z ξ hK,mul_add,Finset.sum_add_distrib]
  rfl

end SevenEighths.CenteredMomentFirstLocalization

end

end OAI

end Source602

/- Original source: OAI/NumberTheory/DirichletL/Moments/ZeroMeanBridge.lean; sha256: 0579fb487276d19516af254446717a9278adb35d831b8510be24cc535208e85f -/
section Source603
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentZeroMeanBridge
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentCommonSupport
open CenteredMomentFourier CenteredMomentCorrelation CenteredMomentSupportedCorrelation
open CenteredMomentSectorLocalization CenteredMomentFirstReduced CenteredMomentCanonicalFirst
open CenteredMomentActive CenteredMomentFirstDiscardedEnergy CenteredMomentFirstLocalization
local notation "O" => ActualEisensteinCubic.O

def quotientMean (a : O) (F : Residue a → ℂ) : ℂ :=
  (normValue a : ℂ)⁻¹ * ∑' x : Residue a, F x

lemma normValue_ne_zero (a : O) (ha : a ≠ 0) : normValue a ≠ 0 :=
  by
    rw [normValue_eq_embedding]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

theorem quotientMean_pullback (a m : O) (ha : a ≠ 0) (hm : m ≠ 0)
    (h : a ∣ m) (F : Residue a → ℂ) :
    quotientMean m (fun x => F (frequencyReduction a m h x)) = quotientMean a F := by
  obtain ⟨b, rfl⟩ := h
  have hb : b ≠ 0 := right_ne_zero_of_mul hm
  have hh := conductorFourier_lift a b ha hb F 0
  simp only [mul_zero, conductorFourier, map_zero, zero_mul, AddChar.map_zero_eq_one,
    mul_one] at hh
  have he : frequencyReduction a (a*b) (dvd_mul_right a b) = conductorReduction a b := rfl
  unfold quotientMean
  rw [he, hh, normValue_mul, Complex.ofReal_mul]
  have ha' : (normValue a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (normValue_ne_zero a ha)
  have hb' : (normValue b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (normValue_ne_zero b hb)
  change ((normValue a : ℂ) * (normValue b : ℂ))⁻¹ *
    ((normValue b : ℂ) * _) = _
  field_simp

def dilationMask (e d : O) (F : Residue d → ℂ) (x : Residue (d*e)) : ℂ :=
  if frequencyReduction e (d*e) (dvd_mul_left e d) x = 0 then
    F (frequencyReduction d (d*e) (dvd_mul_right d e) x) else 0

@[simp] theorem dilationMask_mk (e d : O) (F : Residue d → ℂ) (z : O) :
    dilationMask e d F (Ideal.Quotient.mk _ z) =
      if e ∣ z then F (Ideal.Quotient.mk _ z) else 0 := by
  simp only [dilationMask, frequencyReduction_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

theorem dilationMask_sum (e d : O) (he : e ≠ 0) (F : Residue d → ℂ) :
    (∑' x : Residue (d*e), dilationMask e d F x) =
      ∑' y : Residue d, F (Ideal.Quotient.mk _ e * y) := by
  have hi := scaledResidue_injective d e (d*e) rfl he
  have hz (x : Residue (d*e)) (hx : x ∉ Set.range (scaledResidue d e (d*e) rfl)) :
      dilationMask e d F x = 0 := by
    obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [dilationMask_mk]
    split_ifs with h
    · obtain ⟨y,rfl⟩ := h
      exact False.elim (hx ⟨Ideal.Quotient.mk _ y, rfl⟩)
    · rfl
  have hs : Function.support (dilationMask e d F) ⊆ Set.range (scaledResidue d e (d*e) rfl) := by
    intro x hx
    by_contra hn
    exact hx (hz x hn)
  rw [← hi.tsum_eq hs]
  apply tsum_congr
  intro y
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, dilationMask_mk, ite_eq_left (dvd_mul_right e z), map_mul]

theorem quotientMean_dilation (e d : O) (he : e ≠ 0) (_hd : d ≠ 0)
    (F : Residue d → ℂ) (hF : ∀ x y, F (x*y) = F x * F y) :
    quotientMean (d*e) (dilationMask e d F) =
      (normValue e : ℂ)⁻¹ * F (Ideal.Quotient.mk _ e) * quotientMean d F := by
  rw [quotientMean, dilationMask_sum e d he]
  simp_rw [hF]
  rw [tsum_mul_left, normValue_mul, Complex.ofReal_mul, quotientMean]
  ring

theorem quotientMean_finite_sum {ι : Type*} [Fintype ι]
    (a : O) (ha : a ≠ 0) (F : Residue a → ℂ)
    (d : ι → O) (hd : ∀ i, d i ≠ 0) (G : (i : ι) → Residue (d i) → ℂ)
    (c : ι → ℂ)
    (h : ∀ z : O, F (Ideal.Quotient.mk _ z) =
      ∑ i, c i * G i (Ideal.Quotient.mk _ z)) :
    quotientMean a F = ∑ i, c i * quotientMean (d i) (G i) := by
  let m := a * ∏ i, d i
  have hm : m ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i))
  have haM : a ∣ m := dvd_mul_right _ _
  have hdM (i : ι) : d i ∣ m := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) a
  let := finite_quotient_span hm
  let : Fintype (Residue m) := Fintype.ofFinite _
  rw [← quotientMean_pullback a m ha hm haM F]
  have hh (x : Residue m) : F (frequencyReduction a m haM x) =
      ∑ i, c i * G i (frequencyReduction (d i) m (hdM i) x) := by
    obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [frequencyReduction_mk] using h z
  simp_rw [quotientMean, hh, tsum_fintype]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hl := quotientMean_pullback (d i) m (hd i) hm (hdM i) (G i)
  rw [quotientMean, tsum_fintype] at hl
  rw [← Finset.mul_sum, mul_left_comm, hl]
  rfl

theorem row_mask_expansion {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (z : O) (v : ℂ) :
    rowCoprimeMask P S z * v =
      ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
        (if primeSubsetGenerator P E ∣ z then v else 0) := by
  rw [rowCoprimeMask_subsets, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro E hE
  have hp (i : ι) : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  rw [prime_product_moebius P hp hinj E]
  have he : primeSubsetGenerator P E ∣ z ↔ ∀ i ∈ E, z ∈ P i := by
    rw [← Ideal.mem_span_singleton, primeSubsetGenerator, span_idealGenerator,
      mem_prime_product_iff P hinj E z]
  rw [he]
  split_ifs <;> ring

theorem quotientMean_mask_expansion {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (a d : O) (ha : a ≠ 0) (hd : d ≠ 0)
    (F : Residue a → ℂ) (G : Residue d → ℂ)
    (hG : ∀ x y, G (x*y) = G x * G y)
    (hFG : ∀ z : O, F (Ideal.Quotient.mk _ z) =
      rowCoprimeMask P S z * G (Ideal.Quotient.mk _ z)) :
    quotientMean a F =
      ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
        (normValue (primeSubsetGenerator P E) : ℂ)⁻¹ *
          G (Ideal.Quotient.mk _ (primeSubsetGenerator P E)) * quotientMean d G := by
  have h := quotientMean_finite_sum a ha F
    (fun E : S.powerset => d * primeSubsetGenerator P E.val)
    (fun E => mul_ne_zero hd (primeSubsetGenerator_ne_zero P E.val))
    (fun E => dilationMask (primeSubsetGenerator P E.val) d G)
    (fun E => (UniqueFactorizationMonoid.moebius (∏ i∈E.val,P i) : ℂ)) (by
      intro z
      rw [hFG, row_mask_expansion P hinj S z]
      simp only [dilationMask_mk]
      exact (Finset.sum_coe_sort S.powerset _).symm)
  simp_rw [quotientMean_dilation _ _ (primeSubsetGenerator_ne_zero P _) hd G hG] at h
  simp only [← mul_assoc] at h
  exact h.trans (Finset.sum_coe_sort S.powerset (fun E : Finset ι =>
    (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
      (normValue (primeSubsetGenerator P E) : ℂ)⁻¹ *
        G (Ideal.Quotient.mk _ (primeSubsetGenerator P E)) * quotientMean d G))

theorem tripleResidue_mul (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ)
    (hG : ∀ x y, G (x*y) = G x * G y) (x y : Residue (a*(b*r))) :
    tripleResidue a b r χa χb G (x*y) =
      tripleResidue a b r χa χb G x * tripleResidue a b r χa χb G y := by
  obtain ⟨u,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨v,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, tripleResidue_mk, tripleResidue_mk, tripleResidue_mk]
  exact tripleRow_mul a b r χa χb G hG u v

theorem original_pair_reduced_mask (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (z : O) :
    idealRowHom z I * star (idealRowHom z J) =
      rowCoprimeMask (fun P : CommonIndex I J => P.val)
        (principalSupport Finset.univ (leftExponent I J) (rightExponent I J)) z *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) z := by
  rw [original_pair_factor I J hI hJ]
  rw [common_ideal_pair_active (fun P : CommonIndex I J => P.val) (common_good I J hI)
    (common_odd I J hI) Finset.univ (leftExponent I J) (rightExponent I J)
    (fun P _ => (leftExponent_pos I J P).ne') (fun P _ => (rightExponent_pos I J P).ne')]
  have hactive : activeFunction I J hI (Ideal.Quotient.mk _ z) =
      finiteSexticRow (activePrime I J) (activeGood I J hI)
        (CenteredMomentCanonicalFirst.activeExponent I J) z :=
    principalSexticRow_mk (activePrime I J) (activeCoprime I J) (activeGood I J hI)
      (CenteredMomentCanonicalFirst.activeExponent I J) (activeConductor I J)
      (span_finitePrimeModulus _) z
  simp only [tripleRow, hactive]
  convert mul_left_comm
    ((residualCharacter I J hI) (Ideal.Quotient.mk _ z) *
      (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ z))
    (rowCoprimeMask (fun P : CommonIndex I J => P.val)
      (principalSupport Finset.univ (leftExponent I J) (rightExponent I J)) z)
    (finiteSexticRow (activePrime I J) (activeGood I J hI)
      (CenteredMomentCanonicalFirst.activeExponent I J) z) using 1
  congr 2

theorem original_pair_mean (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    let hi : Supported (Ideal.span {CompletedGauss.primaryGenerator I}) :=
      (CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI
    let hj : Supported (Ideal.span {CompletedGauss.primaryGenerator J}) :=
      (CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ
    quotientMean (CompletedGauss.primaryGenerator I * CompletedGauss.primaryGenerator J)
      (CenteredMomentRowNorm.pairResidue _ _ hi hj) =
    ∑ E ∈ inactiveSubsets I J,
      (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val) : ℂ) *
        (normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) : ℂ)⁻¹ *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
        (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) *
      quotientMean (residualGenerator I J * (residualGenerator J I * activeConductor I J))
        (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)) := by
  dsimp only
  have h := quotientMean_mask_expansion (fun P : CommonIndex I J => P.val) Subtype.val_injective
    (principalSupport Finset.univ (leftExponent I J) (rightExponent I J))
    (CompletedGauss.primaryGenerator I * CompletedGauss.primaryGenerator J)
    (residualGenerator I J * (residualGenerator J I * activeConductor I J))
    (mul_ne_zero (supported_primaryGenerator_ne_zero I hI) (supported_primaryGenerator_ne_zero J hJ))
    (mul_ne_zero (supported_element_ne_zero _ (residualGenerator_supported I J hI))
      (mul_ne_zero (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
        (finitePrimeModulus_ne_zero _)))
    (CenteredMomentRowNorm.pairResidue _ _
      ((CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI)
      ((CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ))
    (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
      (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (tripleResidue_mul _ _ _ _ _ _ (principalSexticRow_mul _ _ _ _ _ _)) (by
      intro z
      rw [CenteredMomentRowNorm.pairResidue_mk, CenteredMomentSourceRow.primary_span_supported I hI,
        CenteredMomentSourceRow.primary_span_supported J hJ, tripleResidue_mk]
      exact original_pair_reduced_mask I J hI hJ z)
  simpa only [inactiveSubsets, tripleResidue_mk] using h

theorem canonicalZeroTerm_eq_mean (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalZeroTerm I J hI hJ E W K = (K : ℂ) *
      ((UniqueFactorizationMonoid.moebius (∏ P∈E,P.val) : ℂ) *
        (normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) : ℂ)⁻¹ *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
        (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) *
      quotientMean (residualGenerator I J * (residualGenerator J I * activeConductor I J))
        (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))) *
      paperRadialFourier W 0 := by
  simp only [canonicalZeroTerm, tripleFourier, map_zero, zero_mul,
    AddChar.map_zero_eq_one, mul_one, quotientMean, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem canonicalZeroPair_eq_original (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let hi : Supported (Ideal.span {CompletedGauss.primaryGenerator I}) :=
      (CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI
    let hj : Supported (Ideal.span {CompletedGauss.primaryGenerator J}) :=
      (CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ
    canonicalZeroPair I J hI hJ W K =
      (((K / ‖eisEmbedding (CompletedGauss.primaryGenerator I * CompletedGauss.primaryGenerator J)‖^2 : ℝ) : ℂ) *
        CenteredMomentRowNorm.pairFourier (CompletedGauss.primaryGenerator I) (CompletedGauss.primaryGenerator J)
          hi hj 0) * paperRadialFourier W 0 := by
  dsimp only
  rw [canonicalZeroPair]
  simp_rw [canonicalZeroTerm_eq_mean]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← original_pair_mean I J hI hJ]
  rw [CenteredMomentZeroMode.pairFourier_zero, quotientMean, ← normValue_eq_embedding,
    Complex.ofReal_div, div_eq_mul_inv]
  ring

theorem quotientMean_congr (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (F : Residue a → ℂ) (G : Residue b → ℂ)
    (h : ∀ z : O, F (Ideal.Quotient.mk _ z) = G (Ideal.Quotient.mk _ z)) :
    quotientMean a F = quotientMean b G := by
  have hh := quotientMean_finite_sum a ha F (fun _ : Unit => b) (fun _ => hb)
    (fun _ => G) (fun _ => (1 : ℂ)) (by intro z; simpa using h z)
  simpa using hh

theorem scaled_pairFourier_eq_mean (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) (K : ℝ) :
    (((K / ‖eisEmbedding (a*b)‖^2 : ℝ) : ℂ) * CenteredMomentRowNorm.pairFourier a b ha hb 0) =
      (K : ℂ) * quotientMean (a*b) (CenteredMomentRowNorm.pairResidue a b ha hb) := by
  rw [CenteredMomentZeroMode.pairFourier_zero, quotientMean, ← normValue_eq_embedding,
    Complex.ofReal_div, div_eq_mul_inv]
  ring

theorem canonicalZeroPair_eq_generators (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (haI : Ideal.span {a} = I) (hbJ : Ideal.span {b} = J) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalZeroPair I J hI hJ W K =
      (((K / ‖eisEmbedding (a*b)‖^2 : ℝ) : ℂ) * CenteredMomentRowNorm.pairFourier a b ha hb 0) *
        paperRadialFourier W 0 := by
  rw [canonicalZeroPair_eq_original, scaled_pairFourier_eq_mean, scaled_pairFourier_eq_mean]
  congr 2
  apply quotientMean_congr
    _ _ (mul_ne_zero (supported_primaryGenerator_ne_zero I hI) (supported_primaryGenerator_ne_zero J hJ))
    (mul_ne_zero (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))
  intro z
  simp only [CenteredMomentRowNorm.pairResidue_mk, CenteredMomentSourceRow.primary_span_supported I hI,
    CenteredMomentSourceRow.primary_span_supported J hJ, haI, hbJ]

theorem canonical_ideal_zero_sum (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
      canonicalZeroPair I.val J.val (hS I.val I.property) (hS J.val J.property) W K) =
      CenteredMomentZeroMode.idealZeroEnergy S hS c K * paperRadialFourier W 0 := by
  rw [CenteredMomentZeroMode.idealZeroEnergy]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [canonicalZeroPair_eq_generators I.val J.val (hS I.val I.property) (hS J.val J.property)
    (CenteredMomentZeroMode.idealColumn S I) (CenteredMomentZeroMode.idealColumn S J)
    (CenteredMomentZeroMode.idealColumn_supported S hS I) (CenteredMomentZeroMode.idealColumn_supported S hS J)
    (CenteredMomentZeroMode.idealColumn_span S I) (CenteredMomentZeroMode.idealColumn_span S J)]
  ring

theorem zeroEnergy_eq_original (η : HeckeFamily.Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K =
      CenteredMomentZeroMode.idealZeroEnergy (CenteredMomentSourceRow.supportedColumns S)
        (fun _ h => (Finset.mem_filter.mp h).2)
        (fun I => c I * CenteredMomentHeckeExpansion.rowWeight η m A 1 t I) K * paperRadialFourier W 0 := by
  unfold zeroEnergy
  exact canonical_ideal_zero_sum (CenteredMomentSourceRow.supportedColumns S)
    (fun _ h => (Finset.mem_filter.mp h).2)
    (fun I => c I * CenteredMomentHeckeExpansion.rowWeight η m A 1 t I) W K

theorem productColumnCoefficient_mul_whole (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (w : Ideal O → ℂ) (I : Ideal O) :
    productColumnCoefficient S T (fun J L => β J L * w (J*L)) I =
      productColumnCoefficient S T β I * w I := by
  rw [productColumnCoefficient, productColumnCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem zeroEnergy_product_eq (η : HeckeFamily.Character) (m A : O) (t : ℝ)
    (S T : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
    (β : Ideal O → Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1*p.2))
      (productColumnCoefficient S T β) W K =
    CenteredMomentZeroMode.productZeroEnergy S T hS hT
      (fun I J => β I J * CenteredMomentHeckeExpansion.rowWeight η m A 1 t (I*J)) K *
      paperRadialFourier W 0 := by
  let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1*p.2)
  have hp := CenteredMomentZeroMode.productColumns_supported S T hS hT
  have hs : CenteredMomentSourceRow.supportedColumns P = P := Finset.filter_eq_self.mpr hp
  have hh := zeroEnergy_eq_original η m A t P (productColumnCoefficient S T β) W K
  simp only [hs] at hh
  rw [hh]
  congr 1
  unfold CenteredMomentZeroMode.productZeroEnergy
  congr 1
  funext I
  exact (productColumnCoefficient_mul_whole S T β
    (CenteredMomentHeckeExpansion.rowWeight η m A 1 t) I).symm

theorem normalized_zeroEnergy_product_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : HeckeFamily.Character) (m A : O) (t : ℝ)
      (S T : Finset (Ideal O)) (_hS : ∀ I ∈ S, Supported I) (_hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I*J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) *
        zeroEnergy η m A t ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1*p.2))
          (productColumnCoefficient S T β) W K‖ ≤
        C * K * B^2 * ‖paperRadialFourier W 0‖ * X^ε := by
  obtain ⟨C,hC,hc⟩ := CenteredMomentZeroMode.normalized_product_zero_mode_bound ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S T hS hT β W X K B hX hK hB hN hβ
  rw [zeroEnergy_product_eq η m A t S T hS hT]
  apply hc S T hS hT _ W X K B hX hK hB hN
  intro I hi J hj
  rw [norm_mul]
  exact (mul_le_mul (hβ I hi J hj)
    (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A 1 t (I*J)
      (mul_ne_zero (hS I hi).1 (hT J hj).1)) (norm_nonneg _) hB).trans_eq (mul_one B)

end SevenEighths.CenteredMomentZeroMeanBridge

end

end OAI

end Source603

/- Original source: OAI/NumberTheory/DirichletL/Moments/SupportedZeroEnergy.lean; sha256: d22595b37d351401a1ad1e2223afa93f7cc9eb85edd512978c49c73a392be874 -/
section Source604
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedZeroEnergy
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentZeroMode
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentFirstLocalization
open CenteredMomentZeroMeanBridge EisensteinSchwartzPoisson HeckeFamily
local notation "O" => ActualEisensteinCubic.O

theorem idealZeroEnergy_filter (S : Finset (Ideal O)) (hS : ∀ I∈S,Supported I)
    (c : Ideal O → ℂ) (K : ℝ) (p : Ideal O → Prop) [DecidablePred p]
    (hc : ∀ I∈S, ¬p I → c I=0) :
    idealZeroEnergy S hS c K =
      idealZeroEnergy (S.filter p) (fun I h => hS I (Finset.mem_filter.mp h).1) c K := by
  let e : S.filter p → S := fun I => ⟨I.val,(Finset.mem_filter.mp I.property).1⟩
  let ep : (S.filter p) × (S.filter p) → S × S := fun q => (e q.1,e q.2)
  have he : Function.Injective e := by
    intro I J h
    apply Subtype.ext
    exact congrArg (fun x : S => x.val) h
  have hep : Function.Injective ep := by
    intro q r h
    exact Prod.ext (he (congrArg Prod.fst h)) (he (congrArg Prod.snd h))
  let f : S × S → ℂ := fun q => (c q.1.val * star (c q.2.val)) *
    (((K / ‖eisEmbedding (idealColumn S q.1 * idealColumn S q.2)‖^2 : ℝ) : ℂ) *
      CenteredMomentRowNorm.pairFourier (idealColumn S q.1) (idealColumn S q.2)
        (idealColumn_supported S hS q.1) (idealColumn_supported S hS q.2) 0)
  have hs : Function.support f ⊆ Set.range ep := by
    intro q hq
    have hi : p q.1.val := by
      by_contra hn
      exact hq (by simp only [f,hc q.1.val q.1.property hn,zero_mul])
    have hj : p q.2.val := by
      by_contra hn
      exact hq (by simp only [f,hc q.2.val q.2.property hn,star_zero,mul_zero,zero_mul])
    exact ⟨(⟨q.1.val,Finset.mem_filter.mpr ⟨q.1.property,hi⟩⟩,
      ⟨q.2.val,Finset.mem_filter.mpr ⟨q.2.property,hj⟩⟩),rfl⟩
  have ht := hep.tsum_eq hs
  simpa only [tsum_fintype,Fintype.sum_prod_type,f,ep,e,idealZeroEnergy,idealColumn] using ht.symm

def activeColumns (S : Finset (Ideal O)) (c : Ideal O → ℂ) : Finset (Ideal O) :=
  (supportedColumns S).filter (fun I => c I≠0)

lemma activeColumns_supported (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (I : Ideal O) (hI : I∈activeColumns S c) : Supported I :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2

theorem zeroEnergy_eq_active_original (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K =
      idealZeroEnergy (activeColumns S c) (activeColumns_supported S c)
        (fun I => c I*rowWeight η m A 1 t I) K * paperRadialFourier W 0 := by
  rw [zeroEnergy_eq_original]
  congr 1
  exact idealZeroEnergy_filter (supportedColumns S) (fun I h => (Finset.mem_filter.mp h).2)
    (fun I => c I*rowWeight η m A 1 t I) K (fun I => c I≠0)
    (fun I _ h => by simp only [not_not] at h; rw [h,zero_mul])

theorem zeroEnergy_eq_active (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K = zeroEnergy η m A t (activeColumns S c) c W K := by
  rw [zeroEnergy_eq_active_original,zeroEnergy_eq_original]
  have he : supportedColumns (activeColumns S c)=activeColumns S c :=
    Finset.filter_eq_self.mpr (activeColumns_supported S c)
  simp only [he]

theorem finiteColumnCoefficient_witness {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (I : Ideal O)
    (hI : finiteColumnCoefficient S β I≠0) :
    ∃ v∈S, β v≠0 ∧ finiteTupleProduct v=I := by
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hI
  exact ⟨v,(Finset.mem_filter.mp hv).1,hne,(Finset.mem_filter.mp hv).2⟩

theorem finite_tuple_fiber_card {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (I : Ideal O) (hI : I≠0) :
    (S.filter (fun v => finiteTupleProduct v=I)).card ≤
      (idealDivisors I).card^(Fintype.card ι+2) := by
  let T := S.filter (fun v => finiteTupleProduct v=I)
  let f (v : T) : (ι ⊕ Fin 2) → idealDivisors I := fun i => ⟨v.val i,by
    apply (mem_idealDivisors hI).mpr
    rw [← (Finset.mem_filter.mp v.property).2]
    exact Finset.dvd_prod_of_mem v.val (Finset.mem_univ i)⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_sum,Fintype.card_fin,T]
    using Fintype.card_le_of_injective f hf

theorem finiteColumnCoefficient_norm_le {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (B : ℝ) (hB : 0≤B)
    (hβ : ∀ v∈S, finiteTupleProduct v≠0 → ‖β v‖≤B) (I : Ideal O) (hI : I≠0) :
    ‖finiteColumnCoefficient S β I‖ ≤ B*((idealDivisors I).card:ℝ)^(Fintype.card ι+2) := by
  calc
    _ ≤ ∑ v∈S.filter (fun v => finiteTupleProduct v=I),‖β v‖ := norm_sum_le _ _
    _ ≤ ∑ _v∈S.filter (fun v => finiteTupleProduct v=I),B := by
      apply Finset.sum_le_sum
      intro v hv
      exact hβ v (Finset.mem_filter.mp hv).1 ((Finset.mem_filter.mp hv).2 ▸ hI)
    _ = B*((S.filter (fun v => finiteTupleProduct v=I)).card:ℝ) := by simp; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast finite_tuple_fiber_card S I hI

theorem active_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤X → 0≤K → 0≤B →
      (∀ v∈S,finiteTupleProduct v≠0 → ‖β v‖≤B) →
      (∀ I∈supportedColumns (finiteColumns S),finiteColumnCoefficient S β I≠0 →
        (Ideal.absNorm I:ℝ)≤X) →
      ‖zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^(1+ε) := by
  let δ := ε/(4*(N+2:ℕ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hn : (N+2:ℝ)≠0 := by positivity
  have hδn : δ*(N+2:ℕ)=ε/4 := by dsimp [δ]; push_cast; field_simp
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  obtain ⟨C,hC,hc⟩ := ideal_zero_energy_bound (ε/2) (by positivity)
  refine ⟨C*((1+D)^(N+2))^2,by positivity,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  let c := finiteColumnCoefficient S β
  let Q := activeColumns (finiteColumns S) c
  have hQ : ∀ I∈Q,Supported I := activeColumns_supported _ _
  have hX0 : 0<X := zero_lt_one.trans_le hX
  have hNX (I : Ideal O) (hI : I∈Q) : (Ideal.absNorm I:ℝ)≤X :=
    hN I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2
  have hbase : 1≤(1+D)*X^δ := by
    have hxδ : 1≤X^δ := Real.one_le_rpow hX hδ.le
    nlinarith
  have hcoeff (I : Ideal O) (hI : I∈Q) :
      ‖c I*rowWeight η m A 1 t I‖ ≤ B*((1+D)^(N+2)*X^(ε/4)) := by
    have hI0 := (hQ I hI).1
    have hdI : ((idealDivisors I).card:ℝ) ≤ (1+D)*X^δ := by
      apply (hd I hI0).trans
      apply mul_le_mul (by linarith : D≤1+D)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hNX I hI) hδ.le) (by positivity) (by positivity)
    have hp : ((1+D)*X^δ)^(N+2) = (1+D)^(N+2)*X^(ε/4) := by
      rw [mul_pow,←Real.rpow_mul_natCast hX0.le,hδn]
    rw [norm_mul]
    calc
      _ ≤ ‖c I‖*1 := mul_le_mul_of_nonneg_left
        (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A 1 t I hI0) (norm_nonneg _)
      _ = ‖c I‖ := mul_one _
      _ ≤ B*((idealDivisors I).card:ℝ)^(Fintype.card ι+2) :=
        finiteColumnCoefficient_norm_le S β B hB hβ I hI0
      _ ≤ B*((1+D)*X^δ)^(Fintype.card ι+2) := by gcongr
      _ ≤ B*((1+D)*X^δ)^(N+2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) hB
      _ = _ := by rw [hp]
  have hb := hc Q hQ (fun I => c I*rowWeight η m A 1 t I)
    X K (B*((1+D)^(N+2)*X^(ε/4))) hX hK (by positivity) hNX hcoeff
  rw [zeroEnergy_eq_active_original,norm_mul]
  apply (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq
  have hxpow : (X^(ε/4))^2*X^(1+ε/2)=X^(1+ε) := by
    rw [←Real.rpow_mul_natCast hX0.le,←Real.rpow_add hX0]
    congr 1
    ring
  calc
    _ = C*((1+D)^(N+2))^2*K*B^2*‖paperRadialFourier W 0‖*
      ((X^(ε/4))^2*X^(1+ε/2)) := by ring
    _ = _ := by rw [hxpow]

theorem normalized_active_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤X → 0≤K → 0≤B →
      (∀ v∈S,finiteTupleProduct v≠0 → ‖β v‖≤B) →
      (∀ I∈supportedColumns (finiteColumns S),finiteColumnCoefficient S β I≠0 →
        (Ideal.absNorm I:ℝ)≤X) →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^ε := by
  obtain ⟨C,hC,hc⟩ := active_tuple_zero_energy_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  have hX0 : 0<X := zero_lt_one.trans_le hX
  have hb := hc hi η m A t S β W X K B hX hK hB hβ hN
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hX0)]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hX0.le)).trans_eq
  rw [Real.rpow_add hX0,Real.rpow_one]
  field_simp

theorem normalized_supported_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤X → 0≤K → 0≤B →
      (∀ v∈S,‖β v‖≤B) →
      (∀ v∈S,β v≠0 → (Ideal.absNorm (finiteTupleProduct v):ℝ)≤X) →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^ε := by
  obtain ⟨C,hC,hc⟩ := normalized_active_tuple_zero_energy_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  apply hc hi η m A t S β W X K B hX hK hB (fun v hv _ => hβ v hv)
  intro I _ hI
  obtain ⟨v,hv,hne,he⟩ := finiteColumnCoefficient_witness S β I hI
  rw [←he]
  exact hN v hv hne

end SevenEighths.CenteredMomentSupportedZeroEnergy

end

end OAI

end Source604

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceZeroEnergy.lean; sha256: 36580660b4eaff83b11cbbc31fb80e0d00f2e192144ec15654f17fc21c1b4074 -/
section Source605
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceZeroEnergy
open ActualEisensteinCubic HeckeFamily CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy
open CenteredMomentFirstLocalization CenteredMomentSourceRow
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem profileCoefficient_norm_le {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (hν : ∀ j I,‖ν j I‖≤1)
    (Wslot : ι → ℝ → ℂ) (P D : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (D₁ D₂ : ℝ)
    (hD : ∀ j,0≤D j) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hslot : ∀ j x,‖Wslot j x‖≤D j)
    (h₁ : ∀ x,‖W₁ x‖≤D₁) (h₂ : ∀ x,‖W₂ x‖≤D₂)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    ‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖≤
      2*D₁*D₂*(∏ j,D j) := by
  have hp : ‖∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j)‖≤∏ j,D j := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro j _
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hν j _) (hslot j _)
      (norm_nonneg _) zero_le_one
  have hr (I J : Ideal O) : ‖idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J‖≤2*D₁*D₂ := by
    unfold idealRectangle
    apply (norm_sub_le _ _).trans
    rw [norm_mul,norm_mul]
    have hx := mul_le_mul (h₁ ((Ideal.absNorm I:ℝ)/X₁))
      (h₂ ((Ideal.absNorm J:ℝ)/X₂)) (norm_nonneg _) hD₁
    have hy := mul_le_mul (h₁ ((Ideal.absNorm I:ℝ)/Y₁))
      (h₂ ((Ideal.absNorm J:ℝ)/Y₂)) (norm_nonneg _) hD₁
    linarith
  have hm (p : Prop) [Decidable p] : ‖(if p then 1 else 0 : ℂ)‖≤1 := by
    split_ifs <;> norm_num
  have hDp : 0≤∏ j,D j := Finset.prod_nonneg (fun j _ => hD j)
  unfold profileCoefficient
  rw [norm_mul,norm_mul,norm_mul]
  have h := mul_le_mul
    (mul_le_mul (mul_le_mul hp (hm (IsCoprime (finiteTupleProduct v) R)) (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hD j)))
      (hr (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))) (norm_nonneg _) (by positivity))
    (hm (s∣finiteTupleProduct v)) (norm_nonneg _) (by positivity)
  simpa only [mul_one] using h.trans_eq (by ring)

theorem profileCoefficient_product_bound {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ)
    (P b : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (B₁ B₂ s : Ideal O)
    (hP : ∀ j,0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hz : ∀ j,Wslot j 0=0) (hz₁ : W₁ 0=0) (hz₂ : W₂ 0=0)
    (hs : ∀ j x,Wslot j x≠0 → x≤b j)
    (hs₁ : ∀ x,W₁ x≠0 → x≤b₁) (hs₂ : ∀ x,W₂ x≠0 → x≤b₂)
    (v : Tuple ι)
    (hv : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤
      (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  let e := Fintype.equivFin ι
  have hzero : ∀ i,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hz (e.symm j)) (And.intro hz₁ hz₂)
  have hsup : ∀ i x,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x≠0 →
      x≤sourceBounds (fun j => b (e.symm j)) b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hs (e.symm j)) (And.intro hs₁ hs₂)
  have hn : CenteredMomentAddedZero.originalCoefficient (Fintype.card ι) 1
      (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
      (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (tupleEquiv e v)≠0 := by
    rw [originalCoefficient_reindex,←profileCoefficient_eq_original]
    exact hv
  have hh := originalCoefficient_product_bound (Fintype.card ι) 1
    (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0 (fun j => ν (e.symm j))
    (fun j => Wslot (e.symm j)) (fun j => P (e.symm j)) (fun j => b (e.symm j))
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP (e.symm j))
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hsup (tupleEquiv e v) hn
  simpa only [tupleProduct_reindex,sourceRadius,e.symm.prod_comp] using hh

theorem zeroEnergy_eq_zero_of_subunit {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι)) (β : Tuple ι → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K Y : ℝ) (hY : Y<1)
    (hN : ∀ v∈S,β v≠0 → finiteTupleProduct v≠0 ∧
      (Ideal.absNorm (finiteTupleProduct v):ℝ)≤Y) :
    zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K=0 := by
  have hb (v : Tuple ι) (hv : v∈S) : β v=0 := by
    by_contra hn
    have hh := hN v hv hn
    have hnorm : (1:ℝ)≤Ideal.absNorm (finiteTupleProduct v) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hh.1)
    linarith
  have hc (I : Ideal O) : finiteColumnCoefficient S β I=0 := by
    unfold finiteColumnCoefficient
    exact Finset.sum_eq_zero (fun v hv => hb v (Finset.mem_filter.mp hv).1)
  simp only [zeroEnergy,hc,zero_mul,star_zero,mul_zero,Finset.sum_const_zero]

theorem smooth_source_zero_energy {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (R : Ideal O) (ν : ι → Ideal O → ℂ), (∀ j I,‖ν j I‖≤1) →
      ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (X K : ℝ),
      0<X → 0≤K → (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)≤X →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K‖≤
        C*K*‖paperRadialFourier Φ 0‖*X^ε := by
  choose D hD hDb hz hs using fun j => smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  obtain ⟨D₁,hD₁,hDb₁,hz₁,hsb₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDb₂,hz₂,hsb₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  let B := 2*D₁*D₂*(∏ j,D j)
  have hB : 0≤B := mul_nonneg (by positivity) (Finset.prod_nonneg (fun j _ => hD j))
  have hend : 0≤(∏ j,b j)*b₁*b₂ := mul_nonneg
    (mul_nonneg (Finset.prod_nonneg (fun j _ => hb j)) hb₁) hb₂
  let L := 1+(∏ j,b j)*b₁*b₂
  have hL : 0<L := by dsimp only [L]; linarith
  have hendL : (∏ j,b j)*b₁*b₂≤L := by dsimp only [L]; linarith
  obtain ⟨C₀,hC₀,hbound⟩ := active_tuple_zero_energy_bound (Fintype.card ι) ε hε
  let C := C₀*(1+B^2)*L^(1+ε)
  have hC : 0<C := mul_pos (mul_pos hC₀ (by positivity)) (Real.rpow_pos_of_pos hL _)
  refine ⟨C,hC,?_⟩
  intro η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ X K hXX hK hscale
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤B :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂ hDb hDb₁ hDb₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hraw : 0≤(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) :=
    mul_nonneg (div_nonneg hT.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Finset.prod_nonneg (fun j _ => (hP j).le))
  have hN (v : Tuple ι) (hv : β v≠0) :
      finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*X := by
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
      hz hz₁ hz₂ hs hsb₁ hsb₂ v hv
    refine ⟨hh.1,hh.2.trans ?_⟩
    calc
      _ = ((∏ j,b j)*b₁*b₂)*((T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)) := by ring
      _ ≤ L*X := mul_le_mul hendL hscale hraw hL.le
  by_cases hsmall : L*X<1
  · have he := zeroEnergy_eq_zero_of_subunit η m A t S β Φ K (L*X) hsmall
      (fun v _ hv => hN v hv)
    change ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) Φ K‖≤_
    rw [he,mul_zero,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le hK) (norm_nonneg _)) (Real.rpow_nonneg hXX.le _)
  have hradius : 1≤L*X := le_of_not_gt hsmall
  have he := hbound (le_refl (Fintype.card ι)) η m A t S β Φ (L*X) K B hradius hK hB
    (fun v _ _ => hβ v) (fun I _ hI => by
      obtain ⟨v,hv,hne,hprod⟩ := finiteColumnCoefficient_witness S β I hI
      rw [←hprod]
      exact (hN v hne).2)
  have hpower : X⁻¹*(L*X)^(1+ε)=L^(1+ε)*X^ε := by
    rw [Real.mul_rpow hL.le hXX.le,Real.rpow_add hXX,Real.rpow_one]
    field_simp
  change ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) Φ K‖≤_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hXX)]
  apply (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hXX.le)).trans
  calc
    _ = C₀*B^2*L^(1+ε)*K*‖paperRadialFourier Φ 0‖*X^ε := by
      calc
        _ = C₀*B^2*K*‖paperRadialFourier Φ 0‖*(X⁻¹*(L*X)^(1+ε)) := by ring
        _ = _ := by rw [hpower];ring
    _ ≤ C*K*‖paperRadialFourier Φ 0‖*X^ε := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXX.le _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ hK
      dsimp only [C]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : B^2≤1+B^2) hC₀.le)
        (Real.rpow_nonneg hL.le _)

theorem smooth_source_zero_energy_at_radius {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (R : Ideal O) (ν : ι → Ideal O → ℂ), (∀ j I,‖ν j I‖≤1) →
      ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ), 0≤K →
      let X := (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let E := zeroEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K
      (X<1 → E=0) ∧ ‖((X⁻¹:ℝ):ℂ)*E‖≤C*K*‖paperRadialFourier Φ 0‖*X^ε := by
  choose D hD hDb hz hs using fun j => smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  obtain ⟨D₁,hD₁,hDb₁,hz₁,hsb₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDb₂,hz₂,hsb₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  let B := 2*D₁*D₂*(∏ j,D j)
  have hB : 0≤B := mul_nonneg (by positivity) (Finset.prod_nonneg (fun j _ => hD j))
  obtain ⟨C₀,hC₀,hbound⟩ := normalized_supported_tuple_zero_energy_bound (Fintype.card ι) ε hε
  refine ⟨C₀*(1+B^2),mul_pos hC₀ (by positivity),?_⟩
  intro η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ K hK X E
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤B :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂ hDb hDb₁ hDb₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hN (v : Tuple ι) (hv : β v≠0) :
      finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤X :=
    profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
      hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hz hz₁ hz₂ hs hsb₁ hsb₂ v hv
  have hzero (hx : X<1) : E=0 :=
    zeroEnergy_eq_zero_of_subunit η m A t S β Φ K X hx (fun v _ hv => hN v hv)
  refine ⟨hzero,?_⟩
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hXX : 0≤X := by
    dsimp only [X]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg (fun j _ => hb j)) hb₁) hb₂)
      (div_nonneg hT.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
      (Finset.prod_nonneg (fun j _ => (hP j).le))
  by_cases hx : X<1
  · rw [hzero hx,mul_zero,norm_zero]
    positivity
  have he := hbound (le_refl (Fintype.card ι)) η m A t S β Φ X K B
    (le_of_not_gt hx) hK hB (fun v _ => hβ v) (fun v _ hv => (hN v hv).2)
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXX _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    C₀*K*B^2 = C₀*B^2*K := by ring
    _ ≤ C₀*(1+B^2)*K := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : B^2≤1+B^2) hC₀.le) hK

theorem smooth_subset_source_zero_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple J)) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0≤K →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let ρ := (∏ j∈J,b j)*b₁*b₂*H
      let E := zeroEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K
      (ρ<1 → E=0) ∧
      ‖((ρ⁻¹:ℝ):ℂ)*E‖≤C*K*‖paperRadialFourier Φ 0‖*ρ^ε ∧
      ∀ X : ℝ,0<X → H≤X → ‖((X⁻¹:ℝ):ℂ)*E‖≤C*K*‖paperRadialFourier Φ 0‖*X^ε := by
  have hraw (J : Finset α) (hJ : J⊆F) := smooth_source_zero_energy
    (fun j : J => Wslot j.val) W₁ W₂ (fun j : J => a j.val) (fun j : J => b j.val)
    a₁ b₁ a₂ b₂ (fun j => ha j.val (hJ j.property)) (fun j => hb j.val (hJ j.property))
    ha₁ hb₁ ha₂ hb₂ (fun j => hsSlot j.val (hJ j.property)) hs₁ hs₂
    (fun j => hWslot j.val (hJ j.property)) hW₁ hW₂ ε hε
  have hrad (J : Finset α) (hJ : J⊆F) := smooth_source_zero_energy_at_radius
    (fun j : J => Wslot j.val) W₁ W₂ (fun j : J => a j.val) (fun j : J => b j.val)
    a₁ b₁ a₂ b₂ (fun j => ha j.val (hJ j.property)) (fun j => hb j.val (hJ j.property))
    ha₁ hb₁ ha₂ hb₂ (fun j => hsSlot j.val (hJ j.property)) hs₁ hs₂
    (fun j => hWslot j.val (hJ j.property)) hW₁ hW₂ ε hε
  let D (J : Finset α) : ℝ := if hJ : J⊆F then (hraw J hJ).choose+(hrad J hJ).choose else 1
  have hD (J : Finset α) : 0<D J := by
    dsimp only [D]
    split_ifs with hJ
    · exact add_pos (hraw J hJ).choose_spec.1 (hrad J hJ).choose_spec.1
    · norm_num
  let C := 1+∑ J∈F.powerset,D J
  have hC : 0<C := by
    have hsum := Finset.sum_nonneg (fun J (_ : J∈F.powerset) => (hD J).le)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ K hK H ρ E
  have hDC : D J≤C := by
    have hle := Finset.single_le_sum (fun L (_ : L∈F.powerset) => (hD L).le) (Finset.mem_powerset.mpr hJ)
    dsimp only [C]
    linarith
  have hde : D J=(hraw J hJ).choose+(hrad J hJ).choose := by simp only [D,dite_eq_left hJ]
  have hrawC : (hraw J hJ).choose≤C := by
    rw [hde] at hDC
    linarith [(hrad J hJ).choose_spec.1]
  have hradC : (hrad J hJ).choose≤C := by
    rw [hde] at hDC
    linarith [(hraw J hJ).choose_spec.1]
  have hr := (hrad J hJ).choose_spec.2 η m A t R (fun j : J => ν j.val)
    (fun j I => hν j.val j.property I) (fun j : J => P j.val)
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ K hK
  have heq : (∏ j : J,b j.val)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j : J,P j.val)=ρ := by
    rw [Finset.prod_coe_sort,Finset.prod_coe_sort]
    dsimp only [ρ,H]
    ring
  dsimp only at hr
  rw [heq] at hr
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hprodB : 0≤∏ j∈J,b j := Finset.prod_nonneg (fun j hj => hb j (hJ hj))
  have hprodP : 0≤∏ j∈J,P j := Finset.prod_nonneg (fun j hj => (hP j hj).le)
  have hρ : 0≤ρ := by dsimp only [ρ,H]; positivity
  refine ⟨hr.1,hr.2.trans ?_,?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hradC hK) (norm_nonneg _))
      (Real.rpow_nonneg hρ _)
  · intro X hXX hscale
    have hx := (hraw J hJ).choose_spec.2 η m A t R (fun j : J => ν j.val)
      (fun j I => hν j.val j.property I) (fun j : J => P j.val)
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP j.val j.property)
      hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ X K hXX hK
      (by simpa only [Finset.prod_coe_sort] using hscale)
    exact hx.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrawC hK) (norm_nonneg _))
      (Real.rpow_nonneg hXX.le _))

end SevenEighths.CenteredMomentSourceZeroEnergy

end

end OAI

end Source605

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceSecondZeroEnergy.lean; sha256: e92cfb5bf34badfdf411b1a15d0c6f21912f0941fcaecca4c0603a22691b0653 -/
section Source606
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceSecondZeroEnergy
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondDiagonal
local notation "O" => ActualEisensteinCubic.O

def sourceSecondZero (S : Finset (Ideal O)) (β : Ideal O→ℂ) (η : Character) (t : ℝ) : ℂ :=
  secondZeroEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
    (fun I => β I*heightCoeff η t I)

lemma heightCoeff_norm_le_one (η : Character) (t : ℝ) (I : Ideal O) (hI : I≠0) :
    ‖heightCoeff η t I‖≤1 := by
  have hn : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp : ‖(Ideal.absNorm I:ℂ)^(Complex.I*t)‖=1 := by
    rw [show (Ideal.absNorm I:ℂ)=((Ideal.absNorm I:ℝ):ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp
  rw [heightCoeff,norm_mul,hp,mul_one]
  exact idealCoeff_norm_le_one η I

theorem secondZeroEnergy_filter {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (p : α→Prop) [DecidablePred p] (hc : ∀ i∈S,¬p i→c i=0) :
    secondZeroEnergy S a ha c=secondZeroEnergy (S.filter p) a ha c := by
  unfold secondZeroEnergy
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hpi : p i
  · rw [ite_eq_left hpi]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hpj : p j
    · rw [ite_eq_left hpj]
    · simp only [ite_eq_right hpj,hc j hj hpj,star_zero,mul_zero,zero_mul]
  · simp only [ite_eq_right hpi,hc i hi hpi,zero_mul,Finset.sum_const_zero]

lemma sourceGenerator_span (S : Finset (Ideal O)) (I : supportedColumns S) :
    Ideal.span {sourceGenerator S I}=(I:Ideal O) :=
  primary_span_supported I (Finset.mem_filter.mp I.property).2
lemma sourceGenerator_primary (S : Finset (Ideal O)) (I : supportedColumns S) :
    ConcretePrimeRowBridge.goodLambda^2∣sourceGenerator S I-1 :=
  (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I (Finset.mem_filter.mp I.property).2)).2
lemma sourceGenerator_injective (S : Finset (Ideal O)) : Function.Injective (sourceGenerator S) := by
  intro I J h
  apply Subtype.ext
  rw [←sourceGenerator_span S I,←sourceGenerator_span S J,h]

theorem sourceSecondZero_divisor_bound (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (η : Character) (t B Y : ℝ) (hB : 0≤B) (hY : 0≤Y)
    (s : Ideal O) (hs : s≠0)
    (hc : ∀ I∈supportedColumns S,β I≠0→‖β I‖≤B)
    (hdiv : ∀ I∈supportedColumns S,β I≠0→s∣I)
    (hN : ∀ I∈supportedColumns S,β I≠0→(Ideal.absNorm I:ℝ)≤Y) :
    ‖sourceSecondZero S β η t‖≤128*B^2*Y/(Ideal.absNorm s:ℝ) := by
  let Q : Finset (supportedColumns S) := Finset.univ.filter (fun I => β I≠0)
  rw [sourceSecondZero,secondZeroEnergy_filter Finset.univ (sourceGenerator S)
    (sourceGenerator_supported S) (fun I => β I*heightCoeff η t I) (fun I => β I≠0)
      (by intro I _ h; simp only [not_not] at h; rw [h,zero_mul])]
  refine secondZeroEnergy_divisor_bound Q (sourceGenerator S) (sourceGenerator_supported S)
    (sourceGenerator_primary S) (sourceGenerator_injective S).injOn _ B hB ?_ s hs ?_ Y hY ?_
  · intro I hI
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (heightCoeff_norm_le_one η t I
      (Finset.mem_filter.mp I.property).2.1) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hc I I.property (Finset.mem_filter.mp hI).2)
  · intro I hI
    rw [sourceGenerator_span]
    exact hdiv I I.property (Finset.mem_filter.mp hI).2
  · intro I hI
    rw [sourceGenerator_span]
    exact hN I I.property (Finset.mem_filter.mp hI).2

theorem sourceSecondZero_eq_zero_of_subunit (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (η : Character) (t Y : ℝ) (hY : Y<1)
    (hN : ∀ I∈supportedColumns S,β I≠0→(Ideal.absNorm I:ℝ)≤Y) :
    sourceSecondZero S β η t=0 := by
  have hc (I : supportedColumns S) : β I=0 := by
    by_contra hn
    have hi : (1:ℝ)≤Ideal.absNorm (I:Ideal O) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.mem_filter.mp I.property).2.1)
    linarith [hN I I.property hn]
  simp only [sourceSecondZero,secondZeroEnergy,hc,zero_mul,star_zero,mul_zero,Finset.sum_const_zero]

theorem tuple_second_zero_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (η : Character) (t B Y : ℝ),
      0≤B → 1≤Y → (∀ v∈S,finiteTupleProduct v≠0→‖β v‖≤B) →
      ∀ (s : Ideal O),s≠0 →
      (∀ v∈S,β v≠0→s∣finiteTupleProduct v) →
      (∀ v∈S,β v≠0→(Ideal.absNorm (finiteTupleProduct v):ℝ)≤Y) →
      ‖sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t‖≤
        C*B^2*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  let δ := ε/(2*(N+2:ℕ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδn : δ*(N+2:ℕ)=ε/2 := by dsimp [δ]; push_cast; field_simp
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨128*((1+D)^(N+2))^2,by positivity,?_⟩
  intro ι _ hi S β η t B Y hB hY hβ s hs hdiv hN
  let c := finiteColumnCoefficient S β
  have hY0 : 0<Y := zero_lt_one.trans_le hY
  have hbound (I : Ideal O) (hI : I∈supportedColumns (finiteColumns S)) (hn : c I≠0) :
      (Ideal.absNorm I:ℝ)≤Y := by
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv hv0
  have hbase : 1≤(1+D)*Y^δ := by
    have hp := Real.one_le_rpow hY hδ.le
    nlinarith
  have hcoeff (I : Ideal O) (hI : I∈supportedColumns (finiteColumns S)) (hn : c I≠0) :
      ‖c I‖≤B*((1+D)^(N+2)*Y^(ε/2)) := by
    have hI0 := (Finset.mem_filter.mp hI).2.1
    have hdI : ((IdealMobiusDivisorSum.idealDivisors I).card:ℝ)≤(1+D)*Y^δ :=
      (hd I hI0).trans (mul_le_mul (by linarith)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hbound I hI hn) hδ.le) (by positivity) (by positivity))
    have hp : ((1+D)*Y^δ)^(N+2)=(1+D)^(N+2)*Y^(ε/2) := by
      rw [mul_pow,←Real.rpow_mul_natCast hY0.le,hδn]
    calc
      _ ≤ B*((IdealMobiusDivisorSum.idealDivisors I).card:ℝ)^(Fintype.card ι+2) :=
        finiteColumnCoefficient_norm_le S β B hB hβ I hI0
      _ ≤ B*((1+D)*Y^δ)^(Fintype.card ι+2) := by gcongr
      _ ≤ B*((1+D)*Y^δ)^(N+2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) hB
      _ = _ := by rw [hp]
  have hb := sourceSecondZero_divisor_bound (finiteColumns S) c η t
    (B*((1+D)^(N+2)*Y^(ε/2))) Y (by positivity) hY0.le s hs hcoeff
    (by
      intro I hI hn
      obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
      rw [←he]
      exact hdiv v hv hv0) hbound
  apply hb.trans_eq
  have hp : (Y^(ε/2))^2*Y=Y^(1+ε) := by
    rw [←Real.rpow_mul_natCast hY0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*(2:ℝ)=ε by ring,Real.rpow_add hY0,Real.rpow_one]
    ring
  calc
    _ = (128*((1+D)^(N+2))^2)*B^2*((Y^(ε/2))^2*Y)/(Ideal.absNorm s:ℝ) := by ring
    _ = _ := by rw [hp]

theorem normalized_tuple_second_zero_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (η : Character) (t B L T : ℝ),
      0≤B → 0<L → 0<T → (∀ v∈S,finiteTupleProduct v≠0→‖β v‖≤B) →
      ∀ (s : Ideal O),s≠0 →
      (∀ v∈S,β v≠0→s∣finiteTupleProduct v) →
      (∀ v∈S,β v≠0→(Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*T) →
      (L*T<1 → sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t=0) ∧
      ∀ κ : ℂ,‖(κ/(T:ℂ))*sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t‖≤
        C*‖κ‖*B^2*L^(1+ε)*T^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := tuple_second_zero_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi S β η t B L T hB hL hT hβ s hs hdiv hN
  have hz (hsmall : L*T<1) : sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t=0 := by
    apply sourceSecondZero_eq_zero_of_subunit _ _ η t (L*T) hsmall
    intro I hI hn
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv hv0
  refine ⟨hz,?_⟩
  intro κ
  by_cases hsmall : L*T<1
  · rw [hz hsmall,mul_zero,norm_zero]
    positivity
  have hb := hbound hi S β η t B (L*T) hB (le_of_not_gt hsmall) hβ s hs hdiv hN
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  apply (mul_le_mul_of_nonneg_left hb (div_nonneg (norm_nonneg _) hT.le)).trans_eq
  rw [Real.mul_rpow hL.le hT.le,Real.rpow_add hT,Real.rpow_one]
  field_simp

lemma profileCoefficient_dvd {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι)
    (hv : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    s∣finiteTupleProduct v := by
  by_contra h
  exact hv (by simp only [profileCoefficient,ite_eq_right h,mul_zero])

theorem profile_second_zero_energy (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : ι→Ideal O→ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (Wslot : ι→ℝ→ℂ) (P D b : ι→ℝ)
      (W₁ W₂ : ℝ→ℂ) (D₁ D₂ b₁ b₂ : ℝ),
      (∀ j,0≤D j) → 0≤D₁ → 0≤D₂ → (∀ j,0≤b j) → 0≤b₁ → 0≤b₂ →
      (∀ j x,‖Wslot j x‖≤D j) → (∀ x,‖W₁ x‖≤D₁) → (∀ x,‖W₂ x‖≤D₂) →
      (∀ j,Wslot j 0=0) → W₁ 0=0 → W₂ 0=0 →
      (∀ j x,Wslot j x≠0→x≤b j) → (∀ x,W₁ x≠0→x≤b₁) → (∀ x,W₂ x≠0→x≤b₂) →
      ∀ (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let L := (∏ j,b j)*b₁*b₂
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (L*Traw<1 → E=0) ∧ ∀ κ : ℂ,
        ‖(κ/(Traw:ℂ))*E‖≤C*‖κ‖*(2*D₁*D₂*(∏ j,D j))^2*(1+L)^(1+ε)*Traw^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := normalized_tuple_second_zero_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η t R ν hν Wslot P D b W₁ W₂ D₁ D₂ b₁ b₂
    hD hD₁ hD₂ hb hb₁ hb₂ hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S Traw L E
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤2*D₁*D₂*(∏ j,D j) :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂
      hslot h₁ h₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hn₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hn₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  have hraw : 0<Traw := mul_pos (div_pos hT (mul_pos hn₁ hn₂)) (Finset.prod_pos (fun j _=>hP j))
  have hL : 0≤L := mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun j _=>hb j)) hb₁) hb₂
  have hN (v : Tuple ι) (hv : β v≠0) : (Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*Traw := by
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
      hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hz hz₁ hz₂ hs hs₁ hs₂ v hv
    exact hh.2.trans_eq (by dsimp only [L,Traw];ring)
  refine ⟨?_,?_⟩
  · intro hsmall
    apply sourceSecondZero_eq_zero_of_subunit _ _ η t (L*Traw) hsmall
    intro I hI hn
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv0
  · exact (hbound hi S β η t (2*D₁*D₂*(∏ j,D j)) (1+L) Traw
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD₁) hD₂) (Finset.prod_nonneg (fun j _=>hD j)))
      (by linarith) hraw (fun v _ _=>hβ v) s hsz
      (fun v _ hv=>profileCoefficient_dvd R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v hv)
      (fun v _ hv=>(hN v hv).trans (mul_le_mul_of_nonneg_right (by linarith : L≤1+L) hraw.le))).2

theorem bounded_profile_second_zero_energy (N : ℕ) (ε : ℝ) (hε : 0<ε)
    (D b : ℝ) (hD : 0≤D) (hb : 0≤b) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : ι→Ideal O→ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ),
      (∀ j x,‖Wslot j x‖≤D) → (∀ x,‖W₁ x‖≤D) → (∀ x,‖W₂ x‖≤D) →
      (∀ j,Wslot j 0=0) → W₁ 0=0 → W₂ 0=0 →
      (∀ j x,Wslot j x≠0→x≤b) → (∀ x,W₁ x≠0→x≤b) → (∀ x,W₂ x≠0→x≤b) →
      ∀ (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (b^(Fintype.card ι+2)*Traw<1 → E=0) ∧ ∀ κ : ℂ,
        ‖(κ/(Traw:ℂ))*E‖≤C*‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C₀,hC₀,hmain⟩ := profile_second_zero_energy N ε hε
  let B := 2*D*D*(1+D)^N
  let L := (1+b)^(N+2)
  let C := C₀*(1+B^2)*(1+L)^(1+ε)
  have hB : 0≤B := by dsimp [B];positivity
  have hL : 0≤L := by dsimp [L];positivity
  have hC : 0<C := mul_pos (mul_pos hC₀ (by positivity)) (Real.rpow_pos_of_pos (by linarith) _)
  refine ⟨C,hC,?_⟩
  intro ι _ hi η t R ν hν Wslot P W₁ W₂ hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S Traw E
  have hTpos : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hraw0 : 0≤Traw := mul_nonneg (div_nonneg hTpos.le (by positivity))
    (Finset.prod_nonneg (fun j _=>(hP j).le))
  have hh := hmain hi η t R ν hν Wslot P (fun _=>D) (fun _=>b) W₁ W₂ D D b b
    (fun _=>hD) hD hD (fun _=>hb) hb hb hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S
  dsimp only at hh
  simp only [Finset.prod_const,Finset.card_univ] at hh
  have heL : b^Fintype.card ι*b*b=b^(Fintype.card ι+2) := by
    rw [pow_add,pow_two];ring
  rw [heL] at hh
  refine ⟨hh.1,?_⟩
  intro κ
  have hBbound : 2*D*D*D^Fintype.card ι≤B := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (pow_le_pow_left₀ hD (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hi)
  have hLbound : b^(Fintype.card ι+2)≤L :=
    (pow_le_pow_left₀ hb (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
  have hpow : (1+b^(Fintype.card ι+2))^(1+ε)≤(1+L)^(1+ε) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hcoef : C₀*(2*D*D*D^Fintype.card ι)^2*(1+b^(Fintype.card ι+2))^(1+ε)≤C := by
    dsimp only [C]
    apply mul_le_mul _ hpow (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ hC₀.le
    exact (pow_le_pow_left₀ (by positivity) hBbound 2).trans (by linarith)
  apply (hh.2 κ).trans
  calc
    _ = (C₀*(2*D*D*D^Fintype.card ι)^2*(1+b^(Fintype.card ι+2))^(1+ε))*
        (‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ)) := by ring
    _ ≤ C*(‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by ring

theorem smooth_subset_source_second_zero_energy {α : Type*} (F : Finset α)
    (Wslot : α→ℝ→ℂ) (W₁ W₂ : ℝ→ℂ) (a b : α→ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : α→Ideal O→ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) → ∀ (P : α→ℝ)
      (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T →
      ∀ (pools : (J⊕Fin 2)→Finset (Ideal O)) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),
      let S := Fintype.piFinset pools
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let Y := (∏ j∈J,b j)*b₁*b₂*Traw
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J=>ν j.val)
          (fun j : J=>Wslot j.val) (fun j : J=>P j.val) W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (Y<1 → E=0) ∧
        ‖(((K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier Φ 0)/(Traw:ℂ))*E‖≤
          C*‖(K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier Φ 0‖*Traw^ε/(Ideal.absNorm s:ℝ) := by
  choose D hD hDb hz hsb using fun j : F => smooth_annular_bound
    (Wslot j.val) (a j.val) (b j.val) (ha j.val j.property)
    (hsSlot j.val j.property) (hWslot j.val j.property)
  obtain ⟨D₁,hD₁,hDb₁,hz₁,hsb₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDb₂,hz₂,hsb₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  let Dmax := 1+D₁+D₂+∑ j : F,D j
  let bmax := 1+b₁+b₂+∑ j : F,b j.val
  have hDs : 0≤∑ j : F,D j := Finset.sum_nonneg (fun j _=>hD j)
  have hbs : 0≤∑ j : F,b j.val := Finset.sum_nonneg (fun j _=>hb j.val j.property)
  have hDmax : 0≤Dmax := by dsimp only [Dmax];linarith
  have hbmax : 0≤bmax := by dsimp only [bmax];linarith
  have hD₁max : D₁≤Dmax := by dsimp only [Dmax];linarith
  have hD₂max : D₂≤Dmax := by dsimp only [Dmax];linarith
  have hb₁max : b₁≤bmax := by dsimp only [bmax];linarith
  have hb₂max : b₂≤bmax := by dsimp only [bmax];linarith
  have hDj (j : F) : D j≤Dmax := by
    have h := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset F))=>hD k) (Finset.mem_univ j)
    dsimp only [Dmax]
    linarith
  have hbj (j : F) : b j.val≤bmax := by
    have h := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset F))=>hb k.val k.property) (Finset.mem_univ j)
    dsimp only [bmax]
    linarith
  obtain ⟨C,hC,hbound⟩ := bounded_profile_second_zero_energy F.card ε hε Dmax bmax hDmax hbmax
  refine ⟨C,hC,?_⟩
  intro J hJ η t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY pools Φ K S Traw Y E
  let β := profileCoefficient R (fun j : J=>ν j.val) (fun j : J=>Wslot j.val) (fun j : J=>P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hcard : Fintype.card J≤F.card := by simpa only [Fintype.card_coe] using Finset.card_le_card hJ
  have hh := hbound hcard η t R (fun j : J=>ν j.val) (fun j I=>hν j.val j.property I)
    (fun j : J=>Wslot j.val) (fun j : J=>P j.val) W₁ W₂
    (fun j x=>(hDb ⟨j.val,hJ j.property⟩ x).trans (hDj ⟨j.val,hJ j.property⟩))
    (fun x=>(hDb₁ x).trans hD₁max) (fun x=>(hDb₂ x).trans hD₂max)
    (fun j=>hz ⟨j.val,hJ j.property⟩) hz₁ hz₂
    (fun j x hx=>(hsb ⟨j.val,hJ j.property⟩ x hx).trans (hbj ⟨j.val,hJ j.property⟩))
    (fun x hx=>(hsb₁ x hx).trans hb₁max) (fun x hx=>(hsb₂ x hx).trans hb₂max)
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j=>hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S
  dsimp only at hh
  rw [Finset.prod_coe_sort] at hh
  refine ⟨?_,hh.2 ((K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier Φ 0)⟩
  intro hsmall
  apply sourceSecondZero_eq_zero_of_subunit _ _ η t Y hsmall
  intro I hI hn
  obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
  have hN := profileCoefficient_product_bound R (fun j : J=>ν j.val)
    (fun j : J=>Wslot j.val) (fun j : J=>P j.val) (fun j : J=>b j.val)
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j=>hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY (fun j=>hz ⟨j.val,hJ j.property⟩) hz₁ hz₂
    (fun j=>hsb ⟨j.val,hJ j.property⟩) hsb₁ hsb₂ v hv0
  rw [←he]
  exact hN.2.trans_eq (by rw [Finset.prod_coe_sort,Finset.prod_coe_sort];dsimp only [Y,Traw];ring)

end SevenEighths.CenteredMomentSourceSecondZeroEnergy

end

end OAI

end Source606

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondLocalization.lean; sha256: 1876afff230a7390df38237c72f14c4ea7558d9faee6c55149353aef84fa966d -/
section Source607
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondLocalization
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSourcePoisson CenteredMomentSecondWholeKernel CenteredMomentSecondTail
open CenteredMomentFirstLocalization CenteredMomentSectorLocalization CenteredMomentSupportedCorrelation
open CenteredMomentSupportedTailAggregate CenteredMomentSourceSecondZeroEnergy CenteredMomentSecondDiagonal
local notation "O" => ActualEisensteinCubic.O

def secondRetainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
    ∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
      actualCorrelation (primaryGenerator I) (primaryGenerator J)
        ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) (-h)*
      paperRadialFourier W (K*‖eisEmbedding h‖^2/
        ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2)

theorem secondSourceKernel_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    secondSourceKernel I J W K=
      (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
        actualCorrelation (primaryGenerator I) (primaryGenerator J)
          ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) 0*
          paperRadialFourier W 0+
      secondRetainedPair I J hI hJ W K Tsec Z ξ+
      secondDiscardedPair I J hI hJ W K Tsec Z ξ := by
  have hpI := (supported_span_primaryGenerator_iff I).mpr hI
  have hpJ := (supported_span_primaryGenerator_iff J).mpr hJ
  have hk : 0<K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) :=
    div_pos hK (mul_pos (CenteredMomentFirstScale.norm_pos I hI.1) (CenteredMomentFirstScale.norm_pos J hJ.1))
  have hs := lattice_fourier_split W _ hk
    (fun h => actualCorrelation (primaryGenerator I) (primaryGenerator J) hpI hpJ (-h))
    _ (fun h => CenteredMomentTail.actualCorrelation_norm_le _ _ hpI hpJ (-h))
    (frequencyRadius Tsec Z ξ)
  have he (h : O) : K*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2=
      (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*normValue h := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq I hI,primary_norm_sq J hJ,normValue_eq_embedding]
    ring
  rw [secondSourceKernel_poisson I J hI hJ W K hK]
  unfold secondRetainedPair secondDiscardedPair
  simp_rw [he]
  rw [hs]
  simp only [neg_zero]
  ring

def secondRetainedEnergy (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*heightCoeff η t I)*star (c J*heightCoeff η t J))*
      secondRetainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

theorem sourceGaussEnergy_localized (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    CenteredMomentOriginalChildEnergy.sourceGaussEnergy S β (heightCoeff η t) W K=
      ((K:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β η t+
      secondRetainedEnergy η t S β W K Tsec Z ξ+
      secondDiscardedEnergy η t S β W K Tsec Z ξ := by
  rw [sourceGaussEnergy_poisson η t S β W K hK]
  unfold sourceSecondZero secondZeroEnergy secondRetainedEnergy secondDiscardedEnergy
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  have he := secondSourceKernel_split I J (Finset.mem_filter.mp I.property).2
    (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ hK
  rw [secondSourceKernel_poisson I J (Finset.mem_filter.mp I.property).2
    (Finset.mem_filter.mp J.property).2 W K hK] at he
  simp only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2]
  convert congrArg (fun x : ℂ => ((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*x) he using 1 <;> ring

end SevenEighths.CenteredMomentSecondLocalization

end

end OAI

end Source607

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSectorRetained.lean; sha256: a5b41279b637778633de30f67a78a03a29dacaf6c8e045f96741305c39bcf6aa -/
section Source608
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSectorRetained
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorFrequency CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLedger CenteredMomentCanonicalFirst
open CenteredMomentSecondWholeKernel CenteredMomentFirstLocalization CenteredMomentSectorLocalization
open CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

def physicalKernel (C D : Ideal O) (W : 𝓢(ℝ,ℂ)) (K R : ℝ)
    (j : O) (I J : Ideal O) : ℂ :=
  ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*I):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*J):ℝ):ℂ)))*
    (retainedWeight R (normValue j):ℂ)*
      paperRadialFourier W (K*‖eisEmbedding j‖^2/
        ‖eisEmbedding (primaryGenerator (C*I)*primaryGenerator (D*J))‖^2)

theorem physical_sector_summable (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    Summable (sectorFrequency η t S β C D hC hD (physicalKernel C D W K R)) := by
  unfold sectorFrequency
  apply summable_sum
  intro I hI
  apply summable_sum
  intro J hJ
  by_cases hcop : IsCoprime (I:Ideal O) (J:Ideal O)
  · simp only [ite_eq_left hcop]
    have hCI : Supported (C*(I:Ideal O)) := (supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩
    have hDJ : Supported (D*(J:Ideal O)) := (supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩
    have hk : 0<K/((Ideal.absNorm (C*(I:Ideal O)):ℝ)*Ideal.absNorm (D*(J:Ideal O))) :=
      div_pos hK (mul_pos (CenteredMomentFirstScale.norm_pos _ hCI.1) (CenteredMomentFirstScale.norm_pos _ hDJ.1))
    have hc (j : O) : ‖idealCorrelation (C*I) (D*J) hCI hDJ j‖≤
        (Ideal.absNorm (C*(I:Ideal O)):ℝ)*Ideal.absNorm (D*(J:Ideal O)) := by
      have hh := CenteredMomentTail.actualCorrelation_norm_le _ _
        ((supported_span_primaryGenerator_iff _).mpr hCI) ((supported_span_primaryGenerator_iff _).mpr hDJ) j
      simpa only [CenteredMomentSupport.idealCorrelation,primary_span_supported _ hCI,primary_span_supported _ hDJ] using hh
    have hs := weighted_fourier_summable W _ hk
      (fun j=>idealCorrelation (C*I) (D*J) hCI hDJ j)
      (fun j=>(retainedWeight R (normValue j):ℂ)) _ hc (fun j=>retained_complex_norm R _)
    have he (j : O) : K*‖eisEmbedding j‖^2/‖eisEmbedding (primaryGenerator (C*I)*primaryGenerator (D*J))‖^2=
        (K/((Ideal.absNorm (C*(I:Ideal O)):ℝ)*Ideal.absNorm (D*(J:Ideal O))))*normValue j := by
      rw [map_mul,norm_mul,mul_pow,primary_norm_sq _ hCI,primary_norm_sq _ hDJ,normValue_eq_embedding]
      ring
    convert hs.mul_left
      (((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
        ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*(I:Ideal O)):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*(J:Ideal O)):ℝ):ℂ)))) using 1
    funext j
    dsimp only [physicalKernel]
    rw [he]
    ring
  · simp only [ite_eq_right hcop,zero_mul]
    exact summable_zero

theorem actual_retained_sector_GV (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    (∑' j : O,sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) j)=
      ∑ U : Finset (CommonIndex C D),∑' h : O,
        if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
          sectorFrequency η t S β C D hC hD (physicalKernel C D W K R)
            ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) else 0 := by
  rw [sectorFrequency_tsum_common η t S β C D hC hD hCD]
  rw [sectorFrequency_tsum_partition η t S β C D hC hD _
    ((physical_sector_summable η t S β C D hC hD W K R hK).comp_injective
      (mul_right_injective₀ (commonFrequencyGenerator_ne_zero C D hC)))]
  exact Finset.sum_congr rfl (fun U _=>sectorFrequency_partition_nonunit η t S β C D hC hD U _)

end SevenEighths.CenteredMomentSecondSectorRetained

end

end OAI

end Source608

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondRetainedPair.lean; sha256: 7502934c751240ef3d31ccce0c8c446eef6d020efb5536010a491067ce3fb781 -/
section Source609
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedPair
open CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondSectorRetained CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentSecondWholeKernel CenteredMomentFirstLocalization CenteredMomentSectorLocalization
open CenteredMomentSecondLocalization CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

theorem physical_pair_summable (C D I J : Ideal O) (hI : Supported (C*I)) (hJ : Supported (D*J))
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    Summable (fun j : O=>idealCorrelation (C*I) (D*J) hI hJ j*physicalKernel C D W K R j I J) := by
  have hk : 0<K/((Ideal.absNorm (C*I):ℝ)*Ideal.absNorm (D*J)) :=
    div_pos hK (mul_pos (CenteredMomentFirstScale.norm_pos _ hI.1) (CenteredMomentFirstScale.norm_pos _ hJ.1))
  have hc (j : O) : ‖idealCorrelation (C*I) (D*J) hI hJ j‖≤
      (Ideal.absNorm (C*I):ℝ)*Ideal.absNorm (D*J) := by
    have hh := CenteredMomentTail.actualCorrelation_norm_le _ _
      ((supported_span_primaryGenerator_iff _).mpr hI) ((supported_span_primaryGenerator_iff _).mpr hJ) j
    simpa only [idealCorrelation,primary_span_supported _ hI,primary_span_supported _ hJ] using hh
  have hs := weighted_fourier_summable W _ hk (fun j=>idealCorrelation (C*I) (D*J) hI hJ j)
    (fun j=>(retainedWeight R (normValue j):ℂ)) _ hc (fun j=>retained_complex_norm R _)
  have he (j : O) : K*‖eisEmbedding j‖^2/‖eisEmbedding (primaryGenerator (C*I)*primaryGenerator (D*J))‖^2=
      (K/((Ideal.absNorm (C*I):ℝ)*Ideal.absNorm (D*J)))*normValue j := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq _ hI,primary_norm_sq _ hJ,normValue_eq_embedding]
    ring
  convert hs.mul_left
    ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*I):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*J):ℝ):ℂ))) using 1
  funext j
  dsimp only [physicalKernel]
  rw [he]
  ring

theorem retainedPair_positive_frequency (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    secondRetainedPair I J hI hJ W K Tsec Z ξ=
      ∑' j : O,idealCorrelation I J hI hJ j*physicalKernel 1 1 W K (frequencyRadius Tsec Z ξ) j I J := by
  have he := (Equiv.neg O).tsum_eq (fun j : O=>idealCorrelation I J hI hJ j*
    physicalKernel 1 1 W K (frequencyRadius Tsec Z ξ) j I J)
  simp only [Equiv.neg_apply,physicalKernel,one_mul,map_neg,norm_neg,
    normValue_eq_embedding] at he
  simp only [physicalKernel,one_mul,normValue_eq_embedding]
  rw [←he]
  unfold secondRetainedPair
  rw [←tsum_mul_left]
  apply tsum_congr
  intro j
  simp only [idealCorrelation,normValue_eq_embedding]
  ring

end SevenEighths.CenteredMomentSecondRetainedPair

end

end OAI

end Source609

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSourceRetained.lean; sha256: d7ddcda0755c013cae0e440df2af0749361b3c7f003c4508fee4d79aba99fc89 -/
section Source610
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceRetained
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentSecondLocalization CenteredMomentSecondSourceEnergy
open CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentSecondSectorColumns
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorRetained CenteredMomentSecondRetainedPair
open CenteredMomentSecondSectorFrequency CenteredMomentSupport CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then secondRetainedPair I J hI hJ W K Tsec Z ξ else 0 else 0

theorem retainedKernel_eq (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    retainedKernel I J W K Tsec Z ξ=secondRetainedPair I J hI hJ W K Tsec Z ξ := by
  simp only [retainedKernel,dite_eq_left hI,dite_eq_left hJ]

theorem retainedEnergy_common_sectors (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
            retainedKernel q.1 q.2 W K Tsec Z ξ := by
  let F := fun I J : Ideal O=>((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*
    retainedKernel I J W K Tsec Z ξ
  have he : secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,F I J := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [F]
    rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]
  rw [he]
  have hj (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort _ _
  simp_rw [hj]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I=>∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ F

theorem retained_sector_independent (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
        retainedKernel q.1 q.2 W K Tsec Z ξ)=
      heightCoeff η t C*star (heightCoeff η t D)*
        ∑ I : sectorPool C hC S,∑ J : sectorPool D hD S,
          if IsCoprime (I:Ideal O) (J:Ideal O) then
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              retainedKernel (C*I) (D*J) W K Tsec Z ξ else 0 := by
  rw [←independent_sector_pools C D hC hD hCD S
    (fun I J=>((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
      retainedKernel (C*I) (D*J) W K Tsec Z ξ)]
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun I J=>((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*
      retainedKernel I J W K Tsec Z ξ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs <;> simp only [heightCoeff_mul,star_mul,mul_zero]
  ring

theorem retainedKernel_physical (C D I J : Ideal O) (hI : Supported (C*I)) (hJ : Supported (D*J))
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    retainedKernel (C*I) (D*J) W K Tsec Z ξ=
      ∑' j : O,idealCorrelation (C*I) (D*J) hI hJ j*
        physicalKernel C D W K (frequencyRadius Tsec Z ξ) j I J := by
  rw [retainedKernel_eq _ _ hI hJ,retainedPair_positive_frequency]
  simp only [physicalKernel,one_mul]

end SevenEighths.CenteredMomentSecondSourceRetained

end

end OAI

end Source610

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSourceFrequency.lean; sha256: 3663e69a6141b46f0669cfa451f2d7bccbda6b3f60e971cea836191f195d7192 -/
section Source611
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceFrequency
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentSecondSourceRetained CenteredMomentFirstSectors
open CenteredMomentSecondSectorColumns CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorRetained
open CenteredMomentSecondRetainedPair CenteredMomentSecondSectorFrequency CenteredMomentSupport CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

theorem retained_sector_eq_physical (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
        retainedKernel q.1 q.2 W K Tsec Z ξ)=
      heightCoeff η t C*star (heightCoeff η t D)*
        ∑' j : O,sectorFrequency η t S β C D hC hD
          (physicalKernel C D W K (frequencyRadius Tsec Z ξ)) j := by
  rw [retained_sector_independent η t S β C D hC.1 hD.1 hCD]
  congr 1
  let c := fun I : sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I
  let d := fun J : sectorPool D hD.1 S=>β (D*J)*heightCoeff η t J
  have hci (I : sectorPool C hC.1 S) : Supported (C*(I:Ideal O)) :=
    (supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩
  have hdj (J : sectorPool D hD.1 S) : Supported (D*(J:Ideal O)) :=
    (supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩
  let f := fun (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) (j : O)=>
    if IsCoprime (I:Ideal O) (J:Ideal O) then
      (c I*star (d J))*(idealCorrelation (C*I) (D*J) (hci I) (hdj J) j*
        physicalKernel C D W K (frequencyRadius Tsec Z ξ) j I J) else 0
  have hs (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) : Summable (f I J) := by
    by_cases hc : IsCoprime (I:Ideal O) (J:Ideal O)
    · simpa only [f,ite_eq_left hc] using (physical_pair_summable C D I J (hci I) (hdj J)
        W K (frequencyRadius Tsec Z ξ) hK).mul_left (c I*star (d J))
    · simp only [f,ite_eq_right hc];exact summable_zero
  have hp (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
          retainedKernel (C*I) (D*J) W K Tsec Z ξ else 0)=∑' j : O,f I J j := by
    by_cases hc : IsCoprime (I:Ideal O) (J:Ideal O)
    · simp only [f,ite_eq_left hc]
      rw [retainedKernel_physical C D I J (hci I) (hdj J),tsum_mul_left]
    · simp only [f,ite_eq_right hc,tsum_zero]
  have hf (j : O) : sectorFrequency η t S β C D hC hD
      (physicalKernel C D W K (frequencyRadius Tsec Z ξ)) j=
      ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,f I J j := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [f,c,d]
    split_ifs <;> ring
  simp_rw [hp]
  rw [tsum_congr hf, Summable.tsum_finsetSum (fun I _=>summable_sum (fun J _=>hs I J))]
  exact Finset.sum_congr rfl (fun I _=>(Summable.tsum_finsetSum (fun J _=>hs I J)).symm)

theorem original_retained_sector_GV (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
        retainedKernel q.1 q.2 W K Tsec Z ξ)=
      heightCoeff η t C*star (heightCoeff η t D)*
        ∑ U : Finset (CommonIndex C D),∑' h : O,
          if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
            sectorFrequency η t S β C D hC hD
              (physicalKernel C D W K (frequencyRadius Tsec Z ξ))
              ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) else 0 := by
  rw [retained_sector_eq_physical η t S β C D hC hD hCD W K Tsec Z ξ hK,
    actual_retained_sector_GV η t S β C D hC hD hCD W K (frequencyRadius Tsec Z ξ) hK]

end SevenEighths.CenteredMomentSecondSourceFrequency

end

end OAI

end Source611

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondRetainedAggregate.lean; sha256: 444b5fea70a7907a56f35218a41cd06f41e08f79f3623fdf339096f925e0816f -/
section Source612
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondLocalization CenteredMomentSecondSourceRetained CenteredMomentSecondSourceFrequency
open CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

theorem commonLabels_supported (S : Finset (Ideal O)) (C D : Ideal O)
    (h : (C,D)∈commonLabels (supportedColumns S) (supportedColumns S)) :
    Supported C ∧ Supported D := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
  rcases Prod.mk.inj he with ⟨rfl,rfl⟩
  have hp' := Finset.mem_product.mp hp
  exact ⟨commonPart_supported _ _ (Finset.mem_filter.mp hp'.1).2,
    commonPart_supported _ _ (Finset.mem_filter.mp hp'.2).2⟩

theorem original_retained_energy_GV (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ : ℝ) (hK : 0<K) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ p : commonLabels (supportedColumns S) (supportedColumns S),
        heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
          ∑ U : Finset (CommonIndex p.val.1 p.val.2),∑' h : O,
            if canonicalPartition p.val.1 p.val.2 U
                (nonunitFrequencyGenerator p.val.1 p.val.2 U*h) then
              sectorFrequency η t S β p.val.1 p.val.2
                (commonLabels_supported S _ _ p.property).1
                (commonLabels_supported S _ _ p.property).2
                (physicalKernel p.val.1 p.val.2 W K (frequencyRadius Tsec Z ξ))
                ((commonFrequencyGenerator p.val.1 p.val.2*
                  nonunitFrequencyGenerator p.val.1 p.val.2 U)*h) else 0 := by
  rw [retainedEnergy_common_sectors]
  rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro p hp
  exact original_retained_sector_GV η t S β p.val.1 p.val.2
    (commonLabels_supported S _ _ p.property).1 (commonLabels_supported S _ _ p.property).2
    (commonLabels_data _ _ _ _ p.property).2.2 W K Tsec Z ξ hK

end SevenEighths.CenteredMomentSecondRetainedAggregate

end

end OAI

end Source612

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondRetainedRows.lean; sha256: 83c1d39ab4ee02d7f7d262f80d72f45d5b5a5afd0814d6b2dddf5baa891a5989 -/
section Source613
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedRows
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

def retainedRows (R : ℝ) (A : O) : Finset O := rowNormDisk (Nat.ceil (4*R/normValue A))

theorem retained_mem_rows (R : ℝ) (A h : O) (hA : A≠0)
    (hh : retainedWeight R (normValue (A*h))≠0) : h∈retainedRows R A := by
  have he := retainedWeight_enclosure R _ hh
  have hAh : A*h≠0 := by
    intro hz
    have hn : normValue (A*h)=0 := by simp [hz,normValue]
    linarith [he.1]
  have hh0 : h≠0 := right_ne_zero_of_mul hAh
  apply mem_rowNormDisk.mpr
  constructor
  · have hn := normValue_pos h hh0
    unfold normValue at hn
    exact_mod_cast hn
  · have hbound : normValue h≤4*R/normValue A := by
      apply (le_div_iff₀ (normValue_pos A hA)).mpr
      simpa only [normValue_mul,mul_comm] using he.2
    have hb := hbound.trans (Nat.le_ceil (4*R/normValue A))
    unfold normValue at hb
    exact_mod_cast hb

theorem physical_sector_zero_of_weight (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (j : O)
    (hj : retainedWeight R (normValue j)=0) :
    sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) j=0 := by
  simp only [sectorFrequency,physicalKernel,hj,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]

theorem physical_partition_finite_rows (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (A : O) (hA : A≠0) (part : O→Prop) :
    (∑' h : O,if part h then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if part h then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  apply tsum_eq_sum
  intro h hh
  by_cases hp : part h
  · rw [ite_eq_left hp]
    apply physical_sector_zero_of_weight η t S β C D hC hD W K R (A*h)
    by_contra hn
    exact hh (retained_mem_rows R A h hA hn)
  · rw [ite_eq_right hp]

theorem actual_GV_finite_rows (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) :
    let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
    (∑' h : O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  dsimp only
  exact physical_partition_finite_rows η t S β C D hC hD W K R _
    (mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)) _

end SevenEighths.CenteredMomentSecondRetainedRows

end

end OAI

end Source613

/- Original source: OAI/NumberTheory/DirichletL/Moments/LogDyadic.lean; sha256: cd86b40a23c7f4a556bd0cf5d9741434b2e029cc509478ffe6ed15821e075bba -/
section Source614
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentLogDyadic
open CenteredMomentSectorLocalization CenteredMomentFirstWholeKernel

def logAnnulus (x : ℝ) : ℂ := annulus (Real.exp x)

theorem logAnnulus_smooth : ContDiff ℝ ∞ logAnnulus :=
  Complex.ofRealCLM.contDiff.comp (annulus_smooth.comp Real.contDiff_exp)

theorem logAnnulus_support : Function.support logAnnulus ⊆ Set.Icc (-Real.log 4) 0 := by
  intro x hx
  have hn : annulus (Real.exp x)≠0 := by simpa only [Function.mem_support,logAnnulus,ne_eq,Complex.ofReal_eq_zero] using hx
  have hlo : 1/4<Real.exp x := lt_of_not_ge (fun h=>hn (annulus_zero_low _ h))
  have hhi : Real.exp x<1 := lt_of_not_ge (fun h=>hn (annulus_zero_high _ h))
  constructor
  · have hh := Real.strictMonoOn_log (show 1/4∈Set.Ioi (0:ℝ) by norm_num)
      (Real.exp_pos x) hlo
    rw [Real.log_exp,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at hh
    exact hh.le
  · exact (Real.exp_lt_one_iff.mp hhi).le

theorem logAnnulus_compact : HasCompactSupport logAnnulus :=
  HasCompactSupport.intro (isCompact_Icc) (fun x hx=>by
    by_contra hn
    exact hx (logAnnulus_support hn))

theorem logAnnulus_norm (x : ℝ) : ‖logAnnulus x‖≤1 := by
  rw [logAnnulus,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (annulus_bounds _).1]
  exact (annulus_bounds _).2

theorem logAnnulus_log (q H : ℝ) (hq : 0<q) (hH : 0<H) :
    logAnnulus (Real.log (q/H))=(annulus (q/H):ℂ) := by
  rw [logAnnulus,Real.exp_log (div_pos hq hH)]

theorem actual_dyadic_log_window (n : ℤ) (q : ℝ) (hq : 0<q) :
    (dyadicWeight n q:ℂ)=logAnnulus (Real.log (q/dyadicScale n)) := by
  rw [logAnnulus_log q _ hq (dyadicScale_pos n)];rfl

theorem actual_product_windows (k H a b : ℝ)
    (hk : 0<k) (hH : 0<H) (ha : 0<a) (hb : 0<b) (n : Fin 4→ℤ) :
    ((dyadicWeight (n 0) k*dyadicWeight (n 1) H*
      dyadicWeight (n 2) a*dyadicWeight (n 3) b:ℝ):ℂ)=
      windows (fun _=>logAnnulus) k H a b
        (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  simp only [Complex.ofReal_mul,actual_dyadic_log_window (n 0) k hk,
    actual_dyadic_log_window (n 1) H hH,actual_dyadic_log_window (n 2) a ha,
    actual_dyadic_log_window (n 3) b hb,windows]

end SevenEighths.CenteredMomentLogDyadic

end

end OAI

end Source614

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondPhysicalWindow.lean; sha256: d5a73a7ba56abb8e264b5e5e6e2e46eafb45f7dafa03c8106c4c3d666d728a1b -/
section Source615
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalWindow
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorColumns
open CenteredMomentSecondWholeKernel CenteredMomentFirstWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSmooth CenteredMomentLogDyadic
local notation "O" => ActualEisensteinCubic.O

theorem physical_kernel_window (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (V : Fin 4→ℝ→ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    physicalKernel C D W K R (A*h) I J*
      windows V (secondEffectiveScale C D A K) (normValue h)
        (Ideal.absNorm I:ℝ) (Ideal.absNorm J:ℝ) K₀ H₀ A₀ B₀=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*
        (retainedWeight R (normValue (A*h)):ℂ)*
          wholeKernel W V (K₀*H₀/(A₀*B₀))
            (Real.log (secondEffectiveScale C D A K/K₀)) (Real.log (normValue h/H₀))
            (Real.log ((Ideal.absNorm I:ℝ)/A₀)) (Real.log ((Ideal.absNorm J:ℝ)/B₀)) := by
  have he := second_frequency_whole_kernel C D I J hC hD hI hJ A h hA hh K hK 1 W V
    K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
  dsimp only at he
  simp only [mul_one,normValue_eq_embedding] at he ⊢
  have hd : ‖eisEmbedding (CompletedGauss.primaryGenerator (C*I)*
      CompletedGauss.primaryGenerator (D*J))‖^2=
      (Ideal.absNorm (C*I):ℝ)*(Ideal.absNorm (D*J):ℝ) := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq _ ((supported_mul_iff _ _).mpr ⟨hC,hI⟩),
      primary_norm_sq _ ((supported_mul_iff _ _).mpr ⟨hD,hJ⟩)]
  rw [hd] at he
  unfold physicalKernel
  rw [hd]
  simp only [normValue_eq_embedding]
  convert congrArg (fun x : ℂ=>(retainedWeight R (‖eisEmbedding (A*h)‖^2):ℂ)*x) he using 1 <;> ring

theorem physical_kernel_dyadic (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (n : Fin 4→ℤ) :
    physicalKernel C D W K R (A*h) I J*
      ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue h)*
        dyadicWeight (n 2) (Ideal.absNorm I:ℝ)*dyadicWeight (n 3) (Ideal.absNorm J:ℝ):ℝ):ℂ)=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
        (retainedWeight R (normValue (A*h)):ℂ)*
          wholeKernel W (fun _=>logAnnulus)
            (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
            (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
            (Real.log (normValue h/dyadicScale (n 1)))
            (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
            (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3))) := by
  rw [actual_product_windows _ _ _ _ (secondEffectiveScale_pos C D hC.1 hD.1 A hA K hK)
    (normValue_pos h hh) (CenteredMomentFirstScale.norm_pos I hI.1)
    (CenteredMomentFirstScale.norm_pos J hJ.1)]
  exact physical_kernel_window C D I J hC hD hI hJ A h hA hh W K R hK _ _ _ _ _
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)

end SevenEighths.CenteredMomentSecondPhysicalWindow

end

end OAI

end Source615

/- Original source: OAI/NumberTheory/DirichletL/Moments/DyadicCount.lean; sha256: cd26719a1f24465eb4d47391f2d754a08bf3e1debb8d7392957bfb9289295e5e -/
section Source616
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.CenteredMomentDyadicCount
open CenteredMomentSectorLocalization

def indices (a b : ℝ) : Finset ℤ :=
  Finset.Icc ⌈Real.logb 2 a⌉ ⌊Real.logb 2 (4*b)⌋

lemma logb_dyadicScale (n : ℤ) : Real.logb 2 (dyadicScale n)=(n:ℝ) := by
  rw [dyadicScale,←Real.rpow_intCast,Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num)]

lemma mem_indices_iff_scale (a b : ℝ) (ha : 0<a) (hb : 0<b) (n : ℤ) :
    n∈indices a b ↔ a≤dyadicScale n ∧ dyadicScale n≤4*b := by
  rw [indices,Finset.mem_Icc,Int.ceil_le,Int.le_floor]
  rw [←logb_dyadicScale n]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(Real.logb_le_logb (by norm_num) ha (dyadicScale_pos n)).mp h1,
      (Real.logb_le_logb (by norm_num) (dyadicScale_pos n) (by positivity)).mp h2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨Real.logb_le_logb_of_le (by norm_num) ha h1,
      Real.logb_le_logb_of_le (by norm_num) (dyadicScale_pos n) h2⟩

lemma mem_indices_iff_whole_support (a b : ℝ) (ha : 0<a) (hab : a≤b) (n : ℤ) :
    n∈indices a b ↔ ∃q∈Icc a b,q∈tsupport (dyadicWeight n) := by
  rw [mem_indices_iff_scale a b ha (ha.trans_le hab) n]
  constructor
  · rintro ⟨hlo,hhi⟩
    refine ⟨max a (dyadicScale n/4),⟨le_max_left _ _,max_le hab (by linarith)⟩,?_⟩
    rw [dyadicWeight_tsupport_eq]
    exact ⟨le_max_right _ _,max_le hlo (by linarith [dyadicScale_pos n])⟩
  · rintro ⟨q,hq,hq'⟩
    have hh := dyadicWeight_tsupport n hq'
    exact ⟨hq.1.trans hh.2,by linarith [hq.2,hh.1]⟩

lemma support_indices (a b q : ℝ) (ha : 0<a) (hq : q∈Icc a b)
    (n : ℤ) (hne : dyadicWeight n q≠0) : n∈indices a b :=
  (mem_indices_iff_whole_support a b ha (hq.1.trans hq.2) n).mpr
    ⟨q,hq,subset_tsupport _ hne⟩

lemma finite_active_indices (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    {n : ℤ | ∃q∈Icc a b,q∈tsupport (dyadicWeight n)}.Finite := by
  apply (indices a b).finite_toSet.subset
  intro n hn
  exact (mem_indices_iff_whole_support a b ha hab n).mpr hn

lemma logb_four_mul (b : ℝ) (hb : 0<b) :
    Real.logb 2 (4*b)=2+Real.logb 2 b := by
  rw [Real.logb_mul (by norm_num) hb.ne']
  congr 1
  rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

theorem indices_card_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ((indices a b).card:ℝ)≤3+Real.logb 2 (b/a) := by
  have hb := ha.trans_le hab
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) ha hab
  have hu := Int.ceil_lt_add_one (Real.logb 2 a)
  have hl := Int.sub_one_lt_floor (Real.logb 2 (4*b))
  have he := logb_four_mul b hb
  have hle : ⌈Real.logb 2 a⌉≤⌊Real.logb 2 (4*b)⌋+1 := by
    have hh : (⌈Real.logb 2 a⌉:ℝ)≤(⌊Real.logb 2 (4*b)⌋:ℝ)+1 := by linarith
    exact_mod_cast hh
  have hcard := Int.card_Icc_of_le _ _ hle
  have hcard' : ((indices a b).card:ℝ)=(⌊Real.logb 2 (4*b)⌋:ℝ)+1-(⌈Real.logb 2 a⌉:ℝ) := by
    exact_mod_cast hcard
  rw [hcard',Real.logb_div hb.ne' ha.ne']
  linarith [Int.floor_le (Real.logb 2 (4*b)),Int.le_ceil (Real.logb 2 a)]

theorem scaled_indices_card_bound (a b T : ℝ) (ha : 0<a) (hab : a≤b) (hT : 0<T) :
    ((indices (a/T) (b/T)).card:ℝ)≤3+Real.logb 2 (b/a) := by
  have h := indices_card_bound (a/T) (b/T) (div_pos ha hT)
    (div_le_div_of_nonneg_right hab hT.le)
  have he : (b/T)/(a/T)=b/a := by field_simp
  rwa [he] at h

lemma dyadic_partition_on_interval (a b q : ℝ) (ha : 0<a) (hq : q∈Icc a b) :
    (∑n∈indices a b,dyadicWeight n q)=1 := by
  rw [←dyadicWeight_partition q (ha.trans_le hq.1)]
  symm
  apply tsum_eq_sum
  intro n hn
  by_contra hne
  exact hn (support_indices a b q ha hq n hne)

theorem four_indices_card_bound (a b : Fin 4→ℝ)
    (ha : ∀j,0<a j) (hab : ∀j,a j≤b j) :
    (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤
      ∏j:Fin 4,(3+Real.logb 2 (b j/a j)) := by
  rw [Fintype.card_pi]
  push_cast
  apply Finset.prod_le_prod₀
  · intro j hj
    positivity
  · intro j hj
    simpa only [Fintype.card_coe] using indices_card_bound (a j) (b j) (ha j) (hab j)

lemma retained_integral_mem (R q : ℝ) (hq : 1≤q) (n : ℤ)
    (hr : Retained R n) (hne : dyadicWeight n q≠0) :
    n∈indices 1 (max 1 R) := by
  rw [mem_indices_iff_scale 1 (max 1 R) (by norm_num) (by positivity) n]
  exact ⟨hq.trans (dyadicWeight_support n hne).2.le,
    (retained_scale_le R n hr).trans (by linarith [le_max_right (1:ℝ) R])⟩

theorem indices_card_log_bound (C R Z a b : ℝ) (hC : 1≤C) (hR : 0≤R)
    (hZ : 1≤Z) (ha : 0<a) (hab : a≤b) (hratio : b/a≤C*Z^R) :
    ((indices a b).card:ℝ)≤
      (3+Real.logb 2 C+R/Real.log 2)*(1+Real.log Z) := by
  have hb := ha.trans_le hab
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (div_pos hb ha) hratio
  rw [Real.logb_mul hCp.ne' (Real.rpow_pos_of_pos hZp R).ne',
    Real.logb_rpow_eq_mul_logb_of_pos hZp] at hlog
  apply (indices_card_bound a b ha hab).trans
  have hc0 := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
  have hz0 := Real.log_nonneg hZ
  have hr0 : 0≤R/Real.log 2 := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hp := mul_nonneg (show 0≤3+Real.logb 2 C by linarith) hz0
  have he : R*Real.logb 2 Z=(R/Real.log 2)*Real.log Z := by unfold Real.logb;ring
  rw [he] at hlog
  nlinarith

theorem four_indices_subpower (C R ε : ℝ) (hC : 1≤C) (hR : 0≤R) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ∀a b : Fin 4→ℝ,(∀j,0<a j) → (∀j,a j≤b j) →
      (∀j,b j/a j≤C*Z^R) →
      (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤D*Z^ε := by
  let K : ℝ := 3+Real.logb 2 C+R/Real.log 2
  have hK : 0<K := by
    have hc := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
    have hr := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [K]
    linarith
  have hlog := (isLittleO_log_rpow_rpow_atTop (4:ℝ) hε).bound (by norm_num : (0:ℝ)<1)
  refine ⟨16*K^4,by positivity,?_⟩
  filter_upwards [hlog,Filter.eventually_ge_atTop (Real.exp 1),Filter.eventually_ge_atTop (1:ℝ)] with Z hlog hZexp hZ
  intro a b ha hab hratio
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hz : 1≤Real.log Z := by
    have hh := Real.log_le_log (Real.exp_pos (1:ℝ)) hZexp
    simpa only [Real.log_exp] using hh
  have hp : (Real.log Z)^4≤Z^ε := by
    apply (le_abs_self _).trans
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hZp.le _),one_mul] using hlog
  have hcard : (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤(K*(1+Real.log Z))^4 := by
    rw [Fintype.card_pi]
    push_cast
    calc
      _ ≤ ∏j:Fin 4,K*(1+Real.log Z) := by
        apply Finset.prod_le_prod₀ (by intros;positivity)
        intro j hj
        simpa only [Fintype.card_coe] using indices_card_log_bound C R Z (a j) (b j) hC hR hZ (ha j) (hab j) (hratio j)
      _ = _ := by simp
  calc
    _ ≤ (K*(1+Real.log Z))^4 := hcard
    _ ≤ (K*(2*Real.log Z))^4 := by gcongr;linarith
    _ = (16*K^4)*(Real.log Z)^4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentDyadicCount

end

end OAI

end Source616

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondDyadicPartition.lean; sha256: 16304423a264f40cf3328ac77f19ba610d861649c6db3190acba10f7116b67ff -/
section Source617
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondDyadicPartition
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondSectorRetained CenteredMomentSecondPhysicalWindow
open CenteredMomentSecondWholeKernel CenteredMomentFirstWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSmooth CenteredMomentLogDyadic CenteredMomentDyadicCount
local notation "O" => ActualEisensteinCubic.O

abbrev Blocks (a b : Fin 4→ℝ) := ∀ i : Fin 4,↥(indices (a i) (b i))

theorem dyadic_product_partition (a b q : Fin 4→ℝ)
    (ha : ∀i,0<a i) (hq : ∀i,q i∈Set.Icc (a i) (b i)) :
    (∑ n : Blocks a b,∏ i : Fin 4,dyadicWeight (n i) (q i))=1 := by
  change (∑ n : (∀ i : Fin 4,↥(indices (a i) (b i))),∏ i : Fin 4,dyadicWeight (n i) (q i))=1
  rw [←Fintype.prod_sum (fun (i : Fin 4) (n : indices (a i) (b i))=>dyadicWeight n (q i))]
  have he (i : Fin 4) : (∑ n : indices (a i) (b i),dyadicWeight n (q i))=1 := by
    rw [Finset.sum_coe_sort (indices (a i) (b i)) (fun n : ℤ=>dyadicWeight n (q i))]
    exact dyadic_partition_on_interval _ _ _ (ha i) (hq i)
  simp_rw [he]
  simp

theorem physical_kernel_dyadic_partition (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (a b : Fin 4→ℝ) (ha : ∀i,0<a i)
    (hband : ∀i, (![secondEffectiveScale C D A K,normValue h,
      (Ideal.absNorm I:ℝ),(Ideal.absNorm J:ℝ)] : Fin 4→ℝ) i∈Set.Icc (a i) (b i)) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks a b,
        ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
          (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
          (retainedWeight R (normValue (A*h)):ℂ)*
            wholeKernel W (fun _=>logAnnulus)
              (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
              (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
              (Real.log (normValue h/dyadicScale (n 1)))
              (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
              (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3))) := by
  let q : Fin 4→ℝ := ![secondEffectiveScale C D A K,normValue h,
    (Ideal.absNorm I:ℝ),(Ideal.absNorm J:ℝ)]
  have he : (∑ n : Blocks a b,((∏i : Fin 4,dyadicWeight (n i) (q i)):ℝ):ℝ)=1 :=
    dyadic_product_partition a b q ha hband
  calc
    _ = physicalKernel C D W K R (A*h) I J*(1:ℂ) := (mul_one _).symm
    _ = ∑ n : Blocks a b,physicalKernel C D W K R (A*h) I J*
        ((∏i : Fin 4,dyadicWeight (n i) (q i):ℝ):ℂ) := by
      rw [←Finset.mul_sum,←Complex.ofReal_sum,he,Complex.ofReal_one]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Fin.prod_univ_four]
      exact physical_kernel_dyadic C D I J hC hD hI hJ A h hA hh W K R hK (fun i=>n i)

end SevenEighths.CenteredMomentSecondDyadicPartition

end

end OAI

end Source617

/- Original source: OAI/NumberTheory/DirichletL/Moments/ActiveSource.lean; sha256: 2f62e2fac885604a0e206df33911ed9ebaadf63e3b1be08d46ac8242adfba2b9 -/
section Source618
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentActiveSource
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentLiveDomain CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentFirstSectors CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

def activeSource (S : Finset (Ideal O)) (β : Ideal O → ℂ) : Finset (Ideal O) :=
  S.filter (fun I => β I≠0)

@[simp] theorem mem_activeSource (S : Finset (Ideal O)) (β : Ideal O → ℂ) (I : Ideal O) :
    I∈activeSource S β ↔ I∈S ∧ β I≠0 := Finset.mem_filter

theorem supportedColumns_active (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    supportedColumns (activeSource S β)=(supportedColumns S).filter (fun I => β I≠0) := by
  ext I
  simp only [supportedColumns,activeSource,Finset.mem_filter]
  tauto

theorem active_sum (S : Finset (Ideal O)) (β F : Ideal O → ℂ) :
    (∑I∈supportedColumns (activeSource S β),β I*F I)=
      ∑I∈supportedColumns S,β I*F I := by
  rw [supportedColumns_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs with h <;> simp_all

theorem sourceGaussEnergy_active (S : Finset (Ideal O)) (β f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (activeSource S β) β f W K=sourceGaussEnergy S β f W K := by
  unfold sourceGaussEnergy gaussEnergy
  apply tsum_congr
  intro z
  congr 2
  have hp := source_gaussPolynomial (activeSource S β) (fun I => β I*f I) z
  have hq := source_gaussPolynomial S (fun I => β I*f I) z
  rw [hp,hq]
  congr 2
  simpa only [mul_assoc] using active_sum S β (fun I => f I*primaryGaussRow I z)

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then
    secondRetainedPair I J hI hJ W K T Z ξ else 0 else 0

theorem secondRetainedEnergy_eq_sum (η : HeckeFamily.Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) :
    secondRetainedEnergy η t S β W K T Z ξ=
      ∑I∈supportedColumns S,∑J∈supportedColumns S,
        ((β I*CenteredMomentHeckeColumnWindow.heightCoeff η t I)*
          star (β J*CenteredMomentHeckeColumnWindow.heightCoeff η t J))*
          retainedKernel I J W K T Z ξ := by
  unfold secondRetainedEnergy
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I hI
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [retainedKernel,dite_eq_left (Finset.mem_filter.mp I.property).2,
    dite_eq_left (Finset.mem_filter.mp J.property).2]

theorem secondRetainedEnergy_active (η : HeckeFamily.Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) :
    secondRetainedEnergy η t (activeSource S β) β W K T Z ξ=
      secondRetainedEnergy η t S β W K T Z ξ := by
  rw [secondRetainedEnergy_eq_sum,secondRetainedEnergy_eq_sum,supportedColumns_active]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi : β I=0
  · simp [hi]
  · rw [ite_eq_left hi]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj : β J=0 <;> simp [hj]

theorem commonLabel_witnesses (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (h : (C,D)∈commonLabels (supportedColumns (activeSource S β))
      (supportedColumns (activeSource S β))) :
    ∃I∈S,∃J∈S,Supported I ∧ Supported J ∧ β I≠0 ∧ β J≠0 ∧
      commonPart I J=C ∧ commonPart J I=D := by
  obtain ⟨⟨I,J⟩,hp,he⟩ := Finset.mem_image.mp h
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hp
  obtain ⟨hi,hIs⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj,hJs⟩ := Finset.mem_filter.mp hj
  obtain ⟨hi,hβi⟩ := mem_activeSource S β I |>.mp hi
  obtain ⟨hj,hβj⟩ := mem_activeSource S β J |>.mp hj
  exact ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,(Prod.mk.inj he).1,(Prod.mk.inj he).2⟩

theorem commonLabel_norm_bounds (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (h : (C,D)∈commonLabels (supportedColumns (activeSource S β))
      (supportedColumns (activeSource S β))) :
    (Ideal.absNorm C:ℝ)≤H ∧ (Ideal.absNorm D:ℝ)≤H := by
  obtain ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,hC,hD⟩ := commonLabel_witnesses S β C D h
  constructor
  · rw [←hC]
    exact (Nat.cast_le.mpr (absNorm_commonPart_le I J hIs.1)).trans (hH I hi hβi)
  · rw [←hD]
    exact (Nat.cast_le.mpr (absNorm_commonPart_le J I hJs.1)).trans (hH J hj hβj)

theorem residualPool_data (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C : Ideal O) (hC : C≠0) (a : Ideal O)
    (ha : a∈residualPool C hC (supportedColumns (activeSource S β))) :
    C*a∈S ∧ β (C*a)≠0 ∧ Supported (C*a) ∧ a≠0 ∧
      1≤(Ideal.absNorm a:ℝ) ∧ (Ideal.absNorm a:ℝ)≤H/(Ideal.absNorm C:ℝ) := by
  have hm := (mem_residualPool C hC _ a).mp ha
  obtain ⟨hm,hsa⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm,hβ⟩ := (mem_activeSource S β (C*a)).mp hm
  have ha0 : a≠0 := right_ne_zero_of_mul hsa.1
  have hpos := CenteredMomentFirstScale.norm_pos C hC
  have hab := hH (C*a) hm hβ
  rw [map_mul,Nat.cast_mul] at hab
  refine ⟨hm,hβ,hsa,ha0,?_,?_⟩
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ha0)
  · exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hab)

theorem source_energy_active_sectors (τ : HeckeFamily.Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    sourceGaussEnergy S β (CenteredMomentHeckeColumnWindow.heightCoeff τ t) W K =
      ∑p∈commonLabels (supportedColumns (activeSource S β))
        (supportedColumns (activeSource S β)),
      ∑q∈pairSector p.1 p.2 (supportedColumns (activeSource S β))
        (supportedColumns (activeSource S β)),
      ((β q.1*CenteredMomentHeckeColumnWindow.heightCoeff τ t q.1)*
        star (β q.2*CenteredMomentHeckeColumnWindow.heightCoeff τ t q.2))*
        CenteredMomentSecondSourceEnergy.secondSourceKernel q.1 q.2 W K := by
  rw [←sourceGaussEnergy_active S β]
  exact CenteredMomentSecondSourceEnergy.source_energy_common_sectors τ t _ β W K hK

end SevenEighths.CenteredMomentActiveSource

end

end OAI

end Source618

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondActiveDyadic.lean; sha256: 5ac82d5a0d28f3e325c4a02a883b7b10e7b58af69d2eaf33d5e3693cce70d92c -/
section Source619
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondActiveDyadic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorColumns CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicPartition CenteredMomentSecondWholeKernel CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSecondRetainedRows
local notation "O" => ActualEisensteinCubic.O

def sourceLower (C D : Ideal O) (A : O) (K : ℝ) : Fin 4→ℝ :=
  ![secondEffectiveScale C D A K,1,1,1]

def sourceUpper (C D : Ideal O) (A : O) (K R H : ℝ) : Fin 4→ℝ :=
  ![secondEffectiveScale C D A K,max 1 (4*R/normValue A),
    max 1 (H/(Ideal.absNorm C:ℝ)),max 1 (H/(Ideal.absNorm D:ℝ))]

def dyadicKernel (C D : Ideal O) (A : O) (W : 𝓢(ℝ,ℂ)) (K R : ℝ)
    (n : Fin 4→ℤ) (h : O) (I J : Ideal O) : ℂ :=
  ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
    (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
    (retainedWeight R (normValue (A*h)):ℂ)*
      wholeKernel W (fun _=>logAnnulus)
        (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
        (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
        (Real.log (normValue h/dyadicScale (n 1)))
        (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
        (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))

theorem active_sector_norm (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C : Ideal O) (hC : C≠0) (I : sectorPool C hC (activeSource S β)) :
    (Ideal.absNorm (I:Ideal O):ℝ)∈Set.Icc 1 (max 1 (H/(Ideal.absNorm C:ℝ))) := by
  have hh := residualPool_data S β H hH C hC I (Finset.mem_filter.mp I.property).1
  exact ⟨hh.2.2.2.2.1,hh.2.2.2.2.2.trans (le_max_right _ _)⟩

theorem sourceLower_pos (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (A : O) (hA : A≠0) (K : ℝ) (hK : 0<K) : ∀i,0<sourceLower C D A K i := by
  intro i
  fin_cases i
  · exact secondEffectiveScale_pos C D hC hD A hA K hK
  all_goals norm_num [sourceLower]

theorem active_physical_kernel_partition (_η : Character)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (I : sectorPool C hC.1 (activeSource S β)) (J : sectorPool D hD.1 (activeSource S β))
    (A h : O) (hA : A≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks (sourceLower C D A K) (sourceUpper C D A K R H),
        dyadicKernel C D A W K R (fun i=>n i) h I J := by
  by_cases hw : retainedWeight R (normValue (A*h))=0
  · simp only [physicalKernel,dyadicKernel,hw,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]
  have he := retainedWeight_enclosure R _ hw
  have hh : h≠0 := by
    intro hz
    subst h
    simp [normValue] at he
  have hrow : normValue h≤4*R/normValue A := by
    apply (le_div_iff₀ (normValue_pos A hA)).mpr
    simpa only [normValue_mul,mul_comm] using he.2
  have hb : ∀i, (![secondEffectiveScale C D A K,normValue h,
      (Ideal.absNorm (I:Ideal O):ℝ),(Ideal.absNorm (J:Ideal O):ℝ)] : Fin 4→ℝ) i∈
        Set.Icc (sourceLower C D A K i) (sourceUpper C D A K R H i) := by
    intro i
    fin_cases i
    · exact ⟨le_rfl,le_rfl⟩
    · exact ⟨normValue_ge_one h hh,hrow.trans (le_max_right _ _)⟩
    · exact active_sector_norm S β H hH C hC.1 I
    · exact active_sector_norm S β H hH D hD.1 J
  exact physical_kernel_dyadic_partition C D I J hC hD
    (sectorPool_supported C hC.1 _ I) (sectorPool_supported D hD.1 _ J)
    A h hA hh W K R hK _ _ (sourceLower_pos C D hC.1 hD.1 A hA K hK) hb

end SevenEighths.CenteredMomentSecondActiveDyadic

end

end OAI

end Source619

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondCanonicalScalar.lean; sha256: c52f4a4ae80e97f80fe5f761ebaf2aae357daf373f245f5ac6cca7e3e4f6d2c8 -/
section Source620
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalScalar
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSectorLocalization CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

def normalizer (C D : Ideal O) (U : Finset (CommonIndex C D)) : ℝ :=
  partitionNormalizer (commonPrime C D) (leftExponent C D) (rightExponent C D) U

theorem normalizer_pos (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    0<normalizer C D U := by
  rw [normalizer,partitionNormalizer_eq_norm_ratio _ (commonPrime_supported C D hC) _ _
    (leftExponent_pos C D) (rightExponent_pos C D)]
  exact div_pos (commonIdeal_norm_pos _ (commonPrime_supported C D hC) _ _)
    (unitIdeal_norm_pos _ (commonPrime_supported C D hC) _)

def retainedScalar (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) (h : O) : ℂ :=
  canonicalPartitionScalar C D U (nonunitFrequencyGenerator C D U*h)*
    (retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)):ℂ)

theorem actual_retained_scalar_norm (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (h : O) :
    ‖retainedScalar C D U R h*idealCorrelation C D hC hD
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)‖≤1 := by
  have hs := actual_ideal_partition_scalar C D hC hD hCD U (nonunitFrequencyGenerator C D U*h)
  have hw := retainedWeight_bounds R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))
  rw [retainedScalar,mul_right_comm,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw.1]
  exact (mul_le_of_le_one_left hw.1 (by simpa only [mul_assoc] using hs)).trans hw.2

theorem original_partition_scalar (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (R : ℝ) (h : O) (F : ℂ) :
    (if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      (retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)):ℂ)*F else 0)=
      (normalizer C D U:ℂ)*(retainedScalar C D U R h*F) := by
  have hn : (normalizer C D U:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (normalizer_pos C D hC U).ne'
  unfold retainedScalar canonicalPartitionScalar
  change _=(normalizer C D U:ℂ)*((if _ then (normalizer C D U:ℂ)⁻¹ else 0)*_*F)
  split_ifs <;> simp_all [mul_assoc]

end SevenEighths.CenteredMomentSecondCanonicalScalar

end

end OAI

end Source620

/- Original source: OAI/NumberTheory/DirichletL/Moments/ExceptionalReflection.lean; sha256: 95e9a3ec5af47f18386762c8368eb5cec63baa17ac21db5d7b43598c2aeccd87 -/
section Source621
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentExceptionalReflection
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CenteredMomentChildRows
open CenteredMomentFixedRay CenteredMomentExceptionalPair RayFourExpansion
open CanonicalRowCompletion CanonicalQuadraticSieve CanonicalUnitEuler
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem child_rows_zero_off_support (η : Character) (χ ξ : RayCharacter)
    (m A z n : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hn : ¬Supported (Ideal.span {n})) :
    rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) n = 0 ∧
      rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) n = 0 := by
  exact ⟨rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn,
    rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn⟩

theorem child_row_reflection (η : Character) (χ ξ : RayCharacter)
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) (n : O) :
    rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) n =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) n *
        elementCoeff (reflectionRatio χ ξ) n := by
  by_cases hn : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ m 1 (A*(-z)) n hn,
      rowTwist_extract_sixth_mask _ m 1 (A*z) n hn]
    simp only [one_pow, one_mul]
    change elementCoeff (childCharacter η ξ) n * coprimalityMask m n *
        idealRowHom (A*(-z)) (Ideal.span {n}) =
      (elementCoeff (childCharacter η χ) n * coprimalityMask m n *
        idealRowHom (A*z) (Ideal.span {n})) * elementCoeff (reflectionRatio χ ξ) n
    rw [childCharacter_ratio, reflectionRatio, elementCoeff_product,
      HeckeUnitRows.elementCoeff_character]
    have hu : unitSupplement (-1 : Oˣ) n = idealRowHom (-1) (Ideal.span {n}) := by
      change (if Supported (Ideal.span {n}) then
        idealRowHom ((-1 : Oˣ) : O) (Ideal.span {n}) else 0) = _
      rw [ite_eq_left hn]
      rfl
    rw [hu, show A*(-z) = (-1)*(A*z) by ring, idealRowHom_argument_mul]
    ring
  · obtain ⟨hleft, hright⟩ := child_rows_zero_off_support η χ ξ m A z n hmLam hm2 hn
    rw [hleft, hright, zero_mul]

theorem child_row_reflection_hom (η : Character) (χ ξ : RayCharacter)
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) *
        elementHom (reflectionRatio χ ξ) := by
  ext n
  exact child_row_reflection η χ ξ m A z hmLam hm2 n

theorem fixedInducingRow_reflected (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hex : FixedInducingRow (childCharacter η χ) Q m A z) :
    FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  exact fixedInducingRow_of_product (childCharacter η χ) (childCharacter η ξ)
    (reflectionRatio χ ξ) Q m A z (-z) (reflectionRatio_modulus χ ξ Q hQ)
    (child_row_reflection η χ ξ m A z hmLam hm2) hex

theorem fixedInducingRow_reflection_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    FixedInducingRow (childCharacter η χ) Q m A z ↔
      FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  constructor
  · exact fixedInducingRow_reflected η χ ξ Q hQ m A z hmLam hm2
  · intro hex
    simpa only [neg_neg] using
      fixedInducingRow_reflected η ξ χ Q hQ m A (-z) hmLam hm2 hex

theorem not_fixedInducingRow_reflection_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    (¬FixedInducingRow (childCharacter η χ) Q m A z) ↔
      ¬FixedInducingRow (childCharacter η ξ) Q m A (-z) :=
  not_congr (fixedInducingRow_reflection_iff η χ ξ Q hQ m A z hmLam hm2)

end SevenEighths.CenteredMomentExceptionalReflection

end

end OAI

end Source621

/- Original source: OAI/NumberTheory/DirichletL/Moments/RestrictedEnergy.lean; sha256: 9379aa46d3688feb0e18b78584aa660ff69de898771519376713d8d8180975b7 -/
section Source622
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentRestrictedEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion CenteredMomentRowNorm
open CenteredMomentPlainEnergy CenteredMomentPlainChildEnergy CenteredMomentCauchy CenteredMomentSmooth
open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def restrictedEnergy {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (c : α → ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, if keep z then ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re else 0

theorem restricted_summable {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => if keep z then
      ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re else 0) := by
  have hs := Complex.hasSum_re (rowEnergy_summable S a ha c W K hK).hasSum
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  exact hs.summable.indicator {z | keep z}

theorem finite_energy_le_restricted {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hkeep : ∀ z ∈ rows, keep z)
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c z‖^2) ≤ restrictedEnergy keep S a c W K := by
  calc
    _ ≤ ∑ z ∈ rows, if keep z then
        ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re else 0 := by
      apply Finset.sum_le_sum
      intro z hz
      rw [ite_eq_left (hkeep z hz)]
      exact le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)
    _ ≤ _ := sum_le_hasSum rows
      (by intro z hz; split_ifs; exact mul_nonneg (sq_nonneg _) (hW z); exact le_rfl)
      (restricted_summable keep S a ha c W K hK).hasSum

theorem finite_negative_energy_le_restricted {α : Type*} (keep : O → Prop)
    (S : Finset α) (a : α → O) (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hkeep : ∀ z ∈ rows, keep (-z))
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c (-z)‖^2) ≤ restrictedEnergy keep S a c W K := by
  have he := finite_energy_le_restricted keep S a ha c W K hK (rows.image Neg.neg)
    (by intro z hz; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz; exact hkeep w hw) hW
    (by intro z hz; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        simpa only [map_neg,norm_neg] using hmajor w hw)
  rwa [Finset.sum_image (fun x hx y hy hxy => neg_injective hxy)] at he

def nonexceptional (η : HeckeFamily.Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (m A₀ z : O) : Prop :=
  z ≠ 0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow
    (CenteredMomentChildRows.childCharacter η χ) Q m A₀ z

theorem nonexceptional_reflection (η : HeckeFamily.Character)
    (χ ξ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m A₀ z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    nonexceptional η χ Q m A₀ z ↔ nonexceptional η ξ Q m A₀ (-z) := by
  unfold nonexceptional
  rw [neg_ne_zero]
  exact and_congr Iff.rfl (CenteredMomentExceptionalReflection.not_fixedInducingRow_reflection_iff
    η χ ξ Q hQ m A₀ z hmLam hm2)

theorem nonexceptional_ray_independent (η : HeckeFamily.Character)
    (χ ξ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m A₀ z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    nonexceptional η χ Q m A₀ z ↔ nonexceptional η ξ Q m A₀ z := by
  have h₁ := nonexceptional_reflection η χ ξ Q hQ m A₀ z hmLam hm2
  have h₂ := nonexceptional_reflection η ξ ξ Q hQ m A₀ (-z) hmLam hm2
  simpa only [neg_neg] using h₁.trans h₂

theorem whole_kernel_restricted_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (_ha : ∀ i, Supported (Ideal.span {a i}))
        (_hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ) (keep₁ keep₂ : O → Prop),
      (∀ z ∈ rows, keep₁ z) → (∀ z ∈ rows, keep₂ (-z)) →
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (restrictedEnergy keep₁ S a (fun i => c i * columnPhase (V 2) (u i) t) U K) ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (restrictedEnergy keep₂ T b (fun j => d j * star (columnPhase (V 3) (v j) t)) U K) ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * idealRowHom z (Ideal.span {a i})) * star (d j * idealRowHom (-z) (Ideal.span {b j}))) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η keep₁ keep₂ hkeep₁ hkeep₂ hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * idealRowHom z (Ideal.span {a i}))
    (fun z j => d j * idealRowHom (-z) (Ideal.span {b j})) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_restricted keep₁ S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hkeep₁ hU hmajor).trans (hleft t)
  have hR' := (finite_negative_energy_le_restricted keep₂ T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hkeep₂ hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial S a (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial T b (fun j => d j * star (columnPhase (V 3) (v j) t)) (-z)‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_rowPolynomial, rightColumn_eq_star_rowPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentRestrictedEnergy

end

end OAI

end Source622

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondNonexceptional.lean; sha256: 21961176a61b9d6de5d6496cec5dfaf46d6acfffb780c87ae80053e915468a1b -/
section Source623
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondNonexceptional
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth RayFourExpansion
open CenteredMomentSecondDescent CenteredMomentSecondScaled CenteredMomentRestrictedEnergy
local notation "O" => ActualEisensteinCubic.O

theorem whole_kernel_nonexceptional_second_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (D E A₀ : O) (a : α → O) (b : β → O)
        (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
        (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j})),
      (ConcretePrimeRowBridge.goodLambda^2 ∣ D-1) →
      (ConcretePrimeRowBridge.goodLambda^2 ∣ E-1) →
      (∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1) →
      (∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1) →
      (∀ i, IsCoprime (D*E) (a i)) → (∀ j, IsCoprime (D*E) (b j)) →
      ∀ (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η₀ : HeckeFamily.Character) (χ₀ : RayCharacter)
        (Q : Ideal O) (m : O),
      (Q ≤ Ideal.span {(72:O)}) → (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ z ∈ rows, nonexceptional η₀ χ₀ Q m A₀ z) →
      (∀ z ∈ rows, ‖q z*actualCorrelation D E hD hE (A₀*z)‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₁ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₂ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ χ : RayCharacter, ∀ t : ℝ,
        (restrictedEnergy (nonexceptional η₀ χ Q m A₀) S a (fun i => divisorCoefficient L a (movingCoefficient A₀ a c) χ i*columnPhase (V 2) (u i) t) U K) ≤
          (B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ ξ : RayCharacter, ∀ t : ℝ,
        (restrictedEnergy (nonexceptional η₀ ξ Q m A₀) T b (fun j => divisorCoefficient L b (movingCoefficient A₀ b d) ξ j*star (columnPhase (V 3) (v j) t)) U K) ≤
          (B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A * ‖∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
        (if IsCoprime (a i) (b j) then
          actualCorrelation (D*a i) (E*b j)
            (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0) * (c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖ ≤
        C*∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_restricted_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x η₀ χ₀ Q m hQ hmLam hm2 hrows hq hV₀ hV₁ U K hK hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [actual_scaled_row_children rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  apply finite_ray_divisor_bound _ D E _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (movingCoefficient A₀ a c) χ) (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹)) u v ρ x
    (fun z => q z*actualCorrelation D E hD hE (A₀*z))
    (nonexceptional η₀ χ Q m A₀) (nonexceptional η₀ (ξ⁻¹) Q m A₀)
    (fun z hz => (nonexceptional_ray_independent η₀ χ₀ χ Q hQ m A₀ z hmLam hm2).mp (hrows z hz))
    (fun z hz => (nonexceptional_reflection η₀ χ₀ (ξ⁻¹) Q hQ m A₀ z hmLam hm2).mp (hrows z hz)) hq hV₀ hV₁ U K hK hU hmajor
    (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL) (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.CenteredMomentSecondNonexceptional

end

end OAI

end Source623

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondIdealBlockBound.lean; sha256: c56505362654c570abd4a2fa3af134d41983bdcd5a9d11d2d871dfc367fb21c1 -/
section Source624
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondIdealBlockBound
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem logAnnulus_enclosure (x : ℝ) (hx : logAnnulus x≠0) : |x|≤Real.log 4 := by
  have hh := logAnnulus_support hx
  exact abs_le.mpr ⟨hh.1,hh.2.trans (Real.log_nonneg (by norm_num))⟩

theorem actual_nonexceptional_block_bound (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ B : ℝ,0≤B ∧ ∀ r : ℝ,0<r →
      ∀ (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
        (C D : Ideal O) (hC : Supported C) (hD : Supported D),
      primeSupport C=primeSupport D →
      ∀ (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
        (ρ x : O→ℝ) (u : sectorPool C hC.1 S→ℝ) (v : sectorPool D hD.1 S→ℝ)
        (Q : Ideal O) (m : O) (χ₀ : RayCharacter),
      Q≤Ideal.span {(72:O)} → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let c := fun I : sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I
      let d := fun J : sectorPool D hD.1 S=>β (D*J)*heightCoeff η t J
      (∀ z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀ (Φ : 𝓢(ℝ,ℂ)) (H : ℝ),0<H →
      (∀ z : O,0≤(Φ (normValue z/H)).re) →
      (∀ z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀ E₁ E₂ : Ideal O→ℝ,
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),0≤E₁ L) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),0≤E₂ L) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),∀ χ : RayCharacter,∀ w : ℝ,
        restrictedEnergy (nonexceptional η χ Q m A) Finset.univ (sectorElement C hC.1 S)
          (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
            (movingCoefficient A (sectorElement C hC.1 S) c) χ I*columnPhase logAnnulus (u I) w) Φ H≤
              (E₁ L*(1+‖w‖)^J₁)^2) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),∀ χ : RayCharacter,∀ w : ℝ,
        restrictedEnergy (nonexceptional η χ Q m A) Finset.univ (sectorElement D hD.1 S)
          (fun J=>divisorCoefficient L (sectorElement D hD.1 S)
            (movingCoefficient A (sectorElement D hD.1 S) d) χ J*star (columnPhase logAnnulus (v J) w)) Φ H≤
              (E₂ L*(1+‖w‖)^J₂)^2) →
      (1+r)^decay*‖∑ z∈rows,retainedScalar C D U R z*
        ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            (c I*star (d J))*wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z) (u I) (v J)‖≤
        B*∑ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(E₁ L*E₂ L) := by
  obtain ⟨B,hB,hbound⟩ := whole_kernel_nonexceptional_second_bound W (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num)) (fun _ x hx=>logAnnulus_enclosure x hx)
    decay J₁ J₂
  refine ⟨B,hB,?_⟩
  intro r hr η t S β C D hC hD hCD U R rows ρ x u v Q m χ₀ hQ hmLam hm2
  dsimp only
  intro hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hcopD (J : sectorPool D hD.1 S) :
      IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement D hD.1 S J) := by
    simpa only [mul_comm] using sectorElement_coprime D C hD hC hCD.symm S J
  have he := hbound r hr rows Finset.univ Finset.univ (primaryGenerator C) (primaryGenerator D)
    (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
    (sectorElement C hC.1 S) (sectorElement D hD.1 S)
    ((supported_span_primaryGenerator_iff C).mpr hC) ((supported_span_primaryGenerator_iff D).mpr hD)
    (sectorElement_supported C hC.1 S) (sectorElement_supported D hD.1 S)
    (primaryGenerator_spec C (supported_primaryGenerator_ne_zero C hC)).2
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary D hD.1 S)
    (sectorElement_coprime C D hC hD hCD S) hcopD
    (retainedScalar C D U R) (fun I=>β (C*I)*heightCoeff η t I)
    (fun J=>β (D*J)*heightCoeff η t J) u v ρ x η χ₀ Q m hQ hmLam hm2 hrows
    (fun z _=>actual_retained_scalar_norm C D hC hD hCD U R z)
    (fun z _=>logAnnulus_norm _) (fun z _=>logAnnulus_norm _)
    Φ H hH (by simpa only [normValue_eq_embedding] using hΦ)
    (by simpa only [normValue_eq_embedding] using hmajor) E₁ E₂
    (by simpa only [sectorElement_span] using hE₁) (by simpa only [sectorElement_span] using hE₂)
    (by simpa only [sectorElement_span] using hleft) (by simpa only [sectorElement_span] using hright)
  have hcop (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      IsCoprime (sectorElement C hC.1 S I) (sectorElement D hD.1 S J) ↔
        IsCoprime (I:Ideal O) (J:Ideal O) := by
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  simp_rw [hcop,sectorElement_span] at he
  simpa only [idealCorrelation,primaryGenerator_mul,sectorElement] using he

end SevenEighths.CenteredMomentSecondIdealBlockBound

end

end OAI

end Source624

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondMovingSupport.lean; sha256: 249e832bcbb14b298ef644fdbe3b412b704f3526ead201411da96e4476e9987e -/
section Source625
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondMovingSupport
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSupport CenteredMomentSupportedCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem actual_unequal_min_six (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0)
    (P : CommonIndex C D) (hneq : leftExponent C D P≠rightExponent C D P) :
    6∣min (leftExponent C D P) (rightExponent C D P) := by
  let (P : CommonIndex C D) : (Ideal.span {commonPrime C D P}).IsMaximal := by
    rw [commonPrime_span C D hC P];infer_instance
  have hglobal : actualCorrelation (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)
      (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      ((∏ P : CommonIndex C D,commonPrime C D P^min (leftExponent C D P) (rightExponent C D P))*w)≠0 := by
    simpa only [left_generator_product C D hC hCD,right_generator_product C D hC hD hCD,
      commonFrequencyGenerator,idealCorrelation] using hne
  have hl := local_nonzero_of_global (commonPrime C D) (commonPrime_supported C D hC)
    (commonPrime_coprime C D hC) (leftExponent C D) (rightExponent C D) w hglobal P
  exact nonzero_unequal_min_six (commonPrime C D P) (commonPrime_supported C D hC P)
    (by rw [commonPrime_span C D hC P];exact common_good C D hC P)
    (by rw [commonPrime_span C D hC P];exact common_odd C D hC P)
    _ _ (leftExponent_pos C D P) (rightExponent_pos C D P) hneq _ hl

def fixedExponent (C D : Ideal O) (U : Finset (CommonIndex C D)) (P : CommonIndex C D) : ℕ :=
  min (leftExponent C D P) (rightExponent C D P)+if P∈nonunitPartitionSet C D U then 1 else 0

def fixedActiveSet (C D : Ideal O) (U : Finset (CommonIndex C D)) : Finset (CommonIndex C D) :=
  Finset.univ.filter (fun P=>¬6∣fixedExponent C D U P)

theorem fixedActiveSet_subset (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) :
    fixedActiveSet C D U⊆U∪nonunitPartitionSet C D U := by
  intro P hP
  have ha := (Finset.mem_filter.mp hP).2
  by_contra hn
  have hU : P∉U := fun h=>hn (Finset.mem_union_left _ h)
  have hV : P∉nonunitPartitionSet C D U := fun h=>hn (Finset.mem_union_right _ h)
  have heq : ¬(leftExponent C D P=rightExponent C D P ∧ ¬6∣leftExponent C D P) := by
    intro he
    exact hV (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,hU⟩)
  rw [fixedExponent,ite_eq_right hV,add_zero] at ha
  by_cases hc : leftExponent C D P=rightExponent C D P
  · rw [hc,min_self] at ha
    exact heq ⟨hc,by simpa only [hc] using ha⟩
  · exact ha (actual_unequal_min_six C D hC hD hCD w hne P hc)

theorem fixed_active_log_bound (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0)
    (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z (Ideal.absNorm (∏P∈fixedActiveSet C D U,P.val):ℝ)≤
      Real.logb Z (Ideal.absNorm (∏P∈U,P.val):ℝ)+
        Real.logb Z (Ideal.absNorm (Ideal.span {nonunitFrequencyGenerator C D U}):ℝ) := by
  have hn (P : CommonIndex C D) : 0≤Real.logb Z (Ideal.absNorm P.val:ℝ) :=
    Real.logb_nonneg hZ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPrime_supported_ideal C D hC P).1)))
  have hlog (T : Finset (CommonIndex C D)) :
      Real.logb Z (Ideal.absNorm (∏P∈T,P.val):ℝ)=∑P∈T,Real.logb Z (Ideal.absNorm P.val:ℝ) := by
    simp only [map_prod,Nat.cast_prod]
    exact Real.logb_prod _ _ (fun P _=>Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPrime_supported_ideal C D hC P).1))
  rw [CenteredMomentSecondCanonicalLedger.nonunitFrequencyGenerator_span,unitIdeal]
  simp only [commonPrime_span C D hC]
  have hdis : Disjoint U (nonunitPartitionSet C D U) := by
    apply Finset.disjoint_left.mpr
    intro P hU hV
    exact (Finset.mem_sdiff.mp hV).2 hU
  rw [hlog,hlog,hlog,←Finset.sum_union hdis]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fixedActiveSet_subset C D hC hD hCD U w hne)
    (fun P _ _=>hn P)

end SevenEighths.CenteredMomentSecondMovingSupport

end

end OAI

end Source625

/- Original source: OAI/NumberTheory/DirichletL/Hecke/ModulusRefinement.lean; sha256: 10760a970f8dc85bb90e2d797f12f13a34f280e5899b55fa34bc1111d73736c0 -/
section Source626
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFamily
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def Character.refineModulus (η : Character) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus) : Character :=
  Character.ofResidue M hM (ResidueCharacter.inflate hle η.residue)
    (ResidueCharacter.inflate_global_units hle η.residue η.unit_trivial)

theorem elementCoeff_refineModulus (η : Character) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus) (n : O) :
    elementCoeff (η.refineModulus M hM hle) n =
      if IsUnit (Ideal.Quotient.mk M n) then elementCoeff η n else 0 :=
  ResidueCharacter.inflate_mk hle η.residue n

theorem idealCoeff_refineModulus (η : Character) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus) (I : Ideal O) :
    idealCoeff (η.refineModulus M hM hle) I =
      if IsCoprime I M then idealCoeff η I else 0 :=
  IdealCharacter.ofResidue_source_mask M η.modulus _ _ _ _
    (ResidueCharacter.inflate_mk hle η.residue) I

theorem idealCoeff_source_mask (η : Character) (I : Ideal O) :
    idealCoeff η I = if IsCoprime I η.modulus then idealCoeff η I else 0 := by
  apply IdealCharacter.ofResidue_source_mask η.modulus η.modulus η.residue η.residue
    η.unit_trivial η.unit_trivial _ I
  intro n
  split_ifs with hn
  · rfl
  · exact MulChar.map_nonunit _ hn

def Character.excludePrimes (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) : Character :=
  η.refineModulus (η.modulus * ∏ P ∈ S, P)
    (mul_ne_zero η.modulus_ne_bot (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)))
    Ideal.mul_le_left

theorem idealCoeff_excludePrimes (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    idealCoeff (η.excludePrimes S hS) I =
      if ∀ P ∈ S, IsCoprime I P then idealCoeff η I else 0 := by
  rw [Character.excludePrimes, idealCoeff_refineModulus, IsCoprime.mul_right_iff,
    IsCoprime.prod_right_iff]
  by_cases hη : IsCoprime I η.modulus
  · simp only [hη, true_and]
  · have hz : idealCoeff η I = 0 := by simpa only [hη, ite_false] using idealCoeff_source_mask η I
    simp [hη, hz]

theorem excludePrimes_mask (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    idealCoeff (η.excludePrimes S hS) I =
      if IsCoprime I (η.excludePrimes S hS).modulus then idealCoeff η I else 0 :=
  idealCoeff_refineModulus η _ _ _ I

end SevenEighths.HeckeFamily

end

end OAI

end Source626

/- Original source: OAI/NumberTheory/DirichletL/Hecke/MaskDescent.lean; sha256: 6aea5168746b85d4d9248a4debaea71be43fcdf969ba8df0c68d028c5797f69b -/
section Source627
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.HeckeMaskDescent
open HeckeFamily CenteredExceptionalProfile CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem exists_coprime_shift (a c r : O) (hac : IsCoprime a c) (hr : r ≠ 0) :
    ∃ t : O, IsCoprime (a+t*c) r := by
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := (normalizedFactors r).filter (fun p => ¬p ∣ a)
  refine ⟨s.prod, IsCoprime.symm ?_⟩
  apply isCoprime_of_prime_dvd (by rintro ⟨h,-⟩; exact hr h)
  intro p hp hpr hpnew
  by_cases hpa : p ∣ a
  · have hpc : ¬p ∣ c := fun h => hp.not_isUnit (hac.isUnit_of_dvd' hpa h)
    have hps : ¬p ∣ s.prod := by
      intro h
      obtain ⟨q,hq,hpq⟩ := hp.exists_mem_multiset_dvd h
      obtain ⟨hqr,hqa⟩ := Multiset.mem_filter.mp hq
      exact hqa ((hp.associated_of_dvd (prime_of_normalized_factor q hqr) hpq).dvd'.trans hpa)
    have ht : p ∣ s.prod*c := by convert dvd_sub hpnew hpa using 1 ; ring
    exact (hp.dvd_or_dvd ht).elim hps hpc
  · obtain ⟨q,hq,hpq⟩ := exists_mem_normalizedFactors_of_dvd hr hp.irreducible hpr
    have hqs : q ∈ s := Multiset.mem_filter.mpr ⟨hq,fun h => hpa (hpq.dvd.trans h)⟩
    have ht : p ∣ s.prod*c := dvd_mul_of_dvd_left (hpq.dvd.trans (Multiset.dvd_prod hqs)) c
    exact hpa (by convert dvd_sub hpnew ht using 1 ; ring)

theorem exists_primitive_above (χ : Character) (Q : Ideal O)
    (hdesc : FiniteConductor.FactorsThroughIdeal χ.residue
      (Q.map (Ideal.Quotient.mk χ.modulus))) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ ψ := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  obtain ⟨K,φ,hMK,hQK,hK,hprim,hnorm,hmask⟩ :=
    ConductorPresentation.exists_primitive_presentation_above_quotient
      χ.modulus χ.residue (Q.map (Ideal.Quotient.mk χ.modulus)) hdesc
  have hu : IdealCharacter.UnitInvariant K φ := by
    intro u
    have h := hmask (u : O)
    simpa only [χ.unit_trivial u,u.isUnit.map (Ideal.Quotient.mk χ.modulus),ite_true] using h.symm
  refine ⟨Character.ofResidue K hK φ hu,hprim,?_,?_⟩
  · exact (Ideal.le_comap_map).trans hQK
  · exact IdealCharacter.ofResidue_source_mask χ.modulus K χ.residue φ χ.unit_trivial hu hmask

theorem descent_of_mask (χ χ' ψ : Character) (r : O) (hr : r ≠ 0)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0)
    (hind : InducedBy χ' ψ) :
    FiniteConductor.FactorsThroughIdeal χ.residue
      (ψ.modulus.map (Ideal.Quotient.mk χ.modulus)) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  rw [FiniteConductor.factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨q,hq,hqu⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk χ.modulus) Ideal.Quotient.mk_surjective).mp hu
  let a : O := 1+q
  have ha : Ideal.Quotient.mk χ.modulus a = (u : O ⧸ χ.modulus) := by
    dsimp [a];rw [map_add,map_one,hqu];ring
  have hψa : Ideal.Quotient.mk ψ.modulus a = 1 := by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr hq,add_zero]
  let c := idealGenerator (χ.modulus*ψ.modulus)
  have hc : IsCoprime a c := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [show Ideal.span {c}=χ.modulus*ψ.modulus from span_idealGenerator _]
    apply IsCoprime.mul_right
    · exact (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (ha ▸ u.isUnit)
    · exact (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hψa ▸ isUnit_one)
  obtain ⟨t,htall⟩ := exists_coprime_shift a c (r*goodLambda) hc
    (mul_ne_zero hr goodLambda_prime.ne_zero)
  have ht := htall.of_mul_right_left
  let n := a+t*c
  have hmem : c ∈ χ.modulus*ψ.modulus := by
    rw [← span_idealGenerator (χ.modulus*ψ.modulus)]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hnχ : Ideal.Quotient.mk χ.modulus n = (u : O ⧸ χ.modulus) := by
    dsimp [n];rw [map_add,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_left hmem),mul_zero,add_zero,ha]
  have hnψ : Ideal.Quotient.mk ψ.modulus n = 1 := by
    dsimp [n];rw [map_add,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_right hmem),mul_zero,add_zero,hψa]
  have hnχ' : elementCoeff χ' n ≠ 0 := by
    rw [he n,ite_eq_left ht]
    exact MulChar.apply_ne_zero_iff.mpr (hnχ ▸ u.isUnit)
  have hn0 : n ≠ 0 := by
    intro hz
    have hunit : IsUnit goodLambda := (htall.of_mul_right_right).isUnit_of_dvd'
      (by change goodLambda ∣ n; rw [hz]; exact dvd_zero _) (dvd_refl _)
    exact goodLambda_prime.not_isUnit hunit
  have hcop : IsCoprime (Ideal.span {n}) χ'.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hnχ')
  have heq := elementCoeff_eq_of_inducedBy χ' ψ hind n hn0 hcop
  rw [he n,ite_eq_left ht] at heq
  change χ.residue (Ideal.Quotient.mk χ.modulus n) = ψ.residue (Ideal.Quotient.mk ψ.modulus n) at heq
  simpa only [hnχ,hnψ,map_one] using heq

theorem inducedBy_mask (χ χ' ψ : Character) (r : O)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0)
    (hind : InducedBy χ ψ) : InducedBy χ' ψ := by
  intro I
  by_cases hI : I = 0
  · simp only [hI,map_zero,ite_self]
  by_cases hc : IsCoprime I χ'.modulus
  · have hn' := CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I |>.mpr ⟨hI,hc⟩
    let n := idealGenerator I
    have hn0 : n ≠ 0 := idealGenerator_ne_zero I hI
    have hspan : Ideal.span {n} = I := span_idealGenerator I
    have hval' : elementCoeff χ' n = idealCoeff χ' I := by
      rw [← idealCoeff_span χ' hn0,hspan]
    have hval : elementCoeff χ n = idealCoeff χ I := by
      rw [← idealCoeff_span χ hn0,hspan]
    have hm := he n
    have hcr : IsCoprime n r := by
      by_contra hr
      rw [ite_eq_right hr,hval'] at hm
      exact hn' hm
    rw [ite_eq_left hcr,hval',hval] at hm
    have hn := hm ▸ hn'
    have hcχ := (CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn |>.2
    rw [ite_eq_left hc,hm,hind I,ite_eq_left hcχ]
  · have hz : idealCoeff χ' I = 0 := by
      by_contra hn
      exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I).mp hn).2
    rw [ite_eq_right hc,hz]

theorem fixed_inducing_mask_iff (χ χ' : Character) (r : O) (hr : r ≠ 0)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0) (Q : Ideal O) :
    (∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ' ψ) ↔
    (∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ ψ) := by
  constructor
  · rintro ⟨ψ,hprim,hQ,hind⟩
    obtain ⟨ρ,hρ,hmod,hindρ⟩ := exists_primitive_above χ ψ.modulus
      (descent_of_mask χ χ' ψ r hr he hind)
    exact ⟨ρ,hρ,hQ.trans hmod,hindρ⟩
  · rintro ⟨ψ,hprim,hQ,hind⟩
    exact ⟨ψ,hprim,hQ,inducedBy_mask χ χ' ψ r he hind⟩
end SevenEighths.HeckeMaskDescent

end

end OAI

end Source627

/- Original source: OAI/NumberTheory/DirichletL/Moments/FixedRowMask.lean; sha256: 9a440781108bafcc585539e3335109767636da222a130c3c14bbbfabae379a3e -/
section Source628
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFixedRowMask
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem row_mask_mul (η : Character) (m r A z n : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    rowTwist (elementHom η) (m*r) 1 (A*z) n =
      if IsCoprime n r then rowTwist (elementHom η) m 1 (A*z) n else 0 := by
  by_cases hs : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ _ _ _ _ hs,
      rowTwist_extract_sixth_mask _ _ _ _ _ hs]
    change elementHom η n * (if IsCoprime (m*r) n then (1:ℂ) else 0) * _ = _
    rw [IsCoprime.mul_left_iff]
    by_cases hm : IsCoprime m n <;> by_cases hr : IsCoprime n r <;>
      simp [coprimalityMask,hm,hr,show IsCoprime r n ↔ IsCoprime n r from isCoprime_comm]
  · rw [rowTwist_zero_of_not_supported _ _ _ _ _
        (hmLam.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _)) hs,
      rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hs]
    split_ifs <;> rfl

theorem fixedInducingRow_mul_mask_iff (η : Character) (Q : Ideal O)
    (m r A z : O) (hm : m ≠ 0) (hr : r ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow η Q (m*r) A z ↔ FixedInducingRow η Q m A z := by
  obtain ⟨χ,hχ⟩ := exists_row_character η m 1 (A*z) hm one_ne_zero
    (mul_ne_zero hA hz) hmLam hm2
  obtain ⟨χ',hχ'⟩ := exists_row_character η (m*r) 1 (A*z) (mul_ne_zero hm hr)
    one_ne_zero (mul_ne_zero hA hz) (hmLam.trans (dvd_mul_right _ _))
      (hm2.trans (dvd_mul_right _ _))
  have hmask (n : O) : elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0 := by
    rw [hχ' n,hχ n,row_mask_mul η m r A z n hmLam hm2]
  have transport (ρ : Character) (mask : O)
      (hρ : ∀ n,elementCoeff ρ n=rowTwist (elementHom η) mask 1 (A*z) n) :
      FixedInducingRow η Q mask A z ↔
        ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
          Q ≤ ψ.modulus ∧ InducedBy ρ ψ := by
    constructor
    · rintro ⟨ρ₀,ψ,hprim,hind,hQ,hρ₀⟩
      exact ⟨ψ,hprim,hQ,CenteredMomentHeckeVolume.inducedBy_of_elementCoeff_eq
        ρ₀ ρ ψ (fun n => (hρ n).trans (hρ₀ n).symm) hind⟩
    · rintro ⟨ψ,hprim,hQ,hind⟩
      exact ⟨ρ,ψ,hprim,hind,hQ,hρ⟩
  rw [transport χ' (m*r) hχ',transport χ m hχ]
  exact HeckeMaskDescent.fixed_inducing_mask_iff χ χ' r hr hmask Q
end SevenEighths.CenteredMomentFixedRowMask

end

end OAI

end Source628

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSixthReduction.lean; sha256: 537bfc71b25e2222924fac9bc770fd1da57d2fcf61c8912dfbc174606faa6254 -/
section Source629
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSixthReduction
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondMovingSupport CenteredMomentFixedRowMask
open CenteredExceptionalProfile CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

def reducedNumerator (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^(fixedExponent C D U P%6)

def sixthFactor (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^(fixedExponent C D U P/6)

theorem fixed_numerator_product (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U=
      ∏ P : CommonIndex C D,commonPrime C D P^fixedExponent C D U P := by
  have hv : nonunitFrequencyGenerator C D U=
      ∏ P : CommonIndex C D,if P∈nonunitPartitionSet C D U then commonPrime C D P else 1 := by
    simp only [nonunitFrequencyGenerator,Finset.prod_ite_mem,Finset.univ_inter]
  rw [commonFrequencyGenerator,hv,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [fixedExponent,pow_add]
  split_ifs <;> simp

theorem fixed_sixth_factorization (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U=
      reducedNumerator C D U*(sixthFactor C D U)^6 := by
  rw [fixed_numerator_product,reducedNumerator,sixthFactor,←Finset.prod_pow,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  rw [←pow_mul,←pow_add]
  congr 1
  omega

theorem reducedNumerator_ne_zero (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    reducedNumerator C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>pow_ne_zero _
    (supported_element_ne_zero _ (commonPrime_supported C D hC P)))

theorem sixthFactor_ne_zero (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    sixthFactor C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>pow_ne_zero _
    (supported_element_ne_zero _ (commonPrime_supported C D hC P)))

theorem fixed_sixth_row (η : Character) (m h n : O) (C D : Ideal O)
    (U : Finset (CommonIndex C D)) :
    rowTwist (elementHom η) m 1
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) n=
    rowTwist (elementHom η) (m*sixthFactor C D U) 1 (reducedNumerator C D U*h) n := by
  rw [fixed_sixth_factorization]
  have he : m ^ 6 * 1 ^ 4 * ((reducedNumerator C D U * sixthFactor C D U ^ 6) * h) =
      (m * sixthFactor C D U) ^ 6 * 1 ^ 4 * (reducedNumerator C D U * h) := by ring
  exact congrArg
    (fun x => elementHom η n * idealRowHom x (Ideal.span {n})) he

theorem fixed_sixth_inducing_iff (η : Character) (Q : Ideal O) (m h : O)
    (hm : m≠0) (hh : h≠0) (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    FixedInducingRow η Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) h ↔
      FixedInducingRow η Q m (reducedNumerator C D U) h := by
  have he : FixedInducingRow η Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) h ↔
      FixedInducingRow η Q (m*sixthFactor C D U) (reducedNumerator C D U) h := by
    unfold FixedInducingRow
    simp only [fixed_sixth_row]
  exact he.trans (fixedInducingRow_mul_mask_iff η Q m (sixthFactor C D U)
    (reducedNumerator C D U) h hm (sixthFactor_ne_zero C D hC U)
    (reducedNumerator_ne_zero C D hC U) hh hmLam hm2)

end SevenEighths.CenteredMomentSecondSixthReduction

end

end OAI

end Source629

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSixthSource.lean; sha256: a7d4be0ef4a6a5f38b7e6b821501c373910a301ae057e77148e91b081aed4bf1 -/
section Source630
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSixthSource
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

theorem sixthFactor_span_dvd (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    Ideal.span {sixthFactor C D U}∣C := by
  conv_rhs => rw [←left_ideal_product C D hC hCD]
  simp only [sixthFactor,span_finset_product,←Ideal.span_singleton_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  have hc := leftExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤leftExponent C D P := min_le_left _ _
  unfold fixedExponent
  split_ifs <;> omega

theorem fixed_sixth_coefficient (C D : Ideal O) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I*
        (if IsCoprime I (Ideal.span {sixthFactor C D U}) then 1 else 0) := by
  rw [fixed_sixth_factorization,idealRowHom_argument_mul,idealRowHom_sixth_mask _ I hI]

theorem residual_sixth_coefficient (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime C I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,ite_eq_left
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd C D hC hCD U)),mul_one]

abbrev ActiveIndex (C D : Ideal O) (U : Finset (CommonIndex C D)) := ↥(fixedActiveSet C D U)

def activePrime (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : O := commonPrime C D P.val

def activeExponent (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : ℕ := fixedExponent C D U P.val%6

theorem activeExponent_pos (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : 0<activeExponent C D U P := by
  have hp : ¬6∣fixedExponent C D U P.val := (Finset.mem_filter.mp P.property).2
  exact Nat.pos_of_ne_zero (fun h=>hp (Nat.dvd_of_mod_eq_zero h))

theorem activeExponent_lt (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : activeExponent C D U P<6 := Nat.mod_lt _ (by norm_num)

theorem reducedNumerator_active_product (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    reducedNumerator C D U=∏ P : ActiveIndex C D U,activePrime C D U P^activeExponent C D U P := by
  simp only [activePrime,activeExponent]
  rw [Finset.prod_coe_sort (fixedActiveSet C D U)
    (fun P : CommonIndex C D=>commonPrime C D P^(fixedExponent C D U P%6))]
  unfold reducedNumerator
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro P hP hn
  have hp : 6∣fixedExponent C D U P := by
    simpa only [fixedActiveSet,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hn
  simp only [Nat.mod_eq_zero_of_dvd hp,pow_zero]

end SevenEighths.CenteredMomentSecondSixthSource

end

end OAI

end Source630

/- Original source: OAI/NumberTheory/DirichletL/Moments/PlainWindowEnergy.lean; sha256: 215f0e673c53068554f80d6e631185b7cc28c488c845aefeb8ca6fb12417b6bb -/
section Source631
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentPlainWindowEnergy
open CanonicalQuadraticSieve CenteredMomentRowNorm CenteredMomentPlainEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open HeckeFamily FourierBridge CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem plain_column_integral {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    rowPolynomial S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        rowPolynomial S a (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z := by
  have hi (i : α) : Integrable (fun w : ℝ => β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*CanonicalRowCompletion.idealRowHom z (Ideal.span {a i})) :=
    ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul _).mul_const _
  unfold rowPolynomial
  calc
    _ = ∑ i∈S,∫ w : ℝ,β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*CanonicalRowCompletion.idealRowHom z (Ideal.span {a i}) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_mul_const,integral_const_mul,← height_column_integral V hVc hVs τ _ (ha i).1 t θ X hX]
      ring
    _ = _ := by
      rw [← integral_finsetSum _ (fun i _ => hi i)]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem plain_column_integrable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      rowPolynomial S a (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z) := by
  have hi (i : α) := ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul (β i)).mul_const
    (CanonicalRowCompletion.idealRowHom z (Ideal.span {a i}))
  convert integrable_finsetSum S (fun i _ => hi i) using 1
  funext w
  simp only [rowPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem rowEnergy_hasSum_re {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ‖rowPolynomial S a c z‖^2*
      (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rowEnergy S a c U K).re := by
  have hs := Complex.hasSum_re (rowEnergy_summable S a ha c U K hK).hasSum
  simpa only [rowEnergy,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hs

theorem finite_weighted_le_rowEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rows : Finset O) :
    (∑ z∈rows,‖rowPolynomial S a c z‖^2*(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)≤
      (rowEnergy S a c U K).re :=
  sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hU z)) (rowEnergy_hasSum_re S a ha c U K hK)

theorem plain_window_energy_from_shifted {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ w : ℝ,(rowEnergy S a
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) U K).re≤E*(1+‖w‖)^(2*J)) :
    (rowEnergy S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K).re≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let u := fun z : O => (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re
  let c := fun i => β i*heightCoeff τ t (Ideal.span {a i})*
    CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ
  have hnorm (z : O) (x : ℂ) : ‖(Real.sqrt (u z):ℂ)*x‖^2=u z*‖x‖^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
      Real.sq_sqrt (hU z)]
  have hfin (rows : Finset O) : (∑ z∈rows,‖rowPolynomial S a c z‖^2*u z)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
    let φ := fun z : rows => fun w : ℝ => (Real.sqrt (u z):ℂ)*
      (logPhase (θ-w) (Real.log X)*rowPolynomial S a
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z)
    have hi (z : rows) : Integrable (fun w => columnDensity V hVc hVs w*φ z w) := by
      have h := (plain_column_integrable S a ha β τ t θ X hX V hVc hVs z).const_mul (Real.sqrt (u z):ℂ)
      convert h using 1
      funext w
      dsimp only [φ]
      ring
    have hb (w : ℝ) : (∑ z : rows,‖φ z w‖^2)≤E*((1+‖w‖)^J)^2 := by
      simp only [φ]
      simp_rw [hnorm]
      simp only [norm_mul,logPhase_norm,one_mul,← pow_mul]
      rw [Finset.sum_coe_sort rows (fun z : O => u z*‖rowPolynomial S a
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)]
      simpa only [mul_comm,Nat.mul_comm] using
        (finite_weighted_le_rowEnergy S a ha _ U K hK hU rows).trans (henergy w)
    have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
      (fun w => (1+‖w‖)^J) (by intro w;positivity) E hE (columnDensity_moments V hVc hVs J) hi hb
    have he (z : rows) : (∫ w : ℝ,columnDensity V hVc hVs w*φ z w)=
        (Real.sqrt (u z):ℂ)*rowPolynomial S a c z := by
      rw [show rowPolynomial S a c z=_ from plain_column_integral S a ha β τ t θ X hX V hVc hVs z,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [φ]
      ring
    simp only [he,hnorm] at hh
    rw [Finset.sum_coe_sort rows (fun z : O => u z*‖rowPolynomial S a c z‖^2)] at hh
    simpa only [mul_comm] using hh
  have hs := rowEnergy_hasSum_re S a ha c U K hK
  rw [← hs.tsum_eq]
  exact Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hU z)) hfin

theorem plain_window_energy_from_height {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ v : ℝ,(rowEnergy S a
      (fun i => β i*heightCoeff τ v (Ideal.span {a i})) U K).re≤E*(1+‖v‖)^(2*J)) :
    (rowEnergy S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K).re≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply plain_window_energy_from_shifted V hVc hVs J S a ha β τ t θ X hX U K hK hU
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow,mul_assoc]

end SevenEighths.CenteredMomentPlainWindowEnergy

end

end OAI

end Source631

/- Original source: OAI/NumberTheory/DirichletL/Moments/RestrictedWindow.lean; sha256: 9a00ac97aedebd1bdf351d3fd97825c13e8555dadeff4c588bd5da42083f36a8 -/
section Source632
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentRestrictedWindow
open CanonicalQuadraticSieve CenteredMomentRowNorm CenteredMomentRestrictedEnergy
open CenteredMomentPlainWindowEnergy CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open HeckeFamily FourierBridge CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem restricted_hasSum_weighted {α : Type*} (keep : O → Prop)
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ‖rowPolynomial S a c z‖^2*
      (if keep z then (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0))
      (restrictedEnergy keep S a c U K) := by
  simpa only [mul_ite,mul_zero,restrictedEnergy] using
    (restricted_summable keep S a ha c U K hK).hasSum

theorem finite_weighted_le_restricted {α : Type*} (keep : O → Prop)
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rows : Finset O) :
    (∑ z∈rows,‖rowPolynomial S a c z‖^2*
      (if keep z then (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0))≤
      restrictedEnergy keep S a c U K := by
  apply sum_le_hasSum rows _ (restricted_hasSum_weighted keep S a ha c U K hK)
  intro z hz
  apply mul_nonneg (sq_nonneg _)
  split_ifs
  · exact hU z
  · exact le_rfl

theorem restricted_window_energy_from_shifted {α : Type*} (keep : O → Prop)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ w : ℝ,(restrictedEnergy keep S a
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) U K)≤E*(1+‖w‖)^(2*J)) :
    (restrictedEnergy keep S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let u := fun z : O => if keep z then (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hu (z : O) : 0≤u z := by dsimp only [u];split_ifs;exact hU z;exact le_rfl
  let c := fun i => β i*heightCoeff τ t (Ideal.span {a i})*
    CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ
  have hnorm (z : O) (x : ℂ) : ‖(Real.sqrt (u z):ℂ)*x‖^2=u z*‖x‖^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
      Real.sq_sqrt (hu z)]
  have hfin (rows : Finset O) : (∑ z∈rows,‖rowPolynomial S a c z‖^2*u z)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
    let φ := fun z : rows => fun w : ℝ => (Real.sqrt (u z):ℂ)*
      (logPhase (θ-w) (Real.log X)*rowPolynomial S a
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z)
    have hi (z : rows) : Integrable (fun w => columnDensity V hVc hVs w*φ z w) := by
      have h := (plain_column_integrable S a ha β τ t θ X hX V hVc hVs z).const_mul (Real.sqrt (u z):ℂ)
      convert h using 1
      funext w
      dsimp only [φ]
      ring
    have hb (w : ℝ) : (∑ z : rows,‖φ z w‖^2)≤E*((1+‖w‖)^J)^2 := by
      simp only [φ]
      simp_rw [hnorm]
      simp only [norm_mul,logPhase_norm,one_mul,← pow_mul]
      rw [Finset.sum_coe_sort rows (fun z : O => u z*‖rowPolynomial S a
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)]
      have hbound :=
        (finite_weighted_le_restricted keep S a ha _ U K hK hU rows).trans (henergy w)
      rw [Nat.mul_comm 2 J] at hbound
      calc
        _ = ∑ z ∈ rows, ‖rowPolynomial S a
            (fun i => β i * heightCoeff τ (t + 2 * Real.pi * (w - θ))
              (Ideal.span {a i})) z‖ ^ 2 * u z := by
          apply Finset.sum_congr rfl
          intro z hz
          exact mul_comm _ _
        _ ≤ _ := hbound
    have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
      (fun w => (1+‖w‖)^J) (by intro w;positivity) E hE (columnDensity_moments V hVc hVs J) hi hb
    have he (z : rows) : (∫ w : ℝ,columnDensity V hVc hVs w*φ z w)=
        (Real.sqrt (u z):ℂ)*rowPolynomial S a c z := by
      rw [show rowPolynomial S a c z=_ from plain_column_integral S a ha β τ t θ X hX V hVc hVs z,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [φ]
      ring
    simp only [he,hnorm] at hh
    rw [Finset.sum_coe_sort rows (fun z : O => u z*‖rowPolynomial S a c z‖^2)] at hh
    calc
      _ = ∑ z ∈ rows, u z * ‖rowPolynomial S a c z‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro z hz
        exact mul_comm _ _
      _ ≤ _ := hh
  have hs := restricted_hasSum_weighted keep S a ha c U K hK
  rw [← hs.tsum_eq]
  exact Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hu z)) hfin

theorem restricted_window_energy_from_height {α : Type*} (keep : O → Prop)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ v : ℝ,(restrictedEnergy keep S a
      (fun i => β i*heightCoeff τ v (Ideal.span {a i})) U K)≤E*(1+‖v‖)^(2*J)) :
    (restrictedEnergy keep S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K)≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply restricted_window_energy_from_shifted keep V hVc hVs J S a ha β τ t θ X hX U K hK hU
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow,mul_assoc]

end SevenEighths.CenteredMomentRestrictedWindow

end

end OAI

end Source632

/- Original source: OAI/NumberTheory/DirichletL/Moments/RestrictedDomain.lean; sha256: 858b59af3e7814ef82790be9d11f50d9abd81d9b1c33e08c2ace28d73e496a9e -/
section Source633
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedDomain
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve
open CenteredMomentRowNorm CenteredMomentRestrictedEnergy CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

theorem source_rowPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I) z=
      ∑ I∈supportedColumns S,c I*CanonicalRowCompletion.idealRowHom z I := by
  unfold rowPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*CanonicalRowCompletion.idealRowHom z I)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2]

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem live_rowPolynomial (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (z : O) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    rowPolynomial Finset.univ (sourceGenerator Q)
      (fun I : supportedColumns Q => c I*f I) z=
      rowPolynomial Finset.univ (sourceGenerator T)
        (fun I : supportedColumns T => c I*f I) z := by
  let c := finiteColumnCoefficient (liveBox S B hB)
    (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let T := finiteColumns (liveBox S B hB)
  change rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I : supportedColumns Q => c I*f I) z=_
  refine (source_rowPolynomial Q (fun I => c I*f I) z).trans ?_
  refine Eq.trans ?_ (source_rowPolynomial T (fun I => c I*f I) z).symm
  simpa only [mul_assoc] using live_column_sum S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I => f I*CanonicalRowCompletion.idealRowHom z I)

theorem live_restrictedEnergy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    restrictedEnergy keep Finset.univ (sourceGenerator Q)
      (fun I : supportedColumns Q => c I*f I) W K=
      restrictedEnergy keep Finset.univ (sourceGenerator T)
        (fun I : supportedColumns T => c I*f I) W K := by
  dsimp only
  unfold restrictedEnergy
  apply tsum_congr
  intro z
  exact congrArg (fun x : ℂ => if keep z then ‖x‖^2*(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)
    (live_rowPolynomial S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ f z)

end SevenEighths.CenteredMomentRestrictedDomain

end

end OAI

end Source633

/- Original source: OAI/NumberTheory/DirichletL/Moments/RestrictedSource.lean; sha256: 4917a704ba366169900d7b835d9a0ca78c0b9ab3fef38359efd84e176e628da3 -/
section Source634
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedSource
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedDomain
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentOriginalChildEnergy
local notation "O" => ActualEisensteinCubic.O

theorem rowPolynomial_allocation {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (b : γ → ℂ) (d : γ → α → ℂ) (z : O) :
    rowPolynomial S a (fun i => ∑ B,b B*d B i) z=
      ∑ B,b B*rowPolynomial S a (d B) z := by
  simp only [rowPolynomial,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

def sourceRestrictedEnergy (keep : O → Prop) (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  restrictedEnergy keep Finset.univ (sourceGenerator Q)
    (fun I : supportedColumns Q => c I*f I) W K

theorem smoothed_restricted_allocation {α γ : Type*} [Fintype γ] (keep : O → Prop)
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (restrictedEnergy keep S a (fun i => ∑ B,b B*d B i) W K)≤
      (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*(restrictedEnergy keep S a (d B) W K) := by
  let u := fun z : O => if keep z then (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hu (z : O) : 0≤u z := by dsimp only [u];split_ifs;exact hW z;exact le_rfl
  have hs := restricted_hasSum_weighted keep S a ha (fun i => ∑ B,b B*d B i) W K hK
  rw [← hs.tsum_eq]
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hu z))
  intro rows
  calc
    _ ≤ ∑ z∈rows,(Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        (‖rowPolynomial S a (d B) z‖^2*u z) := by
      apply Finset.sum_le_sum
      intro z hz
      have h := mul_le_mul_of_nonneg_right
        (CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B => b B*rowPolynomial S a (d B) z)) (hu z)
      rw [rowPolynomial_allocation]
      simpa only [Finset.card_univ,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using h
    _ = (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        ∑ z∈rows,‖rowPolynomial S a (d B) z‖^2*u z := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      exact mul_le_mul_of_nonneg_left
        (finite_weighted_le_restricted keep S a ha (d B) W K hK hW rows) (sq_nonneg _)

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem original_restricted_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K)≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K) := by
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let b := fun B : actualAllocations S C => frozenCoefficient B C R ν Wslot P
  let d := fun (B : actualAllocations S C) (I : supportedColumns Q) =>
    finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I*f I
  have he (I : supportedColumns Q) :
      (if IsCoprime C (I:Ideal O) then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)*f I=
      ∑ B,b B*d B I := by
    rw [original_source_punctured_column S hS hp C R s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hsC ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂,Finset.sum_mul]
    simp only [b,d,mul_assoc]
  have h := smoothed_restricted_allocation keep Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) b d W K hK hW
  have he' := funext he
  change (restrictedEnergy keep Finset.univ (sourceGenerator Q) _ W K)≤_
  rw [he']
  apply h.trans_eq
  rw [Fintype.card_coe]
  apply congrArg (fun x : ℝ => ((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  simpa only [b,d,sourceRestrictedEnergy] using
    congrArg (fun x : ℝ => ‖frozenCoefficient B C R ν Wslot P‖^2*x)
    (live_restrictedEnergy S hS hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f keep W K)

end SevenEighths.CenteredMomentRestrictedSource

end

end OAI

end Source634

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSectorEnergy.lean; sha256: 6719453e147e0169819e2be3d90d843cb30583589d40fdce3ef071f56603e3d6 -/
section Source635
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSectorEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentRestrictedSource CenteredMomentRestrictedDomain CenteredMomentRestrictedEnergy
open CenteredMomentLiveDomain CenteredMomentFirstSectors RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem sector_divisor_coefficient (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (I : sectorPool C hC.1 S) :
    divisorCoefficient L (sectorElement C hC.1 S)
      (movingCoefficient A (sectorElement C hC.1 S)
        (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ I=
      (if L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,sectorElement_span,hτ I (sectorPool_supported C hC.1 S I) t]
  dsimp only [sectorElement]
  split_ifs <;> ring

theorem sector_rowPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (C : Ideal O) (hC : Supported C) (z : O) :
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I : sectorPool C hC.1 S => c I) z=
      rowPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
        (fun I : supportedColumns (residualPool C hC.1 S) => if IsCoprime C (I:Ideal O) then c I else 0) z := by
  rw [source_rowPolynomial (residualPool C hC.1 S)
    (fun I => if IsCoprime C I then c I else 0) z]
  unfold rowPolynomial
  simp only [sectorElement_span]
  rw [Finset.sum_coe_sort (sectorPool C hC.1 S) (fun I => c I*idealRowHom z I)]
  rw [sectorPool,Finset.sum_filter,supported_residualPool C hC S]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp

theorem sector_child_row (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (z : O) :
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ) z=
      rowPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
        (fun I : supportedColumns (residualPool C hC.1 S) =>
          (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I) z := by
  have he := funext (sector_divisor_coefficient η τ χ A hτ S β C hC L t)
  rw [he,sector_rowPolynomial S (fun I => (if L∣I then β (C*I) else 0)*heightCoeff τ t I) C hC z]
  congr 1
  funext I
  split_ifs <;> simp_all

theorem sector_child_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (t : ℝ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J : sectorPool C hC.1 S => β (C*J)*heightCoeff η t J)) χ) W K=
      sourceRestrictedEnergy keep (residualPool C hC.1 S)
        (fun I => if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τ t) W K := by
  unfold restrictedEnergy sourceRestrictedEnergy
  apply tsum_congr
  intro z
  rw [sector_child_row η τ χ A hτ S β C hC L t z]

end SevenEighths.CenteredMomentSecondSectorEnergy

end

end OAI

end Source635

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondFamilyTransport.lean; sha256: 55adc5b89a4d92420e171804c36a7a48377ac83e0d68b6ad882eca5f10fd60a9 -/
section Source636
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondFamilyTransport
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondHeightFamily CenteredMomentSecondChildProfile CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredExceptionalProfile CenteredMomentRestrictedEnergy RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem row_presentation_height (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (I : Ideal O) (hI : Supported I) (t : ℝ) :
    heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I) := by
  have he := idealCoeff_eq_row (childCharacter η χ) τ fixedBadMask 1 A hτ I
  have he' : heightCoeff τ t I=rowWeight (childCharacter η χ) fixedBadMask 1 A t I := by
    change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
    rw [he]
    simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,one_pow,one_mul,mul_one]
  rw [he',rowWeight_split,←heightCoeff_eq_fixed_rowWeight (childCharacter η χ) t I hI]
  simp only [heightCoeff,child_ideal_primary η χ I hI]
  ring

theorem exists_second_family_presentation (η : Character) (χ : RayCharacter)
    (A : O) (hA : A≠0) :
    ∃ τ : Character,
      τ.modulus.absNorm≤rowConductorBound (childCharacter η χ) fixedBadMask 1 A ∧
      (∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n) ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_row_character_with_conductor (childCharacter η χ) fixedBadMask 1 A
    fixedBadMask_ne_zero one_ne_zero hA (dvd_mul_right _ _) (dvd_mul_left _ _)
  exact ⟨τ,hN,hτ,fun I hI t => row_presentation_height η τ χ A hτ I hI t⟩

theorem row_presentation_twist (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (z n : O) :
    rowTwist (elementHom τ) fixedBadMask 1 z n=
      rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 (A*z) n := by
  by_cases hn : Supported (Ideal.span {n})
  · have hc : coprimalityMask fixedBadMask n=1 := by
      change (if IsCoprime fixedBadMask n then (1:ℂ) else 0)=1
      rw [ite_eq_left (fixedBadMask_coprime n hn)]
    have ht := hτ n
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn] at ht
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn,rowTwist_extract_sixth_mask _ _ _ _ n hn]
    change elementCoeff τ n*coprimalityMask fixedBadMask n*idealRowHom (1^4*z) (Ideal.span {n})=_
    rw [ht,hc]
    simp only [one_pow,one_mul,mul_one,idealRowHom_argument_mul]
    ring
  · have hmLam : ConcretePrimeRowBridge.goodLambda∣fixedBadMask := dvd_mul_right _ _
    have hm2 : (2:O)∣fixedBadMask := dvd_mul_left _ _
    exact (rowTwist_zero_of_not_supported (elementHom τ) fixedBadMask 1 z n hmLam hm2 hn).trans
      (rowTwist_zero_of_not_supported (elementHom (childCharacter η χ)) fixedBadMask 1 (A*z) n hmLam hm2 hn).symm

theorem fixedInducingRow_transport (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (Q : Ideal O) (z : O) :
    FixedInducingRow τ Q fixedBadMask 1 z ↔
      FixedInducingRow (childCharacter η χ) Q fixedBadMask A z := by
  unfold FixedInducingRow
  simp only [one_mul,row_presentation_twist η τ χ A hτ]

theorem nonexceptional_transport (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (Q : Ideal O) (z : O) :
    nonexceptional η χ Q fixedBadMask A z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [nonexceptional,fixedInducingRow_transport η τ χ A hτ Q z]

end SevenEighths.CenteredMomentSecondFamilyTransport

end

end OAI

end Source636

/- Original source: OAI/NumberTheory/DirichletL/Moments/ConjugateWindow.lean; sha256: c20652c3cb5db5ed9e349a2481ef32beee5eb3f229cce272eb50f99dff73828f -/
section Source637
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentConjugateWindow
open FourierBridge CenteredMomentSmooth

theorem star_logPhase (t u : ℝ) : star (logPhase t u)=logPhase (-t) u := by
  simp only [logPhase,Complex.star_def,← Complex.exp_conj,map_mul,
    Complex.conj_ofReal,Complex.conj_I]
  congr 1
  push_cast
  ring

theorem star_columnPhase (V : ℝ → ℂ) (u t : ℝ) :
    star (columnPhase V u t)=columnPhase (fun x => star (V x)) u (-t) := by
  rw [columnPhase,star_mul,star_logPhase,columnPhase,mul_comm]
  congr 1
  simp only [rootWindow,Complex.star_def,map_div₀,Complex.conj_ofReal]

theorem conjugate_compact (V : ℝ → ℂ) (hV : HasCompactSupport V) :
    HasCompactSupport (fun x => star (V x)) := by
  apply hV.comp_left
  simp

theorem conjugate_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun x => star (V x)) := by
  exact Complex.conjCLE.contDiff.comp hV

end SevenEighths.CenteredMomentConjugateWindow

end

end OAI

end Source637

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondWindowSource.lean; sha256: 1649b0b03fbb84531456d08abfa0baf3cc9213a48bf4771f9705e92bc3d01e94 -/
section Source638
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedSource
open CenteredMomentChildAssembly CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentConjugateWindow
local notation "O" => ActualEisensteinCubic.O

theorem sector_window_from_source (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (keep : O→Prop) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ→ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀ z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀ v : ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) Φ H≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  have he (v : ℝ) := funext (sector_divisor_coefficient η τ χ A hτ S β C hC L v)
  simp_rw [sector_divisor_coefficient η τ χ A hτ S β C hC L t]
  have hh := restricted_window_energy_from_height keep V hVc hVs J Finset.univ
    (sectorElement C hC.1 S) (sectorElement_supported C hC.1 S)
    (fun I : sectorPool C hC.1 S=>if L∣(I:Ideal O) then β (C*I) else 0)
    τ t θ X hX Φ H hH hΦ E hE ?_
  · simpa only [sectorElement_span] using hh
  intro v
  have hs := hsource v
  rw [←sector_child_energy η τ χ A hτ S β C hC L v keep Φ H,he v] at hs
  simpa only [sectorElement_span] using hs

theorem star_logAnnulus (x : ℝ) : star (logAnnulus x)=logAnnulus x := by
  simp only [logAnnulus,Complex.star_def,Complex.conj_ofReal]

theorem star_logAnnulus_column (u t : ℝ) :
    star (columnPhase logAnnulus u t)=columnPhase logAnnulus u (-t) := by
  rw [star_columnPhase]
  simp only [star_logAnnulus]

theorem sector_conjugate_window_from_source (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (keep : O→Prop) (t θ X : ℝ) (hX : 0<X) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀ z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀ v : ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ)) Φ H≤
      (E*heightCost t (-θ)^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*
        ‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖)^2 := by
  simp only [star_logAnnulus_column]
  exact sector_window_from_source η τ χ A hτ S β C hC L keep t (-θ) X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth J Φ H hH hΦ E hE hsource

end SevenEighths.CenteredMomentSecondWindowSource

end

end OAI

end Source638

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondReducedEnergy.lean; sha256: a0f34dc0352edc3ac97dc6ae00c5308675a8af32a7900f5209d8daaa156c2ad8 -/
section Source639
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondReducedEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource CenteredMomentChildAssembly
open CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion CenteredMomentLogDyadic
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource CenteredMomentSecondWindowSource
local notation "O" => ActualEisensteinCubic.O

theorem masked_source_energy (η τ τr : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (hCD : primeSupport C=primeSupport D)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
          rayCharacter χ (primaryGenerator I))
    (hτr : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τr t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O)
    (keep : O→Prop) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τ t) Φ H=
    sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τr t) Φ H := by
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs with hi
  · have hI : Supported (I:Ideal O) := (Finset.mem_filter.mp I.property).2
    rw [hτ I hI t,hτr I hI t,residual_sixth_coefficient C D hC hCD U I hI hi.1]
  · simp only [zero_mul]

theorem original_window_from_reduced_source (η τr : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (_hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
    (hτr : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τr t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (keep : O→Prop)
    (t θ X : ℝ) (hX : 0<X) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀ v : ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τr v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
          (sectorElement C hC.1 S) (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) Φ H≤
      (E*heightCost t θ^(2*J))*(∫w:ℝ,(1+‖w‖)^J*
        ‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖)^2 := by
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 := by
    rw [fixed_sixth_factorization]
    exact mul_ne_zero (reducedNumerator_ne_zero C D hC U) (pow_ne_zero _ (sixthFactor_ne_zero C D hC U))
  obtain ⟨τ,hN,hτ⟩ := exists_second_family η χ _ hA
  apply sector_window_from_source η τ χ _ hτ S β C hC L keep t θ X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth J Φ H hH hΦ E hE
  intro v
  rw [masked_source_energy η τ τr χ C D hC hCD U hτ hτr S β L keep v Φ H]
  exact hsource v

end SevenEighths.CenteredMomentSecondReducedEnergy

end

end OAI

end Source639
